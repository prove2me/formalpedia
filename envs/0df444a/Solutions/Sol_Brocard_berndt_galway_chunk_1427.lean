-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1427
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:56:00.356051+00:00
-- url     : https://prove2.me/submissions/d0b2467c-0b76-4163-85e1-c7cfcc9477ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 256474820 ≤ n < 256654676 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 256476070 1250 256474820 256474831
    0x110f060d05040f0807050114060a050603071206050a1d07080c0f0d110301120c0803041a0d0e151906030309170c120c0117012d03020603042018 63
    0x2a20340700024100450500480c0c805070b0301140290300c6000b10708205008104c1c202402c0320650a007400301d402480d000686c2801c07900d000f40001c0c07039a65007274008c031080c0280303582c542200ca0301c42e0300c0429946d0b900803100010b484c0e11810380782125003000a034183c00401800030802d208604042c082e00f4040b000407240702009400000d6034520021120000a00451401c3d60034034401100200300c041444411800260140c004003031101d88507103081e5140d208038480e11840305062020218003032030042c060310303030780410030400603881d11400308103804d00c40010007407100390450004002120814032640c20340101e6040042061500316900540303040e00302d000c0c0c14094000c2c030002e0350740050100003415840700d0280c0102c040c5195000c0c0955501c41c1c0f1483e503400700b0b04070320384007140440302001c0d103040b2420303003981d03070140300d0b01d081346003a0742ea9641e20398240c0c5070201e9004000b41e2200b000030741c0200c0c480c40400f05c0d0040c3c403c11041c20400c0324080c15201b068903200242000070790044540c0c100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 256477320 1250 256476070 256476097
    0xc0d080405151e070605090c010e0d080d050702010605031b090103030c0f0f080405010e0103090c030209060a0807060f0e09040201020a021909061404060611060a0c051c09110f06 78
    0x518038888007902c28021010101c2d00d0000520043d001482541e01810006101d24400d100580340d811140751129810701000c2c2c00075800001055807854400500258140145012490200e0310700c040c4090700c0040745c90501503034440b00100600c0c02d003004039044800301a40034002401440b000a403d40d03a06200140400821542080a12500d0b0b142e8a101d02c1c1d20010204401d0158500009690464441c4070f02041e05544900b006502034000e00b03c1c40c0d50f22080440a1314119400c10140030405498030760080200d680106613008100400d03800303008681c940f06e00405a101d402010000d030503910b24010120300341417000503600015403801796030741184e14180c2c1003910514090b41c012503900c016041800c0c488001484a04614800d00f0014151810b00030301d5240c0302c00340c42c204410150512164400710011700344110650003900010b04078580140b812003520ba140a0640389040560620790b51062040200185038035100701c0000305480300615914103c001520078001d0b00544906c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 256478570 1250 256477320 256477339
    0xe040f030e060c0307051006050d0f0f0302010207050d1d01050f0901110c031005010e010509010510031107020a03030f030606141e040503060f090d05090609120a0b07110c0d080405 79
    0x102d80d9070109450105140008407078071000c0b1810460303590039917035180c00403642c90f10304081010b05000d00c810064a82129600c4050311155581070000100403d0507000c41d5824080b07900010014000c0600b45103650b50741381e80301e0b03c80089103002c8c807860541681c103101007000841000358036002500d000319000d09181c804903800300c4205007410101c8880d9580f41c02a0100c1510003050350380118180c41c55141101810b0f030b00c40707040c0018560203014195016131651402104644240c028032404059101c06909045c0c40d0303804030b0240c04540c0c000301d000c506000c100c4820b9552600c00c0000030800b030310305500402d1000745591040d2042d401a200342c60a00d00581d10201046812180240000f800300c0e03030f203498040c0c01090390080554161000307019060b07a5025092180c030603036461107401801286001c00c1d4104105100b1010350b00b0f20f500c1d00032005d811003c6050102028801d003006d4498000382d054145c030700da0803d901c500d040e51203903501441400100310a402513405556065803503904 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 256479820 1250 256478570 256478597
    0x120e1804060c110708150a0e12071109010e0a0c09061b02010c1406070f030603020108010b070f020d060518070f050d17030703021824030a06050405150a0e040f03 71
    0x1090a9060a0f0310a40d20500d84002148a00003811118107035540c5d074004400d4489404000a4800b0714409800b290300411141a034503c0d0714005010340341c49841080c01007000d00000c240d04000c00d0f40541d03119a1190100710400358280118980503000c3e00d07045160608103007024082d0055480320a526200302c000706c004590086d0a4500400d402580030544546072144c41a6103110459220380050844031643c070300c81d40240203280c10b036503058455084580c20810b042040d40c022032401d0310207000c554001005030f201d543c403901702c49015460101e03a03868884000ac002082d400500740b81d59100d12810440d050804084600f550000c545048aa00e654202050f80c12201e440003a101c1200005100c9000e80550040110f05500b881c0f0310300e0442c000041207902d001d001120407600010341c14900384001343c800107551140c00d44d00001800ca0310786000c41e08440040312030000d4404546d01d041c03000e180c07903030354900200300c0c540b11401d607450142e403000d00c1035000131401814004180550407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 256481070 1250 256479820 256479827
    0x10311040f29010f020c100909020309071a120112030507120903050115180b06270901080316030305070c0b04060f050702010b0d1106090d120e1804060c 67
    0xa81409201000c0c054114a115070040c00100d990311540d10b0b00c4258079114055001c1c510345103050303074150080d100c144144000d001d042c840d11000e05042000052010407000902e02c007942c05900500024808581440c01409034503410080c0b420844006000ac08800040c104245041d103003a680041e202c00e100d45402d8400e8000c0c01c000510ba0401c440c001e0542e00c2d8002c0044088a005a00920000303410b582c1503009200d44c2c0c020780350112022858846013001c1900171034100440900018900b0b80e01140ca64042c8e001c00a400ba0094030300c1c0b901c851245000b80055001d03050306006140740039803860811004019000c001001c0c1038440000816441c050b43e04400c255411642403005c900d413515040b002041602c1c0701025451615022581861052003815030464000d040d40b10b51003400e4565880c022154103282c5c0c0e1040d020803020300a61525101c440b0764074420300f00003aa45450380c0d4090070860040352003902604120b2084501c40700c05c1d090480e0080e40004001420808044088 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 256482320 1250 256481070 256481081
    0x160f08030d200f120c070b06010807200307020117061c290711121c06050d030302070203060c070807152405010f0512040305030705071203201201031104 67
    0x12102440103c3c003500301040010081c00d040c140d52a41e496207a50729200e8181c280500c1601030440c148840010b80c85500601802e90480c0c8a81098504040184042141d20315690744194181d007010a860045503040f0071840e06583d40f010883c071591038820089440b001540042c66070361201454074405001e1860101c0c020a1003000182d25031444402e95803566400581d5400000f031483c00c844024a04041014040081e04415592502515079002303121107484490000340305584540016296581c910081d0580340319880140e16516603004260601100070480f00021380c040103540e00107042e400840f44281c0d80075007180c0c40d10701c0044181005020034000d080210350002800e20200c091004084201d94090380c1e4428821200c500413151401111359100900028002080000340902d0144d0b500040031301c1c001e07052090540701c010405440b009190003199441c0304160040400c49522582050202c502500c1c1c0800060210300000c0c05210183c0342010402c0051420b69454110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 256483570 1250 256482320 256482371
    0x10e150f06010e1f020d0801240302030a14010e04020a0807180c050903010c0305041101030c1b170708042603070f0510020c030904320c0f040305160f08030d 69
    0x24190465518800179545020402c40000446e003104000581d205140c070321600d144200a8624081400302401540a50030141000915a44034480702d0780760400e07100700500070040210f138030a550034103005220341d00c920368004443d0358008000910180180c3da07034600c4034060840d00014a40c0100c28102c8040c02201035182c0c1c99421301c190500d42c0da034981c11441c0994002d105420000204000560455400c518403e0201d00c3c84e071001e080d4809003c1c210000140201501c0a0b05155040d0044039588000c10444409e080414240010700c048440400094030345509aa00200000c00e602e64130300460b40010120750401c1001020080c0a115400c2c0d40c4021500c10b544507050075403010303200d8001c0c100700c5008515042814505825001c1e101303050030000100e410304081113046490000d80d00908400321144104004003100400d200200011030195000c0c0c200710441d0f1000e880d8101d10b5610200f441c1c0c0c4045010300440d00d009c0b0456400701c08224002900b8008018080c2c0c1e118051003e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 256484820 1250 256483570 256483609
    0x2070b120a0b010e0d060207060207080301060c1101180b030a0b04110406021b2b05030a030e01051302152209050702060a09050a11030309030d02010e150f06010e 71
    0x1100d03100c00038855499070207003000c0300c0144034184021004540e00e01c02041c00c0c0d1343c040202010030002c1060390340200b00090144102619120b9692036000c8207130b00a83c00342d40092000415502444043c0300d507108100c0c002d18000c04260048101038003519214041d1203c41500040854144d900c40c3c1c0c400ad40c441c41c0640b0501c42130bc0101540300b960307000b62080c4009405044a205900071900010b0491f0700c600514040280081091042c0710998416500f0032241e89e580c4020040368081014041e0880030741d0380030401480180703a850035284080c0054079007800009010380141da0f00014a0607400c50901c445460b49809414008400225040c8001850110303c0c0860b4980f665044144600400d8084560f1925103c26610403070780028009051500844900d900054111100312650301c3d0090460b4106030f0f590000034102201d038864500903070340d150502c1046070814402d118508081c20019141450052000851f0400081c440384c104511003000000350ba681d1052850000c00300b10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 256486070 1250 256484820 256484827
    0x9060111060f0a0c030b0310150902031f06050a1e020a020d0503070b060604032006071a070318080702100203040b030907060305180c040f0e121806040609060f02070b 73
    0x5002d48500400c1da0605506420000700440c400d000c1c2c05007802ca810060f00030720a51060310f4213000240490701510000351503882000480d02100d002540c000c84400707240c681401c0303081d810f500d5210340035802601401414858070013415000745070301c1c2907011803450001604100301400c80c113082030f9600c0258406aa0512002800b60000181410700d21488116420751502c030304018442c0290711009201d5441106200c4140c00c402901c0f0303c01e664003410701410181c4039682c4917814242500c5402003806240c04021600f40c2c180903100c070b0f80e00541245401070034581c4840000d8425008060302840c2d01c041c040400a200704221070042504101e8151241406900d00c0e0f12103c40b803280800183c03c0c0008510002140a4542114000b4030010120450b03d0401c1c00003804500d8070b0025034a9807103450005101c001d019400d6060b000f40c1203070355500a01c5000c1c0b02e0884203840320034010a010712051003e2038019800b80140c40031418450b1001d84610300480c90131415030800941d240010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 256487320 1250 256486070 256486081
    0xd060515030f030307111603110307090605011d061b0601150e0a090e070803040902070b0f041a0c0f0a03050712110a1b0804140111070b090906011106 66
    0x1540014080c004482a0348440410982016a150440c00300342d0081d400820200303c0d10307401281d90482c6403005a0a56030b501c0789521032801d5604680d4429144005808510300300c520702482a02c2c00f40411003070400100741020300081134140320746c00f008a403c3d07a5100503841daa0343d46040c0c44141030a4000740000d020b03647d0381da070b07102d9000388101d421000100142d06c41c054001e00000300342d142c1c0548404201d500e4130f2185000740580f0580c40c2c1040c0100880820300d507c09100800280040d001c015a4443c06454030380c0d00b0010050072141d008800c201440005506100c022800c5c00a00314007504603151840c40c1801c500c26036048078884400018010161901a000340e4452941610740d44681415441c103603042c0d83d04140c2c28900241c007004107108850142800c030b44690044a84805e00b0b20b6640e0f920095a8420b420035221040401002021076034842c2c0165861101d03c2c02230b00c201860301d42c1b80c00f4180109800284a90034200018440364030407010f81c41482100c000720f800c9402d11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 256488570 1250 256487320 256487333
    0x1140a0504051003140a0911121b0603040203150402191203030b060705210405090c03011406040e0c07080c0303070801170d1710080f010f0c0807020c010305040c050d 73
    0x80c0c40b526010f00c50381e502900c103a500a02c5a8594110000f0010000f95101e26200c401805088802c072004452a40000c0b102d0311120040e0ba00c0c026a5002005c4000d5281416954042c9484074203200b143c0810070480182c4000c20400d040b91002c0030b290210392551f1002410304440c002c0d102e01c40f12003e55000611000d50600054101d009841c1041402c8490b0b040c00303c203200da8000a40117a20014110712245c110448200000910744681400c11791110001030b43c4004c26958080c40403804401400080c029400b520b08840d41140c420b07140c03a107000e503400c441a2000f0700c00c4003a244081410000c1c130034904100d4600340e10120599035249080c04000d801e1180c02e009280044050040c00b00081c000001c0202050106440b4040d01e071900180300f0b480240300a08000140d1044c6c0800221070204002ca83d6050300e501c070000c40c140c030550810f04200c8502801d2503040206000a10072000e801066040c0035041c00e2a0200d4940d8403400c0c000350300170f05035000b01d4001805011710014081c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 256489820 1250 256488570 256488577
    0x30403140d0c0f0923210c030d020c0a06080c0d14040312061a0705010209060316170c030a1d07081e070e0718120c05011808060a02070201140a05 64
    0x198941103051081002e048070003420b180655200c100700040e00d0b5905c60841d20711030100c40030045ca981d5840b000d4040345552458006c801002551202d9941c024601d41842141d41c1c1952500c01800452403640c0021034542403031040d1414420980049158000903804a400702d40c03114500b805070301c6001003114007080b82103d00b40c001030043d80c030750302d480d802c0360140301e084070f41d15100c42d4038840003180c5210507540410000c6490750f5082080040c80e440d400301442c030548144007400d10310000220081d21002842105240150200e410002c15844050a03a80c0160b00c2000c0090303030003907100c1485c200d84101040d900f098400c00c0c10004005000040d58a1071610850603440440180d003413999845c81280903602d0503400860005d003441c2d105501d80400d21210a41c0020210b507038440300d8104561609069901074500d00c0c00b44640d5030003c00c09284a5094030700004101d10b030450040d03c03848044c2a4004064000074460305680c861584c0e81e0340303244403040706a80c5103e0850041c01d56807 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 256491070 1250 256489820 256489841
    0x12011512030e0103060b0a110304050414071713030c02180a0605150702030c0103050c1b0703030f0c030e1203070b01181416080a020d020a0f020f0f12030403140d 71
    0x40c0019041c2c14154441e025010481d080010110304100105505403038032100c001c2001481d01c401d0100007032039501c034050344000200e140c0c041c0d1800c1c14207503402002510107001d2003181c040c00c0d40c1405044802e000071240d656806150130742c804012031002480e040070b425440001483c02c0d00501103001600c2c1d11140c201e0b00111515101008026410001401140030107035140d08402404101540aa08225030001080907018038203000c102c002d414903ca05d200700e80c0c480d80f00d440140101900004171940000260a06c40d105007110790340108900a80c086007030141c0c075503204420081c0070070400e807640b081c0e00204d06c46247d80c41d4143c0903e055002d80014100e1420400300b176a0a4900f416800d0103810560000c4907210303c1710f00140d80c0040b000e0301c3c0f21507540d030030428180702207010710103081e548aaa42d10340b06045256400245818400824a02c0700e42203501c80400080c00043c2c03041007109a60700305e0303480e540e642c1000e850f41d80e40750004200180b40024540340143c0d25510802800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 256492320 1250 256491070 256491077
    0x50714010614030c1e030703020a060c05060a0203090a111c0b0906010506030f0106050f0d0f0b090c090609090402120618070828020d0c091413030e1201151203 70
    0x32081d0004040c1d881c501d41c8003860b0865171000401c15006140d030b0724035008034006001ca501243c1d496022400c90a081c1c0c1c004000281c0251101003007003030030300c100ea400c40700100b406c2d0300f103080218196031541c11460004004400c500b0035510b5a4548074040010b0402d80c4914911044103070a00c2002e00108441d006807500800002180d5440c1039000e80c0e0084000441c0280680c0c00c100302540d85501c41d0b4402e02062006020318072003213a250240c0720000300038100120307000d0700550900031441000313089002580d0062081e141c540d01e1304406d40f114001c0880306506e407602c503400855803130f40c0303a0107504041e80101010400da410421300300c81954041c0000301d80ca150358a00503582c450000c15410b61407600c00e40c2000400040381003d07043d41e00d0000f45190001c1900d6034801c00c1a50455106509107520340c03d03a2405105032601d1241c0c00de110480281d440002550010300601071044043d200c1d080071081114020000d50140c54034000d990b04180c0360701e03168bc588502e1508c8612045000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 256493570 1250 256492320 256492349
    0x70c1e050a080102030403020a030f0e0402032503290105120f041a091903050d0e0f070f0b090103150305060a0209041d060a0c110111070b060102030f030609070507140106 75
    0x10b0070030502c00c49108540541c060b00c0c0e1801c0c00c0d9811984e4034030301100c2004002c4111420b42d21951144011801b0300150810100c520741160f10b001e80e44d0019002e00c400385440c00d14030440d04910070788902ca44040301520703c5417850040700140d61501928211026001d2031500b0400c03100312050b0039500445c0200000340307607001443e2040481003411105403006402a0064211012075a80142807a80c8207040044c100a0500c07045421101c11807804120b85d8880e000020f80310000744946009440c0f01c095030038060b0300700007400b009842054a15810155204011411201440c40200c01341d0790000c1504c60134241b240406010b500003441b41442580780c055484400710380e00e0702485403d100300001c3c1c81035594480c903410041c196a2030000910440c0c881c450303040c22081c4112010300341d1010040c0d80321025420301c00805000217010300d055500420034020b80c1820501a20b0703000740b0841c0c988900f030f03071480000c070780c58050504002c020300c0d41000c049041c1c030010340002007510a5013003813940 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 256494820 1250 256493570 256493579
    0x31d0c19030c030609060f090507180c020316050f1009020418020306040201141b0a0507091401030809011e11060603060c091314130b010b0a050f070c1e050a 69
    0x1080ea00511000b0301c1e101000c0403c00c00211a50054082c0300d0183c440081e220401e000170744141ca1120030216240c0d04900018050080d01000d44c080007091b19401700002c0140c4880039589200e54040b040d59441c450350b882d01000b004200369446840508291800380031402e905034080d00071030400300e00c61400e001074034078605080e00448250070780040c01070041d034440d80c0055034075540805040075a51070400040511700b0811300900102d05000c4020225024036081c964140402d83e00801100c5e0704041c1c02c41c402040c801a05415280c20684941e507804544006884003103d00c06032440003100d0f0803002d0511a0403400c0a0700d80d41070482a900c3c40d81ea544201034a6200c110340601c241c5109010700d04240c103100a00c60314005801c40e0000d4411b200040c9041c03050011982800d0800b00489214100b00c2c18140090060100340d204506046001401824074013070031048100310000411001e0078803803040902c4004002d40c0042406041048130302034498841801014014042c200c000038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 256496070 1250 256494820 256494859
    0x40615020c030a120804030e15180a050f10111009141c1b0503030112021e0604091a0411040609060c02060f0c1f0f18020907050a031d0c 60
    0x80b0b503522059003015213010050a0342c2c40c41015100350b003040310070740400c41e540d224144442d103000103214200e0f40382c0300050305084070440c8a82c480303400f58249140400141d1100c450443d1301440c229041300c410703800710b2001c131410549206040d11074818007034051035500c02c0383d000f1382106010f003403e00340c40070b1180301c2d480d501c01c104400071000030b550611070003159105100d80d81c0f1030720f07079040c880040f00c00c135031680c0345150005c0e001460f148040d4191a0118903042040b1041491010304c10700b01ea805450000b0181d002d0361040c08800781e1140f4443c043d000d408000240480710040c01084051341c1440d443d030311074001340128000b143c0c0c071102c007090b110b010b44044102e00f58020300c600d12b0b003210030410350b080d900034a00700c06e0b01d4816171880020506560303081c4c0041190310000051010b005000c008280c59040301c0d803c2208030048c2c0201d0158031000e803101e502c4002070a009031f4802e03090034218000c00294103403500e51450580503810305e40e0046035410b9101c500300d0b4401c0344140c1091005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 256497320 1250 256496070 256496083
    0x3032a0506010612020903060c0d200a0e01030623120c2206180902040f020301081905120a0914151207020109021206190b0d02011d040615020c03 64
    0x1800301d40c4003500400505100701e10107a22035494034005402d110000021a1038400d06031114048842d01042c0ad5800c00c0161143c83d011084503d80300c81084900c1e4034405440c8901d400d200100002c00540c0c0300f03585d0007a00110000e100c0c0d1840c07024145c0c1028216115051041e42c0503200780075455090f21910b0700080e6481400700d00130034041a0b0714003108880f000d0702c01c100d440107260761110000140b4410001c3c801c03030064000840440d0821052040000f19049502814001413043c00148403000300000c2544042d803445048924628090800c1032810000000301c4143d40400240d454030030303500c42140e408507041a1800c07107108046200300241c007251602c0000546100b40803428050341015049038100c038141c000001c14082640104100c1032030409034224541c081814403040500d900010140420307006800c2001d01442e000184100100c441c000e03040001c02c18a070348201207500545030344403034002e008001c80c40d0343c0c440c019641a030042c660001343c0030707041e4041c1c0d1900303002c10300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 256498570 1250 256497320 256497323
    0xd12020c0a0609120611130f0e0408070f260903060a110f07081309020414102c120106061404061e03150602010e07050406180506010212030103032a 65
    0xc0350708070303070616582090901c4222400c5d1115a1142d8160b04100b00f800c008100c000b414031992507213282005544070b440307016a88840b01341c00610b410003001c00c1048081d100d200364070090241d170420990400016503441d10b8410b500c903002510042185910308801000008819002c0c0e6072691303100a8250121070307400c04600c505840c100400003a5100d401c00901000e03203d00e003c00c0c01c10444541e4030058100a4016400311036001800740411b0f0729034500608805001c480c0b1400b00c82d008900108200307000f44044d001d10040c0b1800f1111840c9003007030001212406010b00101100c07031706085002e8202d900c500310114030103049420201911900321025152180c50f100002d2131030114080304080404012410580d591400c84800440c0440d0755008022650020940074400c03005a1304022185d800144100d1514504110060200351107140081c412100007405075035002c0140d007000c44242d40100001030020020080540180118440300c00e0b00004108003003038952501d000c800032810 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 256499820 1250 256498570 256498577
    0x301050c0310081f151a04170327060c01020315101b020118080609070303030507230309070509040b0f0708131202030f04090b090601090b04060c020a050d12020c0a06 73
    0x40240031244e894004140621801c0325034446a5614285030803211032003000e200d1509800035042180500c2d01c44004010940c0c000650302c4c0040e8000c00070415104000343c00302409001d4805035241c0ea0b042e06a54000040100a41d92858041040401d2000d100d6041d031089078024005081c00e8030601d580e10381c2c130101c549051b056004540040d509101200c004899902201e072010403203034801c3c040140215440d00040c0030b940d0861501a00341e44004220f40c082000704d0920340d815020b0410340250044601c250b09a4a456801805040140c00c6d0000340d0000008002d000401c9100450a131007815800c0d503440c0c007a191004220350305202070711000740320004c084003a00800d403004c1d001905040c0600427a45084001041400386420592150742c3c0c95658a1240d10607040064038954400402d2800240090074038803502218001c078010720040103c019000b40071034954242070f101401004041d42c2c0d00c000c40e0702d41181c840d2401071202005004145030105070381400f0582d60160b0381c8988 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 256501070 1250 256499820 256499863
    0x30305030f0910060915150c0212070b0703110d0314010e0711061905160206010b0a03090219080d0801030b0612010f05010e01030c171005060f0301050c031008 70
    0x2108007081c4100a84071507981c2c090740c00c40a2141056128200041540c240e000c90039a2280850750000f800d0355201c69003030500c85c45120354103036000764115000341d41260352111035203541109a14041954101311061000060070300c00f4541c018913102c1900c40040c003150b0030308544a0085058444000d45021101c24031070051001051503040141d0102d110b241002050a81c869039519208060b506032601c0c400710300d1100c40c140301e180030b9203901030600001c1a42c0740304080c10080d0346500501c030f01c428151020664606a030710a0304502c6a1940081121000d090707a516554003081e003d204002051141c9146102501e0081001d68100c03500546414040d554150500550b451404c01c000c00d29580d58800007002050784c89850301802c000304480d80298118940702d00d2003040391304074045405500507002100500020740703a5901080740c901280544501c00451100c036184502c0303030b503d542000d040100300a600005075104207084d4241c40400c507a114185525071001300c00d410480c80055 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 256502320 1250 256501070 256501081
    0x1060b07080a02010e06040602030a06080c030a02010509180901020a080f150103050c0904060b070c0506030c04060f0e0d0b2a09060f090603040b06010e010504240201020d06060203130f03030503 85
    0x1074007a00194015000124140f0801c040c0c542c18908111b504450042d8044280803040030148649000740c5200001000720686060000343d44c0c4040700c400030304002d80040d0142d200d45a042c10319403166a00c50a665450402c2035402e0f001c3c1d08144411000140b0100c00034011007102d04005000c1c60280c0c0c9220350980c120401100905002484001c65082c200018841500c1d148900340003084485200c684071140c900e001000711840758032040c401d000500901c000c0031261811142101c2d0326040038408d0206420301a00e40800c500d21459000e00d490b02c008050189105090f0f204a4241d5200525056405d2440d401c3c0c01d0080401c0d440704005004012207070800500410300b5451108100741484150f0001480c654012601183c401c25070f02c2c01d100e4696080b8110044400c030900304181440d042104003010150b4031509144610340c0e5842c1946c0860007036044500041e403c03101402020b4541801940e62350018481000c50200c0c00000030306080c08419040540c1da25070340f040d00c4c47c2c895 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 256503570 1250 256502320 256502333
    0xf070524131103071410020d080c090a03060f0e0d050408100f060305011b090b0f19030e0304080a02090906071407110d0c0617040209011503090209010608160201060b07 74
    0x301d240403100c032881200b41002e2558204107900040ca40d142400b89560000c0d000c1c0404031407110506401d55029840041920350000c0205600c000d04040705510b60b0b5440c40018031581080d40003400c040d1401c4690f1180004a401c00c1400f401d135203003101c004143d80c4030210794920440c40703a06110340220450b41401c503440c1e040040000c400340f03c042400c90312619440e08440c2c480d080300310190340c1580741480b2035030000c0e008001800c80f100c4050406000d00042c0e0068482c01164000002d04d01051035006c5000354429000100302508484e1104c2d100c10031655940780241c802c5e03101c3c0134444006a19014001207040c819103041da68014404024511818541c0000404030340303800d2100100d5082741c46112000c2c90090040d441c4c01c3c00c462130120041d000805c48508800307400080d00401c4096111a01000d0440d44030201c404c0e40340b80304e214200c000301a0000025803000c14600000b50700359000a05e0f0780a030103180c501810758200b112080e404c84a946c42a840c06003001e10091010500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 256504820 1250 256503570 256503601
    0xe070b0f0c01140c0a020d09050604120501090b0c0c070b09030c04050601020a0515060103051f0e1f0308030414030c070b070c180e0118170705120f070524 68
    0x50280011032092004441225070303600481301691620300100c0c070035440a60400c0b42c40560502c60400030780d041d0500c00403906a1150340160720030402c1601d902020031909601040f0b40980191000d041c9041c50020405150b200400f92481803207803490100e40c15a46004a13074440c000200100003c00098060002502c0c0003401c00d410350280b440a40f0120390240030071803000b20100c0c80801c103860204005402c5a6004d0311a1030030407145c04c104585c040a841242c000da52130181c011500743e590101d08502c00d40c0c13500f4000304106e4035103000810442d8070350145000d603109039238200c49030302c000d44404c0c0d4038050144520300d25030101104010400940c80200012400390641940b40760f190101d402210a180300005113142e680ca4001146160a00c5100000080385083c60440e62498440c031140181c203404030724015070001500780821808001046020b845150303c2c50312821441c107440581c1d008070400360f03164091030900e6400c54501500030550f80000000140e4207403500d8845200001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 256506070 1250 256504820 256504837
    0x110106141f0c05120301030201021b030a03030b040b060703020102031e0405061504090b040b04021216051210060806011d0708072f03041d010e070c08040b030403120e070b0f 76
    0x1140800102c00300b0400d001c070000c4144410300842d42e0354514400286442d8840c41c41101e403403e2110315000540e8042014401c883c0c00d4130300426030402003400100148032a40c85540d00040010710390301016019005184141d03a2440d510303000c140c1380405601c105a040b20020400e802c40c0b80081d102602c03070812080c100001400004942107142e465100301402544c050b5588803801d0104000c500e070040360115684403d4014004403980c22440c011900e00c2c500178240300322162565044400410030110504280000301401400c0c1c3d0f64003055110a800c1c040c4010340084c00744d0080c064506e58140f01c0c003a0300703141c0e00c500e440d548a55048604441c1c2146240d1910000c1040540314260401d24105901628004d035980360b20385804402c5a2508030303911104003985070300400205001031900d56128500f0b00b4410003c4000b4a8055640c0c482c541000038042c101009100c18540c0c4000d01071010640c00c2c1c3d0030024031502c5180d06944582c18820016064420014200082c0501000e010304a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 256507320 1250 256506070 256506077
    0x10804030c081605010c0f0815010219080a091d01030807210801140a0e01062609030d0c020c030607030f0207020a08030a0f0807020316030e090403110106141f 70
    0x1200690311000198004000d64008201422626062004c284100c1d540721880d4101300301c00005520002d085190000c00b102001d840c110002000c5900034051203006041c2900032202d070030101d107400e240d643c10a50700c110000300740301e10200f2001c140c502c0c000590300752004019507517883e658458103a41d1202c4c604940742d0086640064100c005100c02914215940c0c4640e03807950b06140703001d2441da03000080948214000301c8200041600c200c0307400c0c1520042c1c81d00381c010100c8010101d03d41ca0000380018200d42e80c120810003a1400440682034403040c4500070f20241c2c4076600c04a03940d03079804401c0380c0d068001001148585002c0d0780411408051010090705100842e000554140c50940c48035840380c1000421590041e448071501c11002610b0914140c9410050402540c5e07000346030306140c03c3d50140003210305044c0100f000c0000700340000d201035190314203850010203840803142100c90941c04c1a00100e11040c1d686180003c8810107010301d58032501c0180f1000070100d0030407000301031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 256508570 1250 256507320 256507337
    0x81306150312020607080606072d140f071d1920030a0b04060f090e070e0403020312010e01120320060c1309050403050d02030a0b211b030c01080403 65
    0x1d240391601c8041d4600b940180005240030f0002030310a060013085a4410f03441005a180094840c407140c400002c20b03d2061034602c2000b0394400f24011000c00c0190009001d191201c5d000c000001c0d64920342442c08080d180c0042e540d10700c1c400d00740306070301e503070a038a0813682c1c0001c2c0d2001801e101c841e0310070146d400114541801404940000c29801a00d50041c0000800c01840d40c0250140010b1a0815035041000d01e262050603582c000d2a4021341c0741054840c0711300b10030380804020000280207d030509a1306810545800b83d41e82e03000c8007400c10681804800000d41c041c400d0741c46812101c1800c0003d0b51b100459034211800030149410800480380e110244460030b008008107441540251504c954400c080c1c2504240d503031041d800360030300700d0900d4100000254003000781d501c0c41a152401589036100c5070702c1030010341501007203682c10241400010441000800c040c158080610041e41c2c0c0f07942c2d1441c00702d02c000d420205115010b6009001070030107544680181c41c1c0c0640a4503010700c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 256509820 1250 256508570 256508573
    0x9270618120f0806031603170405091009140601140f0d050f090f060415020f070501050f07030e06101e090903020c0406050405151905041107120813061503 68
    0x202064505a00002030350b54541c840a00c2c1e000361034a600200c080b0020024001c103205480c00c25521030000a02182981e02000191a0b19905607805414001c003605250b2030041c50381080b040ca6480b0b056260b50825004a141403000e16425001d80810b139500b031b40d03010b19900c040105901039205565514010010711070707040302c00c0c030074140140d1082c0e122803103d0070000d050602d0020f489140c200300b5000a810f020010750340300e0070100c0b10303a074903800541c903042c002000511501072520007408a508000801000c1e0404c8031030203108421588041040910307000741981e441c401146c00c1c1c072481c2d910900501c0f1000d0255490509050681c961000b0a500ea00d10030040d1030003050210090f03844070196100e680350a005050103000240d80400c65481c0141ea800382c0c5010210440303025607022080b541202e9100c42c1d2090142c01c0c0034005015a20203030359459160f6000c901f0640750000202d8500c0c031281d1083c903406020300190008a4001b22142c0c8031440184840e403210000c2c4500085d0000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 256511070 1250 256509820 256509833
    0x30b160212071a54010b030c01090608010911040806090a03091208091203040f081609020a120c02120f1b0316120309121e020304150302090f0a0b0409270618 69
    0x840484c1e03294004a01000d203002414982618420580e06101440078148071003075001030110b044508218001c142c140c94100d514546204039002030b0901d00030181000740640c070018061200ca03100303a455502695995540420100640000901410342000065018a03200d940d050010b10040d054924242da40c00c0144440e240759407007261607411445503660f044000c03070440002030804080541c82c180605900600c10440c2402c81382c040c80c2da46000020243c820020740c1d4451545a1819503600f007440003194443c0c008600003825640400b00d02200e5100100c143d888000f203640940d11a00400e544004400c0c081584030402c25036500d181c24040b07541000b100000c0c007590380314101105850750402d129120046840c60a641c01008100542200e10613481150311040ca40161034112250010f50007160098840340e201d190541e0109503646004001c0c4201c48641404001c2140344030881c0c0000d4403500031101c402c010311070360f480200c3c3d600d81000818001e104418801303030143d562542c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 256512320 1250 256511070 256511221
    0x90301140108010509010501031a1315061a0408030a0503090f030301170c0f0102060105060d0615020309180c040b0304030309060f2004030b160212071a 67
    0x541180d498001080001c00c01e2190a81007031500009022960450701d032001030821001015940c242c42400048a4140c080c07000b10700e0b150300890001140f6002c1c261200501440d010700c4070069070480c048800d0720107000c110340854503203501840c20849031100544403508010280141c600422104102d80c1809100450281c05a4505124411507102c50f00e4600100b842030107000c2e211041c040040c0da80c00003003050468108480e0180c0e1030180d00c0c0b010001e000f0b5940030145461032484100007040d00800604400c01d0300387c07100c0c800e0460341002d4000c018401e4510090382c4404120a0018042d20300095500034080e007000305407140240d40710000c8413140400c002d860744d0384070440e46095500180001848009000701c80c207003402c544505000d031038041c0c03000d03e010641945081c4210700074000d884c03801c400c1000c11629100a4246452101007071140d000b00b212610b00065a00c0007040d08443c0014100e4903106640001400303004404480c40454058059084024103050103920406 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 256513570 1250 256512320 256512341
    0x50c15040c0e0a150e09010902030a0c060314130f0314030f0108010b060702010210090201030e030304030c11060313030305060114180405010504050c161e08120105010302040810050c090301 83
    0x6208551820324003950310348010f420086a1810155142c1c0d4007408505907000751001c1d80d0b021025601d07280030a60040c031801c0c02c006e4040c05400f015100740304070034001c142200c03503c0d1001d000e84460100c2c16400348400f20b0701030000d80030101e01840850b001e003422041080c800c3c208142300740001c12407040c668000b182d007504c402000c0401440030050a00903445c60001c290b41460a01303c55a0020752100002c441c840c014a03070300e00c2000c06581c170980040703210350b80030030950303603a4181820300034004010310109642d43c40b08584040c0050804038200c903c00d01001b60718010450403030b43c08801500003d041c06040002c0d000364290400391040040035500c40d03000107a629043d031a41440190b84c0160702403445903142104100c112404401201c0c110308014000a00309202460700900019801c422501514202d2880a0401c191400246400c40b003540c261151aa685c40c011000c0c0c0c8070314000c0b40d581c0c0d004a03030b080031082d415400103604a00180c005030300b403c01102c00b0030308441d1328040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 256514820 1250 256513570 256513583
    0x1030b072a0201020d110718090b0c0a0323010501120b040203090c0a0902030c0306210a060207021212040611010b04020a18060c02090402090402030c04050906060a060c12050c1504 79
    0x610070708560b01042010420382150601c1031400501c140b0464941e502d51040804a460203400b001c110380341944000e98050340503400200740e007003803c10b00b0b40303541005800c40c0109290884008009048000d07480c200d860a02c4003e40a81c02c100c01151100411400c00f25081d440d40302030641c0f551070340059480b4a4800004202165a04c1c0405c841044a6807082d03c50f1841007003030011080d000b60403a544980241c0d0002014444000c09889201c1c0804444030035001d99202a81044580d4008010290080f1111410001c0065829442e40c0f0305034107a5000b618100b0040100300d01035402c80c000001c1c1c1200005083c41d1a0000c02c05907403101c58020001411003c052441000f50f0310200c01500702c03071030b10102c14441075010420900303002d40302a2103900c0300c8000404641c1c040081c20310721080988244041c2c100840303401e544920948800344196a05080450718a224188408403650003402e40034005070170380e4056800750300c54060344020380244c6620400302c1207915240c0b030140e4030505 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 256516070 1250 256514820 256514897
    0x90b09070e01050d0606120c09080a1403040e0a020409140f0a200d0504061d0c09101805071b031209020105040b04030b160e06031b0408240f04020901030b07 69
    0x10221080b9108c404440091002d01c010501034500002490410240e000101d880a190300344017240c0b85004030f41c003904030b020458042080d441c04903000740c421200c50f02d00c03c1c01407031a0f10207001110201200d80070804141c0030b00041082c203039034208001e280ea00303c1c181744c80c910007030409500c1540a800354000080e140c0003400f0401a60344540b805101155886c0450590f0110b1029120300d49102818480c01d409000300301414030300c0030800018100601c119440800c8100018007800084480f170012540300307040103070202c0c10340c4c17000d1188560541d43e0b80c150040c40d01c09100180702138541641017110900000c50005103001c000c0c000ba50040c1106480e52805e800b042d101c0040d0010b99100300002060014820b8a8002c1074a402030781c0303c07902014102c20780a600040c0d0043da0b0113008030384900c0501c004030381480d10070607201000108000c203080e078583d80e4043c0245416280203412a440070010004606c160110582002e0305260801c0013200a1241708148008034020282500619 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 256517320 1250 256516070 256516097
    0x90d020f060d0e0a020913020d030c1b030311010501060203040b04090e010209120a0c0617010b090d080a0f020712050c09092401051c110402090102030f0a0e0a090b09070e01050d0606 80
    0x1b051960b00200705400010040c4541d4041414010303086401030a01000c203003420304011540d4503c000203041c02e820801c00c1c0741d40741001403503404a071101607401d520300301c00450071a1000c02102c054441e82c00740d003490980780512601c01080764140031031003035609000700039996649091054400c0e0800380145260051400c0565040c145944100140003400d03051007803040d0000b400c1411511075117071440c0c0310316800707010914040c00d91100400c0030303000140d4a20515007002c02440c0f044030503800c450940d07482e9000001c1d4000c0d0540064202da0140032035507054500700340540d512010103000da80d03420079a90503480944100741c0003210007112090041c800c90400c07604868411920420501d5a02055100e80e0411025070140501541d0000750101e5241d0080086514208490301090b665640d0440003c180340c44561146104a02c8a0000590301d4014040d60701c0944000f082003526031920401902c0c0c20141c5c41060381481001d00824500d0f140921031031000700780039101c18200a207203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 256518570 1250 256517320 256517329
    0x80708040311120303040f020d1109091f0501031109070903080c03090f030a150c1115010603050112080a03090614040c1e0812090301060e090a17090d020f060d0e0a02 73
    0x15044803c0c15134418002c110102d50b625014018064041c2c031000421000790130240380c840d844502840e0010000d40c284892400c00240307545040310905650400da100020344507050321400e2002410070010403a04421074500300d40d2442d080350860420f504042d03500e6a13410102c0c0c0000f541207003075400c01b090441c0c90341020118245261400c80c0071344100d43c400d0350f808011003016106d070000e16984225400c50135004010b004589003542045800d40602d20455042d00c40d401d020380c0300003900f040b0000131030805c0245201c0302a84d11029403418444010411002002100300c1034581c42d03151140d568007210f0001e4020301860003000c5002c811414452140f501e92101d24084c0c60301103812404100d83c0301c01040203442c400c139401070b15948281c1d07034000030301401083d001409c22040407010701041c02070003c4c06040c154030800c1506041c2800c030700c079602c031402080e014581055000c64003000624100c215104d4100c0028003e50a0044415102c012240803a100300c400d644061100c2c002e5160 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 256519820 1250 256518570 256518589
    0xe2806061d06070f03020f011812050703020706030507180806070f260615040e040c0b040303050405060a12180c08160e09010609181b050319080708040311 68
    0xc0032108900012500880c16a01c5841c3d4003416140c0d800760760408141c07090104000510121000f4440400000d801200780a55000d003121302603464802c2c0c56515009000f62294250580c019080e01407030484e054016040050000f41040320500486100c500841c2c00800a424007070300900701850700000141a44103107550050522601c045440d10108004550400304c05405c80c41088075251440403807030010100044100c3d6040c0800c0104204200c640f030140705034042d000290803103a5a48520640e840341d4000500094401c01092145013803240003006890b40b2890040c0c80c1c403c0384076950084407410403040344842c6105442e1000e02400d0114000035100364009040001e0300704860000503121840ba054003940e0001c001070700b4a8081d40072100910b02c4032002d102507003141407001c065101b641303c100d85a13841108500c50005a8003420025075801070010012001000140f00300700450b9807003140d40050400403500090180c00181009511440c1010030bc07014030010445210ac = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 256521070 1250 256519820 256519847
    0x61b0c030a0c0501031e0e030901020d050c0d0f0e13021e040b0301030611040b0705070306110702012a0503040f0609050102030a0e01031104050303280e01090e280606 73
    0x24000c04070380c0e0104840140d0203007220024240041c44030440d00000e100220300101070741c195442d203c2a800c0100c0040020001c0180036800d55030007202c800001d40d454001d181128130300e0b03444000a0100b0b0760040c01a03212440042c2800c5003996900340c0040c1c9600008012426942d0700401d4501d54100202c00011403403038488411404c081c14601c00405034001448040c01070390700e031500152f2080c10b440480d0050070404402e03965030350060400325030300c489030f01c4111703051458114005282003021080d16112903050303407902094207450108550316140204800d00c0c40481140900000f1030800061000389041c170340580c0d4080c41d206c3e01502c00c1c28a81d00032030554208003c118501c0d944113501c1e6034403c00c242000140e08985035152426801180c014030b40510001400903001c41488800105c54003032105003070103003080984201d0b40700c90a03401c035602040b8000742c00d008040322090000c5c1c4c8201e0007810001e82c08020000c4444001591409011180d5200010f00100c0e51010001c0440b5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 256522320 1250 256521070 256521073
    0x40302150601050a080f0711120c16031a070210020414030705010f0212161a0a15080705060f070b010f180b152124040912110a02061b0c03 61
    0x1302010103490f4400040c503001d0285085400500e06030b004000c1c1103c030a91500c11502940c40c481c8078a0f01c1035200a1041504d442441403421b010713003440e1088015203030301001400b03a01c0e0605c01101004500502440b042d409014000c8548214900c007510040c0f503c8080c0d601000445418541050b0481c5c002d1810441d000c104881d1032900001c40c00d82c0c1d0207500030305642c2e800016880d1200309a046000070300d04a122450b104072902800001d074025100d50808003ca41c5100c0d9811140b00c2c0144544002500414002c0007646000b001421040c05ca415145161014545d81d50852442c243c019003102c1005040c20700c08260302981956410b402c601003013011801c0c0800284440c1c40b610306004403480001406195580c0c0850120030008a203042c031b1a80342002103d50420300d1003408146001c0440c0840b415440c903040c05040300041e0042c01000b2010148141280c41c80404541d4050500c502d82082340183c840c00c0c0200090804003e280001220f40c0c50310504041040780d156209 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 256523570 1250 256522320 256522327
    0x90204060506090a121e1a0a141603020c010f1b0207030506060d0201020f0f030a0e06071505040f0804062a03090e1e1003020117041505130b04030215060105 69
    0x141c0355407003441c055800c02c050260a6a13994a40711981c1c1b180e0451980d101a802e528102c1041440b807070303024030301d100800d10f100d4558600649001700ca09003034408401d6140000464070b150a4403c0d1240141c0e29031070058030786002302000c0b9003074684603000605030310ba80c0c0070700401441851142104200142c8068840b081c51907c405070707518130180640784650f8400d642c503000c41e0f008200c00b25004296100303440340ba4100f081941d4507500462038000200790f40e0100c0f1041072030410121a50207134400030703100b640c903881c2d0b480038001c000040c421150010140c012401143c10000900014a119583d00116080703c00340d40320700f40e4803a10322526880d01508c00600081d0400303200c0042d10716900c01d00ca1255a098400c000c00380c45080b00e0b00c016120501030080e000480c40c600c0c01901d000f0b0701c4400d0758400180d803a8400c1481120080c1800b06c001c1c0f25802d082c1c00c00d070010760b013000540780750100c8200f05880f50641c9a5060b80d084015920920304680640000c02d05c440d4850002d003030403400c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 256524820 1250 256523570 256523587
    0xe010f06030b12190b130305030f04030c0506040b190501320a0b1e1201230612090c01020606010c0305130305150403030609020a14070303060b030a090204060506 71
    0x16a6814062201415160107500681d6140c940d0041095222403086410303500050302c0156903c245200192240c035950070000d00d0f4041a501d06407207143d0301d035036150720b0769070b40e0f100c2041d07141c20251040f000c201c0b0102134800800c8041000c540514010004c142c828200145800c4482c050301591041302c90501c001045030414000040503a00f5500d0040c00c03101080f100091040b034504400170303510081012001c035100c40e08202038583d94240304913207003007284500390350031a600070a13110f880c4d400210340060100c000007081d14881141012985219000040005000782e045640c04d2809015440c0401540b0201000408005007003030024160904200c0d00007031400702502d01c0a81071000c000b036204011905100c003100119048010368904140c184a501c143c06000d0794107600003070901402090548041c421100d8100c4141c650450b0040441c100d4151a040400280c09140c0c0e07654000a0a2130150f004520801041c0c800117000000c500c10001210450381000d80115014000c441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 256526070 1250 256524820 256524839
    0xb040210680312030402010c150203010f051806030a0210091d07030f11090f0d0f03020105040c0e010b042c0709081504080306040e03040312120e06040b0c0c0f01140604060e01 77
    0xd03017043d0203103099400e50100307003132601d00701c129526800388072407002000280e1b0810000d402001c1d140b0845202c841915008150f02e1001c0080c0d8105a15801403d0741900626041030b15121134082030910b11031059440d01d03031103401c2c5400e01181c000f0f4041740d810080855810b201c0d4203412051a50104510484044030320300b94026450414000e01c6045ea0091042c0d5800841c010125400104104054480e00d0000e02a040075541200d465404040100e5006c42c40f9204078140c405035010541800e00c0d02c5680800103000c0504e0003582c0c1c4510380584101400340e82c0da6031080300c1d48d03110ba000482c45c01a2480c138243c440108000308845d66010f10000650381c1c070490742c000100f194041a0000110860340c1075100d2980014000c4020007824216241c010020072000c01d0f50800c10450300d91241800d07074560400b1a4002c240300c8200c00000d1054030340034090942051048201c1d00c00c2c1209031110b80c21500a43c208280c052035180420203a4034040c0543c1c07000d072007408011203103540351a0a19 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 256527320 1250 256526070 256526077
    0x1b0b06120f101e02030103050703020f030714010e13090f0219050105040b0f0c07060903051006030803270f010603050607030c020a0303050912070b040210680312 71
    0x508600d43c44030120000c40300340307031071101c1c00c103c2a001c115070b03035656407410360341d100c0c12840304038002d141c20040181d4600c0e0100d00042124049841c1030103400c21000110348020802c0380d11035118001d000d0520400059100e24001c8610480541031011361034010485d400c0b03e2003040300c0450b040c81006020340c0c2d0340102540d046604d41e03030741643c496107039840c080c5a50190b0402d00ca0701c5d101e1640001070040d032101140045070b000e0802c2d120740c0e01d0000c44400a0718001d00000c2e11214040011401100304080c54415421841c40d10300c00e80c0c2d1420f0305203400c0a42c16100004269110f81c41401400000d111a41c0c0044807030400b00450992060040e41780c00145101900f855a5480040e04e49d10042c44443c1f044000d0f0100310b503a0702e178140f0302034a03a0042500c1c181e0189003616075000c6841e0086d406140e019502a0a004c101c8000c0180c08240c00001c1410048881070b1000c0d581c1d515003034006a80c140121109524000c044140007040039107002441d041c402d504c5914100ca81100e00e1045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 256528570 1250 256527320 256527343
    0x10061406030603031b0304060315050d02060711061b0c03010c09060f11011104060e04140c070305090607111206060a0314010b030706020714040905030301060c031b0b06120f 76
    0x20744035518200001d0550080c0301580131503c80e81102c0d904100307804001042580c9094804000c15100302c0c00640740f111060041c9508400030802c08809894001c01a052980c415105c0c03402907083c2c0c00110b0910742103d80f07588600358a11825001200c030502c404100c000301903008026400034904002d001c140e0521503d018000384100d00207046100342d01c07034042d01c8521402480102c08048181000740c0c014828000060000e40741d103c25071800b4090580807085041c4100e038207440301440040740d40e008440445c1448820840300006032200c0c0044c02d185405661410941940300003030105080d0b90322039200c02908400e08000090b03407281080b2064030b80022010860310000240c250062a10000c956810300c141e400018985130300291304001d0f035440302c00c00d5070409504010b006c140d03044814024902e80043c001408518425500c1e0700303115000c0c0c41c001c1c1d02c130301a4551180d451811940240c840c0c0c0c0d10f26041181c14207210010301208000c1c0c0006046143c40841c115465000d103418 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 256529820 1250 256528570 256528579
    0x2c1507080c0d09030c12020f07060e0607020d080702090106050f0f1608030f07020d0504080c0603100b0408060907060c030206040b07091802040f05030d0906081b0f0a02100614 77
    0x104064040e201c00703542e15030b00300c0c00c4200082243c1c1d042c064017002070302c58100c4004240c1400b07001e80703e1001c0780f015900d40010005000550911105440b400044040c903900a8010b12801c2c001d030780d601034804840c5000f0b03403109985601c503005100420700141c00003824060100714902041255100302d4040e01402e808094990840020404d540d00c00c421000d0100350020060160018a43c1c0040d4015200703070b008c07aa6030007e9803030140c803907001e6481081c105802c21071800c0924207012000710b521102071403a0514041c1c031207010281c2600550060740071a0b1040302040401c1c6001c00c2031002070042030401d025000c1c5241d070000d503203100c0104014a901050302c086090380b801008008090a010480c0c40381c43c2143c502ca010003900075104034044821003000008545c00c0c0490440c6580065030340d800c0180d4105401076421034030160a0703038840c9945940c0421400b20002c0070301402d500c000350003a9180600c100003894440c00d0341c81075215910302201080700482c06c188503031600e50b0564 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 256531070 1250 256529820 256529837
    0x110f070203070e0a1508010b010903030c060209040e03070c0e191812031a06090d2d0c030209100f1205150103050d02120f030106120f2c1507 62
    0x40070a0902500e83c1c00008181e4240381400498005a0001143e4182c004060304050740d503030788814261a807a01d241e50200e00800c0051010a203d074411815560040c00c02510302101080442c0c11034200c104080129003010400c4810400c0b141c444800078601c2924010301801e00315a03500e03039001d98820740d40b2203d907902c0c4020345041c3d040c201400859004070300140c0001c048000030740540010b104004c0800b02411500781d441c54038100b80c95020700080c01450040f101962008d460314000711242c2e824201141c0c03005040021100c6080889204040c0304031030340c0c514410700c44400b41c0580322100c1a40040e80a2040e0b441c440c0004089070100c81d883e5180c186603080c403034181b1584080b07803001c0034480b80010060000014000308042e0150b400c45059010421715500940261401090070440401c010000c240c801e100340b900c03c030174400d00060074115070002401250540070f0101c03650900b4408600100047c03103090b001c0340a8a0b000f0304101c01040040000c5400000c6c031410601c205034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 256532320 1250 256531070 256531073
    0x70203030a0f09021908070918140a05071e09200f090405100602240a1d0d120b0415090c0e27221211070f05040e01110f07 54
    0x1600f081d2040764001d0036245d88804061040c10080250b4020710314a489410f030002141d004a224080d42c607040c4205081c4090580e5681802c254542104000303148104600800410018004280142000c0e10241e0401e15429042e1003d00d203d0350003640755524211204441d0344028403000582c89860750001c0c1e0315003070310070080054007840c040c5a4001e4600020011520000401141a10003680885009908180c2005c02564050417640c030107401c0740011843d5551141c00400051544002d1429a802c01c9c240140c5410203400e8450000382c405021440024080c1c443d4400c2051f0580b03084c0003130707400e0950105a141e00c600c201090300e56504034070f000e400c1c40751a406d00d41000040807204032610849400e08004240384070403e0800001c8046070a4021319207010034171002c840c250307200303103071250300d1b44c1005001d0408200d0034400034000e5501440f1090113503a002e0038400c04281c4040f42000244012912808404a083d81c544220203801042190540c0c0701d0a6184202c10750347c1109 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 256533570 1250 256532320 256532351
    0x11160602062a0703050408010513080714010f0504030f0815180a020f040303020a0501050c1204020f12010c031508030a2021120f04110d03090806040b100905070203030a 74
    0x244402d4440c00400400d4880800d54020000c2c4100d0b181d0b04000d01c115110a101c01c0004441d000c0b008100e2041000b00b4000940c420b0a1561145400340000510036a0342c0d03800e00a8071000c603021000201c140e0703048103580341c200602581180c100e42e800c25440c40100f0205d8815405c0d84060298030307102e0750000c1c4049402d50111252741c103206103000d880743c5c1d882c40c000e9550070090b09d085403030354241000544d01e0f00c0d0f90004d903911100586242065502c9a4081c8003440d0035503c7d0191b00300100040c1400d0900090107a240d40a009503000150b80c002d1902c001c071100403a41201009070001c1000c00d0341141c1c0b103021200080300550300c50200400300e00c01207140c110b20220240410101c048a00403581e18000503100c00300825100101940d55003035458031011045400800154891031500340c141010881e000714240300341481c080c0f05071545075040ca01442120100d42600c1c014042085400e07040f41d201c00200610a42030006050141002e926800003c106219042c2d6070450300448015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 256534820 1250 256533570 256533631
    0x906050a030e0c0604090905060906060307030f0503070b1008070503060c0910021501030605010510020c0112051308070c05041401030f110d150902010e0102070b0f03061f1116060206 80
    0x100101131a84e0f45660384171441c05020094002e0f5020f0003030100007409840f01080c541d22543c0000e024288803801c554442c201005180020380b500e00c414040e12001480403400c40e4080c900003601c81109610b0104924600103c50b048680607030032060030b02c142c010f2401e003914880b03201207072320f20b406110110080780b0b403102071111070740c520700c1400001060026650046040e41d00c02d54580122130703c2103030260303601e01243c03c4540c0041da90200c0003404121541c400780d00242c80782c500030710014094403980c040c3c1d00010010748498103004820030061600340701d00c99002501d40070159442d803464413030f1641c0140301500904800c4150380c0d00c601c6903130b540c003040e124568480d0760b0a64400c0803061100041159020803408030706000050415507000250442c1210810b24010b8a040c03406041400c1c3c039040a00302c617402943c0c0e103141d500880362500c0f05012404803a500d08252401d0540043d00c3c203507503014100300b5410501000e004944d4040f0740180d00101e48015150b5141054408590490 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 256536070 1250 256534820 256534843
    0x10c1101030b0d03030e070b030403050d110405041e0f050603060c07030302121e0c031603020d0b030d0f030f0902010801120201020703050118020123090d030e1509100906050a030e 79
    0x9140fa0101410140c040c0c0c0110a540342200481c4d00c0035440d5100280c141c402502c01070040f520038084000c0350362590b0042c02c2001c6242041e00d080540e10700109059484034051226840071107028012506128840c0c5071580c02488010f00040c1460000b180c1c44040c0a00800e00107500000d00354140350080d01200c0541040041060701860302590380c00081740000e40c580f44100c01140410380b620640c006607805101e03214a00024941160310640095112080003811542c4a850030703062a9000e00202491090749e444040d041240648024211a00602c1c0b850741c3c4d501e01108000941d03072180d200c41c10348440d03100c6003e02541500050f4503000c2154402011076090440900045c80c22040c4110094400c0c0c0350310511326064030700500d001c50011033038008420705000318103540c40e040e521052001c1c0a030905992410352500801c608546070010303090202000101d0600605000d005641840c2080c540308042c1802d0240050081c855003d55100b0981c58050704550310006214486041c1c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 256537320 1250 256536070 256536079
    0x90304030c120b130b0a090203160e09060c0c0d030b040e07170c030f150403090905071d0405090709051902120702010e06012706260f0c010c1101030b 66
    0x480d65004240450064901d0440c3c02100d8075000c104c030314610080000c490340d803080a1509075600c5608030703001008200e00c260ba052107a00003405540842200e0440134083e6003011003c1403402885683c0b5204000d080310001c100d0800091814840106100c50015100e180100d800071241001030058074403a039040d402c50203451000500805281c3c0d007140c1c0070b0150300c20b4810b0080780008060300c1d1038882c0e040380d145400c10748802a43c10700b50801c86500030b10070b0401c80005615410f60070120340c401c840c010f01265400801c03060132800541c1e002d10701c030012141071117a458500b00a50b20740066110f1130201580700e20101c2d80f0714940c04624500e2142c115804c5464041c207882a00e01d0860641c1d1340c1000d540707040301c2580342c03c1c400b0400da03060359180442d940d0240312170080404910400700b04080a10380d034041c0480c0290250102e0b000f820380014002e00602582283c0d5801d01235500c0c00004264001c91407403040340d0b0411192052903402000320300000101200680140c6001162a54031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 256538570 1250 256537320 256537343
    0x118031709060c0f01090b0714030103060c0c0c09060501080a11120912220e04050a0305070c0e01080a03031505010e010c02040207020406180b0321030402040603170c0f0a08090909030403 82
    0x40005506c9841e00f10b005d035104800301d8640c8041941c0c80021700e0144503079130b0402c00050002c5040c6070003200030001c0c985442094007041d61149000111030f03401401140e519240100040e60b03101e0913030380c1c00952080040050381c09418080c103081c8900d040c0e40340190900703c002001ba50051018070310741150010f080303669045d485c041c0c100c03109864400407521846860040b41d10540c2c0c0440a20035580040240a070200c152825120f603081720000301d810001c046400700b100082c0b641d6560080c14100000e05074403941d45005816140340b040b8040c660946030508100903a8000c42c014500c580c2030170710001a520500220300a44210f0501a402c6401c281c0d0004120740508265581c101050108000064040080503140c2d035102084003420150f409078450400ea25000441d001803006000140c003d40d45e075a0001e4079081d550b00445180000702d0801e10341c0c50280101c0e00c045660501070b00101c1180d40d24010503008082980e8061860707500090b180c620b0801c1141c0103160444802c019 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 256539820 1250 256538570 256538593
    0xf0804090606051629011818051f0204081204050f03010911131103070206040201120c0e01050d0e0703081c06050a09110d05090a0614190b0a090504050604020118031709060c 76
    0x2000c0303020074890b04d03001d488d004000c44600c13110802082d840d688100036110803201d603584d800d00c212658070b036070100c3c41c1e080200298003601080540e22032402c4140050302c41e4548010072400700e002c80300b058046c2c7d0406d002c4500007000d0608800b03009008640502d94000d00c4d42e000e400508421000003400000007042c01241c5400181262056100343e8804010002d0455150140c070b170540d866102007015001002c0d580d6001d0809030411102c250000640c080d54607400d5880c00a072548103a5035440002060083c40c0030700c0000040b0410031070002e000c20351521020031400401071064030307001561020740d1180c507040c550450308220390302407091201e17082c254006900c49441d03040490b4594a03010300103034030f40306c8070065038441c1d100241c1c2d070440390f00c2d80e0900700c001d00b17070041a8951007404c103840410780700d065200d01c60040d8090320003400a8641840050440f40c1940f115600704010b2090803c005020007a62008003181d2040607610b4140c110007148050141e84407841c560300a03040060f2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 256541070 1250 256539820 256539839
    0x22020103180f0b012d05090601120c030515120304051c0b07020312010f0e060f0112110c1908070602130b040602031306030e19020a030f080409060605162901 69
    0xa050702d10310085c4114203d100d512840200c503a041d6036000d4040041c0d010840c42c5840c00029901c0741060500d503c1e030903121048402160440c070440c901207503a500600200c0f045a100300b029620054450314a040f01d120507856a9020b40d10683d44100300c0d0804190505061041e10180294440304c480036900b00910060349a81010790302c0010052800f00008040d0340610004044a45605000000d5298007080c800c0c00100c1c40181e81c14400c60342c5d10302c04074040c0c0c2c0c80744621250031304111540716640184104c2c03d10388c603c1c03855810717000c80c040c8600c0401c0d0482c0450300307129404100140e45541500c10402c80c580c05030b100040c1c0d1400803a00181c6150088000c2c020304001c44420142291201019011251080340420099018032181c0300380c4030000000d406141d00041a103550f059882d9540365032407100c02411038003441d000c030301009082c401b402075001500316410880d0900c004810420f04032031900001a00101e515140b200b800e1300030060198101100240301542580c68000d01ca = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 256542320 1250 256541070 256541093
    0x23150a030510240201060b0a02070501020c04050f07120b10080601030c0c0320030f16030801060801271b110c0904050a26070b040201030522020103180f 67
    0x210042030038240040c4041003850155000d0700d0b50f036074860f000c03000b01005644014418000c0f60b01950350742d00010501035070715005080d009407594010f0400303a007410002801d04c02c684100c1c50085080c0404e0241d640b0b40350f42e405a04c200c151629800c12040b0b409014060b08650001c1e9030400d0003020b8030881e0355070107000140700b400281c030144100c101141c0c088030807403005800a13000070240030f03c0e4031b00b55a51180b80d151241c1648212030418030026491802d95100da5461b45240f03900d08864010150041540b60045c4500c2c20000d00541c5810700c540ca14103800e840c26840341c0d1250000108021350b81d404048002203000c4921501d00da040c001038104548004c2c5080d403071082e148045c0700c07850070030307a85441075601030080c00c034002056803001004003070340c0105951414001c1544140520f9030303010303101c1b40d0700a044014150038540000b4007101c00c00382180d5030895416451440c036545000c0c450300031076421b190026041d94030b542d0685070415507520007041c80544c6885c140a02031244002d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 256543570 1250 256542320 256542337
    0x302070f140103060b0a08010501050d0e0105090f01060b04080303061c061d07052704031e170601050304120e0102031c02070209070503070219020a0f09020c0105060301020903072315 80
    0x30401103032181ca641703042c2d0107007000c0080000d0316940144071a510440180c02049280c000c085010000403c04070300b5100e04503025000c0b60702c00724030550318807801d01030b9a00509021130100d03e01400c0c102010b07100e00c0f008200a004010004e079140c2c0624841c0d02d490758503500b2013000c005d00740048000c001c22800c42c1903038040f98071481034049100e10707110340500e1038822001c1740316504000c0c50b1104003043c0781c010030039030500400d1240181e81c1134160701c4003145005160744091000321030a042c004154006450103040000510402000511048002003107080508010328034410100040b80340d0b229011004903c840007110507203000090b45c018200440c4210f8041e40142d450020407591030200316804001070b8844403d0400c0d41e4842c082e903c0341c00c0c1c0040c14224246403550a10b1071046800e9002e040302c294002010070210340b080c8102d80d00141d04034002e510b031520040c00203a03204a14060013520a00c801d01c150a0b0600b0304002c90480d00016000310300029400200c1019600021207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 256544820 1250 256543570 256543577
    0x22080109020a0906061b17190f0c0c03230d02072315070501020d1b030e0703050601060302090402040f06030b1309081b0c0315100b04080d0c0302070f1401 68
    0x100b200ea207a0700860003901c0c05c5554051030400210b0a203409000c440400342c0d40300c80c1c8504084034a5250400401199200040d0000318802103440101050003000d040c0040184464045002650340c4800c1c2048a802c01ca6031051102c40ca80c0103c154a00514254918415241c0072028150007103403040c219400c80c10044000d00f951006e000d0024201a0b280790b0140c8078101c040440201c070005084003501030f10005040c0390740d02c03c00320104e5030784040791902800040503020300c04ac0d042c012101244901c5015203512480e40e96140d540b09418022181456000300300d07a080d644540d81a036005020112001c0d89441d51854090003d0507903000660141c144610041c01da250b09001c0d24001c20390040c40d2b140343c03d22515540410016419201a4a014100140c2600e40d000c00480d44410400e070780184440c10112085100f40c01c5940c089120380e01d0901040108000101e18113111185034200601001c000c0c2c07174100d080c04110b405c106c41d92603880c0030100702c0fa100c6411034280c02d8001c5c0c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 256546070 1250 256544820 256544839
    0x903070f06032d0e25180905150615040306091202030a0f050a0302040518091b0102070905070e0603010e070201110408030a1d0d08030412080103020a0b2208010902 72
    0x159801d041040d60070448107401d6228072482a040025401103640035a03403c29140b2130412140d803024120211410465022001c60040c800006c0440440b0300c50b1900100400454080c0da461944441000086002e00819a00014a2500c3d044040c490f06819103265556450303ca00e081c500a080200c400d5500811810b0004a128000012100d0641880e103899208071022141122150301030310404080607002d000004581c1c40e40d946460394681000050461840c1c030071991450008200200440021880012083c030790b004580c07801503400c10580468a0750701ea82003510401c655061046c1c005130000000540d41000c0540240034443c903500030300c1030043d0012105440d000c0ca010780c0260b500100508003081d40103541e01c065400110950700d03a03502c04500018449440c0780701c2500c4100d000000c00081200341c50b188940407901d030401e414154103680101da0f080503140141103120000007199138079070b03070300c2d0400070154000300b4080781601340c450079428083c20500300101c0c084c5c42102c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 256547320 1250 256546070 256546091
    0x40207050a0b07090303050f0d06260f0c1c050a0209040f0501060b070314031801020d060f0e010b0406050c101a030c040911010e010c020402040306091a0403080a020f0903070f0603 79
    0x4d540400459805540c1c00b820000210240652940080c1c54070b001155200310014105c131b440380a460a21060611104214a10b03040b018101003070a0282021030b000300c00c02056560b100081541c3c0401c0983c5407040c560241c4c50014586841c1c6c2202070760000d0300500b0041005070300301d4447c6680c2d20440c000d02105580b110070400e80d00071400010080359000a000c5103108135600a154012190306100103810f65003031070282280d1003803002c981450784410302440f540044620f800d008004c060301b200c0c55585080c0c20b15409003e1405a00200700b00000c04619a0404000c41184250801c80401203000341403044084100c6018100340a8082c1c0b00300c00e00b4900d020712900b0780c8180c0020000c8442020300c801140c0450300d0950544c1404290b00c80d0b040035885500c05000698480c00c00042d01502070704014070403d04030788551907246021010800044e80c411180d64004c125000056200c60301044489a1802020b00c0d0700d0b01442009000100e0a4001020390211171b101d841c10007850540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 256548570 1250 256547320 256547327
    0x4022d03041707032006070905030615041806020f04060905041a090601090315060623070803061c03020618070f1505190206060a050904020904150605040207050a0b07 73
    0x2110058224120400040c10040c802e00050501c03900c6864282da0020f8000c12442001d80e442680100c564080000c0002a80d00500c0480141c40100c2c001c0c002880c02150300403500d000e400b6851700907034a981a00002650100c9018003207035206074150744403682c1002c503074020380252051000140c16031100040c0ea0070140319400e118150031200f107140d82c00760418400034600c0904100e04001a148001000c202d4141002c0c07400750116a02080c113601d8913400401c521903000c81d0401620000c0c10481507055882c04950081d644285072540340da44500c00240c50b0030074180c8165040c44501d503440e0402d903001c103001d4856151065411181e0300d03001c44642e640c0829000d5150303030f228410400e0048920314880b06c800c406803031400a24002889441596181a110500e030159000b038062021900e01426550060103040c0d951003220700d03280d000a501c0365030241015011820320403241d02801c0c0d071500b240003e0708002d0425565031040b80b903d19650040b4502c291104a07440003c07031601c40c070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 256549820 1250 256548570 256548577
    0x3060f120210030c0519120c0c0b07082406090607030c0605010603020414040b0301110a0c03171e0601031b120515010804031107030c030827062704022d 67
    0x4d05aaa00303007880c048600c9030101c0c00d480003051043c0050000b003000080c0082c0030761803624591360b0790440e01c0480c9260074111000c025100c2c5c01803010103800c000c01c00c2d45c82100482c00c1c01d41c60580d01c4110f4800e82c080384091181e50060ba401860014038841419008405512800c0c4100c908000c03581e030b41d000071000c071300540c0101e821005194100081c5407509800180003000004c1c000150f05901c0702e50325240e98040041040440c2009011500b8517411104040c0202910b0300c201219140101481d8402c11031000c440002c0751045010500d1a4480c0e4042055007615240021540701e110030050b01d11002d01e80b003002800d080800064003210341c503480c020f0801e41a140c410450701c071543c060782c0e081004c0c005040d0a1044030f80005c00701c0d09248642000314001c111050f9a00891851040000d881000703a488412503010340b0038050b00c1d08005c031100c010b0030489114030300400112012149001c034022651150002c03800f4601d0102103014902890352443c0300300a02d880c0110020f00f07900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 256551070 1250 256549820 256549841
    0xa0303020304090c170109150e070f110c10020c1905090105092a270d0b07050d020f040603061a040e0a0209030a030c061d0a0f0303060f12021003 64
    0x304144400c02c540940f58002d0001c0184a080c41001c81c40d500304c3c0c0c0d44030760788240c0c0207620041d00c1d02c82c040c6642c0301c61184513000d010800c404030b2091031f118002601d20340004006104200f00f04c4c0010103d22400e02074071010450040132245400c8403030000941c0c2c4c1c020b11125038412150142c0e000c4003201201d10b901d044603400741c699400b9a181c407040000715100107200d20000120702621808407082d08502e85110700200c1031050301c805640c01e0308846420301481c01c02d00d041c42556000c485598841403c10590b901010600b4296500001200c00e4015010340300d100030b0000c41c00003031000030403003d001aa2001d940800c1041d64400d0b0900000790100c000c403050590410050014174407483c03446e40d00108143d80035207440003243c0800c2c80c204040c0e50640000e01881e07e000c080100c140130f581040091103926101d4151035844680e2202468400144802c600f00000002c150080d0010f0f001004110301298604daa1130481c00c18101c9201012032040505040390100b03580a4070800b401c64 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 256552320 1250 256551070 256551073
    0x506060307081b04020c0706020313050a030b15120313031a0f0703050c04050a08010c030e030a02100b2803060c0f0f440c0c0303041b03050a0b0f060a030302 69
    0x440c44101c400c4a5200f656225600150204040c0300088010080c0130010306181c1e006596441d032a02c10000340445a4100c03911506070f41c03008201241080074065040003010b000e8842c0706220f04005041c41146218101150001280080c181108154004216801340d040300341d014585030103000d01188210b0f000b400b040000c00200300000e201c0d600555010900d81c00c841c0ca0079031200c00160030791490b40d02078582a9141d1080901c5598140555a904099080218100b9a41c0031019403543c0303050408681c801d98590603194141d80e07149480340c070010002d1a280c4910880d18000c145010180020381d011410400b103191418803401c501c041710040d41e9100e9208407041c80084400003c2055145615814814242c503041c180314036032030741c034080d01100c40c1107a105c0b845081401d01d0001c00700400b000c8180179450801d40003000322503000364003001d000d2013901000d0500d11183e07002c0c2c0015220f07100b20701c002010480c180c01200c0c01181241b0084e850380e6100ea00b08506014030b4000107005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 256553570 1250 256552320 256552333
    0x3010905030a2105040602220b0f0904060b1603020d020304030302060105010c0812070914090f06060906070f05010f0b090603070e09070509040507051507030c0b0a090f0c03050606030708 82
    0x1058418284400000004065011003c1c0150509820354405032000e40c3c92543c0010300405580704408103a9023010015002c96120f0319014130300517507016001603100700f007500103514801580c1c1c640c04100680b42c0c01460580300d440c450340100c100310000781e0840c003610681696407c118000001e41b400c480e4198001c00d800da0814004442c0d0341107502c800c80381a0014003005403071141c0d4841140c1b08950954813240c00603d410042c0d034400405810480c06aa00c5d5414030498a40030a03855501100984809540301c0440b00490098400c840c0041c01512162620804104064000c8072202e01c00700c00510581401b44100a00d5400a0354559030603480010f0400c034103400750403c554824880000e17070320f0060340d420109140207012074046659401140d818401032401e42044000c044040e40c10f64101701305d65030040c1c41c0601b22800500442c03100800204105803e401c000f114a9104840f0000d02d6401c3c541118031181c140021501d0740030b648001000307030600040000413164040010840b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 256554820 1250 256553570 256553587
    0xc040e010b1c050a050402090615040e09070e0106030221090a060507360602070f0b1303150e060c1608030402040605090c040807090504020f06160618110301090503 72
    0x650340003180300080c000d2040300340070344001d0b144101c900c1a802e03081c0108607481e0901c1000110280109018881d00c40104440c80c03211003042900c090f00d0900c0044c5034292590b041e1546002c807154403507650130384c019002003407065054000e40201e60310044011481059905044411a421a01d8141c141e104001c0440890102d400064100f540c2d8102401c440f98070214030843d501070b00034902c1101125524404445c0c5644044100404443c400740101e1800c0c0060b040709079085206a0020040100345140f0244031005014011540240d0101f1088020303540c2c90064240350b0440f00d900d001d00b4001502006c07000c41100d81c210380f0500d8184400900366210300407a000034000381d030006d6a40d000031646031140042580140321000b0000d4071946420501071901c00c80350000c968140c244000d100040e1246202912881422034131141c941c040c0d001d00299100c203242024003454103104203013211055403550f44a200c1d015020086141c458074003850300340c410a00c8020642da000300308144 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 256556070 1250 256554820 256554839
    0x1605041413060e0106150206310c0e10170705030607110c030d0c05100c08040204050408091509040c090311060f3612121303060e060f0c040e01 63
    0x281d00c0c1d03102e40c1001901e2880800e250b0708448954005400000c0c1c01c0540b24240c0360108000c55008002d0240d07071000544107a6848840300070702051468280d00c140c0c0b1a800c0050a08410b80501011134400203680b5100d41341c400b2500c220300c608010b030b452031104298400b00c04103400342602c5014004080070f0300c842d1000c49200d07000000c24101ea0245240c00c047c141d805101010b91500c1076907503603070101d0203410440d05002d583c280b01c80e4010302d850758003460641c002e41c9484d070003034044600007110303a103074200707542035120f6801c010307503c00c418540e0481c1d02c0d40840041c0000d02c8050b01e04216484540c1c600b43e400401500010304404901c041468491801400600700d4052a40d0820300340740c07103d419054070300240108980c0123040134a00c14580e0050700b1858060302c1d021100500240f80001501d51a04000340b41001499000603940c2500b5654900207030046078018410000005291000c1d9103c00c01680c0c445440003c04010991259281c23054a0039201c500380711490903440c01842c40c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 256557320 1250 256556070 256556101
    0x5070e07020f16140907020c0f040b03010e061b090d020607050a080f0d0c0305010605090f04110a050c0d09050a060e010311030c1b01020c0307060e120a0216050414 72
    0x600710302c51041040007000042c401c800c103402840c400242d9481c1040d464016000d43e45414078024910201080000f6500046406181d001a41d004100320042c8022601416107407075041c0d050760a011000f01d030180f0001c0c407540b290382210310e03d08082d482c420b0b6500061041035600c5511541407034221f005032a280b8020501c0303034459011203000c417641d40e0f40c416094020001c3c0081c26580070410000440041c002d0200c080d00e03d1404004d158148040905180100c1315600e0003000c1e08404120141c4550340701d150120a48180a5241d00b90410010900d610180e5080900c0c011440482c1d02c05001c0c51180c8150b40000305803c01181c00c005c0201c500d10550341c3d209040580701c29031449030703030300e11401140070b11003201c1a6640c51406517240c083c2240050460034407a0300c10407032a07854080110589078019072140c804282041031181c1c4600d40340c0e2501503e00c4099001800c0f100d0f4903000142e000c0d03404071098145400b20340e1041040200c4000c0c207642c0540c1c0300d20800240d10780c0700c0003550 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 256558570 1250 256557320 256557331
    0x130c08031c0e1b190f140d080301030b06031e030711030c0607080c0319050d0506090c0d0209060d0f14070f08040809030a061b03060509251103030907050a09020705070e 74
    0x49480094003580c0c880c0d6138900710780c05026080e0880c10b0074081d016900c007100c1e680c0d40d03080c0c400e0129107160f5582e8051b03902c4144030107001c1c141000042041a80c0a02125220121440c81280c6803801d00c3c020b90703101c1d80955030407941c40c502c20000509a003008209500304c420000c2a060070807403191030390302e02c2c0c2d4000001840c0ea40001c110301c48800d4044440703070305070b40c504c3d0381c40b80e0300c86c0707240901074040b60409800a4800c4c64100b0401101d2448002111164030420324090703202d21010020030418081c9001100e83c0c6414070021001c424115800a40c0741d0400c0c3c800403035591559a800c1d6000c11203880c80c000011002000100072541020060100c0c0c20054201c41c0440d206032074000860b00684012451855140d072880300d03890345801104084d08048807001260300305001480c048945080d2010440a403030400c1c801c006008100070307001d94202c802541e56a181002c0380d15160309103406240c0c840c01484102045040300d901c29140140e6100c002858801d0034404002e801c280002c09 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 256559820 1250 256558570 256558579
    0x60d030503041e03020d2c040e01020f040306140c0703054303081501090311031908122827240c0503010303030203130c08031c0e1b 58
    0x5282a43c0e81030041118050b030280c3e000e081d0ba45401305006144229803c0b0100c41c001041508400540a81e203605180610403540041c01c410a4a10a406805424400848014003040010900043d81c011603140c003034041011400da079400c1114401c60199003070243c00108203229402c42c00e0208800d03221a0104541b02c6420241d01c080411844400b24078007110b0403505180007c10160000701d41a0465136050040140d044040e00003025080c0610000d48104803980c0250b401e42c60501c00c800907a280403448030b6684603d1b00b0408039580c031480740b03016045203c40014101c00078803c000b58688400c083e004000d102d00c00184c00c0504842d072020031100d10038420104241e0900c58800d40218030403200006940c4130201c02c4d80b01804400c8640d401076040c8180ca860841d8481c0c1100d040d40c1d454140180c490300c480390708480306a04e0280007401700d448004c000c10a03480c0000a0040f000c40d1911540203141d045c886c210560714080d044121680c000314019180403540c11035203580001c0a013 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 256561070 1250 256559820 256559843
    0x12030a02090d0c12030906020601080d081e010b04060e04050f040b06030c030609010b1e0303190302071a091e100f090f060510090207170c0120040518060d03050304 72
    0x100c0c0c5400c0f00034150710101c1c55a44000100c0101038001c1c4911004121500241115624010314540c48001404c102010020b1510000b410b02d40101045213040080c1043c0c08280d41e1980e50041503a0300c07a018400206001c40c540015524113801114400c20008002d00781c03d841395038400b15a1400600710607458000c0000801c03107074030204002403060b900100041080980c09013802950308550b03000c41e5070151041481c486035100082140c02c2807010707103809103047ca00304404038002d004200d030081c440c2c50802d294001240c80d94841c14041d04415042e5a41803826041130701d0100c4540d800415140c12042d80c0500c121a16404140c9000c0182c0e03010a441606a48000f02c842c044c0340cac02c80f070585e501c10038440c40209203041c0c0030151001910451030444140c8075603100403007202c6400300c40400003800e42001602900010304030300014003c909507407000040c0c05980d03003280c043d450040b044180c8060600980420032400380d1405010b0701e014290340d40702180e041d40024015101c184184 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 256562320 1250 256561070 256561073
    0x803040302211506040e0601080606092d010f140d030e01090b0c0a03020c1002030304060b0f0402120a0f02070b0c0f1b0c03120301031208071e02011d12030a02090d 72
    0x74020420b8418402d81040c080c2e24084082001b2180e03c44040e00556000c08010700c03038a40d00080301a0021001c5480c0040c40e907441d03403c501380c2c0103d00e8501c01e0904d10740071486d020024100d126410b0f0340070822800d40c46526100c42001c8074100e05441640b00301c91207160004280118904031420a061402200c1261510341c411280c0d44204200c070210340c00009a01c0506606210143c0310034800c0f0fa5034000501c050000a5a80c0000f0340701a00e1503990307135107200c220382e50240400300000c0003070030964881650380364000c0905412200c44060304e041c041503614485040c4202c40d012903000042c2c6265403070f10304042c04c0e55000030900d0182d01000704160f16424040040460360264944014084000040c0505050100424003005120030a100500000e8080c4402e1054075480b071408030150744d1030f5601210342002030b56040d0b00d9548512000c2d0405541074002410148422030708041c3c60300c42c901c0c60b40d5a050302d904400000007083c80130a01481480e001480d0050703000303064000b0300056 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 256563570 1250 256562320 256562323
    0x2040c030b041a040609020906030406180b04060c02011a030d030e070305070e010819021c060b0918070816230603011d060f01050301050f0301020d181b080304030221 73
    0xc0518682c0c40210806803c00e451409005a8010b002c4030003003036051140e4900030a1041c04040d10040419444028418000e1440380b000140581c01071558502414503040c0b01d001040f240d02003800550130004041c1c0002c1c0000d100f01c0003030034003070000c28048585250481c014042c40d01c0c002e5a44c050702038000085001003100e0340160020f0010b003440e951402c003c9502d00342056421a00c0e002001d00b000000d6565600c908441e108240241d5814444a01c1d094000b4020800c0260b03000c140c600034032108908500c2015a0b1407094000c80b00c4094668400c9503441e1000c0305031204080400b00c0900c4040d60582600603c41160401910048401800030782181c009810540410100b0488000c5580382428001e0308401c090716010400004480000c01d1440305000d41401006120018405620300b541107910403031071030344100459140d000d08803d0413003840f4001d44080100c005030039442d50720280c1d50310449800800540c502407843d42803041c098a684e274000928085c4240e0442c40300300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 256564820 1250 256563570 256563581
    0x3020603010e07110606010e0d030e040e0106150c020a150203161208070c031d0a0b190e030f07210605070809010f020901320c0d020105060f0d02040c030b04 69
    0x1c2550b80c58140c50600e2000784102018002400310758852000e000460b6003006140702c115900b81c420302c800100e00d050a5614000034201e0b243c02526181c24600785e00b4040d48590b060741c64003400e000026158440440c1c144611440103580b0101c8070900f0410a980103149501c02682401581d0803c4900b0305041070390a540d46085d210f403101e0070b40c0c06015583c17000849600c107105091841c02c0b81c40caa140100700c056222070b160315071071104c00d416103142d803900c2e00c080003400d4043e4041eaa0300301d038107220b010094500306102c01150011806030110300e000709144501450041c0104074061800d080c0d02c44400701c05045020000c0001401c0010806500403103100c1c1d01d4036200c2007030b2030038940300302400c607000c1040724a0094410310241180380c0c0e01c001514480ba8003e0301d51070303007002804024001da40400503131011090000a01001440717000c90600307542402a0020070140c0d641d88203102e0641030004c1e0305507220100440207401454681d004540100c081d00e80051021520008913040b2003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 256566070 1250 256564820 256564829
    0x5010912030605010f0809060417091201060302130b03031206040f02180901090218150409050702071403070b0f130e0717100e0c07030302070b0106080a0c14160303060302060301 78
    0xa450740300c140010b5800c010310303805c120030510305045c8074a017545046403922400b0b0001800d0494400d2000d040d41d92130740c151349104200400c9a07480c84001c0751004d00924035480120f00403101109040b5012001d8401d003100b100c40a07000d540381407003c44040e449600014455544166240344d280440400d5101500040e041d10064009207000c61040002002c0142c0c8070502c098010050f91130104040d284a10700e2800c1a100c450f0043c07480380c3c141a83d401a900f100039094541810030540319800200002211070710090301c034403525090181358492010380118541c80800b040740700807240801c0f0080c03483e41b03010b80300741d0b0700d00d6100c030407911807980141c0b0031000146900b441c00000008030070890f500540600c0e04000568600706002d85042d000070f00010100c03c3c0411000d050602903011940b880e607010b4840c1e440c2d503031a030402500d83c58050b1000041580341c0211184124011540081c080c04c10b407a1a90506105520703800e029161400c007141015101d280000c01600e8030030246001c4d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 256567320 1250 256566070 256566077
    0x70803041103150c04090b030a0605040606060908030c070b163309020a0e04050f1c090b070c05040b0319060209040e06070f030f18050c01110304030c1205010912 71
    0x40c0da44034101898540000101d80807461100c0a1011305031460045504440c040310021500c11601c0700003e08040d40ea400240089040c80100001c21000c2da011100f40e40080e2035071008603440e6121982c0ea402454840151a4410364003888078002a902a12140d030040100b103040c4900c90350303100c15450040e81c1003912403107000b030385000c1003142183c60095928000c0c0e00b0420b403409d03600000c50040240c4110001b603074541d00454140b01d0144688200511000111105400d0901a000100300c242c44404002000d00c1d501040000d8003504545000360040c50b1081d40768203190401000b0f0408070480d50303041c8202c01030006880a8201b400c8c070464043c0a0040c4c85124500c2072105461400c00002203d8002e0703810808a16003200003072204000e1703844c2c00900c0c00040910350000b002281d150007100483e4203000e10400100259007072009170281e03143c1d00000e01c4150700c5507580c06103020060001032a40301c10b201d40704400c2804180540140c0000c43d4191041e1240401500744c01d8405000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 256568570 1250 256567320 256567343
    0x2715060305011403150402150a020f0c0105030405030d0b04230a1104050a0e041a010e0601110304180b0607020d0b0f0907060c020111011b180e0c07120507080304 71
    0x40e010720440b8010618040c04103c0c0c000040e00203a1584212002c607410007810130040703000d6454284210003070700e015144903540d9100000d0302171f6849640e000c40884501c99500014160351180b402c1c2d90059910000460420300454009000f030548503020640040e580c01c4602c00e04c2c0c41000c00210b0365074000e100030715142000c40034003042d0b540152a81000040030030003080745840750380c410411112105080d1903503440d41e1070300954020240000c00c44822050002107168000b405505000c0c80c4262119081216241c00c40c1c0c1d02c1e8041c0d485030030b44d00c2c088401c180184000700d03040980720703820040503039250602d2341d40080c0c080700c9024015658140e0a00402c10702d04102041c05810101050081601c035181c0a8020290540070f10001d04100410484440c40381007500b04514406c45030050303100010252070b00802140d490308110b0401071100100160020020312200d02035003004801510303000c1030343c40354074500d08038110a4007001010003905c2c0101d036020001d180958030586a2603071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 256569820 1250 256568570 256568579
    0x10806063f070f0e060d0f121404150e0d1e0804080142050111030712020c040c0e060901030c0203040905091501050102370503030a05060a06090f2715 66
    0x3400c41008144900504035a80c141c0c0105414560614486a01801c283ca103800c0c0c0784012038085001d240c4111389c1c6a004100824008940c045c5107204858a1342e890082450507410400407045c0b50b0400717000c1c481c9122624444202c0041e02034905406107803402e00d02603803100c00c40c1c2142c001545c0418070101c1e064072a40c4500e1008400801d00313180c03002c2c80c10300418070020400c0301800c0d8445c05051010840400b01c0c0301109200383d82080343c002e040341d5005196500040c1d101c10800020714800e51800d4000b848882c041c54150380c0007e405406503050480722001540107180001040007076200c140000541403585001e018452030000001d00341c0049030b8041c8594000e03045c1c2215056400200460030202034181d5031301ea00300e4108100500c40c0290040c603092622050a020304503001c000b08000d4808101e0300f03c58011340b420740310304003050382d280000c4507075680d14043c01903070384d159030420020f01c2510050b020600c80c0e0707a400d045641d2038840c041000c8507003482100c9008518040e0820 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 256571070 1250 256569820 256569839
    0x60906011403031c0b0d0b0a0c030f09080409020c01090b13020117010b07060f0b060d0902090601020319031a0a0e1603051923010e010806063f070f 65
    0x610301042d4021400c0c0030900711120b1082d000c000302a50850b9403015000400e540356a6a8912039170401d45602e001d04100715110701503c0a508010046420a0a031030303c0e4600700e1140300401900000b0701c0d4105800d00c240301e4042c2d40700c4004128107640b01c010410103d14004e807210702075a0294070115070107043d0320014000d0b0040304810000d00906030010071840c039608084548041d400311000135030f4002c01080e0001020700c00e09490300301c0c00205c1d220060172859440700324114000ca503000813542d40e2400483c1e80788100307281007401c00220411841c486020781c1203c03c1880b01f040c0d19085545080021030007801c4c1d164080095960349805100c0c546000040c0d020803090103180078841c1d03243c441c8025082c4285c4d071065900d00d45c0d0f600d01002070414603640d040512044901200e170385503520034429010744000c0c00707540407901409010880b00e2808031301c2641d581c060300c00c1c4a0200f400000c0e0440c12050840f2041071200603a100c4c140e150341c0140601c8000d0044010101801e508000b0400b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 256572320 1250 256571070 256571099
    0xc0f060c040302180601120e24060d0b1012030305040210020f060115140d02091302120115051b0607030606020f0318060f040906030209071803111206090601 69
    0x60420403030802080c0050785030440b0742120385940340304038072058a0b00750040b6000c0120294036004a031600404901e4284041140180700c10b000f240c100a1749a0b0345001e0600d00300990340e5940c45880303155003070001000b01c5200c039481301801e1010b06a255490301e0f0150856480c0344120000307644e603001c02045160101d01170b8070403082840101401c00d281489182d8528060144281d0300e00c200802d401d40380d1140c00d0f2441d10000c2004001d03203d100c16800000030f90000e88240e403180740c0940410394140034500c03d4502604010441802c0d42e4600941c1d08404117005010004000081200603041e5079014040c00015004600070007051070301c04da0040440b19150800d07800c64000048404c0d1408000007650240080050251200070390600000d00302d10070380527440b29040e0007080029202501c0e9000e00c1c103d90080d59502c3d910f644814003220a000503884120440e158101c040c80401d000544204010001400c481d6410901c164991314154088520301c841c1da0000005010398004103490 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 256573570 1250 256572320 256572331
    0x51e09011b0c050609030c0418020a08031c0b0d1a040501050a060b0d0213030b0a0e15010605121504060e1603021908091507080601021b01090315060b0c0f06 69
    0x70701403a4902580ca1000c01421032051504c203440215104000399800c1c0b11a544060703000344104119044203640c0000d45103d4803040c0d105a9080c2400503041002204440801021810b22607076403242c0d4115100408030071040a4101d046d050801000416205103501141c44100c120001460b1500d04542502c07030050101007118180303c42088050b0482c000d4070030f20b944518015844100410b40134141008691001c1c0c090380c2481e0911803002e0740d51340700000d4100d007201540c4800d201d4070000701c981c02c420320964000410810101000d0352400c64101d8101c00c0340e200817034040003034100180665007139811404103e000e140034414020712400380348000c854541415410308186c4c6005110711126001c03072809005ca091300045054800b40520b06681a14034070841e203604008070300414110041391014094410b10148044440b201b00b4081c03000f100517555a130751141076981d6000c1d8111414030400415807900004100303c0c061101a1a051036080028a90203513081d211614200f030150a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 256574820 1250 256573570 256573607
    0x120a0b0a0605040f06030906020d0518060106020606060406031a030105070203090109050f090126030d021207110706030c0e12060402100c050607030504150f06140406140d03051e0901 80
    0xc00c0040d040c1d100c45005c071a505e0034000781904040c02d10001a100c3e0b8084401c945281904100300302c60400601103108000108440c40d683e00c0310b00581ea034402c20b44100c0e83c080014070080007554401c0d049140c503040b4403560740c01c4040c07aa03000b00c0d0a40e0419125900580c00103d104141541c0c4144010300802c81261440740d08480d05010940700c0308103004590f8204800c10b2103140708107440c0b20340c1c030740084100100c0b030303441d100c00501400039044121740c04144405040030404903441a4241d0480100e8040a001c0f15840c00c2d0090b0b00806194861030240003401407841400e03a0f0f00a45003100e40800000740c41145014410889100c200310ba86005102ca46034001d030100b000000d00603407042c094200061607840d241820101300d0790881e50b0081d5241800303003900000d41160018012a0600e11051a0350341c100d500300810340f6150300850040c1042c6d49044012841c2101d8005000c40c002d060031403070085101c0d640700c20b02003207a007030071a0403800281007401303540d000380e845210491a98 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 256576070 1250 256574820 256574827
    0x1e070620160b0405032404020d021c0b06040b0103020903060c03150a0e07090b031510140304241802091b040303081012020310050c0c390102060f0408120a0b0a0605 72
    0x260314131b02c2242d0142000c0e025a01502850045407611043e0010b42912660507091001c168074059610310005c4585600540c1000110364555010b030003a140762003401409801349039206d00b1030809542005128095618040c10f00b80d03c540c4402c00b041002c0c0400c0006074505c1d00d0075032005000703825070390f001c0d1088280030030401186660b141c0403180000821500c410600b61011801c41d4074003030b6030300d03204540000007040c40108051500d001360316140c1501000b02900e44503414500329035250360000c44d04240303c0381810052500c80750701c60340114030f01c42c000e030720b018800a040d40d10340250300200c01090000701441800042c01103800001c0144d041d150810b074030507901007134032010f0380101152801d460318040b40182c11018151000c81c04a40102c903000c0c40141001500c81d01c2c0050911300d441503181c00b01c0e030341000c481c0141c40840e206800a00f03207911130350360180c100b810041064420b21814003082c1c02c81900c41403900c2c010240254046003848544080004003a00f031b9104005026080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 256577320 1250 256576070 256576123
    0x6061403150903040906060e0906012303090a061e05060603060d060b03010e160617090303060d0f0218071806120e010213081e070620160b040503 64
    0x340c01481008440072584007a1100b0504034030754062038000f001d11500301900810803507801900c003c00c1510494408600ba2034880040d00c01c0380d20120080000f290031400c110041460310011074201d00000b00302c40490350140ca0722022684801c500d8007041030895a13840caa5100da0144540002080b1120b034a0741c280030002501c1d20305441070041c94961111140c0e04269429440480314030103c5060722030b0240070045498200c1c4d040d018210104040d040c03120810021605054031545024004600d103880c1d40d030421008084c103100448403270090820010058035201100314400035542401c0500742023514000d890030ba80e2110001c0e2186449078100103840d880032090000007844480060011580600640039104203214820260402070700069484400100e9141401c0380c510a00186510420340d01d03160b00252180c0320001da28060901002465415404081176010302242c09507505607216041c000c00325441054071003030106007004681401c3c0050301000c0e5000710703008031400b82d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 256578570 1250 256577320 256577323
    0x50c0403051216030e03010e0a0c090606030203090d231c060504052e0b030411090606070b0109050c04081009020108070306081e03070b1006020c0108090c0f03120a080406061403 78
    0x20030402404021170716120510a8400b9406158008040d00995103409860708103007020a680f481807031451460400c002a103907103b4420760340944030722009030468400d8050201e43c04000078009401001e0360340401507100700d42c075005141244801e000510021541d21540b001c5500c9035210a0246003031100f040006010940020404d40c0e4a846c0f10b400ca0459083c3c46503560b00a402c04400010000144010b0005003100340d00040c408a60b15003640d0f0310042400040d014880c1d00030050703000b15006208600c43c6800007070f40650300d43c81c2203003803556600f035940c90a42c0c15442c40e20065650402c10041d564821181d66000c80141414003440d4a062a49070340c44010348040c1131103669014883c00c00b01310074011250907540201c5051120f091480032000c4842d0b0612660001d40320b0880c00003803950103848514810032654000e0854100400180440e8981d40c40e480380c0d146c001e0720311452030403c1c80f1010301001c0649550314440d500d007619003e4216412900b120a183c06c0e505603900040e40c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 256579820 1250 256578570 256578607
    0xb041d061c0620220503150a0c0509040207061b140f0904022a061b0a0503040c0e0a090201080604020906031b04030c1502010f06060f030e0a0204050c04030512 70
    0x80c00140081c41243c00840401e088a200100b0000304070700280c1c0c0d1803d60020500289010609007504519550760750070103684801d201e4100041e541030000081c032410303840e071100302c2d841454204503107400c01c003900040807688280c03001c40c2c4481da584002d002c01c2c800003500700455a141e040c14010010000100301280c02800940d107900640054421216107070382c0c040e600f81070700405490203803031841542e03100e0320708021908290a1240000090301012180170001174400b503410344614004007071404844940c00244165254032110f0760003c0c0000079025041d2042441c040001344010316480010001c0d207000d070401303104030b0050029140c6a900c01c0212504164203491101c4c80e101c0c3c1135040b555a00071a0300280510f1100030001625601e901c070b0502040300703a0741c001c12007403c0809803c01110341030301400e4001042d6110f15908280260301c144aa00310302c00c101c3e0f126440c0c0340e0004042c0c2d281294072564000c4042000c004000f41048010407588031411850300785001000c22440800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 256581070 1250 256579820 256579823
    0x3060c041512050117120f0702010c110d060501230310020304031209260307080711030c010e071706070c08031504140603190f0204020d02040b041d061c 67
    0x100d030000280711070301400d040340c12004030030380c00d1100d507943d9017042c454000001009445409000c000c580041510021101c403042d400301705904040241d0011204000d88038000c0300d4800d9141d107401840d41c2c400c07100d5402c0b5440340c280421150304000400c2c001c0001c80940302e641b0700d502681e403011941c0c00325a1400c0b00c0800b2a00580382e07911410100c0e620060f68190f5100705291030b2401c8140144184148600120420241c5600002c500c038644548401c550010008600c00041032003030b0310440c0c4c00440c9991b10320403079080c60f4440900900311403d582c4843c00c0c0c0c1d4400c8004000f0300c0310b1425a01c405014202c080e049519207000d01910f0341c070075024000c0c034140d00000002c044841100126044200160081203c183ea1030f00e4070340941020f6990350700ca8840c00520952000301201008495940041c12180c880c929500780b0019400c1160001c11440d000c0c000402c000a140b00540001c101440d0401310401c100c0303035440821300c000740500d8001c500302c0310b03413108480442080031080d6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 256582320 1250 256581070 256581089
    0x501080117010b0613050103050105010503060f0d0302120c060f060d0b01120204060e01151d10030b03190309090f15150201090606090f05010f15050d090503040905010603050603060c04 81
    0x590070044031500402103142e205511940c04603046030384101030124001030311002c0c5c0702004503903211801540e09010840c0c400c1d91164810030140d0b401d080000742c8110b101c1c0b20380111942003d5486001c00f00f40c03c042e01e441010380c040c00c10440355401c29559540c000c07005560120140045403194035100c10140184034103590b038409902d0442d225a4401c000500049042212a585421301c884011003410080000510000280c8410200c552803600c6511b4004240c1818504c0403070091700981489002150b040c0100d0b00007000c2c483e60030000d040c801d44607955220708582001c85000c01c4540f0450020b1640e4503000e03078440c801e00070b4071140051728902c0b17201c5413907151030800481c00340803070100060540d400c0000008080045130418500e185130a4000d00c4941e8071003822182031310130b0f807140041c054a00111902c90070300450080030014120711012505d80d0fa070f44c41700b41c0396a025502103043d0f1661140100082c0d5410300c60701e50002800c90280c01e00c0e04284c07910301c0080c0281d02482045 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 256583570 1250 256582320 256582349
    0xb04031404180608011b0909110f0706091a0105090103082208030409200901050304050307050a05150f0402010806060a09081911030703200d0501020d0605030c030705010801 76
    0x14408914240c800909810b2140030480e05180c0e03078000030f0191441186113540c01c04040000c040c885044100701c9078a1a5070f480c91080c41d007420040504030001004000410801c00c01e01d00035400e00061401d103002e044081509030b413034501310841c40c21000202c01088195001800543e5a10290724116500701a5450f00d0b00c0100318224503202d00ca50390010010751810340004d40e880048043c00451f80c2da00c004122540400c000525411941011074005031070030041141550702072030145400c14005c4049900307180d010b0b51107910700111018256100e9114110392a96058160005540450000e42041c03040c24907500180c24203030003a055911031503001c240c074103a2600c01c9101d000100600c0040b6001008450076060070104421400d8030712012003c0c1c0c07908207017000a00d40e4201d0358486559038a45041000001809402d07000503940310055608000103c0c0e02400a02a000c02080c00020200d01d070a0030186810640340c8214001d401c164020043c90303070400740742c604540d4240c0200c101d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 256584820 1250 256583570 256583597
    0xf0f040609061404140c0414160306030f0c0e010906081905160618081f020a050702150c0606030d140c010608150702010c09030807080a0e0901080a020405130b0403 72
    0x83c1c62034100312035070b0481c500200400d00c04814540c048041004094480d41300c14001808143c40d014122808c40a0f015800b060b01e00c020749109900554041c5000a0030f5a00e88d61000520401ca210585401600766414002983c408455a00501500d44100b01c900e19180c5106d40351040400c0401141d00706c40c81b0041840024030409845404142d0400900303522040013404c014003042c0441c03102d030248480810484800100342d0b00152070403e100e527101041c00d144d200607600c5501000200301c0140801001a00d9000c542040d550b80c81c0d060703a4481805030715407441c0c0140184142d22a034001d4140d4680c03590000c200c940a00003000e266540c0b103200f0b09007a0b01500c41544009000d104498000c21000044100036000d1035050b8001e000300b50000c641102c1c01d020b41e00016000400030403002c0300080d11040180101036070b1703080c5007036404480d90001708480000d90107181580c10500302081140703410b201e215403081189403809a031040340d469051321030304010700040601c03220400104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 256586070 1250 256584820 256584833
    0x30f030c0203030319182316171006031101030e12180a060306060509062a0708150c0723030c01090b15100e06070c15080f0f040609 58
    0x40310103401804895513420203010340c8160041d0808540800b920f0811444482c400080003440c0c510b8200600d42d905904003040b80c0500b00d21180c0d2450030b440b885045100c03101340307031401c28000d05904000c0d071049005000f82c03500b030191544c0001c408901d0108103100094014106000c16982803070000b0343c2404400890386491004003403820000000301d2003600090f100025800c1450003501c510100310f5440b05d00340e00b40d494071700810000c54024026941d4905020024084200b04a110134440305c0411501078980301da802c03400039150300080740500192408100c1e6880e011132101090a451030b04510070350a50041e000b00030401c80100f6040d402840f41a00d801c4241204001a65916540c908209008007041c91089409100c0f180c002082c5201d0f903050320344140030207417540d19411100c0000300c8600320f10301d00f0243e12003014006080850706114604010300341400000c2c80f84140d006020749030300c0c80108050100c904240c09c01494000302141e41e80c010758810408294042640b400c078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 256587320 1250 256586070 256586087
    0x1a06010504050310020405041506230904150f06050405130f0905070b03041b0605070605180a0b010e0a020304050a030e060d020c0c010807020f2a06040b0d0605030c0109030f03 77
    0x3070f40c580b00e015448a12074a241c2e0013401101c0003100c042052081c80f5150a0040000303202d040c000c00c42306112901c076030080c541c50091104201002a107440e00c4074001801300e5003490080c1c091040030341d100340402c081c0000c40e1406030a05081041c10a0300d4500001d00c0b10542e81c248080d0151a1302600450310410740240300c4140c2d1200694a0254480c200d416068004a4080d5001c00c070b0b24031544c40c0e414154034a04260f41040e50390710715061032600d401000d4000586102d207a10b0b14004100c50071041844814030003449a4280e00c003d51500201514080c005044031450324810824070001400000b441d501d01681030608008046680c8001041402604142c811244c000100e11403450004261810300d02d80907210740c2074544891000302c1e03595030184902051980003c903c000c0704011108002c40f00e0094041c041c4483c524400880c000303810507808210300d000701003507d088510041c020540030f0041074005056040184000801c640e00d1840090050001038021106161040307481303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 256588570 1250 256587320 256587329
    0xd0c060e0303160e0901210218070c0311060f04020d030e0301062403050423030f1902060c0304030c0605180708160f0506040b0f0d060306060f05030102071a06010504 73
    0x780c0b80c407860100580c0d0f002a0700003000b540050030350035180f809454410640c9050ba00f011480105490a0100d440806450b440701680d00c42e51101c41c4000800c80c0203000d80c400c1100d591990000c680d24580a0030340101c0f81d41d2300090b50000e80c2086440502c0140855229404560441d04920300c0c0c00d0503103140a00070742040e007550800c0004034038406037038100b0145902d46c44a030030141b903010100b101110401d031070040800d0400d0034400102c0c0680e05200b4109007001e4241c038600394050712084102e40c400c080844045417000e40302c44000b601400101e5000c000e07017014a10314a0300345c1d0300900716060241c0081105a40304041050076a0f0f0110758003684680c00e00b100c4405d603d85a1041d62541140044412050920004a55030110b4020101181c10150805d8149400c104404c44503400c00800c45160700c105200c84604905140918002103000d280b00045847c01e022801c1c203440c8207900100e01907801007154400041c1d44022010680c1101490b0002640301e03040121410721903540b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 256589820 1250 256588570 256588573
    0x70809012706020d120513060b0a0f0f0f0501020a0b06091017060901050601021209040203070311040f09050c0c10150f0b030a05060111070e060a03020913140f0d0c060e 74
    0xe020070356603000a02c1c84946441c0d0f0b00d400d2445c80d040031050017541d0003150f41c14014034441c0c1c40c1c03500090250b040300200350300080c140c1c03507203a8a48000020880044c2e000c42410040724a040125002200c00000502002e1000d01080c00854480303496013030780645020b00414034080090680c856400303406001c1c2c20443c080344500780141d2100c9546550070345074585603501c4c14020400541c0000b400704040c1b400b0500007420850038100300002904014a00c83c149511040e0307809070701034108010300191102000d00100b0320704182d0340b042201c074020000e200c408030401c404004c100740000c030000603401034000800c544900d2000d0320000100b90340552800c003442c1801040803030300c1002039441207500746402c020b20b5407084011074904280300f02054091300040790074041402d820241643c000c9018261042c20340d83d0781e01159a90404aa004034201c40c4078410204104400a000304016425001411041808120070352184100800341c0c091210308000e401c04c02070280c011003160800c410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 256591070 1250 256589820 256589897
    0x804030518060f03090c0a21050c10021c020705010509040506030a02090901061a0703090303050c1906090203100504080405040c0c15050f010608090303070c060e0a03031e0207080901 80
    0x882018803500705480c030120074000c2460722561407c10140403811514214019114000700000c04210010154011b440350300032184c080b88140c9901c20000c440001641c000c020081541c2030b0030441c0c2410310381d281c3c115080580104041ea80c8201940c0948000b01ca00084c0c0d5165207000070b251000c0c041000f90410000420800c0410044d403002040700d00348000089488803075211442103119901c002000311300c80c00010b0000c40c2c42400a40055076143c012154081d441c103160380c00e952412003044880e80c2d1118030101c1181400c1c000c03050700c0b1810700d41c2070119040c01d6483c0d00440c0558064503004950b04d003031071884039100b49690422250482e1090ba0301d0903c7c8140c1401400d03084401c0081402508000a500752292a03514450040317903004e5401c50322604411520b1042c12041914000d4032800c070013451203428003042f0f2415100362400114440d1040e44036587d51580002c0c55199032043c00341c3d13804101d941742186c4103403009281400c13908060f86043c200e11040c21f02018084100007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 256592320 1250 256591070 256591087
    0xe06040b09070501020708060a0b030f0a15060e1605090103021309060801060e16080c0d050a0b0306150604030807140d092301020c010c080c100207021f080403051806 73
    0x140e004a4900c025552400c3c0c4070b2005a0380c0c1e45a030300c5600ca0365400000004c2085046a02c6005c0d03081006054510028a18544514150f00c00f01c041c0c4510480c440c44961150540c030402009000584900d4824030344031111a44901034490341401380840050101900d82c481c0c1d048400b0a90305030715911141d40c0304c040000040c080c2e4021266190b10f0b028001c034201c50308403241c0d0720807490351140114202c1c10060803a060b85d0060600d00e162710052207032603240102780c001c80e40700b910102000240381461400301072414401900c03c0d40000c0b4200f0750351019448800441d01525001440941e8134074a51404a8440042ca103a120440c09401504410305900545850840d61140070489019070301007411079142c45c0c0c000707029001d82e08c40f0030800742c2035001345011442640179030011801c2060036240341c1d003064540042110203a83c0003d00b041107241c2400070000c1d0b0345011200c4100c000014401800c81107003d0005424014042000d24184000c000f1402805501614998482074003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 256593570 1250 256592320 256592333
    0x40b070809040e0736020a022a0109030611040302190303140f041503090206040f030311030c031605160e07121a060a0c050d0f090e09030a120e0604 65
    0x41078038510650a1a40d100104440000d443c0240d5820421922905030a1500e01038000c1c041090144945424403009000110510241c000340c0159005001d01c602e10103207180c0220f04503111107080180004551095903403003011841076a40c0164002407141c9811080c8005010351341c402135010aa13058040b84400c018000081140d129885102c0c00d90024001d0070b40c2400b034408402c1408a080c0801c016a80c500b4103810104651420b0005610040c3d401150043e841a000000f040c80900820805c06d9482030035a04104107071000b950a18002c940995203920403494006004154001000f0038414140f201a04088881c10380900c01751303a991070800c0302ca4044604002007280e482c20404041c15074001c0000300701450400c0b03c5c940160314100001900900351103403c0050100300c0b4000198100400401101192a1443e5012031044010812505608000000c01880e41405070b803010000c10f8030302c80046820b084a005800c007449a0013000c1e0101401c83c49d2003507109000c01c1c0a00d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 256594820 1250 256593570 256593577
    0x1713062703080f0613180606030804080c120d0c0816050d0e010f090504230c0702040c020f120307030207120e031011030112020a1503050f150105090114040b0708 71
    0x441d45882c4081da80309185800c3d001011100250080001d0103101356019003580404035102241d56407070401c070f403540c03a020f0032600d090b001142c80050010707040c041c0400420040c0c0130000111604120540ba10f0210750f121016200752a040c0089203105a042014510070344041c101881c10b07013a120030184c00c0c5907503280003080002e404640090f0101c0c185500c01c440244d01850035403990824680b07408144802030000c07072000018619891741005042c2d048079421409209404046901c1d4040c5004000846000d1441311096501004000d80030382c00201d45104518424081c0545a13900c0c188190060b228202004002d03008800c441648640c12a0250700b240741c041d021540101c50115400d02100d8002d2010010f40f50144010882e038400d14000c42d00307062014007410051590742c0000c46e104c00e4200c000d080420340710000c0200140c82c2c5000a6440410b240141c0210000720001030542c0c0300d981c403900c0c108030706c1901c20b54606103030604842c0245503080d14183e81d40007a0406610640 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 256596070 1250 256594820 256594823
    0x5060a0302030a0c0c050d0f020c03100b040b04090b040b070c020d14070902030702102c070303120b0109140d050d05071403031012050f031606050717130627 69
    0x51400a000c1400c510405e5180c1000e540180100b00d000800030050f140402104d004d0011407240c4204203225840134095121454580400130131400d20071030800c000c0c2c801102d1840c0c0640d00d005078106c04100600c0aa03600700c3e0304810907843c40d40320010125400360a03e100603402a01c00d0344298100001a00e80110351a820300a540743d82c1d4681400c03600342e11041e83e022005034000301000103100b540d688115000040ca603080005840d0b0500ca03c640000c00e10309640054020179820000c0c0b540211072001c0c44000c2120803c0300d282e150300007a0450f60f160150f40180890300c401c044c4c40342c0728002c000511542100403504c0d00b4080444c01051070317100c00011100a401e1104d00c98094030008140c074050055140c00d10350b02402c00c0400003016590103403d41d0076200c1c4a0700b00240b01420710041050441001c3d181500f10f416041c14815242c001d0410b104000c10030394078025008108040791703003058004e0b0b040110301c03a4504100c00035000040c0134155940c800d41101c01c1c00092030200030000c0c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 256597320 1250 256596070 256596091
    0x3080c0c0d050706030e030d0c080105010f0912150b030f030307110303060a0e1009050a0504030f021b01050d06051e030606090c0d020a1202070507051f050405040902060405060a030203 81
    0x4400409001c0118074a2100400d01d911018051110b58020b41101c0d04442c0d8000880e130421040310904130541e124400c907903000c01c0300f0100500c00d41d42d000508440c0700c00d80381094001185801000031284122503800761148040c80038041020759141c00c4540b8100c0010111221000f5500f8026220f034015249200851080c0c25041d200c03070001f1080d81d20071030000380341009862500f0140e548000c0001c00345170b0580c105410204600311944280b5004201240c4000760a16152a01030420803803010007000b550302500c22416035404808503004940420311380540c03118100f01c8204041e000d19000990700280c0c0842c0e603040c1a411030381400030644102c080b600d684d20381400381b02c0c01700003c0d2801003c00c901000300740403946254009001d0100b9529000919005580060702242c025078002c40380b07a00031040800140c9411552060845091084c80031a5080d01002904610440c89524003a90701d4002240c20740d681c2205440040c44003610f550356410f0580c3d8010003c3d40203c5145110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 256598570 1250 256597320 256597333
    0x10060f052704060902030304140901050916030c03110d02071110050304031b17030604050702010209060d0905030f0a051210050603040b27070612051e070e04050103080c 74
    0x501d854400a04481c407084040320900d4a80d00168403003180007001542d01d00d8641c804000140c804000070002081e1540d1843c40081e5060308003c0e85180607840b0b148519940020b2226012070b0566070201d8003c1401e001030010040e00c000d8000d403070b82c5894480301c1007010400741400b11082c4c00418980c0d02c50003600680c1d0000341d0030052442d4045201500054082c400a0000390151101104c040c00c0d0003803051090b01141d40d0003103d00d406c035030400380d170f80301c00310a0050354100b50103078640080c1c0b2400290306003110080404c2c2c441c00b40a0070758004603101d815110074454240200d803070346510ba0700031954031031000a010b45154052030000607043d20103030010b8441d2800001c5c40301983c0c001080310303196032529220140d044102505444480e6020110200a510f00c110b090500c0b184101c06070030818030f000c10240c030000e03841421181343e5040600708480d032048200840210103100802c40c070a07469000003100c02d0b01542d04100d401c64540303000403050001e420060402d0a1440044565 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 256599820 1250 256598570 256598579
    0x10f150510140a09030203240906071d040f1d25030f1a010915140a09150b07050c040c02032b23070f081e060a0810060f 53
    0x70324280300040d02001070041004100614034850051804501600d031264a0036141c0d00041c0c01d014004441d60004005441c002281012494850341d00450020145c00070749448100a003105409000221801030201d9000d00d443da80d030b50003041d920802c09020801405801101403540c02841200b480742c1c480c88801c8840340c048800c040301d071041501c482205d941d18581e581d02d5961f5441504456500c1d8001a2a60308402c440c8010b00900c0003604c0414000504020010340c1c2820341c1043c2040b8440110460b195200c40c00c000e0308480024a001520306d60b0201101da1401403600808910308000400c04188200055140e615045c100c0d0101b280301d40720503051b41c0d00d105840b89000201180e6a503004607500b0f600c08440361207005140800ca540300300c1c03156030b088056944002d4885296030b041c060b00c55808100c1c0c81e010720b80b90a18080504049140103d420190b02c0808801104000090300703d481e01110b100c000c040000407510040d03514104e100c0a045913000e51001c10035010710016 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 256601070 1250 256599820 256599829
    0x305060f0103150213050d26090f06030618070503060109060504051c140102070303090507060c02090a021e0c0a050d032705030405120f1005071e090305010f1505 71
    0x6049941c03114001140032000b00f403c0020f500041201c000040d1001c0b4001000e4403203070502c01c001071007883c0c0c450f103050251440d11100c11075210a1100714205001400d09a01c0f2082c244540042c2114820740300e81d501070004668600032190341d00e160500302c041c000981e420001135409040240c840f0010244c451908881a001c0d5111b4258000075510041c2d81140030a1005081c140c000c14054040c80c0a030004182603070301a8408030f00296441d20842c0921400f44041405010039103400084031004d500000c1c141200a01103000040c0c0c006001024501550304205100600480c4c0c545c40c2c8146c810743d1501c4a00316001920103000c1c04401841491191065200440062495110380340c90400c01074418408410100c0e42e9110400004c1102da40f00d01c03030102103007a100700500c60300b008403d1082c1044007201d4100c0d2114101000d003c600c9412841300c0d00141c8554210150510714820100c0d6241c0d03044d4400b420951030800c12032915034090f000b141d8503820140d00002600d54410601 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 256602320 1250 256601070 256601101
    0x4110a120b0c03060d0b04030216080c010e03030406090e250305042a090207030e03013603080a0203070c0b0f07020f16060503060a09021c05070507050d03020904091a01030506 77
    0xd80d4044455013000340011b500f42082c0b9001402032040b01c1c0d4a0b110002c201000050603004000c0c070b03602c031100320305481d81c0c0a41040b120103000c1d03000d0345c1401c0c13400c1000f500324115409a1180d00b100030340001e090401303000e003104c8403030b015010200038494940800350007048260340c1075580d2443c40100280804020900e0319201e0341101610000c41d01e0505400029001003070b046040042540c84803200c0d607400d018611818400448a600b00c048031750014050341d28403000d0400355075010550340e02182d04100c1503540500c20200250346d907a00c2e2001105d28101d401c400800e814010740502c110880c0e0309403414401c01c45074003118a0912420311643e91441d501120f0300314610b0301c0e44184000c5100d00d018580001e8080d2601d00a640c55541d6502641c00078070008680d2101024003520042c968011940c0289160420a10b80b660b15141d9a071200c0460200d00c0c141600010512a580c40d580c0c80694456040710307050b1800c0c6048145011000e0b020b02c0162060b11401010991410110b41070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 256603570 1250 256602320 256602331
    0x60f0a06090e120a0908060907090518030315010c05060a06090608070b03061207050d06050702070504020403020612042d062004030b091203070810060e03070b0304110a120b0c03 78
    0x10000b00f80001d0020040c0d0340300d4426a0100002c1000000e0305400800aa42c01085003501500d401800c00b52150211940180511840914070554130004040801201d8000e01000d030b0040200d4001001aa40000301400080641c490301c420030581e8607203a481203041c0c0b80d03882005d0001d21342d206089551120180600f640c0050b0400c041100c03460500c441d11035045200055410700c0d41d036400014112503814130262038aa0310741081107130069052000c2c0015100031102141050700396004100d59004101c03081d0310110104001c1824410b0000b003925140d00d0140c0061075a40340307031131b440c503c2c3c080481c000c40c0d600d400d01d110324803407610240d02e111500d11450950f9041906d5602c03007040080020b407444400d406500200624040210019449000b46031184203031402c1102c0b130f5802070121076002c3d004125800d0350327282c503e9402080101c11903580c416803903280c1d20780b03007050580e01c400c07480c050754000c07503540c0002040da010302c8042441c54061404510552b84a074400182840704444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 256604820 1250 256603570 256603573
    0x1a130629040510030807051e0d120228050d0534090902070c0e0f010608010b090f1e01021014060405040303020d15181b0c050f060f0a06090e 62
    0x140c09400c1d06055010503804090fa01c0d402094950300d8845188a500513041924070360003410410ba9005026600c0c14010050f000c020503484a4201d0000c148401400c040032041ea0001070b060301b070380e0707608821080c4c090304002910504102c541c40074140b43d0107400d1170407200c1d003010001080b039120401e10109140c0c441c058842d08420621890009030910300600e8203002d43c1c1070340442e8a0f035442c4007a02c3c100e40b04127948072019081c000d144c9198040240724506000100e030040c0686640801d1007070459001d5122140c40d82651400100310f03103401418207030041e00c071a008a10304041c100c0030000028080e001c2e0303400c0d01000d030701d9002640d800345610b8941c0c94501e4042901c41c1440d40c080d503132050081c5001400c040c041c0601c61f058401c00c124031343c0303555101a024066085441080030804250701410002c1b0018089840c020a41c44c5c071a150600400408120501c18280000340501400e84150340d007034030341504034001801d015640b4002c50707881e100c4c0200700300744070b40304410010107a80d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 256606070 1250 256604820 256604891
    0x709091104030f080f0307080f0a1a3d181a0708160f0326040f020102070f0815161710050301090506090d03090209040f1a1306 56
    0x111000e8030983c2034501100c0703403038007004040740700b101580242d0b0050120341e6038500035040c0b9014088650001400c4101ca0380c0c9410100c20660b24286d0b0540407450b4240e480041070101c4011078850140b40c40003407005a010203030060001d8540340380060042c8066100c24000600b2403801008010150041d020000e6503030480740018050040502039613403040140c1454103031125000e2403045401c120031207584052810010406402442c0058812160172100c00d5a02003200c0001803944050005020641c01c03042a03015640b081c001d54010b003c1100b044006aa40c5d02c00c0141d444207031072007254803909480e021032a00760549814488000303090f07a414112054200303e090140001509220042c1040380700040c4c681ca080c0180c0b020b141c040d2018161518081c0c028608002c10388450b03004051a00b0400700c010780d43c3d00c0613140c1054004000643c45c401c10714100c002e2240c03c16050803c42e422104204070078440c2141c0300c3c0078503c5180284403c151100c4400801000b01708900179140c52803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 256607320 1250 256606070 256606073
    0x10504051504260915070201030609050601230702090f0709060519111e0f06060a0e070c0302010e031201260c04111903020a080115020d0311090306070206070909110403 74
    0x202100e94202422954071842d254030000001e1403000b107141d000d03110f58000f180c06d006560301031207040024120200103104a2504100080c0350300700d181084111060610012503540c0400810327504410f038050464405800c0103040000e40e000100c82c104001107980d480440c240c0d00c9a415610084040c00002003184250801958030103003820f4030b0444e500c211a401d00c09490300d400b504581d05000d0001e000004031600b850340c00c0403170007800305000d2034076040d080210048410b00d6035880205882c00180d10001c1d440e00300c1c09040840b540c51014030022a0780d00d01c1045c0440440d04136400340e03010100018017000031103036402c42c92290540681100c50f64210509182c1c00a200c0c0c111040c4107985080d40744050403400c400c0410707803200003950215402d1102c0d030300b0030041070242020504010a8159229000303550b40b440d020050101516480084501b02c035010598032002c00050507034400f407401c50740080d07030b90000f02c415900080c0c2a0400003143c14251103110784800c410b0400703d26007800c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 256608570 1250 256607320 256607363
    0x5190503060f0a1b050301150e030304031205070b04120908151f0b0d140c04030507030305090d0f0311190203071202010c1e050c0603070e0f0a0b0a02010504051504 72
    0x20710f140622615011658002c4086401000d80d00e0656202d46843c2e506100c04440801000d0031800c0600c07076042c040c942260f50000035601125404102102500c569820446640c014028000c04081030542400100700b54500c141040b12441d56a060440340d4800440d0794444605420100999540d00450a82c142c03143d03284540700000c05010f01d03607585d41c0083c600c5541c011004031006941c2c0703103003001030701c44031464264006107030070103090405065403116511050701d444010180100001c0c2070b6659115208070300051303900481c1042202c00389042c0645a68400c0d0f402c81c1c00c1c3e0244034900c0400c10307031304100f02d1041c5402400502105060006c1842d200c0d06a40080c2d0500c403100f200c450001d400b000f03440440311800540003180c0e0305e45107020740c42c0c0551910720512491003401000b00305948440304081c0f1190499661000000270700101c0d22040e83d64000c46007000d4000b034542411030301500035602544c451070407144010010b00000349207501c252001400c1100441809805510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 256609820 1250 256608570 256608601
    0x50f120405030c1501030605011401020607050904092a0b031b0d1d0f06063c0618120303040209040b0903041d0403080f0c160c0f09060519050306 64
    0x8103604880c43d00c181142c84510303101d6041c0700f45400c1c11040c4014810440c1c01d001c5e6070f004000040200c801010840000b030745550008209404114001c1180c1810344d595400140c61550401c003441303035017000307180000615540c4400206841c4051030001400c41142d00491f07103d0034885071080307011304880f0340300a49030384010f0100748503948030015400340340d00d05074020444c42c000b0701c010803100d0f083e45000c5050040c0200080e2040c0c0c843c0080250800080140542420707152440ca000095034606545149031400c0170144c01034004144e443c0e0081c0e0802c1c0180c90ba29003100d003440d13a00059506075a0368442224001e4012501d00d0228000a1100e24940e07000548401078a040c161103608408043c0d1080c0071211220650344140001d154012466035080130903244030100901d40b08032844090b1140803c0611000c410710080300500030007446440c05800f520714a9000240d5030004807000d000c05001c0c4910a0b542800c40e40b20b440034400b40e800460364094040c01c980da9850424200c000e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 256611070 1250 256609820 256609823
    0x61b050d110d0614120109030806040e030705010c02100b0f060702040b1203030c07020906010807090302011101090c230102060103030e040b0607021807030b03070308030f0903090a030c0303030507050f1204 90
    0x240280700007030b01034400f8002c4802a00c83c11819041203011002000030145600d00300c00016490b164072900465480540198800740c1500c0c0898100309040d07400b803540c8980c0c04060110b510b000119400b00c3c0d80494000c0d100b6074100400d000c40c041e4281008250410004010360043c4108051401410035801c54882401c005050f400c94001051710035055600459181925500c0043c2c1e603811445c0950540ba0400d00070300e01185d0619003840c002c0d01191716800f01074140079058a0240081101b504130b03800c25948040328956066031002200301101d24411103500a4a00e031260048039440000c92904890301680ea82518880001c240401005440c0515400140c10031080003da2541080e2034804042d02408080910b85240c0080444075200d11041c070a800112080001c5a04801500d400c80519821211310f5150200d00a195200da1098290400141000001030050500591084a001c0d031030512040e541c1c50303c125800d11980072504c0c4041c40c240102000d07006210010303030780075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 256612320 1250 256611070 256611101
    0xc161715130c0303090302040c0c0224090402281106010b09030106090524040606051209031b0601030605010f060f0c020a09020f0912030703080f0703090f0609061b050d 74
    0x140e441d074980750098410b5800a81c0440d01c689000c20450402c1d2107003170b50038600e41c0382c012000c40c0705500141100710285481c0c02c1540740c608014007014800c1d8212441c0d4040100219510303000b400d40e00400522014080004203003541d50b100d1000c3c01a12240042c4940340c020b0302c02ea83c00c04a0410064000c8400550159039070030010941d0795040c451a4010b51406a1a4904400001c0546071421407000c9030350281d814038008111032500182940c090401a2408842554132540c1d4980386010f9407480200301c0400348514110480c0c04a0040d050341d0003588240302988e2112004203552403103200348000205000c44072130005200e003c441c1c00080c40180b01110041c2d8512500b400d0ba003003110101f0003184001070261183ca8000c82c04002090800301460030000c0c2c548000c0c015005c0181000503030304404d03000032007e621903440600c80a0303125080307031540842c44c01c0c04070084c6035194080b074406103040c0ca129444242404240c4480000b90b40b0745180c9054101c800000d4404e101405168 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 256613570 1250 256612320 256612351
    0x61507030c05030f07080d050a1104151107060801050915011403091c030f0b010201061202040e12030a023a0c021501140102210403020f0a0b0c161715 66
    0x1070181c20343c020208140200d0300944c1f500b01e03c0242a00700c0d48050000751480d46080c7c0c1c0c20814210690541702100c40c000360780491005c80c0381e030aa450003894250581c170341c029001e0215420b41c00c80b9455050752010b4a4421183e07540d8100085035164880e092400714442c035810f4241500c0d00030007582e000017030340103603181403a0000c0c03840031601e10304c1200c40c013194445503c2c003000c0d1241d00c90076240c0030b0244003d101592801c07141059a0410300340107801580c450048050504040000021103561281d855a5034034028082ca0020b42104840700c0c1403e20820b689440074018007502d9080f088140c14000a0448200e100e000601d40f0030319802c1503001d29204038000d400241190b074001c00038905c841d1070055003000024141144001c07100271075481c2c141c0c0380b40502c0d1108292000d4079030590385e815442004100064004929a0145504030b000046c10090420040782491280b16540d00d210469503c600380941d074031203240404103040c1d1016200400b03a201c4000f034940c2090107054500311 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 256614820 1250 256613570 256613587
    0x40609061a03120f03130c0e01030b2a0d1e061404050c0c0a030c081e09040605040b010e01180305120c0607050708120702011d15061507030c0503 64
    0x1680e240c50104161a03601042800c1e072400c2c1030181503c031500948010b440c1c20509030050066000213490b2141e01054148924104400703402c001c0c001e440d451f04990002e40e942d1429a038200e608a0303a40c4100c49000c030110300410342e01d040600d403030602101c0540c1000395140c6254010510002c05810109084001d4076080f00d1510884000d13080840700003002c1d140400920054400c00f03491a038081c0300070480380d445840d01007407060401d941413400c5489540c0e181000101030003104250030b0030104007004043c203000310f0381c000c004445098801703001c225a5801008100e903644070f01b1070301158801c1d000a04a610440055465107415048040c006442e85c90b446d181c49150f00e5159608103000403644082242040fa2759840388241c50000c0c58810240c0d90410240182d2696003a542c00380004124060b000390040c105007681041c400300810f464482c81981d030349a4000e02880c9410300c030089030060502e1f0301040d9008460068041c54040145d17070890310800342049c00c0c0c40500003401400d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 256616070 1250 256614820 256614833
    0x1080109020a0c23010b0303030717070203070606090e010f0b03071a07060203040318150c1202010f0e03130911040e0402011b030507060c08040c15020f0304080609070614040509040609 81
    0x3840300144101404a04200e195201d0840f80486c0e50365209520500c10071240540c00320001c2201f400e400f020f03040f980c5507140240d16501468400806c1141001401b00c1c07101c155520254868003210000c0c000d401c042c1111400f183d070017406c45500364000000501010018100c03200d02502c120350014030f8089191207880c102d800542d030072000030b180c00709080100c01d12540b0300340241c030807850034854191100c3d0000d0121149088001c0021540809c1c60300301600030b502030061400980000e010741c400324201d4075142d9020f640000301e5040c5028021440c10b846100d55107a042403c0c2c001c41c60182054490042440300400032810460f9004804a0a41c0030042000f021442070322031030b031070340c2e5185002820380c0e500004c0b200030415a201001b0124031000790031011103442c01b00704010307404000c0e01203041004404400d030b4284000540001c004100040c07040c410388040e019035188585849003290004541d4144010f828024007042c8828a0411030440d042803144600080307403c2d1603503540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 256617320 1250 256616070 256616093
    0x902210c0f070812010b0c0a020103050c0d0509100507110303011205010216030305010807050f010509040903021204030b09010e030313120306120501050603012d0e21041406070201080109020a0c 85
    0x2c031040040840c0d103208198001d004d103409010221b02c45800c0552040740c2c0b80e501c0c280da4078040e04268448010510601c442400c0320044800300d1800d0219103049009170707070f03101050444030990303a142c8000551038604c603040750074114408070090752547c0d00c0c00030400d821140340d000682e0155820003035a201e0010364042c0f0503010340700382c8010442d5807401c10018105100780c4d01450103590000290b69940e03038000c04480410f201110006807a40b09401c049280c441c0410985418220008003c02408038400416100c0c9010034001d001c0841040d000e540caa00040e82c07209a06800c80583c800040d91034102220015074901e070015001c1da540d554014040b0b4285001d075034a942d100d090080500b008c0c01200f18204038441400f00c05681d2032035072800440f150120680f1141c1d621450030341501c09011107466155120442100c80b2109000c10704c0c0c6038003a1242803014140b1414915113420584244c952458050f140c000960b8038180c441000b030350000750120100f010388041200050703c0700048 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 256618570 1250 256617320 256617323
    0x100509130e070f080601030b0f100b030c250c0e190504060218040c0905060c120a02060106230f090102030705010e010c1b020d03030b1302030109090308010902210c0f07 74
    0x2c088252a0201c2108803580507005004581c1094006002059064003c985c0201000c00409030990364400e848070011105d8011840440000091010241086000d1700001d113000c4080c2c545e480768030404041901140c10004c000c0c4a01074000c2007585604111643e20005c456405604628040e90440c01c0b039004880840d0021703804070300c03401c000c1c0346d00341c10204846040d9000c0146100d91a00640341300d0083c400c45100358400117407042602401e100c4006a2942914480d031200142d542c041d480e0503003401040300180017200b04000b480300490103110f01d020304a10740e0f881c100c644040c031429a48a022100e0651008101d0303480090801d2048420701d80c0508000150840f084a00418509003071540071444803541140d1000344c1e0340c0410b03125501313a25080c001049a1841e0200d08441c550004000a15202000028501c440c0390000c642051280d543d00e003850780c8500400f8120700500d204064550761450341516104003641c1c110790440400c8851a003404030390000c01d012a8400c110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 256619820 1250 256618570 256618573
    0x4020f1c0f03080a0501290c07091107021c030e040b0a0e040b0411030c030c041503020a0803030103031e0806040b22021903140f040309030c12020915100509130e 71
    0x2c22002000610417680503205041502d44606080c2042c0140e205c0f9202080c036400d40f000a03119056102004080300070509120b050241007804260381c01a071304506400c3e4010b0f2480c03c2d4990704070703410f1000181c0300366050300e440c1e04d20b11301c040a10004200c44044180c01c02c1d125a004200310000303201d9503104038410404160a46858034043e02d03140701c42881c0c940240d01c140ca0b00c8442e59404200d00a100780151000039000c03e80b80d01d1100e0348040f0f40c0c8083c1d041310001002003002c11020009505903400f0f03440f4410b01620780030130000181d05040002d000107802e03101050321480c0c036403c08001610001c1021000500354104880c0100d180030440c0a950384c0085e03c406010803101d011040c07507266060800c40c00766049050089504011304030301c1c040413007200040800d0300034403c1101441d00060308841254680b0b000743c20000e251a0142c1c0b1482458001130200c3d600c418203242d4000019004032003250400c441559076070094501c9075803220b00018840f031444a070303100e51050542d43c0300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 256621070 1250 256619820 256619837
    0x307020a0911090603090a2d15240603150f0308130528050303030702070303050a0903080d0b091b180409050115030b010f082d0a061a0904020f1c0f03 66
    0x40c0c4008c0f074078011104d0f6040070500481201d0a04202600d0761060f5400006400c40301d07415508880040580f41c140080445051030400314400c01c400391142643d003107490401c8000c40c043c1c40005d55012a100d880a00b000245007400010780a8024001520b5800d409a806549490004040718000c0c03080c000184e90f28044171800305d8503040458000e02c1c095014520350304160700300a4480740b507408081d051041c00a42050501c2c444c5080c1401036030030207086030316010b1912402c8003620110024900c501070b044041200c3c0001e009036100c405200589540c5040500c0840d0f41c5940072355009107510035a1000e5480100303c0a0041c0a450360f01c0082c561440307425880e090406c1001a08110b15070141c42e00107000c80500095040301405000d020104d0700c0c1c460109800c1104d2100c484d1607614042e00d1060001c000320ba0b00030482415511041c0404c601501d014400c444504442c003961003118064078120724204000a0003000201382c85c41002030045449031864100030a034100c00280541 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 256622320 1250 256621070 256621073
    0x90510021c0509060a0c020a05030301030c06080705211e010905070f0512060906060403050f0615030f1c05040b070312180f110a08010e01060f080307020a0911090603090a 75
    0x84a07100209409076401c00140c20150700843d5503240007040003a80ca5566040e081030076008029006c240e551000449980b90313100e180c13814500d407030340c4601008100404080b0380e1090050090300c005511003900810340751a10f40c2003402d0341d200030702030b40000c0b01100401000d12a01d4104c450280c0000c3d500072605042c01100200024101031090b01040300c10700903001850514681e881c2c1050003120712100c82e48035400002c1c0300703200e6a8002000c51081c19440d001c11503010401a11413122280b00d00d0030121100107050300c486003030700c040b82a80c109022460100e603000340000e84020301850242c0c00e094540e159154180d110140c1500420096503020203510100d004e00b003003c220201060050618960341d40180046c2c0b00001001e01d52002c2e20f54081da141c000c0140002e0480e20002d2200c1350b1003004d40c6000f41041c0c001c09074203c0c0e20340c1c000309110000008595801f17a01900d800c42d09450300c4007803001403510100100324554204418400e41da25403019500682200000d0000b246c1c41c0e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 256623570 1250 256622320 256622347
    0xa0309030c0b070b1b160f030201240306021c020403030203070b0a140f090a020a15140717030a1e0c0315030b0601050901030207050f071e0e010306020d09051002 71
    0x80b9406208418030030032540e4001149881c24541000380391007810080a120203818206010300041901c00c400d0040c1e2140600112102c1c1e803c129000c0e070020004d025880c00c181441c041c9560805841e0f12012008100143e4980d000b04075204001c142c82800c206c140d0144020303079000b070b0320a0300180d00c085400750030320211822060f0001c9040d5010458901002c01c0d41501031801818140100340300800a55948028022441d4181e030040101c044582c0b43c0010101d00c0c3d441c084002c001441403204000e4900810045a40300758001c04000080c45440b102c601540e40020314140d0002c0d21902c044a0541000c40204030107a80314030081284040030704000c0454800c1d200340946100790010030800f285c0d0040c0003136041030007803034042d80d10342500d40185c000e4815076000405034412641c3c030a40146012031040142d9031009004684200c00c511901c5840e60207000d450342d0122414010800507107154000e2811408000380401c103401c050b01e4031030a02203c50700304403000d90001281c900c51500c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 256624820 1250 256623570 256623593
    0x2030709080607090302010c050102070605101505091f0c0b0c180f090a020a0c0b04150b062110150807030b0d050a080705010e06011710050603100507050c0a030903 72
    0x4070240204418507241c1c0000740409281e22010303041c40026101c481c02d101c000e4044810f044d40000041c402030400030802d40c41c000c02031040c1d44d1000382031100e0005039446082110200c0c207005083c00c00c0400d101025072440c0c8508040751042c0b01034800e10b600000c01900e2600c2c40350f00c03490321041c0c69018084030146140743c0101100d110308600354440c051546c0302010b0036001090395200503122110b082064450b540c0c003960240c12540414100010003a41f0390440c20700307100100c001c0c007030070542c0000e11900e4025101d880e0f03194544000a015440001c1040ca50700c0035506c01c00c0c0e600b0f40c1d524024601290701d440d5841c000030301408100500c164041c00b5664600500b0381d5044c040380e64036202c268994407580001400180001030920510009412158800400400769a141e5070341e00c2c1d00880c10f11141030070004034051280900a5030442c4e2003081e1080384040c016000003210180c52500502d0010719142c14001d060141444600d010403003030f1210344c407030381f04c0000860560820100c80072 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 256626070 1250 256624820 256624829
    0x40b040c15201905010605100302160f030201020706060801050f16170406060506030702031b1506090403181811040f260102070f0605090105010e1906050604030602030709 75
    0x5107840244510940c402c680c0440c2000648008003510a602e00c524100340e01c04100005141c0e0b421950010b014040d8406011100b085841c400b0f600304184040d003c1e4001c1d160300c40518002001c428001c00e002c481ca221081d4400c0c0b00040c6001600d54800003150f10507040640c19039035442c1000008403007903003c0340c3c01030b9400554841c05900c141000f1b24040b00c01c1e01601502c04484082000c002c0d0581020300a041e0040206880f40340050f0029500d400c41e5140380d12038501e580500c440d032000403d200c070a020240f44452840d07656030083c02190140504210200900e4422070360603501020004800381c00d240303804901c04200550b044040d42c1d540060030b2001002000108000044065150308541015903072600c0f4480b00c0c07008000c170103a1080c0c507050a50000480743c0400020580302c0040301d22408040019032541c1031090300301d135030134050030b00c21601070408281c1140718082c601c1c01c5900c1410001c908951500d0218149810692045a240d0b4009c014400b84580000c4240c0240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 256627320 1250 256626070 256626089
    0x20d0203042310110c010c08160e09040b061329041406090907080f03070309090c080103030503090304031a06120d0903031805060703020a0506070e090609130b040b040c 74
    0x61503a0050b15220752404014251140d07560901142103103c1d402a501514001002000304043d0000c020308149001c031402c260080102d810550803d0280030090003074040502001f0443d0380d50758400803088406440e059001044001d01c1e4601045030190002141011605005001150040c480c0d500400b9614901c15814416580148803942c02d000b0fa01190443d81d11800f91a021541401e003001d03038114001c50b01402140042c0d640000000300000c0e4402d641e1202002e5407800e803142101d0454017a1b80001c0c110f0801040800c2c0f15038065500003090f8000c1d079141560300d50742d12004c00c00d5040040310340d803030f040c08004480c5001005600300340030172005002e0001c04001d00404100540c0801824481c003000a00d0721b4164206030b01002d000007424003566a80e43d414041e655401c18036049070984511400140c50503c00d009003400e0b0903024104248a4a98400f0402103110040182054001d0f9624141c0031030707611000b0602407402940402c0d190b0400c0d0800b40c0c03103200c26420403000f4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 256628570 1250 256627320 256627373
    0x3091a0f0d0504060905061315020c0c04090813061d0904020d0f082b1109030c010e040e01060b040915050907030b03070b040f0611010b060712020709020d020304 71
    0x512082107618a48410364001400d03600ea20f481c500074490740c00050210b109002c200300800141000d0210224020901480c0100c0b00c0c00290050703104520090300e00c1c3d0401442031300c00c4d007002c1d000008858031030600c0c04e00781105840c483e031003030030303594001d000081d030501c0d000f10803501c0001c4a00c00240e0580c3c04040a1402da000b103246540906001442108112403803810710102c00d041d0b404031030b10241c809120f00c1480e1011000b0020a4a021000700d1410492a00704220b410440310f120001401400d00142c1b4a801561520b4010020a030015100c0c9a0f0000540c001c0c0701b001e01500c55601516103d500700480001254100d805410400c240810140310f95520703013040780d80c014040c3c1b4010890f4a00700b00441e052840c10b520250020307401003400710765800c1d07074440003003034034680e0360341080e52016408024280c44480c801190401c00400801001c03400d580807011820240d4012103400581d110004800c13607000b110001c00d65540401804100405640b03441c25854108090819 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 256629820 1250 256628570 256628587
    0x4020910080a110a0807080703140c090114030903030103050d030509031209030c15161d190f331403070311070807050114040308010605031009020703091a 68
    0x10905928103002804050000200b41804541289070701079a2a0362642d107409541c0005000440207686e08000329203000c0001d80100c0c4240320b4600c1e440002011108591a5907112150f03607032202036041e040080c040420f202c14203081c40158040c004440c002c540e80c1d803550908034201121105501d0405050070240010704000005075a9070f50340844400d8002c0d01c4400003189103200d450144900d41c09042140c5130703546541e00480f8801e45010000b03400c2900b03001d40c1120700d56140388600342e04e500d551040495a04180d03003440c03440c1c840402450030b415180e44844030301048640c40014158405484500e203580007030080303030356031801c1c120090b40d440228401920011004404100145003c00080c400364803d420000383d100d101e0802655900b11401c0100b41c0d503020380c90540f8235600b40300442000c043c50700c0850344210b8243d6542400f80c0d08024040f60171760720241500d03c00441c0c0041c042424002741c802003d03858800e840c0d51410320700d003594a0005041e02c40f00300b00f01e03080074000340b071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 256631070 1250 256629820 256629829
    0x313051227010e130b120307080d0b19080a0302120322031b03080f01050d02010c0b0901091202030c060109150302220e07090f0203150d0f2906040209 66
    0x108454254184079095079640c0300100c0e03424114002d0301da40481e00e442c1a04440f1510f9200114038030065503100c0350007440301d0304140e50b80b0444100500030417041000c031704d01c207481368014261403038024003585154001d03035000f0410a0b00b541180c0100e401020545042540410050940140000362039040d884d0114500d08400b44841c141000d6103864581082010f1007040040d140d000c1801c21903021540c68100101512421280c55030410580b81c00499207240900342144411f030705079508840c1800c155030b00141d500020300b01400d1507407620341c45000501e00342600d540002c0281e00035034440c46180c3c01340c0c2c40c01d00c06030b000c0c04240d0301c1c2c00703000e0a2003442d0064400a45c1d4041e034148031011044852902d0030525420000185490b0400c001790740340020074228116000c41d40144032040d8100210004c074070007900c450b180c0901c1c9810a55003401c02d00d40c42c1403618040d0751891070310f501c0703500d403a43c203ea44010400b10002c00d5101000c10107107440c000a81002090702c0031800c0584d88400315 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 256632320 1250 256631070 256631107
    0xc0d0e010e010f180b04030201020c03060105030a0f0623070806010905100c050c101106090d0c060905030d14060319050a0311070b0a031509020310031e0803130512 72
    0x9410040a000e03c2000301d405202c8000c542081c501c8014040c990315038001a080d0441c2c0003c0b8018006c0d00001c18081c6000160b0a0589500030f01410f01841c0a03610071044030800c0a044410720303116101a0740d0f1f03000143c048940b210320b00320016075915024900908042004041c40d0500402c00f609201a89030844450405103203030501d880448c406050032840e0541200d0b156500c00c602002d203464144d030100342401c2d03000c140d000b102c0c6183c5075503c07840e84503601c03507100f6000620172511301c1020580980022003001d005506507454650816a00d1041c1d54130340d070103010140e82850074000d190408200000080d088009002c5119007940d403003030744401c0e41a80140801a41c2c2030f24842000003403062a001b0a810340704039035a001c40341c0c0007601030300f02442034015500c20240c000500c03071114000c603480b4a08030010200b0060941d07580c1171105202c1441c840280c46040200b200007048000294003c100702070007051319032443d142007890300382c101e0020a032040090003080314520850406 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 256633570 1250 256632320 256632347
    0x5040f0c17090114041101020717030315060403150905070801060506071202150f15090c0d05090c0402070c0905070f080f1b030a15060e0d02220509030c0d0e01 70
    0x80410503200e1081d02805003044210404e0340b200880244410041200c0f04807940d6202030b001c4e00d1000360703114401d4000c000518007440064008000085410f0b403a403d083c1012240140003900300750300e81c0c441550049001120100382d03603540c0324074018000c00b0440c10300200340e540300174081541002d020503402d004a8000070044107642c0d24008002d4000c2c8042d025208540504075168035040f62010800c002c00d503201d5054201e904000304040c1400c043c0d540c030840110390350a1030800c018070154010030000700b680140c0c4c001c0102c80480769803207000600840780100e4020106d50304204041c011541c0162000c028419000040081c041d008076a80d40d01150307c070038049036507803001182440078007580d00d0f1807018030000040001d2000b59034000000c04240c002880c00300c03a101c110588440341402507d0358802c060a91003030040c03918840100091040701c00ba0f904400e10503a0301d00684400791600b9440350008120000d42440800c01200c02403071520b4003c0b64900101c0c0040c0210302e0341c400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 256634820 1250 256633570 256633607
    0x1090201090b1c0b0a030b040b1603052502120f040314072610050403050703080702070f140d0203010905010603031205041104020f3603120f0c0a060c03020405040f0c 73
    0x80c1e0b805545e0300d41032080010754108403468801d10b480d00d070102440760110b078503c2020b114030a800c00b03968801c1c450030b84a840e40c080002401081c001000162500030807094045101d100030300d13409030303d0300405484101c0000d5032040d2100c0c00c40c03030014181400700c2d14000d515413100c58200400401806440c1d5101d09a0810000414100d0000b03401c11a8142102d03084604040500080550006c000c110450183d82c51017006d0b12030880c2241c680c005442868805032a40c9010b01507200d1041301c0d10402c0c4401482001d4030f20066010900b91080312406503030b9030355201402c10a1640180313011400741d00c0710400300128a070079075a0f00321001001c0700c8180242c2c0d0209a0725a080c01c0ca00132504052891000105603040001642500c54020074802c5a10240111080b600c1d04001030f8082c0a0350b00c0040320303400d03e070060040034a550440c1c80441e00c0d51095844000c0071620a01c030707154071880d607941e000d41d940d41000c042c4004c0c0c421400c01c2c42d01340c528003040408081c1e03020071540b45202c803c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 256636070 1250 256634820 256634831
    0x2031b0a0c0c030b010504110705100513020a030c1707061211040512010b04110702030c040b0f0612070305060f0904030e060913050906070c0b0106120f060801090201090b1c 76
    0x51080380c401e5031000c001000350a5200e8040144920030300c040f4125902102c00b80b020241049003801140201003000340030380c4c0004002070220360160012a0b0041900b54404002d161940000d0f903400304a900c20b641c102160482803150b240700810b1112088082c1c1d00802416103800c00c010100e190040c020000d50b0313900c041c100860740302d16013110003c6c00020301100040c507a8000b181d00921291086034425490488114228141c000c16500041d800330050507801c0c42e00410f200150102400b00c82d4412864104040265100710150030b801c1d06505000340a480c142c6000350840d24041c2001c0d11901d40301ca181d089590b124803641e40d01960500d805070043c803400c00825a24000c91a020b903000b0300000008a40c034a180c0d00c04c0b4414110141150481e441d004015581500c503260701a140b0500c540060000078010600742045421404002034515800c0700c0031400c441c00e940040132141d4443c0f00c00030940da4070550707010181501d00a05803078010380d603800107801010014003149154071003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 256637320 1250 256636070 256636087
    0x30803040f110901090e060912040504020c0106030f050d0807180902090d2a050a0f06050703050c010c09050310060e06130603050f01060f0b09010c03080613090503031902031b 77
    0x41c40034201040c0103000c0e90f0307044d42c450455001900051104131103510a03040000da081c0c038002030a0303500400030004d0503c0e107401c1000b400081d41c801000701c1899034036508000f0014202060180420340110050718462508010003054071801820000c10024805481d61407031b000040c01408856401400580d511601c402003180e61406510103400d00f40000d10b000800303d840486024000340d001d0504540c60341791410000801c034140505c0c650b03003284c01014841d107401440201038907402800c10909100c483c50341c2038251030900108000081990300c0070001400c0810522501c0c1480a0081c81100c3c01c01b81402d1241a000348241d100d1010813490780070604082e8403010185070098144e8203081001078510380648110711400c01c0c800504440003900e070350000141d03200d6010503522441c0c3c04200d5202145d29140241401380c0c05000114034090310005841036034402d030710500255840b890040041a40c07004448a143c002e10b004004020b46e82c4008004050030803070164450391504c544 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 256638570 1250 256637320 256637333
    0x209032d0114070509031501080106061103031e04020a0e100f060f021c05160804050a080d020d03020711090a050403030b03190f1b06021b040603030e120309060a030b0a0f030803040f 80
    0x802c0d1703c048244804100100749c4c0603040d0021020303a5a03544403040e45900d0007814a68a00c000c403145c00e507a100c9440041028106203041541260000300320340304842c2c9031a02001350b5842940c0c00e800d81d04190404020307003051400c5c3d14000742858105841030040514020751501061410564021020344d10400594003900540300421240003060f00e2840d0180760030000360703102c1e0040c10721a4045c3d00c4005001480020303c00d1010303d80d94003801d165400c0b081c094000c0d4008580860342d18501e40c21440b02a1a03440007240b0850492078007281030b04160038090211006410040e001c3e0300480c3c25000380b195400040d90407154031203c4054006242c0c10100070030005400b007030700711100c0d40b800003910650000310190200c0c40c2c0802340001600c2401004100d608501c40100800c0341d80300d410303025140c0011301c0c0401c0740050045e01d25040291001038081d920a0032011302181d035a40c005844d40c1031141500000c0c20458900e400240c1c11902d83c9070280c04000d00050802c90075038495010400d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 256639820 1250 256638570 256638583
    0x10f05060108040b0402131a0a0b0301060c06021309020a03051e01050a0b0705100204031b050108070f080604110319180b040f0501060503070b120915060111010209032d011407050903 80
    0x404010824030304400c48008c0001c070b01b0300c04d035842046801d501195036024039040300d0403100d180d240c40c40034007002e80d90301c4041e4211072200c0b2100055502d0001d81001d0500040c007082b074099038009802e02d401c0b0501d2150071a144110441d0131103610041c80151926074a00307054a0b410500c82d038440b1483c0c0782c1586000c9041c01c0101c0d1850000c10000b0400602520007189402c12425550b001610b0340011600c3c0d01d0100c5003080060242100d0481881c01002c580b60007100182020036901d8084030400e850707900548110a44c003c0e0100007160312402442500b8000740e422044071851440c54440110440000d0300c09041e04001140d2441041070960200005050240c1582c0000c1c0d540c1071071807001d4000703c41004640d181c5c01e00040030000049205c050600c26882c2d001c105444901c011900c1c40900d54030030b0b5480d07608004461079681c003004589564004110020300c0240c0c5850001c0011034540c210041c0c036130414401500e111801c07941d0f15030084031480c200ea190610740002030714104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 256641070 1250 256639820 256639849
    0x1d060c0105060306090312010501081305010c090929091003060606020607030b0402160b0a2009100801080730110405060a0305030715020c120903010f05060108040b0402 74
    0x10400a88029400810740041c1d1080d0401c60980300141daa1042040d02c034403520003005020240d00e070042c00340b5805500c485401212000042c44840c403c2e03514582101c07020000140481c030303140c10400001c0b500b0f02507000412401034154051500c2400c1e00000b007080c1000480c07051000c14000381d80815a1001180196007003202804100e0380c4400103911041c00391051000241000c0008407a400c03d4021103d00c240010120b00c401030039601c8000c500003000e0009591242c56500e03104805942040d61032807200c01600e02c0d95600142d41c20803608120030100e03941448603e1340100b042c0600070410740111848030f0308001c00300c1042141016508106080d10f10400012210030007445018090304c800018156410001900c42030108280d03150180300040c1294020000040003940b070900101c0303e03158080015051065828403036090102d1906044071400e00412291014a024010050202c50345103041049003402c100080441c0301c01007001c1c10280348132021074110b40750b0441031126103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 256642320 1250 256641070 256641079
    0xc03031b030f0d151a030a0f0b04022101050114030106030f1d010c12150302061629010608060f040c021f09020f03060106020c010c0611040b0301081b101d 68
    0x9030352260307003480201300c50b06401d00d044000840105241d40025002200005004900c43c11691000d402c2005019030f100c4150300c0d40d40f5100e40141541703440c00034240d030031090100318600f8045924400c0d040c5d10143c0c441410051004609a10411201c0460741900ca50b4540401c119403d16481005810340703980780e9403d040310030102c0c4100c175010340c442081d61007242d82d030414200c000c40528080d120320380043c1c07000d9210349104000618003c0c00a02410140d00c9218131400c14039200c090f0801c105811a4011103545540ba001d0600c0e40e591440c05442581030074103641c10414042480d9810580030f0600607070780c41c500e0b891481c1c004c100c0d5141c11800c9000f038400c24103c00d00300d100a822485003c1703015000110b408240c515000c034449050340c079184d0081070910b150400440e6500b00515041d0342c0e0035900c5d01c6013150f43d112040180f001c3c007204402c01d03980c2d501d03104c0e40c82d14000f549039045200030702e076000146456960041c0b03100081c43d64034011202000583d0402d41a154108075103900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 256643570 1250 256642320 256642327
    0x150507050a061409010614010e130c1707020d1e0c0506070f091703091c0c03050a11032d0c1c0b010e0403050d0c050705010510170c03031b030f 63
    0x80000380d8001c1c0c040c0c00c82d111582d5880e91104c0741c8080c01e892442c0281c1a8841d40c05010191651040460098818005041301851441c0c503040c0c6044560b00d425900019084070781100401d58a018012b0308400240b005144c0800040d10043c600900241594003454007044180000340c4210411100d098100d01620300c3d904043c0005070018100e500d1650104e00c5841000541c40044c3c8202501076140700007441c80c1c243c40304104a124a413382c0340d142c140240181290126a85101c181d001c1c610440040c00d1044044c108180c7c070000703900d00305100e58003000c8018881c0341b5640000000d28110f40100c62a607800015141c10402e15448494100185440c00d000b4051000722503074041d40a1400d41e01b0698844100f050841030448018002c02d00070890b0035441c0d8601c0d40689100046c600e0007504201c0ca07950707002d00392402900d096451602d50081030141e0101804c20402d5002400f001341480c4000a021a0b2a4010200c07a0744c2801c0951005a100c00d00c00d0080f035100720001002e0701c0d903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 256644820 1250 256643570 256643573
    0x20f2101050702070b0f040b0c01020c1504030e090705090d0302190c18020c251214010c0509010c080c0712030f02060a0515060705010f02030117011a0a150507050a 72
    0x705070403160307400188910840014a0350288048412070008003a22514090600c000003040b1ba1160070403031925035080140c106003140034019501440514225290b050501e828014038030410444483d128078864401d201289030081304844001501342c52803804000c040c18180e044c08461081e00b1044070510001c54108403200501000762100818007501d0502403800700f0040b80100e14094000e6031080c1c0004d1008400001850003a9032200c4c90302061a8807500102100c10350305d04c0894036154013080c0e40720903c6083c000c1e14100d01d09440e00d14207010b01000006e1108600100203001c0401c0001d03c21a0104140300120103040c404180e041e40f986149801018021940301803030060003900c0100c3c0c031010050040f42d02075400002c00031490700b9a1804c000e003030341c403d0408485e20f651340c1640e0004150a40043e60003800301140758081303441810300c0942922280b000c8401084a6050080000e07959403c1e4502690505c0076070f25100c1070382d8181a00c4500c10100040d0a0788a007a21000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 256646070 1250 256644820 256644823
    0x1509020403060f090317091f05150d020913020d080307110f011b031112150f0303030f010e04030212130311030a020a06080c04050607050607020c09010e0103020f21 72
    0x40741d129607020440b842e840c00c0c860f0211030640300018000365034804c880381485030702107200741c00078158400d84110404800f40b011300c90f0140c401d45070101d80c8910410109403400c1060324403102003130766100c83e040c12517400600c071820018180b88001c00c5803022501035444e16241e1000071036100c24050b03560704091001030413a80d415800070f031a510941001c54640300040c0908081d45206070070508a404e4445801d40141c4400c802d50f894102080c0002140720300c000c1a03482c000c00c000300d0361450800100c814001030259040d40c0c180260700400034400060404646281102c0c01400c401c041929103180032400c005840822822503100072810424180d0034844200842c2c0c814915100c0c014459420316443d00885c05020b944164901c1041010030302135002250702c100c080c140b003440c043c1c4402c0002e10a411031704059545502500410090076010000301004500440d8042c244d50b140c55824071000405002c002e0080c3c0c0d000d00340110684030810110412011001000300c1d4030a443c6046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 256647320 1250 256646070 256646077
    0x9120b01051504080f031e0f040509043f1704020609030109051e160b03060910050a12050d03090c15020307020904050c030c0f0102030909100e010b04330f03150902 72
    0x211010b01e02102040d1087c3c40790100c82c6065111000d42e420249000708001100da0002e205440102d0510480456001c6a001e4607075604601d203140142e01c44060010820004414050814002807082e101c214404400b08194080e904548840d640e01c00d00010078003500d04298020100e20404035503000d0013a05510140d09d9080140845412114012400070030305540d00c558400d400042001c074589003080964251b110005c0700c0c40c08940ea64803000326040503210303400703401100c114040c0101001014005030f000c800d510320701402224100c0d1100c0410210520941c45903006541014121a00a00c152034030760390000c00741c42d000d18003410007644400048426510a02441c42d006144e454901b80840d041d000681c000c3d41014480d10522440300009060b001c1c0030f070101d403000281154062009400b90600105058659140c0f24140414481d43d0046266104004958901101400d0000080d106c8280b4258842c6504440268014004004058042d0151000104c2c4a0160390000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 256648570 1250 256647320 256647337
    0x5030c1504050c03030319050604110c1b0a0e0601080a0e120901120606120e03070516081207030c060f200a0f03060e0a0203070224040309120b01051504080f03 70
    0x2e0fa6050710303041c810591284001ca4030159205035420b0780c0500302810794021a80100c0141c00007425000b003076040c103426001440740220079070000440c05000c00c8001031060301e5580030351325111142e0506200c0c94011800400c0c5030b04100d518800103500c0e00e80e903085031204111700380540700754240307100d1801c1d13171903105480d05030114020882c0c04210039160320500e0f0841743c485da61054504004103484000d080c0c1c40c243c0d4412480300b801180c02040091100384006590300519900c40c52504000300e0a01070b12501c03a080c1d00c030060240c00d0200343c00c14400c4500c250b00500014000924682c520b00500a007950701c500f50080f440c0f104000c1c982d500c000c1c2002107440c2c1b82c1e050211140c89044050b42c1690003210b60740165078001c182c07803143c1c90f005142c01050300d00541d0740d180c0c0c2040c0c11280d940c189422640028022030207200601d900900f040010b0500c020300f054404d69640c0364580c10380303018424140111629003001c4110000720080d40d02610158064410310310204000c01c0e56904210030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 256649820 1250 256648570 256648573
    0x50901080c03060a0b060c120d060e040f0209100308070b010303090b041a0f070b0c0403060b011b11061908010e07020102070302060109200304032304050a030f05030c150405 76
    0x494038034030018504161600040c02025555070720081600a000d81d411044d0300000280710280f0480c40c00d02a80070782d2003000390307280d88500032072569200340c501d03a9001c800036204040c10302c004298050720034000d0a4058403850f15070b88a03024a2030480020740d0010f0454a40456201b00f04560170a605049a003c1da440701c880944403c0d041c0c0451245110323014480002c13010350120002034901604024139081401c5003420147e845e80c178189141195280d012010000d418010040b4501c101c6002d040e0038a483c0305c0500c0903100e0b021550500c05005022680224601e10035a61040c04a504924070070102589003448400c0103060424203000d880c0103407554200050030248144250381540b030b0540d00901c80751f403034000d54a0062540601600c201c3c07031451104403024030307507500940c000c80c070950740c0100702c1d0348a140080c9030f010110701c0925010410442003010350b80e42034415090f284c01018a030a0540d191408529510940c40e40705c015000740e68043d03c4181070408140d10540c0101d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 256651070 1250 256649820 256649839
    0x509090f01060207060c0c0807080a0611040b04050607020f030d0e01030501140901030803070c05150601120e1209060706050703060501170717040311070b0a030f050c0a0c030512090705 81
    0xc004101038403003401a04016031050200300085c51251444646403406018041c00d25600c1d003081905042098020105a030712030b0140004002041c85040d40020901816a082034240040075000d88a035105941c80707940041002815541d4400a11801c000300a049440407080010007a02007054540081d0200b032800000090345d181d05600e5021045000b400640715a0840da51400300b074001518040800015000315000035104000c11003086a00080340071144c6460070005081c980c215800352807171428858107110003813000030100003c1c065410502d13250a000700105a0a00610b20040d01d800d042c00140b05082c0c0d0554042002c0d0f440c280d84600d29005401d90420032420f069410030300284856400b05464850114080e40107486803070040144049010201d2a10711389401c803007251500002c0241c00580c00d4804c01c82000c1c1c4441c0300784400d00c1d2400c104100f80c0901000c99090280451052007014840e50440c0c05809604003a0813180c02c040749940c2d070318401f43c090180642c40c440d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 256652320 1250 256651070 256651081
    0xc3108100e030f130b0406082415092d0102010608060708010501180306020703031509060e240901060806010e0414181c02060a06090e030d1e0c050909 66
    0x18000d4200a021841c0110b01d05003804280380740c0b50303014030701002c80f00d41e44400119203044200c00510040101d03565020050038079100d07510701030b030b0205060754030b20040316180000c5490324200d070910f08038003075482a21403110b80c0c0030030800400e8002503201041010307101400201742c2265451040c400b0b0307000300078494440c0e13152540c49106a0310440881e0300c2c0d20041040e0b41c400c4d45031242d021003010143d02a642e4a41d604026600071440c00c401207070702c3d011078010801c9030925803030003040440c800f40f10743c0e45040303001e03480c0c2c160181c00c9103e4501144007012181004a8244040c0316019101450960352804002c0c41d502041c3c64080c00500c40e041d01881600d424003410341c14402c488081c1900d42c4a103064501c0b20150450003201c68028100342480101d82c5020040e40300070301c1e40141c5903d00d800c03850300048840c0c0382c0015849502e03000d201c040d071901c0001078881403401d80a000404101c4903042000403c4e1038550100110b00f0004010f88441d8454040c00d0440b006813528112900c86 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 256653570 1250 256652320 256652353
    0xa09140103181506180b01081b04140f10020601030507060810060807020f0f01140901050408090111010b030304150818061308091e01090e07080c3108 66
    0x401115022030a403158008041120070f9640d40a1003000d0000141c041d50340c210069402440d01400080c45582d00344010903075070840100b9501c01c42da50068209a842140340ea807150081e401841e0764a800f400b0f001e0001d072102ca0f081c6c036075210000c0000344003041d2001d000f50740714024001240d09005001000550341e00840d4094041d00c80c00051040c03060030810200d55039000104450110711440d10452203d51042c409541c00d0a1303600004140d0240d00c581815002d017018000b0b070940d80c5004c0400011521a5007942c950010900e440c0401094444003540984514145964180000600054100b100d114412050400c03520f6207200c40d07a07a10026600040307031105010640d0010030001d98540503103504408001c1c442d4962030300700900e98000c64401c0518074030b405a0047c01902295643d0b0304a10000010001c0c04403296040ca0078942c01051080040d000030352510700072881032020b020500c091242052084002c010718030000304480c0ba410a14828016a40102035600030040710 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 256654676 1106 256653570 256653581
    0x3200a020712020901030611040b0c01060f12030f0305060a0e0108070819120c0303090602120411010903080f070c03020303071103191212020d020a09140103 69
    0x5240180c40c003002a0000240c5542d8100504016070b110035003035054a6100c100801c0039840040004201c1c00303960072203198082e01051405c40c5540543c400c504840352010030800c0e4036a5045c0fa0800d124444101038000b80000020b02c04941c000c0e08401d0300418041e107440c0003a0380d5054104180442030b0880141a0441d140c200304c01d480800c0340b580c8003a0107000e8260005401c0e5100c1c0a4103242d2054402441910000071040c980240d00c0340203020b40040c025942d40314040c81d81c0d010440100d030700f10703261080121004a554880e890070001d903036022941d585002c012540441154002d05d1080300e94015030f4a0100050b10184058040740c2e1081c1314402c00c4010b03000405050800d030689071407000110140f10400300320554000000600d148c00c00147c81b50b00110064080e2242043c054184d074000140396042640c07090552017203803008005201024a07203001102940d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 256474820 256654676 := by
  have h0 := BRFrame.cov_init 256474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 256474820 ≤ n) (h2 : n < 256654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
