-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4428
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:35:13.86354+00:00
-- url     : https://prove2.me/submissions/b343a0d4-d914-4330-b173-cedfb8b0b460

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 796223021 ≤ n < 796402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 796224271 1250 796223021 796223023
    0x2802090c1209061e0618060d060906050f0c030912031e041110180b070204021306020601090b0904050606010818010c0908061501020d05130b0412060e01050c0a05131502 74
    0x14031441c40484d40b140a1407031500e000368000d2058521940182507240c030846550940e0103490382c000b1010b488101341c540243c4481055032248403094400d10340c1d5406103c90407452032203460b409041e40754a107240d81030065001e903547c01c0070b8a12111020000c000319142ca00403401e040d01181c038150410209060030704028400010603419544266402c3c00203800c90790260a1040300100f9004032400410f1410064180c190b001c030108986c0130340d08010500c0c420201d40e0b0224040c104c40c0e4003c00a0b5810260444129614005100e04c620007031010031001840000c1e440d0350001e0700307180502154a440c05150340c42c2d070720304040400d40d500b0b024030750301d065502036007190032500500100e800a80300e58040803d02d071824940c83d03005800900500c0c542c03500032401013080120b00482002c03820390701e07407002c001a00150040300c015000b8004030424408940640e0a02143ca0700082156080035525101c41d440343d081010180840881c078a08000440215003000303040c038400c61000e2448880c2c0007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 796225521 1250 796224271 796224283
    0x2090a0e0f07081329010602030c0115120210030f0c0f1403130f03090e01090506040c09060518041b0201050916030c0603020f0c0a0c06022802090c1209 67
    0x180312907004920001d10b21500c500503090140e20960a549030008040c1c6450640000c00e03032070040c1800403a01410300142c6100d01080c020300f1164003542c5c65485c19a03038039007134400a40030036547c80b001d00400d201d241540310400e44815030446100f400305200100030b5001d0034404000c08541c91500f078040e64940e0f0056204070078851a03540350030403800d00c20b80d81e00081c041030301d440c2070080e400014480043d02000e0003130080d41c001c0c02c0120411350f40f48042c0380503030000d8100005840c0c90f4400d0241c1c03410a80034915224149007080d40110741845002040c0b0300841c120360500c200d004481001c291219403081c0e00841d0031805050488459400180c040e08050704d600c0c00340e101d402e0000f5600d05034000a40250795201c04c900240070b00d800307002c030302075005004103640c0b11808004203405490100202c40c061031045804035170705480c0c10f2000e410110840031802d003044150065098018256290341c1e01a541180d008900c0d0701c0c1c0c6100c90760075029410011105400c03401c1400b803030140000744 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 796226771 1250 796225521 796225531
    0x3a02121c1a0a09020412030318080d09110303070308060405060f0405041a010803040b180406150207061d0102030f0705030408060406060905070518210a06020403170c07030f050102090a0e 82
    0x500c0d0040f0799400d0300e10101e128621820325028543c401e5580040d1090300010784411132040d4103006500107803280c030700c980c1c880c0c0e10422842d41d0741c0c40208208104001014030641084014505101c15514058584000240701e1131203a990307580002d80c5907407040c804181c010340c050b008000c0c0345860300c1c1c003040000c134140041603000c1d1300000002d464480002140d05684804038041d0401c007104010240c2d00e800b41240f240d1142d2607110104048800061008040b10554001c180c00ea14061001d403c3c0600801038401200760102880403598001084500f00a80182410742d110440e00f0410306500854011860701d00400052006100c00d94000c0025200004410000c540b580030041e58036225020190959188200040404e072915005080e8081c00801c45a8240b0110440700303420b059410400302d601d568042010300c01e001c00e8030414032010140c800080e01e071082c00e110041c6d0340c0030544401484807502c44045000c220013034065035141000903040b8600302e80c540d9003080b02d404040311 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 796228021 1250 796226771 796226779
    0x10050f010f060903060902010302041d0f0a0203060312030414010c050408070609060f0806121c02011b0507080a12020d0603050c090621030c3a02121c1a 67
    0x400440e4680040c0c9000701110581d40b14200f80c5481c5540300c1d0042c0c0707440b000c01c1c0d061660910002071109004030110000d000000c19a03041481c01c070710114048140030301900f46407481030040181548000488001c28104100c17020f4896aa514222500514100600010b9402c011540080360b410101400640d009a03040e40c1c40c4980382d4104841002c940d210f00000100015140c003a03d90040601a4202c00d003e0580c007030440c1c40c86403180c030340304500184582083c2e51145004000b5428810003030110750018800300782c1302191200800a018114019295080014a0045060207443e40e849403520a003001e54440c001002544024221403005071a0b600541181040d1842e25000d828410705000303146845d0402486231011070880a000c2c0c1c0c65051004006112a010040204110b514024118034943c40c1846540001c01c140f04144850101d48849609071010303000b00308400c0c0c0c1c07960030408a46490080b5211429071170b140346c41d00e00d17880c81e190740000454805020b560401e04251 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 796229271 1250 796228021 796228051
    0xc0821010602150c0a05090415060801062012030c0c0105070806130b012c030703060509010c170f100323010b01050702060906030402041104150e0105090607231005 72
    0xc04411090f40220340501300310408005412119006401a2003083da0140c40024400f840d01950140c64a40d0781000c400300d080580100913056200c40d042c14400300c004041c1c4558407248800c41d65070070704410881160718001c00040d07607042e0b0120680b09101c000c82c000b8011400d20b40302c0504608026101d0a0080260b8440b40103841154094030a80c9001079541c1d07400074801244d030707940e01c541c1c410052a80f461052198210360390100705080166009100001b801d0030861f085c1c03401c443c155101d0905002d61312454006181c0e1100110b50711403401d42d0b050706260703501c0c0394600c2d0614054200925126040d514595422082c2210003216818800204003404942c001541c0d6401554130081d4090801c015207801410840091070300079102410104442da040401889941c005800c1460464208002d49010b280d204070f60b110944000e00b041d514003c16036010503030f40e102e03440340235001000f140005104406101d21030100c007550101990758503203514605401400080d02e0381d80b0340e14003031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 796230521 1250 796229271 796229293
    0xb0103080d050c18090603240a0e0601060804080904020d0204090527072312150109110730020102090405090d09030b0a0b060403141e06070c0821010602 67
    0x30880d4001c4d00c070500220b241c41058030030030040000080601d605402200303884120100b4140c0c010303056094203154806903181814260007201c2c040c401c0308040f6401040104402500109402c1d00250004082d0343d5a0707014a000c1406803040e030194416462001a0004140c41650b10103406001c1e000d41891140d40e120244107420054a40801303440d4000c034070200079100c6070307600015221414941c0c0101c4d541b040c00020f003559185856800c0340760001141d00920506104881d4003600b0b000c0020032200b078190004a10030b018806004000c0c0317106035031891900030404040c8883d101710f10210208880d580000034082d41002c0a5a8000e60608002c0340012030f000c5204140034001d03540d5007620502d1621001c900f490003070f180001c07d5a40341840840e54482070000d2001d540600d4441c9110200b4842c814505110b03180747e4400394000540c504a11600400d09980244030f0b850030600c148460b05140c1402e20810802c000300c0310300300420306041a00d1122441c104d403226000e440407071400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 796231771 1250 796230521 796230541
    0x6071a04080315040e060109020a0c050d0216080d0801031509020d031110140403052505011409011802060a140318060105060a020304050d0f0f2303090604050405040f0b0103080d05 79
    0x138074455801741d908960700500000519030702401300329501d45000681d810941c0c4655041414410858005070014100b102410824030b5451000301030800003440c400a0207400280401d03c1030200070003171070f08140b1507003841c0c009402c4107600c150020000006500c0d1803402500960b12080102101d00590040c41303400c2c2103e1086003280042c00d14114150360321a80e0031111507000c0403454021072143c2003481d40ba0385030224480102c40c03048000203400c0c8842c004403071414000600da00001da040c40318140c1d29101c1c201d020b80205605440340b5885402144099600340e41000c03244c04d42200110801100544000300c01584007052402c0d0b4806036210b000b8800b0501c9014224000360744104000c2110382018605805124001e40c00005d803070300a0354550166105200f000d07500046018074045001c0310341c01d40700e108001540b00651504c021100400c2c0b85000794400c6074821662400003c0c00d01c01c030803801c0049194800b501d0084da40c7c40f4504042c05401505a01c0d0180346083c00048800c1307a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 796233021 1250 796231771 796231781
    0xd05010807080a03020c0904210e18070507030809010b060711041104030b180c0d05030a03050903040f09021b0102072004060b0426100e0c04020703050906071a0408031504 75
    0x2800d5400b1b4003208408000388204810080c104039603110100603a119441c0038030302000c0c02d2424680d20003d02000385000c0242031f01200200200300590002070000c002d40086c21502032070f03130504002c03c01c1e94980100310300520004a0325070700f042000510718104407260401140074101210100603004056104190501607400014144010007020440c0703002060322840b0b280220300120307804011184080b1700c01c008841c02c21502940701140490000b9050f00130a0383c4402040e00450800d0b00c4c00c0984103d8400e28802c086a007540003a01c0850020080c280c5294441454001d550742c041078904804030708402c41c40e4011340c4c18a02c800764498079150094204480c00500c0c17007412b060a001c8055034862801008035030800e50a0b6242000768400e01540605010741d0710001139803500a10f40f42c0c1001120402184500d00c10041800000d400005580081c6400e0b140e02d5100d081c5460300384108083c4032030f8a1400100c01d02000300b0050030100451103801680b9101c90f0341c2d0b11300424001910 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 796234271 1250 796233021 796233023
    0xb060d23091e0d0921050d1706030105040b0c130f1214070506191809020415110607110a140304090f140406051911120f07021b01090b0d05010807080a 66
    0x11004441040b4282100c8050490351918500755034400b417171035842510300040601031101103400c00c1d00e403900040c0e40c12511030303200c98241d0080c00b46140558550408540051403005140d0000c03d0105000c124040454080d06034010804141501e403e11500605000941218042c5407840308040800000c140e8604445014041d0750501a40e4200d0868070200840c01400304041007a001500400c090001c400400c90854016907450800e46040481450054640d00340500000401c0c10002e0004080360b00c100e95103094248101110180c43c1005a080d00103410307141d2007800103082100100c01401103899215003001a980000c01d404241c43c994020186907404d03520000b00429140c4d003115920403060fa02c140302ca00100300d1074000b164182040c000d01606c003ca60342002005003001780b6004090030213014001d16003043d0003550303168400300010a031070032001d40c1c0d81903034010032a034800781c847d80060680f00c03c482a0f145004150903c2402114030138114001100c07007010a003810340e2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 796235521 1250 796234271 796234277
    0x60301051e0f340e060702090a02090a0320030715200708010e07030c060806031f0b0607030f2d0e0f0d1a06040b060d23091e0d 56
    0x1995942c0e00c0c8902d030120083c0403803140e20000c000c65003910f00030038541c1c141e15107804007964500a000c000410000038010214000c420821002002daa00c40100035800058000d01507900c01d410300c046004a045640010b2038070410302c88144203c034010104400540c0142e040b44c80c82c2da95410a1220302880307100c1c840208640b0981000100710300b03540085008100d504591029948803415401c44400d40800b180359004884140300708502101c00c0300081402e131404110604021001a8965102980482207401003414010300140d45070816200080d0042890f42c0341c0806040c06803c03a800c40841030b00048115501e1010703040350500b590f22015800c00c03c2542301000000036640101c2003201240d000394450407902c4550341d907004d107102d40b80c4203004a108908036140501c040c02c00240100b446642083d800039440c1c0c80b100b043e10b00c0000c0c000c0d00880d9480c48440c03000c940818048a114000f9031903020803d89080005030007844c0d0b51842c103009401d154150025454900c460307090400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 796236771 1250 796235521 796235581
    0xc0d0806131d06072d0519030f02070f050f121b0708012a210b0d050a290402090403080709081504030e060310030605181506030105 58
    0x800d965078420340b0080794503401851114101c8607407510b0501c044918000051a40c05241c00359076519125031078540841c0310202d09035081e204080c2c001d002d0005201c0c2102c20451035260654801d802c8954030310801d44046640f000141407a0740f2620302d2030342c10f5800c0c1c810f58141201000000596213007440d011041d003824602c03901e4410b00054000c81c0041900d00c501310000c11046420b106141117200c1c074601c54920300042c200c8101003014152000800e0106003001c4c949210105210003002d014200c900091940085c000140c1e540c00c10b0308080d12502c1401c45000400081c00302598071350000c0320490b24600c050b0303510090501800c940094001c005000441c0000780240c0d4032075007080c0c180c14800d1440b80c440e00003a00c4c0590004a040d6000c0b102000d00c0107142d00f144056901000540700350345146071850303500d40303603601b20f120003818180e86100140d14041c0107500301744001031142c192847d11010741910360114030151402446546421f001c160b021003100840030381034400c2000001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 796238021 1250 796236771 796236799
    0x30302090f010e0d021309080f09010311030426160506040b010f0812070303110c0c090604050c0912010209060f030117010b10030c051b0607090801020f04030212210c0d0806 76
    0x286d451060012514400d840f513001400064640e4058005e9613031000381c441d1241d040c2000101580c0c025040104c0c40310080003840080351411003101d10034640742d600444040c0c09048018054803d00c03043d11760106030000030308200540854010f01031400f480721107800da6250080041075400f1032248409030340c0100030303160110503008054a0203500034240025040c20030a100c030703000d50086041070700759040044004294500741c640f0700e4001c0c8065808218a24061301d00780810b10510160a1180070301016000718130070250115141c00102038000b540314a0b840e090100c064000b0b00610680d18070049641c45044c80c1440740001d4100000e145844481c4084001c0d4000c2482c3c1c1d141c041005410448034906440c1c0c00d04c1d04106c008088002c28803450103541c0105255820b0700b140d10142d0041024076010105041940c00762501111050a04e441d51041c161602d0745500c14149036412007455050020100006803034524100810f03280c06800420080b03c08907000c03500107a1004001030005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 796239271 1250 796238021 796238029
    0xa0804020a0e010b042916020a1505040608090f060f0c0c060115020613170903010f0614030d0e03070e0c090a17010e060c070308100b030103030302090f010e0d02 71
    0x540080c009440389850a03124211114444001d070444801104002401c010500b600c15910041402080c00706540003418200d442091056180c1c0c41104500020b4050030743d45c42003801c4c0028610900c00b42c00810000c4c902038440d41203803041d60042520780001581c0e65030007207030500c46061850064040d6684015401806840c09031010340c2d240428031030038a0244040224a01910400c064030048600d80d07080245031010040074041030020003108040003d28510a6185810700c01081d291034921040220340100443d00245080c04c1c108900000d841901d41d841c01c4d003e200641c29601c48410b6030000b0307900c40f2010094a90076a0000904200c90b20300c64142c190801c2c03140520700c1c03404c12201300050700440260040304c94036101110880d80031009100c1c1c060f041200201804052415003110000c90046001c00740520011400095803403000f90030140c064101d43c0080c645039616814000c000350007c0000354001c200d40e0203911480c3d80110031400e80020020040c02044509a00340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 796240521 1250 796239271 796239287
    0x5010503300c030c030a030f0b1f0806010509130506010905011d0d060b0904060f060f030312020a180608100605180f041503080c07090b0d030305060f0a0905070905030607050a 77
    0xb40c0181e0005000d651680e0300c00340000c2241074615500441c001110b59106000c0310104030807907110b01c2c80030140002c084111100f54000b40120708124000350b40380c1b1f0043c0d0301807140843d9a50701c40030740c4c0084805100c0c01c0d800a40510400e9070303001d3700d0b561141c005546d888010000c1120404000340031403001d1901300c130540d004a02c07850b00802d48018030004981410b00a03501246d03d261200c3e1007902046c29441260002c1003080d014071003951568502500c0081a0001400120340014087d1102401940c80814403903416503e29441d079070380c00c801014040262032a092600f0505400680c5074171078001d603510000220403d0034528403000810010f00c10b04070b046034106449806541803810740884c1c07000110700490b58a43c1c0c681e0524039080c00d1280760707000f00d58200c0c0307002d8001c01030780c0300c000015040d6949420005184c0c3c550000166032880030214403640900070b5907000c1040c0c485a04442d01490745600c4950700035480710101501d44a084a807180095800c0c0702e058580d520500c20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 796241771 1250 796240521 796240537
    0x61811042102100f110c180a0207050d02030301031a28060905010b09011107121b051509040b01080708131a07030e060703150510170a0501050330 64
    0x185224034420b540441c4011007100700f000f001c0f44046407000c8419400c11258088900300e80041e0416160800000b10710f85088a054100940c2d04000a950150558125005240c0040c12038010142500b0000c2d0703aa4800d00080303403072581801a0146955a420402d030113a01c00d10100710300002c1810f241c20078003801e5450382d9180e98a0303a1001641074424410782d80a44034103200e450780d80210b000051f1610084000000700743d80101400c1081403a0040c3c28402986e00c41d000e40c060041d0184130240c0d4881e103410995100380d141c9186105003091a0050010100558003407000c15602c0c030055811813001c40b074180200c0c0d0b811001a0340941d040c80c0b12030341248a81c0400009d004040d9024070b005400300e54401c04207a9800c210020240d0070800182c0c444054a03080c4908100c404c1c1c14010a4a1403181900403071000304100d441a0041c0300c038822821a08840200030302c0d043d04404041e080a00c100341c082c0c001e600c0c10580520322900d1141d41560700c01910840c0b240440c10501080d403140d03203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 796243021 1250 796241771 796241819
    0x403020906131b0e010f1409040c0c0618060524040b04090f11031c0e0103270614060a05150a020c1201020414010305011206050c040b070606181104 65
    0x84442ca001c3d801d40c0401c800c4007003556180350f02c1410b80d002500a1000d070802d501400210f0804243c41c218180890b591041d003907030f0200b0350014641c81a2514500804024010342c14486001d82140b5400d9031411000d014080501150300c503249500c0300d50320f4401c0c1014041000d00c401c0303a02402c098018103400403020f4070008130000785446e91b001c1803400c0707142111002d00440200481c0e00e01000402d419503041071818501d00104a00600058058106641803644a0948440680c0c0c41901484020200800840040c0071460500020a40348a088240182101c0424103d007000c20f01d880a44101034031440000c14401034102c0039800c00e506007000c512408000c020360b038403192a02070803107a0710800136841e0380c1081e07980c46c41c000b1007120503410035142900412501040101510340c19400940008840e120101443c10b544140c0d040140840e00000e1518200551135000134203c508441c0d441c0c3e10500e469104100b5107000f0160414030340340900041c4800e0000e0f5400d4541a46111 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 796244271 1250 796243021 796243031
    0x70b0403030c060914030c0c0f01030537110c10020a02030a03050408070c0305160608060a030b0417041e0902031e0a0b04110d0e060702100e0a060204080303040314040302090613 78
    0x24140034510b51016400d86016001842c23081c1c05400c008505480d02402428244010728100d24020440c5a0092401119040c044003503d01090000092600380f16191014004c2510b0100303401c140354404011704c2d8240c440d100e45540444810300c00d41d00100e500e40d0103186000d1900070f044016010103001910160740421584d00015030391003408008610441c040d2070810111001000300305216400340d010b00012108021580d69804603501c2500d034000d01d060600c1d210343c02c0256210342c0c2003a0fa1080b900000401103042d08409084140c1074101c98034580d102610f8110700d501340c2c00191118511440c0c1d001c0a250440821012194420701380100014607950400000d0248ca414100c0c110481c0d00c005a0030160040034091060411500d10040140d0309151000039510000d42480e49034603540c800d45100f00340d00c14801c600c15103411060540d2103984505080c0d80342da00a40c0c0450110382e01c0c1500b80c058103100d00c165401c8035001041c040c0103a40d00340c144a201c21300d81e44110800356540c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 796245521 1250 796244271 796244303
    0xd03110609060708010807050901170f060c1c142a040f140d0302151f08030d0b090106050a1d091303030507050c0325150c02070b0403030c0609 63
    0x400103184112110750007000d4509246401814410043c0c21035210394201800a00641d02c0d00c40300070381181d90f4288084c601c3c400c001c03812030404020702001c3c1090b0240a0900a00c44054009400552481181042c8106080200b942152100c8101c800400c045c80005000d1240901c0300068295514450050204440d00700c040303550312039000b0f0b212506015106001020f04c10300d032801c1c3e258090341d40d001d0403201600c000c0d54a036080c000e01c94404280000084200c0c0010450340c01d4428101d020980f21a151610343c0c3d00ca8101070008400685044440f28461030b0a1004074121070a80d1180e620b024855034086508540814030190443c0c0e5071004040e06495801045118203040212050200300d0380c54018190f4402901d40380400500b813001300c0707a100c4044119007004445400c520045044d201d84004140d0a9040113480b0384070807114041e1651094000c1c900c00ca01e40c0e42030340e10b40d9880b610585002d000b03502026000482501d4010002803280d40002c0c1c0c0940200007114950b001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 796246771 1250 796245521 796245523
    0x1707261e030405070f0501050706050a0e010f020318120313050304051c02030c060307090e040c0914070810060c060e1f060f0e090607120e01020d06051017060d0311 72
    0x30206500420303000010030070042c08000e0140c28058444031604e8811030b0b06e0140000c1c081d026041004e045070b5612804031301c1040095200840c0105a50000e00110300c51405410003500f0031902c0c0303400402c1c5c500c0c40b80e20402d008100c0705051000b981e485401c685540c02084d211503080c47c13080716644420031022072282d64038a8207005070300980306000d020100700d105040c10240c1300d090710741c0100000d0042c403980d59040403648040d40c002402085e4940d895082101c0004180d03401801001c0c581403940d840c1d580310007605071103100c0507210100c0d83d0321041d80c0c0d141360507240e1041900140c80001c0190009083d0341040c041c140403d01112000c0f2407500c6d80e603110321800d0302c3c81041941c1e079810401c13400c0302040c180c100034040c00040d00c12900e0001542501e80400508140c10044081d00550742418140c1c04031320182c81c41402151500646400c82e070040006019081c81003000812081403a40300b540b0441003028285a1092251512818408904600b170740c100d0610003504030710408024 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 796248021 1250 796246771 796246807
    0x1081303020c150703031a0303180301060306020f0c07080604052d1e070608091c1704110906060c0706030506060f030c030709050d0f03050706021207020a170726 71
    0x41d5100111340d2501180307409800caa929000c50580750103080c640194540d4044256500c1c1342801c2041800c10080000190041a06d608010321180c03012981090f429400c00180c060201000110b503551a03c0d04d03055540e0300d9086038000d00641c42482204e585007021852440c90354040848139501100c981d503108d040c4403241421060440e10500c8101c5104410488500100340074101510035040089510380c942482c840103890a01129245510b140e210360a00b000c000754003c418a15810a442d00408041c0301c40101441010340c500030a8061510380125440a1007403401000c055242c0b0340198081d050041106034014010301c0840301a01001d00190322408107401800d40d24074020b00041c0881c016500514040d40f02c1c8142d07400010804030240320b4040c0c060815580712a50b03481c00c04003900c070703500b601041e20801c00c040c0180150001441024dc078401d5001d41c40d034000100b031200460090042c00340005030185560706030700d48030302030340c0c80117080d80e040162030f1245201c4104c40c092 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 796249271 1250 796248021 796248049
    0x408010c02060405011d120a1709010609050a0c27120f23070902091f0c0201021b030c01120b040c080106081311060a0c0c080106051e01081303020c 65
    0xa040340b02080300b0840c1c00e1185c1e1061702c4100da001c5040c1004402626a02c169044030140c01e80000601c55203103030702031b000004291a8581c0019058501841554003900c068400c01902c1810940401d0f05110b850141c0300700012075544010760b40c2ca1035002d0511802114022114903440c0c4d00303002c58540b491903003181615010b0041420000100e01c0c04881382204030a00034640202e00e1142c400c1c044000c582c450032a50740d0b140150b210400b002c0011034241c007021200c00d0410311a106044000d401c04201c1000718001d8082d40d002e9203000315410a000124114183e05801095030740c000d540c090011901115100100040c481e0814800f18040f2000c4901c0302010401366001041003643c00603103554070040e80100034624078110703956648a4980804168070a90740400c49902503403040c0c640c40c0d80503400824120741c240d5240b180314003c0119005050041c440e685510703002d0803595004d40c2c801c00041c0d5844a196458004400100d2902141102140110980400140d07100d03002001a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 796250521 1250 796249271 796249273
    0x501051f0314010b071407062016090c022505010507080f0c0319051c0b120a061b0c051b1801030308010501030b0d02030c060a0203070c0909031709030a12020408010c02 74
    0x5005c16003000e864003110740c424200c82d40e100d90030500c03440c1c0d03000486116407048030300d00007600420b03890698101503c00e0803c044a040030b40c800100301601d50460030101016800b42c868840240340c1c0d0b040016035401c0d001081a0301d101c01004503500ca04001c1040d039024801c003071708140808001c20f00750f90140d6007041c0a40c0c0b02141e501c0801c40304400744c81802c4d680d810014a0072107049000d05010b82c0421000054640e10b0319074103402c0c0c82e5020303e089141c400710103480e6041102c0c54008014002c010700750340b880001b83c0d00d074a166401010603198a0390020000c01e001c2000d00c40c0b00e07000448842c11035410aa80c1c02040c3d0812240700b0000c1e01851107500d03a41510b41c18017000404403140142860300c1a04207410850158a0110749030242080642e08a0707602d000c421b005031f1039803041a400a042010300c7d1070000d031044090740700e4120300e44a0f41c2d8600c2c940d22500600c0103104e50550f04852130360401c200c0c0070129405a100941070781c0c000003000d81403070358983e821400c44407500704202c05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 796251771 1250 796250521 796250527
    0xf020c070e090607081f080d080106180302030616090305030d1b0c12080c0912010b0f0301291804030e01030b03160902090d0b011d0108010501051f0314010b 69
    0x10a8209194071a808803a1034010051403804110042a000000d00119402400c45000e00c1c41c0d086609101d4025282000c102c07043e079101c503c001030401d1024452000022884980c011200c0590100c0508494006005201c680c440442000303c801000c1c3c0340e4024401c66841c008005201440545011006903900041c101c40000701220110071124884007003100441c02c22001429070804481e51841c02d141c9040d41d07981d602d4201c012445039002859001c1c8841004502c107100540ac508282501a600c01d40140d007414149401e88640d03e02c00f50015414680704440c21008034045051010014040b01c2420360f4000300517540d51060b41c0640000d1300540c100e884a5806008081d8103039070590082c03400c1e07002030b40b40707596014240c0240044541c0018100c240380d6220340e064011980c0054000e68036507540c00c00a20300c440050840303020944140000101100113204050482d2406003611001e50300c0c00c10266000510b0468a50505a4890400c4900b02160751018040c00d281810b20742d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 796253021 1250 796251771 796251779
    0x1804030c05070e011505090307050913020301060b160209070207050a06082221031508010c020609061302130906110306130209150c100e150708040f03120f020c07 71
    0x10400c0710b180c03c510a548080300c0100084101c01d0000009001c05251541c0c1324807104d03001a040200c10f0b4401d03940200c1c20801d10484c59040f294000100744210000c1104c039641d00d04d4003081d402001921500f0542c108200005070070148002548150f492054400b0142c456001600c00c80c030a800c60b50005090305c0401000640a80304c0d5240503000348405052a11160748400702081c814500403050b624120303411b500d06000740c2041e600300748aa000302c01d40d1503c034584c0034000c1c1041c1c005a00180724241c0440c481441c04103035640580c150b0456500c4941e090780070b000d040000402c08604a540d203100c040040f50f800d1140c0c20440e0400b510540c0d403070800c0c1c0b082005600343c980c411246644100f00461650752038440410921b00045440b50b100c0042e040c4050500880c0303c47d4100141c00c000c1c2c140315415011a940000e00c1c003030031108440e80c030303403880440b00810129001440a5220714211022074060310350000411003004020400301c0000307411506903004900000c80031b62000200388 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 796254271 1250 796253021 796253023
    0x60510050913061104211a090a03050319090f05070906060819110a030c03060b0c06040f0c051009051305310b1321050a0e1804030c05 59
    0x100401084030708004030306108454030040101c02200510301e59403921a005500d01c0300c1d0580c1c000b041c201401d880f48400d654161802c961040204464901c504002031440012800c64103010302e09080003000303500360550781612140d202901038494075014248c400c0320888180100c4040303a00c192000400381d0898948a0300d4049c483e040001d8160902c1c4003400100c1d4041891503016144807010820700381c034034009400405045003d1103c690000400390700d00783d05a045030344481c2281d60100035a40e560581c0d5052070095048901d8250402000304004c104400004187d103809682401240b940d40c0c030001c0c440581003510003001c180010410002450a0008a403102007000001c4c412882c20b000c000c4803041c3e07541408496120300344072002050364003d45000748503070f00c1982c080a0b404e000b1b4000452007414581151803881c0086401041a5000e07001001203001e600c0b00d42c100794900006961141c100340700130390400c41c01c9442e681030030b440da401c01340143d0107620b41182449003400c0007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 796255521 1250 796254271 796254301
    0x9030105090105090c0d111f1407020105190e09010609090b060406080412050d1503050d020f1f110313031205090303180f1e010b030a0804050f030304030501090605 72
    0xe11526450f0000704004400e02054440340d04208583e0115007200514040304401e200040e0a44c1040300891403885580ba07001507600c080302192144600e01d039800b550014180f0605a000b40050802d02c601c0780499030107490307469800f45e02d081440e00d920644000c148008400d9005900050031000d08010030030061280c480310721030135a6841d00e011304080303024000700320181c00117016040541b034101600c1c0c41a0192140d040725400e050020b0004086511442600f40c00141c0f200d005040d0940f400a000103030511401c4144809403140499941d119802c01e25044402c10300a51030b07800e9401c00480070307801140703d41c010200201c00000f8030704004111016009040700c00030301e0304045c0041d0800c0003003501e521030a5000c40403420713541c0d20401c5003060000c5403800300a00c01c480c502407141c07401d40e060201c903503581402000001006010156078040d0984050303c1c041080109018500303006248408c2d91001904507403070195240c0d078444c2101c5407e0b03001d44074140d80b401807186084001c408 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 796256771 1250 796255521 796255531
    0x209100203220b07080306060d09050604030e04090506010b03090a241512060b131506030e030a050f0a030b060d05040b0112020913170a0c060c030e0316080904060b09030105 76
    0x1500310b510b4201100d0504074400c81d50003800348400400041c2d04c641d00d9004681c580c8207510400d201c0c20105140596448100f51812004139103d10a0b13400641003900c200c0c0f0308560010000c02d496440d0210a41c4c0c0d5a00203442c0c01e0403402000d800d1000b003500ca143c110300306081c03103207074107200c00c41900420102c546404108130050b40f646010030403901213001c030880c556007103038001a00d40c501d0800184140e0984200408440c1000d02c520085d0359141e01700001c44200ea203041c4401c0065a8131203450781b180e00c0f4a200807a0050100e4101e00041d5030240c00c214026040028070b04099100007019034020311180c0d45185d4846041004110100f55100c0c0107140ba01c0c41000b0522a80e8005410988010031050150101490040c180700f4000702d500c8504034044001c607a110301b43c80300188040303085042070340c601c2e040c04800003540d80b09124100004031950f0145003001004200c0e641c0d0954020030950300c1540c20f100580150b520351186100404204614070b956400395814035003504d81c0280 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 796258021 1250 796256771 796256827
    0x6130f061b08180406060e040e01021603230f070606050d0b070c061b020a02190b16050f010c0507050c030604082b0c091e080d0806040209100203 64
    0x1c6680202000c003074149129600805040d118081000c1800c51210380101d0b4079409403c05200041c020b070070101508040000307407014414100d484400e03600b0313482800325070300c00d041030b030316460003c00c1c403a0a190030f1071207551542c4616050340e036040c01100c0d0041144050026000200e0b403080148a1103094028041078404041080840d128142546002000c642c03c3c0090f0044410070400e41d40d1148001c03681018042a002c8032000009580310b8003040d040707001d032000d0781e191101d00414294140c00ca84144a80c1071905a0070407084c4000d03444004101d40e82d11441c0c070790082e404420701614070112074659585413a522982802443c2c00304006100f40640c000c2001d11002c50840c404a0f001032144100c40800f0b9840a0303400e403c8200d41d02c01c180011403800202c1c0002945c0808004111280020000e0540211511842c414801c6104000d201d500192805404502501c0c5c0c45602000050ac0181040810804110a01c0040780b842006800014400150700080c10a0018404a40c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 796259271 1250 796258021 796258037
    0xa0825050d0908070204060303020607030e030313020105090604121a0a0b15090d0602040902030907061e0e01030b130e1006050f06180a0b0702150f0313080906130f06 73
    0x51000e4060301c80c511680c8880c0d5169111801404003a0040314a0700340e014104004a950320705009480304007e0b83ca21001034141501c0c808096000016240245660074641e5085240c65005640a070b0000a03074a42140081c0b00020b03490040c5d5488102d464080d9525078444d1080d00c00b00004a040182601040c0b40741c9404001551210f03141c1540d400e12036000c51b0381d68410703440024549a1100700083c07036103000240106001441d50091401220180d08540e0120740740c1d00c042d12140058001d4140c080c545501803405a407082148040700074043c1030009900c10a0340224041c40c15044d03c4c50880350f103540c51821440c0c010003a07090b0030b10300040c2c1003203000c2c20440090382c9401c00340c250601c20341010440040394082e0b001c031032450390801014803880036920b103d00c2207030b40c0004400f80c0c8a20001901d40ac480903140003229420b00c400106545180c0d200e1a0416021041140581c4c0300c103c140000c600f01d844000c014500b1041407803006481034601000c0401c0c0c04465044502001a02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 796260521 1250 796259271 796259341
    0x10031e11060c0a0b090331151409190b07020109080106050a0303081909030c0501050705040605040b03040c09021c0e0d05040315090c090506011d03060610030b060a08 73
    0xf15034080c41070b40c00313a00510240c945242c014514001d100f0892440c50079514099031003012a0b40200d941d0345141c14085180380c2c0c50300004104080a500c04000c610308400c0c4002400c01c0324001c0c070a800009000142052007001b100b205e03052940c121140f0a0800a614000e541c0c00124640017405280028030043e0b0521010890030451407000800f408849008107005042c04442444001c0d18184200144045400c00600882080703905454552070500403440551107401200d0540704142c56017890701e0f2802c0c2880c3c405510052054a42d81007034507022803085000d00040c1594180c0444410744441d40200c403a0490b02c0507450649a54400144c0e4000c642d00706c0c0640d001c590300007007080090b10078402e50101501c0c004400a1a20100c401d01240d00100d5a120713131f00481c1c0a0341c5115a003544d00441c001180030500707196a05d42d2194001615901e00b0480400c9201c00e46e240c04a4500340210108480e904030100f4600800e00200c100318100050031105000f400505190301003603840 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 796261771 1250 796260521 796260523
    0x2120a0606170907060f0203190f1e080606180a0b03100b0c0d03020304020114041e151709030d0510090e0610050d0c121a0615040e10031e11060c 64
    0x4502c40d4405001c049201500b05078008e105507071404822a0f8400308003107000000074030705400c00125202041a1008030a0700500307100c0e4001c102c4c03195441c0c3c482d0585451081080e2600481031310003444030410502003c030303241c001c1564014245a8441a1642884e03503100780441501d80042409040030302804009400015807242508114100180c1d00c0d1a1400126500354210106605000001400182401440354040026140c8000c01c035180364a450034401100f1070f9148541c0004c030032014560004200015881c0c03c001c6a42c1240c0c506464005400251002210703003002815001004024611481c05190724012041c40035140314900351642850544141c06614052515446071200700000403004002510341010322214000c46807030b156100c00d41401a01581840700070106689082c15840c0c100001c81f0715042c0d034201800d0003003204801c40d0041003070068184500000000c5215007616405541054000a07000038090030a202414807071248640501d00401502c842c50304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 796263021 1250 796261771 796261783
    0xf230d0e01061208220515030601170601020312180706090f080606060d0b06070204050a0506120d091e03061404030e150304140c0415060e0301140c0d02120a06061709 73
    0x280c00a034170400031006117503403010040300d80115810008207150040c100b11800043c0d41b06490903a40e5002a6056081c104c1d823415003900e140380035034001d10003002c0941e03003078114581c0a03480411035401020031031840c1d840c1c0861680304001050040308180141000090b4040141c03100308020500f50900e80c0c0414040d2040f07005d84151640c1d00c0c10300d20000d40c4c618040356400c4c1d800a00c01c0c8994100072240a0081074140c40c00c074800d801520000300544004160305040007600e880c4c901116181c00320300c600921003e20010f5510040e80e001000044103881a4501000420001d9200f032406140c00740000b1507d410b040e21030446840c030703000c0008443d02280d5100c4d40c801108820403803208202803510785d07001c815551050038081040d810b03074541c10b08801258210f41c2c0e080710309030302035050500f22150995080001c840c0480010940d0040c200104540081003900502d040c5050740c5000d0001001d0b41d0301d010050703c401041040369409249821664003a902201450400603501c40e0768803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 796264271 1250 796263021 796263037
    0x10b0a05070f0c0906180b0102010c120e0712030201020a09120203030405100c0f05032d04090504030c1a1504141504060f260d0f230d0e01061208 64
    0x80540c2c41c030000c00c00807280c08001402c810f03405216158075841d40c85c0c842c0b031440704002d1a2a01d049290a10b41d0f2050080d452aa00551501d044503200300d030000340a801c00e08401440340c030075101d00095600c2c202000c0d4441a019900042c4c41d081c1c2c5650080000304d6030303031105501c0d40442e402c44026940c00300845003120700c210f0398002100d00b01d0038103a030302c2101514007600301c5210340540f00500c0008001800f90303d803803c16150246924070380c40b041c096150400608201e0b800c0c0710030f02c0310f44101d51240741c0250007030820700c09030201942da071080b0b81d0b1840c040303444c825600750504c44881c015000001d00303075508940500c04003d400c640c145548000622604804000760400c1e070541c3c46643c04071001d00707003035107900183c41c0e110711900001501015080a070f0650b000301296084501003402c0a0355440b550700d01400c0075501c00c04942140190034100342c112500288810700310101d500501d040005014049070712040351103102c1c21a03d003507000d2106060003400d41e00005101d541102c16407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 796265521 1250 796264271 796264283
    0xe01030c062d0c0308060a0b040308070c0308030709090506010e061c02040b0a030e0c06250302011506031401050105180405091009031d04061401120905071d010b0a0507 74
    0x752800101c40d02c040e20068590240d01c420111100448650044010280740d010f078075200d41503101c01003441941c0075203202d0a03160901c10310003440005c07a10002410644c0c0507403150f440460b1aa2541d00356a84207a404002080300c83f041003105444074000d2a601440c242840d00c001d208a1004c24658415168020314106126615004101140e410f44000c1d01c8007144141e151410814040c000340040c04c810b10791032140318401c003010b10b094021190464184480100e03c140c0030048080020341c01d4400b1000c1d5500c400c82250160000c96400e401400035550100e201400c0b614404a80320341a040b035410090100701035542c401484180c0100c4210a0702c000425594105640c0c3c1050b81c80c80159141ca4140343d01d030300a03d03038801d40300038400c601c0701062300d0341038542420401200c000d486007a420114018180080e503003c1d5621800c01c07103c0344404550100159a01420180c5940041d2014141000841b824000c1c4041c0d4238090701c09509214075213106440042e01e10b01426200030301e4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 796266771 1250 796265521 796265537
    0xd0507030506010c030f0903080d02070b0a0e0307080a030204031703070e150a0c1b1e090c0c080f12010f3f020d0501020a030903110c0a092309030904060e01030c06 72
    0xb078641f1038a0303240d0007113801403c0305495501e0071450f003010b580101e03c103403a00181c44011609404c00361242c01d9614407480000d518044807551070140b2500301c21405010300d9820321000000c50701c4035039a0f0f9101440444516540d1411050141410302c0d901c1d00c1502480049485103c0c181200040f10020030305401c16215100741440d14020001c1c001c4070690507017400d054006001d60410500f07103034070ba600000005045460700e003071074202c0c0d041540c00c0000501e02a644000714038000010141c0d0650300480d42c0c03400c8051240c29400c500c0070381c4154803042d00d540040007404001c40342e442c03001d064240e80c0142e004d40b41c00e1404e080688010429204003c99013072400315076500a801d024194800003c0d92140c0300440090000c020124090300071850606014030103400120307a044064800911020b005030070204828001c0440402800c0000e40703811015003219044031580b440b07288440015a52102d503082440145d8400b940282181c00000e40103000107107441e0301d00d6040c2c405600d81202 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 796268021 1250 796266771 796266797
    0x1305092803121a240d06080d111216050a030e01080703020f2521020d111b01020106090f0603020a0f03080d020703020c04231501091206061a0d0507030506010c03 71
    0x2540b054013921104d0614400503a0085020080d00900201c81ca00c5041d0b4821102c00c1c0c0041e1002c481c15181e8000700c1c1c11056001d92290040000307030101072840f8200401090031542d400d40741c80c501050a0b0701050030100380c0340a560b48203440c654451f40740c3c90258209031801070715002901500781041c80d038054041800700912148409052210307040034188009104041d00c81e03100d00382d046650401406600c0002c1d6249004241c61410540903070000c040c100400c00070403000b0b44010b84858115521900300180010241c040d0492a801d071150000d0b04525500c1000707070303542083c5d201c1343c01d029494034200041000402644d00200310200c0142e6101c10914049003444488160b1542c00b91800e080681009028107042441d8600004048071a40703030b20070003c410044c0c1a0803d400a40107a00c140040391003084201b2000713128980124103181c44440f076422070384406400c840c400001017000d00300c0c00154000c49410126a040401c040c1c240f80340001e10101280a015090150508040c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 796269271 1250 796268021 796268059
    0x6020115060201290d300c020607020d020a030c151e022802060d29030d05090604030c090b1903020a0308180411030a0b030c1305092803121a 62
    0x40c0c030690348401040300c0d00009101060402d0049400006e4003119201c03905da6580c010302d100031809400030042428003200e0350801c03041c03140100e8101e03049240117400100084020504101074000218400e92103030390341c8002400581c50074841c21314a0b006000141e0305d2600490700020048480c09000300c40c0314500030b40c040320b000040c40203401c404005280250402564441c8201c035504440720310700c2518500010551072000b030301c800d51503048061074001450180000744100780007c4c003042e00301036880d00d0301503421003154490500c02d070f1502c06071165480d2041210002c2a400b500c2c005005003140c002c6881c4880901000309001e80000e008500d20191300c00d40b22121070024018480701c807800c500d8040316001900d196103285e0611000001d10b00d00404c0b0310841d43e00c050041c580442e0041d940c00041c000c06840413034140a080000c004c1e100c0d54022848203220b407a000044100e106260003850b040c00001044002842c0c0092030a20240c41c1050b40380d00340d03084807507090190b140400c034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 796270521 1250 796269271 796269289
    0x906270804060813051605100509211005130506070206010b040b070201030207060e070f0b07110d11030f210316030b030309030102120f0601032c1203010602011506020129 75
    0x307446841641c49042e10074400402c1b21080e103609403440d0700c0240701c1c3c070700139039031402045692a4858043c0002580c10380c00141c0222404a590048030044280d10180384210f85054500908801d13455108405020b000c200880e00200284010006585031440d01881d1740120300507078004010008805007507a201380c05403035009802007420885042803607a1160f44403600c0c800c101c62034a10004c00910b41a101084d031700710503003000654102c00d03c4030341003090305801240c0480b80b2010700c2081004c0e9407420840505c7c01d00c4414000c104101200100e6409102201021f000c580030810820807410702d2181401e030103942a0801240e050010b500103420b5000d0440629015840868040005640060080d01800702020a072a254840b0001101503c0802d2001a00b064a40d41003c074194465a8994295408202516065100390b403100e0358591080e4400f0005039107946520054282d805411030082000d40000c1100650030800d494544944103001406003203a40c0540d010360322a0644 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 796271771 1250 796270521 796270523
    0x50114010f0207060c170a050a02100605132705030a020c0d20033d0501080601031e021507021e030d050a05040b0a030207030f020606010806090411040906270804060813 74
    0x90786e62900b1108a0050540e00700c1a200b03c0103204088015a802c449845410b099030b5028004a00349401001400050040101d11506107500d407030446841d880401c480d0580d05120300041e45d80c4491008000f8a425030592405100364110800300300061558000140d01990b0000c0c0284403055000c0001e0600000025842c00c00c0c440c00241480121142c000b01d2500041c2d07001682203c40d043d00c1001290000d006200a030703032010005002080a009021100b80f019910002c1030404a501040055501d540280380365000840d131482145081c3c0c01c101c1d038100020b101d202e25a034510f40020380d81e0352111048001d100c400103c24400d03600c03510440740900801c8001d44da0320900400018000d43c003203042a40000c0c4090400f050440c400305100b0b000707880c140e580c9a01c03a2078071003c102540a0281044640142d141160840f80c0c54a00a0240d458014070b0300081070700d040003148040041c1c03090f96407a024a4140d55000168080040d42c0035605540b4111244d03658024000035070b01d0f04408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 796273021 1250 796271771 796271813
    0x4021201081c090f06211401050405091c0e01090801061202040c09180221040b04170f0d0f110304080a020c06180d0c050d06050114010f0207060c 64
    0x70400100004086403090781404601c50031542c2144101ca00301c0943c00303944240402007804002c8284200320701203900d400110814600804403844030110740000743c0d60305081c2d5050300100900d103440d04c11517a114100f94060303e8181a54118046c203080c4171560002400f29140000b201c59210b84ca01001500000d4000c0080c01e80ba81c50602c8400c9241c801203100780d007001810868607100300062000c40700041e042d0020040704200e0f00d40607400c1400c1404001126020003050103217203411980c080c9000d640301d040c10341060b052103880700090a00801d001407080004544206404086401101c14100005165030410440c0e502801c926566040d00803804014007041c0f10b00c1d480203011700f880d107408880d004c0c030312482404058010841a18000a01c0003081c030003074140b1814a80107640700da603801c4149034841d4001081030b0700507042614441c1e030310001404421136410403107103807103803d0816001064848400035a0381d1030f00d0203000100b1401d40815010071150540d46401c0c80d03d219 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 796274271 1250 796273021 796273057
    0xf1012030809010f090210080601050d0606180807050f09090106030803160206070c08030f281d1b0616080a0c03021509100e10060902130e0c180402 65
    0xc10300600310241603564181551030b280840f154003180d80b0400c00d005a0180440f00d09441a0505440c40740c0e004007180e060210400100c800428588180c20240c4030341e4aa02ea0464402d2100002d008a5a08190030303a500102d0188026942c0b07190000300d0301d8003242d13040369560310300e004140500b00651000300304a00102c10300084011400052000c007007503034200c070a80c0d9102e4000320b070b005c0319a8001a002c1027003000070682c8101416607860740440c00040782200301002070b80c3c202ca50302d401d11800d564590b0b9036030016100e114010420036141c7c201c4000305a100381c0302c10441c2026513080c2d01180b04807000914072001d80903000d405954282c0141d0385a443d01040080501101e400b60710403001400750811034081c1c4401c0d59141409184080c0003818101d400c0380240c401801d5004080340c080c07085410301080d6507558020980505071034071015865409188aa00c0761003515000f0544000b52102003040304007402c802d44000d02034031145440d031034130b101000c14000d110301550404007410790 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 796275521 1250 796274271 796274273
    0xa030608100506090f06090403031a030d050912060f011202030703062c010903140a17010f030605060603130303020304020f12010c200a23032b060305060f1012 70
    0x740d44400c0c469402903401348000c1d500c5260407203020350f04680c0c99500180880c00714001c01d100e0341c014055403103003c200c01852600b100c0064601500d00c0b89103400a2800030380322045050443d40321340540b008000404035030421402c40503403202e05009541004200c2000e500555404001d11002960071480400c5100c0700208518240e48200c3d02200c520701e141300000c0c40b409014800e0300a25600750f6945010410f0241c02000580c1c0a01005800c020010f20300100003029078220500038085c401314200f2151440c90888107641c401007805201d07040071310410800c01031541444038801d506203001a641e81da544009444c00b811020000e4100b8207103694008100c03015480b03040002c0082d00e4403072804000300c40241e18220305159418650300700c644420002400192a01005801103100c80c140d0b4081e64420741ca5a0400030030050032140c50906848070303c0244e0850340700616400c905004060650f00c541d0f9541201800748030a07000c01c000040c5400d441810504090100c0307039040c206500403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 796276771 1250 796275521 796275553
    0x1050f040e01240e040f06050301230a0605030322180e2107061d01020c0715051323030313050306010b0315121903170901200a030608 59
    0x209000e0f00b00e42c282c039000e001079010084614080e108206540f10f80a525545003800003821152000f0380b05c0503201da8021496641c00e00500d05410f0203a10754201e00064107680007007600002e0321240440e85004400e03c02528044111040d0f00d00c16080f500c07510012180444900c403807a0b00140300c1a40752902c05800104580004800444000440322040c028090300c00440c5075803100001114020004980004c03aa50088416840c551034840440c0081c0020b1500366030012010117440c1e04900001d1002c09003d0702c205421034006d1030300324244020b82070341c110681c0071801000780c02c0d03081c154100d0384103501d611000e04808002c1c00b5252039582c0281441710f11040d070301440b031090198000115031401c00c68252071041c0080d03440c0c2c11003c110007041c03000c001a1600804600d009501c0004903d0704060a040c8000d0300c40c1c0d48d040403542e1541a900421034018241c2601c0f641000048030b03108213440d00d1410300180314030707255994003040039059004100701d91080489000f040e500079007481b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 796278021 1250 796276771 796276799
    0x12090302011706031b0a0902130e0a0513030827030a09140303040509070c0c030510061e03110a0509090705010f021c080403030207020d050703020f030a051b01050f04 73
    0x8400e0320b801d010106084404001c40500701d4410b40c05510009900300c5c40b448154000881c008043c211200c070035291a01d45060364402c03040c10400000440c410060011110043e90340011901410040c40c00d01c600001402c08000802800f007008076404508500304084c3e1052110700141d030780000c1d60801070301807a16900043c010710003084a840002500c01c0d40030800710120f64000303015500d8541040c0c100f200c1414060203520805c1614211000000d0030001000007542c000c500410089500101c0c0a00fa2036441c0c0140c103c01c003202c0843c2401244041e034103c280d95000c0788282c444541900443d080c0c0c00d49501c800d92012000d02404500c03c4085904020364170301380c1e50548001008181a0b982e20809000c4400800c0841211482c0500c560039141e00280700303180140c5010b00d80e40004204081d0303c40107a4440e001024204210710302089042c51114054002d41000816600e540e504c07003a04c0880e0400503110040c4150aa070720450446034019a50605561139603118040154441 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 796279271 1250 796278021 796278023
    0xf020a05030106030f1b120507030203011b080a0903050f0723120409112713110a03020c0a1b06080702160513060906080c011d060322120903 62
    0x11052010104540c1018002d01040c0d81e04402c11a8040307050707070385441079005211800b16116408207408243c400c030072800310300583c4c014002442505c0c1140101402c40d0f100300c0c41840c481038900060b009480c3c1002505910241000340040c041106090554403441070195414004078002282810010042c0c1811603410b200d5210107000900c103045036540380a00181c0890030341042c0001c200424454003c090510303600a2090704040c000e107100c0d8050a80c4210038947d0500c001000702c900c1c03d1540320085e6201008000b40a004d1a0420461503403040300c59510030150006003020611004116075000264045c08800c8140004c0b07081071400e524a00801000590740c40208481c64400604080c00c881100d40b522000c51a1004000584c0f59410f0f00c0c501480e100c000020f5004081c0c41400c005084400103401c500b140306000604030750044648400c07800001e00342004540b0707030b6420780b075011083c640804110084514082c0085030b02880c020007508625500392641a41700c04c04030212 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 796280521 1250 796279271 796279279
    0xf0302130e071d060702060f031e0f16092709020a0f0f06050c06013003020615010c05060109050c191707020d320c0105060a0e1905040c05030a0f02 65
    0x30a0f500c1003081003074413800f9070281d4490000e000344c044500340c4c0e400031504858013504000c40103040d1025082040c80446d81c440148046500b0400031403040f025000302c008062070425486420000b0380030314100d000d0310f600c0403c041413200203070030502903204000301a0000d101220003a59506441d00b9044280105200f50082c1140020400e01178030a83e51516240760283c0016030030800765107445588080664200c1c9943c4000e1194031890a21240c00a07000340d028042d949450000c1941d005800202d040c1080380032004034010070004207005054039485600130540361a0441c042ea4203001d20f094000c0040655940502c003287c00c42c071134031070815091840903a2a600d050050340c07504042011000460500c14419042907030074a8071000d1001c903403c40710b24800e50340310070a80c40e801c03812010509a42d140c00f8480103260505090000f0321918035189954604000c0b1404840c9404509224060715032001c10100704030340543d00003401014040340d05c0728545050926030300040030310036030103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 796281771 1250 796280521 796280567
    0x3070203160b04030204330e090c0607140f071e090203040506040f140f07080717150709030210080a0b1002030430030917010204060f0302130e07 64
    0xe401051000714100c44228410b54289403031502800f01400382c880741408000c0d0204520301148076800d00c040162402c01042c00c9020307050070785a016401010703040c0303089a03116811058095442001301c40090f41d101d40b42070011801d14110500d00840040c0b4022a802035030004a11035108500d0303580d4070301c54040b01201042e5140e002d40124032042e03401815580204001501150036140102031940c41140c44c01c06c400580c0c0380c4142030410240800c100ea41000e513040200304020030002000d00380c0d4440c1d2220200e44a40d01035981c06c80d20f805c9100b4030038042e0020300d1150095038868000c6401502241c20310041c0040100450000c41d0340d5409640380c141d0702d505034180304036264880c0071190003d52a050a00c01c00e030708002c40400d00c040101595140400c040071145801a04d000c0c440d407109420103040031454149203030441d8610403180e02c14042001035039400030020100c08081c1c20b0050703a64082ca5181d151403621901b0209120081c1d106000308190320407030f80022044a8015201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 796283021 1250 796281771 796281793
    0x3050d021b0d030c060e0c1302090111010c09030314162a050307050f130e0a02031c23132601110702060c070801050109090308091c080a0b040e03070203 67
    0x7071501502e240140015006104d50000610550300000c0300300502402c403007481e1602d1000034444071407075001800550f000f1031610310329604101c1d2880188041c50090003c941c107080c004094448501c0050100a80c0c0104410105103203421100c80140c01a00401540380030b050110304840c50300d540590b00650621000070a00389030309900c096900040180c10040c3c030b01410040c00e50b50039074000b41d10280040380100c0c42c90242c800c42100060036005440411075900405040c2410401d80c0044030031180741d1104004d6100e992a20009281c0b02d1460f040310b01ea5441c11410702419402400c01e007a05403001c544e0604040943c981401040320441c006a82400341d1820b03110894800a019241403240b0001403400c98064500c1d19919400c40302119034468450342074a0080e40301c0300040d130365001c0304018168000f18481c1d21190900040c03007044481c10541d51300040b0754100204208560b40446d0603010150030200010b64010400d11502a0022446440e03500c0454124401e20500511107 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 796284271 1250 796283021 796283029
    0xf0c0a1202061e150d0f0201200d050a0c06020c0604110414060d05151303030f1404152d05180d050f040902030a09060c020c1302090a03050d021b 64
    0x922070944600c41908948001200f00e41068018062000c003400321030b8840b40588880341c4064907140185102042484a40005010402c16a52205000300d603005003208500b00002c0c10b9040c68564500380341da0740040402120030402400c0014000d90002408900342000014083d0045000c2d075541c2080c2800d000800049542c0e51180e0900c100c202030025001d460011004110180a2025102c2c400d441402140381c0301400c48500203805502c018040c181a8180700304400301d000f1002c01c014004041d00c0c581a00c07440140010300346001ca40b581c01d101d000d42c0d000400311003d01c0602108585001710507124060340911340e040c0d05441d101c0014504211340c030040c14a90110002f8111400304640200e46c01c0d1b00844c220111107104000000707041d0640d10040d8481e55007400000f91040c0c0c40e142150658001601050455000b06803141c110b0340e0b0105103446d0f1180d1194016690601000811880d4480341e001401501506409130130403500421109840c0d404c4861082d10104030b10100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 796285521 1250 796284271 796284283
    0xa0e0402040b0405070e01110a02100f030c1b020919020c0c011806081b040f0909050d090311060c0c0402030a050f010909050d050c0f0604120315140f060f0c0a1202 72
    0x3540082d61b1020f1150710313540521003000701034581d0410b0350848151500401c1d80c2804072402d40000480c80245080c5140c0d051050100c0b1180740e182194100901c02141e001d694410384000c0d21444040c0082040250040500c588500c5440d01c04c0d51101c00b002030340c507191011440ca0502081440e0358401c10004031520b440140e4803661103c0c1035545801000f00e00b0700206a880100341d03401000081528880c0030303100c500803c1c0c0250003194210540c500203003040c0d5500f00400900540314014800181c144a1850b500f420646d200f03910340c1c42806070b883c54040c2881c2c80700d40140c800400c2c0611180140c000610039010704581c8103040e40e8614548044502814000d0215084040c0c80040c00d4459401032004c030315000d0850301c030400c00c0202c5e40d041483c02c1d501200d41e920300c420010f41880d0107009403007a00014031580e041131880e004110130304100b940407891003050820002ca40c42e580790400c0d1a548280000c0c041c0e00c90084803c1c099844414000550755680d02e1065102c11510011324 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 796286771 1250 796285521 796285531
    0x31506080f150d0b0405011d01051b0a021f0b0108010b0c0d210c0206070206150a03080d02130905040510090807021e0607061b0c0c060804020f0a0e0402040b0405 71
    0x74603840d55507201108801c0700040707404681d102c41070003101c5010414241060780282c0c09680002101e10707440c50808000d0608003482c035890b03410107040000f600b80160310301c0c1c0350030498542c2c1903a441003942d049040060190691071201144540d400000541b0b40c8070401f020303004e0b03d0b035000caa600c822070714029000b4007482000c141c0c00301c0380d5400018465501c41c100d500c6c0078078081c1c052005040c00034040c1d07118003e032040160701c800c7c10400c2c0d80d80d042100c150024a5000100d400300720080c0851030307070000c5020140840b20005018101201d040e8102c400070000900209000d0703844140c024041c00040d5026110f40c4506541e81c001c0e09018458040c189900c82ca21620703140c5030303600380040800c03010040301c0d03a207807003d420380c1e07154803a0300080c19110b1040c90002036115156a0102a400003a102003013001840c50a500001d400d1001200a48900d4103005500f6611480010030f0303040600b01e120b030401da05060004013003070600c1200c1c0c001d031b100307d40c14000c0040c0c002c18003044480132a6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 796288021 1250 796286771 796286791
    0x1e08091b0603190b220c030c0905010513151101151422020d0b0a0f030b061e150408010c030c08011a0f0a111b0306010612020d0c03150608 61
    0xc0460a420341108a0fa10b401c051224041455410100064410494a421500314130103642e501d510820051040314400c018a040802100101800080c03242442e402014144840082d88400103200d00b10b1300801000740100c0e90004820340c01000340710a024102c040d40660038001001d60302c08006c0e030302d00250b43c4c0084940e0710000c6114104510500030b58401a60030302c00004042c1070b240c56000030152050802da01040d0944000c1c10302c80d8400c2168002401c0306918070701840040c03400d414050b00044101c03481d000c2e01d101c084181c070880e0f5014002d6684002400c10000e80d2000e000003030070440d00140f000b08807640107018180c040e0355000a511001880d154010b2082485148080418243c0301e20707040c0c24058115021b898076031007400c1d04c40228860400c084503012007040345034a001c900b25000b40c0c81a03484004a581c404060040000340200c2104a00380d04015a040d1056200302c00414130800c88994006001800240c0c2d00714108400c4500224889001d07218a07400f902040c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 796289271 1250 796288021 796288027
    0xc1203151712181905310e07090504111302120610050c01090609120903080f0d0e0307060501230a140609061b060f0c09101e08091b06 59
    0x4000d54081e58811200d81903410202506180d03140c03250280140c03004c001003421101d8906110801c901c08810360701c0b03401c0b200020004500c12440071315000c2c1e20243c55090120702c4090000f8003505000464215503885482e01d4100028030028907614210100e0659188000401c03040062099100d0303824490100c24850000ca407481c01c000450304040a040d1800504103026040d25030700352150104141c0c1c0d445e4445440c841070040040c1300c1341085503d400c0c005003c0f4691785d40d201d0b10b40564002c450745480c000c0341012100e00d141e040769011a0480d015aa5102d10a20301040106428090703518484003c5100104030402c0c60f0110000324401040031250a24044200f43c400d034003c0d0f0b41c0d5410890501060549840c0c03d00948200d504607121010003060320030015140c500001c118940544002c0c041c4200d0381030310380403580c00c09010382e80c80c80308107d4400c0607510000f0355920907030000203051014142d02d81c040039481c0030b444203409650358500e9002440008461090203e94820020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 796290521 1250 796289271 796289293
    0x51206010e03030d060803090f0612010605031e071e020c0d0f06020c07030c080610060c06051e100e0c03041a18160e0a0501030b07030c0c12031517 65
    0x5203100e03079426900800f01c03031924402940150a070f486650207145541c2c0003289002003450580000c000200081e1001e038180002c8a02d104c400e058180304031b80c144503000010440d00f4421041102001d07d03021020902801c0c1001e00402494802c00d040c448081003074586070307030700c0d00c0402c80c00484400100340480301c600e282c8814004001d4210111801c541c00c108494030310340107000190081d4000d02c1c061030303010302d0900c04a0030810002d002e040c003002c0200040c040c041e000704807031941e2908a00000b40703542e03501c100314090000350328044105141031010001410f0100200f03c043c1c8080c6241011140c54032210051140000c0d2002069404800d010b0035083d8441010b042c1d11035000c0e207407a4481440740c901070381015040c3d03042c3c0b82c0d582c2003a0020320841c400d9080040d00030714841c07020401503155850303100004030007070044404c242e12100c11641c1c507842006448030041c0c1100186001e4140a0005801040c0074900e0f240308180e560b034001030304a00c0100461965087c0006800c00000c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 796291771 1250 796290521 796290527
    0xf060605030106120603050d0206101508010b0a0c061515053c12040b090c01120e2a04051807060c1a0a0606020f010e030d09060b090c0d050705120601 66
    0x13402c80700d41a0503960720300002c04031f034080207140d070700040a8000c0c01d020700b00b00500694840c600d0f0418900760503034a4001281c254000d24450440700c040302510740714042031004451444002c500580114107065608941d40c0c0b0400956048941d407066008004205480640b841c0c0034035600e18861884210072036260300310314001c91036851306c810640d4504a071041070b0001d0941241c42c03041d2102546204000800041c0c000260300034040b4801042820300703030b80000789203010505008a540740c0b98203403030702503200070451202d140030303411140e43e000103240c000001030160701c0608510542c02e002c086031902c280d40c1060706698404001400280c0c0c00d00f10255141c102720102190f03544118203260401008804113070b40501d41c240c002140d070700d1805400a1508030700c65081052a45041002d252761040081151a914a100e4011449605604042004082c4182c45030780020310700c0100400703001e03003d00812030a0709086081000d42c407404801c03550790050103480d640300d0070044007080035580 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 796293021 1250 796291771 796291787
    0xc06090606042018040219030b0906120a0f11040c0201021c050106051803120711040b03070506071b0b0705030c150423120a0c0203070e0702191a0408030601030f060605030106 77
    0x4005440986400d4031105890407541b140d504280002740e0710020710519240002e98942c0040c0c08076001892080c44c1c1403a96180c00d5903800041c910700001815500704003010b402d01e101e40200400030840c2d010030000c041d020f9440b9004240595515480f10441603441e84500d034180d5001d5907aa0b400d02c101c070480c5102d44140c407561164036200742d90580212641c0c2c1382c02806035034410340000c07100c021501e0510040d9441d0a09882c4603070801c0134140100d86541e82aa00815086242880551051800803550721140c2c0c2181100c1d4100152400c28844000001c2c142d8029200444080e540740c1602c100004038141e50007000c1e0035940342c4580d41b4003500c0d05902c0c40403440f83c0584030b94018031540200568840b5520102003644270000c2c01c02e500e000e100c0076000f0b0655012004681c03a107554000d4582540c000301100009440c40b041013406404a40b0020304a05920150041d062905060710590021034416000a041011207451f1180b1406044200d41054403440c0c156401c08800382e445407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 796294271 1250 796293021 796293067
    0x40905010b0f0406260a09140715031d03030103031815051605031201170708150112080d02030a14090c130c05090310020703030b0307080a170c060906060420 69
    0x15185a000000460310006141d004501b641800121003a461500500c100380d22003c1110542004804118030924000c0112064100c2e280c0040c0400ca01461110445483c400100c064440800007008061b005519401e0480705000c0d04954030b80d844141103044220720006500140e010b000b0740d40700000b04040040d1080c81801902d041424a004c0f100446400f640f010b10480140d24404600000c14018000074004c480080c00d5148107810800b1000e0006100f2040030400c00d100210a0010300380c00c2c0c401d06003c6030b04c2555241440503201001d4254880e1040301d60000e43d000c1800c502c1c0004482c6160200070f08480f0110b0308000640b4024074541c0310b0041880320822000041d95000e0080c41ca401c0c0c008040181c0ba01c2c1c0d03c0c14028200d0340344980c40740c000ea10400c024000c0e181c0c0042c40c40152a802545d000303140e035241c0f1184911f0701954007000032511410080c401e20500108845100b22800e91701004000302a4583d140d9407098100706900c4c4910401c000c40e030241910541c036240c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 796295521 1250 796294271 796294307
    0x13170c1509031015060c0f020d0501091a06040b090910051008030c06011a040e0a0905010b1c0308070201020a0e190e1f0e100501050a23040905010b0f0406 68
    0x3101440303001c20308024400c3d200000d0556a044520039401c08032108801400c0103140c4030007070425607640c2c1c0c450110300c40700c003034818402c032802001000400d4100c0421290312041d038410080d032500f042a0140c0050780c407140310741d09002d20340503541080700341584601700660045c0707001c1c000e00d144c40d00181806807488a94840509000c80c0c540010002002d40b000440028006989000c184500c50404021803901551040000b084454810701c541500940080e20009400b001d501c2c0690040c8159900d203500a51141d0f000d141688200303a64510302c41c0a03031140035039035981040482c00c038030540d1104070100741801b10a6401c1c0c00d00074450b01d2904199594051405e4035408003c00140e0100c0e02103000380c021404040000168101d184010300c0041184076650403c4c0380807090620007401207070b041200200701c00c81c800d0b00c0340300c18007405103c1c5188032000c0403041c2c01a092641c46801040700c0300d401c2100004528a080003250040c466031802c00c0d0134241070140444444002d807600200e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 796296771 1250 796295521 796295527
    0x90f0c081506060702010c021c0b0615090915040f0f05090a0b0a11070b01032f06040b07080714070503010b012c011202033112030209190b13170c15 65
    0x58481000c0b0107a10080d02d8440c1d109c043c09440c005020410080400d0b0181d9003200e000070f0560800419540b003188104c2c0c035510565a104840c1180755460404c240d405828a0101a2941d2090340009910810385078248820b684400c91107507103404802006141d11505000522034100981c0003070b042445c0c505aa45c1b808000742c42c0c6050491080e041174801c01d8400116000b1446a072480148070341c0d05182181c0701d0030448000503258000c1e0b20540000c100c1c0029420200440041101c800b075900c090503410a000901156556170300ca801500e02a43c6807200040b45503008146400400002312001d1140c4a95200b070000c51304256040b060502110500301365680545002851007100c5480c03040d03410110720066003161218950781f143e81101c40d040844081140429a50041403081c03c016aa1388007000101c0c002038403000c110340c04d0018070000400c03160001401406051896454003041ca5110070041c1d40100c151640c12000303034004038182c5500c0c2007403442c200341c3c548001c5000e42 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 796298021 1250 796296771 796296773
    0x609150d0b1f060c03121802030d03060f06090302060403060e0f06070e0a090c120507020717160504050c04060311090411070201170108030a05090301020904090f0c081506060702010c 80
    0x12501505540004502544501002c10440200140c00c024050361034801184002070724090300842e55000007a01751a1181503058211454421440d0066800307803c48200c540ba480000300240050302a500300318104050000740301d4402d0004505403038004102074501482d645c0c4450040c081110305140f240210701182c000d82304103102c0c40b407046c0219155103003a100e80b1003c100340420310741c0090b40b12a103002100001194407140c1c0d502c44a1040a00003915192841c080c0e16101c4158040c00001d2001e2801000859000c50b5407003140300b0318441150348607207940070041a104c045445049450741880208185440b80d04841c180c00700c1220214904500e010215003a503100d0340041c14100d0001134960110f50f808201d0300520000701b0706003099541407180302900c3c1e2088080b92010460041808400c95500390704480c00280000d1041000c26454903101341c1d451900903068031381907440742001400101c0400c1e00c0904400c3e20601e00f0050740e0305d00030418641c0145d03405078100000e50b0708a034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 796299271 1250 796298021 796298033
    0x10050402160c0504150e0712020c010f0f090f0f17030703090201020c01020115141809070302030d0203041d0405010b0a0b130503071505030c1204080a090b030609150d 73
    0x1c41a004180590a182400c03410701c411540c1c1035500040c040c9182c41c4019102155508110090700e0380b04040c0b00c00c6807540c4404884c03041c444115503900030b00c000389100c101e000562140c404440e8010060040e420882d10b29800c40d40d071258090403002030400c99000060303d841403ca41140310b0000e200e48880e0842c21810700760012901040800c0e41c0e01d01c03590a5603010022081190002d200034400304050340e075190b10051041c820200e045145070181501030350b505000100602a001c001c2c09146411440c280c1d45050764801a8040c3c0910140390180c0343c408412142926075100c00a064410b403911900c644100041c01600c080d5a504400c10700361f0b8580c07511070003d090300f8403440d868840303460081310414001c1d48582e10039803007420100203c004041e60150481e1550801302c1e10fa56078042140000e108005110441d0140c400c20001042a0b20014020080c2c04e5030780c0d0401cad941ca410300f820a074402550110381c00880303540012070700d1344c0308552400c5082c0040c184014413160f5984403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 796300521 1250 796299271 796299277
    0x3080c0f070e040b0c19080a0914010606091a090d14030705071e12080a0c0210260609061210090305090915090f06010c12021501060906020c0910050402 67
    0x20700b00c02c06884041c08140861500b40c190040520040303140b030009040b01104010444d4001801446200400240c0c81c403c40c0d40007081d8135410406c0e4410106c1c00c020100c0c02018035004a2010032005013000c0b80c07007004110300e200300c40858012189402e030701e1000c200c2044a10036045811103040806103c4481d01407014124003803190307008004007810403141040e9a800e800f42c148000381e40721030400c00043c0314443c0c5100c1c281c01c081c1031a50b90140a0b822509000e25180107508641c0308800302c1050381c0e005408441c40c54440c000a4407180c90f220030b1080301001501ca02e6845600d507400f180d00341c5002c1d00700202c881403039012600441520f074070341804c4e10000f650a80101c2c1004c070310403985003403a40200ea840240e0601c41c5c1e2245c0d8000d03002070540070f4041c2000000b183d0820004090340d000781d02a0b6200f54001c0700400000002040081d034401201358148000389501c00002050340c0103901200c1a6401c1c4e801600031030b2104000c2c80038103400104804e807110500b200c00a00e948480c030003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 796301771 1250 796300521 796300529
    0x6121306020c010f0b0f0f01260112120804110907020718060314010902030a031206050301020d0c02102f090a1719170a0509130e0c06031003080c0f07 66
    0xc00d883c540071080b04225264020680c0c041c6c070a40c00708541d85c2c0c2e5280c803003c0c202e41013405c020030a482c038100c020000156401b240c801408000e00081601601c43d108540010311920f821160507503030b54011540d8101c180c800400e40b11030340c2100640d40c581141c0c842e42c82000b510440c0c100981c3c3d10b00c0ca040c0c903461046c0c1c425800d03660b000180284030102d4004a400d00101c03000b0301461181d43c0c01309903500741c1410080c0030480c84031034180302010290000320041c940140250b40f649490f00b600e034010305607031a6800c09440fa103400b1080a02c801d000c0d501d1140707501c0e068000c200b8205c070421144c1c9080014009901c0e01c0400c40c0d0704503a550708404001900749009a07a40f0444410000d618160895501841c184034184410000070941e1000003403403d22035503da601c0342c288500541d85405854001d0b80c0c0019844035003140100250300c04500481c14100701d0f03e400c900501488660710050701c102d40f501c0f1507800c041c000710700a40006e0115100c0d00c030480c1c44080c070400082e4209030083d04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 796303021 1250 796301771 796301773
    0xc0f0d18150b18160e1809101a01020706080a06050306180d052b1e0b0a060f0e061b0601171b1f0203090406080a0c06080606121306020c 60
    0x414102900b481007408064850f88680a000d80c00c0501d00842c0520140714528100001c80d40114120f072a000340c110b42510b0341e43c4800000c0e00702040d085440c0c456100031941c22605d00784401800122030801a2000181038014104050911400b1215550002c1680080c00d44034840011651800c0245c1c3d40b0a950080e040d04480c41c03002a114100b500c8090b1000c204001446209821909101e0710140c0280c042c40800c14107000e410040045c002c0101c40c45646002c5580e24482c912080d04102c401c1d920441d175182e115a22444d056801d4820401d8000001c1c001160707514480c20000000e200d007282c1c02692a01800ea02c40d02070f446c0000903040960703540003082c0782c0d1015000030041242c004100c1910401d0b0070b050800816002c40b0320144611022105150319040715009104940740e0300c0016100744103003901d44441641e1809031a80843e5000900300d800914103129550341e600421000b040103281c03007095a030100c444030000c3c01c2c008240400904410008059100514207400070074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 796304271 1250 796303021 796303031
    0x15080a080706180201020d0e0126060a05032e0f1e14040b06091009020406111203040b0612030d0903030606030b03070609061202160804030b0c0f0d1815 67
    0x2140c95400c0d0b035031a0000c011101524900c3c280140c0c1c020482e0f12148140345070a09035079440700c00403190710520402c10f4130f0302034003202c8d840c014049403074215100d09820740e1882915030b0f8410600d55207144400e070041c21485101440d480f404a541c1381040325141c5001c0c0800c028810080c410200c8a03e01124901c50100c1d00c59054034101174000c0400c101110000070b01546095191400c040500400c2e407171280071801c00082c0462103004203400a0900041e045444546a0070050301c240d0340c551048545105004100c00308082c2e070000c40b4440d6920003074464445e05c17104140a40c41034481c42e042c4060209200d5607400e609903124044a82e4029580800c21916040024040315a000c9200d40640c010020a1142c150010100d004545951400301107000c20680590000c0c000c4091800c102c054880100c020301c0303001c0d4054001d0701e00507020824241c44002005c0342d0f501c83e12030b01c03445400d000d101321000f59015501c0300e582c0c0040d460f1350034207071029a03441c003041c0100b0340c0c2d40b080220380c0c503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 796305521 1250 796304271 796304273
    0xd0207060c1112031b0715141605070617010513020903071802030a0b0d0b0f0a0b1306080c01081005090408040506030a0f1a1e010203070818131e15080a0807 69
    0x3030755104003040c5254080e08001f400c0044038000b2400032000c20007440b801501682860102c2000c695000d80000003035030b440941c901d0003a403580003130310500001601c0e410300c080f04003007040d00d000c0c100d800007441c5007455074490f0250340c0690445c240059240c0a4000005420703409541c111640100c200d40c010703038928200140c40304030342c054032949000d40281e082201c005840c440c00381e074204000040e03d1059544540122011700b030200b41031a0002d0580c480e48018403206e40011041d90404010342d00c8000400d0011134100c42c040b100350881d8400c0540401050070103580803a0400d0140300c0c01c0d442c094490f408600071368026248244d00942c2d8044445e600103d03482a040030500c0038000c9032486044000190b050360216001c1d003142d8003407605000c806c1c2c2c000c00469260300e6004140301c0e110b40c03000801e0040302e46520301c040e000c0c8210313031200302550809101e541c1102c0409103264420200b00d030083c50042c16042c254002c24010a80046405c0c00c0801098240c42d00c00c41c5600e541d4401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 796306771 1250 796305521 796305547
    0x6020601033819060b1209010e0601060815060412110109050f1302190206180a030507140a06021603260c07060207020901060c0201020c030d0207060c111203 69
    0x95a0400c2d040d10b6460010310040200e9044580c4444034000c000070040c0c035907007400b50340800e0380c01c941c03040540344c0580042c0440700807003e0308460003617000c43ca42d99551070030180d080e1070701540103840300e401c11b00050204d41d0280d00d9031031b00014034424051107454201c0c00305440e54003071f41090050f03400c0711501e541081441d91200a00907400e00c0c0c100c80361407510001c6596070401e10700281c07040701c100010002280c5154107603900541d0303500601c0c10f010701c400c401030b4032007405031942c184a8070174002c840c01d01d640028540c1c01b0315505035902d030324145142c0c4a0002c000700b01c0307007185114060b9034150008039803680003070040c2c6004181c83c400e402111f46400707003e0406004c0c00c04800240740b2000c0192030f1480003000c0e4030400d90302c000303035076066070b40f400d20020720459100030362002041d80007141841d88500040843c3d407007a000c6a05e100180c0b4101030386d41c1d100122140040e44141c0b803d0080a1003200f00c4281c580c45481a00200c04550b000503102030505603a980080e40049004159590 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 796308021 1250 796306771 796306793
    0x4030c033206070c050a020d0602071b030203030702060307020f1606021b0f040504170c01060e060d0c030318030f0b0907050a150e01110f07090e0309210312010602060103 75
    0x702090400e00580d450002854507101c000300520140320400000c4000e02209101c3c0120050380100300c0440d40c0030914002009411000041d52100a8041182c0c1d41ba10020a5041072300c0e0010021418134541c2e0f030801c4441d520050401003140521800d070132080d42d0411011844441104144403030350308080000703192542c0d091a04007602000c0c0144404ca80300d840301190854004d68020030180d4a5082008003010348034035240d41218000303008592080e043d48a1810783e41a48001c2c601502e61500f00001c50a4200d070280071315001c4642080020301400b401a04640c0d101c4180407030a6580d1036800d4404031851080d80e4416098040240c0d40707000f03200000191008560099406017062098020481c5106011041c4080f8065410071030f8000c1d00d10045550710b80089803580d540320030603d80c49111610600d54a030b420100300452022011065840d5841d010b081c0e03222840d116881c43e514503682200c0f101c91404100191000e001050b8111340c0a40565002002e10b54036503d80700d01c200d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 796309271 1250 796308021 796308083
    0x3050d020a120e0a090213050907020c01122904110f0d050f0420060706020a11101b080604090b04030206180115050d02150a023a0f0504030c03 63
    0x1003d0511070f4074a43e00c400807141030740c52540b40141c8034491001e80015410840c0c015940c0403540c4c004104600e41e000075800c107000000e9031044400c003210156501540c4c013a9500403a444ea0041401c88070803102d0005d100c80000090003c10700020a031800c1002d9444100c003143d000ca00025644080030040c000c40703410800c0c2d445400120300d015110384420f540e0480086190a003511303e402c42517950380c8150f4103d1b135005039085648101e0f845000e40391800c5003501c0e403540e0113041445000740203a0f11801003601b401081e5126030145c0c0603001c072255440100700c95400303940d50036090040340e04403d86504c03a5101e90000c01e0710341408141540503040d054125042e580c10810002302c280301c45042c40d41211402e031103d09075107121784000760810003c0c01c100068141d0201d03900c40803660005030801d0030a4150307401c0e4090403920a048800035051a1440b426501c080718204000e4828120b000c942051864400c0c105912a512040c1c50303030041d807050b500580d80c1130740640c0206134080081d83c09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 796310521 1250 796309271 796309277
    0x3c0f0f0e030c0303040f1a01090911010f02070512070e130309090b0f0d020105070506091b0103060515070f06150603050a0e0a0b06040e01020c010f06060212040509040c03050d020a12 80
    0x11162800442d40d5038440200024119031001c80c0799010009500c69032000c02002208640141da11084154014407034000b0a0301c21241804418025500460903400402a0750b400303030040f14181400d001841c002c640c2c41d00d81a214800c0c0020b01e02d400b60380501d00a010201d0130b10000c041a040090002d600c9401c0041118940101c001141e83d690308086942e102c241e40304060201a800107803103500590001402d54007a0300c003044802440420f40c0c082c0e030b030040d04000303a0050f0198011400c036406402220b820543c1c4114410b828054207018090840c41403817481941d01c42541c920081d0760781c1103900d1820f104000380502002d501402096480752a2105c01c00c90152108000c0f0f030344101414024256030b021401003034041d01c441d004016251040c00080d0360314051441213900074440d40c085c041c44e151a100000c644c0c03510109800c2070815482a03580c0c01c0a0514042011113070024100315a558111080040019800d103c2003042d602d02e03802804030b030303001c90030b005070405442e030355072410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 796311771 1250 796310521 796310527
    0x103020a170a02041d0121031b210f1d0a0f030803071d100f12061706010b041503020f070204052811070609140115030606093c0f0f0e03 60
    0x707c0e140801c411504110424441503240c582828240c07141844403070341e500f8402c10f02c0714080c1444101d4051012891030045004008a00707440c040312480000d01445000400e400a010300c503068580c0042402003004140c6030095036034080004c1d101e940d43c0e0040341c17007c10100030440f07400d4024507628103510040b12a2140b0300e20040019a01d6007089285400307124100449120b024407070340c48003040d0b500b0210300b049541c5c5c440c507000183c1151020015990b2140c0000441c2c0700d03002c0426a01110049a801c01d10160210b1041e00070b5000007500703180b551001d00c55030015039100c0c00f40c1c034051001d8150032503e505001144003074814148900c100c05600780f140f130107070089801c002c81d140641c02c084001102e41841c070303264403580c071244c44a00c030039070038012000c202d10b1031150703d401101d200701001c010031559949420240c0b0400240c40e40032804500070b1956078201c00c10200c01402003148404020201c40c0000012161500100480c103591250b044d00920030310310590000041410045007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 796313021 1250 796311771 796311779
    0x130803030f092119120609021b0a0c0e0903090a0303052701050f13180c0f0206150d0204020d06081612050706030b030f030c0105070306091a0103020a170a02041d01 72
    0x2c4501c0744242e0b58504a07006044c000c141803007040400c070b10f0411300c0e0051100d2a5680301c100040d4100c12094400109551803004007090000381c14803c0d85c1c0c0c0b1501114010b490a020880721500061501c42c6900040108000f1980c4180c43d84000e10300c00e407207164450484007a240c580250401c040324194003c0100254980c0e0000141ea4221000002c495500d0800e40d00302c0e4130410070b40c0e012030480d040041a894005003280c02459005069a035080c0050712005022039840b0000c3d1800315040908548040c990300b05008044944d0340007038800351401480ba9054400c40300554046203c40e00140d00301d1040e04041d01c0004010003000040e08440c804035124680c41c0d0280b032186005060341d6070310400352600d09200c04980a14560140ca0305c0d440c902c000540070748011501200001e182030700218a00d2518401c101003070109101c001c6040580000640081d801031000e8000d00491b90b100020b440200f20324184a4048043d01603180ca1030310ba0307400d0a08040f2590b281d010540000180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 796314271 1250 796313021 796313083
    0xc0a060624080a110c070b030601080c18040f090819081303080a05250e0a0e0106020607120b030703050a0b0703021629040308090706030501051005130803030f09 71
    0xa50801c00092000136000c02c4030002c011548143d40b040101d501802030006643c06c015400b8620800080c1c0780d003905951a005201218410001c003060303001d0012854000a0400c0c0e40140040e105501001a0882e02c42d11140400d401c42404680c00d40300862013405000d40c8031345140e0b002203148044400d20091643c000c0c1407800000c00200445903181c000500050b000d4030704121242000c030400002c0140e00e40c00800540d0200940c3e8007030700841c11700095105008108a048400c10781c060a843c1e19100c0d02120802d24014801d0f8a554840c5040707001c07a5014005c02d0009c521031401002c140c00749103009030402000070000c0003810710520001540365082c5c100002001c0d13104211080007407880320309440201d1799109030189184920100020981c02403070240c00b928200045400303050307a89008405407182406401d8100006020b4040340380e0050000d000e240c45400c43c203d000c03e494000e0645150402c440391115110020305021140b10184001d05420a40c00b94018801030711480e00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 796315521 1250 796314271 796314287
    0x9010b0108060f04090c050604030302030a0201110a140702010c0b070c0317040c06080907030819030e2802060c030a03020306011d0901120305120103060609060803130302060f0c0a060624 82
    0x40780515101d222820801c891b480080014010060809884940b2401d009603603400c0400b02d00c2c00f6610380100021841094415039043c1e000070380d204400c000c0000c4401c3c1580d04112812414010810900d0000800c040700140c45101190b490706940d0381c190500814030b8880d99540000b0002d41020700011858080c0000107540702800c0c017181c151180210a8070f03000c480d034809024001c0c00706280b842250282c03405800400c00d0f44d41402000703100604c0759201c50307a2940b6454101507001c90b044038072641100e112900ea000401312414240c401035100e00f160b02a0400d4000264000100034581d131308074012400c442e448130030402c02c1a5019020801080703040c0101454090355581c14030406219108031048142140c1c04070841c1c0d6924503148014000a002d940b00c0e40d4100390700451041000030545009018032b103800e017030f098030391b03028001281d10601d0300c000341d00020000480700120411080000e40d105140c0040d0080ca091800015445030711070f8420921111503005030010381c8541d02c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 796316771 1250 796315521 796315549
    0x1e090807032612270718060306050f010302150309030406031d010c0c03031d060406090302030c1912050a020c120f240709050105071101030207081209010b010806 71
    0x40c00040960a00141d00014000d40000030b8400500030041c2071003641220f0090404d1109801c84441000d01215520400403060110394051001042058400e500c1c00c110010a0f101c00a85107440c0d499107020303a4021581c031412903240c68010000c50034418070308007115290715100c03825818171440b5203840c1d1080b4401c000c01c040d12141c100c141032640c02e00d07440c10a0302c2d4030000c0120310b034820005440780140e0300f01903000c249002c5540001824102d20031014180c9a0042d018542c0c2d1540c0d42c3c2c0060100311010740452000f8012101d119404024402821080f01000703290300001d440c10b91610000c5284071020080103006034400c08ae000a40c02020403001c076401c10240310080c45070b80c6012041c001c410500d1145130036081034107403e280580710421401c110260305603904442130341c02d0070a82c4985d43c00100c0400000010460340141055080c005140251030044030761a00d0b481d64000c0401c0742e11821940d030603c5401e540034440c03001844000e0a01495078509803000454007aa0307920 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 796318021 1250 796316771 796316783
    0xc180c0304080d020a020a0209070315050118170318040b06121b21090d0c120201060b030403090e0a1109040f020f1201051905090403050c010b101e09080703 69
    0x2001c00c04001d010b400380c82c550b0003244021074951901d40002540c9141e0281c1c180d02441080d40403551461180c055807088220740112000c0b078910b05801140c6901c03800ca0301d40c05038214a80049078203c0c0c0705422100d800a000d00940d1a6103000400920020448003000e03c100d18003d1a0b003023a44980e400c1d03411600c0100503071101944c03460750481c080c180200f03095605070f100080100d8640c80355881d0309142e0160507070741c1140399680daa10503580c907250518080414403010000002416245a070840280d140c80045040385d03403180108565001690704034040784000364103202100344159144d0b80111500c13001e004050f4610480e51481c03255540c5680120b849039012203510b074180c1c04807154982300c0003c65650f0512494a210001001c2c0200307445420029411343ea0304440d00d076464141c0d03800910320001600c4503541078801e40e0001402c0003a954890085080700d9a51124107443c03104107440d124051900030f0324200035181c0040c03400040c005001e10500082e00d00103090401d81c0e42c061 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 796319271 1250 796318021 796318027
    0x10e10050d0807021302030a0f090209011e1a091e0904060f020c100f0c1707030b0a03080a080702010e03130b07020a0e0406060906050d05061506090a0801020306030c180c 75
    0x4103014142e8407840101039080442040070080442d5503074002d52285591080400c109000c0d100700d0001e4030031182000c0c0d0b000005030014070603007041c1d00010380b0003500c00d080d120030300d075a880134500754030303009002110f80c1d440104481c519130a149075001c100344036010030381041d010b104001a4401c00c002d08041d1a440c0e94510960a075016507044451000306075040f40c0e501c2c581007241d5005031450701c070b809075550304004c40442d69501400d100181c2101c4201c103034140e41d440c0402240141600540164840450b40b00003012490b040014146012181d80d0030715503160140c0c1c0a030946480d541d004059031b1040010000d51644012402c064034445214550307562080d000140c28030506411003609061118140010090940e01c040101c40314208180042580d9604000c0c8509840343c000d40540c21980014510000d80384640070701c42401000542045030200104243c2a5203811024285e940003081c001c05140c02c01484d01080022265551003800d14405424044005400482481c0000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 796320521 1250 796319271 796319273
    0xc050906010318140111042402060403020d0503100b04060503040c0e1308030c12011203140906030105090a0e0d090303031505150a0c06090803040b060a0521100c090608010e10050d 79
    0x7034010103000410186400d0701c50b500d52141a941c0411110501c800c000072001c8d407507080f0300220f40d0754403a40e00740d00030f411100000413060344c00341c1c0000d01c411160400c450004c500c04582d5005080980225614240c0f00d02c0c180c0f03004520702030142c00207c04880244100aa4000c03604410048194440785103516902c85445000150288618041180180c0e500100c2c2b185417030600119030074001e5488204916284100386050300c120b03002d040c0c00540070401400700741458a00c16421004507030001454141d42c044042c104440c848056000500b000c0e0200b0600d94140101e14a043c410004014245d191034009251003000c1e00152840020118154100c0c5c3d0050384003442c12508980c0c02c1c09005513134644284103900454040350214008004150b6a0030598603901c107441019211603020f074504d800903589440000d0039001ba030304c04c0b810450680030003030180845c00441500e6050101e41000c0000d01006416001058807031600b00801100c882010062001c6410030b480c1c8407031196003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 796321771 1250 796320521 796320523
    0x4110409020409061109011e090302010f050c3003190c170106080a0509010504120e2b06180b06040b13142211090606070506040c05090601031814 64
    0x1284405000c1340e00d002491585100c01000410705983c0076a10900046814000c4034108410000c1d40000100222401d200650007003011800d00d4415007003103030802c0c1451142c81c2c6440e00c201140c001e181c0804805c072110480301d40340300390b1803250b69400714154a800391250319001041c0c81540c2c80c41303031034041c0c1da100140074055100c48010001c1e80c400d00c941e12204050614901a00c0d2411403c2c507200c00034004010602ca4540038590100c507000e1022900e580c12900f1440350720b0181d81c00080d290210700740074500c031254003001c01e42100000120205050280031544121009000d280c0080818030006951200382d55000c130040360000780829881c00030800c055007108a0021203072428420071554241c508180c0c0c031510020440d032403c2094007004849080e003407a0010407002851840c064946000d1104030340c0000c0160101d4203012494a03aa40341c034070161002d0703c9140520600b4021424040409a8085001c3c00c1c1070000025441c181c10300380508041c05090a2411a03401d245000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 796323021 1250 796321771 796321781
    0xc010f2009010c29180c040b0607030f03060b0a02070807142d0d0827010c03050912241315050a15060e0f100504230907030903080f041104090204 64
    0xc103101c0c8008007481c050540b080100c41e0201c1c0340c5ca1600c84c0b0150300720302c2e24142c000c08140410251446041c0202c503a019601d0000b04901c0605241d26418042211070005001c3d0110b00c84a81c000c040b59441c0405141c14038440385c00c101041c40c000d0800e90729a0300c90004000c1d10650a0380c05c2c03400300c04410b03115100e0021869031603500a12101c101070620403681e000c2c208416103050908011000c2d103032082c00c100450f034030044c041a901c0c00d0a00220b03025001501300d500c00540b08202c203040413829142028900c0000f102e00c4156991503a44142524240039800712520600a196050325110039401001050b50289403507200c0002643c409099007140d03401c02e2002040098454403802c0140c40740c100302c2000d03030080d4400e100010300c8d4600035681c5411541c00c1d4450703514003810120103da00355101d4904164000c05c02e10105001c1c2c072030034240d6114502503030707002841010794a0020191000074085111090006c014007011030709212466008034800c9070000b52048052000c940981 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 796324271 1250 796323021 796323083
    0x4030b010605040905180606130b060301060f0f02030c0705090a090f05030c1b06030105040c110d09060e03030903060c03070905040204080c010e0a0812030c0c010f2009010c 76
    0x1111800007589030341000290090340c004030740c1408181d82e1070780c5d001c8141c0c000354404031881d8414808540c145c01c080302e040305803880c0d4950201d00d101c03410001ca02d0590081e40000f0005285003280f50700d81e40d10001d003408a801c0d82c03001c0e510308140d038000540d583e07240340030341c0d0712a404000125080145c550b1050b21241c0d4004000580300c2e000b820805c0d160780044158079454080d01141006031485d0a040002038500207140d03d0669080000f40001044100400707400e001d01c0400200d0300301c001308548800c090090b07489020b07090820b2001092a42c1c244240c41c0694414824900c0719680420180d51000c01c24501d182ca9079a00e03c0120380b903d035143c0c41035030801d1001402040f240008210f100100c0802c7e01c2d0b00000405500a00c100d40c0003078407524010380c12100c60544441c00782002560000411201a4144030100503078a0031246841070b03001c4420790780c2c050b07103c001096200020580250421107420250702d0360020b01410315069004180110b40082001128440c4811301140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 796325521 1250 796324271 796324283
    0xc01031a04050a14010b040f120512030f070201060e010e07080601020705150306040b0a2301020c12010c02060f0c040506070203010f020a0203071b05010c02100306090c020c40020403 80
    0x181450041e80c001402c000c125003d0601c40c050010403540b192001f02d4040305c04140c4080d054a2500b50b900407105140c0104851a00070400c804416940c41700c0950b010b540c031044a184103003005e1201a0071603100d907001d0721207003161000400810218203042a03001003281410351b000d81d28400101d040c4200d5030417455100c0c04208100351400c4103007020b18400c1d01c0c190f0b8200600301044042055102d030038800c110509452103089102c0ea981e01040081c0d8020600444400d0942000081d02d075942114900510f42c0d500c603a020802c03541001803a400c4411090500d0603401c103202e90700d42c41e1140b4042c040c043e2200082200440d02c00f588500408500c90300308544901c14904002c0d1245e000c1d140c19984051412015906990420925022614142c49280d41c20221b94244107003185580c8101d0185035480600080c921842d000301e40b00000d0341d9014220001d10f490400c81d0520421281500d05181f04020f0015142880203505170640b540500d08540a2074604010103485160002411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 796326771 1250 796325521 796325531
    0x61003021c11030f160b0705070522050a020a0206070c030f0e010908010504240b0f0108060402090306160f3207080a0e10080412030f06050409320c01031a04 69
    0x444080422118450b440e12451507005c0e0799039210021316030103200e90141caa6086660100900d2821080b0302690515080008500e00c000006110803640101d42191145030001600303d0507980c1400321036484031644c00e0840d4950b01d9510024010301c0c0c06004c400c1070120700c1030940010780c02501450300034410303000240003514103440c200071039941402c400e21080c0c054221810086045000790510890050017000a588600004540505000d01047d400035820070030040180c0b01400b00314405c0e22402030800c603ca840c040000c180540290241c5d0422040c52185844240084a8000a43c1980b04004208012040c401030240b0540340001c2c000741002961408282d00940d1141e000f6100701c95100c51003000b82d6040d5107541c0c044800408401d0124071a84030b250003503100b12050b0088846c006516a01c0384d0100c0d0840e10360000035682241001d01904c00302030741c0e80f03081d1201070801d00c1d00100e00c0c00781c03001da07540d80b0ae200030301c5414941c58003540d40900136100c90074456401c5c01402400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 796328021 1250 796326771 796326793
    0x303040b030412170c0304060c0c060c0315090204080705040c0513080609100225050c0301091a090106030b15040b0904032102030106051e1317061003021c1103 70
    0x16101c41d40d01800800310b08136280d00075008507450651880b80e03901c0381d4103915558855031040d000f041d82078070303c00a10040d020035401044a41c4120910070300151030004485088626444001101e940545001d0b40108001e00050344042071a1007190400e07074021a80e004032281c2615140070b036940c83c80e0401340103c400a00c1010009480303000d240301078161800c0401099080050703104500402000706802e01424031000e06a56a07101c0f103170b02400c1610031141d5440002801c0d200c984c3d90554010003044548811303103003510421a0006aa40001c100f0303140756980e00d540024008040f1070405507118204d10842e200c41c2c00684c01020000d00d00e9030b95150034500503040350842c010500c24440070540c038039407880880c82128107880003925020f0134901c9641c01e20785840742d4148148140c060a1005010340b400e00e5074580064191084007034604000a04454503140005000c0041c200c1c43c500c1c01c00c00750b165042d4007028a01c04002061590032079007020664200c220720925018800c0700d254607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 796329271 1250 796328021 796328033
    0x30903070b2a190804240b0118081906020d02030c0705100501030b0115050d060f1502070b0706180b0106020615040e0d0c0519030c061b17060303040b0304 68
    0x100d011001c1c002c001403001458030208280e4020b400d04111503031601e0f00404001070003513480c81d40c0b1a204503081d41148154140c0d507003904119200e07200d1890b480d031a143d581c643e0004425503000704007024a501039487c20503015900d082413654082c407520011081418031041c2c2e0120350071000b200742c05541d42e0130032030000d0000740d102100a440714083d000208003644624055141280e801c481c030b04403d6400c258241403040800400e51041c400308110000f00b0803e00c0c000c013001060010b0140e02424900b0449948071030846900320115048044103210204028041d01d000c2ca0b04060001640d42841800c030100582400d00038040d10754110000407111ba0004010b0b03c151881030110300700c2801c6800340001c0c0d8100e1010383c105500141c0940003100d116451451484c1e005000311680c0041d026101c0c01c44941c41c1106a0000351403034048800d000341401101e0040b0f1204a002075240c202c084000e0152a40313604080030202d146005c610f45a80800580c1c010340060b09180340c0c0ca0519180103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 796330521 1250 796329271 796329301
    0x4090608031309050906060405090c030f0703030e010c0803130609061e0615120b0a0509040f1a0f04060f0f180203010f020406021c0c0c1805060316030206030903070b 73
    0xa180e9500c10b0b0364011480d02880e00030344d0b0058544600400031a112441040090400144000c07014403500c0d01d1303072031240c1c0d0030050303803c04c0000080582121401d509004180f0060211018140203c0584420005e4030303850850380d00441c0740036400c0c0c0ca0b072610724180000d0311900101800d1a4100740f04114182034051414034800c08002d000c000040d83c40140199800c12180018003080c003031210b400d2030b0078068104244195004082c0c0311050b440d4030002d242140107685c1541c2d00d0714410303c03a40401601c244448020020301000c81d44501e800300740c120403108000c04c0203001544030040c2022200c2c1d0381d00701c8214284081c0043c00b01000e50104203400890a9206a12070b41c242908c891a03107045100311411f4072265405020000368203049a00200103c1030690108424207400380042000110407902030010103005020014a4101c200292240a89080c0c801d0304a440d2a0152214034111481103d5043d01c1c0551295550b00483c0c1c01d60094400140000502e0001c000341c0741141601e03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 796331771 1250 796330521 796330537
    0x30e07030803092b020a0b130602040b070506060102010510031b03061a1801030b2a1c0c0e0108181905150c030601090504020d1d010c09080616080c0409060803 70
    0x108041d003131020104410310500181c000056044802101c02003813120381420b034400f02c0032030792844a11103582e8100481e07200b41d01c801c01e602004500c10081141c10b000207500030300240300a101034182500340c00030701625444003c01c1c5084200700d1504a210002c0140015078006000f0410f00100c030345181c030b2001820030310a1148620284032409003040321800d6040ea900305002c500955100d071050b204c852000c544020724080c01110b0480b010310140c00415000d0321610320200d05000301e05101051300d407505522818400607000110301640c0c400d0007240e001049000344241c948500394901d040c0a07804400300c0c00038580084600a010000039140003100081c10101150380d100c50030422280001e0790014001940c0c800b00b000740d894aa006440030300040c06002548441e28002c4164220a02c3c001900f140d4496204054203504945540c004200e02c0700582081c0c079004004155640f4018000001c4c001e1100c04911048503040981d400780021900c108420b40d141d00c50581d0725044110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 796333021 1250 796331771 796331803
    0x203060a060f1703030a02070f0c030c06140711010f03060e0c121008120a30180807060207061b0908010506101e12090f060b090f0403030e0703080309 66
    0x15001907810f08035040b5500b0842e01c00091415511090388140181d440118151400d981c05443d510210310360740d105000170b40c41010700c0032031589004030146c5002c10351002c89154510601000010805000100c00703040001d207419024010414000c2e401000c098008004010945003000030207141e02c80104402d080507031800f500e0b9514982c4849400b80c09004100c080e42008088401c000c40a00c00b13004040c189041508940410921401441800c0d40301e03405003900311940361312084214401c100d00344250320b0714004490392030b89a03070200384607c1900410055000640501340001644603200103624049108414400004000d180404034001c0009c103510f88ac002c11000d1078850b02d000b650f900941c076095180c512811108403050b0000c02401c0074081103c484034051b001b02c0c400d94603118441c0d0030803042c0290509140d41111003d2060600919140c2d0a00907051301c0b20444550260345440c2c0820f0a881c448071007420030131103900080c007400c03011040c00516200403c801d2030500c140d00e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 796334271 1250 796333021 796333049
    0x9020f0d0e03040f15052104110a12020904020a0909050a0b070207180905120f120a090f0f060b040203240a151103040503161e080607080a090203060a06 67
    0x203240642c60b44034510032000207612503101041804a4608039403504201801e0460411412198003048003602d01c103110406485241048100407501e4080d400b8a403050300d21210150604000300c00e0f41842040c00b0380319100341e00001c0c0456079407601c0c410207052401c90600002d4020310b8101e0380e4040c2c2d844215a11040000041c5100c3d10003d00320080f00e520b00d10000b80c100c6c241007204010b01c01d90109075030302d004440354841d5068101b001000c0c40b051941420b5134400300d04880241005018101051060030214018007003905407a15650042c2c20100c000642c400600d0520020f01003400d405800500110820030300e2062501d00e82c01d0801f461751003400b503d000383d00f004142d4040d80100f40c1c0d11304072041c5a0440c0b9108004050134a00280100d17071425845800003071800000488420304225155030074030a00084185900404d070128000758070f00750801c071721941c861400900b07007001c1000e00000075400007116002040425005030a60385c25003401c01c6100090203203401107618030b216074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 796335521 1250 796334271 796334291
    0x200f070518090304050906030a171b03090a0302010f0909060608010510030b0922020a0803040f17030412080909100504291903020312030f150607110a09020f0d 70
    0x811500c1c03050b114400594a4103007040104a2100343c00391106406100350344014001075000021880d181428001440e21a0000c42c0c030340740103041000395000d441d0002d0100b10700c15124400c060050b1307542401c00103c101d9403d503041710501040d0b84a0494103007028000541c0c1500103400d07074103849090382c00b50743d00e000241c000c5d8155140385450301d401c40d816400248620094070b90030782c40c0842440c0040c506040c1c40d00011074017110380c1c1188805030000682000140106c808060003001c01868203044481d00080e62034482c05a84210321000b00c0039500101085071100c2241c101c03545c02090a20b40342061006c40340b04039018000c0710300462a000c10340380307040da414081072246503407480080e424000140511102d007210391040340b14407614040100040c0d0381407116031300003c0396010380c0e07441e0f00d00349505151100300a00320580c4941c500100700410784656085a41d61600101031a00708420b41021480898036584101000d40c030224240c805542c000c0018104800050000e03c4240c1113 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 796336771 1250 796335521 796335559
    0x6090406110d232a0412061a03060702071a1201060f030c08010f0909060b0306041209050901120b070c1205210f0402010c141c120e0d200f0705 63
    0x10b031142c515115440c002d040480e0302c06103c404d40004c03061441803c099842c0d502c020403004186044072203649445000203060020003082c00c0303045089008011908003104040d4850000f4000c114800300c0072014582208031001c201c664900da82c0c032140e0115030b52054010031609000f00414006403c08501d511441c1c0704c3d803051410303240314503a811b070144e2612000a000304800d8104584450322000504a10365050001c3d40c803030350280907500403040314404001d19004554100714880c1c1c81c800300602440c080704452034140d55002c085190580c031340907026542d03561404030060041049410ba4140554802c1c003910000500115280080000440f103150035a0125000150b10003444000303405580700340c8504d012940120014214250031030007440c1406501c021181044002040e41000540d0040c00f1480580c03400383e0400080070005085038030381041c12166801c016a0b50f40c1000010188125940f6242c811f074100d808003125140d8203601c3e6076032403144911414060101070401e1003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 796338021 1250 796336771 796336841
    0xb0d0606120c14032a0c0d031a0f120a0605190c020d030e0f12040611061e06010c1406040311030a0f030c050c060117010509070e01030b04111804021002010b030606090406110d 77
    0x21038061003441e96106d01032000640b10145245e41c00a1452010380b5604002ccc031140010500440c00441c02340391000704034040714401071100c00c805140c2050303004038541c00710f190138002207285070120700505942c002c6484c0051142d0746008a0180e02d0124264500080c014012140d0035207a003c0d0035141ca800d8a0f846000441e8800d001c40150300300d00d2030301c8101d44040f550144050620302040c403216100c0c03100b2074544140c00b8900d5032120f0103000030b064000d000c03d0181c8003058001c2d4038001c00594018a034290b44440702007410703201c0309010100da02440030754405098020841e011980e540d8110381001c02203c0d000310a41d440e11303000c10000792021800740c09a510030034151360b080c0d285586914442030028026500c0b02550300d0351405c1c958450034462282da1300e0040c5980c3d41c0c00c142c010007021244c040c00c4a8251b80c541091a4000e45011030490360040084030400941c0d86d036810000047c01d002e03800c5400e81080000c0c090b1200d607a40d03101a0b03840c080c40c000d030500b480388220a04a404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 796339271 1250 796338021 796338041
    0x1020706200f0a0c06080609041e080904020a08060a05030d0203180103021303030806010207090e100902040b0405010305150109141503070b0d0606120c14032a0c0d03 73
    0x901c26203000c200382104440c11184940a8012241404603160002d07041840441080315203809000c02044500d0b0b02000c1a40c2080341212018907a083c00d9580a18a06000440080801a0080c0c000c1031050500c1901c481002c087d00070355591a41c0308008004000c200c0340310744100701c0140c001c503080c10b001800030050503144c3c0043d490700005060b58646408825011410160200000c001e007004151001000f180f103034503111601d0800100181c14442960055001c00d441c2107840600d002c2c4c002500d1450003981c507030000c1d20700c00034000700b0060b080041d526a042800c0800010400c500080c0320990340030111080801a625910003205691003003040ca4010089003011900b11940450741540005000b4101c0311910342d24195007030744ea001508104c41031a1b444804100c0244c11140000c0c42c03007242c000802103980c01581c0a050f1075400300f10310400020220000c1c075100001c2401c08032030303000032072041100c0030350560220a55001038810781b468023600241949890203400340030440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 796340521 1250 796339271 796339277
    0x220f050d0b1506130303021519090f02180f090606060304060c020f01090b01081213030809120a0803061c0f120203071a061906050706051b1c0b01020706 67
    0x20a415494410369100040d01160071a01e02c840149001d54880c4010320903007a64620840c0650b00d903013400380c1081d98a160800b0541c500004001c1100080d04000052004115001500c4182801d00c1902a40c650500030341120300c07200c07103a80c60599148034a01c81e81c3c6400812010380d464500340d0b5150b46081e1040b9030405414001f140000d201c40e00202c940704100c0c411503030b1040c07a03585001e0944403240b2040c0c1d2120000001801205414848811a10581400e85141a40d803804005107000e5904c006403001c1c601081ca1551540c450302440c141c1c4003030f84202c0307603943e07030341d08258074280d00c15544240f107941c0103640b01c2c0c000e01072030345c1c54503415820018210070002143c507045032210310b9010100c00c60108100c8440010700d0051003c8035000e9800d60119246444020301030401c030380b241502840380241c06c0030030003e40e100003111252640203001017941d49452100c00c1803042d03403c2e501c504e0b41402007800c500c43d04d903c00041e40c403005481e202707010590419006a88501d01d03800f8080c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 796341771 1250 796340521 796340539
    0x60c04030308015307030515070302070203030c0c180610081503030c070e09150711030d0203130c0f0b07081c06060206071412071211220f05 62
    0x3c00f00c80316000a1014000b40300303d028a039150041107141110801124000c00184c50030400303102803808404406011005100e2682941c81c2e0302d0b030f903c88440950f025808c3c41000500310031300c41d80640b018150b0140450703480740340c442e00705034031500341001c0d4501801c01c040c4a0703601e60a80010040c0589400b40c0114002091240c1c100c5038070030020700d889c05094000e23400c07103c1500c0403c010148001440081c0280b17508103a00314001c0781f009032244049501080071852112440030049030490b1540c10005102a070b0300000c58218040c01c689074895034408002c014211000e1070340c41075120b224401980d0800e480301d0f1011a424900d02580e00040c1f403d20500c0d0005042c0b01c001c00c40620b2012045002c40c10408501060b215140c00180042c2c02050900c840d4540040782c0b04031401d56035010700e040200c001c21880398218020218020481c0940020b01c5415544d48100c100b00f000a25480e5142004000e10584084501c00d0203c000d6450740001030003861034142409892004240c281 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 796343021 1250 796341771 796341779
    0x30106120803060f120c0424050d11100306180e030306010e2e0f050a020a02090711060c09030d1106060d02060c0709090b060915040c03020d0f060503060c0403030801 73
    0x141c0c0750001042581c014440d071065486950314414146050402c104c010081c0c0340d0017a0070700060312401140803a100b4008916021500400210f5501361001500c3e00c800401d403a0a1075011001d50701152600400d01003038410580b036060704800301751405442d48800c1d02c1c1d44007182404407241102142034640090000c24500e45c80b402e481550038100809a034003409401c414942e0400d00c4452082140003110f6121842e2500080445070380307400c07414402e00f8507076580c0b0040d4950f000d00d0b078000d02c02c7c101440040d00c1310740569003401c600d02c136801c21101140b5004010480644c010000c261003031080d141c01104051003501041c0c0c14203c0e00d4098051910f441d0144038840b424610120b1340181d09100200500a082000d1801000310307120114408109080111b034a440241c0072034085c00301d6108011406104481c42241c2a0054074005900302c1e41d0345040740203003c0c4109003000f181c2407101e0a140045150802c90540f50224251500d644030445418071900c074a10009010901d4a40104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 796344271 1250 796343021 796343033
    0xc0507141c0e010c03030f1d030c0c090c16060f0504060e0f0d1d0a0b07050a0308010506070b060d05160e0402100e011b05010605060703030f0501051c152d0b03010612 73
    0x5020340740a00402d11013507256210322a603108e401e8000b0766a1010070311044100c400c0014215804d010f0701ca003681e504090080c98164401d1341003441c000071007494480300300001070b03011240381000c3ca5420031a84c1030501e0580054070f030010205003a44070b030442c00309a0b0030021485000b403075400e0311280c00580070a00c0c0031120b2000c6950311b0358000c101d403d00007220540e610040210902c60f0340a05050f030030034603000c0c00961060304141c0c007030441401035030300060003050b5594000000300d0b118190355500b442c00600c0d04903494a1441c4000c1d180c1e03c0020311035080a960350003240301b20b801c80d00d1951028000c0700c02481a69906002610540f0f4040c88240035048000304503005800106400751600c0100b216980411000c4002030380e00c000000e10040184036a5014040c229106400c0c170070758800030120141a03d80291450840941075007001e0b1080d4010250000e80e20320706a0520f241c0701c1c03031182c0102c0382404804180d0404503111124a8188140d5040e20102d42c6400c0740900e441e1124 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 796345521 1250 796344271 796344281
    0x1c1a010512070905090307080a0512100509040b041103370b1303110132060105091207030b01080a03090609122904080d0f06050a03060c0507141c0e010c0303 69
    0x20705c42c0ca0008205a8010480f40030040039015480e40f030300c6076140c2d140714001d841000024410200650034640c20302203a44c0c0d503100c03590010f40100d02d0480c10380b03441c1040c010810b90030128a9240c403607501404c0390b801352a1500740d0280084400e40101d07100c00410007030100e0007800b00400c0c0d41c014400062203849542c000c0400540a4982824803000c986c245908540c0024204c02c4071410762201c0aa882e082d605d0000000c641e007a0341084142003540020300079002c2c1000d5544100f48004900b141481c0800042004640019440415580d41c7d15a031b0340380e2100e850b096000950710040480d101c1e024090090898204907195840003507240c5034100d04c01c610900400107048910503606560761000c0c1070500031401000043d5581d0043c500300c40880f1a488012a21141010f20801c0300755605c6981d5000c5a801003000f14049101d020100c400f4800d920005004c00c04000c01d81d100d5003000075031004031707c075040e400305441c450000c81078604200c03000b40d80b0b000503007880d01d110000f842a007013 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 796346771 1250 796345521 796345531
    0x605041811041d0a030e120318091305010906020301030623040303020a0e0d0b07021605030c130221090c0402091f110d031a040621021c1a010512070905 67
    0x1260129200401260400c4040781c0290300194003084d000b001b900d0603104500c45100020700540c5440d500c085100351b030540c514041842012010005a010b6480519003100698400c001704284455407034048000d400a02050358a60f25010a49041c0e9507a0500944c0f440900d00303508056503283c0da8224060b6200410400c10000481d0018080e03446141c1c000668610606004c2c0061402c404021720300a44c0e403a1441890341d0f100c90810240d100418021190907054603407907860858214224080c2c464040302c0740c030550801000030442d2400150090107034114a0a41d4903609510701080143e0050030481e560192849010058170140f400f00e41081100302d00b810040010f0340c402560801880c8a5004d001c030342c55a0200c520640c6041003500e644000311800c01043d4100b0402c4250368041300f40000a246140203000255610b400302c000c0c203011500403103460007140e0320f08408500d5501090b00440040c0d00008641468000803401031070a0b014020007a41e0b1600c1416005810f000c2d02c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 796348021 1250 796346771 796346801
    0xc030207020406080a050c04051e0627010f09020f03070302370306090608030304080c0304050307090b040c0e22110a0c0309080f0d110f0a0303060504181104 69
    0x54035005888038001e0380010300204000e40a91982400c1903401e20404a0740640300704e00c0c220400080900d4202e054030040c0100340d0b8100c550307541d4404030300460904004040481002103551100d40b092010f018103030f40c600345072403400c075982d1519a001d90107103012400f00014240000381c0054402e034058401882003080342e81404d401c02c1140c0d07421028003440d03084840b840405006c9a2030701030242031700402910070100300681c54064425200d02000c0e1008028823000501d4040c1e4003010030540700075180003402d944036190307900c2d2144000c21075044135074002c0b82001d45424040780201c0d0381021288000d803011100800d40c000b040c520342004090030380d030301d1b5a644922018143d00b4014000201560f140c50610300c4590030701403d400720980c407031007041c2d0261030f00200070000856105601c002908000c0703c030640d06040c89050840c5500204024071441c41c0480916070305401c83d604030341007235070b0812a9400c41020281a100500c1c00036010440c00302c2c000d546030034598007019801c0c200d14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 796349271 1250 796348021 796348027
    0x10504030e15090a03060f0b0603060a060503070c0506090606040501060e01021b030a080d02090f030a030c0f0f02060309011512050c091b03010f1a03151e0406080610050111030d0c0302 81
    0xf0000400408054000307840d06907560b82e410301405500c0c030600139800002c90b03a40341980b80007400505849241c0c0601d00400401102045051380180081495140c3c4a0250748552400e039041d2550354000702d506521480c20300f000025000e00940b002c1d913802c0300c183c1c00380048030000d010f9182512a0202000d4242c8a0b134405031021850003c050b01d5001c2020700050f0f50b40c181c3c0340800400c540c0c0001c01c144203410220358440003e4210044034062688100341c2401034800d4200101c0300c80340700781e000c2c1d0800390004c20803903500010f40c00041a40c00c42c014000003142c0300d102d00c012400112200405903800303440300d5030041c900303188407d03480725800800b4100350a51004078001ca800a920a040003a0060004c1c03220010980034007039040d856900290951802076408200241c20303039402c900403681110340000310684140d03240d00040c1c000d8414000e00e55180f5000f40d036040125800d8005001d003202c045020742c4150b4059403c021301c04001e6041c038035111203000c0109003000320507003419420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 796350521 1250 796349271 796349287
    0x801020409020403051c0c15020f04080c090a0c0e060c0102090a060c1e08160c05090709060206090303010e310609120306031211150405060711010504030e15 69
    0x2400240007a10300d00c03001680f107030310b9440c000d80707409141a55005203c0070031449102155001d00a4550150882c240d900215011644200203104409850510710000140410400c80020301054600e109a80e603034141d50b10318011800b1201c03007502860000b6030040d551041d919051000d0140001c60f0300005150050700c00006800d2444d6501000203c0da0711483c5506100c00c01401c0f07103140017203100300381d0070040956507099180f099074003401c403103500340c5002c03401d00c503500c820075024040c05032010032142400341e0080d103c9040351240c81d0040c0320307440014005200100a07281280c0312140b03503600c10744949024445031b04000011180d140a8540303405c040b8204034080d511030501a84000804202904001c0d00030340704824004141401c2410400c005814000194842500c900e0002c510314042c0c90200d003008840c0485440d2541410184400d03c100412402e004181984500007500d04a0102a0982c0c000303c80103030100340002508084d40c1401c0d08254001200000c041d0320304841 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 796351771 1250 796350521 796350523
    0x1909060608161d0610030207050a1a100b0403050c0f2707090605070203070608070203040b030103060e010507080f0112020114070c0e01170a111504030f1e0515070908 73
    0x8003100802640030b0000b0001c0000b60040d14602c3c0041c0c4a400b4003a203006030110310f0318404044840c00f0540c0c00900c2500b801000e102180309030b82d00c5201e003d00440b004044503e058030560303051000f468240c500141842081c4200e0701103c0c3c1c41801342c02017000000401010029224416070031580c100d8040c440030140489444058851801c072050b40d04004074001c000ca4100c0c0c000905100080140ca00565000a00c4008551031498802c44c2da5440c03920880c03e50150703078050409201e000c0004000c11285400c20383c6144608002044a0703500c1c03140449182e40280c40008100807224014000803003000c004d1103c0c240107061640994005087c0001190b01c140401e451645a444050000900080704540140902c218440c00c41244080158903800076010040c40c0982c0030040000d0350b190050324002100c1e07150000c0d40c03102e50ba4142403900d1002c400041712100402ca502240d11100c10882d0b48281c3e4000c4000d000b001e2031100b000b1680407000c0c0c02c8a040c03002003000040c80c010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 796353021 1250 796351771 796351783
    0xb18090703140a110406060e0415150507020301052d04020301091a1008031e03130501060e040501050601050f0d02090d060f1d070b0307210203100303171909060608 72
    0x10316a0b004142c0100a401d05245000440340c100e8400e0341800000c00c07103103078800c0003014101800c0310000340600c42c1c082a00d015009580c8982081100d81002c81036541d04800030b08002070096009110f965100b80382d210044002d01a041c0040d000154140c80030202200c07044c0e480f030b00c05000054440c2d00c03916202c02c0b01c904040220310114040d0700b0043c0301e0300c4104001000340300c0d6100035424414001d011007081c02c0180c110541e808400b01c00140130748080d41e907071000c042d0000d008000301c41d1100c2c85401c218004543c01c3e5070b00d608003000f061722075115000700c50240018584050402620030942006980015820342c2e01141c28502c04010803481c0c8506141d84111210010303000300b4052314400308003843c07540c5410704d030032407034041040740d40c0141183c3c0d0240da079146c40d441c100780380d00c170f00c542103440c0490201c1800d00c00700c20040c407000c3d040044000e6900945584100c1a00311138250040103040b110001c0c0160500c070041c254240c29001b00c0495481000c0200e02591503800540c9482 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 796354271 1250 796353021 796353053
    0xa02011d06160303090b04060b1011031804180305070c080c2103090910290301090504050304120302101803120506060919061e02071806030b180705040b18090703 71
    0x36a0b0760408249c0d038a03225209822100d881d05000c0b0201000140c0c55480b40140001000e04c601901c848101030b0783e9a51080c0c1c0c10349074800102c0c410311644c0c20700500311341000700304a45041000320085054040001e00807a2008010898460541e000e01c428400e20740020001915100500002d00030340e584d00400c92080a501004800540c80c20f01c21183d82c203600e4019403040001c10700c0c03a01070307400e50780e04a9041d11503c071004140c9444901d0000d286118651051240313900034401e40c0105030b808605100041c1034540f091020414103140340c14242d02e0040c004011419040c00540d800100d508456844500146418101028000490a51144000f840c000840d0700d410034800c0d650000c59558560442031890856180d103040c02a598200c0b6024007a019481d11402c485010411f400110184d503108651071020b08100307540c55003c5023964030784450350240d00c2c00411941420710030801201c0004004090408121000000300040a01111018025a080800461540310b8144010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 796355521 1250 796354271 796354283
    0x2a0102070f0c0f030201050d09030e060c030a03060605030609040620040612051f090924050609010b0c03040504020d0b220b09060d12030b0901080a02011d06160303090b04 75
    0x5000e926201e07000d010150051201e00003c8442400941d03400350503107142c010003060010361a0b005090583d1000e41c10701003542d100b074002031416800040480544102a40751320140311040d01c545059480d07010071908a50005d1440d40082d000c104581c20440640f8189441030010040e440c0c1c41900f039600580241c0b007c00d03200c00c10340c0b00b1410144602980a80602c0490840c00c43c40300c09552021554468401c4a9441c1c44330701040c42040f00e420790404000320644070300202a4130003040542021a07641c0d110f0f04d600d0740002449850141107414080d1104050361900e0f0402d0700b00f100030740011040d201480d982d04442465a102c02e60110055000d10b4075840980e203424a018003a12030510a4a004440c0d400901915440302c000c20380c0c40d1544482c401d2404112071508400819142010a600510351400084c4445001c51b02c0c0319054000e9a4a4883c800f002e5180f03003515a0728402190089800c000f000959101d88006010f10341c0310345000310f10b02c00070340c82e904480b2000752425603030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 796356771 1250 796355521 796355543
    0x907050403050c0406140126130515040507090e0a0c030b060907030204030302060403030902040e011b030c0801030b01030f0218070f0908370b0f04021c082a010207 72
    0x520904014540c03c41e04121010300205061001b04034103c5113000c1054180000c0300984442180e1100880300200c1c2410b000e00040e00d0800c6e4100d2403444510300581c1c0c00e0052190042c0d644943d900000d2055070414000c1192a1a1000b540010207404503520f00758040c08604000244075000544001d60091415081c1c50405104110a60314058210001e141c41048204002034010a4080c3d0164160500190080050000c60007804418944c66030135480d0109040c1500d840010041d030020300d41c0d501308400c2198880c1524050828080039101c0000c410042000800e48a032050a80d480a842d241000100801260b2084d4080d80d0040206180c3c0c0700c28005a0b5200c210000280340620017000e5000c8840100040e82c010b1010f40b2032106074a002150080e08400d1503241c1645d0b004030760103000c2c13078201307662601202d0586049101300b80c2081d00004120700d83c0200b505080e041001d02d841c000000344182d90091061400c00c448008030a090003060b0800c0c4050071485000e041200c271 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 796358021 1250 796356771 796356773
    0xb0a0219050c03190f110a081606020c0a0b040b09060c07090b09070503010e07111e0102040512060103150207051e0a1401020c03180f150c10050601140310050907050403 74
    0x81024908034030001420f6607100e07144007217071074205a003a403d60801c0f038102440d5804000308010700302d141c0020307696100d180c03085109486261b0342d003004c4802507070980d100e04c40d051080103211210781c41413400b02c1e84180805e000d000540002080109001000949064825540d03542400d0307555020b06203540c3e64030700c00031181c04c000e6692a0320100700e00d06140f4544c1030240020806102070810010446104184681c86908110300340c00c000554501002407288205614042e5101c0e00a4074010603120000441e80100020801c1c180c03031303010310803442d0b0b203541200080080d000300005860900c2036030060092a4050003024040c5440c08010300208043c40c104000c002050084c41d0390242c4c4100402c280100c404015540c0300031103030f252407214421036000a03254400381c0034040c1d4001c140107403504ca082c500ea402081138a40c0d02c03003500d141c003035245030201c00c6138421544c484c04540040010f410000c000300c004c0d60b01c050705160788400a91110701147c031109041300d042d40840c2001030301340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 796359271 1250 796358021 796358023
    0x2070e0619032006031603090c050603100801111207052b0b041505031c02031b03030412020f0705010c1412030a0e060c041a16060207020f030102130b0a0219050c03 72
    0x3903d03088003580c0d0030b89141021641c50000100c5146900e08051b5148018000c000000d0700b0b241c01464001c0020741c80f8141a4000b8a0003c5688640350740c0d50700e800c86000d543c0170b612003519032000c4200207e032055900c4c2e94080c0c0d00340e842820b43c8500520058411341e0300600007803a03210140050a400200d002d0003205000840720880804a007282d25003400b08003c2e50000340e048a450301c80c40001510f2142e482003a4918043c051009204988034810407d00703a000101852203030f806040316051194100302c048e40c48003005075104500f40c0040b58140031b82e5005080c000b6105100b1106400112070024582c1c0c2008150860480c3c11031000081c08050072a034080e1081e8071502c0c001401c100d0601030111403080c0300300c0c401d480c039000c007a50650718160f40c0182580e0109201c003e60306545005031a20000a511501040b44105541800740304a13050500c02da40d0400400c2d071107458682d0a00520035074903005050038004611400301281c000581440c1202c9045100350000c02081d03507007600309 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 796360521 1250 796359271 796359323
    0x40804170a050f010b040c03090c1a070204061d060a031101050a051207020a21170c090a181109010c02010c0c0914011a070308040305030907030b040b0f0c04050102070e061903 77
    0x81c50408d402d00340318a02195030320340500d044034000c800c00070004841e0360418985000710076000c0c2d44145021000140001c44d2414403032030043d108170300780311603403900f0401800e2002030101030107100c012035074040341b035004500818194000f810301c10300f44150700c2c7d070108031200100e610000603044400d90004112a10b07840c0444010120030068584124910080c0303108c4222107801c08109541c0c000c1900404801c1c101c0742d06100143c1201041601c81132100c41156442044004452625955000c1654000f0580d42212416910300c00f188106030011220a0b180c00740503180c403020500d0000701208140b00300c803500c0181c0803041d005c3d507241c034a02d13200007010282d15002c0c40f0000c1000e1400681c1c440d849581c401e5141c00c2607920307500d41c200e0f05464096581c0000344450000c5c030071301c07007400b2882da00c5510511420404804558816604111500462080340e015a2198501f80980c030f0944103800e5000d200500121030b40418a400300031400e160b50310503507041d01c1c208190b030715007507400c600707 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 796361771 1250 796360521 796360541
    0xc04030b09030c0d1b110f0a1d06010804030f0c0203160609090b0a150c060b0603010e150f0a1503020d0612050f0a08071104021b0601060314040804170a050f010b04 72
    0x3855452104001c0d00924110303200c5c0040603072a240361000202d40d11000c11410075400074110100950f261842101c00f28010340da143c803481c684000044440d803065495900c1180d069442a02511000e8402d44d500030611100720303494011600d20074040e03c1c00c801d01c9001404503580d08460a850b00749000704540702941014000e031884903045c40391a13600a81186000032a01c1e0005260079141000300041098044442c2c0c0424004000501c400c040218540509041c0e5901c10030060414200842c4220006080e42c00c103011030b00400900c00c02414034040d1092038100580360119007140c400407039200e500215048a2812030305c02c1400400c00000c0203103002407004082d0240152150f40f010302620200030301c5050441080c82480e100d0341c0545203264407000c0e00d007000100c00b6070b0568503910240248800a032610359101451008030030814010b5030883d40c0545043e0600e0392803e01c043d00e81580708107070320030b0b85140b8002400800c13074800b080c3c058400002d10041d0180401080d9a04481 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 796363021 1250 796361771 796361777
    0xa0e09042402031e07090b0301031212020306090a020c0f01140f0702030324280302040509030403032a02060c010501030302010f02040302010518030712060905330c04030b09030c0d 79
    0x410410500744d001c420041e60728801940b03442c1070342c849008072006c041d00d800c403800401b0b011000104004404041001303001003501d0700000f40768800003010481c081142ca01d984407003101e01050b041c0b90b9960041005119071416141c0304008501140c1c02d44000c0555900c00c11044010032105a03c08120030341c1001281c4051072650402d071031030810503058408440c0042035200c4c1e92031096070700c441030507501c5144941e44486aa0701070464114040940c403040e13004a0601e4001051010044200c1d001e0701d9140e00c1e0300d0000301ca02d00c030215543c2d80204c58070340c00300038500b00c500c0540c0d10360000e4071a5140040c0041801c0d81503180c004d0955405000d00c16040d0b005000500c0183c0e0814151002403124201c0c5140316900280041e181944e1030303210300010011003d0300000d00000b90414030180303020304112001e952120142e8952040b004460201d00401440c61081250030903c5c0c080d0030091504080b03040c01c4e01d94a030580200420707034024a15900008064600a001b440b059113400c0480c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 796364271 1250 796363021 796363027
    0x41706010e09010c08041407030c08010f14010609061b0602040e070e01020d05030109050901110f0901390c1a04050415060207170a061b1b12050a0e09042402 69
    0x80401782c0000e90140c13006200800d09401c180300d1040c20440c25000f15008041494102d5940034034500030141034000d90f596274207000103002e0342d4048040c00360407102c9036a641c03426289403150440303801740001c130070328110714040c81c071440481c0d090300182c00074041c6441d425a0f035042c5803402a00401d0b2110351a4107540041036407580385504082a00d045400c1c0c501d0108143e036075481d0440c014119041c101800d80e4000c01e01c20f0741440e0007409010309030003e80b106c41d05c40c82c0c0010005c10454803074090015507105040c0030b440e035604c0b071599000700c82d1052915201d00b41e150b0a039020702045c500c6401c441c1e494041010441c524290069030700002e9410701030800c103400e01c1402910341c0c00c00d0152024600191502c00541031013040307603192440c1c00190411082c0c0f554a03450b80260341c7c1d101003400082d40c1c1a500d8a0844500390f42403101035111a0b030382a000c1030000140e660360030041302c84046c00100700420f02c141d1076003e159441039204501020700e80840141c06502c03144c079024041c42c018414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 796365521 1250 796364271 796364291
    0x302100207050a1a12040503070c060203090a0b031006050a020a0507060c060f1811030708030f07050d020f03071106160b06030601230d0212030a050306040b04110d0b0402041706010e0901 82
    0x4c04100d50141c1e84000300542603541e903042003461031040d4200244403440070100001d0f0180d000c0040e241a20044441c40e06042d501c400c00b103524007040d40d40b000316030520101005610b0103000180740c181124015541030f80a0f98035076a091043c00c4d8807000c0800c0c2640032607020003802c2e124920501070300708801c004a6003400b4041401100075080200011050740c0210560780e0104101d800400510044903900c3d842c00002c42d105800010088079584524000c0845880c00070420461b0400341c4d1000b98100743c0303c0c4c0c444801451640c540690030620820031041003490300c82c156032031135004017104403690074114141803a05905901400300b506191b140c9500b00100180a00402402201c400c1d4070320b0000c1c0001030b43c0c003081002c8161244030024040300d08941110141d44200340843c0c041001034004020f00050f24088207809414250030000f02050000c9680a40d003000e001030b00c01820300391907500d1603428020541102c4020350240d0010855410180015607007d901203000b80401004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 796366771 1250 796365521 796365569
    0x5041d03090d02150418060806040b040807061d030a12050105060904091112060a05060a26010b041a090a02040b0304080a111504120c0b130c0302100207050a 69
    0x1815110500c42c4070401c0c0308030250354403030b998141d06022034040a544e50350346070000342281004014010220341001d0000038901e401003180d5200e15041000c80e2490b42d40c0c1e0b644d104041d40f02100403583c1d243d031004410a840c2c4031500f180d802007100c500131740d0b55000c0d00c14090034050340002540c80b030702e0500b0018000c030b07295070303080c1d0b034405034241c902207040d061615161004001444445400220500e0b40b04c005920014450b406901081400c000c3c1e500d5440a1001085440c050f64903040f0188100c00c90890a0351440304280c40b10304000254800384a0005054890102e104001c200062602c4501880c156090a8120340803002c1103282914069200c40140801080a0a001400708102c5000c5002c1d02845d420206140240c401101c0207401124102e01c041e54203031030b80140e03044003c0c101405041000d4020f40c20565020042d610090707a010307002d051000c121a0180c1c0b21100000603100e00c951902e1103400c980182c9003103810501400041d000e60361051943c56222403d015540c50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 796368021 1250 796366771 796366777
    0x23060414150d0516020304080607052a030c0c370306090803010f06020d1e0c05100203061c110112060806071106131a06010c1b05041d03 60
    0x410400810040d822020000741001d041c0303405a103440500042d2048404120b6001c0c40c40f540c60701c00881406202e098003260b981c0140d001c2d881d041d0f4405800b007440c1602500c0504a5900003e6145440803030840414a6074000c0440006841c0c0c0081440e070300ba40c60034042205818000d90f5449043d4844070780c0c1e6621035000000440c81c0381e8101c05441065180200c1107005950040418032180380c05141c00f05580d1300c24801c002c60021924404142c451003c91955034028040d6034220800c3e20f01480807448005d101156418003800403201000580280581c1da90340c4400c03800161203140c03260a000e240300b21400301c4812030322180740c0c000010700c05d003509449200007841c00a00740140d01c1c0600c0010205e50f00030b518140700e440d08000180b03501090034241001c0f05000e0b22881c3e00d55400c1c00300f01440c015001000000c01c0e0317000c9008490305607043e07540300c081454407109111060303e6000003024010006901d003100305034140884e040500803002c044c0e00701c0b030350117009003080901c180d240c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 796369271 1250 796368021 796368029
    0x9030816050403021002070b03040f110906130c020309100203040f060f0f1b0c08010c02070515040605032d09060c0a1706150c0a060e03070b01051216030c230604 71
    0x5102c0749042e16035181b0800c9000094a40a849107640742041e0501103d5a650688211044040d550201703c0a06160112a004000c0941541d1015800302400c038050040b11042004512047c0181c07006075603500c0200e9400c414a07006190782d0760402c40d00080d042c0d071a80206080c082c4000004d00d4003507012651826100d06440e0840d08001501d40d0000c200c7c140e40c10241400710206404160000190b0141001c03003100d030215005140d4500c180907403103410802d40d04060a003844100055030140c0d004551045103007040f01603140301c003081c0d450b111445441009554a20780208a41d042080041982012440010504040c01d080f03005203400f400c0c5101041d0f20f0703540c40c0424425220348010350002039400200d1a142c00c01d008a07035940d1150f2150580f07a4500b4072030905280b58000c42154001a00010f01036980d03800c050900c48280c4c100c00f2518007501c5441c40b40307124500c6543c1e9100c00b851140302040455460060704140b081155800d10411741c112140f007180c540d0f40e0104840c111 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 796370521 1250 796369271 796369279
    0x1c1809180209070c05060c03090d021b0105090109090203010e240f040b010c050a030806040c360803030c03040213140601080a09080d0c300b0f03100903081605040302 73
    0x10b0f548194088460703903201503006080c0c2c401d0f9000c0c400d264066001561040500c5022140421760840e0226616407190f5030302e03040501d4074000200207501c034400a103009881810006500d40e654525078040b43e000742c1c06156009610b40c280100c03580c495144ca1401050072000c150000010300005500402c0a00110300c04c0d5929110034580741d0062040203116a0404143c94200d145c500b00134208203800c4079880c1c4180d2070562a95910b0303008aa40c8080c5451901c02124543c141050b4040480350719075048000b10540400080d481a080009500c625061080a5240c0c00c0500c1030100e00c1c00e00440044000e4140a000000b010030500e0300750344041b0900e0304030141c0d10703801c04c00c100030003981c040035007140340000700b8241c06131240e08280e00840c180d5441c2640c03820303e4205241e114014140d0041c0c1c0f20484622403004070101d030401007100d070740100b5514841d840000028074200c6001c28100c04c03d0746070750012044c5508040b91513030040d0303403111902d19000e410710001c00c01c1c4100d000007441 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 796371771 1250 796370521 796370539
    0x50a06090b030a14070305071b081803071203050901020d051206040c0e1e09070503011a13050d060504020103050105030c010203040b03091509061801061809051c18091802 75
    0x441a41c4e004114100b40400c8514607900302440014040c0c03800702e42d0030000c1403600302e01600315004c01e01440c42198004240c5400c2400380942e50b0300c420524055507601d807249400200b81c3d0004c0620a41c040c61080d02d4141c4e40f080510006800e1190008114007801800c1c04017540c8281c5100919502110854000400e2409400c007600c080034291030594016006201c000c80300c013411705580d442d100c411990805035130703540350084070306110034081e44940f6590780d1041018001e00c80d01a001c6a05503000c0428556100c0d80418640e154815003a20342c6a01c540c01d000c02d55130144115405000143c000c1d000100c2c4501c0081e5680c40f50744070700307603000c000000090b1082c9010f11800710140566040404182070a18465984a605a407240300300100d4810a030114501482214100e8a0281303c1044202c2da1614501c010800b20000351014018502d54003111000180001050221501c2d102c43e0300580c8410611840019080840d8141c988190001c215201034100d02c2501c0d4101d6001d60 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 796373021 1250 796371771 796371781
    0x7020d03020a14010c020c03010902010f08042a05041808030106050a0302090d21030605030703080318151e061309240c0f020a1101080709080a050a0606050a06090b03 73
    0x4078128450001401d0083c2011120402040c10741125284044a81c00c840d022400d0f4000c15003290200200240864090850003481c02c1c010b4104590040c0035a01000144641210403c850003448810224840d40c00300d0511030340c5400e00c900200504802e8502c40c2244040e0f48552662006008040900c640400e540001c14880e4040b00e00100004c0c11090000c50307645040c0d001662000700340c10000710701880d0040e280740b003072003000100c0e540100200209491a101d019803030b030029101d070300d1404045040d070000301c1003086140b0950043c0d1907662000c1ca03000846103c0603402113441845443c185c42405202e6442041c0781a10b842c080c0c4d0000786259944c90710008600b182c80356910703c48012581103220408a5218103a80d030225201c1001803c60f90000301d031510720a00780180040115601100d8551040d14a964040000d06000c0b40c803036140c400c0c541c0f401910707000032503c3e43c1c000550700341081028000e10000346400d0740c0420290741040070107080c0c014540100f2080c0c80010002070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 796374271 1250 796373021 796373023
    0xf071202070203070b07290a0506010302070204051519030c0b1803060a022502180604020d061e0e0108191502041d01051c02040906090503120a0b0303070807020d0302 73
    0x50101c550040445010903603600c056005031b0802901600d1a50300700b1400300f90302d11480e050310010100008107490baa0382d0401071000a00001d450305042690a00c4200e0060b140c51140c507020323003850040059130100041c104000c0b4860042d00b8160078010703c00c2000014002c51012040c0d4450451007078580c542e01e082070300d144d8424841c07158544524014860366050700c0d802006498142600744a00c1844510300c15140954030a0007500300d4000d415a00115400c000b449030083c600800141c81c009c0340f0706c01001a250a900720a9040034602420b0a10034800008000240515140320300a90f142030082030700c07606035403103003070030b00e46440a46000c10000b81c80c2403903c448408070841d1603a0b1900d64000380d18100340100a008902c80b8004196450421996030307600a09800440890420b0703820710014090680d0200c030400e0303c404c2e0300e40c0000c5085c80034003000103220360825102e140589c0f62a00b51303401d03c0d480d14000e42040020202046100c0c3c1100c002640585000d0380b0250180780132 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 796375521 1250 796374271 796374277
    0x5010e0310050717010b0a080406020921070503100b0a0302280f051804050712020f040501080a03080f19020f0d0906020406020d02150a050601120c020307020907080f071202 76
    0x45a1050310705001c0100c0c07140c1181d010040b0701640d20710344c0500d03a29070280940600c1030340307103072404030300344400160000d9029002894514000350a20504800441d01c0c5c1007044013a50f20640d4581000000307000b01e081c204000c81400142c0310050000030700d00d40110305544407070300010f8061000c81000189100f8884080c0e000d40c3c200d14070000070f844d078a54040b0f4110015020b01481012001490740004d255a24440d000f42d0b0403502401039a8035000184103100b180190032070b000320048111032496600c3d0312400e030007841050040d00c0249540d14000b441600c0041ca0710351412800b005105841c126003e00d180e0049000c0350040c1c0c1d406982012000b54050380d071840400c1418000c0c007504006454003e4800c9400d0350302100e840e401044801da0310f8900000745030518940070800500300305c2c8a5001030380c0085e4181051541412440c034100192240d00c040e01000da400000d0b0041141070213424254402c500d45020642801c00c140600e4116902a008904104441103598910b101581c12 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 796376771 1250 796375521 796375543
    0x307050c0313121208070e0f04142d0709060e0406050405130b10140f010e0a0b04080d21050a15080a060e0f03071e0206120402030606150405010e03 65
    0x40c08a0065540c9004028443c1c000401c40c3e80040d0400300c810564043c1928900401d11601d03a142ca041c0c64505110705001460355459107d070701c5d02001091780d41080782c1240a0b140c2030b80c0075000d200715000586000040515403428a004290070005143d511002080c2951414903005084810a074001406050540c01c000da000340380806220341401484010b5000d1481002c040805a0351024202601c0600d442084202c07040842d08428503e0702c104107002c4150141000c2420514903004992030788102e41240074090b00025040c0401c0e0b004012803500d0042038a491001c410101184d06c1c4104c0c115502d1100e401e40300d01c0802e04105054000204910742d4000f03000d00ca0382d0300c8030b00c541d8803861150144c401500c0c005c0c48a54400c80812200e00707503c0000c0c01540781c0625035544040406081d8202c1d20302d40c0210050340e00503524000181702031104040c009c0000e040c1030041508024000d403042e4819442404c000d4151180342042d02d084070400d0820060648000340441d041000e4484 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 796378021 1250 796376771 796376797
    0xb0306010903120c141c05090d061805100603020f06090301140a0b0a1a0a080414010515120a0b010b16080c0f070b09090c1c0606050a02150c0307050c03 67
    0x19a4801461380191281c0d601e500483c01031414110030100f1507101d05049820103a680780082c00411024010704c001c0211060141001c0d08080303050321640e003216070008010b6207101103080200248003080207161a4a0a022403c000b42071866001494005840e00c13514068840465041295602940803064401d480300d0b400c115840e04143d403800401840c50070324400e40160324045000100c2c4a55030513404419585c59103803001c0710f101546c1211009200311004c0d640032080380707003550003070155038010b10746e44880e002000608020485031141c1080c3d502e010342e01c13996042c00072a48007d212811901c80d1700110f660364075488030024050f4203101c2c0190480e14001680c00303007030100252440103142c842c420b60ba10540c4900d58158244074108040354403404541c0425030500d02d181c02890840b42c110481c1440c1a88030794040c040d211141d0140c00410430125843d400207405100c209624503000c640406946051002103401d800047d096008000d00070451407455101082100c41061040f2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 796379271 1250 796378021 796378043
    0x90824182103011802040f03030819112701090603020a0203130f140a150e120a0605040b0606070f120e1c17030915100f090509060702160b0306010903 66
    0x8810407107030310a20484440c0769400001881d02c100d1442507030240c440070081e03126440e145480407600707a080a080c40034101140151101810100d1040741c80700c0c40000c0c0c4164490690740e80821400e8060040d95640c440300303420004c040c0c1c1e8840d40b074400b0b0f55514240140c9410080380d0403440c42c025401101c0d180a26a000840c0504a14a41900725441100c00300000c420306070901c050681d151107041e1040d1020154510140e004c1c501107140301c040503124649160810586618008401000380c6000d43e5403010310080c4411035196640c440401e8034a24940b10b8039540d902c0018000c058041c000303241c0d000d811100244280f440c200000c200178140d01d0410340c40c240b0070f40c2140030b0f110102c401c101c051500855004020054034421403000c00682940b50240d8030420701c00e103005000844003603080101251400803600103401134200e0000000340ea250031541c103464240c0103401c90080d5480101c0512071030b080100d0b40e0b0140d0710710100740c5450b51507907030060b45c1410150300001c1894102e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 796380521 1250 796379271 796379323
    0x3360f07030c05030c13050c0f030112110109050607020112200c06010e0106080105190503030c030423300a11090718120f050a0309082418 61
    0x10304a01038030300400400c82615502c10405030b903001c6580d021071304500b00010300c600d100c80c0b0340d00c0346510102c2841300500d07029a41d00c044030150302c05d030800c0d00200c070300c1c0c0e90314070601a84640c440e81461007800c082d80220b0800000075581e0140b90402410880c0c1080c4400480c0b005404c0141d19480962019140800502c1c0780704194128201e0041244507110000644445114040d412181103445141c92642017400b031101340302d050583e004a80c0d02c2c00d68005074588080004000c580b4030b500c01796803198113015411180d1012020201010b12648400d401c1c203590322020700b41200400706625101140604150f01881e80c0604a0314541c0211142c600130b2021204140f40d0b89402203c041c001541c8440c4156aa0420301d0801c88030104503180c01e02104c020101005000303401200c2072640c1218541d14ac40c5801d90038841200000e60800c3c0c104032030a420007000840000c02d01440d07042c2017405104d5800d80a0051050140c2603904c40c40c1c00701a2000d100d40c0c0c3c1d0306104910005103032640 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 796381771 1250 796380521 796380523
    0x70e0d0305030c070507150f080705131a120a0b10020604110d02030a080d140106050a0e01030f0b060c03131a0702010c023c030d050d0f110c100f0203360f 68
    0x50000c0f408080b0740c170000000c10051090048540c1c51010b400c40aa33258189842d101132264a0003180325900307810020700e400501d0010b40184580c00340040400c01031591401d000314011481c1e01c10044d54001c0050200140489240004e2081305880c900586441400000d1900090714000341042da40040d03a04a608010380250a000f00301e03115000560340c1c0c603002140d09104200c00e0710000341a211300405036621039004100d40c0003890002054100e40000082c080354002c14440342030743d00000c1d61594800c004890240108900c605540d03481220030510340342032061940007410011001c1d1034108640e550f010307260b40305540d0000a20661040c07100001500c140752942124002d00c54042d580a14000031800c0d42c000c2507a9999040486440314100034002c4141900e411903216600d41c41554a5840a4804844203400411324000c000c1805c40c201c5104410340c00740c0a0040042040c18040e101e0221100e0403c00600c0303040f682c0e80e00107a40390310568441040d20380030f20b417182c42039018 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 796383021 1250 796381771 796381787
    0x6060b0703080403031a01021005041b0f0503060603010506061b071503090209010b090a210f0305120c0310170c060d1e06080c0d1a0708070e0d0305030c07050715 71
    0x111a4401b0031070700030070090011108090455260040c0d011040c10a210703902a003019421610030000c500d03002110300610321000c14150040550f04070315074001c000f81d01e8204000da0300020151b008111504044000c0790b5244240340906010411484032600184410040f110062000c060441c610300030b183c40c01030240042c4e010030f9205100d0003002181040c0d50500321407100e0401810700040ca4900001c500780c0e907181403008010310503079407081070200311503ea401000a01c80e41d01d0680c0e40c00c000080034903001d00035000e011142c200b03000b00300c561108040c500c400d5800f58007020b180c00380010541c9107002816060300742c0196020035038951054072900803460b209191001c00c240611005000e20484409110b01e080c01e40c0119000790503800e080c240349100a0042845490752a503d804143c041c0340c0588c4c94400140c18401007003002680f102080307035154800c84214001c00700030f031001005400054045150304400103002010807004100e400000c160280100e00a04c1210602412500c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 796384271 1250 796383021 796383023
    0x16020307031103010b150a0f1b0b09070807030213240f06030c020f0d0e0315090d0905011803060c0504031707020f0a030c0b0702060403080c010b0307170a0f06060b07030804 76
    0x4d8288a070140407850440c24200c030b504e4920a0240c201004a00d00b2030750348250240c0d4406204040302d000d1021200d01360044100c074040d04600a150401410482c94022640d03c40e001d541c11841c0c00780016559020000403e66104101140d10a0038114103d81460311590000041206820002d4040e0f4841840411900d040d1800c00c21440c0c808026a1500c1e481c40403650190450401418000d000e210400880c1c0d01c05411912103000c0d198004880f100305030b940901f55880f1200e400c06050f401484070002c0d0400b842c2c89401c100030340369035400f50b40392400000c208603128a02240710754803601c140d41c02543c0103c104044011340000304003003680201c00c10390181194a100c401103042c400078030001c6a0340720340041c1c019450f00502440350b401101040341c0c00101004004080b0b400d41c4040c011051508000156200c4d08800309850080c180c1e020f141d4400481410b0711b0600780208080d2841a04040c54100151441c0f909000a05085d004507880781e0000c11050709040e0301c8000381e4891 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 796385521 1250 796384271 796384273
    0x8180129031902090c120a050f130f060c11030406080105030c0d0506010e060613090b0a05041a0105031f0803030f0f010b0301031203290306151516020307031103 71
    0x9854000781602c1d402101d01410300040090324280c018200105a0350b40809405442c0e0b003030600ea24181c003032800d07094036400c50b00754440092040e110550b0380c005800040c14246908452115030754006018003285000d09025580c01c100102103001d030b40c00c3e4031416041015603646a0b2148000b0306201400e0040318002e00c107000c50f2180701c0c105a228001c106230828002c041c280c2c602410084103000013405a50807140c1440441c060b0000052143c01030132405501282e00c45020007885200065a80118480c500305800308400b0b103803604808112080030320b4034560700d584100307640a040d080c008241d1680784e912540007800040c0403006d1406400c90028000c03040d29072400c92030001500780516454441c1c06c00040000a0036400c3e84004c0304a5030402040508000b01d006210411894015861211840320000c2074541801426840112941e11075551041c8101040c90341c007040d418040d040340001299610b41c034600c0c0f604948a42c0c001c007200c80c81a101d103007040c804107031404080d0103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 796386771 1250 796385521 796385591
    0x30e031f020a020f0303010b0712050f0409050a0515010503060f01050403050a03092d050603041407080c030f300d3204021e060412050610081b01081801 67
    0x4075007130100c21030303040346d6005c417440d03081214035111800c0c13040c2c440440700e051000820804031000408005440104809400060113141c03014068040d01c0000f4041078071014080e0301c0107803580c1c0040c2501c1e000401074446c02c404450001c0182c81030b00c40c0e9000584a4407850003040b040651010a0006440b80d00e20300d803d2501d842e0751000110941c81000d00184c8448040900c044e0801c1d80c00795501c140504250140050007001480c14000c06070080c42d4603400c001d0311100581010000d640c010000400201294008540396400041c4a481e042c1070404009404030010044030040e41c070743c41c0c28064204913080303207529078807038250000302d8084402c05000495020990381c0c50315070340721795001f40100e8024040055081400c030900c128040e80040141b0012603210504109030000700e1041c00100f2141c10500e103210b03540707000c40d4098591a8402d070040100e6164012030a104c10345c0030b00300705100707803569854202d030012802d999554640ca848203002032a20412903036001554045e0355400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 796388021 1250 796386771 796386793
    0x30e060f0109050c090d03091401050c03040b0d23040b0a0504110103090c0f0b07110a030f060f0f1e11091c0501020403020627030304050d030e031f020a02 68
    0x1885820440d1100040412a80104040c000c1d03500000d901082c40c880c400d241410280000d2192114404240c0028001c1042400910300b0002000c10412090a0050400d249003411540d41c0c403a5024401e5491300202d1042c0151410740c001200c850052402c1c1d440300c2208940201c2012400c46090300e141d43c2030008200421001d104042c02550440307040c4461020840054001e00300080003218542c108140c002100c8103501000c03c003038509403403443e40d43e40d1542000002460141002840307444100c1003040043c4840c030704a00245d0340140c0104181e4005188040200400c000b110a070b46e007400324400488101880301c411401d20710b1010001001411001040c6006440c690358120280f40400b48046129070440c00344075101b5000903103016100c0d404190f0b01e403c105103216071090008145024403010b0a0303980e01d0100180c00940c1081e24190000c1c0898140303c01c05400e00c41c0c0c041c03d00301152418001c50b00d02e9019440c10194a9030f10300e559500940c00000104014010079040b15 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 796389271 1250 796388021 796388023
    0x6041208160f03270608041a07090e0a0b0f0118090507050a11010902013c020102340b0a02120106020c040c1805040203090304080105070306051806090c0306010e030319030e 76
    0x2a00c5416900130000e012814190251510300020313000303031450045101e51502041c5080400e600c00d5440f6540d99580034604100350144c1c2d8405020030342040e0030203028503800d8541c2200945203070001d00e0310644000d40710303034000d40304449a000803448070b08060400201a411a00a000610b034503566150312642e07503d0320908aa5071000d00900180c10031860780b44803101d2000b40444c03000300d09800a61204402520200740807480d0000340541d4021501c80c43c8a500301c030036008100c1c0040c58071400903918013a100c150706281d800040602e80344601140320150380da410756055285001c1d40300d8080d40c442c80d000c0d5440d0003400a00d0f11071418054000c1c05203100d00740d5035000c8903420030301501580c2031004000103500010034203141071000340800900e00c4000d0003058050303c45602e002070700c6401e02080c01042c03540354400d030403600d045000303004568480000c280c0d400080302d15a40d40380d17120800100d54024600b00002c0d07140c031010074000003140c0c041c42080f04034446a1400c0020020b40182d80e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 796390521 1250 796389271 796389317
    0xd090506070c0308030c0d0204090b090903030708070305070309150605130b09220209041a07090b0913020d09140717061305150103080c0106050402030606041208160f03 74
    0x4003118518041040001d06880c05550040070206c80701d801c4c40c0013003001d04100c0e0440d0f440101a0364841050304000d041a070440c2e504900c06d00040c42c5141303071800002e00001c00142192041640d03520010b0000d610030b0f484000d406034040900504c03203990b081c02130302400c29805002d110740302c4400c95405484c0c43d407013509100c85002c2e03341d00441c0d4605044103450019404d0b03040144c0c00408500c0700503650501c086203e180f14050704070000003800ca802d02840c800820031800d00c43d21010034010406c685040c4c030034030101110366462600d20302c030400001c1c6c0100c40c1c030300c0d441c24201240364080151019600410a94000489428070f5035800410441c1c1005441c0100c0c0303400410110740c0d00020302e25401c180d0381c06441220342c101460701c06103e45c42003d034070039101c190000c20001c0301c3c0303802800307404000c0004840560450800b6400255940701d0b0b8401c240540700c2003c2d1203c00c001c9003d05075403488007005601d151001540c1000c0340d00f241004401c0300043c01c1e181c0c1950b814001d038400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 796391771 1250 796390521 796390523
    0x1020408070e10030506070512100e0c030613020c0c0f06122202180a18150e0f06010f150207030b0a020f19020f0c120a0303111b0d09050607 62
    0x103007030891410302c0c00300c0d1a80d8090181c4070441d07800c0c0b40c0070000c03078410010980111016968142d840c940d40005002e40380c0040d00800020294030000c022292200140e55000b0801603091603494544100180a54a0010100182c14008074040c990f09001042c44201c02c142514201c002038802010080e8601c00d4007510010f0188140c0031034429041d14501307071480401c03190825003000d001e0300012098001076070140e50100411040100445d441d004003c1480c04412402c00f03c2d041c15a16102110303c5406402d01880e40c90500100d114010801d051100800100b512100c1d61103800c50284038205010b0181c042c41c0c02c0207840e4265100080c044c0c11203030098404030b081d4a40320107031400f81d404000b111520325010303c03140d0120300ca15003021942448d1034004000d044a50701e202800d0590b110305c1e4500c504510410000c5554003c02d0102126038103240018109140035003001d6a0b00507a0145009a0041880c0500d80d13040001d100e1001810303500c4884400e5960010000c041c401c01c28 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 796393021 1250 796391771 796391773
    0x7020601061407150507051c020414030607020a02100e0405161707270306020d05090f01061a0928081501060c0f03030b040e0105010e010b03040206070b04020a0518060a0801020408 79
    0x4580004e00c070740c4120b4101c600ca00c1c1c030720300d441c4811005101e01d40084000452966000030208824504c45805600f40d020640180106150240001c0d40390425400081e0240348801405004a440b03484041c000034030040080240d0f080c80481440d10314a21078410020a02482210408c0071044146521400a03039030303400a084c040c040c43d0310110071801c0030207041c000c3c4100040000b030282e0000d8040040a0a000180313403520642c41440c124032800c2074107840c7d26042d8140002e1001d0360a01c0c40040c84404095611207480022031100d40000090142c4610f0810010860010011442080742c0e203410445126440c1d4004004000d40d0a102b010040707110003d00000080e00807180280c19030080c00c0014058010344003080a907102c080e41d0b0310841e55680010304c14121080811405007240540c00c60031413600303901007a80c0780320709070b00030780000d21100c0001c2c2150340b2804804080c0c80c2c041c102c40003003841280180c0980c42c05548880c8207240c009004580d401d014800d440488010300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 796394271 1250 796393021 796393043
    0x80105090105091906200a030b06090a060311251203050121110303131a0304030c17041a0d0b01210c110a0b01150c050a080a1707020601061407 63
    0x30700d04c18400e4560404030340c040d481d6043c01e41e02d103803c00b08260300e02501005c0160341e44c004410040440707001c01036452041c035081c002c4942c55151074400405884c002e0600143c001c1c20300100034800c0c05503078030b810842c11901c4048103210080f5100003031182c1c4540488002682104419402d454007400b4601400105a07103454800440c44221800180120703035812160201101013030840e0300103403a2500d1510900300070400d840c490314655205400004402d0f045052a40d07000707003141c81a500103000418150103510805540c482220010081c044241c030054415078000142900011640107401d0300d0003440c800503500445008c0d01712040c4406050440411210354801850204400020403045070b990a000300c0007003015041c00b0340a91540200d0358545807076130341480c00000a1508020740c02501070b00040d000502c920900e61b20448050300c50185d80811a41388d081c4074943c0859882440134820016008204141a03426a0750b03a02001201c080c00c0d501c1c244507000000f04108046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 796395521 1250 796394271 796394293
    0x903021902131a100311071b270b0907023d150609080709110d051005030705060f091203130305030306090a09051903050c031308010509010509 63
    0x891042015601c0100004501e4698000280c00c41d914600d90800b00c0407107152032440c51410b0381c1500300d06030640c501400100c1109001c08541d004802005210b02004040002a01391102c90301014000c0c3c0f50104543c00c511b9440708100c10616080443c4882c0b5140d12a0420304141210034852402500100400c082407079903403030203d42c2e0b421196070b403083d5440d032051054402002412070448181000c140440d00070711f060540303a61136010a092055981d0104891000450400c0441c2e0114030001419199090164518800c0701c81504001d8580401c0180320300d0030101800542d1829021180801e485e20b00307101c0c0794451035040034040c0c0c205004a03800d600c1e203070108046c03181c1d0305d100396030501c04c5030103001d103035810b4a8004a885810120130808039080a100099003e480000706004c41c2146444a5442d100840e4400380300b000203000300c0d418580100101c40150f940314080340d0361820342da004a40345a5203030184030019401c280204986d10360500400703000341072010281c6990190 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 796396771 1250 796395521 796395553
    0xb0d02180624070b090118081c110c0106061407080f25060e0a03080c030604110a0309030201061409160c1509020f03210705100203090a0b0a090302 65
    0x80615501030104260005000200e0200b000c194021141994a918071450508001c400c01880303003456a02d4000007400e01740718102508002c0b070300300e6440b980d5019910000c0c02c020307001800114001741070088144200020000401c20a42c1402c000c0141648a84045a0b8008080030b0981c0d000e805100110100d00c41c0c01c01000016180d42c0d043d49065008413a00b481c0f82d0840418580c180d44042004050103014001d1901c00c850405c05062178052982e0f02038280a00902440420840880040c1c199240c0d0790200c03240081251403243c807602d440500034007900b40c4840840c0154284913000480d8189100701d43c0d00d16000070401c0c041e65482c00455500c21074440e0003e0200103c405803c00400c1040301c080c010309002510118043c1003d0040c0f0030051005580140240e10021202c0d1582a03100c050b0414000c840c0b0740555101d0003818442d00d04121225820901071002003404003407200040c001120070710031410440d482e600c1007c404202c811012000c2c02580041040e0800e0107a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 796398021 1250 796396771 796396819
    0x103020901030626210a0c02030f0f01020a020c01050405130b03162c10061428030606020f030f0a0302072102010e0a2301020c10020901030b0d02 64
    0x90103240020307400b551000f414100e481132101000028126454115400030203000382100c200c05203072035050000c001d0115202911a07285d81004001c0c1007032a0400715074050000c103070030189000840d100d032020542068001d60108284c00054031485906a200d035000b90281c80031610700802c008401210030400c800030380b60403407000c0d038180074022013015902d43d02c0c16043c01508182c140403601d151551030303031005034004c804110b081d0760070b00d01008486001403e1140030f4401901c0c01d0741400b58031211001403801400320701c540301c054140c1c180812103403071000d02003038206d144d6051200c580c1d60103050b80c0b01e11510001c04030a800c104843f0b6502002c072001805407010a01e00140fa00300941c55921051700316021054185200013100e00c0c0c025424041c40c00c0034000c44018240d007209965913044070000485070214400c0011945030f42940c0298151341c81001030f02d040c1d44144405001c640001d40c42240c1541c0403d1401701200010704005e000e80350381c2c80d400707000425408118881149408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 796399271 1250 796398021 796398037
    0xa09020108040807050f160e0a090b0a0b0a0911031e060907050307021002070501020d0b040e33010807060f020d0509010c230706090e07020c010c0c09061d1008030405010302 76
    0x41b00f29013604290340010820a40044c400d03109034a521411b104a51010207805000c52414605003103800001c610521131060704541c4881f0000ba21000e4040414205c14065100d83c107168a0300c00c0d00604000c0d40b800a6114654051810b8003204688072091441c0034242c0d101f680102c6002d0014100600802c003d41c4c0140e460700459500c0d400042c401000c0c1d90110360100c1d202d940104811400c3c0b10b26000301f08440300112800c0c8031101380c450035030350346290808020520000c02081d4080345002c1c2c10b83d00482600700d420030039580d82c407503441c00c1d655013030340c400d82d4001045a04200040c510204111350441c445550380b52502a40e030004640860900c3c0301541d8007031820f081b410034464000b9020048048040141411500e00b1744060003e036000c1c0d0040c60522012010429846e031b0211f0300100c40a02401c081407110b85604006c00421420741040c3c510615120000c40d0040d014070801e4074100c081828180255144408451030a80500c192040740d4030500090015601079000340c5000707 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 796400521 1250 796399271 796399273
    0xd1709070b0d14070206070f23041514030613051f03030206010906170d140d0905010218100206150310150620060a0f11031e0a0902010804080705 64
    0x61501c410260300960701500582c8415075807403103158840300001840650150550018044928090102505124050b481c0204018500c00ea080b4070481c40340c40c81c0d00c0a2801700c006511a512050444142c0d0b031416003c20128100c0b031444000d6250310401c0320700c1990040c1a184000005003044006010040c0020301c00c00c000e1342e100080da007c620001e1004501940c01019654507002040d02194a180c1009045503044048010480c40c0042c007081581c4c80341c40d090700c90501030202d840d100d01803100c0702c0302e040d4105540c20040c0030054004c2c10b4106454411040007003014030801410403d624034034400b58001c03800080144110503140141c24001905481c0b10a40d242c07419001ca49030380809001211713543e072040c80b500d54021300034109013820a084c41750356417408248a6507400b0080c440107105031039009540d5007800540001022108170001103859080c01e0890710845071009051070402d400c1da900082440303d450040200302901a1500c03c0151115210035030035901c400410303201d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 796401771 1250 796400521 796400533
    0xa051507021909090b04031d031e0c030706020a050105061f1202370503010b1207140d0b18100e04050114010611010e010b09070507050a0209010b04090506030d1709 72
    0x91040a0300402c104a80b01305c0079a556494a0b15024044003100d8030108242e0302c50000b83c54454900080b500da50301d0300f520b200700070b0f0b1b80c04d060010715000c0140045601802802c10001d200c5400164020f401c074890070082c065540d40c00284407055080401914182d00f980c019140700302e001d10f2044020034014000540780c42e84d10706100300040070996410b0444480903100041000020300b050104111600d401c0e440c551500c7c54252003402413603442d85070340fa85140807824180c0510040e100c4c220340b6400d1700d80c9034410501d901009080c81d40301d850003100085000301501003281c4c0701e1881101c961403184241818014101350310070001303004944640d0b03585400701c43c0f00c10000c803080c000c0450f0303501c88456030040f000c40c03800d444030f0394801d034160307810105482c2c556078a80340031960140d814130700b5a4861165041207440c04801c400042e41005049002250710102007006006403140d01c0010300c500c0e00c6030401d00d079941c501c1c6107000c0300281c02400c0c1201000780c800201c68201d500041100d074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 796402877 1106 796401771 796401779
    0x909080415090e0705090f1002030307050a050904060b0901020d031404030e18070206060414060306060d3009090c0905100207090e0c0a0515070219 65
    0x41e92801d201d204214910420503030b00201482000081c0c0ca05203034901a02550004880e58020b0003034001c00d4505042c00c0340e03007407a2006550300440c1b41d540c0d6800200e03a603030001101d0500b0003e041103c0e0407241d0322801204080c210b406e2041d0340d5003024100280c680074602c00c040c0d06050425503200c80d07280c54201202d52080e00b40c1403040107407040c900000e81c45454170100031080d1241d441800103199000580c61311030742d02a5810005404d0380440c545035143c2c116006641544a000050700c907007803d0f130b800301d0b00900c9812820305a40c03440038003c00c0c00042c003039846c8004c00f40ca280d0a10769588414418000e0103040001c10003d002c600f40240091401d01416015a030010b0b00c4c82e1a030ba02c2000b0420040003650010048103450a103410b480d503440e1f60f001413164040d4400420381c1d1030080051138030b0b0300c150983c1926000d0564240509000102e040c6204202c05100010b = true := by decide +kernel

theorem cover : BRFrame.Cov 796223021 796402877 := by
  have h0 := BRFrame.cov_init 796223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 796223021 ≤ n) (h2 : n < 796402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
