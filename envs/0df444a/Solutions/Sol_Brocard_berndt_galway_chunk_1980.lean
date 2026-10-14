-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1980
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:22:32.958718+00:00
-- url     : https://prove2.me/submissions/f8a755d6-9d93-4df0-92b2-c8af753b35de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 355935251 ≤ n < 356115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 355936501 1250 355935251 355935269
    0xc080405180726220c0b0c0601080d05040b160f050f010c0c120c0f0812100803130b1c06172e0f06090513020a060e1305130b040308090115 61
    0x4901351902001c10b901035074680d038144c2d44031816445c1d9200740130440d001403030fa0f0311000800307c41d03a006c100401d0b1b0041c00210040c01d82810510740c02416440789100e5521205404a51079134240442e02c201c03030340181e000200e0320149c607141c90720a4032501d01d0348991302c155180114458031140580451400141d00c1100c50762100075040f1b050b40c0c0c0002c082410f903040803010b0152400200250300406019101c101000c01902c1c003040300c13440e403001542240381c90742c20501810301c0c0c9003203000c010410740b9070354880b9a8413003003441d90002c80208010b0f180c15500b17050900005040c402550302110b402c0d44002511031840141502254442e501c080d050411841c0c0300c2e4900303d84450303500c07084c2e02c030364058408100c00ea501c0500c02c0035200d080c0c4816010145501c3c0c1c4104610707200002000900003800e043d0014a01c03040000d00f0013481454100026071072303100041c6d400c41800942d2030200d03403211a2400f20b00749410000c0c94007500f250509065072818000c4140b00e050745a00d88201c5084034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 355937751 1250 355936501 355936577
    0x2070b0105091509041b05040e0c0d080c070b0d06050d0b0109050a0f0c05030f09070b090409141f0609090b0a150f1706060a03050d0c0804051807 64
    0x8014020035240083c440a802200c0803030703024003696860451401707580141011940039881c1510b0441e10480f41c0d0026200f80e28011802e14800380114846040600c210382d8065000054203144800707114444815490340110140420300401074005484400448142000880d4070f45041c044000c03da580042d001503e00c0d0010492614150070680e400200c45201244c00b039903a800260030740e0b080b100003402148020081105034240541d110350700211140041c04a14903007000c0b0030507482428040e601482d154820303803043c091580b03462100c04412400b01c0c0c2c0c001e00c0ca1003200b9418800e0030301c03692006052110009038884580078403003400b500102078030400c0d1140c0350b2110080450115800340b41521a4001411150a680074001001603e25078012282868007050074100010025407145803040300a00101e1400901040303811000c2c100081101c0c0c0500b005892402503034031150307024080c4841d240307100b00e0048805019a9641d103650402d10041854000c003c1a03140046400510131 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 355939001 1250 355937751 355937759
    0x3141b010f0e15150a030b04020108060a06140a050c03040b042402101d0105010b030907170a030c03050408030703020106031403030f0a0b042004030210050a05030a0b0103022a07060302070b01 84
    0x900f45550400311103a03134035032020340744408610300840700e600a96a0340d18090420081d560003d0100d9400706d4110f43c02d80c851400d140c0d02810f009c01082c100400314101040b244000350088040b500e0321010300c400ca036140c903660050030000e0340c07203401001b07044441c50310b100609401c0e8019090f0f0285150f00035002405e91040380b2001030180184103090603520b4858a000384c00f080c4a02c501900041c0213071030303a0b450109203680c40e1444562141c0c0245004540d54a680d04e000700304014140d80c0b516144d0031403940c0f410200d41c14002c0e40c000c0c404501000603598105601580884102d038890914a4500b400050380f003078aa002c200c0f040c80076400091300241d00c02000354030441925100030400500404003141500843c40c0c1503480d80c540110005040c410b61400000310300e030070300e000d203007044c0303480d1116a00402c24000a0301080707081e0744851401455078029015140b02c0c6082c8070b0b0443e240d50401c445040c440c203858602c0303640782c003504a001c254a4880d00881d083c05400c9500c142840e40780c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 355940251 1250 355939001 355939033
    0x9210703090e0c070f0302060402040b150d050601171e1b091002030c250b19050313020d030314160504030212070b0c060717070e04050403141b010f0e 66
    0xc107003010f404010007800e000a08804041030505c0d0081e030060145142502c140302c03c4580c02c010540c440c0352000301100030010b004080300c10b440d51485011680c2d8075044010307611901e00710048000100d08604000404a0012060001b1694200c0f41800c944546d403200c15094013418081030119410003510b416803c10764482c0480264a204070307031622805895190401c0107080c483c49103800c0803140f0326410038200d000000a0032080a1240c0b41c0340550f00020341052801071508103020740400012034103200e0340440d03407240cac0c0c01901010044810f854014011314105100340e140407410700115141e0001c103035085620501715100c09181908603000c0100c810222845401c4074410000f010078240b1112003d03214009001004086070b003003000c4054403a403100002c604481e0000c40c03c102000380d1281801d40140015a0300090603115400c048420805403600015815000561a120301e031103212040b030543c8044000700080d421058100703050712000380c9001201c1e40038520342c60016103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 355941501 1250 355940251 355940279
    0x10903110a080304090603110603070f080a09060501030807200f0d06020408030403050309011403060d080309010f0c0909060e0606030a020c160e0403030b18010b09180921070309 78
    0x2401004495210342d10b26075a851903000350414401c05407150410400c10101c1004003429904c1107500904525110703030010310040030308200b1800c01071700c0d1380440c520804a500c00741c00540c0115081c1300710341c1c490410b003005900c1082c00b140c007030b603140b044e408161803030b01203074506010010946039000038244100031625983c2401038810b00d42c00c100010b0084401c01c02000218400c0010319102e141410005d418410035900340c5100d04d004008018499444000c1440c003d68400803160722515036034501d90040c80315004890801c0e01d001140303a0030070341102c04401103a1080d081400100e440d0300c0c3c2c14807103400a0316140e0b000302003400418100c0c000f80d0094a07080c807481c0700f00c480403104c0c12086204101158030003506441c41d038080c807080c07540c5401004080078096407044190309080000d50510281441050507003540440d40002e49d68400550000700c4080301c032440207508003000c03040e0701c4140911600070700043c20410244030750078110a5901c49905a143c90420700e117041955403040f5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 355942751 1250 355941501 355941533
    0x6040209011e05181f0b1909080d08010305010c1d09041a010b070b010b070305090d03030f110301140f1e03150f090706021906110f0304051b040b010903 67
    0x1140406020401e91155044030a21a00700d00103240c081c240700090500300f503280446900554000c1c41d01b41300c9071161804494802d00f80011900154a01c0c000448a00485401044c85d41c020442100303803060f40010102e059902980080020b040000b030269405c00403108060f2000740c444491101c1403512603566680300740184100310300020000d40c0361078540d034241c00ca11202080406c48106114580e40d0344c038058100b1542180c908100c6450240c11344c094500c02d2032048076100202001c061003508550b040c2d1401c51402c0c003010700181c8081c29280c20034000c144000302c40441c46071140c078004020408100000e0030403119010061038803628070030228902901482076444111842c0c840e03525a5115550091013000e90f4100340b0800d90030150382d94444011580540b40042400c44180041c101960b407020000982c48020080010309008648040d40f111401000300018070501090442e1070300810800412969054001c0200725054142054000741e0091401e1000a0751050002664 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 355944001 1250 355942751 355942799
    0x304050309030d0f0809060f0420040f0b0310020a0503010b03100b1603021605010203030115030603050d180b03130f1e12090603091707150c0f110604020901 69
    0x8440407001103481c01c00404150000600e180c080800d02e0b65001401c95040480c442c061301e01e0381002580c000b00781101400142401d0400c604424100304000c074100c9905001810a000540341d0b505d4810040c104100f41c2806406808460303400d90145108682c02c502080c0c617400c0c156400c0c10344480c0c0c0c0745c10040050492010000010400b001d240d805001003441c000071002031054207140007810150955042d40d000d03a12400148210b0780c001c030540e41510324a0150140c142a1100101e0207800d807940080d081c0c1c0505004502040d50000f02e156200e0580c9403c100300c996500c40c3c2e9482031008482c10303124111030725081c3e000920f0321f03072002d03031198002d148052560ba000041c0058002d441c01c0100c2d941d5000601043c9000d4028030103a009007443c2c141040061002e4581903c1044100c000000c1c4540004140080007000e0081c082c0a84075484100885110050301400d084008640303034003c29451031000c501c2440c000343c0540300b0b55010307007400030903480c0403480e100c003003520000482c20f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 355945251 1250 355944001 355944007
    0xd0b030307200406060f0c03030e011d0604030318050c0105031302130509011803120b0102150f0708060618010806060906070b0109050c04060906111018140105090c0603040503 77
    0x1056590b0100d031000a05592194030100e0810200030840f0340c00e81c0714400340b11003003041c181030980107004e080768140c241c28041144100d040c401401008000e11000086a0000b5071981c0d600303000500a03ca288251010401c001240fa03031400a00b01030000181254403e0901001551040000d19004044c40301c10044c8996240d00080000700c41510f03e94226550344104031902c3d1702400b51414640541b441d44080a0701034400074003800b03080044102003503c83d080a81d00340d00c00c1140405440021082d0300c1642400000c40020800030f466580000300c6400204416141220443c0e8200151005040480e050340c401034500000041139140d009005000301031150b180c25009090340752080c903c140705513041c00041c0b81203410150035102d1101c0f0912080c000d640e0410200403e0340c0e12070a00c280c65102074504e42e481d0144011440482c0360504084030220755080301322080c494403820b80c103d000e92054090502700c0307900b10f40c0b98095a04c003449000c41400c14000441e080781c000d50549103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 355946501 1250 355945251 355945253
    0x60412020c0d1a2a030c090402070f1209180c0306210302060a0924021620040c0f0c0302010e030c1f0c05030601200f0c1201050c0d0b030307 62
    0x1a4035a8444240e0700032603072100500e43c450039900265400b124144050300e1403081141140c500c803008a821040c0f040001020030344110564042d2002d07086c0040c4159500c114074a0222540e054610301180d601601e40b51588506014588403400d03a00c0c00c2030080c1e07007103407140c000f00081c0004009010525540707150105000c002a01607070000e00c0b2510461486002c1c0340f40003403524000801100d140e900d00359100002400044a42c5a05030481d00906010b0b502c10482d44028802c010022000300d1410840b04108024070030414088180e044941c503c1100c42e50500c41540c2c40c0b4406080041d02036444420004d000f8804901c1040c024800000e081c21860440c2d45142d00c4000200019440b041d0294a8076040605000c00c0500084062180d48001500549640001351049060259004a4050f442107132128100300188840845407080c600360559030b00c48040e0035040f0b00444107400307000c10305030301401501c0c000c0000c21880c1c0e19200800500000600300f418501e0b606000410104d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 355947751 1250 355946501 355946509
    0x6020304140a030f090902031b09010207181406090405071e09022701180902030c0f1810030b0f06030414030406090503011a010503070804080405181e0405060412020c 73
    0x88091442601d1304420380c0342088010b000700c00c86034001d10401c0d00400410240c0680c0040142d0030025080c441c50f02ea64030040181c4c1892b11b42d401c800b111820081c0580082c8080c1d81061919212481e0183c0079615088184108418202c030060a01e0380124401c12005001c9000800c8410b08404083c03407242c4c0703418040069070300c54405d03030f078100001c0b640d09041c1403410040202d0341182420051218291100071662001c494851101c0c01940800010380b000304240403129891010058169100340d00740b405807052502280d0680200388010010712600c3c000e110b8140d060340001c003c62410741d00c500400481d588024012603a500030160f01045006040001c1c0c409082070313480310300845080106250071285040c212400501c0c1c101e240c440a030340c1080841c0d07041030240c82c0010180d642c50a0403841d51003035070302c081d8112180700000c0e419400e00f2490b09000c1c0604140c41c46440c4a00d03140c01c00d07014000d944c058181d0300607102040004021101c0c401c00c0c403500740181d81000303031420005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 355949001 1250 355947751 355947763
    0x30f0405071e03060e0304050924130e16050303250b0106020a1205030411010c1425080102040303020d1805100f0f020607091505090406030c03050708030708070602030414 75
    0x542c1c00c2004080c418001c00c6810b0044000b41c1c107803080114200f40c900783c00680d9100c0d01410707240e000310b09a5075800d00700a18078580c107070404000d40814070306401d000588008107030a00010105005113080729005200c04032103101100d01c0140207500741075600c1d1920544130f0080000c0d90900028145200000368031b60701c058001c100d03c1c1c020308050b04103820102211829013030f0040c03c002041082200140f09036a00509224003882c291030b09032040c0c40c04960340e903000303402003c403842200044492040303403100020310702000725004102103039615951800c1c0d020301e0200401581184041c50601c0d17214442824440d110003101801c02a51980480c0d06400c4800400d8002755036680640030007500109030314051700c070901c001c10640ca001040103004460500881e040d649047c1c030071030025880361054440043c8000c0003048a65540d1510031070b01c00d95440211903030f000e50740f00090f500c580030059409094000848903d01a402c3d0b480c04000c0d88000c10494140380f001142600d8075004000c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 355950251 1250 355949001 355949039
    0x509190512010212071823090411010207050423041a010e04020103241e0812030103052407030506060c0102180405090a020307180209091f140105030f040507 69
    0x5030303100d10f00c0c1031030340594000400c0b00c01441b0078100e85003c1c59040005d2030003220110300c0018410000d240b4111032a201703c40c03200d0340c0040c880b4140424844112034900705036009808850702565928180b109607400c10400d913040e034480a4a01e03001c207020030903160380244510f410304410202503680e1100c950003070300600205d120f0a0104400c44d40c0510990403103602401e408800d00c0d50126200c43c10030314a000d01200b04051b0341d8030018910511442c0340140c40908141c40e010404404410055002484181e5080c401e60707054443e4a035a0050804681e21100b40080d07c0355580b0138254040d14000c0c1ca11034024004004d40069140d0a1018000122203010070403000303d510000c000c180c1c1c2c40900b000750b007a00320142c44801030f0f03000a8603a080303824072075099070070b040d00d20812002405490f00460700300411604102640444603404182c2208001320485407588034110b9030070120010b0301d1a80459020404900d984c0010750303245a1083c8100100d0341c6550b1114089044a0714840b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 355951501 1250 355950251 355950253
    0xe180f27060601020c0402090d0f030201020c07030f0512030906010b1c0c030507080c040821090d030c120201140114030a080f040e090f06131e030804120c030509190512 74
    0xc1c01225a814088081d64201c00c0f1401c0d401c00d108c80c00059440701d640507004001551020a031000c160003034050b03402c401490000e4612195070382c01c0c00d50328060841412141c5000b140308414100b2101d0b815a4051001040144410b80c00c0503001030b410740c4080c00c40841e0900c040c0d440e00c07002445000c1c00384030000d1550081210700b40084007814024000d0055814400103001c00d000380305000440301c49410136002908505242c8100d865004e20607015480e4010000760b5002d0141504028000c461034450004190000301790b82c4102d08031407a1039001400c5031190b00c01005992107602c03029201100c003d055540059142c1d03121600340e402054405849400440d04020030204ca510203680445680041d0101c1194100c1d401c0e01c800700201300004c1e001d070302400c0d0024000706420b40341c21803400a1000a030191700d41405081084216800c40b4040c007124031180407207104450390340c0007035410744882c1d05000c1360303008211748240c00107400120701d0080f02d00001c0e40d0b62101e04460f440f4182234 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 355952751 1250 355951501 355951513
    0xf05070503040b0a0206091507121b030203090f030301030512030703240515041208160c0305060a0506010c0b07050a030209060f040801110301030807170d0203160e180f27 75
    0x4d002a06120300101840f41a400008094008401180929a0002051821034003198107000b40c20020b16080b2038804080c0150f40d803c4041c5901750b0b0086001d907a10b00216505550b08691042c0e5900c0700f4040140642c101c1021802c0341c996900103150000b50724107001c2003400d10107050490450544024102c1040e030185c0c10061410a01d041030710364034184144501c1c0034149562852510000e20000b01686000141c0090907200e2181c14281d003580700a00045d01d80c0c1c0d904000303589080c00d80d5200d24030340c07905021941c9580190200e200d810750100040013903985020702600c154110341810010301d83c00308502c001c5555110300419a10038407428880e10f681c1411030300c0d401c41d6250056103070895800c00043c00810b00076800da80c102503000e220307002056040e804a010a00800321440c1440340040305201d41040b2443c2e80c9041120700d9921000c01e007005004200300e645907a90944d03411044e500c0854240104052481d500c07801241e500d075148a015100c00c114401c840d208010342d50440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 355954001 1250 355952751 355952767
    0x31905150628050f0a062a050706030b040f02160b090c0a031a09060603030f0906040e0705191409011b0f030909060806010303120f060314010c030f0218010f05070503040b 75
    0x20790138030f1840c0c2d0400c3d126141c1541c1407442c06089a070700308081d02030182207001101c4003c142d2440c04010642d000c411742d440d031a03403140050058403811030b10394403842c10000d141f541d2410038426515090700d502c07030550142d4110340b1560082c40d40608041000d00800341c2c040880d40701e001003800114450003c51a280000d20441c000e1244054070300440c0b0f4101e442401940d070340000c01d503045d442e00a1511680c600c8608000341030707449154066000c0050146c02c101318660400080c122a104440c0800c418052510040b900c00d421056901c407a00000d001410342c55200304080d09440d451144510701401d00b0b030b21144036503030748003404a00091045500703004202090045400408103503000307102a50659601504250114000b40d06140c0d0f10800482901c07203d4200c88000c540218201c03124281c00108203028094142000c00440c0c107060180381030b000c16108907810355140c05210401b4268040c0115400c0310254200d00c104242484503101107441400100000c11900c42c0c55a034138001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 355955251 1250 355954001 355954009
    0xf0c021f02070828080a0c3903230a020d0b180a08030703090302100e03041a070b040206130b030c0a09050d030210110403060204030b01030203190515062805 69
    0x1100c8600e402042d5030a5084d0340356100700c10140707285500010050321080c0c5504121038549800a0150403a048540c0452240e4081004203605038001d06440b0070304210151204100382c010702c00103110310780400c607992452039400a54184e0055420594004050395000a40500c655207800c1e106031000d1410b10000b150f07140580b0f4441900074002e41440201a00c45142030b000040242d020f01d503c4103200c004046c400d12021320b44041e5410704002218141d01e0040d0360740c20500410264154ac01e2030400041800405d0ba0040d0782d0104000d0400d035210303400d000c69038201c041c030005036215101e804a01c520580024522510382641029240d07002e034900240030550b60340c4614020101c40d140c4a02007079000c1030b9550444201c460101d00745818402520341d07841990b10140c0b079140702160100801503080010360480340224201c81714100300d43c5c49010246002070000701694000100143d00b07040300d140b6282d102000a1566510002050a0078121800103404004417001000c0c244442e00d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 355956501 1250 355955251 355955263
    0x612110a0e090304030f02040609140108010e0f0307060b0409050a060f0c1b022806111b0105190c15050405010e0c030a03200327040c0f0c021f020708 66
    0x895018804060b0500b05000d5489114038040500081001c1041e2025500d50340c0002004018940c820882030700d40603114400940207000d40b141c00c0d4280071540d0351000c800550307141036140c1d640103985015501e030350b944000c08001c0320f000e80050701e500720000400c0c001d001e0000358600420000c60790425800d038100894243c01c2c000c1090000181c14013181c00240c02d0341010701c1d0b074155070f040000703002540103174884d0300110209a2103000d81c0c0c0003c110b030b0742d00419051a100d1490100d1300060200c05640c0008002c41c0030b454001a024099414809461481e1503a20200342c2040c10781c0119a03190390010060401000444a40f0307441804100071091243c000101c1c2800e01415001ea01e440000f41c03500c0d2160009070410032100e100e980001002e0130616040324580e02101c1e602da86070010b40c035008070300301071352144208014000521400c02e40500180e00b00d0b15600c01450004164060b00c030701180000c26600a482101c1c203109140700c00030071002244960b0020b12845240140191500c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 355957751 1250 355956501 355956509
    0x5091e03151f0914070804050c060c0109020f040c140d02090301051e0f0708130317040609123e1f0606050906091210050106080f01080a030e0402030a0612110a 70
    0x15107401480318904c0b40d522529900622940341140c0c175a2102c6c1007840c80c0125600c503c507480240007560500c521015801520360510035a041d0412840201c01c1004907a1401800404155000c2c81c59641000d42801480843c0138040f0042c1007950035008282140c50445408080740300740e490b48c115a4086420306980035106104c0d4040c00e14001c080100940b10180c0750b103441c0008410741c1010036005140350356502c400301c1c083e55403a280c142401406030126000540301261400306001d88648140420f050542c4100031011203845001076a2085450142c01d45000082042130100b92010074001502040c0d510540e41c411170300c40c1020401220810340c003171b1050041c1000100c201d515039109680300e47d04111030034036030000074072003031405c00b040782c409003011507d07100001c51010380100346140104480c05d0404000d03a02e0f4824969100710301c81001c0c1c085003212014034101d1031305400450307102c06800d002040c6507030b41e04051411100021801c541d0003c0b568140d5800e810b215007084010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 355959001 1250 355957751 355957769
    0x9101a041b09050402090a08010f02040509060d1e0f021815040204050a0512012304032a11011b03020102030a0c140d1802090a0e010b0105091e03151f 66
    0x34007030040010b4103001451082601554003c10703080e48076598000844010140140280800b0300c5002d0175000960007405904e1084038800c010a06508092114686096101d5000480141d122615801180380210200e4400d8180c444940040e1102e40042c00e0071a00840e00002909140311549210750003079039a0b9020b07130b01c103000130041ea903541f01402c012500103444181c00202150702d03581c05440452051aa2003034030034a40c9034101e0042d0286482940070b5502d20400104400828800184000e400001d10a03146001c402145003045949040901410603804450341040703111120350303000c2c90039030250754084104100340c0814011030000b10118a03041c8103465001141d100140219000700e07011685d03c40f084480202410000d00003140c005052020760302e40394800002810084034920b085508101e044145035010b003040c0d0f140080001c068000b192005903018408211440c01aa414403482500400e091802c06aaa02440095480702100003c90a05440001c0030350f000c4106 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 355960251 1250 355959001 355959041
    0x818040506010c02090c04052e08010e010b09031e0a0b0c09180a020f0f0301090f1505010e01030f09060c021c020709020a05071a0106091a04090509101a04 68
    0x140e030f80810075164503941143c040700c00b5100e00201c4000d0780648c1e0460b0f42c020307410f5460030000e800c00d032036030041411280c0b525105400101c60200c851000078860400c0c0300b0a91030060010303813a0070026241c4200b002d402c50303814a401d40b100244800c1c40b0b550000c01900b00010050a012280c1020756000c8030011010b803a100d00400462140e4000d80c020440080c040c4001c40d000b4071194044400c500d10003c03620752607644510245040d42d20030f218428441e4900304a030030075085240108490044088001c0c03801d280703407400641c5c200c5150798030981003580c1d40e00e04c50b0440c00700e8442c44010601074a00018080c142c054040d1400f0361850090110b00e140c0ca480c050341603070004620065a00f114400360311021190412740c0d40f4000c0e00b400030003402c10705044010543c48092460b04803501c0b0f940340060160703681c810760880a280720070f41c54a054100824480400b2a070461038000404400300c03104000d41d60911000c480110618420640c01d2030881086417905024101c083c2c0a80210350300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 355961501 1250 355960251 355960261
    0x50307020a09020c0c0f0f0909071502030a0905010305190b011b060911010c0b16170708090115080a020d0c08030c06040302010506010e0904020904080d02121b07030503070813020d08180405 83
    0x16010700b8110238429400f040020311189418403000000b0243e45404040300c4050800180d103e800150b0800006000000001025071180c0292805000c020300c0e03408a080082d0002000b03040c2c0c1020340c6042c00b01020786061651401405a40e000f07005a000166241840c82c0c01d03201c45050301540c80c100108075542c5070100d400c40c04180d80101c40d850a5407440008000c0580e15020030002030007040d0446400c1008071134105808600c110715001c001c201c18041d562000100005601603c4016480a0442c40c0141401d0182c0400076004800103140d895a0720700c6246036510011249155800030002d2204040c0c090098030303000300e824208040703842001008101c40d1140104060700c5200c1080200b400e011098080f1503880000090a5544403050b8103000b0b038100c82502d00410301c03094071040040c0b00280c10140d418840d855a9100d107540c0750f500c1d00b16540800902000400b00016004a00580d0b4401171808800d00c110920313900c488070b03a0404000850301d5650b25015900b0402045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 355962751 1250 355961501 355961509
    0xb0108040308010b0721030e0105010816170f030a0906030c26040212010515032a06181306030201030e1203060607150c270b0403060207050307020a09020c0c0f 70
    0x25041d04c0800ca00d06485908a080c0304818443c0440c0d040802c0c0c000c43d0300d52140f00d40c1a0811f00603001e4050003400b040c1d80e41c0130a42e69518192400104020201d40c0074450000da615604140d0840741040303403815101031064509540c4500003240215400309400c01485405001d0140c00a405040a2022107140082a00c82c1103a0410042070000ccd00000a4110342c0d0705d60000c1308542002000700524a00345e04401d602c40858440c02e84a4411240c01551092080080710001c40c0010104040041000d09000807500082203a4103044a090745140c965280e01229071102103010700301042280c0742d4000541180c0311248501d002d0382020031407812403c1c9407002c80790407101c1501c0160340c0341b4803410004440b02d0300c0310a001c101c2e0f003080d803482a000e40c0300800042c11803443e048a0a4603001c190b0308a1866607500c01c0c11915030041c4000c00203d80709a020b456128081c0041d645440ea8550001c0d40074031041d000b084070250f000c100b0301c440b480e041098140e00708081c3c6400c281514600005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 355964001 1250 355962751 355962767
    0x3100e0f0304060e13020d06030c060912020f0103050c0d050a06060f02031e0a0c2103051e0126060f011a070506040f0c050a06030b01030b04050613050403030b031f0b01080403 77
    0x6005d104140340240e440340050341181d119244d0054108070043c0c0340d16010f4074040c2c2d0307445818006609000e0200f0340c00003003411000615030040000749113411100056000e00070061404040304410300224025841901900748104070442e400142182810005810903c400000030708640c41808090913003002d40989807100349048801035202c903a00d1204172201402e450307004100c240315598291440100ba16600082d40031600e06100940d103898100a10400300001d44071b011001000400000000b0684042d505000c51b101e15a141091620b092030b01c00c0584503001588800030040000a0002003550402e1290074000d914100325901c8196462401400261400100d00b01c00010048055412802040e01602a80580e03503910405402070070782c04a5980820309000b8121100c0c0352500c40d85114500c014031065410000552210040200420480c14150349841039000ca60301040090070802c9103001001541d078004a65000f034a5007180c12031b05010b001c2c4148400207800050b8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 355965251 1250 355964001 355964027
    0x9061d061e0904020c07090b060702060301150302190c151506140c12040e0a050402180915090309190b040b0d060b04060302180f130b0109030203100e0f030406 70
    0xc0108810480752810050320a00040c690700502c0015500764000e40440c802040794024130040100090070341c2440003a200351080203610480420040c04100000603520a081c0e0081c940141002075048000c8141c07502c04030f04001003015a400d0398100030002c1100c1c1c04000300c1131b90a0191004880a0100c070072540d0080105001c680500407000f543c000381918944c00014080b241c0029213944100840d074028090701c10326903401400036441d18080d02030075002c0d0f0350150501862904580440000c1100900341a40c0c1d40a21075100410108ad406a02d020f02e8013800690b9440c1c1c0da580c10000b00c200e001d0f0000030b442510a10070015840f01c103050b54101ca4907501d08503070302d0b007403080c01200820440d040f0500054000ca0301180d0740ba4160302034140c6e00465040541c0148601041000c0340211501d07641c1d001550801540321036040382c11031414003606040c2144515240c1d800a818868045040756060741e9403074a001e10404108842c9001d801c10501030740c5000e0400c5c000802c0f03400c078800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 355966501 1250 355965251 355965277
    0x60313021e100c0201020f0604061b020c0607020405130b01060801050102010c030b0315071103120604060618210b0108030c01050f0114060f0d0e0106031203110915071209061d06 78
    0x60070303c1964024003030548050001c1c001d480c2e4902d46484d0000040080040c540f205540001201d40050b0001580710510a0001c00e000c1c00c100b225400c01003d400002d0030401941c0849081200103155661404d010b029140ca94480542c1010b000a08441713512041208060401c900071040740c030702152143e4101101e4440000039540c18038191218181210082c5080c400081d41c900304004244840c0c0c0617400844040c404259510b0f42110300540207001745c01c126103100d00404c03180c1620b605030120203011041403200c0001607100c1d1442181e003648020220b4000190300e1010000030f2083d182e00c543e075529a50303c2c0b035042400b14002030609800c001c2c0206400200300036100c00290903201d6150442600f48003088000220074080d1440b440100d031054000c0c519444014000c1c064044010b41101035281407850344000c01030540100030382080388282c20403036000862540208802e40204580b121059203292001c01012030030290440c4500d04e40503a01da004503610750003103c8407007100388 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 355967751 1250 355966501 355966517
    0xe1516030c12020d021507050d09050f0102070b100e04050d030504050a140a170301060e06071b0608180114061915090e0105030f0327060313021e10 65
    0x214003616801c040490107040c40ca0452180c1030300e03d900141d480c140c00d80b95425103020856102c0c40d200140804c4d01c0507004581c05000c000c0c1e1103881076100f4460203009604644011081250207400c9a210180c1a01c90700d101c0000c03c8503c1e0030f5181f40350020088940c5003075807480d01c0e403900768079602c88203104010903071101c1c00325060050410050030405d030004022803e8035864000c19580310b04440080303c2018886080b122101e0f02c16003624121220380d110039802003034210402c4600d030b1052108035080940681c07952108406800ca080282400303131a01c80c15030801c40a81c40c03003881c42c40348148480c1c0c10701e050070400d0450740c508150007503019100340550700303940101e0320454a03184e00001403500c680b0301240700d81c90344140c80000701c40b90603502a043e40d890307009054030350301035800d21111540304000c04148010b080c145100b07110400c00070b1200321321046001a155510580d100c072486686200307907000794600000e10040004a2203160803a2020f06004510303074003200100181440707400c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 355969001 1250 355967751 355967753
    0x3090303080411090106030b01020f07030c0b09030109120507150e0a151d030901090609120201050c10050a090c050402090a0302120703020d140d020a0507150306030f050d0e1516 78
    0x80f01c1c080b600e00700c003c2c1540541d41e15564024010141742c504a40180f107042000c050740c5001050402c02d407a0040e0100301c8550421141080640c440c102083c0c1641d41c0d481d062020580c02d094010003c0340d030b035880c150303940428100003455082c450300c04cc0e0f640c0c0c0b07404980882032800082c00208030f070f4410a220034051404030340400615222080000030b0110200d4002c0c1c02001000428001d00d00740c0300c02c5241a1540001c685174084d901800714a1400703002440003660241d0301400c121194402240d02c502c04c9410088240c030810303114540c031075844100c00c000f0000307682c1034075014190a680440c1000481c0002507030382040391001030700a141c11441c101e05480144030390340156402404460b460842450200403068a100c6141541c1c014800b2000b0041e10200d420040a50018024485c8609081d11101c0f1100b10310b0700a418035540c0c0000100103112442e8000340700d8051400303495515828034003e0501d180b9005028403881d200c02d5a100000741c0392050b2111400000d041c19084501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 355970251 1250 355969001 355969013
    0x91e1e06040507050903011e050912070f020409050703260f031503011503030507020a270f060e010803030403020610080a080c030d02041511030a09060e150406020c0a0b07030903030804 81
    0x3180600b5405508148d4111140c42c441050401c0f1801000f00802469951030011615450381e5421448003074400c12030000892502552000c1e10350006000140906040d07440324030704942c41e4004c0390401c1c0444020b046a005044034244407500c104e0380c41e860710202d05241c5082c3d20008100e50203011804641441c42d03202540020381e0740320600000c03085191681005025604902c404074410311081c100400d43c102c1c01c010940700100d41161099403440050108009000900d542038181eaa4a045c00070347c0389111094a4001c05550020b50741d41d04150400074104030008200a482181c285801c1040301000152105d0983d08450b2654803410743c01c20300340c154899498048400e0340007050101d0040301040d50b5020200240e01d55a600031490003907544c03070380a00c0b41641c000c030300105000c03c0210301403a00f01451090051808581400c0a0780408854009401100050703000d0100e9654030304100c10000c004d811821031850070302500740d0b401000d59056020050407c8032900200d410130007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 355971501 1250 355970251 355970257
    0x605100f0c150b15070209010506030a11041418010806061302090d08091e0918030c06100906080a0210050c07150f031a1f020c091e1e0604050705 64
    0x7034080314608a00c4004010007014000d5003e045104e0742c1003560281c000541d82007100c5d011640540740100b00d03031801c003c000301500010540340c07003d42c8038003c03010744400d0708000340083d0504c0c80000003130303180034030501c030601000034070050000359000014050305030000b6005a01030011503881603814118182140680190b050082c3c003d030b9040b0000040140400140c04011000d4031a03003403100d0036110301810100b91440003074102c1d4920011881d0a20b070000702404180001d004c8034a02400100b407a454060111100003a0303a40f8002c003400064018061840141160402421302e11190f0700062580d40701c024404040c0500014006898042030003070703000520340f00c14400582001e051010301100115041000001e180100812104000d201c10300060341000d0b1100002021000448000200c0c200404003540310781200504079035a06003002e0703c2601c41f60303440c0004604403000324a5a00020f80210f142da901041501084013200324400e921420440d40400d05440b03024084e1000c3c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 355972751 1250 355971501 355971503
    0x1101090807080606010824010e010509100e0306060301200c0a12180603060815191d060702060702150403090f06021b01050c0c01030b150a0906030c030605100f0c 71
    0x8010601d0018010314040b80c80c610525003a21040929500da0b80c02c6110003203020308010403203403040561285544646c403810b080100606200386400842c0c4001064082904010340c0010341c000c0c4405864142401400e4011000b5002403210340c0303d851401020f460101218010042d011949001d0301000308075007160701d43c0142a6042c1c14480b10700c000c2000032070170381d001480a041071000694038404d02c524004c580d60341d0017506410b0040c04a4044190001e4040c0100d0b0031090080d03a001c0070365204080d054030401e80d007035040110a0012a05000000742002c0641d0082000c000250f078001c203030a600c080403803456204664a40c40d05a901044ca9084415008040540820000c0d00007031807690f07409000e200312801c1c10100740111028860b03101c10380c01c1902f01e00c04140303042d4001e42202400c1d081c000d14200311034215002150958005103040c80000f4800b1100308421501b510940c200924180390a00c4080e00702008900a40074080e40d410811641d02c0c2002036491181d845400c5030307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 355974001 1250 355972751 355972753
    0xc03040510051927050d02071e0603051f06021605040b06030c0a03180c03030219050318060d02070f0308070e06090111010b040f060f060206041203020a021501060206010e010509060d11010908 84
    0x10f201300703041c5181d83c3c25081420380054800c0841c0400c000520400130781d03d91100d280d440d84280e0900e6004c0b4090040501404186031203402003000502e0280b95040c05807001d80c2c003c003110881481c031203084100640c0544d0103140303003411148403a103a07601100d41c040b40c420709155443c5c0401c0360480040051480c0b50002a02d13041034102084040b005603422a4003d45c01c585440000c4008207030120000e080040007035000f080040113104d8076044100c0d0b5103800030700c01410a051400030360305903401404200c3d00c4100b024080001c040d0045111034008000f881e1542c41c03403024001003130852180300d075800d050140c425509116100c094008640c1c0f0baa0160083c04003513044107c8074064035681c051130f04602d081c03020224246200086151241d90000d17131001c04103440c20f50a90080d4418005d00b0114050900704526802c0590130190088c00c003540140307021740c508000d2200d0350b401030300030341d104901103410b0280541d070b079030350711094140c016403c030f1303040b548100060310202015440b100311 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 355975251 1250 355974001 355974071
    0xf11120306130507021b0103090812102709060b060d050907080111030a0e03070209010b120c0412061e060b040510020303040512070c0e0c030405100519 67
    0x85004580554000c10301540d6201c1501d1104070004292107040310100700682c0f184600703038002c0d4841400000c850206040000b84400a6152112580d20041e04010407a2241080c00042071018003458010445100c06030700405000800311080000803440300d905944400d90308050140030341c0404102e64004020a40e81ca142a02490140c801103072803c83ca0700540c900020030b00070601070490070420f042881803840c2e94012000e4001c080000105100e40720034815540103858800015000e402100401034a40c0c0703604510300c005850003083c848404000b800200031503071400d0344c91500d01e64000004510101c402042007100e41000078003a51060601000240e4906103100420a4030010b6461103482c981d0f240d01a82d4a1109a900401590088807485400d0181388044c14030390b4811904d082e101ca503a1300014803481d01c20b0312980c1800388004280000c012040201c0c0c11516000380040c0407514060520440e400b400f800e584030065180c00e100c040054210125201400c40210240c803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 355976501 1250 355975251 355975273
    0x160302031b191103030705070213090f1416060507120c0c15080604050105030d0804110a0905070810061e02010e0a05010603020117100302040905210d1410060f11 71
    0x9840519034144000300f80c0d8011104180030020044038414541500c40c47d141c49129424131602020030040245080e907507180c15170020b0448401064a2400303800d142c2003c00c1c983c181a41000b5009448000c441c031401d40401c07420760440f00f0b44581c00d410040c2d00d49a00d510b5102595544500c00700100314919131200416a4120100b40c01842281356a42e42a16604c4400344012180b0a000d0240e25502032202d0b20100c80c42420700d07590040c0702c0c09042030024241000b00d1610241c6800c23022115032076204010700b41d0382c040f644c00d600c514164800381c00180340c401e02501450700001c001c132484050520040009000750454901000c0c1d03d411070340e10840c5420400d008069a010885c00200d040e091401200d0041c10914040e0100c0508000002d283da4200300c002c141d801000c5459020b01d043e004000c00740985604040c00390822040d80e20742c900182041140c03491310140241d01000c0e824042c00c44604140d91098820600703001c0000501084103481090010527600c80a118940c40d032a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 355977751 1250 355976501 355976527
    0x230301140f070f08010302060d0903021e0c0913020a030209150901090605030607050c100c030b030d021b01030207050c152502040b0105032208090a06050c060f160302031b 75
    0x140c4582d04a03900c11144100d600000c4540c41001e1101a600813414407610040e0802a404110b069102e401190b19800e81c4480864414040c0302e41c000719078000d4022205c2e0f03801c00c140056440031581809000a0206900094818040d400302a0244100070005003640c0e01d0380ca00c041d00301800034061101903a43c3c08240f400f038036032030060501038000c4402280c0440d004101f9107030030504040c05402d1000800c403a42c401408908588003c00d40c03034500480484d01c042c402440203400c540c0c0075242941101207240000c1240b0242c0604061042140350040380340400d8507002d410b4101e54039a058000f00944041074040d1142c1c0e441003141e184411078000c0b0241018042d0035109603418482c01c7d0111005607014001164081c0d0f468400d081ca10b8440322540809800c45403055a110f410b120702c1d00082415420242c102c0d0000c9640055500540642001400e5000003100c03188040c918240703200c203144413030511843c4141034011000c64142020a40d00e40080100c06112a440f5102c00c0100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 355979001 1250 355977751 355977781
    0x1c1103030f040504060e190e011119030507050c03180d080c0f0f060c03010506071502190311030709051306081504021807050a0507050c060d2423030114 67
    0x10134450b0380340071000070750074440705910b030f100710641d507441c85c0d61040d11401c69002e0445c08070030600315541c0c2c0180481c00301581d0050100b0f01c003c00301c1d101400035291006002c542d0050201002d02c079081c000c403039600000008032201960b44010440d0081a9000071030315032807171440000d10403140403402150b43c80b000212941d0b203c490340200e80010304145419611040705035044580d01d42c00b0401031005060040061805e18494814108000f1000c81d4a034100c0c4c101c1c504001171044c60200c001d10b0b143e498010101c3c0000e642e0310742455800d0140c0e01400740c07401c52083c41e000e600c0b80755074130b2942005548103000a01610050b40d58690020441c1e010052040b94201d1040c0d20681940402c0e901015030644035894545030701e440c0c00d00b44241903a640c2c02c920030488040c865890100d00a454a102070448034018440124002c1c6402210714030041c104e0405415004008408005421000c0486149844544540c42c100309448000c42d014013401d14500e000402e40c8001d10600c140300c2240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 355980251 1250 355979001 355979009
    0x6081f0b0406090b100e0d020108060613060e030c041521150c0305070c0506061504091107020f0910050105070c0e0405061501030e0a0b0a021303030903020a060e1c1103030f04 77
    0x20440c00b105020140e8008010100541d00b01508410b4a0015409101003a030090303001001c441c14900042000007140e6400d400000028100c520fc0801600341000340c50017540d0b084809204102e05545456a8020542b0440d6814159105a4103101032840b242c0b0003c1c0b42c020b00082d4002a5100f0102c01400c4c10801c1040004d15200005c1c4a00d40f04d9811414030b15481005071210361112420020030005404c241951114204400203a104062150070f82007021017007140c1d240d00c1c2c280100070701d803800c1d0302c0624046c0c041801005608a070485010f4152002402c00035118440c500b0310b02c00701c22594100d03d01c9508203105004c01e10900052407032082c030030010b2500300745178590011000e6070001c105070050b907408080e61500207000300489613440300100390014100078030845030440608440c0c0c8250701080c000c2c0d80a0040d410442d40400282480d800c0002109082c40c01083c42202031040140f86084050105000c004614055000e1000010100e82d01c4202c810004151030748a881 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 355981501 1250 355980251 355980259
    0x203010f0603050903030601230c0a051005041208090a14250b0f1b0d0504082506050c0c09180c1819180c090c0306081f0b0406090b 58
    0x200040c42902c40d0040a1013150003901550440e10b5040054410380d006406c0d510300c0301401415044203d6003400603108154440c0001c0c00341d01100c0c10b1060811b1903203000c08400c40d041c1380800001c00c01010360f44078418072610304959907613120a4982d08281200c0300080c29400000b0081c3c0e0150400254041c59244400d00c140001a9120742d20782480c0d107900c600188508140101188513103140c02170b000002c90003404880140d00d0000190a0045034490000420b10124043c441404100140300c5100320194040d103242143d40c400c0d140141c180d01c10801000000103c080d004042030204007210700018050710032500b071074035100d80b2310071000101c65120b201c1d141001046140100383d4801c1450707261800c00703082d12016444040800c90307214107108641c440071080d000e01d2043e200000c40c0c0d80521030151125052880540c140d6000e80c1035982050f05041003030200a102140e0740800c00d12094034200e07a0340c440405007010b84070102032151b000303241000000e0801039580040161a00441d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 355982751 1250 355981501 355981529
    0x150907140705013b1908070210020a2d12051c060503010c080402060a0509180702030901030c08070e1e0418021c0b061c21020d020c011d0103060503030706020301 71
    0x100201c0e03014481e0070500130755501042151030b0314050380d0581c11102d07004003a0703d490171030340760040f85003140811100030059100c00310318024040c01d40e90441980e0203c00e16034542d0a42400202c8000041a00c05007001d124030448090850150044484090b079400c545441d0101000f841802805d1901c10f413400395003000e003041c48051003408518402c40d4010400c0e8140805944e0032070302500200c1d4000e810150041c240190307a00401042071140710183d00460350341b00000e00050030b540316800d11209100411082c4030300a038000302a030000316010b8560a042e6002101407903c1810015589604280f81840815802c0644503410000d1030081c0ca10031041060104030969640314200060060280200800c0b014a0990000c804420354200e48044400040d290307120074007550f1101982c00041254502d00842c0c0600801880f4250340c000340c0082e1000c800085c0c4107290400070f808100c4c10001c1012180d0303000343c0c0404045d1902a0480e40c444a0354501100254000c0c06204210780f400c3d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 355984001 1250 355982751 355982831
    0xa080a050d090b0118151505040806011503062106051f030506100b130b0c010902100e09011a12130c06110105060d15020903010603081c0515090714070501 68
    0x180c0604000c80c080c44000006d178500d0034101d03102c1e02d0035032480401000300070040003490101c201300f075601a014810030001080c80c9190083c0442e0f0b020303030140c10341c280c001042c4603120300d50140c7c0300c0e202071304445c5c041000c0c1e0340c4640000e00343c144e1034a460141d02c803400c800b00901c200002c5442c4140c241d41031010403540ca4180c40c00c214000c4640001e2904900401400842135001c064102101c0320b000104070808540c4c00601c050405041110018422504410041c5000011039005204407046200c008001c0c044510b1107208a1060a40d8110420041600ca80c0c001d0450b003415034001c605030400300d0b1245001008455071600c001655800d02c4045901403a00050303172611107500c07030601c12218200b078080302d01075085011081e606540c1da010000c081641d91005110034050800004101490311500008440002d40304188911648912840f1502e5400b1599000b2500d401c2003858a10900c41c86c2a0511942d14010318550900289003c40a0851040038160340c0c40c40c006418030100c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 355985251 1250 355984001 355984049
    0x80f06100e0403140d06270c020705060c030405060a030c0f02070806040f030201020c0d020708070f05060906070c031502090103050c1303080d02070516050306070503090a080a050d090b01 82
    0x890040d521900008800b180000c2e0040100c1c03000f500c85284020300f001e5452080c9802c03980789070301c50b0341707030b50342c565a481482955820180841c01e078103c8100180c060820b00256a00454081c03580944030000b0800c400d807004000b40c03401450020000c507990540742c04024081c160000c00c460209d890700f003070a0000b90010402c2016682400e008200c15a220b455081c80c0d180b2202055056560030000c581584d08184801e1039502c0070303a0018200940760519092910f0495401a0302114a1850500855452100303c43c41403000f110056104c49031424681d50b04441c41d4002820701e429044407181425440e000390034180d030240c070100020b56071010780c910700f84a9213880740e2000c2901d60040c000120f080c4054103840f40030b441d00508010b11550b4071745c40c104010304581c1da8030f0270200d005c02140c60200081c5900c40072600e4000c2c10341c2407a888007aa0750040d103000408100e03000c202c5070021446030094a018007007116080c0030816013400c1412a0150a014290342e80c4072009114101d0340d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 355986501 1250 355985251 355985281
    0x140f0d12200a02010e041415090a110403120e030a0b091207030206040b091f060f08010603120e04090209040b1501051312150903080709050d0c0e1302040501080f06 72
    0x14801902d030100040e4011261071201c0c0750b486038025942c5aa80700f4006040300103910444c00c030701c12003040c845884200401c0c40d01c01018500c6c0c0600b0066191802502c05042e00e00b101d500c8404d80c016120000d00a481003400e100160b50548524420f03d000d04c840360b41d0840c0a06032680c107462004210700342140c03843c841d6a00107800b507803180c03020030001041c001009502c07996000607580d140f8940d0350101c4500003136000d80040e45480e0b144c14040309000d803500b54000c00ca4070008000c5a031441d0f9845203c0300320b0a201c03209005800c080e100c6140c035903410468805034001d005000c03c2c50940b400c49d0f8500001d8601000414030039138461080e500030760440b011810403c0e118410341e490140d503c030001c0700c3c160f011690703240341d2645c800b0b50f1031640c010381148500c6900c40c0f40c82450514002010000c496000c0c1e8480d008581e403001c080b80d051040c1d40290f414140d030064041c2c0d13a4000310351003502d400034000e400c43d1921000140940011400e81c01e003d1800054403c951900c081000e0504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 355987751 1250 355986501 355986557
    0x1201170309090106080402150a0507050705030d140d06050d200d240f0203090304051918050c1308010501050a05061309090f05060f01210507140f0d12 66
    0x480b400040c000a400366a500b5401480108030382c403920000c4c40312240075082031541c200458008180c0c2c1041040034856500600b00c00d8005003400a95610024a107e001403010b0440c03400024618101068607081540a0000642060002003003803900e00003090040744d03061003800d0903a00100041c582507030a034803455084001900d0b40c50a4503410788002c511090005844c981d00c007041007251074280081e41c07180d6080b00140d41c41d1464081406080044150019407a4841c02c90a11030843d49004e03080e552400703000d0004503a511038204281c1441a6003180382c84010010001400c401d0542080e81602d005850b03803494503540d001845036074042c803070340c21044c002414010300201031541c1c8034002c0180101c1a08950000300d40710705090a01c203555100350407109100500c070502c1e80890031815420780c2d003c100495038650b00d44c182c4843d61170003902c50a201600041c04199100d0074045d274a00707002051800400014540386003441c1c2994010408101e4504504540342d200003141d803125 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 355989001 1250 355987751 355987759
    0x90b03100603021818010f0501090b03070302030402150c010504030f0c02060706020a0e09090102040f050904050618070b0c0f0f01020f07110414090a050f01060f0323031201170309 79
    0x50340c14401c096020390000382500e584155500e62a01d00c0707940c1c0070800000344100c0032000d119541822000c100c0c1c00d61503000f440c14082080410020240c0e1902142d030f1000c02880c00503203036203d03840012540501103a5121101ea008142e030b00304c00e0010b42c8405d01551107500c0340c02ca003048051040d02c040c800c60201940c080030620130000070400b590000e055006541c41c2c45170341414a5400a12000401d490210032030b0740c04641031114016200801c2c015000172190781f81d003442c040c0d403650ba41b80d500404e807516191030010314050908013009001c0c080e03d0070401a80c0c482003c1e190060703a4042c604101c0e403880c800c0300c81c9130b09200c00c10301c00c850016040f02000d9191140c941c841a03845490b0000d40c0c1c3d006039503005c84481d007403a91403500b4040d18402e8042c0c591000b040c01c1142c0703825131555004025905d889010000030040140080840b54000390150000c1c040ea840084401c1601d42c489519000c00500c0110546032003e115040e50141c02c4000c05100d01c00502d2030b540e01849a10a0f00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 355990251 1250 355989001 355989031
    0x1020d020c012106090c02031c090f061503171210080322150309110405010b04050f04020c010f0c08010803071e060e01090303020904060918020f0d0c0312090b03 71
    0x50303114004002c85403c4522001181e141c1c1d82d02141070490b0b100c1003070940140c0022400440c0c1109122a150350b40804d04001d00110b0a07a403920021090900e13070003042c20740d480700003e42a00050519600950300030034008107500312810200c507541d100c107100f05442981b0b5000540304507850310b82c1c4816520001d000f541862001c185c405001d650066100b2034105003075500180418580d01444c0b070240c5140da0110b14041c8a24000310345002407503030284901c0c10000144003904d410b10644080741e2040315080a16240007010034000d10455400d8407203542000c001c00e4040202d0703000030040c200d06a45030b02250781d964070031684034014590010b001e01d6000300c241c00140c406150780408980074800000342c9000ca840018212200c0c180c04a011940204000c43c1d24613261007010700820086406001074542d180781c240e0300d8420110003e01c0707046400c84501d410f84030800210b0324560721950700c50701e580e145e0038407403e6001d02c410070b8000211020700c04a00e18014070192802032210303d181843d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 355991501 1250 355990251 355990277
    0xf03030c0304032d1209050d0f0507080412030207050603040c09050c1b010c08130201020705040504061b03020414040207021f020f1906060518010902070812041101020d020c01 77
    0x307500280007a41007250700d0800c6000542100d590440c411030080c0b040241440c0000302502840300d140322003000c5464001503101255010400218420051501c40307208250b80509452a00580354040c0282001180106d20611513414010b0071902a40869240582d40e404101140c40115030003413040c80802c10402c06202c4075041250819420304070182440b05607811040c031000441518005030f91503100c5401c00a81240d40c09070081160010503412014680020b562045c40d84281800b40c0da40ba40017800b0710525a110300d11a802422800640d2f0260300001800b9400a000c0d00c2007803441640c00d400c00d403a15108032245103034040c1c040061014650305c10081407508452150039070040c03000c41492090700344a91040740c000550f42c0100c0001d5401c0c036204890036a0002ca000d410310400c48a04803840011290440d422400301503950301c4107141c04d000300c0c0a000b0080030680c10f000180020004480c0350303580100403e0303084805c1100a10822a03542c12950102c1d4041204403003411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 355992751 1250 355991501 355991521
    0x5011b020a0c09090c27020307030b01090f0501171f030b0411090114060304140304120b09032d0c16093c020903060c03180c030c01050a02010f0903030e0f0f0303 71
    0xd42a994520b0040c110a2082d06e911007030380e10440d42000026a2811024144e43e080540302d0080c4c82c03e0448950803030304000000c0e02190b41c0e0b040d04e4a0002d00c04000550000340044043c4980c425000c10185480d40c900e8050181c500c281c80c1281c100440c3c0d840c603901420001d80380e60480da402041844090381c0340092041c0da5001030415030700111107540198002c50100024401401c5d00b0481410072005410412070b802406851a0704a82080082c820443c10071103c4c002060302c005400000210525212003061081101c012228000c0365070704400219a020740e10220f03a0340c4402070010390750480d4240007181000d054418140c00b580381d041c049481e41007550703180861441c0e0040c0f4005040c03000920b0702500315001c0500e0000042041210b040c034251081c584e040d1000142403240000000070b4032a0980c0e6015410081d000c03542200b80751013500301d2280f8140c03010041110019a09004018180c600510212403150440c001c2000d40c0015211410402105c0614110349540c0080703 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 355994001 1250 355992751 355992779
    0x806011a040b07020d170c120c06060f13050a02091002010b01091503020c100209030d0906022509020a120c0903030203070b06041b020c04050a2705011b020a0c09090c 73
    0x82c1e80014800a203c0000b039110595041c098441d41006520b030344500207c90320f004c01032010410440002c2c04610701e0300c54005060b541002c01104c1c402100441040410304880c8481111541e0300c0c184414040300c114642e00424002c4002c1d62000010301000d40140d0a954140085600080512401300000e00da00001410945614a000761508000c548054609114020801c000c07a50024454010b494100180030701d10095003003403000d02e8505080a521040784101c4d0448901614070212010102040440050308070440304546034200140c0040018a07005150040c5601d403201d00c041072800350156508480d4198020341c5030022a0b99905018040a019540c0080d12984003c1030580001c040322800100d5034020090103800400304400d07a00702802d00d1100310310380103001e01150211490040d440105a500e41114011031901d20300400301002c00842d240840104a2207065000c120b48200501813080008016229400701e02290a1420010010381d50104e04020326000400c40e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 355995251 1250 355994001 355994003
    0x30f070e191701230a020901020307230606041b050903070317031e01050117060102150117060108060105010c1205091305061c0b19060506040f0806011a040b07 70
    0x41400c1e50705018580d020100110307080301d4400402078030000c0741c030702c400d20410503803110044907a044200140e0244d0341d200c03000f4164030b41181d00061041e459034000c104840b2201e52140302c1942d51840000505100c10420000407014000c510100b00d840c5464011447d0125080d42c1c0a0092861060242c50544c80240481e07003601840c6000800302e900c20031154001c02c088829680d072850302100c24503c001c0c0300c114024604210500500041c0d0740720401e000c450007180008145500c2798030042c1d2411400c490410442001c0c0d20012900100a00110895a032440d08403400350b603c582e489900c0340424061075000403500713a01d00d4040361440c1c2c0b030b01c1040000c030b040140c9003035442408280a0490f242c4802802c6031100c1c248401410400b55541100b400007200003680c54069440400303020300503000e09007a4070040d514804103092548040010403006000c030751f4550b40c445800320070381c190b0b2042c022140108400018042c4103940e8a001a00c06102170381d00c0e20303061030021800c607000b03407034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 355996501 1250 355995251 355995259
    0x1030c0f1b030c0c090b030709020c07050f13050c1c201308062401020c01080f0c040e0901090311121c060e180708030f04050906010c080f030901060b030f070e 70
    0x4881d0f0042440503414001a020440022a0300310107101454502a803d500c50480310344104207132400c0d9400031070b13403600b940e0007101c11003131030241500005d43c0420300c104074030040707441d040601411f850007a000306800c000d4034880030031000b00c03000300e081150f451010328030300018540d05406d440103484c4c00601915000c3c048691030700b6113072002c4070300e001422184005481880102c4050050101510544c03011007407000300f0070040c0301d00008140900182c110381e040c10380d020100310001401c90584001e006110b1104100e450080307a01c030301138840c503c01a404103070b500b0038101880c2d07008504605640c6044015500d0180032500e03d800c04000c2c40314030101c0c1a59201c02041e0106c0c4600380d0750054039010001c1c1a884246404d05051059950002c80d4079401040030192a507030500649085600c111081031280e80c8460059031030307a0320040c00401114000420039450382e00000918051520744000300821601c0742403400d114403007982c114a0640580c4001078105125032000040344101130 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 355997751 1250 355996501 355996517
    0x402030403110d0e0f0901030317190e01061802040e1f03021002030a03060801020c0a03110111040b220302010e09070c0507080304090b09160c0f2001030c0f1b03 71
    0x49000d8200032800c03000d07030f00050031400c2c03100291800031001c41421074112010580d40d403555038050005003080b88500f0040803040009124030041c0c112242d03c4450422060010084000d00c0714000c02c0f1901500000103452200481000c60390b00c01c0c2c0381903456201c4100340688500380700d02c02d0303008040c0a40c00d1000c0403280201c010b03114080103031190601034000316129000010040c0035252140c100c400709a00c140314010300d03481d0009000c091217400d030030201c0d420b40c140c030f0109000d080c001440e10780c100320003d00058560807000003000d445d00e108842c1d40e0071018031111100000e14901c406400038011085103c0303140740210103c0e4101d40541001c2081e0a040c3c1d4a450034050590301ca07005580012404005081490090b800e00000803102c1c42e80791700e03107440c2c8081d10252040117182005444006042000b100f04061480035411148440340da6143ca258074407005105440e1900081c14940b04618080c042e08012101e40020307190042e00d40722041c00240840c0004005a0420004e0b0f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 355999001 1250 355997751 355997777
    0x4082503080a050c060a0b091b12071e08060a210f03080a0b150d02070816060605010e0607020a0b0a0509061b0708031c020a030207021e0109090b0a050402030403 71
    0x10304000d1072080c1da0b070780300c098407404400035582c10b00200400859910382000b01d00801513841450f51940403250413850132902141440c10003450240b01e0340039480017850810b2045090700110108500c5500510300e1840f071000043c100c90040060f41c00a8000501c0340c420f001d2441d016081c07110a406140f4615072520381515440101d8041c5001036010600e20307000d01444103003900138200e8481050f1440c00075001e4440e40700003140f00d6a61003c40c1c1c01c2d4049030020400241004455040f42c2803000790010380d41074244000140310342c0c86594003003a107914035640a400c16505841c682038009050483e0319180072207400071640b25264110422070b04012507045990703008041c000100c0390b904403160f0b089030550702d246011025041032410361b01c14000c048402c0c26100041c0a1104110800b50729a0354450b002c0c2c1c040d00914800950054800c40040e2040080c1408005a080d0036603078000c03d19601e44056088074041b20580e504040000740910140c20300e50025900244640703008a071301880f03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 356000251 1250 355999001 355999013
    0xc010203041b08160506130f080c0117090316021f090305071a250c030f030e011b02010810050d0503071101140403030309020102070801150801050a0204082503 70
    0x411102115182c901c0040000c44a84005500d00036020402c020704140c4c0b0071604c0243c00824500c105441640001640303540880e14450b280b00802d802c0e00583d15542d01d480e000754440c904400c1c15800651420000103410341840c1582c0d02890129001e18502a84188096031b803c00100c020b0b6040625040b2000b010818004a00380d1004a41c0e80ca0318001d0440c07800c2810070003035521561794001043d100b58502d0070400211b405070b10003045000b0600e0400b08000c00d03040c0c0c0d059005425001910350010512540713203203100b500c0d0302c01da65480d0040c1b00d400c010f480151030360020081d9510540c01040065000c3c1c240950440c102c0566510302558603c005030b20f40c001d01320125a160400f0803a2002c21500100c0896040400d00704628043d0801c1c0c144100b40c0124440a01050b0300d03400d0f610b003564000c1c45600090714010009200140d07021070348000030304c1d0070710450b440ba601c0c00c1c0000300c4a01c0c1c0c0b4820b0b40d05840d00c1101500000118a0b03902c4984000c511040c00d400f6000540000001c00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 356001501 1250 356000251 356000257
    0x100b0c0f06070c050c0f09190f0903110c03061501270b04050907030203060f0411070230070f1716081605011106060402030a150816150905010c080c0102 67
    0x112903451011040480ca4280d040c41c1007405040e0044240400e080304685c2d4401c407d941c003030100c0d180c1e01c00c600286141d9001410300b044131303a107040c0c1c507000b550014194005981c003030b0484204125040403030b00500341903903220119604c80ca101d0140001c040258464600c040c8840000324282110843d15032400080f680250b000c15410300700002c0401040c2800c140c41c5600c403056003000c5046150030800b2501e600c05441902c1d1080341d4070039400d544815200d054039a002d03005407901c442000e4007100080c0794071300c0c002000c618100e0110740d42c986810004000b030a58034403c80403402103152000042081c002c20804c0010b9011f0101c03807698650740400b1800c02401004020080031244011200c01d0740360507000541042a0b1141448070002c00041c207d8002c8802d4a0040e0380399900c0d000c000080060034548040404c2040300064039010010b5940700d4450989441c030240366441c04a00e5840c08c403500c0d10000b14403c54420803581d07009400b200e00090007001e0031031034190050540c0782241c1c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 356002751 1250 356001501 356001511
    0x150607051c02010c11031801170a06030b01050a050607021908060403021b060322030e1c020405010e07020703060c0207030213021b011e230405030706050f100b0c0f06 73
    0x240300040a401c10035424002d00c0c0c00102c2900340501d4209122090940301e108400400306110325608000801c1e91040480c210341c100702d040744041c241440070540003e0225444140c0b110501c0100104242c81c001c84a20122070b0010310403071a00c41c1d0b03603081c1700180422580100a115950300d001903a81820710246101c0c80c429400b504a0552020604003241c0700444254000d01050041107142da4424a452409420755003004040030090328045032121400050b0a41046810071402c00c0409044c102106052080760b0500071680c8698401810801c220b0f0303040c00683c81030384100040b54203540240244036061040d11071407a125004103a000181104c07050443d680060340580c4400400c841c0b50b0000c0b40e44009101c0341e00c501924241c0308440f4500e0b68071090b0f80d21070041c400c0300326060b440840803c030040740b00c8525060030400e4494018400c2615201c0c1018000340c1c18080040078ad91103201c103c910701c0c00703c600b0464160441c2d00700e5110f0802d14455441e20640c001c02c204601440b0b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 356004001 1250 356002751 356002783
    0x60f0a140405090304080d11010c0c030503240307090c02010509060408160312110a0e0136080a0305030610170c07030c05060103120207060212090f010216261515060705 74
    0x181c8c25000700e403400c4500c002000703401c0100b1102c1c1c180010354044216070b0400c4064031407881c068010110300061481149140b41d0501c034111700043c0c240456003180d01301c44516002080b003a80c54161041d00e8039000c0745c0c0100040d004004802c010150b00f0082c0103554043d00d400300210000044079411642c01c860490030082d004500e054000d03511200d0550000003c1c42e00c03001070003220400d480c00c0300664510000490141c0d00441c210501c0d6078110004100305c0c0300700c0d400c03c0f02c0c1d41000742040e4410780f00c140c00f48588449000d9294094050f905201c14030b490b40240d6075444060f813400c4c0b6002003904800f001a1651810085001001114003a40c018502e40204451801d0003038600000c1d0740c00401035401c00810030605035503030402d480444800307560101c00c115402004030f0400483e4084142150340c00403010800588a04503500191543d480d042c40320040002e590342e462080c21001082c50641c2c1c00011600040d0200000c08913a01425090400f2060f58403181094a15040c594036 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 356005251 1250 356004001 356004017
    0x9031e0c0a030e040c171503121207081312050a031d07060801060c0b18070807090605011b0f0f110a03060b0405390f0c06060f0a140405090304080d 65
    0x50f43c41c02d0b03c03035144094883d0601401d116021411469848801072450220b0404a81d00503120b44051004040340d08540d000790b0342c1c40192610b02e42801106554810004101c0b800103011403a950340807034012500316880c00b1060501d54012035456206200310810075480c1c81d170070007602ca00d865543c050b000011010708050ba040038002032501005a2191042080a51a24001c41c0360011210740101411065080c40c1c0c01d505601032a100b10381d8002e124074400d007580010340340c10680c080301c103071042640d609006006000c101000940c24400c05000e41040c8049080015041500304a40511030302d00407100b40e0b420000148402c3d42903100b92040c0340c4440b07403a051403500e88200c0c8e03070140442480b03d4039800d1440c0045070340c40c482440035202c00060702400030000e9290b02541c0860303402000e9a5580c0d00028091510f800040d00c80c2401448800c681034000d15164259100b940e00c5503000e0050a2005000c02010b09405080e283c1103020400011882d043e080c48044900b116544440740 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 356006501 1250 356005251 356005277
    0x603041407050406271104090b04271127060f060d0905070b04030b0103030f17040f050607020d0f0c02040e0a030c020a1418040302011b0e0a06050309031e0c0a03 71
    0x848907090003420040c0c54120040340d6600c4040941f820b50343c042e4400200c01c3d8642000c42e00601c0400b043d54082c00d0a14110910150040e541c2c003141c0c0c4c0b15400c628240c00300c0f00240300100c80b07040c2078030803040c03519404d2500016024480c1031340600003d000c11100c4c8800404070b40381c0c0d44000c940711302c050380b02c41040c0180031040020074001c01071a1002c618051854803851040385060000500f00704c0c0011841c100f0510030000700c0c074540400d401245075403d0a20300a0620480014111158040d800006280e140003144e01000c0900c9a10780446120301d13143c1c100c03000f440d07440c0b00320381c0326075200c8414001c1c1c2c0b01080203589680c42a124072190062a004201c502c55481e8030901c500b00c88103144128171380307840e040880188854500d00f2803545030340c43c0c16405400054450301c0e8000d40c251004442c1c5500c6001d154050205842c5070600c5512540202d8051108554100803940200900404040010701c000c1003004001c0c080d90429240d12112418600501030907000204541c440d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 356007751 1250 356006501 356006549
    0x201080622060f06080411010c0c030b0a021314030a060c02120c010204060315211e0b04110a0e040f2301020c0c010305091e0f0d05070506070309020603041407050406 73
    0x10001e0b10131401d1940d9245000d0b541c114481410322805c5041085003c1c9680c1001480ca21030b8000e581e10101808083c80c00310207880c0250071210200c0c1da0300c1515400001c0e40a0750180d0b134a440e03100500a8002d048007030304c84902518540e844181144034290200040b440352601a000000300c0f040003503911072030100000e040c0e44000300c038815030900038a0200b000c1c4100403a42a144501400c55074404003480c10005242d009035258801203290309204a8100402c644543d44a40d11035401c0d440c03503220030020f001c00349070365004518104005102003004a40700c0c9106861007441410a815117910004400340440072900b01c0400a03034020412828982003805844410709083c40c003005203281181100d40d940c004000d00410706414a808080742d0182408661175001da04000c0f5a4204007a60004001e64030030042a121801150041000e543c0b0174042c00c0c8604e500105050300b1612540c40d04d03d01a0400070100c80c9901c109800001c0580b104d015a10003001080c1d00001c002049072208 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 356009001 1250 356007751 356007779
    0x2d06070606050910120308100f0608060109060e030c12030706060608330402031005040204060e12072d05030106120204050a051605090f0d0b0105130b0d020108062206 73
    0xb10a545514030103000074160400f0f0b05c9403140d010702d0000f4482c0c0310303400210400c03940c51b00410010130703072142c0208030076400c058460300540c070a0340c0303491050740d40301000c0302c0c14a22182c0b4940e00d42c0103490100c40c1850452040300c41c0c9000502940d00e0f0400964a80c412903140b40d11640120f8031032810001d541d50300401440c11314296005444400200908418981909808441c4100d5010000c201070035401911800580320140003155655100c110180c0a045880c00e5244580191058045401e00100c2c54200300c8010303500c2c00b1403030745141d182964200c4141200e00ca042400c92030000d9140e03402d00804000344803489050341d070200d03107005202c00d079003008048086690814040c4007200000020b681100801e901e0184e03182e082840002c0c51001001c01c520b9805269808482e060112011040341220710817104504102c0001111a0541c0c45610910764401211203000e000b65000d03800882c4e0004004003a42882c40583c2d0b048a00e02c101703014003803161a0740c0d2034280512680340102c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 356010251 1250 356009001 356009011
    0xc100f050a09090509151e040605040f06090c0f06020f060103030c082104111009170304091b020d170c0d0e0604050a0309060201110f0708040f06020a05010c0507022d060706060509 79
    0x10b00b0b80c130107c501d45041c1c2000d00580020032440c2d0721000101440034007040000384551041e41441140a1410700e819145a20300440813a07800400c00007070981e000048141a98000c90080c100c16881c41d1815a10240d039158180d4568408000c2190b0040c0c01c801070700200c46e2105109101804c103410041d200201036002d9601a44078410100791458002c0403240444001012054401c0710020009040d8000e41c0d001c4c90500d41444410414190100500740008480e9421030f0105412103100300e51038441e850001040b284483c0c00301d248d03084140001c094200c0020b0011030044c525426081ca400d40c00c80302500d03140c100001000800d179111100300000d104134402070104d1012100304543c01d10420402444903a8002404402c0000c10000c0d01d0042c600900706601199403114080e45800002400712819442c3c40c1a8a0501e0b004409690400380c01810407540c0d40008000c0c0404c10504032224030b0419001c2d07082040340d51302c8600030155280b0601e80420018540018000c14280241c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 356011501 1250 356010251 356010271
    0x50604080307060c020f19050607090e07120908030f0613060513020304140a1a010902040e0103021002011413050f0703030507121407030801080c100f050a0909050915 73
    0x1009404400000e03285216000f1030b0005000e61000401d82c40c2219400309001c10340140c0003540c01f40e41404003101c504502510503104030f940c03204402c8480e41182e0140300010002c510204042d140329070808040c0c0f101006c1c0c0012404100d81b251015500102d880500c4040401c0800c0710b83d0412900501c044904036204cc41800d0a180006010410305202d1800c40b070f9012000034140680800d000c0c504110800503100c83d0192170800d880711030000d0f090f04808901030000020040f841e071080b50200c581180304400389909540c00c000b40700044078904000c540d02c60951940c1107181059031070040f03c9100c8081d00707a02c664901039060407413940800703090780c1041c4010000701c0e4100d03045030700719540403030b038042c0e000310b01101540c09055400b14182c1d50000032030740d441050340101d041c5040e64485002c5a00000729002000080008071884400158151400c18021806a80503040b03d40300b5007040300e802d5441d00204c108503801103544018030b038001c0e0041407c0040801000d42c1000d2800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 356012751 1250 356011501 356011507
    0x709050603210f090d02090a0504051506010e010806130c021b0303160f170d02030a050112020f040c02010216050109110604030f110a05210d050403030c060b0a030c090608070506 78
    0xb100300c1054007a1440150024074000703030b400c4041c0e9401810341e0080c2c0c0c0c01480c4079100d00f09218214028001101e0032034a5119080322960900b042c02da080344220070507902c400b980004c000c0111004000500101e40011440507d014002590301038041030082729801454100c072600c0103141500d00828540740607400800c129038803050001c11403000d1640201000719005090b15064410030b00294840340480008900802c80750040d40084d40201d1510030140800c0e603c400c800c00f10a4800180250b00c818a81d58009503070400e90080381c500a0780740001806c00c919507414500440c15003000322141d075551525041004204040d0b00d08c0c240082d50454180741c0ec6a07103039403c42e151000b0182503c1c0d4511003110055a5040129014100140c0101c3c0c100031304100c184010480313400e040c10b41c0e018902c1041c0c10030344990700303403030440387c041e9a400503d4601e0b40303e1500a00790301818980000200c80c0110203c0c25a01004000b480c00000001d8140d2400084a04003207840d00f00500c124010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 356014001 1250 356012751 356012803
    0x1b0f0d030f12020a02030904051305030c060601030501090b011b0501060f14150313060b040b040f0203181f1d0f07060e010302040b190216090204030c08031303140705030709050603 79
    0x100341c4a85000c01da800250585420b211200f040642b4500141103110004e803540310010702060060050310203803020b104590700c070700d415001d5405c0d070b400c0d0368000707080ca2806202c0c00b4030403210680620701a100000304161250004006542d00d5007010020364550071016000b0700f481841142011101807030f09046090003200034a190000d0100074001c280c80e0300740b080301e0b551180c0c003590824100510410007400418401d0000c0d400c00c0741d4561260420700c0310f61000810206240e1098240c0c000d0310508a22480f5000700245004801c060342c107080304d900c0d515806010030520103410300300d500410002d460140700508480091203860304242c011300042003100c1440003950700b9040d128003c864201032a034012807030304d00d14040d807040c000003501000603040c8140c0d0080007a20300a43c0507010030346e126400c540d80c07071107101403d94455920001c20800706200d0004003090342050760654020541e1840024948043c0760050b0003560341d03c2090002c149410401d1220191031078442c0c400c0c1d100b103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 356015251 1250 356014001 356014003
    0x180d0c1104142a1803010b0d02010509041104090c080906070306030f0f050f100204080106051512061203031005011d03120a021f050702010b0904051b0f0d030f12020a02 74
    0x1014080c0700c008a08060280e04940b820074043c1e28105203004110b4a40c00000d000b03843c1840c041003240c1c02035203000d612081c2401c107c2525132000ea01a100c1610f804601070a000050199070a100546030050002107a4021540502c0c25980d80c0d9580c0c5d10220705182c000f5604003200981140c042c9031400004200060600e440d009425800c150710f114440040d051450402c0c000c0c0c007080040d40100d80d202c2d41084060b501600545000c00c2c0200160340d1100b0074000c0001d0902c00034061000103220031400c0100990b64a46d201c0d4002c0d01c800014146030801501d16002a00c2407028600c3c07110041c001d41d40d000c40e44045540c0380c4071100c0d40000014010a8651b40704640182c0e12041c001400c0c0b40c034034000c100300800718020081ea0040c81e03503040c03509001414141c841c900154208400d8000d280f40041d007050040350000003610203000d40351481800c0b586040d900039005001d02c07413801010b41d0b403038465103c1c030760007502d034501061110703140185009500003c2c241d03880e105001102c82158 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 356016501 1250 356015251 356015291
    0x603022704110402040e1603050a0216020d020a0b07081801090b071b08030c071a03071b062307020705061603030e0703050d09090b010f0e040203180d0c1104 69
    0x508200101e0781d0b42d1951000c540a0320403504044100c04039981030151140c0b0043c00d6541141103590100f045485a07a0b201042c1d200c2c10141840e0014592000d201514004043c141c0a40c4000d01c0780903c00c2d540c10ba49c00064020070010388182c4c0011480199a80364420030001080c400d1800e500702c0d40c11301c1105541d030301a40c1e402030583e0200c040302d403040381042c02d04000138040a004990b26141e804c414140d13511510f024690f0240c189034201c070074105501d030640f8002c2d00280c07614403041c0082c03107150240c4459070806640d01500c6024001148a4074a00001020001c9801c1d148a1900d100d02130f02c1c1801991025005d1101042064505103e0301d42d01c100240d030514022074004480d10410380b4184458001500c2e40c0101030600c0803807038120040c84203c4690050600c0079050070001590550301c031162039004900787d022400c10314a0207074020340e440680c0d480c4a020000b9611600c1c1e1811380f0380250103002c00e01e518218000e00421800842d1201c9046606200b07183c031400c4003c100017 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 356017751 1250 356016501 356016503
    0x1d1e070e0a0b13050a0b1c11060304030909020423010c0b0a02070609151506020c010f030b010216060504090b040b0a050d0311060709051002031207120609020d0603022704 75
    0xa6403440e02c02c207907954510702d0210b019250b1900b0b00c907500307055a08000800024114512544240b103000c0344a0078107030840c2014903000013900c0140400402800000d40c0020822020419102c10102d0302440d90700c007a20160801141d03031020485810060013220581c24400c0d0f0622580200500000300d44901f0140d00103004480035032541483e180240107810280001058220b00b0706043ea040340c00f40d40102440c0201d00710740d007001c50343c0300d1013640c4580010700c4481c00a00c00c0500440924001c0d041301c100c412040c070444421503c0d007201c8800d90460390b040302c0001100014100716404031401110002e1404960030010001c0c00700010b00003048a1203090301a085811040301818010b201d0409903689840c156904c40c50205030080c85441c00703004d020320401c6401a02c401d60f51000041c0c801c9280162102d045030307101c400c42901c540055407840d46440e5122240800c00d0340d55400509503d0004000105809041d0310420440e926812401480070071880e0b2300407085810300c0141e6401c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 356019001 1250 356017751 356017771
    0x106210c050c07290a080403081e070309030201050106050f120c0f0301090501080709050723040b070b060301050106030c05040614160b0711030405031f1d1e070e 71
    0x1a00c040d04081e145030003a41c1852045004003580056210110038200007a08252148180038180305640d07591a03002e84443d41002400b58000100024001c0488135004031891045041407241044043c80f14881260040c0029440c0c600340c0c01010f80900845000d0502400c0c5a41886041490304019004195038140c001c14220042503100c0389039412034091100d4594001e64968503140c1110140c4000c0c8105035061003403402c00200c0c1e600b40d200d12402098940e03074583c5001920002945012071510316418a140d00708000030b840c0030041c00410b0494441c0000707501628051040500b1600140e12050605041038022071000d6845411642524500c1c20080d60032500138000c2901d60240001c220540da0400c0101c100303004c9040200d034460710440d070710700d0440a95060101c0e02d90199201d1540c040c4d22548024003000d114015082d403a1040950000b50031130000100c100d89100503815034202d0300b0910382c416041e01211560b0420041010060070010300e450044900100003d001e2020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 356020251 1250 356019001 356019011
    0x150c0915040e0403020a0c0501020712061a1c021c03080117010e10060320030c0d110a030c030c0b04081515030a0503030109060e130f1506060512010621 67
    0x90038821050760003925840e4400b42440c40c081c540030b0741e2600c540c0004c3c2c8003071140fa50005165840040d0180c20b4a100c1c19102c2207640c40350341c0d42009886c201041d000c0c2c1668041103901d058464031301c0303c2d021501a070682c2902c1e5220740140102d0320345000c0b0000c0009231502109003c690030500c80b90442d2030781210910f00c2d410b4082211700602e00e481c400495401204904034042200d5000309040d41e0290506440c080354130001c602101c81c98050841d00b54201010540700b51404101c40d0228502420f8116580c81c5100c0c0005c0c09012076410881e00c0c0d1101c2c80d800d10030310640e04800300141100031412460309040c0344075550780394091850408031409020000d0305241c4260041100143e01404441241d01d6034038050f92240c00134080d0890207440d2502c0000d070704038441c1ca601d02a0b44c108511b4460704825031100b15207002240c0e415220615030412644000030b107807041100606c40c80c1d850b551920400040d40d00250343c103900a204100689080035a24602c00c2909800441072542c0050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 356021501 1250 356020251 356020279
    0x30c0708091807030c0807180e15040204030f060b0303070308010918021807260a05040303020c0609010603200913020a0b0c1c020127020f060a03020a02150c09 70
    0x1482c03454010344002040e20718041c400303001d4058000041c0e41c03050707456808240e6038018040b200c00610a0300c038038541c84454400c0102c0401014003e81004180030004810403d0001040990740243d20403035040c02010700c044140407241c13086c00710003207044029520f0524651402042801d060103031480c4596030340e0348a903403007030721201c4611800d42c05080c804204164000000340f00390100c40004c0803903c500000c031a4148074404030b00421034a2000c103000354a0301c540c14030040034001d2003141411b034200300c03801d101013042100314402c40240001080450451510301943c2c0c1091409030b03615106c0141c403a140e59100c082050340701489484441d800042800000d05241d52644800385d01100007880c2c548111020450001021406000a40f08050b0702c00407070882e000c0c05800603405100442407a90742c8140031031b1706039a41c001818409031104200024031a03500100007640841d030700003040304400d47c06102c0103280d00d00c2c10460040300e00c0d00c6041411103200711600180303e103101b080c0b00a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 356022751 1250 356021501 356021509
    0x8060103020139030c213009121715010c020f3307050607080c0409020301060903021c0803010512010213141e0307091109090a0b15030c070809 63
    0x1c0100c07150700441c8190505820b024210340403c40c4240d81c0d2820a04560115844070441a58000342e41d60301c8140844030050040340410b41e03003d0283d5000070007503402c42c0c80c00352406410011030003501e031034000c8270f40c2e9440507043e1101c00b541800c10841250405c801503081c1000f66402d404c0c203080100000d1018400243d14403c0b14040b00c1d8002c0140c000342e000040d01e03c0905c0d01e603541054440d0090b1102c200705042034011000018541d900c0440002c18080c410802c058008031400800ca0070151581d06007000d98100360003200016519410400940ca04275007101240c4402887c0603000301c3c01f94803440320901c01405100d0050034400c04884015100354115410030520020512070552100807414407040030400d0a0303c141c03003121080111289400b5100b10301d8200500070620300b803410480401034582c2e0103600c880c02400740866080d42c1c0743d82d040e0506c901804000040c0d480007050411000051800442e035822800b40104185030201e8001c5039501904845001d4a40360f401c000a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 356024001 1250 356022751 356022827
    0x40b04020720010f032c1e15061002070308030c130f080c01050c06150d1b0f060c0201050706110c031b0c011704020409110d050313080601030201 64
    0x10000e201c1800c02c08620000c8a6944411460980e214000d2000251048043e1801820309048020141503100020900442e0b101d020b10355101c1541c11161644401051103588510000c00e2600507802e03c02c2c40102140c2c00580c172040440340207036000b2008800a60750345d000c3c08000d040a82c0000030502420912003619071205035903030308100303403078481c0000c0c00070260a1103449038a218551040944c0d40c0202c054800c81c000c00c400a008580d50a030410004034169444650454184088c9a020641c2d81580c40c1038181a00103101810785004940c0150050300d030300c5102000b000c3e0300e0400060303a11108444c0c40d03a40101c0c0104070600b04440040b807a1003043e0311400c15110005407020030180a0403410503540050082e00c03035103031440d801540c2c00c04850b0b282c8020781001800250040c03a166000c0c103013140c004c103043d140200048001c258091000e01b0300384d03901da01c00304a454425250410510141c841351005e8000c07035146600103840c070b2072107031056410020142410f07101c241c016821 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 356025251 1250 356024001 356024003
    0xe06011e12020c030c07080d080c12070314010801050f01090e100510050307080601031506150c0303090b07180f0506190309020603040b0a0f050f06060a0e0a06050408070f030302070302040b040207 86
    0x40e280ea44900703503a5a03131303035108a20551246008800c8c00700301090094034001e1041001c80b013030760b152420f480401d0f21000d00041404c0d0a05640e030207400b2894a03504c540d58080e05002c800017030340e42010703103114030824016400081001d00303200c0842150f01c0c010898182400c81c1c1d480225243d22080c5803030705044071301e0300402c1d094442c280d1b000840000c0000d03d18103d83c002c88401c803c4032176861022098542d54090314a03240c040b1021200014851321503c43c0240c040d2034005805042c03030ba00c18084080a86800c00000d10003c0800000d113040307519078009045c05c0030000c0205191038003182d52400341500c0c040e4a11030b10170000700441d020350445180c00303a00400d240d0792490a0b14081184000a0340d01c07420151501e80d800092802501c41c20340141c4444002c04503aa82d903030104501680000303a0042046445502c400d000d0701c45c1c5010380013034001a150b440c1c481d81401c189900e0440503500010140c240d021007000442e80128000e819070b1b4055401041011004002c02c010340304030350b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 356026501 1250 356025251 356025253
    0x30d030903110d0305180d080106050d0b12010209040c020a0b060d08130834050909030d09080a03183813020f030705090f1308070c0e06011e12020c 65
    0x100c0000d0f15a419800907100e805001070300c0384d101134820b80c817035070742d449004049000c00c2561005009813401800501070300540c016021a0140e070b2100450441c4d026250b2824040e900070800e110640f40c030f40210305100080e880241441d10460311025040840034140c01d00448400c00108103101c110001c40b030f044038444a407c440c690340c0d0322105988500340d004108490a90010744207190590a095203042c9110755012034060b8106820000c001c00083c0c4441040e10040160094481e1a801404040d6004400b0a600c40440d114041e060341c0d01c07680038508034106000701c240000c98440d016243d04513603801c210394010401c184a42807090000900d0b10500310002041240201c040c3c0f041c1047d407081d10b1080d0118064018155121040d0140e150301811724800500c880b00b03610580d6501c40c8800c080e2411400710350700c0f009082d40c051a0140d41307507081c140f0148282800710990a410000070b20307080364030300d81c000240960205028511000c005107400c04018410181d0180d4044214ac03070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 356027751 1250 356026501 356026513
    0x50a09021f0c120206010602060606040b0d05070e120c0a050316030602070201020a021f090608010506370c0605010803030c070f050a051002120f01060f11011404080c0f0a02030d03090311 82
    0x910f001c0e50310b03a42440b0f294010f1140c000011941d08152050f1000c4441058035142020800458a0041c1c10014143c100f0012010282c01180c0e981140314031071408540080c0c0b20718031800040c031141c641d654200d140281d00110890030018402940030302100e400290058030380701c0c1c41c40100d08101e0340200203544580c11006078007000c81d02d6402244410155160b42003040e40d145c3d400d0381ca140091040c16070150060240c07141c40b0f0001e0303003150700710303110b5200400032180285c4801c403083c10040c0c071003c0094501e4148004102052060501502c0f00000550840c904504815007910400c030004060960b00342c0d0080410004110403040c03c0d0323104007521255203454003120001e42004817200c003003074050804500b540700d0900c0308605032190ba641c0e9030388031001d0250548026410580307040359076589000034402c4161640c003d0780142d220b4440307c0d85e1103900c85d03852481c00d0741c1e1800910154001c50b84100042c0c0d4001000f094000c03143c04d0205000d001400c059800e044001c00110150041c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 356029001 1250 356027751 356027783
    0xf03090f031707030e070513020f0406031e0203060d1113060905060406060c053708040306060603020a200102070807110a0806071d0d021206010306050a09021f0c 71
    0x3182c0000702e02c9100214442c0260b64108086042c1e032600c40901c40241c026060502c0a407c244001c00c3c45400c03030600151400121105440095010b5409440069640c54003125641400d11000408885801040d4150b040040004181d05600f8000500e894030300708004105031910f004041680c0e044040030040c0d00d544140850241a0444040d40b0641c9481c40c0410800d018004907001107410400503c218801d090002c1c1074040b80701e820041c0341010010301100941802c10001840e0321480004d6251859031074100c01f0380e850341d000300c414940140083e0b6501540300e511800002c80040c0c03401d61581c00c5801c428024860f0b500050501300000441c10140481c2034490b800d2080b00765101e10246540e611003980702e540c265003110004900026580300265514403940f000c00000300386118007902a800a440324510985d00807007500a10300401c184805882104c1e4082240c03041480f03848043c2e0700050000c1c110b001502c0b80070086184580744c40e8460341c260664264044840040c0c0040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 356030251 1250 356029001 356029007
    0x20f03030705060a060510090b16020a06052d030a09060b0414010519080607050309071805040b24011101020403080f18100801050108060310020a031401080106060806010f03090f03 79
    0x1044803a01a140d0070480b0006490a101a0301e0854a41c0c0750380e0040c0d052709240301c642c1035030f00003000c00e07140c04072041038900503a5800c8490002002c0c9925100e584108840002c400ca1108150034119408403012100841500c903007141c4d40b08802c01000615141103103041d100074002c0341c85440c2c1152402e0018070003a024a4549416154200c07040d800c0c4118070002d02046240c0d40c0a8429150001d1002c40c403518001e2021b56000682300003603070442a251464101c1d0407c0c4107554a04180c6c880061105000700c2e1060346030804c10000d50010602d00482c0c3d48524054818032040c10040c0401c4000490507080d81502d01442e03009603a55a075503907041c03142c1195000302c10440942544044400101c0c038002d03020f05496003142d10f4015180e803030600151000030000b46244c2d0580110f19410400840c184001c0c40621483e031000240e005404c23001d100c0b0850142c10800b046da242c824144080c0350018150780c2c3c040700900e0b000c0d04140e590340c011006000c44d070034028400c1c0c00c220030460426030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 356031501 1250 356030251 356030263
    0x2150903041a0a1407060608030a05030a1a01270e0702070614090f041a0d0302030a02011109030703060b010207031a2e030830071403040c060309020f03030705 70
    0x30b0410aa594002988055600c0c1c5200c2c14040320046264080c8400102c4400c0c0d0203031003118040c0d000000c941c1da66030f07202800d5901a01582001071000400c0150b0304403188200d80403040078481000a800f1808006080e0440540c2d184145c0c0d4103884138030820700f075000920400760844100c0c1d12900d0502c020081d40d200d080f03009082c0400c0c24428000f002542100a5542c500300c0180087c82a000319070030b0000030704040c203035a8030001c91014031801d252948880310700350714440c1d401980e5a62a02c00700070300310380914550502d140d104200000d0706580020f551000e407a009440082d54000482c0181d01e46070555000629a100e4060000c3e4040750391403420b41304000c480d0380345a41101419105070900302c00140851200b21140c4180003251801000d00f1020062044c01055401c004001000880b81d0b80c142181d2070300741c5c03010012402e6001c0350b2040008074441d0310a003182402d664440d0544200e001d5142050790701e1401d842950f4074a0366441c0300300ba002c0c1c15259034030064105039032128 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 356032751 1250 356031501 356031509
    0x4061805151e09030703120f0510090c0c03080a0e01060510030203010603050117030a1d060c06100510051e0702040c020f011a03191401150303170f0601050a0215090304 74
    0x40e0072801e0402c1900d40014580c42010b08801651400c9415035051311250400410462295690101558a155580f145a0142c92144444c03605585000d1800d019202e480b40c80303104100c500d40a24001a0704002c0d038580003580c070840454094080021035004120b264002e81d440400b07080514030702d5815500550684490b13503001e10260303884841880b052a22811a40050340c02041600c010038400d0701207402d08206031030034806200904000411540200c3c24031100358001105020328414131414041c001d001c1514500041c11390404041c1507400343e04071800480742c000c007823040ca0010700000c0702c4900e42c0c000c0080102c0b070202c0400070340e01d180103420244c9542c130b001040964420040103e08015400400400f05980c4072042280c0d4800d0114045901da800034406200701c440a02403840c0310b2070992400c09200b841c40c1002444403113401640e1080000080c2880030404000040076801030b802c0c00d0590b0380e4041880c040349400c9041e0046213103e030502d02800803003440400240211 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 356034001 1250 356032751 356032771
    0x130f0b090105091603020904140714040e210a02010207020301050c070b1f1a0409020d020909100f03030509061603030b100201020c30040b1c140406180515 68
    0x40e65903180381070313840701010354160a000154a042005142010f040703680148104a90000a016586454580041508180003080000c19121401d052a104c2c444000241000401010041442d1081d10704140740d500b400c0b03d100080c003125814000d4040f500103d60260081055141020320941140c1086c401112500301d8800418094480409a50a078045c0840c0b01000b45260980c3c91551035100903401002c0041408009001e1030648050101103105200160b80c1300994420010700c018020000e0300012014203007441080d0881c00c201050700e5140c2040740c2d43c0c032601e20008440c1d0142c5400c5080d01020031600e002050b40c503070001000d072001903651945000d1142001c2c0d09034000c048411400d40e1100034444021f5001800c00c29014251170004941c0f001c4203003d1031450743c0a40c103c1c0070352041c00a043c05203d000302088402d60302c041d42c0c0401001e22040b42d50a001a0094006442076458034180b031209400e054040301145c3d88a000c035910903844160303007080b481c0c0c1262103a1034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 356035251 1250 356034001 356034011
    0x30709030b07030e0d03020c0a1a0a060501050f160303021c0e0c0402071e0305040305030d0509060114090714040b0c0f010e030a1b0c0f080a120f0e010503130f0b0901 73
    0x100d011340200d40d20f05241602800340d0034440c0350200d00031b421491410300184103000c0000003149400d042802d2554020210030b1041c03401030440760585070703550300042c1005420011040040102c1e001c0c0c0b4148100c48588070104101414101c01a0003404484880c400d91003031001d14124465200703080c080e00080035240c40e2011581004102e0080020203004800b0000f4140100300000d90862440c3c0d101e030411a08240d05da4859901c1d680095040e42c103111b80d52014810444020040d160051503034000914685454001203803180700050103050034007100125407203c10020100361360282000c10345281d00c90303120041f003550718680c640c1080034551a10781d0880b65000c01100300c0b80766200c251129000700b0001c403103d201000c038041c001d030784103c03165201181c03076081a61458010810b4100070320710015103062000f18507198040c642c05001e001c07403840810507001004444400002d081c89612a036a60181403038408402c90001c0c45404182e801204111181c04064040c24111008010b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 356036501 1250 356035251 356035261
    0xf11042315010507060b04180b01080721140c060c010213090603020f010f0e030a03080117151602010e060405032503020303010909030507120e010f030605090a0c0212030709030b 78
    0xa031206074607105070015a041116002103181a0440c00c004100904005120000ba00440c05640911803048450304c4085d0010011600204540000382c44a450040010703050846585910008030400400f64000e4100d041c114540c1408401802100900640c1d9a20b41040203c0c0c000e50204040402070103040c10f01085000c06442403200307595000d4501360303d102d0000015a1140c04880a00e01085000207400030152402d02c0059061403091700d6421440d41001c1007440d83d00c145040503210340c1e0204e0040e0300044001408540c120030460034600070001c031900101e0141c03140d85090b861600c541d100740420450000020140c841d4101c0e40e030030f04003080880c1c0038070200000401600592051006004000c04c42d40008980c0d031103400e03c3c52130f01c120b50755604000d860702c8910f0030105807810020a02545c20645c44120005035241c00c0101d1801c0800150103070002501c00348040c1d170788600703031004640200301101244888120b03040d1207103811a0018614012408110344615604001c54 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 356037751 1250 356036501 356036521
    0x160602010207050d080c040306060b030402010f0c020d020114090d05075010020c03010f0209090f0703020c150a06050603130201141308060f0615070f110423 69
    0x3a80640e03ca005008401d0046034101d03003200d0068400215042c0c01c000c000006640d07482460014071401080e02d442e860302e0f00001d021031400000c00c109000c02c48004800603074a010300d0104581d1b0900f41081d018440d1442610140541c0c000503400c5550300b0040001d001002603044110342004918a80d001d1040019001407084d640d28083d07510720989a0042d9030004408214240305c1182480518050507c005080c01403050079080150304000710181040c01d0a00554600c046640425440c1a03500d0020580d44c1302c0040240f441c1020306004506481d10980480c0c040b10300711021a43d901c4200700e00404444c0302561607040551070030b44001060304142e802d582c424410f0200040200402d078005540409010039640160737502040300440d140b0040018802130003038000100603910301ba990803910650064002d43c13140d81c0e229004106d008104080300e5000b580480c0c92171000949180400c1e02d45444560301342c0c0b141c20103000c0d2101c2c001e075032241c6418a9039a14000040d4072499211 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 356039001 1250 356037751 356037757
    0x1204090c023f04060e0102010c110d050705010207050a1b061404140a03051f0b090c0304030c0528120e0a0909021203042705071e030b0307081606020102 67
    0x9491019541c080c0c4080d840c22000e8025103010b1070b07a40c11640040444100350036540a500f0801c0469199940b1000d1964244501c82c1110003d0420100070700880f01d0740d569516018044908100001458108100b0300303406803090680c3c0002115030780b19841c075100d210740d00c0c03017505c034481614030000006015101d040d03810b43c2051004050307480c080c01c4c00c41c005400454034400c3c0c0e40000280f5000000a0000c00c807401d075030703511210742c1d51103603113040650001c1c1d0344030b4602144252145818403100b0079120b030860750042c1c1c4c14140700480f881d4070f1402e2814607800c41c600c18444054040450030f0100080c016000384da200e003080b0100e10204007020b4451544a54182c2d4003c1100c40f401c0c042d0810940c04800d100b40000c00c0d054100c041550182d00c0d42c0d010340c0000d132034282802800351046602104625240005004c140031a14020000501c580403074425114015082100c628209000340c2c0310f010317082c0380a81170742d41040d01c801d0020b40d200d5004503941248544014005191403061081d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 356040251 1250 356039001 356039023
    0x509150411011b0b0702010209120714060a0903060c0903031b17090310050c071704140f0a080d020d020d17040219050904240501180906020c1204090c02 67
    0x101d4000e03035180c0004492290300000a200c0c10181d040f0603401044c5408500b07403140c81c00754000759032209201c1c140140c2c54035081022030240d000050034460035074100c07000101e160054402030b0b103031807400760300700c4040c3c22035400a00542d00c0c0134944800305074051111010780f80607403183c00c1000c1d8200c6800e81603410099015014010900001c2c03143d000307400c01400414001000c4401400102e90f40c9000c03070740296940d5420501c0002c1450401411100e00724031541008441400c00380741031454444400c084444074031a550748800010707280ea0300c0100b1005424070701c08840c2c1481074147c1c080c0da5450f880203020003510411000f0f800035031040320704e2140020b02e004000745984940c1c0c24040070307010780820381e8041c404096000c00c241d102c60003000d1043e8000c180404103440154003002c001100140d161080c2070070320005201d40400c601d0000203652f001480018406030600745440240211300c01c1415900078144540303406400313400a041619141d62040000130040501a1f0740ea07c11202 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 356041501 1250 356040251 356040263
    0x605010912120e0a08010b0f0105030709060e0310090609020114030613050402042003011a030f04081b031b0c0306040f0b1810020304060c140d020a020a1505091504 72
    0x44110000e040038081c04440c50850800c0007060003d40002414940c1c0740d04501000d039034032100c60303200307203008d10440d2107403403081c00d0807480c50411000080c00e01c00c2c60300444052103407000d845512500c0401104188801c4074a04010407025890240090300484400ba400540d5601d41203241241000889018200c001c000d8583e40d403d1040d600042c060040082e41d01940e11000c2c00c900904d05c0b0104041103110102a96032581806404100c03408051101c0d18807210030b00c10407086d00c1107581203581064000381001d4a5146a82d02c2040e0340c80c030358902175400d010105101d458a80807840c00c980c0300380140c054504880044c01419907940080390007814600800c049440400e904200941c0c12013040c040e481204410901e98030700c0d150060b101d42c20351550003c100400c4c082d451040180702001484c06d6007582068818480c0303170313000d80d024015031554001030042c0054020020000c110f0340c0700b404401a00e541e402020700520b02143c0c9201c060159210040c02448100105485a98426 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 356042751 1250 356041501 356041529
    0x120c1a06011d090a11090303040321020109030801121b0e060109080c030d0c1502210a0903020706031d19030206010b04210204060306090f0c0f0305060a02280302070606050109 77
    0x4007003002900c04440c00552917031301041040b0140d24248020006113026001041e41d0041c00c0702c26101d480c0c2054519411a403512a81e907000030342c020700541c111001c2c103070114680517035428440c40107201141150b88803600c3c034000044660720140c1d1141f00d100d00362070341004c1907603c501ca9515080080062a070540080001030700140c000c85407140c0c01401505d802c0080c1d4641c4203107400b2070b441400c1511210041c28081d0020b5000c03005110340c001c4e00c050381030001880507600a541c03043c00340120018152228640c4a0a01603041e40c840b41010041c11180154180c503102c2c800002c0e80a429001130151100124140c0041c1003140c04035180899032014600c1c0e0f46010441c40b4820000403030380705407100b00000201b05140280c000860050712a0340c4a45804d107080c00d1038511650251030706040102e42080899400728107a58800b0204202503524041c503a90300641e800c02850340b811150b5070440e404070540d03056029100c0148202c00822126403103500548006030301d4410041540446 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 356044001 1250 356042751 356042761
    0x307090207050304150c050d080109050a06080606220c080f15010203030406020d020f0301031b0509090a020f180f0115050301050d0f0609140c040f0209030a120c1a06011d09 76
    0x40103894017000442c0b0709010b03070200d030340e4070f0a00302101014404001422040144401c4d5098811590010880c4c0f40c2001080e2810b4a07040c2c42d010000e00161042e60071100e865000400041d80348502c41140c0020410344210060140000100b504d06040c03030610b4000142850310308004584460105800440c110f548a0b80e031030303000e540055040940c4a400340b0032464104034600256002e54454480300d4003040d029540300710420040d512041c410071488051150149010460302501601900d10000c1a600f80010615864040031804408200d4808104204680903602e50607109000c02c000719404a403401120a4002070041c0c0e40e00551007646400006d148107012042c0c035204000c00b0075240403d403141408180042a0101541c014a8055540b49030610403050140c0103040c0842c103011150010030781c0c03242a1400184074244016110708214001d0075038681441c2d00010f8081e038030000d00784941c0104070544590b808500024992840140510740004540e04040c045c00240d03a54 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 356045251 1250 356044001 356044019
    0x603060a030b09120a03060311030c060a1115012c06031207030201141603060e010b070b09030f16060b010804030807030b1311031b430308060307090207050304 70
    0x20340844640d10466226480ca1301e000d001038908151240c0f0b00061503407440c24060056000e2060b541d200340c002e400f048596544200c00c1d94074a0810745459a018040d55235940d1800300d00b13088084e20b06a803400005044a245240400b4515190408900105180c01c041070030940548425078507030808194894265081d0000e000b07400d00038070004c110340c004100400c00303002e0241c0e240c980b4440e1440c05040c5098146c000c8100400101d0100801c662502c04140c078107004e00380c00100039015807800300d11200310410644181c01c01d840e03400d40d55440590701c2c000322554004011501c040c1000200c030201c1d80903030786551241d03030551907420b6950384003181200204660030900303600c002042c030a06001003840c810042c1c0c000c0440c0c10640e51f4107009901c2c40c1154610900008000c0b030800c0001003c0c400c030688011441c5054078000d4000c00c0301c2142250448844015603100c9164140180505511030b01d05400f4050507000e4030f003a5512010301c4008d070310070203030003816a9104100030092040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 356046501 1250 356045251 356045273
    0x1609150801120f0b07020c0301052410030209060409020c12070203250f030305040812071709010917010203060405060301020a0219021f0f0f0306060f0c0c03020402030a02070308060603060a03 84
    0x4425100c10302510410307601c4132031590040c0d030707031100617440701c070044105007003d1060603040782003080c034100c0700900e107a400701034105170031000c50142005440344c0c0306141c081d8041d40e0301d2542c020300c0703507481c0d0ba21000104025001084c2c84a014883c4081c496842e890b407800b16030560360080d0280103451008141105081520b000f5000442d6074a00c000400010030f07031008015502c00e41e2125503840c070306400d542c81d25001e0b5281c15003902c1c0070003490b40000e00e030308042e0540040350310300075031143d069500681d0b00b240160302458120700046001c644d06481940214810541254100406e071242c1003414200d001d40708007880542e01c42c006030780040254580d11100303648001c00016510507040190441203904028800c0402c402100d1072030010341089050341512101e180402603a46850b10060506c0c01031440c5a0a10104038016400d022204041001558014105540e00e06283d21134000952051009400103030035840030810a1601c0b5040301d01034440181101001c034110749031184212 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 356047751 1250 356046501 356046503
    0x1409061b07200f040204090e010b12060105101215090c0905060412020307050d0302060405190308010902090d0516051c0c030809060c010905011505010305040312050603070509160915080112 83
    0x783c001e034602043c40d81d50303000901c040c00107004080b500e811113400381801d4a1043d2419841440042181e4940160014590303045800840309180814500390701654003017400b6602c489601e0801000b00070000e0024041c104a4444803400c00c10010800800c80d03c0d01560700456a0045e030402c001c100c0f4004001c006545a8002029601644e83c1c602c000742009100450840c0540c000104110034028244248004401240d01070443c104883d6801010b030241405491a41e6501140811140d00d9030440c0300c00c0030754040200c40241e40060440a03448010348602ca1181d480d007800d9101400302a20340c1014546e0006078000ca55003560740f02002c2d81c018081883c2c02c10000e00500b02103031400d00076010903900031000000c8040c01f00d07006c142c4862054104c641403504040c1030000080d4400c10030200d0091915001585498540000303060440b247c5c0016400b00c00003007403201c1c0c000d84030329921001036a5240c0065542da01c2030b500c1c0d803004400314074001040c0740000421082e000800f49503101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 356049001 1250 356047751 356047759
    0xb01060f0e01200a06060302090609040b0a0c030924050a021c020c0102280e011707030e121c0e0106150e1c06020702092a0903011409061b0720 63
    0x5224016107442c40e06407540310985d40ca81c0c40301410410740c1020b00e52583c0000c425035002e181c610381503d03030580040c0c0141c00102c079103507160710180869210f0351107103c0c4540d10440c020b0030300c0285401c401000d404040c40c002e0040c9080b0120306000c17102e10803141201e5003641c0a140220404661a000390070052002581c0e5408110380030000403a0060780c0d410146056041006520040f0002c03d0603c02008050621540c3c0c040f40c84580142e0540c1980811b89140215100760100354a42c01c3c07100c0100511918900401d0301144200e0100e00c0f011144c48004040100410f845842800e950700d511820004080001108032441c0c0b00d01c524a103000700c043c00200d81c000b0a0100804030800c86103003070343c240da4089082021403510080403038100c000002c944452028090746c5110301401e22800d145013443c0082c40700c03480d480039000550070f0721070507400c2c1585140a5030040d8517013404840610140007080d400400300d40d20780e402c0e41d2038103803c0200c10003156600c0c1d50031884284c240c9001540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 356050251 1250 356049001 356049047
    0x501090c2f0d050408060f060d020609040e010e0c041410031b03050a0f03020c040e060703020a020109050f1e012d020d15050112050c0307180e130b01060f0e01 70
    0x741807030030070075a8030760109996103e544070302c0e013107030141401c40107081d40d200851000c0c18810503540c0c25902d501501e1701129000d0f41c034000000000c00030001c160041205501302100e62088410100da1142c120a0644c0c05004a85513441c8001d41c0e514211600c101d80e6a54040038404140902c40c0c1c3d0308a0702415003015240c1e0f44a8541c689020109103040f12010310000194041503030503c02d206e5109420383e0148200d00791032140b241c0310b50006000400b095404603405c2d0030240300750406941140c10405596103075140b40300c5c403500d07007400546601c04648500011203980078148035016225190800151a01c50340b06018079000e4104241c0b040c03851b0f001d00c1050354500c403d02c05c000404083c1e049040c25646802e002511203012a5000b08804e0701e84030410544000000859612a802d850100800e0100c1d05012058408540000da462202c1008008121144030000d000c02809000114440d031703a80c50080b10010149500c000004441c030184215035401803000c6d089085600e04a061 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 356051501 1250 356050251 356050337
    0x170307150c0c080706060f08190809040f18020102060606120708060127080111070218130c030803071b121107150306030c0503060106020a0f05030f0d020702040501090c 74
    0x300380c2c00040c405d64880d0ba03192020030136400142041802404101c025265860032130351000703d1403124035000340c00c1000010343c1c8090782e9510391000c49079806514040110541c045078080a0140e0004104d02500c83d00010404038507106003601d032044c110000707503543e44e61104012290b40d0740c06002a81406400321089e8201301c0761200b4146c8444101010007000d07440d0411090175603148145c0319059200c10846500562580b2801106030b590041500c00d0b25100c0000c83d20070341e02040000340205000304000f10802c90400029409000c0d01c0e507491105030f4950031003141c01c48103d68018041601075680013002805404440814840d01007030302c60091351a1041c1401101001d055400680d541c0018401c0164819a000141c032003030740242815070400101a642c0d03040540301403da008145061801c04c0740810844d0600e1038540720998960310140d0b0840e010307410040d4102d00c524140000461003000500c1080c0300e1028556441041000c45644840210407030001000c4540b07480c20414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 356052751 1250 356051501 356051513
    0x52419020715030c090b09030d030515210705040b0f011d091008071703040b0f090612190c021b040621031e0e101206060504170307150c0c 61
    0x241c0e1440481d180030030b43c8024607800078403030170b0150414200e05000740060009070b1000a00b140e030100e0541000200e607190480b480c0348188071120340613807203d00341114007440052805107100d40e82230b20b03044500154480d010403040e01c05239054503411280d403c20340d5a0b990306c5807400b88242d066265128624550100210780c1c03581040703440d000c640c000580c04222581080200d2802008a20140048501c000000a480e40308502c01e11203040804294083d600801c801102c009820041c10569620301c101c44200b0008012142d4029044401d0740000148104e802500d19504040c0e019081c0e00f0030081e000030641000850050300981d40d60404244004000303201d00c95200004505000b0024074a070041c04410720601034920103841c0c0400101441e001102c0d4801004111682d6102c41d03103a00f0200c031510990300c2d101c400d643c102503001903a560004020415105003250700d4403034010142003d640c0c0c0c86400d07802806000800000095450942c1c410f24980d1801c4c5012219011142c40e51 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 356054001 1250 356052751 356052779
    0x30403052106030d032d1b0309080304171209010b0103051509060618030f030c061332010f0501080f030a0503060420180102060a0c0203030a0c02030d11040524190207 73
    0x8051180da5a0004007200508047da46504039a4a010300000c40ca50703841c841c01d8000074000a180d014081001c2442e40e60a2081c0c41160900d034401d04258501103c0e114060545000b285000c24a00b01c0071171058280742617400203040c0e028101c0b1000361910020f2240c590b02880e020012401d590401000540d02840440a200c1080f4019500d541c00b4250444c10428045c0c1951414410505000300003100503848807101c2e4070781250b4580e9084681c28455058941e100f1084103035180110004640c000e41d80068181ca02100807a8a064000d05d84665a442100c500b480411400c1c0005092490304c0c1e00000c02004540d66000110f1296108240c2c4640042c0c03c5000c2d02c0e80401000c08240d42e0402c001603100849036014000d41c03000040281d10b0384000341c15417250540f81e45801c01c0c0e00c0d008004950481387c800310100942a00740a030b62190340c120f030043c1845207440300c03c00c0303450001c00703001082201d02e140d18a5190100d051010122842d80302503100035800b411800054201d2a00d141d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 356055251 1250 356054001 356054081
    0x160815100e090106050903061801020d020301030b040302101a0d020a030203010204081e010501030b01050402131a090117060a0b07260304060b03071505090301060b030403052106030d03 81
    0x1440d5040c1500c03104000c03600b80160040e50400ca001d0140340b1041d40e0000754945c10110b0300e00c00e00540780701400740b540607102d0340510404850000cc00001005004034542e1311a0b402a825103080d8000310b0b00c5202178079903090039061303c80c6400030300c05000e00d44100c2244000784003e143d8201c4540d03a038046801e81e0019809604150049101070f451005200c4440141d00070141c020441581980d50b03c0010f480103010b0303680240e43c00701d924001010703c1c02142c0054042280c070b004031402ca1185840350b580c0140c0b8494002641a600c0030b5020481d601c00314007a040090440c401d5508000c103010717050b0090242541e8501103602e80c071103005000b00d08408103a80d00981103503240382504190090782d01c007000481c0258006071342001924049400380b40c49480600d00681e03901101000280541400d8211216850000045c0020550030600030114a41d10000342c42e41c0c0f801c81050303080420f6040300d401c1d0b0503030005800c89641600c264440e80d5090000b41000016049000703010b89a802c104030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 356056501 1250 356055251 356055257
    0x7060f06170a02060d0f090c0f080c09090a1e120903140c101404270b01080910020f0c031908090a0305070206030c040503060f040c0b0316081510 64
    0x4401c0c420084440c00981c28041400020700d00032840c1e50104055200309130444010907038400720310302c00d081c694001038015171b0041c0c1c440305010b8503040d10000500f124420910144148000c00d002c0b41480840c403481034030940050b010340b20280c0c403000c100c2005509489400c0300c08141d04000039414245400c484039855840c040060305511b0102d54200f4036400024469200356184c2c0da0740c0c5c1d2000405051107040d807504128a400c224104c00c140e0003107401681074000c400c0b0281d086075142825441e405042c06006003c80e80c021001910300840c00c0d20811403680100c80305000c2192550010110440d0402080745000322114109041da044203003030b8a403a4001c005000d8050368084602d41c2c0040c80341016019502032030364050510300c5042e5000740100f10200029102d0040c0c4000e58000301400390a0310503034640304442754003800040b02d00b120800c1804002040c40c039881c0381900c0c800d0038414900c40a200302c441c0305440e41075008100c03403004034882c404100191600c04d41c540c400141c40d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 356057751 1250 356056501 356056511
    0x11070f030906030608100c050c0d050706050609040b040b04020a0e07020609060901060501090512010e010c110d0302070f30030204230a0e07020109170d140f061507060f 74
    0x300d002018008590300103000c060800034248400103010401e9102c0c80710300140080d0702c1034180c100351003034001c003c184c41e814050f80f100600b070141c01100502607580b00706402c0001e6a951000c11019890640303028260307030f00030307400140001d444500c0c050300140010700c01101303259075007141c4078103840449035800140c2103a0140074a99404010003a00310410600030310040342030000007414501e8078856a40710b081c0014001c54030710000c2d4024481006000000d10140e01c00e0710002d01030200c100321038100303440361500c1541c00030b11a02c03d66080c40d52292881648200d2512050304044100c8048400c031901c0d491000010103000283c2c050900f0b003500e025803103500d00342d84e0b0340c0d40d035019110768154101600c501700c400d079640440ea90141c0c0c400440c01c41c102d8881540072030042c99940401401d40102502c60b55020400708080c1180540f014028400d0050981c1e88405030781c0300b0340d0145c03c01c0e01104045001c2e031812008458003e10150001c0341030000c1d940b81c01040c0c8406040c070810f626614 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 356059001 1250 356057751 356057753
    0x703082110050906031b0f120d030204050114040e0601050702030f0a0311150c070b0c1c0902040b190b0a020f01050f0a0b0603131e02061803060a090b01030809030111070f 75
    0x1001c07000e5000c1c100b20081c1800c050129000401a100c04006900c031f0307100070700006480d68074440d140d01c1c800d00450071910030480104018009610074058540420301402c400ca1581c00b030102118103480c00009005d441f03031105001903450741c20007001241d15000b204043c0592540030401610403500980c1c0e010b070394031101c5a4460400305110494004038190300e007009152800b1108885c2c031540d0141400d112647e6400421003180112000c880c100e0142000d12200c1034070f141c000b00b851034000c850030006030150804019030402c43c40c109045806100d48108064120038014040c010000d00554407c0c59004030324170b00b11340301200d150f56403d50280600109208901c03520103103410070356400385103040071101c030300007408220401001c0740a006c54583e401410460300346c2907194054860b64071a5207070300c61f0308030014039108068024810f00000800c402c1e010300441d5002c940003c1078002e1a4210340b03074494184d100540483c1c0640d00c0380c80307030242070000030000d0451500514800c00d04142d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 356060251 1250 356059001 356059009
    0x9050601050f0a0605030f070521010302040507030606020a060e010608011401090e0601030b15040b0603090d021203010f0308090d0c18060b0a0f1b0219080c0d0302070308211005 78
    0xb0707005502480380048140000d907040801c40c0d03080502043c000c11143d41d804005c550070322480310120200c480503c054450f0030204049a03059a1003190140b00326900d01108800b110214424800168400c0a0440102c0d40d41c0c2c0c0500010b96084001140c915101c00704da90075103208180c0210340c0c40c0044010014000380e03110b4001820b9100029148030b52451b12401e580340d0b40a0414440c44070401c00407801a0f41c0ca070b00885010402034009a00c0340750078a0856180c030f042c40c00ca24054000c20608261299040d81200d05a4060310341401c1d1581c1984c941450b65084070003c030f50044440e00c124000704903da07280320010140d4800e45402c1410708070180081d80c045610002c84900700340301141d102500300a891110040d2032a0107041510423620f02c02089240c28006500469141510080704650350900c0c3c041d0703513120b81242d440f036060780280311704042c0b050760140060b08180300500020300404014801000300009041d5500b01400000809500903202e030002c621040c1010405420 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 356061501 1250 356060251 356060269
    0x7050709060501201501170c01030912030e010e030f130f0b0315061b060105243106050315090f04110607140105040507050a0b0f0304030c060905060105 67
    0x411030105000d030515182c0040d007210740c1c0c100c1c4415810001201e6944c1d9000400084401e40d190907803101455130745983d00e4015250140300040c070390081034120745455000b4020101c2c000d40c8940805a4500c203107400f10010560b200c1c50a41d195210240142e441d8410400751035061002a8140c0d50394000e844000006c00036540000d41c00030601d9410055002c0c17281c1600d901107410364203d186c0c41080d074005441d910504030144c07110290522900e48041000550b541aa030301562402246840c00080d5107246002c0518070010701c40030000310b0503a210141106c0211550307603140600d819001603e91852428940100000550210400c5104c660b08450030003068030941d0107040c20b0400760069903c40d000140003030241504070a01c80d511f9225502101c1249400004045c610b0039007031250350117003805841c01e482520680c040420b242c075040d0380070b00466006241a915151210244c10180d03040140706900344054490440f000c15000d00a41c40d041c0d00c140041c00c03441d810b0504000101c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 356062751 1250 356061501 356061509
    0xd0b0a05011e061808030d0f0b0102070810020c0f030f030703051510140f0d060906080102250c36180201031d1c08060f3d0203070507 59
    0x1412502221840c0c0c50409220401c1e42c83c2c0340340041004190345910a0842000d81c0035013994880051500f00c609059131018402c1100400c0511988555500499840b07581340100031864000f00c1d00440207407001d03401000f2101c04a421760b520b0610207038446041d500000d5200c812030800004020140d0342c0751090325070103240c00e00c1e04610309002c0c2d804a040c502c115106031080c09000b981002280314001d099440b09800c5000c82070381c0d0624050000080c0856120701c416660502102003410001030090300c400c94001070320381042180300b540d44060161401401c1d20518004a00402c142a0143c003000084032101c0b1b120000e00c840f031004c0c02c10605a01c1051b0106440c145015400070540d580c500965902464007180001d282d40d4241c160100703442101c2c4281c4540142d180c601c0044029001c134402e0303140c1341c80d481da94504061024810303500160540c81000c40481c0c0340511100300401d001c15440380c07120707506540608072130448040c0c00c0102e800507074404146582003007800c00c0060081c1c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 356064001 1250 356062751 356062769
    0x1207050106081606050a12020a090e0c0a0e0d08160818100207090e030c01020a031b17041203090b0f011e080712020123040f170a08090a050d0b0a0501 66
    0x2e0140c010b12031202a94040c4d0000c0010018a83c1d0341c06201e414900c001e20f816420841d0b031042d03c1140509410524425004460305040004800d8844031080d14480c012945a8081c54901c1d00100a40000c0031401154013400600003003c3c8c88580091840c1181e100b4500759030b0b1820445541c810459040c10301512a40040c1e0880702c9043d808203a06080710521075000c11804483e201184c154015903006110350361010481890840d81508070303040c8000341490302d501001c015003080715040d15007400704040c0c500c000081000075481d007440040007002031400050b0316000b661513610072901990255440700009005000300c101c0010b00d511540000180c4640c514680b03c401900c0300414451a039071070b4040c2c1d02001c20369004001e03030020781c1c000b0145117411502044d041d03680c9402c117001c1e0b0388074400c040802054801c948945c80104059040003094031903882d0ba12008aa48180300300d607005a8a13000025094880e01000f02d54103200e6504440d41e4038282904000b1a04164003c01c11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 356065251 1250 356064001 356064013
    0xc0908100519090213020d0b090405070e0106020a030e010e0d0b09060105010e012a0f0f03030608060109020414090403030b041104080d08060d14210d060b0c2508120705010608 77
    0x1a81e40440c1841c101000c81005030307c5445103520135004144a81c04540c000a6080c1000300b009400705005003a50307a494040741c52a600c0b901d04994031889800b001b00490399400d511009503000d07010300707400c6030001011840f8082c169990260a400103aa2005c81640401c006001d55070700040e01401440080c40c0c22650b03d0100d40748000346440c07444c18441d001c05414411000d000341e0403d4100f0b2030317800c07404441d020006441e0003001400640304030760050240d500049107000207402240d044614410f48822803aa201040110341c22002d0001c600340b640c0c6106000707250325103003d81c001c0e00011007140c603156860460200c0c104040c4c2102c540070444004100b000b180e803241243c038100383d0071030403050f41040c044d00b500d807034404c0d100b4030041950300d0712000a4030f400f035034802081580b006041c1403010755a518074440c2c0f240600d00704210280c00070121075070038522501c4a4408a0310100c803012a081e07139910407070304064030a01170292611001903540c00b444001d004010090503088000d03c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 356066501 1250 356065251 356065253
    0x5210c070519170c0306070c1103030307120f1509020d050a2d0b061614060108190302010908040f1a040308030c0313060624090e04060c090810051909 66
    0x42522514040d4006000c1001803416a10404014060801401804540040c100640040d105600a030809c0701d0182c0d02c1440c5040c2c906000c020f8a0143c156911401c803112210269040901001c1a040e2151030751182e000178100d40c01703190710300100900c01c0010b903a403c8072a01001501e01c02006d203946182403085032400c0040c008101280810790714102c0d050550600c034a44003408404410030750029001c54800c18410118100502ca41e1041490f45102d45045c81c50646034a402d10030070005811400c00b91540040485e640c0daa407a119200003d90640c4540d901c0d010b50300b05401c42c400000425405101120403181031031415400c3c42c00d4103042c42d103580d460012510000385800303890b80000c0701044400c24014251140207501483c240035240c0c4400c001500004404001c805c0490807000c2100c02c54058440c18041d210072a041d80d50942d2396444100107803c000d100241001440b4400040400040c446e401840c11001c60100e1282020345074105851030482c18419414500800c0034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 356067751 1250 356066501 356066539
    0x14040b0d15030609210e1807090f0e0901110421030306050405090c190e16020a0b010803070c06030507080406050603010204090f0203101d0403050705210c0705 70
    0xa91000d00c000022071401e2404111a4401c031071503200600c1c150822113074408210703007207003800b2110780c0c00340304144080300e010303400c561106501c1a080c0c2c00840050340c1c85000c1c28104062988071605042403440035941c1d078844081b0ba4611b5000500780d1076000700f444040d04080c01686961a000c40070300d41450f007414414a4000e52403001120f0b40142301c80180c0230107001c4e4111200404004008101034a029010191a030400000042c8030b14071515408c40d0380501c8a030010140e500300c034003901c015518188402e4204402004500c00d51084200110000d030b80b111005018211300005552554080e03d400c5501c0200c03500100305050500c0104111140d01098442d48640c2206020a55440311b0000c20300911032034210380051030408100f001c0d021300580095005240d43c218070704411781d580c3d42150b5030884c1207900800c0641c1000c00b04020902c544003500041c0d0013a4159400345802a003402c903145003c01d429600c240021503401c2c61450182f207410004c0201341e50020034101e04805807 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 356069001 1250 356067751 356067757
    0x100e040e0d120e0a0c0303051908010803040e0a0209093903161416021309050c060c0709090309030516060207060c050f25090b0102030a20060406050714040b 69
    0x90041d030b6180f074104103201c4104420140c5a4000307891042d242d450b41001022070388168485014965144801701c04103119001c0203040700c0798130018608050414043d10504c40f0081c0004214980a002410403a80c600550b6402100c40003104c43c0d00c41c45808076000c810707200f0220881011807804014507905200b034203ca41c045194020075901260344201503400652540d8180302c10100840c07091910300e1003503070390780c003103402181c5c0351107001030360340b0410207070b6522101c000c01c10b800140707039503e442c2821ba000e041c0402c90401034500e040e46038900b9504446040c1c500340d0006490b071404106000c0c09104c050b440001205440c1d080394240180a59209a103201e5103042003d0721404400f4030806000081c42400c414085e960044103002e51740140700741002000c030745507030b02803c001142c035550302c5810001181a000395052600e000416510340da45d140300d0704070400c400d81c1c040d42088030038070a951007140f044e0800501410100001800c00040000903a40840104410b1100051000035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 356070251 1250 356069001 356069027
    0x801080a020a06110f100c0e0f0d1101050f0d050f13020306010509070210051005040617210d0f0f1b120903140a1106060607020f090402040b100e040e0d 67
    0x411800e0580426000c0d02c0c1042005ca01c4e400f80c09102c080c014035440c25000f22083c0f542c1030f51002c0e0001d1982d03040002e500c00c1820010340c05044c0f0b1101c1c00024801407800140c1034014101241000d09400c512005076002080a8109943d1001040105440c510000f5002003031410180c0040c00154042583c8502c107000300d42c0300e0b045660004015a1007001040e800381484041800181041000700c160000140517883c461810010042004028401100c00d040c0e26840100111404003280d0500c010040868284410003000381c4050005280210b16816480d04000621201c0d802200001c440c3c6907008592100401c04084074104c1e44082071440c00e80c0001000502c0c00c200b0300c0c0941c1d80f0502c05004880380840490302c80b0b0038940282d62010603400c5401a03c0480d03889004001c028802e03c44000c0d4031140404184103281410407605274042c2c8050f0002a241136070100103014012404001d10006694500c4c0f145c0c24102405001c42261a07600100420440d000c400341000002d10030f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 356071501 1250 356070251 356070257
    0x603051308030f06043809090303160c080708130b09030706140c0d053a09060e010213052b0206070516230316152a030801080a020a06 59
    0x1140b013070b07580da40c401042110a0800c00450000684506280c0b280010360010302c24021100384585080ca0900c891107910258091889c49c0c1d40c6103049090880c200d12920200300304d41864000154074440101400303070050044980343d40c44040e00c415400c1685c0c2150f10400c000b07202c1c84015880c001040000d9400c18200070106905504440f4482d010340c1c1c44e25801d03885103500100206822000414501e034100e80c07095146c2d081c01d15111841c01d8400b1952a844112800040102c03901e07501021030148100c40200301011240a00c5003a82c0000f080240e03000c403080f03010400b40ca08840344901d40c045000d11000c19041c04146403100110300300019005a900042500c200001403007841c6440109041001049442d1204001e1028110b008c01c0810318072a00703e07802a140000341c02c44884551f11903d0040e509140e000319400242400d51824842400c3e4401c1a07030140c02e00c83c0018002c44012a02d290007942002403c0032410f0b8448501600900307860005601c4854510060341c20a003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 356072751 1250 356071501 356071531
    0x30f050c0303031915030b06100516030f0f022805160801020405031e0a08070c090c020c1c0b0601050d060b0d0e060708190c05070203030a020708010b0f03030414010e0d0804060305130803 82
    0x2527016121881020315103040d03405900300c04003c054210010b042d280c030341070f03441010701c00c7c1d08281a81e0341c20050480400c0c249403100c85540c814150320104c2600d6120f40d0070b4172525802c17110032020000d82a0440d0a2607500410309000c01d0404008003502c11280d00c5d1611349418000f80c2160703c5018245016091100009a040500070381c081130b00d0003801e154008100101d80d420009494030000507215200c0c115440748240402003d071501c12003646c1003200854541c031420300560b803a51090459405c0b85071500000034401003104e0191010803002c90010a40000025440c0e0810500801c1e20003400a00b2040c020010300003100602d41440750400069400540001034400d07000d2414001e40c944000500c01f40301c03642c013154890460381688001d02091001d04104414844d40002541d09640240420000456800459086a0f8041c141a510305401001185001a20440c25034021400040c04c104a0741d03d0b1107010740c440d4020382c1c908802100c59803582c80600c0054a41c82a1400e00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 356074001 1250 356072751 356072779
    0x190221090f0607140706090b190305061903080d0c0f080a0921030905010e0c0d030c060605030d08041103060c0d0203100b041508010e060a030f050c0303031915030b06 73
    0xc0001c4a95040c0c00c40303c51190340518640503942d031035050055400180b00a8000244c0c600d0388005d84202d850b802440d9290249c03469801c900410000b008607034400b80b503601e89050f03407402202c49405140200c05099583c601400e003401a501c01890541c2045039070022184c82a91011440e5085500c2d01000b144000d9181800c6c0402c52170381401c20110a041050040c0c06030f0980c1c0400281d6102c0c074028011141d8105202d81c564541c01c000030742010b4030104410000748241c00c03454000d0721035800002d1560b11100468905048039262102103011241804148198000701c1700c04d002c0c04030000c04207841c103e4094800f038081d18119035410390b008004241050001c60464000d4080c0302c07031aa440d5982c40507490454010214408040344101c0004a480c000781a0464815080a45200202071440d40e80e40302000c840e140a1711203000c0c800c001c02c0c0c03503901400210b004a029461f000c5144603180012000c03909a1620341c04036003081c404c1007001506007855250f1101c81118030030203040d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 356075251 1250 356074001 356074009
    0x5122d1507030e0114010501030f0e0601211a0402120c0102070e0c09131a0d02150c100228080f0c090121050103030305010b0301030c0302060702040b06190221090f 72
    0x840c2d032030f940b4294200781d8078031002d10303921481d54100c0300260313820311140c00058070b100110741c800c907606102d81e0400d030014042191001e01c58690040c41407841c0004184a413078860394034070800b401d02c14401145003400309514101496002c28854280070f003543c86e06070300000c2d54448052050000710a203000001c2c0440344040240c0c1d2155401402e41c1410008451000303004046100c1410488454001d0318620740c2820711050228036409000e4260b0800c100300b00d5025508680d1b0b141c9402e104420118a031a80310380007502000c8080f200d205929620b002c21302e04040303089a003000c01c1003035100800114030a45107501d07402079078020320f1550354114400100c0720081000340360315082050030b0001ca0401c00f154000c60480c4d003e035130100800e90300c403075100c07219100a11001d042181c0110060015180410091164510083c00050201c03072090101d40150410070300350603000c02c01c0380d4080406806004004902d11126441103104d4240404038102d405402c840c140104064041c5000c00d8071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 356076501 1250 356075251 356075261
    0x90609060c09082107060b04090f080c1027020f0d05030706050a0c020a030806180f150f010207090509070816081b06030406020306040605122d150703 66
    0x2400100621102101c654040c00e24031451091404a00c1074480c110820610007861204a00c41000d90901d80001620b61002409810b6101540315075186030040c00138000c4103100c5170075032081d03e456880d00d00100c1c15504050160905074061424010008659050b00c401072426482c0304090f0b204080701c038004104103488074107049030040c0801c00b0a01c14094008050150b90b44915420320081e52040703501e03001e035429144010b025130f1103100d8810000e03004a54507944900041c004540450101d0070400340120b00f510760802d000070b01d00a1081d08504801120750b0041e0581d0b640d00300c0d50220340008d640b0303003031803107000d0034540c1c1d510101c0c1c50f80409202640007049407804880143c181c814400751a00410300c65010548580d4030304c04200c00010340046104880240402d041d079075640c903600c020303610080c00c0341e40c8030756691f002094030b07a2040c0d040619981c0030001021150640b0301010364000481c00c109580c003924444c418514840025040c2c0c03284a030f4401c03441951144602a0702503c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 356077751 1250 356076501 356076503
    0x160c0909030503061e030f15060d0206092b03050715052e0315020901080702060105060a030f090f050f070902070f06091e2001030c0e01080c0906070803070e06030118090609 76
    0xc080e496459445003c00a08d418240ca0650032488540d142e040c2001758140b503001000303400c18014090040f051510f10302c5c030881181c0c0a007010305004000000403004020100c8100c003c2000443c00d0424000d41200e1900103921420040019003450401842840a2607024180001203540c0b4942c1010840201e90021a404960200c00c103030340c0120f07070029410000002d4000313448400090056031000545034100c4030050081403902c51041002c802030000c490101d400a1f0b1120342c00b000103119400c0c0809154001d4010b0403500d09209030550034400e407507104400352401413200740e01140c0b014044588c01c66002c140004c100010340380840c1800791800603003c0b4841e900080c2c9050020714420030803444200610241c0d1046400b0054044890381007112000907002c010204280d402221025044003401710700a06143c01500090318503440300400f15518100401400003081d04800818110702040b901c19046606044450310291100f86050401c01d403a21908800d02050768003120303003a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 356079001 1250 356077751 356077753
    0x70b0903030d060f0503012007020d0303060315050f010f050312030901061a070618030c06110d0905100e0307260d05090a0506061c080d020c0102160c0909030503061e03 74
    0x42544c03001240c80364411482001c3c065400c00c40b0341f0403180c901074a072400703549441e141a0308114540e000e214040150b40300c201c0038150343c0c00002c0080b41c4941c03020903c00d5465800441c0e01d1601350403a00d071600040c2d2064010300e401f24400e01007550082400e184400444100700c0c0c403075940746c8099014044950190382c03607000b800c0c014460748048000600c0594003c141c14007070642c01c0384c52401141d200320070240010b400f03105100c00061454118400070f1486500c01800d026034201103404403600c0003401c541d240c1c009030240900e03500c0d5010313124140300ba44000d103050803a03949444c1405055900780141030360005190160301d0328507006481c4014001c0b07208202030318000c00c4c5240d9070020070b03905071500d01c035050000d0820320b4041d0728001203401d1500c9410480f412641c42c69415000780c0e41c0c2c0c9518540a201000d000b8030240301800c80071039003000b03601c0f807502030303003800c001408880c0c0203e1481400c0012882c00b00750018100c941011040d2007030355000500341000c00040c01e04040c22645 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 356080251 1250 356079001 356079011
    0x102090a0b070303150e040b04380603030412080a020f0316111e01110f0d1e020a051b04021e03010f050a1202060c070806040c2402070b0903030d 64
    0x3070000352800b80540038841c0e1001c2025004188030012030600600c43d052005150310002030000b1400004503412602c01d03102c031140f090402c0504610365425042c110554003070200301c42842c0790103c1410740c0240055028604d400d00b003540d140aa8200d00d000a80f4890000904e408218400c224045000a01e00191b03030b140c00c00c0f5848428007108100042e240e10250b00d900c1034140c9829015040240912401c850f08418000015280b00d140943c05402c01c4c014503881610340754050040b10030000c4d0642c0d41100210250300c0c0340300182a201005005c42d4080b5507014001070b0f0018091a102c0007051305802e59010140000703000c1d11840c28404400300c0d615410403040340781c00000d94103a9454030300c2136460031344800c02d00c0651591340c46284000e00d60741c04031802500701074000309480b585c0d241c15a030030680c48000c0d00e03180c03480a550840700954601d400300160940030078140e1400c0c160902d041500130441034002d40d40e0405002e142615100000c44802d40e580802c103c03052901581c4050003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 356081501 1250 356080251 356080259
    0x307080604080a120218040b010e04020c0303070912120c0c031209060f030207020306060904080c1c030c0333232814031006120201090819030804050102090a 69
    0x460b54200029030800b2030343c1c26070b000b40c40c0022802580c4a40502e102000601901c07442044041d044c5100001c0c184031210700501d03c1030316640000c00030202800010342d44c80c14050740061500350141e02165000040703c021000090038800103607210150f919001a640020b03050000d921805a4001020320203024048000160451401d004985007500e44141050343c0100070740581c070411200a51503044000015aa840c10072040d40d00680503007420760031308105c0c981c454605070000c1403034000300304540c002c60000e5030315015098a05150785800d02602d08030984844616182c074007038564201402003c04882400781842c40c005080110b00c5000b0a100d18140e9240015480d01c800d00494610b402d400b03410b0720781814240b000303070550302440c0b8030792074449001d580d1040d41ca6402c1c1d05010f00510300c00044014090034011700150300710303001c3c103080b5440050045540d903400044030f40c000741d40d4514850b00d0709038184003064042c10203c1c483d681c0d618000b4024410900003d901018160000c9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 356082751 1250 356081501 356081513
    0x41203030c0f020610030b0a0608070b0d060f0b03011403100501140924190902040905071d0a2309010608071206080709020703030f09140106090b1c020307080604 71
    0x460a480c0399110350a50002c540c10890b110801100c074016000034603141080022001008107a00c1807130300038001070f1705031102e03011400c1034004d6011104915011549003001142c6208a8000700100c045000004c0c0c0f4000c0e19201900051056801f90300e0915803041441d103083c4039892030440e0b1131100308415030310b403802c504004200202503806144100000b030620f641c1c1c241c8080240002c915a4040303080f1003801c002c1c540d03030031440d141100594040c000480915500107040500f034000b43c0410203103089003000300003603040900700b1824100044103540341e03141c03888070500307540340301070500c1e94540e0070001c05000c84601c040d0075803c003a40c0d10000540f41e60203020140180d00590b99201e12012a86256007511143c1c010b03419580c011900401404030700d680208807040c070a0801150381e054040c41720040f506072840640310f803198110300740070140003031141901034844140300700002030511020a08070b58629070800071082a54160a080d580c003000810700070080031003110114a440d03d404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 356084001 1250 356082751 356082761
    0x10c020a180b090405071401050d0501030b06040b01170601030f0e060108010911030d0f0e041b080601030b10020c0904050c0909030901030c0309080a2a140d0c170f04120303 76
    0x310310a5842c1c100008064601000c040d40510341200045c50804d00742a0034900c03e8184502d00390502004106101c400c402134040d80f03009500800780032a503490300c00c06001c01c0e1581403007031a0402c010509034000300b180c1a600e1a400c0442803034001419603100e2000030040400c40c50001c801c0c81454000542440150806804e2a00c2402003511480d5018141030351041c2101c10b40b4080b90840302000400c6100d4420300c24040da004001186044288104894465015a8510001c2c05800401096580601401d00e143c0307800d0300d0070b804503401c5600007521032141e030f9042e81c41040c80001207403d1040030404100c500600619902c4e01d42080e04141756030b980700e400c965012038200098203213014000d1041e114021780060007a071410051a0080f11410010752070100c0c00369010328902401c00c60842c50300481407190400310303008040c600303000380b61440c00000b82040068484c11000003e000c0000203c03014805c5070713a1500c64102c4003402d019402aa080303414994840f44181c0141680750b041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 356085251 1250 356084001 356084039
    0x50d05030310090603080d0e1203010312080c0a021f020f0c061e070e0d03110607020d0305011a0a05070f060f230928020613030302060c130605030402010c020a 70
    0x3400b0100d40e162421000d0314058070019081800500c034103100040181c10900355040e07941c0c00d5668454500c0610302e8250400e820aa0b4002420000458045c1c0c008600c02c1c0c00410300d0380b85c1c600740041c0040007582c640d07944000d0b14a071194001841c91015094058448200201c510b040e260000310352019586c8400725013403e40312006100c411980200190360b140944820f680b1f0910406007103040c08030310508048120100042e0f00300231030a2050901c190340c01141c450703000e00800c8418010050581da41071304000021003d604600c0401000c5900712610001c03107007001920b8904c5800c00c4071884080400c0035007071030f00703004103800b8075030303080d80072450200c11201e0001d00022008140080c2290031500d1a455030700c040891034038480c4540600c0c0345c04011030407081c0c000006501042c0c0719002100c91282d60710790980c0c10b20806170180641640103440844107400c091030482ca085007441140b1070b400510000001180c25648a041d40459140d0090401d802082d600e00003202d206220b111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 356086501 1250 356085251 356085271
    0x20a09022809080a11060705010c022a0d24110301030c06031b0305060f040608010e0d08040b06010c03171305011b050d050604060e0f100b0301030206030a050702010204050d050303 79
    0x16084100030b004100c1c0c50150342c0440e00a00f0f03840420b5403200940070800b4a0198040b5080c0490b2000910074000c1c410403d0352940601a840003040c440d02c0000c42800405403400007201d006001c81d25444c11150307070070350810036508044e20f541c0d02084120050241c4010954285101003031941c0204000314100e0b0b1150308181c20444d0344400c110202e445007651003010010114003460654404d0f0001500950014440700000c4007079800642151401d901003650350b515030902c07802c0c80800b8041c60116002c4ca007403014440c0360030703611101080801446c007410301c150044c0b40020701d840350781c69607030309605003904059500380f688800c540a18066000c544035070904509090b40d070003401070003074501c4060712014200b42458450002604000f800b040c3c0040e5074400005014041d0500c144c02500b41541240311824007000a41107551690051010341004000410041e1102012030342d206001c03100001d41d6849007001240640700369409154450301c060084414000040002e600800e00c0741 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 356087751 1250 356086501 356086567
    0x6110f03150123090d0201090504140f0903130b070303021303050a05010c021b0f03190b010918020603040206031f06050406020c0d170c07050a090c020c030a050606010c020a0902 78
    0x51810443c0c00c41c421000703000e00074070211400713084c951403028006205040112034203880b170002c9411120092543c0c18440342e00400c2c040088420320006410000c1c4c100503519016901002180244c0c081c41201d0700f2030000644581418440c3e419919080008a9140744141e581d080450743c8202054098403254a010034980745180006101c000c418503160031f00100c1c880701c20410000c3ea10f0070514075018016000034980910700b030340107080c406100721080030f190750401204000b160002c2c02940e00d0221622000343c0075a81e0300c0c1c1a680d2040d03040f03500c1540c1e9901c1720000d000d2800c941040b003800c01e880f1803006c10042d4105014105503501c0d90308071400700c841c80302007185410000101810b101103085000402149601c01850ba0300c03201c104491000784d640c00824044000c95200c2d010301c0303980c0c804e0051001d9040c4010302c0c81c038200301c0c01400300040741d840e4aa21240007130320b801e0500c06140402411034803501c40050060100107421910b6204003050042621764540100300d06402070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 356089001 1250 356087751 356087777
    0xf0307030c15050d05070915021209060f070213020d0e0109020d0602130b0a02031b0a03080a0513080d14060d05150709030f14161206110f031501 64
    0x4021084a4000082204180c0303484607015041e419201c0c000b0400c041080691100a800c0c001c450052045544070b00d0f40382d250040300c1c0700000c19464564115000380e0300b100c0004d035540301502c1c131004045a06660f44e1b8202d0080c0c5d215840b43c0c560007900050310124140807200740c1e80c083e003200d00c4003131024802c64508640050898210f09030095005418000c0d0310045178160b070240c03130800302070613040c200e0980b60404a081d98000301c102c04010f030b2000502814502403032501d409981111002000c4880c055034000e44601c3c0000e11402641c0d80d01e0002400d210a0424000420303a04040842da03102c00541190000c0c26009103941c4451075441d001c600181814074544c078840d40c1000142000c04c0306221050744c1120060140010007412030404004118001c040d1400c0074455181500c0100c01c84504900304040dc403448040101c11481c02c2140681001c466030001e03030300c0400003451003224049503006000d4200a01101003002c000c11011004c6090961840780c003d07220071203c6e0102d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 356090251 1250 356089001 356089003
    0xe0d0e0f01231b1c050a020606010e011209081306020604030c030c110603010e040b01140618040f0509030c010e0303101707030506070216080a02240f030709050f03 72
    0x1040c4102800151011003a4207941c80070501c2c0306845100c0c1c621103290643c40000c1c00707800c4400090f4502035410800e08404100c084211480303a488503410482d0400d00c01d100080c0d00c1d07190083c001ca05000f041c41c0d004a50340e200303c8100f02d00d0305c1d103031000f0041c48109080552407504901c0c3c5a00f801744ca50440854000d000252080c42181e15a5440c1844501690225814403c000c800c4810161a0820b0940f40d511100914084c00091900c071303031145800c0c02c21082c4150b041e448084004881d100c0f508882c1c844504648054419500300c00d421304800c000f0800400d601002c0c3c503502440c0500340b10a610020008068603c0008004d202001041c1515070702c0b07210654210b038154403040003c008000c1d05e06080e0030f140031070f4015a91d10642da81c071a1800c02c68200c0b48900181c01403036680800d1030070b0303905040140003002c1c020210945d0f1a4045801368851140742020740c0501540f942c040078101046640c40c4015008194490030414406401c0003103034010a4460000c1040035421800c2c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 356091501 1250 356090251 356090269
    0xc0a050f0c09070c0501020403023c03060109020a0908030a170f5b0b12280606050d2937080f2b0903060e0d0e 49
    0xc0080c81528540c503803c0007512905200d41c001c550030754003484000b015a89000706034080c294501c030ac8002c41c1e1543c0e5031000c5c00f5103500020400000045802d14100d80700082c00c141599850400146e603000c3d0032409590041003540008102d210000e4000e0140d980106801a070a080c11100c540a440310144841018011943c0204c0402524003c05501d4805456040070a4408080b00345000ca003000b00030020120217100005c00248260390018980324491280040109819050401400c444420216400503043e008003640d411040c9100c25081c0d054000d800318494401c10030b1558a5002a1203508151010b9800500e008106030000c0340101400c0e410644165414951000386402c00150400d0301aa0428035120301040041c00c1c251403500f6020b2841d0b0360400d114080c60705070b403240b91070b2042000c98100d030405104a25034450101c00328a0114003120702c5e406c003814240c01181c0116030740e44080e05050908410310142e00f00447c0803800c0c0c017030964814070400044000e11810075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 356092751 1250 356091501 356091523
    0xd030c0212030a020f0c0604141e0c040203070216081b040e0c01110705040204030819051315050f030117060a0e0a111f020f060609041a0403090306020c0a050f 70
    0x107001000010750f0500c050780109944140c8217039590a2162500200f0b00d4940100d4044614048036058954140300801540400c0001001d00c003e04000c1011040d88810054800a01a540201c00326450500900c00e40d803120320405940d500b055600c450080d40c412a1100032400a850425a000d05080034001d4040482c5443c006019050384203004603a001e400c841c800b5034a000b48000803810f96507a000a10080d0302a203011504c51104841c202e00711284000400c00340035003000034008034181c00c64201c04903160840324107280c180b030850a454a108901c0502c04e1820004000325800c03115000410460350300030f040f0f4030b040d5030307102c41d030310854070280d000e0b10b050740c071420700140001c5c05404101803009004c2e055003541c03949108000c08140d0440141400750b082a203640c0c0d40c0a400300101e65100d08100c03011b054034180350303c1d0754101040640e0003140102d000000101814001c0d0b12190085501203011561824101d60680c1c68071800c90b0111900d004220b2444040c82001030098400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 356094001 1250 356092751 356092783
    0x31805010c080906071401050a09050f031218030706050a0501030308060a0321091203020a05160e060108070c05061f051f08100305120a03050f070207060e0d020a03050d030c02 77
    0x440d9a4080280c550417400b822601c0188040007403070350345803c1c0686409800e0110340850300c80c0071490302e60308150021030740030416402406a2001d5143c804581c9402008000d00c2845c40031b102c4443e10b045218180c40500158100300c01c3c071010851550005048900990b1650126107809040111f80481440054081c1ca010340f08400c00f0080400140c2122200341441110203694080b04280c80d18554030942c00368206003030900a001003031200b42100d220040c00e01c0040303030420520b0361341120054146810403070008002001e4074058070107070011640140403250245480c565501704070030705e40400c421201038230b9000255800c00102c0040d480c4030078140c8200f10000d4550450f10440000c0a01c1d40d1b00f086e00e80d0020109005010180000c1e1407000215034a040302000902a0303200035102120740e04c032800800109540c007084c0c0c10282c1c1c260740b50004904910f40c0011391070300d4007880c010f076101042a03000010800002241e1030f2400f510749081c4410030304940140c1e240d20f1441007003000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 356095251 1250 356094001 356094007
    0xb2701050f011b0b06040902030a05071e1d0604060b070b011a09060403021c020d0c05010212090f0d081314040c17070c08070803011205010b06040b04030201030b03100207031805010c08 81
    0x301328000301580034902401c0064643c40d1500040c0c60b040e00c210040e146038100310014068402031000d100c8500c1c0c2d016004849151408481e110007a11215075417503032a250030041a502d80c1ca0b80c00c040001c100220b0b506881e11014100b1800040080c0302d01090f031040e02407602c0c65003031a44141c0b003c6000090503030741402c3c039540a20800d06840e0500c3c0040744424581d8100580c3d039070b0f40034182c241c00303204d48031103c5080400182c80c060600410001080c014002c40d03031140e491000620404405482143da03903080c3c0c0c9008180c40c01119180346482524a6022840d10004e2040b100980012582403100c00403000040c0d0340c03032090850146055402c48005012079000d6001c00804074410310500380703845da864403401c00d160001c0e0840d51080c0604d44a06090040900840c802da640484a0500c0e103840d2030034040b140d1090340701c002d040c10f0715001d40c0d000680e070a010b002c0c410302c503403e0150366801603480c0090030310071103e038000480440940c001c1107551040340d004105950052a90b46 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 356096501 1250 356095251 356095253
    0x10e1b0618090f10050a0308190c020a1205070504020c0d050c0a05060f06031515040b0103021303060603031101021c0b040b0a060207090c050903030304060b2701050f011b 75
    0x12180e03024001c048102102600c003454252a603000b400d00c284440c0c0c3e031200807818030004003450310000d5802244101c1251200744049038002c0d003100c2c4001000d01c0915400f58590000340c0d400805541d020303504c0b810755900040c440741d8444010b5809446403040d66801034403441000224094460145419800b0b411460b01d01401080127101d0f40120008884401e94180d0301c1e18035048046030230340c5246204005010f5607003030411024403c010590403110031403820172807140843c0403100b070f550721581d22003125031140d90203641101c20b00191052131907015a16400e104014080b01d01c07040300005d041a6071a455000184240c849041c0c40840550740c0800180d001e10241c421031075015400790391800802030344c1e0307503c854280040c00700350042e02403503240a03e49412035850320380701402e01c0410059111550380c04011a80c0c410340c0190000385030b050345804a01d008d061020850800c003014941c10110b1a88480424101c9004a4081a40803210380045400b030183e80c005c1c01061940e1920304e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 356097751 1250 356096501 356096509
    0x30d03050702121c0e03130305010903080106171b091503060108130807080304061409010b010f020102040e01030b0c071401060311011103070b0406110a0c0b0112030c17040f06020c03010e1b 83
    0x4100708021801c582c20300251100002e40c47c01980c0c02111669580c80c85081050b030042c0b00c17140100704c103007404404c0515280c5114106070005199103260070214002d18400008941503034081c2801400c131b039030004140c100c0320390381360700135503605020441903070000d49440310046500e00220360000e411410000710b680d901c002c58001a004135501c584500748a03090328440d50620f88108030034000403402500340000034107007030a6140c2c01c4045900400c414044c401d00f1812050440782e01800d218459a074030582e0740842d0003400b80c001c040381d1009500800b13054054001c4000d5078052440b00911014000040d600120040c10300841600705010240220f00d070608409c1c1c2c0706000f4040828210345d00454011594030240d80140400d150321840c5c1d0034450080302103401742c2440340081342604902e4401804000c1050302c0100040c00c2d4203c1d101200010000741c3e00280100384540c0a19034270b0b140c0207074880c816440e800c0c1c084d42c42e12001e81408200040c240118031480c01000800000b40300c240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 356099001 1250 356097751 356097761
    0x220e0105130e010f0c0509130506030c0f0d0501090302070614031905070903080a0903030e060c07030b0903070606121a0c0417010b090403030203040c060806031b010e030d03050702121c 81
    0x11502c0f07568406100c48851000e00a101d9480c0f529a16190f8130b203101c0c810812144454490002050b241ca41049490b8800190084110780b00715503401440005500182c080e008640e402040d80d400d04901e007082580002e580b200780d95064030750400041908100814902044880703025901ca41010240f012580b51301168004c1070618191200759201d881d528600c0c0d020000c0207001607a007081c1042495404035003c240d01c0d208131180351604054030600c135039804a600024241c81d00390000300380c0954040080354499688801d061101541e10001a1508a02c0e40401d03141c501c42072075000002058000003611422841740030070300307081c10035200c9003070258001003e20183d0759071241010190394141c5c480d846a4441e03a00503940346480d1500c07081d42041ea0b40040c0c03d202001c0107002c00e03a030b4080344148100507a0501401102003090040b10259000b54159030103000d40c000940c0b640303a142c0c21051180220f0340032600c0100c048001e201c0036100310f20f48203010b5004c07004004808036041d008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 356100251 1250 356099001 356099021
    0x190206030f19090b0a2003220501050405010212070201020a0212031017010c170c0d02130314060709080703020108131703010b0a121404061d03220e010513 68
    0x550074454803618403080494107003203c1a605080e83c43c0410010215034003890300c10091103a42c0301e83e400310009a46a0600020f0800200b441030040345078480c07000c84a1501b05039800c80004e000724106401c165000350f000343c83c0c0f001d102e8242c0d40002c0000c0e0050003180c0d240190703075001340740801c9545101c030405d0700050803d20110408000c006071254540a650020141100001a11110803000548000c14201c3d1000d00d401120040042d400b00c03880644411a503212005641e420984804003044011a0002030084c461010803000810001800c103200e01070790780b0384d00802500c807928503554050030b00c0004d002498120010b00c9408141310408140f07449000d01c032119101c1c160624505030401d070041c0c0003c01c00860350010142d400148104007200f0944108801c1030084020b00c00709000400c094011526148000070f8091258000f0300081c58060507603031603070701034400118404d18007084800307d802620000f1030100480741d005412100010006c840031112409003070050b1010340c030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 356101501 1250 356100251 356100271
    0x1050c06070f0e1e0a0509010f090905010605060d050601140412021504050907020d030f1b1b080307030609050c090f0112091527050721020a1205190206030f 69
    0x3d0f00010ba6100d603280d00c610b50015003180481c0c801d10005002c0c0c00892688201e02c2080680c00411842c035920f4400c00661b69101070202e000000c60400c103001d4000c0d0351005412010004480174038030903a074441c41c09540c0990b50450542d85c0d8808400141c0182d0040054940c113440500c8014a401000110f000b29030801842c1010f81e90000a00c0303030801141e1280160700084a401c000507418482c03003262071034100080100202c0a11901e400e045039140f85414490b450003015140c031300010030100c06c80c0d41700a0655607072a0411006010f42440d12400c46040c1c28500410200010350050301c0350524040d01000c2c802503440011240d03010510107404030150f03180303403401c040b400c8803042e100d01d42c2d02d540000c5914001d11a00807800b80355040542c01c2c2c042ca034152040081c6000c15180d0071128030503020982100c1001002c11110b400c0c80c8003d50140e014040064010a0704881a0350a130090040c2d07403008003c116504001d9a0141c8000d521500400000e031284400180340c5400542c050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 356102751 1250 356101501 356101517
    0x61e0d031107171905070302090402042c100509030d02160605070c021f0801031401060e04060c08060603070903020411070b04061401080316110415031a0601050c06070f 74
    0x301e0010b00707002003a08580740900070340240c0b802034074040001c1a800062080040c107070080c2511034603103a03911400001d218004507004101550340342d810100b0661056490111031040501d50100f00401210500d8514050341c100000b20403400e100e0781d4441d0640328040c0d850b100304001c4140007988038000d445110240d1080c640040f5141d441345610a041c10345641c032000c1c1150041200300380700300040113140d1407007015041c0140d500141007070442e80d01c02808180b240c0c90030341e21400341c12190048a0f020f50b245080005000a40c1c119400d2840c1c541c5031003140b5282c0d041400030034881125900045040a00108014201175008000c0c5812495229040c01055541d80c3d04104040e00d096a0003070f1a0800d81d1040b1001d0015680104090340085203896034000603008800300e030010142450b05812030b020400d44454222180c20040e16142c090195220310b4020f400394100c41504400001400c0096495409032048901107142c8c5030080c01d1565601130708541080e64003845030100301c448 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 356104001 1250 356102751 356102777
    0xb030c16050d0201020418060501021b0102010f090b01150f0915020c040f0906060602030a020c1905150309010b22021e13030506060405040b060d1406011409061e0d03 73
    0xd000050040b40b5580c00581d4591400328100f416080103001c00708480c6c42c1ca041001260f8000580d00105115400071481d03690b807405c0141d005043d004000c5800d5402d044045041002076100981a074107402100c81c07119044a000310b4441000c106001d0101c0d030512018031505a2205080c0401181e03881110f1900f81c64401140c1a40c0040c140c1741001030300ca58100e030411481340101006401184021030820b56000002503031004500041341c0554001001088042060107441e4083d1174090300f80494869034100001155100316500b40c115442c007084009c0618200c5000d0320340b03141c00802e14400061440301040203501c2444402100c0340601600c0c900005501c0142181003059051b4a4910340366051042c1030810040070540700700c0c68041040000369142440c030307401c00320548a0724a25042c615040500404010a100c4607100e26400020402100f250582c0c11007019201026107441e10780901c003581da148032004078140398900c2c1d40c00040c01d2048091034120f001c0d2400003500029 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 356105251 1250 356104001 356104003
    0x150311121c050a0f020d020d0e04110a0f09080607080414100c0203090a0b04120609050a140a030e0d0c140402070611030a0506011704080306011709160602070b030c1605 74
    0x141c80554008582c000c1070031038245821008002034203206001a200c0d180c8080f4000b502e4a8559a40b80140700c80c480b11101c50341c072550f01440c1c001160400042c1d4402c0171600141c0003806480d1541c0010343c02c0d01c004540000d0102c0d915000c0c5560b602e40d2905034035940d0703c080240d2090628407080707118242c0140d11210082c0510940c0c1c110307076005181c2d16142c400500114400c030390041030000d142000100444a9030112500044d078100743c0c009607419a44c40d0a6041c0400d02c1c0c80507145e072a40e0440901c0407000411402801841790b140c003c1c005030480c06002d002c0102c1c071805800d145070000d040007003000501300b124035000e0007007005241059940e00d1104450510f140100111008420015018041d1041c83d4104e5000d080102c1c00c0313400b403a2003c0109070000c2005240500c00300c0459003d90103120340c1510800007030031a150034600a549a0355996420302001c0499589030000a503941c00800c40e0b009480c2c00742907452955035207522001066000710840101d6407040c43e411404a94 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 356106501 1250 356105251 356105293
    0xf140909040f02130b030303040f050c03030d021809010302031e0717070e070201150b09010306030606031104140c041a0f070b010906060201140105010309020d02030d1215031112 78
    0x111882c402c2c04604024014459020300c82807511403c946050006041c0f07035000820ba03544640d20508900307001140d0311380507041070880703110340d50035100c007007840450600785030040c10130181c55400034461002c4000030000b0100c03080c40042d400d070300040e42d8804100c10045101c0002c1c814202141d94050361803503145210042190309100680108800b4418103a1805442e50400c40a200034410040004520b0f800e82c4a1481154010392000030016103a90198111600071500304008010b002d5a0f0f05010082240c040021440f540c58005440c5512502a1059001d400d02103031450515060011081c140300d40b14140c0c9184200c20700403000c01c030325400000c3c04281e00c07401c00c424165251011300c41c1a940303150400700079a414001c100000c194510b481074111002417a002c030f608074240c0080b039607030894500080d400d07015401d0800001c9821000d8141d40103030403501000001042d40c04800c900000e8000241240e419a00004030380c9401c040040c0c00450074420703100c4900c880e40c81440128 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 356107751 1250 356106501 356106503
    0x3051305030c0f0c030c180717190b01080f060607030e03030a020706090f0b07080307120f0c020c04020414040504080d0903020601180e060a05070201061a0d0605060a0f14090904 78
    0x43d10034003c02c00f44036000d00070349510000640c0103000d83c503166000a200c42c110310402040601803200000d800c0c07803051100c0d07200a4010f007060141030500714a0704142800c16030020007542c1c10008400c545500c41c0d04280d20964408542000d9030300c4080400c051503001c0b40007903042010400014650f90740a10090032039105540040800c42d14040014201407010340c0700208528958a0030400400910100e607541c59021555030303941d0755880001c1e581d410008003854001850440180b444887c0c9900200e44407501c1d8003200c607520b00301d900b0401648124065001d200c0c814140781e10190402d50440c0ba040340c401c050250420130201900f104803419407100f900180d1081c030041142c45605146500078000b40f043c280512030450220b40d6881c4000b0b09441d0500b583c1c1e40002c3c44440c800c0d032240b40500b400d01a80d40110300e100350030890341d40001c080e14200c5460040001128a0544105c40b40082c164a400c01032140303518054032200c030078080d880034209042040c03c0d2103613900b0030201c1c411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 356109001 1250 356107751 356107753
    0x306010903021e0603191415040506042304210c02060c15090309040f0504110d0201200c041b08040303020f0d0c0302030a0c08011409060d0614150a0506040603051305030c 75
    0xb07080c0824046e0965a2604500c411140b5510910082c1e5008084411384440281c40218036a110324000c500240301040e881e002880c28440d50820394a00040842d020b18000e49103802600c040c40b40124002945040c5040400c0350305001b800141024406084080001800d80e41e902034400407803194100700301d45180043d000015400d406d80b8013031103056030402c0703401030400031403400340d40b000081d5060710342491042203624806011a07108601c0100004010443c2010180040581a46d9150301e000c0c61440b941c113100c09440e5038141e045140302c146c04180e42e507540c1a2159201a002540078900c1c0240b5600d040040440341407840c05aa01e120300181c2d40160f480c83d140466100701c174a000545400c200f500c4004214080d4404007500700040200d856211a442e0400000c04103981084010704840c203100d00c2d40ca400411300d901c20300c5003428000000d15240001c04116141c6028010680c0c00320007070000388038042c0b00741e10441d0320110035000202e001c1d03500e4440364a560481860441c02d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 356110251 1250 356109001 356109031
    0xa0309230d080c043c05090a020903100e0102090418020303190302070203030f0403030206070c0c090b01030207061505030f070b0414060904051f0806160c030c1a010e010b0306010903021e0603 84
    0x2c3ca10150760440381e00f1307145d0509070302c540d0603d00041e10301c20010705040803c940201c0c0c2401607070b5007440942d002261400c001c201c2a50101d1074140030b5003005800604c29440c0075604468126410741d1546220340c010051441e104241c1c06203200b075590341591104041c0d080c0403e00058804000400d007405440b9502a15240f440c90000c1c64840300070b00002c00c1201e4880d480d40000d81700d80c510401e8446803c40400c6500d00e29004070002d000310b1401800785801c0c40fa0840450000d500d030502079443c15803d6520348407808651603604c070118481c0d010484420030003000f68946401d802290b0200040c4690301d06401840042c080d101c0581d000a400c0c0c01448400b400d0a560650b40d100070440c0300c020301200d2401020001d940c0a54564100900011000510800d4443d82991041641c0480d0300c203045811108604500b040901802c81c54081450010400d000250140d0384601e5050f507a44070405d00319400e000e19143c04d40c0701c200c91000703402e4401203180d0300c0d5800745104450308034800107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 356111501 1250 356110251 356110319
    0xf062b0c030605011415030606160b1501180501030c0905040f052401021002071e080405010f050304240e011d010c080405070b07020609060a0309230d080c04 69
    0xb085410680c04a011140100103109040d25200c1800c040524005042610381e55140b0210f0070b11310803260303808041c3c00c4188444082007020b800c1c0c0c0e03000c0c0c0321413880c0104200d44600150f45110092801c5891113004203000c014540c407a03045440204403514045c0310481c1e4038001301d0260b0788039800f4030900580361010028603207503280303100341c020218540c40503e1003c5600041d40f50209a2400c0b11001d800040c0300c0c003030107400500f100180c9a07018601d5042941c80c100203c05400500825000a5119842c9640d00e8404c1c402d032809680c101515540e070000980880c005500001d4404010030707103d26030490050001e101d507a01103007141a10010203490540b00c0e40c21690881d0580050020710301c103020210300001202d0381520b184c0c0d100c00d540d508107400040e0703060081d200115400301c0e0014049440682c160402e0054a1251044006400161284504103202d014101d2542e500ca0004215030328817424003503800c070f500100094a0b1a455140700036486142da40180c200c1c180101d0044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 356112751 1250 356111501 356111513
    0x6040b06030702060f0601020d0c080325110106060302071a0402120714030606030703031713080304030e010e10050316030207121115010b0703030c0203120403031a090f062b0c03 78
    0x15440f1000342301503c0b4540301c221001e000034540b8103014101c440c020000583c0c00221001421000032450b460800a80c4102e030018800a1460100340d5a0750030311100241480c06802991411341d070100712114843c481c441c0e90540400001c2003031764007031031a403805030030f4901c00d10a00001c0d121106d11505024402c10500d4500078001d00881d001c0d900400040000c694080b48030303405111090391564654940c001c036142c0c110490301001d00018400002d01041640003e0f04101c2c8803000c1e21100360003244a030801c200a100b80f042000421801c00004d0354030301c0640340c18041000181001800c160701d80d01c60b0038000d0342c042c154002090b507800c0c80c0704001d00c040012440d607a0b80c016841c11b0541c1007080d400d85500490b0002824141ca9800f5038044900a1068032100d48589100d030000307103041d04004003c0c10000b02d00171120442a20880400d09120700303c140301c0c2244407204c2342c0c55141c15060200354200c0c0c2041070901c44040c040040d810a5901070172222900980c402e110050441c102a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 356114001 1250 356112751 356112781
    0x5120c0318161a040801020315010801090b0d02090c0d050903040303031d121605010e010504110303070218040c0308030703090201090e0f0402010c050c03070603150509070c060506040b0603070206 86
    0x10324034952080300354600c507803100a88403080d1148810803e021110340851000280560382010328294004000c2104c64a40c030100400c2c2080300b40da0703000f00d90b40d8401c55403044901e00d540c4640c025440c00401400340c100b55444a4112590101c99848c1c0a016100682250021f650003002d0344c02c0060200706041d81400741045e80c00300000e0101c00315070540c1031266214100581c0c001800e50108002800501c40c101218083c4e810000911600108103940e60091004403000c40301d010550481c0e28440c10300000ba201c04503400317014540880e602c5144c559094030001c00488190780c4403c004000548004003075806000b543e00e010407004e0640c4005000301e40140c202501c1c500c1c001c001c03c0724040803041d04c50340198080c01e0580e41001c07036082c034a013000320072240c0035014401c0d99000a04591f140c4c2c0309503100f12446540d0174044d500c601c10000903080c00d45522000402050401c004511107030700c03082c2c003c04e0040c0700098509a210104495400840345400560003031010003044c10701d500c6c0c0c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 356115107 1106 356114001 356114041
    0xb030127021f0509010e0d14070e09013803010c020708010f0506010c080a0302090a0f0509070906050324030f0a030909050702120a05120c03 62
    0x41486002000d80102c0c0507080181c107410761001d2001c80c6211820340e6036907151030b000c00d050046800c503816000b00c0e644007040078103010024410800040b00c0f8540174010b0400c2034030308070100c52081c000030028400c990620b0580880402038422600d90b00d41c1d03d81840b9500380d403800003030725404d00034031607150150f181a0410440c00d400186010444034203900a0145c040e03801400000c1e508251209070100d80304000f4500050903120151200c90306e00d26005017804100c0001036910b0741141d104400400300034805124504000d001c19911400d03070f040c6194090700d8044e00824a1000616046d00b560512203c04601812170440d550b40003401001c44080c0300c00c0852036500c5400e5070360100d000c00d00d45a4009080b10960003090b1040106130060f14120300d914402d0003242d4050706442c02084810000210b5010403001190f00a008241c003460704c82c5800c42407000b200c509006 = true := by decide +kernel

theorem cover : BRFrame.Cov 355935251 356115107 := by
  have h0 := BRFrame.cov_init 355935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 355935251 ≤ n) (h2 : n < 356115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
