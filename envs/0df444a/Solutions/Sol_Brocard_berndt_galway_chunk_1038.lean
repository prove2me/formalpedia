-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1038
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:57:18.787559+00:00
-- url     : https://prove2.me/submissions/643b7929-bf27-4c4c-80ad-8c329fd54c67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 186510791 ≤ n < 186690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 186512041 1250 186510791 186510799
    0x60605070308090a0c060804020f10050f1338031012151a01140c0d030507050d0608060103030801050405090604020127092309030a03050406020d0203040302060f0c18 73
    0x40d5a600003c189070200700200a010400500c2001030003d034071840291142d4401d54006140c1d02c6254140315a2100e80250384020a00521000700c00d03210304000f808d402e0b80e045591040f455901c95034141da01c5c15507907581c2d10f6034130041c40320801d08101400d010000c0c1d00f100080e03855485c0440e102c5444491a0040c96402c05040f14003100f402000140e808400c603402c3e078104603901c1070868907680e101ca1104903a0214510001001e004d175822416110f00da508400600300c00699a2411001400000c2c0000700f800f1003480803001c64501c600c03885020784140f00c003c001e2941141400340121005a00091081b8108402c101e01070401188003500f013030303083c24078015150100c04400c0d1000030400c02458415a00d01000403a03035119080351580600724040f80301c08000f4040b1042c80c82c803044803035020a034030411640085030311992005034002d02407100142480340903900342082c1d0307009850960059000b40c0038440407401d440300143d00700800e02685440d00c03600701442860b0402c0354120604c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 186513291 1250 186512041 186512057
    0x6010f060219020d0201050409020a0306090b030102040b070206070609050a0507031502190809070b131701110403141203190e07050f010c1412072d083601120606050703 74
    0x2164092001e2314060007440a05645424100d0307401001003107103120300240f2a04000402da16400c0600c2120191054040703107914085042d0240300c000c0d401a0b40480d41241d0362201940890b10900031404558416030250400c1c80c60744c21700d00d4404903001d0021110500c10041e10f150ba1910340c0e692000400c0c182000482565108415030900752194042030320080002a0052640e0503141508107032024803c00380d038000581400907089610400300080d00b11410030042c004184180e103903210281c10ba40032502d6107420f20a044030907800548150603150210051483c50345400d01500706250907001c01048014a050001100035104460356818484041c02440038803c00c1c078004042d442960045440303007404403c159415501440302a03400c42d0780340407180340800d551400c0050180f84450130507004180e17503c410b20141d010142c000720040000001e80080c0c0d845410303240f01a003845684000c40742d42c480c00034050340c031540e41169119140c44001c0c8403454000c019502855054600030003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 186514541 1250 186513291 186513293
    0x150a0305041407090b0a0b030f01170106080d05070201020f06100b0d1b02030a090f1d0901141006110106030803070503040c03080408060a0605030a050d052a06010f060219020d 77
    0xc0b15681d401215850240d5000401c07030900da6005412000d8040d108200160b6440e90003d42500080c1c90400141d07801c4401006500392911800c995003502100000e02e90f81c2d1000594074081035681c02c2404a400403582e0025580c042c82504c20301084100900403500e010514003460040d94024032102d2240840c0031011003946074405000181c40401503000e44d01503d8000e99260869201140055403540000c03403155413540507981118492160312840d91401c404402060300002c124007155942d410207420764020101c661800b5001050301080d00754200b40008100c0001c0341c1c0c444500e603040c42001c00c00101c19034112a03005146107041b075200e03201c1d403400c040302c40388661015151308004100803d00d9103000c9150360250b01441803c00140f039840d81455100e48a0803005003454101440980c403560242c00240300c088074001d03062400f12810400e00301e02800341000f460307450348032030011300c000c200314028403010f0002c60000340b80e0741828510b9400301d00c040c890b00900032103030309400b00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 186515791 1250 186514541 186514553
    0xb0f0114181308070b09012703120b1f0207080d0c110607050604050d18050108190605060d0501090b01030209090c090a030606060f0210051e10030204060b031005150a030504 76
    0x103415950282d5001d0360703203249003813482213038100380c1c0c6c11000c5518050f0000884050004620900e080308011031805404684081d100060543c80c000302d0b4a0f102c4508004a030350303d044030407a110088045412403100f03035074001d20b403011030b811448480c2e21000000c1c88541c0c000b01c15080d1150301016000010480c3d001013002d901440d14020100e11881045c0320806c01c01159540355020281c0d14005e99800c1c098080c00344000c28411240411000e00100e00c5182010091080c150021140810080c0d543c1003c505075a00c00040c0e844007540d184018001d402c52070248020710802407a05604020041e400102400809030084056040004103003105480c1c104241004640000c0201300f400d60311100542048040c0c615000140150040c2d00040c4a4030300c41c8034041d00c4c00400c0140c001c0703d50711541c540340744054000140e0320b841500004c0180c1c0d0701d0040c040506042c980f95500c0b030030948901c103051440b030b4000c24480c0c101c0b0890728100c04820005d480d0001203903c0c0202d419242c9040c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 186517041 1250 186515791 186515821
    0x70611130b0903030f03070503010e0f06060d0c030e100605040f090503031303020c040c03060e0610140d0216030e0112020903120702010e040c081e0112060b0102100204030b0f011418 80
    0x40502c00d00206c204461103401c100514100d442a0200700507503607a41c204400d54200c102c8542d0351208013400140300d40320f881d0f441805020301908001400da81c40040c80b030b140194100b80c256203241c0740c200502050174203001d0040d42c504104401e00100c0003e560741a224040200305c0d82d0080ea2815281d0300381482004000c07070385040a03004110400c1c180310002d02074100c90152414056054002c900a070600c106203c0c5802203940e501001c1c5007a000b4200502e42c0318080760207103e034080c8003885241c000f4505045c02d40e4070944450300d210365040d0014002d8103402d200005043d20520050703280d80c81c081a03041500c2403010030f040e541c1805200507910381440c07402c0b40b40c101e803800c0d4144102c0b64105040e54000da82c110007001b0740d82e240c51080b070b64542d001d0003500105201891550002a0513402000c613855050050b950a000070208010880c1c0041c0c0c01611031075032010921030780f1401d05e80d003540505554036504050842030340204000c0d113402c4c01c620f14101728500015840301c15031612 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 186518291 1250 186517041 186517057
    0x9090207050102030103110603070903060e0c03011a01020105011706190f02120609090724110d0203180f062a071403060108011b0c06020f0708070611130b090303 71
    0x440d114041030400074000d4000f40421614905d02600481c103500d045019244241195507a1074182810b554500018012110340380c09984101e00380902030ba5020300a6410303004060340320440361158803000a09650040e4810721088003d2441600750131000301e0f0b26940003401e8680b00e43c2001c0350802c41e40040c645580d01105451010840e2644105280112409071404a424036983e4a901c080b541e2034002a22410120181100001010b1201005a16040300362418034880b885860500107090880c408052401a000011800e0f00d410180404001c1180c041d01c51241c58501d00b408a811842009007640b1446190b01d0301e2540b00c60314600203104041e402c000d0b1503025a491700070b40d000103409402c0303500c030340502c5d000420310210500c2562003042d1001000c0c070094520180c1900d5504001d001030318125020480d501012410100412403140304810084d905d0510b400e185086072904180c12100070410004800c1c000142003d43e010b80d24200c3c0d145c5c0e5592042d90000c0e2a620a5400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 186519541 1250 186518291 186518309
    0x21c0203091314060a150e0d060912021c140c07090e1b04020a09050126190c11030406050d02090a030b060a080a0b0a0b03011508032d0702010e0109 65
    0x9041c0c91444141e0000d030f00d4590603541d50304154075482c0410442c0035003800382c18510700c0b40026880c0c0c0c4034401c1513000c4001c0001303466010140000c2d29940300f9500b00040c10389891005910600003640e041048a410230f04803070107000c12400040c001440000500503000803d5400b2948668074002800840000c000d6220100146400c00f162183c1740c10011a0401c10683c0642c0c02e04494201802142e0040c51141d44603c4c0305410100191383c03d0444054036481c0c0e18110350b11749a00344180c0c4190b8028000c1401d510460f0401d11744000907640084144000c101b0041480500102c0c000706036400c1d10400d0402640722114021100c0081c0901c01c40103911904d101c1c000828081d6000c1480e0052200365042c014407915106101d69030200c40d0b00042103a12910005440700311543e0280074501001000442c694128140030400590960086043c1d0f03000003804031400c482c01d90b0600082140199010381d404030404843c0c07502d01071200c01a05202021100c01c400f68820840200644007801d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 186520791 1250 186519541 186519559
    0xc0a030e0c0d110420070303020a12020309010203010e0601050c0607110a06020310080c010516030c170319061505120a0e06090706090608060d060b0a080a1a0f010501021c020309 78
    0x4203101c10020380c0c40c02580c0c0a02e01e410f1048171815001400d0915861081d60132520303000e46a903044001354456400c40f410483d40109004031a43e8a00095014403200f0380007603120b50406261412500c80508100d0502204101d100c80e03000d008070345168000103a0600c94481c00742d01100074204070181d10000c107120b20000c00c00c0289080c080c0c014040c4c1e480310f030407500030300c41c29001540d65219903902c440d25142e810950400091084900c0340040344200840798070110280516001904180d909007400e4010180c011210000d900c182c0e1300a007441402051a081d2295014000d4070414201c80208011800029842030580d008000301c0d00e2034504450142ca403040d9455241c00322401400005407111400007a098410440039000340c800600d00c444c0508250b031040002c20080d5641c9810035100e040000c2c1440d418403848102900502d0640419241d403030480316941001410110505034202c0140005d0364002400010080200e802410a110032142a45140140c860059001c01e001c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 186522041 1250 186520791 186520793
    0x110c0d020f0d111f0908120f0a0c0f081807030803010e0a060f2607090f05010f080606090403180303050c010b0a03030f1d151902060c0a030e0c0d 64
    0x91005102500c1d034003075401003001c0039411201d41480d50380540265000c80e051105480001e0300400100000400c0041c45074566901c01350103400042e158501d10140c1d8003044000d007034a104003603000300021000c05c210000d98402415160084070004100200c000000302a400e554000320f4081c1070b140211889559039207001e00c4a0f13802402414403034140300c00461007004043c01804250345071003031008081410001201d01007078842c0f1000d8a809c6035000301c49a1680c0900c242406001c052101080321180094900155181079201880d80c002d020b904101c012004902507800003001c56462810f500c86040440e410716030506480001d03001003000108058100004143c1c13000400d009001044140041107008a554400540401c40186070700310b51074401c038182d5445100d070045524500e4035a41c04075181039490300000070200ea000078020f082d18400911014070001510090141d840d0140518603940261800e8805068841608400240c401d20070354200e50070180c00d503100310100b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 186523291 1250 186522041 186522043
    0x130513060302130501060903020d02031e01050a0b010819021c0c030b01030608010b0d030513080307060e12070c0b16020d150b0d02010903080c070b070503031017060703110c0d02 78
    0x100e21049124860f01030301d02c5512611405083d0403074100707451b0464020316580070720007031480320381c001c07a494081c50b2116203200d0158003141100f400c1c4040001024a049072102e001c580615402c0d60520044904001e1500954407117605174140d40c20340582c4a0044618160340c0c0300e030210741c48024030f04003042482c003141d0683c401812030038242c0e028013905070f403000a182240d090984507a0444091000c60303000c207010f14010813403812030484845005654030625821604641000c941c0340d500e8050200509204220740440607001c1c8061071303e0800e80faa140c0d8640e200510402400c0c02d00130441c1e000514050300c00c5408070740c0150010403a410186030210810850140d4600303420b1a00001c0e1080381403008030b00004e40c2e4180c4403903c925045031900318054111500810291040714030118482002002810802e403140d00103544130b00b040f0264095800c9590082d2105007004445500e912400040154000680d03050001e40d43c5a8ac0018071014030403100c00050714418070380d940480b680c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 186524541 1250 186523291 186523301
    0x110c0303070f030513150506030c03070b0913020301080304060f022e06090204080a0618120203031605030c041701060302192303151320040506010311030705130513 72
    0x4140c0da0f0070042560741040c840b800d12402c45010740444102110b1894501e100c1d4050b070b402500040480d07036441c1003a40024908110b58020301c428150210780c0026500388450500a00c4061100650941d0304000400b952401280304160821007e5400c13030907004d0080c4420009594200791301003881a203800c0b4152400d000c84140c4030094902500000e4101d105c0c42030b2400d6840c55006080780030110f4490201070a06091340d0240440c0fa07600200005047c0c440b4010b4100d10b98020f1922481d10408100c561203881c984c007001c1c820b041042200c20024030045a090383c10740c40c0c00703494800c281c140701401054550402034000c040c0020450030201143d20343e1040340c4028440084c0c80c002683c410704040750008116400d0b90003001140d94000d02c0c40102a440724045d0441d1904010a440b00106401805480c038116610398001103010b0400e0302450307900070001c3c00c0c24441c514192030714280038400207210308208840828140a90f143d40e0740c0450040200605000c400b044542016009003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 186525791 1250 186524541 186524567
    0xc09130c06030c1101090b01300501050619030b01171005090304212105121603061508190f0e030c0105060a0308071203020c01050703060303180803030a110c030307 72
    0x83d040030461120014140682e10241f9800811511641d107400c0410b00d003a12458a008150413140e0300b1700c80214400c0490707948a90282d00080359909007241403002212580c1d1f2050020641c81c40c1c02d02c04512501805030440c1c410350400540c20780d94481c0c1c10b061111402d442106a810030003030001041000018005503104c8040c0d1080d104035000e03a9420b0804144401880e01e008040b1409610040054000e03600c11503042203450005400e201c1035801d20700b11a40d020080c51801c0c03905c2e00b180d242c8650800340c9000e04409080064100f80a010078200800c889101e1030904c42d00b041800e501d030061039076164030302810301c0309007075403111075840c0d030031070036202d0115840d081c00144180703088000d5404030b03900000e040f850961141c40b0080031310300c1142240e0915808000c0006210b07024402c00380300b018969400076880b8150b1500414003404201e08542640c1218400d0283d80404021260004504000050491044990312079507002d0742ca10780410b0300002c4108910541c02c810500300e00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 186527041 1250 186525791 186525797
    0x20105010b25020a0305060408040305010507050304080904150f0e0405012a030507180b07060b03011b0309021c24110d02070c03020910030203010e010b030c09130c06030c 75
    0x16a0300c480080d0458054801d05040b10a81d1079402d0800c00c00c011460b00610780090914860652603444045c6008010b54048890190005003007044c400301384180b035004140c9140080c65800e058075215510702820b40d040784550307aa800f218030514071090b00c000c01003200000a2041c60340e20340d00281c0300346d81285d050b1459400c01010000400c9100108603040c09024011101006a00411002850b0003002e6109200440104107515040e1551030402405149070341b5030385029618098043c6d42645510700e00a038100f00e4504106010010040300b00211407400162000080c000680301d03004880f4040c401c1031000001c0000c1c0aa0164021002032442d262500b4030007101200030300301c3d114417117604401e010601800c000d010860b00202840b07030042010f848040e132030b0b8000503141e19054401036580101190f003001182000e003c1d61180d0301c13500008100041c003140110352511560161a0720902032840080d001c020018405618290410307003d400403521008042c0081890310240e01c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 186528291 1250 186527041 186527051
    0x170f191b090f05010906050a02151014090103020105030a0c050d0e0a0b0711030d0b13060905010f050901031505090f060424091502030c04050402070503090108060306070f1d030f0a030201 82
    0x20b429042101c42c02c40d0f4040e0344040c202407800008550a0b041002d00b201103008244003050080650b1141a0240540c0543d00b2a01403500c408200e1101406c0c1465016201c202c00401c0940e07000b80c01d880d40417040400111b0044252002200c246c442d01003009d00080c41c0c450b88034920440010003100340791240880c144039440d604002e0f41d040c400b131000483c880c0c0c0b08011030200c02e07207140c20060f500c8101900940300d0111052000056a49681120f24000d03640c41c01000482c0714815010700078a01650940490f5065031103010a1000f02851490f882e03440e100814922481000b0780030039110000709982d02da0078107140c0241d5100100c5541c2a000007103401c080c80b203013014441d094800364050781c0032034549404131804000c0e400003812184012410f000c00183ca0f1620300040c641144510059903490541300700141480034003030200e600030f41c030840400c080c1076000401059580f0840c1803a13440301d0000550b00072032100409105402d40500070800a82c410002404c203803041c481e8000f803003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 186529541 1250 186528291 186528299
    0xe1213080a08030412090e24100c11010e061206061b060105030d03050702030901080705090a06080f37020f0c06060411090a0308030603070308040e04030906170f191b09 74
    0x924808603024411403007401f580858200c135402641d117201d202004202003600020640081c0180741c0c1d00c042400840c030342d800c140081080c0b11512041c42d020900b06030084c085c541d00851407078003d109500b481e05503401c2c089420340d41d610b400e0b544080303480f8000a51080f000944151901801c0c89110300a11980d10002c00c50740c000c0c040d6038800c4034998011030400410000444008002908003814004100300d248104d40340ca9454001a14040c0c071200e1403400c02c10040154004000e040c0713048000d100076402100200180c1c01e49e62007800f82044a0341d400035540d100700034483e030b416400c05d0391800240481c00c008045601c52107500c0888042000100d203900280c058454030b111140d001b5019041400000c12039009180c010170080c1c22108256101d030b49110701a4801c2c0c011080110700c20040101701607100d00500054601e41c5020b811040c4d0b1440d1001091001a10031103598400a0004400011f005444c40c1c4e0101c81820512421440d400e58085041c59840d40038000340d1600c01c046 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 186530791 1250 186529541 186529547
    0x6160309480501081603090b0a14060d0b0c031009090f0b070305101710090605090d05070c14032a04060503030f041502030d0e1509010e1213080a08030412 68
    0x882200c0041c1c41c0c1034070b540d4804071040c4080c5d00c4107204a00f4143d48120103000729181c0100c540c8100100c071000142c180401080b442c1000004046c94440c00804400c200010240032003c0c1e003090310501001c1d200d4a0311203141e6212a000e070010349149152400a00c00c0c00156172261820380d0280c0e0345404079885840d004c82c143c1e4800c90303421304250343c0510200208010014403840007240c100c02d680101404043c40c00c10380d540c2c0c80d41510203644800074000f408109001c03c402c07019940c03c04a1404919686661803000c040c450041d41c40500340c00c21049032000c0c00650b004000c060b9414220348129170002c0e1403002420b001d0b9008600e000808076050070b0001c1110500c2c60f000191504040c40c120040344100c0e1200c000d1000c41c0010721442d00005a1400f644075426440d0014280e00c00721001c5000722040010280c100c01d03810401c4a40640d070340820b15410914203c2e41045e654484505860b007480c03040d60000300d462084901200a0141c03040255000724420802c0c00001c0300101411 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 186532041 1250 186530791 186530933
    0x21c0b03070b0a030f1a04060803030f0a09080d09200d0b060f0d0807060b100801060c0f0302070803041715160e1804060b0103060806160309 62
    0x145415901c405400c0c000e0b001000c001e080d020201c3d00c0d010450a0282c0030100c15035980c4a5514500c0604e41c20b40c0003640380c00d01400c00a40300c0390004600b149021030241c101d500c40500080b2200ba600c00c20b040030f00c219035007125000348480d5801d1000c1c08061400c03d118006455009407101154841143c49241801400c0c41107504401100c0317107911010704101840c0401c07191360798031591000b00b0030000f40b01100580341060003150000356080280b003c0c402c290200307014030b500300008080148030341d54221640c000070940207180201d610380189026468406143c0000314288400f1400241d0017002c03241350741c0d0081c0c00304151800b4124030101c2c44010700c0300b581c91096581205110018061060204903540d031402001007000a8510071119100c1c44d044e942903c1481c0c1701c080e08201941c0600500c4020315600c0c004040341c0c98070034840d84000801c1c03600c00d410942c031094103505101544050f10300781c00c01d0700301182102c41304030218481101000000070540381010455502c0c02014541 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 186533291 1250 186532041 186532061
    0xc06061008071d060904060b0705060609010e010608060d02060c070f0f060f0503091002030f0f060a23010306030506010605070b0c091c03030f06170f0705030c121f021c 74
    0x54a410600303e1240035596452149500b9003100c005e125a81300c60784d850103140c004000140d540e580d0b0f0140d6040150400700c00030f00d680d000d542040010400207045016090440781d20345400c41080e111040040c800b10109403003e0b602444c04245540c2c46200412001e049900344052441e100f99102d40b10121500144034030f001141d81c080301346520a025100659000300e5035003e8640446c00309086408a0300291500205080c09904010344490141e14242d0012011200c0901e528588071111084400c06408140000f0310500d000d40e044e40a6040070010310f601ca420795020750f8407180b0040442d00000380541d01c450951021845032001b040031212190005401500003074403846403070039815034400048040550b1904049c0244e40e683c4114000b0300700c80e0107040c03200914140414600002e2300d180c500c06070407440c0c04000580c1c0006891003185419500822406000125542003110400c0d035a4501010101411114030700e9500920b8254040c002900c2030600e11810700c01295001c00c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 186534541 1250 186533291 186533297
    0x16350409050403090806040501150b090a03060f060f0909030206070f0f0e0a090c0c1704140409060b03060124080105010c0605090c030f0106050909010504080315060405060c0606100807 81
    0x10091040300440d4200650090003810448009595440c000b4074120003200c060b902c80c0d549415049580c90700c50b6407a00181109105242041c0040c400241202c805100080c441e0356106a80c0540d41c3c59500154010300d40d01030844844c40c0d6030700300d01010f0204018110014000c050014131054010307940030201c503845944100462124010548600803041281e03640300003000c600040254143c001c41c42001016134a01000c0748680c80c0c0f460403460140d040c0800c03e10244014000303000951010001070300704641c041203030686802c16400520b85500c0380768041c050300b0000b050602d8441030882261459150442602e0b0300c038501110704420a000b0180060741314803003040803460903000030750005071540c2941c10041492001078a0f000e9881d00c00c422a94664404200701c3c17400702c0180b6485101b001c020311152400b60340d04451440001c0c488401c86440d581c0030034080d1511f00a0f1805000c000e080d0039a500400b4810b40c0d9110002c8500303e2141c0c1c0000c181c000250301c60764105000d550320303403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 186535791 1250 186534541 186534547
    0x5070804081c0b100f02060a06140d020a1e17010501060909092a08060f1b0d060b071110020a02130207060e0d080709080a050a0f05031635 61
    0x98a440300300c0100c8031100d00b86544505144000b690f40d8241c0d111900c2894030341009002e5459406070824030000c1040c54a80e12700041004401140909440e14070700890391340312050314500c0028004040ca03080309001a1894094210360705a642e8070740243c480d0300d51014446507500c2002401d8075024081d0100242c000c201c104021380080d00014440c5100c0d507001120800040044280302402d60307608280f48017880400c0202c02800c1c401181c01030036060803c00c00303107041061600232102c2e80b821451024000101c610015001d548518068412541d41582d245d4081c14208a0b01c0940801d05105203541d6405541c2c050000814265217a030151050a58043d0149100e0080d0000f080c292900354848203822040c1d10140980000320003142c80708005410a007100a00d80c0c800c41d00304c0100e85d40481c480601081002680c1c0d140b05901c0300740004200c500e858414214080c206200030000ca0600c3d0744000c000f0100303244032100c51000006820042e4070564001c4186005805000f142420 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 186537041 1250 186535791 186535807
    0x1d03071113020c010c0206060f03030705150c04030b071d03031305090a11041502010605030a031202030c16060c020d030b060304060e01060b0c0c04050c09030303151203070b0603010507080408 84
    0x4681914080c032a820401400d0150000b203e42c00d41761a05081c0300180c002008110603813604222550100b4010350045003090541e80d1a5541da408400c0c6150007010030b080090285c0301c1c0d05080301d02550f8001c0700688282030414014050a050109003903030a0072900800200d800c0c0017041d150440301464415440700e280c002401242035020380180605038a50f4a8480d034507243c003005200502d803443c0c1d200743c54031580310001e017100c409402c030600c41e41140600c007010941c85030142184c224444070059890312070090340e80781841129668600740c1103d01c2d0344001d00441e5402035815041075000d030f404052802c401102150710700003c02e039015806201080100d003c1e80d105c0140c1d44019030000409a8070341c2005226500700380144c40f00c80e4002901001349050a000b200d8025140d002058207240c42e900004c2e03100d02005041041070942883c0868090380c40050b140ca1885482c1d09036a83d440307a6003441841d0550803541c00b03000307600309004103c041e4820151140300c1e90304944407034148001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 186538291 1250 186537041 186537049
    0x902120a09020406050d08040302120f0a06180605090d08010902090105071401092406060c020105030610020a120c05010b190b0c150a09050d0806011b0215030a1d030711 74
    0x1044500b82d80041d52498003081079200c1e40165003400703000e00026502e86103140b04021610101605403426a00081081c2c01c00100004854003a40d85c480008246030304040d000a20a40c0d280e480a0600740c280420f0210501001c95002c014207400d03601d8a109a0300e55030000b0903882813594080c0052820801400481c541d0f0502031424081c03000081114002511082c040c0c0c021301524070021603076030f00013006008041c852800180b038a0304050008240c0c0b50006007490100400943c0034024461992800500c2880340800d0982d104100e000c041400800c02801290751040c120b441d507282941450052901154284004411030f61300381509040c010f500401b60032250703c4138003512844c0104200c0f03e211021940c804c90044a002a0605140c10300300c1c0f0b400180301e682d00502052200b40601a41c0c40141042e40325200e0314041d104aa981c4085521081c4000280a0160011040c4000b2958941001c8203500400b000400036800c6008001d4880c4600c1400405282e181e040c2e583c89410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 186539541 1250 186538291 186538301
    0x9020a150302040e07030c1706090705032a09040f0e06060424060e0f180123120a1b060f030b0a0504020c010c0f170c072d0c0902120a 59
    0x400c40c9000b5050968a4186a6010b80150b9251011079106e0b00707006042a8080500110710700c10020240741e03030030401d020030002c2e000a001a01017200020000c2d4a01d518034115201409030740c8400029013174003006145003504041141c80c8243d04200040d00410740c0d40c060b88079152645405000540c81d81410400285030440d58002d418080001e001692503240c07402c0c07002040d103622001c5580e00580e04000c42116031241d40d17440350395140d0f248240003d042d0745060655800c0300714181604a04403c00c1044089007220b240c0c00382d40605030022501e00031079020640d5110b250000d07130394400403d14004490003801101c1c001501440398130b102c6031182e04482c810700b902401d014400364803040490241d03070050030325640700c0c0e4594014414031a805043c0b100c0c52030541c0381203e05011014140045210702421203102e1503408a0800248020ba00c45c0d020a8404a1000e000c010040c2500011044036500c080ea20030452144c0014912032078000c0758510704c0d200c88482850343d039561041000780 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 186540791 1250 186539541 186539579
    0x2070e010506090f0603130c06080604050c03010608070c0203030c120d0c05030c0f16120507140715050309012304050c0103090803160210020406090f05041104050d080c07030b0108060a09020a 84
    0x440c15001c1c7c20118403a146a0406043c955840c45c00624094083c4800d03608060040d0101c5041000100310070342e88204040e41040441c0383c142c2e104002400000c0c51405039800d604218000c40104d01c1c0b03000e400500030110000c528000344410385015100f600c15002c119684001088204000d2001000b180020300e001c0036506660b13000c0c440243c40700400300700b0030f620007404200c00050000034807420f9814212010071500003032868a0420710710441d20070255022409204002c000f14481e040c00707400100010403c0446079401c0c29030f490401d0b00402040c1c0e420340d60307800b40d5185000e0651003402817090700341d00320500500d55158a40d0045290511210040c11030142c0d010030090030510740000c04c014101c0d44ea07451600740c202807000250f402035510640c03241d813901d6052030b403c4d001300e019242101d00031640f0740c4660715103040141d803d1140c07102502c0381c2d00600f0008020850510801d6040e184040b00b00d401a03503501419108644546074041d52012000300200840b1520802c4c0304070b66 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 186542041 1250 186540791 186540811
    0x130b0109260106090c0806030109020a0501030c0e030a0609030810052202070510021801081003081e0c01050a061403120c120d05010501111605012d02070e010506090f0603 75
    0x10701e8041030a00d084a51640204038004d448003c194038031a4429a4241c001070124007c01031280a40d0009411000e2403084906054582c0101c1c0b0701d5600801580c2c80070343c00030b01560f4000560f4079100c001840f401b1021004110070202040101013001440c1c82076400203000c181e4802409030310000c20800580e0701050301c42d000c11013580068000c0c44910002d009440000d0f80f107038135100d00d030340750244100c600c1c5040100c01010480d2036603080b4920402c5030b4000001c60394a0006502e01100018211190100560006a584803000c4154400d40c07141505041c1040a1074480030510045200c10a5140d4140c1c800720342003038423048540052012180c40b8086501e00400d2064001c020b40024050040640e42c03040100301c20b50700440308403501d120b40c00141c0340c503101017040c3c501400c900f801014100300d0706404104e810040040940102d8885404010640d607a03058001d5840c3c0c082e0003085000000c0800025480c18440240e0302031860044c005842900400140846a00024424095 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 186543291 1250 186542041 186542099
    0x8090601030f0c090c0809121c0903020111070803010e0a050c0910030609060b0d18030c12050d061401030b04060b0904110d051602010e06010501080c0c0703051902130b0109 76
    0x40d40313a41c403880b0380400c015101c4c151940742a4000c242408001c0301001081d02041040c401d001d8188490700c10100c80381030001580641900301240180f0550184c43d2404100041c00740034804254095030413140400d07070700d2030b07940d444510072000e9034015208548500401d20038170049181809070412484894500012110380d14101c000690705203901682c08005d00141700c9a4095803401080032900340070f0600451000c442da0000e02000000710090420a4461020b4a04034451411503054498001c000e02c40f8607194001c0300181024050602d0103c1d250a079041051700b000d003d0681241d43d510345040c1095241020f20001c0d00c44140110b080000410101c584102e003440b0f8140604007000b425610444482c02c064211407d40700004140e5100800420981ea440803825a015035800412604d95034000c618514203100c0350002000c07030280100130891700c0c821200c480007190080b0b801a0f04440c00c80e070440d04850903e504940000e010003028440c5d288089040c004040c5011802130b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 186544541 1250 186543291 186543299
    0x4021c02030c07030e061602090703020c06070503061f2703050d0c02130213030602090102030c0d0806030d110c06070c0306090c24020c130e16030203070608090601030f0c 75
    0x20032688100c800c03020b400c0c03001c07651906059015000e00c12001c000c0d13030080d107001c2c640c01011800484180c80240300e0040d21000459082c82034041d1210748d00003808035815801d00c0ca401130050307041140d125000390300d56039110102444000d0442004045a1689496907810101d04545080f5401d0849200e00c503240f07002000400401441c245041c9942e5504403078045071040201c0d0342d00c3e98601042250040c404900e6000786c40f034060b0201c0341e010f007005030307101aaa00182e056000d00a1000142d014054142d24000d4100102510620080301a91848810300c5002d48044203a094081c5c11a400140040710314200f80c0001d001c09030103150880619a582d65442050b1054403504031888440e1703060070003541c214440c203d010180348202c070400f45018010001d6407090070902480c400c00b06818514041c1d940343d07000781822800a420360389c00b15811881032001007081d1004a010b031091007000031700540300d030400c50300424260018003500d074a03640b1041c2c0240140f0b2008c0d5180083c01c2c07070001b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 186545791 1250 186544541 186544597
    0x11040b09042306010f0e0106020303090d03091113060602070b0c15041110030e0c1804030f030f020a0e090c030106140c031c0b040e1204031407080d0c11010c110402 72
    0x1802030901054174903026003042450b8208046c10780c02035003554000c0c002e2003402d4001017001c500d04001c51900060203c41401c2182c203c401b4455121f802c44031030103070200f0780210340c0c0041040d9141c0740c080383c05203642c40c61801070b2031250310001d1034180c1102141c400c3c08120310410701e40080c000c05000d40098120741c00501c00440b00408070021a559009400c46030740280b042c0700c0c2171502100c6c10380c0c41d00c0c4140c008100609009000400b00301c40b401703041010a00076484070800700c0498004646526050340b0107001c1042d00e214151140b0b00c1e6200007981c0025100483c1d0584030b860f62152004462400300425582104849c12100e00042c80050351a42024140b001a0000710201203450380e6010240030031940044100800340d000124008181540e070303c102c1e401c60360701c80140da000d0712040d0705580c02c100c0e854004103200d0081e0692010201c0e84046d181d8103480c000c0340c44070541c1e01404d00540d220007142100a161500845442004e468258094a070910000d89400b401ca0701010050b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 186547041 1250 186545791 186545803
    0x30c0d0503010806060d02090a0b0406030834020a05090406020706050a0c1206060807180302090c03180601050f0d030c060501032102011a1210150311040b090423 71
    0x4400040d00110040005500401c0741541081c000d0b60b8031107042e40a60080340c0c00381402001692601e459411480782c40c0c03034691000c0d0040d07800c50340c2707da1a0f00386d074a04d140800f5130390703c80e6440e4866400d8003c02d003c2900c1d880584019802081c0281c002e00d01028804001e1000b8000d40f40b0aa080c005000451428050382e8400c0300031000c0090348082060014011004040c0f203005207a25005091060b03d4000ba07080da045001400d200700b245400e017015035800c130345c1c54200070f40104404e0280f00310700c80034402550041141c0040400920350004070f080e40c8140174428503a001da0041248805802c0031801460903c0c024581003a1406c80c0742c0300d210948100ba80101c034880c030f0180e03c451f2081004450300e05080340e20700c024410100d10b80c41844090300144020ba09c01c001c0c00c01c494220038010001c001b404e0342c1d074500c00d03c0740f200e01404400c1d0443c41444251008040c0c20707080c4031a80b40902c9100703c40300004002aa03e6200c580700c070b407406500b210311880001890b0002d050412020090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 186548291 1250 186547041 186547063
    0x120427021201090f0c090501181703030a2d02030c0c0102030906040212010b012703050d0f14120a0e030c011d0c040b060301061d130207051b0d020f03030c 68
    0x11910725454041000200d42c110b00d0004009803038000104100c56128201e881201c10900e04401081e1041405600704101c0e0790140e03080391000581704000507808000f441c441c000f08002004455180005400b81e441d241303040c110028011004041392200a9004d160007401c241c8025003421181a40c0c80c3c2240e1098440e08440d0703000750104003c52404040e214101400c2c00003e1003119000300002e8042c009040f854084050340500321980801440c11074001543c1050460304106013808010384003c25144038803000072952048141e160756141d00710b91000001107511070080d551001c52000400c0444a11091800204002c1d5500c540c05d004010180c040805044120404103146901e0200c440b00038501072404c1c0007812807180d82e8103082e00e0440e070890070a00c1d200b60703010108000c1a4510004203510109144072001e20080903406410389070700c28012115450001c005650a805016808550004c4021820341c0181400d4610011000000c0c0413a4200903029140504005003490 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 186549541 1250 186548291 186548317
    0x706110a0c0e0f070e030a0b0c090a0e01061722060b0a271107020d03020307061406090a0608100b010c0501091410050c070609050f06040c140312042702 67
    0x305024418440c1c603c481d4200e00141080340b500b000d101c0100c1d4480082200181002401d000020081c000400880c3c03260700008114410003600d0b241014a5100203026450000700845a24110004030041190185021400810801c04004c100407501100e410040381c150351a507050b26000d840d86810b100180450202c0c000c2c4044e1000340049070310300e004501c4910035007485050301c00d541034801240c41554044c0c480c0c94000d10a400c0c00d034610b2040c5100109034a03c4c048002c40c0b06040220a24080c03030048a60a4264880d03c0d2490192090340c0291007840d04204001d188903d295400355080610605200e00b18480d1602d80600f19840c030304041c0d40050b00c2642e291003004040c0640d032004d0100300010011400d00070f13003040c00da00031460b00401c104d80c0e4900141c140034041000704401040c85040703070740c0c0c0e01d007a1510103850f04061040050303101840c42c0850407860040754100120200304155810245405051944002c40c07819550342d0280000b01504081c0c094001807400b41030b144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 186550791 1250 186549541 186549569
    0x114190b030106020f1516210615020d08060f031e01022107090b09040204080f010b1c08071b050603011502060a02160b040201050c030a020109110108010501020706110a0c 75
    0xf0602074282603480c1031020103500a410b2100341c40b240c1900b1540c02c0741501c005141700300e44400094642c90300742c120100306610300f030b1145c00c60a505038008500f901c1d903814108030f065400b100c090303940d04c4440e995207011034128000180142800d0410407a203800060403200c6c0d01440b00092020302c292110041d51503500010100d030488441c240c040c0940302e00b000d03943c1951400c09401842c400550082c0c41040310b0000b81c0030300c1c655451b0142d50250609109803650040c00540c1c050080150111a600038101010001c0c04a84036901c40800c031390f0482c034114030f40041c6640307110780e00344800201201c0d00741c940400318041d100c0c4009540a0b00f8012823040b0305046000b4060301e81031004010221990042140764642c43d0911010406180e20420303c840e25102c03440169418001c9807200451032002041d8040d10a41c15000318414901074001c0d4501402e0510046603400402d0003180d0140c1d001e9070b0104001031161344900001c2010300c0a407039202c526035461859102c816030201700e20000036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 186552041 1250 186550791 186550799
    0x130902040b10091a03040b0c0708040308030f0f09060601020309040203040c15021015060903060e10290604030305031303091a0a1701080d1805042a03140114190b0301 73
    0x1040125007041281c0040c0c11031900e5038450742c1d81c103001850040d2230f0a0104240c020031160300f064a010b9a0312082e020f482c0c0c901b0b08261100c1180c2100e002041c1303001000031858488021400307902a01042e4090f6140c039030280c080c44042e510260003140c21108904000885d9a002c00d4510b01c2c1034001d5015100b28006000710005540701c240d0090103516810354200811a040210a0f040300d40c4408040ba0151003140c900c0c4c10b1030640c1004081d0036081500b07604680078060440601e140c4240e15070152212b0749003d0048a010318080100428001c10129159190403110740c00424800e16021420903198003000c2030040703280e01680a0100040394041c1d020350400c00d12442000c0c3c811740e87c5c0240d80343c40d9060760340d0fa100c564a102030220700d9002c281c420300507003013040240c80042d00600090740b01754803202440480484144e2a20b8611032150003151003030080fa0110080c408100507182d003000a150300d022080c0400b294001c1c110304601003040d120703151800003000d5486030161207600d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 186553291 1250 186552041 186552059
    0x30c07050d030b0f0d0305190f02010e0105040b070e1c0b060405010504090f03050a17011d0603070b1804060801050405100b12030304081812070311010e130902040b1009 74
    0x44101c1032014581041828072481e210740c004e200ca0480102d400c5242e0482c2800c00b55283c0c86031400601e00c8044101ba00484503070440400c0181c01c8450340200b01d2011400e0a641c201c41d0243c4004040c0d03880d100c080b6025501c50040a01042030081a065403130b41c180c2c912464828503050216901545c2c031040003078902d01449168010801502c01307000e100d00f01e9490340c91040d080e07480101070040100f18030410314428540f090040040600c00c0b80c1c01e584070a8038003048082d000e0140c00c0c0741d82680001340b4070b0801048143c1102e942809490034140360004508060030001649034000c1d69500340010021400d014403801580100090301c0176400202d0b800050b50700c1c0c1041540554400b80b201d00030f0000c00000c80c0e5029030402c100c03645582e064004218000020000c0703580c8880105007840f001140031980c80209c0c0d100398403041c6294035840c010345495505042895201600700364401d005481600081e42c00c0c1d08c0144001044522080010084400350008000180e64080c0074403401103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 186554541 1250 186553291 186553303
    0x4022e0e0d020117040510060e0405011b08010306020904151706060f03030d0e010b090c131a0d0b01170c0406030621020d0c03050604060c1b0c0b1c02030c0705 70
    0x82a00d007900380c0d24482e00041c0c420b00c0200c580800c41c0030242c1c002411700c8814440b140e0660044da50901074240d54819420a000702954180c0f07155203003d0b14203801200800104140081e16211543c4a0f8a15280c1000030340112141a822644800e092003845103190b203804040c1030800d03480d540f000b945d58486031404200410700b030f005114406200d2080da60010980b40719114103940840e4030702e1094200c0d80903200808549070410203240c103114080d007205010b0200e03480703602d00303220300320fa0340d01c01d040801301401c00e4400e0725880401036020700075180d070043d21204d8010706050803da1002c1d074200754060404c54176000c4599020400f0302880d81d140c09504002d08010359542098043c00c1704440c01d1a041c1c05c0d0081c03040c1d01c50343c210010001105281e0b4010b5030400290707200c610300350416070040e111440d9080300048030085000d041c1402796a03515003041d00402140d1400d420081d80d00d10301ea00c0340d4080400d00300120308018812000740000d61107000c0f0b10103001d0b1500e402e0324146140c50 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 186555791 1250 186554541 186554567
    0xc040305010c020d0504090207020307053c1807020c130b040b030309060d0c140708030a11120106031109040e0102090301050123090a0e030705010615110309060304022e 74
    0xd01300381e2003248000d07840003d80307058441c41c4d8801030741d5004034400a45098555072240e904811840c5410190060070303454840c041440c0b80d4000c0c40c11051850701551003528803200f5900500c049011400600b180c1c2019902c2580c50045440d480c41141c00104201001250303103281c19200c0c40160403a080c14029000d4a0b2410340c019400d01000d00c0000d02c003401002990301029582c0c1043c01070862003a845c03c2c0003210881d14880da03500c02c07420049440d0388204d40d4021a40d00303107001c0070158680b4400701c031400e0714800040941c0d6428441c045000d042c00750240b4100044c20300c2204030950340c500c06c01c01c0d1100c400000680d81c4076410245401c0d254142e01010100ca809126080c2e05014401d42c01d00000003114403019a0f6110f203110710044c2600b040c00080340c4008680315042040c150b1144050b00c056030046240a60091011100440c2030000186190070511103425641001009190402d00c0103115040211900c66280c0f440d400c40412005e07403861050b00298020380000c817070745d404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 186557041 1250 186555791 186555793
    0x1504060e28200a05040506030a02031b0705030901030c140a0903120c12081f0b031b09010507020f060705060c0417010b06040e040f050d0504050103180c0b0a0203120c040305010c02 79
    0x2006008045a001c2441101c00c1d90b01c02d000042d0f0382e00c0051058007141d000d004000c002c0d64482c140420080d00039001101c2d425501a03e10a0300d001180b039281c10f4134103507a4440000c62808a02100441c003503e00882e200f03003407009a04074818040109409401d40382c08581c0c40303206191460601d82a04150b0b07824827000d000141280001103100c0c2e01d0500302d244070390305001403140c0392500a020300750b03c9102890101d08140c000455486801d600560241071100300740c2030442c40710300c3c40000a10503002c81c40d001c02c01c208003610040c103004a0404501c40e001346400d061903955100d1500303201d412600001d00c02c02c00201403040950b0640501d01d000e41a0000308030510840d4040340d420700c40d5004029252000c0c0e0005020403003420078400c1343c41e503c030742500c1f031001d64480054040d8002e402942c0c00f00f420409450070300000700d203c00c0d40791904001c0849140c0e01d001c0f148542da03842800d2480440c0010010300034445800c0c01030074094403e00313040c42e41d42c6207141081421036075909900c02c11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 186558291 1250 186557041 186557051
    0x20c01080a1103180f0d03020406120621020301020409022d0708041404020c01090308010f17070302091308070c0335031515032d1504060e28 62
    0x248000d86401d40e58011509070095074000c1300000d00f1072600d03900d540c030030700c07180302c0c03030343c0280901d0342c550040e100722001610b8070195581b4444182c0700b6904c81d4021307200a4525150030a090390340d10702e02001c0c06070015000601d030584139411001603034400411450f0341c41c100c480ca4524091410102031550b80c400340c1c100d04040d00c81e40c1e18907007885a403084000d030301c4414500d4185a0703502c2c0c1c104c6290000740c6000700010001c501c0c002d011b00d8000d200f5880b4410516030000341d030380071110426403c1081c6038080e11207242150708100c440000079100303404000001190302d000034100030007003030071600075412122580e04d10710301498480074441c51400000768080c0000b044214804900300d1046a80c40f440392030383d4410301c103034400c0d00d2910107050740010585044c0c2c0c90010020021b50241210b180b4095041201d004591042c2c00c0c4110b0518900c40c40f240051740d40d000078401184034000080001c6805070b81d95081d000c90200540d2182c844401d0700080700f001100128044c01c02c000810341c2440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 186559541 1250 186558291 186558311
    0xf04051002060115050d060503030a090801060603150b07110901121e02030d030903120c110706030209030a060507120c2607020717122a07030b0c07150c020c01080a 72
    0xd492803282604e07806002d00490031500d400c00a80003800904400340440c1d132030b4600305100404079a5544241c51155203001d4012910a11a00032404081044250074a00d42d140020400c81507010b003030b00342c0700340201c403400e41d082e40c2d110081d0314000c110591401100724103500705150541d007600c0900c0911100b60300c40740016100406ca40d5070340030040c100092403002e1420700750b8103020f0300055a003009107800d04000c40290088070112850070440210388440343c0700c00b1305404903c1001180c1d42d060703000510312400504a50002c50784900d00789002e07400a50001001420b503810001c061010800620b0460380c40c242001294400c0300c1500042c401904000802a485204038002c10000c600c00d82e03c0740c506004200b008154410a0681c02552040b2850042410710503851701d0005401403624a2490000e0000c1d0781025603130001c50320011501d40340c4014119074440d20003260750842407105444905018822140c211859401030103003119004c0c00100440c800401320419207241825040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 186560791 1250 186559541 186559559
    0x315060906051e0a1503230103030206010b031b0d05011e050a170a020a0608041406011a0702121c090504050f07050a05123309041106070203030f040510020601 70
    0x703102072240f03508041c95000e80810010407071030f08403100d151100c2403000f180325030540c02001c42140c54080480903440505050120b08800e11028006a005030014040942840c0c003c60300804d501c002e10031800f0b5594005401d0f6003090f0701107540c1341e60f01c800400240d04400c0180c0c01a003001c0c1e10954000d42000c0c0040d0b00c100d0320f4064040d1300404842c041d0581d4604020803044103400802209074640d407000c00a1202208640c2100e10140440761501c05510002d400c5042e51440c5985050f6000e144100c8409500501c4050364880f20051181d1403000042c441070ba282e6200800801001d240880064400c40c19544020f00072403a10042000010206454580041140ca041035440300240c0c0d048a060040e44120618448000103001092a41900303801c968411044200c0107020314042410682da031000e8411781109030380000500040c01000f0750b000051300204001c0c20401c25801181c0340d900003801d00240c070400054184100e24111800100c1d17255284010034041d81812160 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 186562041 1250 186560791 186560809
    0xa14070f06050c0d150303031107050c090606071a0609060d0f020904170a110d0912020112061802070c05040b010507030804020307170a060b1e06180406031506090605 73
    0x380072141d445010408016205084405840a0749014403075110841c030520780414907480214042440c0002c80c1180d520050180d810042e0024081c2c0710400c51801800099240100103070340c409000c00c410380004130f040700500c10b0503440302042581450721070180700e82214050040361051032007a10840c00104504c200110b403540c19680c0700460307240e07803400e104410302103491010310b80000308005582030780c080301d0180b02c001c2c60402c49500d54444882a1569002d901030400e50001100e8800095409520344680e810851000091810380c0d40c3c0112981ea0040f40c840710000b0340009080b0240100c03030032107401078a41150100708012102001a2540c41000001414888004001010740da020301401005000301141c0c60b442c0b00c8240d2a440d00d9295090041328800d240c5045072840d801e0407040d01a030014040301c442d0395807000c03408005060b0003101d0104840c6a500d0000701e1a515940122030065115004510000b07101204590907125540c00c03c440051505004004550b940c0001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 186563291 1250 186562041 186562043
    0x20c0108060d03030b03072105010b09040c03030c1704080c010809030c06160302090a090902010809011b12150b0417030c0c040b060c0105010608090f07121e0c030501020a14070f 78
    0x10000d17481a00d140403070304201182d0710039030001c10003020341c0d1320a47e0403c03400e096141c800c8000b00901494041080541c000c01e0707030050189000d400062001a000e07070102c00d0900e00802074511160031100030880d2030b034416041070005401001c40c40503103580144031160499111805036003029036159240780d40e0070004200c41040245914900c040728020344c101c80301444007410500392251146100400b62600a00490000b21003500142001c8010312032100401d14961003c3d43d00181968111005000010607010440c0c0e0b8001300d051084004205000a001c0020100d07251858440c8806041c5c0b64201a501076030800c00400401e000c0c08140c602c0080e50071200007550b0020702020a00501030000300070078941c40c05001042c4950401d40152190030520100d805507503011100300c0c0c8540031441a103441d441d000d5042c100095166030041148442100820a204141e03250440301500e80d030310940780c503503000600351712481c0e2240142000a035862001032500c031159030b0b580303070000c00040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 186564541 1250 186563291 186563297
    0xc0f030c0807050f031b0d020a030f030e0709091a1005190b180a0f0b09061e0708071208060619020c0411120106030915090c09050a0903020c0108060d03 67
    0x16100400c94020181c6602982150444c0d690308104c00c2120341e40d40c41906840c03d02d4649003030203441c5810004207101000c00b5903010713143d04072281c1c0d0250b030b02032480c0700b5410a040c0c84010441e40c88004103c203000810302902c000c10032001d41e041003100600b02d800d045010100c210f04012440038504013190803610140d0710101882241d680110160105802c4074542a500180303019200100f000c28010190048404040065031480380b030340380032542d11a00650781000c0c0442400f9241c0320006c1c100c0220942000701142d000d6000c102501c1d070222104440c0360710040344020034400c2c00c580a070360880c018180210340c2d05041000a015010385050b14130200032112030003550b50310900034107a03034200142040c0310b00c0000c1002c2802c290019400382c0040c00502c800090080d2290180740019a0080403028020301895044000741c080124140c41102c2c880100140a0007940700313180c0f003070014541c0011418800d00d0001d040400300c001c254100007110041c0540c039a140381c1000000795141c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 186565791 1250 186564541 186564557
    0x30c0e060d06020301030308070801050a140607140304030c09060b03240a05041503050f0d08040821070e040b0406030809060a021906091b060512060f0d140d0c0f03 72
    0xd000281d80e0020030400901c10b60020000008064200110b1401101c0b00e03101c44520743c0e00e030400c0c00003062051203020000007a0000403402d030f0621074000c1025a01515002c00c0900c5542d001a10316849640b04503525081d440040009142501c40c0d0b4000c0c05082a05501d1400c0c10100e01d08441d4222411418118046200c3da02c1031341c806646400419020748107100140c0c2d989040c001c070f2817040c40151100c0c055032025102201000c40c4030340c8415029200e494050300c854680070301e15003010b4400c40e80c00514181d0945404091036145100d0f40d030390f41d1240213402602040c0030580c2d560307100680c056418000184002042101030b18807a07803007a5409612001481012447d0120907100d40c0001e010050302e41050202d43d40003000a207002c0d5840b40030509468411030007400c45482500d00191051201c864400040e6186941014000788401e0059550702c001a058100d80c000c110b901107039001c40f5010314042400050401c80490604403560062512030040122600900a0421100c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 186567041 1250 186565791 186565801
    0x30b06040c050c060c0a030f0209030601120f05150402010f02160b0c19060c08100609060807170702150c070c12020d081801180501210209030f1005060901030c0e 71
    0x1e002990031840c1c00f14100c50141c240250440b02c150f200c904294002810441c040e0714070184d40c0201c407032a80014008000781e030320300a0466412405c504040750300c0d6034003840d000c0101d001000641c0c500041800c18a0242c1094400503083c908100d10100640d08400040c1441e0641c00000004607003a1980090740c0304464070900c0d0420f08a00c40424507240b074410400705000709603100520440d125117a81c0c4207038550003500300d03070a500f6106010000d655880709000719032084485980000c1c0707606010990b4051403100c03600000003240c4800040e80700c2c800c1c91007611041c82c2010340107072102e01603a02e0b01c111a113070400c41003018000d4030424404d0441c030100715102c42e03001c05005500f248104d0748500782116503010250500c0c04050014103410300c5803010130602285a02240c81c161a040d4402c2c010701100c02d60105800c50400904d41c0c00d12900707006440521a10400d0308a22000d401c0101d400c843c0002141c1c07020301221302400c001401403000032007800d0030354156030b10070b4400490f540da0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 186568291 1250 186567041 186567047
    0x13150f06050d03020102030105040b060c0717071d0a060e07020a021207090212041203060608060d0c0f0906170105010f18150b07030e010c02030d03200c0c01090f030b06040c 76
    0x3103900c0990052580c20980c410302d513043d13015505032441180d0034000c015090f401c20001c1c0c0034107609440c03140c00c2580d04000b2500400c1580c3c112860039002d8610701540c0306c14100f642c101c0c03800d4014502c072078542001a0346140c0d00c40e14018103c01040908607081c880c50003135450014034802401100032200900900c80204100c2005100446c0706540c0c1d070801d9102041803040a446c00c544901c2c40c0b00c0010301880c044d02804050307a1103643c0e90200c941d541405c200781c44690f0b08055030307988001c20340481c0e003c806901d40c3e40030b040d402e400462080c0c545180080d420f00000b000e500e40d80d25200040c0038070858420020111104204101c0988406600d40001070075000300750945009151000140e880580300509443c80c000d495025992068400540b800004040700070b6058100483c40702c459406079000201f11420131450360031850060702c050515a002c41402103065000c0d44882242d90790007100ca42c0075103041842c5500161131652411080000038261034421900c6424003110300384 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 186569541 1250 186568291 186568301
    0xd09120c080607050403020a060503092a1003020c071a0703050327010f0501050105070b010e13050604080c0f030408030f0d02090d030903060c03020708120a0e0708011413150f 77
    0x346041c10340e0928140004003401c81d0703000d40b004034040c40149000146140c05001600c1c822182a0058a00961107221030094070282540c081c3c1203104c2c0c8c0c8061105501e0380b94088a0f484100c4d00d0050740c5092100080345000c0083c0d1040034a880400803a40603660300701c00340d035080e640c0341c2005a2252112420080300e4400b2100c52000030540c2015201d81c0241500040003403c0122810842640c94500440e03091046000c00b074284c65054004014001d00c03040b06d1980700254802566110240f82e42d030901f0442c0c243c3d01078a0880000c902040c01c80402e2182e0030f404103100c0025031800b403800d035555841e8000c030304104001910204a43c423091030706404030380c2c1a290042275088506550316000d44010300741d01096561524240a18020364002d208403910580c0192585041c900b14815100c45a4801482490501d48580c0c0303800c1c1105c0108103c02c041e111040000c208500036286800020764003d1105121442200864ac042a00300201d176031203d0020001082ca5801408090082e02e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 186570791 1250 186569541 186569549
    0x90f010302090d11090a0212062107090e011107021e0d0b04060212070201200904090605090d020f0d090e0402180910050105040b0f0d0314070807060e0d09120c 70
    0x2a8142c0c3ea50001c0280e480c1c1e140080340012100805961100d05d0200d049009421041003e0906a804600e252400000303034a941c8003800042160200032562540c2400030340e9200641564032009803242207070003800350120f001d16600450303040444580001c0c178030f4123999124451102e506d40c03008650381c40f0f203150781c103107940c1240540b0014103151a0000095000000d0f040d1019154004a0340d0070384180648041036500348041803405815410a001d158440108103502a60b5241c0f8000056514000c9500c600c500c04050240701840307400c040c2c01c04801d2410142641c02c80341040752600d410940107016200355964040c06541c0f5403000c940d424000c041d50001114000c000c110511000141c00e1075841401c403810310a59a039007040c00300703031146410305507030102d10084001d10742c1c00c00d10020080c0900138504905c441c0901c80c00c00015a1003480c0590b24204001201014020706014440c40a41d00f00000d01c44d1420050300180900c1e028041d01030720b0f00a0201d20000e000c1d400b540d4002030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 186572041 1250 186570791 186570799
    0xc01090f0b0403120515012001060303020309030d230f1605030405010212091005090d080406050304020906060306090f190203010e061c0809010f050c160f08030708090f01030209 78
    0x203810905003403080600454044000880c603c00a101000c3c441c01641d01660b0b2400d50b0b003e01e4240407006541074442248141401541405044803001090060b00020740c0241c000c0c0d9500c251031828141403603610481c803014054420240c101d0728941880d851180074002e41426101d880340e0344400020300c10890000c0822000c4240307075003480000302c003c100300c8200b41c080f00c88038148040c624949000b605103056005a90411902009010701700400340800f0007072a10040041541d10b044030b58102c0d8121a0000b1800301c10001182070030115250410070440b0395a065190a0002449542000b42004802400c04003c40e001407020360303030305406640c07550080d52a903071039901c0300c42610021101d01d44110201003501e072403140d0704401c00300041e400070410f0f45400300c0c0600568004074418902e03820440e040200e2200c8003414080300c0414440c525414907403d01c0c061054165003480c0d000300442d60801c114900019844c001201c40101c0305a480d0f21000d025400141c00134091200d550b80c02c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 186573291 1250 186572041 186572063
    0x2040209040929100b090603060415060c0506010605070f020d05030f0708070209010e0705071b090f0c0e0a0b041a041d09010c02030315060309070f090b01020f0f070302060c0109 78
    0x801c0d48220304403c400e40c1c80680200c43d40d59001d40c0c1c800d081c0c0041c8550304c5107030000c12200c101c1c2c0c140b01000310307400300d8080c10205101a81700100000074950780d10040c00100e451400c00d04220f030601c141c1c5e004002502c3d00505200981d240d020300810a440001c1c480c4003450004420071100348251045014a00300441d240d146c1814088102d40c88420202e01c2048200700110300020740d401c1c09070050308255191400c101d80c6640700540c0a120246021004103001000100240140036800001043c036401040844000501038400b120060400313200f90310541003444101c0c0c03e442130301c1c1100c02002e051010901040c04a094620464111490b40700040c00c0359840c1402c41c0c1e1880d400340300824000c1007114078541e0100c0c2c490109891030440c01d52416034400d15840e00704055a0451410001c0e42d40681e07030388000b500f0b005500d0344030b1a881619210581c05075a014417600240b0036030600030b4801080c507003200584402c21404000d11546010414500a003003d40c03010020030b520200100f4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 186574541 1250 186573291 186573323
    0x5010906050a0324080f0d080f04030e04050a0209040c0c17090f03030d020301080712020901050d110907090501120e03041703070f03170108010e061603022802010e030f07020402090409 81
    0x42c0e101383c10301940b9500e1040d010307002e0764010009080400e05440f03030348444d05a240d0380c1420f1a0154050411740c10460002c0c504c0d02c0e076a4551194601905a04c000141e60700492028442130300c0c103145089c4203000900e084200400d01660504030302c1c0d000c0d010819a1090035030006007036890b66020450301031002141ca809120080d6006506030b5480d10108c8210607a2180741c041d2203840614020340144080300108020b080115055815500c9120746c5596044490b010496010040341c50000203403450b5000c10895820070788400e10710341068428086842c003240c50603501d10a038450760300c40d40ea01036440200c8400030710903144255440411000e140b031441c00c00501c01900005c90000d008081d41c00051140d00c14072800f4644000d010141c000c070358500d986002040c09803201e03602072540800140300305e1407803844829028201481c403500c0940c0702d880300908540c442d1390b020300070b94802c00c01030004402640903280b4070766045a02503601c5500c0c8001c034019201020005080703c3ca41c8180603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 186575791 1250 186574541 186574601
    0x3030b190b031f1d130f05010c08130201091505090901061718061308040b0c060a1a0109030f0203011d01091203020306060409090c030c03050618010605010906050a03 73
    0x15004031040801072800f48101c0c0c2e201404401244281107800c40c144c1c4000411000480c0071562020031011607251524698845002d6280100d1080702d10365514071007804419080080031341c000c030854103940c00340710881d800030780803c41600a03590064003066220748010b20030021a04000c0026101144c0d81d40e40780009022042c9480040400344103031000150314180a00c426242c100b91071009140030384524001000c0d80e400c82e0030a46403002c0801011458452000c0146814400035006100500d44803100404450a0241820801910b2003204449a074400500000c1e030703030402d41040c2c05280c5480003a006041514100c400680c5100d14110300203019400340302c11602507041500d280e150b13044100c04900c01141c0b040d610a409000901409001c5d520804605220301101415603842e0b4440c0381410406138400c0f03070f032a4007000801010320308000107031318200c10000c002d011050400c1e0000e042080c00c0d02030740003084008240303000d015219400515003580d0034003d0b400c900342081c002c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 186577041 1250 186575791 186575797
    0x9120f0314040f0308060102010908130806061f08070314070309030f08072c061201210803010e06030a060608070f0e09030405010c021f09030209130201020a03030b190b 74
    0x900100e49001c1c401c10050244441691140f68406840c0503042e515580030b40d4011809006d590456584007149030014613541c2c020304a0215404803102d02d50301c3c0440880c58000010482401109140c61a4440c1403000c03c1441a448050038540c0b0a0f6a62034012401401d1078491021200811400e012000d03415030300c0394078558083d40c1e8081c0c0c01c013007840082c0c0d083c420503074038040080e40c00c0c103140c001c440c580400304014545210004c010b00750000c00141d402e030030200c400301400103910010031140303003800d0140301c0301d0b030444405964501490700c40c003c440c0014401d070a4030031540000102195414000c2c095a1a80940100100754680c0d074295503880da5070040d00b00c5503d9040c00487c903201c2160105115241d0f15008510f00340c1042d00465a000082008076080040c0007500c0789580403c240603503408400f40d566010461641c0104142c02101030407008a940c0c4041c1d2140160364042211040b00340c06060100c1e1814400307010913410506203005565241200d20b021880310800350003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 186578291 1250 186577041 186577067
    0x1a07020d0b011e06020115090e0a0f1a010807060212070204090f0c05130209030615030120071e0b06041a060703050c0610051c0804050a120308010e13150912 69
    0x40c4000552640310a038202d03480c0d1a800b551070700d00c940041103003000b681c20440d00c4407003270000d4800c41c1855075140710b94442d0a0000311b0300010350030311000c2110f4504034210f0042843d6801030002c2417030910b002e900c61003607284099551800140d04015922140c000f0000355900980c500091115410040c08944070ba000307032485849000b0000003113890741d0081d42c00701c003c01009010070384c98808001c11030704582902540c041d503d914008510303544905042505a0100c101103a41d201c00d443c002000d0b0340c90004403444041e84000c0e04e004104a5880035078008804e03079000802800701e5501e082d00442e1040925440480020041d04040c0d004025064800707801e801c841490b102c418400080e01000c0c050641c1205a120b1a002800d141605400c0c050380118a140d00d429255408240c1c111826046803070b550301c0c03560f802d20405a00580c654010322035034507420b4860903c507140c120f030984d00110140103800880f2206560306910761150740c0c15640000000078042c004c05e4003904052076410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 186579541 1250 186578291 186578339
    0x8031015020f0c0402091011151602070501031b0e0d080d0b011d011b080904111c050708060d1a0106080f090f1203090f07081b01091a07020d0b01 64
    0x110102c60f9003054002e8a100031710080100c2141b540851049840c0b42013600c140c6818494150340150054043d940d01e40034040c41b040900c40034000100207480d14089600590402d840c19071141031240c207404046115144514020394a04803400001e680c1c4c013000700000c0c0081900190f14209a14240e0244d080c1c0b68007a02c070b4556040300d09003c0a4645441e040180c08116480c041c03914009684c100c8240d80c03031040403518140310004e0301250032190740d0314840c41c418038005141c0f5080040d000d682e0301c02c1c50b1280000c7c04189090a40205101e00180c0301e94001c20030108002c0800c007207240e4210000b10b10301d0201c0740d2983c0d111b03c0102060b80943e00807111407004004180042c001092444100c015480104030b040352407002908143e00060400701b9500440342034501900c0140423440051400400901341d0b5140c5076a86090500e15611171410310811140800800c0c02c004140590b00c101c800d01b03507840d4129800814900391003050014690400d1000125030284019410758503148111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 186580791 1250 186579541 186579553
    0x5150a050105040b040b1e07150e010507140901050c030310090e0a0c140a0b190f0e0102060f15120115050406030b040b09010f0c050403062708031015020f 68
    0x340042d1039501c12402444d81540080000740700e12014031004281103400c59902010700703442d1000c4a15650031801048846190341182c80707403800c070640200d2005a01d400020440c42c10f280e000500502100795000540c00000320b0007030703441e0703000701c1c00c3d1040f5200c40026295649000d4503024001c22450041c03140c554034010900314200d0000900310b07403550f8801246000141410480c40181d51808016640100803520100d040b550b0030003c0d04101640c00e610311040780d06684082e1240900c40001c50400c01c01d10710400c2284ea0000b540c07900300e180ca0501c42a2038540c481c03075980903d47c170b100c95034101e100120390347d007940f505602003500f050103c00c2c981070448d00d4108220941ea80ca1101820006150002ca800300b801e1000c05a000104040002080c0003102c24103410341d90307404d1108020590203d000c01c01e100140c000c07420040c07040950121001894400304104482e600b03c0a001000084001015001c0c001400b0780640741d80102106505a91000290354200c0043c000c5805d00501c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 186582041 1250 186580791 186580799
    0x1606111b060901020a05030c1602060c0102070309080606060405090406091a070807020705090403030236120307082208071203030b10051e0d0510060809030c03070201111005150a 78
    0x603c02c2d52045c00866550344d2440e158440802c28640000b01400e0503089030604a50040e510500140412000d0070000350319020b450501a0019009612241030780c1c12000c100035042c1c0ea88801c445c191001200d072108113445505000740145500d50300241701544000300c104445407680301c02032043d00c0ea6a41c031811955001022611264548070381a0801004404035000034060b401415941902003140d003122607014004810300c911000e03c1c032078003100d040c070386001e2420401300d03140070010395000552810b0341c00ea8500303200d4880e1b420116510040380710780540900340181d800d0002e10244048400e0140c450300307011066011800c08901080c5001c410b8039480c1098024800003e030f203034030b406080150205c10751001b13102241880381e900208000e404150a03481c454207014084c121004400d01c4d081c400050512140589881000c2e4424042454200e9000040728210759080c81c1a00452900c250b42ca854420704520000f00340b420b000421148000ba660020a41c1c0011a070304081107070341e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 186583291 1250 186582041 186582043
    0x8220512030105211b01120f0f0b180103060b0a0b0307080612010e0a0201081801021803070807290d0e0a0c060918180c09020a080a050105061606111b0609 68
    0x5001503035580d00f04121380902603841c0005d4080074807041c1000391448540d443c500d401c880303070484008042d0f9a602210480ca804611903881c0c040000d58068103100c44102400c126644140300c001c00342c4e6224090030343e40e034032511500801403484001d80382c2c41e42050b4102500070b100845429001c0c4074444001e80c41c011050190030441da8086018104080c155001100c12040007400840d40008014400305100300c244000c06802d09030256001d00d80c070f050000c242c20200c45501c00c51644e80038140901880c141c2400042900c00d0925206414141e00c018007403541c060b42c03c04244451030240c10544624000c0b484072195131140c469004050384030201a55403a2280c01550600a947c20a440300b00d40c461f070000786e0800c807502101c24814103da03164800480705402c039a003525004200300e0700503500061400d4000c001000e0174405907060401040450044030f0741410030101304034015007481100c5d03021780c5e880e1400980c8603a40d81c0f500d46c0c0e84005014440491402e80c410240014003103d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 186584541 1250 186583291 186583339
    0x90319020d2a030f020c0a2d0e0106030f0908160204060503010c0507030507050c03060403050408060604020301140405060103060b0f04030c0815040f11040c12150608220512030105 79
    0x403a40504440c4102d03103480441d840003030002103000b5442416004c003080d941d2080c00700c006191100380b041040307040c030340c01d030310003003000141c00fa11041514002e0200462100100d41541d0f51703849c0c001103880402d03000101500d0303540c4000d0300012000901c1d400301241340503285201030003518240300d107658910602d4201c4010200907000610b0600c080380010f0301c00c500514990740104126029000001d00290805809503022400b00d180000c042103100341c28440168401c804507811400c42d85020601c04c400040e60800e9840b407070b81c0d140000c015a00907881007026100e00d0258640311000e440c1302444a40c0140001c0e01e0510960f2030000b040c200000355101c06d5007102e01d03a0300786a141d5030f65029000a0b910b42c100c4000328000c2c02c442042d1150300c511b0031490031a99855031100600031406048668801032795141100030b00d414440c10390801051030f0030240c1c0c8081d0031196a540c0c895030110036a504001410380c042d40d205002d003045c2031805141038510890380d50706082c4160103581c5920b4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 186585791 1250 186584541 186584597
    0x6050c16030b0601120e190209070f0933050c010b0f0a0b07050f0607080f0708040201020a11011209110a05120604080703050c0d090e010504060803040509090319020d 73
    0x51109001843c154864030b0781c0071a50000c00e4011500700c10b421019800c14001480202c00c0002c0b051454040d4980740c513030780750005d0480c1052046400c45460060012b9854003880c103d20102f00f10000001228810340703006a00341156110310b100b00346100504030b07400700090342c10b10f41c20010b80d2030640c0781142c418541c0c4403008258951982c58590031101c9078101d501c017500d0b82c0c002d600c0d25510300c40042c01071034402e444594424465103410215001e42c114003804620030411241c0c104801070b60001503d0320f0035900420400d4104111000482d400003c0c41c0e0344100041c00c0a60840401c440741c4410380105030100d03024403020f030311101840481c1889100c9a545540b10702c0c081008506040d00400d6000c1c020f281051401c02800f962500d8848051003400c00a1030702007080040c2c103482d003102805003008660601901385007080345983d17070049000d061320544040b0701003001101c041080341e034401440343c80440500c54408001e5110441c42d86441c000c603044000e0810000b013044d034445c89107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 186587041 1250 186585791 186585803
    0x15010e030d020706080a0c0c02100201060f090608060c12040308101a04180207022202040504020c03031005040b03070618031a07020705010f0f0503070309051e12160201080405070f06050c1603 84
    0x1230565002c10906100c17012088017955130b14440414540c8107144600050f2040b043e02140d030620380a007461a10300000c0c0400070310b4006008a0104002d540e0405811a80500c0c0503913054961401c1d803041030f82c80b68030880007005220b802c8107020020f2805001244c603c0e50703d01001d0b081206181d41a41308100c1d0080d484044003040110841007454003503650140f01c1170060504c0c1d10780d00401c04070380c0f1508110310719074000300030404140d40074500040503100664003840324501e2a40440d907145054001d15090208000300c0c2c19a140342c0b94002d00c005c41c2c200d0502690344220b030414800c11a42501c444005008513480401c1c154000d1094210f801c2090f5508815a014840c0c221040c2e08007604101c201a02c03407480c800810002c104010290f44507401401c09019440c00092401c8083c900401406005000c420902c00c1002c8504840c0f58082c20860744a50381c1e442c004e0f007041c140390000021910002e00208031641e10502622401070514101c51544070258100b2100d000f45100042c91 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 186588291 1250 186587041 186587057
    0x1202010519030212070e040b151c09060c090303020610060c06020c0f073b060609191e0b0712050c03210609011d15010e030d020706080a0c 61
    0x9180d100080c5101e00c0054030b0014204400b0b00d681044504040c0c80020009412401015051030180b080307001115080352070076102c411129030380c1300368050341c50340c8217103003208441d4114010b005030491614543d10640c2001410001e0201400315585808180e0040c801d80c4001251914411094000c1e20580d49811954504954890f0080d42c0030f0a0160141e01561a100707220550411420b006001c0b007003075800900c20b0b2007010300e0064066440b00d65690540301174403040001880a51f0340c0114003948d403155607050850100302c056060220301081c440e100440041c601100c1c00485080c00d683e1100aa503c950302d940020322801000b60242c5910b001c3c4095261103070081c802803036100d103500156420030030229141d0b0190b0070212086908100301e07004100951410014250241c2000c801c98803000d00f22210100940c2c40c010a103205115001e07150180a030302520388070351200e9004080344e000a118490003511070266104000c04030f01c0807804a200c2c101c1c04d0081c1045c0c1d069699541030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 186589541 1250 186588291 186588307
    0x503130803070311031e1302061207020a0c08280201020c0405100512030301050406050a080316030c020915120105012312010e0d1202031902090f060c10050112020105 73
    0x20303607500c040c14a80038161383e0701a4400780a13094000e50703c150300c0002032000e20301c0301900c52110030f4070040500494050310318400005a5a41c0b00703035100c0d01141e10b0305401035070324180300340d10b40361018a001d440034000860001e10202c00040b101040d00f45508100307245d200100303800d1030000052000030b01503001802d084100d0306103030740400d9010107903040b07080c60a0303a90000300312011784041c42e903249034000200500076400d00340a45001032005640c1101e0503840d01140544034040d031b44860705603040580d12181414070445044440c0e40d00101295180c0c18102000007155034030104a5000b004400744040100740103204241c12200d00c000100d20740d5a050000f4555041f450000b9680164104502c0c030402c0802d220700c01c01003200000074105103038003003005003079913130940e01e87c0c2c2c01a4010010050030300c00d813860700e4030300304601100587c0364400c820010f00303008406654240c0084011410818084000580c56078055140b2070400040e42c80d0070a200c02c034031240b14040e001c24410030800c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 186590791 1250 186589541 186589553
    0x3010b130605210a090206030a060503060c0702101101090503130303030c03060806070309031808280c06110a0209070206011e0302031203130c030302031201060f020c040f02090409061a01050313 85
    0x15400f548400e1300154414095002170030b0b1740c10503505841525600c2030184100d003010416543c000c6403500005d4140100c1344c4c00540300d0503039551040704010301c07041c0c662910070003500066007030783e031200549840f41c0028601c40074090081c8401c0d0002820558036142e0140a13200f803900b0348450718080c2041c0c2e81d4541e000e41c060072444a0440801c190104115800001854464060a5054050304540540c13484104941501c549880c12500c50712042a00054665007210304449280c00d2032041c107910b803080d85003416036150b03010350800455020080502d5011a01c0d40c140c0d4031940368410207840c0c0240d04000c001c401e0200a4156110030340c2580c10701400c201a40d808052074441c0a0b600d0300741e070b6603181059001d40c03040340544d00101d03030b05040140402c00c4a000d000c540c03600002110710300384d000359100303d403007023083c010307540d07400441c401c410241c0443e40c00c1040a8000d1100042d603245c1000204840c61100302003240340004076506620440450740a10030303034402c01d44a2a4262509 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 186592041 1250 186590791 186590857
    0xf08060a06230f07060605060f091909020a080702060a0b0901030206070f12052701021e0708030a09080106090c0f0e0a0905130201020c040626030d0203010b130605 72
    0x441c8004002e000307030a10016004024054284242c40d044d0700c60080e803406106480302600003030b10441046c400107055100c107034191040e005003103407001d1090056020051b41440d842e00461109400004c51000780ce07082980c180c0034052541c02c80f4003981d01d06040404030b810140d5059880301c403807030040001d80f906801504015010710204002d41c0c4061703030303206400c4000a00b0b003404504c1c0030038581855455825a0750015a40310e215036140349020000079110310400310140c030b00200030710107001c0c00d940411080c0090300541c5c080b650744800c500006400701036103104510040d8200900402c100b580c40c000c5000407100d5480e003500b91085c003038058407600350304000c0300c0c0c000c00904000101c6003154002e01e4020403440b183c40b0645140350000a081842640041e0b0169003071000400c19940d11280c1422124000a0072008100c07505e56400d0461083d41d0842a840d0b00200002c11946c090200030207603103511007141e104550f543c24042c0c517540a00400d80c1c054603152040c4142c416140581 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 186593291 1250 186592041 186592067
    0xf0b120603010b030708070801060e010b030c160210030e0609030403050619110301030308040b0f06011e03060f080c031e0304060516051518060606071101020f0708010c0f08060a06 79
    0x80380c0e000101012070b142c280c1561148040b6840307c031080018a4080c81440b01030070501d405600d0079030500714950003c0c88040d01a1103000300c0007400441c2c1d03a40e2450b14000a5074001c103440d0300504000002000b500c0e2010003e00c00d4010320020580801c4008100c0341140c3c0e0202c050081070362000aa072008004032500d0340a51600c6000c0e0700e081030b903004000d40c0618403a40354034116041c58200011048001048501c0d8503005606100c25a078124019007079060140340019402c0a4443c001c0300134000f5036004401e500303110b13076004c514001d010507900088181a422541e40b18200d02c1485a0344040b0508002142c1040005104440c4200010080001d081080e440c01619540e6841e1070410340c4241c100d410701085061080c41100d030347c88403191105420040c03065060840024000784103140d07005015810301d403914620799000340417019400100505031050a9a1035010a01a01e100703030b54003001407800414041c620f801801d140c0d0054502a10f1846550304200040d5101c01c10425 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 186594541 1250 186593291 186593293
    0x10062f12040e0f010b0901080609181c020129090402040603050d08070e0307060509040203040f0b0c090102010b0a0303170c0f0403030c0209070912120c15020a090f0b120603 76
    0x14401500d89410000340014200c90100050ba46070040c460444090181c20003284540d0800001c40c8580c0e011394601e801c01e10480e07200000e622b86125000d01d40780030001c0c02055015814255052000030a080c182c1e18013103400030300402c4044038205850800404507003407004038040f4210840e05041602c2c5501c6440034000140c0f89450342c03034151401561410850014252100b0090030740e83c880300e44036a0303007403c0d0024001141400d4002d04113000303c071100350050307178040005018089515042200307550842c0c2038645a040440550949078000405e043c050340c200710308040c43d0f00380300c4010707000c0700c0e01035a452010a111a0080340c070004041c10101020200740030f030030300060002c80144010344c030940b607a40c00c0d1140c40c03051012140004000e03900b80541401c080088111590030750038a2a402a05030400320502c074026500240041d00c050200c0c951034030a075001181c87d81c020300303609510b5161101455a00e420010b850801c50140042c6c0d08401d00c0140843e00001020940080000b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 186595791 1250 186594541 186594553
    0x90a0f08070b041119060914040b0a060f08150a050103050612120c01050906062b080a030e0c03010c2f161502030702011d010c1a10062f 60
    0x1403507940ba0850140c0d0142c421201c2c1c0c0301a0000d40c81d01c030010340c01d1480c0900c450540e09103001000380151089102e07000ca4040048000c0009550300c7d4030140d4044c0c1c000f440c00c036119469040003083d550202c0c0c00600802c100001054800340c0281804408400c024646545982031400450117401c003d0001a0440054a81e04280342414051420a0250f00c01c1c001d40355014114601d09440010700590010f42014090108544480140c051540300f6285004840c5200131000045000100c1e406401d1038004101400c400c2d60507049001d01c00300100031600e545c1c504c442054229008003e940c00840c1e16500e404580f200c031501d0b075901d00803a40c11041e5141503884100740c140050400041d070a1802030700180b00d9800031300103d040e1841c680c03000b5814803d060380007034502940f06081611241041e1041c0b40c540e841500030b10b843c59400800c2c0202d1004a0b1904103403054142da0b003e44000f61000082080c0c2d1158500c0c43c001c010381d48a0342e00c54050412103940c0c4210a2003000464001c0d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 186597041 1250 186595791 186595793
    0xa0b060715020306030c18070c0c090e0a21020a17090901081c080709030305030a0e0d020a030f23090a0302060a090504110306060307031d0a0c05040c08090a0f0807 72
    0x140c400340c1d2860410880503a407450030b00304040c01c0419018110303114400e0503c07039081403020001c065611a8031410308102c1c554681c20000801c1600b40c0c84200d14500f8905215545440401c0c0450164480e00c0a0382404020004500f0030024840480c80103038417050111004c100c4503108441804000e400c01890800c02c0700129485920036000a04503610058070408002060164446903061501c0d0010141c14090002801807445100140400c4000302c0410084500f5031f0100884800f00400c941004080810194075464200b000354003080070108014440d90107904520310441c0c884035040c1940050405d54082e68220104258011008a02c00300040c1c0f0340300700605500441d40c490043ca2860141000705441002c1c50807026584103001b03014090315203e0640e50000c1d1182030100f011070300750050810909212180640600c50044101c3c03d021031140c0210070303544243da003070000c0a81c04c8400e0b18825400ea410036501e42c002c2440034007140d1412a0401c04622444900e441d01080d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 186598291 1250 186597041 186597053
    0x17070305040809042306040b060a0c02060d090b06100801050d02060c0a0203030307090e0604060b0307271e0f080a0f050309090a0b030d03050609011e0b03072a02090a0b0607 76
    0x11007210817501c491100c243c01d500344800e18074594032403c00c540502162880d080841c0041c0a80c00c501d0b414003040e00040421550343d00b003034030701031003101004100c803081c14202403840c0709054800c0707402002400503c08800d07104603032041c103880001d0711031900c92a15a090044603405988005100d015100a10005a8050004501960040d80d414900908104584489903c042d00d4648a0303031401408121341c03c074480640b940700b0700c10304020882d4043d13400072407031400b4641c031103070325200001c600400d01c1c0c1c00c1c100680107610354019181908984030802c0d08410b003980d000325651030344a42c0325400000c07148280e10001900c12816642404060808078000501c103075180f04584d515000c000415050800ca040110a41c901e030a002d2401d0a90224540388410300800c4e240f01040b0403086120107801c0c1900d00107080c050066a41ea140240c1d004000c443c0ca188020401494103082d1480c03265050790303890b14290000c0c40c40700c25407a4084240000d09402c030200b9002201440003601045d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 186599541 1250 186598291 186598301
    0x1401020a02030408120403050a030305040501090b1f080c030307061d010627090c0510050f030a0b04050903070c181b0e030106091e05060103091506151707030504080904 74
    0x203841d40007151a00d0821900600b40185030741c100010070001c0c07008101003040007078114100d540500740016a0384550601070302610a15002074202c0001ca03007031140800b8103802650020021070303130200300240c540700415201c900301007405078107034018021900840c406034070402122000b90340c0811407400c0100e04500b07549156010210302c900458808024007801803c00155a0342868100540c142e1503440d0040c2c010315000702405032005810108080b80203d0407110080650119203460345000c10100c40034205055045002d241424081108204000107850034a9807010740c08003150b0400528242040c0c0c11004400c0040e150b400355001d00c0c800b0f85071880c60410aa448400c240010b0060509640f400d03845403001303d14003841e005613400e4000020a00084148001c1803540710b00d00100d0141200100160a010380119645d04e070854640c403401c200c0303a42060140c44242e11703203800e403580011912118492107140c400a800c1a100b036108961080c40703001f03110708000c136110200701201c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 186600791 1250 186599541 186599557
    0xb030708070515130e0f161d061309060510020604050a15110705010e0601050118120204020403080c061008010b1023030903090411040303020c0603040303060306020f250519140102 79
    0x7501102484240d82e901000d2503848001d00c0307c0000c502d482110002d0082100ca800060060081e03480c0c1d0525548450844079001003040da00250039445558013070040c82c540c410b041c030070340321020020045400031503524803650300b110140801c0b040341e0f02c54140c05c410b990383d14144255100500820040e072a07020300841c0d401600005401f10703059600d03d24081c0f060308102e05105030744e24490001c8649000040c2502c034000c2c0c841c45c59610b180f020401074041e5400c024020b460125020251040c006000e0748554086040c0100107a5115001801c80b02d00403001500030808008203060b80780105130502c000c68401c0c1881c10060010600302d0500d8000f5240d02c00d03a034000064103522441d05000d504007440e42c0004c5d0750324140c61640e02a548100f1100c0e440d000d5070b4080300103000e00d0f0180e40100000c540004055643d01c0300c10342d441c2c4096000b100d2101440002c9607411141012072883c100c00c0f00d0b40600203220301056180100807500d81140c1c112440c20844d4400c031010242030000d0a080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 186602041 1250 186600791 186600809
    0x3070807020c0103051009091406070c17070c140f030a080a09050105040e0115050705030c060a0f0207020901030204020903030c150106080105180a0b0609040509060103060b03070807051513 83
    0x140c00c2800000382070808280d0380504060403e818415219655a020401c40b403462000050700080c0c0d1411015440c00b100d000707915402000b080041194202c580346200902c651610b0344241511401d0f41d61034003a404001c0e00d40d511036031040c4440500100e0121004200404030111500040002881e01c0c2125508441d40300d40412001c2c05103401c90341c9030001d0402420a0b900781401c2201c0030a104905100b90400c122101c109000154028002c072003c01e03800c074055942e5255100981c0e55070f90802e031400ca0b2954500414000701240030f20940300b4003070f0300910011060b46943c003004040d4114141981c1e15000c10003c03512040c0d000c000041468bc840c25171102a0b614051004e81038200c140e0125001d41d41c8403c1c520f0340e001021443d5540700012420010b0384e03101340303004a81140a1b84424541207840e00f01407124001d40004e01c0c5040301c0c407510050000c01818000d01d45c0340d2806206034005940030b440300784020700e1721404404110b840049d006007091080400c19010002c4c1d41d204040e0b0f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 186603291 1250 186602041 186602057
    0xb0901140a03060f1517100b0c0303040507090501150e060d090501050a0c020a021c0f080409140a110a030b04090f080a0f0309020913060f06140a09110301060c0c03080307 75
    0x12058228000707000f400460030040b41003040d25006007044e0b05180b40a20446d24140015440102c840c503d41c02611402c441c071038681c0d08010320259203901c251816541c42c4904c08000034801184d015490580d065540011303c001c940e09030907201c6441d00191241c2c842800e004550350402503100320b005181c000c20012031142048180c0070120ba01110b0315004541007240c0c1500540c0b68446120071140c01e00c0300c40d60400c20941448034010001082c0140481070024002850352503540140d82114407000d060503c07603c64403030150844540000b051110034040c845203802c0780c02540b14283e803510107400411040003d030b07120480e0720f128030750403540c0c0074004c50440b00c0140d105641507a031034040e040c00c02c01e8070110740000b4190310005000b02000080c11864804011280d001380501c40707000f232010b101c030756115500401c46840307074140c507401030703480d040c000078150100e0007010076000041d6081407443e420720000b11414110900d003602c030303558940d400000107000c4500840c81a091640c0d9085 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 186604541 1250 186603291 186603299
    0x19020f0105070c1b120213061d040318080d050a03020409020703180e0f060409030c0204090c1823040c0308070b060423150406030512030901050106050a090b0901140a0306 75
    0x109078080c00a0006441040e22028409400c003042c5800c0307425011203207601d0020882c1a1f03d000703003043e038124403080840040382c48000d080e281e110900a0780b01e500c0e03c1e098001814402d50b21303403065100d2041140d1012a00340030719805140204003065192501602e0a40c980e0046c106a0303101581c220000340380e28001c0810001d00c04001400f070040110f01901d1400d0007060340c0d002d03140c083c050a20483c2c9e608103100826010b84014605203501074800c3c4245005030503c0503101d01035204481c501040403007102002c8100c3d101e00071204103100d01ea010000881c010303840c14003c0082c02290121290540440440e03603120140414a100303c002c0c02580c5080c0c0107003c2030b10f20101c12205140403c68004041015610000342e1020300040ba0f409800045c1c1c0000e40a0051030b4406005802007200782058044c081004610501881e002030045c4e0b666050200d80910418040d40d00089501ca01800440290790091070708000514100c60440c07040d60800b03006070701146450022076034a0740104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 186605791 1250 186604541 186604553
    0x3160c06140423090a05060a06021504060c0c0206030c0c010b01110318010909060909120905030a0809040207060f0207110306011a030405030d06170106120819020f0105070c 76
    0x140648081c0c601615001d800c2020740c0028010b5018a4800407402c070301c0003c07000156803d043c0300460081ca410500d0400c3c0504000921003640c01c14001c1101c41004100341c0e000240281080b4084501c00c0c0c0703240c0d181d80f06c8000501840000c03000f00415102c00501581d145400f46001e18190950969505400300c02d207401c59000040040c14003094004a912010022060340c0343c407051300c0b80b000e0a149510340120340c20340c80c135001994a1498401d010900d80302960010191610400d400f03c12541c1400d03090700d00050601c50290f00d030340008000d00000b444035001c2e10049201401c003508003881d0365102c2c82560000c4010b51800b69000c01c1d21820700925480403448990154051704041d41800d480c1440200401c104854001001012070108181001201c030925410001080070f192911160040240001c4045d80e140d803d20602007482d29900c820007154903404403d003441c0803400450201418851220102503000704040310901000038051035209040329501c03601d42e00e186141803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 186607041 1250 186605791 186605813
    0x605160914010c201309050c040203040b1b13030b06090708040b0c07020604090e0601030312020c0705130b1012060b040b03150a08160e0717150409050316 68
    0x76404030340c58403a00354080e0b40c0007040e0b02082034004088a40c050591644014050b5010002ca50080708403508411a00855801081032610032001e0340d01d00701c420020002a0300058270f000d0003403002030011440c004102440510b6171180078518905002c4c1903071030b90b41c5445c03041e8403d8820f40e1030b010410001d403030940d0321258440d4090501d81c0341401e01c0d4864550046d4010440d0b01403c0d070001d60300c0305540d40c1d10103640062480380c40c103002560000240c00d403101002c2c03200f14003140300c034003026a0840041c02500c020004560081480034540801c00001004010944c030300b9a0381c510781055544c580f0318982d139074850a901c07015071121805001204403201c650003100782c0c20f4144000d00203001c10380c0c00c580e005610101e0882e01a80048006403c03000d25900400962140c070060700011400c90a43c0707000c50305000410600c50340d4198054503090740c400010380050442000082020400f602401c0c0c08950181000030f02c85080c0c2e46103407859004c0e07440805801d00c030f5542c0b001000003240503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 186608291 1250 186607041 186607049
    0x30c0519030606031a060105130501140706110405030f150705131e15030b0f0f0411031003030e0901030503090904081b0f061501020a080a1806120c0e0607081606051609 74
    0x484ca149c26a045100e40540501c5e020f02410002c0f041c1301c018580c80d00390281c071440344d0454000c02c89241450301c01c00040c0e01602c24280a0b0141e01412102c0d0040440c807040c219015030000c030440d68485008444603404080c0190b680c1e0008140807403240d40340401906030904003d080b660a60034640c804000c0c0c2411407400041508103405055580c9a0750041c84070524207980080311038a0a500103800b40c40c6803166a60102e002000b005000700d0350304844402c403800b94581001d02c007408420310400b02c07003d01015210307138802c0007000014181148107a500902900d00d1505040d41402a5101290160a0402542e1144046a0030381c0005d01015400c89010107400030199a1200085c3d2580012000a800c480000c2101c00d9582d004a80c00e000c1c004c4415801248140c840202800316030f0b10755003e00000d85041d8406918901960201131400002002c00c0e00b0700e44140e843c1c941c6540104200f04d44003055201880008000340515802030220304011103018040040003081d5107031540c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 186609541 1250 186608291 186608297
    0x7090b0c0307200603041208010605032202010c0b07020a02091503060705070501021603051902010c050412020109180509060702060402010c030815090103030f0315030c0519030606031a0601 83
    0x150415030a000411101c0351944101002030000448507035600d000030454a50340c02c204000b0400041200044c208071803c82d10343c403142160b90702e90008551a020440e803010049004050151040c451850204003a62052502c2d4840d54141d6903001000c80007a5200c0300981d000300c04420462070078005544c0d011b05503a002d560307049003000000b03980c0d040107031080040c80000a58002804003c0d01110150010440754141c908a1403400401d03580c0b00310692485441c4207105181703d1071040c0140b82180b001c07a030780c05040504008004401c81c032580c0307080f03050001000340040c10042c006409440c20403c1c240000e072a1810386507850400034000c0c20744007190424410840180e80020f040e182d141d0f003501e0821030681d5841c9104e0800c8800200c0300e0b070f001c0c0340c1100000c00c0691000307000480b0060f6950510030102801c41d20b041d180070600004040b1401c07044140241d050002c102030310b07a1141c0361100701555407925860100c0b04207820035a00840c803020134891b03514a00c0c0c81160009401c1c0703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 186610791 1250 186609541 186609547
    0x807080c090601051312080d0f020313110103090b010e01030318031e060b04141005030106051c0501060b030a151215150504020c0102070501061a04030605130f080307090b 75
    0xd0000d822044018030090501074085424640d000740403d0403009000f0040740352a000c3e41d00d007030602c0960080c22100c040c49041080d0316074803500307500949020b00200c80c800d5080c40103651742d00820420b451202c0d4100350381d541000000c22078003903174680203241c80b0070044081c1d4150f040052425038039000e072a0440100040400016001c1c0e00031480c08500c070b02c0700e12480401c0d071400201070010044074560090500740d41c10000c440501c01540201b64400310180c01c90b541d241850300340c40d0a0300c21941d0000610322103180c00108182211600c500c900e00005409484166590240e0025191010b4103076031111050201103030310740450054091820040b03a29025aa504642038101800580303d00e44c84611444410034070380c075198054a0014030035034a03040c401203454000c0d0840720080d1340c103600300382002801d9003040c54486c0c0c019441d0000c042c90281542c842c00064032010f880442c0c5940c03080080c00c0441d1800010030a69803140040b2a1b0303e0401c1d64004210301c0c003503040010096010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 186612041 1250 186610791 186610813
    0xb010311060307050d0f1d10060f0b1602030703050d0203070b07030b13020d150b0d0f090b060910080a030c0302100b0109090b0d02040906020c10090201050304201504080708 76
    0x4002501d81848001e02d0110707100703407910b01c03500c05082c07000b2052211f50f1018410445500d40459035000c00c20703811000308035681e580e600e00c0c041c000c80c621840c58090b0080000f0403082454034692480c07580007404a6124a643c0d90700d0340c0c545020a420b4000503000031036184100b01c407040485402c024a0b28050144101d0803000540c10311404114061141d8002030020f085413460b04004040c218029845e1803132581d519041249500680e1071001d2580f4050300c4003c5030386079125010720507400c044a6421603840905020031640c0141510040d001907e10020300000c04212521101c1c0c46a913076910070304614070307029262107901c598415040f42032107405034081c0d074015112006c9134000d20f80400d1004a1314046001d0884600001c1d4110b403c1088131410310940390004c081082c00c0c0400ca4400009600d0f05200710380d44100300a00281081009c40e001c03491000c08a4401a0740040c800d9800120b03100107151542d07a07000d07101540e030340885d0411003070109100e0f80d0001c18542c0c01a04241d644 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 186613291 1250 186612041 186612047
    0x9020406020d020c22140c0d0b0904110411070606091a01020d0f0f03020913060e0c070809100306180515030a15021b030d050411120c010c020310090b010311060307 72
    0x80074150b648001c520310f0b044008003440f030300402502040a801c06c0a14200b2a0561005074072200c0300c2e105450404182400301c0c00c2c00d2140b60300c21783d0401c141d500303510401002c200207401e000450410700b801c24060344000c0b560030302c01d9100415100ca4001203196145800340904010346a00e68155001080e080040d21342011468210b103600c0d1814142aa881080035002070083c11400313604216007015048402060358404002e079a161640700e84207507a07041c0400740606c28204014141c06044c4041ca143d420103500307a42002e400c5040105d103581d19034520818841c50245c4503507034261142c0c14070000e9001a1514000c4d10410307000743c2440c98030350b00d6412030080190032008080780d0001358030701d03401350030841417120303000c10001e980d601d402c507401080182a05460650b03041003c0d004501992400c0080b16031154510805020008044030040d42c8040c52040e05907011301035441a10b02441403440f81c0d03907a661243c84014425411410105082c00e00c05404a000710b00800c14000c0d4190 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 186614541 1250 186613291 186613309
    0x170d110a0203030f090106090e0309090a0605220605090403030f0506030309010509060d090203030a080403020c010503060f06031302120307030201110702010503062701030c0915060906030f090c09020406020d020c 93
    0x80400303004000c94440c9070100303005044503403200c0240c5151070040600c1c9e1001200805407441e04440e4401d242d181c904c0800103c41c1d103881100e91016030b00c00741c444c00c202106445440100c040200140c1d107540e4401040004000b16011000a5581e004001524445129868010030160015401c03c42000c1c0041d155100c0d94941501c41c86010903020244034260f0416072905502500b60f0303403603180710040a0710003841500c044001d80940b1a414401d0b51040c815a4400d4078002d1040b003c07912950140181e542c0060071030548852201021400750b200c1c0e51190228801e01e100039a5250441d0034000d084580500401d52814410020600980c0c1c2c08002c0e65006041100c03460f0450f20307540c600c1442c45410400008281c03412070000014007202040c0403045030354100382449032a8028104000e100c0c0a40100ca0104010180500c161403013540249146600084002150305040e101c41e5004d160551000a42d05d4000600388099541800766034030007290b41c0014a1092105000070b010a1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 186615791 1250 186614541 186614551
    0x10203150301151406070212070605070308010e0c0403020d0305091909060608010311040b0102030403061401090e061e060604050a0e150a1211060d150305070501020a0c0b03040f170d110a020303 85
    0x560013251900c07d558401c0418010f101800b0211a170165944002800c240c000e220243c022500540002400c0217415500500c5003110100241c40c260440c1d003042604e80c00b542c400e40070400d080c0b2004403a5150705500d0111145c5000144002030300d8050203e00b501d0301c0e03420500c05c05c40f21100420000340174213505440d6400884003c5984055000100d01e5030050b17a1020b4161030610355000c142182c480b1400d03050342c01c0f00000b41b00040800d142c02d9991141a911405040c0b160786c59074040d50311451a6503041070b801445185065900c40006120385003e401860b0b803541c1c1c043c10700c011454103040e0880314102c140c45050196261502d8079003100343e1a200074101c407051a6400d0902d80d110021191000c1e0314410410294101c4800c19806040c18001111180708180001c103066000081070403ca82e884100e6450700c905110544c17100e50000740c01214140e0f030744e20505d00003d81c0d52802e5615401400c0f041919402921107600503240c40d00f10300c48003c40204100215a42c0c0882203951013 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 186617041 1250 186615791 186615799
    0x604060f050102061501020309130e06011211010806040615051b010603200103090609060f050a0209060403031d120d020d17010603090c0302031207210c03110f0102031503011514 78
    0x1400f251700503820b501c05c8202c2282d020240441c0758030080c032698007c0711703100c1248040340d10a07078a80e01008100111382c03a0140c191010410300ca1020f611030041e03035500c440080d2000c00c3c07880e6508034945103085108210030215401064010b0f100303158408243c0901c603164000d014240c95a240d0b04042c0d2041c56907500b015030360b80482c1007564000c0e0404410781d0383c0140100920a21380c202040140a0000c0b90101541001c5c081582266076000f40c6048801c0201118902840c5580541e2040220004142d03442e102152800040e51200d4500d03502c1a103480283c2820089024028100300c400d0140906000700000810088620300702e89605550030750400003000c1032907050043c1c01940543c0000e41c1071080040341d2440340c2d000c902510700340344039221400c0480d03aa080035a0300d501601401c1c80002d48145001404644180c410304245c2509000351900030460a04043c2681e000b121001d101525400c001d140c1030800344035005110307019102d2086414100111307080f0140740c4640c103600c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 186618291 1250 186617041 186617071
    0xc0f1513061b030b03010c180b070203010b0607050304050a06020d09060e030a0203010e0309040f0515040902150d0b010f0206090c04020a0201023001051509060a03020409050f0604060f05010206 85
    0x8010303240d4040d6448040302e0024401410704010018040c0c910122030030300039400d115640804601441c0d4036641c4103102c0e82c01144003810b004000d181d03034000d42c0702030f83e0564843d60082074544034a40101501030182028503034485c10681401780c24282030744400110340c0100e50400c40542e204036a4000d039010791419101c21520a000a0b02d01510384501951551030101e030340c15950400401400030001c1510144145d034086081e15044580403241e414103040d0343d144400310381c41e00307a2041403024801098810000507a05114005d500803405e00d4038440d5884609624668010400c0c030f64000c0c04e40300400041c50284d24103900c1d0042103188500072500480c0300c0700c485000b0f40503030320000ca610184494140f001c802501200c0d01d8002422800e041d60000490304c1d05014000d00034a0b1440200c00b440d150340c02d010b00c00c0561210904d00c0400d80d0a100c041500b1400c0d02130140a00a085101c90781400c082003008200c8085501101c00180d600d4020030590b60045400c0794440c5540980d000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 186619541 1250 186618291 186618293
    0x1406090c0f010915030510080d0c0204020a02150408040602070b0f0d0b03030910230f160305040e0c0703031b0f1202281404050105220b0f0c0f1513 65
    0x60740f180c0c54108111201c2900c1d00d80080c954140c0c07051b8400d03002455a850200e58a060090300c0b03c40c0c240806001810100a038809810107400070000c03020a44100c8210078010492020300300016541140c9500b0002820000160304000060141c0351004002d4503044c50380d01000014440c40d40c40780c60b40342d01ea66581603166414000ea5241c244042d05d4078160305954400206041314440814142c0140c901e0604800300001c42902c200190740032000d8603081010308040780d489058102201000000c01c00072844019400c0e200d80510740d9030181381d4590143d031402030140c0c0c01c1c07500f030484102c0c441c0d007048802c3c42c0d120359075005002480c1001458054070070041406417091140080f090081e0107000c0c0230710302d004500480c170040c0740d0b40c41e502040844410070301d0a210350301c640390010303034240100000044202548101d454510348035601059580c985110305802c81d0710281000c40c80410381405202042c49201c40d0b801c9004081e0000345d4100b101d02c1c0410101402c1c0c0c01501408113030140c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 186620791 1250 186619541 186619547
    0x110702090414030310030c080309010918020f04120b070305101403010b0303070c06080f0c19030f090809010e0a15080414060907150f020703110114070f1406090c0f01 73
    0x302500070b101920703035914103a0ba03440754626981c4002c80d8500d02103030002076401302c00b00550710000030503035420204500e48480401000c442c4005214240d42c20080b14400007242e030010401450381a0404516001c00d00302005180c100a255005050600c0d00300310706140707121041c00035902d030740c040a95601203203c0030a0042c0201c0300856090701c400074440080c0440000c841048940540d01c0200e650742d20707888810080000c0c3c03003410900b141484250f88010a26258490705d025a01e0700055a804c003641d50425503000c3d85095032042c200290303002041d64070149006440c1800e4030000e41e00752a00424071075108030390001d5801c04c04030001050801c185046100c5284803004100d03070550030a0155991620154421010998560894031600f940034000e03280d80e10110341c0240c002146180c54581d400c440004687d41003004c0841000d9044106002804049001d1340040d0500b900d14580105002c0300c8aa1258990f4400010800500400078444209a0060f10740d000b014540350016 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 186622041 1250 186620791 186620813
    0x109270204030506040227040609021224010b0408100b0d0206030403050a0f0807020627030409021c0b06161104050f070216080c01031e0c1709011107020904 69
    0x884956800024004284000040c1040c0598021182513400d48504440b0301d0180188026518107814004005000b1515a07030281250318005481c2d404030a00d80c0c41000d0130a41d07060f02800c98501c500010145101c0f0813401c490242264100c01c9241c5810229165919090740d00c110703040c82d854010051054998504d035680840d400360181da26400d00d468080e0440e0404640c1c000010807107030040a07841d1062245c01d008019a0f00904207644440b2031182008808030b83c0200d512031401c2d2502c407106010001000240740f002801038451044100b0222500c80c08075490900d40c2c1001c1c04001e05aa407901162440d0070020a2070003050b0403454501242d0007001801c50b4014600810000d450300c0215519105c0c003295820f035170308030039100300125040406001d40b11a03a8005840002c55501941c0f00030b1505441c0110900e00081610401040d0b0b0012a009000640140d112001e000d5150b0300c025004844e100c02840075075180c401c555002d008203080a4812a4141e0105090200c1c01002d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 186623291 1250 186622041 186622109
    0x15070c0602130906030b0103030206060603010302060a0e0f10090501090506040807060c05010b04020a05030411040504081c0902040c1701170a020d1a010b190c0b07270303020114060f0109 82
    0x4d002040d607074103024454540920080e0058000c000001d016031070b114003181c0c1600c0e4014441030405d0b8240b4411506a480a0f44103034204100504100306a5070700080804a01c40503661845800e0400d0001044280a980a940101e1050005000310341022070304400782e031140d103003004610405091083c0505034900c04540c21500c0010000d0711030b40c0c003500540c452801015100100328070714040c401110000c640c041d002200078000244090350020041031482c0b540e0002064030811500000d04450400a02d04081480c43c0980c0b684603602c0e481241c010002c0020005003001c0e0990b12544484c001d9000a100300c010300b80410400c940b00d108105c1c00280c42d01e081c1619030310340b01d03002c155610400c2120107500c070130750081e40e18601c00e401410140e80d0004510990b80c841100c140c0d00c9103049454041d0340003149070500d64100c11519040010350103607002003210781201c440d0030b0300400058130f10340c010964000440344e0341e42c00440c1001102c1c06074100700c008401121010f015021040d41d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 186624541 1250 186623291 186623309
    0x6050d020604171e10050c09130203070e1305070e0a030302060402130f020309010504110a0b070f020301091a040c090b06070b1909050a0c0e060915062a15070c060213 73
    0x130219811800046402420f50590001c2096490714201c0711028000c0c0340c49a54000c1002c0320442c1659100d8001c1d50700001d4a08000100420107030006070142d0300081030841720750750b481c100112141c0c0a2405040e0035030030703030701050078078190f850003900e443c00140080d01410f00d50040003800c804640c48252041a0b1034000c54803418450030841c040c0c001601c05603039880700c84120200f0351400e42402822500d0500780750707240c4a1b81d0b5aa05000d01c00c0010140e03495580c800044001c2041c407001e040c83ca200540c2003810b58541458820324501498100c005820b107011015609611b5110850f0002d0b500034a0a4038140d646003550107100002900c10302c500c0781411040b40412100040c1e940c0b07414410750b000c2c101d01d074076512200e060060403540c2988c060005004254240b10b01c00000c4500440509070314900b002410700314402103100032410300c0d00d54404900341c0c882c26061100440065404040d01602d05000d034008001803180800504140d43c002100d011039030700c0c0c011b8680105100c00d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 186625791 1250 186624541 186624583
    0x70204020403030309031101020a021b0402120903120108190212011b0c0b180606130207020301050c0405030609060f2e080a030908010204080703080a0e041406030106050d02060417 79
    0x80f034010090030400d50101d001c0b84404081141200b0107000703a40003402560700901034040c0c1c070560f60309600d900c88070880e005070342049070300d9607608441c42d940e00c982c0b100e200560b40e5800d800400ca0704104140d1003041c264014900c41c03158080151120f42e011601261407421480c0043c0025006140003150415201304081d00c21281a8100352035000d0b8600892002c91142e90305440224040c180b02070441498002c000007454900c0c103400002800c002c140801030400900f40d000c0390842d142610100204d48010070100010301d010072401c3c2c0d1003016400901090705040302512410030000d41380740f050f00e108016404c2c0f880100c1c400510810343e84140100c40c6652948610344a42c2100403c3d00010344202d00400e80761014001c40742110a80390082c04510f145072034001054200652072810480e202200005c0c0e56100e0007285420103a201010a503400d0020415003100d4466010328020302201a81c0c0000d40d03038020983d421035030f00c80c0e20881002000205541451000001052000001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 186627041 1250 186625791 186625793
    0x3020606120109050c0d080c100902120102071109151e040c0f020d030515030124050d0201080105060711030a03080901060f030b070e031e150a06080d050708070204020403 75
    0x10510300400c8103540312894030718200700540c00d0781c103190301c054510382c003108612000d42031480341c4c00940b500460400e81062908194941052500600303095425110750b0083e0661a0460400803003800340c000862428281e6541c0564410a05c8129842400d0f20000521055200a0760680722413009210301888a6140030381c02130405005800c074001c038a01310001c0f00c514002c025800e6450f0581c0c0042c440706044880c100c01805000340054111103410324640381c48e032400d00415411040c07103081c0420707440b400003001101900944c009803045c2d007030b00326500241c0d800000440c1503172015034016581d03141e2030900300c90311486c04100740e800d4403500c03e0300340c241540031070030a0140d030300d41c0004e00030143d407146074028a06240c080580302c11100e2001c181d000d80540800500307100c0260a8030046401283d1030201c0385000070340001c040d000b801d4040c11054001c00e44951110031314204122481c202311040d036803104c0032858030060120000d1010140440c080a40318010ba00603c19541d90b622 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 186628291 1250 186627041 186627043
    0x100618050c040f03150b03031309020307090504060e071404060c02010e270a0c05040312050a020a1b140604080a12030612080d0507020c030c0d0201050c010609060e07030b0303070f0305090901030302 87
    0x18114190343c401b441c0041b110220315000c400c440d008151801c0e0304140c40d00b0000390030001e51010700018107004060100003413a0310303240030b000000d02c05000d07001c92900d0018400b138a020308480c0d4805c45504200005d014454000da4082e500c41e13028603180b44000301c60740100300424072030500d40031f1101500313030126404040c0304030303042c850700703000009100360018510705507054040e50000070458803454106d008480c8c4124050401880c4a1048400508054031b40c252030003080c2e0300d01901503803019070602c508030b1031494181c6807000c1500d902d841d007860400c800740c941d204200010611a50001d802180d98800c0e0007140c042c1c0105c0c49030032401c00c1e181c07500c1c06480d804030781004c1d852070400300061103060022840d85c4100f078000c0c01604161548c581005244000c0c0700080b414402c0601c41003032079110901c14100a05510f1000007001d60820f80440c1c150080207054900f010f04240741440e06883c0401590329056116082403d0400c061a05482e98004e1464154101da01e12000009140c1c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 186629541 1250 186628291 186628313
    0x3020f1605130203010e04030507081b160f0b07062c01060e0a090b04080c0106120602210408071101030603020301020a030b040c18030b060f060c010e100618050c040f03 74
    0x801c850b00c80750211081c2c208800e90000b403042800c0d2013040e20005001c2030003000105005407141d40d51516240d108210b14060381005036211059521a03080d002c02006d54a00e1600074000e941c1500642c1480c1c03080e445460b00c6074190041100d0780310a40050700c84402c0841211100002c00b41c001844003000781d6500a0800740309450f080085003003c502455064428081c48035049140380c002607031a511078101c0382c3e03c44041c2842d80d41d40e501001a41200507904000d8a40c07152030b02690315085034414101c144041241302100942d06814080001c90180880d224590b00c00b030400f01d081241401a0014800b9038800780d0503500000e181d61016030315074807550401c0b2003120100102c40b0108021100b13072034225902c00100c0702c031090a2000c902c991403190340c008002080c00202d4080c034008104a03801034508002c591f91510400e091a1200348522554071419020804c03445d49420303a1501010192607000205a070f4410101e21425604001c45001e01f00d500c1c1800055607a925021125030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 186630791 1250 186629541 186629549
    0x20903161215050903031b0c0a03030e07170a0f050c0612180f030405040e010b04090807051911010305091005070e01020601150806010825050405030f06070801060c03020f16 76
    0x24901080c80180902ca1180314001c0718144001c508550382d91050300b101450455a410340d44206028015100a04002c2002110b21030364010a02d800c0c0001201d141c10380075000100301e40c880001401c2503503000038030036401c0c0d0b0301b00d03c00c044207074200d003052800c00000f0404103030400c0c07000031040d02000c44200401d0080e5103195000c01c0031100e040d11143c6680b800c1240300c0e5603420822007007000d0310300703a000101e8100034400001110200f040c0080c00f02c40f0707200b204445944000c1114000c0c003c0c2440040102d003010010800c0e1000183d8500d2014040c03a0307817440c18181d941c004103442440030400142c0c1c08507911130800c05824103640c050019403544c0d40c0c02c1d00520030100007050b01c0c04903403110000780c051034584841e42d481d10001500e030860002d003035495074000103864100c0d02080d5101c543e035140080e241c041e40d85040601307040c1440c40c0c0c403114501550114003440386256104030480d0440d202881d181408008900c1c00300d0400354807580c884181d1144213446001c2e00c08058801e0122 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 186632041 1250 186630791 186630803
    0x3040c09053c011203141603090e070806040e0114040b09070605072006070c09020a090b07050a1e02042a08010303080a05180a050601170115090209031612 68
    0x5409141d4000c0440707455240011440004400411039440321841099050f8400c1c01c2c41b8002e06000c0c02006c41c1c0d074004900016040043c141008117260308118400098280902440111f251200014042c0c1c0805000705008a907941505508100298010f22620707820000c1e5200d05d00b0641041d4038140c100b0340d0142c00e180140080000e8170344c052411160b41503070000e641c003400342c07181d20108208039207902c03c1900f22008005840001e0700308a00e04000c5c00745001c006842e00c00442d0b0041810b80541c0000c2c400d10010068100030440000b900c514044d030000609810801c0401685115602c81000039080303402c280350703007124803208809490445020f4800c00310b6010020403c4603201021b00c03015000c0742c0c454002c501c00c0d82c1182c0282c2d41c02102002406c41411605100c185001c0380d07141d003901c981c2c0144c4d006001700a0341c00200d040807456600284030350b2129441d0300191120901c104000254001940340d201d407424012011004d5880000c3e0310050b40e01e41c0040c5012451040846035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 186633291 1250 186632041 186632101
    0x312061805153c0307060203030901050708070507062705030702040b01020d0503040b100e0109020309060106020706090e0a0906050106110606010507030804030f0c05030a02070801140103050c0603040c0905 90
    0x250502c096000070706094000f4844101c4403004509001d0b001001000450314038444032040c503510f0800a010040c20103a00543c0d07079103026415107003118009051030080050405c20b200d0403551081c2503d00582e08600300040d4a0740221500f41c480206600d8601265030801088041c44004005030030254000d072020f00c6600c028000498403030070580500804584103001050118258040c150392042c085010300f01584d840305440d0780024800d81c41810126000000c10030103441c107100003801840503000614866050901c0a0103440c44c0e4000c86030300e003100300002050b070701a45d0426000f103900900200100d5855480041a00d00d604100c040c551241101060140d403040040300e02d6190595214519502c956808481d1404d4841200342044a0012241c010a1080c001001c100c40c40380c000300340c2285482105400d45415054405000ca20000104003090b4081a00e141400c0112030b441d6503a074503032404001462031030308484100ca1809080100b45094207031004410031910110641d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 186634541 1250 186633291 186633331
    0x3022e0905031011190203040305060a02040303112d010207021e1017040212030c060106090602071e2705010603060306060e0601020c2b0b0703110a05070312061805 72
    0x603513002803010361010008002c1d80711710410310f00d845441c003803240c41034a24181c1d807a1203107071030034005603012004150b00203001c00416400003400403c1558405c060020314031300c1e01c526800310006100040280001c40401c2405203800c0d4111010103500900f017030001011504800010001d20000c140140030300c81071248a2801044031507007015041790105000d0b0364541c2480742060841140418500c410311003496915001d00085029202ea9a6821010352824000030328001d01903000d10404410b030005408012800e540c00030a41d403e10b180101154000304407002c002c001c01c220428041c7c0b030b020000c51310540c503402071011240601030501107039403141c00c043ca82810684d10a13026a0044000c40d6641c141210300f01d840125008000550820483d0084070411000038200c0d10207030101d003003100c0d0035058411607490452200b685418080b0001c03001e0b003503100e00303000602800356078200e410f00180b507600080b002e05442c955031810b10751058804e030b0117480159591103400345000085d04d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 186635791 1250 186634541 186634573
    0x60e1e030702010e0406090515013504020609030a030201063b150d080409180b04080c071701020307120c050a110106090509060a0c020604020a03022e090503 69
    0x9804450910255140111607801034402140c01c4a0b01d80c0c202d52158000240305c4007500c12030b80b00e848100c4002c0c2c88510001c00041200c08c860164080d8007211b100003180d82001c8a090f01c1d0703c101e80e49040307445900d0f00d000059041c0a1484c0d038946c94842c00c16120b0405070f0640202e41120400c0e201e20700c9081d881d85198130050b4080c0c0d5540302c400e103c280c04450003c5c5100230650002e58028440c4141442840441c80c01d03600b0b14401d4a280c2400501004000f0b41842007000710000040d25803520f5a003587c0781407440c8405400a01851030104541903540001d01542c070003001c2e041440b2220180070071126010f90022102140490440d0030215660001801240c030800400c0d070b18149007855101e819a8201012a41d00600e076507070b4400030412140c03078460580100c1d8040010b000510304280d040080c1c42c640138142c0c0071500304005000c01a1100c45460064030b80c1202c0c1c1480035440c1e074404003101d002245060010b018060011030480340c01c1510718040d101c056003620820140d0591803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 186637041 1250 186635791 186635833
    0x30a020f0613030f0315080109020a0902040b030103020909030d06030f02030609070305100e120301030b180a020306070509040e060106090f1703030411060d020a2606090402060306030f0a060e 84
    0x50840b00c20026044001910407410400000131a05000600c100004610320780c40b00283c014280c103a540c1d0600f0b006520b0940c54040040800200541c506420441400e19902040c8402401001030304081548540d0500c00c0e25008050340c0000c0003c0c964a040c410202c00303501e00141d010b40101008110317100750110704c000070340340c0010042800041c0d01c00007800800403044132b00c0c4107010303d9030030042d803004020003540294050b4a0540307140c103001d038403801850b80e28104a201c61b1f00c1900d07070388010389022038100d604c800b2a080440c1c176a04404046001b420300030780c0184050082000115516401506250941e101303540030300d101c66260011940800110b40260314a80c0c401c0c8002030000b502841c2802c03003d030b0042e12031400c00d11a4400c80043e600805c00c40d40106086501010f503100c043e0140c2c145000b96508003030042d04020000ca00d1482014002a00903500040040d1560320100701500030080b010b821140070005e00e04199000300000070b007810352409583c811304121260421a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 186638291 1250 186637041 186637051
    0x50d0215190f1e0e01050d0e0303070207050109030b060f04060503060a09050d03020c06150d050f070602010f05060d111207030b10050a03020a2c0103050a05060f0114090612010e030a020f06 83
    0x8401d60f0a0100545015100f058994100031040100c940801903a000c2c00418003c88001562a4108040081d0800007075400441c10440c00c03100403c00301e42e50106558101c902600c041100c1728100300440c015000e25017000da0903219a0041c009503c031a940552119405241541c80c0c640b001c400440603031094a41d80170050744841c0114032000d50302038040171074032801000440364504540d580c90901c00313071648240b0310360040350041240940a014291802c5e103100710030083c13460800c1c00141810b0b0080c102400d0038450007000032054445c1c41803902542f500c081117400c11690303440c190700540011501010140c0200f00005003604001c00c480040e603a0080c043c102d42d5082c1140d1042c009010031006010074052041c40b10038201c1e4441080c040d502841c05003080c40028200315142c0200075000d03015034810680104504400181031038910003048a82a0390380d1220400107110000c081c4800c174095280c0305442c100050008020014200d01d03401751b40078006d210304803a40f55441254 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 186639541 1250 186638291 186638327
    0x60c030c040e0c0904150608131a060f03030f0a12050405070308130e070c060e1609090602040509071808030f0904020a031401030623060a050d0215190f 67
    0xd0082102d5802000e03484800c3c15690782c20300604100007800c0d9080c2c003c0415940806820610031950302c503c0e00e65005400036440842a0803d956200007107104da000851402150f90110307030b1950f1481e10307018100c007000b0100c80d110803c0c0052020243e01c40100071000c0f0303040082c0c04524070440d000d8584115004001b5010903855600c0f9406a0380c40728040510340039411802040d124003d00b000350142d40c0c5599500001c12541ca0b04000302d60207089940140d60007481004400003414001d001074503c18100071601c0d0300c152038898003070b0056400241d130000d0981c1c200182103600003a8503904003900f4002d54000c41d910040c10b86c80e4407402250481941040000c11124101900103251400c114600000d0700c5000c1c0001c5010b00c5001e8000300d481589841483c4520010703803040b4034041c607401103501c2440c103084002848075945481407601a16024141405560320101d2003504542d134180c0503a602c004c84140100d0004a00c2d1046011403000359540c1d024503c214241c484014030300d0303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 186640791 1250 186639541 186639547
    0x7090c0c05070501080705120705072d080f1b0a12090e0f1305010c02011b020708190c15030b010906211d0a03030b180603060a050705071202030309060c030c 69
    0x8001180c5a00009140300d00303010040000c207070300b010a0800746120301d030107079103042c0c840320f0038330700110414008124030001e210650402c5071003505403040030345601c2c0d20009141d40d907400c03071610150600a001c0f0010620465001c107107540600420707041112842039107020b08031160f054003a9282c89490107080c0c104503001000500804008550723540100c0d802d1000c081100c0d0960ba80d41c2907404907840b40d00140d4640001c01204000316a05a12006031400900381c00c3e0f041c014425680d80c141c1080044010f850900203040c08030307680c04080644400307058a041004034000150142035055484e90018820b4480018590f100d40f078180d01c140c035584e003411017904000501501070900724020158030402c07074202034600078040052480481c0b180e2404031f6820700840801108106070545d03a04007441c40300412040d0b542c04903041d64000c100c00c030300080303685404508540602417120007d0000c40d4040803041c01c3e036000070155200c2d81d031000844050b079031004a1103001d80419165095800024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 186642041 1250 186640791 186640799
    0xa020f09040b0c0d090602030115120b10030b0d0609050f0625200102040603090c05030d0516030201150612050604090210140d02190908010e030a0e030c0a0807090c0c0507 75
    0x43c020100e6200c214004070b40310020b82c031884120781c02030f0b1001050603d200d0901c800980c12005100d00115958000c00c80c80840c0d01c007007031060b44011008410160340300303514549543c5100d6512222a0801820010160300b468266a0b61140740c01d04036051041100041014003003048481001803145510030003c08180d40644d1030b41c10414055154650402910720a1007007440039200500185d0340c08a2031205908102200c000c0303e402985c001e4000f4a5201c1c2c5079074020044502c0d00088151584003603e6a050407801000249414a030300e1081e1600016126400481d203004ec1c80d1f8008108081c1d11801d0410048801401000750000500c1c3c0c4140d1105003e400c103204030120400f503542c50080c110316440308aa012a000e00c4518480503103103000b081d03101620b0400382981400802070800c402d011965280201202e040420141002c0890b1644050191882e400405400b00311004d46501c10262698003d0003502c040030700c3e2403590304074903109a900d1a021034102000d80122410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 186643291 1250 186642041 186642061
    0x90d14090102010e011401090f0204050312031b0307030203071704030e12010f020d140609041509060e0f01050412051201090c0201021615061a1204051e0a020f09040b 73
    0x503400d2039055540e43d0b0300f04055002d00780207100c0d0b0051140814411507040c81003803811a003d555103880101d105000a214a03100003890800d03000c4504100f42e01c0b075940022095050041c03041a01c1e0b26100030040c00a0aa059000b80d07002d001c1c1074445a2502080381110030312500c0c21a40900000d19141c002d01460500a00c0e6940c0501c3d00170020449140e400c60f036400383da1052100c100840d5880c2550100c40e002a00751603080030701120405079604042d00c5400301e005851506195141d5920454070411043d6070000004e44a154241c070601c03c5041d901d00d008000c100d40c00d880d840481982101154410300484071400303181a415840c03642010030300f20040961072400c00556600b0400d4505640341218a040c40c00d101d00c0d0031b4070000b0f000d002c08034155080c2e580190030528448445101b4581c4040648803007005a80607074582c0e503224201070f8600104c00130050207030b420520060450305804a5040425802981e00032040042d00d0103000403104215009801c200c16200410000b00c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 186644541 1250 186643291 186643297
    0xa0f060b1e100e0301180204150806010b0a1e05030a05010b091810080703080304120203030114060c0a0204180302060609070203070209042a090b0307081b011103070b0f090d14 77
    0x10b03516004401c046074a002c80c0c00c60300138080810703400b80784082d20030451030540101d1072005403034801d41c1030a40c80c100265035243c2041c000c0407034074180800c445a0045c45641d495005104c50100b1155a0688107009003186d0b03c146c0e03c440f50141440b0010400e010004200d600340c10015041c4500224011845071481d20040d00b980307400040e2810001d01100c0410182020f1402000c51035034900b000e00d007136602c0c51014403445040d500305000400c000201c1c0d0a071100407103020b40341c550b6074181a1490303508165070f0340002035001e403904d01980805a6020761481c0218800d030219001a182d81c01000402c0c03804640c0640181e000300403800060078854589a0400d201d1903000c40301840e00c21084113106400d80c0400e1038608104d02c200455489406046000c040540142140340d04001e401c0741c54021036269601e5010b040211900143d11500701007a130f80c1044815281c80b8170b803500c0e2440700c03c22b0a961005c20110800c010a07e405404034501e00e2110040e160950071081c3c4924070207180d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 186645791 1250 186644541 186644569
    0x250b0a090c230a0807080c010f110d0302180307030c1a041a09011b020310021305030304150801062a110613081908030c070203030c0a0f060b1e 63
    0x15102040010b00101e108031402c1c08000740041034214840d001c8244480344030140d01600c81684200170800c90a500468190009802882c2c080706000e0300318400c1d5032080c03c2320034124541c800d0804465442c1d500d0b0340980010784040f800e488902035a0003c142c0e80e11031034000a02140303800f00c2c08010b103107a040b40e100199103414040d1410203580b45520b02011f991000d400b01c40400005802c01c00703690242c1e024005d0065808440b0004a958001c207a81e01001c07106800b1455001454000748103035070081d0780041000400303ca64481c0c507101d11100140c001c43c1200007003420b5000114215008030144880580e00c61049100301d100385050004e003030040c0c1e01c1550400009000c1d5041d540300c210052107085511a007607495240b5081d065440e2514041e01d03800b0800103a0148000922081c0c12607400407400000b5544440c08e07400028250b11500b039084001d482000003510030841450122645140113520800500803034805000358810030103000340312503900b50300591540c940f41003054801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 186647041 1250 186645791 186645803
    0x1406040b0c0a081305030601090e1c02070b040b130608060d03120f09061506030510140f0303070515070201061a0a03090b0a0209030c0f10050304080d02030c250b0a09 73
    0x180b00d510b030f400d0264810031095411300c003085410f015a0900b08110f60041903103403010000880c40f250344584803e1607058110711180a00d802c0200c00d0705c208400703000b178005010b4243c0d8566407a0200443e580c80190101b00e02699204001205030007440591b2062402606071181450740e0f03501210303890034908140c641d0300d5407121084104000c902c500480144201c500044804203880c1309030004207203500c01010181414200028110019074510850312000040106152100005000030610020417909440081403040a010001910b090b00107400301b001d41ea10303243ca890480c213035002c5001d100780880058a1030040840c1c0c110083c20032820511300040d01003038aa070f400028035000c0c3c0700d502c0040e8020909451502e03050000ba0f00028081780c9000c09030702202d0115540100894a4200380000440014180440202150700484915000315a00d103440421000350382c00440c0e40c8804040390000100c401002134405894194220b01c0c0e02c102540c0e0700e100b0384040c001c50003007120f507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 186648291 1250 186647041 186647053
    0x908030415060929030a0201091403030c03031003020a0605030106080c0d0912020106050a09050411090403051b060f010b070309090b06040f0803030105090f04110112090218040204061406040b0c 85
    0x5580c1d20788a80c203200e00002c04803d04115130441c0481040030f04070038113032007900940384000c0141e1f040b580c45001c90300c411510030001701031000020300314091034244616a0100204000680c92480d400c24150b074400c440d8200c01a443d0300046550b40024010321010984000106041c516584041e06081e0050308000c0384c04495680c401035181180208640507031344a0009025500d090441c20300544140c010030886032400d87c5a90341605801000b0502503405100483c00b41440f40c8211582038400010109103941c4007442140d555030101c443d920070000d1000080381054460085130b180503010703558417804c103082c09812402000c21845007a800320081000103645001c100845009000c49005542c60750b1404040c003454800c000c00801c240e040100030000001d9503507c600c0170103202071034400d46850380020302500518a0100103584480080100f030781c9800010369880c8100e109481c2403001940d50a081c1001a002260b40f13684480180000d004507448800640304261800e41101c103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 186649541 1250 186648291 186648299
    0x60806042c060121080912160f1a0711010f09260f0109020108040f0303061205030717250215030106020703060b0109062a02060417010f090803041506 66
    0x310441507140035101e5000940100b03d191070305512102030800050b0310000818055a60281d00d00c40c080f0f056110700e90030035801e50700e80b030104000c114412280c000fa403646074403402c2c15401004540301e031480d619112103000540e10142d030b003524410b0703510080100c2c4040118006588004902c1000c00400c0b680d94030008840596540007550380d501c82e40c01e11321076200100100c0c01c0114204480000b0783c104580c040050343d02001d0190300540101c9240460100b5240031006080c16510a174a540c0400c04c0034030511001100070001144502442401b55401284d401003500455501c2c0f03030a00a4090040d1440600008e4200900d1004050005005006880100031382003070300030740f0060340211001d0080190718858103007812801d08100503564035081c0c0051001982606071105620302005074811500b001030010345e61a8001c0805458030b803506c1e001c41c0744c01030f10441450150309200d4401440d103081c0c40b515400a80116074140b940d616520b400d2400c242c2d5034102c40b0515504c01c1c00103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 186650791 1250 186649541 186649601
    0x1b0605030a0207051510080606030d0816090b18010f1d010e010c140604120c05032b051614120705030702150403050702090106030c020a060f02040306092a06080604 72
    0x1d03101b00c40c0104461556400d0980e211720340740000304800d020ba84000d5507a0b07001604840e040794080041c19020036041d00c13162003241c580e40e040d803211910200208004107180701400c2001c85541d002c0c0d883e41c64211050504440e0b64181510340120140516100c8050354130502d4035030550302041c1007240801803555100002c90803030400801e007a23080300c030a1100300081880c121001c0d1540341b40503640300300175444003601e80c81034038040c940b45903481110340c144030706080400100c42e0030010100701a250580c0401208014004140b0002e0504284200701050038005c0d503046844c49501408580d50380e02003074900303a00c05468541944500030070394a650365082c00031442580f00f07544041e20707840300381305010313542c681a00408149402c0c044030410780d50303000401701c41e500d80203030003c503500c40da4040500083c4110b800c0500034604021402090019001000105420012040724080340b0107020941b040014007503000001c0c6400d01080162810350020b0040c3c3d84c0c003003006011801c402401d6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 186652041 1250 186650791 186650833
    0x2070e040c06030605030d0207290712080601140f070206040e010f0603140103021c0303020f0d060807050306040b040b040804120605040b0117030a080c090d030c1b0605030a020705 79
    0x7140c003003034800424040c031a80b42c082c00340101429001030400601c40d05021f5100d0007280603108204617400a41003021030308a0300d0030700f2481140342855980d2098142400041440144000400c5400021034550351042d04400d00050707144490504121241e001d0103180d1303000c000242e074800300500000c24136001d400b1703545000702464507001003810b2401c1d40140c1500d4001c04000103100b2030400400160719401031200c0071001c0620985902d54151900340c0081c003a1038811a04d11101145a400e082c299501034005e036508042200d24a40d5182c00b0140d03103000444d0300a1021a041c2e0100d00000e084500f442d0300184240340690800d034803102804d00341c032600803040d0380c0b15841e4000d02040c049454525405030000842d100742d0701921000aa6403441460079203001c21502c11700003011000d645040d1000700034001e10030300c1c007030015040083c00700198550a580c40a415070408103840e9040038584101e03003440c0c50700c40c116924050500d0081d045440c00f6030300c03030040d030b45009800003000e80c039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 186653291 1250 186652041 186652043
    0xb04060903080f1b0d18030209190f0501080c010909090302120a05160c0306200301180e010c0203120903091f02010b0301050a0f0b0d17031e01080d030e16030305030702070e04 77
    0x10003000428030b000030301c6da249020302924001c1c2d620f501800903858001859500141e04034901c0f070300310084903400d001018a0484011058a07100012030b090300f000c210021003c80c26a035132030300d082c1c50340303801c07001c4070000381c401005030f0302c00f410b01c5c0314551010f0090302800005051803410104841802410b0302c3d07040c6022140c0c0c2068110510400007a0f01c500c040002d1a404034458448013058078a0f41440103000301d00b0001c00c40500101003100d01c1d0841402418084024450b038503d50300065643c0c2c0080c1d40e101010104040010514034001041c1e07491a5401407086d02c6d00f0812000354154030361042250f10455488a0001c0741c151000d002d4103014030b038000000591003070442d208a04581280c800140300e141040e1000c00441c0c1e000003900c0d40c02901d0301c01c10359030761601090700d40c0c7c0104888091061100480000408100114101e013503024503403802d20a4540c00c0c10750380e031201490a50a000200c20800910100348154040c1d07500c50b81d41e0040300c500c16140c2d01c54000c110800c40f0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 186654541 1250 186653291 186653293
    0x115050706111c021809060a03150603020f060a020d0e1f020c0f010c0305030402120a050609011b09030305160809040e010608010e0a02060403140a06020d0c08010b04060903080f1b 79
    0x2540740420345280d03d0811036110358074085040001034005010752051000c80e00344640003c43c04030710107540303a1085000442e80101030030a4860301030b49440c05000e1500c4140d00c244540c0c40807480c5411720b80c0440d04000c115501405080410300e80940d102c44d40300f50f104e50000c0000380400413007140180400c2c6c1505c029001084034807144804c000c1c010503146c004904200c4000d44403c00603410500356030b0420b038100c968101ea802040320f064940301c2e20b080050300718071510741403112103030040d40710a07041b4141c4800c1c0c030101030851800b03503000c0a980c030000340052402c2107a0f0720f00452214006508511600c901441d0030462400038082e83d00e101c2460b04a03035910001001091001d11a03919520104009402c1c0340c07605400041d2a40218407000c3c0c01400700c20440c106d0740c5d60901c41d080c16298025401c54481d00d142046034000e00d00160964080785001001151000c2228165022540580d0302c01d011141160340f40360b6140c10040315105050781c280003800151620060014003880044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 186655791 1250 186654541 186654547
    0x60902120c1003020c100f1107030914030604020604050f0a0801110903011b0906110f010204140f0901030b070516080a0503070801090c05090111160b0a0e0117011505070611 76
    0x100070016501e4102c24840c06051040042107000c003001300e00d56480046030080000c0704260146600c0c082c28600c40811603001001032640100754102c4408030940b04e094134034501480c00a82455030f00c5c1000d40c3c011354004000d000800c118030702000c0360510740e60050072000b005541c80321101e003950038084115600c5640455210b0740c6041c01d200710b000b00c129403500e0380300030004114041d00000c102e01900003000101d5113004200d95003007140c201c0c0e4003c03802c003c40d5a190388030310b002c035500c518141c0303140725a00303600803074800d4034111107414146c941140c01c600d000c1e00c07000e01c203841d40d80c0002807041000d00780d05000400300e801940030b4100c031016038442d140d813031405250003800000141c2010443c0361401d02c601c090240c0c00310945030026002c2c03c0580c40b4072500c59406207041c000501011003201c9983c404140c885001006d011503001e01e84400d000319a4003c01580c403201000c2058044003c000d00400c4414122800558031003d5810110300c0d180168481c0d0055801e18200d88031000800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 186657041 1250 186655791 186655813
    0x4240507120c0c17091f030207030906110706050c0c030105040807120801120303051806090703020f060405131a030d0804030206060901080604061a120f0c0603010503030d050406090212 81
    0x60007400050120b500c2d20456061481e03460818420113130b1007840910501003081d950302d403250302e030215100d44c1100c2c00252881400800030007a61104030b080300050b955440004010380a803e22010502c40000a01051810420222540c0e0403420f228480d9204d50144401c3c01d48081c4600780c0101e018071071507a43c1d151113051102164a412000a04120001004201c0d650000035019003003980f600c1d021a41d510344079180150a04030084211480c00381009000c0b040da00003415104a0b40f00740e071140369550404040003014021072266503000043c0340c42402e0b400406500c003214404601c035091b000d80102c4c00211b07140900783c42c2140003007040f89051100b85601040300301d501013422a2418031560602c420203842c1c0e040580000d080340d0300c5100d00c40c05003400c220244080c400c0500900040e5100120441d039079110b502810059020364882900310381080e1003100c0c141d50300980150f01d4002a2603409000782030040c400d440d495641c103001c074016a81c0800c90201e0020180042ca004c10030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 186658291 1250 186657041 186657077
    0x50105010906051012021303060606110d05130911160320120d050907170718050103050c090703020904090605040209131e03050c0304080610061704240507 68
    0x907042144603001450440301c072107900040c01e1048020705c1034056100c0c20312a020400c00d64031500010000b40c18490003245683e07010b001864811011402c0b030380f6001c501c10701550288281c01c1c080c224400404401d0020034030300e8002e8807070341d05072514561400e41c002103202030240c484c150841c0000c1c8010140301c1c040034100040b41c500a000009010005492108071460348180345955602c1741c1c9500014542c0e600c280410401040c81c040811a40c040000c40e10b62903900764050740050940322604000c0d090a24441d032810380c1d034000001c0001c81040f80c104444040024051410141c0170000100546c0742d90043c009101c1c031401b40402d4609107272041203410314004192011070b4801846c0b400100c2c03458024500c400350102c8140785084a01d05045506124000300300140d48400200000e805400042d5188903120a0b0a48903407136440740c0e421102c0a072400e800b60720b070605c0b01010401286850007084c03590b1801c0c081d00b03400114440c0c1c1003004d4030300c100c03a5200410307400c0d2500c0b002c3c294 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 186659541 1250 186658291 186658301
    0xd08130503070801061202040504020607240e0c0307060c0503040b2b0209150c0c091914010b040618150206090d0509031218090a05071b030f1101020f070501050109 72
    0x34459009201746800c0401c02003400001e000301901c5561160040340543d16214200c40259401024019001151040d04030128120154400c40c1e9803030401c842c08080004986060000d40080140003190f2900408803000e641886d01581c803800100000142c0040080023041062007004002071403402512501d101580b81c2202041c80a004100c1c003503243e038072041e0a10000d0001c0160984030100c0c2c4120624050030340c1a49900005a482400104003640c0071900307422800031420301501d00c0411490702008030a1181568401040c041448110300560a00c02807107000700382860034131b41e50014034a19092540010003d608098103020221206003d051304c103002c9402d1440c540a004d001103a6101c00403103488680300001b00b80c1c91141006c40e4040c3d100c4440003040c1d4001420100c0c0510000e20003a10a80c021070f91214602c0d50640031194954410354154441d440e54078038a21003501c1c1c1200001606c070340f955080110004032808840580845406100000b800d90f040400306800c9403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 186660791 1250 186659541 186659549
    0xb0a05010b040b0913110f09040f0603050a1e02060a08070e030105070e011d0406260d12051003060509030901030e210a0c0501020a050a1704200d0813050307 69
    0x75080105200c490b03c2c1c0301c01c4440c03484007a58028107088121000000900b000000c80e43d40407000200302c02da02d603142001d44810001110100040000d20356260201ca9007844000c20540041c09a00e003c03d001030100c40e66a018041b003800400100c0c0d0000d07180380c0c041c5500350701094010061000180d88502420310300101038008010301c0c00e0400c4040c001d4284503900328100241307a0b00e01200307110443c0b5204a001c4001c2d100707103c003503142c40d4040803154158034046442c4041e06001d040b031400014400788803034226115800400140c640c841d01403c0010101d0900416402c4004000340035485014419030240c0069501c0308650f00006099403c050401c40103139000f02e031186101e031050346080c07544c222171805095481902c040180c1d000060b200700a40554408180100041e4100780240800c0e42070b541c40c9580303181400380544940e20107990142001c069504078401d80c1044055030041d00c040113048403255081c659800000b6404100311600b480c00504040099007000c0000710058 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 186662041 1250 186660791 186660809
    0x90b0f040201140a030b040c0509010f02010501231206071d090c18030a0f080304020103111602010809161401092408040804030203030a0306050f0420031f030b0a0501 73
    0x2a05207600000d01890880122503c00c02001420602c040c2c001c1d484020311340805042841800c544e04c10203441500034070b00c0c1e01e02080419078207075031661043c070800c0e058400f14062150100620b46d01d416004000c15112900515403a4040e0018401005150311805840e964882c00c18580c0002d110741582586205010701440f0050000c00d8800005607410600d5040150740100c480000183c503001c020708004c2c2070741d81030002110501030240001d6105900030380b03081c450803611707080d654424403c91007140b0540e5040c685e00401036110fa041c10f5005042c01d0221090854900050804012560b00c035003110000e40404501550300884104001c0203180951615a0842c0407040d14581104200c0400c10460310300142c2008202c100369400355070040d044946a2601c203001900400315406507500c0341c1150803006006103071034000e41c0c82190201044e03104606a4030846801c6410140400640440c2440c0c0d181c81603020030300b084015400342c1e00100050400c08a008100c5e181a0803d44003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 186663291 1250 186662041 186662071
    0x703030e09060a0e0a050103030f050c031e0f040807050a0503030903030406030902011b060b03010f0b01090311060904020a0f080708100303051308010509070609080f0c060d0902040c03090b 83
    0x800e4004260503614802910700340e115035030741400190000d4190b0488041500c02c42c00340451610294052030503288241c03543c07118081580f40c00e40340d0b402880401941039208006280300203480407502c80c48801040c00e03450500710085446c1360103410036005406543c0c8a0b01c0c0800051030008110350003844282c024520301800710002c6620381c0700f1802098140b41d1601242411a4070480c030080621103a0024078002002c1f034940341c0c0c050041369411520a40c201014030903e04094401d0804c095016120302e02424550f6843c4451140c0c41d0707103c0d1b40e00c22010b1107040d00540340d900040106001556a20741a105680c001405040c409003c0c581040801c008011110000d011100e0940750942411030f218a0082c0043e0300320422508011065400c190a020400d0750010341c420a40d030b81034940001060725403c0c07242d601d880c0c510581d503590740110030351441340c100075004015083e21050046207002d821740105080e14a000300d40400265240045030070302c80200e00c020f400080e12029000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 186664541 1250 186663291 186663293
    0x1020d02180a24051218010c02161401020c04060e040308011d06041e1a03070518070302130e160305060f0312030703060806040507032604140105040b28020703 70
    0x42c818030380c90190f540d411142c0750149543e0b80501c2c01d840100c101078280c0da00e60710b041c911019062070b85000c0001c1c90340c00c4c000226926400410b07400c00c0c54602c02116110145003000d000c048400013080306055000d0a18043c8460300c4170300415000e40541900030480f400c00d450001c0c600c0c2c005030300024103009145440001d500c0f46800d0550820000c4602050103c00350043c903031015500301841050318644405401d051b032010915108581044090340d02c40d5659206101c0780991040b120180380710305030700007400d090184c2d01500300384000f0500104200d0700d8007407499211a09642e9108002c807600801c0d60316550602a0030b80c000800d45544822540071408256030f00c103690701c5060000e01c00300c0002c00305442503020b20001d11301071040701d80030b0601e801c1c1180c80700741a020542d983c1c203107081c190b8040140c042da010244c2e0000b11107a4545031410100c010300d8040610700504002041000051401c1804060708038210385c51510010003460064070311040302c207410560199000008104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 186665791 1250 186664541 186664559
    0x31d0a050f0c030a0f0b0c0f07060c02120f091e0d080927040201030c110a0c090c05040503120705120a0806010f031a060d02070c030b1008061b180301020d02180a 71
    0x4805546c880c81a03180c6446000740401350b80502c42400c2030740400800e55000780100ca41004104c24041d809403403502c0203240c21817960f40b1942d903011542000803c40c0d0b052606040700c0340030807045201d4400216035a030b01c002034000c80d24030070141c50503900450448510700d8480308a00d00303209c034581c040c41181d14030820804000c400800c060f06059440141034440e600604544004d6a00702c000d03603440725030310724000c04158841c0c01402c00e603502e4030003100c1d00a40180c00310780980d84018014001a414295102b40d103600645c812501401842500c100c3c40301c81201411015080303446003841c03840c0c0030000420300384414900b10101414a101c0b440b031a0754504491401502c1541d51503511128045124080d03c160a8024010b1548910000920140748451030081d48070020004401c1c0e035603100c0e41d513036a00030b48007490140091030450491a00102c002d150140180101e141d40d002500300003801c9800c100400a51140c0002e0340e2034002283d03c1d081566040211041040b641c01c0c500302c0d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 186667041 1250 186665791 186665813
    0xe0601051003180204060603020d1503020f0d050f161701110d0b0f090a09020a080705010518010c020d0c050a0b120109090507030f030c140105070c03031d0a050f0c030a 74
    0xc030081c103542c0d080000c0b0902412543ca246140c01500600096650f940014001d610000381c00d1005c03803500b84401151060032101400f00c035001845c452140c0c3e40381d800c1081c480440e035001c4585104110000319054401e2060700b40e504141710120407568036200e11041c040004c40c1c00e880e40d6902d000b8135039a09611040c00d40385041070a200c005282c200c500d01056810107294101e0390b01000c031008100701c00340c168010b545180d00c20790301d0200140d43c5032035880d5200914000c0c140440d04c14881282e200c510002414091101403516504480050300840d17038041c1004425203c00c240f0703040030b01c110708080201d0002030250f5944586810101400c2ca0b40e540c0b01030144c2e6031003584403600300003400003c0080074051900420000c0300100a8500901110740040003112002d120005c01d01c1d03a40c0d018401ca5225035941d0b111480d6110490b40c040b00100f6042d400264000e003d0760400110b601c041000040300780c4035a00520300c05258518040c580014800d13518841e40c054640749001034890740344 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 186668291 1250 186667041 186667069
    0x507090905060616060203011406040b03070507060f050421050c06340e0307050103090201120b040e070803091809120d0f020c0c0a05032103040602040302060f030103060e060105 78
    0x4005955182c61000400c40d20400407626459140c580201c1c0600c60582c0c0198100c42d90005240c10b800c07000003d110717403170280f4842c00408039828000144018050300007044018801d800026088852080306821600c098074143d40c0107400700c4c0c08024218200b42e103641c04c0c82c0d89003403107414951499451340d9240d100811100d4031910b01c06400c010311007203078400b42c00d90b61000c1260007500f074058030041c900000803010f030b4400e214481c0300080c0d650003407141105580e01a55038145c40b281402d20540940b400c00030b006d0700655903c03081440e11070b05102c82400b13415240007441d91000301da020880349803002219119000d41640c144085401c0005450300400103107184191204d0b29501caa0008081200345031015600001301b940c422000441e000b50002d40413512550700c2074641081c50360f2044100581e011081c01d01428201000c1d411028560151150201610780ba0310303580070840540280362119400000480180704101d8580100e001110984c0010b003100c0d07160400207014860301c0304c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 186669541 1250 186668291 186668309
    0x30b030c09091902040b0901060c11090709050d050f060703060501090503150622060b040501020607110c0609030a150e2b05181206091908070212071706010e0604050709 74
    0x20f20408540f607580124581d04401002040c0542c1d58040c007030140c4880042c00c0740c2c1c80f210103041000500d13003901c1c418001c80c113913580d0904140c100350900c030a00051300410303240c91141c4000710801c1402000800e106010a58012828600d004005480d603c000e0f00414403a4000782200080d115000034038a0340180300321b6040030003007580380f21603040e8042131407060001800e001d03010400e000004000c004842d0280e085481c5170303550035411a80f401d066816080e0940201e1f00c00003180c60501e0140c60b800c503004007500ca56030702d1507a5040c0081c2d40e8900e00103466840707001550580c1c1040c8803410003130180209401040c1c040e0404084020511000705060120210b44e814085981019103000ca80000c1c0a14030304840c4500c1c810366401086410b032205108140e4800d20003105101c0e2404e409034405605818002103a080210f070355408400e040710b40c4900140002e86409580c7c088075050002c10281506504080d800120040d0045c1201e0103182440140141d555001815004907101c400f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 186670791 1250 186669541 186669583
    0x103020901090e04051b060a080103020112020c0102040e1b03040c060c0c23030c01020c03060c0703170a090506010506040b121005060705010506090702122b020a030b030c0909 77
    0x3100590701401c0a80260700c200381100e04104c00c122002800c070341803850550340039408013141810030056100d0140017a001900c2c8100400040d40944112508054045405424820100031183c00c80c1c02a5004500750300d1150300388400700718070794005846500c107044e84a2079440c042c0c466481181062048600b0401009550380501c00b01405038030240400305c000034001c04401c800390b0f2807420b46140c17203031203401000028009580009008001214081c1c003511046d80c90349100440750b00404426400e01500041030782d04594184440c40c07080081440006640c640390901518251050300040d02a420401060040384074040039a1110011071101c0d11140c0d940c0ca00800525015502ca550040b2010401d01c04101040d04802d01c505c9081c2c82151040d507030480e089a07941d400c98980c10400c001002800d001c01c1c0d03415503030880c0941610380040307011030080150040fa0320005003400026501c031059400b501e001d025482813904c3c202e810880c01d00780920304541740c00490154180e42c0302c2c04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 186672041 1250 186670791 186670807
    0x6540503011107050a0f021f022805030307081902040b03071821050f060c04150f09031509240e0309010507120e0a031401050a1a060913020304080a02070e09070905090a0609120905030a050606010302 87
    0x1010c42280c1900c008041591110b589501c60b05494206a4041e40400c40350050f000c0111740200c000310840d48010f80104404000e0329003121100d00c000380135581c60040b50550111003008000c540e004008052185544e40d260410062880c0440500b000401c0100d81c0341d444003035030080300402600e07004940324401d003214406a8004280d10707900108000c00c004102950400e00f9090619940f107559000e0107040c3c50b10400584900c10701d00c2150201e0300a210314004554081c0d2030341d402070a02d04000614110f030100288540c080d076401111201803d240d805900c9500b806800d80004280d042031049418a4141902030401400001d004801c0410440d001c0d640b0049000c3d4994200c0d04210758074200b0f8200f4081551281900d00c001d0712900703200040801e150f05880c2c2c41480344902801d500d43c20104510080c0c0340160000b60148181d80051011030020b00c46d030b012035032041c00c0458944180d844040c21210882d03101d03a2081e00008070120100c1c2e40031401c01c0e03201000346401a41e513415 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 186673291 1250 186672041 186672061
    0xc0606090708100e07020a0c0905010501030c0801080d05030622020d0623121005010b04090e161401050d0e1606540503011107050a0f021f02280503030708 68
    0x41f0180ca504035240c000148482c01d507005a06035031081ea0144038134108400e0540b13000380288038181c00355100da0824041c0920400c05113800c034070000c00c0d000c0d42c0030f000c43d089800030b4803c10185441d030b58002217205d80a44640308403401030041480d00d202e0700b4500c0300c04030024a4420509030148900c01c04a0300c83e010144292440c081d0b407500108042c4d40c40d00450741d201c3d04503010707006ea158a0501903651050b40000c203142400003121803480c8450406440004100201e2455814048144480141e0745224001c1c130b0205815000205200880e851400343c0345e109681c81402170110f000c030400400c00a0b40c10f201000c149540a40708806550f102080e280c0c2c0210690b403c0a03481d150507041d184003000c01606c100c0e00120003d01003c1700348e0310807902c3e40c442c4003801089580186602d5000030921210312030424002400848030b000c1c2c1d009805540301c0d01a11640050f041881c81d4215000031021800481c0540c820003111451035517280f507a43d210190560042c440d1503000980c4a4031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 186674541 1250 186673291 186673303
    0x30d1d0d0803010306050f25030908070f0b0601031a0d0c05091312020303060607060c02011d16090b0f010c08070501110c100c120c030209060c0606090708100e0702 72
    0x40098094055201a42014074042e0400c1c00212419030414000c41c14454075254198002c0810201140d002c0010705850b4010b4424401e41d141859260f2000c540800c1d81c20005d81030403809020490880c41951074098400742000f01006d041c9480c00380c1115110a000d51914443c01c4141c40300c0c242048541050712442c41d0b50b03404070b580802c5820400462940c20500d1031600342c4942084c40c110410424142d88a002c1160107580240c414000240410f0141e005410445000e000002c0c0a048012600303001544038803112900c1d43c00361900807044c40145010800903c00f280040000988810009050044800c1b400e4100a034851948017400005802c503513003140d04c04020800c15400d0301350220a50041300c0c0c1c1c0d540340d00441c2020300315801907000d0304207100c3c07280e6140c00305000c9201c003200013482621500c2d02095828401c01005032100001001c10010820052806241080230080010b00c010005010403154030107100360b50b6442506a4259111030920140690b40c00c1d40803880d01d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 186675791 1250 186674541 186674597
    0x70f080309010b0102070911070602210903091009180b0a080a1a010e04030f18081203160c0b070f14030a0b0909030403030905150c07060207140f030d 66
    0x1a00205209020300e055000d840340100a80030388000030b0340c031500b4808640d01040c1700c841d0b86038208048000141d0950043c804429149032503151016800141c00b40320b41c00704c803140030b581c0c0002183d043c2d9203407001c50715007010964503102c0849810b04011015140c507120b0034030b090070380b80c1502c0003013a0f50b428002406800b8070b0040341c1e4060914100071507030042080d1070200800001001091080ca401c40c158442c5805480d0011120100350044074000f18028405021040c80300010078080001d014110b107810103040c00f90344906120383c0c200383c0485561494802d00c5805d8962800096030b206020b5842005414000c0b070b10b06030310101380d51416040c540610001000010421060001d510000d80c402e4142c45002d180e95844c4481e42e0342e0710440c0800b401080c17888200b0042d9180c01c40c08161841d44044406003801d02c149149881c1c103026820080c05600142c209009079440d1400042543c2000c9850052100c1c02501003034039421031072108000c0000b14008045203104e1305c42c5d2203441e8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 186677041 1250 186675791 186675803
    0x903021203190501060327060605060d09140307050706081506072f0f09180d1713021e010c080a022508061810111809010b0d02070f 58
    0x3071034200140104a41980c00d00d00241e0f1070680080f6445110f03104a100401c0d00c0180e00c107080400d1220601c07050005841291850784429000c10240c580602070302c0c4840d4030075030100d5503810074600854103842050391205194400c0c40a0030215000180900480f4418181888252600c603421040b181c0407403401500a0000a0010100414021011182c2c1205d06502a07400e6003000e507245200f0342101d0b002d5001c25800c5116040d841d0403404550401407140f801000501c00808181c20f10038404400008100e580200c80500c10103000b0707560340007400210429030b518040e0b00182000d00841982d28608903184045441640a071461000ca150480e0f00d4545480c44c08000030741d40c400013001903c44802c00c4005080a20001d160701c0b040d1512140500041d9503400001410617144003102e41d140d200380c0229000040c40c51084403144660642c400d60389042031381e02101e400c2203c0c115035000d04c99800040060034501425500c100c04c149001580c2c812403420310101c801044100600f203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 186678291 1250 186677041 186677047
    0x30204050d12020c010201092f0301050903070c270c02030705011119111009021519090e100e130501050f010f0803030103050601030b1e100305060a0209031009030212 73
    0xe000e01000b8020055402c0d90840c0c3c4030451441c0121300741c9488001c01080725107603441034103844809050a01e100404e240803045601c8241c1d0001b8251502500d81042d15040000d550b001d001c2d580000001a0140300d10202c0e80e07e107014681100403140072030364038140390350744107c06e542e0340b007030040342c00e0300340c204000707000d510b01c84035125803a940314944102e03505690783c030b40c4008180940800034503800d4140140514408140502018200e8250201d84c4041391b01b0140900c449420f0107043c3d8000f410011749144109024054251a4182c00030510281c54004104404a120201d001500c0001d810070445840e02603012032040b80d0081c3c018415400c050030060b02d408070900b114100d60890f00003c2c4031079550103541d80c0328802800054400c2d00094014800f241510810320707009458500c040075150001a050324064005460b140d48164240c9810010f01004021071500b2840200045103030a26480000340e4030001d01c0000140603071501c099038140340c028010302061100000d29156 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 186679541 1250 186678291 186678293
    0xe040b09010e1603020402130308040305010b04060b0c061611100b190810090219080f010b0406061d06040e01060f0f030203040809130914010b0102060f060603011203030204050d 78
    0x1485804691031401580380c41c1d1071102e8080009051144a001000064002425034090101a502c0b01c009138030700c00c4201000100040700240200700171801000000f880040b090b0400007030380c08a5006141140007408200c54050001c910103411210082d482640d07101c03035803c1901e028414074000e8034240100114000305400641080004070421203540c091081d030f0170f0641c0c2450f1414000c15120743d00080c2c80054080300703640003ca18500041c0001c4161000000700e0807010055000010b20703400c001d034044443d15003401201071665003150305001450820340001d05172103480c030300384405142d9040000345a4441c2c6044070040e0070070211106440d82c44010140060444900d40000070705142100c105081c1b1a10950740910b610000851602c86014104243c018499070b20040803540e88050700d000449110003004244c100800116900d1504000a810044002c010380d0100041a007003040517035401003228150b030300340c0c90321200b0b600c1e250a080b402400785803c805d0300040c0504140c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 186680791 1250 186679541 186679553
    0x405090a0b1603050c03070801060f090b0406030608010c0305150402160b250f1707030b0301090312060b1c0c110106030506011802090a0302041a15030109060b0406080406150e04 78
    0xe140b04610392000d20003620360b802d0f890424402110200b0024862100600c51148280c102c10744607000b5180900007691540340509242c0d2080d480040426910b910030490781000380900d543c1e0f0000d070700f010009840c0c8031a02c01044520140f005214640c0094409240e810b42c050030070b04541c000e40c0d041e20603c0c04009026074a21280c45036405c1000081041a90a11695007901e15942e6641e48140c8000300e2015503600041c082c2000c0e0506860b0343c5405050b0301c00740b08000c80c0301e010782d032010a010310141d00e0b20f003220303040d4000c542d050504000180005030b1140099400c405141710000e0076501080303049070340702e0305096010825401d02c0c5c800002c1c484000b40c014184d03070061088040040711000050200d105980c0da0541041c0100410005850250b002c8180700da403841c49104a4007584c5c0005010442c524140100f03404088014032081845204900181207207541c15886c05007041c1003d86007600007000148641c2e150b605d82403201400d10041300042c502c01c10300d460715050516000d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 186682041 1250 186680791 186680821
    0x40f0905092a0406031e1115120402010c0f05070f06090501050301051908030c0a0b06040902030607110f0708060a0b102001090c121a1005012316060b01020109110405090a0b 76
    0x10348114030004406081841d128504c024034180b0007058a14041002784400c85505004005034148100c1c0c0307040b40c010a501c100c900484a200f0b1000d4004d080c1803412070000d880444c0c00401c00c0003144c41c070a10003640c00400700d0781034038411500c800c0c1e010102c03c0f1110903198140c00c95211404049540041e04200081080c141ca1007503845001d11340e502014007048608070b010180d890340c81940400c00560151400c0e0382c034003d064080d01c64000250340014034003040b6901c0303400350341c7c0140b00b00324045003130784a401c9505500300e0b95804801c09441c00148181035049149040900800d1058559a402d500c00d43d00780780d00c00c030034401642c0c0e5241c850070b01e001442c80c281c64050108030700101c42080a000b082c0320701540c1324956007460030500116002d09140b0b0540000c00070000d100005008820042c020985018a4444500c0c490b498400b06a0341103242c40d40c150381c14490601c0019072440c4400246c410f09680005060751000020340c980112590f014101c40141c10500082c0301c020000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 186683291 1250 186682041 186682043
    0xc0910091d130b04030c120906180605030c0310030213021b0f030f0f0409050907050328080f070606090204050a0f1404050403090b040f0905092a0406031e 68
    0x10000d00c460718840d26900d818044861441c1d18a40d6031401c030000e07180306041e80e0814044d150080390f084807542c508100c030744400300e500d001ca40c0440b010000c46500c403c0340301c2607039000060b0220b01441c00c1d00182403401b028040380d10809000c03000488400307400b81a41c00940d0020701ca1904504205aa600250312101c5174015422103649003039081a0000b40001c0c031111000c0040d031912101c1642c81c005034125200c81e004a01c010800040d800b441030043c54002c01303c0c003001d403c0c26450101014507281d0b02c2804201200c58480c5941c0030101e080c5691001550000219541c401c0c108205040c944600b84008181515041c0d010400c118294043c0c815036100740c81158090362102800c00c4144107920552100c0d035183c0319000183d0610b42c00c100c1e0001c1c03183c01e041c1c102546680c0c41b503110750081d402419680d006040d04100220841c059107410004ac0f0000d02001c5082406244c41d800c1c55004040e2103c0d5888161003003510307281c0c0320f1001184c10400410f0380300000d00c00e000ea03802514030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 186684541 1250 186683291 186683309
    0x90f0a0c050f030a11130623040e070e010e0421030c02011a060315060403050303070e010e010801050d03030903020f0a03020f01060b0a0909090206210405060903040614030c091009 79
    0x29082c07002e4100000c0c0340001c680c0000c10700c40301451510030441c40355454001d040c0d0071501c1d410005482e040b6141d400408155090b641d2103a0030240c000d0104a9004810090b81d95001d8001000381ca8403120b0658107460800400b80c021f40d4660628100c40d00300ca180394404e0004e80c00d05800314513030551144a03400c550703500070710125203d401916030f50703032440400d2540b02100f0804a15060484041481c4050018081c0c03400c00342c1c4e0780c0b10329007940c10403540a80070800301042010fa560b4407000142e40741009003040d5040d54100b0380821032100c0e6602d0f005048c1503882148806041c004c1082c2a0540d1605040b034414001c5440d0094840d00d000d20b07900716660034100701088044540054414508180d0356044405281c40218401f4100101050343c22900070400018110349043d0701081c480c962403403251040c1040d241003071078000d0040900031f03141c00501c0188480c2d035100c584076038840072640c0a144c41c0d0316500c007401c42610032080f04640c0510050501a401a086018030044801090f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 186685791 1250 186684541 186684559
    0x301080c01120515090402150703020a03230910180f051509030634051207080609061e120105010312030e0c060706090c0f0807170601030b090f0a0c05 66
    0x929600251501030352144111138038030081d44110704103001d1040d8441c0c002010b0f015140c5068012540c0c5901404c0700794016084074014005141d0041030001500d4a40d0f0180a0b40c212000403a407418020191240c1c4104102c90480348403912408203146034040240181c5c46280c1d98081c4032956590fa1300c01c3c079001e00b00a9a5121001c1e1070b8509a4464103405405099966a200c0780104000c60008015140790440e26200f0001c0c1410072410b08040c03c140c6510355a100d440400c9044050003c024030208181c130070401419858000c2d840e500304c1070a07070f2035400071002800c0c0c502c2020740092030329400c100c080840011141054020300d0490780100001252044d5610089007036609004885500743e01c00074034205207041034001004071a001c0c1000041e281c48564868035140720a40c48445032004012060003006c109111f444020001154100c29000c0c011a00075100c4605210181002c1030880000c0c101da04107016600a42406000b5150a00600d01d4101780c090168010f40307025070311714 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 186687041 1250 186685791 186685817
    0x302030a0b09060a030b0c040b041e091509021c051e0708070203120c0d09050a0201031b0e040e0f0303040b010e012c0703020c07171002070206070b04060209060301080c01 75
    0x1245500f4090341d4050504030b065030454071000c0802e00d001d040020029400c1000044a10075003028201404c3c4048200e100390040c0c020384226130980da001040e82500c0c0c00840d41c4542141d03541c1008582a6920158841409400348506545030705200307130441c1c0c100f070b04000e05a0490303c5200b421800c0004040129199008216642c200c00c861440c0176034000c00009049085030754556034480c004102c0c10b440c0c0750081400c441a02c4c10401c04079089c0d40201858800c568050145524881c040b0010305440142e168004000401c1c1c1c079171890003103944d11034030181104184034440d0b2070028803007101c1d0f132070810b840c0000401c1000d11415442440c5030002040c110020040003011600440545035024000284848112805894601130603802c00ca40004500c052105200401c01c0071205c2d010707034402840302401c4c10349214450308142d20401001005944210598501580000025601d50f6440c0340c003900038440e4218082e4003802c080000540d54000050107080003400713030780700200111070f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 186688291 1250 186687041 186687049
    0x160905041b0e04030c0f0f050307050609030f04140402040503010207210306150315080d021516020d1103040902130303021b030709110d0c020304150e03061303030207020a060302030a0b 81
    0x10381c0210140b141081c1c002c500428400c4100a403c240903002ca800c51111030f94030b40c040b40c40c3c0404112000c0d0004180c07a001d01c82c0902000f940854010081d40c50507030740c0840d040b4207114601034100d84c05600c0c000d52585440ea6410388010300409002190ba070b0407a801d024402800c05000401c0309041400e40181d0341e8444d024160488105001032011051081010f038090200d149600125540e420310000b50342c1d03c10000211081d00035000303488030700303208410651900d100412481c4001e01c1b220348100b6082d070000d44820000c226103030400181800d01c903020300318807499000d01042400401d281060024070442c0b00b04492094088900d10160240d5405402003419040ca80c9a000024200180c00d000e030070401440c0da40030400c515103170700c02004c00d0817190351031071602c016030000c02c1c20301c03800940c005c0240614566080c5462404039000020340d0340e000003400e0f0500c9d503a10380c29600070140260140c441403540209210152910b862000380203400480d02801410b0034201b10244a081c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 186689541 1250 186688291 186688343
    0x21e0a0509040516060e01030c0915051b030d0209010e010305060f0603060103270201110f032b02070f060506040e0c060a14040e04020907140d0e16090504 68
    0x1005842401854a048100149004000c00c1a2898080c030307012030301ca8a034002c8a0202900c002c0c0c40f03000010404071b000408039541034140c4418003950302e04c240000c41c0c070003140c08001c040f507180c00340d17031403612481103250500c000103820090311000c1031031900040d0360b40203000c8558082e80c41800c1d42c9209070045040d500705844c0d850300094a524000c80c107003481c0000f190300030310606000c620486940da0300801048a40b0480d5100802103500d03000319030344040c4000110400c2402016040500e0b41c3d0151280b007086a1050428010801802882d651500040c405194440c1c115140e01050403c11028000003030200e44403483c24001942501c0d05100314007070360302c10100800d41e042080e4140501c90b84008503070818406028081c0d00003500d80301c0184043c00301400760440d01e060510500200040240080080c0100d925030790803062801c0b400d07686001d04140300460343d0581c0d84d04440c20608038290246000d4880d0f400415810500e801441c0240d101f02c0c6a8181e03050031a4018040c02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 186690647 1106 186689541 186689599
    0x30a09030506010504050f0c0306012a032307171b150a020a081f0302091608010b0711061b0d080103120207360608070302 54
    0x85014002c1c580140b00640f0b00b03000c00d00b001aa4011100001000004000c1c008400207415070312a2200e8945031122020040f0656016640c0c030803c0414208140c000c500c500040711002054403807075120802400c202d2030304040540d600e0a90003820004280b8100f1801e0000341c07500da039560120402070030b00300d0003001d84200308490600b134000b0003800001d0307091050081c0389115811000b1194021240c0707820500304140e07400700568003003043e00060b41100b115001c1012420485041042a003c5030700e480d24280e9071001e0b2216148104180244001808084a4458102800a8004094200092107150001507111854066a80c1888000900010040040c0200280d101c3c20702400c1c0e01c0586409402d1080f03080781e82100f0b50802521485540380e0004d861103001550b4020118804203111883c4e42c1d501259585850b0b010591284038620800000903415800c1a0310030 = true := by decide +kernel

theorem cover : BRFrame.Cov 186510791 186690647 := by
  have h0 := BRFrame.cov_init 186510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 186510791 ≤ n) (h2 : n < 186690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
