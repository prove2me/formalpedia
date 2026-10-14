-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2513
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:55:49.987052+00:00
-- url     : https://prove2.me/submissions/e3d3043c-eda9-4fe7-9aa4-132ee667c99c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 451798561 ≤ n < 451978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 451799811 1250 451798561 451798573
    0x212130302040905190318081c0518061818151201060506160209281d0102040308040e010b070b0f0402030f0d0f091d0f0c0706020d05010311060705 65
    0x240c1041d503c80c100141c8658100c4401c24442c01c0041200710441c01e00320002400c49005003c400c0201d61b041000f0001c000041120581e80e080c81040c128201680e0003c11502090210000ea0440c1c400000808007616080d0750315090000c0300f10f00007500b40024082c5980254403400381ca851402548503200043c55402158000c1c010411980c1031026001c15a6495100104582c1d55920090008000405102c50b080c0c0b0b151051007143c2100900c40007003506c404402107104400c210780c84200c0b900d4804001445101c0192a00c078850080c0c6183c600340d84042404010848084014825a0211000420682c2e603d0324140d855100d200401084861414003240c1d01181d4180000d41182c4014140d0f90750415420006241020140f110340000318030040c0340307024503081a83c400282c50071a00d080c205c034040d4a00c01c51407507400f9210040703129054000440a9894801399004940d00c40b1040d03540340000c1d42c001010741401c0c00144d40d001c50141940c1031500e00001102e514650241c081c0031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 451801061 1250 451799811 451799813
    0xd05071d01143619020307020c060a1412040302010e031801051809130c15020c0906010c200405010b07050a030e041104060c0b06060a02070e0604140f0702121303 71
    0x9015000030b8240b201507000802c3c0402507074101c40c08040f420303602c401010618504101140c1d9090074924035818454410401c0c001403d03400301e007074202000c064440907518030011504548080f0a00c10242c0003600229507040e00001503004540580d000342d0003403041c4154020a2500c0348906182c0402c60005101c0350507941d4014805000c041e201004c0701c058500007413020036190501102c800a9108107907a24a0030486483d149101401030610151089003a03400041e686407440b100c0302d441400e007000044e660b60300c12104003526540c841000540601400101c0d4514a046400c091181e03040000104007024080d003910f601d01d40000007400c01c0b180c1510b055074000000c1c91284d40054407001103924148258009000502040d903400541c01c0c16814216100d40d0040d102500c0791f4400c009480d425907000540308107689100701909166216840080d008060542e003041896244d5000c1008071010006102e00c106807a40035541611203c40c03215045106513125003801b5103800201740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 451802311 1250 451801061 451801069
    0x30f1c0507050a0f030b0d06090611161106040302030a0b09120906030411030a060e0a032d11011e0b100305010b030a0f020f0c070302130504050a020105030405010b0d05071d0114 78
    0x19180d001030708000031000092008141d80c2407c00400360340c61134607003440c1c2080000701d01c80c404d454122a441107082a91070303807010811103503091000c2e18140c04041654070035035846080700c0080d50700804881411039030b8039000840842c2107035104828003841c0305d001c0400c803840040300c40c00c2c28003d244620355035a42c0e031906054440c8507021303a05403041350a1440003600512070003200d042150024070200c83d491400a01e1240c84103841d007111868940075204441018508000d8034140303040102c0306001ca80150340c0103224040002e9924403a00c2d066400f031010903030044801a00a88108011911150094080c2c84081c4104003001a0400005416074100c1e8046c4034040340244003d03141c44c0c0040c000c18400d4214105028040d04003080800842c9000f82e5480c54001c9029000d114510307064aa090329250310810281c144400040000d0803c0020750200054030380003409410802c1450600070303991101c601070500e04035040d80b0300c5403103120307107009990481d020072105000301d0a0b124144 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 451803561 1250 451802311 451802327
    0x191208070e011d0d060e010b010e0f01030506011715090f071e050c1c0905030a150c1b14010b0103020915090a18090c0f060c060506060c030f1c0507050a 67
    0xa442c2c5800e0601c03d0002507a2186840d500490080e1008100304c09442c0714103084450000805040c000180181c1c161900c03050741c242100c582c242400030712981c5c1d80c0b0058490039207000c0900143c0c90600100204448841d00341c0b850780c0f509031120300d50f941e115401001c01c00c0c0c00380c8010002c0317400385505076140725503102d40070000002e0389001e40c2804661200c0625011791029100076403500901420101c0340d000c1409802460100c009000303900e410f07203030f41108002c800f400991240e254400340ca0b031540078152051940c4580c0004041c80d41450800003404c2d03460402402d800d50074100e8543e400e40c828029100891002050210480c0d0a0307103060070b00307038400046140c01001c000e02c0040ca009002254044100e2004070100d15504107103002d139001590754000040400f0380301d1061090681c0680003100c11a4024800211a19640c2c0010428041c030710340c0703c026200c002030a40c10210014003030214245009209007650002d00c412000b5030341c0c11144400011001d2142c407402d544a0b51b40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 451804811 1250 451803561 451803587
    0x14033708040615170c030d02030310061107030c0605030a0c0305150d02150307020706111b0d06090803070c020f0607020117070c1a0f070305090618030c191208070e01 73
    0x103010061a601c04200348135600060060425401541c5c5914450030103104000c504821440510316620780640c080a8034800c03800740a081050016900012200c10041100516002001c02141c10b0761a00000c0039540122404030002c1e0801c6039031400a4001c0c010039010341c0b01c240401d02d001c10305d441800711000c1c4448050342d0000440c2c05421040414400643c00707035060350f0150198606146020788a25250b5080e42e00741e81c0910080b00f0008072219500948280448042d42d000b429400c01340b020300450007001d001d0040000602800139000210076207a40d1094aa0100501d05042000068066804080c2c04904403040c010f81c00020405881c0d80010903080100c1c1500481c1c42d482d0b200181038a1015150010f2400e0088462014104691095061030140b005140c07440100d030b200c2c00003030841003c801114258008483c0240300b1380d502d805202041340c0210761481c40e0f00085c0202c401c42940d01c101c440c0c90200081c0d2044d001c09201c3c09041c3c0b1a9551404a00011154058004c00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 451806061 1250 451804811 451804841
    0x71106040c21170901090803030f010501030b032506030c051314180906042a05131d010501061404120b181b0102100603020307090504140337080406 65
    0x1031004000b40102c0454400c1c002800f0310680c45200349000981000059040341407079a00901c10450380004841d11103042d29000e00e40840c1d01070101001c249800b00310851400405160f4451082c205225965102100c801760750612003680ca1140545651055044160401c881e5030300600c4185500c01509504010181c0513804080880c43c1c6644081400c0d200081030b1b4002900713100c00d102c60340f00440e46c0c015007a2884c070380071510002c0f0081c101085104980c000c10203e00c83c2c0c28105590f500464407200d242c40c2c00d0b41101d0b11252494001c0609000d0500801e41091001c213519081006a80070b4980c0350040d400600c0040d2031341422958020814031003807002c2400040388502c24481e005e201c41c0c5a94645084000794000a03083c21500b01500c4041c0c1c2c9007a2007080942d07030001310705084801c03040300095107842d5424540310385a44040100700912001074200d041100d2658000041040c0b1360310310a07048050b0484103800810041d650700080c40242c0494040303003450307002e9541411400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 451807311 1250 451806061 451806119
    0x11041d040611040f14240307090506030903070b041523010605030408030109090f061a010e06030907030f051603150c0302030609010308130816080105060604030533040605071106040c 80
    0x11251180050080c007001101d460120230300000580008d220805002c0880741c0d1400d40c5450b288140d036074094118040c040311000c0c0041410320001c0b901c40e541c00f5030900014051200c40c3d034000268450001e94030081c0c0e009a0000040c1c0c1da00c154252401240e00c0040d0619591030700c4940c1e400340c00603042c103407800074100c0d0f080000a0228810301c1c400040d00c0c480065900d2300300c000540558160385241d40030b88000c00400100300e001160307010669030f0240008642c0301460a0007441d00034071240c01c104841e052000401032200ca11808059200342d40d0081c003800340c0d144030840c181c0c04180c0e0b820350046200001400081d0b68a000307004a00b0200e801e40080d60750f1000904e241590b420700c80400289840018085102d003801003035030040c004c0d0f031524940b924603580c07180d441d54500c0c00014121000100c40603000345c0145107100c168048181c0d60101c0c24907080550040500303a0703560000c56402d45803251030502c04601035220726001070384d41902030701c0c00d0b41613040c80c0c00007149071840001d10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 451808561 1250 451807311 451807339
    0xb0d1b050a0e0a0f140601050a03090b010308030105090a0c0c1202010e0105070509033f040801050f16020123090705030105091c0203071511041d040611040f14 70
    0x140d07400009102d24000b00310541003003441c01c0c003141d40a00b0400d40f0ba80c10469562104034560392041d42080003860656903506a02d482100100521200101350601580c000010311111f41c01035810713100121034134030b8141c58055944007210305411190012138202907880340824072000040805002600000c26034402a00d4420f085590413115040418001705901d025410100440031742c40b20801001001d07030180104042d040c11546401d0444d10401e010240305102418003078070004c104400080c0031500b0982107602d0100000c44407145085164040ea0341c105105024122855048046003c2d11403069183c1c0114000c0080c420119403160100c0000d29403001d1048910803000500680901480b001c00f03a50348082d1001d14604550080c480c00300070038580340c3c2901c52540d0100e8000f81e0010a90203090403401540c0c00341507041c41c0781a00c0c07015800d0702102e04c1c5c0315074414074040080235001400c40340d107402036024803007014607225401c1c01807074442042400c0104004000e80200c245c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 451809811 1250 451808561 451808569
    0x9110303070b040314071104090609021e0f04060506030f060613060509030d02030f0f090a0f03081b060717060d0f1b120809191a120105040b0d1b05 65
    0x428021100140e020040009166001e0346113807082003065440c86c6080e1075a10342810340980144814410303503403600080204250741d40b01001580d80940f03140e1016280004401c1070141e40340300341c1e004041009850780149054803c580c2074403002800e03a4117540f03503e0000c8a030031000a002640014080105420b030016076075a20004002031b545551792050208141403c1484040854066500600840940000700710580e00a40c0c01d54000e1620f80000100040c0c0800c2a5406400819100340001c024171808000a1054403c04410142e039217000c080b050b44d0343c441c2142c2e038a002816408504070596032282c0d580347c004100500718100140c0700e0701d03060840106000125004002c1d0300200c6002203022300000b004060020501c10901802d488401052050b80142c43c41030100d90411176461051520410140503080e00301024500c142e140d50303406078400311041c203c01e5084000007a151070580500303669400701034030304070100080b59516000c0c2409104000d110f5000300d100132601d619 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 451811061 1250 451809811 451809817
    0x9090412201f020c120d02041a03011502070501080112020609060d050601170405120f1b010f060b03060607060c05120a0f1a10080a02310608010807030609110303 71
    0x18045018002c0164041c0c241c450505070301d80a00c507010b0042c03003580b0400e200810711034080c078604040c4e143d07244c8046122030002e2186030010008041031885501c10807011a02641c16a4607401d01c00801c4600744800740d0b41c84000b4401c2070300040c6d8010040c02458070304007242d4011480640070318188151140040ca4030742164001c0000b00b551807040288540e440441c00083c42800100075100342055100c0d40c3c0c960302140703d031455103200000c0300c42030500324900f00c92521950141005200240e00e40303c0307010703180354405d000700325081c088041084102002202d00800c1d00920345851f2031a26900d000c00761070b0280007442400b00074404030580401c40807200e8414800280006070002942c03592404441c0070944415400d410f80702010341648622024050401050502200540e40c4031a0900a4031503150b126185444074000e003010844844000080400b0070626007003040c0c0c6030344040341c914500b441649400d1307001e4034042011801c1613000c0702d80300f4021a01c0208948d20f40c40842e19580c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 451812311 1250 451811061 451811117
    0x20d0501090507080f01030c030b070522090f0c050403021003060b07030809010f0504030806090603071203030f0515011e030b040204030506091506030304063f0501050609090412 78
    0x3944a0b0108000c00c1e80c0315031440e07030140400d4140c00c00d41d41180c075914900d90890100174002c9128801240e5a18015415a1803210401c0060070002c00aa00d4505484802d0700c10000040c2c2440d000704440481801b0f4401d07144e40c3c035520300d41010301c1c2d42c081140c49009040c0c00704c14542d0303c510108800580f40c00400d2042c0c02511210094101004810301311528070111200040c600000d05c40025480100103800080440d00a003944d240c032030001e424960664004005440100030300c0003016015004648101844c1500f0403079a40c8501208103180e4603045150300081881c04885164150045240d8204d04d540c500060a0890140400d0403a401900305440c543c0c0070f20b00304005500100840c82c810000c248090510b41064004241d683c001c601074401407204080c503000001006551510f180301c0c0f03441841c0a021907040c110f84035485101c98554440e810100003258a04168044400350712000d4408181035596884500d4500403101c0c0e82e40400004000d0070706210300a964070300c104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 451813561 1250 451812311 451812329
    0x305070611190807060203040203072d0f03030e0108091c030e061006080115031b080402010f09060203040608070c020a080c03100e0a060209030a0b0106020a020a05030a2004020d0501 80
    0x8074401800c45840c003000446000368484641c80c0d0300000807246000d4030442a0321034000b40e203e807650710005e07051040d981c03c900b00e942d45545d040c2014854603518402c0041070040b0039903080d500d0310910780740c00c24240406004142c0504401d1840d500c82c0301c40c540c1c4200c014003902c0310700864542050070000a240d540000a49500d000343d0001c6041c041c01c2d81012100411070b40d6146458005004108140308030300440e1701d18000200c14034000c0d0041c40418016100c00c4184101e11003000d04805000d440c2a40001d00701d002e0020b82d107006131000d60985000c0d400441c181864200221070450008003024200f0003c101c08900507210400540c0c00351510038003404051802805061501120041c40b00b042c6040120b1984c0e030490200700f05180700e4000c04090307600d03889000805d280011400008200c20401400007400340d5011030803501141c800c5451581495a42003090303510500756030087c00705c102c942d494102c01d450501c0b400480f010054005802d000ba80488003007280c0c800d900140750 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 451814811 1250 451813561 451813577
    0x30909070c0f08120108030a080621070e01090501050a03030206150120010621080706090305040e090703020a121e0c09090c08060a022104020f0d1101020c27040c03050706 75
    0x40700c0ea0071004d03501500c5886c008506000d0b91034001071100c01c0203450a0b018600c203000140c0da858001507511590805202241c00f0140d0b24601c2401340f40092207140405450000003017141e01d80395030480c080300d8041c1d0040405454030001131010561001c0b40d07505108185003a811313010845080c5041001c4170000018445150558412048401c084142e1b084000c0f40c840c1d40004e140c407820f646203603822180000f049134103440c0c15240b52250b40c1040001e94550402c11014075000100d074020340f0b200362510741c0061b58038086031a40d4001c0c030600401a59100c240100c5d543c0c240340030709880c00d0041961303c02d02540c9071f40f8042100c03680601036410b00200c140a01ca250740030044290069100350045281414948404084507418034200c002496000049030030b5580e0140b5000c000d03200113200c100844090324000b006103c140d16458058022651070103403074a80409402c0211119072a03095024114640103003c606000b0000c941c1c0c14140000030001c10707000c000142c0500529222018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 451816061 1250 451814811 451814827
    0x315040f02070b010611030a03020c070f12030f020109020612040f120210050f0601080f13020a090b0102010f0b090c0a0c050132090c040902041803021b0d05030909070c0f08 76
    0x5104070058004809001c01015030030080e80c1c000040340d468407003d160050319009903e12450170071001c1ea10201d00cdc1c00410101044c540791002c030b450301c2d55110361604451640c01d698260700b41c0e250400d020303502c1002071001e0707100e4480c40c81419501070b1103000700c00348142860752231301d0300c18002466a40050b8441140510085000d1040a820101100b1500e05601d8581c0000b000454028400c0c00c0030020302e4081454036504c40d005c0550342d54018060451192a0f0601c20024100007281c503005600b00740150b08680000d02c1402c6140d903024140660950f0380c60041703d0164400590f120401840401d5100810001e10a141c00c0c4004644080144175101c0c0c41480101d010354003030180980e00505008182800140780800d52109640114090042c0e000040003040d124080d0f50104100c0100403003010b9000c1421180c03000c204039500301100100051040145150a00802c0e5a104000d800c12909d420b4106580c800c010b40751450003848166501205940d900b0350446550301c01181c2c5030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 451817311 1250 451816061 451816073
    0x50d0219031d0f0a0206130f1203030f0b1e060d020f0a030606021506040504030c02030303100501020610030818061e03090c090f1506130605072d080315040f0207 71
    0x1201541d420b00612000021035422038840c14000d5009108071400106084507030349030142d090080c00c040595024180d501d410718060000010021000039290544c0e030b0101c51941c1c8241c55480c82c0c0542243d0f03128800142240c030050000103a40d42c41070b01484014400c3c0124001401c80c201c1e5034250b1515800b41e01300182c00d60701140c00480541d00041c40900c495610a081681d006c03804035400300701605c6906041e40c180c065120060740500000040103640745800c0c0513101214800c2c2c1c02c941c469942c0c1d491640300300d4032a00004148002c00c214031002002e140c1d640c1001040c00624070741c41d00c9151000c0b1841c1100d6031404a4008d0000700070459034203028007601e00a06d40c2510800982c0c6080c0308840680340d0003c101151066454224006c2c41d00d40505a4481440c001111107005803681006403080d0800c00c4111601d03030003036800c3c460750b204200302140c40c0681200482020582650344881c00c1c1c200800c1c60701d106400303070203250680d031b50380c0a41c03511865001b00069403808282455 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 451818561 1250 451817311 451817351
    0x80114040903360803070213020f0f19110f1f0204050d0b0f060609150d0b062a01091109070201110d0f0b0f03060705090f0a080c01080702010b10050d021903 69
    0x228085d0003d01608026840e1400280a003050b031020041c3e030303031035843c09280c994024404010120200419a641c508204640420f0b58018a0300c0c1c00b41c0801c4046800d907660001082c103040c1580014030391640b0101c0d0410110f0042a01e541d02608041d03c6d200401e40b0b000c403251040c0c502c80c035440107021102c0d1079120300c2a0050b005403222031070000390344045240013003003c6001901c10710025000144d980258044c0041450007041250340f02e04030b0011100000700b10003190100010030300d20f0007841e01c0520400110a600400c01c0500101c42d034100041b0000040c008800d42d5203542c6071014210300600200760000d00c410001512120307002c1e420301181c9424000354003800c0000b088111036600058620b0b031201303841c90915511600d40c004074805038011182d03d600620b045030f000c50411030200d010180c1d01800e9a50100c9036548040407822794110881d5260046981d00115a0940c417400081c442e80c80d20000c09840c000440d60280610a080a5039a0001780c1d00c0744541540344004d070310 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 451819811 1250 451818561 451818569
    0x10c08090601060509010c061509051503030702180711010c1d1009050f04090803090106081501121e0515011503061a03180a0501020a03060608011404090336 69
    0x50000b0360628034060310a03c2903004540c10f118003000c1580c100300ca1608860020740d01240f040d24155036134100703103000e07000c141d8000c0807030494403540202d0b50a00206680c1910740007032413030840108402208c2005a4007808032410800b240413200180c0400b40941d81020003942e403449030940760100f480414014151809206940c01a0844c0e24194400400c03002d540c1d00725511285614140005001481c14542c000c140d070340c0c0070040000805041d0300c0340007150186c1060b1002510000b06141e2850000d000d2841c9514103940900042201081140300d01e0b03552212500c2c9000c5d107611403070302d0b00484003404080711070204010b1040702c56040408228828078202808001c0c100ba0011900313090211007802100c2000c80040c0c104440f0341080031031184402c082e58452211414070078042d61044211401203424104c0004400341310b006018100e910b8050708a001c2c0b581c03c0e041001400e86050700754200003214a1009400c00140301800000000465058200910303591fa0b694481580d40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 451821061 1250 451819811 451819813
    0xf09040c090806270f011a0904080a08280507020c060414150d0c05030f010f031a0415150302010207150828060306060302040f0e0d05180909010c0809 66
    0x4410010400005002c942040c0e40c40c801044114041c100c0f01c10400a55071024503e01c05c03a0403e00300c074907040d8001d0264404011160751440d5000041c0a04d404083c0c0d00200102070801002c240244134205e8960080c003d007902610681c44040714000c003030b07803800281400c0c0fa900d1041c812201c0d0104520006420180e94640c01c251804c12034154507444444054000c411017001b40c6500c450060803601a50620841013000200e104c0004001d500b003281c4d00c542003010840042841a1000c51142c11294810000600742e040e03e401d0445040b405082110441c14000c00070030820800e000d40462041c14030b14800c491031950000900d00112079004081c00107442c5403161006a003e48220b0b444810748460303849842400d84209410707080150120011482c0c94400300411085410040c202c03030085030103002c0420304c0d0306414121601e00c0700c8082c0a51110000340c2489002d080039042d640540901840440c2801e00843d0804800300c0d035106440e55076158508886e600081e40541040b0b50314 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 451822311 1250 451821061 451821077
    0x6080106140a030f290a14060a0519050405040b2202090606071a0106050306150301051804083601030b0a0501030f0207140307061812210213030302060a1a04020706110f09040c 77
    0x40105206101a00a035030090352f111228101484044501130000c2c00d000d8410045e81c5800d050030051b003501642c035441c0380c0380900000c0c5100d582509070300100c44d80083c00303140651960400c10086a0101504840002c1c01c0c03441042c05132200c800c0f181c001e111a0320f401e5641c1c5045010070144003841401d0451075a010310040c811511807507048207814140d0000181103803a1414015440d008840c1d03203001c04c40988000b06108030b0b0b902500e03441c014034416180080b4426000540036110319002d441d402c2451420100300561290300512054500b64400514010803500c480b400c0f00113550b91044d0a0703000080d8401080414030600207403a0030109030f0001e60b10255251000420f22450006c208108444a40c0d05414165001039115680e17000031540c8a04103409041c0d4100d0034030054000d4051075001440c03800050140c804284404080210200001c00820000303410820058806035980c0855031000f4480d400203040c00710070010841d4131a40c03500c04020544c2c1a040702c1a04002e605 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 451823561 1250 451822311 451822321
    0x61508030313080c0a03030e15010b0306010804060b1005090a0f0608011403010f0e1f0c050d02131203110c010906140d110d06080106140a030f290a14 66
    0x4001c0d260404446610014400d09074240a18a0300800e035801019002d224002420990590301410b0301041a40a66030209907030514104003030000d22a1500004e02000026090361092060b141c0c01403141c2000116007000c04c0c04541c43c40c591038019004110000340860f070610f440071280004141d11110380d050141422402040e01206200e9400d6040c0300615520580c2d50030f400c0082c40381401d2504200c1c1c00b900c0e01030302e65a0a120801e01d62684040e05e24003558500034000e4010a10103500c40501c0d00380c41c00c1d2054000d500c601c11212415001e000003203444e000c00008061150f000740e03540c403c18607450b8510780c1011060030600d4140503141c0e0040244580195032504210032110905e916403103c030425074040d010002d1010007200c0009a0600503040d564482401d5070107a0000300300441c2c0b01c1340000aa00e050b20450396100a200e10204000b607410740040807840c1c410251034031081c94007481c2681d0403029102c283c1c05515088200301c0702c3c50340d502c82c2520840801d0340986082c206 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 451824811 1250 451823561 451823563
    0x7110d031d070b040302210a0303021207110d0c02060f19170f04082b050a1d0304050d030915030912180e060301020c06130201080c040f15120e0a061508 67
    0x2461000034002c4400a00013200710807a1f100160040d10813030140c0b9405601c9140081c000d6028004172440d4250301808a000d1030702c0359071303212000261040140207405488106542c2c2c00070054040342e02c02803c1110050f200410006806030640c1f002d6241c000004000e0060a40316407050494042d005143c00c20903401441c0900319081900050b0302e039030f0f900009022400401c0701014143d2400c2d0501c50300000307400a503203c9403107110014010450045400e9072425030040f0a50304c0c6035180e000303100074466840c080b55011851842030610000990303a4a010403200d42c807001454003c25036440f01a4144040400e01100d5040030745003c80000c01b240e50fa4001200c40c03402201c1003003c0140015401c0c1d2800d41c11100600b4034030b001caa40a261500070041d58104082d022030006001c0c0002c16208405013050f51b054400b882e60200300e1600b860045c5640b50001c0711304508003c0b010350003c410754102d00c070724015140b000029003550300241c01c0c8101038403d12030960b444901515010099024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 451826061 1250 451824811 451824817
    0x501140c031b13051e1e0a05210a0c0510050405012c0301060e06270c0c01060f03063606090510110d0e031c0507110d031d070b 56
    0xc1e01c25025110f086410b0b000300c000c6404d8004942000300c0d006100741100e41a0f60130503a80c0700c12111051040078600040c40020003850242d07030403c08050b4203000614005640800f00141030815004080c0703080c02540c904459450150703002c81c01120b0500c014140010756540350036160034290300e004e20b0701000034204c810312240366802d1004000d5060003400c07250030090034440c00800030b221315602d802803041d0041060f07449603c00d0740c40e1b2480d13200c02d018040814014402e9072801606070758a1001200503a0300400303110016560710711000c14810b4078003000001450040c10006191785040f40ca500301043e00c060300b511500d02c80701c0c0c0c80314001116003510b40780c290f101902007042451407401a00c2c00d00c1d11401110304a042282203940c1c804444080c0246c07803075052040c400c1c4154003012a44038031031004040b2826200d01682c0b080c4441540280760480d1041c03a041c40181c0382401c005050156106070f400010b81c6400000c00002e401e85000c3c0d020000200148c03810500c0c01d41c00913690b00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 451827311 1250 451826061 451826101
    0x903110402210a1b0e0307050d0c0506070c0305120a020105070305370606030c09090c1218050109030509030708060c0301030308060121151d010605250501140c03 71
    0x6070b45000050350544550450024603080010b1904400c028030f0000d4000361203001050301078410450b000910b8548190400d006030f0700021483c0045003420140070080d03210b1501969205402000080003e0701003001d90040c81c040200e85865900594000342550006006101010305240c140b04148043d14118414000c0703612058140404a0056025211905001d02c000d40d140c2f45c800210240c054014032002d10a0380e40d4054510b8555418408460454811000048032b250a2880c0c0b1000d90b031181103042c00030040340f0300c1da0445944950035104012811000108041000352072818200101d502401c1c407007000d4520340c5401001e414442c0414403000e8100443e010100c0c901d64010341c1c400714004100340002d00c0c0100c2c410742640181c01030701d0400c9a450414000051141607801700000070b414000d2840c11700764a0510215160703005447c0503a13030640d84402481c0c80d40075841d401d00e540e40c8584000b0412a00c400c00094130003000400c03804981c00108104202510010f880e50704030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 451828561 1250 451827311 451827367
    0xc1104051017070e0f0603160b0a030c1407030c0507090606020a0b10050904051b040207150506060906040306060e0a270c15020f010506120703061d0a030903110402 72
    0x34480d0078400383c079140c602d60141440c00521030034850203106103442c2a1041c1000d50445180104282d40c107183c02205100c1d43c201c9080500280c0304140c400d03000720754442028640b01200d0105000002540d91080b06d0880104007441c5a88040004c188000c00041c40442c0c1c08000007854014082c0d00c651440f000100203617082f000045a0600c00d811003006800083c280c020a450285443c45c0e0380c03070420620701d540e120a07808080316817509000f21071100d5400200c3c5c2c0c101c5901c14812001520000d01119888403081c040c0200a445110181c80151b01441c80440c0781491725400da0140e8001030601296182440114000f40010000011580039450300600c05a2014181181042d45075041050903030302da1020058074681c002000300725800e16400030400b548501b0200b09a100c0c425103098103030b822800c41000400c0b0b05a101540d809446a0002c090b90361240b0001c4c00d04502c500100d02103608140240b040c0311900c03095030012002540e04501c0d00c11810081c1110100e801103815107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 451829811 1250 451828561 451828589
    0x406080901060e010e0a1515050a030f0f02070b01050d08090616050109111c0c0618090e07030b0a0b0303120903090901030c05130501030c090e0f06070c11040510 71
    0x30460250700c45402041c4801440500356110503d680d005d410540359410580e0418407241c0200204441007001c0740d821800c105814026403105840d1600306070400d909040c0c0e0307440000c03011480740c001d039001d40e411000010b80d40e130140e14008540e554181c000c07901448406452200061109084998944088810903110050400b01016091402e00014850b5081c01d14900410510014261070b12804071381e42010800c034410071102da1203000701c0140c9000780900c01003201c2400707202140300016030740d19100c2244da00d41c51244191180300c428004540d020b01c00030800d201002c186030390090881d41082c00b0401c600c034002903482c0240a80c1019560810020500405081040f111680c00103401c41c4020360b541d0801c1000180c03a031040d14015035506511320341245882c45154113803507001d001d200007641403150390340041090b4803018200d441001c0300b00741310720310030040705114450b2566001c9041880f0300e031204002d00040642e0740241d0403d070074040c1c0300d1406041401a9224004a068 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 451831061 1250 451829811 451829821
    0x40b10121512032012091f080f0702160807060305061e01050f0426120a0207030605040503070f080903010f0603030c1101030f0c02072c0f060a0e09010f060f0b040608 73
    0x822031280c401140303030f034820076001129100005010745941b0008a9844606400c0d48000b03618806ca0030507585c00240c0ca0b10001071983d00441103030f5070084070a104844c07071074040c00c1003003100c0031941c2c0003e03c40741e100c46001c1204c154517000b0940d0101064038102c218901d50301000c2d1003c11a0300b49070341442004200c07500311203a20020f4038024a4440000240c2c0c080b0340490f900c9422002d640102240292400d40b18543c000398215a44000d09034010542039107540c513500010400580200e032140010418400030a80c5013036180e0040d030041001a0ba00d134070605c20107003144d00c84800c40e034038182806d2040010980204c440515180c0212500641d03400150040780145858416900402d280003021000d5a5000518400392044150031601140741030701c010089200904035000901e0705280002c680711903901c109508090007038018a600c94842110003c040811142002e081e0f66412007042e0659040c01004014031002c14100002818502c54a0300380c416406640180300c5d440e0007240e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 451832311 1250 451831061 451831097
    0x26091c1b06081303020c0901120302060a050c07240e06010905090610060509030f030a121505060313140304030609030e010c0312020c1213171f0b040b1012151203 71
    0x91000d00007d10704c0320b440d038603180380a08070803075184141e0041c460b901c0014100030b468464140540513080ca42c0f800c1071030365992520800c02c4003034811210b0900d181c811030b4082140c01204046444c500160060750f040007501c0088807002403996059074840c005011015105401d000300b6614689410703030340d801d0408042894020828074126640c4000202454803d5111220a114080c00403040c4074138400c0180e54403902c4098019540e210b18208003260000e10300540418900c0e04c2404c0b00100036560000f070a0860b00f1035070003a10320b50b0325888003008156004c2c200130340c061424200701c008240e460302c2c000e207800d40d08400b00c014564009007a0101600812802842c3d081403141642d907010701981d1034010a61500ca18604450300c3c20944406070303004a024000320130407009100303100565070001d0000c3c0417850405900960313240122890b903294820346110007000c1d522170540b40c5a6010b00038003124848040c0c4102d5810f180700034000c00c5084c080c09400180c042c580301000b03540c22031801e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 451833561 1250 451832311 451832323
    0x30c03100e0d0c020f090907030812010513150311030708010f3c05070512161b03020c060705120a08060a050103020726091c1b0608130302 61
    0x69040c031840140c1030200003140c200c50495224902910494400500140d4680c140e040000b0f41c8000d041d8005203143c24030319801e40e40801c2090071142c4180d034030b46640040d588640c0141a0740c004910046c031550505800d4030072481403818042200003c1054111407000386070000806448054130903140c4c603a0f0401001020300740b01c8008201440310714104200030450040d9212200e0b41900d1914030301441d01401d040441c81290b070464400020741d244d9001080300a00305418084184101c14008020392b1500c0c1c49401c1c101c2280f907a6142c83d4101a003e4801c072500c1208200031000b4010000c1d50128031101841c0041e17079560b81703400d030f240340103030800a0740c48590002e90f50204401282e141c0c0300303030b0550180605890002d4025140c10044041c2d00c10300c1c1001d400c820103004054079900b40441d0b02c075043c00c41b04102a0800c0ea141001540c4040c4a1018071548800404a00b050103c004031003070049040f841a40c803103e103000310142070f000c4000c2080e204020303410015001e1500074400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 451834811 1250 451833561 451833583
    0x605011d10050c03120a06050a06020a0602160602120a050a0b0604090504420501030803070c1416030b060409170d18031106090f1c0311070b040b091c0e03 68
    0x81c4d070b45892250b80c0e0040003000448500e416503007020b00009042c1842d0b8607801c2958040e9000e40407841e01a2039400c081c0d0300c907680409138a20450390040200f5070520240082d6580300a0300610780c00d105d45060143e400150042c40c00c4d41c40c056201c1c01d039a443c032040307504588400ca004900e80c6d9890408107400e0708800d000400c082c44180c4a40144c01d0b50080c0c5001c860340d4007894120400c01100c044040395424013004040746410008a800b007070007a06035402c818490031075503100380402c505e11402d16416418802c00030345080400e10803c00c5c829445903107c0030540e000c01000d40240c407030121160709000c9909410400040301da03800545038200000e002245403181040684615005100841d0700f03400091500079030000c90300070100172442c0703280804610002c220740018038001c200c24070718001c0580185903690810140b00c4010101800d801400350704180301d01c4c9040e04082e06503120040c0161441d0300902c007030810840081520024640d101c0c68140548031117000420300c1c04800c802c07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 451836061 1250 451834811 451834813
    0x30406202506182f1e0a090c030b014d07060f020a050a120207170d0311040608070503060a03021f090510050702040e190f0203010605011d10050c 64
    0x240c0c1514100a01c41d07030082c00c2e201d030603088220b644200e940640400d014901180c24130310040b8110b0180b800b02000e1071150b40c60814000280c2034040050390000749a0b010703030055501c4450084140760507104503002d02200f0309001655104805030310283e00b50700c02540103011600b01182802302d901000351245541a040401045c01c64401460341d140e076107102d1400041e20000401c04041c0c8080303003080c58070741d110700140362008156030381c4110121010344103811449a203100262681c41c9a03403450404c460000a86552210b00308010152000220f425008800420040210365402886103501c030040c0d1500a4503900c030003000440c034041c1940041d50081402120314044208092001102d02d01a2076180e505030f40c0c1c4091010400080d807940c004100180410340160a15030032001407000001e040c0c9803e0300c40950340d02200b01c00010b06450a070304685005085041c00d105a1700980800d0034030121400007114045c601e010b000030201e0003894060441d80080780a00b0503686140a00d82c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 451837311 1250 451836061 451836071
    0xc032d12180a090b090a0b0f06040909050c06040f12110a060206070816090e270a0b091501150e09181e0616090e0705030406202506 58
    0x81c1024801185001c4414407074400c220000444074840d02c14000301e408090503961080d520200d1050040c00c0820340c140c0c00c070508450990300f6a5030b4000810160541850000c1c4480a500f0044d1802950681281c01444c2c100401e0040d00c1c1c082101c80222481c8031500804c2000515110240211010245030002c44041000c508580c0100d010352040c05542c1d100c04060382c0f10350508001f8044200502d0100e4680741c02400b0b206181000c803544800d000001c102c144844140070f40b503030302d03545000c2495908025810010070490313010041c3c10000460080c81c0d0310303007200b0f0761040192040c45140114034080004200301c5014074480103040a00030401c2080d807402d01012110b442c0b5140d910b000a0050380810140343e4041c0305d00003144103804c0020031581c2c0e5040c0f0304c01140791019107072100b4020b41c040d0008400029824140c40741e140d81d621944c490500d8a06807090380d00f00c10032030304004800b0754182e807294003413000e840341a0b010700c04801c040c607003043c020740808900e494041c221728205 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 451838561 1250 451837311 451837327
    0x30604021c03020a0611031501020703170a0e030303010801050603061501020c1002010e0601060305150616060510080118020108010e041101031e18110607030503190623030c032d12 79
    0x3a201442c03060344023510184064a4032001244c54032070300d000c014010341040f0301b00e8400910700c0c0081e00864540381400072404d0140400249142c000345e2001c10969160400c0000d0350509104554201003130001f500072803010240049d444441e1640c0980c010130100d141c8194851003500071503035501e0044269641541c5031000200544401c681100005040c948006118140030040b65101044408990b06c1c03214a0390340c1d40302410000d412000603030345046011071221428410700303e00c030040c44800f01c6185024030000d8200481680416401080700080101160017503201d6103814400b4600000d00c06000c0007007d1035080f400c4000308130b0610b807510f6101c1510316210340080960182401506100102040200611807100001c00081051005c2002c03040381240415110508a2001c0360340f0b5243e000d11400203100d4654001002d0742c00501007030f1424144054401c4950603409400362042c110910300000c8000003200d503d450341c540741051410414860106040030250145030340728a1307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 451839811 1250 451838561 451838591
    0xb04051b01020d021207050f030409060303031112190f14010816060c140a06021612030204080a260313060c02072427060806030604021c03020a06 64
    0x4240d220200904010305461803940c000907626008100c0b650042030000340e02400000d003604990301c01c459612440d90f5926462605101810181200c0c83c0300203980e85c51801c000b019258801c40c1118001300c100a00b0820b5032000c0f015550045d0604003484903a000c0038060001480400c40214016203040422800d03c00c50781407060484062900301c41c4a011403900512a80e40c06108001c003140000c0300c2400001c102d03030722020300d14032036109841c541c42c181d890f09016a44403400100341c02d504403a004040024981440044c84000e00d0214200341c14500615541c8011000c09801141f4114410b001e804c40d404041d1031800514600c1c9880b03040482260030000121242120354a090258810851703100045220880706400141d1121221000902741001c0814401900b000b41c03200c0d40a00711740400b40406424401403640b040b00901c0c03c207000342041c1c00502460301c43d42005040c00007698841400d07401c15102c00201203941c2145180503850425a1600240701e01e0500c4c4d0042d981d104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 451841061 1250 451839811 451839823
    0x703021c020a030603060e030c2e050a0b100306050a06050d0e070303030506240715021e0a09060e0906090601210903140705071e170601080c0108090c1c0b0405 70
    0x11040d0001c0c0070100c60b00c1f0140d5200d004507410f04081d0780c4255030407500c00b190250b05503c00c0c5a003c0d10100b03200c503a05032074000c1c1d070411a1041400303603c13400b50401d9820250f4090b192503000f0f18003000f450703003040005030509a29100303007020860045941c0408404a43c803401000d404141101d010b156a40707000f0340a0710341115901e01c9007400c02c20314980020786100708114998581040391a00b41150b9405e04900b41d40d4a21002c00d90382841000201c1c031511036061038080c901210b16032100b0403000e00400040194000204101071030041854545503045481e42191045036030415030f80e21100121a02d64031040d42a440e051441c602c0c5c0703c04041c1e41d0140000b10f01a65840060205401001e680d9100d00d0304000c1065100440410000e4040341084000c0d10311030b02c000002e10342c1c0d80101180b04420386219145504520300400c0039050400030f03103100480038204a901ea02d05120082e460324600c105441c012001035800b100500381c05a002c5182c5980058180c000c1d003003906099a0b582 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 451842311 1250 451841061 451841063
    0x5070e030f0c1807020606060703030626010c0e030a0f0215070303140c094002041404150e070203070611030702120f070212100912020c180703021c020a030603 70
    0x401000f0b1603080344240b14005600c1003496400800951711401c2c02c1c0480c540c4800010340400d6a1240d02007805003014a19454200c000c6090390b052031024580582101e4081d4030041c1841510b00d80c920050314041002c900403900034100e400946140d001280100d0f000d65002c000c0e03480c001a8240801d90107900ca0140500c0704075030b041565840c9920342800e4440e1304a05c6510443ca03a0b0002c036402d4088a881c01310301c2c600c5881c1c0c1d59410540b00606004501075815171302840e0007080c2402030140e0b1002c00c5218080440301030080c065403c0c00307000b800b0407600648442803c0500040e0900340200100d8920342d038031001c200602a1031031114410703504191640e40041c05040c0365194010743c00c00a0780c1e80a11070b40790303181c0b41143d584e017001051b066044400380b180c018820390200d044120701c40e2400c8680114018518040c00a1000b4245400e40845502c40c4640003002410140130413007007640070000c1d0030016514500c1d210703083c1c683d00090010f41c0c140c2e800004e8100c0c032a503068200303200301c0e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 451843561 1250 451842311 451842319
    0xc05090d30091a07151521031805010e0108041406040f0b061503060f0102071517010e010e150418060c2a030309030c0c091b050307080a05070e030f0c 66
    0x70f0040c0300041e40883c822080042e240f15200441d01002c40d600758050308030b031000d070310040002681c1c401ca40e1202c1d20a100070500e100341c134400c81c28249504201c0c6601c40102407a0752900d81c60178400041c11441c10f4809403030403c40403500180410030350b48526456400250704840342480c00340b820702e845010b020f0007140c0b900d410700d0104080e4107005400012221070f1040c0e1508690340e407408c3c840380c44018030b0300300d0440c46000c40008004c01101a03041c6110119607420790314501101016002c944181d00c04c412032505100104541b0030380a11040d0020b001208444403007000c900014090100089a024011000a03c100420105a0110312080d2491310b641e200c606829040c07080d540c0480d520340f400e5040e80790001c80000c1c4a030380030f100c03030a00c0390800c0348600c03045403a41c602d054529000408080c0d91032281d40d140740c030780e524642c0418007a854003a186281c40308000f1724024000e0042000181c681c1e02080b10540581d1343e6100c00384003c2c08444c80d03010780e04400c035960f550b50721390603001d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 451844811 1250 451843561 451843589
    0x509030d0e01140103150908031e28051e09060405061006020c0402030601090f0b0c060a020a020c0904020303161a01060c080406080709050a080c040c05090d3009 71
    0x5207040c0619685a824003204180507860350300d8140c403003100004404002c0d50340e4940a40007462035400b071401154a8595610108105551200c81c24000703003062060301031412458010b000b0a185091030030300005800716140d1101403000c007002a000c0c10206a03408402c0811005000002c0e0091182c1d000d030048482d00d480302d420103844406180580e034016048007104080b141800e40096070800c40c10316148201d103a9071400c0032808541070304506849800080e40320003030241008070703039000404100d045103132414441000c2d603145840e1140398040e12244000038290b640a1003602e0403680c004220700001c400c1c920340110000c0040341c104040525050010803254480d4a007504a070780e001c0180d520740390400c441564600c07001489181003000301100880c4e0b41d25418103030340041840b01c00800b514890385c001c01043d58024103550081180c144800a210303a10a8241c6000da0303001000d4080000785448001c0100d40c6a044006241980400c1d854600b43d11120240440789010101e82d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 451846061 1250 451844811 451844831
    0x6090b06010e06041e0b13090606020102030f01030f0204061a07020405090319050d0e2b0c02100c1a04230d090b0306060c0a1101030b12060403210509030d 68
    0x80c15450703000b1815000340c810710090088250141d041c01d5040038095140140656502c14190142d011103c899095240c3d140100540d0307815003c1c5001070011400294190328216140100d5000148400b4000002c0041400295201c680c840405040440011503044000d808520b480382e11911080340110318000014240290100603541408044400300610b40c004810895440e000814401d5140c3d07550b000107408200104681465080d440e041101c00c9807002d00500c448403c0102c01b5014049100c18000059440e003088006581241c00d080030760341414206241c40e503c0350307000c04512221100c10f001c1480440d604010200b16085202003201c1010300485888003196030840000c10703c4d8503c1840910b4061014540c840c00c090041402e010782c1d20782c11403602c900804c060f1800c0b0b40a8110807120759060089001002c8241e5448034600c0d18415070b19030301d82c00100040c0802148001c60022448009910f4044241400c414006418030074605902d07a403000246420492034445008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 451847311 1250 451846061 451846067
    0x102010b060304060b12100c030c0e010210020a03020d0e0a120f0c170d020d06150908071802040f06170a2f0f0c070f0f0e0103110406090906090b0601 66
    0x114048030050807282c01c6840f29604c8601502041c100c1e03a0b07001221610403000d400c0101b00d5001c05100050020585a8031040083c1c100c8103a80d0900d001c02403200000c15103660002032001604d2038100c80181d980740e6100f000c90003409910f580d1411241800d00328500c3d618001440d04d40c40e4060080011001a860000c2d19404940305004000c90700103130f03541c40812007010744241042e10568140d864850640007540072a880f108614840030f6498a0502c82145000030701c044900160624192250624084035a00c4002c1e100b070b2060101c03048840d10104e40d0076019a0001c00002800c543c1054540c0d0001d080f209d2001010241103003060000b40c0c2204541c0244002c3c0d81407001c0b00d20720b80c48a40f50069202c1016810071078488410003175110981e00180080c2190403c5001400030346041440341c0c8012001517000804403a52020180000201c4546450460340d01c540c0c0044109500d40c042005403000d035125034034151a02c0c040d807061003441c0e0400519640308203003500039940c03500019 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 451848561 1250 451847311 451847321
    0x1b1008040c090903051207051801080105060f0f04031a070e0a030b040213140a3e0a030e0607080a051f0b0903030c0604080a080108030c0d0c020d0c06030515010201 72
    0x1c1d1403100c403120204401c0340300350f0014400d140280f0b006803400f04e400e00c0c030700c01d0072005844100000d0070000b0011402c0107400041c401c104024030381400035501d4140003418030b000790308282c0103240300040c0049940d1071b132170300b16001180d1000c0346007a8103a00041e00c1c41300000440d025800b103006c81e5207000c800d10300b040105007601d80c00510f028a03500d4a03024402100c000c141c803440b0326555a004800d03509511220240706929200340402c0700340300c2c1d0310101c0c00c4102d40c41c10b51082ca04198010b4114070002042d5140114480080c16211100208118003400301ba155410180c0100c5040c820810340c03003600c0c140f040708909814081d54940054501c40000d00103011241040d08240900410600e8002010240c0008044030b0509241c4211130307003002030640e82190199000150042c200b0380008000340140700a40203942031245215070702d51984490103c04040000c81c46108085548600c1ca9116064104c041d501c10a91aa20098000c1405030760700340c92800788d000c110b00c03a98414011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 451849811 1250 451848561 451848563
    0x708030405030a060207031205010803090f011718150f0f061801050105090d021306140d0c0b09041d0d09081f18021804060501050901050913030201020c1b100804 71
    0x80200d5407030f507140d950007904600d03012000c0008464640200b07043da0302170709000e4a110700103550f03114091020884d01c07801d140c0d45a070502110a01040707600d5000820554040d281c51199204546613040d45420303c40000c02c1303070b6290201074081c410300c00c0001111601c200290100d02206850340803c1106801b941c8180300d10b05c002030001801503500c40c0015140003600034010180c05003103640000c0350020494030b0f0385030326603444d0310400001c01451007161542c0c200f91000240c100d21f40d180c0500c00e10b00790144040c40e4000042c503843c41c0d103450380710601558800c034031103907000080da0b65107484031111344810b1300284009401217075003c8045000c42d09000c4000316000101e900c1c165007800361043c030044c55004031043c1da001002d030301d8445150014031880310211103a45494a0100200e0358103802041c091941b60780144541e40310610030390703000b415000c0e918a9059840c58200d000e4481d8903034030030150140d1502d651020403a84141800740008462000c21030729030f11030807030703800400b224 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 451851061 1250 451849811 451849813
    0x30506013b010207080a030c0b010906080a06091112010b011e0e120312042f13090c2d08060c0703050d060b0a0c060f0e0606300f070803040503 63
    0x4031081e0070060740810020741841801070318034480d074505489080085111003500450f2076200c4840030000902d900c07502520001200700034007420400c5a507038400e54014001e28031950f40c8a60001d008640403510b042200007804034003500940c144080c0030381039102040307002c10341400b41060152042d2500b201099000e5803074420b146005010803c100b14a291108140c0c00708100c0300d4484524134201602c42c5024501e800d605140c1c60410707108a0b00c60303803403480181c13030800c0003941942d961581c115011400e81802041240b01800c0c60103056546601411034108104989102001c10201c84c0032119118902c164a140c0d44091a50301c2d0503040b2130f44540000b00b004500002801400540080320788010001600780d01c4041c0d034400d0f50b00580c0d031b03c008039001100030030030004180030b0480310705002d0006001080545003003c1d40e07210041d0400340b1802800c1041000441b00c01420441d445400401039134607070003220f5081c0c6400c03000d103500e40e0794011020041003400740041200c1c00c90304050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 451852311 1250 451851061 451851137
    0x2040e06030c06180a0b040b0c06090a1101142208100504020f1210020d1e090201020a0b09030c06040f0c0f060c02131103040c0f0f0e010509090a0206070303050601 72
    0xc4c01d040c0051800c500c503d0340815503240c086501200d042c06480640404454503690381c4400c0c00d00c0740382440080800301c00d41d03c0321882c240045da44034200d280c3c1c0402800c0c40340d22008902d00422503070160380c0c642000191054000c1e24030744041c0747c920701110103c4041d00c00710340c100703131490068074021079000e5041003404440c0070940c18045404907003402ca04c02034807030103906449294103a0740030310b81d1262925102c0142c0c0f000282c920250320b9290060010800c030607041940027035116400020094800d00013007000520101c01070044560003420b2100392050783ca09458400390441802000341c0b64480230744c0001c03540c1c03c4040f00d10000e03030726076807210380c91411242d003008084c8032614140f850594480307030800d02070600c2c0c1002c0d500070707840303426035400c0383d81030054103400c000704c5921403086246c4034102008501c5903014a9030549070300f640e0400040e40e410800c240b41608400740207420040c0011005d040c95850f50281d401803c0c2641c404402d07070003000d0100c11400c070904049400100c45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 451853561 1250 451852311 451852327
    0xb04230f07030b031906090b0702010b2d040e03040f330507060504020301062402060f070c030e06070b01060801030605070c12050703031b030f061e1217040902040e06030c06 76
    0x320400a0784a449001e0101d2400c8580c2d40f82300b48001c00f40c4036080035030b440b02030f4442c040c90300b00e45150401190a015450300d204901c1501028540c0c0c60140380200d565011a0070038400c1070003120302030484014203001e45503803820031001d01c00c144408098052140e1300d048024940c20f983c85440c0b0500303940d8480c00c244007510f48100401d00604100d80c03640d038a420000e134000710700700150b004031f100c0342d41c410903c0544203019040000c0144036120800c3c00404022600d17420141c005001c0f9014501601d003d00d004010803d24880c18101500ca294032000000380c0da540500b85e113041ea441703406c05000917110f000055680c8000c20700002c141d407020418a9103000c3c400c2c4041c2c01046d01915003c0b031956090149180e0312003c1802200c000b03a114a501c880d4a001d9026550040c130300601c0e101c900d0400844544098042d5004000150f017170010300c2001d1200d0864544c40c0034105100040d61280d881e9000c1000354810301c0341a1208044100060861801045075168080302805491619903a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 451854811 1250 451853561 451853593
    0x30405031b060f0f04050a0f090c020601050307060509032113090e030d09020607020405010816080f030a050c071e032d12030609092901030302030a030b04230f07030b03 74
    0x119201984d210302c02840300181e40e60710f110010005003551500850018280030380007064409030340c076134003e550200c40100610340f000079864003143e185150032501c0389610f200082c100044031501c8130a9128070700c4402503110b1054010184034041c1c0400145040e5280e11560075190344007800c03041c0d070300188071001c04032555400c95020b052006008520b000b81d00d9000400300c61083e00b05412a034031800034540030480100119000d051110010320b00003e980d48119640c2c8207040c0040108100441c6404024000f000b0800c00382c0170091a62030315400c0d850f0100c01e00c01440c442500c2c0c00c524002201e1141c02c4980480c03400f14041044041c2c480701607120300d44c3c006c0150b41c88004140d500d20000600c5410342c0b0680c0845441a50385813804690020102150f04074602d42071001003051004100098000003140c0740d40b5414100801c0c10454400000c0080c24400b400301071060100c4100e03150702c81c0340c540f450f201d9450520000400d8603001400c03400c0322241319610741c056000c00301481501c05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 451856061 1250 451854811 451854817
    0x9070509041a1206010e07081b0d1a06070804150507020a0e09010c17060f03032104140c03030a030e010b060c0a03031a010c0605090a140708101107120c06060602030405031b060f 78
    0x9c0c24a103000c44031404900d410203070b601c0010307410740d5280e0310140903410307925081407078034002000c0f01c4103414140c1070b4444140c03a22581c4503c480d0740071006021411103000340c041d03840c0c69030014600b034041c0340e841007040d09402045602098651a000030610343d00c0c051b00300b0300140c018407401d81043c5d5494000740000e907c100500c032035141c8001e0140c3e2100030a1591401054940c0f00c0803164070f400c00d490810301e40940300d106407140360401015400962000416226485902e25000c00c4c1072580c09a041d005255004400d608000b00007020034003004001115103210744a0b5808000c04500c4060b00a03541308082c1581d4000f0b5896050032000c01e941e0b402158001060030f00b85c03001c40003150780340c0c040e585d8000050400741d0808881048507040900614074000100c9900f03008407003d441e41101107100384480200112221440c8030780c05c0b0710450003c1d0780031380c0c000000c00205446000c060365a4101d40705c1d0760721901c9048100c0c000348500308054081924090650744c00e240a1164804040d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 451857311 1250 451856061 451856071
    0x8090d091e1703071509050613080403061b120603080901031d010603110a080325050f0f0601170c130509031903090b010909020f09070509041a1206010e0708 69
    0xa1031100000c140302c0803018600d0a198601c1c4025a9070301d04614100500121888607401c10703510306418000030a02c0455615800005030f088a0b42d1203100c2c3c83c25010502540d000501494509010b1030f070f04003440c42d00400c0c107107034580311040035442249548007922102c1c00700030012a400d211250165009400ca50000b80c0d0a9494800c6080589006400c59455500c10f40307150b24080c01422442c1805180500a452400046c615101510f5800022000c452900019402e1400011800d10106020f103040080149045d10110304c1e080728800d9640c03000780110010b2000b4401007002640c1c0c00618451200c101130040c1000d0715060b1440c40041c900100000c40c1d0f408100003d0701b01c1405289140020311031038800288c0a035032401c19000030302c07050308840841072604c170b18238000d46e039941404201500122490809a9030b1240700f110640034000b10540c100e8104100b400f030300d40c0c80d018580d01e40381069800c102c4c034040b9404140c0d510842031003192142d03040e5401003000785108413140d913804 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 451858561 1250 451857311 451857359
    0x606310909051209040e0a0b1f0f1208040302030604031106010803041a070302011d010203091005061f0509040609020c0111030708130317010803093102090a03020d1208090d09 77
    0x101218411b07103087c00c0361841c0c1221212002c0082140f40300d203003e52207861110302c00740c60908a04144c0e210310004468050b0004180d800ca942070200003501044401070f5a015090343c1c20b608140c03a01500034001e4240000d25802508008075884030000103503000c0754442411041c4c9551100d071100c8107548406000e4045540325100103513030189900350f2490f8140d251000580c0c1303152074003450b800c100180c50b8000f2744900300000e0002d1640c0e00b080b081e0340c241000328403483e140484081560140301e80090385410905025000580c1800c0740d0183c0b01004d1500002e01856a00c5140e11a5070312084981a001c01c0e141008a1002c00b000b4484142240c03280c01c00703800451001c0d01ca9103940744240c1c0903400301c2c1d000050072422420418805551541d040034100050214a491850210b89050091240c9907010551500903039480558000030368000c0e124a4082101d400c2c03042080f0514007890021443c0c0001141c20a07400241c0c0e0340c43ea04a030303510b072500d03036051031044403c0c066500c09030150 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 451859811 1250 451858561 451858571
    0x20d0b040203010305061609060f080a0b03060106020a060b150403140705220e070608180a140706081b0a0c02130e07261203060631090905120904 64
    0x6252a18030007140610300640040c9a50314140c0074141804400e4541e00c402c22954603001c00002c2e8000028440c2900281000000c6569000c400001008080501c0e941482000700004005402241011302c0c64000d5074248492181c901c184102c000e00781041600f4240200010030100c2c00c100f01290314140c0400079a00441e540c1e000103110381480b401d440e0b04103032a949000122001a00c140c42e1f00c101c407400504140c40c507081001c3d0041c8401880d009512100c5900c0d50131030740003031100c0300005600100d41802040c104034201d50f1540701d03000b9000460a14000314038504031000c108050742100c40c08403890281c01e4042100c003000b100c5812038001490349c098541140e514007034483ca0004460080425a01d03181d00303203004052219940020030b54007103c5202850010445984000d070143c0380d10740e00c1c0c80d6840442c0252040003103c00348500301c7d03120604506000802c2072500c103c04c900700256551120600c10485441220060146e0b10040560440c3e07001c2d04054092202c0041c40010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 451861061 1250 451859811 451859831
    0x1202041104081002040f081f1a030601091b0518040c0e0d201203030619050604060905030c0f03060432100c0201150b0c0703060c030b040e01020f0904020d 68
    0x854810b406010420f2190046401e208655540401c040242817680c0100281168450540d42044042204800c181d49580c110000c00b42d403110a52168400681111040d40e51180c13020020004034801000b900c0c10a602d1600c518416810f8501c040b000d03141c2120701a5440007080002d10007c40300d5801e11001d01041181da80e10914084d4816000d400c0d000d02d46015490841c8103079122508032841ba0302c0c54000c558217000000217481d0b214500340e982410500c0903111804440041d5481698403490008010407280e44c815602000c60301c098045031800e01c1c80c9410040203200e84214035805512000010300442c01407802d00504402d035802c18034200192540d07113403400800b0a00300020390310401c400c00c1e00d0302462068450102e0184002c114124540300307581c00c0d0030b601d8859848a03100214006180c2c25040c003407000110f5001e03800700003100f09a1000b801600184100921592800c0440400b0100c10b00032594441189980c0518002e60281084003d410245040007815628040742d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 451862311 1250 451861061 451861063
    0xa0308030a0c181202010215071d03070e1e0114150318120c1608150403170f040209071103032206060620010903050d0c0c060606080601110601120204110408 69
    0xc050302c4c2081910206200d5400003904d840c2000000168503010b180402c810b881e44288141c25003502c0c072050304a210301c0c40380080c0c90f284054120049801c0068213211542c10388144110f07406005c240700ba185a81e8644d404401c1c000c08000558020100b0b070849140c0340c590b28025075100c0311115a400002d010000903030720f06800b0404518500c00009242e10724041c0c03c10105244c401d40c007080102c00f500345200075443d0440a4428820f074145840800d0400d030003041583c00185011641106929007006005180001580c2c280d011b080c680d400700358034030300c5401e04840540c2d03008019451901d41003601101d42159008800c100c01c00d0480b0f56000492900a040040c040c07903031209001036400c41c0c03020580e00d6a041100700d0740e140c08a41c01c006504081175800b036082840700000d04205500c1c05a600c403003441001815649495004110141c201250f9030044100303a0315520b03082e5100800c039079511400c0c0a8503468202182c3c5200041c0b903d80c01030091442c4e400c00840c107243e85c0313410346 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 451863561 1250 451862311 451862357
    0x3818061f2105071106040804030b09030f07060606090501020606030a030f1b0c240c020d0804120f1509031b030c140c010f051c09170a030e0c0a0308030a0c 68
    0xc1100d40c60b5401c1c018080d0380a0812024042103001501c0701d070030682d403942070320312403031000800302d00400340082d040050900560703144a5000340400e59410141c0341034030040040340140e03000300b100c40728085806c0d480007801d1442414058001d010003801601d040d101c6c0d140c2c04d102e520400100c0d09054000c0038400c0b990000c0e0718803511241d00c10300e041141c0c9412886d20150b008158660001c081c4107840c0e4044411105250140c800842c00f02450402d8041d6106d1500404842e2240501c0030041103d40d11003c02480c0c00b41d8140c0950500f403800d9081548c0000a0150010307141e8401403564403005000540d01c28400e040071600391081e81e8541ca5041c50002c1d1103241ca41003400e2603201540c210036900d11421035854079500c0c1026842890070005641207280319039607956400c50042000283d0401c0103010182c0f00d0549070000241e00501a1001c40e180e0b9810f4010240944a103040c810780c0304040d260302100d440d0440d5118100000244580c8407010b0070080e1034408445450580707009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 451864811 1250 451863561 451863617
    0x303050d0908160807021c080f03070c1e0303060605040f030201050903010e151602011416091e0f051e100216032108193818061f 57
    0x621038407010741b401001880c4181005507141000c4c2c0c40f09500c0022120400c82e841da048070440c0039120340b1540d1040781d00107220340c0003d05500c0d526110040354100201024a024480e65051152079194002100c1c035020b00d09c80e124402410741000d000541c095801b500007064044c0000812861502d06103183c40071199908400701c0b0b81c80706100340620190680040c400c01130009110b80d803e05207918410540040001c0c0740540c0603460904054070030a50000201071440202e82c0004c020200d0310482d140e540705040079010782c3c00c0f00107614100941e102c080340704003242c100c0d01c44007004188950145001e988200714064040f12850320110314107031901440c000c403078000c450005080c890b4040c114513500002480111820095050800c1c40003500c0f0b642400e101003500c070001c1c420b00d20307603041c95011110542e84c912042040c05114050100850104032149003440302c00009620480d070058410301c1c2c100c28002c4070700445e840f100c015402400011720381140400c8030020000d0300d507103520f00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 451866061 1250 451864811 451864823
    0x3080406111f0902090a090506152716020c0f0103020307050f04030c0e060103021e0a170c0904061e050f120114090c040c0203032a0427060303050d090816 68
    0x1003003c19418071240d0140d000286840130481400c41e5101c00c0c2d80e4a1009007000380d82170200100d03202035200e48070420400e01d212080401400c055038403c404602c000c50f03203402c40140703410400117100d1001808504401018242c0c070030800200c40110080e5000078844c40c01d101e001c11400c000b451005004000460064000714000c9003880c160145600016089604042c01400b10102e070f0020840a44c0a44c1c282c481e80c90740d034120481080ea034441c10742800c03990b0204007004000725015200010a0900d07001c4600f00460b58030740320020300c0c40d2507080110b01e02c1c042110061015043c25645114125070062001610b02820300344c550a6602c0303107000002c100904010312003040402c0000784402c420481c0c003400751b0000c01800039034900004051046521905042d0340311342c8100401811031000e10a01503550740e40740c074802307400c4010200098400b140000c00c40d0368140910f224001c2640d60503902e05140c06000040000540070703c2005888400c0e040045020b034800105500344018400d42c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 451867311 1250 451866061 451866071
    0x20712030c030b010509090f04030e060d0e0715120504020a090501080d1728090204110c0709020301050a09020a09090c0c0b09060705030708040c0e01030c0306050a0603080406111f 79
    0x420000d050f100321009650502c5000c3c005200075603924981e442d13020307000f0243c4100d030b960369090449110300c1c02000c880d0007400000c2c22811101c01900005400c0c3d4401c4100c451003070f40c611140300d500c0c03000340c01030000411b50302d44000202c402e5040160454001440c032240c607900c8200401c1110b1081c0d00101c0242d01404000703000030b400600100818031401814641071901244808224502d08a4903a04244c031211420f1221102c0e40004029500035200f0031144a0005404403103a000b650044024410f5003800100c02c4c81d42c2c000c880c1681c40190484640500d40b0566001035000360174402c081c040400b2003c604c0c26200c0c840c0815881d015529924065a181820708103006d0141030300503203802600c04c009009402c981101d40001244c60420915940c9040807501004503030045505460300b80000802d03c000c8448010641c0d00a200420098a8024030001154124400107000c12400d020410031540240031000000004800380c84100c003c10344030103001521405400c12040d624 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 451868561 1250 451867311 451867331
    0xb1806010b04080c0f060405010f0c06060e04020108091c0f021509010b010f1407080c03040b032419050918030c0f010c0c1a1302041d0d0203041d060402071203 70
    0x20081c0300038813141951140a2003280c00007003501032095000360303418030440c1451401241e10807440d0b4800e00d5048034040ac911500d5011035110104156401d81c0007449003408142c280c480403d104106c01c4100710140c1da200712440d01070b02d00170030281121040d4041c2801110f0f080b0441c6031040e2080c0c44800c000906202801c0015119102c0300d46801c1c01c2207414602108680d544030100c0d80240e810120711929000e050544501d580300703a0300301c1c001c0e43c1000310030721100b0131107584901c1d0303c1e01d06580d4010301008030406001c041030540b00f58120b18054008104503504058404580158191b859408604a455070080c5558007030aa000c11a6118400c0e0f0f001a030420310070751408030aa46000340c850040741d01e5071200803d8612450001c1c0c014a8045540d0b21702000c40758610030342c0a0420b000c418513916010448840b0071511150a01441e400034108501c003004a809a42c0540039040901840b07181611503a01c0c01420369400c03650810415000c0f136801c140a44070404039507000f05501b081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 451869811 1250 451868561 451868563
    0xa030f05070b09060103020918060606031f030c0918030806040c031506020c2e03020c030d0c030219050c030a08101a0a0f08060a050f0d020901091d03030402010503040b1806010b0408 80
    0x3091000349c0b045443d01d00d5640d8101052540c0c0108080361415101e84482d21140596103041650a0a5100a240000400c040116140225002200304002c0300d052a100409061003c2900400181080700000c4180c6013552221031070b51054640010048280c080c0748050306007503001600540e000f030509040514016000410400c0309074540703884040e175101c4540c290b040c0507681c40107140d000710382648505000c10a41d00c5a1000c4c0030203020300000324001900a5021481c84905400c1b46424107145038041d00c229015464020b00035072400c8003c2c41d0413100c20102520141c1c0e02750010000080750300944004032006590b07581c1150359142d0048000d0000c5004052060902104d032040145540c0c2c0d2560800444405903581d0b024141c1050000c1c001c0c0c1d90204000b0741c032210f0400049040d6280398452015449403c204122180c00c0e10b5010380d40780022900240000c20800000c0d0015600c210351503041003601c4441d0b1458a1103000050070008242c1184081503808281000f003040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 451871061 1250 451869811 451869829
    0x4050c040924061407050706110f0c0312070206070210081909170c010b0901090e0c010801032001050c031606050f0f011e050402180109170a030f05070b0906010302 72
    0x1039002010b040710ba4504001500c51692140340c003070101c440107003103481da480000c5170442944a4245e83c4003948450300900380c601000300c051028401c800c02010500702c00241d0002e2488000d0040ca200024030750038048560008004907040441442000016161114102006400342c2c4070a082458440e0340f040e401c3d04031950101c64542890300c0440854503000940030300002003a19541d40e00151519240902090104544c2152404c800007a0540d040e03070041103400916000d6404c21030f07030360004442e00082800060b119a45442e56140780c8054050f0004588506051150905090181440c29600401c2807042d01c3e101d00c04d4060304001940c40b07032941c85003a4420b4103400d400c0401109482c40414000c00c00810741c002800c085d058901c4c11200010800104203654515007950300614199580000502083d071003c00455000341040b414041d01300c0181c014144001c0a89044800340c000442420030700c50100f010030045117109042c244590841c000411141d4903620510403010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 451872311 1250 451871061 451871081
    0x8030a0c0314010b0f07060216030c020102010609020c06012303031206030d031802040f15030606090b0d020102030a21021207021b01050d05040c080105042f06070f03030b04050c0409 80
    0x39610720043c4100c1000f1015170b040880d0381100c0c541c40e041185800710091054001700d004030100031413080c0801d580302000e054824400c2c0d00038800159100381240c140e000f0740d04880d400390801801403100300102881044039a039000c1d204540c441034080401d04640c00300d40078801808440c03082008074181080b40b000ba00e0010b10f001c1000000800340c0c40500e86104000174403030b0392901041d00d00030506400c560060301c45449045006903803490300b000207050f2446442d4081c2c3c02c2120040d00c41c07900c09403861000c0e0b01030300698942080407404540c042c0107028600d13170303c1c11a00e2420170078039005d2000d00403441c0c413140200c009003026480a440e041e010501400084010030b0780203400d90307000c0b0a951300c4005211022901c2e84580c07070070715408070b0380e908025101c1d07203004100018802050040e1103a09865800010f447d0181c220303010000d01223850045c0c02860422035440043d080a007040754040c002d20f40021076a00714000a4241c56054403a07142d400400308090001d001e542c0b151442e51 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 451873561 1250 451872311 451872341
    0x22170c03030a050301061805041a191a031f03111c08180a080d020313060e030628140a0b0604080607030e16060305071412190908030a0c03 61
    0xc4240382c81c00400c1072005016a100b04240001c80d2926010826001005000002c1051100c0388240f0b614860900003004201d110301c00c001c0700400f5102c540318200d030642e40701c5411607148101c020501c25296001914070717201c08030410102107211400c10344140c06140304030b60b6a400d880345441000205441b841c00251004449000540041c40d4001103c411794a00b65290040040d0440042d920003a142c0c454003c0e4000e9141d80609980e020004102c01d0301030045421503542c0741c00341101c2020001600c80d406a000c2d801050200108105504480c1404402d100000048404a40969099080001c0d02d01600300c2402403284041c001d650b02d00405480300380c107051518002c190744681c0a007800d0107040e03544d40300d84015002400041d0000d003a0b250080941652518028010081102d8810001e50b5000b03002e400200441d00700e0748030034548007003400c40351201c449030031041d40010a8003840c55a59080c0705c0c0001d08030030245215540d4038100184034104207901600351808030f4512003003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 451874811 1250 451873561 451873567
    0x60a111c0b040204050310060f171216050d1206050409020117060f09040b220201020c10050912010204050a050607050604060c03110c01020702040f06060e0622170c0303 74
    0x40011401141409400071414101d00800304009102c3c0350001034250107450f141c14800ea5144c2c110724101c41075035407e056240c0d0380d03040b00003001040004003030300c40d0403440481e00180c007074a02900c1d0005480c05800103100060359a9031600c0d001d0520300c004600308803403180c400d0400b841920011b1009031000d01101840780d00003044914940203003005401001f0109407039480b54081848a100c010b8921400c506180c20500183d810440351000d80f2040720810070010750582550304a495411b0700100a400d05007000c10241114042c040c0080007014003441c3c0481d40c030402506c05a403a88000141e42c1d0703007042c0034407046810b00d03040703e40a40400c01101c0e0008400003141d9078410b03007100740000c0200042100303d01400301c440303030041602d601040c0c80c522010194020103078244201c07004c00c01c142c42008200d055070b219101d810041011440440ca0300e0800c134008150020700003030306000440e83e204942e0006180c0d80c210306201582403240391250041042010701d124422001141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 451876061 1250 451874811 451874827
    0x7120e1c2d091e050303070f0605060402041d073b0f031f060b0403031e170c07020103020708030f0105210303070f0e09090102310e0621060a11 63
    0x20079101d84544100c0d01c07128900f0740d110500c0a0400005018002e050342e68800f0f841c18129a071481c070000959000340b5202c08122140303040e1088070110303801c0031002042850a22580d81020000601c54000d21104012150b6290040d4080c0720f0000c884034a0310360310101144c148030070903007440301c05405030202212203103455a00003a21080d00b00015000c1107000075021441d030143ca010703070000022510201f0040109a00241c1400361034070f0b80d0f18182161030507410f0803528151800342c0c540c00c034010980411f042241c082d0080004a0041c10f0143c501911582c0300c40481c0e00132580f40d8440c5103260011300040ca41004160103401808031600c09903c0030f580310f1034070780c40301800700d00c00d0252441c40c0080c00c60080a45003c245d000a003e6101442c100c207020303001c0d6200300d01a00710741700808020400c0203400f8107010310381800004040312450405040364070582c7d02410a0742e200c19a52903d483c4041c5001c89803135206c01d54400707802d0f81d0078541441002d582c0b61219184150800f440840 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 451877311 1250 451876061 451876067
    0xd0b04140f24180a06020a1223060a05130614090f0609060d080a211503080d1407090503150105030c0907050c0f0f1507120e1c2d 57
    0x200100480d0210318002c1e440b1000b4039a82da000442c1c0d2181d041c000c0d1a000002e00000c1c0e40580401002a140c0d03919000e0407174880e104030740707188080c1201d00d03840502a6284480b8111080c1c1d20460250503561b40316181c60005685415250090400e9601c4040034007640c4001942c00014410999015559091881e260140240d000b00031a02404c41c0c6000200590f80e906021072505810428081e55059514001080c50b000d04a181903014543d40030064010264442e00c0c113050141070f400c2000c07034155958021643c1c001070201d4a12500d41d00010280b9070005806030280d0792907103800d5400c0e8540fa09260420b4510300c810081c0c00011030040109417004160380000c4c11044541520175542c82506580e03600400c6860010f52140e440b4031100f00c0d60000e134100c0548c50101c1100c65856481c0da00d2034a55400b2101e000c00034294601000c030a40d22500422048003540c802c0d2540107920400d00504524185c51080c000b41c03030040e00e04c011040302a1124190409162820003248003180c000e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 451878561 1250 451877311 451877353
    0xc11032803141303090902070602130f120308091e03040806010905061c23150109022d040504140f09060601020705010e0f0a15020d020706020c0f0d0b04140f 69
    0x1101c0800f08909008100340c4205013110140040341011500d41c83c0600b0010000c0d004518413036200036030b035035010035111505880c0b01c0844035403094914030b40342c0c2642c044640c080040d012805905ca5610206480d800b00c003201f9459000d1a4001d40e2154500b803003003032518006034412802d26260105004664072800002043c40030340b032250401030807292400426450914551200441110341c00940f000301c0814012800300c40040a880301c0d9803107210003c1240329043d201800f44000796807045080902d00c1c3c450102c100694221401d0070358900c08941a00d1201c40c054000c4041e250401405070701040341180c100c60488000c01c0140340140010f0f540b484207000d19810312208042c480130030754030403080c84a9460050300b40c18240b030307942c00010f6a01c680c3d205203101600500200c1740040344000307031050446004e07074010656007013468103101d404e03106d0000c00c0750031450481180c7c01040001d295180103c6c0300b148459002182c1400c0182405001d55590400d500300d2035454a118140c0307484 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 451879811 1250 451878561 451878571
    0x150a020f040e0702100501090b01110102030c04050d0c090e030a0305011d0c09060c0109060e0c060c060c1b0616020d030207080708030c160b060f0913060c1103280314 73
    0x8807401e40310f80303500f649130440e8108803400329810b110000c80e01c182641c1095200081c207032140c440a5400465041c242c0c04102c513280101c0c401031004112a10380030b009140c40c10f00814040140c10749070013003841a1180d02100e41855070000610400d1036515100b081d005043c0d89c5c000003403010400b1900c602c0030102502c40c0454003070108034500d0941e240b00c201c451140c00c92008010800e01e0786001c001501e110304444d0b0300f42c00b640b5140350302810003608503000c4c06d00400c040e00c0c060340ea0540e21036031038101c20381401d41c200110341e441180d02c000700320050261800a001d540803030013900340245080030320500c0e0b80416006000c0c48000841c6242a5410700b603012800315100c0d9910028052940210303220b401c40603448081d440144203010401502500042d40c40421032038207036040c0009681e003a20000301e402c4c1e0187c90a000714195503c1102592a10315002d88130001400d000b03450f41e04a00c10b280030f61b41c0c0c0d24400145180380410111058455810240701e00500d20800c40543c03040108 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 451881061 1250 451879811 451879829
    0xf120403021618051503100e01150b0a0c0302160303020604020a0501020d0e040504080910121503020906120106090e0c041a060306120a06061715040b070507021f02150a020f04 77
    0x1c10807050342c5c03c02e10600e01c1c202034200c4000061400c1c1c1074020702411000c2d00b095502e08600e480c0da0450038906032054910341082c60b80741440f200f000311002c1017404004c1c1c1c2140141700d0560840300124000324000d500a5008200c0c0d0f04050040100100c840d51129055511401156003142c0d0002540310138000100d0700068660748a04003103c5500c520132913a42d12015024051307505a070000062640900d283d0400c001c400784440c240c00d00c8050a0001940c03003a00d010014401707207440c814400e000700c2d4143c000306655546041c600300740c424150390155982c200380d1401805042c28441c0207214400300344030442d08403058011445034400548000d005900021481d000c00004011a91500340e20050802020340d031030250148180e400352030241140107050120384401d00d00c40c20940110f80145440d109515521411394845d07001c03403012a00000108a14046503860f41241100e4000d40d40103809000312a007510040d1000080c6441036091040c441c2141818490040d2029190010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 451882311 1250 451881061 451881071
    0xc1701090b03100501080708071509180b040908041a1e2b1517070e0a090519210509042315040c030603030c0b0703020f120403021618 59
    0x1004a814844100b1460100c9402c0000000d080b18001443c1f07000c450014040e02d01e0316445c1c50349016208010014031000410280043c44540a110060462880c401d03000162042c44000030405076a212031040d9814600801c0c20010142d010a801d607954003100e0350203107050900708101c101100c01c0c01024146d02c00102d001c80140c03107002040300d1071304d0038080c1002c0d8442c8071800401c06082c940b0303071002c02c5140c136175400500480349a940304034405051001d85a402d080c100d08160020000b002c209205807580710305000b10790207210700ea400b1b01c1c0c0c6a01428040e101400e103507542ca2101c0030300c00204031082e0440f0088a51080c107171145060f044501207100850190380203010284004e212941d00d514009000d504503a8800d210700701c10050f10140b00c0a000781d4820340444201e40700180114800c0c0121a00090124484543c446d074141070040c10054011004106608000d1821410001d21020300061603010840c030204140604140100749003440726007c2450042020301c00784503190 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 451883561 1250 451882311 451882331
    0x60103090507030c0311060c0c01031a120705120303010602070b1606110316030507050715020705030f03011a03010b12100512070e010b07050d0c05010f06030b0403030c170109 77
    0x29008030041036001001c03585880e0b141d0509000d038016521003102d58440c40d040c01d14a500303050003074441388034995000d002c0e220703e200010742c040c2841001900ca078251074080d10180b903585240023202e2902c000300501c046030a180620511200750000c0051507801800100300155002035050f09680b10244200c1d1500b0280c000c072085c9940801c0001c06a900b8016195500800c0b10b000d94498000020100c40c0760110060550441d02e00760703042c100085080080344040b4244401c5415010343d050001450120f03251074090664009440120380c00b00e00000400c150001210322080d11301101c410246194901090f0640c1403055104000000038a41c002a44180100058400400c0050034005164070b1060f99280c861881340540160703044840c0001c911494418181c5040d01d034014010110504041c0c42520007240c1400219034542d02ea14500c3d502c05030718000d8800851184c0a8142e036814240b03000f0f030585000ea102c01d000c0041c0800e80c84e4803861700f03016460440d90741080015840c00c4c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 451884811 1250 451883561 451883567
    0xf0213050d0312023138030702031e040506040504050c13140a08010603110409210e040b01020a0b06060c0102070b0f040506090a15110d360206120601 66
    0x11030f100c000718840c40803c040e14644031035601030248002c81c0703ca151090300c0c0d501c0c0d0f009262107240a03d09004108a02d95500510717510018401c2800d4106031a8048510807074031030310740d40704841003001a000400d03c00c05010010200b00c20b40e480c0d1b480d0150903e0300301030104005001358421103120b151100080340c0510200d00803280712030440b0a0103517000d912000f14a80b9031801c51820340c01003005810009500708184111819641d101d41d01c608014281010000a411804804e4915a0042d692100a040000d2103c01c1c4ae038444c0e114407607040b2030001088122005401081c5c1550006409800040d2000b0b0300075500c41d100b110300941f550030950a0a0081c0985c02000380702082031014401a07403900c49041d842944039604892007980e91142068031010080c0b80107080391040190710211207205d0304a8400e15052044013410540c59406801c195841d42d00c0328030840e40141c0b403241c2c0001a2004019201e8002c4030702031070361200c6034007068240c400c40c0c90040361542c911020400707680c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 451886061 1250 451884811 451884827
    0x40b01140c01060e01080a0507052106090a0314030f0a090c080a061b030b0913020f130f06090b060a0c1a1602060112030503060f121f0f0213050d03 65
    0x4585440c2074031101e00d15101c500929050151006181880c800060a240c00003150300307449078400e003e000700310f00d4402404840c0c1c5e440041c104d601c5281c1f191038840003000300030161061044600030004410070b401c008c6c3c16034485010160f42c04608008001d0414845800507400c19200000001e8000040c01d0a803403043d004c1c0c1009080b0b00440a440d028803099400401d02d000700d1080c60611000c1801081d1b045800318110322303401a18440001e550543d030740c000075100d0f43c0003925581c001c207a0381001401c1040c2044144250179074650451490254911a00b000384c2004141000207059a81c000389040c0500b00c4001d003000142c6071040304000c5018202014402c5159030419503003001d420111512050800100c014810700b000081d6005400c00003402c080e815864461039600c0c1e400511043c0b62001c40e03a560042c11905d10340403d000c08001803d900928a8110714901c20116225415030303c041c01805501070050103c8420141150701d1102100c2d001c49407000300200b20b181c01c0e501c0c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 451887311 1250 451886061 451886087
    0x608040b1f080a03120c0804231219171306021306090806071706061b0d180f0f1e0f030c0518041703090a06060f0e0105030318040b01 59
    0x100c52080c0006040e080014483c52072842915403070600644c0040c200e04940d80c90340c981d800501000c0c04203000c5034803000244504d51082d84e60115580c0c10104141c078007622046205001c00c40007461320030307030044162103260a880b580703484200307182403040402841d24007400c00701946400500b0703036003040601d1b8111440c64124a0308242000d94070350000c0c0c050303440c07440394521710f001700000a0300340c0d4420076040b0303000e590700300b0684e42940b60041070041a402a01d41c1d221031020078076426110400801c10240366100c1907585071403407925406a04c2180c410780c5d010905028107003000380001d40c000d54401041e200c442c104240004c02c6555100860009640951440e019614012040c82191440601a90740c15030f55500e81a410120154640000310f5001d08580000141d06480c2035610f802560440d450320101c0d005130f4003544469040301c24a0b4455000603480c0ca40030804441001102c6006080442c06503003000303890f41002c03004076411480d15219541e100006071043c0e000d0b80e049403400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 451888561 1250 451887311 451887361
    0x70e0307030b0103170310090c0306050603180c030705130906091a0106140726041d0a14040c06080702150106021b06090102210d0507120c05040608040b 67
    0x6590740c1c101480c8910302804280c0c4e01d00b020290200b1040e40c10401c50b4020250702865043e020700c0d0400710002000b060420004250f00c410700003920745e5540024501941c4e10b202c017000044120f1000e249005d01150a01d402070b01b04031001c012079038503002c044034000007610f8080307000c10144c41c1117002000101c5008040191207418141c0c0e1098501416058984940701d1281d41c00103a020001540507171480204083c0d1030551254a03002d500e6050001c55082d060401e00342522410028020002507140307202a90b802400c0200740d0045000350082407510450306040750400e62940072036490300d40216005d1044440109940b1341c0308205900d0301403c1d100c102160395850344402900d8128002c820f81300b078400810000700034030700700e01102e4070007805070000c100c2c02c41040004a900d01a600c3c680c03e6920062000d102c030200140141c51007038059507142100c4502c429040b200711100161301c0c000b080400e210a201c090303000a54640c11a8014a4207450380e42d841c5000c62804119004072081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 451889811 1250 451888561 451888573
    0x405072c220c020a021c0303060e0c0a08010b09011e0c021503040302010b0109051f02120d0b0306010906050a0504020f0c2d0f1b150c1615020607030203070e03 70
    0x25061000c09030714180c140044003400244001d4500726603070b070503050000c1d5220b20314803404041d0710503449003c22401d220b0f003400f1814a07a210f5102800110454102890f4000007800160240d848215607015180c4407840a0814100c1c0c80000c0045203100a1400700d95184010404618050000781c0c1840b40e00629244074454182d42500d082d0b0800e803001c40c055030801400c17003030941c000c0e62140c4c160f441c00b03009400f00c039003c600440c00d0707600880340e6402035000302041400c40d4040c13200100415a0b4005010991004c0e0b4030501d8501340051340143d1117649416010f200d0356035103251080445800700c9000d611108180c0c5040c0852140884087c1244a8001a00c21111a10521001c0c09c40c6030001107142c0d010030032806031a40c0c1c200c1409242a0010b0003000309114640000d080240c50240503504001e030b000d040c0009542c4410b801c813281744d02c00c1d22011520300d04580201c01820380085a082413441344031002e55a1203000d01070106064000c4002a01035100c1c43c0d0241d2201d40060031103031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 451891061 1250 451889811 451889839
    0x403030e0d170702040c0509010816090b04031b081207150f140f0601050702090103060c050f03040b0105041808030420060a0507021201142e060e030106050405072c 72
    0x1040e9484410224051404c249203c0c00d007d0103082500c000041c1030312005002d0350707446600655031a10100c11070522240420105012220f42c014002451081d03d036800c41c5544000000110300c81b50380711040c2070b03000c0050383d00c80c2c489240a1f070340c031a50b1205c2c11008824001c80180c014140c50525035260741d1800040d05085007604005502802012204103002c0d02c0b07030782c0110307424414000041e41203142e00c0010400900356502200300d09420b071402d18104886151100069882500c054420008540051215203007500c6130b140c0c0c90268900c550103403480c0d43d03507d44942c04000c1c070140c00955502d601032010b06045424210940d0f00074184d943c0d81d4584600900b40b03800480c0b003030f401031011444013621070b40c051084080040018048044555420120724003400019801c4020f014400c2c005141110030302c95540040d00c042e85a0381c51a82c641c1040c5801c44080340c0c0003621a40c02e2100b401412078000c1d4540801104011418000f54110303240f81c060040068000b9402600341c000d206 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 451892311 1250 451891061 451891103
    0x70305030417160204061505120603101107171e0903010f020c01200426030702030a06090302060a0c0905010509010c02030a030314090609100c0c06060303051b0609030403030e0d 78
    0xe92503031084030100405500c1b0b821f082d0751142c050881d0000f0910811080c2104103d0f0420140d129034001e080700c50781010305140c40141c03008400e000340d180c100402c00e0002c12856a0704203c0800e682d0703440c00d0a01c88419042480174001103030264181000040c820308644080d04003401031083d01809660fa041203000300c0d4000d282002e0b21504020106070b000118070300304000c58044a01c0c80f038134481451901110a156861800c29000380c501c001c00090b0010388080c0a40301c210b90207031000040082907414043c2c1800310003000c0391900ca150054100c0c0880e00b140d40142910406c0ca0300940b201c21100c0103844d51607003840d010f549071044042e070000b00365050b044a14004504604040700d03071185140c0c503035034040a440e20f001e0fa4100301c84000c086616030303202c85c504030394925017000407040c10345440e011528541c00a4000443c0090b04684000452070030000304c103000c50041202c1e250803075807a5202d010f9400024104030403c4101041c0750303a8022000100c035001148540c101003401014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 451893561 1250 451892311 451892347
    0xd08041503090213050c130305030304030e092403031b010203071b08070204091a16020d0e010804110103110a020303040c060e060a121d010b030f0c06070305030417 72
    0x61500000e100e045000403610078007807000615406040071001400b5100301c10b020301401803842ca80540140b014400d11828051140d00550084000d1039403410103003001006440b030145114054250a014400d003d0049055101041c2c80f480c0f280700007240100c002403c5200340c0400b114100030100c03003420800410740c0154041c80082d06e1305d8111500e90880b000c103440100e0406031401c40240242c201600b403603084003203290307c00c1c0c080205160542e00b02c2c4000d15020f6032300902600c008964103803116010000c05071803800c03600705030104c000102d000a1059200034001411136410007a02203080c0d0194014154001524001c00d0303c0c0c048100c8000d41e25001110b06541c0c510b58084c00084040c003483c095141c90300d015006600d0301107082c0b4151500c21640f40c4c200c2c0400d903100301c2da410b60b42d100300c15050f45026440000c00c121001d801003520b0400ca45908140503045042d0b110503998440c1d08590103140c3c1428035603120b07070369402c1220340b40500c1c00848008030f9001030100c55401b10300c020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 451894811 1250 451893561 451893569
    0xb0405030c011e0c0903020112020313200108070509030a1707050105070c150504120e030c0a0617060604060f140c0604030f031a1005090f03070605190309020105090d02040b0d0804 79
    0x2c004e5007000a000f00d4102c0414800079000c9101c0006c02035003c809500190f80c0309180080c110740c024250f81d5040100a0803092050010340c031003070030004a6902549003500710041d840c0c0a070504200380002602d840046200034080c284e00300e82a881080c81605642c030864118000700800d207440f41024103402041502160714140d6210f44890100584c81502d01540e0400001d1468850300031080e41c4458640600c44e134144034116500410fa940c00300040e000d0402c1d507441034040410440802c54250010b00032900c500018441804106d900900c1a06110114680b812654a213600c51803002d20401d0301c40800b90189400b088185600702c400700059050380d54042040480324908020034074004254a9482100d0007180900c0078818000741c48101d00c003d04100070f159681000925010082d40824081013022456096003441043c085684d07403000e0030103001003c91f560000786144103005002d8465040c043d807000a644417036000309551407018010b0590603032207090958094100d486 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 451896061 1250 451894811 451894871
    0x909011b08070912050307050a1b08010e0c090612031602010e010806010e01080703020d02030f090c031b0103180501050411040f1a0d24140f010308070b0405030c01 72
    0x503110031510600041e4410011561040b264908102c181e0b10091080e1310160380314441409414080380c018014064050310504140318400ca0700c4000d4081c03030702260320910007a40344c50781c1003080d1100807410b1844554101e810100030341c1d845000501003940c0d1a803141242c8001300368211503880382c0b00030701e00c514006d8880582c103080c820011120b00f00101d9640f800070311085134211b0036502403401180c10200d607080c05818400d4100041c8220381040703400450780d00500051091000b0144603d03034003000e068010b41400442c490903c12203036160304105041640c0c03981801d0001040001603003499070720600a00941c00c1c0f505220a880d200d503c5400d2055150404401050b031982c418200100651111020580545001c10450321400c4000782c2d1400108880ba03131070220300a0210070301e80c88415000446035415005250440341c001d102c082050381c084018804545c01c20103842c04203905c90030f00d0402c2e54070751a19031308600a100c0d04014640c03d1011080c0c6103921140000340d140c042e50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 451897311 1250 451896061 451896101
    0x20307090f0b091e04090b10080105040309170a0c140103050a0b03150408070b010f09060905060f0d1a01270209060702130b060a030c11010b060a030b010905090901 72
    0xe407101142c442d10003241803c2000c0691420516030581c00ba5800008018484c020540801c0580e002c40000f240c010160604021000c0b600c09440130140c418440200000d240c02c0d60040c003400064010010b40c0450b51098810900e07040080c00070f00c0744c0c40010f000f4001d030b640e5001d000814004a02e24007003410100010148112445400b00c03c40d0f004008040030080080718820780c120142c801d984206c0200108c2001c1201c0000982c000d1416560b0035051614003421442195915046041d40d20305240071722102c0e50368400c901d40200360840d500d6010426601d00b500005400c071f00740c036840300c2014000080d05800111043c9001284074080d1004455189611080340b0540c000e02d0ba005901344140b10160410101e803080300d251009002512082c100d001999a0b0884d10465001945564030461141d80c844513a41003001400028060510007000189290054808100c1090303514544407400d41c0c401e0000c0703802003c01400d01c903958209481100e0280008108200c8500c61070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 451898561 1250 451897311 451897319
    0x9070914010806180601060c140a03080405061305060403141201090204090b181810020409091104050f0406020a09170a06060b03041e03030b060c0f12040e0f10080a0602030709 77
    0xc901c02c1340c4d408110806060341c0c0e070800030242c0f000c4000f10800d54403003c01074003d920325201049040107050180d10365621500d01450464540300c00100542c00c410030010705080010400110780d41c00c03651504020190840c90794145000d4041c0030000e080b0507424400004642c22543d0042058542d503a03028041e01031ba640c18012212440c0401080b1480c1c42d074006007861403041c0500b88905200410394055059400646041e078115802488103507949a802004009a600040614410569051040c7d01c2c05610240120000606c00b501c403640008554190500c109034071000f9040f420300c0d40d480e91102c800003507594102d0550849005180031000f01d4096210401c4c4c80c881c641c03043d038202c100501000000039117121043c049051544944c0d240211340d8401c4094210001d070700004088010122070706902e059030748150f5829085003004240301c851a1a40c2e6203500ca0601404004c50761980e01d0440c81c4c946482c0d010030341e80d0207120001d00c100074194000314040d101550fa00c5480d00d8039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 451899811 1250 451898561 451898581
    0x3030b03070f0b0d0507031d1b100c030c1b030c08060903090607030c0c050d0807330b031e0703030e10090504090314130501020609030f1209070914010806 68
    0x81d000c2e509560300c3c04d101c034550304003684e00055484152445c1c0031404031803040300701c4042e112000500307001e500303c4820100341958880307501386a080122040d0b05880034801002d001030740103c2d00901004040400039080c050000c0c049040002030060280203241c1e01d0828515544a50140444600520002c6408003c0c000240da07180d82d0014403407490041c0c2d55505803014031035040c1c120f46615405d680000c450b0349182c0c100e052300340641905a518139991400140841315400246030161041d40c1c0d200c055121050140103401c1c044000080b107244801c00286808142c408422107654014404800c01c0c2002c1118800c80c0c0c8661542c1404140c09400c00880c000d402c10214009034110070100510714043d0040d882990080c14503035219817250701c40c00103d074001c00e028a0081c03218902040103590412070a42d1041c00c1ea0091801c0407060910390245100c3e4211111003c04040082101080c050008038020809650200b0144542c440200c50405091081000a0058000107040380394 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 451901061 1250 451899811 451899839
    0x90a0314070e090114010608041a0c0703020f0a0804051309050303151002010903020d0f030b0d0305130807030f08030711160302180601021e01020d0e0f0c060f0901080a090b0403030b0307 82
    0x317411409114507800c160049980100040c001e03603010403e500302c0c1220680c03400728075004102015946640d42d81d91300f8081e2910b28904c9001865a010741191400f00710a2410364003a00c108a41060a500e400348011000d03050f4840003405500000040c41918111313803840f41705121080d44c4680c0344450b49a401d9080726840c0b84042e001da08501c40803a07140e48103801400e200080c6050000b9944c07440c00104448861248044003c11070014070030ba500316401c9010030007005207800401490b4116a1440c441c0050500020110400880407a0025000710301c1013a041d980542158007801c41100f0a07419030350b85200aa0007820034142032007440581041d0f40e8414201a0014a14031a183c0c155005603100311103540000d55003800b405000300c1150044002800c00d01000388904403a20305090304000010812603c00e801c20070107013210a46010584000e14800d0034000000d50710030110002418250303030000e0070420000200010150154402103001c3c0d800d404442d14503494045546c4132032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 451902311 1250 451901061 451901081
    0x3110a080f0307052a30281d1008041b121401060b27010513090207030e031605041802210105100b0d02090a0314070e0901 54
    0x31400c0000071400c0240c80010364124201d0b1600c9440c4c2403e00d201e45600e0300342c8154410042d180104007540d8203404001d2110000e0301d0a00e0391030307a0135401404810510360300008034086880071880404402c2140c002c4001e00e002c00c001d603102920304002c010041075803015040564510489030f607000c2c2c1802d500501103031103207807241c103c2e54686840d40c1000e04a1096a00002c10394080d0108449a0040c245881c85200d041044c6c0005444030f095800e40e040d94105640e80d030405c0c00300080c03040402581e9402c0c4240e4000200c0e031443e6000c01258144980c003071500300c0018602000072060400e41c000d010f0b0301d000e9503403196000d4138031342096101c280c440034600c40c05200c44002c2c800d503c1c00d940280004030568480014041d115400f08840080100c014940320000b00c0c2d1040351904207004403036000714228403001d0006d04014009089014030421842030990200394a01152500c4001201443d0804910342400d61001c041507603910403402403031500305445010412039a0140528031984c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 451903561 1250 451902311 451902323
    0x10e01090305030703050603010605062a060405070506030709120c0302011205071202090301180605040210050910050f0d090804140109033f081e1b1e1603110a 70
    0x180c4550138224040c1001078103103035043d5a103040001d2141c0d200802000d90f964001009606400181034244464904401c00710f1305070000410400061008107080e4181c4000b00c3e205a00d07030300c0c3c0303900c1110300d06c202c0c0c1c0100500303000d20032114050200400e58802164401d80e48c6000d840404011a400d41d4029140300b008503500035100090213007290050515054040c1c000100172208403c18a11a4444a001d603910341d07441050005500707211544440b00403940c244640f80110300008941042461003500f010810040b5004030011002d008840305150402e60500002d11103003001c034402da1240c810400c000e070540000e00d000303501480c04441141e07002800c15100d02d044800603401031030000da2007411182503920b03060390882004851044202d55a45540003481c103170303102028940b0041e0500080c0204207042008442003141c040c0200940c0a40054440c3e40d43d20002002d403131480e071488030041d40400e1080e41c0d00c184038038105506029580c0c5c01c885000450344c00c1d0315000050006024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 451904811 1250 451903561 451903567
    0x30b070f0c02011b080301090b040c1416031b0302060f090f0a080a1808010f0b040e030306010f0e040614030d17220f080306040c0810140409080a0908010e01090305 72
    0x50360040105000c0706451303400101440100359219480c0340d009070000e103501588e5070800d07900c608041c810416400810700303203809501064010105280280c4100c804080a40c03c409c10815200da00c032545507124820034003107002158a8041c0d203683c82102d880103203400c030f0800241c004400245002d0500f50340c1c00640305500c1107440e0094190310015295050011480354001c00541603031800c8020f048040001480140d40211101901c950000c0b1038461401d00c41c000c1c80314075000c82103a401410034205809204180f140c02e8400c862030541d1a41d1241c45d0400c0041c6040101c1c1d590345100300100c00f5a074100002c05000d0711038881880140070034441c000d0008202101c1c680c0c24500c00210542086401c1c1401e0307603100c000c1140c242e000c40d40404d012040c0021801d05000d0400b40c80443d09000c2d0842c42d25280c0c0d030181d071200e4030401c2c2a1756080c681500c2961607550103030758050f40051429031744080c01800a010103500e8410740c541da620b011101e8003410b006109000c0d0031713541a52032a103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 451906061 1250 451904811 451904813
    0x90112020103110f160312020915090d050d050a0219030207060f0c061a030606040902090a09020f0409060c020d0306061205061903051609060e041407090c020304030b070f0c 76
    0x10003800c0c1c1c1c1460b032040500130449414003140420207040018502e0070b2500c00c4000c0b41c6401000e036a440704c3d10040c0180103109002c000d580d031001c40d40080e103840044989401184001400201081c0c8000d0f109000d811074549903264010010058606a0340032904208c100010443c204012202e01500603001807105001051107003400100c68119464140900a02512924201e6600e050070103440403e81403d5016400c007841825400308040310104140310007600414040e0070010810702e07902d0740d16404002156a4120301008040c4050f10401a4682e07909d0810001e0031a20406005440340da0800c0e98014440e0107090290b0318540d4510203160f030310000d1350000d410040c01041d40700c8440c003405110300e044284410021030040b00241150941d0f900f0796010f12003190020592030f8180344003030110072200300000d41c10591245200410303003030031a1400c0c148401d58000422582c2402d000820103a07001000e40240c90240e02c40c800b00f601c45030002d440110410340d56002160a2201c604 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 451907311 1250 451906061 451906067
    0x60103020a11030a080114032a03070320030c0603041208070c061506120e07031104060b0c0d120207021804050304150c0c060504050a17030d02120403020c0901120201 73
    0x10009001d0390a15a044004011950b4259040b03142040c00151002c4010041c00f40411080e001c2d800054000e405050442030603040b640e400060000f00020801b002e842180c1c0b4200b101c00011608800d0650b500c103089251034114030103c010540c070030711900500100b00e207420021030707020716808401c038107021000990507191110002c0c14001444002451180484c005024101d40390500c1c041d010002c0782041c001070006100700c0c410034240c070b150a10b48108a0030019100054941180740361000000301400a0003602c09030308003240c480e4000c510310182c00030000c1c80100c60100780c2c8130100001ea040001070100d015030b58003c0e504c02d00c030308292140e0301c4102c4c440b20f42060281c01074030b10385600c2c0c1d5840030340596082201e400041031030350600700348540c41a01501801480c0b425a03d41351a100000701040b001d40109080c100400103a419078480410031030388001090182551220100702d800044484200e81c02c0d409401030320b1402c00149411103400341a125140e514120101c51031f0011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 451908561 1250 451907311 451907317
    0x11b03051e0a090206030f09060114100e0409020604170129010c0302120a1709030309033a0603140c100f02010b0406030b0117010c0e01030b0301090204240f0305030306010302 77
    0x2920038140c2c0c95035140f0158464000031031140d501070002c90b0072400e000c103910385040f20580c8610342a280c60748000f03196a03600500441400c80e140f03400345040f13240d080040c0080000e401d00952240c400a400501a4001002441d450034024020003c4128135040d0701c007080041040072003010710001c21030401c1d40c040c000500d0158024411150700b02441d6080c9510303680844808030100307252040708030b1196540450315078840888030255045080041030741d40d403805400d00610400d070ba4003024085058600402600c204941c88042404c00c0340c1c0714000b8010f10b4035002c2079481c2c80318180744200c042000100140e4804028000c40950615950b04841c0711002c0c00400301195203403e01000c1541d00c0d4082c1d40003030f500a00c40208294902650304a010b00224523840d00f40c0d041000c0e4440032500b04074400c04103d801e003070114a0342580e00000e40113050b6020b00962140c9814030300c07041d00359904900c0000f107144440d0148825100d10300c1c200c02c090684001882540108001007103075100e40c002d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 451909811 1250 451908561 451908571
    0x70203040b180406030501060504240306050403020a080715051509071b02030f01050a0b19140a080d02010c0f020115030f0804030b13060609060b03070f051b011b03051e 74
    0x1442c000d140414000030251819944190303040c1e91030391300600c194a058030403400f00600c140d03444c400210303580b400c041d40005c8511016165950302c0b00021306150081c40807141d83c07076224040c250f1f02c200d0740c500040d0010000000c107901c00d1403c4009400c064034072101c070071103103801030a8080550d80c0c1c2c0b8003100c205082c4076160020760300d00c810310360050300e00700820400403411900128a03464640c50744411103580d000d003248680000041c100da0540314a41442c140d448807184441e038410341c2d4011506280b015481021984101649000b200764198000c0203000120707170b980400843c160500b00c1c241e40030ba84c02840706007000e0504000003074480c072001504512130006030b814581c1c4c9865050a01c0e4040300d072548480034500c0c4103403c00000e072251300b000e860b02840410100c0c0c10455100d0040c00000d040d0710a228015070034030095070080c420348480c4804950342c160f21100482155020b40b03a0300003414035200c800703590b0f200a80d02901400e441303071050020300d04840c5043c0c91904070740000540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 451911061 1250 451909811 451909837
    0x1207060b09270c0d0b040204050601050909040807020301141314070602070e220c09060f031e0c09051501030f06050105191713152a0908100501030b0f070203040b 71
    0xd4401c6440d2285186486054021000700c1170518042c014001501e0b0010469810858100150155603039841612500b082c0c008503070381c0c9c40351801c0c40807070f00402d5460300400b942c840140810142c15044501000100d20a0407070702c0050030501c80055130740f9141e010341d80141e08000420b10403203054440003a84050070284c5040700140c812000e03144211a80030030f4450804c0082d042c80000c039140a800002c190350202412014519150515886c1c40c50b04140c106021444000b82408a440c4c02e5a000d00580e10040165042081100880b4101d1240a42c082410305081054400403481280100c4506840f001c0ca03080460343d81000341200c110108051000301c0c400e071509500c500208511848000e07500c22190060750030000000009410300c00341c1103040c01d204034030020011003030040c841208041c04e00180d507000380903140c0c5a03041c1c001408910038a5025594102981c1010b4100ca026030012606e588a035003541098042c21102070000d0380c4208020040d0300c119100400c02c1e130074010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 451912311 1250 451911061 451911073
    0xc0207090e07081e0c1e040c02071d15061b03040e1008010507020d11010f0212060913030806060a030e0118030201180201091a09031207060b0927 64
    0x1141411200e015100c01040ea00c40942400810707010001c0742003900c3d0300b0581014a401c0c3c4160790b981c543c0340255140c062440741c81b140285111106203081180720050051010b03100601d0000e60301c220505c00c450002600102c8160001d101620080c0543d001d05442d141d12003030f050501c64907078001c81c01d5551000c0e0800c0392140810b003d0003d00041c04d55180c1c0c2c10014103041000207045483c54110201a0349803009200c9420340006100c0c218a8860405034459100341186030700410504d06109081e0b4000504240f6400c500341c076040c031503182140c412a107904c0b907142d80200b080001100501141200c004160301e0b03e01600a061504160725010407501c0d20700140a0944d00d610398007401d8502c040c030386101015028098001504003155550403e44a82e400003803504402d4450030002051148100d500d121014044900385d040c040c0c2181e01d566161500780000303520000003a0746039481e20411004078545900d545010b440b031012000c015603916840b10300d4188419420316079501c208 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 451913561 1250 451912311 451912319
    0x40e0c12011e0501030c0e04050705041508040b0906060d08071b080a0c15140d020c190605010905070c03110c030d0201020a0e030a0309060c1a0c03060102100e0d030c0207 75
    0x11034140c034060000105160400401d903142120003844a030021818507080103040c0c050107030310240d80440c0e101c00310b501103581c1e250000199000e218607000204440c20f0b205890803015003100341e03640118070806283c2c030255500c000c803075210882038030425802410401d440000c0b5100070098000c05000e1940e200e02c0382c07081702100c207901c0c0e666841110582c1022020006100c10a418103004001000e03001070255039549000380007071031a00400e4102003010030000410f0200b41c0c16940b40040300b10854541c49045070317809640000303540b4122040d40c04c200012071a90464007503a0b005280d07949a0081d0b03020a0b540c1a201c0c4680000113003801e110301701c1c0c003040c141d60400c1140d00c4112039400041c1d503046c404600401d00341091010303074020f40c03080d00300c0000a6440503100040307c40524010011003410700d03081010100000100c64625031358000d02c85410f9144000314000c0c14242c08903482000e200c28604190b410012924140b500000061940d07540a90441d207120a040d01c1650b030081d441e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 451914811 1250 451913561 451913587
    0x70b130b0d1401060e010f02010603170f0c0f0102310512010f06151115180708060a0204051c020904080d0e0a06090204050601170c090d050f06040204051803040e0c 72
    0x2c242c1c0800001440340050b03800c15604551500f200003002c0c802440118115203410750001848081c116503074200050b41081e034031402c0107aa0803224403000303442e07540c1c0901000c0750217500b1504082d00a11000c0c0c0c51501c0482c5098550040c58004c01826a801444d2000700508070800c41c1407244255203c003c00e00c070800f490f10501c0058466000580b100741c803444802031103240c1003509000c69034414480f150000034021034082e408910201d03042120805011001d0501001e03921446c000c0c841c8070244818101c041d000f90003903030001e450044e001a945080048643c4144078080e40206c941004100855180d40c000c00c11090000c0c004108405001c449030328000d0b140701c003603801c5e507614032088003140b503e8010190007400034070304000700304240700200200781405003000c4145c1c0000142c118003900d85030706a4840c280c0120560391000c0c107050100f0b858040c06c1307400702e100e070745480000b03001e0788240d09407080008103c5000318140b505104d50021806006003003090408420304c2075000d1806 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 451916061 1250 451914811 451914851
    0xa090c02010c082a0a0306080f030309160b071203060f060305061804051537060e0c040605160b0103140d053105040203100503070b130b0d 61
    0x6039000040e244102e902c0140320190140070100300000c0003810321281442030160341c00c00300c180310010ba541c0900a2054000300004d5110442500036190700c000c4203540030014520440b20513081d01c0305042000111002c02425004000e003c040030b01c103000104410050b83c541e2035249040c00200c10b5100c521120224049512036000662500304005c1303d4245103266400950424004000c1414940d4448d6122078900b11404111602031001648500300a40302103c1150100600080c030000c60b1075203084c8484c4c04030356000c064180200068240c511240f2140b08903410105203050505244c3c046520368050483e05180021100d50000412008441349000394130070700d9807080300f89034180c0581c04e0044003036500e02031240c14081464640583c048512401007088500110940c40007941603104806400c600d4009201000300810b8102c544860340981d1340807801c48494a580751481d820324441c58240002541c4911000c01200804901038110a031000304082525841e03c040000152 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 451917311 1250 451916061 451916081
    0x3150e0f090717010b030f010504030c17160b1807030237060c0210210b040f050903040504060806040f03080c0f0a0c020108070c0b0c09030307050f0c1c0b0c090a09 72
    0xa5521181c05c482440c2c204449100703440d090000340050300e4151400307401d2204464018042240010a03804c14650340d208503000301281c100c4c4550b506078542001c0c000060115144280180350251710f1079039440c000354860850340d00400f0300500b207024804d0300682000300f90581145240d139a000e4407121401800c090302508440c0e8500c13400c41c0c22401004402824007507075005105003e100211a4000001207070207002c1d01000200c0c0b91070030003012500414007440d110030f045144c01c040c440705807404802041290801c540901c03034651961851501c40344103650042205507a2082a40003e0080300042d5001194000c03480c14800d0320400c900031039100b04142d0000406000f159000c560704160615048941441e1068198540c0c1da2a07580460016100c505210008508503199603010412034000c0780d805000e640324030003901c0502d580c0d59400c903046031048040340c06c3c403003030509840d5082423180d4004281d0344660311810918580c030317800b021034640c220483d110b012a0020403805080522 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 451918561 1250 451917311 451917313
    0xf0706110903070b1216090806040309030b010b0408100e0a0b04080703090b03010522020d0212010314030708070303050705271002010b0a05060d0b040908070303150e0f090717 77
    0x5010403404040c1060f0090300a103200c24414003000001060300c8900c56841105d001c540b400d2140b00040c19a0581c003582d0064903907104800800040542c050412401c4912034800013103240d03220b03420050107011303174041c4100540c8020b00707000d03030f118541d000050b00d4400c0e42e0039903418280c95121002e201c40106c0e002d562138100000d0000405074441c19400060111200183c11541420005050f0b01449064652480000c0a4050800600d541111004141341c08115581c0700da60048180c00403007440183c42d041c0c5a604040003410000c4100e802d000da01070815440c265042d6401c0c1c0c02864050104010040288098101803d65411201d041040765507240800381d0510100310f00c401d000b8141c4421641424008809512245410429528101c1c3e00c0e0b80c4440f40000e0040040007a410a90350003410440c0314014003002000908a0500982c0c090180000100c541c0300051402d11450148110b00c80000c0e604c000c0312030b65160003205110070303180d006541c1c10301c124141e2007009080c0e5603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 451919811 1250 451918561 451918567
    0x131b03050a050f0c0406050114130f06030b011812080d0603080f12100602061b0706020f030415050603030d050703090b1810050405030306010c1406011409010905100b0f070611 77
    0x40d0783c00b000204614881284d00b8402641420b000920200229101004000001c50100990f03c1b070082a80040d210fa0703c16904080d07a2040020040d21204049a010894100f050000c085d02851981c0650b1815819803102c0c0c2100c0d69800c116034085000102810740d64440400000c0c2e002005290a94883c222640c5a00240006007130102c0e0103000f090000300540c1c401c012581d0042342c1c003540910f0304000c0b10802d414403841c0c2d8606108204004200305d02c009044081e604031280514091406412828070445081060504131001518030992552080c050f841800e5000c1d04503982c080d43c00d16011030072145030754501441c5130094030b1049240c0441803100b607803141d0030004512103009180b014803c60410b41c49150b03e074800a0f007410304210f02c0000001c140224907000d160b01e413004504941c000c0d0f94030012144042400c2000911854803100000307008051030103110f010b04c03002c4002c1300c0c00303501c4c01d03d01a56170350141c0b4419114042c103020001c0890384a214410110000600850f5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 451921061 1250 451919811 451919833
    0x2030f090d170706140f19020310050a1203030e06070c0609080918070f020a0816050c0303030f06091003020f040b0f04020f070510200a051e1908131b03050a05 70
    0x1703c0301c1c00c01000d04110580c0c030020411000640c04410500840b0f0200041c0d80b0340311707114008801d419a40007550414039910001800b81380f4801d0005c18913009503420480b0a040d04038454840d50f06070b80040009c0c0d1900340c240046941a40b2071540c15100700000e40c81c00c9111808183d1404d809210201100c00d58010840f10540081e0310303540440c86072010f412050b010340d85101d03441c020301180046940105aa40003000400c121088081c4c00c01801c46c1d442c1d18040f400205503031822150701c0d0146417864041000310fa9114000c0c405d4a9000382050150804001408001c1c01c0300c07000c0b2a4060150346c030566145d1034620003800b450600704400c55031a201802d103180b80804c2214207403889460001d04603040101c0c03180c0b007400000b0011041c0c1d40da0345113510454803030203400c041c4c0c1141c080750840f14108045140c01000c140d0750701801000c0710001004141c4070b040d000c035052502d80000c8840100020207122400507903080000103000141e0300ca03103c03503280441c0303060115103a91080c00750803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 451922311 1250 451921061 451921091
    0x120f0f0903020d030203010b07110607021914030303010303050a053105151603050f09090f07081014060f040902030c03040309080a0201121a040c180602030f090d170706 74
    0x201c3c4024241986154034140071041148904500500901200441940d40da500c148c211080c454000300300d65282e420100b10784010030003920a034020044012440b400314207010058a040700e0301500c0d018100444003c0984607540f00a88180403841d042c0d00c0540d82003004159401c260503c0022000e5071030900e0144480092081c0c082c003462a02442008501c03e03001c0c0121100a900d480c1c2151101c0b03036190884664051560400d40c01a4560300300034417111070425044c41101c4669403080c484e00c0e183c9015a03000d0290041c02d5400307042d06030617034090900c02c0041a10903460f005003480d05945800c10402c0380c0088d0707142c0085080000510060550120401d0054015070f000391140343d0701d0b0380c00a48003d48c018044051642c0300c242c1000e0490800c07060224160024006100d115800f1000404440800038030008a140c0c0e00000b044413840001507803403002c210400c10386022424020030070034410356001100c2181e1a48030217100e00180e0005860800d105d41c4000c02c0508c0000360513 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 451923561 1250 451922311 451922323
    0x140d0b0d0c08010f1107060b0105130b210702070504051314100c0512060906040608150f070912081e12010302040c030905030304061d01060602150109060510120f0f090302 75
    0x4c0281c15080031031010742d0000840c100c1c2d51459205900244480304c05006945a00488070011412071004200041580248000b048007103400c1d01c008800b41000c151401e1648002d4078404016800032800380080c0c10250b1000e50080c03041e65025120950580d80d0051000e06101d0031078031608000780104100710107016480c558040ca081480c201400c05650700b0100000909041c030820300e80c400f00f141a125944500082c0800e2410748040c101d40701c510204c440401e4070304840c1c0e103e03a50001000280f0454451058030083c0100302c2e450135403900d4070262904211180d0300e154004207003000300103013107000600014076880130031030441d03156004210481d2610350241d01130500b0000100700144000c001c40f944503034080b070001072230420076043e25145a11000c0400c1958a0444081021034000800c68401e61000500041517a2501c0c0300106550140c0b00e46900983d000c0d0840c810386014005580c11070b8802c0f0000504d04691218840945185541d5104d405a031510f90006259042c803032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 451924811 1250 451923561 451923581
    0x6090203011d031308033a020c0a26040b0705010b09040309150302070b01090c0e04061d0115050f070303020d06030b060108070207240318030302030613050106140d0b0d0c0801 77
    0x40c1d0b0800a00f81e50650840300040030520103090090361142d47c51408030b0095443ca0f4940004546442040311020354581031701c03005840701d0071310702ca104034a182e540000400d8030481e1040c2d07904151900342c89003040d81004000f151a5529002d640200c0d0725240321480c4035031b000b50b40d0051810300d403031007080c144184a96a40c0c105801001301002048041c0180c1d0304403044500000780000380007a0854404504542c50b651050420310005040c1e107500012002e006119100c950440e41d0b9071000e0304898400b180c020700421018040740e000c103134407880507001c00c501a0801515041030342080c20229809900111144078141003440301c5c55900228003035102859000070540d030b40c209088004207001704c1035245804031746a800402c0c010301c40e410861121300c031045860f40e124024600600070307400172180365018018090f241301c0f560100b4040d650494a250b15024101c400001064015600481d5081c046503120b00c20060301c2d071200d045130003ea6005a60310032805092598040c292411000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 451926061 1250 451924811 451924813
    0x3031223150117070c12020c0a06050307120209130908160303051e060a150309081314030a1502091c0b0402100216090e0c03030a0f02060a020f030406090203011d031308 74
    0x401c20050f4120f154568284c2e0020f9686c0c0019042d80801c074034000b00b030090103800440100c030000b45d00350400e018500802c000e0300c84000e14200008072104901840301c4d2903038010401c0d000395258070a981c1c007200310f042c00340102501c1c00018015038010401c0b140c20440000e980c442c10040401d00c22020070780900007140c00c250003401e00c0710000c0d608428a00500c80d60745041c2c480d010b1031030301a60220384176070742c4085015140c1c5000b203881001940366100e074604010794441885200e1501290021840ea03101c544413400610701510b400094004000c4281c200402110810199000c3c3c8103007003810f031107840c440b0700364038081c0305001003881c034604a0030030741d440f4100d0748080c01120b0310b00760291011701c00000f8400d188a0400c43c60018800e4659400d40800201c06c04103d41c0019880008038558003190415200c0d502402c0482c801e0070441030383c02c0020305c0420009241c80d0000c00c81c03240018000324190000884038003400e44000148400c0381c1c80052200c1003010380c81e445200401140e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 451927311 1250 451926061 451926107
    0x3030f14040302100e0f04060303110f060115030c120e100f060b040e060409120809070815040816080414030c030d0c1214040b0d1401030312231501 65
    0x540840d01303012103004500140202d500d8a104680c640c0040030541c100003c105004c4c0e40c2c3e407428003400c01105800000018003c0c2c83c0f00c041d4030540064030034100d80723280304085001446070b01704a0040520199240411220480c005040c06c1940514100d01c9400c501400c02011003405110869802c80e6958002508091080090300482401e80d0304884080034080465515500040c0c000d14401e0030051145007002003901c0d056a03c41242d40c8202449421100709179250030803190346201000d0541c00440e0701000090002d01c81e03001070030555904020540700b80715140c2c0c03604d096400540100c2c104d41e41c00700d00100d452600700410400441e0503405000f8143d50141c00070700c81503040d5409000c102c196600400d0943c82440503100032007002d000c0139115610341c0012040b40d80601c21000f6120b0601c044226284400d4a01c40e04a990544820f100368600144400280c00d0f0350054489100d0100d1301182d01c0c0700709000b0f0b01d02c070702c0c48942c1002c090107840001400004024202d21a40c074181c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 451928561 1250 451927311 451927313
    0x20106030201051c090219030b0709270e0609100c090825030b0109050403030e1903210501410415080f010c020d051e0a02120403030f140403 62
    0x1240c14101c0030300240f904e1580800780000281c226120000d40218014000078210200070b0200d006591084058112030b442c1c0c010212001c80030303030148841d228107140c003110894819a985c070b00303000ca020030003040390060600011f040480803a800c1c0c00700d40280d030100000342441c1c072555448031030f90700305082e0040c20301040b16914174045604428000204030650344d82050032040e0001160b01c2244c00d0829071316140583d01420054030110003081c00c00185003884900820170150710803840b14101c2d60780d0410340f41250080c00364a05000048090843c096500800c0e01880d0f020b0301210f001b0709400c082213800c465201d0550161100503100c45a203081030113059114016181e041100c01083e01d1380b030070420040d00c1e80580d0001c4518810b4500044a148040d04000031803e410740030341d1142d032001441500c01d80b0501c81003000007200d24041c0b0320904600806050341301c00d180b04407449024940e083d050a64050341080d40811030100000b040c036a80016001c507002030345400b80d400e140c51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 451929811 1250 451928561 451928567
    0x705040213180b0306010821091e0f330909011e1503090c061409012607080906010f0b09060d0b0406091409030a080612031315030c020106030201 64
    0x9401103102c2030001d01601078007a16550010350380d040000f400d0329210359481001c0380d80e4084080383c50a1404051090719209045801500c60303540001c1c000111040003104207d0064000d840400e511059849410750b0a031140c40700d5a460003500da007011440c051203048240403141c009a980103040027001014860340750b0810050458004c8400c7c0b0300c2e401e140e0311020071184015040840300c64a101421588141d040d00480c50705d5025070910414151280c8080fa02c22200b40601141d140c003c00010b0190752182044054018000110b0905c43c440b00c03205101e04203040e10010001038205050200b00b203010700c82c65004001c00d40e00500c40300c0c03410007900000d0288161103407140b9008a200078142c1541d4014180d588001441000f41c1900d580c24100100100101d100a1103000e07030018015040010883d131102e01140c541004039a43e01041014079a09242440610b0106001c41c0105008084550029002c1e005100c0c43d81e0f070354240010200d501e000601011603041078070810140c3d0b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 451931061 1250 451929811 451929847
    0x20a030b0f06090d1e0b0708060f0a0f05010509040603081801021c09090207050c10030f0e0604200d1e0b0c1207030203072304061814040b010e03060708010807050402 73
    0x245c4003603456181c1c5a81080901114550f09014144040c0d010400401c503500030b8002d0710451040b100400010040c80034480e03030820700e00039a2000c030482030b0181b0030366020340058140030303400910203c0c0b01038803a5550b00980e00101c5401e0202c05805201c1b0b6950760f01880004100d50941490414181c08104010043c518600c0754540305540000e4039414030030300b0f03c490a4000b00140a0002ca1010404010000c00c8103001064010b4601010001100d81c0070440a00803074100c14040450304070300444404030104007070842e91044502e4401000a100c400b088100400290f10004060080d400d00003001200240480031201040220301c50b480d181c1e00e4010b0f00928540340050f02d90ba281002035980300380d900c1048801e580c3c2d00c164070b900c1c081464014803d40701e00d1303601c0f011403802101c034a00c250300c52070003490403684845030a5001c0d07003096400f00b0200081450160001c8000d000030a00b404800d4400c80c00042607800184040e00003000110f00420f0162001c52a100300e2a00b0119041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 451932311 1250 451931061 451931063
    0xf14030309060103110d060e060a050109060b0d0b011e0e030c0a0320030c0a17010b0103050603030a0f090509040b1b16060b151309050615090607020a0801020a030b0f06090d 76
    0x1500c1c201d09035016159190580e001b00d82c422403c102103208400e482e0794400c030844030f00308201c2c100000412845c02d80c3c040d41c0c0403240710380c0c5050301b80520384481201810681100c0c074100304030110b0b00201d1b90140001c8280c051070b035484403a01381001d03105250801040d03110315070096a0320300080000036502644c41c0804840100f032407600114100000e03041103440302c0c0c1d250b0300075039a0b00007180c601e040c1d1a404034a040510300800112041800560641c0c40813180d00d17070303d500240704040c01c0c2d86c003450310705000c0c1c1d000c2d03d8014481500d9038001800d4102c19101a0b4144a04100f004861001e00042c890900700c42804a404d0240c01d01503404412040c02008050685604d0131111584800f1210720002e00c0c030841043d25100d50883d40b1407100143c2c440c20401c0c0c0e00b070502140d03060800d21500441c500c010788000d464a80b0340b0061220b1540b1104003260821044c4c6c00000b4244400e1020b404000942c0e80d001c04c0b101480c2081001300d44c1c09500843c400e1608105140a594490590905523 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 451933561 1250 451932311 451932323
    0x8070e071209020301110d0b091305190c090c17090106240207050d08031f0303090308090d170a0e0f06090405090f0604030e010f110c041808070f14030309060103 71
    0x302045201003805070111b0440300e0f2001c0008616180c0050703054200d02e01009003510140c200756242600c05e900c15500000241081e0000a192508110210100c181590003600d00681d41603482c4012800c86208405020000f2a01100702200c81e40b0303001e1880d0055000d8000307021083c00e1103a1403d000e008c540c024500740e40301c043e1080140f8001d2081e04000c180090030b00040ca0110b0402c500140d204a038241c0010390400c804a00841c80c1c940c0d10400e59030960b9668134680d065956000895000041c05580f00420380c004d0710002d4050f040e481c82c01c080e140c002c15241c00381c0c50f201420003650754241c0c5102d104104900040d0f512940c00b5100064401c0302c000c1015116540b800d420809a0b400c00b450f41c1c00799504000500da000503968400c1c40e002c0e81c0e400c440c440d4501d021034465551039070310106900112602000c40c40c05030080c46100000328810031070750310166035035021a841020101c5403010003842c9101403000d4981c994001c220307648c014600e185001d684c06a21144140401010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 451934811 1250 451933561 451933571
    0x50a0516050a090b18031501030510020702150c010c030e01020a0c080f1606150515030a0504021207031406060301110a030213150806090601020f0a1707061508070e0712 74
    0x42c2500c60781c807030001400c00b1450303d035840c80d0180c40300b154000b580c00401c2c06449089545d00345200d1076243d41c4c1c12a50000003800d02800171500034070180d40451b80c143d9000741c10170040050340c5041d00092280c40e440d0f1000054041903002c000c0e040d0384640d203078440381da48140314074480b49400c81c5410b101140d0111400d40da030b1071410031501ca140a00107020008003805410351301004595031206440415443d22441c00680c1d64003013000024001004288d900c106002140c400f0b01a030708580d80013480107000d913400c080b0074103446141c40c2c89503105407190b01002c12407a000b03880600c00c09400000642c000c2c080540d80c0d2000d4121413052480c10005c00d0ba00081200148450402c1078015041010160685231180980205280d40540e0018851b03464080030900302c0d8000250840d510a085001c0d02516006850715040301040c04811130121400b0001c40c80000e0340761040c0354224614800c030305003060500ca10246410039641104407441d003502d09000138260410200b07400f41c14060b1001c83c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 451936061 1250 451934811 451934827
    0x60a0803070312021b160b1608160623090c060a11030405031903030506191401110a060c082a18030f071406031009090302070e0c070204050a051605 65
    0x10080c450b614218041c0202100c101403202e00c01b00f06100e1010703004009002e215100c18061055104801c40700c4030010042d4982000038001c04040c01030314410502101c003100b80d903140c4d1030035200d035030000b0700301c1c2c030a030740c1803aa0704040a10f802c40d00580454000c0400c03a24150110b40548108044002413102102803100d0400e4100103e80207400040c040e80d0f5a180044030520041401c901c1c202c001c40d040030000f4140303007048611903503030140001a900c1c42134900111000b60144c0d80700300d07504003d502868038940c500100070200160b4880d44000400c420810001040410064004051280700c81123403400c80010021076811150045401d44c0c0e03c4000d100780c2041040d00b60442030300341c0502c0750b2248401d880400d9550071281a5021510700840b900b0030000c42d840201c0b190b00d14051030f907105102520746035104e452100e20a00449032a59141e5081c15110701c012210850380d03243c001240400c50074203000d003503085410841e05200078240340301500c141c801c4801c0c10104118002ca0095 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 451937311 1250 451936061 451936097
    0x8030c03060a120f1109040210030b0d020d050705030d0f021525090f060f0503040b18191a06181b0c24190203090a02060a020307030206060a08030703 66
    0x10009000150143d820850645404241c407455003000391045100c841c0c04502074146910001d11590b40209400d400c5128070400340d004201c01803029400c03504914204005031125000071020a0003240101031b143d01e02001c1626154030604041c0c01c0140660980d1041c81c0c0015a210440d208015520303002c0d55808041100b1103a155080d90001c61000011200c0541208100c0103030740a032002841c040c0e807101c41c141c40b4641c5410710280060003c000060110741e0310f0384095002000c0080e410b108003003000103149401082e012007000304030515080801c010a044507451890400301c08500c15140440004001030500540d0a805008807000141024202021510300603107000c1e5503506c414040d130b01c1031368860b03c41450000d110116500c01c20340ea00b60304840e0b0720a660100d00129010380e40c40e21440650400751003c0202c0c803d5201100050341c5000c050b12198403107500454440145050091504c800501414000d0719800003e010a1401104450300c103505800d000c2c1c48503104003069 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 451938561 1250 451937311 451937329
    0xa020703020307061a01021203060102070308030603010e1c0201060e100603020901120f090506100f05060c10060308030403030b1509010323070512070306060f0c020303120408040504061208030c0306 87
    0x4000710b2178440e008481001507201d0103203000d400e038207e41501d490f11078600600d100644181e409039100d944c0420026000c20011980104050000b141c003410060b01c143ca810130034140c044110b03c01d01500c01d0f00990901c2958002c194015140c0c007941802809914907617024000d0030201a00001c4208099000d44030741c07902c5000783d4804200001c400b05544c4014401d00d201150381c0e0290720302044500c04202c1070303542502d05902007030038000d2072b1500304904c0f50300101400c0898021844000190b002e68803079100214000c0c1c180b00c1c2e492030140f900600b220aa400e42e01d1041c822001d100940e000081c0031345150704070a080000d4010440e0307220038034000490341c40741020380e08002007248540c0e02101070f02c0110300c01030104495850304001075040e80d0140c00340c017000989070f40000ca811442205280c03815400a400d0344e182192641120281c107000b1078003550001e030b00040030080c034280341c410480100b941d00440d000c50039081e92801264800585240140d00010010565580c2c8900c0c803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 451939811 1250 451938561 451938563
    0x17040819051305011d1509030709090203100e07090519050603010207200d060e010903020d020a1208040819020106050310021804021315110705040c0c032706021608030906030a020703020307 83
    0x2001b07800640008103071425170000012902900469600140c1506c01e070150f00d000c5503004001c0c1507040080c4194800130004000c602c00d440c40340c00700000d992402d40c4200e600409100700c0c034501a0304030301c00780c0e4180d0f0400b800320b500a030320402110b000310303200c0008001c0c2c504080f059800a2070400d00002d600e4415900c01030130003860180500a40c4c441540044800c0e4440c0d02600c84051414006984442a000f005000f91a07a10402c210282c854900e041e0f002c0c1c030810f0300c2424403442a00c410003501000780301c070015031340d62002130040307190800c081c0c40250b41406013549005541216070521542980d01c040c0a00d40100b15034400207844510351010345040480020440c103e002d00428038421164418040d008020000c02c86003094052202800307902c0d1126180800c407a64115868400c0400e8481c0446142510f6070352054000520350003404d040c3d00402000e409000c6561076481c050b4444c070b40c541d104100d0700842c1c3e04c0302c0040e80d5210845900040c0c1b51081800d00764154483d4004c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 451941061 1250 451939811 451939819
    0x40605040c020a0209010603060e0103060b0d08030703090b06040608070905040503090306040309031a060f010f020133080606032a04050a020c06090708060c0a17040819051305011d 79
    0x590920415030014843c101d40e802101c0850035660303500d00c00d408440c0b0501410011580400040c00810581d42008007460030180110340d05450a846590254000707075500000a40c0b40c059040c148148041c4036604580129010003045d4134000b07001d030390340440d882400c01058540002905101060003550107008000d415140c030f6140c1460010485c0156000c11500031800191140030103040c1d07801d29101d4080a02000c280812060040d203a61414601100c11903482d105001c07210440500000030351100b250030340034030800110b504001c0006076040400030354410030800c2055500060300c40d2016a03d03069000556103036883c41d0303860520149103180c020741000305109902c5100e500600540c04a40709071032441d20384840d0380b52246a20720603018140e00c900080340030100184024992031181d030401c544003810000c1015017a00741220151800d03880420f1a40c002e40d401e01103c040b1010b00d19040b03180072081c2d00002c55005442c0034041c104840d0704000ea00c0b03401544081c185c060301c014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 451942311 1250 451941061 451941071
    0xa080f061e01091d06011b0b130809040903030518031608090a0f0e0a0c0203070201081b0c0105090102280c170405030a050706020c3a0f0305070b0f0103031d04060504 73
    0x12103080350031301030710070300c0c00200c00204806480d101d0103d4007031210360025602c40f01d912400303002446c1186440003903600da00104400c141940c1ca9205007070620b44039490100f2140340000002c2c1103141c81441e60b0055070010000d41c081000c941c9420300605a0110b070711500e6004190204881e0806500a02110008210040f07540c0030007850051260ba19030320140480d410380d8101326200e010307405009000c2129100400d50040841048600500311a4080e42c200807a581c3e00e2380c2941c40640341c41070941d500044103030f00e201880d0350742070180445802d0074051313400c0f1000041028001c0c04010f415150f1414060000c12074040c00c4070001c0100034111103281c80785003080e1b40c44a00e00e12420025101c0c0c00450b030306609080b01c00d2003611224410720f444401c008010750041081034486021043c243c0481c07000000d00d60291201c103d4000c1d99000e4452013a4a05500c1071040074048040906008004100003a486452004500505842000094216000b082c080c1809420250340310307040c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 451943561 1250 451942311 451942349
    0xb09060f0f1b0615010314281503110306070203160219080606130e0703030309050109120c1e080a030b030a081b100203040f0206030c1606020a080f061e0109 69
    0x140407070040c0395185400c15004c02a1006400700c0322607902914088030801d00003841000100e158a00e001035420307400c030f0100460015002281c0360044641309092101e1014414002c01c403404181e003000c1034008000a05100d40065500c0c01940c2c050200c0340319601d00c5d50215114412516110f03040c2165500a5584a03a05240c4642e0104e8540c1d0168004c0c607050300207072400e402410500c4081d5805020010304507201100540f000b850281d8080d901e50038060b001411244910141d084c0e550742c1d8004000f014904580c1c90360a450350360b6403500384201054040303a0500100c032b000c15950706001031160354250211303050010410303004c0e05c060300c04100384205511300c50030f030300406d10101e05032108403807101c000604a0005a4020300760710708841030b24005060010085030080d94034406581400e075104c00c030000340d04407844e0485034681c0208464400d15004080c16800c00c02e0000140780031304d0000c001c1103650064031040040d20305070b141040c049900901e160b2000e00840a20440e40204c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 451944811 1250 451943561 451943563
    0x32f070b1c0c0e120307080a08070906185a0e010302010309050f01150302040f0b0d020613050909061006020f030712090b07110a0b09060f0f1b 63
    0x10010114044058072412000308a48142c8020a500e91194448220a08180301804610900824862004000c840081101300c00908190f0741d481c0c1e103005e180c1ca0540d0005080c0e81a0ba80000b0611880401c481c6103082c50484e10308c1030760031140200380240780020f8001604805441e01040d40c4050161a450007802804052081e06040006004026100581440702130640c420417002500b1900140010762103908021200b03401201151a08286d000d4018216a0b25032140040b00341045010011400e00340503035050740071921002c0015080d100c000c50700c402d4004200a101e0390001503401440b04480225002a04000c0c00480003450300c150084d64503182582c0702807114444090015a0038400145071003900c6100c0d010710b0800b1050f9403000c0700d9610301003090b0144440c0e050007140c00d664a4028040e2540912000440344001c0401d203c50001541c2120a04060400840c08035844403000c45c0c1c5005541c3c2c03c1c2030341c0e40c2c003072480c2d00200340030309070600004400445480344101e42c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 451946061 1250 451944811 451944817
    0x91218130c0806060a050301090914061003120e0d110a0801020a030905011505181b0706020307080903040f170114090a0b0105030105040b0f04020a0302040f27032f070b 74
    0x20807900e50704125200d43c001c03c0403500030b440c03d4900141c020401401264102d80014030b10601c41d40d25200da100741c14450904201007160b1021207145544810000d009010300071144140c02405c10050070400100445d145542414019011100d20500515180c44002e0460001c1800f84000c648490050100902500d54207400b03442e15800c000e8038034018500329924070112440184858a60703418170000345413955000b880d20795200211410150911304410040a010388282c2380141d0b28a42007e02910240000e404402a0307441440b09010000c400b0301202d0681e140d84c102d061400e4010149640500178000d480200900a441440034aa800040101d00944075a4510101baa06d600a06080f00c1007210054003040d42c11300491103400001540036002400a808450a15100d03004681034804c009a80e140d070503600c0c2450000c81c0840c42c44030500104071601e41000100d0b54500034100003807556400c881481601e10030180561740241134030000080c0064890140c1d581c0103042044d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 451947311 1250 451946061 451946081
    0x11010804050709061509080c1c06061203082a0d0e01201207050a17060402072406050a03050627070605030a050117060411010e1f021509121813 63
    0x1b04181404954040c3c0480d00900001c400f03400400c2d1001400d5880743c980c3e54008007610f2542e641c40c0040b40801e80004004001303400b0b51200c080c0c5013004e49071550014072009454114800d208400c40c5850030030b400312040c0c922100d034007059401220140a0040c003010700c0c402c4c0010643c10b41c03030603500a03013005000500d9480003800c2407a5a9017201365041c3c0318000c075403c0040c0c464500c002015140c0035a4542007400503100508040c1d4503620084401e10a51400e001051611a488184002c900940c03000d80401d89a03034454501e950f890a80d100c4001c1d10008500101c140606c8810506000c01600c0c4000c50f0111420b065885801a0040e80f003544c0c0b0500c03850a207030001c1140106144208103c89498009012581c2da0f03072294802c0c01600488a8104400e0485007030b0103aa40c0b001041c20b41700228502440d2000080c00a41f800041d0f4010310204d2100100300a10440003190800c1101e00d00003002e0741c4c44900014220217402c61100107039201c070440b000310380144110f5029545003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 451948561 1250 451947311 451947317
    0x4021b06010509070503070e040207030e1009140f0906040b031c08160f170c0d020408030405031e0d0c0309050604090506031002040f05040b0d06020a021f020403110108040507090615 80
    0x1945039201c04842d41d06c012905000400da250101d030140c3e003019401400214040c5c074001c80003401203030024912020580301c0c50002180e812090160310194001c06001c02c5040ba080050180402e0114a012400512003441644d13510034410903034030240906070b14030041402034000e08000002c051b2280d0801da514080da070010030a443c00050003101c10800324005501c0b940751902c03a150701c0d2110217400500300e01c00c0220500401c880801d690010308041c113001005180c40340c0c200700034589407210f8102402c4040b0441c00f0000700041c8003041e80344007010a8135041412000321700f4203a0341c422490384243e401031000180042d0f02c40080d4001402800114180c034280304c5803a40790820390195003d005c05220b000b010030415490941e1100041480241400c07840c94a00c0d2034910890b04000885005a0800c0072441403110420742e01020000c14014110b0500d41580c8504045650303888941e8148000d800c04601480300402c103441c024200036030107215040c0c0f201155542c00c2c0000101c0c0000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 451949811 1250 451948561 451948579
    0x5010501030b0f0d170a050c010e06061f02011118040e0a080a05090f0a0909050d030504170307030f0504050c0102070b03040b0a02031e01031209080105040b1504021b060105 76
    0x46601c00d0280d60200d80d402007614034004126801c00c4680b81c46194112500c100454851035150f0b00f0001900000505880352901c0c1d43c0719603c400c0c2510348103109964290084001c01c41d1599490700001100700d03044c1030b00b600a0040d40001c0e401803104480e110303018100403403071303081d045030181424070310311000d990078000b000b0903500b541e9aa000d00c440003483c031202800340c17140141c8114007901c07030f8041c0100054000050680403501e6480710b60003030900c4035100c42e410760074400b0070410450b80140a1a04005605e0540c0b0f446190811403c007103022002e0020129180c00c0c420f800c801ca1185c201c0f1001c01490a1034502a55642403807420280940603280000807001605020f43c0e10a0f0341103068058a030303980f052094020340c0000c00d9211464a10300c20300041c03145010440740a144603403c103002403480b840000d4802c0c5032551283e0741760b038100010040003d0032200c0c503e030801c1c21120f10107019050390700003c0180c013420581c039802c26019020041c0075203001038040e040360f40941c5c3c0c42c19 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 451951061 1250 451949811 451949819
    0xb0c090a090b0f09070e0d080a0201060b03040c09050c071b180e060117070b120a0b04060501120504030509031f050609091903120c030c020f0606010f200303040f060501 74
    0xc00d0b10351102401d41d000b01081107050141c01c181c0c504a9102e2403502d4100e115403580000500c3d00078124109503100c1c4000b04001d0410750b0244140340291100490081c194038080da2984144030700f40c064411050744840220301c1d1800840255110264043c0b40b1810010a400d914021460544107042d0cd0240c11000300440784181d01c5070500d1100b0b24405002142e00f400102c800c00c13066210b62001034813450300d000440310000c0010300616008101d4541590030042e07203030340940e82281d4455100350301d840c0c0c00300301a070317040102d11300010417204000c603643e0380d141810341710307406021031640d010f01410906c074501035100100c84141c0d401d4440100150340712031052102110040b100311210303a00207040b07004800c251401c003001c003600c2403506500c000b0107501684240c0d840c01e00ca00001c26100c20b494003003640c043c0401c81c00400c3c0781004214614010000034440b1245001a20034404880340f0100042c81c504883d003115403400b0f08507556400c01b440d0418801c0d40e004425030302d1625000c0041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 451952311 1250 451951061 451951079
    0x1020715060b07060209210303010f06080112110f12330c030c0f04060917010e1209030a06090309051c02060421020301090803091e100c020a0b0c090a 66
    0x1c0181d5428040b0340342810000d5480000940c080d542c040e0b80401c843c41c40111181142c40101641984100515203c2d4508440c00c007145019401113000d20081900500020729189200d1398160741040074801d15140c00e2010881207680e44d11004d40080350800908440e0100040101064040f50402140c074001070b101c0104109407101e5803039410100748081401204038001548d01301c1c10010783c071842d100d070703403502e0700d0059000e41c0c841004104c10b40300c2001003d80112000c2d154140d014001c5c01042d4001c064a606d90241c01403000a0b0800441c15507969142000441406a031124003045416228180507004000620420b40718000000c1c1c841e00d0244203103500c0e01100e902502d01401d090a1180580810091106a42c03540100c80c05030130251740d09009840b0000d024003c1e02da0b83e41401c5401d40e05110b221440e500764290765068540c0d0302000011a04407090804000154490302a00105c0c245a40c1c000b0182400c04050140562180c004005080005003203030011045a0b640c4601 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 451953561 1250 451952311 451952321
    0xd09060203070c140112050f040c0b070c0e0c0904050c0c01050108070e070516022d0102010b0d021314012d03020612060402090301060e06040e070509340201020715 72
    0xb00100000c0f507082100c0540071188220034441410400c00140250001c071048038421100600c0132940d100c02c2c442403200c1c4a00c032030b024100c0c09a8107483c110a54a0740e403881000c510808000000c0380002400701304114064902c0740300004e0061001d420115003600c22030304400316100c0154600740001419200c005a00d00807100e81140304c106541d074050094906030020149c00344120502c074528001a540c1e401c1015022194102010750031100071000590869444840c0f410344e0314180303007900c031581c514080c800800d904a0304110074110180600004d0015100c1600f104000fa00000c03507100701c101d00410902610751042d40c0713505a4101200005200740c4006034010000f00402d041740100c40d601c281c2e0044016001500e880c00c20f90219003190071550001440514160900c003040c41d141c000c21010401c1d200c002c0181c14140000910306020103414110f5042d0003c0d01c14001220741101c00c6503228411481d0588240b5441300030f8042d5000302000c440c018540f000800410400d4403c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 451954811 1250 451953561 451953563
    0x601110d1101240603020a03060f03050f070609050d080d09050a050d08070203070c0918021903031107050114071109040f021f081504060e010b13091434020d0906020307 74
    0x10518061400704c040d4020b5001c0c41d080f1042646a00001c04c7c0d0785000b91a040013180718200402d010341800c8529820300c0c400d90444410404800b5040200daa05d4404c6a04203e4000070301582c0e501200d09010024049008002c02c82e014101e482c00600c0320106035080d2043c071646444000b9900d45000f280c42c4d2040c003500518001400e9020701419003180e001402d80298000340c3c04c00c6211a0f00050044100f070120074455041206c001c0c01010340c0072070041000c004000040506d10b0500c00060025189070012020480c0f006c1a0001130000304425040228005402c2802505040c100000c85401c40c50b0241d02480003100109003010300c0360909020315902c0d41d11301c0c40545900120038540e00107811a01e9010f030b00c6650104408c1c0c0c2d40180c0b03c1c0280710141c2c0307280d5120f5403403000d003032040c0e1140e0203044024038084450100c107241d09912a844581d210088008111659501e140041c00d40170111a0082070a0700820340d580002d04c100c950440c944400751300b259549000c0f82da074070501030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 451956061 1250 451954811 451954871
    0x40501080a050f0a0f0f08070b0109020414041a060306060715020306040c050c1506030703050105011202030f060c090d0204110c0d030e0706090306020d02190905181e0601110d1101 79
    0x2007260204103842c986100c51ba1054152034501142c40e1034a00382c006003030b0001c40290f0350000302005480b040c028030f0541500183d8042c00851100e41e050940b03650201210350040e84000300013200d0343d84507400c6900c1c099002c021102e041e0204685000207410880b4403901451502950000003130241d0191249099090002c0010744040c4e214074141c01005040c82d0380504c0f9619001c40041c6007805894042d100540060781c411050f40109031510003144560b1025422100a00a030364141504540f0000020754094440e1100c1e071000c0b400500c181540c80c40341c4000070034166180b0300d000c2100303201060155028441845207121080d1030344514402c800100b40c0c00c5c003040000a0320390700980441e482140006040000b04028043d5980b41c4d0300610740090003112040c0314900d440c4141c290200e680c00c0740300c0501d03e0103254051620307035000510070302040b41c003002420503846009500240c8a208055400401d80d030540030340040f0030b0224006003542407144140303c00b10445100400000340b22 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 451957311 1250 451956061 451956083
    0xc0a1812120c05101d2a010327030e0907020a0c05060c032226010c03140103060b03010e2508010b061b0a0503042403050105031c0905040501080a050f0a 67
    0x44089002821076020382c81c1070000446549400c01c04c1030008074283d560240c1c07001b5000d00c14000b00d001d20590000e142d410700d0b00e041c0d1601085001204801080c0c03120340c0b20100da1041c00c0c1000c1c0c0f2034000c407528882e44460000d0130022400c0c4c1c0482d1a05a191180500b51000c980701d81c1044054010a080f407403586d4428407600d02401c007164124816406180921903000751512000c1007154007440c4500020382c103030920110f410f00e0034411400c65050342d140c10085000b080003a542901e03010f10025003540d44400e0500566a001c1d070104025040200444400d030701d172048040d019800780d041d0500c440d034400c80e00152003d01809001c80d480b80042160340b50107040401a0003003188120345681074458054941e0000f88100003c00c013030650004010405441003d0f20340d250389481c41480101420300c03004212603100000e05c8125103144845004074181002c4040b103001c11154051503000342014000030320342c035011070003110142c00b44041e10003420720030800305c2d030314900850b005084036082 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 451958561 1250 451957311 451957333
    0x70e011b0314070807060f0b03100c08010b0a05120a0e15041205070c150804020a051e2404090c0906020d0503011203030b0d0507050306010614030c0a1812120c05 71
    0xc0750007401c0f0301d48103981341400d1410f1600d5040072250a2851140016074501410400f032800700084030300c40c0c0181070240700074041014014850f46040c440c4a00700080400e03407400c064001d4080e41c9820850044164441c9400d5400b40302a25006208803298014054508c5d04400301c415501c0c402c3e40c100c01c0c052903101c91088110f9260307002010a44074400320a001060500c540e0f04e00140c0b15040b80d5400303103541005d004000c104261903100e1407046241a00c8003811414820180141140850302d01c0d500c810036091400f0044401c040842e040b04000401060920465000341000c04440e40c0b152165602c03041e0507642d03800c8800d078290101d80103000400506841a100e030700d2091087c078012a0306c8410f5004984100607505040b00c0e181c11101042c80241010080e036401019680b070280f0340c0040d100d120052512016110a03aa158000f642c618614003400d19051081c0c403000e282948150f50f844c440144018001048030440c00848280b008503104040c07102403542c01a01078030130030f441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 451959811 1250 451958561 451958597
    0x40c23090a021c0203060915030a020f01020115170f0c0d060c021c031d03030c0714151003050d031a09040f021201020d050a090503030f0907030b070e011b03 69
    0x20082503440e045070200240c04048914100c105010f07070250402684a042034002c002145400401016140d2500c002941580c0e8000400da00115010790300108401c452100407805003d00d65880011000b0300040004e181200400c2d04240107480300994400240104946031528200c04090358410880c0d01c0d400c01107001c540c0308074100032850049401c42e00b488400d516565102d0046807021a9403074490001032400311400c44850002d0101441c510702d810ba491038081e01800b40e02918001e01c00140702074000c1e0802001d00960010048001d151034000c46201c481040360104840501500d050360400c54001d008850341c090f03080703c50000c42c140070414030942c1d081c0200f0580d490b4403c504070202503162003030620720319040e4400140c2c2d03070b039003500b496800d07200081c0403031500310310306145a40807074000700503079421188030052000b1071f03111102c00c51b1802815800c090a5100c2242c244803046410540200c40c040b02070b01c40311481c048078800f00807040c140290250202e1100e80b20250b01c0b00b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 451961061 1250 451959811 451959829
    0x90108180f100504110405010506040612060512030703110d020c0d21031b090509040204050711060702031b0c1003051b1210331b0308040c23 62
    0x4400c2040700c98240301250110b140c24070b40c200150010340e0303490500c01482031443c1d402103040c02c00d44003031042d9494580810b16a00c1a03200300f40410061010225499402d5088000289002004c0403003182900d110561a64000b40048011481e0400c101d42c4001000c00e08000d41280c54000c2c00c03001d807166051041e02e0301416801c84070301c40100010b600440006a042444140d10366001485c903140d1030f008101030340c2e080a00c01c01d210b0800410816645c03203640d0254001d9042c3d402040360307212072005540e140006402e8204034001e100410103030795400400b90403195544000751043c0700b0a040c1040d162641c039002d050b04181010302d4212128000d40145401c0440400202c4202011103001d0075640c000c83c651111400c26070b000c0c400c003c01c07070a1180014056140c41001c901c0c60421805240030761100b1844584c18a1621114030180101d09407401000c1101d06020190b10328034008081c664121400c980c0500e451700c0200d103511505910189200104654000c2c80a0850070448819 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 451962311 1250 451961061 451961101
    0x30f090a033516020d02011104090c0203070210081b09090619050607081b0f1b1306090506030709021c091b080706030c0c0c0e040c091e050c090108 65
    0x281c0341c2d1621003102000080007032040d0b204100c2d02d0fa0300c0ca03681100034140000601000308680c1841e942110000e4108111002c580d60b9100c002600594070905a00f14028044007a41c004481031040031195004224180300d1840b0000394581441c1e0035942140354010000140e41104032800001c00d5400c2c200c00f03d101d0344092100c00480165540300082c10f551007400e0894400c0000700b80d0205000708400e50401c03c031440c0d0701504815081d2038441c1e40d07640e1011004401e10036042c1d1800910b484050f050050107040c294144203142d1520908809454103941d0039010348203a0710002480d030107500c281d4600351a4a8440e07500b400d21210260080c1000319015a1300310710321500e102402c01c1c04541c40b00240000c0c006070150a18141000c2c7c211a50402d0f401c051062100d9000c0009400c2142e95064442080c41100d440d00c80d0b042500000e481d90304080c180700e02e440d0902c0d001e84000203a0120400360000c06110079951220515918000e40e8100d80c00700d41c0140101d211060030450740c40700c3c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 451963561 1250 451962311 451962377
    0x31b030907030503190206090705060a050708040e040602070b070c0c050d080c0102030709080f060c030424090c0504060b0f090f1c230609060f0606040b0c0102030f090a03 75
    0x10b5160b45615085a009200c180c1d8403601c10f0242040543e0184010f81e480001c00015158151408012803914852840c20204104000036050b082003010350a840261000d10640195454107140c010020b510602e01030b02c2d00480840098040c0e031203210600103003a404048060351500d01810f02207191888801190b80b05030034006910070741e00034405940f1801003aa103107540c1e82d1038501c1150a000c030301d009114041d0803c104004251110f4411642c0003540310352f42e00c3d00018100c121341c0100441c48035035400523081c03001d900c0511110742c0011058800483c0e00701320103607540301e41070205d00c80d14010805158040c0040c0c1d03101e14021002d01d10002c8080c009224048004c1030480035aa00b681c0308039100760450100e94a102c0c001c014000f210a02c45000305014109000850742d00c00d001091810700074926030006640f81c0381c4606407401032003030b80c10003130b20344a404041c607000c6e42084078058900e50020000901021002464044654050f100c0c4500c3d40751f80b85c005034200350009039400760 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 451964811 1250 451963561 451963573
    0x5160e15120a0209190605030d0c120e120105040c08010207170a02070e0108010e0d0e0306060f1f020f0c01020a200109050a06020c0f010305010f060c050a0803011e0b031b0309 77
    0x3da2143c41030b442c4186118000755182d01d4080d00d201e411034103590840ca009501c490503108141c0d4000c03002c516070980040c6001c40440c0080e4044030f40c0501807141c6c070f802800e83d0003412841e4a054021070300462003070041002c80c40d11003055508078002d400c0054201da40e50810b84145d8034501006190011281c8140c4907480d8860820090003207084e4030003140341e075441003101c400d0314081c0040d040503282854840c804550440010341c1d0b440c005425103204400400152010f503a404402e0042c1c800c0c507054021440d010144042c1d269810451288154007130341e8201283d0307610104200880690102c80100b0050b159051005441c02d4020700c0f40c1031041c50b52001c5031715510031f60400c0040c000f41d802481050070810038081c40c200e00640c042d040c5401d1000610091542e0078013241500c0d040c0c64404420015070a1003440c143c80c1010182c00c428000001080a0f50240090400c08210303980105009607100e0b64108140300440d03208440340c040400312080c400301e000c000d64001b0030050031608 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 451966061 1250 451964811 451964813
    0x51c0203040807050f0d08041103011b0c0308010515070803100503031c140402090c09010210050103050c0a06110c10020a05010501140a29030408130305160e15120a 72
    0x12a40140e4050b51564408204101040420050382c0d0f84074201c48090441454030788006401100060801458500d98485a074010b031402d40c4103001c161f901c084c40c003400128048001c6d140007850041500001c9a0500200f20340c2064081080010740d4200030f1403030001680c803182c01540000e80710b90a990000040051155005c0000e0600d40901c0814105480544854541140e4620315410110780c0740c00704000143c3d8641a0b4035500460b0402c10a0340c40c81c00b880100d00703003040d800021101034641030000c0184040052010344a60054621000060705c60030143c4a845810844540d144c0c4007034465105400d00c80030070111042540100c458422003544d407142515400d0700603000c89000c488002203103241c09a86075006045c1c0c80e05682c2c0d40b040820901c0208180c10114491090000020504200c1c14500300d980fa070444c40c20003682d854582c0b80280d01d800044940d100c0444070f02401280300865a18020301540c2000c0d1031041e0b540303400d414032014540c0e5480d0709116002e0096060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 451967311 1250 451966061 451966117
    0xd0503041416090c0e0f060a03091704060f1d010315050d1101030c05070b0f0c0c150a050a050114090a0f060915060807090303030207020d02270702061605 68
    0x4001c4920144960b50719070a101403d01101c0c1c1c00c03541c040c20005c074440e0030225616040d250160800081e549030380d444940e140300b600a02600d410051018040131426241d41c03000d840544181e90300c554a8003412807030034100300d03000c0301d8071f01503102ca00c4184140810150300a48c071084101109202044800b951440058045070000c0c100782c64440d20354459101c2503a0600c5152007850f158100a414103c507034855807816800249500c601c2414400481c5c2e05890136010b0711607000494080b40e100c03000352000c403000c009041d24000307402414500410286400341c0a098141c801640d410302210f860f0404100e1603442c0030b4200e100040d6a10714030103c050a03401002c02804006401040f584a44400001c3c05000c0f507001c8420080d905051000c841c3e4407200741c1d0100c030340600e005a01c801103400000d030301030400d5600a5004042812041c01650248003402c0c04060700b01005520b541c500078140e0f221030b412502c10105901101003000168000c03400f400005c000031094180548245110b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 451968561 1250 451967311 451967323
    0x801090b2101020a14030129070503070c06030b0108190c030b062704061a0c160f090b0d030206130302030405090c04080d18030201050c1009150b060306030d05030414 73
    0x41da940e42d400040d10a015500508122442980624590f181d0b602d800f03000d0701003100c0290403011500600e1100000d1011500176a001c0c0c6030048183d95075540d16192241d1390103e0b42c0306600219050000d11542ca41c00350703c4d1035107d42d83c400c1c04004c2d548000103844005081c00c0b80e40300249956942084400d0700e55102400c2849807040c0782c26205503581403903036550f04000401500c41c2d400d2500600c0b1404152144030401c0290050300e50326050004101810850840410141a00c0c02500015804000c07514001244d40140040042c4a501c2003441100e0300360410180242e403061011941800007611541081402841600e04182d116400035620040555044260030000305091200460500005d004104241002041020440001603505100b80300103414410b021540305154030081c00760349510f2004005c10440400c030780c0b030a010601c140110042040345411411960f0341030400882e405074600500130480310101c03010440c0c05030f000074000c1f2800c440300c43d605001d1510030000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 451969811 1250 451968561 451968619
    0x9011205101802070f030810030602030703140711120f0c0601030f0209090d080106050d0912180f050a0e0402060405130e10060b09240a02010209090c0306010801090b 73
    0x2421109840e103020110325407480301e04280003070b1040007984c0006030070300e0340d41030a03036414203000c00c50780d5480d00416100743d00790b80083d00507400001006070142d4580e01440842110311100d45c1c00b5102c8040c03c46018840c800300c1900b07580902e800700d0184800002801210b14a803444a00c0d1041c2c0d00440d604005080c0d00c1105c03100e240c40a002c0861034a4210242d1156a0f94001c040405100000900001d0103210740d41c140400003c0e4000b4a00ca10f8020103031160300002a6010304101c05001480300741028200c4000003040070300884d02503901c1516900301d80300102420307986800c03c5810f8007918030242040303901c07440170000020181c503a103820003901c1c030003000005514103000c21514100291801c3e40707411586484028490b0342018015140018801e90380302c00c041c00d03103003c500d824100c03041d200208804003140b0300c0595a0705400800507860242d401c80d5468a072201c01901f0740c041582c1c0c9a002c2003150340140000c01c1c4d240d00c203003018040200940301016007040455940880740711 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 451971061 1250 451969811 451969831
    0xf0a060306051003050907060c0302150702060405152404020403051203010f0f0308161b0b0927010302011d09040b011409010b0a0507020a08031306092909011205 71
    0x201c104907624041094403a80c00f41d60400788120701e0702e04030181d00c40105020706014001e0407680001818402c00c10102c090300400041c900504101c04003a50341c45048408507414030034103035096404c03c1054501c0f4041c07082001240c500c8207107150900c1c201a40b40b8802034106600340700c0080030402c20802c917078021000d646c400750b8a5040510b02150550690015014083c1013103003000000c4030681120840d051500401069080b540f4180228144c0007039050442c0c01c20321004168044403400814103550211201d12a030891500f44007807001c0e003070240c220b40202d20760040000d94020109821b81da00310000d4071800520110005030a601e0955007550720344c4a980060010017040255020b41a200315021180c81d890849624181c1c40384d201e824003007207008a600c0b411511011134500140442105032612400e4880c80c14182c06440c0c41010001000394100045641c03900800300d454484103015501200c0c0c03415002d2859901000e00741d410007400c0b14120001125a10805015402c091 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 451972311 1250 451971061 451971071
    0x61f052d0d05060a090603020d0b1810020306040f05160f050706020408030405010e041a120f01050a050a0b0d03230d0e010f0f060f03060e010b1908070b070b150f0a0603 74
    0x3c01488550081c0f40c1040031301c20300c1c090003440541c6d10100120001070344043e0381003080c0d4481c007800c1c00141c030a0305014058804c03080844410f100503005503204100c242d40800090b05401c0e100c90a032001981e101702e0706100c42081040b094070a4032141244501410205e103041c14650b560022644540e01c5520baa0300082001c1c0015a8404118090310004503418400c8490920340541d030703d51810752440c415108144031400004052040141c0440316000030005843d10b0386181d400f902d01210039104c07042c6040748a100307503e00040505420354050382d030014210350302103c5518910f28814080c0d28480240400340c1c3d500c880d030042c021640701c89070000c1040c0005044a03010303244216010840b69003006070078403401111110751030860340c10502c0800c0801006c14a640140f624030002500000b042c03501da240600c0d01116079040300c04041c116000c0340d9a4080203c1103004140b00140014082408242c500c44c2004006185040c01010002a10515800181e81c011113034462000302c2d440b4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 451973561 1250 451972311 451972321
    0x30302010e120c1e0f0a0b0114180703020c030909070c141f022808040b01050102190303020702040b0306010f0f090b0612130204060b03061f052d0d05 66
    0x5004495074100440c2045042c65250070703003d80ca03084032a51503078041000c948048481c610411500803030000c0107041d1078650f103082c00c04481110b001d0168103251141090b844499003020f50801100d92000c40301e0070040e84814908502a6206d695075440c50310080c0300311100c0e1394030b0002e21402041203481d02807041c01d1524000c0322490140b010001c40d600103444c1c1c0d55044142c40245012107100d402c6c010707031760801d15241c0302c60b507241844035103500804d05108200c031310340105a884c099030141401d042c0b0381eaa40c000482e6552200c2030303140c040c541000351030000030303020760080c102003403001300081401c0c042c07080481d02d403803001d034014140245041d00420000c4104030755100a3300c1114010f1255000c0c01020a0341803207540c1c09c0c032604030031400004515502d8844010300710365006106004056840c0d4004d003950300b00b5505c00c0d1040f030a07820301000715000c480041420301010740703a06082100a60b55210003601d070790034480c400d402010b14070340c07507013848030050405440400e00013440c1d00342 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 451974811 1250 451973561 451973563
    0x40302211c0e0109051e030709020c0703171e2a010f0e0604112106070302040e070203090d061a040f021201050a031725050a02010e0d0f060209010513030302010e 71
    0xca242d07003818407894400c00e1120b42c490b100c140e0170180c00d600b8201203030754103240400d190503415403003c1212880461514140400410740800326170040b07000c51010300341c242011003031740f00300070841d03c114a00b800a90400307080035000e0004021241e101904204404003002c101c800050001c01099568040740e850482040c0f180074804603425006180501d0175a4840e0360010303a8000c050312860301060000002c4081e403030112100e101040c16a4082d0514840190180d0024080c8403184894170700010701091001007680c82840d001000110a109183c85e0000100013a89004050050300182050305443d01c2c015503038250075503100180e54200c031404403d512003040e00410f01c0b948241c81e003000881c4240f6458208a040b41d80c54560324094040b00c1180101081107940c0100c900c2c0b6240d030148840030440c5800f040c001c0c1c0f140700300a4044000c00c40c0c0841d050704010f2a822500a00001080341a8041c003142a8181007481c68880380f8410240f561038260300490060791101d101c0144000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 451976061 1250 451974811 451974827
    0x25140f100206061c020d0f0c030f080702040621021306050d0b0a06080a03021509190506040b060102030405010c0f060b060c06070306060206060f01030c02120406051e040803040302211c 81
    0x4412083e0f0a01100a540095041e0441c46c038090500c0d1510100d00080c055480c003600700559204204a0311212a86000c0c20f81da0001d0100303030b200f9843c2841c0020b5400384243c1d9080072009940b01c0d00036450f440ea081020122181c59207291090743c42c01c010800b038032000800c01c0001d000e0b03ea5020a80341c01e8080b0401d480c61604840b0035500040d4622001980000f10404443c51001c2400f400340c0e00c00c8017035441c01c2001c0000052030031000d0590020710a010400d2402135006101041c11075480d9001a60f480c1b02d6407003542d002032103107009500490486071001002078429040820008103540000e9465041030907200b4040d0403000c00d000901e0341500c140801444c0500203001e031807822000050706902c4180b981c506042e01d800048481d0362081c040003540310900c1691549542e101d0200034042d4200803114907400d17000c030b441e00d816540c08d84203840445194000079494142507900348500c4d0701c411143c420400c814180707600d4806209001c0d04c520142902d05c280c0d510445443c000344040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 451977311 1250 451976061 451976089
    0xb07020411070b061509130b10031116050312090312070c0f0209190507120b060708181903050115061d10170a090525140f10020606 58
    0x1000800203140001d0f41d1007a180d074004400c952000c1080c02c0d515a19065100f04003000d980321440759179460950199034030410800034162401116a01c0d000e02c241c049641140f5030700d03100c4034244030071400380000b20b00100d442c9101d00c05603410501072840015078048240d1301540302e13420100c0c44503810000a40300a501c1021840c22841c0c100864840120400c01c140002c1e0240703855a000400c003500f0040b44488170030b0300e03803c2040b9502d00160000d106030411812040c5081c10f00540003540c0ca080015034002542008034540f52803001c2103a9030b01c10000f031590580100c203805500d2443c41029000d2001140204004145880644200064120a9040071050240d00721350880380d49224441c0001c4004190382d040c640500a600c282d03024440c01c1c01c0400100c0c00c00741000113400303840c1c0288104600c02c00403038003400d0180c00d0f030300e4001e105282485003020640c0300400031004495900d0742c00600190030a840c40c503000002c590240d200518080160380000c0c14044030f420a40000c821f44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 451978417 1106 451977311 451977341
    0x30b183702360901060509060f010e060d0c20100b0105041205100b03280c0b030a05071e020a02040218180108120a0c020907030f02040b070204 63
    0x90550b141040302070400d204041940070f441409130314161000241003081c10790782c1c0000e103d071040c00fa0994604115101e44030000355100c0e0402000808c01da40030118025040440141218402c0c0d05034500281e14262035081600d400b03d40d55141c40b2140a000c00d000c41c0c4900100c030a0300031740e000022088541c070005800c22100050b8400c0360b03c8001014004408018105030720354042c2c3d200c0b0a203100540c40320164040c59403c2c02c40e01d00f880345a00c0c5072050740311100242281c008464081d0502c1c0d5078418400601c0d004007019180b0301d1442c411050004081100a490b1890a0740082c0196004100e840e10030b102c00c0410202c1081c080c0614580280958074280600030a00c102c0501d809a51407a8a01140c3d401c01c55142c00d18546503541c0c025003e80c01e00804050080001d8105503448034486245c0807903000800c01050404041c50b116140b1f80104000c07510011920444 = true := by decide +kernel

theorem cover : BRFrame.Cov 451798561 451978417 := by
  have h0 := BRFrame.cov_init 451798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 451798561 ≤ n) (h2 : n < 451978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
