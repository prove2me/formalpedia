-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2524
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:57:52.360249+00:00
-- url     : https://prove2.me/submissions/1cd1a090-814e-4f81-8a2a-5d3cb381df5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 453776978 ≤ n < 453956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 453778228 1250 453776978 453776989
    0x60b120402040c12052e030b1605040522060503010e19020d050a030f03050f0903031f080d03020d0605090702030304082a1b04050c070206131d010906080606 69
    0x801941c1102c001440c440c0c8802c05a42402038544900c90b120b10303290400207a20308400d480560b1521000e00e441c13480b0450948054410000d00014104880c55400101001e4107040041007010303007803c1647c1020781e213000160810800b00d40413080b200c03810940c0d5032032a240303002c0d000190100310000d2290f0384c400725034540d49484110241046110580ca002d00795194a980701e607069400100391100790100d4140075140400141c800c000091402002030913001445039100d0203a43c105010794510b4440c0e010761864800d5512800350300150030140080d00201c20020500b0844158801580360b811014419040350540d5120300c2c01402d203a000c01208030390202c203d80d4000d0780403a216440300e44c0122442c0f00a442402d010340031107681031105860180025804606c1408046c029410f144268140070030740300f0a40c0c514036200302c1400014014a0f0200c003902111500c418403074400e568071070b0a004824680c3c045810024032480c018401d19015024203070260460344010a03450500101048 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 453779478 1250 453778228 453778231
    0x130b03062404180b0112110a030308010b03180102130513050915180d110f0705061b010b09160f050708040b030a09061a01030b010e031e0f0a1104060b12 67
    0x500c00c0350384142503886441100d942e0103003944c218000b00c0c015a150464024000036103081503075400010900da28042c80c1c14503259081c1e9034581e0f1400040d929061601d24190005031085045542031142c03015a1003091004e8100c0c4032600464002c0a0300d40380a2100c068007170303c0b192400e2410034042143c44400080c401100050340c2c01c601480c0e40da003100300300c0c4441041614055900503145034100c80340d4003ea00340e8884c2e0254040d1840001044001666807642e40318540e0040b000f8003c1c040c0340b1a60f01c0355401c03811004400032440585010024050013401c581c19001500480c0c90f588a40750300401f001c05c0d40d981400c0142c81e040e11390f118504207008078170501d400d030070000002030745140160b00880840c5038440d1050102e50640200041242c40c40c0c0401800207181c03164100440d81b00d460b00395031000d80a03010788060504044180d00b01d04c8541003040207449590b2020b0791a10b0200041c8407610b0203640070781180c40c840310030001079511690200c81c00d88400e1120034220000b07801800d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 453780728 1250 453779478 453779551
    0x200301020f03070c0f1712060910050609030709090f0c06080f060f061603091703040605070209090c030f06010f051005192c03010b060708030703090203030702130b0306 74
    0x8113840401d1400d080c2c20303512060300034405a0b0510304400c6000e80c031005040c3c00025aa60011103540e288140503030724800720b4a008401140c0d030300400650600780c009200340384002c0c003900ca075180c40740c642d42c056400c1c6801c00c40c3e4004079040303080140000300009030060001460030383c0103414040c564901034003024044a108011070707032030340006580300700440c4c207100040f4112114034039990034043d04408152085200c40c03841c5047ca104501c10200896056446d0b0381c882e04d00300441c580910506100080c00d040e00d511174034021020035540bc001550014400724020305407581010b20081300c040155101c14003922060341c0d003681d0f094114058400b0500c0758480c00d913000c1c1e0003010031175800a0492200042111012603507140045403d44280040300580080c0452140d0314240b11180c45051006090b182d03003440840c843c00c0c0300e904280c074003a0001301105d003003811540014459140320380103e4022582d45248400600f024041c1590007040c1c450058404000001c0c07080080c400c0002a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 453781978 1250 453780728 453780737
    0x100b040c080f0c2809050301050115080606040902071b0602011803180b0a0c0c12030c020d0503090301020f03010e2518090216031409030304030609021c200301020f0307 74
    0x4804249080035100541c401400b444080c0109810130014070010180b52800180f101802048a0a05010b4281242d02c08a060100c42c155003204036411103014208960181040200140701000e60000d02262801000200c2c00d00000d902062111502e6501c080156410311100802c068407504403000100d07010309014403400018552517070401c889030000504038402040a0441a84c407031281020310b8070419050180b261925080181d14220000c01000544030414030001801c18006040f9840d100d0011a820700ea00e40001a09903007060421307141d40d8a000c0010040d03540750709502d42e0440703504840b182a008100c0005892083d41031a403006000c91403d8400022101004250007081b02d4041151148107031880310040d446990b400340c000403848a40803001070071203405c98a4610004000307600d003d00e10390304c9402410f00e450040c0c0c4c1c85040c0d40e4a58501404490000049510a03034007070850300382031301545030420390f0f07001c682c0c0c000c3c0c0c4103000014524400c0021244c1101701d6091 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 453783228 1250 453781978 453781981
    0x10b19080330090304090c0207144c0e0906040e0a050a0b01030c0b0c070e0a0f050414010e0111072003030a18060302070209060910090608100b040c080f 67
    0x34024544000784042c8046607681004014510310080054000d45103c02d8080c40106d0540200700c2c1e54044d14029185c0c1200c0054202415180030400c04420300c610a07036090a6011180c0e02c12100b2042c6e402003055850384901341c0181400780e001481041541d41002c040080302032010900b0381400a03d130b54051540c41200d400300e84010440d0781591a030040c219142030b02c0914000650300820311049031711800c011000300d0700400d0101550310345c00076507004042c5a450950102400c0002500c2c0c03620303003a922020300808081602900c0e10550003001c0b100c4605041601160031501403045400c0c0591400155142080c01b81e01124080d5810040601501120ba1040040c41344070752401035240c0702c0050780d0502d10703422a051050380c504c9030102d00e9000342c0c2d400054050748120940254000b07920000185246003200c865a0031980061080c00c000317860310704040880d03869800c2007225502414454402c0511070080901c04503059500303020300e168009002e00040809017011060592000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 453784478 1250 453783228 453783277
    0x91a090112150204150c0b1303050304080304060209060403080c0c0402270411190908030406090608070e19050a0506040311060a03090c06030501052e030b0a09050702010b190803 78
    0xf010382d005483c0c8420404501400c085018183c1c4900f29800c072031048010001a5514104000c800216a05601e46074916941c541e1500c00c6980010710840d000d0f0b41c20f01643c000c030b031203100c060b01c0a941310b440f480307903286400d58900e490442070441e181e207d203004020800460018241c04003000a02030450110300e0030020009014240403038420701e4024020030355200004441d40c00038104112920b64043d459180c1c40001d031a481140680004219405400c2089520541a8a0b4400d01901e000c0d00d0a02d1080c1c00541040c503100c0d4a07a151600c80c0c2c0c0c06002c04d241c202c4042e402490202d411034030f018595980d800494800e400d03030601c105008161100b0090003a04405513540c0d100c038a504c202e0b6103030340f0040c00605e0203004040c0108080a045515070210b00849950044001031814202000c0f03101100a0880c50903441e80040c2c060400190052035030061300e000d80c10940020940c2c801c41c1c030034810100c0038076031040c1da884c102d4801044020300200031980e90840b8000c0080c425030880 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 453785728 1250 453784478 453784481
    0x2071206020d0507031d010c05121e01030302031308010b100c03021e01020d0f0507022d03030a0c180308030604180203061806090a0b060906030115091a09011215 71
    0x1030b41054070036030901c400c00408580c1540a0a02c2803001d00c86a41801c0b14454100c1c02c0712005c00464003c5402040300f1000d219040500940c403441c42000d4400301d1030704000f0f880603030800303900850143e880031a00d4680d1204a0340d5030313006400c0c000d000b00181300c0364200007107011600c1c3d82680c0134808040320711b10a02d4402d10541e0458600308035000d8101509840e128003c1d0b0040070280c0146103050390401039030045005a50140d0490307401068444441d59610010f20400d8094240b008074003144030244076414000785106800c14100007842c0d1980290145c031241d0002c5013440100d080e40010310028001c2010350360064001d0b1000608414020900c5000301c00704000030398144070f503c0400c69290000310030206c070b49805005855280d16602d1f0b013603682e0007004100800d00545540010054202842c1d81c0341c0c0080000c00201b0f10705100d04c92039003292100e40281204548070f0100c0001d0901901403006002410354002c101c540c07405c411011000b40401c0010a803c124241c0d00449a140707 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 453786978 1250 453785728 453785737
    0x70c11060c070e04050a03030b010804020f0f06090d0303050406050903070f0b0a18060b211915020307090812040f0501050d0905070602030a110a0c05090a18030f1107060207120602 79
    0x520103c101c0038145030400a0b92038001040440020b420310080d41d0032940700e407820700c2c002e66014088542c0c005210003003040d0091304101c01d85d00460144100112940ca0a170260780090190300c0000701401c0608120341900e20013440c1042c1540b08014020008800c518064a03064102c044000e0705c0d202d4080b590040c0880c0448080c00340c500d17004c01010b0281550241a110a041321050702081c00c0002880a002c00d10091242642090039400050405e9180800380d4910503014220040310307100c00c2104076042503501400040e034004e0107000d007800402400f000d201c1d02c0c400700750910b40b070040710680f916942c0c0076a80c104000881c0e2850982c1c030079048001e0b0b1580c8142660403058854030029074a80022240d54002001c24141d11215000451445255a00a0401d06004d401c00c42482045a006080d445919681310071012300001a040b0341c054141c8250760b0350f03450781d146282c0144105448001207800e13811000b000c00466800140d180120303003210401c52200421424840000d008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 453788228 1250 453786978 453786989
    0xb0409061a13020306280b040f15090b1e070b01090912051c0e03120a02090102070f050d0624060512090c010c0201120207061a1801030b2202030312040506070c11060c07 74
    0x1181c0880d270028041c55010a549000f00d502024040c080300c2200c507920b55108041d0440020800c0300e0020104201880d1340018a6070560301c0c082c019947c0707202010090703101d0104203545000700020440680d609010300450381c41c2103810148000d410021b007220900c00c941d1030581c0c0e228840795420301801a250a20740d4160409120f26002c81814084d50086209a006004860300800d48000340c1d40300c2004d43d90040c00c0c15582464030b503503100040024030010b10342c1c08074a00c6200d441000000b00c48000d00126070310140c41d641c0b003c000310068440906003c0442c0c0010012030f150781d900550100c1d0998091800d20030000700c0881c00d100a2051540140610742800c50b8030b0707031207090b01104c1020084103407602000300010b04800210104c0a0000600425801c00428038815000e042e100c485106004204174890080d03001a01d1544090311540c400b03080c1c041000184541885200d80c40700300d41c24448000007041c0d80744080f041e03488903114462400440c41244161007000144040c1a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 453789478 1250 453788228 453788249
    0xf091214010c02150606070c09020d0605130606030605010c050309090411100801180903050a030218121005090106050a06050d0f110304060e031c0b0409061a1302030628 74
    0x184480e000307450758400102a01300604500120b1018140032080764160354003c40703210b401c00d0401c1031b50000ba5110415510540351101c4d030101d0684c0d80c3c10541e004452694200055041c41c040018040c1d034960380c00710303060002401c01100400e1000c0b040f10800282140c44040607541ea203800d1303455071b040c021000d81020403654a0240c468000b01164161659400314241c0c095090501d1010f641c48010000c000810074414401c420b4026009480d5001c085117016245025000c0416610381042c90f61240681c413140102020040358030409400c221020001c0c000c0c2810306010840e05800d0b44500310030031800042c0361105003826800101400c4940c1c0313061150f01d0707850043e400280c1040d201601d03158640240f841003405c000045840c162000004e00d05655907444845005002080301d0341c0d0082d0705c40480744000f4045105044485403442c048400400c510805d21610f005481c0d0b00c080d00600c10400c0c040c4a40d501e4446000c000c0e90300201c00b401d20381818401e00700f02e96661041d00d596 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 453790728 1250 453789478 453789491
    0x1b120a200f0334030b060c03091002071503021c06050a0b16020603130312060e010e0c130618090504051506120d0503060418020a05060d140103060b010305070f09121401 74
    0x40f0100681481486a950500105610b141089220311451403510302680c8204201d04244c00c1440d020f0218142c1030050740c1c88596107440141d080e2885d41c17402c82c0040d0340050b94802c1c100404030b084140c00318142c0100501800c14012032071303038121400390000070100450f20803080c2c2e403101e643c5034980e94054425905ca0030400e01d802c80b010140003048000c1108814500d92801d05803250108031613000c00300c12450f074a40160030ba403400e405803030b52299507000c0080c040e051100b0035140004203441c0d900e0b0031118018402e0040211f0403508031100070343c00d080078400440c800203800d01501c4510195a005a103c1600140740c04580e601d03c40485e004070722a074994203805c04042c40c41401d003071b034082c0401843d0700000034185001c1c24000b540b100c2007510605c80707810804003901a81c00007110000d48640303041c0c0c1c88030019100364802c4a01c10307181c2d2030502ca603582c18007030f03142c01ca000ca080203030f88405020005451200180200c82c429010080c0304000d0001004a541c0059842c40003007048 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 453791978 1250 453790728 453790801
    0x91018020402280c080702090a0209030f07031407080709050a0221040303060e0403020a11030102160c05130e0319020c04021810050306030c091b120a200f03 69
    0x14944090200003d500b401481c8010180120318030003903694012280c0c0e2a10708130303508205030120b0107400420003035030074800f0b440180c8040050546851040008040031807030361501c004540d40c4500440c50b40d400c500c1c4104280c000010b10102a24035040002c6541e541e40c1420a000b4050a03d1510514641d40c058003032070340c00122481e008500965060140c40d032030b214041e68412050f50000c00503401464000b0201d002e03280c00001481004001616040c02c00544100707541e01c02000b6100030401200400061400a070b40c0703190300b6907203c02444648903154013242c8a024140024400103000c01c10400d0640c42880108810302e00100704640324600e18551100ac000c1c4105c0030760080100360051505940550181e0303100d110000c0c000d003000c50b454801e104540700040d0401001074100d0300d1500200340c510018000c1c480000520441c64038004149900f07070b40e0444101c0015030034490011440343c20303450894803110300c0003c2142e41e0781c5460020122500b41139000e00407160000820760036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 453793228 1250 453791978 453792007
    0xc07030c0609150e010518130b0306150a03080a03021c02090f030a02030705010c0f21091401050a0f0e03060109061403030310090b0d1424091018020402 67
    0x3518076642e01c0071941915540b5010030800d400d903c40001c6401d9445016696100324010115440328034401d030b001a18007408105032081b051070035600603845c4d01c407050003400e00300000e40c0e0102c4810b0041c0c428811307030390203d0344201e494000a01001c10004100805c03038082e804541000484003400c0c00c8840c07401074064001d4000c1d500451050b500e0040c9541186000aa42100039400801030b02a862400c030054031120f03919a000c81c1c914281c15846004200341e9140c1541000a550111305482d4100c600200810702c00c1e00030518000d004030001c3c0311a6400340c00c0d1001d010031400d2901001100103000d5a0801384001081c2c0e05120b80c20022501650f250005c00071102500c842041e80d00d12402015142d00044460300c00000c942e5600b00114102c54206040805000c3e107261148501a00c80710a2164522081e04050388908004550501c00d0b214190f40e5507503110000b03141f401c0810b0704544801001501d103152075107400c540041d00031b400e100044070384da00500c110340e2080d0766150f040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 453794478 1250 453793228 453793253
    0x1170a05010302121b091003050a080d1d031608041e030b0a020901080a0b0402040315020910030606020d0e01090f03030804051e0a060e0c040504111e0a03020f060c0703 74
    0x13405044d0300e0803010444003000810882c0150a40c003004100440321040c88104030004040e032103019000345001022600500582d15418014401c840e80c03051080703201c0c000d4903058420903400304449a03818002d5074010066070b0021400455409a403040c80c18841031500980c1c00c030740c0381c80304020f40c02605e04210b0881941200c5c41401c0c040300c1a42c494890344100d0180700a40390100e00c11000180324491a94000c80f0301440081c001414142c0701d440d102c007101c0011002444c42ca5000034074200da4900905031940703803002850280710403424020002d48658020f65212705110303603942ca00400b80c1c00341c0100809441e502e807a000000303540c2d080042c143d400c20f54068446000301811517058040c446201040c4091800003030840e403040c0d50304c840040010b810034010602404100a006598501078030b4000c5000d402031350340c012010300802c4015803075090700100d886803120080c0c0460f124840d0b0034044940440b4114a0f40c44000007284680c070910900710003a0080030004003c20035081c5642 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 453795728 1250 453794478 453794483
    0x408070c18050a05181510170304032f040905070b03070e0a0914130804081b10022e060302040504030906110a21052101140f1c0201170a050103 63
    0x134072964903aa40002141c1c043d00880c00740c1500117004c0d15600b040400c1703075142c104140441c0802100d0b904c00c11132013401034050406082d0b404c0082d00b003040c0840c2d1108070070503501d0262003801c0c039441061110b41010903d140680116140c1502e00705022040c0040c000500b0b40c42481740d1340b854000c2d401013003e6540c0c200203119900c104408902d181e46440342100c08403041903010220346419080381400d550f5482c04407149401000b0205180d1818048190202d0b00c00c00c910004412800810501604042401d400c540c40300712081070402c9405a038214044007400414141c080392894980646401d8002a400c1800c2c8024807003016840300910301180da05035543d489009120142d40e0301c4808c01c070000352940c0402d2048400c81d04110355028012885803c0452504084c4a0724901036419148101e0007411000c00401010200d4212007541c0c500c1210f1541150b8813240005003400850b4a030308416400d08400a411a40100e009092a07010304210001a26006059030081c0030240401c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 453796978 1250 453795728 453795731
    0x409050c13020f031b0d231e0c2104080c070509011818050f010903020c0a03030504090908160f05150c0a0804051f1b05120408070c18050a 61
    0x507210610949520000c2c59400394610b44403204080f9140b0b681000c014403a80040200790010001c42c810300301c2c0c601d8001109503100301d60940c003074a41103008125402400e8034000311120ba820081400e42d003e201c40240507110300d480401544a2032501605941c05070081e000e2100b80121070380586954003a017030840d0882612030040c030a200310284107200307694204a58420b9000c40b01c0c0c100039000311201040c1c00388158281c848924148203e180300c88aa507440d00e5202c03d040e818418981c01d140187c51b240e00351441c3d41d800405500c100d106402c1120786d1080c3c0744080114030011038407080c0c681c4a11b0f05141e0b4103400c103d8906100c01c5001c50300c9101c4d1075412a20300704100740840c462401040300c1400c2c2203a199050b10340c0c1900a0041340c0601a44100990310310440d600822002000000054041a00d042000b0a0071101c020301c001e20806002e202240e00440d5a80e55100f0761017070b5500e45a80c40e510b07001c1052200c0c2d0300300c2040c2d448000b00c034071a43c003a0780d800070344112522a030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 453798228 1250 453796978 453796999
    0x36010302150c0d030f1104030f0309080706051210090606270e01030204090f02030d170c07121d0a03060c121506030b060c0a0b06030d260a0b0409050c 66
    0x262610300c24552003181ca038022100f803540f02d03402948207510b0303d401e11102040701e44030b40c0c10356456944290070441d2040d00004101e824191300400c50005021104010410103052540190860103002544d00b88404424005000124440340c0e9030000c142c04442448010b41320403000d886072102282c0b08410142152413100300d40340c403802c44421145000703080f80c841d900355020b1002426142c9000d0315012000003810b00141c9080103460020300407a81e070010360001e410307202d544800700901555000030040c84102d005c00c45500e0501c00305107840c03d20b81500411000c000c03c64000da0f801d0b60743d101c000c0140000500c499034000c0c0d400600103513240742544030300c00d1008003260380200da0801c0300118004103000050084d400743e025001300500f40741c24203250341515482c2c807604c0101111150b824030103004580c1010041c5000c1d000041c18401c1d02200e02280c1060410240e00040200c2084000401d41c580d913294000c3d580c140006d041480446100c0c10081d0b9150542541c441c0240b20010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 453799478 1250 453798228 453798259
    0x140f0a0507050307050c032209060e15010828090c08190b07031509060e0f0705030f06152106060705060402060703090503062e060e36010302 62
    0x4140d5108030001e8031000d04603168108201e8035604115075401052208000307040c244070391800c43c9607d140350a644a000c00e0700f04124030065443e81d5019480d0641c42d04180030501440c0740030b110051701d00b8a0514220b54902c4d0569001e090401400c8105074465450740e921903041c0c0c1c0011071082d006c0c4c2107e0300850350711200715950f11108140d20a409901140b108002040500116044141c615000c5007410044c150300c1002c000690041c404d0541d40d01e8104840c19034030380301950207804170003041020b1421b880c001d059480020706811444c1160000280c09076502e901c0c820041084124035500c806400c403030b1140000b0344a00c0c2e103a0911101c00007920515082e1300319603503e5400009040c081e1240d909010903500184011018440c04800111700d946040013418892000d40c0401c0401440125940404043d04002e040210611709003d01c85150006604402558251030249110003801310b1910101d1280c51603600040303030064980400c0901c40d840318144c0e4000c95042c00000e5205 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 453800728 1250 453799478 453799481
    0x6030705010f021903051312060501050901060801030f170304080a1805030307031b2901050a0506091c060e01060f0f0819060b100827030904090f020301140f0a 70
    0x180b4104006030310480208016542e071a00c44140d45101b814003034201864000018002c4400b500554000304050f0804028001c481c052640103107c150b40501055040880040c11501f05000141582e180c0b5007841c02000341d64114070502c03200c01d80c25103840e030500349408805507000040c43d800088202c0c0f080c0c03002c1078050240c4c04c215440100214a841c07203564090768040c00682404010758410720000d07001c0340c50006420140c920101500007018030b070400d50190303264181c22441c080c03503042409001903140e6004031400c01000311041c00700c10340e48400c00000c2a451200007840642440c0c020000090150000c10984408a03808442a0b40b9600e03c0805c11005101c3c4003410f6000e2121103c06003101002078210500460012480101c0c410110b500c02c03c203001c08000081d184402c114803881c04600140c441c441d90b000042d401d4243d222120f64900515421070311440e51040303410204211031311100c491f140c1c00350003481040144480d03200b07503c200700c1d01d921368a20260001900c0c90a503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 453801978 1250 453800728 453800747
    0x1f120302031908040b15011e02120c0f1b130207051f020c0f01090807141905030d061e0506091c06020703030e061003080d090b09060a11040605340b0603070501 70
    0x41c0d545641403900a0401600b490f800008c0c4000d600038150384c1c00d440d0002c180244031101c18000181298120383c51401c2c42c0010010312124101c2e040b203a08002942d84140300300c1e406028402c056120710b0706040a9040200c440c150b01a411802d000400141c405500034140487d00a4141d802c455103a801250980f040048000c0809508004400015200004e640c5151a072070089444e04400020940c0304021841d400b50340b00d0380b001c60015118400350003040301500210150030042c403403100c903c542c0c01c48180202c9104807000306008c4074503140c8888081069170300320300e8210040c166050600003548541415070019081401c44001058001480d0740644007081d81e1036030807481d540300c41285070001d02a604200c2c1c0c560100714007150712908000d004901a002034001805c0002d00c110448500504500c2ca81c0d10900041191a400c841030304d1a01102c0303121894461031203020344d1500703261003003850910400806400181f1503c20174042c403446080d0101d5105c5034035440150b588006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 453803228 1250 453801978 453802021
    0x5070302040e150c0c0102041d0f15010f0e031015080d03060f0608070201110a0f020c120d050c030702060304150f1418070e130302061f120302031908040b 68
    0x10441c3c08100502043c0c0014045003442200040c00d00380c582c01c0c5002d041602000f510500c0302c550040c400028200301e003103074210b92070052000394841c1180020701651034941d4258180700600000c2101500d00b4800c082b2000c07104902084000354070240c02200740014020b0311028407a1880c2c500469000e072048000307a030103440d00d248000f1b160100440e00c1501c02010310085548a03854040344505800140c00513100c59281e9410b420401c40000b0300d4031210701075580c800e0705c0031004004654804960b112b40308409250003540c82905101c05480c40c0714140c40290840f00020422043c080c00301486043c04a01140611190140a070058191020309407200784e90ba0840011460000f00f4408100c4243e0071079060301c06d65541e5045508064008a130075420300800031603002d040582c144940c40d804a0403258a005003d0310240403920080c4074003d003120402c50800f00800d060007041501d201403910b0044020808416400416041c000c0c0c0b0115004c800050101b0714407035500351303d07054112 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 453804478 1250 453803228 453803263
    0x222140105151b2b02100902010912230102090a09090206190c12021f360804060f030b24030604020c0708031b0708101509050405070302040e 62
    0x503180c035241c0f0b40ea4503104940e8506120358201d02003100100406801a5842c440b0301e40700c049007600300a41042c2d14122402156440c4c24443d00c0141c0e005040f031020344034010000076180d00d0a01e840069003010740b00841c040c04085132040100f0340c4c1500100b58403401550400345807076540101106949c41c08000950004e010300c007010350800e802c0041c003039804603860a4000b401003074841d400b034000d11001050040e003021031000e0b004100000460644a10803008120007080d0703202d031502c0c90f803201507004080c02603d1a42e40381c1e103244400b6080d61540010310660f407295610005041c4c0c030005100c250110782008040c0b00e6520309103109400b00c00d4981c006c103a106140d03035040849075000800c000d2b80725500740141d11103c9810800304018081c81002980c0d41ea000c29446200d41c900308880e50040d5100c00f07018441c4020200d1190901e000c4100042051280c4000301c1007080100e422602c2e242d445c110411050180001d00b45003224000c1c0c50412204210307803940341c2c468030071508050644 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 453805728 1250 453804478 453804487
    0x919051813060b0105040909030306060e0f0d0b04050f060f0601090b121512070b03010504051f0b0d0b04140708180a0318030605010f08060c25022214010515 69
    0x1916941080f10080350525203289810f8035003000a00301c3e07810a10540010307507580014418140c00080c079a10300c1004907102140802c03641d0004400c818181070061003140c3d42c0c00030404010081005a071850701c10307002e40e1140e103007800740c56840c100c0444410b80003030742a80000030b08035440811035070340d901505d0304800591358003407a445604c80c0f2000900d802071442c00454000d0001807000f10050892800c060741c2ea035151a0400043d5900500381450002043c00c00125100c890204041140e80f94040141c0328152030101300001c1c2248000e1035001030600f0341030301c4104a40c0029034410303841520740d0300d0142c4900074001036084d200c408408041e07201510b48400f02e0b002e0210002a810200e0398000302688a03512030003569408e900c0548d02181d4a00240424102881084d61143c000c8050301d040005a400a10510103d01440d000c00c000c180050030a545460521031210100100b42a0324003a145c40f1600c02820707a69150010003e020002003001d1620700c107000916858245900d042c07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 453806978 1250 453805728 453805733
    0x70506090f01030e070b03092a030303070c0606050a0b0301090e0a021c08070501110712050a020d0806120a051c08090c04020c1504031e0527060919051813 68
    0x7810481403906691062490000e6080306d000d00851252009902030148800229181031520b550f611440c0c2c8681c1c40388080e00c580b0748000068a038400954505108560701d0b50a05200411072070700202d40000901c01c0100d841d031004002181285c80d140820048084901c1d4000e0311180d000d84001c2d88400b044c42c0b511580c603a516540701e802402400c403d80340001c0f607a95682110101000042850001320300700090080c0d203001d031050312000d030038082d1a00068800094a580301d0412403c1400500300200d529034071401108502e03100100f040f1000c0405900703100d59111840304500740a0100a83c00450700c0d4843c1006c41e014040841c020705d0a0850001004080d401c01c8400780800d1140c0b28040078801c0c18030a881703020b58061303107619401242e41000c1c0c502039005c149503501807000801004172503803c8480c2e0801ea980c4d04450f114016503180000402d03900c6070b43c0f0380301e901004034221400324400e08842c0350219001168850a204001e65000a0021044403070000500c05900603002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 453808228 1250 453806978 453806981
    0x40506090601081b0d0c023325020705122b020c0d0c05090a06080c0f0604050402120610020105090d1209020d0f0b1b07110a05041805070506090f0103 66
    0x700138200f154201c00d0901c8500e644641c50304101c1c402a0030545038603180e2001ca030148040c40c1c0c018400031803200101d1004160366514440010521407040230140000c100440c441c00506041000b000141c1400c0440f0600031b6442160340a0b2921498820042c0c24402000250101c0c1c0010f400e02c07501030b400d03407400740c0e001078064400442c000d5001d0460505020f54550310321544083c2300e0744540e1000d5040105102071a0801044826210328083c0140101400068850b00d0031000310340c0010750100c400040b81541c0500d51100360058008500c0e001c0400c00c5c07206441c0320705c6068401508020950004900303031642621248620b400800361036020521804d192104038900103004100854654045098603501d00016201d44a060f1106401c01a06811054101da4400b0000000803220303060510140310305100100101c410282d0300615490f0b012010000300030051041020700c4149030043c01403480210200e072a80522200469203180010940b01c05407005080c005512242900540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 453809478 1250 453808228 453808231
    0x1060605130308130b130812070f0f020a080105010f0603180321140a0c031503120f21091e0309120311010e0c1c20060403060603060c0e04050609060108 67
    0xb00401c1c1180b60100c2c0c1c98170020010413100703840e00034503440d0b2403410806070300348165451a49201a030400c0742d5808100d00070300001032150000e45a1480034124800500d420602c1e0f8000403265003420000641012080f22010803039545403014000751170040c2002030070440b100001400301e030444840664200c4081c07149500c600300c1c2c02c1c000448850320441d03803103564001c0799a000455110740005414551500402210888201d1130b88545d0341190f80e2070128045420503041086181001d040d5081c1c400d0300780041f00e040316041d5102c0c10582da00c040016000b00d80c1c0c20f44403010343c20a654011010020b100681a405030340b109661810000503440207200f60f40143d003004140f4088212062080c0300305d03c000160b940040c2001c941e88018840c142064180203180b003a1041041c00c045200110080c00144503000015011004c0d1000a01d0380d000350307000981214074200000c01080003662203109040c40d5521000040c284072010017060392411900076400c00c0480000c2035841d401907070810f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 453810728 1250 453809478 453809497
    0xa1b08091e070b0f0c0709020711030609071505070218180721022b15060605030a09030c0c0605030108010f02070203032d120a180b0106080c04030f030f0201060605130308 75
    0x151a1203265a417007031504030150004101c4d2a400501030081088a02200407861419000390520385410620182c682020b0711681d960070181112000d86603100e00c1c21100c040394001e056128818440d47ca562035400100e507101d42102c224984501241d9000803a0001c0f101d10007400004210140042d5020b80d4070713030b4401c0f86c111b5540381c0c00e500c80d0603081d070304903175030801510301150048050308143c0c50842008480c0f0304110300d8044141702590b0702c041165403000c828030010a40c42013614040343d240c0400f4102402c5903010090216129501100031412188160000c0c4031a00c514a0090120f104074038000f58150720820119a946601d100e540032030b085890000f4030015014041d207605903015807960100c004000d401c118001d40c0074480c16504544414905081810b04c0d603503034103008010b006002c14408403e000401e039414040844000d582e10095000e62644c01d0324029056000d25100c800140d4202074010609030310a1003500e14891030468007613006440d503165940c0551104015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 453811978 1250 453810728 453810757
    0x60405061506070614190203070929030414060a0b09010504050a150b0405011d1c080415050304060b0d210201090c03050f12090f06030a1b08091e070b 66
    0x2084041132042c495451000c2103101e04800d2850409a1320304030300041040c0102041c418410300c42501e0f84900300c43c040d1445032192030131340741c40c900c41c2008909040c01c14078001c940020800003007025040c2d140032450040c60071903070b1301d17240c603040b03102901c1483e0601600700c4011001000185429008150000420400081c2c3d01e05012107200f050506600410090840040c08100380e50780308001c101c1000e91010304590410161000880860100c440140142c160404160500c551002260010020030002c18184846010301402c00d81048406840c00b501d881a6a8480d00f040400c4101c1241e002c101308502062014650b00100740610321107003151b5807408030100081502c081880918081d20062032100e910b650b006103049408006038000f11001c3c024140a03482d400000104035070102c410719204d5035900c00703920041800c0e03610120407120074110025910b07000040d4034020080402603034244100d1070101e4246061240f01001d030703035200890400c4144040030240c030103950036022 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 453813228 1250 453811978 453811987
    0x1210303020702120607110d03050609011415070b040b01081903031d030f1b030406120b0f0405160801050f090105120a0c06020102040602160308030403080a0b0604080f0d02060405061506 82
    0x2844d000c0c0880310306d4042900e0301001206080100001c118016251a00b88004e19240700407500c4c081062044d54107120142c01c06884c03030b548410702c11510140c007070aa6501e46020b1704000308044010307582548c0e6240311a002268950010801503001a0052302d45e4001e05d6a0707950880007004d45050442c040d4228000104041c2810303c0180528401c4030300b804d4807040c508446182e85040c040541d0000d030300404c130400a072500030122680411031000b0000b0070071110004101510314080701d00354020324101c20041c2c45402080175070425030095031240b40d10380e2544184241003041c0440e42d5440f03c42240100b104d07141c5404900c40816450043d22541c890f5503403590b292600031342101c0c0140c2d4010805025082d1304114602d12020000810f00b29a4179640300c00d0128440600080d040050f1800000c08042c4950440c4140c0c0e0b47c09130045946640d10580643c8400c119882032840303024080c456000d140c80010554000e070307001809080c0a0721030890300c00c0849818520690008000d02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 453814478 1250 453813228 453813259
    0x1c0c1d033018040606030501060801270c2105060f04050a0f020c03030a270b060406030203070810110301240201090602031003050f01050403020616090e040305040e01210303020702 79
    0x40107465070800307034000b00e01880c00050400c02a6800740e00001c08161030b110040084562084e501411034103045c08a904250022180c0c4150700f103070000c1003c1560900b460082016400b8100c4816201d664110107144205500c0c0300044d0390040d114a5485504442881c81e5443c141d40f0081d005000408006203130100314500c003069030410311940b115070300088204140c203000c6000f80300100101c40b03040303003c12408003c1056001481d54010f05070003181030020304545c407194044d802954004085403004c5544503d40e6585507400310003d201103042c030320508918401641900e0503076048294460488410340c420400130994840e100c0b04540d00e032400382006c601c0500c02180101c0501e00035001c2c150642c10200d140c26a060724010381c50303141c9010000841c0d800f00ba10741e00418065015965070b0744526003242d40840a810000068518000b80410182c214000300221b4006454084071a1b995030450a40d0b54025084998441841c0425a000078401c0d030040180510044c51801c1941c03411 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 453815728 1250 453814478 453814573
    0x28210203100e1203010e0f040f170406020d08060f010305060a0b03040f030e01050a170601020313080c0a05030a050307150f0c030b041b020703171c0c1d03 68
    0x149070765011562032402800040040c0400851000940d0415165515040030f203594008001e251501c0070424002140802102050821140d0f03004102640450401c00c2040055405440703000054400c5080559105011300d00052180100034030603045c010141c40158050100100403d52000d200200812450001409540280d005040d02107034000c05280241904844810044c1800001c1c009e01c1c10071588400d805059081024076030a4685400b00180d00d10b000ba0404204450030031311000c1070707612000605050841080b201c001540fa40c9800741500c90f02d4646000d002d07a0000c02c1291b0100b82208021007443c111300b8070024040014102c0c84040300c4580072140c00007500d0324040c503814507090203250a03500f005810200302c2482c2d0384000c0e540384c10070701c0000c012a01202d04a9520107030361099401200c0038078100121210b81082c1203006104244034040420700c9805626a41204c2c44c915035603030388002d00281810001003143d0206102c2402075440d80213034007940c40b6541c8140c1e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 453816978 1250 453815728 453815743
    0x1215060a03060509130f061104170a05060711030a030c09180f0b010305060f0108090309280b0f040504090c080f0106030605010e0f06011b02040908030628210203 71
    0x407a0741c0001c0d814100b4042214020340900460080c01a43c1030040205008200c0306e121294403090008100071804000c50301401580d1140c02e262083d00c0c41403980c0d80d00441c081c03a006211f4001d51301e9617520300c0016a1409250708a400e500d034402c0c0410b0703060078060b0b848403003112501d0402ca4034040e51802c88220704180080700d0404c15031255900042d51626004664901c002420144201d01d00580455803002c902c400e00b90402202202007544100248101c0d00710300c02c040c1604003080868600e5002141d0b1900384203886506c0c0c0d1100007078054440040c2c036500d16039003d0241c43c0925000030403000d00051101030300c5804580c500092922001c00420490f0b504100000c201d107455800e1041c00c45030164007114500c0c01350402c111b680302c420007445a1002007400c02035000c2c040042609410b03c3c01c0c5600940161900c100038084c005075801031842204110f070010201040d806000170a428088443e2004090080d014031610003074500c21b6000c100c01800640440314950002480c00d0314 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 453818228 1250 453816978 453816997
    0x6011107081f0c0903112404081e0a020303030a0504021f02061f21170f1c0e060f06011103030f04060608030a050d110408010f0507110111121506 64
    0x7100811090058040e0103036840d228003605001464070315613102c40d40700c4050710501c40e208550a47c03405a014203615203a000c00456440d1843c2c40b6a2280e800d04da41f01034003420040c00391903d5101d0b0030020000159184003a501502450640d214140100060720300580200e078451984c451552a260000c82700a000c1031180c8d008045505003070054010407415420a00c1c400050a501032000284c8540409120888040d1150340ea0f401c1d03086c81040701d405500210b003108030004804004c8800d203c00f5003807890301611180c0c000d41c00407186d201100c0c8984e500035555001200010b00d01445484c01c00e40c081d0040c1880d180c4858002c8005055900840c2d2080c0010242d8003404240121440b50001a103180c87c011440c00180200c05840c0c0e000f10342c43d0b044801d4440b0710031088a141001550b00818990000b8440350103140502ca0142404848a000041c40f00c1e52080c800e400500a445000c0040341c001803074580603810303001e11a40010705103e0f45502816040800c0d40341c0340b008008084 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 453819478 1250 453818228 453818263
    0xd0b07020106051f0507082209060603051806070c11030106121a070914031c020c0103110a120b06070f030903050601061812030e09070320040e0601110708 68
    0xf8240801c00009480700c0070803064401400501d1202c0e5a0007004540e4107a800c01e03140794450100c440460444141d10440c00d0548440701400250120f984e008003059070000d44080c041581c64203009916000164910a0680d00050214040f203004d408a8030b0450301903198070031041c0b103d401003800d5a01650159902002c1d084090040c00450242c06002095010002400c2d05104400514520140c0569200e034425060b10342c606580402514410468014800154048540380070391502c0c071000c0013a021a00f04071114100081d001c0803120300300e040361aa505003001c44498100207004056000d40c110004001e500042050803503080401880f03641d80b40c440341d0540c5400390134088184d01c64414098643e5520309000000100c010585007000f010070f0080c1248d04040340c00761016402305401012003418000151361541000e0b1511280c504048a400c1d43c3d0030b44000d40f882580314030181c2103d81400b282a540c41800c0201c400f1104a040f1002151201645414107111703904105064 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 453820728 1250 453819478 453819491
    0x90c07030201060915060807050d0504080315030a0206250503030a020a110601050306151801170c06130e041b0b030f090118080307090f0306020c070e040c03020f0d0b070201 76
    0x50342405202e01400c1801030a01c0300c0c40c41c01c644044054400c1c09038405007e0858001296a0700c59000d803070607151444400e20103030800b4103110040e9803040c0c440d80c503450320b8a40549114180041c2401c00a640540142e1810303c912017100248a00211a07600c202c10608810f000300743c0400145010b00000d00c801642c13903d030001c0c090142801d640c80e001141d000040100042e0b5400706149900020300c40303010004c40c0d01c07100069004103030a00c902101e0181440007013003018184034030005100d00381c41180c0a15000b0360800c0542e0140c01284401c060070b04105100d9403803400c0849402c14450000506c400c410380000800c2d00d20243c00444110070007108000412f1258071103160000c02c01e4000f0072003c0340180440030040f041e0080544050350000c045180c0c00c0c0300302d00042c014590000b0b1070160075128540031020b076010404500480c03240030b00c041444e04444640701d020700d612090849000d80b0f0742d801d10400d50001c01c600b9502241c00180f06011a0b2801c5006204007415400040c49 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 453821978 1250 453820728 453820733
    0xc03080d0b09040803040609020103020d1b09120b15010c050a0807030921060b0a1d0603070e01050918010b1c02040c03050c070816140a031b0309050f030c090c07 71
    0x440d0310000c03035244954802c10902004c10002000c598200f034015601140c00403144c0010380281c03003082d482e8203c0c2c41c5004800d0700c140308601f050280c06440e6544101e6a50b682d6100c02c00c0b0074405020150104030b40c0b402203600003543d4ad0416000801c107040070254540380b41ca409003049040c9030291004e90740020114201a40203003400301500301e580704c0000b40c2c4008030b0300000c205203059000f80035690306d0400407416520f02c4c1c0c0c0b0000811030310b8030074000b05460515001c0c1900094407410300034803a0305008030740ea10320300745028142d1b1005052440b0340e03525403501c403451004064002c80381b9580c1d1260305206803201d0310082c0d000181000e4201d031020f2075106010484000c450050201850303c41030242e801d8103101100c65003504900d1503612030034444811072a114030440010001000e0a20541d40400041882c2e0030b500c1c065219400100d04e00d00703210040070312048000b000221695418429440c22103000c0c1a005805000c032600d1100100200b035030030b141680c010030f01e003038042181c204 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 453823228 1250 453821978 453821981
    0x19050d21021b09070315090b03011a010e01080a06032013090809151b0f061f0302130f0c020708010c05040e012601050c04060e1f08060a030c03080d 65
    0x18400e0051005101032008600c00c03149011461090602c0f071900780c00801c20b1580b091300403681d10784240c03a44082050399038821300700800d800d11001e8002d50070b080703030520207003400d2000d82040d10b0185c403900751449461004403540040140304c68101c990300c03d4048089440c41c001b40c0010a420107000080309099000c01440030300c1e19500102103820304991400088450056800168043e200c1c1d07009288407014107a071a0150a03440c1c1c2c04895000e0010b9000a80010005031009400d420b54140d500e61012182d00c59080c000c140121001c0c2020800c014103103285955021005104006034039444a42240c05490207000050016400b000702807060507000e106440d5040002d007010351405160000c01850042c052003052510168210544030500040c141079040421502c000c01061502021442003a00300d8000c0c40e0000340d40b450542118100121862803e4001c545031158041d204d60741100d1403107006050580101c0344030000400910f07080d103a00050740c4604140e51300c90118105050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 453824478 1250 453823228 453823283
    0xd050906180604030f0e030f060a200703020d140c0109030c03080114030601050f041e150b0a1e11030706090b090102090d08030939010201051519050d 66
    0x261250030500034880026001061404400f401c0d00b00b06d86280040300010b0309110700006001c40f0b42c01034030104240c400d42c40d407000903000202d5048800a016a03d50264140580240100940d01200a80c01094040c020916120110720820783c900811860803609494444204030042000264200d0805420644240c05000141c540c81c41ca000341500181c2c1e1032006109560040082010111454803141c00040e484207405040d000b680760311486d003000500801c4d00030140d10719400310100311601004112004181580c0c3c54007468140582003089030ba184038404401d00c03403191040d0300800014406400124003802d000541e649890501c54031040b8000d040701400e9104100032000c6035925491400450303040455103840b555a80c16840c648014005186a14a4601804001c1c2180c41103604c1c0000303400340f150500300d210704005909840c030550b4080c103480c3c0e02850800650400003035007401000a9848001100c0d910400704005501c040000da80c4101c01c0c80c00d620100310f5450056 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 453825728 1250 453824478 453824521
    0x809061b0606120607020d12150b180f0603151f050c060f0702030a0c050f07090e190201120209060405040c0306080f0f060f070302071709130204030203061302060d050906 75
    0x509103880d1000009440d070b000d0091f00d60600c952008422161482d0b41d02c24400760242c003261949554440c502011741d90000f00220142ca0f0004c18009003600b00056001c103184400385c400790070354546040703c5270034045041850341c00400034035030400a89404021800d480c0519120981e0701c15155030308034249000148412203041806080c0402a9400801c9401d0303c2e09030300d00440b09421901d070503820b015404440514620030300101042020031940301d403054421100c101c8032007403000040d944584443d444007030302040644d41c0340140c15042e40c006002912000b0082403620340c441e00082e040707945107541c0c000080d07078425060242d148204a00d80c00075040c3c4004103008485802c0d15035480c00c009004c444000b078500c02050540b030098041e01d8515074048408400820301044200140d00000340c07061052a40b1035481d0500880f600c21501502e030041d0140a0503502c0c04000082240300810890f0001000c110905007031070340303118803402202e980011302203e0800544801c070090703840706e40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 453826978 1250 453825728 453825733
    0xc0d0906050423030c0d2d0816180603020c100212090601050604030f031b0807031d010513120218040501021c02030606030402010309020604171e01060302010c0809061b060612 77
    0x1849151100061321b00030810b41c81c40d006240d10b900390961000d48040400c41c0c407406040284181529400c001590321402c1040014041c0c42c904c5d010171140e42c0d00034542c22500c02030740d1406120700d5200307400a1840121040848400b044105644012a40703c3c0d0f4180c0700716011502402400c0d03506101c0a4018170044505d58100b50130341d202c5841c0b88408040040601c01001103015491124030040c0c0052a006031205440e09850304000c2c0c4000a2861b20b84084040c0c0c40724204950f00410a440040d1000308580c0d030030505100920110340700d090410780c0e10000b290840014070820001d0103114078460000982c4940012500111441c644001c003841e0038010700420820f603c1352400c0d01d500940910f40403c0498090000c160300e03100b1a0001c1c0310219102002d12483c02e0001074601050316210020719406442034882402c9400600000b400a5442034900300810500d00c041d101a050042120f0701c0c003140c081142024816244403480caa40001d01000300c031380f8024601c1d500e0500d00c40007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 453828228 1250 453826978 453826987
    0xf19020a050a03200d0605011511010509031c020d110a0806010201090b0f041a070c0c0f0305060705030a0605040617060601090506160f0b0108070e0109140c0d090605042303 76
    0x6601082e100b001000c00b50f500c1c4d03500034014240d0b0300c1054400090350061800c0280c1c0d40c41d0002e5007008018502500007003810070000c00c1c8032501c14480e080c80350010f68040d600349400c40200d1a0003041004809250740d40078414001110014424008445442705c102a40e42122003c0075011503002003809055900d082d4075400450098401540d02500001e0108203550312491301c7c2400c0512004c1185142441c0810400d05580158200001038002d42202c101e1581e40d9088003080e4249010080c450303042100400d1125005901960700320303128003008590075403a01c02180845d0400c2e440130300c008040e8940c0004042d01401078507040071081c030f4604140750400700801c9062207031088a02c0c44010610450051064242c84020350742d501848410503540d40e4207445544180500a0b410034890240001411020f18030900b00e10201c030a120400a950f50101000942c1085641c1c0c3c0d0180d48070030090300015601d1064600c03880c440c60301c03d8090205034061055207502a00c80c0700c02030f4001c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 453829478 1250 453828228 453828233
    0xc100b01080412050723070f080c0f1203031e010512071514030f1012030e0f120f0d0305010b040b0409180506071d06071a04050f19020a050a03 63
    0x1d0082e44550000c9810b1030181503000216454480c0b40405015040343d21207208044640300c0c0343e030046040325000c40f002d03e6192941002c41e00407a100d034004940c031820455503d410844222091024010400f8059441e41800d907419580704803a201d00403500781040648046000050703501415054409032403071101d13044c500c1c4d075400050049003902001800c06d44034152190003a10a4100c0e811290340c3c03030341051001c13840742c450140d606125200c082d4501007640c42d100f101408191341c166a44602810094062007138164001c8001034100d501d40c5098000c0351002c1140c41800e0341a1002402407426080c801000c4500c1a048041d038110104010820031035008103403415110260b9000801c800c9411490480703129284008149002d00b004001c0215000f00d480c1202200399002d40309801c00c5441040400d01c51100c0c002d0520750701001c810700718075503c1021a40030384140c0450350510141040039141c43c08489100c80503080040301a07045042c03c20700f14004000c01d590a4031a542140e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 453830728 1250 453829478 453829487
    0xa03030f09020f0103050c1309020c07050f0604031103240702070b030712020c0c1018090b0901060804020d081801020708010504080412050c130606081003022d090c0c100b01 76
    0x103e2503810141c0f510040f801c4409450708aa05548111404001c641d59a1080320084e411182824940d1f0103080300c0090b55003002e114803554090b00512403031400d401c0d40c2e0380c8009a803480c10714075014410703403103041e0308030503880c4815141d541802100b008500c4c1580b002417030103080c0d80051010ac070040c014005025042840070200b08000e080150729003404107190740c940342c007040840c0d60185007000c010314801d4100d210104854800c0c0e00103084661980004016a0f80c8030f80e00b00e401061035401004501c0c8646001c5401500c010905140750003252585403264000c450074060b05414845101d29540e010444403000b80044802405246040e0311100803d000d10f1081c0341c680700d902c0390442c080100a0001840b0880300a00c910080c07041c4002c841e0051840d4010100807840e254041051b021403415210110b950040c0300c002c0000d482640c00d14038911916041c1d81010301703100b02c1000d980e12070008600c6075070b404064540b81e51400040d2403a0035502c81c8840303402ca1074000c0ca8211039900 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 453831978 1250 453830728 453830749
    0xb10020d0f02010e060c03070909180f0807170901261b1308030d1d0d0e0109030b0a0b0312030f01030f0807140a151e11040b03090a03030f0902 63
    0x21424407a2025880280a0707024066500e840280c501501040010352410980610f026021640d619155544c03501a518211500343d8503410268011103d4040014100280122080d1082072403600f02219035444126400403c0c1d504402c80c02c02240c40d211659008590005c0880729440d00000114001c001504481001c0c2440e0051003640c0a11a811900c600c02c8400c018900329180b0103065860360365580320b4100714000c004981c1440c0403507502c1c40c0b008081c3c42c3c442204030058121190170715070940710034260407001414491010703070000c0414600000c2e20311840f404400031130324015100810d82414040418400400b00600034010f58082e00c4010301e0641c2d034840c1482019003d1070900d5400d500960074010001201003001000c0041c011074900c07a211310504915079560341c091002020354100000c1042070b100021520080c00290350005d030b0064a031b41c003015207030607101c00c1803180e15801203e01c00362030391009200204155040c800c804051800d508200500b240550005400109 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 453833228 1250 453831978 453832003
    0x10020f070818190509010b0a052212050606090711030304030509030a20150c0c060913050f0f09010203070806090403030e07080c030715090b0f0408031c0b1002 70
    0x50110382106202c9108004965544008100b02c1e07480110030070007034046215004043c0900162400003500728111400e885441c11192103c608049801d502c4082c14258100b00541a03900410009520b035500080780b103182e0300aa026200521380752040c00a81c190240000c8200300a50402124880d00130058a8010b5410f2034810307550224900040e10703210702824060024000125100f00441c03008188461745203042d10000f105010907020014580180c0c20903500c160403812008850b0f103000c0c7e006082e082001008005801d20000034481102c508440d08488000b08100384403018003050ba01c0d80e409603820f0025455484e081d80c0080080d100549a01c2c040d680c039001160825009422051202568204803036a0ac0d580c2e01240ba50744a00b03800c480c0c0640110b03140441c03040781d502c0121840310401d45035110312524040d110441680a01000800214107000108510b00e092000b0880700e000100c081c0c00350294011715a0031101a84005445035101080000c6202d40109140a01d4031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 453834478 1250 453833228 453833243
    0x3030e0c031c0201090b012c100909030c060c08010807121703040201031d0304170705090c03042907030b0907090302091f030609110109060516030e1f0210020f07 71
    0x1441000c2c01d90240a209400410f0126200000700b810b109005800c082e01613a486544541c0641002110716108152003c070703442d0307402d8841809500010f4010010451191921441a640b00d03142c140403503100d0b20b9500d000a155500412001e42d0801152001e420b03d0a90540314440b00ea9482c4c0861800d00103d40f40c062001c0700040641e8005d910a07240100d045500003000c201301c503120394680d03206002d0034111000402150340d410078001000002e60300090f003410315a403a219109401500000c000710b41600c9808603203210403450403512844002d0b443d443d4866030501180180550341c0c601d01d03480c000d07551a8100b1807020f502c1004441140d8060314029095181c240c86894418000c40723004400d480c20340300000030007d9a500c00d00b005400340096069811808004480c0e0a406105540002c1c0040c000e2440303088040502c480278a10a01300b40c5214800800800c5c0e4928030005290350125662851940c500e0f01400142c8800000e160214501011800030700664002c040000c1c4c00f44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 453835728 1250 453834478 453834523
    0x90c1a19031b020705010f050408070b181207030b01150806040504060b0d0b0402040b1008150a03020a0611010e16031103030f03100816050919090c0b0703030e0c03 72
    0x340e0090707200c1051001d40e865821859102e4907006540c8080c1032040f00d0002d01000c80e12511035200e1026101600d0301c280142c40d080c0c0c64140c2100f0141c021b000070030040c9000041c0e0b10000d81d00e118818030441c1c04c0a000c3c103031191450510260706a0143d1110342041030030501d141a441d8007990301c940c414011240010ba13070316242071800c01003240c01e042d69041184480d088086c040d081d50480e2085100315814840d0801c81014890f000e90f4800350100801d0000001c04c02d001d110344680c0810420151610410a42e00e400107806400030f07030f00a1340401c00450003c803016038280103070802c101d00d402c01040102e052403c09001d54401c0d03c000392028400f1440310142c0d5900f80125070418a4451040d80c0364204030f03d00e0110300d43c40d481100c070780e03200307045440300e280c0043e400080071154000c180240d540d45850540b8102d510000001080c950b48880f030000084e87d00800002500d840003035141c44080742d150103001c80c0d4201d5501d60346035021a290b94616500000c290040075003485003000344 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 453836978 1250 453835728 453835777
    0x30b01060801081b0918010507110105130302060c0d14040c060f09030506060f221e05010302060d020c100603060221160c0c0e0c0a080109090b2413090c1a 68
    0x1031480c90b07104a50038074040c4a00107501011500e42b0054010080120b5181d030011024034200b10300c030050141e082100014500f1244101070310344648078000101c0d0a80f110b1107554000708084034211200204242c082c0705c0c4540c000c06840e805070040c144144000d007107440d002e0307440c80010500c0c0d110f0001c1e179002c4000d0b038545031402081a02500c0c03c1000100329001c01c140500b00c0c5110b412480455a83c02030f0b41c401276402034074101c0b50050222451314070b480f0740000103540712040005084c840d81580031341c49c0b007252080000650241d900180c0301c3c08503400e100450a04517080c8000300d84601c060000340101c1180c6c810001c079450811070451881ea01d45849107440c5a0b2200c2c030b4805001007001100380b00c10004000084150340d903071005070380b11a84c07031003100d0000802410a8480400148000a411a045000c000b0952444da42c010007171380001e807400c08404031900c42d142c0701c0e051a810001c915103c80050801d60607041014002e00c51290480e002d1048a448049039a90b40a5103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 453838228 1250 453836978 453837001
    0x31d130c110a060603210f0807050c0303070f120e1002090319110405160c17040b0f07060606090e13110a08012a0903020409050115030b01060801081b09 67
    0x4109201d6416a0b00a041500b000030043c907951200781c5003200032600d201155174200b034030306107041000c0d20f0b107005001c1100c0d0202c0d4103d00042c516424442d04001c0c00d0716085040005d54480c0b2400e50700c072030784541c1d064001000080c40c0d200083d05a801c0030074042c0c50010100d901002c54500c205c00503282d1030700000092420715007240c4407116088850300d0205109110280c0700c2402c40c20f4609000c19101c1c2420103445108945440001501d0041c05c14005004040f0b000c0c0303000d0035455410b0400d915070403000e0490344000c0c2c10703500041c00003442000308485402500020821424050102460310340259140000240004900c80b034207620700342040321443c0c5015031200b01a154124142e12100023900038004d22940b607003140c6000540c1480251000d80812640260769a5140032900c3c40d17007400064051580304841c2e95407610340070710244912140003001580030340d06080c91940740100103007078070300181c0041c20300f50000000e6485030070a40150405140f42034030040c8042d41ca1005404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 453839478 1250 453838228 453838247
    0x30e010e0318210a0311280f1203020c07120308010618090c08061c12030c0908030706200304171612030f0b0a0f031202031e0304031d130c 61
    0x401502c0d58100040f0382c10000701a9039541c070a440e840c1c121a81410002e039a41e000b031800215414440700070071f03030701c070b040c500c02094280c442c180c6c0c01d22040c101e6450180340907036000c030500001e40c0071480980101041101c0d4000744248910050b00010a46000709468014043c1e6000d0040741c602c5242c8800603142004024400c002e0100010b000305a40102003860591300d240c4114a054151010181240d0410a030340350304c060651801d00a6a000303801030402411544203000b690100054000c01c00d000034108144103a0000440720072407484840760952011003441d140d00180300700b000003480304140806010380c900010b5190003003040c461038002c80e406401801400d0842400b824107806412000f02201070440c144034000c49e0106020f07040000e0f210f0402000d80140040012540030500307000f081d075162041c1c0f860412125500b54485518103031002c01c0c05d030000f01304002c0c107074042c2c10314440c220300641e000854000100010051a180b00b10540038581e0303402d407440003900a08049 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 453840728 1250 453839478 453839509
    0x5010e24040501080619090b0303040e0412020d0219080708041d0906010504090b0c220f06020c0a1401032c010506040609050601080f07140c010c030e010e0318 70
    0xd40400652914400e01908039208041c00700d0b02e10404100c26207050700241c000c140241c900c089071a40b800008502401c400380085415020030000801e80c0b00040100301c1c4200d0041075a10704420100750002d00d4601070810780707021500001c403507640741e200d548165080030340c0118199807030f0b0a40707041882a5218582c0312035128903920406d01201c1da00d0344201e910074031b0139600b070b1401c07607907203c00340004e48085041c010101107521002444074000980a01440070401420140752001c88425504041554003c101c008400c030100f088440d0b8100035040034218103441001c2c94901e003640c086001600c1d6071040303040c107031501c03600c600300c041c082d10041c020850000d101003208201c018441c020704045d11a10b020300c3c00c0180109100549000f0070340110010303901c2800c1999071042002d07081350042c0c00701c3d0402c22801e50541544040b4000b82100680f6100009644100d04501404a600019440d1000e134104003005c008103002000b640e0004803900104456008450002411460504d000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 453841978 1250 453840728 453840769
    0x91401052503090602010209030309040e191505250809010b0307060908060a0b15250308060306250509040609060605030402031207050705131d01150b0301030c05010e 73
    0x30201d03000d4070490300c40d6200e40681c41c1d0200203900c54104034240e116024003140c0580c82004208001e040aa1003010841014400e035601c4e035100c55600c150380404440b0a0321006050304015050384003d12466400038400f01030728800902500180c080816050a400b050040527000110144020b402a81d202c540040984003603030303299000034201003458022407555110b0000001c0f4044880c1c41044801d04004000500c3c60050791490803255000d009181940c13103e0809450a000c13103100d8000d0300d18440c2e04d82d80c140740303060340a140c42c103c001403c2d0340321110844a481d078011721100f54480000b000d854074641d514040c0f4040b8001e44501d138000d0803060701e40741002540a500c50050750203503100310162091180300c800602164000d50001a00c075401000c02001113141c218110034040a9030f201c08a56602034801018003a03241c50b5030720860741d4560382d03071100d0010b9080d500000b90110511321421541140c0301c00c1031400540c040c0c2c605100d4a0351506029071344e440d9200745040c042191 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 453843228 1250 453841978 453842017
    0x30d020a1a04021f020c092d150d0218040308160c02220608030c07090b0a08070b0310091b02010b0d08070204050403020c03060108010209010f0905011e031b110d05070309140105 78
    0xb00040c1d070740003090072070002340904840d48038114072030000501504203c00340306c003a05010401c201c0411003c3e9402c03a885014841070311000d0358450b81581c481c9000f6110b44109107401054a40c030141038054aa040000041502c001a075540d10130b50b0111030026213011890200c0701900c4010031054100d2119407001040000c25102c0000380c80e02a9104004240061010a4280a48440c09000b501800d03002403009200c00c1c00c40c100a90b0348401c144280e052010b42c2d400402084414400d403c2c40c0c41d21300800c0018000390240283c0c1c40d0084c0a4401c030300c50703805135201e8000c0350040100083c411503c0701d0108051510800c290040d16a00506941c1d165075100400340c002c3d407141007a0340c00b0070135580c0381044c8140524460421a08183c441c444000c0d078410f9841c0176203052000210034143d807030095040c80074841d0765041030a445a1201c0802c81c0c00d20f131240740341803160311540c010450704014007000640d000046200312244420b04001a0205000513120380c092400c19100d4001e2250 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 453844478 1250 453843228 453843241
    0x100e0102150c0d0e101b0503010e1009060611160f030204110702040c09060f021903030b030115150905040207050d1b05032818060e0102010b030d020a1a04021f020c09 73
    0x507296805c100c41c68080000e914540010a50221043c00c5440419428401005003000c5580d195034411207400108850310f484580c68000c071241074004c54000795401c1064011320b034040002c440c0c401002524004041c2c50310801d10100724860000a0290380c0702c810f4100e801c80c011040d030700002d034010410300a03089006001401c5140521070800000d080075100c0203001c1c00890f0000d95548a120800702c0c46045441c00e901800c4191407041d0151368906a03012414103100c18200a05255030300b20610303c004c82070041c0004a642c200d1442203104006031800608002050b10b4645200c0c00d04000c11f10070150b8410050805510203402d034003000544070310f100e5016189582c907201c84008040b0345280c0c544110340c801076201d20303642080301408007405118001e210000c0f200c00144004100310040070042401c041c5da80c1100000341e03005165800c2000061041000c900d1000c070000d00040c42c003900014642c21a80b501c0340c04d800d1079140c09250440c4203011400c181d01019203081003a06101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 453845728 1250 453844478 453844483
    0x50607172b05091e1903031a060f0703080c04090509010906110a080411120304240f0903021509060a08010503010c0507030e0f0a23100e0102150c0d0e 66
    0x248215001006a0200c0303001c5405074070a581c020b01c03c0d00d000300828445802c2c0039840c1000d18030044118881d0306220007840a00050785010244640d13008900520039031030104090000f201c60b00c2c4a01014490020250518000d9171561605441d11014070385403001c01c0700c594030854001c4c03103071581410200400c1c560305420108040b40320b020104040920b030380c90b41c1c1c0240249020140024404000308011500c3c3c00300204410500402580021100c940d010385541e101e98090410360382c0d640c2c0360f00404841c1c5a10f000c0e5510160508481103042a10300030f00b0b030080c0740002486400041c00d44590b01242405807101e11001034107290f82c81440c004050000038091140d640b1035802c1804104046215105079400f050b4191038000d110f214440c1004002d00110b00300c0c6800040c440740004004450302d595907408110b1300d940c14079403610401800046200208550300f4040b440303080240317503680001c05146042040c1e441d600191550407030000c00c0c0c4901d00244010170b00b82000004d801401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 453846978 1250 453845728 453845767
    0x1e0b0105041416031b031406010e0609040c021c02071706010501080f071b0602031506041409040206120f01031103060c0f070501090203030a09060806090705030f131b05010f020f030405060717 84
    0x6444a0950f180c1c0d23840c00455400302d004284035003016050041c11000d0909030032041c8d6440190040d183d00320800c03188120280c9007402e41500590005800f04a0511140c0c0b035140140b0000c0d010b814a0360500700007030a181300282c003000c8039410f03000015080e10f21528910702ca8841c2000c03081d10725241d901780007010f03400554000d900901951602d0070f851804400301c804540c2d903500c08480918900c2e0800c164400300502c183d80098003048070350b6031448100d04c0584503da20403c5060194110300b40007940d8080800702e64000e40c401c2c020300925031918015240400c0180081c0e03680c038080d52070094090100b5500c0290144004181000c080f5008004001030f100140e980008c182e0343c400030481e5000051b81d410002c901c042001c1100d0842c0003d40c030364000c100241c41c0b0002900b6aa42e80b1060a07159080c2d42c0400c0e0621041c40380390381c402ca15a008a002e40b0041074008084c141c6207032a8899841742c00d124000c0002c800c3c0070403002caa8403441146a040860b038944400c005c514520200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 453848228 1250 453846978 453847001
    0x12c060307090312020a03120f02070c08330402040504050f0706030204060f020a0c06030504081c06050103050a02070b0c1309021803010c020712080f071e0b0105041416031b03 77
    0x2e2001c12044d03c52000a8010f0304540603552241c2c01c41010078510003d086041c00c0541f82602081818040742803280540700400d0760708000d00c5080b10154610010f035252049220820108914166445401c220501e80054041b1000203483c2c40714501a403900041411490203406140f500141080d0140d01902c00c40300740391100c890490140c102241c8900000b00300901c003103144c1400340301d554480c1c5e02c20741d4080d01c01c1d400d462910030040c50030000e075031094241c0250b86480b20420f120950349401083c0e000b1141e14801c2d420014075a41f44014031000800c07115601101098810034240003c01400003401186011035840601c1204d044983e500c404804c1d01075800c04c064000781502c006540006c0b6104000030710360030042507545440d5030707000f00004115468144910004a6200d100a43c11140b1855880104d10510300d04402d4030b48050303200c1880b0301d15180414050428514060ba8003404109008024040d0030000f034005008016034805120341c070b00307031540360b450305588070a40301c10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 453849478 1250 453848228 453848243
    0x609090f0308010506070206040b220b0307140301230f280b0f0a0302130302041b030e0712080f12040b010305100b0f100e090703020d05090309012c0603070903 70
    0xb130300d640c180115481121030003504440104000c1120f81d180b00003800501001102010320683c2007079082101200e10f03001900c2d07000000050010080c0c00044086410b07106c03100103403c40d07142c40d509807140003103550389044054130f09000c4541a6200c08401110b400d00401840350f041c0c01020840da0000d180c1d1042e204c3c40784c00880401c84030460b10035905010381c002c0740f06240c241810002c030042e4201d007041d21020407035084080016035407030061003802014003405503585141454010b059902c0081030800301d4100d440c05100302c91030050514105900090025590001e00a04044a200c4c01011170303062400c42d024402001a4410b00e54102c038050011100030800344614003003241c60950103142d0041c1e00078844590380c101a20301c3c034059a80d0707091400e40d200000000c030344030002c00c4581c45e0000f40d00040c089100c020620a85070890040d0f00110304021000c2d0002c0e001ca0741c0034180380b0160041a02d0518402801c800860032800c01402c02d50300c9061091001e0003440303e0340421100b00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 453850728 1250 453849478 453849481
    0x2a0b030a1a0405040533010b0d0b0a051c0c15020f0f03130e06041d030a0207090506060306040b0604030512030a0c020c01090509102304290609040609090f0308 70
    0x3842d00d401000d02a94001014040d0b000980702d01034900044010796a0f500030900c5c10b4110040c188864190003000b51210480e078481c080214402215515000c41d03216180c074440034003880c0c5030b0200400844040045901100c151810160b031100480c1d4011074031540b080c0d211218880d4041514007541c041039084441c20440703e640b00d0703100d000344858200d46480c000c80c1002541c3c08044002d80010740504001100388180c400715042e104481240c41140d0320002c1d1404620754100001c000800b0303080400c0166003408c10000d000c510020b402c0300e10941d2680c00185042d0342d0441150010b40d48081158241014000703018903e4000310f96008125142c00d580e07810203030002c5110404218165141d041840c107200c2000101a0090314001619a03d0394021842d60410302d410042e041000313601a04042c8403204100550300c07000c1d64003490030784d040c02541d40784a0424020210990885c5d0103034039100940c0200d070060000380d201151042c2090342400030700403035200580c007a41c0a9604c140d107a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 453851978 1250 453850728 453850781
    0x130801020d1b09030809040c0e0d06090c0512070b031f030506010f0506030103120c03030608070602251203030c0e040614030c120c0105031302150c0d020a2a0b030a 72
    0x1035a030704d20000d040741c0c1d800c201c070b001c99142c584c0c412034840000b0304201d160015941c01141c440080c0c15000c0301e04941c4d4190b45014800e060b4560300c02884204d4070b00d5405120a800030703403502d6051007052401c0d4408008203540c0c090b8042646454013015003a55219580c03801d2203551810b00303104030640b24050300c00200d9070303050040403207040e03c0d041010310040c00c511707840898002c80101400e074101075403104040b440c8c0505224005c010856035005004a14142a072101d0114002d400b400b0881c02c002c0042140c03c4002580c4e04d405a0141000640e880c108802500c508140b00d01c8980c1c05440e00b500030a0b001d02040b800c0c1c0969400760b04564403031942c4411300c00310580440010400d940005400f5001e503101d000110323400132000024030f10710340c0350380e001c00d94000e182d0100e647c0030701c40410070b000e801108010904410381c1c544014407007451240c03943c102c4100f10050a048110201038040300e045000c1c4082070060951401d6a1f80d0391a02c04543e8000b0b11103040515145811114034011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 453853228 1250 453851978 453851987
    0x120b0d0803070f090905090106210308040312020d0213080d080108030301120c0909050d2309060307181502161a03090a080309060f010e0f010605130801020d1b 70
    0x5440c0c0d000040501c0c648614105440380d91240c4142020051505004500c5407154051306002d44a84400851003c0c01c00c2062412080110b0490034546449184000401c3d4448403054015405041451002c00801308040280c0300f1400300c3c40a4500000784510b824411411880885407218107841d43e255041404441c144003c0c031070100241c0c001d000501004070700d05001e941182c13007182c115107800d640f04140d106a401046081d00d003500f00d5442400700d160842c403030a9042d015140450001e0036020001c151600400d4002030103640c0201c001280c85004628182c5002126503040e2141750b0395032000b10004a01005403401406800c0c03c2c0b501411100f080d0405403555840400e445981840c4032503a550001020b00615208440c900c0c008150380c1d50046000304201c5010301400d02d0b001c11160000c1c40d06a00503002c0c5000d0100300034850b41d00c072103041d040d00d60a14001d6542e06c21100350540580054016008552001451610103030b8aa4801401e1076002c1c45040942741d005002601c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 453854478 1250 453853228 453853249
    0x8030705101805070905011e060504180605120a0203011b0e100233010f050306060d02040605060d020c07080a0507121703040b0402280e0c0408010507120b 68
    0x20305960108003a44802a5140c022100c5014070607018500e168040c0c9400e0719150496008010159840f001417005040d00c0c4c42c01c0801e01503003600145114903007600100288a1841040e01c8c0390038044003410b01c950b454004000802d4014044e40030b682c01c2060945c2c441c820705c00120310a40c80d102d041d4805500701d40900524a455480701d800700b440741414801202c0084110400311b000c0d40d8102030080c40001283c3c161800c02094240f558007a05484611811043c0c0040020100d0304404006a03600090b040703038001c0d07054484541c0d20441e88041000b070b01c0030381c101c2c0340d0242011800641c0d000c0c0507405070207480340c080d00300ca08540d81c841d070103600c0d898103c0d00a0a581c2000000b480a07949100414141d03500c594a04c02e84506500e400705103035002030b40d0440b160403088040c0001d51804400c07560450703032000302031080311003807140618140320684110880c540a04000811582942c400daa00030071002000344003616010030001d02c2c0300d94002c5a84c0c0b40c24074001040718a424641e040c0d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 453855728 1250 453854478 453854483
    0xb0907090b071703010b030a18080f0717040b09090f04050606100e09040305070201020138040603050102070c0f060c080d110705010903111b06030c030910090302070f080307 76
    0x42203460070528020780552000c102900d001249048181094150000460090000d890b01685a040c90b035183c07010340b8940300c00340c0901050078030408041020001218440c09402030a29514a5649008282c1d80741c1d100c6409084607000c90300103081060180203200c1880203c80d2001c280d42c52802c48181540d050b103001e0320765401040014418144010862644006820000210400680041d06460342120103c00050000c9003030b004550302409041105050103185845074490410700d1000c2c201e80c900001507003d9000384201c601d072190382c00280a1600700d002507580d1281c5d41414449040c2510501640343d180c40f40019500b40b08000c41c134100c6900290031880d1100c50f040d200003030329040e400c45030348078400c1290b200000c07400d2056002c102d11a0f0ae48018141c8041c11007070a0807000d007600300800c900028001c0e010340d1900c003103940c800200244292030ba11140d254910340742000c04100100ca143c031841209043d0001440c81c03c071800251034401a544540502c0d4403409100c200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 453856978 1250 453855728 453855737
    0x32603091005040804080a08070309080609210f03040b0609010609060503162d0212180d0c050d050303160c050c011103190314060103020408060f0c0708040305010507030b0907 77
    0x141c0256407640e8200342d801c2800345600700e007030a07114034242c1e04100202c0f40c111010000000c2036170405410805410007801c869000d070a0071301c3e10759402503c4d5000b4840c00c1041103020f00326015020400e80030386c0c0c244500101155280c0c078141c94091100c420030345205105a502d64000540980304c0d40510090344c449548035415621210155450800550784c50424400c840781903188a454038030346015038601058170480d80e0510742c10b0190401c0c0741c0305590015400200031103c0c17810b0503880c4080d0b1443d13054400403500e500d54141210f41d540b460300700b036a1002d0303000c07840c00910200202550150a11640c169002583c000342640da1040510008205411a244214040d802840c41800d00040340003681d00d450301010003151401d8804480c2800719aa035620050603424000415a0200e402c1c2021460141002c901395960b2400030b05a00f81220307110000b840602d181d03007e81c3da4095006405a403500d44034908180a8142100c01c500000d240140202803842c0001e401d90044013035844 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 453858228 1250 453856978 453856993
    0x3090c03061605070611070f0c1a040501050f040801061d1005010c11010e12010e07120b0c0a050c032115060f0a021501060c0b281d0703260309 63
    0xc054a45800988090310041c0d0348440c1400c506c000d4000800d034803407049420013250750b0741d031814079a0701d05c0c1c50b040000300410016640d000800345204440a592003400c000740c6880680c81105140c1c404c582240801c2e50a003440082c0c280f0031341c0300100342c40c8040400207000e80e45900229000d0030240c0f0406001545024260010a034000b80d0164100c00601d025808030880c400800d18402c0d4542d15021540c4d0b4662040c1440e410910400b000b80240c0007003405548429180c02200800c06030520710b9840c80000c9680704140a2400c0700c0842d1a14402c4d42d40b9030f082010000800c001d00c000404841201d000000c0c40761102c100c8030302c044c200060445007049080c0d8940c10480e01703da0a414154800c4103540c0c0408811840c407a80240301556840710f03c11028134045c034442c1c00241600304088640c100041005003d40740440808650240018140144080380000b20701c0076101004940160b480220a0000d0001060101e48003441c1c45010703c0c48940e8189100d01c0111104880781e0032051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 453859478 1250 453858228 453858271
    0xd050703023a0e101d041b0503060109030b01150305130c230a0f1a070507030b1e100801110406080a02070c0b0f0a02010b0607030c1407170303090c0306 67
    0x8020000d0010b0310300d000080b00c008074012640249403840020041352030042c107403245241382101800058021354041c842c001f803803070140d41c0170a00d003410141444004800a100742e40700714011300007150000245d4030b15507914417400c11000b4188142c04002070a01e000541285540d41c0c07404121980580000f10f050315210003400446c11144034401482c8042d0504407040c3d96480c4400090310b01000c01c1c0080500e48211414403181c50036101c2000f400c107011a0f40400d0f0302080800480c1d400200b984001d17601c61651010b820300280d68841610742139010b0140c40100880400f0684d51000c008200c40703030340c141038002c060081c1d1243c180041e015000203090f2401d5a00601261481065284c4000e500c40c03800c080160802c40244203e0744010540c03140307290b42402407a941000554103145480d40c20340380102160580c5101400d92042c24503800868001000200020044550301200c1c00703000d0040c0c20745a43c01901d00404910071036010185520f400b00303503103022740781680b100e030311121840 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 453860728 1250 453859478 453859573
    0x3060e070e090a02090d060f0c0f170a021204050606100519050904020c010e0d0f03050609011710020c070303080f01060512180102070f0204050a0902060a200d05070302 74
    0x42402c400b06409103c00172440c0c59408000e030390399125400108260b0f003c02c20086c11920b42080400402c15102c05c0d5422184d004149007202100742c0c440c1c21803a60300c40184002070701c10b58443c0203614812500304810b010300481c04500030708086484c907180c640b0003c0221400d014900300e0b86900d040c0080c0700c40116000f90f004041d400c80241015041069884405007115243e41d16501590040b4050320002c0303502035100541c1c2000c9041c10080e609200700071840c2d0306c005000e103401d24040e03114900880c610400006600e4140320209540d03c1580d0a005031b10340681d88004c5000c6424240880d000f041a5580113050b54500d5a4040c01c140715030000c410700c0c19024000d24881c5441550070300c20810280010207101340600c440c2000040d0520500045540003440078440030714220390724006a0b920f80c216010303240316181458034040c0b05034402c014000300c0d440510840c840c940040550381c1d0004040d0111601940950b00300440311100e03240001003400744580b41240a060402c86c90080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 453861978 1250 453860728 453860731
    0xa0b0904150e1e0a0905030f0d1503050f0f0307020f0f12070603020414030d020a061509020403301e051b060a06060e03120d0e0304031203060e070e09 66
    0x8810201c0596a4401e5108000c02a07034511081c200640302c100c1d84840c501c00d0680c000c041200e04200300442c540728252603000301c079003070b00362458000340d0b2400c041e065400401c030301a021083e101c071b6555a0310b8001c2d915221001030070341c80c0c000e500303488110590120541d040c10750082c1000d180e40c00d080042000c0340220202186e40700165003800c06d6134600400581010740300d40d450050341d640c14400400340c0c1c0861031808a01c80d60008001c400c0b019400311b044e50701d0f40e078011804901c0504000d549000c400c5d0542009802c40c0c80401e00200340000800303200d40703400304e054001a0342c60320700f00d07042c03481c000c1d015042011403070710064030614102d04501d03040150141c0c601203003080003a40003c01032282d1018040e50660004d42070000032580c2d0302c5014000c003100d040c034400c241c88000110343c0f05e04121440d41c80c602400b080d00080c01400380c00c1000d115200c642600c1d0b8491702e03881c1807004268104d46600010349420408104c564030907070158040c400300c1e1900200601c5050421410010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 453863228 1250 453861978 453862001
    0x11802060717070803040602090102060c0a020a171c05010e18030414030a06060e06010e0a060e010804050f0d020a031116050d060b15040501020f06010f0303110f0a080301140a0b0904 80
    0xb4100849008903160704050360240d44030725009a81d6800300d40c00203250910144c03103080600002c00040c4001e0b500000c102e811694032207429102c00d144c0c0b50a9403078601070040c0700008101c100d01d41e14000e2070b80f036004605883c0d100240a000703840e40340660003201100031400d2036540c400c1105001c840c998801c145e215a800400300d418910440d82c9035000e0310110b40c40306c241590000180541c40d0703003000d80c0ca06100015210301c074a86140410040915108080382414425640f01007818088144031103403008008404072a11101e1410000b540c40d070300c0714402e0b4009a8032500183c04090041030340a5a4403c0c000c490503690f04003002c21000e40030786030089403640d58230741c0900d180b91a078990320f80d41e44c01040710302d81d01d07945000c0001e8140b28941d5902d000c103400c0100144018a014001c12090f01d130149440b40c4104400f84000b403800e1545034101443d446a19007080401002c2c20040d81a50500c00e2140501c2c18584240008056107020f81e00440f0414080000d0314100f13988641d24410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 453864478 1250 453863228 453863273
    0xb0d06031a0f130209130809030105040311070b0f032707080c040c05040509040b06130e060a0c08040506010b0f07080f0a080f010807060f11060a0b030118020607 71
    0x580c0d90341c03030308aaa840210040400340703420040211a0039824600c90b88403035601000040103085500091419400a1041010030b6030228000140034058003a2039880601500812076070070203043c050158150b980f81e0740d07207034440c40001288462510081d40c1441e0f0146c00c98500311340b00c441c0c141c0007100210b9202c241d166041c280341f141809023040014000d0503140041c00c004010f08060005840d041e140ca0001d00000700001c021340d486004002e6481a080340d0f20f20216118800020440041903094114960174138007860f0107000b010941c01c0c02191502020003044246a4007503072110000c0720094400d4104400401c4010b803644028545002800c000790311b00300203030b581c500c403e4100443c009031508001c2102d0800341d8020200582080003454504155850441c81654540c01d601440c2c1c108518031315a4005a801400c1140082030544103440503840d215400c1701c010021004010b10941c207100301108550030301405000095006409189844c00c1500c0d040200a10090310304041e5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 453865728 1250 453864478 453864491
    0x2e090f0902100905010e0612010e061801090506030c0d0302191b090605130b151c0504081201090e031e09100809010f0612020d02040914030a1202130b0d 67
    0x5a07101801002d04405a032540c0700c0c030700e050800041c402c4d04110781e06030040000704900ca203004041d840d40750454900d100c41d40c0050356103001085a50240a64a140048000001256580841e08000d102d0310084c2e01b21aa10801d100c03c100d208451002e010f40540c00c0002c0442028821540d070903030041c0258401c06452406000c07103c1d1210345980040c03469a80c41409002a24088401000301a40d00d50b0034016900c148000510080f8075241c950028007000504c01c1071107402011001c110340040e24104030034a001c0c1005c0c0500d521240004501c03081840c00800c001d010741c4617002080c0f452100950500f081940408101441500d40c000800010b0050001d5940d40d060b00b0a60189141d641041c50b081c000b0000e802d48030030581d00100ca500707001d030500410f07443d01008280d040c0c045914510380344890000c07500404c840140909088000c40e0b41c1002e0450000003800c11780d40650321046803201041c240302c02ca0140211003440004100300130046081c0000180660848035080061070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 453866978 1250 453865728 453865733
    0xc1101020c090703150b0f0a0807090f0906060f030e0613020a0e01080f1912030b0f03070b1c06050604120c08010c0c290a020a03020c0102122e090f09 66
    0x110422111040003e445c0d25036a02d811003c085000c00030084d11001c5420302904a007210024091150903004003c074510004851600c95002440146a04007000c2c0c1c0240c2c88002c4580542030900036000403d02900081d18054802e01c01c0350700400d400d001409080d1070b2042144200d80c0503002c180c0e40031400f003001140440c0040001802030041200604410489405650400303900c901410714001d1140700c1f85002c0b4808070140d1820664900c2c00158408003400050501103651381111341501c50000c0c0800c0950151004000030481d480ca1200030110342042c40b8280c8035180501c0d0341102042c082003003075100390620510000d225007820305c400c3c0d0320307500c0d11401c40328044003543c00210455104030500c8401005104c24403010740140001014401c00324807034010140224180d954001380304007a052103a81600c80d00c0120000940d0340340544462070706076403070541d403414512208140c10b11140e80041c06150310301000007609100c15140c0a40407004008511811400680b01c01e900c500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 453868228 1250 453866978 453866989
    0x150b010201020702130501050a1502060c031b03070e090105040b01022116050a1203020309190503040f0308070c05010c0b040f05210310050109050d080c010b04050f0106020f030304030c1101020c 85
    0x1901e50411740029550b14010400402004d1580076081e011564089440100da000c00c04130350200c0a50000f690342e072a891884403080316a82c0880c0020680030090011580d40a01c5040d107050b01180c4030b1040ba42c9540c10070040720703200140c4c1c2c0c0c0940c0c0300a2843d030145c0003004070030076680005440c05050445c10790421a100c01050030850b4541c0000c1d062500300030031982d0288060740c0c185070840c190f28008400a07a641310006410b01d01403c100340740e0042003c200700701c03405446c0c0c441c2c42c464000c0d545c1ca04054070390844d40341220b00a08020700400c895205003280070166420000d98100c03a141c903280d441100c617609000303460500030039800900d4280e030a0b1f0080364844203000165902c3c9409080d101d003000860300030a040180407070302003002e44e540c40b20105460740c01440e4950384002d10019140102200d40000d50403500f400d042006c0300740d401e202d05048a44076000d4403d41c05141c2e82441c1c8a04c0112030003804201640559400701e08846905001c800d018011101d450400c8000100e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 453869478 1250 453868228 453868249
    0xc07140d05010915050a06030b27070906030212010e03040303050c15040b07021b03030301092a020307140111120c0d0e0601060e010e310603080304110d150b010201020702 75
    0x280c0780d06603002c20011010b005e00c00c10381d00444504042001030700359070700c2c02e10421005d46807401c041200070404580c06100740203010621200011160460317620b111000240800c0d21059104a61708101c201d01140306010340140440da80010794901429960140d505400c0200e8807032003882001c00030005447c0c1001540d000341d0094030032038218900701100a117800f03d640000c04d50344080243c5581140c400009070f82c1900c1d2019000305240801800c1001c441150040b40d803805840a10440e80c117540110040000f02d00503003404503a5040c41d40a14240d0303540040009080b0f0040003540300400c0b40881485d04120201e001070b14002d498078015040c0c1e4000c481c0f00805801c034200400109411842014a4403400e0070210446014040040d8142c440c081001e001a61000c3d84003440c140c1032900301e2904071303a03408100405a1a4207019a140d042143c0c1290a045200e144e68014030748040b606080a03407100b034540091088a0701c00000c1d1528100c07040c159074007071104038016502c0c20f5150 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 453870728 1250 453869478 453869483
    0x110d050702010f05060409020901090e10140711030c0a03030213080313090c030b01120510030b07080a05070e031c021014040209060108130f23030a020609030c07140d050109 76
    0x200f0030142a6a40508458000d49038901c22886d190700900141c692a4a0b0b504689201c00c1c00075013000306504003420206100c03121940645003c0103601d50311000800c0364012412035032007016200c1e2a840c41a501d1180780002c3d81c1d16801401c0e110b0000740300390020148c4401851008400696455000e490350b0047c0703099007001c0e02010400e0040c8503403480341d21014601881e0500410b507403000040d10440c0320b910004402500c4800044103c504018030b20021039008110301c245d441d0440e002041204240c6580c04070301c0c00e14011641c203903c41c20440c20400e100502500507072040341c014840c00203000300e40c070080d4001d4114112065040303200e9001c0c4506c649020000c030340f0341132041240008000b08002e0500ca0321030700340400303c5107070011020010782c004604c00c800269418072125490440014404240441441c01d04590340480038010700504d5808541003a11190060b42d100d005010000c02d1650081c0400c2003800444d004904031404060451001c2041a031074003030950f6000d8806 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 453871978 1250 453870728 453870731
    0x40b0c010b0f040510030605090c0306040525051005072301020705010b030304121709130903110a0b0a270309030507210807081204200103110a03110d05070201 70
    0x100d0041c140b0b89070708441d54000315403c000714640003a0140d0003600320f020103802c00d542c0b00001003080504200400d80b44600504807405407519140071503480810840440c5040c201241021020b102121104140d0708014200200c446540034202c80740c0e00001004d44807035080c0c040000208224003070103061005200005603881189041460940d41c2002d01503029920030407080044180da001d5448606a0101000f001c14441d185181c066020309408254130801c0c3c1005070710104920742c400d503071031031007600d8281003074030742001c503503103c41e4490b81c007404060744140050b0031519540d20170b510545143d1910780030040800030303804070404032500450204074222814000e000c000c100701401041c100c1c0e1490302101400c00c1f052100d403a51440200905c1c408500d03201084285002e40311100030a142d014151300e801d06103064040d402c5d914005a0001c0c02003c00b500354403c0c002e4032000041c070f04445203050988a41100140100040c1a5480000f40500b01c5102400d000e01400b40c20103500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 453873228 1250 453871978 453871991
    0xc0e06011214091204080607110f06010b090a050906010e21030c1e07080304030b15040e0d0f020a2d0b01080606040507030605221829011a090402040b0c01 68
    0x564900b001c90113804403801d00c107000c00c11180b140001c542c1c3d402a1946031080300501c000c440385160024140e6400e07090300611001140c00b1101a001c1d0000c41c0007281c00c460000e981d04140031403143c00b039a01c680007400c240842c0b20a420034580000750070313140f4007510351203070520150a03086d90082645080e10707800402e110038162030200080b40706101c41c0d034050903546261207501a500c0c401e51100500b110031420000302015003007840b0169241002c1d00030321288484200d190b8441030b50480160106400c5884000c019100045c1c5986150303000b6000d903e0140c4406070584c500071144000b59080440b5400c00780010580c207003441c02441414020b01c2d01d82894400c00080c0c0c0e41c01081c09040600e001c0c0704100300d5844035030070709149040895001c03480010b6100400a00754a034001c8241280b420000010040c02c007522059140981e003500f01954018030001102410a00c215481060b101385001114080e50300100100f1000420041c0b0702691941c2011041e00442c85803095a555004c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 453874478 1250 453873228 453873241
    0x204151d04060b030705030a03030905030f0a02030a030c02060105010e0d14010e0303070201060b091e01030e07060e03010b190b0a27060f0c03091e1a030717040c0e06011214 76
    0x612074403d408070090f014050518000c039a0350031101c1310160826840d00045400c0c003206104507060515414052580c8603195000a556980045810000a0318022240301c7d400d1020030000c2c16110143e440310000c0c50319200b0071070101707407480054490019088017048100001d1107888605004440515100d150840c07029003124050360000003007150412840c0c600e555195203076400042d0003124007064224400040700100401601c14000d0310903194041a09904070625405180c0e045009108140c015402c1c04808685070880004250401a0512002c035404000c1e010101c414034101d0350822030308041000d0400d4030450802e04804800f024481d072607221006000814040c14220021041950003c01c01c03203451040318140c6010890081841c1710b1104440010501080702000768400d049042000d50b200b0303920000824030060003503042c0b03450555964440c6401888031848140740071403184103104000d0007641000b4084a00c510980034a12940c1a80002100d81406138a84030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 453875728 1250 453874478 453874481
    0x20f060a0912020a0b0a020a0c02030a060e010c05070203031204030c0c090f140402090411030a02060304111002071d04030c0503070b09010f021e0f12011202040f0501120204151d0406 80
    0x92800d0b003c541100582c04041052920781c541c01040b840d50041e070310541c8640c01c44d03019010110003036040c001d80030b81e9800e2080179000b1905402609000700104900d200041c1c070107110b185002500343e0000e0000f00c0c20b00c0c2c880442c1560060090402203c09600e03995400460652904845440340d620b41003074104942b03034071600c034040059014007500ca00b40740d0000f40003454001c100800010b655500da0500c2d84050050b07c040c658090701c81c5880741024500f221100c600c003200d4500910080c3c1811b6492440082e0100450702c5183d9040c051800001000c5041c0b0300042c01607040c030001e0008140068400c100401303000d80580400c2c5900d0401c000c250b400e413060700c211022182e0041c029001c1c1c0d01402e20501003495402c000140d9605c9016070020401e01401c42485a40080700d400040e000c40100325040781540300b01c0d410050f603d10700c4001c01c22104280515003220056102c0314005082c107500100503082c00071150300721560b42e07001152800f0102e0780548524000c0e4000d00003040102d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 453876978 1250 453875728 453875753
    0xf15050411092e0309030516020a090e06012409030b061c120305310204180b041401021c02071b1419080c06180405010303090302102d020f060a09 64
    0x141c4c40d00b4000c945107610020302501401000c0008628800c4c0f0706e0085545500040c0014152144140484181214000d88401c024071505d0180200141305c3c10341c50340b111072001c0d401100343c0c031215030180c11922089040ba8000304480d40156040b01d50b9281111140e5001200324801c406074012101103800040039183d000d0021080321030420017107418180c035901015050502c11501200f402e80c14000940079200044004000e101c9a40d840c0050182d807000052049014002d401007600c00001614201e00c10030400001880140c1000c06118000da00207101b128090301100c90568511105442e480c03501da40030903c42d54015504905a08110044004845900a40c04d40f5103180c062940c4d2509000501a80710b541c0004010f04403107920360801d2807000c00a40204025a124523010f048070395103010903445820600141c1150a1040d4507981d07440c540038164452201166109101002c2030008860940c0954188258802010001c051240001940100d080b82c49820f240d44446031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 453878228 1250 453876978 453877069
    0x307113a030c0e0d06180c0e070e010203030711150702030301140102160e0606220e24011803080f040311010f0801030803061507060902040f1505041109 67
    0x10b066040100365000f1014045a0605942d280044409483c0441c01010310188150100d0070a01c0c0d141e06100c4100c078071a05483c0c070000201004d4460035815141680310500450040e80f0410000b441c0fd031089103d9008080c400b821151044465910001c400c2d030210b80304401644084010040140035007840d001031142130028003840c6140b00901150340c5514050220b42d003086030085002a06c0e4003084500124041c200c028500c000748589441d8240d162007010801e0b041d41012a00b000e00b01d42501040700d055220303070040b11004400541e00c0c0014005202200408424000049403002001b4580c0360040011107a07101e00b140750481400c81408903581c10826250005e06940c0e403c0800d040c1900d4000908949135542c480020781103002e0001030b00300c000b0020404804100c416004001d1041c400c4405205140e19400d000c8116002e64084840020589508019504056000a60f006120300702a0301d0f014028010543e0980701820401d091010440c001808490141c0002507404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 453879478 1250 453878228 453878231
    0x3050106050f070618080406050a0206071d09070201020f0a02010e12040e07050d02090a090b04050a150e13320c0a1e18061d06060307113a03 62
    0x503800c2d4030702650301a07a10010300840e580e03010f2481c0001013115585d90507a00c50f81c802e0307880e901c40d80002c3c501c2c2c014055650251240a0205030b00e1401102d52080110600400d4160b11411030704100d00620098580403d40d5400c001402601086000500703c0e150140c00105240668211041c500704038804614004002800180030f00543c0403c1d4641028040c54126141c00c1001704c810001d12500d50080e500c0a1103e0002070705490341e070400013081b40c007100c0400065035690918410765201103084400c03203003061010300100e90b07400c00264108840341404140e550556aa4081715070a103c030744401e100a0207915880c146684018a4180d5404006480480c840c000030910b000031a000c0c20907413001030030760000238444541c0d5a100a02281eaa003aa0301c050084084004106d6400b88924000c20400540c2d8401c03801181240161406442a4a50307500c45004070b8500728500c21b405c7c0c0300c0c001c81407400754990b40e60b40e0f80c461707000410792405000008089800e0321496002d08500606 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 453880728 1250 453879478 453879487
    0xc14090303040e04140102030412030b152a100516051e0714151009020f0405090c071202010c030b1002060126011b0305060109030f1b0e13030305010605 67
    0x544010007680e003142d800800c0c000e095144d0f03207420008207656040e50100c561000c41040248000003529043c2c00c02c0944080180200c0034080c480741003401d4404140e90b220800c400030300124a802c8a04035150a803580c0d41c0284002c2040d1824001c242040c44075541e1200140100c3d40b08002901048243c1410414604070741c480a841c040480d44e01d49555100000c0b4446051084c0c05000c8840494108144c548810307901500850150090390036910784001d081010030501403501c00c07510322100c140030f994205494601009440c04005043c590010800c1c002400050650742203445050925000071812103044c010080c1254148007403a442054210415210a600480d0207415500c00c800185258000713014505ca4900c80911840c2c800e41c0b03040718000b007030000c40040007011009179074140101e480c2c61004403143d446600020303044810240520300010070103290900004c2c0241d101000300c5d5914089510250b03c11220b0003d101c480c203100070308150303040c41402d024110304d08119040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 453881978 1250 453880728 453880747
    0xb0105040c09031205030a0f1407020606040917030403021204082505010f030c11071205060f091b030a022817120c19050a0507080c0112090204090c090c14 68
    0x111032555081301480b40000100e0105441c5400000c280300c50b0000901c000400415010a4540104c0d01705005000e200b001c100031b454640140c0700402c2d0444030606260107030a1502c211a03001800c2142548203801408400c41c900300e001e400107182020250030110100410518508420742c046210360480c0304041c48603a8000c240644012041d03d800150801510b80c15103085081402e00811841003150000b4a46901c80070700803080e110300c05954541d03e8284185074400d42c06e64610783d40d07030070400620b41400b00507240020905401012103951031820f4000c030b40451051158403450048151043c50302240000000c001403400d4203004c0350306061b040016403141400405441c4131840011144d003022410000410329000c0c1000d4070540010502e011b0fa590645440101e8150080c581c000840100c041410b41240f00180c55071150401c5a00140c00101442002240d00a03520303a9000040b4224036901006000a400009002000808040c122039406100d4011540003004110003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 453883228 1250 453881978 453881993
    0x1712061008040b100504060807090b033007120e0f09270a020604060e09070801080303010b1b0109050f150c04030b040212031c0c020606090115030906090b0105040c0903 74
    0x10b2058100702a0b8503d80c485103410030701d100c05940f040c5d900504184000c2410500814641e04484109c0810405500c61400341619402000084004400888141100400078076a40e620704650b20940c9807406004d075030340340498003c030128840010034a00b0410502d0400103800510381104071407c80080c42c000707000d0082d401d118100161f001c01170351401014441e0400a5000d8103900a244640b03c5899070001400000d445503194032a00c032010124803854003880d0924107885a403009585903a0a140340e410041d40030f0142d842c880400f0000340c0c06651400e20910199a100f10701500d1560444848246442c410500141d6001410340601c00b006a05204580c1241d0303002a19010681e10340c00011807540440815038000d0100080c0022201e60725103200c0c0000054030b004105074000044102c1c0d1780ca8040350099000314002c401031160811140707955515410a2a002c50300003001d03540c01d015220094411540c191040d001405545024001c481e030615203480c02030180c1d0b240d52540a07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 453884478 1250 453883228 453883231
    0x20115090e010618090b0115050405190306150315112218090507060c0b0f0a18290403051c0603020622061e0311071712061008 56
    0x40c658031458840381590030742180006040382d501d100e42107401412110040c0024041c03c50711000103000104100785001c101607002e2a841e43ca541c00c1606242c248007161100c14210b03a0003062003040000010018014900000c011081c0c0101a81ca145802c07182090349143d58403c0c90701703002041c0d100c102c401090381e40e0345004480c034124800c50681c003c06004850703042408580d40340c000140f5070050070382126502c50703c2103084400e007030381d00d01086480d08006c1c04010040034940b8080b0b8040254a105690402c0e84030718001103402ca160202200e2542020040354100c03960340c01c0c00d0780c80481d52611911282e1000b0004500e2800d550010881e110340541c80c2003402c1003000c0e41c510380740c0c04e900880246a001c0e04040d640d03031010611001e011118582d2100125544001148039803045807803a03060415051305100b2641030000940103001031507031520b0700c01010310030b16005c14105a11103507042d240b10003680c0e0300c144001002c0e401800040c4042d006030b507410202c0b0811644911080d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 453885728 1250 453884478 453884489
    0xf06080a020d02120706050c10090b240a23030105010503030307050f160804050f0409170a05190c170a02030a0e040b031e101107020d0302030f13060906020115 70
    0xd0800e42c0d107880003501c091004001d5190794031404101044503a0800c000700304106002c01100c0044100c440020b040e80d910b40f1004040390000404126030808084445d0b6450300d59480d54810110000c011440803111548100500070203c03030212003031000c0c0314040000319025402800035604240c0881c0d80c0c0c6c4005403841c0d00b0020000b944610401100c8280e4420300035070142a08a906941440011a0468020740b0320800c90300e50b500d022440c0078401e1000b9594021741f213213412404107500c1c51b000d400000000e010301c841007280c810b600080d000d038a5030202d901c0d01d0705a03507141c031030030310010444000d0011b024200c1c04210681200c0e8000007035070034810880c43d058048822003000308000e80b020303010f20ba403d8458004403408004103000d00f5801f07203070301c0f0045039003508810b506142514403000da03a410194003001100c0150600d400024440340c020700441c0e00d0040ca2580d40c5400e41e00075214207109803108801442031a0340030601100a2060788001e115403913280c641200d104500c1e00c80c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 453886978 1250 453885728 453885739
    0xa150b09090c040e0c2802070b09060d0501090504050c010c030206041115030702010516020d120b0a031502030103020307060305160c02240903100c0504030813090603050d030f06080a02 81
    0x7034160808a000c40303003d41054104c800e0282407540340c03100ca40c4c1100407043d56283c2c48001c0c0c0c500100c40c1080040a80000b54010311219242480d010b0381c6d0781c0109810384d08103404002c0c2034000079190040320300801034948002418540303802e004c2c1c10035088000b880e04000078000c0c20004030f6030000b011a0000d400c02c4068600026402c00900e007080d25409445c0811000700c02c010313081d5010750005200301d90401d07140114403000d24040341c844000003002c0000c2240c1b4049004103031042c0e4000758003d44080c000503041901d98564120754402d08203480d00d00d640000c0140218217050100700000c144c00c0c102807046081c03210003d150000180c24110401405920700f10a660f241c00c0401d081200c007400726080d8280d241e80e400426445001981c0c0a44107180d2a0f9918501d244241402a0b000350780e2541054216601c1ca80594002002060045084040481c410302e251050740c3c000c500c41e100401c6d14454520003d03060b1404000c0c8080000d00d02070381007141e454007090a0301d880d681100d9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 453888228 1250 453886978 453886981
    0x3010e0708060d0b04120207050316060507060b030604050a0303060506120a0f29040506060405030a121107170d0c020907030e030d180b093d0c03050a150b0909 70
    0x81891110b4620f03000e81121000001d02c0107004010101249080d515400d50300425100d9080c1603807514012102410101c94910030030a062040002d888194400c101c04103c1d100800c000030314040f400d690a440d190458030500003010b07014030038080148003e031809030904c1c15417042c500e40c5940051001e2089626a001c8101c4841d240e800032104e104c44001241003003011588516140d180d080c452030245183c140171801503d40641a42c4c12650000d0042203482050f5450301e52040500d0340c075106104100303030103062502090240c00040c0c0491007014007501c1c065452a8580440f200d0352034144401c4d000c1c0301000d6194034540681c03144c45070030f000c103103828070600061841c42801028480c2030303e84043c01c924a45000440407000c4d0241c80181025116244141d880360320340c0c50103542420381074504800710030303218220404a1960b40d041c1e0540c201d66a14900c169400380401c000025075401c200011124540b04000d400c41c80030043c506ea03e070504000404511900e40000d00c00c440350700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 453889478 1250 453888228 453888241
    0x10801050123030a0f060f1a03031602120d0f030609051501031a0a08070807080f030d0b010507083403080402040207022b110607050c010c03033803010203010e0708 72
    0x1803112039a05c048440c854440301d05000c4000c01e990041030003d1400d10050300300941d00d0004046410038002c02842c6000810200c03583c450400301400c0f81c0120060074000f0000109100090b8908a2525070039820704503004024111040394002104043c68102488103000d01d8090b041120503003828002044002556841501c181070155643c0c406101040070441c06008980f0000729265003081310012070301d90864a80f40d0300388145201c1194024030800c1401500c58011110545d01810328a1401000d42c9400038168030082500192040c00090001c0c0e0701e00d0020704500e05a0740c001801c4c8070908a56000f000b502d03000d40040e22898001c42e1100a560382e4400d500d52801c03910f0141c604035280c1030140d42d980b040c21103090342d25001e501c0021800b400e11200721011154043e002c0e1441e02220001511144c001e20030980c10165540c1c40408242803e0a8640980c2039104031051032034845050010407103c2c61a1440c000d9006100411691551414041d00000b540c18100706507030b90351 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 453890728 1250 453889478 453889483
    0x9180311030919030203060a0221060a0e0c0c0607050309071a040b070c06091e0303030c20010905061f05060304051510031b060206011505070606080607020601080105012303 76
    0x2d003010ba1000d0003040280110340c4040040c401c4a209070141c070a03582e910700810081740a0740122200083c1186030105807a0302c0c42030000e40c0706000a0112017002d4030b0b58040d00c1175503c226070000303a5501c00910b003941007904019484c0d004906260003403a42c03928a009036150800c0d4861101060048422640754028810965010b0700300554242d894022900308604099120300c5108040b4030459404103200d022103807100311050500010070701d01451540c2c00c03030051007108900020400200e0001702c0501c1650304250440324070000100f80d81b0110704140303040c000058104c14002c071500754030508642181c05c10300116401100d03000d0f1a5542e5007086421f0040c8a0b842c0c00010800000b0428108040c03803c503400d80380510600c156540c0468907401d038940c200e000c1c22000d680b09900400c0410944d0341030100079003541c078095040140b10b80d10b030420795942d0781025003aa00488104500d0580c104912030041620310001c1c411945484507205030003848220304069225510600b41e9143c804 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 453891978 1250 453890728 453890737
    0x1009031d040b0d060c09060e0f10020102070204110414040b092d040303060e01080120091503011d061e0f0105040e0f01030302190c05090619120b010918031103 70
    0x40d0065680421600d01300005101e0b40e0540804510340400110f0503071f00c16095540c007000068140042d14600004001080041d8003141003150f400300b0592005807141d028911a440602c4201c5803183e080c4110214424080036640d8000c600d811100601075a605020315008060290880d04021640060b5540c28500821405841c40e03944140010960f15522200072122190070540c01a44c0303030740304503099908190600c020080a0314000102c240500d00508101c080244a03514003038a81c5840181a00245e12641d2042c00524084041c3c4103000030a90780a0300481d040030301d19100c90a650032122001c50880d000b280c171100801030690182040310050014a0304a02c1e907460911424010101309020880041c017510040d5030001c6030b13001c103501c0840d80c00014800e6003424041404507031007000b0911544040c1d00785000c0301000e401c0720050081c1414401544009480d400d0010703c0e1501a48452485440e0148200c0c907407400742001c1509640c14501901c1079240c00c2000b034a107015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 453893228 1250 453891978 453892001
    0x20307020a1202060714040e043302030f07080402130218132408070605030a110408070303090b07120e0307030b01120204051b1c0e0303010b0c1009031d04 68
    0x31018502d00a82d00081c001d44503245541e101820240704082c03c82d01c0e409180310b00602004a2000320340055000303140c540f40d011051003c8c01c80c000c0c1c03240000200400348520b0303000f016400014170559451502010b684002d407070038090340909252340440d0450b8210000380c415290b02242035404029001000c09005000a04803440307e1140c02c12070004105206401070741c2042d10342d0307c1c480d60900f1402c010441e41200080c100092a1400949030b5900081509038291396038000030405802c82000b40015010001c010403100b802c5d460302504030710044c1c01c5081d02080070f100c1e60b40010078042100800e00c01c40d151501c64000c15902007440c101003030b0801081c0d80703c0c20001107100c218160039154114001c88040c041a101e030307100180464080c030034003003000c40c08000c0c0a100005128074480248801640021494507000304541140c100fa0402010b00000159130f1501328004c01001d01510100340c8200488111079801900300803144400e0310161000d414428036a6803203038071031811601c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 453894478 1250 453893228 453893243
    0x22060b090109050a0e1b0114040b040905010f0b0c06220b04050105070216140613030606080d0f17062809140106020a05060a090c15111c050706020307020a 68
    0x140c42d4403042000d400c00b198044401480c0c4502c0b0070b03506000213840215030003417038803507142c5206602c0116030100542c040603043c5c1d0010440028a002d8501c000c000034684200001500c1d4101f0752419050101da42c400002e140e414000c14030342c0c060100c2e505401026456004500f014652245621000e5900019102d040d003101004244201900b04c10b2080301e080e42034441088280c0c21928262a180c00345091794030f04d202d000521400d0940003000059294034030300b090203580c1c0d0764840079180a9085200541c0210100c0703402d140c0c000e00c0b54442c940d1749003051070b44840d00d10080410f142c00100140d02c80c04e9092103a00100d00c258802c101380940d00f10340640d08544500b0b0710740140502040140380034800744000610b9520114a04010a13406000b5003c2d54690011f441d02602810006440c06218140e00013a40c0311940740240480300c1e07546400d440c6011840106041c40703807401080c2c0d0384420900d21950143d5001044034221680302a0040c0c503034071144401c074a0095480c1c03001305060b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 453895728 1250 453894478 453894481
    0x150c030b04021207090504060f05041107080a0e09010608010e0f04061b180e0c070b060a050d0f02040617030412050307080f030a0c140702010503090111031006020c0922060b09 77
    0xf00f000d22924890b5260762900200c95030344000340011284640b161141c014200030303040c41a0b2525402c004280019500c62a0a221040c0c88412082e0310050b0a1000328046030755a100c9810486021070040c855400c020140d5850f1031185041000020010800080d01c0d00001d0100011544410f0106140d003082100c0014143c4016001010410451800c0010108001507101c000740c4014403448204854500f801c0c507a40e0780b40c004080c0070381003582c06420020086070315111042d40d02c41250044007901700190650040c40102d95403600700d00c0c42c16a40000d02c95030150000111011221055855181b4200a0500c0e80c150b018084006103100340010386040e8055804020314068455000c08000b40c042405090b2104031500340000b6a94105010031710141d8000d80107564001100c80000c0b4590101901409050b030085840d40043d681c00c0400340a407950400c002c03102d5030801d5034414100e05000303198204020090482031821030a05d0504d40c100501e5401400120101038a419040d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 453896978 1250 453895728 453895747
    0x100c030204050a14010c02090a020d1517060603060c0912010608010203070f020304140405061f120606030911041509050903041706042409050307060219080103150c030b0402 76
    0x658010310031140f00310f05007071001c100404400450005854161134800d0540202e900b07201c0c0c2044010541148154203200c0181003200e14080e44100103503503254510100d0a160494403040301380a00e600b8940d20010401400e42c600044c031542011b01074003503a449082c2c64000a50b000c48100300c0654a50a007440003d241405401660282c50b80f501c030980c2d440c0030404101c1c1d881c0038038810344203008101c2e154011107050a0303002035044100a4074503840100442d02c00d4032004030203c48400050065040c40d80352000521464000d08070034a024807031050191036040e8000302c822900b910070350f07640702c00c07104066000d9000c4c001404140e00c00d20040ca01142d9584d01ca0300031740700f4441d001040e5800b10031403101c0070501c644510b038041c04450b00014501415a0100c81d620380041d0000e80d900c1c0d01c5408180108090201c2034481e000c0543d446c100e0f2281c2144141240500c023051150100c01400014841c000c030064440d400039001075290180c0608601518074400802c0d0003a20004104c8031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 453898228 1250 453896978 453896981
    0x31d150c0f011b0e0328030c0218010501120c0801090c111902040501171c050919170303061005091807120e030f0f1606020c06010e150d030e03100c03 66
    0x3814043c640340c84940e06054410306490b8843c00100140d032041640103484801c0c0300440c001c19a0f4001d2400d4001c0360180e80c08203000031984041002d0802141d40104002e6038000381c120a0002d4480081c083c001201e074001d84148818020b01200302c1d2202884101c440c40380222a803002c18481c1218001c224000c3d40402c2c3c085031003402d030700881c206800441c6106444900e02c038240394440c0182401c24030300540000310f55010a040c1c08000c004c000c03031111552148803440e112259505c41541d032500d0f0403030241d2071090300c41142d44550828420804141d031010864244402d180c03d000d039079100f5110000d00700e00310700c1c01c40741c84100b40c1005214805030301031480211004641020025108505106503407401800120000000300700110115883c0b03c0700500451091351203104200f01e40d82e5580c200f41d800ca50350410042e446640104403d82d0041040c6c1d40200b510605241d001c120200810b03020718015401400b071001500c460740c12510208a001b50084140d10b0410074403904400050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 453899478 1250 453898228 453898271
    0x80c1207120305060904110d06020c01020c1605010f210c0302090102010507090f0501050c070e070302070c0f1212170a0f0c211107050316031d150c0f01 67
    0x58041c4207200c146154240a8400d540c06840000d1010960b90b9a0fa40e0b41820b00144108290300000410111000502c81d03001501c0c5011000c000075843d07035500e40c0c0040c5031080071640000b00c118521020842c59800c5041c1e504090494585042a4021840c5900c5a1669209802c0c05107107040340c1c60000780d5041d80030303140169099009021b90381703035010100c130150b109010741c03440283d4010040007558000c1000302034600e106016a810a0f9940345211081d07181114107002007900026030b0b8007004140100344010740f030708a03003800a182c14810343c1030764541704480c010015140c0a5050318100e014000351301c0e038001040c1200c61107152440060010780315a0500140e15402c2c070025808442c046c28401d4005401a204210300002d01070721000507003001c05003a02a104d0402003140480c0e4240002c2140c400c90b0860006c42084a190080034110103020102d4005400b4800309000d50750521f640700382c0440344d40d105450703010070301d800c509092002c00009265803800c000c1500d240080078284 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 453900728 1250 453899478 453899483
    0xa09170c120105070e10030603020a03110411190e01030902130b040507020a020609191d041b0513050a151202120a0302030d090f0209040819090b090607080c1207 71
    0x504814003241c1c03156003030762419182c200c08900380340140041428060769045103644c03245404244503035680c000c43c1d030341c81998200f59060b00200382c0ca01c04604060242a6250304041401c5141440602610200b11074900d4508100710325021a1110b5038465044400e0082c0c0052010408003841100e0308010150b02001900981c02d01001442c45400800d12040003a0041c015a103441c50701000c11924240202441707805a0741010042100117400c0c00380001c0c0d41e10b03140b400c070442c113003030900310318141e40f0400d07071007800c100c401c0240008e85907803d8036002011840c40100e1075442c2c500c0c1c00c001070804403002c41403005002e60000358680b00b4000307000c10b050094403c005a18003610400d5140c4024200180160340108042002c0060702d90100a81e41d02403012080502100c0d0f000494203031003074900781e5031a400843c0700850105411007011110000307081c64000030b0301e800cac0b461501d070240c0d40c500d51017100c0100f030150034020070034101c0b80680441401d0322100c038040314040101da00040030a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 453901978 1250 453900728 453900739
    0x414070e040c0504120204090204020c060c0d0e28060e0115050909031602090709030f0c090b0d030f031503060906021210030222150f21080307050a09170c 68
    0xc03282158010f604035802d6031000c0e1084698a0200d400b40400341a0100040ba0440c6d42000240e105081c107001450042124001c4e86699a101850400603641481b203003510300e40202084984070042d403034400c1440e00c442240c1000c15451424102c00401004c0802c41c425420061005c0125075215142c13811380d41c04a42064a6407110081c040c0d40b070054014600110001548450142c588021003550061042c5410a00f154490f5070340d0035540c1c1d60803012503403c2519542130000103014068121040825210800c01c7c44146e2001000e0999100c4510245951075007c200303a00c0020301030402640c1c03ca1020712032101e5900e8024000d601501150b000ca064031008629155000001c11045035001415019021074a0707002040e0031040c4162041080e540d0800d0f01e003610300c4044800000c01c070136068541000d24250b41380d884800c0c1081407016032070322011070340d000515181c00e80750424a2807030b02c552600040300040e501c0d100583c00440b02a0070603503900c44100000038200c0c801c007900742d07078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 453903228 1250 453901978 453901991
    0x3060a0c20030c070e0c0a0e030a0f0c030c09020a140a1103041d090d020c01032310030203010b010c0b0109050c040b0408030a030b0604080a0308041704060309060e03120705090414070e04 82
    0x140107100310415140744c1d0682c2c404001c03400c041485540423402e5403900402340c0f51318083d196070301c07110301400c4034045030800007290081080c03098030608c803401410210015481d001e280080146100c80800700ca102140c8003083d0340104074032a0a010304100c602c0e0007200c0ea2641c403010005030300c8404045401b640000100021860070011a003444070030100d40013030401c409460700640141001d4000311200444503411000203040d08100700d4011a00b00d240c43e1085421801410b082d0b95a002c0d210341400040d0108800082c4806400c0341160312161002480e034a40300c3d11700c0c4041c421613000e800ea46002140211302504040000c1000e08402d4034200100450341091109602a0340f003825000e03000100c8540100e4002c11856910520444051a6441280025503d160056002480020303585d089000070005584641002c8040c6180117605000184c1420180c40320300a100c5410000040340000c46030701c540c0c02c000c0c1d400c5401c07098241d842c0392011000b414110b15030381052041d41041c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 453904478 1250 453903228 453903239
    0x30f0709030302100507031b0509030d0e06090d060b061b06060f0907051b1605010201110301120f050c0405250908060129070c0302130b03060a0c20030c07 68
    0x10111800c50394942c0113007034181a010090402080300a05460606494001250588000922000148209440d4151100c0e024014140303005030021345201070042d25054541990b0b145015142c2c0000c0466000541404902e80200548800303401a5084400499078151180a0200b912600f080200803240103517030348000c0001e00380141c21115004128407001c5150340380314a004000e45070403915071a94081100d0b02c0c071468151080c4c0c0342692150948000d0105603030a000f0980c3c1c1d000c0b204c94442c10f5504145c150780114078102070003481c0111a000040c10030809100075004681d000f0300401c460718110303200505c0906038008004481280702c02034428140202041002c1c0d40190008010360b80c01d00380304c040e8840ca1000407200b00d000e0440030700102202c020050040b20721607001c900c88549180305000c007400898580c2c501d074604281202503292800100c0a610800705034011807072003a00a41502c041c1c109440e405000c50103000f01c0c2022105c004010a84004404200d030070165480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 453905728 1250 453904478 453904487
    0x71e02090a02030601081501230307020d030b0f041e090b040201090510080a2304120201180807060c051c14062407031107080109170405030a03080a0209040908030f07 73
    0x8803081c0d40401e02c21004182e1504104140b0281184181030000327406807440701d454910040000307007000405c1c0c00800c20080588c10304c2280c42d5801c0504007400189441d20000da030790040e002486006a40d100c0002002c441c0c00d00c1c41454110a40404101000075800c0c5489072204c219003d9000c0b985903080003419040102e10b004007103940e47d40c1c20050791948030000001e82400540150410040700442083d00c2040355058020b0748180f400c006407080f10b2602178203545114805400c1015064800c0000c80c0003201100c00442d44450002440103201c58261042e0041811180c001c4606500d07504500a04d41d02c501d051405000901c130155491900b08122049030000303080400503191045480b00800c8130141500754800d0400c0302c00c4850a5500c589881031660004071103a45030260750702480301107015403d0305840009041c6c5010b0908000c240e07224107881c070050401c0714050026847d01000d41c16602da0900040c000d0100c1040b500b441140d5420580e075034034240c0102000325131444e016 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 453906978 1250 453905728 453905731
    0x103050d184a040203070602060105060f1c0f051b03220812070801031109040c17010e010c120b040605031c09050d082703120c0102071e02090a0203 65
    0x6081000d040d25041e040d00a81c0e02e00068880c4180100103240c0d150300603007841200c886020b0800d4100c89078600fa00405103452900c1d80100e0035904001c0040c440e0340ca4240072941714482d2580f0341540c40104030540030320103400c900c1048a45240c0715046051005940041d4054401842140706020207800d4041d007900c810348100c0d040b4940001c2c2c0c40514a280110014518000c04406003050310701c481c0300b000003104654000018403900c0040c010824040180700104c0c105840d47c200c0c614055903294060441c80c050000f002010501c01a905d0070250043e40f981c4001000a010368440310801803e0086c0102003810b100c0d0030301000c2000da0905100f6102110b400400902803160030b484044410040203030820b0410881c49408140d5031500c11501007000d114071009940d80b1402d0b180803200c80421480300d400005004035418540c1d800141108098a0510b08c080d990b150000880c3d00912071014001c10000c0700c1c00b5803022492021001440c550f00035105800e86540b98940c0340100d110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 453908228 1250 453906978 453906989
    0x70c030c060c1109150103180b040501052715060d05011a010e0f0303160f061118060306011707021618060b040806130f05030309060631091106030103050d18 69
    0x50b00c1d200460349621a81148d25031000091026034413050300c0d12011600b05d400c441c20b0340c3d240c0d1200c00344900c1121014100440c2c0300c0413a00c80d8020b0510415040d180c02481914008044820010ac0e4866403400c0d20403c13141d62080c02040001021206001400080850180071803a0151040014244201c3c030101c41c041c000c015518102085c070407040010517000c0d05030707a603107a54030040b030000c0c03c076224154095404860a0383c40d40300c0c1074440e1610001607c21140101c00a00621019981040f1203656440071901409403d58440c902246400c08180b1569040040c101c400100d6002903281e58911070340070f02007807042c0c0c0c0c1c43d60200701c910301c120310580c106031780b00500068100554150111010384510b4094400c05600c1e190341d07103182c00c140c5000c007094008106010980c0761070380032044000c031185013902d841c443c4010104d020107040c142c02c1c109541c8496120701044001201e200e00482c0c0100025220750b124104140d40e038100086c0b0b540402d4096850040c0180007420350000c40300c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 453909478 1250 453908228 453908251
    0x105010905210a0f060e01060902090306040f030e0414090f160603090c0b1903051f0911090306040c0f0902040b0a050901020705060f0d1506080606070c030c060c1109 73
    0x3100e041c694903818102410b03140c1240a1541040f0000e036900b2064034400340120000301c0c10031002201030b800c442541d0310014280d841041006455100824042d6005410513141c000c030b801c560a007500c0d012600086264020310300000181d00842c0703900c2150091881c0c0c1c2c01c0350382010b410070907540d854990907402012000d010385d040080c1482600700d1000c580c46002c044070b5069552604a1241c0c01c000a40110442c1c1039482c0c402d0140c0c180f041c642d200c101c1224012088a40d4180400c101042d03005d1617582c0c3d9141c2021032640c504510481c2c04603403001d000c40c0d000f440c1900b4041c80040341800b85100c203980300d0f01c0028004000c0d000b0f0310709507440410038601e081c085100581e4560302c402d0501d03040d4010036500203160341d030721800741c03041589000d68241d03650f00507544c0804903010151250741c218098201444410f500510041c1d2298043e100d16035a500c032410080074115081e4801009880c4192004c5041544618a003032054031503801d460049032098200020040e04072200c0c030900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 453910728 1250 453909478 453909499
    0x150d05180a1b0305031206280902220605030f070203071e05010e070e151206010303051c020a050703030606030b010806090c0f070c0e0f040c03020402030a0e01230105010905 76
    0x642e030020748000a41400e241040c00395407030b542d0a040d500b1188a44e40048105801c00c0174074100450300e045507030200c0130020f602d00881e0031803070959030b854010207015550200340f5000003940c0c8038082a10360485103424058550360300000700703a07910803281c036805008002d0102c0c0a02780008117456020f58803400e0000c3c5c51407000021a0f02c410741d04015102036494000c414510001401000c0203401407403406402890b181c501800d040802491503030140a0802d03402e105c9000100d903241c1501d80c9407070500e0303507a01302501c5040030280c1c00c4455002548000790769181c06070800001d0241c14447c1d01c0078802c05030303211001d80c115030240102501103880040081c0f0540f901d85051030707224401c810f00c2d50402106100609480d000180200d610111166003840080206100300b07a0140404d46040341c00d1415650700395201421340710090160342c0110208022200310307081744100b8182d031402040103e041644420310455039017801c1d00403134129000407c89500c03d00c83c12090328409031011109 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 453911978 1250 453910728 453910733
    0x501140304021c0b0a06032a0905060d02060301060504060306050604050306041203021e033103050d0f1e050f090309190302060307091e260705150d05180a 68
    0x20f240300078403102003102d0800b0b501800030740280ea646000720404000001e881b81185001104e10021035a03100a420f58402c070152114185200d500503902c003514041600d4640801141c1010b01c00360000354004404000440c945d41d00402420880c0c103240c2d003e02840e0b03034131420b0000324495801000d405400500c001400b03d80481d2440340300300c66030301e001490900030103809401e994203100451050301c8000b0a100f54100c1e40c03140c01442d01c0a181500c01c80c1408420620101c4112800050a00030042940005c038007403076101d2061603800e50824000b60366017407016041c180d0070101e2110200d2130040890720507461844120720640b11381000714900018130003007115000c50096098204242da2178041300685411001d140a1110b5844841910341016041c4804024511031202c0b031499000b81085181c03905400c06151b440003100c020f031021100c005081c00c0c41101c1d081203030009286042c4c8008860171340011b201500d60903404110544900c074401c0448a60380c1441d03002e40e0307c1030240101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 453913228 1250 453911978 453911989
    0xa0b0409150c0c080a1205060303030112170f030a0b12060702070909020402090d03030e06010603091106070302100e0c01030b1e062a03130e07080106080601030605030703060c09050114030402 84
    0xb4404003e0a005028a6403503950b086140d10441c10f04000030340071880742d02d510020f0301505400c0705048014504560600d61141c15140110201a060309201140300d04e5074502d1038100e48140b892000607568902d00030a0440c080e00c41d6512450041d201d0040c03109400002152203405017000c5d901400580f45401810350140405903016644580e08001c1c035225a1740c1c11448881071403090301c000c25804080030b403180c10103005a101e03405150170400400005001012509040e4804840d00c070703211203039410b01f00c0c03401000d501003500203460700e1450411454001341032045c01c035091b6414030400c06a84180548074003840c014034030204803403981415604d0085c0242401d1504601b03a010000c54222000c6c954840e04030403801071b0381000039581c2c02d440040009402070b0a2000c8940d255090402000b0020341d4144224000c125000e408215180c1c8a600104c0051800400b210081500c0e070900d03a005092041e6a007001c04e40004000410f03500aa507000c040c00b8844072103034159543c41d000d020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 453914478 1250 453913228 453913241
    0x11010c08060603060f0406120308090d02190807050610050a08030a140c0a0203060c040e060409030c15150f090506030703020a09091b0803030f0a0e0d0c0f05150a0b040915 75
    0x50340044500c070a403219488a109a00051224925058a0345020b05004c3c1400f800500140d02c0d64104030040e3302d4898000038680c4a07404521800d11044c16241081d4000740101e042c014401d00a140c203200b8000396140345041510b900b150803c5010b641c88003411365900c00e0038070000c00b0502d0f00741400d24020027607014107144d14024040c4c5040b000280e00007400c000c1d04a51402060702c0100341804403061132460ba80d4420401c0c0d508112100c500d07100901000041a0300901746041c3c18181e00854042e5000b88480351148101c0d82006c64650230b0a0300c505285028003540580350100190251500007185004c40307030080e20705100b082c1000c86000280c45800c405a5031a04002020307410004a000054002d18003480615228101649241c0354460f0240500740b000341044003071400c0c29004600010790000074144090856814a0043e0f4400200a800b5045000701d01c1103003100c8107040131940c49407800c440100100c60b070840820040f250780d114040c0155200e4846101e4140c1d4550066 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 453915728 1250 453914478 453914491
    0xc0605180901050d11060c0d02100b06040b03180a05100c0201050603070b0a1d0a141002070501210906020f0304050f0609150601051b011b0305040f02060a050c0d030c11010c08060603 80
    0x17541fa04484e0110a0701d024088044240140d1103110b020003406007a00c03403022051000c5030000d141c035150003030052403400b0150204a483e0701d140d8200528160800146003095480001d440104400700d180c40000c0030302407103003400365092100094140c640440c4003001d491240d401c40e4100135036010101e82590943d6046050090940c2d0600c0d51561840803040c02000c8800c80c100304070762000e050200700e11001e041881036500402d003d0203540c2e0840740524200e400003002c44185491000001c02404200d400503014901c001600c071b0a804080300103501c0355014508950444802110490b039602046849a0a0381c004a40400c86000320f414015001001403500600740380820000107241795200c008806980e41d11240c41001000d0b854188001410509040080b0301e02919007800484100d280203100b6400003c3d10444680a0070544644030342520441d02e0040700660b001d802024840508404512440750340c02004405018900794943d00740d4510a083c3c4540c001e0010039000506003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 453916978 1250 453915728 453915739
    0x3010504080316090e09070f061106010308161712010608091504020f030303091606110c04090f0c090b3d020c030d0206060906060403170d090c0605180901050d11 71
    0x1701104a9150640140f1003034000e05620f80c940580d99405a01170f0740b06c070040c01000b41c2100c40840020400ca41141d800418042d030300c040c035500480303e04e10b003404001c2202040407800c10916400e940540b0356000c1c81160b00600364aca030300041e2a031a8003120042c509a104880200078800610011908584090510a07003004100002411f5030011900b0a19545c0020012500c11a20340000d000801e180c0c2003045d034292010544580b00c0289c1c00c0c1d03c0c0e00994440d948501001030b254032684902d5004900c1e020365985401f0f00074007410101c2c48080c400c955408140c50038200c10000d0902c00ba4556410713901840611040050981003280c1d0003003940200d54900310982c4041c007110800400c164054625803902c030040102928014020300e0081d401400141b0004e0b0351564045881495a40840d03190b034810051040505080c4000410128502d4000540160000007030050052090f0080015107811000c0c0003684d00b09110300e40d8404c51013000a0b000c01d240e0403a000340128040d12 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 453918228 1250 453916978 453916997
    0x501170a0e0c041b0906110a1b0e04080d0c08062815050c070803040e010e33010f1d0d11030303040b07120e030a140d0e030d0b03010504080316 63
    0xf904803116070046007250b2004180c18aa416440200e903005403c0a013450b64195800c9031074580e0342c441c030b04001414500842100001011520700c14802040e035404c8414551402c0d20304502d89410041e11031103d2030410401c480c3d0b0600074107880703218004c090043c2000c2c1c00300300013103080007100c2c00c01000421245000400c003038090580000078000a0b80710711b0755542c100700c041c900e0000300c0c1c0e1204485810902c82403240804038204907045610485985956032280f24500d20b24062034080050b03459132030301540c0c0c4c004846483c003003e0700e4401d0725039078114410080f0a8405140010440e40b49d181030750300c907082904c0d03e07000c1300c0302031800380b02002c0034011014042403440e8000e03141030f24404110001c102c4065400389150000f042801c20038446403000301c0281d9620b00072421041c041c8406110621482c1c02c202061b154007540880080c05803504092455881340d00500301414400c2c1031031200c41b441e00b0705006650046901c80345052541d50b0b06081c01c0701c1900180380501c20004440b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 453919478 1250 453918228 453918253
    0x1b010302160b07110f0601051018150f032901030c02031b06040203010b030f0d0c02060f0a03050a050903090102031801200d021b1f02030d020f03040c0501170a0e 71
    0xa0703051003028280c413140c6480540d0765660385844400740948569500c64801440f4a45902465150001c028105159159494000c0d040d0207040358100c4240c1d4184422000d4440d64494207841040f540ba4030104070a040c5008043c10381a078a803040d90400c0013800605020f5482607001a02d600d403584103881c145038443d411030b1200e980042c0920650b074006000d02007075150a01c50b030f84403200220000d0012031650050952100d2800d81e6240034410020204015034454a0850f00c10041d4411060b55582d14490050020042511300f048106e00d030400241184a0000454460f000160011401e011160f6451010f10202140c924108203003446006503200c000001c0c90924902e41d8040c08003807906050017807901034110201c030b1f88041c6844440280744c07515180f442d0984211509010300003841c0d90709074038600c100985018940e1000030007090461402e0091401184110641480c1541c0e03003004407190512941c0f12030301011150003040685120742d010041c156942c02c10390760303040c0841 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 453920728 1250 453919478 453919493
    0x170405040f1b0201050105012c04021b1b0a1a130303110105060910030f21030e0613120c050f102c0705120114010303050a0f021b01030216 61
    0x3005031044079107840c103895810820082d040000c0b01d03144004c100c95850600001c1001010503001c08181040034080740c0e00c2c0b1600c40e012003226a0140003956518078454000110041003c0402c2c140e0203400c00c1c80b0b0112150b03082031002204020001d4050314101b1026010b40425000001d02e0700c5010414541000c03242d07030b6803038021406921078034214200c2c0e016103030a482c070041100b0b02c941c281d4020408901c001600c8141543d400c40309000d280041490100040e02c016846d000a0100102c5034585255140d0003800c410b1081a041e509203171544007004150003603a4030010500c01c0c068580e0304481d84550304a034407150140c01141e840e100c1111000d07060552000c3c070911030070f4840310000c070710380021038202c0c108010908001d00702404114229032250010f006032071103032090003004c000580007500141500007032107000011a50750391030301904503408074a802021400111941103400d001084200e403e1421040044034441894011002907018a001e1030803501070480140c00305180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 453921978 1250 453920728 453920741
    0xa02090a02070c0b030c1206031509030a031404080910090306020403080a091d0f070315090204031110090e0c04080615040e03041406070606080f1b0d050a17040504 72
    0x102200582e1011035061001c3c02142940060501074002c000f84000603034018201c4000d10b05100c8080b02a465040c006428103851103a0040000c1290050280380003011004000540c03090310200f08004444181400d980070884000c2c00313080c014003243d0410b0500c1031040c40d00001501d8000c0601e500c80d95030720100d81180d0401d9905150218040000e0350b04104e00e00c0140000d668154007a8803203254080340c0010040004210103894408121814000d030086100c0d503669249858040361101708280003900640300a07126901102e40040240c241101601c2c009510303030707840381e242c10300700100110030760406801020b00303080030000042d4210040c05400d000f242540060703040b006114003000180d42002204a4050300204820001742141e01c5020280c800140c03a0983c0350a11814108010101584902c502d8000c0528071307040c5a4000c40c0501e100301c01940c59a80c04d02405080c8107800c03005000084c2183c1c0900c841202040030000001060790203103483c1464192200041001e8550 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 453923228 1250 453921978 453921991
    0x912040b070204021b06041e02090411030102160f020f04061a0304020d0c06031d030307051e0706090312110f030402040f0f180b011409041211030a050403020f1e010f020a0209 77
    0x20080c03004211240c520501ca03061048140040c23409190002003100e90040d00040c80616044958100c0ea1029015038031441c0804043d0304595845081c0341c483c1d492403110492003441505829816480d140c410441a507104450f01c0c04480119031a124003980050010ba85c8000031841c10800910319100a00140116642c040740b01940703444e010000c8551603001000540091040080007a4800c090315407008040605100c3c2e00c01030340866205101d02a006010a42020850030074950442c01c12541c07001291780810240441207031004985c000c00c84149240c26003000800c0162400e5040800c9545600c0000500a0f00000b404421940741c100300f0081082d002c82094107100e22134400380c0c01000700d00b010016264000c0001504c1d408024402080e4040e08072201e5035a034800c6115130f41c61501942129501c1c040c80e14050940d4106100892081c2c0026105040a003003141c070034916070450701c041e6440b61807a00e00641c2c00400c0c000c0740e80114444e00043d8030240c0d84800b5900e00541 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 453924478 1250 453923228 453923233
    0x20c04020d1b02011a0f130617070b160f0201120c0306060e0103020c06280656070506162d0309080408030d0b090912040b070204021b 59
    0xc0d1400040070b00700c0c1024050006591601c03c0400080050607017a25400d42c04a6211040120030f80005d402c1c039580e0010071600300e00d07000020a5541500888403c2e070190b040c01c403a8490750700c103c1407803603205441d07404801c04504400e103400103144582682070248141004100a007070007515400311445002c040b8000b9403900801c11040da08088201e080c0102860b055141c500c200840035074612001e04101d040100003020080025425030145001401d050014400a40d035407041d41400b504242070103403031028291368861010722016044e00d0520102c4035242d14009111f21000c81c495880032507400101e0300b008400c00103081403000c90310440c4010b60000202c604c00300010904000729490091009460602a06c403000080800701c0d000200d15010808003040c0c0742c00e00484c0210390005c17440d4403010482d003015020b15000141ca144003900d03109080c3d50b030200342c941d551000700c0c40d03001c045c90304110034040382603440000c24040303002400c00341ca000c0300c418803400d00d41e40042405461f41c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 453925728 1250 453924478 453924491
    0x6071a01030201081e151210150b070b07030c05041a0d0608070302010504300b0402010212091302090f0a0e04050c03061b070303090209010b041d041110020c04020d 72
    0x150703001313101150001e00f46042d10413801107080e0780084550018001d0409070b13950200300040d9030f03a145144801104102e0075a108240e408590801420049901031740c544070f5900046510b88402c001da814998120351201107135242c03110190001c20410304030307400300001040041407009a11002c13061303070b681a102456442500050240486005421800c15600600420000360380d11000740c800355520000c050304004402c038641101e02c06c2c1a10310345021401402e00809215000701420b208500070380944030b0054625121281501c200c0003802d91003182c100d0103058440f1a03034058450307001e0107000f00551a605500141e8141c01340d60069810ba038a4404001c1009001d001c14107101a05800404650600c4019203842030040c00d94040d10081c081150420b140c1701f07070411003040c2c0d00a442c4c1c2e0403550b1500604445a0312901805034600d000a4502002c4107241440a10454000301d04015010003031341001900c5004519600451189400200706599a44000c0c000c1140840000844 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 453926978 1250 453925728 453925733
    0x51312084606030c05151303030c05010c08060307181116170f0306121c020102190c0803060402070302100c030603151e0506030a060203160e0a1208030606071a0103 72
    0x250714070415949041c0d0410340100300203a9508140c205450040380c1031681c0f0700c0c041c04808194010b48001900300040040c00000741500682c0781c14130310740103100a01a49140c10820b89540d00261161505070703001b01d000704020140180700551242001d46c003c1360030903581d80341c00c829820400002c0104000c01d1201c01c03c121a9034079203a114613140400c541480c10444440d40305000003824507000f0300302c801354030f401d110041c00300c2c0100301d00c0100c1003e065019040028000e40020b002c00d0415641420b030101060b0040000710300465020b50500d01d10754481080c0030294228100480951280c4100c2c10701da04800c3c09074041c214031966000030b02525505000800c550303038840040300c1d9480c0021484400300c00f9074507101c1c0d0350803c200c0400c1c291905030100f49441d18410f0050b202d90710100900401c0c4205004943c0f580720700c3c0d568450101590fa04000c8040020f102d102000806910240001100d2401540e4020001030929090071001d4452405c03000ca82e201840300044041b005104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 453928228 1250 453926978 453927091
    0xc030d06080c0f0904030807050307031806150803040305030301051905030609030a03050109050c0d0b1c0c03020a081f050403020c30240a09081c05131208 68
    0x903903c0708a41a010604103500e01130140c0002a00c40710400c040000003a003141c1c000e4120b195548101c1a02035080329190070b16400030028041058490500b071070000500c1c18001080e103060740e40000155180d6407910082007072007035480c2100351414001e2980016190340c00d2021a204006000c0919600c40074980c0007022600143c01540520b4500f00c140444982171100b900c81d00d505e020030000c0d111314040000345070761003504503502a0b00603c2d03a0400030041c0540542013103a02c05c1c1ca00c0c00102e41c840010030b8480300b05000e0600c4a828914030b400f1151540d4000c0c40e00280640140c400c02042e20011941e1b01000c05005d2a11020114100c40c0006907413900103007910f2241c01401204c0e202e6181c11072405080c441250180340103c021814520084c0e001e00001a484002c1954655120b0300b01c0300d000c0401201c40704e00629200010300c1c0340e0000c080001d03415500441e031680400c0c1200081c0d840c1080584280c14400316010901d503041006d400c54502081045280155a01401015032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 453929478 1250 453928228 453928249
    0x20c06090c030313170a06020f04060e040c0f260103080702091521030c030a09080f030a05040b031305060702030c19050a231005040606090902150c030d06080c 70
    0x28002c0d4404c00c001d141c0345507410761041c03d588030f160141c40010050844503103080122003002e071505100045032005054400002d2007140da035501c0b8240442d20090800040b01c00300203a0350b02051b420700030045036134481c03d40b07580d080300c2e402d55000c1d04251401c0b101c0300d002c3c0c09800c1183d4940000a43c0320a5260100f109a0302c5030280c2c840780745039030800c00410402c415a108101310b103d0400031001000d070080c0140d8040301004022252510304094005100540a10452125000e04020402e00401c044105d544550381501c4551404d8a00080031056600082c104584540c50485690000da0140328a5001d9620340c0d0095454994042907642402d41009940d950040c0d40b5500720002078010a9015019130846510521000c81c078000015075600d103010640c4030b0241043c0646c030140190f01c094043da0240780c0070010030b0b03201d40d60f09003101d0304c3c2000650310038801d034000130490002e03400030f15000360804140c03030406c040302c1844c2e81a103115401ca0203e540208044281e03900b4942ca540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 453930728 1250 453929478 453929503
    0xe09070e09031603050c192604060c150f090b100b04050306041e150504030905090c0912100908070506060118090b0616030f0e010302041a0304020f04020c0609 70
    0x21807401e00c94141200140f0b9501000400740000460002803584062116158010380b5250400346d02c05140b030071010032003442c4240000072500f402c0e041011030071303201901e080d20019254400242c0e041d0725024080400c0c030f08800e000948610590004034030f06e00440e280c0c1c622507000710189090802c030740b0080d02401c0e08001080d0300c00740010001903400280207a0081d070081906819000103030782c41242c1000c2c15a015041810351880c950804849900c03541c031850017035580c0c8810300c3c1c59004200143d40152808131042205022107080b42c0382589841c41d100075405c0886074032244d005e00038816a62840c20581d00d045010404405106051004a510031401d00e000115640c0150145690201034001c560240c0c0c1c0e110090002a00c98104442c410038481c0804d12400078646402010014042e120100141d0a40d500c030b0340c903501038001d84041d10740018052056442c2c0e0100d0211030742000f00280c2c0c0c0131324548075407038468841e44000c1803490b1138000540384500d0710121043c6040b1181000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 453931978 1250 453930728 453930733
    0x705010201020c03040e04050c0405010b070b090a0807031d040f15080102040509130507031b090e0c030601060f030603150e0d1b0803130c091509020f0a050a02070e09070e09 76
    0x8403900e904010003164240c1d07001d036840c40304541f0340d800c00619040d00b03404180e030001d143c10300210300301440380003030300c034080c803403001260b807960b0303060009031903803104a4000c080c003500f441450006402504012000700d0141d03850944000c9080010703064074034019104009a40d034416400314440d03800c0402010301901c00c025840c1500d0000400c410f00002841e2505400c00f04000300c0c01c01c4002d200520066411100e4800072038040d4409515a00c2188100300004d49414440103c0e80b4000c54003101c1040010082c010581c0307051402c1d03540b218031103041810942d54050100001d0040300c0408650385c0014400113407902d040750340f1031810151090040c00e001600300d501c81d007180d511880ca1081540000b145480752107101004411852030b85004041035142c282c04248160554000749510200d0064845003136a14580c080491151802c4d8a049103c01c00c000044a4001c2e002050329100510440d8481c9650b2000c0001010040c5c51000c0140c0090f8010009035507043e0010340c0000300c1401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 453933228 1250 453931978 453931987
    0xa03080c0f030903331e13050a02010f1412010e250c0c12141902060717070803100e010f060f0e040b1002010e060a18110409060e01020c070501020102 66
    0x1c0d83c0c0e003800030302c041c0090135404044105081d01c001707072019100d4242c160a80034200f201008418070400324501d01d10680e16000a03032030120b130440c0340b90495000809030030710107410b03001110f940118030040c1081c0054040e040149007103890042c4000e420201e0301268a50520700003182c081c0b4050f20000c19103064030021000c1d0300e584100c2c11401074440c1000340512419280000b1b890070309a002079102c048162038802480000c10031605d0058090702a02d42d007810300c4049010f00000d048001c0e4008509110020028411a41d075080d200d0340142807a08204040d03442c00120b5100700d0303131501c0c50364040a0801100c011070f074149000d0900c0d9032490440a0401d003004107c03a000041c40c800308020000400c10940f11540517040c0924040c010f5804252150170203800380400e0108141903105141c001483d900440c0304514250603901054105202591503842c2d40404103131505a2107503582401c1c40014025110304070101e101c0703400150b01c0e186d40c801801d0600406034005415a4010003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 453934478 1250 453933228 453933247
    0x19030e03160e0a0504030315080a0308060105030c09090604020408030703090303031a010c0605070e1f180e040b041b06080f130b060d030207051503100b0406090501050a05090a03080c0f03 82
    0x100c00ba94410031070200054a036445040c218098055498000001c410320580810f54410104000d101280292584111034844000450706031004451a114103001409100310074139200c59030b5600200d00070009424151200b440c0760940d0711070031048000c1000010b082040640600071004c1d4039542000c01c5461390114070028012003811350f8018519584c0d280060500c60254101028016007d0700031499680140c00d059403442440812802080000c403d406100d490414100285c0303108050000759030311680d440c0e804030711002d08101c1d040700d42c0031506501080300040720802401d09546808090a220554a10300c0401910340e0b50040f240000348004501c842d5255500300300245d0754031840288a0030b00b2410501c0710340010794406040c42c0c10362112151030000d503018000607120b00c0612030390f41c18030b8900d40c40399100d1240410492482001250f0207040686404080e50030f00d140380405c003d00040d000103858104885480740032441d9410401c007000419104c02035a00214589000c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 453935728 1250 453934478 453934499
    0x51f0602011e0c18060f03140402030d080c070f0507030b0133090812090108011d04030e0d02090a06031101030207320f07080c0114091219030e0316 65
    0x14462440a07803655102c0e91184e1280140c0c00e09043c46a1361850080e490f0b83c4003c0c40c5000090b412800a41070602952050401d1450385000325030003801030552018409c001d80d11048010310342d05000c40c00380220004281c0380351485c24550300c40c5002e00100c504610340340c004100103030000402400011150903c020822409076a880000852504c002c00b0301ea200f203c407000b0030b81000c40f00c0d003c0d1031640002c800e0341c1800340c19914002d803102600c42c0e0300c80c0d4135070b50000810030110380c0b00c456040210700800e0141b0101c05d810303a409403540c00d94900c82d4010030b03160030041e00c101c09840d0780c5690800501402119110510700300b40380541c40d00e80d098803414400e0582480c2030540002107450365507800d50075040c400250000300c06450200b80d0305d2041c5920394215101d814000d026202190310750358454070312200c034400780b080030b0350401090030300f8070240c03070f41c00941500a0b01c01c40b92118001c0c0010703805454068801c0e0303034500e01d00c6c0c603401c1890b0900c008031034210380304683d9080500103000766 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 453936978 1250 453935728 453935771
    0x3040308180c0d0606090b030a0f060f111819050604170f010e0d020c0a062f07080309180402010f050a0c2306070807091202040e01051f060201 63
    0x148076520040c2040c10092400c080412081c075500240702960381007080400e8001004440e2017400c00c015100c5140c0905403200d6209e02e00400031404841d40310001078140e409103024074401c090002d4520106400c0c0ba46c0e42d80150226078210540e121844034528158101d00401e409280300114510310300004a000c600941c000d001030020711070240e50b01410704108500074000081d0082c002d20b56640200b580320812042c0e03180060286c42210b40682c03c281e120070b4104c44644e5640503a0300c910307000740400d869130322451594040e4561124049441c04104540c00740c0780160180daa901940e9080200d0203551071110b0101c0c032806010000903030780203030360f24142c2001d50828a0351425020000c660041003400300420981c00e01144445248240e60140e164a04074822504141c030340d40c00964140008031145800a1642c0c482484060b0403640303d46902d910140c004142c0040600110742560001c448083c1001c0700001000c18002402140c4c50041550b80000c11900c03180320169500c800d117 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 453938228 1250 453936978 453936991
    0x1021204140102120d0b010906050f070b090c1206161809051803030c040501171314030f0d0507022503060914010912031b05070f0302030910020a0507090203040308 72
    0x90046890070303034001c2c00b26040b92102c801203290785034409803c084c001e0550742102800181200c01c0030801500074012503001010b035076006414058980d40f090b1203030900a114800d035020309100c50480e03031a4506030710030801000d40644007500c0e0500340c54441c4030798003240a0400024800340d9006840c104004030a407282c1507004242c42d41c0d40e1490480c0d14114050010440c440001049048003c1d4000f07081524802d0383c8609a0410039403484060480684241a0905240c01103c00060302840c0c01c011400040c41520f080c40d00d04500c2101c150003c0341c5c17041525032076008000d0703030b940c2c18803104401c3c1c0c0088032204950342d440c28007050005810f020003030003d940c5413002005d100148510002140300b0300c0081c403800d201ca1510442104c59404140c0100b0b0408100b201e032100d050901c0d4001ca0500e0351890304002940e15401429010f40c0f60a5041d0f0004009030300d03098541c10381e82003900b4826001030500058500c3c085160031060b9000d8004d0381d206000f0703c000a80c1c0000d01035003002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 453939478 1250 453938228 453938249
    0xa030b24030412020a02130b0901170c0d02010e0604090509070807150503040606150c020906030d050703081e1f061809021305040c031e0203090a030f11030d051501021204 75
    0x54250f800c3c0d1800b0303503050f00658021040740004030090241c0c0c20102d51404151043d0340540d81c3c620800c11140100d030307c20742040e0400c4100c1c0c2e6850801c0312910343c800340149000d80a16211101041c060303800368000611090310b442c1004518401001820b00400e4094002c107045480c0c50015041c510510615000b04100000402d0a000d00c41c0c104502401c1200c1c0e5500000012507000380034205c510600b00d024041c0f2a00150851030041a125803080941e1606840c1510b19035085844040090254483d000545d0000889500c2080340f1441000c00502081005880c0181c420100741c1c00c0d4070403810010000707401c140100310390f5110803c8400f0104003603111040e12203480c080800c01d0f080b00da003180c80c00c680030141341d91540100c1c0312003080c02d6081c3da000c0880626001070388011982c01c200c81d4412411140068481d04012040085900d0140d6a09408041180c1583d01c00d6000914841d114420712040101a03005414883c1090009111594002d8408080750180c0c0c420307017035480c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 453940728 1250 453939478 453939503
    0x3081501051e0c030a03060806090d02210d06030b091b0f0114210a06061e110a0b09031309092a0b040306060305061003030903020409020409080a030b240304 69
    0x420416a5011003e09003940d85810200400070005c00d680d20038006244206004110005000f2500000c65030050340a003085440c0340074540b180003286145005a4103041003143c02c6240d0310302c2880e01840c410a40041107040000301c4524000c190403e8241ca004185c5403c0600ea40f141081c01c0c4103513003820070344540082042d00c0c44160084803c04000d804983e50960703120310340c00c450b0610030440100e04000103516580c0803941045d269403086081703400c50008511140c0a0062202c820070074404072944401559550000f000040e148100581d10116908101d603e40c1c104040c0549915001000000c42540b514840c8010132071014181c503e0000c040000207003001ca82c80090075901e104d507641c990780c901d0301c0c07070003840148025109401044003051032482d880355514100c03505543c5030258281183c0070040184690b01d0103d03882a994004540002d0078100548250001610000745803c00c110603c041c030f20382c03105407481040d41c0105034002002c250040d260030603005005010607 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 453941978 1250 453940728 453940777
    0x4090612060c05130509060d140a02090718090f090c0303050d0506060c0307061a0307060206010e011e031202011401060c06050108010b100305060f06040e1e061c0204110d090308150105 81
    0x8d14070740c05000340070001d9441c0702c00e1003008005103540c2030a200380e0304070a00303540e0814110b4480413000c06115040803403440801140095422940d640c0000e0800064110719951b2504170840c0164401c90105502264410800d4424491958007a005450203440c103019890069200e10034a100107020503038a002c9500c403144280340507602c001c0058100d480c5641c407076601954440d02446111401030030840042041400f0030761041e07450a10b29031209200c0d00f140e40b44088182054515800c43d0340e601c02c0c440155002d00c2109008080700c1e1a00e0020850314103100d0251641600100816070400d21483c00e00d480700f414208043e0004e15000815803100800a0320f901601111036600c400007280115000341507030004e0b40940100400803140094a2003c4030411a048400541c4190381c807140420010040c8a0911214402000001e00b0101c101540c0160b4201c1d030a50310505d603a0340c208004060700039410640000c07a40303d85a1041840c900020300912841504222006040c03040604 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 453943228 1250 453941978 453941989
    0x30b0d060c140c010605030f0c100507051006180b1203040b070f02030a030201230405071502030909180f010b0f0d031205190501050111060a0b01020304090612060c0513050906 77
    0xb690450465440d560750030034040a4040d0940c0d02030188640603c506140c409030000032180d0844401600d0b82600c80fa03014800d507801e030000d120a6540c0c1c01031020707500c05d0039200d10078040603000c2000c81d404c4401c031000c0040f00b1200005900c1d80101c107110325410303841c240002910201e8903035070a101d541d21164034000d08040110407009415214400003038040503019003116204400405690340e8900044c0408000745806a03170140054001c480107104d29901083c8038407404529004403407803e2224070124294040803034500c80c941d0240204065102018030103000303101c8265000340a4000180002032102c1d8035602e035103206001d47c0b07482f50201402400d00d10b003c80412081000b6a103481c40b02030b00c0c1043d06800c800e40c03241c90328001058079070065071880c41d10390721348005044994420881c3c80040551050503415071000707000000307044956009400c040d05100c02013a21140180c034080742603840c4c0c0e0007042c3c1405024003e4081c4981100c100c1e008442d02103c202121740c494802182d2f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 453944478 1250 453943228 453943247
    0x41a04031d0d020306010b0702091e06040906020c0d0e01030c02030406080a02070c030c06080f160815041808040e01150c0303050c0f0304080a0f0e06041e1205100c030b0d060c 77
    0x75014062030000040b070380380d400081c1142318002e1300e41542603641c412204c0070000c46a043c103079000400d04003181040c1032070ba026211081c4035600045c60302c60b030240c40511340f19140140790f0004c7c0030306154042d10b5903d03001d0b103c100e140d1400258109800c10030090a1103500809074210700342d0201d452024010200320a4006640110300c041c107203a00da40b0028042e210450742c0b0310030780c14050080b40b0201c0740b02800e440c250151351b841c904133071140085d08440482e44884103038810f843e0064513900080d4001d5003d44a403088101950381c42c0307081c01540d15100164881c14500c0d08031520a0220354010f041c241c00c0580c903260020700b07a695544850124068540003c00b4403002000f00000c00400c1070003803c180c44107894005203001c8903c000c03a0f100d051060050b8111805200c100f121803c0b00034140c000651108209002d0f985801554050b502160170581c2c90741e00009015102c1c42d0705103e46203500f2040d15061054400410100710703004182e0000400040d40c401410b00494800c0b105403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 453945728 1250 453944478 453944483
    0x1120c2304031a0702070f050609040b240d051e0708100906060e010e0a050a090903020a0f03022103090703030e01110d031a0613060c02060c01090308041a04031d0d 72
    0x51208003038a0200c40d00c6201210b0160262242841c0447c048407840c0002c011110000d2100c2c0c40e266040e018403000c0d15030034800b5038200b03102125445204948041c00540440d40000d026101d51041e440402a228040d043c043d811080d48000380044118405c22980000ca40c00c040d0410346440e2860303c40c1070310740d42c01410000d00d840004556150300c580380001c0b9160036600c114080342028100404400c00d44a02c2d644a071010b182042044410b40148c00c502c0d000307005880100741207848500303401c0d00c024000c4005822201a400304401200c190013000e07000e0040080c114940401c155548003c103001c040c0a1207220141c1c21416841900d000c0c00d40020b180075203032032004e064400340c040c008000f420b680010070040304100350304101c0d06650b0070090011004000d20307e0080251002000030000f030b60441c03010000313000c0b40542401842c4126120b0f0b40c45507802d1405003408020010303154207511100039407409210120343c1c003005000002084001a00048071980d000450a00071003400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 453946978 1250 453945728 453945743
    0x60112061202040c11060105011107091d010c02061519170f0105070309020604050603072006160507052509060602061803040608150a030f06020901120c230403 70
    0x41800d902001c540d5003440c0c403d035020301500500c010b0544601d1103c031303480100f40e48038400400840d803043c800142ca004010040d00c2c040394031420324006942e0b081264480c103170880c1501c0c10010109208101c2d448807248086d1100d4149540407042050098580512030403d0401840d0302d421402012030042c0381403200503101887c0c103120251201c04c19010403410b5460300300014013141c028002c0107040765009156625003800c0008105107900007070907150401c00340c0ca980642400100d030110b04504203601c0104010714000340b108007181d101d8221401003190071b0008070005400040c20650400105a00b200a072a01640c0c5005912003907110b00d007014200b5100251883d004100540201c00848440d002044a641a690381344205d1266400080b51100040d0300212030008407008440010902d030142640c0c0c3e200c9038190340801ea400d5621503800030308650f440d80c000c80384150100082200380031942e5a4040030b480704501101e410402e4400040744802e54101104440c041c541c4401d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 453948228 1250 453946978 453946991
    0x3140708090a0e0703060501021906110d06081e07050d060b030c2d10050a140c1002090108101a0c1e01060312050f0a050d09062d0905030f03060112 65
    0x10f0824080d0002e9406401107403400102003442d51012403008040c0401003014102c013901503403090000d1258480800c400744c0148030032051030100e030007120018030510740188460200d2010040c0a09242110345020381d006520412854860b902d0703140a00b60407000020348100c65001180c1064160000310790710840c070000071404900442c0c40904081141148c01420043d40350034015007080f002c00701c2010407802d1101080d400e00c41e0500b02010540703042180c0c1071030391141c2c00c2e03440c101c0c000b10320322955500800c0181d00707940e00640381030344032181e6895003007060700c0e0903d2508a071180a980d14a40e4100081c0f4a000d400c00700414915120300c405030100312031020400900a00d440d010803a040c002d41200c0c4190f15200d0410b403100e003100c40f00d08a144c01441c40f02915250300c44111028441d49680900d8080742452182101e8205100781c0710a94102d60200b6030488d840314070104030319500e88812100440c2c0c0c0007094500c19142d030040c42d40d4a448690040c0c0c0d40c90700303040c0c01d0703a1124240003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 453949478 1250 453948228 453948239
    0x7080c011104090605040905061321170c03040f0314040308070b040c08060f01060315090203070201060f050102010c05040b2101120b07110d12020d110304021c03140708090a 76
    0x107006000b1521911410030105465004120980b00f410102070b0642e0301c041e01250f00b001c017501d10031208a120702402003001c061a00780c42114202c40019002151140c1c854417091801c40204940c025041c500e2249036161503610803090201490002e170411400e0106042c1025240003218051500054415100d486500d0203c07a03424081f9000c42d1003000b5610005554400040c01c0b50007a640149860801d030300304141200140004000c130006c1840031503002811840c1480194000c60140e0300110305181004100450f080f01d6a10942c110b80c5018052165585e12806960036100c3c0342c84120b030354200249654061002804884125014103000020042c1801c813013a4041c6102d0280352103256030742c0e10141e800f04400d22010041da00300c0703880ca080051095060b020302a4507050300501f0601303040c11280846140e821050030042002080c4015490210203401203500000040814144d150343d000b4501c6584001c80c04140c400822051704010202c001d0303e5800f0b101900c66181180d544 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 453950728 1250 453949478 453949511
    0x160201021e1b0a151505060d0e0c090c0a030f090602220f0e04020112090b0106020d020f010c0e0931031d0109150c0b0903130b09010804060207080c01 66
    0x2c22002101c0d4603060020380901c1011410702916608108040081946419020058021001c01075820240766002140a07034440000c1c00c551400f00200142c10616034220500e031114800c0307414070902c4e030070b020402e91101c0d9000319440301c121850080b8041d02c01074540d102511980310001d0507640080351250702e201283c03100d90f030071880880b00701500b0b40c2c1da4a101038000c0b002e4007854201490520010380954041d07841800718811741c60000844001c16220014184400c4c1c0003000140c000103062040c1d603604000700451412828020040080a01c2e000340c180004006000d000300346040c0025066452003d00d2120500b180300c054521505100380c030300c00d1641007034045022480000d10b603c0b4410494003000d10400040c1c41d41c0a600e4200850180c222000c00122000c00c0b064609401c001121001c0c6140200070344002151128014001300b81e1080950300103d1034040207000a166580e8002019500b00703420000059541010b8141a00ba078420282d02481540c00d00184000c526010b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 453951978 1250 453950728 453950737
    0x91501020c270705030103050c09190e030c07050105130302210105091501080307020a0b0d1d0105010501030c020f06040f080d1407030b0d0b0a0b030a0b010810060f030b160201021e 79
    0x81da42ea40415036904a030540d0180403e0002924552056004803280c0c00e0417005181c200e1101c0700481d904a10908010040d10945020841c580d0808205800f9041007001500041c210900b005401c002602c0ba07504010807031840007a00c1113104015100310782d2401c034441410100c0000c020700c40d9141c07210f1125a03070038440140c800800d18540c000101c280300801aa00302c0e03035000700141001840d0440188050304900f0902c00c1c500c3d680c400090104400b20b0351800140740241c00880c0b29031410002604540c01d0119480540d040000d0b08002c01c0004501c1603801a07100302c2c4050f411080e410558058001c2042c44114503143c14035520209000c94901031094030ba0b640d06015190000d4140000000e6003c030007802c000c4000e000c2946129103400c0345c44096400380c01c03506003c03200d03100c0f4480000f0aa20281040e0812610207604c0706590007001c02401728134005000091466a8101c240c02d03004000c20b01075403e00d035664004c140700390101c81018403001c0301111000000d551641c2540d01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 453953228 1250 453951978 453952039
    0x308070207050906030312070e04020408061005090f0712110c06040c1509060c020409080a090906120f06050411030616030f0b0a210b0f040b07020606091501020c 71
    0x70304070006001c2c0380c40310328288501000b901441c21700c400d2482c035002110001d07100c5000c3c044d004000a055880c0d62020380014802400100b4140c240580c2045966003190003403401015404104250545032040007500005a45000c0000ca104000c1c074400610038000c0841280c0400141c0c000715010008809001d10700451902d5400c56541007020300201903414000045144850304011280c091200d10f522940040c0c404a18440f00356a42400b81d4402900080458190801401000709500ca850064651490580b09141068a172000078009102008141d1030310b4000044c01c00149200c003400a8002070110754160400000b01c407418000e2440d8180000d00d8003e501501e140b043c010f0114080000c0c100b0404d07642404108080038450340e0139240054004115100080c60200c0c0c0740d44035420981c143d8240d810240f40a19801c2c0001d441074045612410600040e03039104043d068000d03103207484070b122440498006034104078412801a601003d44410ba0380000840c1d12507448a08 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 453954478 1250 453953228 453953233
    0x60603060507110c10052a06130305030105090703090b010305010b040c090e04081303050d0905040c080702070521030412121106010905040c05030a060605040b1012111603080702 78
    0x203807407010440d40c280003201000d2580d404031100302e205091100d05004000303560300e8017900d408410f01031041881c000700ca00b811f0103807100040b10184401405090342006a9480031030b08c20310240c80c020424001805981d101c0c9501a010400060081d0b01002c0015800540e1184941c3c2d42d0804034020061083c1483c042c41c14030709064041449040b140050341c641810301c0266032116210030700b06070070040c1058810b0175080b40202c0840c6082000144480c0f156031620b50080c10306080c88252100e03070f1501010702150000b0300811076004540841625000c0d15603103a109081000e22000408050360a111400001004104400f04201141c41c0900498608a518007400d9080380d5140304034051442c41c0e0040e10040c44021010f030021a0098002c460540f5003c0d00c0b600000c1c00d203642d200003191102d594582c10006030500d07004000c2003003800c80310942071041c3c030791000c1d110b0200c8610000340035035a0040c488881c0b110300e00b5180305c51408030380d4103003a903240d14000d000c00e901a00c1010251 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 453955728 1250 453954478 453954481
    0xc030c09100f0f0309020315042916080c0a030917040303020106050a0506070506010b030408090a080c04051b09040e0a08040f0f050402040b1602011106070c0b0a09020303120a0906090606030605 85
    0xd070190042e41045d0303501500038002821001d044c50720300d40c4e029000300e80c07445a031b02c6402c8086d04000c42c0c2e9402c0580024003034145051041c0020380f030713000c40002402444a000c00300a040f5086206480894000e41008642c08401d0b181020240c851884040e18421000c200403007030650540c4214103454060301c800d15001d88410800c501409880c43c014015401440140309040b07240e80650b81191081d0107050614583d000001e0082402c2e80206c40385a111028102c028038050146d290000c5407081071052006c4040c1d003482a0f0302c14851540e0066440703c035044018034040246030900c81c1c104d280c59484540318103416901c00307000d214818100302e0038200801c1d1441d2a2003100d0480d205202c401e0700e0a0000c1c40502c04018403400d06074140018080d03c03481201c401d01c4000d114483d10f03503456202c4d42d41460b003003400550240c400d00100e4901034400006841c000b0486210030010381680711a13a50b104480340c054910403d00522180c01c01c407900003000120707003000c02174912070002400603 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 453956834 1106 453955728 453955757
    0x40e0715050a140f0c060a0e0d14040f0803070c0609050306060f0d170c160f1707270b09060a0315020906030c07020306010e0108060c030c09100f 64
    0x840344c0000d290040c40b000707002884d0b00a02e0444108401c2569451165031151070640700814000c0711070451500110007002e4400800303540417044a00d40d1039025080d01e0f82c00280045404105400d00415600e000750721440c143c0e032001d401002e05913282e00400130307910080e48034690070201d411194000b2600c20404200054141c0c071100d5520b005030b4909519060b00c1007002c10b00040d0205040c016a000882608204e454042c201401018458440d80c141100da40c0b2200810902c2c104007140e0759040c1d40042c02d46400f000040181050700410b1140c0c10f03200b210200d0307004402070400c0c000640c0880324080034251503c401424140c1050201c2d0581d4810340e4080301d080c0010400c801145001c10000b170243c0b14140001501354541200700f0303500c0d0b030085d10a05100c80044000b0340703806070a500340d0710f41040003002480305010347c1c440500310840301038014000540c8256010710 = true := by decide +kernel

theorem cover : BRFrame.Cov 453776978 453956834 := by
  have h0 := BRFrame.cov_init 453776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 453776978 ≤ n) (h2 : n < 453956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
