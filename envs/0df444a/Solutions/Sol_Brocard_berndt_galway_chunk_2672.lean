-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2672
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:23:57.935834+00:00
-- url     : https://prove2.me/submissions/e3ffa329-7cc0-4e95-b2d1-98114acd9ca6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 480395683 ≤ n < 480575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 480396933 1250 480395683 480395711
    0xc040b04090510050105101115190e0f0d08040503041415030a0b040b0102160b0d021312020f0d08030a0218031603110a0b030a0b04020408070801050403020d0302120406 74
    0x71401c28024558080c3c41d2403080401038640c0641d06844c0c1c2074425840c580401801134030511141c07040c521056110100d05042c9282e26540c440c0d008142842c101c14900c0400c8010342504e9130324204150310340002070074a556038810052203203448a11700d020b003401d04094441948030321680c01000040c69203614002c0c0c064035000c1c80368841c5030200c01c00c80da0760726101d582c003001421081358840c8654103090031850250310029402e0400c1c1c800120645850b850620644110f0340720310b0000d0300c455020302c1036050040100c049900282290603100c150043d4070720400002041c980d0080380314481140911002c18460011759903c0070081000682e14114030307817947c11266035082040c5d814440d84003d80c0703103200c5591405040f20710400840e4a00c0006104100c3d042149000c1c1013410758040c070001d01c1411141d0000c1c810120090801803900c5d072141c1324241041210740107804180c0d118424001015810042039000ea40c1c2460118100000b05e0704444e041100a003003c5c1c6a2030f124400861500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 480398183 1250 480396933 480396941
    0xd0f091406070b10090b041b11100e0307021528023a110a0f1703040f1e020f010f03140a1505040b010804020108090a02100302090301050601030e0c040b04 68
    0x5034101000c1c400d1494074008110a82c401c030b0045800c0c8a0400c6d082c082d1a007010300840c0b014030419a020150100200c02c11a0040003505000449108585150000c0c83c664810342c100f00030b810b005155604484e0043c80f04c03c00d41d1380e000d4100b445c400c10aa58180242100e4296501c3c20804064442c07401c0e140100d10b44511192071000d4141512500e00030842c0410001c8500c1102c80b140c1d120708415070718141c42d02c20001140010307a0701306400020001e1007000703050700b000f8458501260300e500f8150064506800c00c070f03070490710307403107640c80030414480d40c3c50a49000542d600c4200c25154510703030110341c01002c1c1070006410b114403a85118481c03402600100c42e180c45008d42092a450000c8120700030f0106000c0600d00b1250414012410742081d00881c016080c041c1c49044903500da0743c0c0112160b00e0000e00c0041d560140c041c0c0d00d401a070740c02c0111185603090b03030b5003d600d03034420008040c2107910282c80241410b00d8010440c000a01c04030b0171809071413017224006121040880414058 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 480399433 1250 480398183 480398197
    0x100614040902030708041e02010503060d050a050111210402130e15070e150f04140d0b1614130303030c03110403060204080d0c08040504050a020903150103050d0f091406 74
    0x482c000300c2080300160f40040c82c144120701034191034501110300250003170701c00d0b680e480c0a80015400c00000f0250708004030030b084400c1c8104121014a4042e03140d05003141c855400780045a1000511b0701c2500340d8000c07640c1401041d03038107000d10508107940040d540b2200d043c2d6009030503841c0c5652462000040c4084203280010590b005100d24104230300030080600b4484c014411000f004040d8020140c0000b84c1c0c0c0d121081c500d60318a000d081c0046000010009507035654004015100c0c04002548030212900804030014400c0002c0740400018090040309090581300c08010312048000c003d1080c40c0700c0c02c40e138040c01c0018403100c00700b03011006422043c900701c8640c00000b800008100566008004942c007000c2510b28035400c505044881ca85203481c0504500818081484207152640c8081d4218011706001803410b02c0c0c56011900701f0184802c14038607016840c00400502a051007502045006860417024003103501c00b004e04191b40500408200340c40003c02c01d900e60311030104841d01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 480400683 1250 480399433 480399449
    0x90e16030c030b100c0506100e18010612080d05010e071e09050a060c0b0603011e0507030b0d061b08090316110303070803090708120702040c031e02091810061404 71
    0x180c1c000613400542805540750085446104140001e203200300c2200c0c10105036401c20703800d2199034440044d02500c00c05502030200c080c1d5a981030010300300d10900045c81e00e06200d810250b4440d62581e06e004100c900503401900c034110f22030104020954803c081112440c0820079021360342b0155081141c114401e9000240c1000c8020004500c440c2c201d00c48400d00d911801e514015036940c0c000f45400c0e40c05c2824144507000e00445d034a010300c1500d8001a500a03000d141c00107181002000041041503041c005480b0b940c0c0c1c40219800c0c102c0032540101c1c2000c450f0078809914142500d41565a104140c0503007502e0110a82540811586070141010301030010122a200c0c1000d0812529690050303803104506c2c07041c01c600003041c0e207000c1200c03041c00041660f990b060240726024400a0150f003d009403c06035140a060150000384c2c9a18103242c2102030f00503110f1700c4010500000d0740000c07400800c51007880c0c0c01c0084903950684c00d0001d69200e4074005160a03103000c011101c60060350000c3da8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 480401933 1250 480400683 480400699
    0x513170f09090a1b1d0d0f031d04020415020615011d0303075c060910020303070f050405090402010327050d120e1c12020d02070201090e16030c030b 65
    0x24415804424206004407500d100700001c3c2921003040741e880c01d16140141442c0682c0b1f00e03200405d008142c0200741200f440064090017400e6000901280c2c82a0410380e1780c010f82c1803842c3c58a5504019035588109124004002c036401d001c0060700d1a030083c041201c40c8140d00e0004a1281c0341401661007083d40803881c48210001c07203c000b480030f107101a15071230222005107425801356100c08400c2254002c4440742c413000e500801542c0c1590b005035030068100c1c2c000c1214000715108e00220107048074050b0f01458490070a0580108051441d2000d00100042801f060120303580c1d80c80e171513070003c0d07090030b0001c0c1c0d12042c0101c08010b08034600c05415450001416202440004030b01042a01403036a2418980448000014115078020200500d0340e40b0828006000d400e0500c00942c9100e1a41440006407042c40001170a0303901c218180e0502540200d03d440441d600038403210003a0510b5990040245498605d000e1250891b001715405c15440740301d034030380003802031740515840341000e0185d85c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 480403183 1250 480401933 480401981
    0x60c0c061118030a03120213150c050c01050c0709181502040602010f27020312040306061410050d05060f0d0303090b0a02032a04090513170f09090a 65
    0x1c2950058100182a6000040450360703a02e40860280d2020383e250325070315841002c031801d1030000d40082c04020a030828903200404c00141a88907805a4580c0d0366038100d40442c10f00e0554284031807242a1418000c0c148104c3e4904900400c0e500c0a490241e500000c25850118200e44184a01000605050a01381c91000781c030311103800800503140303150000d0207c481100340c4001104c10060007060512440c0c601401090b000c1d03440a60b40780e000a080b030b000c260b0b40615800300307a40300b94402c4071455554401003100004142800103880000c039100f80c2c030300403184005012882007070701414049a5450008003a66100d841c40a0450742c041c204644540746841d0180060245d41d00c151a104000b10016140401074001c4911958801440700e46400480341106d040c0e520018100d80c015005110101c0c0d030400601c1024401c2100d506000e031228858145408544111200e582d84440100700c18801c2c02e806900f1111611000d49104d03a00f0b0b0b445140d0b0100800302084400c98002a4032150 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 480404433 1250 480403183 480403211
    0x2070329040c0f060806010507061503021e0316030b011503060b0a0f27050120010207030f35070c2f2b080c0106060503010e01060f0c060c0c06 63
    0x100054070401d0110340c180f1600d8907401d4610080c1107801600259041001800054403500115044c144500f0440301c40360f242e500207009642c4031984030403025003026060704207190400c0454440c403501528580c04030b096444401180405004003600140c01020313041441d072180c0d001c0b10050100301c0003103484104c4480001c01c004c3c6044554800a254441025002607807010000c20100f000081200442c0c54030b401910f2500c07070003101104c1d000d006250a03001d0341c020b000811019103c1c0d502da00d1400d00044020708403820700c5602100303090852800c070f0355204101604c0344c5000c1c15500704200a95841c442150b001c6050700d0010507910b40800040c403810305005000c101e103d1171140c5298480800d00c00d02c46e0700ca03400c0e03249124809642851030900d41c1030030b0100f18994090039200345070070880c185540c01c0d100c0c50f9000d28000340380000100000c9046840303041c05012280b41c142d08030100050001d0146201000180540c0c4e0307581c084040c8035021366612240c0c20b07402603051003525001004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 480405683 1250 480404433 480404453
    0x60608160e3c0102010e0a060f140a0902010206010e090c091519090609090b060402220b030a0b01090e161215080c030706080406051005060c01020a11010c0207032904 73
    0x2048003001105115000c25130043c080d5020403202c60700107040303d596a07180d81d03001e054036080707003015603544070b0b40041d0740701c0040d010501c501c1c0e82010125540085200091a0010580c840e0f050203078944240070700080046520440c03501708440b12201611080b080c1540b80d80204c0220340c3c480302881c400703904104104150700846409150821401d0380d41d420840031303540d880174020b0008161100188141c5056400741030311040106404803000804000040d501055800c03010081201008000d0245074a00429000e00828a8100c201910b0000f0211580303c01904018034403074801560b005182c810403c0d411042d0101000740132180c4001d1564000c00b089028801c91130140d8110fa60b41400c00040c05003c0743d07a10740e00c003901176072952a108010300c0080c01220169003491400140e41e0380d88009494510402c400042e6111910840a05241e9040704103412590412144111198020600c602203d42150038072648440f220301c0101d00505000300441031078038140c2070009000300380c05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 480406933 1250 480405683 480405769
    0x90504110103110307121a060403051f020403020f01051c0501090c08010909050c010c061808040905100302060a0c05010e1207140f1216050a110301060608160e 70
    0x82c1000341c0021550303029142d00c000c95080002c583c1c000c0800746a01c40e203922501030b095450104840741068113001440b03941c415482a2016808068200321200070000040d031404c00c140c2c0114642840d40d80403829003c4070b01542810301c50701040640d80307090400765220001040c10000c000661f10780c0c2030000200b8401e0802d030700041c5501d00200d0542d0340342c45a202460307005402458030941c60001114400103a99003103c4054850b40300026201c554110251610f1050400c9901d40c1d0508200400f112001070003444841d04011041002d611184104e940d040b2841c035142e2010400c82c140280034003804480d006e514458100034004090508001c2c08085100d070507802d01e5208803a00c41c603513409006104502d030f03410603002d02032969002c00048c805000380d400d030b4100304600e684a0504180b1100000d503200c01c072512800341589000e05c0380c0c10181410382480711803810852008020349003800003540034000112420045559142044180503003100c3c00c01541140d1090b02e6001180e00398 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 480408183 1250 480406933 480406937
    0x10f0624020c0303040905060d060f14060f0a03060209010c020a090b0f012a021513300b06031501060f1706060328020408010204150203250303060905041101 69
    0x2103100381005201090041090000900450400f810041120010040034022a030f002c0069014040000c13490300038a112520f1406000030800300091a08488910044c80c1c0c42c401e0038003507110b00a554075030400034103a0760456030043c4c82d002d030040141d810f041e40f100c000c0c1d40520a9080001d00844039013000c80c0d81c0b001a2500680480450f005403032060a203060b803104044140e03082000c1c2e0500c00d00c002d4540e40028030410000003800c00034004c0f540001e04400e80445607503011310151001c0c100300f6800e010750f1400817140c3c110702c160250a100980000500b03003025600801c0c1113540401c0b0510700c0855101010310030b960b503900040c1140c80c09914050105000070301c0c420490355107040d0903201d0715000d040c80d0724503650041e0b0980c000107a031004510303c01050075a6030070704a0714030192000e40209000180d1711340c01d00c5c8400750741e11404a4140210751003000040d05040429500c40d603140f08201d02001040009e00d410f4000d80740c1900030603440752a1104000034019911a010000e442c2070b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 480409433 1250 480408183 480408239
    0x2040f030c180209030d0809030702060d0506150a090905100e010b1209030913024806011a0d020403020d0303020721020d05160f2d020d02010e03010f06 67
    0xb0452101070f80551102c05034943c001c0700b0711420342070050100c194441000000d03a07103840d55542c0003a40e640c0021100210196480042040500345100c142d0b407568000a4100c2c00d0144a0600401c04082c034014195115121800300310410784003c1070601601d10f540e080411580c6075920001550400603030780001c640c4540128422610110894214000c06051040f00d800342c0c1446102962003410441d04040280c85812080e80c1035100c00045c00400a81d00941c50740340c10b850070b8120301240d800ca40e04e900000c00401c402980048026002c4091007031090326020074802c0d00001740510361002c1d4118056480030010190300d9402480000c0c0710b4004070440020100420b4201400d105884026078002c001c8824694083c001030111051000da5907072003142c4a0b65011119698020100c0700b504d1004980d954261520040a00340c241c4283c4920f0315500b186c0019000e581c4050700a414064000c14006482d20290030004140e2000081448100c3e510b820132414125141d1900d00e40c0100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 480410683 1250 480409433 480409469
    0x3080a0315091a042705060a0e012307180801050103060e010b0a0531020a020f16052106070e01020d1d040c020309031009030206061c03030f02040f030c 67
    0x10b28400c50100100000001c04042602c10602000306242102c20000c0604201c1200d0b00001c503880d201d0915101d80050aa603091208185040e60503403000c41c0c00f243d04011440e00d20000003010384902d2420110b500480d81c8504000340c0f0200002c00688074500301c0d601011803494030541041e41224400d074010000910f00503042404c0f00c050050f0103a002a00010801c090b150548894a8281d042111780200ba6140380144105211001411010a401203100c07468142c05201001c0e900c544078000c0c00300c00c0c1900c48801c100d4031890213911300c1560080400504c080110300011516000e54049502500740444050103a9441e8841c0337078010710400703005d225051303c5103548081008038a006102404280b100f040003401100c1c80c07035030071440705008006031540c0800c103c4141004003540080c10030710b1802c0c024105078004001138054041341001207602c91b000c100e028020341c0c0520740018600741440c00000039201d281d00c411a802180304010040c004628456800c4844107030942c480510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 480411933 1250 480410683 480410699
    0xb060105070503030601030b0402390d140c07031403070b0a060614070204020d021308070b03060607110a03021009090509010501050a060c0f08070f1e02060d1503080a0315 75
    0x20031400020420f8100340007250842d4025000943d82e100001d00160400d90184101e260a02000b1b245484510b01c01c41803090156008001c400e519440c1b0b005040d0300141071318003030012007681440c0c00b80c51000092041000c8030034400c602c0515408008409103100c842e1550b5905e4100d050180c2c2c00061103008620f90321498441d403401c940c03a5803a0b04421942950503202c0035004918240d07041a001c0002c61104102c601c0188023100c101c8041400c018200310341c561a0028a4000d5401e5441c100b00b8824196258025105015402501c00754401103805c0030510140b01a40004d410014003800101404c1d000640c040030b90f410410b00300440d5994061060a0b10350030700c0b03456002100c4100034440c59200c0c260542d030050007881340b44443c88256076030011561001c1e00c203032090030798103000304100445605400b000803a0152142130390005030b00007039418800e81200f07031541035032181c9800084d03e107103c0d000300464100d1842c2c2e0b103c2c9510000540038015400d20071014100148010503215 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 480413183 1250 480411933 480411937
    0x21f0527011e02190c081c1b0203030702120a0605240a0b070204020a0512010306060504050717010b2a160b0a230d020c0c10050403050c040c17090a0b060105 69
    0x16089500a01d441301c004152209a18004181540d0042d42018049554002000403031240c601e50010301415488201004040074110040c500100303003901290405650300001380d5008580403140e80032031800402c8124980603007000014811428101000f001041700400c4e88044007840b807402718032090900800000280b6800303119010a418008040036080a40c041d00303a049a508080d45095215500111030b40320903441120410340f1a1414001410240259600101c0a080500c840a20a120503c4400d4140240c00340c0480101d4500d81c001c4205040001c015803898034001e0b030340d500c4149651034141500c1103039501580280c002481803000c0c000c98410f50703c1c0d0b0f5900629080001d01d007019441c000320500d9000041400344a103400c201744000d018201060008041c090750100c02e12a56030141c0114205000b400d2008102007038012170b002100701804c403800203a1603004582074075480c8655003420a82800346040102c0d182000503000d05560042c1f010030000d58464004440034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 480414433 1250 480413183 480413237
    0x305090a0503030415020403021f021b062d070b22050d11150a020a0e04050114060d1413151802010804050f0f010c080105030a021f052701 61
    0x10341c2c010000078000c150410130700d20307404582c0000985825a42e80004640c2c0c201940e8060411900000d510b4405404014081600d100e02d0030322072004100000041e843d010300c110140c12440c81644841120010804543c000480d050303082d5122100c07401d0142800e030084440c0f81d081441c0030241e12690110080702e00c0e03041d502c10010f001603000184212200042c803807035035045200d49201c8094030484d4200c0c9520840e9600e0006844415510008041c0101c3c8111035018602d0100184078407072500030010125803080c1e41050b40e03446100111801020180c4030000300032251001d0216200802e444817075164010002e40c89400c50107c1300f001115600000c005440812048aa00550240303024030b1780070340644141d4029401c1c00b580c103030400e2001140c040c6a6550780c4001182c2c65000140c0c0c3e0702501c4160001d10809181d81c1c0800c0300310303101c0c0242c0031003007a1002e0402c0100703129204880a0303909002c103a07200301b418034200207051030003d04a240440c0502000103c03002421b40c841550b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 480415683 1250 480414433 480414443
    0x1150b090a050406080a080c070806070509010201050612060105010c15060f03290a0e0a150e07210809031c0302030103060f0e071a0909090f070e040305040b18030d020c010305090a 79
    0x3101c05903100b901590000764000b5890156850000d400c52b42802041e00c15580d646403e9070341e460301d400090854400500d0039215640140c600050f03a60300044040c15514203090166404a103030811403202c4c138075000000b403260b041c04408a2258090800802264801d8412002c0718006c0401a00d110001090165141b00c4100000c1c189211940000c03000076511001c2d607160b81e2194407450f44c61a829003503580c80e5601c0d02244800c45500b040040300506407030001c44c002c02050f030300041e207030540107402410340040481d040342c540da800d00c4800c03502c0310a000501c068044002c00038010350800d01c01612907a2401081c40752804507405148a5144500041d20440d81084055074101d28030390010405c8030400e02503290b8548803410414010140c0600601c0d007e031500020a00c1d00d03015070061600b20350600d0901001a130000d0603641070321400c0c2021601d41080c1c011710049565496241c661501c200070884888603000b00e040c0e008803000b0387c0e0600141d600d102c2401e989600329040100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 480416933 1250 480415683 480415693
    0x11040b0d0b04060e1f050102010606080a0b0406050d050a05010c0f0e010c0602130e0a0b01050c0a26071505060604080705061e0708040602060603060103110603060301150b090a05040608 81
    0x124103030641c08458810740041000910a80b61001c0c88890b0b20102c440c80c04039024411810100c0e030b007a50010b0003c02d0244002e000280c2000360043c000c110181c100c840070741d1102010700040d80d680d040500600006461022140001c7c01e0555a500c0c014405549551a040300c44542a101d00c6600c0d03180c00305500c031a018408080011500e00580c80c40c2682d840b03a081c0300c03911030140c04030303407400091401ca182040142441d41101c0e044800724072025040c410100000c54050300042403d03041c268000c81203d861420001b0040c40d100c0206990b196001000104141040710244d40220b00f118118403c00c8150380f20400c0c820340c2c1c452409000b2880d48006800c1203a8600000107146400401d54400f0010b1031304200050185c00c03a690840b500c40010409021855041102650090b8202c6c0185030035403540c2c48266001d0140084d007801510f000000900c0c40e10301b5006261340c400c14602c80542e05980e4481b00383c6c4d54110640d1540304002c5550005072030715280c010503060304c1720305010300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 480418183 1250 480416933 480416947
    0xb01140a0210050c09031b01081b04030209040b150d0309170309060c030c060a050408092b0c0618140f1f050307080108010213180b15090411040b 64
    0x4125038100a0510045220301d1044000c9101c1078054203002d60404410251281c04650804d820284003180d80c07040c044c0c0585140308580c3c0d10840081e000a001c407015003010745140c1000ea0b051055410103904442c6010900041007614200184900c18403840f05a00f401810304108003144083e801500258034010180000f68026181c0c0e03d003010444122841c0001c10408204141c118810310703041a0008500c0303a540100c00d000c0b5076070150003000c0800c082d207003907541c13540140660901c1500524503504000490141c1101d041800c8450f0707610303050212010b140480c840c40300ca0143c13000003210618080c03c1414100303119001d54014104000044920750180320b001c440400040ba44a403002c0261410781100817020440010555104c0b540c074941240098069a8181d01c06c100d547c0c410499524445200103400081c1c420640c0c1e5600c01c5410042c451000d0070004210681c4203062202c0f81c0e501a20301030007001d18042c2a40d0a0240b2524120a4404c0380100d106464080500304521 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 480419433 1250 480418183 480418217
    0x80409180f03050a09030f0b010e01060203070807060207021c0b0603120a080114030a0804090c020c1f08450a200301060e0703021315050409020304021302120f010602010b01 76
    0x41c203403008052601701181c50b0750780c40700801170305205806e940000b40c500c0103100c0828150952030142441c0c2c0011881d01d000c90744c91075254892074001030500ca071702040c09000c40d911070100d2400c0c3c40341828034664440c11400c050b02541400e4802512074403445500003084110b07003055824901441c2c6903148140c1c40d2001d110180c01c8141a0700fa4180500341c0803900144582d005003000e824070b040e0000e8400000c410203031400c040a039202d40314140c1301c1080c1015000e10f0701d203150355074205d240002c0c0580752100f000486000d04983d0414021070568807060104030b4001c07441545090b05549103038065010407042d110500205c0280002e015242d0104104140d005590602c00c009000018000da031560021803c110964036500080c0d00022200c10000d6002c0f88100500b07103c0c4080105400c0306100502a407080e4800c41c5401c0790048001000d55880001c1003e0f00d180d1000c042d59106a10079506d010b448003181c40c0c039180c403184070010415610500c5240401107040c0c450044024008800c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 480420683 1250 480419433 480419437
    0x312090118020f0f120601030309051906110708010e010207020f04050912160b161106070203030703180c060504031406060d0204051504141611070306020702010219080409180f0305 79
    0x650380100784c0c0c0600c80e11684840c41c00c020100c48640207002d541d4110b241c0141031248c01e030b00c5244241790402014248148030882142111018200707400d03044983c00f461428022076500682040d468a91181c00e010019001014a10f1003118500d902051180c03c10044520990ba444a10381c00b1210f03201e0300c1e4003000010602d4051140e030075076140c0001c2d560074400107011030300a89880c100340746800c045500300c584003c900d01901c0c080c042c0d520701404020360ba404014a000205510b50741c40000840c1c180142a400350b8005001106a036140c41303015103198401c0c4000c962451810182e0454903001061040c0240d90051052141d46055020080900006065100d5001c968610068540d95034410300320925155045001a0f10f8030369034000040d064206071009002c0d214403ca1419a004920b40d03060384d41c0328100607161540c2d800104c0c6400020200940388401640c02c202c140500040904200c07016904148640881c140c0d2400d680c3c16100001002d002e64100c01100213801400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 480421933 1250 480420683 480420709
    0x7080d09030507151e02070b0423060a0203070f050c03120408090d030c03110304080715020f0303092b0807110f0709021908010506040911040504020c031209011802 72
    0x600b580c2030a019455001e101c004110381070040b03135514242001c1440c80c0c40f401c020a1042030303000714200115a125280403010080005040a003c0b52024042501c0c0c640d0b00001030070310600f2120340385032041c02040207500c2070ba400c1000c00c5118015942c2644918100c400c0d4108180c040d50500c0e88a590700010710a0142045885010503c081380d1251105d190a8121a00a40d1050214042030130090b00c40145a07201281641082109008c40c4400140000440d18800f40c400f1607003150741800c9040580c44074954a4a01001051100a603c00221001100b48a110003c044040c1000040c080d0710790b8419100071440c0080011007140c000c5c0c9000000008000944071103680103810507091030400d03003014080a40c08038004441e104d501310642c49000c91810f260300c50b54140310014480c1e000700d01c242d405082c3c0310b1020402e101c040c28240d43c000c0c071001e802551151080401c4645a400201c1c000101000103c00036550b007405000e0209503007400c0700058a82500f075000d200300c140d0607032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 480423183 1250 480421933 480421937
    0x607090e0a021c1a190324021b07060203071208090717011a06070b24190510170c0d18110a0603091716050f011a010507080d0903 57
    0x1c05081664986a000d036120800180790000741c6408035111000ca40d8004104d1034081d60081e07441031003401d4201c911105894000c110707a0701d0300e074514003182d034110000340520440500104220314140c0d05840b5600034800d87c00152402540c881c04201c2c0c3e07a000d50140a0048450003a035190942c1c080c405080c0c002d149003040d160815102d01c28005006451045544960b6503589202e00d9402c6140e00300030b00c03c03400c0718141e2803c2c04940790008200b501400d900b0452015001e040d0384180070314805c00c95220043c01d0207054032425900101030704518803443d4003401d540c3c201501c206104041031024021191468a150b8440e030140ca017040d0441609001c440741c0d90764402088556484804002c0c038800d4403180c002202c50300c18402440b4055016134241421b140325000010340c007a116100d50342c520401d494580d0700644d0300220003034108401030024040c40b41001403058040d0040c2600c032a4800411300008680801100c6521a000300540950014841d003145e502c884c0e040381949500034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 480424433 1250 480423183 480423187
    0x50c0a121e02071a070206070b0711100f0506030c0d08030703110d0921020604080f0f12040309150530070306030209102303030412051b030607090e0a02 67
    0x1d85861000050388124503001d0707071001d9404c0000c050501200c0443c10a6110282c1c05c0c05255404a8028000c811008082803004800105824416401c9003149801181160200f080000180d130041c003980c050b801c50b040c28400001c416080018460b400d040d0080c140a030780c08529100c007040c5800150002d010035407148840c074420316803480a01200d040c08800060001c1140c540143c0581c21501042c1c880720280e43c61440e03080d008118558004c2d00248096962500d0a540b101d0758420400307491031000f0007160071a50417640d00070341881036105e51201d151030754641c600c10705440d456010040009070104951015265010a41860804020010004010b0f02d40f4000221101160707428006503954100300254074285c603141e90003070070034241e80d003a0070b051a0410f051110318000360100304001255104d03541d00c040049800a200c002012805d09000d840d10b143c4482112940e040c5010030245001c505240100b600c0d0700039013480c0c03a06d11a0074988a80e4421050005000c2203909a003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 480425683 1250 480424433 480424457
    0x2060a1a010e21011a010801030302060c09150f121506090d0609060c02030706150609120309080304061d06030c120403180f290a11030d0e01060e0106050c0a12 70
    0x600ca68022452003d04000b01d0113042903003150600846101c005810844030800400c04250080380207030b0840c00d031213500c907941c44540300410f0900807645045515601d0000d01400c1001c030310340282400441e0940d4a000f161141e013605070010020306080c0b5440b0342c2c1003100210514051070070360400c40c4610300c0417075001c1c03090310b81104031564885003001581000a0180400c049449035500003503000c07000403860740c1002e41c001c101080034000c0c030a00c20114194003060502645400c001800352400700c2e40d980d40c882c0c3d0024458101e0b00b80c02a01640b840444122038648601582d11038042a1200d509102000b90040040c15002d401a03003809a121031000c0d00c01036030b0b10f03101d01410980c0301084060b4a84180400824203500302001d000031601141078070521760800f15600c4624510b000c0d40542089440b040c00d51040c1c0b09100c1d8002d00d8041041182a03041d04060110b4500c1050b21006030b9072600192118400d2800f6060150003641c02d001c00030744003049880d460f44003880d1038130400c07003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 480426933 1250 480425683 480425719
    0x31b0f190e0f0103050f0f0a080307021f0c12020313060b130f0c080a05070f030218120a021005030705030402300606030f2d03250302060a1a010e 64
    0x4002e5482c203910140c50300c01841407000400034403100030714400042408204614115441d201c1811000b4240907002020400c21b6200708901c10030fa084896500141c5111030801500070b2030802d41c2000401c01c40030003075503804041d1096921886601c100e1002141071a0b48039001810f84e45e9082d0b5104002850502c00e44000d8030516044021a810010b440400004050304806005024140440c2018100111240c0c4440400e0000c0410704000d44c64940060612103800b210010960b004583c1080e402043c1030006500700080d8000d490341c0400c5c03504c4420884251100316564004034000304085001802d0181300800d011580f00c403042640041c480d10041d0010820420385103590041c0c0a004441c070303081c400d03000410914001002c1c428901c00118089020300402c1c1015826070724600000d17603c0c03d100b200d1040c1d4040c0b1103400d5015504003100064400010140c005110300400660b144d1414821914103481f0315a010340070035441001180d00d0503c011000380c10601025918440c20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 480428183 1250 480426933 480426959
    0x70b090708121809070c050a0c061706030d0c03022e050702070b03070c030c0609060b0312041409040f300503010b040b07030315080d030f02120417041211031b0f19 72
    0x81d00c20a190b49d4181d01c0d1104c002d0901442400e42e46070b00c02c0c28011700c8019a00090b07145004052400c005000c0e02043c1070a0341050400c00d0092560f0007a803808040b03d40100e90340d40c3c0b20349261501000039403540c010403a5945500d0058550105003000070030503ea000d5210100a02c2c80b0b0301d400d001801c095a5a801a61070844080300c0454a6000c009038038501800184130154031151102d081c01e240070484c0c0f07566440041c2c0c0c81c4c041d0b050000401c3c28001d8800c80d031a6043e130881d12003013082c9140100c01ea00d000125901c00901d55203070751583d0302188a003007103d048689102d01c1c0380c20a814400c7e0000e0782c1d0301404088050650750f102402c031900c00c19030341030018219000030b07040c100d040a101a054806070075005039158410000c000211124101c11a001500041c0103a15503503214248680752081e60000d841c04070144442d9010801c41203002045403400b60140c03980c000c05000884468441c80a845501080c841c60701c2e4014104102514039600c141d2100c206000c0d52162008602 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 480429433 1250 480428183 480428203
    0x31b090c0e0111060903090112180b0f010905060108040b151369020a0905030f060c1602040e010603030e06031614070b090708121809070c05 62
    0x400e01502401400b903800c14607216404400318041e110501c0e0071101d003610392041c0000706e410f11250010b41d418450316a07010340d4502c40f00c40440d00e0100101e007070640c00000708507150040b86803103400102c0e40605a0007400c2c006c1e501030310740c4c094588880d0b6a048046c00c000b00303000c00310701c0502200741079543c500c454a40725991b90303c00010f172111031071904182840c040324000306024013100619110f02d1190790030070505480700c14180640d0200c14003040407040c0b00ca1034078040036079240c460001c6c003200c0d030042402401507110601078aa4500c181902c8100880305c3d03440580000002032800300c072840c02071400008a030300d1003060144683c00101211848009904141e5456400f80704143d00301c00240540780003110264110f1038006114034040c0001d551410400401951b29801c0c20f0302d18040e00c92440c0e001c2c03541609490480642c6640704c40c18410070503d44500e2800340c0c60428071104945c0054014007100c21501005001c3c070100d08805005401080500d010502c0403910070700c1280741b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 480430683 1250 480429433 480429437
    0xb060f0405041a010902041a0705030f040f0e0609071e110a29061509010201090c0803030406050117070e06130501080d03050c0405310e030a081f031b090c 68
    0x1e110f18000310100c041c80b0580103044032a00c100410321810071417000860081c45030074206907441d45645402e60460040030030707456010401040200b81500700703462140544080350003a00e02a03840b6010040420403e440b043c3c00b00c4c00545112303451000160740c1101102684c206611080d505041583c50112007010a4034802c4614240064204802d40c4001c44da000c7da1800c81c0090030801d00013a2124800641170700c00710070000f0340d030015034003e400a21140d500441c600700100d17a02d145658603a030044500300c03020751070000045240c4100d0f215503000c00340303400002c0c811941040b6040343d490304c0141c03000b6804a50824a2242141d080c000c49000c0d0080c2800f0b4042580c4041c07003d402c0c0c80d0050811f0328a00001e000900098031040151030700b011021a01200400c2030382c800d00d00716054410503004a5083c940070b035a400c2000001807020007151354030507540d951120442e149035402801c42d01999142c40c00c040011413002208215200a6510340c1000d2982d15a040f0003215000030320030700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 480431933 1250 480430683 480430703
    0xc060513170a03021509030f130801061212020d080c09030a080c0102040e1b120a090501090c05130204120605040212070609050a060203191d0306010e010306180507030b060f040504 79
    0x3c040c0e0510590b4400001e2010340106401c06800f06071b03d80c06804550f40c0a5040422015164855002044001c110080081001c0381e12444240107c3c40084400d4912030250400c101e01b407480012819501100386d50b501e0172a440d49008401032ba8803d4030134503418418414640d01058900f030052240160304400160380701e26004104181e40c2000f003006500d4480d109030300c01e100310050210b070700c0419503140b80f00c2c00759075208540004003110b4901912a42c40d09441c0f01c1002000403004068031001c5400c00a010100d030b0340c035000e902c118050321194000c0f40706c031f0318005003194200c075401c0344c4010141145480c3c00c007140c034504003540d032210700001e65002c0b0070003003410400300ca0006400f07140f0180d89803506042d0f40390008805000340b40b003048205585501c14a00070300440c40200030003400e48003d96541c900b0750503c0700c401e000c10303030720303149010000c0c05d40312022213508841c603034404040c2c41d0952841e11880480d1000070840c54104442003050010340c1d94603c9118891842666424 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 480433183 1250 480431933 480431953
    0x20301091407020d050913090506070201060303080901200903030405130603110d080a0c02031f06080105010609030506070f030605180a050a020928080102030117011103040c06051317 80
    0x4110002500c01015904040c480d46406170b484821a550b203042a20b180d41c1c0340c0407114140c03006241e011005007a03405040240030b080399064002d0320481c1c0c06642d561072030b0703242c400082e4201c4034800c09a0189a031413a03050502e030800c5801400a56000500307403400e00796140080b40d0401c428000000c19141e440e80b0a00c10484c0762404a103910030180c0d041c4c02c2c20040d80d03940403064132840c5104824000150f83c84021540c2c2001500303100701c214035586000503044000240a00b1013400340d8041542418000f0a41c14420f69110044a4200d4010410b0303403103545081c1c4818410414500805440314004203c503100d100260a042c0700100c03101566161002d11101101c0d400741070051110300400400229595461160f000b141068510f22501120a18813400021166100c00c6403035001000014581c13100380d01d2a4100c202800081c031600000300c0036102d07544404c840c01000700c2c84089060100b035210780702510009808110039417850317856641c80d002c042425640c003401d23030703101680ca8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 480434433 1250 480433183 480433211
    0x120a180f1e06020a111905100e0108010b0f0a080a0209030118330b0619020c09010905040305040b0903031e09010e0307081011120405030a03140f07030e03090402030109 74
    0x244004140300d2001d4a84564030383e490604400c200e90302c0904c580300c611949070003031b04540d0514005100081c01100115402e1101900024800048a0110b170101000042529803103041328045284d4141c840e2400c20409425504403402070568030f8000e900b032003403d146403003d10621f507041c0ca142c41c000c66004114904901d03914035080e1440b40c88410020311629640314040d0b500c100068100000c142d1700101404200140030721030b0401c0c0170315807107085008000e0700858258000c1c1d0055440c15926a210360b028400d840090718010f0010701c08200800081032244041c001c4001d004003600c1c90040c0090015030543c20b01e0f400b070035007818001900f07145903802584c1030001d0002603025107039091900300c081d900c0310000045005000e403154007022103801e684003161244540c0c4125500a4103082c20301c41c4d6650800602c1c0000300317240c502444411050440482e00c110313030208200b40c880d075643ca4120040d00c605e021040b21848184000015551746002a40c0a450800b10014060060f6165 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 480435683 1250 480434433 480434489
    0xc05030720060a1e0e09041208060d0b0615120915180303150a030203030a0f1d0f12030d0c03020d0c08060303180d0b18010509120a180f 60
    0x440c6100c1d4034108800301d903440d04844c01218840d50b010b00d030070941c1902401035030322880000009500c410380000700810000c00050310b000c000d0550382c40c6402669904280039410007046005440c0c101144001409460500c2c03070002040060400310303040881d50f030036904840c081914a0950381d00104140c90341814507028041d413000000321501c20402e180c51002e41c4a11028095175030000c81e12001003070580324801c01d0801154050100ca3382c512402c1b40041c100b00d40c00c40724178000368111190003d90711004c0012084030800602440340100300504111804810038941c0145000c141b26491400d01507104010b810b000c16200075940c0c4091580706801c544482401d00309100d0143e050100c0c0f52400800d403045480c4c40205502d110581c000011600340800d100180440aa5020410300e8142072843e4030002c40341e0002800103440e418101502d61605901c1c3c601104003d21200c0b40d218810a03003c4000007a40c0b603d034600c291031301c45000c4901c800d5000144011440f4110300c4200c012008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 480436933 1250 480435683 480435743
    0x30702150306120303011d0c1b030c0106060c080f1e0a0f080f0103030f1805040203042a0605090f01030204090614150a140705010b0405010e10050105030114100c050307 74
    0x201a40c510340c104030b00038006c03a0030900c0024121140d440012350800f4480308503902d5060b190071403681c18000d0200305940380d214048a0b50194201380c000551240070341d682c480c4d02a80807000c542481507521000320301b60409841c400e0007055200c6016444e07020000100440b43d1180d89a0064010b06030010f8052100600144070810b5001c0041000c640c0c00304c0c0981d1041e025151030014101c030501c500072481e42c103820484e8403c0c4000700744010004d01c903001d12400780700c0344020294940b40c50003d14800f1000c1c0301d5280460001c0024024a01e0106ea0750744008405050050400e900c0e8070f0440102c485a40204100c2125545511840e14205101e980e2100c0100980c524210404500403e26400001c500d2803c03000807031284100f040c2900a07402148020744104110340e550840c90f00300074001e551814050300d0140d400710315035115400302e074182c400c02c00c40c813020701107224207105500c01044188000c1140119035000061024002050b041b809101c0792481c14030304254410303501003002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 480438183 1250 480436933 480436969
    0x306080c0901090e0a050319090b270a030501090803042d02010e0a0e07021605060c06061c080a0507060510050108070309080c0d020715050f0f0c030702150306 70
    0x145444219620110002d040d60540c00c00420240d81a504062030080300e580010722500010450b0310b0000c2075142442c0b10380c1000c0e40c85014803951540f44450074070851030048e00c0c003101d00d540e0807548006080040c458600c050301607045560b5989426007100c007030403001c41c1c2c8040d000040c40180311a04503001c00ca14079154198500060450081014415442c0000d05100c20000301c42099a0b99000e010b00408032010050700318079003000000c0d11407107801035602d0f21240149000c81c1509000c0c0039585101c110000400140d20742c98100040b00041814000b1001001241c000000d2000fa0103402c2200c038940740c1a4607022a0300d014416200028002031210034842d2041160b07a0307001c840c01e0b8214807541000543c510b00c90805108501c0340c07854a00740c5110387c0a2410416900042a0707040f1003013160401070801d007190342101c81e031050103524041910700b48082800c0000c060300404070105020110707440c1041d00c2d40400c080044001c50748122400201c00c010850a00ca004c0c0108a91785c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 480439433 1250 480438183 480438193
    0x1202330606040810050a02160f050d03020c071205011b1d0301050714090d020306160311030f1b0c06010e0a1409100b030c031006030c060305040804030f0f0b16030608 73
    0x40b00a8540c0c0e0741414000c0403580d51950041401e55065a0444482c400008e500030782c0c0d9845800c20401481c500031040f26140710704024000480e00c01e209843e29801c001c0003500d602031a102103054038580b40303c41900d05540c0d42e1084024103850a020118a40301c41c4c40d100400b114404034611103582d01c8140f98001e9041c4010052040e612601d490005203001034081d48034080040441c6908041020094061107080c051041c8482c0380400c0c80d00b00c4980d42d805004548600f01c4030391181c04180c60312001c005514000c40d100caa40c4001d070b2803d10051074070700c0c0c3c2082d0302c140b051490325030700382d01c00d01640001d50140000c5000c4c074000c0510200f5416960651410590700701031b2303204240080e420f1200c1c1e0350b200d5000542d40a1100201d0440700a0890303024001d286000c034014030143c40102c0d65078080c041e001942502074040c1600c1960001a0300782060700e562030703441190000060441d2401d00100c1e890000945c01035156000d60058240070040c15449007000d82201c285805c0b001c2c882d03001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 480440683 1250 480439433 480439439
    0x12150f0907060e01050f120f0a0e0a0b0f0c07080a030203010f0504021303021909020c010e160803030402010f09080109150b150304110105040e04080901090b090d120233060604 77
    0x7200309145100320a20701140d80300e104251212031030142400c0d0081c0c03211080b041c0002301007904660350084c0040c0900f08140c40181140f5543d5201290b8010204411440000c1c01094140351035980007440c590100e10b461150ba4990040c2d038004001c01020a0780800180410170340c02e01900007604043d1011407400c0311000001001c803245200c024828000c3c40000441114042c074154014118030031300b5900c0b414940c43c181d02a242c15540c5c0080761103000c03007002d040e03070089103600e084980c1c0340e0103940342d81c40d25001120103514580b50071040c4425020b002171540c109119090609028040b80c2c040200c452440d1170594902121592080141c092075000c00e40001b0b0440c0d41180d440b844504a041040c0700507a05401964842042094150308000a01040d40018145c15409a803220b21183c0c0344c44504d01c190103001040c42d0020613840c000400681c3c54440070084080310700441c0c0050544c400c41d1110105e40030030444203224043ca20000b03040d1504145070304414101c9902d820b05013 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 480441933 1250 480440683 480440687
    0x60a140112150e0c1320120a180c081c0212090609041517100612030305150303031f080c18070509130218030c0a0501030b12150f090706 60
    0x41001c40306442c66070f51107a80030140743c03c00c0602240b0380d0240ca001041c0b40c0d50544040100185074954803204454020f00f018501c800c0202e490152609010b90b6558640b2100e0400628007040012604003480c4001c10101d642c06070010010010040100284404501020002490380d11448203550110075030700c0d105000b41c13090b620f1052064400301e441301c0701a00001d014107045082c10411414404000c1880100d007503105582000c15811114400903800503103048500c0c0e880b5002c040d0066410400020744130b1b400c0365411030700b086403c2c594481c80b81c0009055030f00980b4480b02a25003062000847d00b54603641d20000c103401405010b5400311040400c043c01114003448140050910005407910302610a40d0411100078207003055403480094100000c1d804502c001040144030344d0407a00c0c82c540092544a428400317400e001c4e1540c680340040d00075000c0d494440341d0020b800c03014008814001c00165900311001c1e1074071040d600b040b00384d40c5c40195010300120040c0e00b2690342408455 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 480443183 1250 480441933 480441953
    0x803011707051c050106030606080c210703020d02040e150709090e0334080703140a140a090e09150105031204031203061d0a050106030204031509080903060a140112 72
    0xf100044803880300c10814600780b401071040740c00041503103142002c080390500e000600101e0482d070a503043c04416643c44c03241c0c400c0fa007000742130b5142d81e40040710500050800c0201c01da0f40e1440508045080ea987c0600541005e040b01603040c1d1080040c4104480d044d448450b000003800c8800c010040d8561481d8000d0f141e02c00c2480c0c0d510f1402078114650103c1130f003070f040000100342608442d501c3c1c41c4c0b50f01c0e110220fa0320090042d40011140400e000101c898142114501001a1600001045211400fa260390440720845040c406601e000258aa2141c00701314801c42103c00a0400603154030310480c01d40d01c0680083d8000d500540070b20400401c40d104540599030802d4015403001d8491342d0440c00b0303112603040303021603c1440036070408041c04104c1d11070150391104010310030b503a01d58800320200d00840c0320141000c642641c0c0000075036040d43c042841c56006071085031034129250302191402c81c050309c1c1075403000d59a80003a29007000390700d0520302511015170590318014268841303c00c01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 480444433 1250 480443183 480443209
    0x90605010b0f070210050405031605090106081302010f09080a0c090f0605031f060506071202010515010f1809050f04050d020c0f121c0e030118080a121503080301170705 74
    0x1703040740040721910b4900400030b6030000c003030080c2118003424200005a52035900783c07255a004840e80e000200303400c2c1c00749034110310412a14104440000f040d4004649009008940303c09022a01034089140c81061050740840381c0540740e8852107902d464808400c03034080d21604404145000000d000594011541d1903009100c202d400b00d501d030010148000801181d44042da00181c001051010022103600348100090103030000c010580e200b21071020796103103901140380020112140a00400d018241e2050f100c02a03a01c10b6507469112414582180d400355620885680c104040000300302c0c080060051508581c4041d0100010b03c4000c214089080c0030014420020441c1203000004104002c5030b42c000104030410700041100c9015002070860007a60b8000c0d4204281200e01d4000101d02c40002507108d804545040e8084100b1030710074502c0030b85484041c3c3c40740700c4044d40700307046c0200c6009180110300007540c03945000c41d81c1d0540f03900c0380441c0100e5000460100304030b648480c0e100800e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 480445683 1250 480444433 480444439
    0xc0f090b0708041e08030a030e060619050d06020c12040509071b1401020903161715040314040b0706050a050a090f110f031c02060601171b1606090605010b0f0702 71
    0x140741c040100c51074400c00c03980205070b0030310022800e8501c0700e605030401044031800106654180d110141802021042100ccc4061415021142007010b420404172000301c40d4003d10300103040c404002c01440c1000d11081a0300100080403605010a20b8440d40ea00e81120860071305000050b101003414035031a60701c5101805440c403482004044080039012144068001007e584c2c0b103079012064004d0080c1c60380260101c00903000c103e0200a040001c1d403d414425564080c0c2d8560344e01c0d6811150144500540c940860f0f00b8040043c04074982e901501c035881c80ba074000306040c41c10200d5070701100c000500c01c17295a0705089072000030442c06080380ca00716403c9601d030b0300707107918240100e200c2c40806c0c407600780c140c403500c03103039846e1901c1480829090000d1035094841a031505001181c0407507203c404881c18500300d0000c103032000310744c402d0388000640f05d0301702c281010450620300c0c100c81c200c41002e540d460b0b1a2501e1208010030341c0f1656016050240d042070170b140020740400d0300d074001c1e500000c0c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 480446933 1250 480445683 480445709
    0xa02105403030905010903030617010b09161403040807110d0f0f06110f070c0501020c010f1d10050d2703030b0f03030408031206060a080c070c090c0f090b070804 71
    0x50501c20f402c0b0410164000000707101042283c50010020040c0380b01301110b50300030100201540e041800782d10b0b00e011000b031540d1190f807120708803444440c070040790440510040580c580400308a20001d03502c03a601032005a916100ca50801c090090348510705948102400280e00e4006244d07013852906a0b500020190158611440d01c070004000742a01c95003072040104111190040800090045031b00c119000c0c514507559500581c3e85d5424100d17039030f002c201031140698185200d400c507401c40c183c400c07115509802d10400071400030810910401c0000d1400a006000d14070315001b0802019100d4564012a0b04d4a60906103d40012407000341055110041c400c106c3e81c500c1d8009080c414004c0c2600d540e03503036603900142e40b9404940e02c450414401ca000998030316256040e210040700315203450155035200603440c40c490f808100105c64100400d41c0c04502e00c0345030b1003842d40700900c07515030800e6404100009400d040c2c4540c41003c00c40804c10032440000c04001c1590700f1501c2c0250b44103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 480448183 1250 480446933 480447101
    0x106081f2c0106090b04050408040e07020a020627030a05100b030c031603230c0108040204090f030810050409050d0e1c0b06130b0102120a0210 63
    0x1103000148034003001c90203421001d004810703a0640c81501119056101040407190b26020f00040c0c4404803006401400180300402c01002d000c0ba42c26486007051042d43e40000f595800107086030000d882842d0f8046101c06036801000c1107168100d214030044008150501059031500c0d51480c00310f14546000d07407500c02241c081c7c5c604001d01c0c1840140201964058601c0103580302d540c12a138030059421507a44402d181d010200344c10b044480c4c0503000c0141400199880055401b0714003d4800c030b0308166550300c2d44011034141e0300d8018100d8402c1e65012003d0a080160030704102c102e4100b03034800c030b03c2c2c03c10b110300260000802e20350711100350500740e044070321240c00a18204403604508481c1040325900c0002c020310814614401c030750455052a1480c81c1040c00c1d000c4442002d8038074090307844054061640304440001d031003880314510480300d115079101c00445c2a205402c80610000f484100d0100107181108070a00700e1108502402c5042210a00b610380300c00c2c42010303444c000f1040e0358042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 480449433 1250 480448183 480448211
    0x30a050a150905030d150b070812060609040e100507020c060306090c160606061409031036061404200103110301150207051215150406030b04050106081f 67
    0x200b030a400c80141d07501c401c0300481c0c074005056140084880094100f10105d0f030055a030707050340c0185030804030290800c070180324003080200000c0c1c40113a20860900803200c00d99214000c0e5500070040c0d201074095855020400e009480c4060100720a54102c007600704040c3e11a038003580d0348040100c4818007c0d48030041441020312132100c04a0310a0610800c51091180640200b002c0f101e09541b540206900c3e20100000c41c0185d401300343d415003180400441201041e0000b4001e12409811840340311030709c840030036400b820101860201c1003200e15241c2444051303c24028a000c0401400c04949001d035101e41a044008580c40c01070f031802d40c01d1500b144d00c2644034411503080c219240d13603203586074140824072042c891001001032080c148007140900304410100c0400603400014218014a2000042009401410362111904407500416181c0e1030303002d200015805800c14000c0350038079007090790a450107900020190b0703001a4140c425a403040594031810700040b90f0000d400d2134000c1030303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 480450683 1250 480449433 480449441
    0x40519020708042105120f031f0503011b090915060c060e0123180c10030e03040f18020f040b0c0a120819050f040206071416050f030a050a15 62
    0x844da282080b180c00e40881004440c50308412800740044802040742c0304480d007940c0c814008060038041c020f1001c40ca4028950400d0134001144e070a1086000e84c903800842d0850b4280b003103a100b10384001240a4296400c8005200a0300c90180240800d0900c84090ba001e0b1341d0900c5440100207100c1741103014080c055000008900d11140207205460b948405100240180d502c181e0f4504d1000b408644054925051400060440705c00340401c04505006c22a000034020380940a164031010120420340e4240000c20140407040c07402c0014509000035008500985508407000e01d20403c10340c0c0c141c5420406503000c9030510000d40346d48040352624181000710050009060b1550307170030030412898024240307134840c0c1c62101d11542542900c0c407080d0305685050715034188903076a541c003240150400d64001c200b8503000b000004200106c803404103107441ca80c10040c0310710703121340b00c0d050059260003212a109200d0840003040207941c2a12480e85810f8070000041a120011441102ca0009500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 480451933 1250 480450683 480450689
    0x50903032503080f040f02100215040804090e07060806061c0e010603060b1c020603130c08060106030c2a020307170309101b06020c0313030602120604051902070804 72
    0x2500c10040a070100a69a001014a00840100f2142c0c030000e45a02540802c1d54852500075035849041001c1c0d4007030100b07400a03894a58118005d0102200c4420303c070403100c1d801544162002c0303580301d14241044c000c4607032000c6850781c45d40004030100841544041c00c207800c0b071011034216581d1000400c900110302805040464980e00344558550130b400194002421240200c805119011070365007001031300c805d90ba051004030840c805450016040140c0650b80c0049600754002c064a12a00d81780030000c05540300740c1040d8003031b00042c01040d0b4940190045034903141844084a002c28004102c030800509202c841c88100c00c0105040d5502003060000038404941d8540d070031b964dd092415100d600c100300c0c1c1e074000c0402e40c609217403803803282c0f00403100d18902c034081000030000d42d070701c01c400b80d1320103901c0890600c018490300300201081e03050301000b14814a0010390310211001c5254003027a00401d054440d901d0b050030000d080440d54120164032104481c0180c0d40c0c049454051110f0040350 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 480453183 1250 480451933 480451957
    0x11d06011214071205090712050102070803100807081b22020307020a0b0609130308040501090b10061e0f0f18030b060a0b0c0c010807020f0610060e0a0b090105090303 73
    0x88200703080340c5807070034502c0e000d41c5181c3e48001104e50654000700607038905840b40243c9a01c504801c00261100a62003000644520005880c015084d03c0c0c0303c51a40064a0b0740090418103903041080f130604229000042232001e01900c0c0c190040f40184401c2c9001841d160301076110207004480c0a48810f902082640d01918215102d0400700402507584540c6001100c00b6520403001c51a5483c200c0c03485441a020100140c0724458185d404603011b41024100712000e40d203a5910b000001d5011995910515000001d801c04500d0102d00411800c40115442040d100e0000e9070003010b64000010742c45400a41001140107000140490700180040d0341d50208080415002c0108a44032444902401c81215070f69081ca450300c103481602e11886017100e0990744507011240c965402104121b50114450041c0c81c402c00c003044800e828604100e1300d5200010041205014072074008007401c0f850f01c416203001107803c0c03d29a54003501c2c480e0b0100745060100c08144240585d82c1002100d000807420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 480454433 1250 480453183 480453191
    0x1302030c010e120706021b0d0507050607080c01060902031b16120512010f080115080309091302180a0c0306050d150b030d0906020c0f011b15150f0806011d060112 71
    0x4c0f00021f483d11600e5081b00030b656110307003526440386000101c0e803007400d4026000d044064980410000d00741d00002c412128920306021841000703a0a20941e4014501c8040c050307564500842c20700d0036061000d803032000840c0b051000032149405000c101c1c10840d804401d4074030180c12080e05840502544014181c880001d000106048c145900010b00320b50001c0003c1c00300f0009540c0c14402007009004085c3c0c142e10a0150440d03914180d258550006078142c0c025455000c0c0e50003142408140d0f80328241444050b03010301c282d0414030300c10710300c401c409071408005c0c4600303200000e030407443d000c113000e49079030b40c0130101d02c0342582158840c54034000028125030701e611409a01902e42d0725a442244054050701031142941d00b45160612016a016500c081c3c101c0507007c140740200b0510142030300d40140301c03c0301c0c01003416a0f20601c50300041d0180000c010b02e02d401c500e804c0000c8141c2010b0300c07a402010040101c01624000c01e0f940c0c04594489404a0340e802c1d004071603000100d100d4040300b900b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 480455683 1250 480454433 480454439
    0x30102042601050705181503041101090b13060c080c190302060a060b030c0a0306050a0b1b01020406020604020108090f070b030405010c021609090c030b0a0608061302030c010e1207 79
    0x488880540002880625102110801d031107031802c80f10116240740100324204160180e54041011441100308020501d150180441c03424503800c1d003040703408075950100d00400c0700c0c00d0740c0c00c075401400914102901034a0405004400710954440d072181009006000c4410b5080007054002d4800c03001e5550b0848030320392040d0b902d070455040b02850a5000d40291408611241854000c1d001030f19903042c80b0b20f2035a12480d0041c80a035006200102c1050368418000c201a03440320480d01c01000c4a154042d111040b1902144400e4205107611440d81e104002c04c114081c1c000c1455035000d070302401c200d166550740b00803445c1040749440322a607850061110120380d40711a400510f010b00d005a000f00051003014000340e0b95080341048001c0c0c1a000014100000000c0c5d0f0403c1d4160780c45090105034095403035a07005501d15060362103030702c4540c03109014040e814040095907031004012030101201c0d041500800e40b13400f01510300d9810031424007220b00c0e00e51202c003108961000140121802a40d03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 480456933 1250 480455683 480455699
    0x708040b0711190503062d0a0c1b021c0f060e06070909140f1509100801150b0405060a0e0303030a06030b0c0a210902030d02010911011707030c0201020903010204 71
    0xb900c0140070744a4029401444844100d00786000152440034000340f200b5100c04001d8504102070103001b034165410076503484d00146d044e51802e8020b140ca00004200e001182c3c40c064012801d03240e40e18007213044982c03241c0250351542c4081e07507466100035440c568441c084c148411700c441040f90190580307043c48100c401c1038a00085103403107621079688000100d503c541e80c90080d50140e44001c00700301c0303240012541006822110a402c080c010045000c2c04503030b840410824281252050b501508100040082000a00405007c4110591000d448509065000285000c0ca02034507020f01c8020603600c1c2c24078003c0d050651031450060469460745404039100b8003600782c030300049a09411403400305501c2144801901c4482129403a2981c110300200600301094540341c0e50010301545504100000d41c03014003444d0550b203240d5002040002050a00404078080c0d080c00504001d0204900c600b009642c80e10181c0000c101e10340030440f000d0801c0124064003581007003a40c19440010001503104c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 480458183 1250 480456933 480456953
    0x6040806010e1602030304060e0304120c03020a0906060504150c0606030b06040b0603060609060c01090c08071502060601050702130b0a080d0917210c03040e0117210708040b07 77
    0xa003500c60700700a0350781d500b09680e40f041242507905015074024404030b800212170740c0020b400a40c80d03008580c10a556882c1041c03001d45c80300380176500288140c00500541c2020b000341000341a00060a005061030050300810030321462061702e50801415055003810340c81004200c40558108006011860316824841002c1310182c42080c408e03071508509181c076041240c03d607446684010b0110381880092005c0c06041d6200000c0c914455588640401c001060302140703602807c20580100441410038105140d10030030024008107552104040200d6686d1100c01c45500c203a060780c2508580581c0ca0003034018000e8681403941c04145401c01040c5480e0009140100a0080d914081601c0d40c501c100601c18002141c40401c0382c01030080c40c0104d070030030314600c0140e04000003403924003c0104501da0454019401c02010519218010004580e00c001300c0b22021030150080c2c070302176403000021000c040044a21000c03041d8003003819404e01041c2010b940c0141034940703030207039180e00f141b03010241c42d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 480459433 1250 480458183 480458189
    0x5070815060315060102030d020d020403050a1211070b040306023603070b03010e040b060d0602030708010608010803130e07020705150901031d0a030507150e1e120d0f02090604080601 80
    0x3d1003000342600c541e0408080290054006030091450035103441c00c0341000c0d6000c40351103110250200300000019108000100056000c4c40303010410100c41c0000811100d116418415240d1000034284013a64220007143c00312540510016074a81d040a8242c1c8104103086020b0350810106000300c3c000f072104400d81040c1081102541c00707035900c61101000030b000a00070603c4421410340014001840804580c3e000b51008100030031a02240d40c508090744e00481e10b480000360240b004105094020100c6405428008080c0d0306090500d4003a0103418000e100c2d03104100a0207001c1039805000740822030280c075010348040000f50b4210b0840307850758448101103001a01c0d28085c880501c0003007284440c0070018501070400c910715505d0803592904110b030b05403120303956402c8240803183d8520a00001242c1100902542d03a203d060001c1007812040150700741c0d4100703041c83c0b41d001c0c80c601d0843d404414680030000e1402a12804040240109205650040400140401c8407280000c2080c12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 480460683 1250 480459433 480459439
    0x622150b01121d0d2313031209090b04050115080402190e0f060a032003101805010506040506060403030809030c0f070f0602150403030c0c120903050c09070207120507081506 76
    0x1211318469022180180000000700e0804800103042c00b13204884001005043c00f1000414407503502c6c0d40354680c104c07170000040408070b411580200581040c03401840c0c00000100d40800c4950300d0706280a000404011050080121040024086503204034100d8032419520300c10b03410054590440c210021001c1d01c1045850709400006511307403510070701070f200740c2c0e0f07208040f010b5406000306c41085003c9071210300366140c090304445e803661910a100b08010041e00c800c52014480785407c00c182128000b91145004a01b08002c00045490320340c200c3d4100ca5040c07400401c15039400c0061401d502400c44d00920b24083e4800c030f581c00c004002242400e0311554081841c20550300c0c00141e982c0c000070486013240913181400240468083e0344800d00303244150030600015400b507514807a0540006203d4401f0500282e0284180003041040e060030b08010783e00c1134031906114102a550307055074446c60180100c02100320040004c1400503400422a110840307a40758410040c012208204407402c81c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 480461933 1250 480460683 480460693
    0x140a06061701200901050708120a0209040c14090f150a0309050607020606010914030a02030106170d11032d0a0f120207030816020c0d050622150b01121d 67
    0x1000c6100569150740d581c90b440c011480d000384c042c0103640c3c5410440080c0c0301c0410901060041c000c0149000c0d2003502703440c1005235654045001c2204460742000d00a0401c030112500404024046d004c030307098224200c0e211100e0058910025001400d01c5914144084000c519051102d4054100115032803194080d0341891b030310308408903a18007040300c046000408110b401c1151000100072002115809016144046002c3d00400e080d42c6896010f1034001092a8001c010341c0400c0c0800c1156503214a0084e00d0040801b402c40d80c2d0707001d14000402c044170030382800000e06c010030030910201c440b0201450703210101000043c1c62681507800389800b24440a42d26055180d2510888a215515854001d443e40301c90019501465888440500b544120948500b480d81d031003c0c00804035101c0d41c010700441c503000582902138415460343c1d20100c010300c2c1c2c8103000945219034404c5002041c0c1400200c0000c084012030300c000c00240031018041c54040001c2c600014031440c3e03400d05054000b01c030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 480463183 1250 480461933 480461951
    0xf09170702040b12030d021e07140106060e01020c06090321040504051503250b0c01060519060210020f0d0c0804020103050c1801320c120a0903140a06061701 69
    0x10030304492100d821301030b400410035030506452541c00b42c0400a0408408405185008103207c003541c842c840035a0321528036a2241c000c0c0c0c009004640c0542002d29051a034115030b040083d66901e14142000d1140002158441c0140c50810075030101ca9030b6003002c01c0d5000103c10743c1c0c4916500c140909800b550515002410b04443c103500c012160300c000d00107164940c01403400f85840f035040a4642110402d803c00000e40311680380142424020301c10000600d28900010400a039035a0305040ba40480ca8070000c103e1941c0120350000072401c5201c000d81d0b0b9081e10711900c412403082e480c4c4c04004628000006410320740c0710354000d02c82d034401e0320f0410158032111113000e018014882d5240b01410305504150300341d4802d018a1140758020700925500704859a076110401c0c03030340321000031105030104600c0340f5140c04000e4661440001985245806136100d002000803640c0d000c05041c800151074034218029080102d0025903812900c00c2080076114201003402507a010702c0022658240314080c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 480464433 1250 480463183 480463189
    0xb070309050117041b08010c020f0f0c0a170309030a030c031205190903051308150c0301060906140705010501060206011a09060904090f06050f010504061d0106030f09170702040b 78
    0x780c00ca4800c0490800f20f075903907640d5000c02e02c000c4041e00404440000c000000c28030000d0207400d0070b11509802400304500545822440d04030788c420244203990107040740c03138003d0f11024039a40580c0c107030b001d441512621490700d0a180d88140881240c241c0314a030700900506500440441140d8460f40d10002c40ca903184d6881e0003a9403041d0780445042080d80390b012103200d4594498140b00d071007820a9400c02440d0184155a0201c0390310904050300044018103a1401403403c42da1b114280b40c918a0565040c2035004102000600480301803098454114811202000a5416039a0311500a12103582c40e034070025283c402c2031043e00d0181c184d005c00c892038040100140d40d40c3c80c401408040c20040c0c20030030030014005c141010761314200030524103800b150460003602d2103007002102250403545002c0500080f03c0740c039400b41c1c07155500d24541c1141c90888a0002e411603140786804100307501684460002010003103001000b00b85280114400c950b808005481070314000c98042006514503824 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 480465683 1250 480464433 480464447
    0x10050a060509100b130911090f18070305060a091b0e01111b0d0b010f031109040b18031902011e02030c2b02040602030c070801180b09160b0703090501 66
    0xc2d9254070f80c01c0324418402d16003440040c3c11510302079501d04043e50f0ba01d207510012902e0040300041f01c014002502d164605150719a403425080c241d42d07071850359031407121406000310041e104a00f0551500c01044032590384000000c0500121a010824614011480c45856050340a031101180e82c0b61401c0d56258041c107041460300c0c1080d8043d002d0200e8410904514031850100e40e940b044440b000030300803c00181c170180c0038194908041a4003070540c2401004c0c05601c0c506244558036203401c100000d00ad40b1803241d040521640c2003112034000e490240d0442c0608004900009898480b0080780c40d4150070440c009c2c035120065181010310094644140d100c110b40905d4441c00c00c02603505800f052005010003031b609001542a1b40814640300410ba0740698030140041e44040350184490038180414801011148002c00114880b038003c4c0800203081d0f14060580440c1d40d00140b54200c00380b00b40d8000e025020080010140c8511443e05039800c0403909500250340403102080f030b54000d0b02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 480466933 1250 480465683 480465691
    0x10f05010e060a090e01060902040b37050901020c060a020a021206090303190b100c03030b09070e01052503020a1a07020601090e01020702090406020d0b1e1c0510050a060509 76
    0x910029541810b154901414010380305c03800565940b04000307071102081c8003030400381c481440d079540e6400a2103800b540c01d050b42004000f203211071540c804400c0348080c140e903a148015082c103135120410000141d08003004401119042a000107500003416808640c00d601e440c421103110100304080c800c42e40e030701c040480d5510302d194000c0010a41c506d903103c0386186d6141c02c81c1000300b060502a40400c50306c072288985100852004a004c3d020140c0501855207402e0046d80e0b0850355251403000284480d0b10801018140000000c02041e0070b82d520720041e04072109020721258a000342d140085d950381c030a8400740c0b1a800303102c2e06184000598a1068001c01d002d0303005043d1a420018803000134000e00c40010060b40d400c00c80303040140c480c40080e070f1156005102c010384806801083e0800e580000b40440c0c411415448c0101281c94602c000d0703200382000380c5004030345c0480c44800d0a408500c035400074000d4806c2c1d5100324081c01c002e4124500c02e00602106011040d5607105015800c10305171 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 480468183 1250 480466933 480466939
    0x90706031b08090703140c010f03020901021b0a050301050432060708070c1e0212151f080604051c08010302090412090f0b070c080601061211071202010f05010e06 71
    0x41c10030000e42c8034414075034102c00c4940c00d03180b5440e45d83d660748580003009241100300350000900c005180d030300510031584441c170a0809610b01084039000075280d840012030091000180c0503280c0c4192100000c400250101178000c002c64109820181d14400405030040100b0b12404c07000c0102540d880000400803861000900c0c076a256070000395140c2200401030380800040a107024081503014a9014940021307041c0305154030356500600082000024251582c1d61000304034000301c025440d091030780704542c206454009145e4010f82250140389500458580c801c0506200038800080744d121112580c500c1d075009104010340382510080e809200c0694084402e00c009030220300540d4500300da15a20381303040d500503501c900446c4400c03105a00803001d082030200300b400801400c020403601910317002009082035894039500030a501020f8240000044c0c0380d2505451a480300d0054501c6d55600007500c41c5240304c102c100038020003100c8013541020f4101000092605000079030280281006 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 480469433 1250 480468183 480468221
    0x90902090c0306030a020a0306090309170309120a0501060e1f030b070513150207080601090212011806150e031009030e06071b03050313061e080903091809070603 71
    0x1505481c035182c000a0016805010311803080740160b4441030303180d018510640c8001030b05403181c02c0c010b02891403074114041c46030a402d2410031415000003034481c40401241d003401d4a02003c1030880c28441c00d500014015801c144022821080c1c0307012603480380808540c2d5000c61000c50b5610036000c1d1061201501044150001c500d0312441100280049a040c8007103864665070b0f18210003411072814440001a000100180400b040030f02ca003e00400c181e400c1941080300c0144042d50120041c03088402c64031408022690040b02c98004200070140c05030001d0402c1340c8120701814246030842001d104e4001c040f9107540e19890b0348580c1c0c0f0715035003540c0d80702c007541ca0382014445107a008000c25101b120303000b804402c1007202c1c0d4a440004c0d5110710003860301c2c0c9101a940e444049000e81015040c441e41c8000028406003420843e01c6c22100c5182411b480d4a420104508500c1016591508a1030141d00c1c1031030f1000f22001c82d4010f018520032103480e1070380c981003142201e80c5e140300008107401c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 480470683 1250 480469433 480469441
    0xa02040501080a11090d140c060c060114030f0303010b0a030f0c020a0b0606072a080a0807020d030921030801080d120e010608060f07020c0609010c0b0702031606020c0709090209 78
    0x20f964044145800200401d51403c0030b0180040ca5410038800100c601881481a5503d4101c080c011542c1e28007041e207407582002800c4004645400c03050103101941c1da200d09602c101954100404040284908140c2c0d6495844139850640d0740c0c040312a000200f400c1010341c00710000075120711600b403041b03540034150070396042d49c1d0000c200b1400703409142c0c001024405040812001e00003009000c0d0b000c2c4079007036071402c16050081d42a00030b9001e4070190300150480004118210700f200c926a0741151a20250b28240c070b81541c403090746401c0031f1301e43c112001d4408840c88025440403481d50180c0c5031650282e98425800e81d94500c498003d000103a0503044d00c0c070b100c00302904604100d0a480f030000c070b17015440b070300d00a01d00101160b110302d00c1d103501070900c450203070103108000b18640141c1d112850250032100191109205200081c00c2da5140c0001400d00c078403d03c10f850f29a00b01500c142c00c0c3c0c404900b4040043d420000b080c1e1654080c600000900443d01e02c1421101680500007181d240d60b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 480471933 1250 480470683 480470701
    0x312070b060d02130c02061b030115080a09140d02011103070507081803010c090f0f0e070809072d0803070f080309102d090c05190503030f0c060a0204050108 69
    0x1015030b00301d030005000504403001203020300a000c00700446130700400e000e25001c50795155080e9044d601c203600c1d030750810040c003100003c0a0088003008580c20b0108142e1105d400d007a004081c845805031a192216284919040020405483d821107560080c020202180440d503490300c01610303583e010543c200810000640c02401801100c4090740b00f00b11082091700100313080d1101400344100043c0d1017072083c441e82e940020410040c00c0c110700c1d039601481c1400b86121310150040c0034a000c2c0304803040055901c600411101010304841e10701000b10003031000741e100b02c800580c9044200030101d4140401c0e16100001034a070495081401906514015280d040b40ca40c4040c00550080c0212001c00c103107a05940945030a45411508005401000760707028400c40d441d0954241711241440c0707040011172904403607007064800032180e100042042c1c403800300844c0402c0e80226003500002c940100100b0256020303284409155042e20306a54601000b40b080b403285004090208910300c01150542e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 480473183 1250 480471933 480471949
    0xc03060601020618162c1332030c0c01170f09160605040e070206070806090a0204030b0f0a0c0906020307032016080d1b080a170103110312070b06 64
    0x1e40135015621240995202000003014a4021071407105038290280e0300490284541c0d00050082d070b400030b4640c02c00003002a04070f000b01c0d2003d04075444c00c2c296078071003107151002c611400e0a40080e01c201841c20943d101c2d01d940041c003158825014540404116502654001c0800d03410310000310740e03903562481c1c2404041e10280101007a0322400380f200d42d048102c5000308001c2e00c8940c0351755440381d02c0c200301c081c411030300102100115041242070000c41600000216000b407401caa541c0140d5441b01c0011000b03025540c4050f100c3d0206400344000c040081105070b00402d4512018441c00f58144c4064480c26142d20920006a004103c6680031911070800c01c01506c0080e07031030b041012107111340c480c030f000d4010120940d810031040c2c2c00c11600c1e604021100201106040c1142840d000790260008501c007400058054030001444000451140e2402075808186400400303103540c590400e40d006000641e030850080c0305100550034099000b0041e5154541e0160041c8000c1c1e960a007808000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 480474433 1250 480473183 480473221
    0x60c03220b01091a0f040f060e07080108060a110712031806060302030d090b0d020309011805030a0306090b0a210b162613050c03011a0a150c2009040f02030c030606010206 75
    0x8a99420300800c5100110034052b008203540d40e80d04e9000d504100700c5604140b0094007681d4142d15010304003030221082e070309842980da001406d00c0c0c841d410501060f80078044101d455070704a10020b44440400c00a54024025a0b0081d001c441d0714a410305426649603085000e44c1140450910107090803000540045600201c4240082155030480000e6207400740600001c0340c9070341000c40c50554043d8944504030040c0440302080c40080030f0040803075100c80303480c010288480140a01a04c0e01150b10640c02c0446500031002015403501c7c1c4d201d80d84100c10ba40071503000490f108840c50501042e9241c07080c50070484800300002e83c5604201c0e07000b405804008950b28020040745c43d070141d03002c1c13107180300b03124a0b0380c4c00303034507080c195000c1000d14266034001d0604640c40108be00c6600364442845d00302c940d0300508506c4080c098922a803000307142d0100e121381c4402194200400c010780e07401c1c081c0400b07100b60121413481031280105510345004407540c3d07005900010004070041c1d039007a524019 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 480475683 1250 480474433 480474461
    0xc06071109010902090f10050901230c0c010f0509010813020d050d021b0312031f080f010237031112010f03020f060c060c03220b01091a0f04 62
    0x255040c0345000c6507001100340c0c0082140c40c2d020a0b40105400c240c401079a082c5030444945817922101c0318040c01a0049036101c40c1041180070741c03006580e8020007105401c890440c07800d42c80309152441c40c1e56400990419500040c070349103003c5002070041044e02c3d40654161030707010103603442084040103030560300c1e0207980c069962000280424000d21160746c514640768082c1044904104030180010502e2441501030b510607541c0c0100c48038408103882e00300803a075104092035107400328400040d5441e500a40114040c10b0b4440d98900815801441140d01c0040d01d1800c2e00607644030400c030024800c81d0090a54080700c5e050303002522a07070120301c00b90313450711486003007407501d845c843c560b004240c2080c4400242d1450074815441c00d2800c1d0303141104111a030510f04004210130b56110707030028007846080180400454018520101c03001d2400e002c3c01d0b60700c1d18080301800c000748454020312401c1032492500c01c2007500a00401800c06241c00040c02d4640f0324182001444000d0110141a0b44 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 480476933 1250 480475683 480475703
    0x60f08090730061b09031109041b0905310213060911091302030c160804181a010504080a080306060d0501030506070305090d080402090604090605010b0a02150105030c0607 75
    0x2510041da0302d2180362140070b1080020000355014001c0c2041c00000c894000b0702020200400005401c41c900c00f9901d03205554411050b02d41c1d181c000049091003043c03261006050b500071407a206281d20003807260b00e000e805080c548124504a55050b0f607040521409000d20002c140c001d03040480110000032009580095002e035202e22020803604c0072851050071001c001303101c041c10324010981c1d107440303c04503500718035504104055045034460109200450000c00420708207100041c1c0c1518010312401c5a1003080e01480106140200500c040c08100f032100d0101c0c900041d4819815501070340c007960300514440310107454880041c2c1005141b82e503c0002004080b61098150058500a5201300000c1a16060174040a01640c5004101c200b29a01001400000390340c801221600301d9011380d56440c071520340c100070070090030600b400078100d80c0c10040001405455200213080c070745c40035400d4618050b29484c005020260a20a29515511640b00c50020b0f191a800400403584240904c50f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 480478183 1250 480476933 480476999
    0x616031701080d083d03021305010905090a03080711071503022515020903010f1506020d05030c0a050310030b0103060603060b0301050412120b0d0c060f080907 70
    0x86a4100c240c0004002c2c0c2c0141c8000c801040d00700003107640085018082480c000b000e4021503404141d205404601004d03c0751031903070030000110040c400f45402500c1051650764890700f00e4081c02c003c0c0728441d91149401c000418554010030385284032985990b80c1b07151515089421032740c089005003850881e01505100050b20300007080604038106140c1c0340582c940320841c2c45203000c4103020720b07203000d0300491701e0120000070344824a4880c000c48510300107071034100304000700e8010003c4161031202c043c90424a01021888584800c089440303580c200d5241440500084402d4082a18a024a8003040c040890418041d2001d958030400444001103001e949865810400e40207920079600165074030010720520a0a0181001a180940c020701481c202551060251080751810f1800c01c0f00900f40940300450941003c500c207000107004a4807002581407030503101c002e501c1058041034681c1d00c04d40c03c26004400551003080d0400140c0390491070070b1004080403011401030064007090340042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 480479433 1250 480478183 480478217
    0x100219110a0b0706090317040c060f1b0b0402030705041802090403020c100302030a1b020c10030b0301020f0d0b03152a04080d02011401360c0c0507090902061603 71
    0xd440024002e041c0445c1c8910f05003005403086460340f0025900214075030410000c07540e42e25400044542c0e41c540516845c64190013100c1100d07420035144e85100140c0e1642090144004c003241c06940214103590760740d9550030400c01110050000211034110f0f000c0309102601d1710b403c0055205000f0700585a480b41e600e00000d0210307911030895000b00c1c1c1d0200a003e0b44550a22500040e184c071914074042c2c07800050000781d40c404042405621801030100b0841d1300302e10941010204603030150095480d800000b1469016030400d46981014a19114402c85a0301d00000c082c2c1c3d44e11094aa052210380700c10000c1503648018034411003520310200310321509451988003d00003040345202902c1240d0034104000e0175a03110380c0480f54a0080d01c0c006100c4040d5a840200c0c00b0419000e81c4403080301031800100002481484140a803843d000c86501d016400961603503640d40b02d0019110f0041d11038075410219900d100e03028ad0003071410b000f42c101500401410900150203414002d842d000c100c20701c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 480480683 1250 480479433 480479437
    0x2203030c06050901200d020f16110121020315040e101415120a050703030806090603070b2205030a0303050f0906151c050706020f1216030302071a0c0306100219110a0b 73
    0xc83d009d410b1600c00103105001100c060101d41c2442d04aa5035149501d488108201c2c5224400c14140e0000c0482c0c7c2155904901c40341d40704002e04103010f0f048201691548070035001034036282c00f82c24403c164840703580d001200c902c187e640d4038090050500010034010710015083c600d224900c41c00141c40c0c0428010030182005511030f6603202e102d443c201040c024199009440c20303009601c065001d0108840480548007070301038183d0300c0b8a06081c9004c40c2c03680b5148a41c050740e0140510780e102818941e05402c034900c100c1c00024442200c0c0c0b14a03028030703603400b012104041c1c0009909138510b040d16041c5000980204031340580400d4404a4441c03604102160f401040903030b02039400c120403800d092110202900400d11030b142400295008803040c4684000014101680051254104882040340c01c407090b81950b65424145048020040c03181e20540d1014451100a90401e052920004100100c050b00361010040c40c0419031310541304450400090303910288422022030a2009400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 480481933 1250 480480683 480480697
    0x60807090306050112060c0507030e0f0604050d0b072c01051318060e090102070218040c0b16060f06180908300117070b2203030c06050901200d020f 65
    0x400742990396286c0ca498421200c0000f950340c1402814010b08001c280c00c450480d0000105032031420400c80140c0006105100e15041558024102d00356282445040411180314805a07101d494601400345050300354540e00440c121145004004080c0070b5500c2100030305008840c0180c1c0c0c04249880e01380103801c1407441202a1359040c1c0d43e00e0300700701d80c106030141140c0281e46540214a460b140e500403581003450310700404102107502d408182007000f69161040140040c0c40c6d00780d120f0181d10b9020024001011702660681c0c02c04448001d0b005691103180200c644420480004440d0700032100051701c0c45860948201e842407200342c0c1000c80c0001545075a0b0300802940b10f40613010444041070a00607008114108081a0140c0e014580065400c080c0c9403c2c220541c0c44400e104c140f13420f28100b04260702001d42181000004058000c01c5001469104110901043e81c0f03c01e6001d00701c0d01c0c024040c115130444511040c0c2419660001001d095000e02009807821746c2d80001d203911344c6d10081e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 480483183 1250 480481933 480481949
    0x1090807050303040c050105090303070602160501150807151d010e04020d0b040f0204030807030c080705011112160e01112419020c060408030601030e060702011b05090a0608070903060501 82
    0x20802c010030403842c0405c4040c04090030300c941404240c9004c25902d008040380107204990005801f003504030030502d141c224551150081c84581d400c030242481c0004c20388a5541035100b551000f2030256910b4040b0020300400366155140d0815016110410107148070809041c06403d04640026413034a000a0195900170100400c0014020b814407007152000510b0356095441400240b0001d40305d0021910f4050f054500109413040c80e04040303615220718a4010020f6103080c0503240d0b40000e6070081c1c05490fa02c4503501c20a65150329500202c254507030020300003e40241b0003401c5560180c01d2485010174103000b00c0c1c210010324041812004016180c6010700d04100d0304100150003440c0c00008040b00c4d03002c0940c01c000002c2c48060742d03100c01402c0240506000320005e54264480c0e4001024281d03031174210341d02400c01c9000a8000e000842009030342500c0180700d203100d0381c005c50888010303140103002d01d00e601d49440000c69900343c010301b002040100c8601c0000103e0080c0c05500d01070078000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 480484433 1250 480483183 480483187
    0x120c05120711121303020d080d230a1803080c0c0304090b0319050d0e130207031205010518010306020c0102190e0a2c04210c0611040e070e03010908070503 68
    0x154568545400c2803c003c0c0c0c600420010002032543c0c100c0071a044903419111400040158540f440fa01c0c020414444099440c10910411420611040d2005010618000d48554031074402e100240c1d00c040c80f035030180300c515840c10b90000b44141e07000c1350300c41014210682042c020740c072902e00356401130340200d25603512100308102626061101c08020110034203045034600050360f649403104e058040080910803540e02e03c0d00184c8514180b9503c400c8011030071952500b41d45030250411101d1010301044500e803900109441c03d1460020b03101d0007d20b40c580f00c89a10f16a40e00b80690702203409501595003d200f8031400c240c1c1154110780114168444035074007050801405400c0c01e280e440017134500180304020464495180300b4802da840441c0c40800b40b03540d00c0c240b50001d2081c5d004031680d201d4005c109109416030254440d4103080c424074041c0610007000300400980e0045010b80d40c1025004d9003c1540940110107003109560007800219003580c568a0700407443d0407c031310aa542da040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 480485683 1250 480484433 480484457
    0xc19320d0b0402180f0c030907050d0503031509091e01061a1c1b0e030a0804090213080604050618011b0903050c0108190b03100203010801020403020111010b01120c051207 75
    0xb0100349400c03164407004130a1a4a000d00c0f1030074000700040c00101c1840d20000100701083d01c18006c50000e09006000d11101c01c00a04e8031507500e1f482101c0b440c0100701110703030110442c50003401faa8010204103008203000a0108403000982980e040c03000714540d80c0e0b0000248a40e200d514a041c00b0010310392041d11104e10302c0341c40100154210080c2d11706032a08400075900d400401403004000c0e01482e0208000c005c64001c6480d1281030500502400004a800602c0482e80d4000740b040308540c1d86d40c00401c0b6552032404d41e9418040c0c0d00103000d90440300004e003a80540214007200342d19482c00119140c0980e09881031249c00b600e8540000690600c800d000340b00d410803000c403000d0310a04e0600700c20f28000c05080c0030032034010305050800d900c514070000e031554104110005044903047c00c46d034950f1f6800586000350700c0351200324042205c0e00040c15482c0380600c100d401c080f0040e101c250514130341030000d41c002c0007a0b80e070f1241031100074056000c21070742141d0003c1c402c2e1780300e8032201c00c4031f01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 480486933 1250 480485683 480485689
    0x31b04090f1e1415032d070506040302090a23040308071707020c011412012918090a0e06100806010b0405030a2d050c19320d0b0402 58
    0x100400c0b0b1403103590400240030952680e0452031030744144d54818042c1c1c0404c2d144c00007420101e800125103244110110203003c02c030050400350088441e01000c5400f02641c0d00e060010f40d0040c0e200203540400aa4005010004242c0000c030f03400c81c44d00c00b140700100042010040c0034401f52015400141d81e14100b00409801c00250740b4202e54040b01c0f041c4516010750002d40e81c60358201c04074104010784000d60342416046050380d030351606d9990881c00303035a1030300004500162181000d0807030368080f0410b62646034182c401c8904003a0000c150043c0305c2005002e0090000c0c0240041d2009a81c44411010161087c0101401031085605030810f031443c1600b0035103044d01c1a045410549000c00003000a65000240c00c508184e02200001c020304015200b41a01d8545010418891095070b510b030040150101d00941c00131001c4404500d2001c45c551030441d000c0a030300413a950304660500c01200d940040d85a44c18a031405000162004185008500c49200225080f9440d01040c414441185 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 480488183 1250 480486933 480486971
    0xc03030c1a010b07140c0a170d0e01020304090e03040f030602130509070e040b0a1a032e051e060d0606020c040b010e0d150207140c01030e03031b04090f 67
    0x1020380700c60280c03a50600c015400d07a1301c503481009207007449131a81040d5000c018400741801800007040303c00003d50f6058640c0e12140000d08408030b40c041e400c030b03107120b55008072150546500b06030300540c01c0a080a9104000380140351401495100a000011b0084094460100a54406c01d000b50311902e02d207812003400d4903c0c2d005180b080c50500b00b00114150300003000d12103031300d0440d4003155032603039200400c110450720742041e80550051582c0d44581d16902000310301440d2203140345950003250070104107445a00307a200700395101030a07108003e103280c0388462050412280050060b0f5503400c20001d00b441e440000181c0b00d03e034542c4401c224664042c0304501e02040d00303032014000c0c04909400202100d03c242021440f0384a400c41d0b0001b8400c84a40140484e41014021540c80381181404144008541c03440e1a042c451001b941ca030303d503c280129800e510f5620011411a1920140403180905816076a206038400b0700002540038054014540318036815040011320011504e0030038504 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 480489433 1250 480488183 480488213
    0x903051914070e06150412110a1703090904030e030703050706090803030c030a050c16050604120203070b010311040e0111030a0b09150f060906030f0601021006080303150406030c03030c 81
    0x2030700062000c0000c3e60105039040c2d8031000c11141903120190083c08000c2900854114160140b4144410800c01c40c00110f188180c04048848024450f80d80c00c1484420300c1803d403124545c0c00920026119040ca061220b401500ca030600500c0344100c0c2c004070349041d14aa1040d1413562100208100154000c401d01014000103400745240d4038100c628a809448058503003611240d840f000144110b005000b624442c2d050160300c0c2c41060020308000f99031315800d03036042c0c030822507500c401d03e01e45000000310350029511070081005686180c41e030740c010032945214143c002e03031034170419000c9841c203108032143d03181d20400d803903182d003840c08040c402c0350442203040d402906010309101d03e9200880d4400050b8404454001044103100003141443c001c560300c80b60080004801e21214210000f1014400d060aa00b1108001d100102c3d20301610b03e14412420f4a402c00c10101e10803170031640200c41140303400b40010070b0441ea695980309041000d68810380c005840d0b101754400308046c2081145030f03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 480490683 1250 480489433 480489473
    0x406150c030809010e072303071d06040603020f011101150e04060e0a0203121606020403060c080f060a0306050405030f28170105010507020a1502210a0c030f09030519 73
    0x15004004c0c80c40c5541b0f4419000740045c42140f403800040042c80c074808520000c5000c2c05503100a075035045a0313200d03e0f1480043c2c150f0103500e64001142e5060a2240a00b1640c008007050000c2c0000f900550710305c1055152194655211a11410945140d1010780f00500310800000b04134a400e0030150125004003440c070140d5001030344a003001d03940020300110071800e9003039080d03507450800002c028032079022500100a140080780010a210b499800180706050307644607404580c0e10030310704102140c41110203e0717110b12585814008202d0715801598450301c111300b1249883c40d0303441d00400036041072190100034000890308100d00e0b4890102e45800b000e4509000280b44010103141c1c030714180501805040000102d580c01c05e5545080429005000c040070945911091141c001d4950003c00a00f19958029001d1101012041001c80300c2040b90307075680042c04241682c003103a040264407407800030440a41008030101d1018130000c00e81c0000786416202c102d0300391031300d04414003882c00b003089 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 480491933 1250 480490683 480490691
    0x616020f1507290112030f0f1d03010e032d0f030403050c2a31091401050f07090522020a020a32071a03060406150c03080901 55
    0x292981c10203003501c1080b54480c03a0a000740e04040d2042424079030141c5120205a50200000343c0c803026002610700b05806a40d0301d071800010301d082924080c0d00103844070001401e040b0720820a403001d1001521005008001051300401026014070710b40101c45070258542c0b1900300a03a0719120380ba00000e0701000f0f911981d060410308000c9100900000f40041d0032b100d0002022504000184400c400042c1844031504c0440741c14000d61400c0041c0c00441801041d00040d004008001c0882103800d11040941c031140820a00e8001000791981003800ca500e031040441c0b04140d0b03002070043e28030401c00d00044046030300d080900200390108907444180140c3c0d001ca03000c0380000b9603900400b040d500e12130026946080c202c40481c6000e24208018040b041d0000b6100ca644514031103240d02030390290464140c0d1088100f85940702c941c2e0b881011261811a00e5006005135140e0240d41d20034030042000504607640c40380855101442c280040c0040d84880902e010145c200c00750a410141d2580204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 480493183 1250 480491933 480491959
    0x20318070e070c02100e030a1a091b04110f04080c040b0f03030a03110d060f0f080106060c0303050c0702040f0902181506070c03170403140a0f03110c0616020f 70
    0xb9003120383d0400060300501e108010580c6142c050303600021b51040140440e0788440702e41c1081001c801407040b041728070707140d40e00102c5c80364100010b980c034440da0940c10708c041065040081000800646101652065080c00500d080881210240c0002c01c0d690010309001c0141c00304000403241c001d03800303500c0354050351401d0300c064034000300752569024181800214241e840201d42500c0c020918813070800e0b0300308400801d01a42805400c011650307000300c3d103a640d6490360952400d86085000303180c0010070720500c041c0400d10030703000703a604800350096240c5401e0b03281c1c000c98180c45042a110a60a07100c421800450800110041d2084c180c0214125030f0300700441c0000495070f0594420b07109010105550080c025003c0c01a00115070100d24200c488800985500c020382291005a521200b04030000c0f906c1036011898542d176543c401c030a1540700d140c582d4150750018203544a0155482582c08071883c40d2500402042040703032007280b20301102000d1042003142041020402d0241c4a908898 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 480494433 1250 480493183 480493187
    0x3190b0a0e04060f0609020c0c04050f09120a0c050a0803061804110d15020d051602070b0904050c070b010803090f0a0e0a1d0114100608060f0609040f020318070e07 72
    0x1e8002d94880400b081d07079440800d00360090500c0d9004851600e10000b4038000850000624003a586019241030100c1d9950207010040104126403c1920f504500c08a02c0040ca04100610580c583c5051401e4461041d4075424680402c4070741c1165807120000a2142625007881a441229204c5910360054a4503a41c0c118210709210300050182144c0d180400400102c01d00da5801d01000c13060441d1100d61000c24400507110070707680305c09165048247c2e840b4082c40820140305407004424034614080440c0c1c240802032100030601c1a41c90800d00c4010f000601001c0341900071b19207480210749a20866040021185512041c18451240440204203404481e64041d51041040e003001075500c00791b041e01c000105441011710701d154a00328078000e41d61014400e80f402441d81d0200d90310390781e403a48410398115009895060f0304c404000c88025540c58010001c08910001900215405040101d00000d82c1c0059441d1500486041303c540f2071140100705520080031000400169410300300c0d40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 480495683 1250 480494433 480494459
    0x302070501080a090f060501090606140a1b061e063314031e0f04020f0d0501020f2d2104020402040513050a0e061e15040203190b0a 58
    0x10181800b04503070008600000580c0801e002607000b11088440440b2850090001d00b024010704100c0c0d0310b019008148244500b5080503860b41c802d40f2a0b10340494140191100c100310340c0034031038046d001980c04c40081c1580c00340c20305c0c40c12600d050158014112031488140e400c507230000c184600e0400c0b00c40c001c3c011580c0c2c6001121032802030b03070092a2001641120b140090701d5034000c20001c0002030041c9010410501840342d1002400c600300380e1500590107050100075100694000a911480000c43c41c060604600d17051007100014942440130b01d6101d41030304002d04641e008000300209000c2c00070380c0010300c0d0410031007000c041c2c6020240d03c42c80700000e071071600501c1c400c00300c00e0001c0c08644840e4122800750800400311310610b0003a00359540540780455555400b14200341014141c0170000904a01990800c84d6151004a440040031a0440000e1400351901081c421850a0391103038801140203482142845948223100301444c400d407507a000c410b9020308400380742000b00300180340c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 480496933 1250 480495683 480495689
    0x2190c0605071b1403040b1308010c050405060301031509120c02090a0905150717040602040303030e06010803030606251b080f1c121e0c020307050a030c2a090b0d030207 74
    0x400b080c00800b01321200c9145024540044132042c0340011084200b8120700845011902034200911400301c604100f200c0b42d006500c54035800c01d1702400140000f400ea050801c3c9205c01c1c0d004006508840d58661140030348004508070081030850703000c401503003400340000c1e82c880800d9400b400002415070342c19a481200007000342c507800855000c9a002ca1045000034001013a007100281350f424681400002036119100480200e403170003400703c800002c0444c007141200e0034a8091802c540d41c54061150552103402030490604600d00c0c44c12114044070001c850721800707040c915445403140b500040601034260080350203a400502912a02200050341b4074094019060445034044030b640182e80d2032407854554400726041400540b00840d0000c010203200c0e5903440f041c4000c5011039420b0f40c483c8035900028000b070b04130420740004240207100000c1400d01c200410050600754000c0800601c100b41c494615994061004001c034403598000e03075084039811680540e990709031b0368010350399031f060344 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 480498183 1250 480496933 480496943
    0x130302010804030c0b0901050105011e0905060a030906060305010605030d0c1713080d0e030d03091707051c020a02030c10081810150e1b0301090f02190c0605071b 71
    0x84000b808240c414110300c2412680032201000303a0405445060107000c0c01d02445000588440c04024040c03052102d4000c101c0154580d191030780e0901082c0549640400c0b502014180c80310906400a40f10b403050000441c020700000610a04200405040070904d43c4440200202c911381074000ca040020703900c60003800703809103d036110b0b10b21800c61078009180d400804540900589200201d80040c001984008210165040013129440540803158141006000c440d10f082d030003000146141c2c02040f841d4000c208403a0307011102d0320f090403505000c0480341c0050300070b030886500710700301000f0f0007001c000222001c080120751800010f103407940c000d0100c1c02c0c90054407550703803041c2002d0001080c102c48a0310288003849001d03c60107100c441c20f108d04204421070301c1c0000e0018070320003035142600d43e4010300e039440e59180200c00000f5203810425070220f02d034204055002c01c8410080b40022000700e4070341ca183c0d014181054422202c0040440b81480f100c4074140103000c24091070008010f40c45 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 480499433 1250 480498183 480498197
    0x40219050604061101090b13030807141c020c06090304090b0405040b0a2a020705180601080106050a02070803040303030f0509010b28050603180f0304080307060c050d1505030c010513030201 83
    0x14202400b400171b0140c0039240da40c902c0140304661440020200c0041d00070b46a403000ba80307540400311864205000c0503416404244685044203210340c000b646c00200520000d8149a00042da15041c0407003503983c80c0580e40000750030401d0344039034041e08101a0084130204503c0c84d10b5101c0008590000b0301015505545501125800180144031407041030803080c00140b181078104040d50b03a900034081c107403041c0c2c0218030f901e480c41011403040f0f1040348180d4403007100e640703014000e0b200b68000340014001e501400b000880d5843c001c0002d480114040d580109424003c0860101150ba020301216101c0e41442c47d2140c1c02d440e00c1d420445820032490502058101700380c142c1c02903d40c190800da0780010000140040110b00300409034041c5480030603181094030320110f0036501d2061784035448450f00184002004188507900c00003c00c0642e00b0018079001c24242100101c490700301c04100780401020062240b410100000c491001c02800c1c100d1501c070380000940300751615407000034100f0000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 480500683 1250 480499433 480499457
    0xa0302090c0c0601062c0f150d020a0207061103160308130c03050109060b030604170d0e010c020d0e030c06040e0c0f0f04140108010e1506090a090504021905060406 72
    0xc00c0c00b01c0303503016018825503149585980d4000d120998104091084880500d41ca0480d10b4101c602d42400e0800106406451201c500034015600000d45640c980300030240b08034000402d050004249249681d03003c0c121103400e056026188a819040561306540280400081d440403240c54401c0c1c6a090304203030805a030740341814220700d040c04000500c40420030741e0000801105401101020384070364410b20944101c2d0003816078684046071301a1944e0074a2070325040080f0018002c0c07900c10004080419201c5c81c104510307081d01c0300602c090005922400c07441c00707200e600a00300300c00c85001310041d14031484c02d200040c000340a02e0194500170041d45002c80d1a40c03034000c2c216080c500b48000d440b5180c208a40c1c10780c0350340c0c1003845010140e158200d100e2840390310860005040e9014941c014205032941d1080c0303070a41c0000c8500e250091002c1190001030381d1142402d000904d481000030600d480d182c41404423810480c20140300201100702c0902407940c80c002520b060b40d4040c5841c0d40b100360 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 480501933 1250 480500683 480500701
    0xa09050118060e0906130905210702130506040b180406050a0b0d030e0301090609030c1e080f22080f12040609051309020607062a020c040e070305060c19020c0a030209 73
    0x2e0f924a0030301b100d140c050040100070010848907034070291a1900e040d0300f140045c11405520415030300075441640d119500141e440310354002500140044e00000d5215020000b04d03465815400f14151070000b00c9041004110203400341da5840314140f0014085501c403d004176021003c0984010f00b40300001d04107030401d45003503001c41603040d085039043c8504541c500f00500816006041a030701c041140450b96180c2c0444483d9540b00755002800c0c918121074100d40454580081000c11b4aa0004040d002810100c002d01100517104001c007405460310b615102501d0007400b040e940201d0303001400100320a5402000c0c030402c07100250b80c4250a90219030040d4000c001d0540c1c000e40c4410302003005c9040c00590362002030040d0355807403090b84079194000c100329504034103544800140d005581c100000e0400e07810200840800108a41a10703403070341d8905040203030851305482080c4000c9400c99584400307140380c0d02d031415540041c003541d00900780414a6100d003400040d0007580e01070046840c0e41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 480503183 1250 480501933 480501949
    0x30d0516060204141804030c080912121803010e0d03110f07060b120606300a05030a03050115050706110c030c0a030206011e0e04030e03030a09050118060e0906 70
    0x155020104543da1916166401602e0a00f100c4981c01540d0180540c1e20040a0f40c0c600303409590162240001c1c51075a03905e421166010b01c1c0040d4015034020306000340d44000b081032009941c44a2100760302e4290034041c0304401e806c05401e181c0300c0c1c0c2c1030100302c414030030000c100821042c1c043d28010480d10300c044600c25840c4070740300490000002c00071f036040031705c0315a6118401807041125208200b8164141c150ba4600b01651b070a42d1002511100c01e2206500c2e0003180600d0f02203d44801d403602c09a140c0e40d007011040081516107400004035400041d0307051050781c0c0903000e414a400b003500764003a0000c20b00e018015006011681d00c443c038005040c50b00c400e96510803104c50481e0b50350290b00e10115100ea410f04011005841008004144076280c145481e01c200c1500750821241480d20340b51021050001c0e009400780161961102c64945052004052001d003644424043c80c1c6460001061049540401018000400c43c103200c0294480c0c038920302d06004807041880d076203442c1c0000e9824 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 480504433 1250 480503183 480503227
    0x314010c120c0c1a010e100806070c051009060b13110d0c021504061b030b0121110c03030925030204091104020c0f01060f0b030c0d0b03030f0301050306100302030d05 73
    0x2803100c2e81c4207684e8000c0e103c0e4049060303c1c3c0c001101580d946841a2240c0405858090b02c08603401080000d010345200d0761504600354022000c8030f403036000840d034035021940c071003201740d9a10342c545620407564180a13024032940981450100080481c03401c10000d203028100c1c4419840e034455065610862080101c0000c0300380b0420f41012a0800b0b2034658010503c62a54a403801c1c01d45144495440c040d00c03650f010b0300010b864107013400040e0f0380526612001d19444803540c5a55446800300b1026a1028100e00c0302450000d40e601e082c40803909180042d545000c1c0442000101c3d00740300810003400d030030101e0780d041c2c4021a120034a480e110f900301285900307841d0400d20201b21800c2080d8005140e0442041180013004825240d103d41040f01c00f003400b0784502101e00304003150740c00f54400000d101d8201e07004000104a00e0803030011b0300715448807108012000c00400140061f1a05001c96a0170040c0b9100c3d102140307103036a001c00d8540c100400a5400c0c4007021a0030f030740080c14907038000e600c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 480505683 1250 480504433 480504443
    0x1509050607020906010c0f170309060f01060f0f11070609081218060f1605010605010e0904020a170f0a0c050411030f0a0518060a05071103040803030c0f1209070314010c120c0c 77
    0x80c5d48249400c508d00d40c0c00c112114a06881600c0100c0c500c1e0b4540d003400c0341616416940c0188980040c041994a98040b10007402041140c100903802c0200c10b004000c0604076654410202e1480d01c00c605e80b4184607403801c410446008c000ca003880000c2103004c80702c10b103810384016031117034603410020b41c1c01c1c0101c00e100c0f8102c8003c22440c00403c0f0040d4044e0080c1d8109887d802c840050007018005e5511045900a4101d030020906000380b4500000080459507a0800c986500c80d85103d454104485480d040702e541c00c090304207014520341405006c880d0700884000c00d08501d403680c102291180c0103000b584002d030341c900204040d03030301c0002040903048030700301111101e042502e000c90041600b03da5400002d40d44009540304c0c02c07004000c84048401d400300550a41d206c0d036900148039400100c0500240000304428271440ca11a20b019108222040150240e1072660801c618509030494030410180d150480340c40c106a044014001c5404482400140b85512104141e6200c0e8036258017501d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 480506933 1250 480505683 480505703
    0x303060618150c02030d080a0606050c0c04091b030819082202010521010305010b04020c060106111908121b040b07060213030c06020d02060609011701090c1509050607020906010c0f 79
    0x8041d80207c1a140a4140a90208446951000c003190036024024030000e0395040f80030b9030007031031501c2d40100d8101805203080d03600b80300094128010b01c44040d0300481d88a0408111a8a100f4007100c20300c0c4550310364207104415140c0130005150700c076950100721080703003180c1070a41c1c196440780040d00d0102918034820700c0300104c80099940d50719001d2204031040c3d0b08011130440c4500b4a4002c2d101801c030f000e4010850350342004000c1d0707400e803000062900d803403040c90103000501c038500381c0f0000c08a00a00759070380c0d50344c00030004008640c80100380c0014840c070005140c203102004400c58080b07491401d111602e80d4110314112020340302e8854041400001b8030004030620442038103090843d5416001c0f9000c203202c4840503a140c1408498081e4895074035801080180300c010300c190307003040c0014000a651001c4c0c4c0d0b101c01d140134442d00007042c0741c5080585440c4146c2c021100e00082c010480e40141081002e9000510034000207080c241009540d14041c420800d1380c655080f911503100e80522 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 480508183 1250 480506933 480506953
    0x2a1a03040521040e060d0f0b0703090b0f04030f080702060705090a05030a06140f04020d080c2409071a09060c0a050a060207020406090209030714190308070303060618150c0203 77
    0x840b40750454011010007400d5100880d24514280c3c820f80701c515840b240100c43d412403521000c00c2d192000f040d400034580c44018400010f403980e001e56200d00004601171505050030f013001000c0c0b0500020003000d014280c0c0c14000290b40025a180e8454500d141c100c0e0344c5c20700640030a100c041240d01243d003500c14121500104460340c4c100130301100e50048000d0035a0703a01840d00c2c0170f001055501030b4112404041603808144010018042c00710300504070340d140000c02003100301d0140011100c10310b10b130800c801e10040d1380c001d010180c001c04510402c903c01303040300260302001e480b950044500c5032030002045001c0d12001d1003a605c5054005003510700750700d51820040003a41c4205000c905c2180390002c04a552607251090310305680c4050300a1056500b03140851000c0c035034484070158030400b0100003c1c094128007107048040d5216070110b9440300003030319025007035400582000060010343c0046060548080403240c00300d4140c0d8074000030741d81405170181e0381418280c3d17001e50140039242d402c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 480509433 1250 480508183 480508243
    0x31b020d1e0903230c1012091a0411030709111602181005040501060504062f030a0306170601051c03030f14040c05150a03050c04050d2a1a030405 64
    0x1c044200840c00717548611614004003c3e2a80d100c0742050007148005100000010050f0303c208049482290003d1502800c220304540b42c4400b21002c40d040c3d1901d0311401c1d8942001c1c0700780c030b008042c11141032088084514100000313010702c0360b900d040e2180304200d460641d03403084c1c0800800502003c109500703040c110b0038406e02e11158041c05d8003c0f41403c000050851285086030708031001561080b8000c0901c0c986004c2c20030891004501200740c2808400389a10700740010100900a505d000603558580503030b5a096480741c604815158000100400840e00e507001401c0c2c1c02425441d06100105040c64283d005140380204021114640f018030711401c2050003946001d00e005100860289544004201001608100c82101000140041c800c03003130003908550b40080f4400e103450b05258807034003c178101d50002d42007901d03118441d6000007007401842c2500c4080110789142000402e00317028807055040d290525000002c1c1001001400f80700041c031910400d81c04004c4c60306190002003c2c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 480510683 1250 480509433 480509483
    0x304030c050106060507150c12020a02030a08010b030405031b010e070e0f0f04111c080d05070909050f040213020903011401080d0e090c070c09060303031b020d1e0903 73
    0x104550719032038210007041d401d000b80c1c00c0d101500c0d408152914109403c038184005030002c1001002800789100320100380f800c20b800949100c80141d40150b460f1140403030014020b800684c49404c0c009410024000850780201c111003281703070324804000c5416183c10145006021100c83d101c6240075985000c13542000e1181e80a01030401008104050345806170400990101038a0040a1149825509070f083c2484181d512252003002d061034212601a120109154040c2c00c0402249680728200201c2d56000407411001d0000daa81c1003001e483d0900a10003c02e00140c80a445404030707103641c920000507034044840048002c0c0092103000d40e10a104c0d480c2070400c0c01150780e1800303503e14a1030f08030320480b8405404e0800074031400307450303c0340007400255920000c4181c0d54000c0300742020645c8015406001c2c0254480d035070000c1d62000101c0340403503011040f0304040440d00580309140b41c40303600491075014540110f09034410a01c85a2081d15403514580c0b00030450300c03800c400c4244c0500701d010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 480511933 1250 480510683 480510707
    0xf04030806030d0f110a06050414011d07090b04060918151802100201140903030a0c0806010c14070f1403060f07140c101b020c0a050d02090615030403 66
    0x11018055100c1804060f00c503110503c0303000c0040d0054150504840c402c031404111450f03504142c8080e480b0720b40320b100c00d50b00100c0d8107a03500300601d80c1c3c1605009003407040c254600c1c040010f000890401c1620300c1e84405140c460701c2403054480c024802c140d13031254051001490412000c1020340300502081d529600b0a00064504408890b94002c05038002d0240002003007001c0e2031005e07900d146070f08024070000100903a00840d9612000b0481c900001c6903a9801845110015a16864113420000c00e40da0840c500c001003041e804140b03c401c1e600164002c104503800100700b480d03407102c000284e141000711b502145d031400c2d0301400083c40c0707400360948607151542a819200d5070750310304032070301101c04c0c0694085000070203400c5180f14402c0d05c4400780c0105a01d01045c0c40148100003130250945030100c6042000780c0036140c40c0c40c1202e40400001961081c15101800d00c2803805002034250045200080e0284501c0d400043c0c0e9940c0741c405480f0081d6104585a4aa040c01d0030010a2035140e01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 480513183 1250 480511933 480511937
    0x703020c032104170a0804060206150105120c0a0c0510091106040308070f1a070512100e0601031116030305191109010c02010309141b0109031a060105120f0403 70
    0x409000c004401c28440e8a1110b061589040c40c15240c401c6404100c258100c80f1911806042d0941c000103914070001e0000f0b00455004100c0f40c00c11f010001d0a500e4420341c0c080c14000c0420011884035016111190722017902001d6a80310559018151400d0b4ac807040010103a0040445082841c000361780000301d214083c03213480c0204400c20052003d40d1040b4000601b4141050201794009404d081ca40c4010034421000c0310700c401010354021540300e40075540740c000b0030780c08030b50320b4803111003112059441142c41c07456980c0c50780791001c2200301c0354003d405079042503200c00c161126844003030225035220080c1101d0360311000160030028002d004c10b0341d003010880e030488401150038000e03008400080c804010102d00d450039a80056440305031030b03a012414076441301e07036810200c1c5184e2811501107460724060b1000748481e10140750000117140380141400a841403e10202e1180800391501e401c1c14007601c1120340351a8010385d0076000b480c020f45e24942d070000401c40712840f9031104c3c2d40036511903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 480514433 1250 480513183 480513193
    0x1807121505060d0b01050408070311120a0c15050c030c060105030d02060c0d090606090f050402040507020a030203030615090a1508010f0e130309080102070602041e08060c03090c060703020c03 84
    0x42100c0d40440c8400d205482d8860010312420b418040c0301c1d4080c0061910504060f0b21b4996201c8505042504540c415626910281c80120050a0014123800304061110240040304041c6d6542d4081410f02d0050840c401d0491a00c010001c0c054400c5406003610b05045031340301c4010120540c0d480b142402910300038000c106c100000d5174000203400e0b0103409007035200c500b80a01d40b82c02c9401408031070700a485d86a2a45400100c020b918410301161314044071012841d0329041c01880140c9030090300301d8046610a410580100740e01205494101c40104d450121558282d20b40203800c3c01014101d59010840c800c001071381d50581c0c0d802d41d014190a807a0000141c2e0f0303c0c01c2e40803440d1a070307200d09040b68101b4400101d4400340e482d4880c90143c030a0800b4443c42e500c0b8540c0c0740c220b07000102c0c101c0f007403030740000c084c000402c411004a040f0240200307030b448501e05101c1078035180c55025028500129010000c20600c4005000c0240801c001401c0035842d0245820000d40e42c24070041c050b800b84c050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 480515683 1250 480514433 480514451
    0x105090c0909060a0203040c0504050c031e010f030311070306050702060115030c0504060e01020f1207050c0f150c010e030f0415030501140d030903200111010e1506180712 75
    0x1203540440e100b10500400750009543d100c1c6480041e41c00100212506511400c0118066840c1c4c81898040c6410100303a6480c0e16152104000b11408003151503103c1440d10010800c8200260250302500d5043c1b510745011480040120710b00b00c06030300002d00340e80c100410070105c15400540780d4102c4001c40c045040340740c15014240d04894000d59400000742040200748803031400303810f403921114010b104032070440c15080e400701c0c1071031610754408890f40d00016910303040c000704000c0ca8071b202e10100c809100c24a8400b0000b200d40c0180a6440003c54001c00d04142001003940000380183e001401e90396a0b401c005004040da1740580111040c94044030707100c3d070031140b180c81001c0c1038803407804014910440d010100f1041e41a075140844c100000601d0100c0001c000c000c1000003007002104183c21424240c0003d840c8410a1a4000e443c0e8036025690884040004c3c901424404210b1581e815031942c20202c0c00c3c0c28068000d03050180461010b0110003a8003a0011207480f0200c0401c004400c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 480516933 1250 480515683 480515689
    0x11070314030603060106080c1c0b0a0504020324060c1c17040209061e0604030f030206010503210d0209090411120a020a0306020306040213030c1a0301050d0b040201051b0105090c 78
    0x142c1e000c1d074266000c00c0041c441c0b83c0c01260000e8001100d5072000b0304041d4804440c48030900907201c2c808945442e0b000002580c181515444040c19044806500f14605042e5000c81c007a0100342c032001c514518215214151030306800c444a00d200002961000412100c00b013802000d158004400525403400088541500c0d600c0c85006590062501b000b41e00c0700c20070090300c4c2841106200201d486007200c04000d540da0f07001070000350301c01e6540980d14509810040d0074920164030581c040c0d0403c03040f144020790b1260300243c01d40d039152040d5031102c1200d486c400c024003481d0b4410b0740082c2c1d804c003070105200140031030006501c0c0460702c54804841c2c4c00415603c400300c1140094110582ea0001d000003041d5402031680140083d02c011f040610b01307001089020b400350310991341104240307020b1000e02d0100c01400320f03014161030b01c05d18651400f0080741540081040c06810b1003d59400304046a05c110100d544585014034090705c8100c03402c520764020078041c1c4007010b091003000341d2122941 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 480518183 1250 480516933 480516937
    0x31401090504021c06150608060a08030406051e0708030a0515060a050d05150a151103070f080702041104140901231e310e07090f0e0111070314 63
    0x2683c05005442c0f000c800d00020711070340000c90811200c039500d46610081000300c06002c50000c141e01d80e5590f0b040c1c1040018071044800981003114140c00801040c840c0a070003804858400302c40800000700c00ba4001e201c04079501840c68001d0840c580001401101945504858000c0380500b42102c400c0d1a80c00800006215030411000890001e200882c10000d05234006036000c080070903e407001d0104040040c0d528102e5030040e000b04070455482101c3c07103501c1045001c0c0b54403250000c52602c9131588600a05c1341014000030244c4400080701030840d2165084200508681105203840c1d0303407105601042c40c404028968081d10308003000080088580403410404074184014280c0749a5030002d0000c503001d20306911482c0c140b070f1980400c1030340b242001c0d0401c50310151442c6400e150405c003249002c0700c10000121105003050003400b0400f07004213445c4102d400c16040040c1c0000c5911495025204d090210030040d4a4660201066a000c000500a2074070a9135440c03106d01c041d41c9002458 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 480519433 1250 480518183 480518191
    0x31305030a1d040506130f0902040908070b011707030204050c0c070303020c10081b160f2d0b0c1b160302030c011701061b08030703200f0d0207080c0303070314010905 73
    0x1040c400031035201e146c0300c1603000f5000f00100c0480420701c81c2c4c203500441c2c00c1d6000140100c42d024400500201846081240b25004d81110b060b803440d4402055480f0b5625400380c080a4441c950390000b2071110403e40382201d044c80040e00c142c0b40030507501c2c11f000e0b4652040d14101400b0b05401480006e005211b0540588201004110f481d10092030b03810380c0b45240c1001618110100c1c42c031041c803010880c41c5501c030174124451800000003400c3e8a114001030744030001c1800c480c1c020b6202200c000360456090a91000c1d944020548510840c20740b0110506503202903083c50180e8240d40f118460740301c4090041d203000b50211050080c44100441b4084c041c820707003441c0b000220006100080c03040400801214888082140450349070b1100c009650060310100c01103540e820a032140d9035a2804c1440f0f01104c08540e103410044035840195092140c580321001c140d80c006424010000c241e0103980c4507196042c1180e440e85032000015000302440035a400b0306010315000001d00d04000c0c041c40e880303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 480520683 1250 480519433 480519439
    0x2a01050711190f23010f0603020303030712110403081e03070203070b0402030109022e02031303020103051306020a0929091e04020a0518090615031305030a1d040506 72
    0x104091814602d01d24030049012919811000041400701d80c0c0c404c01c111800107a1580e09010003013500d240c0d401c544245652a20f280d0800d241000507941c04410780350b014125041c640d41d40d920701c0500c0c9006000100c100b90042c500882c001c42806108005081da54610908922a40b0070414210419000417030342e0100503801000700900251000044a0b042440500041441c2040350f000820100398820070603126054082c0030541c00d110b41c6108110201c0760700140d46080105070301421030066601010781496120800316500740e010404900085403ca00c0854450744196802403130462180700d0700081c00182c8031001c2003100940404212103072101411440d1260f40003d10031b1141d03018280c600c2c44281080e503860191560b0006120003c126680c455856140150408814400d40111070103214030508101c0552103010340f803a03031841908480c0752a40d65008410b16500d648a0004045001c0450390080068104010302c191006121020140100f01401d0000726003089907020380c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 480521933 1250 480520683 480520693
    0xe060118020424080a06060905061602040504061b090b12071209080405100503091203130827030a0b0a18020a030521040f0603112a01050711 62
    0xc05220241105092210050141c18541d44100c01c14014400c03046003010000c00f00203191031160700907503203584500640c0003040f80034107150000300050040e00030030703001d844001040c5500a40c0300348075400f65680100140003920740b5162420282c1280c0ca6441c2d15103207216a04440700c0e0240b21440180c40c0c0c5064450309045149003254200039001d000c100500030149445194416203002e0b58946034080e0742070340e40d198a0301052240c0810200d100b081040810b005001d030700c00d00071031100b4001c0e6a00c1d180c41d07200c0c3c4881c2c20f04803001041c403200815107a0000780b501c1d21043c40d480340c600700d441d0a00e1407400444080041c5030325140c00c060018a090f503600001503a031040c0303500000c061008010604c41e040d4459004c1003205406810541d8281e002c0702481c240402903038801c4895201e003038011030400d032410004504410040c0155410715450740c1e40000c02c13814050945580e600c20b59104d884003601d54841390a107500c2ca6008440550034040001c0c0d949008100f00d802d940c00c0200103003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 480523183 1250 480521933 480521939
    0x601090806060d210f08100324021b01050a05070f0807210c030b0301050a0c091a0702060706141f180e0f0609072102130e06010602030d050a0e0601 65
    0xc140182c400f0030858030300c6000f0304603840c40c1040c44030400ca03499881e01c60407101c80d0307081005021410010103d00e40d007010f0311800d2000403125000907180103180381d5401903004c000c0074298003074060700d202000722543d054480181c2400c1500402c1c0100c07100320302000542c17540101103880d01d800c0d000d07010102c2d840d007002c202424401c00309403501e0380d01d26610208800a1043e84000c0c2c400070000c00001039254000b040da00c0c0f4003031182607040b100743e25080209181c0060003070700c040c1841c8500c642030900c4a00691544000c0c0d8100c4004550040c01683e88941030b2621000414003d2010313400c00d00100d00003182c042d0003103070070a149840030018555003850182200003902400201030030071a15254000107195007080900c0030804580094119440c00e844024074000192340290001014003451070340e0f09481d2440509440d0701070320540407410311900385034043d00c17503910b007204148030302e5000203009907020024090004002100b4005030f103400c1d071080141c1e0340500340380046c2d4000784010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 480524433 1250 480523183 480523189
    0x301050c070210020a0b090109030810080a0b0702030f0703120b04090c0b090609040614090708100b0703030b0d0b1806040503030105061c11030a0608010c0e040b0a08011104030209060109080606 85
    0x5000300f1081c4110342c0b9442180d91a0719021606964540c0d56a440d40b005204058202c40860b5001c51110220100d0303c1c0340144480e6590440c072000b505400c0780f0703c00b00b06001c0c1300f88210340900f40309900c1c0d9541c40c10a4603008090324085044880600c0c94502410001d2401c0d00a00c240a600044040c00b01410103039941956400540f140340c0c0903004000401c0c0300e49440c0940300c020503440e08001611107000d014440081030041101c2c041003140020400c2e4005009001000d5a23020030059840d0300491606800a12940c94a281d000d181c0a10300010440c49124551142240e030385060403882c00010310070703690070041e60f00503d41c0e0170600062006042c008060f00740b030b110725690003501e9080c001041e03003100c0c0a241410541f4400108112107442180113280042804030000c02981d60846001020041610032540c812911104482065038841d18080041c04c1f0030380007040b9a102c8021144d119a00512040380106044000295590301807210b01088504000242c0219900c0340d00f0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 480525683 1250 480524433 480524449
    0x915030f15010e030d0305131e02100f120b13050f27121305060a0e100c0203150712140a0606030504080f07050a0c0303080a06080609030d050a140907060e0301050c0702 74
    0x170180510380741c3d480d0403000c14154278006504e403850708206000c200503030042c441820350f48400f141c00d100c1c805000402c40c03075001801404655500e0b800042c0b042084000441d52084804044106418401031040000010707146c64000c240d06500d10801da048503281c0007142c8001e08030100c02e904070b03110b1502e0602644004107003003151000080300c490748030000640030b600200017800c0010005000b82503030b404c2034810031101091a040070a0031042c10f40c0001d940c0c0e04032410601001e03c1a801181619000c0c241035a80611421410311484040c545440c0007100c0031101d070325085041c00c030001880c600a20686001d25040b503100d03413520f50081011000c41d40006801c0300d0520861aa600200303002c0c0c04040051846940c07510990b0402e01d812409940058020542541281007071013000d050000850711100c1c03401e0300c0855140d8070800c01d0001030460710001c494601d0100c04001e0320401c0890190250b031000d8449250300700354101814200c490031614605400c104002000c05490501c0e5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 480526933 1250 480525683 480525691
    0x706050f22030506010801050f01051f1707180b120112030c0204020d05151806010c1119170606060405010c0228090c020c0d080915030f15010e030d0305 67
    0x1c15000c10030620081c0790141500da0050f03038590460b81c01400040000e0113669000341141c2d032002da180d41000d000a022105802c0b0912100300c281c214030345060f02481101403c0117403540e04410603d00180058110785050400f030850302c01c1c500d03010803071a000c18107441150701c0f0b684446040b682401e40460341d0040d101c9050301444500402c50006a807540010200341e4008407000c40c0904040c100d008000348440e400318070580814440380c00b18141c03040025801074007460a01a68429800c1c40042c80d4498400b16800181c2e50081209800d1258178003800c50b1b4049034810350b56003680c984aa101c0c401510a6580114208010040781d0b210b440d60b0706c030f0b15000611041c1d004c40840304072a0705c2d0325072141c00003440781e200f0010442c200e5680f14440c11a801c07400900007607a850340028950000c841001030034100701145124050f10340450700c3c041418a42c003030654034185602c40d003a802904071b52032155000381403020881c55100300b018442d070030409002043d40c8a401c900030f81c040e0800030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 480528183 1250 480526933 480526957
    0x7030807021509010209092202010f0504090f06170607020c0f0103110c01051503030702060d050c0702060703030f150b0a030c021c0c02100503040201080406050c072102010507020706050f 82
    0x486208904a0010403d0140710840b00061783d4158903414440404002007a1490516040031101e08540d8224020140c00780d09103000c0e00b10119852003941e01c2d00440e08080551458040b0040c1030b0f801c7c80c0e002000b500c1a210942caa181d02d80003c3c16946c1d00c04680740c400580100c441c40c0240c0c2800400c1d190054014100440d00c1c1230741030080003481d004104000c030103039150b0b41441034400c20b0501d400700c40001500518a0440300340c010504c1841101020302c02156900000307801100c91005461070251b0090003140d44090f6400c000b001f400c03003140700784c10b85440c2c2041ca51000c4101ca0503041118149100c8509000c98040c0c290f00400402620405500640d031124205001454901040e104141c65031241c80500d801844581c0900140800a0120070002c0c440540c3c1c0121800754025407001010070310340d680240e0301003503008890700107120400e902c602e91514008009136980004071540204400e0b91201030481c0e403600e031881a031011520800010032801090700003480014428 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 480529433 1250 480528183 480528193
    0xd052116030c171629090633060c030904060807030c050d0f12020c090c0a03050a020c06130f08070308040b06090606090f0d02100f12090206271f020f120703080702 72
    0x9050450202160704501c6e0f50403480c100b02000f100721811094604083c4040903540c0030402d21480c03845080050507200700b9000c100742500c1c0d00b040084520740319003e0003e1103030a030f840d100c040c1c0c0c40d090303400304032200b1103400c00100301030511780d011003261034012603441c2c4030f81030700c1c0c840c4510160444215011402040703207850306600c40709085805900e452410301e42e680c86800008045034005030065421f5401000407007005000081d0854004540d0720307100c04507a49a2074002001c1c02c500b04028944080840c1d40c2c1c0c241a0481c4145104a0180c242841556110804c00815842c21101e050b4011000d1210030810f080c04840602d41d030401078004906c4820f1900002d41c0741411200d154001a0500300004075030750700080420108401c0701051088140d594000f88460060708400c22a450f002104400c10551481c11000c0141c80500f1440400c002e118440c015a510040100090310501e020a41c0700200052203c03084912070f5100c0307041c101141e8017201c0010000e04404110310603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 480530683 1250 480529433 480529493
    0x3030507060f0c050301090b041503140319030207031b0b010b1b03030f070e1008010b0d24030c060c030806062a0a03020105060d052116030c1716 64
    0x4034428090f0700c1050f0344502e0f40b00d43c07404040390241c900c0405062700607400c0c4155a0651030040e01000180d9600c00d221078002644070418078070b540542c10b07410300740b0200e0300c085900d882e405038001c00859001c0ea46a500e5520703141d030100d2080300d01c0381005110220b8000100054076641d005481200442c81c01e6480305607511a0f8149950415941481444030b0a403d00c01d5040c0c010098500e200c40a607212108080c0d0106c000d02441d00500c82c45001000014500807188501c2d030004074040e46600c0f1a07004c0c40902c0c042c500ba000c91a001c02c59540c4141c0d4408a04280079903041121954940e13070f1002a5581c180c01d000e030303940040449040c92180315054422581041c482ea101601c0c03100e00800958601d1309001782520406080d031347c0280c0111841c6001b1940210f42015100001d4900760900d000c03d04a6401c0c41c4070340f1807041c1c1e40b0050780314a14201175001c18603900e800c0c010111844d0014000c004142e0500c81c60303000c801002c1c45a10403100151038500500c0030710204400c400a8a00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 480531933 1250 480530683 480530711
    0x102d052205061c0b0319060203100504050c0d0e07080316050c030d0809210304060c17090f01050630070b0f0a0f0e0319020607050703110102071401090303050706 71
    0x120200c03410410040020902d0440281c0c8545100240c00310018545211b189040c003075000441800a01880d4002001481c0e0baa16054003400030500078004109a03c0d041003040156000000403811950401020a5a5850015020003500d07000300203145410182c1c152007101c0c100d600c200311114018005024283d98052020044030304542d00c41c11210700c2d03c0f503400f9041c14840c0601c030003844051021540501940b030240c6e03611541c84040013803400842e140c01d8500c1101c4000c9200c01040c02e204000002c0800300b01c00904880340030083c0001d44400081000201d1010714030f036000801c420040060004e0345800d035401c0b8581000b40d4201d1901c828240301281d010495116034010001690011680d01c4001c03003491094601d00150440200700002e500c98002c060b5015030320340341400590655846c85c2c2103c500d0303507210341218220b80e0303a031070f0114800714074100e441c1c0036005000c0001184d0b4500b14490442c5001603654440443c19a0380640d44c40c2c010490031b0f41e031103507220034132601c000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 480533183 1250 480531933 480531937
    0xc0f03150709080f160515070c0603021306020118030f090e100e06062a01020c01050f07020d0207080a0308100504091121030720102d05220506 63
    0x601d45a85121030b0500300f041003031414513100c01543e420380c040301950350b56403011000041034480464540000380c460304014811783c0603e840140450101c950005507180d01075005100c00080c1840214000781d4981007a0b08035944072986081c510700d0054108001ba10070300b40440d01e03040c1410304840c8941c442140c40d00c0180c00300c40c801283c4400d030030240b1401460400d21a4010713021a081e9243c84210031500503c403d29505201c003003005c9280e40844110290192103903044440d008100c01e05d413402c0200b00c40f8074203a4500c000340c0100380350080b4007032010459006580105001b415020281d550841d0b444000a018100e0200500000f00c0c2d2a07403540158000c2c903004603810003141c0000c104202c3c240c0141c0090220f07503040707240141110800130094500d0143c001c0034191828005402e50102c8408a02e2401e600004040070a4185034202043c03520b410030041d0142c040c0303565850b0742d0040e04a40501d080104406104505a1076075003050000844981316200c09942d6692000c54003035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 480534433 1250 480533183 480533191
    0x6120b120f071a0306010c11150d06030606060305071409010323160503070c0809030c060f04080c060f040909210e090a021815040305060a090201080a060303020c0f0315 74
    0x80d0000d4004010040001801c0c110f401207048041e45941070000010b0403031004064014440c80413100c1008480d40c54002c203080e52680140400e0b1703182421852200140a1804200c90543ca440404035800784603201c2c540c412044c40c0c0780c0e00902e05292040e5240d5412101c0181e042540380d0005003032000c800410400d4805180700c6220070b504000140c0000d442c4141f8070503003008414402c0098991313200c00c4e0100c000742c014101550f2130f6070703200100b1b01340310100c07400d5a0410000918483c1c0d0300000c01c01402100e54800548100640340f404001c0988658040303c00512420300052184900c0c907400304807542d1051004048a80a0950000c01e0200d0700c40d008010524410003855a400c02c00c45043c5d0004440e00c0c01c51034240d2200c0d04104c914403840e2654098182c80e040c580e9421070503c210340146400c40211500d524100810038042c00c00b900b400c038005007061000c00d040031013600901d4141c0ea41070b001742000b1140003050082da650f04400d03041e0705214801c0900207071121514002d0003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 480535683 1250 480534433 480534463
    0x9060d0c0f0f1b080c0316170a1409040f051f0611030a051303060e07060311090d11030309130501061116060c020409021e120706120b12 60
    0x11005010014041218a108807014400d0070a03814442ea81e2010707410f03040e002070700c82c400070000035030030a4900c0380180c4012484d1480001851b0032060b0041032803034030350340c0300e42c002540c0c85180d5a00500680965180715010400c40340c0c4103042010a18080e00c40c07984060000262403400440c1c900c141d17141a81c2ca520a218800d150a443c000c1d02004400500100c0c1051040c111000a040d0f54a00c2103005100400034086200f410f5104400c01c2030006503040881032100302850a01c1c0303a01c65043c0e01c58040400e00d0000d00304400b100c1c00d010b40d203000000400c240514015503c42c407000c0200b440080c0da01d800100b20405132036540101e41081400100c10004166051850142021340316400c2021107502688210401107040350080050310814600026140385130300c00329000d04407000009500c011409031256a840320a41020800703602103480720340380320100c0d82140e15001c00780103140018183c081c43d12041045900204040320000d060300d60a2406a48800e0a26001c0071070461 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 480536933 1250 480535683 480535691
    0x180b011e1a211609060c0204181529060703030c0203041d010e060409080304030c1b08031207051e13050301060612053301030f06090905010e010b0102031e09060d 71
    0x2000b190f20301c20308000401241000c0e459141442c0e0041c0402136040c2000744119254518060003100d082081401d05510801000c40310710421102409407512422060b0594000c80c624211410020851001180c001e4111403502c446600c0c00c50107041c1c0c0e03d8908043d44404c01001404910038182294021018580c11990b5410850190100040a00707070502c41e0b424001c2d01800701c0c040c54201c81d0815414100034021070003038601030b4122420264034040c3c2540305a000541880c010000304810800a84549a2980d40309400c0e980d83c0079841c480a288d6140c0c81c00c0d000d03000c92142c000d00034080081c00020300d244c0d031240000e007592060340100c00081c612041c290078986a9000759604070750342201d8150407091040c960346500f580413110482407180c00703810482e50b901940c012800703401b07414002e20040d81c50710390040c0540b150041c01c403160345c80c02c1001f400003a01840380781e4038940140d0145203001d0000002c024481e010f0901c000e41144204845007103981c80c5d400620302800000c078045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 480538183 1250 480536933 480536941
    0x607021b0910290a09031221021e130602100e0d0e0619031b0203120f180102030708180c0901090e030409180b011e1a21 53
    0xc424030500c0454034000c9010405200394074031580c0045095036041c410410240003583c815101541a4001002210600090212845a02070110002c1e0b9004000b1682031b1014290101c0d001c110b4805c807100c4407a0500d5800d003e2600350380081c00c00383c80c0b00901412010700010b8101140d80b04100204003039903014000c001094050203d5281c503410b92100b08004420540c201ea220036003640c1d100b0400040c06042c40381c82d91103405581c400c007455001010425108403000d0003c044020281d8001c04110310418001343c8000200c4440118002d114080d030b842d60135034680d250101508003031a070309e0b1401c5245c019010074805580314405c6036a03200201d090003080b0718a821002c1541ca0703010303044041d00d000c0988581104a0458005d44000260b0f142d11881403070450103650445030f0110308240d800c082071114030846080e0540142d104444591341d40030b400c0307000344815828a4058607603440400c40060101c44403480940c280e00d03074a144c86070050140b100d2030030306414104554000c0044c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 480539433 1250 480538183 480538213
    0x18160b0a2c04020d090b16120903020c040504030c0f0302070906060302040308270d0602180306060901031203230901140c16080d0207080a12060e0105010c050708060702 74
    0x202100d80c0624a4003a9220055907045036107071540302828040c6400040e9a0014107565000c0441c4a81001d414079160501d24100b030366142c1100306c00700008912580c4440e00f0f00d00c910400041c0756140c1c00a02c2d207055164207000c01340900070030a5042c001003800c0c18022501084120641c0c610070b034041e00040303040115440444050307810034400c140c818841400040c250504039500380300d10903d10809491a00c80d0803122208941c03025401c05424814501000141d402612a881080c40341c40c0704c610b1103c0c141582e90100701d40d415403003005040100007040403c156074214103214034010802c107a1482d55242d00164001c2c540d0003420f9548208085803200b8411850591900703e01441c1604051a00800c40c3c00748400e80804042c8501c4410108900c0d801150340841c500070f0f0940d250035941c20500b009804c09101c06020503204800c1001b201c0091043c1c8055a2041000414a0f400e00004451000c04844202c88a1003a1407001c10810002c01000703100300c190703a0081100e800c42c00c00c0c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 480540683 1250 480539433 480539447
    0xa0905030f0a080c1c020c0f071404050a0b09041410090b0402010806041401050f01020f0703061d01051303030c020c0a0314250918080307050301150f0818160b0a 71
    0x2802081360060081c003440d0346280d44081c4074540e80c84c030050707114400e20100600b003002d0702540140c0b920400310700003a10105110903901e40c9804840411195807807014010981d10484249a030020401780040c0024030007149118000324410105e4000e03d020302c800008840d0766140940b0700745504020041190703846030b440c941c0103c0070b9906024000c3c2105491030700c00c3c0c0600410b0301c1090543c1c1c240d580e0342d1003081084010007255088a501036a28100b04004000c40e19540d080740d02010182d042c4020140220342c081c03403140000364061811743c0c500310b0081480044a80841c01800e074070b40030540d10303210000d02541c0a40d0103504043c0601c000346181105109508041e009402001894141d580b13a03804201d880e106030104440c00c0d0700c10080d508440e0044010280d400200170b0189807644040030b0b6041e41c0034114084902c01c4144010b0b00c501103134402d07440c00160707914000780030100910030401d44c940e0400220781680c030407031040c800f0000e07040d0046038619001081e41c004603a44001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 480541933 1250 480540683 480540691
    0x60a09090b070e010c0c030c0e06030f10020703110f0d0224190204030b010b0c0c0109080c120c03030c01020903150105130e0c040203070c0b090610030b0a0905030f0a08 74
    0x2900304901902540c550079906030041c0ba01c2c2c28080e0410404a03036034080c400304888540e000d492491040d40b689003c01c01c0c6000e500a00d0f0700d5a40000000d13505041c001402a490b00645d00108680d05445106034060f505c0342e07400b14100010f14800c02c0c404542001000c891f0024040a0603040c410203030700a207880800c030600c00040f584411014560101c80c80c00a4001486140d80803a00c00040d01c840c1c082d105581c00200119603034000016488240c0c000340080c1080d58003603464050188004444020050160780d6a070b400003104010719181000320804032154243c1980d00920f840400a4115001072100590796500007641001d18a024080642c0d0382c042c00078020042e50400011880d548044800c0c0f201280d9140350110780c8100800401c160054002d00566480c5400d1800800065140c001150100550400704600c4000400c00030301c82d1810b559100034480c03840e1144141c60700007800490407150b41e2084200451424030080042144004260307075626102e01c402440780c48000c2c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 480543183 1250 480541933 480541949
    0x903031b1404030f140604030206100815060d030e040204080706030b060a0207051203070203011b180608071d030303040f02090a1415121c021b060904090f060e06060a 73
    0xe9584142440300c80240c400342c0390001d1100048a0071450108690711700614444011302c940404c00c810103a001441d640704107903c100c0c0706090713a0390b4101540d070382000d0b0016907080c03904c2070000b908500b090300451641030300914200303428041a80105040b40c1c0320f074100a03c1d6400c005014881290113004101d0b41c400107403210343c540181d14200a403605002d01996200f00714021500c1e1081400b0000d0701c60b0642c00030001c01c00e0640e00d1032810302800e030031004400450301c0e056021072150108902e00040f10000e1701c88000710750f51030000300e40d01000355210b5242a50a2100381d101030f1010005140f28038883ca600380304049140c010800020001130001050360706007202114904910020300382c22040040495100c904188001504031305106841071651058803c0440c9040160600d0f6094034499001d9800e0780c08034070ba8007164448001c1c9202d4110104001503081c5050991107980e000b401142c145143d0744a5a40790001d413603004248151ba68002c50a20031a844c0410301140101400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 480544433 1250 480543183 480543197
    0x9030f0a08090607030c1406070e0102010c0206040209060105130906052b060f06050402160212070501090323030706020a090f06080f100519031a010b12070e040903031b 74
    0x41d507101c050502c10702c0101402070b40045088000c040c0214446c03d030380d80d4002011031810301032044031580d880045461100081066149200d10b5006100311682c070340c49580079043e00d9440d034003070141c0b5902c0034190904004c010026141070004a1010801401d200740000c20801d1500c0700700011110f00e181d0100c01d410701c96851818084071009940000c1d0381c030050104400c0c0d0700800540003020603a10644d0807038000501c01d02420701d90158114218821289400c81104038100c1581e00c242d107006031804140300040500c080742c41d0314040c1a1440c842d062681524801e14955821504518811180c05402040c1c000c9080d0f000f001a9000c1c081304000100100d1420718020554000902004004603103440892100003058810348094071019040303131254400c4501c000404000d038031065070310340c041e034007040d8500108400e003074122081040080c1c01c245401040180122018010005114440d0884c0e40180c485000e4400b481e40a42c0300000c100c00c910100041c100358884655042001c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 480545683 1250 480544433 480544453
    0x108070807180c090e0702010213080c06041202040b0d12020f0303160309020433050d0f230709020a080609010321020111041509060203091c0203150c09030f 69
    0x2c10940048000860707240490003140000090b281054250840f0410300c120004016503182c05400501c00b005d2510f1058140c1680e4100c402d0b2540100d149440d07001c68100700070030841140303c240c0b01355039000420004400c103003007000584aa0082a041310032814404500c0b25058040c082ca400540c400d101035803841c508a8210014200c00e00040d0b01410b80da0b0111405540383c9510003059441c0d003141115120070700c640b00c08000381506c813415803030fd1341d11100890207043c0510303c103103c81d0b8005417400e041c140c0703640c6640001c00078203001c864400e403c40c8903040040040001000900700c0305401640c2c1e40d0022001000d01078010000d6024034110001000021030200241d0144c114010100301075540d40070040b8054581c1d081c501400c220701180205018410b00e840210201031904d43c9a840f41d62408242c3e140e000380201c0c541d003d845403840c04081d072101812240304a10040544e40c408607500c07031112030341c1001c2c0c440c94960300340420304003142d041c00c020b41d0300340140c170000405400b48 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 480546933 1250 480545683 480545699
    0x1205180d0c0323130801200403020a0b0702121f05070201052e08030301171c08060d0303060b0c1501050111280c03260c0d140c0f060108070807 63
    0x1440f019581c1e000c02441002103002500b80549610401808648000035940c116280c06410254410300a1110020300400741224140481d01200d0b4050b002e80e1010789408080482a0401c8038181d03042041c00034014203003003040c443d18020b80c0b040368120f00442c2025042c4c40848030700400740c009585c500300900c40d580020381c80154140da51030b00c5443c9138a8080c134140d020180740358481d40e081e100c080b001203900800310704c60304504014a4121010360000007490340d90b004500340581c0100e44041c001c140d85060910101500f40c0c024100812040c4c0c0d10059035000d544804a000a150072600142289034804c00310f00303004200911f41502c11003503507203119031919400300d00310f82484c43c407031004100440302c803500c0ca00403a0440c0c8445403181e600e0400c0603154407175422402007800300400e60b41c80380240c8002e43d4510300c4a00d00520480c44001c50640c0e00c4005114002c000038024450100d08481c1005424401406007000d003506500d0b0841452404060782c0041d0215008031a061280724 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 480548183 1250 480546933 480546947
    0x103060b0a031a0402270a0509030922021309090203010c1d0904020f09160e010c030e040b1302030a061a09010203090907090e250309080a0309031205180d0c03 70
    0x14071050b283c1495030b203c501c0003803203200280d516074000f5401c01807040150004140843e1007225140c20501040d52030741c030003649078481c0303590f142d40c010080716081c0b140380c00300c03501c0011248030000f005107041c0240401101c22a491790000c0142c81d158030808046050a001c1c0541d42d5a00d410711000d00300c0c00070341d10814100002d0000d07008500590000e000d542e59000d0b62035403144050969281c500b049420080c40442d8032007524007056141c10404800c2d40300c0c21507040780c25050b40d10000d5200c0200100800342c921855020380c003001c91840c010b0400c03064801140103e01003040002d03d1071921300190b011100105c841038091000b800455113598022044402c1c0f628119150b00f0183c0d14881e055800c80440c0e00100040c401500802c03490580c2000042d1502980e0a050040800ca101040b000d8400d100c40c0107156441c01c0c0100e9081c1802a006081c24a11038142540043c0a4400030001c07514100c07050001061500b2001d0381000007401000d4501d01c02d031070007011080098802409070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 480549433 1250 480548183 480548213
    0x22409060903150a0903090f03050316230705011403060d02210303070c061406030d030e011d100534140a180602010c1b020303040f08060103060b0a03 66
    0xa40001a884007107a030309200c4030303080c1212401900100d0626681c1040101840c103001c03404101c0540b40031810b50f410542550440e5071060055141071940079244584070112481165581c540e04c021224000c0400d4800f01c0740b02c41030004160711468000010600b140002c03003404012410030a100c80c40d2511840940e00e1a010748100c1c1307201d00703036410820303a00882016501c580c1c000030050240c1c0d03d92018080e02190300079031060280403076804000c1c00442c000e803445503050707000a0b80b5000007406604011640900640000b8517151084000d4004106840903102c00750045115003801c60781c2881200d4100e21440c42114100001041c141c13100c841b101c1c2140e41681d6040c10380c00450b841032801c41418005110b0f15034071880603090240c00c0313150440ca1070001c0a01c0f6440859800c1c81442040440f001c0350ba108002400c441240f01c0b81d85850001c01c0e40c26000070000401d92000f00740050008103000001400c00c0d41c91420014111054940d4480c80740103441c8017080411140000300f252 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 480550683 1250 480549433 480549439
    0x11d0904020607050a0203061f06030501050904060e0705030708010f050f09030406180902041401080105330d0c0504081011030c13030507080a110a051005071a0f04022409 75
    0x83e441c40b0b801d0451400b800301d10020350520031441040403c1e25582000000a003051192406d121b4035130000f5010341d002401903c1d0860030b8500024041445038103c42c503d641c0d41004e071800c0300e403521701080c28594950418a2541c1d11940042c0902c1c041d4490745030b00c5018102c00c0c141d94144407503440e03207038441ca00c0340c01c04002c1150b000200da070a10307008002c014a1205021581c407543c9134800d451280051280502080d900c40c00000ca03414840100c0744044050700d000000800f00c421000802c07056050b040c1201c0d0018445200414140d00c01c1c400411801e40765943c5461502e402145440040031000c01158142409a91440120800e42e60800c0c1c0c000201034485550b41c25800c0036944650010781244102e150000b030b545c01c04a80c42d4a01c034004c0b6803c01c0c4840e240400e01a19a41038800d0b030303400045032610030950522a070040d1013030178811001e0000c0201008003102205000f52184a815010398060200310320701400707490319110322004000e0800c04414102c0009010f454a5070b40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 480551933 1250 480550683 480550687
    0x7080f031009020a1106100305150a020d06090e06060108040b0a021c2c0307020607080a0203090a09020c010609020c03090906130510050108060907020601090b0d0606030b10050307030b041b12030e011d09040206 92
    0x2c0035400c1601a941c80040742d0a08000ec5075480f200b01c00544080748035030b0800c0c020300d03010072115480360f4a0144242d411803140c14103034441d03000040003944141d040d80111880c00820000c0d00d0100d001d0380e240301064041c1350f2503d1400b07a070300070310320b070300410540910380e208105c080016158001940c1f001500400c2c02e81d01c40c80d0080c0140d0031446408074050740300c041d016011880b00301c503a02074200c00c8100310081182c030351a19050b00032845040b4681405510610100c0c400380f51410703009038482400380c0401d041c40c1c1c5240040040e10020b0701c40722200384002c0700034002964070460490340107004031556222030074249006521000107002d611801c03a10342c03100742020b4540312802c00c0202d0b401300007000102d959080c448410316060756041d007000410640080c0a140001f204000c1e00c0d00304840446e661a103030b95a10a24500f500e00c522410300c180400601076420501114249000e902c50340d881d40071000c00140385c0741a200718003501c030314949041c08458803104c10055000794103461072030b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 480553183 1250 480551933 480551941
    0xe06040518031c0b0607020307120302031209071505090f0411090d08030f01120c0618090501090903030e0d020a080313120906021207080f031009020a110610030515 72
    0x1200c0e2840030301807840d940b00016503c9a46a1860b030694100c0200200c1040040203040c01c00c503452003012400303581540003140c1888242ca45611302001144280110b918003409501d9441c18994100c034168801d421241c0704104001c50340301c400710440942d15100c0c0ca0401c0b041c0c00241804400c00f5140d00580e070751000400e0303165154003107880d5500b004000c1a0000114038011006500c03c4030094087c58a0f0700001a45030225910085815404250702c80d4007810a00201d940819644500d06580307402c41c0e00061a120314887c09000e000302e034070049545805070070040e099178a40305110001c0d0740005154400d0716070119a00581a910840759540c80e2904070500f11a49058807000c2c0c5461140c48415100d55040394080044820b0f80d002d54240348944000c03186103015220f07020f012220f08001111174000d80700025a0b00200c1c0d803000101d15500c07a48080200d8200034031200c00f08228500c0304c096402c0030030566a0045e41460090079440c19540c40c59100c20804640103000e54000c03000c0303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 480554433 1250 480553183 480553201
    0x102010b010503150a1a07021c0201053408040503061f0b0906130608091006031109040f06060803090f0a080c0d020d0501140a06060302130b0d02090a0f03021206010e060405 76
    0x1702c4010503048200010340342000c0c4030100c06500c007113000c901c110700440041c00c0d4000666000a444d54050b11070a0800b082c2d880400a8003040048450318007441c6007054500359809140428118010451140c07540c2c1008189031a01c84042c00b8000f0429002c20041007490144880100752480403880940b075111050200b421806070b50481c01c0c26120007240815031560102800d80324440c3c9008071041014009002c408035055800080d0107806100c466040608001d03403103a821600c034030302c64500203040340c941804568032600001042d0b000051000002d203481c2d801d43d6100030b4200c41c2000600d140c650704075507600324aa0054014001050749005645c1c50b108005082d03030304813000344603c100035900c480102e10100e80300b001051802902144c01e03440f0b8400c0d00d44152141009400c0316040c0116034049030020a81d4881341c230780810003c078542d207070400c1c1400100414072a00300c0391800e510400c544090f20382c117820071640c42200104403c084460b41c0a070007800c1620b000429880310903078 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 480555683 1250 480554433 480554449
    0x14071101050f0d140417190f09050607030e030c030f07150309170a260414030d0c020705030120120c1b030d0b040b010e041104050a12110102010b01050315 68
    0xa0f0030402880c00711945a01e40212021a2195100f020a031a80c25074072804941d407400f070282c50124440035141000c02e140d0207400f9040260990b401c06150704c56803100058210351260204030700040c030b11040340700103003010441d1800301c038030440203403402d201d56058550341d5647d14440d21200caa603150590228078000c5d0f002e008825000707a5922032000740c880e05075140758002c801d024000f62a1000d00c02c6000721080708100105105400000740b6250b43c0c450789810341c0343c080c1c412428041001500501001340c800c1025149164002d0104030349408109400c5030045400b030b0b003003062503d208411000d551002c44111420380c6089070300703544500e40e0302d042d00e00404980c8401d4211003907000d285048000041c0142e15045c0405000c0f410105050000362000b11080b107000c5014403034560054501500409070564000d5452410540c1d520002005a241d5510604250f540b240d003010902c4544400d5200c82d181c01e00090050010714000245a41b0001b0031a06848e50040328000f003d035a2824 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 480556933 1250 480555683 480555697
    0xa0c0201470d030f080c0f0306010333030c08030c0c0607080d05070c1103010605010503061003090b15030706020609030304030f0c060c110705040b0d030302090316030501050714071101050f 83
    0x102075a5105164034000e440da8003004c000c5000700e01e145000410b01c10300c8004880a50181c1c950080c21900d03200700540c05890015000e6a010140c65005803a00d2542c040c0016802c190040040c4600d1841c1040b140340403194010701d0700c40c4c04c2080014100d0400050034070030743c0d105980096840f03001e0700340383c8054001c1c4130111404900340810b00981c264003400e01d04070540601075a020503140001014201e07030042c030480380440d41c10710006100340351031030301d178004980c45040218007048180d070b44c007007031000c00c4800208003401070244401e2420204401000f0b0103543c0024050b9040031114a0380e0717404000c20060070494042180340340944200c2c03800d11401d0b40001c05101c0c960740200050216066900c03104494400c60000150b0b51070107002e0b00000140144c1a100040211b4030200d01035808500419003500c144c26410741c240c0c03010000c82d0b00440c0188000181802c00d00702c02820a41940c56001940304203101ca0004a50083d002510244007420165981c800c88850b41d2203c0c01004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 480558183 1250 480556933 480556939
    0x30f020a0905100e010618090209041e05091603050c090709171c03020f0d0209030c0a030501020d050f040209070804050c151309060b07110a05090a0c020147 69
    0x100a00c03544014480c3ea01080d1800c00c502c100650780c95010844204a040d11455001008400200801c2100350f008203d11040038202041c0c55582c031080b801503403501003020b03521658034800c1000c1002c003400712107041d09810203070354062071035a22260360702c0b02c000c81514072440c0e41d10007041005000e008400300418050b1540c001c80101805440e45502c0b038841c5c400203000031005041591803003842218030f000480045103049c6000041c1100c002e42101e413001d03405124004940c00d240e9201300211008502c0b4600140c0d0761038080d49101300303480002d02881d43c078100110903c001aa01c131114071341c2c05143c41c0340c0101a13582d6400c1c00c61500d614100c00c05d800555508d55580441c202c00f0040101201c18502d0400c80380d0f94182c0c0720112400d52050303110f40c80303041c01071200180185a07160501d22008041d1038075185c44400041c01500141c1c0e02c8174459542da0300301c003825038080c0540c0c3d0880011004520240f045455201141200e1152040030200c00404084403850000313900c0d8807585000d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 480559433 1250 480558183 480558191
    0x30f040b0703180506090717100207050a0209040b01030615050d030809100c2003040501080402130f110903060a200a0219030818070b0d0905101506170f01030f020a09 73
    0x1905100b602c07988141c40c450898090600e0104802c9880050780842400800041c04141090303241c4000940112f481100e81c3e000d002800c2c405655980541402980100804075180d40745140040842e0141712946080c034010400801181d0b0311a56061080d54250400c0300e40c81d0b03a503140c8642025903889400032405d1900500f181515401110405801d03282620344110607549003030f9660700d0140b4851103000441250004005080c11860151804411791001c030785544880e404205035010104505000840800c8102072468100b0a49030000400350b0101322500413012079101c0754100c620180d450810001d403480300340c3c1c402c100b03071210148140140c08480d225851300820414046d00e9a0700c104665448030081034602041040807280e1000a25103410140c40300c000c00b4005450307040d903583c019102c0c4c03d4400545da004000049000781c2d103040325039041c204050b20040360010644c01b180700420400a41164801503941500d03000340e000c2800140610008102420b0707038011801035814 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 480560683 1250 480559433 480559481
    0x2100207110d050d030b0109051005130308030f1e0f060603100e04050d0e120705010f03060503060a1b0f0c0213060312020706020c0607021e2404090b06030f040b0703 73
    0x7004c40c2400f003404140d9414011b0668000c011100c0347c0e114061145d001c1d044000302e070f04042c000c400810003c2d0b11303002442a056900d0f1242d030700c150021079010100000c528100720700340d0102c020b87e91422044282d54401403d000c1c0b4448001100188200d01034100080401c40030192204840c00506405c28105110302c1c1a160540d11100040c0590010403a0844107030b500e45000358111b19020000402803c4940c41d0400440f141d0b03503c07207007002c00d255407581c0200f030940b000c0c002d581c07180ca964480400c034086c490000e601144a00302079041002961400c803011a03030f1014895954a40443d40703102c01e141909540e00003400b040e0b00013400b01d44202d2002140a4000c500d00c81158030540907662a03003410000c0c0302c118070644500a42c420744003060b8005611100130b281600490203071025281801448050100d03032041c0032901e6003e24081010008081c070390040607540b01d820f4600608505001446554064000d00b00410040000000071043752007588a52040320f410201d48140d102 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 480561933 1250 480560683 480560693
    0x303161e030b090a0606020a06050606090a0b12011502070519082a041112040f05060a020c0c04020c0a02330903010c0809030406200a210e0102100207110d 68
    0x102d0080118000d01065000030110a401d110315411a0301d581c020348038120f6180c0d00c8400900c0d004140c3c540c000000d1111503003c0d1903d0b107561002d4a10341448a584010504007100000b905a00c0452081c64940c001e4140584c0480c8450407078006a6107004004485950400b2440d80d5402180480c8948141e9448007003020080b0080e04204c0e05580c5207102c40c217428001983e1101c00036072165442044100e1060090514281d0711600550000007090100d9031294140f02044d540350b80255004a4031a0640750144440340d201a0200e50461804e0000540030ba240d071b0000e440a40300702c80070160707660150754000d15004000c1400e101c00380d1080480c5c070001415000507112602a40c680b03e44110340a00400e921030041c004e0310011410146083d004980404807a0058541d000c0c0c81607441000c0e40302000f00d80c088901c10030b081c0c2036440c001c42d00c9400c1c0010748451081000307400c04d4146156600412500756204503c1e02c00341c3c1d920864102148440c2d100b5400c1d54110050f5160001800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 480563183 1250 480561933 480561941
    0x100e1915180c14010206043f0e01020f060a022b020d0c05090f1909020d0e0c0a0e070f1413140409110d0519030c02010f030504050303161e03 62
    0x1446100303411a4075807102d0300204040742e040f01090150340640c000c100402d928a802081142e40c014190f01800d1407a801a045407682c580d010002c0d040c4020801030564000c0c00d120f48503e8280300610b85420465a907130364a110240800f07d850b82d000401120054501000340b01020150003500c1c0d50b0f1700e80c907080000a502050140c0195843d01140c14045d0f4412403c85160070702c014940b022a0340000300304001c015600d40500303210300c552140090710300014005000440302c0e00c2d8000541c500c1d890003650030016151401481000015024001c140741410b006400c01990300d010301c0100b804070780c180d415496824448000d00e0b408240030411400404183d0b0039074075000010b0200094100a000c04d54106100081035183c0306440284541862150014403600030300440340c0c8528201c0d0707040034410001605400141c0150078490543d6005004212240e0786440c0421552811b40c4aa03905c80c000076000d5200d8140d0744000d83c22441c86000c02c0020f1503455007000d4850307446868060010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 480564433 1250 480563183 480563231
    0xf03030f100b0d15050a0b130806070212030a090b1305010b0301020f09121e07032006091012020408011a030703020303030f070302120f09100e1915 65
    0x6120480004440703042810701c0108460754007452505108801d6120343c0034006100700c0441d410140f10740010030355a260288030042141e80d00303a903a5421603101b0340d0f0380c15042d5003000d06030360b001e6000d000c400359000a040e242c41060b01d104640702e496642280c0041c10401e05c024001011500500c0601c03000303680c0d44031805100c1c0c0000c1003228a0742c0b00f814241d0041d00c200e8404140c0901004009050982036240021000b00544100080c0b500305100020400301200400e0352084c4414000c0006e41c010090700400610380c040f007a01409000550548a2050340602907803241e144425100d0180c1c90824104c503a526040d52215102c101850081c85104107103603920001000030380e05418040380d10015030707070054080d45c0f039542c03140c1c0304140807407000e0038840401d0740c01c0040310070040a41d480513010350b00100d00d481c250b0519000d40c0346414000011000c00034502905d8001d000b0001401011b1069204244e00e0504403e08103000c3d2500400102d035091820094001001030266030175800e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 480565683 1250 480564433 480564451
    0x70c02210717010e0106060801150215090a030f05090906041e090809010216050a1a190201020a0e0927010902180f07050c0303010915080a0302060f180a020d02040e0f0303 75
    0x288204c00c4040e10300382d4105204000125511800610500080103901d82400b181c1d0b00481c0c054136100503004200041c01c860000c06500000300400405901030b40c03420b207d0205240c961f041c03600c000000380c1d003041d01818182c8603995460031000d0441006400715221202c48804002020355030820070190b5109070f02060040c040d5110190340303030340000703020826510040d043c0050241400e000e0a0041d581c000382c06020101840704800c4038800d200302c007815006503030015841c1c40d800705002d030640302002c00443c0302e03007110703400c204c0071184000c0c1c1100d401d80000340b21250860781c042441d004007400000a0b400501200d0740d414605005208e5034001d004100c0741c0c031029030b19446d0482d100d01402100c0c19aa400c20001080111101e411188030321004581032072070555030711040351400b0f038069022409a081802049801100039103215800781a410449196074101d00440391100001c4000a1041030703160b45003815519aa0711400350300300030b48102d4051100b0400015940d400803552504 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 480566933 1250 480565683 480565691
    0xf0306150e12151819030906090b09010c06090c0f030b0603060a0e03041719060506011e0203090409060b0406030b0114010203090114070f050717010f0203070c0221071701 75
    0x204050000803401e02c071091100d105000b84c0c407108000551400616400403191051202000d01204c2c10301003006114440d4030341d800b2051502078003410520080e070040502d00402d210100260340c201004101941d4802800030b00d500f00c901c0d15210210558019001d40a02141d020080201d48419180500821000c603802c9a07200c04001c81650b15800c8460450b8200340400c015407021070711b503911000b40f00c1096a411038080458160350100301013043e01e103951110240441541c00040d2901103840080c0388800c1d124541001035680d00c950340c5594011545e84e4810824040140c2c000000c192004005002c810346d41e0400300726800c3c081c011058030700790740141c05400758000401c0b680e2090040e12800d40346000280c810a454001000a039007241010280400123a018420300010b8848404040c1a80840050032801c54254800c54101039104009001d00c0903040a40900126412035940d240c0b18401c1c42d0003043c101124031080d905206d00100840d0484210706402c1314040c110000f08 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 480568183 1250 480566933 480566959
    0x121e05070515010b04061428090312030b040513020637230408070905130219080c012a030c0605010906051f140a030905120c011b0e010f0306150e 64
    0x40b1f020b209400c440c501e040a03889528100210028800040c09100c5c10501c840554913200e103000c3d40881200080003a03640c04501d24145040e02c907280d007201c11106007525a800c1a40800c0c00c501c28540403084480c4d100312054400500508001504021281100c04071181c4400141c0300781030403420a500a560010307480700d8403000c1800d54040b5240301c0b0007030494030710341441c0c0001031201034088032081601a40d01c3e0090784039101200c0900005052a080152070103000606200300c8203111410003ca8100d8425045202c8000d1511740b0040c08c6104494009407400340e981111012004009a0800d00002200030099221000301e40040d01c905006481e000402c0600380151031009021802084003190b41020800144c0398140c214207001450140e1620707460f00e03040d8000702080721315000103090010035400380207603c1c0d50440c120706900c00c0d04c0042000341580b8a00b203100b6041141008200491030b210707801400041111064114405080d210b000b000f80c160700d4001c5001d030005a04403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 480569433 1250 480568183 480568217
    0xa0e10080307150f0609090b0403090909050601140d0f060b040c0c0b3709110a032607080c011a01110309060306060702060a0c121e05070515010b0406 66
    0x1100282e5000c8603010a0804000c0700e20014610134124150300c540da04808551056503100c1d500c0b00901402c504003403444c003494010304c00c00c031f2608207104143c105003154001820000f20141950028440c80800e00303031020129000c0b0a0448001d0040603140c00c005040c410168000e1036030031003d0b101801643d0750440b040c1c079070b40f000310001002e0f5600c00c8000384801d00d40c6900c002c451446a1103410204c4080d108080006000750103034855070340d480720b8000800ca4a101400000541a2039038a000c9140d601c03042400e02d4a2446840800304400c105044410400103d840c0c03035501031101c40c0c03140d4118024078000c0c142c0b1440b2100108003000d0944080d0b00a034160305015042d40000e600e00390003541840300580000d0521608000144055030050f52a00c0160404240a50720480d20000d1410301034203200002a03001c091040d00007a555181d401000303113042640c1d05003010399480040e0700d0603038500202c00000b1002034803610300109911b000c000c0180200c070038036a2013040c419081400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 480570683 1250 480569433 480569437
    0x50d050906130b09010e1609051024020c0901090905160b1801090f1202150705031828150206061e01050c030409060e0c0c15090c0a0e100803 62
    0x82c200700c40c0c03010300c05000015540b800e0700d039001c1941000440d46c904011000da1030220702d5003810220460019051221211600c2499417003080e0103441c00c41a0300d00501c2054400b6100d03404203180b940d111444148030300800c445512103402402664032507039609483d0b00100801c50b41180d0038010b142c90302c482c006c0b0a009410941d101c40303003031902d00700d008140c003000200080200c3e810b11074000750001e040900810180010010502459450f0b900c2d0b204000507070005c040007444402c03090150b400031a000000303542c3d140c48040705050f0b41401990014031402e00c032140c40b0907503e00499101c4208070800031004d0844d00e007a804031040c110704280c1680c03103001c102c800c030303070041d06408a407032692000c1400c609209d40c040c1045403414440300107a506640c0203422491590761207000c201f0440c1d44055a49a0110001d03c105003441182e01c011034890500c640c0007c1400c082c0e070041a110101448a2120702c00000c000b0a1415554624007105102c222400e040608048000281c51840801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 480571933 1250 480570683 480570691
    0x50a021306030c090e040b1f1406030a09120c060b0f0306060d06022206021b10110c03010c0c021c120807140c0a061a01090b09041b050d050906 63
    0x454050407401e0907000ca0080c580a042032080040400c000240041c0401d20a4010b900400c4020b5a9180242c6100c8503850100d0001c415440c140b50100012400c0180058041d042200c1070f66481e1100c26850003c2c01240d4001340040d0f04030090915120b4004034644079007071082c4007d05c01801d0b602c0030440300080d155542c0f5010740122001070b420349800503220360040c5c4542001030404c1160040510071a41c45140000448080907043c80b01c650100700e1107d10f00051441105042d0100010410540b2071600b20700a00150070700200380c0305024003548000380805402003002c4c406010004100b0810940260b00841541e081c0808502c00c031480040c1d06030b0000d0200d0444130320081d0403100040018840810040d1341d0003030821805101c8002c15170503900741c0c02003000c04070908011b4211100441000e503403c3c096003e5043e10390b00700450b03c1c100c030f0081410036100c540c100d011402030450180d0515440004140540d040ca41120140048201003d401c02c501d50390052401d640d50810741d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 480573183 1250 480571933 480571957
    0xe0a050d0209090f06070f1e0e0108040201021e03090405090712030804050f0d050d0c02010b091305010b0414041202150610031b030c0e09041211190b0406050a02 71
    0x100e0300026080c040d140c9504071040d201110b00a40c0f0400c8081d04001c01601c0310000541e25210b2618150b522190780404504010512294401c00500c0035218165600300c49050004000c0081d041d07a000313024420581c0c1c0104c0d03045442501c040581510b9901445025100d54582804942d2021000440c0c6042c0e41d843c08440081c0c03100785d10240c53381d070001041100c00b4441c1e1003020820007400d12005d04040b0382c03602e03404c0d21a000302074030720b0660701001c40100071685006121802c5540300ca5029800c01400360041c00d01c500c0d141025030250400514081d007003401c04800c24140602c042c48c0b24410b034040c800d0403c1100c80580c00720f81701c4903e00300032006040d4603400b00e4018a003820300c0b806041c0e41070500047c40c600180440c02d5555583d83e41130082952205440342e0183c0040400342414411100d6142030f02d015999000048050401c4204103c802030603011014020400340124042107100000c41c1070399440e248120300f4088404a804908000124411111600030355800321110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 480574433 1250 480573183 480573199
    0xb01090918061509020a0c150b091611010203090a02010e150a0e060714010b0a080712170c030310050a09140a0b010201231e071e0207051f0e0a05 64
    0x640715540030f0311060705541c0d11050303d1400011014202c0c4004d2042d07100c16102c19024058900b0513080d0014840d1800310707540e003071200c0b104043d40c0d612038555106070101c0c0301220403414000129808001000c503d20390758400002c1c403541d001c0000340400440e10036030310050b20741034407401d0008821034150740780107040041c004248030302d0084200c0e000c4140050700141c2000c40a44800c8083d4007580003a0600b80d544550704034a80c201220317044050320500d00106980c91512118007007100d24a400908210900c1c8083c10307201e800d0344201c0c1c440c0d444080440780c0700d043c16044d0103c5c107091845518440d0585520001c0e40c0c519502541007000800040d044041e50340c0d4209002511013914040e0455686071002d240c015201030240b6510489860500a40c2c5019420f11902422441c84a80c900c01f0074001c004400c2e0f4001111502000040784103514030300300f00d4003645031007082d400c03165202b110810040b5410f034015003462121509a0344140c4085e0400c0e052000900440c06281e0b000104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 480575539 1106 480574433 480574481
    0x1060b04060c0510090b0f0f01080c0103050c09090702070f0801051b070501060504020a0e090c04141309051915062904090e151501081302030a0c090b010909 69
    0x103298035080303c9506000075281c2e907081414001ccd040603120780000d4951060b6109403441190041d005444500304010040d48a030718a0107544141c00320f03540c001070440c105029481c000c9034441c58880301d00f0302e2006c0d010226440a10207903040d640b1104002066151407004015610840e500d507800d0041300790401006190140c1414003a1406110611202c1c1005a09601e41d810031503542400f0070028801c407004d40103580000d06140501d40344014041e44445666460070f100301c102d0b00c1400d45660400703080307991900554040c0075501c2000410460b08240118000000780c0c0b0315800c0c0341c1d4410041003940d410010040c800e80294014880c10302e40c00c0036250300440c04504102c0c5986c0f0140c0002d00a40d001002604c41d1701c101c1d40d428003503403818807000396411341049265844645510340d11014103c0b021000d0b0001d1181240018000b015101e00b40d018a10104030075200c803c = true := by decide +kernel

theorem cover : BRFrame.Cov 480395683 480575539 := by
  have h0 := BRFrame.cov_init 480395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 480395683 ≤ n) (h2 : n < 480575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
