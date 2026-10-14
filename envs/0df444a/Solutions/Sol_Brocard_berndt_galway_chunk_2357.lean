-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2357
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:28:28.530599+00:00
-- url     : https://prove2.me/submissions/483fac1b-d84a-43f6-afc6-eaed8603855b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 423741007 ≤ n < 423920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 423742257 1250 423741007 423741013
    0x70f06021602030d020a02030f16060f030906021c1b05090607030c0b01060c1704080c0f040f050c0903070501140a0f050d0c0801050f1002100515031204210302070b1b 73
    0x88030345e00140d00300d00d0b02d2083e001c5c2e034800c92100300720360399801c0300400c0d003074605090290a000441c480c400000c200d0301c0d186000b0a00c9106915a90100e90081c25900e000303c0d031001c0c44400681c03041c0907140c07510488034003050b003124190300024510700510b41c0140c0b01c3e4100007100424144510f08072030001d074110076132003045d503500c1002800303c4038a5030b42100c24017044101c141d02e6080c3c281c00d03130301200e440002405003220084200808014210f01035036100c0c3d950440083e0701e003070a03c2918483c844050145544020741c804142c03400a141c0d0010341003160045014051080081c01c1c0c07030142245c2d0908018001c4061025109401010a0045803070329144c8001070f89940f28807843d040b80c0d000c1d194284550411030501c060900c003405044056031042c01c0307141103038220b680410390201128240907a60416000001c0c00c1028501403144480d40104080c04005c1c0c04800c010509a80c18501e000d5515442d078010b5103a452a2240510081010400e4030136081e801e40d401910305004029 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 423743507 1250 423742257 423742273
    0x1710091a0402030108030a08060904031e050f0d06050406140f0402030403021c030906110324030705100816170c070201020c040603120905030105150904140105130b0c070f0602160203 80
    0x203421b5894003e001008001100d88020034000d084c1107004a0049425903181e101a0008450714004401c41401c0f540c104042042001280b60300754011740494811300b100407510030301d4201004103440381c580010b00cac1e0800c6042086100d80e14612030360140d202c01d4801517107035900e909041e42046a0030245805075006041c0304655240c0c994013074414176101e400100000044048007680e2800112411040c0005400402c68401c3c40300182c8102740600404031a000b640307403030200d00c3c00190740548102060b16101884001d04650380c81126003603851411200c22100b01c0e4892200e0040909180c1c88100c00003090400e5910a0100d0245c040018000b44085980c03850300a03140e2944615404c005603540d0b00c007155920341801000e0148041c0d000d1070414070f404030104110035102402c200d41c4c0f11064200344604101c28024580f040003241008010f40080d418244540c8100400a4404480400000c0d001445d01c04008400382c4d00321100503200d0490309885006118000c001942c10301c90b420b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 423744757 1250 423743507 423743519
    0x403062007030908100b100507020f0a06030204080f06040804060f0c020d0b041a09062217031b2d0c0703080d111603080603031e030105011710091a04020301 69
    0x20f042401c840c500380458003640d24070100c40086440c000d80c95903208034000705428801e03100b88041c1060500041405604e12807400014443c17299652142012a8003c03e080001540c00c0c40b00e028009098030140005107041d580c3c07000746128502800e07042c4581101a40540c0b481100b018a200394080e0004c108001503040c255800e0100711021115041000511a031901d0b043c546c1e14015009580145801d440b505040b8103c0003c009440c192015000220408941840001801c480e00181000da59041013440b21101454010600c0b0032054200060324844402c4c000440305044128000c6c92296911a49454944508040340368144920f2501105101c200002051000901c03201004080c0400800c203001e4020103070400608030601c0300700000300b030041c00029402900203042d40e10b020081100e145414404a00c1821021000f20044c403443d41c0003a0401a05d505e01a0002c1c064034010300c4085503865907014031400380d40c840c031100d648144c0c0c0356810300c58100c009000755200e6840354 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 423746007 1250 423744757 423744767
    0x280e0d2001180c0b090a05040e01090204150f0806010b0a030f0b04090b0601200303130f0c030302070509060409080d0e0309040e0c1c02130e10140403020f0c0105040306200703 77
    0x40143c40040030040001210080d0000b00d5410f1100505050040c1e407a25040000921b9032401c0c51143d5500d41600c1c2c001a42d035031243d610303101c031100b0048202d5070412840c848000810b400c11303c40d95000400502c00000c0e1001511900c0340d0f0b41c40e01180344000742c2c603550054035400810030b03005810540e05c42c0030010702c1000d052044400380c0e50000070800b5420003c1403809102e0307548509410030404101824000e2110104940c0100380c0c1400204046d641e0f0100650640d00950050700142000c1c406031030b00f16255904000216003c1c49882001e84400d00c41d441102c10000b0790315074404041d0310525040c011780e414240020003c119000c18104d1003a100c03e0501307400382c45112420b0180c2c000707440e034000a030401a0050300c181b10514a901084004044142c000403151080c01e121480c1081903000300d240790b2440c800d03001100d04107464060300e00801450012020382040040391490b0b42d00c0800e03101181d0300700e40c0110341482042141400c558403054000100640024280305060b000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 423747257 1250 423746007 423746051
    0x251109010305011a0103110405040f020f040f090f02090f121f0b042f160f0f060c020f060c07020109081506100c02030703030e031005280e0d2001 64
    0x20004d00e292030f00a580110704940c19010100e007040780501061102d0700f0190f00070151104e0b0351000510703200b6914010744250b08146e101c8400e04203084010721140c1e03903500900c2e52040154005608081c0c0b0500007135880039801060354050205003d11106900003003200d004482e100e14100c04468000c0c0001801800074564041e0240f81040f1600801800f5082d00c01502000c441e110303a0420708000000190b40d21420b295581149001d070070401003088414075407440c500c0781c03040c0c032099a418030342101900e5500c0844419274000004450400c4c1c004220950300c12100d940d582c1c3c1d14401c1c1c1c40161000e1416400c500194892654940003c0500002c003900401d400c80b00118503220403082112800316600000390581c000c0c00081001a000f0311401d41d61280c02000c2d202406003032024035040341d1040700c0c58000310702d24480c80c540940b60881c0c2401c407aa1019401e2080c0c0030540c01d40c0b5070b614410504c0c2010809010807507078511900e01180e02c0e200300c03880001e0000c0b9800140300c070380c68419 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 423748507 1250 423747257 423747281
    0x71202011b020f0d020a020a030602090105070503040e0a0609090b0f090f030c0d140403030905101209030c0201030b0612040b0a0603050d0503100e190f06050301020a090e090325110901030501 84
    0x184c8103282c942c68000038a00c0d402c01d5006080c1c520090071651602c000e5004100d02a040c44424091040040c00030300150004e03107200d055224031460242c13908410b550003940108092850000711401180010900d10703400b04030b040800001c2e403504003905141c07204c00700018642c0e020224141e0b41068010840e41080a010b03a07560201c82c3d02c1100c41031052040381701c0140400c2880c0000c0125041c40030683c80d02a420f400c00140740120011000152406850218002030a0a001d201150b030180b080180704242035844504101045854807400000a0000792843c1709000025403213180301c1d044030014691106c2078440d00c0e81c90000c06403254005482042c0701e06220f41012a14491104d501031280004040c0060480011180e50300140549201840171940710381c3c01141c183c500f4001410380c01c40c190380c0c400c2300c00d240200c00c105204003c0d0184450390800c0080d40381030b54a0107400010940824141260040b0b60314020a40518510302a078110509400020030310006500c40350301856 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 423749757 1250 423748507 423748513
    0xc02060412150b01181401120f0b0a1502070306020d1d070911030f0411030a120e01020c0a030c060809030403021c0501050f221703010b1e0f071202011b020f 69
    0x14a110054078418007910245c4500400d444c0100002c00429190800051040c1842c2004240240000c815a401e4841d41003040d0345500c1840400d0500e064402c0c024504099a09044800c000e00252a442a480041c0c0183d8000c1880302d00b0140381d034490703a040b0365104411180c205500b03c0c2103440341c00074803408603140c5c60f01c0c5081d652119200c01705c030300c641607000350304400b41c0ea00d130740e90243d048550030441d4040c815255414005a03a01741e0046102d40643c44800e5078088039000203142001d40307141280a55400c1c2001c00003d4000301300d00c01600c006041c50071090f44c400c96154130318055980040d41c0301c1580c07000000d024807102d5082100034044d0009014035521038080e681054000c1d1990502450480003d5040220501e65944a28030900b40c071b0044001450001c00c05030002e81200141000008901c1c7c4141c9d07a84c0c05070f80c0700e0b02c3d07440b1038282003005c0d8621252403400b070b0240240c0115551040307404018800c0d400303e01d41c9410f800c0690b00035401e20f50005e5440c0203400781c6221900c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 423751007 1250 423749757 423749771
    0x313030308010e0606121503101b020f340905010608010b16030809070905090303060307081603120903020910080c030f190f021f0207060509010c02010c0206041215 72
    0x3548002d81d03072003050050104c2c4d180042c440c0d0034280348000200141038100c2c003100780040750340c8c061120300b10b01000d075a00840c0340926980340090210310801040b080d0360001051002e00c2d4800f080582da58003840b409464014046500c0200c0b029800024000d4500240c90108040b10f8aa008605a6170b10380d403a0b45441e070f03c804d01e2406610801c10041c0781c402c080d040042c0042e01c100e0007150311041e06030944803947e83c3d441c0340318162030b41070f0b41070070ba250800302c104003560804020354002800090018540719800e80a104a00744840c040908058008040303070030590f01540701c1d44011a4080d003101000c2c0350000c1d01c544c0e00303900d07402454034502981c0ad0030325681c50009182070b001002d1501410300350000260640c04a02d1410302264860b440a001b074000d0382e030f000345103011010003440034224a40b200b040203080410640001041c0001803049505a99202c0c0c60690019070a0034109030100701800095418065a1700c40401c2e206000032550404c9a02c1c08003259500312600103000032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 423752257 1250 423751007 423751019
    0x30203030a060b0715050c22140307030b0f0702031b010f0f02030106050d05041502040806070206132a1505070309080105010522020d02030c0301061806050d1a03031303030801 77
    0xb034404c12102405484600120b00c1c0020260782c0100d402c010380700c184074601803800c54062840b8101062448a0803000c807802c101580c03a030032444140c400d044010706107441c02c40c4c0c0c0708607591601400c01c40c130440e02d200004100c98000c00c11607110410042c0301a1010000001480c080c00f003001da07440450b401c2c03a841d98030184160096a060729000c0d10f465041c031401c21450070080800a209441d442c9030350b00c10322040c050340d10091000d06034000142410f40741c0308802a00d0480040c05031481d900d120b001030800724580300702c008529905484800da01082c0042042c0300300c4416005800b12032400c420303110000b60460001d00501e0721945640846580e80c0b200e0900b00c44d8240305003900a02d801c0b4150b940244103c81407403841510400040c2815041380305a0200d8104403181020014004018010340740c01082c142001c40c1790f03184c0d0040031820240700406134000e2040305040c0a80301c103400a043c030b0b00e0400c1a016000c000d000c50303807165280c9400301c13505000e611042c1d0118501e0390011646c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 423753507 1250 423752257 423752279
    0xa051b24090409020105070c030812010f1412031e0406110c090402010c02030f0304030f02150a140c0a05030c030301091b0c02060f09120601051f0207090b06090607030203030a06 78
    0x64049080c0419081c00020410300020344280b840c202e04000040201c1c10004090400a00c0654000d41c03030386881d11120b00003403880c40c4c0180c10480c0301d1028500304000400e00b401c00c149178018103481c0c10041500c0716064500d94025000e183c45580d0b404000c600600b04e6010140003195804c0d0340c3c01405080040d0044d0700c9070001003400b47c01028000009002d075000c0e81c813260341584040e080340c8040034602d441c40c2c119001904111040e02c541d04d40d0006500c1c090410b65400d00798600940d20f000740c0d4010140c40402400c207210702d00c910120314070241d1182840549500e540090aa030703070700d03403005d45415147c1d4000d024480c01035152000e8071880502020880b90704507031710f440d40384a220880e02000700a8010884000000340304109800c1a0b80300c2540700d11704000044000c2c2102c0d4105800c10549201064500c08010301c5401304080309940000c001c411513544000005d40700c408070703021681c42d1148000c42c41d004400041c00104040e4004011889030800035010014107031034000c4031700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 423754757 1250 423753507 423753559
    0x1805010b01030b09060909031e040510050414130e070306020d0c020d050703030e030f0c150702060c040909020a0812030f07090f0b0c100f0606120203010f03080c0a051b 74
    0x11300402c40c00c0014810b410101c000740d0304506518100d81c10080d040c801c01410070701c82c5c040300481d04400b1508020344c2c1840c0b64003051282c01810310764149810a100580d8141c2c0d04080584030b008a0140c0d28a416411b074013040c3c980928005076100e03c0d40b40d04146019601066032680500d162031030506140b4030200e45102c214146030f4850b8505503494038103c001c0d20b03c000c1112440c2c0810030100c0c810221900041401c95040b0014000c10203038105038000e191b90003030844003550030070307001c00a4995944046606031030300f01d1f50010326103500380045842200c407500803c030207114124049a030300f00d50f04061071158040790040b2115a5814400b281d0705101c0b44122586440310900a0002115010180c400111818100c03003404bc1c2c003141080549a80289446805650314014400c10b948011010755050300207505502c0c6516100c3c040102c00e19a100181c0b200c0c0002c2b60161301031105112031f41410390004103e505c03004d11604260203801c0003841042c820b103074044103004001d0310303085025 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 423756007 1250 423754757 423754759
    0x207170403031704050c090f19060b0f0d0f0f0203041b0608040305030405010b0d080c070b030402130b010203070f08030709060e091f030c0e062b08070303020d1805010b01030b 77
    0x400060244444a018002400c05c86490003202e606090765200c0c100070368480c5c184c881011001c1d052003c00c44c46000d0b005080115180c0c1400c00c24090050783c2c1d012580c0031a604d40d40c6a40e03520511031181c00910f0400401c0356820300b8070600c20052810f640255000c2ca0041e047d0149076501c3c103050524028080c030420780421503910026000c00d0080e0080d50303020b4011070006c46c0c3c0c180b4a400065440c1c45000d81182c801c107000c100e0448805080105001818903a403403189142000d0300000c0d2000d282c40c0042080e251680c543c03003001c0c0d100344151114242d00483c1201042d145207008411500211034400004111580002d0399078860341007841103100107070507200d454541500d0060300448400403510b400c44202c200000103107194060b0001458400007446940c1803410810500105198078814404440c00c44427002c03420301d0302c800c6550341c0d04c621455680c411a2400f90081c1c0207010550401d00e02d401e6601c01518100280d0245442c0308900800c0403640740c01c01507040750f110408003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 423757257 1250 423756007 423756017
    0xc120405041103130b040606121506090b0102060f1510030902040513020d0b0403140706021b06070206070e01030f020708033102150706181a0f06040b180a020717040303 74
    0x2001140406005c5070304180100303008150243c8540d0b8201c2c04600b880002c440e2024807030400381e01c07120b003485540d01425a40c803050101e2001c1e080000c0d901c10000d0041c8240346503d501060a40c24111070240c10408013402c915030701748c2c08140c042c005240c13114041e4042c030b041100180d025100b0074200c0344540d60003051000c12500c2902c801001ca60010400c80601140014118441c82e1400142c05203a202e2035000d41d035404002110740070403601e008060398030b5004006202650750089003041c5e00400c0c1c0e140c14208079000700d0048019200000100315078500c0090604280000031008610131803e80443c40741100d0307a024081c61006c2405031002905098003042001880c0c100c0b0307900440c40040c04110300b4000d4030340300c140498002c0c08054400d650354400c542c2c00c02c40c0b41104051408000a400d0f030092070504020409418020300c0144910b030794021030750055a5600180c401904c00b0740c0e410055281c24441d15009620000d400e80c0c04a5404406003505200c480440d0143da40c15070b50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 423758507 1250 423757257 423757291
    0x3040b010b040f271a0310020301082a10081501080103050309041104090203010b070b0c0306031b0112050705130f05130903140f0901080703090c05150c120405041103 73
    0x458044198410313825020700d000d05044041001c28001c2c20030540b582000e5140c4165280c0400d498641e81c114802012801400100840000030442d000350040700e40c202c1e10b1903070001c0f642106000036082442c3d8000607451001c00e905501214081c4601078181e582c07500410b9030070040d10b4245007440000e1032603008010ba403041c0d003003641041e074106a15051036403d0940710b910b0407003641c100341c11881c81ea0b240410a4400c1c08040d040541c0c20254500c80c55146040078808a522001c401e94951001c0c0022510022740e40d02c641d41705213200110400400440c2400000100715901201ca980c02d19203a480c000300e0301c0801c5201d14400c0f101c0041c4081058503078201002c002d4400c0c0c034800c0d03081c4012640c0500303480f4800c80081614800b03240c1080d6881501300300142c500314000d0500c10400d4900824030001035010b807411015240210740300b2901c0c0c4060100c0d104944a1076a01c1c00c1c090007550300c0c010011038000e01610548004840034410208091801101c501084860002d421f0140030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 423759757 1250 423758507 423758519
    0x801050f0414030c011a030d0f0909020708040b03090a03091e14010516030302030601090f080c011d0d0302010b0a090519020307020a060c0f030f0b0607110310090803040b010b040f 79
    0x80401d0b10480301c1900d041c100c2d0020582d0071607081c85038002101501c0300301040c03030b4501400210201e28550030301c01c0205040490045c580401405143d0020390f0015230f000500c43c400341598005c02038400c60300d85c0c0c0d2611006803511981700b0101140030a16050700030800311091551003a01d41100ca0400e8030641c944015070a409a44588490601101b0808140203d12620341076022038002d84001d40e0740c0c14901c0006203000d4103540540c02e07135599034406214100001c110040142d80034a0b101c90010040c004100f036000b48400003035440305000ca441010190103420400304200229000d0030300760754030080c00083e180204d4a1907410f101810400c410304100340d002d9600000e11b84125414043c05a840c0001c45018002c10000319a003184071042c02689805450300328a90140c00344110401382021642e240603401c5d00408454150b4020300d916101004062900f61100000340031601d41c0d418080801c0c0c1c0156800c1d90705000302000825082440c0b022070302294920754590403443d01d440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 423761007 1250 423759757 423759773
    0x320031b030a1e020a0308071703010b0703080912041806150203030610021005040b0f06010216060f120c030501150509090c0306030f011104170109080f090a0f03080909010801050f04 80
    0x80ca403c0168101442d800d40542c441444c0302016500c00d1a401d0740c1c2e11102d042100d040d0600210170b4031448410401030090255031810740d540c0a906007000242502c48505a03810900520300e0011040340c045030000e080142c1f200c03008030501c80b15108108c03240e1190303581d0745508804080800560700400c0820624100342c3e071220300044043c03041d540b440c51010014410303110161425500f1410300c9050058002010303454580000303090004000d800180c8a0f110841419807098106010404d00b092101f14040c41c6408517003062280204009022a01c010307008000a009a01120700b00c510221440740c002d80803185005002420888160f0740c2c100891800d81c0b0003070119405014603500180048024012602c806030306002d455166418140940c200044001e181c02c05a0b04020640001c192901c00701c4030022514203040d99a41d4191010858100c0a0340c00001034841400c00041032107140c0e0b020703169009003201c00514036661403100b00d007654402e1700c000407500040c10104000560391 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 423762257 1250 423761007 423761033
    0x705360601020a052b02030a02252402070623070602090603130312271406100504050606030106021b4e03071b0320031b030a 55
    0x144100e60310b00da0f03580c1e40c1c681402091400708505448810444400d0101507400700d0691549200131410300c407070758000956409080c550341096a16888244144022601c00d04029024483d031003100e2003d506038030700f00822007181800050013001e41c0440d071b062140081d490b0b202d060b55403243c8110b0030018a40c840e07611104d001c035510342d400c0141d0f002949590300914400d4210030241c080d860b0340e038240581a512564450702c60a880c0a603107403001e80703005e02c000f4400c106403552041170601c0ca14041002d00d2010300d55018610410040062000c0c0d100c01c0d14082d10000c0d00d090042d82c81d044180201c5010070301500c000344c1c00c0b1600d01c081c43e201d41c00717004000e21001010621400310f8400c0c81c25111034001c04824805260395100c84603180340c2c180d5028489070300024481e140c1e0740f00030440d44030b0148a030b005101d0b42016400242c210010700130712000e15088074140103820050340503184002c0d8281c42540c00b900030000b2051020300c5c402d42c0d04100a0024028110300304c2d80d6a520440d074001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 423763507 1250 423762257 423762259
    0x190b0604050a03060c11030a0f111006151206030206162a0e1302030a0318030b070306082a01050d06090204030602030603061003030c02060f0c0f07053606 68
    0x420311002510759101c800c40c0700214090780e4005142414500b00401d500180c03805500310754810820b800003207500c00042100440585000c01c0b50070000d03548182840002103000442904000c00860304641d00842d030742d0300850300d4481c000b2444100e11280d054406074800658044001c1c00740d000800303e000280b2080d548540350000600400090304601507911910149803e41cce4008284070010000036030540000f21212041d60b251610790001c0d6454881c6034004040100d50f03040c94018244403085640036551002112007140340c03540e030040c020303c00c07489071441c03d12440c4240ca100e149014900c81c0c2d801d940412600d02c0504c518019200c1c1d0703002c2c00041c03104035590300300010030504a04c081d20180d0311505025a40b4205042054607190740a03040140b080c828000410010303070401b0036446059130654241d500c482c01c48500d060540580e448800450090074503410044201007441025034070225083e02c40400290220b030710902c50b10010081c4a01503c03010502c40d0480080c865002e14 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 423764757 1250 423763507 423763519
    0xa0f060c050d1d0111041802070542070206011e0e2a1908060109080105160f03060513020706020c0d0302030a0c0503040209070f020c0a0b0c070b03190b 67
    0x1000580740c90483e0200d00007030500010710590f40e5110302007806818210508031600e20b0500c0c3c248003100407003074034001040c2d41302c41d40007a01c041003240922050740b8240308095505028805013103804400751400b074130010700c003140c0000e1890000401410030b001f114164024501c0b0f031b00381046103500080f034515440d446804860005610290034100c02d10030b03a01814620420880307022200e43c1d105452050441c034071400d10003000c4c1448054620b41403a95245003828454840b1001070b40c15489580200e07038a9400c00e0100700c1d400b4240b507102059500313175580d98041441c00400442c00c0340c049004460303000d100030b141c14036510115000313846042c1c000c0d4001890503c0b41012a41f401c8000104d40c00881c0c0c000c03003080340024552081054132400d80c10b00c20710b1880d190340040c2d4070340d00040800d410701980004842c89648204614404460301920118429440e9001d4180070340040040103007030700c0788c02000705005040e070701a01d00800300b880b80351420304c0700005044003908240001640102e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 423766007 1250 423764757 423764767
    0xe06040e06040f240e07080d0206070f090b03090d1d180615030f01090b0f0a0504020304140316060b0f0306060d1407030c1e1a09130f06170a0f060c05 66
    0x350300640038600000b1070b00e13000640c0420740c0c03901741d040913040e60102c40c00d904049421281c84c0d80201e0a203902c20b005140c00b058401c0c00d0f1030180e40860450308003c10b910404020010000c0c400644a08a00d402e030f00e46614040c0c0368000180c0241880450640016600700c4405c0c100a00300000c5810480013848241c0e01011150121181d82045410001c6002c0610040200302c0462007148503030142500d0b883c44601101c0007085441c6410f2082500595001001030127100119020f61144000750094070313556091006640d05000d08110140e42961401d00450002d107170140020098040140240c266075540c42c00f0401e94140110040d140c2404480511910400512402025610900c06038035000e0030013404603c03044400700e04880d51021f9800030b00444d0f41007100510401d0010380344503904c2d504036001c130301c1c036080609007042c0650405547c3c481260881e0081c0c0251a075142d004080c07960703006003d513540c552114000e080541440500c0340880d1481d04542c6100a00e418414541 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 423767257 1250 423766007 423766043
    0x15150411070213060509010f03030801120503090d0b0a0f050103050703020918070806010e07020105150f152710080708360606010f020304090e0c0a0f0e06040e06040f 73
    0x41c0f400d500807900b11a920728040c03100f07151581320240944418070b039a101c40ca046590141011b0418000c0912500100d401c550401c40200101c8041103400352010614107038502d40380c41c0c01142920103441c42402c3c9a80614200b04600c2805d048941050040c07103103500d982c017800205a0302030090000c0c84036500d04030060305001c010130780c01801440010710040d8500310454030480c8019200000b10b90400081c130001d05001d448909000c802150440405000e00c0300050380801307403143c1102c02c003002180004104921720324120050140c091006821003040b070030008080742c50002c80c404282c8410120780028801c00055500c4aa036100c248040c0c5112581c240050f82c0c00e600c100710508603400c02c0071603c0d4041c01035981041c401c0c2072032203080c0c2d0201e030043d44070f0190f409440c40e01a5180b4030b400301300004114040300188050209102d03180c407038000728a44501c038000c6001c0c440840c3d010943c9802c16105003210030340c50001801c0076032101d94a420107000900c40503260038034120246c1c811b0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 423768507 1250 423767257 423767269
    0xf02040204080f030c0c0924040e160503070608060a0b030a0204030b01030516081c14161202120304020616030306090c09050a08061b0c010f020714151504110702 71
    0x48800700303d0045450b010a101203d15200040d28400d0041701e004042c06101c4880c109504122000d00d9240d4503140100700c00700300181f0310aa024a4644110911032001c1520144020260b0b001a016581942e451b050705940002040d500c45801024984080141022200203960040c00e10540907150a9503030b200c50b00c0c44030003070704181c50b145c20624085404001209e803410043c002440a40704400c64941090002c81441c2c1daa2030030b1007161000c034098050500229208124080c15aa401d0207407802c020a25640b204002d9016100f41c54080300305000c1441503a110b03c1c0c1c02480a4500090701c0e03145074640d114041c0c102d05158036810f01207400f00303590241039120b01003903481c003030224504001c00542c540988d0003542ca54201800703001441c07000d001e042d21030480d8418040c7e41c90110040c074500505503110300c1040c20703201040c41c50820134404c1801c3e5843c4403d10071140c200034816880c040342c0c501540c03110341c15200c1d640130300420b0405420040b058490f2104441c20700f0059000705071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 423769757 1250 423768507 423768523
    0xa020d0203040305220e0a020a021509070815010e07210c080a06050103020408060411011b03050d0b03032b0906052d04050a0308191401090e030c0303040f0204020408 73
    0x4200082440c6510703130080031441105900d0785d81c0b84c1601c540382c00640043c2007000750446010540000c0c451010394020421964440302000c1c02c003e4a103040044151915044d0080594500a1820840c0f5407000410124180d581440b0070000c40e407100d00c0299003041000d62124820903414564540b1002140702d0501110b6064881107007030b242100280040ba155600f00605051041c842400484800224507502503230205010806500120059419510f104031121508008101c0c400c105035022024240f8981ca4440a100c2e10500c01d04140d00da01407040c03190801d2400f1140b04501100c07181d401e00c0e00b00406100001e60900740c0e140e440c26190200c40c2d80010020070341020000401c83d02000d00602502d07118000181042c0c2c1d9125182c080f811005020040c011020800c21101211840c41200040100b040302110f0062a200c2201d0240315000e105850010054111040402218000520040603500e1a92241d40740380038003c41c0700e01a03801540c00d200109030442c04201c490 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 423771007 1250 423769757 423769763
    0x30e030d05040c0b160807060b030f01020d0b10121104151d01080f042405042306280b04231509070f11071508060d030806090a020d020304 61
    0x41502e150500309102504880da00901c5404002c10407190007494a01910050b2640846500c0d907503d010704000e0050000010b1040d4140079107500d40551010546c020320221803220000d00038200400200b01c031003448400b4040105014003040e80004010380d0140c140c1c00500e0701c0d22418a030b00e40c120b000000030610001800700b6040e1341120b403d2202e250014480341000d181850881c503003003066411601d005030008040d020800c00104054044640301e0b40e20a0502104100c2d61400d0306084a03c00d00c861641a0f03d20920720300507031240f0011450307501c04c0301342c0c2180c60028030890b0031a801b0f01c0001c050070080a0341d1a000c056250f43c903402402c0300e18940e1000840f0344001840044403161004e400410381c141001030001c15520303442074459114005040c44110310707041e041c00340c50502c0d61004d94040b5000351036010405d90190720090a600f800383e40d03440704a03660724082c040c00304000f81c00540401e40503000100c080c5480c000d07a6500148210300941401e080e8424030003a6003058500b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 423772257 1250 423771007 423771011
    0x20706060f0807030b13020f040216061b0908031e0c01090813172a0102070503060408070506130f02010e010201090b10140f0603010e040c15020106050405070309200414160e0102030c0715030e030d 86
    0x105030dc00750320600440240c6502000f46141c00e104412100041c1044482c942c82400c01103184080e964080d401129100e070040344043d61146100580c0c00a52820f00601c540c00070404031103400c00900042050300903a000c0030340001440c0d0003500442c02404411060704500c5010300c04211074400b4030886005903c03070001203860303c00c130740745c50390601800400b0b5602c040100041700000c124480020008945c080c00e144168030040c000407400342500d140e0251840d00da400502180c0250b500e816070032100284000305ca13000112007006481c4440da80180e500520902c0140b0146c0c01a10405030407a101e20700c11032a03956900c2003525442d440707081c000d025035034441c4200520304140c0105980220340c0e140802c501c107072641c0c400e000c1e0600d1444048601c1e0b00b05107550882d0300c49500c0f1030f15410b900045800f140ca02513071801c9013410003501d0301300010502601c90455500000c2a80e104542c04030260501c1402c04500e04240341603201c03c9010907441d108200d03000c440c24001070030850040000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 423773507 1250 423772257 423772301
    0x3231506180408120c0f0a18060302073c030201050a1d1c020f070b0c0c090402030703061e02070b1b040f0504020706060f0807030b13020f04021606 65
    0xc0114845010301464403030807824041000050240e401c90304c0d080c070151004045604c0b40c8040e440b150080d66138440c000e020010315000c000b500042aa09a01040613031280e040e901d401003101030f13010700c500003003403529084c168003001c0c05200000070250300882510b44258085106000b03500701d0034401034000d80d644000344000e4244034002d941c40d045014420407003110b20000702c603a0f9030484044415960300c15008840d4003603c2400100545801701086a02c0c0c251564a20306e9140d02009000707484e807081c80301d03036107141c14682d104902c290f40050180c00d00341d141d511204081d140d80310281c412840341c081651031000d04d80c805040d000b170040c12149618600380d8200c4070f80860503854030600100c288410041c40000c1400c0380152841078401603115861864103902a10b003981200882070309410020405407400034084c1c0c02c89000e03a06015540c2c40d4620704207160f95140c18040c2d00007030a00031071034150070f194000703201c072102e540c242c0b0140c8611510b070207040b2410100c0b810800c0c880d8040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 423774757 1250 423773507 423773509
    0x304060503150a031a1017011a030f0c060f071b05030f0c100f02030702040911190b04060503180a030201050106200d0e031c0513080d080103231506 65
    0x50307006107040c0c140c031820001ca00315111810849080040c1080324140000003030b0100c5031a08003500103001f5640c0d01450340c2d1003141d545019041c848104890507800213560082841c5c0025030a9014045c10017a04a41500506124807580b1081100221443c00c01a450001d046405a500483c01910800780d4150524042608055480207205c160354015460000683d130392115203011001c0354284515051400751b003e900718002c81502951041c50045840d041c880c01e140318081c0707840115562000420740d1a00004000303603502078211107540a10052115a01409c010354000c94000209144031599035515841d00c0c0000d00100c0050751220010081546c10405003010032036000304808805950550322a40d0b0031407450800304001c0f02d1100d021040e1810b00c103010307440303503043d218003034901e21800051700e2a403080320f1003805560016000138a410002c80d807014460f000341c0c0c40c13000a9213140c80d000c9110001d00d0303160540030320b03c1000c130b1500001004203002001d0180781c81340141c40c0c0380b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 423776007 1250 423774757 423774781
    0x3040f0b061816090e1f0e0f04150e1603030801090204030503070b040206091207051305010b0a0804050f010c030b0a05030d090b03100e1905090c0a14030f0304060503 73
    0x58100d40c05509803040c40c1e580800707640310725035005440d100d00ca000380861103c219158943c6900211100c60300c0000e2003108400c03003600e00343c10351003008aa4100c50b5101d03500c4480c02001c650f103000d46481c50f008100003c01c000c03501c41405c040342101007808503103000c03038604140c03942c2c1c01c100900c0c01d544000c00c10580c01111650042211074011401d05103180c40300c684a1190340001844105401c001404540c0c0e140242c9a840c0c1000d005010f002440e11a45540e6040c10700603035116082e00c80842d00b40345a10700445060311441a180d03401c010f1104820b40e00941c005d4411100d5014100080100b040309100d407100174001036a020842000000030301903034140f0358006234081d0b0001061002c58a421842d2402180d070500100f56495807400e807040c9902c1c190307030000c0c40380c8e05818040c4076a140c400745144611a4402c8400c004940b40c00700c90a603181d13a400c0c8100c0d0000706802c010000320f2028000b45c0e14060024041d11002490011401c1c1140d0203500200f001c68004401c1c050408032354 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 423777257 1250 423776007 423776011
    0xa030e010e01051e31080a12030b0a031506050f060a141303080304030f080a05010f27050703020a170705070206030c130e0601021005010b03060909070b03040f0b 71
    0x3824264020301d08500002e015218400340000b0b6030404071203500410f01d1210464841c10740c80281c8805100c03845007041407400300d20404040424a050002c6a0f1a03004642d800c82c0b250305c06034902c992170440c0d005070050101c600f241c907071144090400001080304000b1070100c8921b00d100009800f818081001300c9400003804090240100344240c950898211585181c0c84840030040d40d299408200c5160178010103400090150348080180402c050300b002620410f40c0039504c801c14a07603104004541121000d118402c00d10007080000c101e203c030040944100d0b10380701200140105c50f0b82c00c0c9101650740a4650400182d1300140800c00b00340d20540004610a492407490002c1c00c101c0b04c01000790040c000302034855100000482d83e005181e00407540c1501c1d4441d002e5240d244d03240140d998142d0708551850160282d012101d440d001e00c2c0c801c1034180e40c2241a842c1c00c2d0313141d510600152070f0000f403270f00b481842440c00c0400c1c0000d640d00135502c82d52150025035240401848c101c2001000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 423778507 1250 423777257 423777259
    0x1801110705031b0a060609091a100302090a0e0303010f03110306010e0106080a0b0306040b1f0b0403080313170c010606030606020307060c023f0703020a06020c07170a030e 75
    0x4203000d59000558003004440c0004140c00111031070100e030004050411010800c000c3c0500c0c036000340012442c079240c00c43c0c501240120055041540680043c5617095802c903100d1281034402c090a0005203040d0540b00c3c0c002c04a1703500040d20f040d6442d2614590703030003030300f0481c03000d0f0b083c100420030000c50f0354803103644043c103034060700c410352510b900205400018080c5205004081c4005448910355074845458920020101e030301074140340c10810b25119041e00c4d010200707601d1568400180440316110f5048498004010b80381c145551a6856250405850781d45c00d901504039035404078400c8104100051401e0704240d80e07034007100f04540d00b12661039010b003042c1810301c641007007456004800d40d120716420800118521492450490411303411564102214241c0ca10004911407504808002d9071100000b00143c0700c60009000700038010108020300603440300b0403500014000750040d158030720215040710250b070380b07900359011640364800e1440e0b0641d0000d81c0c41418581e110008010341c0350 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 423779757 1250 423778507 423778541
    0x40521070b0f0415140712110106050d030c020a05190e07020601060801060c17040801021c020322060608060c0a0e090402030c010c0318090b030d03060e24091801 71
    0x100c0342880040b600840c810341214141c14070804950074002c0d554245041103003260140c5d00d1100789840e2150a2a1300781c2140050b80240500038844814803428050301c03401801504040003540d8111180310b602e00c002c1740c020401001c002610745880c441202502031040c0441031b1241004041d0020f000300801040444d03220724010024140c04c031915a064441614041c1e180c0388041c10115500c0001d1a40c44d40c4500c2c0c00580013a0700a010350282c0215501025045000d910180310740d0300303038042900c440704c481007402c04818400c545c000c1c02e084a40c2c401c800200b07107143c1d650146400c00b442200c40c3c1005500009410120b41d510030802c54807840122102c00303041c203246c0c022a50f200710320703040d5038140507141d080542410b0041c08821a01241041c072401d041c0d41b0b90300180c000e40740691289010348030b440100e400e00c2d8001e0140c2000c0d01d0520f44230510070741d9a080c0103145c3d11001180c1e005035000d051156582601e4402ca001d22a9960a42d05180c8001d20400c003421122040392180c90741c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 423781007 1250 423779757 423779767
    0x60a0f140111073f0201050d0209090f06030d050705031b0a0c08060f0f1612020c01060f050414251106040c15021b06031503060f0a051006051e040521070b 68
    0x284d03450040001c00d0b0302840e119854a07501e1180100900c00d212210358009050800c100b070b201691a81580715003000e5064680e0000e403108241c1d124020b00400429540003489a00400803245011360114000b6100700d620030081a05c80c0030070382d09280c106900d25048041001100b02000c0c0c071181c0c1003e089010819035140803a511002ca98802c29148104659420090785074201a0159000c0d8a03441d8000c0000a64540341520006803611489009906008207255002100c10b0410b1140c00c20034a00d510a010654107a90101c0d5104400302c240040510007908229013080b03071511440c8030b80901e1500da42444405000d2200080c400e40842d40600d08500481020850702340f07158030284e403950780300d440d00310313180c24000e40c5c0100e055050301c181010000200700400c1c1d040c1c0a2250600100311a031242221800d020030180075070f0012031010018901d61090810301040c1c1c0c0320713985031002d080580701c0340014070486c41849490074080801c1d920800003c41880080001c105440f0124580 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 423782257 1250 423781007 423781109
    0xa06080d140d0b0f0a08010902040506030a231c03021e04060e06030618040b040311150106050304050c0301020309031c02130e090307050d080f060a0f14011107 70
    0x80c412010940102c1ea01c82070036550079252040340004a10700245514a0103850302030982c002c20a010003a44298181008950315090204218408903007195292099000c3e03090090f40b5075180307101901091090992003460a00c0c9100c6070144a4030542e00540c6d602c01c8400902001034030340040c404c4280d801c00c410800103030060a58881c5076001c1d103806443c2c0d664040000c0c00c40000b504200d60340150707107040000300a41a00301798440c9100c1d840e0040095a02810a80d580c00381c1038000a0b030030758850044c4040d43c0164091544548500110b0304d400082001003426038000395552840ca50001c0341202032071000004171600107403018070840c10217240060f0901c07111481d100d1005036a10a07404940b004d40c081c000c4078202c6400c001103c03605c44030444002c007409000c0741e403490484440c030007103100b07413030904980000c55810025049a039418690210407805000d4202410b00032148800c0e1702c0d00d04280728601c01044002c0520010400c001c0280c25420008814003000c0d04c0c1401c400801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 423783507 1250 423782257 423782297
    0x1305010605090d060204050a09090309080303010b0d090609060e06100803031519080a150e0303040b041415010e070206070804031b020a030f060c030c140301030210020a0b0a06080d 79
    0x540c5604480f00800c5019500f41007000f84107581100d6005a4952004540354440d600800e030105d209a41c2c00c0480c0b699403070304584070301007070141141d0004c00b000180c01c0801260030240217140205c200150f07031089555401d00b2202d441c514070819030020350402404e04010500382e07000704a40405549185000b04552412680c0950180c0c0720b08186101c000c0c0c4807690140042c0078050405c00c0b606001c5860910a03402c42c2d0000302503401c07a0402c220781d049040044162030280d641b00000400546031aa214a44110414140542807155108090002c404c0403426402011084a140e01074207080d0002401e10100a00c05c0342401421000d00c00000e900103440c4d07180401d84034400400303038514400959650300d035a001401d034a0554030140d090250941c40b11050703141c2d0303450400a9042c41802030790700e106541386075001000d05000400c050300700907001b40c0e04140c181c816a04185443d44ea041030262042c1c2d4101c03015039483d8414002d4000422034411010400d0520808a503101c51002e15 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 423784757 1250 423783507 423783517
    0x8060303041d180d27080309041a0d03081006030908030109050a020d06080c01080f070e0f150f0309011a061b100c050c060f040c03080a020c060403060b1305010605 72
    0xb018034010400a80b0003010585482a044003c9055403580740c0038030801880d0300c0100c94840031031029509070400159022400408442e580005982010a01c0b8100002030100c44e10206401e07001d48070142907641d84507800782219101c0c3d225200703141001180d8040c00381e0a45c0100c010706280010480200b62f012080d24111912480d0110340c41c1d881703106a00c06801001004190305003844c001185010022401241c2c48200381d9450b607403542c130000036031203001d0190341003400301d111540c0451817414410212102650044c1c00d0048500400c2c4500d141a441401e280031250408000d015a07000280141e42202602c9030340071440241035030004010348520104010043c0c801e540030102070409200e64070a102910038200300030300d5280c602810701d070f12550010790140108000506040182c0c00c0b620300070b0b07400400043c1c036a400c2d40e8625445038040074280c1c4c03e6100b00250540c03aa0381e0790000b01301071403007190042440e100072424424a400881040298179007002e0060210651080a9503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 423786007 1250 423784757 423784799
    0x20c10050c0c1e030405030d120e0d0f030c1115061f020c060703031e06060207090203370504110a0b0c0a061d070312140a0f0c1e030f0806030304 64
    0x180b2039400b9101101c0c514070486d401103805001f04000100e600c1d0f0443d841e0210307040d00400500c01c000c1151051030f100c0011046801c040707030f44410000d60461090740401d40c44020341c18860182c1074106a940d143c00302201c2e4083e1010070030002c2040b24107004051000b0301703185081c9081a2506910042d44500e000301c03c6501500c00401d951040c5803203a040215081012081003028907151a0a14044c00180c040c010151140310307000580344525208892040d0360000ca100080803100a00c24507001541c6100030003001c107500a2240114140301d010f00841c07103000726080708841c0b0300c10700580c1d1480c2d5000c070214200600c80d10009803000b041c01e404942c0e11100000f02d020484510340004140c41c2c00e03480840c4101a408010803002010115111045440d201210200d02c0500b4610384030300d41d01400013402c600e103000f800a0080c0b141543d05403040150f001702d2029400494694205014194002400b45505000060700104da06410060a901461a145c00c110184211910140d410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 423787257 1250 423786007 423786043
    0x406090e0f19090204020a0309061b09030609080f0a030e0c060301030b180102190203030f100302210a0f0f0611190c0203010b0a0e010f06180e0a0f020c10050c0c 71
    0x440104005078030121040344c1c010b2045440b1120a440103000b8030013a1405c80f0661b140a03608140f0100d5165480c4c0211076079501c1083d06425030740c2c1d0001800f03842c0310440784404188100c103841c3c1440c0b0003030a048883c640e00041c1640004691503d42000303440d000d80903070340400060000c02d81c0603000d41c0d40000d1194140301c041c07404003016030080c4522083d1503030451254100c205280d40c040021401200800000c09868403070081301d4400540a110003948142140e2802d038941500c0c00d100e01e100160602911404030607038455068800482d90b04907070f5481600d880104002c41c6202e4140b0801f41c81580509280c841d003c404004040c000000c402e00c011000c0403001c640d02500114401e480180c8041209a82d4840703408603520b0078010b0068062000d540860040c0c03084800d48103140148400c41642485d006490440000292160102c81d8480c7c0507400301100f5400100042c0000d000200300c5210081d20030740850300042d00d5012008800c1044583d0307100d0018000003580040905 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 423788507 1250 423787257 423787291
    0x71e050f10050c07140708010c17010504020c19030c0b0414060a0c0e0d05160308040501081b0d0506180408190903020a0b030601120c030204030b15030703080d0914030406090e0f 78
    0x3200e14001304c687c0855a5503090206403540d131384d03105013a604083c1ca51000a032869889408010507806120380c20340c010350100c610102151201c0d6041d0811600900f0070382c000701e0003500c4442e4500c10440e0140e607007441c00689c4c4810100104501070340034030410b004000425807504001c1c09080480e2805202c2c42c1044070110920105009140120812000c140916981e030325020402e500244a124042419140014030004003145001e18400382403180c5841c05600c0e581a40051601038580e130f40121411404400780031392025010701942c0120100340e00c03811103004d01d02411400794601e1040100d1010204010380b940704240341540c00803d401c6440340d40d1880102c4000205682c040811420044a80c00642e0542d00920540c1d001307140c5000982ea80514440242550403005505984400d10410203c0c40010140002110361075002c6901586c0b500d9100c0c80342250302c5040d400f904001030400606400110300c00080c1034800640e980c925101c0003105420b40010186000e42c180084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 423789757 1250 423788507 423788543
    0xf0c0201120f0209061c0b241e0313021504050303030a111303030c030801120203060402120f0d0e03070504060807120302010f020307120b24071e050f10050c07 70
    0x10740b2844113014042903201c01c4080e6200c0c3c0c00e0100045035100d01840d100050b6554205240100d542111020b80ba00030940d0001038a4885c0d070291a144185081044100041441d00c0d8015401070303500b4094404035500a00400c607800d03000b101c40c4140c0c940208000c04c0540c03800f10580fa030002280c0400500201c43e001c0010f100c1c85521446840d05440200100030160041d01d200c083d2402913580000303580e2105e14004072500c000501035459071011002400510701305581400da400f095055a584030010401d107454552203c10100104030540c0001600341010400d440061404907401d1040c1407410b01c8454643c407083c002c014644184502d070b082854000d4014400e0400c000d01c04540e03e00d06400010504800d800850205030306080c02d0329914500703074020700304001800c80110f030160115502281e4692190004407140088141000c80489000c0856100d446c020005811000b11506001c0c0c02c1c403000d20710181c0054940018030030078504504c1030710105030f444101d201901c20340d82 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 423791007 1250 423789757 423789761
    0x1030809040c1b1e0b010e1006020102040b1207020c0913060b04091109150a0e011e030b13030c08040f03120305070f0e12010608101808071b0b030708070f0c0201120f 73
    0x86005c0c5c600b031785050000454400351038842c1e10138403000391540000ca0712444c00320b00b07038801e030b00c10707100070441c280024040c0034407a407002c2da000025401140c070429580c40c04584040e108684e542002034040504000780308050103242a01d090403039040111106641c0e440081d4101c0729141750003034140d034002810101d8400c2210700241401840c81100d5a61840d24011481d002d00980c00145e1200d190310b81d0001c8102d00c0101501d5000ca40ca0141e0f949040b8480c0d4410900001034040082294041001c549590003c00203844400181034116096003040f44500b0410b21a0b03004161401003001041c40d40030b01d40000c6d0b0303407152401440c41e404000009a6040c407440020601d5440c0c01c07000204d01100041e21010000e88070000d1000030b2240f4507003030501014250141022108100c4100061000a0391403840460340e4007800300a03031502c001581c241c204454a00100e4101d8043c00020354000c0c5802c2404016807400000d42c1174540c4c0000c01c03000e0726541c203d1116448507000c4007150815 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 423792257 1250 423791007 423791063
    0x6020307110303150a1202090c0a0c08040e0105030c1e090c07120f020f01020406140906070f060504023c13090302150f013002060301030809040c1b 65
    0x20100b181e880342050b000c24951134941d10020761207404084000203201710040030013000650014421a504d50b100408212240e001581540c20007640215102c00035500c0e40c00b60014001ca2504a65070b581000c3c01d1615141c0c80d0b801d0680701d58440501401c1201c00d001272030100300c0d0140e0310b90040340c41d03e02c0c0805280c0110140108072403401003180c00301560040e0307140f400098a41c219000007a0441c9070074201d2050307018460000303450103414a001d42a1000801001c500504a07a1a00200f0b4480080031003400808540c00e0f62214144415480d180940741d440000601848050864100c00d000c04809420f42c003801400044141d0100d580d20b1016000081076060000d0000c4115840d0007526020b5282c800e9680405050101c2c030901d240300f1003181603802a1101c6014130840e2505828028000d1041201d007544541030000140c4485000c0c600a62260041d140c4480e00b02e401c01c4140c89201105804000c00c10154440d40001c10f10501d5a0070f81125400101c5000c001140c0242444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 423793507 1250 423792257 423792287
    0x60605030c221e020a030c031104030b090708030a110607020309062d0f120901020c061801060b1810020a03080a090f050706050703110105070c080a030b03060108010209030d0e09010306020307 84
    0xc048858030b50000d0b50340050906017003655003040040d1b03001d41c0540c1150f001e00f00030000b0503014001032002544918041d504128042c0864110325070315810076240d80e00411040d00090180e05511125080030840d86030807100c64009541070003c0400851424080c0d40005243c282100d0f8104002ca0040044c8000f0400d010414030360b03500d0300c2080140d0b40d0381300a401c090203407804000100c1902c0d041c401da99241415001500740c94607020303d8840d5441200001c1402035589040c00940a40c10740014550307c0c00000407481100a40001c004031103042c03504050940d00312240f4031000951001307281c0d50040208100107a1006a400c1184026001000050140c0b045500200d0080d40010141c0b080c0e600c40e41d5061000001400c49600340c3e142610004041548407a2010001d0280c030301804081100386000034044c1d0124001030300c4c100c400e078050201e1740d6001404a4060500380621400300b403042c1007100d02c05144d9404103d829005100240c0b285d64040040f86905120b0f00c0c410411040e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 423794757 1250 423793507 423793541
    0x31203070e0a0f14040b091506120403020c18160807030e060903030406060b180f0409050604030e100e0108310b0a05070804080306010f2109060605030c22 68
    0x3890f1114440349070b01a010384040102140100c00702490207004e9a051107030041c18001741d60b1205113100e41141500e40f80b05500841c01d00c2249201000004c019110300e019038001d001c03004001040c0b24007182044080c507090071303c0710200030152411850b0480c500c01145441c0c002560703800e604800403d1030003141e0030345010b804184403518a001002e14056400f841040051980d24214100144200d9011540e01100d424409500d032408545452a042d0060404100d02146a4940c0c0c24501c00300c03030072000f08010750419a003d041c24410900c044240303040c5122140c0030f45001800c54900108a07036441440d507028444061001c0500321101000016100640002407030060820b88040b10322410f5a4642000a00c4080c0310300c3d204c42c0a540c20611207850b5444100044581c0e020141c40c0d54240035038960142401c40d00080c03a5003044115200020303503400740d1700d440800d039455640024866130100c1c50311441079440c0140c8845003a05090310a46241a42000b00c0140c0414424400710791 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 423796007 1250 423794757 423794759
    0xa020d051002071b05030703021003020f13081b0f010912230a0515010609091503050d111e030301060c0510050c180103060e011701270507060e031203070e0a 69
    0x301c80300d0f10098100c130080c00f551143c151180285a80c0d0f280b00c3c400a5170200001c00d1a04105001c0e5004201c0000c003a2905031405000c01906500d28405078400c2400303510500141d0f0480e04081c1028860741e0085481c01c0c600448100002c02d049014014006000740c403807268010821b0202a00b03488141c841c0c00c9001462203001d046480300300c400c2068400707000700f100d41941e4000f0096407905a490350b44404039401c0c285100040284038a43c1d5680192078984008408a0410044a00d00f43c05a40c0c650368000160800c060a00d440b484103031154a08110040d00c8405010040c0c034191085d610701039040b5940350400c585041d1004903251845444c10060101886440c80100f400c05d00b01d942d41541d9110241c011001c8800d00d2044844207480301c0010301c02083e0021728040c044c02c80e0b070000725105140407800580b0021074820300200c01c0142c000401000014082c0d2802428a03061405000250102103a201c1c6590901e420310404000000349d030715400713690a44101d400181545c4046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 423797257 1250 423796007 423796013
    0xf0105060d1806051303080906190b06091305070912151107061406010324210605010b040905061c060b041413140118060c030902060f040312030e0a020d05100207 71
    0x10304400c0e0006c0c0e000610b032000180c808c0c000020581c0c099005c18114003e0700e090121041c009245040c00b09901c080304011400c007c0e0f6070110205964030b400300002903030f03080010f40a40486525440070340700c121700c60600008a034141c1610f11100780540d0011842500300070144c1c40700d12130b10341f004001c0c034500302d9540400355601e4400c0c0d1082c0700a03202000810403080f400080f540901c0d242400307080d80e2807070030300c81c454030206100c00c407008041c9070000001890b5103003015124241c2100140381c2001c60f00b00300758100c1d40500d41d00080140c4903504010103800304414041400c40313000d000780b0303141c010300d43d4945c59942c88182c005410107081801c6003800400c0d50f0700d414601c842130340c05040c080f03c131005000c0180706021480782d29200c120780c007103400e0380c45902401d6120400f00501d692442c1c0c0d03001507100d000c0241540b1600103002995942140361200c0040342581103981094900007100500c2c003000246201e5480d012104000a8081c0380f40403440c08075031f1b00f0b2454010f40003041038410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 423798507 1250 423797257 423797281
    0x90a1502011a010306080c0f04020f04090b03070b0a020a080f040302040e01140702011a12011d03130b04121b09150f15140c0a060903050307080f0105060d180605 71
    0x201030000b00d050400c901c07840c01142071390598020540c80f90010364409080345005c8441507080ca201400140c01d00f00780d1aa4071100707800a6000d41095038455000c44468a01031001300040d107001c8a4141c146514520000e682e4400e60700c0042001100190b07251364081e40400f0b0301c00841d4001c200740211005100707030502030014003c1c0d0a060b0161880440c85190045c0500c4000034080c444002001000c5c1003001000c280e180b440c0034003950396000c0000c081c0c5240f40e10a0620744400001d554500060b40000100c0030300390301c002210b00c000c1c0030902a1043ea0103850003d26045110010031014044400c0c4181080b40d110080207454180314144001110303101c00d0882c7d040e5112161856a50451940e07503401691040002030300d841c445e8445c02c966080504406190141164110b00450340e481044076600c04056001c00c0002c002c00c1842f6901400f102d078002c02d0100400301c00c2d403412002c204075004800c1c0110180b9151000050364105070300c020f290311a0814803d110f1405c0205030582d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 423799757 1250 423798507 423798521
    0xa020709092405070e0d0602090301090807230c010c02041b0905040b06120402042403030309060e0d0f0807020309090f0f0708090706031a04020c07090b1005070602090a150201 77
    0xc5001807405035030b490714000c0e21032203108001039140d070a00110386108020b243c180b6284102d42c507a07802e0089455940b0244501c240c620b00c151803d561b6480c0ca800d10200c020070304900804558200d01c844076805c03901291b8403449050038200404414828030026000d007038035000302640108254500f1007615400010300049810540d030030840c0d081c200c001e118a600c10107450000c000322840101e0014140f540c023030303462040340c040d0020712840c82e040100c0c401550303684141c001a8503902428140000d80c46000104400e0310010030700c003216020f018000c00802c10429040c0409040080e030842e0090040741c08503600148041c0481c43c18151290113250140d034040341010b40d003c005180d40d400340c00c503980a100000000c00c181850a0411000b4180c48060314100e480c8840c8946141c2c1c9503400034100070703024000a01405820310b10045c00300c86402815901c1160000b01d039500464100342200c00701d80d00708901607624291200171609090403036001c4041d100c110000d0030043c80e41940180 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 423801007 1250 423799757 423799793
    0xc07080c07060f0e0915032e05010509010e0a0c11070906080606030307020108190f020319050606030c040915050607050d2706050d24030c090903140a02070909 70
    0x41d0450290b10310444e260120321500316000680c010115441e040240c6071414041d10040840f00146004074155408c1e440c0e0800c00703680d01110b61610704e54407040d400f66602400e804c2d141160558540043c104541c1c130060100d4941d41c1d03850321002c20061240f26200d414410031307012581d640c0e59038400c0c0d000605692007002824090304021500728500401159940c0360160745000150b00e80c01200e0310345091814028243d203a41d56402c80f90342c0824009507105881c5a07102012540c5403d14880c10b80c0d4000384424800c42041040088001151013910140c170007000d000145824000d0300034400141c103070002c03944560f02040302c2c0200302000035001c20f9070920380c0d107101600b0040e0094401803200700c410305c00400d00c11001404010701c1800a031100680d41c01010800c282e0312010350000d0001d13019101021500316038180b0130301506c001c03000d000303022003a0300700000c001c20b490003003400000f0486485003500010301d802e0007610812801020b03101e01d000030003400a55191103444111102014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 423802257 1250 423801007 423801017
    0x150e0910050607080c0f0105042001090501020318010306080f01091704030201050a082e05030706081608060d050f030307090909030e100311070b060102120a090e0c07080c0706 77
    0xe02000480c40c052821100080d281c0381c2044403598500c122074114400c0f03041548510603024505241c01d008042c0500d009080d400031001c069407441a446441000361070610410a0017000541d070300004450b00e00040307140c200d003420890001280907020980c80b260081c03085030404c0d0360440b0103511003140c243c801c01e06e030560800780b002c0e0000725006610010380410380900110110a0003807103c070341c1c81041c02d403041000802c5044910100000c002a851517000104410310243c2020445080a8281c17030412100c2490040b4070103d0325485030303080b5003c0004000c040342803600e039010b6500c1d8945e03000c403d4420501c08070081c0b947e282c1084603030000048250b10700280c5643c092180500ea81e40503038565a6103034403401030001d842551414401015074a45080884200a201912615200c0c1464100504000000a1a121a030031420402603410814110781a4010404030110350407403401c581c507581e43c0820b600c490700030740f071024203c600002140c81c207510700415807109a51003a114 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 423803507 1250 423802257 423802261
    0x906100501021c120209030102070c03020a050a12021215250e090f1f08010213050609090a111309090317010810050606070c0e040b0c0a08071206150e09 67
    0x120f0303a8015a6880015100001e0068a00f0511424075486641c3d4070481c00340c0760030089030200e402c903801070500360344c80c4544110030700440ca0b059059071300070305044600c10384081c00e0800480480d0100c0344003d02c500d001041c1040310440a01240b2881c0300101284d00d8a890264410781801028140a0041540c44c80c1840c4a29009014550345954080c00f052055510b40700e18a9004901030b000240c00c2000f080000d80701c002601c0b07484054030701e03080003580340e0107468440b00c4020300d1a007009128031428801030049440c2c0d00490f40c0d011064150200360b48001e0306080f45a4812960b42200741c4c640348801045524058002642d030341d1081d514403044031803a12a4510002d000e0040c120140c21603e03503c00300337942a820240c0c224900801c0c0b1031500312280d4410380b007003000d41c1c08089040d01800400c428040080c45107540400e03840d025615048040702c00504c1c1708001003241003030100f02c401508c0c01c20b6079a40408042c0441b010520402c09032108050861085843c0d014458000c500c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 423804757 1250 423803507 423803509
    0x7120c02071d070e030609030c010501050307032609090130020303041208090306071e02070e070305070c050a0c05040b0105130506160b1f0803031e13020909061005 72
    0x191980444900040351101160400184400b4100250030601045103080d2040d200e03a8082c00094005c07003040006560f02e0302d0b050015825242d059000034402c2c0c203d40b90401c007003020305000b00c81016254240c4502001c200b01c594145000e040025500b0080e080c1c0049004e0088000715200c03c606903141d000903080c81031014003018003400c0000c1d0141c009020401c5600c0e5191003854030075128003441414600142c0100c0d00e0a8011550000002e114404030190304c03066544000b0360401510103410301d2800c0100e404464900038101c00e007015507900002e6a014811324190185643c083c064a4a0719401d0034034902c608054020103104d00d14000c0d102c449980070701c00f182c10300580c500300d8800081c80c0c0020442107800c1403813180c803c0c1c01c0a40d42c41000845040c0524403c102c0d400510410082c04042800c040000d600001d80940c41001800141c1c01c054030031171801541c0c401c5c901c140756107101c0189051104000000d402c050414184002c00ea004600188030320018481c10310900c0d0345038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 423806007 1250 423804757 423804763
    0xf03110303070c0b0c1204060903080601020a030203070803060607080a0206060102160f0902070320151b09090403050f040b0417010501030f0803040f0c0620060108070918050607120c02 81
    0x15075800003042051a06400213140d550304a90302010a05c0b006081c0402d0700021000750008540480781107a441002404050700001220341002d401e2000302801851581c004c0d51780d00c40c451010b808130101000003040b03071359144200c645296109982c40d03241c00c40e222010703645140580b50203001d4003644007014006081004500200c540d00012103c00610744884103000303500440782507081107a00c505054403180148045041034100100400c0340800c18011014000b1000e0200010314100300ea02141008104050f03030038081003251200440d454902d8140e500e4466100c802c0903e003c04607000540454820143c400c80e422440d0081800c80501f101030b00701d50302400b008010700e60411818000c51650406194058400c0f501d0748810742d0141c64a510828880c0e20140000d54602004407040c010000c2207210060180010001035061810701c507101c0720715000b040d90703e550f1860743c0c8030402600c0500d04000354200055420500b040080142030b9a1503e880a07a144d040c002e8545601b8800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 423807257 1250 423806007 423806011
    0x11010b060c0a14010908210a02120726012304021615020405030102120103030e011d24030709051f0e150702120c190b071403160f03110303 61
    0x850103466103a00d43e07a00c2168142420141a02d259a500124000640424014026001d800302c50b2241c0c0300280050800c0e100008040f0080e00c4d00601000001214900b400d0b030f0024a01e041c01c250b21000ca40e6280c001d0082da844160281e044180002165440a40078211004809040301181c10400003400241d206250b1040881044902c410b404a07240b1a81301c580c00240d4078000d45403d40e25000030f401da800100c0c40c0700c1c1200f525001001019000302d201e015030b60b130038200411285041503080041410100342c050154102140303002241d00883d4002032659030001b506510390819250050401907d405618058030035541c0d60310f00c2400c4083d8080c000307849aa0b0340c0320400441801c0c0003004010f01409060b5081c14000c48005940340d40c01e586403c000e4400621002c101c1340100a00c8280d12050082101d50407101031103007100c070204a424030790f00b2000d03010451204c402810f02e18840c5800e4628140c072074000340c00070480811035502409000341e403102c0d502d04441e00c03038a80300d01c41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 423808507 1250 423807257 423807277
    0x3030306090426190314090d0807050c01061d420d05100612030e0d021207060f0f050301360f09050607030203040203030d02160c0611010b06 62
    0x1d000940050984400801403a40c40c401900d84480d0641c2002216000b18221406001d0010358003000c0a516104044070b0425408200201d400d180c0c440c01e03180e00700001c101013040300080010780c1840c05041281c420210b000000c10009545042d034a500741403071288502042d1081001c586480c005000301c01c01000e02c1034017003480c0d13803000410000414108040c422001c900c0b01c603055055441c1107001e4103d60049001c0c01c06041c0c805800e034100c1c0c100780c011540d40d546c601c0c803450110364013000d0018050000c0d00c83c611080d080740001090f00280610904013442103682c0071602a80c080740503141d101c02509ca480202d0a66501520140070900511030350144422143c07449004240300201d030074230f11806c1807940300081d05841050b1080710321030750f41c019103c003558010480c041140b1540408185021070860606500003500c1c1c0c1310380c100307072110990041031401d0745a814046101c0c86950218002500607070f90580070700388400c010030403060340d46407030601e10090600e40e00310b0b122100703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 423809757 1250 423808507 423808519
    0x50412061406060324010c0212010209040b01020f0a08030406060b070f150c36170f0c03070302060309030426060a0603030806060a051e041505041d060d0506070806010e03030306 78
    0x61960401c100070495080003410001001e4086000da02c8270311180301407040440000da607641d00c4d20140320a680580030054115889580d002842172400300b04850980d0b0720007201030766902ea505020010b0989900503000301c0c1000108141003209031a160207000384515500000c962a801e481c0d4115801090700c2d0340031921500014903200000c000c1c84860400d900305035201d005a641049400c0c00043d00b0040d01005901020340704450b00b00701d240090f000560040050b0403c400200ea01c491203884001e0040750040f020500d181024001e0301c01030003541807242108030a0401800e805c1101584c0d580c0300d070080d1008582118035a020701c60943e07800d40c540380c281c0e44580d070500c22154407004004081001c2406a08905041203910050f80d0843e0301440b03490300d04050701e83c900389200c60540b5050207010442085004001d001c01d80300350464020f110142d03034034040884c0840300100001002402124200028150090300c2c6d04c1c000d260a0b40c8489596540609041e6a44401c2e141e441e4400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 423811007 1250 423809757 423809791
    0x90708090304050405131b06020708120f0307170709090b0f10140d0615030615231204030809010c0e210c03031207021002031e0402010504120614060603 67
    0x10134190042900a00c3e07000038000140c3c055140c0303191050843c03c2824020240c14801c109544e81006058090f0600034042c14650404110354a501d00c21541c1302e0100c60310200004817a140078111030305600e0b081078850340e007034a0001c40007000c00000b40540c9103d14500900b010083c1800c60740c0c41000507000d40a0443c10701186001da50f04140e081c005100b5003001c200040030b209060041c2d0005120041c28400c00c0b000405018040d03690036000742c101c0103e940e54105400b60700840151141c501910910a0200210400e007000e1240d41c2d510865800e1107010b22003013587c017410f07240c42a03080300001c01800881d41012240e1864030801c0f240c1c030446100b0108543c5010040010701c02480504581d03c00030b40707034003280c255000540720210b82d80340503040168803601171002007040e04050100f1899448d10204440c00c441400c00d0141c0c4134001000003c0859004808443c0540701002808106211526004024054040c0c1000c000c42c0c1074408180b1504080302600d00130380c60003c140c1020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 423812257 1250 423811007 423811009
    0x702120a1b0c1a0904050f040302150613020c0f010c050405010522051c121403070302130f080109020a0b090906120c1c0516030c15050702030f01050609070809030405 73
    0x2081d00c09406442d80c07941e50000140820404034201c640b102c0d661421600c800c0d05800700011110000c001090815105007084000383e40820064003d84a18404904546941003c111f0040740c10380c1010f1118800102d4207520b000001d2546407105504c002401611020300003203c5038051881001d02041d0180410030006420303a0700d0010071601404113510300f9a403500010141c64040e919503c50341e2442040c18103012001561019180c018103000c15031000440001d112407000400c41e0007095800301c1c0709088014500042c0c0018803855016418407612a03085c58000d01c44104224466000b2010000c0d44284600c00e851024000030120116aa0754006009038500458454003107405400158007481d42c400c01c450700c80049081074021000103529011340b5106040074414641d909101c400c1000440c40300059086d40c140d41c04001034030341d0401c010f030360034004c031400203516015404000801e0703001580b0091092000701c0345c1201c0da80307541c0c0042d58020b006480b01d21041c0c000300300070b01035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 423813507 1250 423812257 423812297
    0xc100801060e0f030d0e011404060e010305041b03081c060b04030f150c0302040e090c030c040b04061a032703070f020109050405040f021f0818030c030d050702120a 72
    0x40b0090301c5012080d80580000741480a00340451001c00c883c9180094a564030038560520400608510303071806043c01d10141046c841d074111181055103130b00c0058200048421059841805100030103480c035140d28082401d5000940982c0800c03d0709004010302e88000d0184004540000c03200070700d03160460b22217000e040344080302501e050321000102c2030107050314860f0a03500e01c42c6580050702ca905045201060b144040c282440070307400065000c40d079076004200341c00100300803140001c030b144000020501504090740508000e4100100c0301d0003070302d0705a005511460281402000e5100355000231003004404071581000f0707a00a0014030001070280c803032050740e2801410714030380c241e941e0030029064038021076040b0343e0040d50b000f0200071410800054440600044008406010310302c00007003214000070000311010343d250b2501ca041140510840d1708000040c5c09480d03030740360720b040c299024007400d80348a80181710b8001c120032202c12207c261583c4505540d50300e01103844a0b07440c454 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 423814757 1250 423813507 423813527
    0x81204050607090302091609080f070501030b121509101e0b090c16030504051216060f14030c0405101d0927101d010612050c01050304030210020a0804050c10080106 72
    0x20920032100300104503000c040110a810180f190028454a3300b450001800c0e95030b505a4540645c118491032450b810010a11005030100e440403c076030340d80c40f100d0052800c403110304600d240503e1720752210b29079209400c07101184085080b09010400c0c0350f00600020190440344011a0030b4140030004034040d1400407881014040d1414506060b12000000c00c80021040746003078983c030031640200c8010030502400010541170a1090f002c1c4210b01014000464140c5640591b400000010f01414180020f0740c0c05080003500e0704043c00411070020b800b810040119000440340200c3c5609589000c10000d4800c40d00b103a5200c0781007410001c0790b50411481e0414800324084c80b00014250301d280d100d050301c82047c00103000d89410364032100c2d42c00c4803d030341c222405684110f0340140200d10000b83c2904051400c0c42c00343d0b626561360500300d0400707030400007130b0113428000504115403d42c800e400794081c038020416251160140700030044140600351490011420721401002145d018490b601303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 423816007 1250 423814757 423814801
    0x3070b04030c06050f0603012a0e040615030e060c03060d062a02070f0905042d0b01030825020f0f0111031c0b0d0503030c0703090308120405060709030209 68
    0x40c41d01d50030f940c840003910002c441c031000b6480c038801007080c10314003400f6094000c5035140c109a030401c2605001030b12403140c0004602840800c401c1c03240c4649032a40840024000f01103035807889402c40e40700070060b1445c0e0242c95540c0c401c0002244982010740116409040e0042050342603a45542d2800050050049010402c810540e00a01d8200c600200c0c9905240700f5405441c0701070030152640382901542d000a195186030104100000d800052001803c0d500e0b803c0c650b44980348542003207051260068000c0840d1500300c00001001201c80180141030b00c00c0400b001840301500001d544402d04c440041d51204141c0300900d640d0800b0441c0d0001d0407410301d000001c4e80030b905403051440d401a0002c01c803400300c4800008200c1c405201d11410f008040350b0388081200c05403078003a50f0780400f82600c1e0a240c00081c14504250017000071000031030b8080c00d016142d0b0002003111b12044e0045505035158015000044c00b00d0b44140c10040c00da0758000c1c440d60154071943c0e40b121824290aa540b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 423817257 1250 423816007 423816017
    0xa050127030e062104030201060f030305070212011805030405030c09040f0b0709080d08061005090603070305060d15020d0609151a21160201140105010e0a09050903250503070b0403 79
    0x50504005441c0558102c1d221358011050034101880c0007821103a840e40071030040b80d098582070001030341c80421030301c0b100c0e011108075030002003194505005203200c003540581d006030b1040c16810840044043c0040303c50460075544c0100700c08040c0300150b102100e005040401c500008400100c184000907040300c003900d01800045c2c1c581e0150782c64660003506c0030001c1a04c140401c502c515144600e030f002d0580724038050742410f1701100890094080a4a040140758903880041c00c903448217083c0c030180b01d8015240801d907a183c2ca27801c000952001e82c03001e0300e4605060000c910102c207030040000d00e07419100e41c00c4e042c500d045400c903000804110109403000040200041140300c0091520b100002c2044107007440c14441ca9110380d13221010111019a410031000c0e01841408001b042c3c11510282400b900b541000c10024a0f179925a0b0004442d183c40c1005020740c414001001d0081b50b50103148031182c0408950800858004c0120300400662040241c00c000407128600b260f089840380c102 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 423818507 1250 423817257 423817267
    0x305071d190b0f1e042411030706050109180c05042004080f060901050f010608060105090a0e070905012a1a0a0504020f06090102070506090a080f0a050127030e06 71
    0x140042551180504050341800425251a403200e01c1c80c1c113601c00d4a030030740002c0c5040d2074050b40f1080c8070f000d4031041d81000d1024404918650103620039008400c1c14805403580c42c4040e223081c40081c4802c0c0030701c0d8821403030b00e002c1c804282c0651002046131600119080421483c0200b04406003168044070358048141d804200c0d05460135802410151020030041c01d800c401601441d49001d40040200701c20f44e04040603c00348180f500306441c1520514175101c4440e5854000507034451142c1c084140c0c0005998000080c03c1c841040c001340281c045545003000540d0320001164204001d440010700c1c1c0508443c031491440c3c800c80e5070a40da03885903c0d5501038102c07824840e603281c2f504032a03403000b19490340204404c500e8100b121808843c0d0854140c1d04000e28180002c2d95000c140c040e460042c440041c1c01c1c2c0c0d0655400500c40000c001d210111150b9050540c1520348600c1d0200f8219a03070740c2410032000e03c41402c00d1144082041103041c080001c4100e840c2160070003400401190410b40c01c00c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 423819757 1250 423818507 423818519
    0x221a0c0c0a050a21050f0706090803070206010512030403021809010e070602150c1204020906040e010608070f090603120305250c020109050936010612030305071d19 72
    0x8803a440da00d001d000604400001c90411426200013820792810841840d00150600754105041d03c9800d550f428001703807607900d1807426100800150a020b00070840c0402000845907000581d2410f0b140700b0380c2ca1011a5820880166490189001c0254410200040d80014074913010116070f00c404220000704410840c11560741c2051666080240140c110780045030a4000580340d1070381050b980b018007442c210806140c1c0c4640c60b0080d000a210f00b08140116855554540105275000f42c7c000082103050b50b5038503819529001c512464001002841000510700c403a4855034088a070021000c0c500003020103001c4000b400010480c40c0104919885040e02c480c0300e030302484030030120f0f49400044201c18000940740700116070000d03128079904020441e040d00068109104210314100440703008100030001100e0360f813a03803481040c0758a08100000c3c0101c02c0301800414a01a480070060360301e135000c0440e50049a541c01d00641d28100440d4092800c000d20444024606034003a0b48206440305 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 423821007 1250 423819757 423819763
    0x70f0608010602011103071709150109060603060503061003140f01090606050f100219150c02010203180109122f01050a0e0a0f0204051008060906221a0c0c 68
    0x1400500024003120014848640c091045960340e03040c0104490952400990080c0f2003123602d40c03000c00420b158000300b401000204155080840042104013007507031503270080e1008207403601c00c281c0001c2c103206000481c1d0501052580c040c0c22050a220069811616590080031100e01c14603158425880d82c02c11041080c4200b5404070711400f00807942524040c2000442c03032070540d12501c158010b1440c040d40d81d4002030070718072050f0090406c0d103107104581403821031840500c8201c05d0850500411000c407550640c0254402e40c6401d014007000401d9105031400c031200203900901081c00c0001405d1741901030b12003030020311028106c10100f81b2b03e03502d12160b41c0011254049a07a074658092103400c2c441c900804d0828600d5100900326584c0d19200c0c0c1c500e02c81c0340e21010740525610b9002c14110f0180352387c00005416050304460050520307074000c03980d82000721410001594046500c02c0e120009100c2d90380310a401c0b800420a589031081c00c030411300d001900c2d2000c400740c00c00000e800c011040c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 423822257 1250 423821007 423821009
    0x1504030503180a050603061e1302160b100b180409020d0c1401020a050303160306050a060918020a02101a0d0b04062d0e0312010b030603010e2409070f 66
    0x1c508544205100b4401d1107a1900260000e9103d94000d204102040c4c482c65510380d41d110804048203007110842c030104041c090f451b00038140b0640001001d04450100d041905a60340c880c0c3c800303001d541e90314900f0f4591901240195180d503803040000c103206800e06000b03a28a800001d00c0000c0d2240590300060400d021000126944880003204200f154440051402180001c1c009400103403159510980ca0f444020710000140034620441c02d0001c4c0300e9402800684005846095056214107024280032500c0c031078664603001014030880c0d140410700950708070038401e400809102c40d0001c818400b0740040003800d40030301d02c000c09032852aa41e82c40c03000c14040c01040803129070300f000e081040a51300a007501c221254260211048540e0008070048822105410001071034450030416a095105405010b4080f880c5007002150035600c850056000e104201d0080103611641000d0341d45400f0508011107040c8235031001803421100303800c0040d600001d00c1041d01e0240383c0701c0130f4112a411036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 423823507 1250 423822257 423822277
    0x70f0b06041d0c03060612030409110405151206100503060f0f13020a12050402090f0403020115060302030a14150402090a030204050109091505040213090503090a0810291504030503 79
    0x101e81070410081c1414810190000010f890980f0714001f400400e40d44ea100d64400c281082d60f98a0203039034801902002da07005050001d0125074801900000e45c40c940d0840100c0540110001001c80d140d49004e02c000c064036100ca0312220301f50354450080000d18060302c0251900900c6100004a10b60340380305800701c00c1c1c80c11810040c1c440ca0b1200008100d45001000070030101d20389400e00c00560b80341700074680d20150582a56070296120b2034104c0c090b0003803840f074181441004601142071505600510710032030200ea03080201c044400700c007445000c815901c65100d081141440381007801e10780c0041162100281090060554a03408581155426408140c845035910405802c12450b2501072143c20101034092001d402c00e6000650030304c41e030860241d2001c3e5586140000c0000910a48120701720007044034041030360301ca11060b181c500c049641e01e042841e200200202058400540000704052600b46941c42141c3c0b0500c0080c240401d04c2c403203050403d00c80040003500403c000e0480ca40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 423824757 1250 423823507 423823513
    0x6091203130b191b0f08010f1203050c0703030c032717120301031101030615080a0f06080d11060c040b090409030c0219080c18060d110a03210203070f0b06041d 70
    0x40c0104e0010150421100500c00304072060b8010007210502040070300948801c0620f88103125458031707041c4c505105122600d005801881000070605402440ca4091280aa110004000c0d420310402c0201c1c40c10350359440c013008055009020030000049903052031654039003103442ca1007404005503d140c0090780b00700c80104414105402c90f5070f040c001d00d03000348030000011040e10340141020b0300e03410004250007001c564a0411000c421030540111004090040035660780418a44000f4090303840c20442e40407030b100350303000b0406c0c1c1d2400c00121004c4460f401e0020b8140b0003100708000180c0503a49007602005819008140981d0b98800078054942c40c20079442d2147d0b290064050a112558000e10f02c500c940c001c4403c040c07003070711082a601810490711a000c051030f5141c40b425451200e040d160300504000004010091030501015010600303103000d0340000702c095400c03a9248500d05000385070300030450ae9440020309680c0e042e034004074020000314100607101c03094002094100c1c05d03489268 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 423826007 1250 423824757 423824801
    0x3061404230c030a2102030a021203060109050607060221070e150706021c0e0102040e01031b08010c022a15030c04080a03050d0c030b060f0c010e0f06091203130b19 72
    0x5c882401d1081400105d80003540c04c101e0b0412001e51103040b5006541d103a1100000003078000c0e0b00c21402e142c05080000d0015403a4010f60400b14029005810320102d0340440148100c851801030070058070032401ca9944540e000c03903000a10800500074070405d10900010300c202c400146203400034014440000802040221602d190001a1810288202003503481000148140c0c80c40144481c107581d00700600d041946510f191803a80190780f5400702040d546008003013034a041d404212605c1074425011040c00b11b511030415070b14403c0c04d90549940c801c1c820008280e03001d12a8010b503610041908440c0d0070b040e903031380a5504107159030702c086000030305c00200c611044000380304203106119a843c04000c00010000416050310407901c3e18258800c0c045900040000d00350000340e041c1480c01d0a441d03040324010801d640d50441590820030324051070709908018030782e0034140d074030800340d8004444940c0100d445200d640100130303101c04a522000c1c0d00c002e584c64464080c8054680b80318864103444 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 423827257 1250 423826007 423826043
    0x904112206090305070e19060b0a0e0906030a1217040c0f170c0613081f1404081c06051f08010611070e0c070b010306020403061404230c030a 62
    0xd6161900a8020700940000038400f1400004010301031781e84017010030f800c0340c441c85ca040d62050f003100424005c00d81019030205154155001500d2500d0094a800c0a542d1000c0100310743c1d40b20450b445a010fa224801840100303e612200703411040340ca052140090000200400e42054101c80030b403043c0850120810080708500c0d00c4500500309500000c40410351051803035156459510031034892200030032442c0c1c1c1d11b4180c0c946000108101c40031a808040440800e072800c0c0101402c031b42d4214500025651003503200c10801c0d210f158413a0307240e440c0805c2c041052120340c861a0480c6c403a2603403442c000c03981b5241c00c828002c0200c8000d00c94107640150080050002005070080c400b0011442218100c01d480007600b02d0541e2418002d450f020380e1107018201850080503000340610401100000c00c0c406207500030016640560b4041c401c41d50440e084c0d60054806450041041d0703510f4001c68002c984612100f420740100741b064400b8000401d0000c3c1c41d0001682c41650f014500384820080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 423828507 1250 423827257 423827317
    0xc060f02100504033c030e0d0e01050403060f060504020414040c020d0e221107060b1e090a41040305030423010903050c0c0f030303010b090411 63
    0x26105107590300780042d180c00c0d6401454a022400d00d114079020120303042821151034403458070103101443c4020302c000c2c081c0f44010054455448840003030302071000c0d0141c2c914030641c01c1c1c6c100c1c16010303140d5500c0d052466507180000c0c04900442850a0307944c0c071011465549600051000b0802821041c11034641c17001040210342d4000703a01e100355030082c80081d140c140c110805080c1c0030000c9074a07a07402000071079400c442c00c8020308054402c5252a0b000c046000d5000d01030304036076002d203400308100c044000520640d07011040009003a080c3c0c00c64640042e15000a850380c1c03000701e00e00b000c244c502d0101104200d055030361055000f0280801e049001b1001d0300f5500c2c80201c140b40010700000e05158602615a01c0003034000b500c4c10300e8601000f80301441503503100d03051341c40b071800800841415040040c199000400405114001c44c900ca24003454105140f003880c1d98000c0145141d41d1a0082c00b140581c002c42009130043d80b1210403034031218980740031782000d0110118080404c41660f4003201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 423829757 1250 423828507 423828523
    0xd060e120a1b021c0501141f0e0106021f09020414010911030118021e0a0c1103161806120506100e040b060108040314071113020406140a0c0c060f02 65
    0xc1ca00c0c2c0c0411030402582e6110509800031011007820108a4402e00b001c0740940307030410a040b40b44c5c1800c0c041c0400e03d80d000c444111400021600c948200d03803a402144040c6030203209500059000361541c0c0d2000016074072143c018007800c4030000380e08006a000c60160b440405508460641801c0100710821301c4d401854220b4a4a040b814070755810881d10b20352941d100c6190880142e40030441c015186030f21036120070901c9038001e6440c0c9851410400a1010360200d07000c4a0800c031280000700942000110f015030b0115020622041c42d0400410000034650b4070801780004c0d440c0c000001d02521a111080346c01801000680301d5860310100580d07140c041640948404035010080002203059060b0041d0400e5007460120350300e85031400c0032103540129085ea00002c042c005401000c0003042c001043c1d01d00000d03915405038010b40860304040380203a00c10030001c07031040b009610314040130000510b0700c0740260404800c00741080c1c48a2607005070540205001c0b840d04040c00c4802501040710760 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 423831007 1250 423829757 423829787
    0x5040210022805010908030405030702040b04061d0705130605091c03140703020c1507050607050c0d0e0a090617120915090d060f0b1201060b03060d060e120a 69
    0x7000c414844100c49001c004038500e020003410a0910b00001c00030290001c007034203504242800d80301d007000c0c10321a4803580241c1c400c0f44542c1c41d00d800d000b010b003401e024001c00c841280e42e86000d4246030410880749402c00402801c20440208004429401313403d4942d03020300600d44c3c400b516406428248540da00d101c081c2c41003170803004120100080d07400314480113181c8802c0d414036101c803503914042e442e0006c2c2c0d03041d0a40c0805280c1e21a10001514000342c5821401142114400e07112000161500e106400321400700d504155510811103020b410700d405540006060084071a0742c42e503887c422180381d0781100e082100860340c4884060003c201c41008158030446151a1060400001e02401078007c42e48080782c0700410f20070005e40c2c03003d08100320b95030000c07400e1241903020300c4000d0090900725541032040d42040d40506010905100e840d090707991284100d0301e107444010401c40070a059440454000d0b81702c1f200103642e07810900003880c42e0310302c01c1c890b1622100341c26005020069071034056 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 423832257 1250 423831007 423831013
    0x70c0213050606160f0203061302090a0509060a09020f0306040b010612020f0d0902030c13020d0c0804120c2a051c0c05090a0b061b0f0d02062205100504021002 70
    0x11200d40d6a0b154100d90b001d454142000d04841c01c50716217801c4031025450084d516010310001c008219803840590721441d4401c4805d840350341d0b10141e094084500503240042c0c03550105000952102251313100c504080e00081c004080300c2c1c80280001d29008044404503000210100100a440d030424991950a81e02130400c5d410003542c41f000c050240130f100d80c91f00c803c0c0c0e20b440d624415502c00740310b20301890a01410322a20b10340704414520203540014000c1440300d2034090b44d4070320141316107403036400b403603002050140104070b0703103002c58490b95401029103101041c404512034038000c0e06586000360f050640d20300d4030310389024101318440128100004d2800c0508000c0400140c0b9180e408043d9602103078031171760646401c2c1a50303004101401080f50000b40c00102c074060714020082c8200007208410848106202c070002e032940315004440c4850142e840a004102c07031060341116500ea0b0900b1110100d409000c5032100c1e803908030190b2040c0e83e010390392030600095090001c540f0071048514002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 423833507 1250 423832257 423832261
    0x90203070821031504020a090816030206160302030f13050a05180a0f0e0a1a0106170420040c030509060906100603090809040203100f050913060c0e09070c021305 71
    0x2020061208400c0d80d00b1141800000668080002054000b1011001d0421501e070698614090820701c02800369000da403250881c280c400040c0030035154156640644600d003000808160840c1404202404030258001444160100048c1c1c0c8080c1144005a44042d0700c1c0344c0c6000148001c2e1582c9402c114082c1c070720035485102002d951281d017030f00205840c4000410f80c4a050300c0b84000c0c4003c4140c994203004140304801800400107444641c14480c00301001c0b2640d82d1039090781c480c40c083c070503071904920302000034011851104e985403191861050004081260200040403508070300c00b66404203907103100b48044180704024169002c2440c000828140c144005c0d6054540b805100d050101274503000707428104001c1909403091f404000d0019910317418032050102c003203220742c01b0b40581c42c03043c01c0d400903141c900064014003403203031900340200d140300da9103c082c007800e2102410003c3c8482c07090504015102c0c0c55080e84580041e40d183d009401c09441000151242200702215150402c42 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 423834757 1250 423833507 423833533
    0x5070c0801020412030f0e0907170a0b010c1b030b040609050f1204260102070b01080d1404030b060d0c0602012c0705190e070203032e360902030708 65
    0x40f01303080d41c0b50903043c80c45507208014021038641244400c00d0343c1142c0510180029250007200d41e07040c03505984815a150fa48600d101030807609543c003911b00240041908601280200028030380502e1503803015010302da00d90b00d0b91403200038181c4045480c03954400c209821300034240080301038202040c010b482c120903a0001c01d80075000b03074050b4843d0100c8441d00701460b101c44d11080c0307410001a01c025501c465440c10000c24150742441111000c5c0682040ba5801900c00e40e41566082100d551a6080030301310b880365039140000400c048c0e00503a47e102c001003c2008004003100400c595400421200c0c148a00760b00001903250b49500d052041c070491030312504000c21000141c91003541d00d846c070301e00117100c1101a6492948107904c80002101072003081640800190301c04c01c200c00000c88600c080b8030070003030401d12490400314904c406c07070401c1c003485103661100c2100010603502030a00b510074890803801d03a5000b111003035505940d1400d170340460500b4000c46000b488044040c181810a00d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 423836007 1250 423834757 423834779
    0x60503131104060503060c0c060c04061707111f0b012102030c0f0412030e09071704111003150807060f030b0d1e02040509060601091208040b0a05070c08010204 70
    0x5004115180300707809600c0544640d48103400908005003203030500d0510146011266005400c1c0355070300d00407000010020040d80040360300b107a041d035480c00b43c8510000307100503000501030400790030800030440180029500700011580300c0b644a100c0c1840e00c0007100c4a000b00c1d2003683c28981070000d28507e9103c80d0105d0000100746035a031810160741e980c0e4001c00746056101e400e560705154000070802040c080d00890355080058840e846042c0d00c540e10703800308a040c51040b11808009107404003010442596043e03540d8201e8402c45926881d0440c2c200061020746085007181c2c0007171703691151154515003041088006104510180025604041d0010a22441c5011200502d80c5071211509a519110203940c032464014007108012070f42c0344c040751080c0414a905030701c0384d414a00803424158000c0380c3c842c000c980584420402500d00201c07400300d0101d403141503400200502c80000c405511744004c2100744081c3c0d485d60b9031842d1502d0001101a0300d60000f4009a1042c0310901c407900c052 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 423837257 1250 423836007 423836041
    0x316091a0309010914030a120504021315090e1f060e0f07050c0a140c012a020310050a0606110607080a020c1e0313090902030a0303050c1e07020a060503 67
    0x3000641d2640c8591289000d400c0e50f40009103030854804810300c805034080701074204030400c0da071001a420a400c420500740c43e81900c010b94003c50080320445507003581d07070008461101070b041000821b5900c1402804071030541c0e41c50041c0350030082510400100401300c42c405602c0342c4004000c00c6040003140202e800c4004c01080c01c0d50100c0c0007080f17644e8010815921803c03c060101c45000c1174500d080400302980380f004810a126141140f200c540c00b41a41c1500d60a440b9080341c1e1511184a51000b03010b120042646c140c001d118441c031f044515400f0b030b240b142c1303c08440805d0040c40d0480041005810381e1501c05150442424005d410341d000e6885900000ccc1c005e030140e121035580313890605041803071001131001c117064041c000d0444e0707001c03003d41076500c080b00101e003a081d541c0ea00c031804d44081000095242d0003101c21500000d010b640320b41c1d04000520019810841e46c9440b940504841c1c81c00c40743c2001010031800700311301c0c00d103400d18080c0c00c991038403506505040846040c07041e02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 423838507 1250 423837257 423837299
    0x70e181303081b180f0904050604170919080606060a14090f04090506151008010b0c0106030f0f050706090501021e010b03250f120308090703080f031609 67
    0x100b5408614460b030b605001e100e02140050003a81c0d00c030041408103021070b80e9501e0030390050001156244152401102c224415500900604007540c1c4958401000507119982d8051580c014000d2078046e440310100142c620550040c554080c1e0700380001245071010003041d441c031455040100940d4154000d1031403c40c0303980321000315247c00d010130000303c100c03000305095500103281035042c3c1d00380080028140e006207180399408142190010034400a0f038081c0c6030040200e16a90010405098410000d066a0069000005007242c40740d981d800c0c48101204180c3d074002504500d00188181404080010300c05418003c081f82d1034180080c1d151500301c96040d2514030300ca200140310780800c1d0403013021074500400b56480a510803208032a020300402141c40201400c0f5004124101900e14000548410600c0503540542954040710011002411014a80030f00304000001503450741c00f8000c0880a0841642c0305d1510100d04a031901c0c200000c0d20030030103000e50411032884913102400b000c41c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 423839757 1250 423838507 423838517
    0x10207021c0503040e0c03240a0b0717040305070e0618042306180f0a0305040e090f010606030c0815012312090a030216051804030c0209070e181303 65
    0x8642d050150a50180d54800d5036560112020048900c4201c4001c500c20f941000f00f8103c3d951541c840810b00700c019007101030304500c0f8402d06024100c880c1d405004d05511605d40d03078011040304019030805400a42c0100ca00d0752000c138052000507078a100c1c41c1e0380640c2c255038a40d41555800b0302800d902c00d024101600c60041250350f1410250f446c0c442c000b0154038502154001c1c2000014545a03070040801b50100b40600300d100d505040c0081400c035155a00f40d0344445c1094201a1050064a8060811046442200c41c0004104020b004850041242c0e0b100090a088000000792100c079004045200444894101d0030460380c00100907030300e40d0070010b42c1c02d01c000180300d40c1c40e0713091003582449411641da8100b0007041000003e8031903141d5220746d0075070701e5032074070110756035404803242c014542c2c00807070946100000141070b09425070050091800340071420303041d0045a4000c42c20744001c8002466112040c2a900345100680340c9041d4401c21079440f1b10b0131507244da003801c08105000301002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 423841007 1250 423839757 423839809
    0x40302060706180507050109120c060513091a090603030a0c061104030f0b040c1a030115050409021206030606030f0a020f0a0b041503060b0702100c0c1e09060801020702 74
    0x101090f444800d80200312204140314100300d0500d02e03a14401441400d00169000b500403d00301c04449526207125408940c040e4401e0401d0b00646203504950402080b198442200180329020360080a11801400d1454032810208005000005c00300418043c025441001411038495020b41c1c01118543c00c2000000e0001c0c0d001c8001340340d44030307d92000c0c14805040e0146c90a114100c031a11780660301c12079088400380e64403e0011300d0841e455101c5002d508042c0010409030241501129400380c05180940c07501d40c0740c180d000d080340c011031302c080c1d00b950341c0d4002c101a40c00c04008540e00710b00118002d219000843c8401680c5041c110b0000b801071580c070b0400d41c1c503078680400000207071004501c050385a0380c56014400d0303800100e240140c0001d090680015800124100b15011140c02600ca081a100d89600c02d4414170315189080b66003a0071000b00040b00686400a0300c103101041001001c158681203092040d02c0d07064005034000c0c0d10400c14000145d88a0000c07442d560b1052810704022 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 423842257 1250 423841007 423841013
    0x61c0b040b040201050c030a0503090c0a230a03060609050702010b1203090f0303040905240a0b030708090705131d030909042d03050702010815030d0e13060e040506011a0403020607 79
    0x146c040c482d400c00c17061002003503403054607802201461107110044110760440001d02c003041043c4c02a0311850807a048140e500d20500d000441074208900406045940155629540d440072650701d584055000c6a80d40c00b4041019821300035407112007000c41c2c10034089090745000701d859106200256100f048241e51080c0140c0303090090741c1c014040c2580400c401e01e8144502c540c0550000103080c02402d84195020302890700b050581d0a03110300060103411903490300c1041d0364030704000d01a105548195500054144c0d1542c86141c050b02c40c841010648490a440b408500d00071907404006580062000140a4a50284150b407041e00300c0000021540003444030700c441d03a520b020890340301d2090b01c41502495080b800902030180700380d0303a1000da60759204400070011404031040e079054000701c0810240a1007603900c0581c0c12401407615403540d160038544001c556855100031840c1044a0400051002c01d02206006000f0201181c42c0c8509075050040c040c403503030000030310039407000c1920b8045c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 423843507 1250 423842257 423842267
    0x10815270106030207030801080303040b04030311070b040c0503070f05091605070f1a0601020102030f070305070207171b06070f0609030302040905100806090c0d0b070e1008061c0b040b040201 84
    0x50380200c040382105550711840002c010f98045841074000c6920000000b582c00000411203109603000301c0046030310780b21030354200c0c094202c500514200c207030103000c0c0002040142e01c3d030700d0103181703c1e0041c2074a40b45020181400c0105691050604500922080081e43c0341d2041c1d16034090500d9049103000181920140c50500030340401421400303650182004121910262210004e610f40703029440c2d548800049003030388400c980c008098120400490301980c041c3d00950b0700030180d401900c7d03101c0c0e21480c0c2440040c0f4117248020032075001540b80003200b04080d0b04e80b1258042642d09d146005d200740c031000c0301d8119000780204001d41e1030440006140c441e40c103540c05880010309c10702140c24820448040030701d4a01854110b402071002084c28104001040103052102a01044048034251a45140044001e042c2403e0182c000c03400d014595401c03001031120443d1780ca900c5060701b4000188a50303c500b0940f41408541e010800901041c20300185540c40303680041000e18654940c801210 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 423844757 1250 423843507 423843559
    0x70f0e04061e050613060b0a1103090607030806130608060c0c070905010801020712032906120903040611030a0909020a030f0e0706260f041b12020906010815 69
    0x30100400300d01c014802c149540005014000032036944a4211029810078104c6070541710b000310000c010001d030a0150b029140e94102d0b4100342041d80e00f0032180c4030100d001d0b5407291000303c0000303444d6810131a0341c0c500816801c1d8804c0317100d9001c001503418044981e03a21072010300b90548607c0003088400d1440c1e8100300f0803000e0b200070314050055594841c50319001c5d421031035044034917030201c1c0c52005d141e0f48203108100d191944805040c00c00c0c20a09035100b0740c40403c41107290068801c1045828403440c50803e64060501c0070000c540d5649081e000808001c00d0101108136131b00100954980180d1040e074000580303030681001aa2000f114100b0350007071007150000043e90341880c18480c02c1d0800450320742d08032003076922171190b010500386544000d0905903140d60500c41081010600c028855400c2c01e45c01403258040444100c401002e0032660451940300380170403e00303000b11104506040310003a40000081c284400c01d810000e60b00705051003402a86401029940e00c0313504080c2d401100301d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 423846007 1250 423844757 423844781
    0xf0f09040911040518060601030902010c0209040f0c080712230a200306010f060305190f0519020702010c060b06070f05030a0f050c060105060d020706020c0d020d02070f0e0406 77
    0x111201c050b24028107125a038480e07040c482d500d0100001c5400ca8850102d41a40035608094010359407550015401003040c00000c0c1d040141031940000180c840510150043e0300900f6000d9045416280c240c4030303942d854005114a8110700700402800040b40619000c140d44001618540481761140c50702c040040c08a2010034419444c41038188010891062405d24040c00701d20540b001c55000c3c90b0f0303505802c1c403e03c030081a4044003044002c0c0700380e0016070464041c121040315038401c0c000130400d9824110705450015951010b01080d0700f00e02c840000c0c0c50510303101c1541080d09640002e000b008828101810081e1603078046102035581d4030460b400d0381e03032201c0c503140c501700d250401c15a02d03000244400301203400c0e0030343c4a03011401b400c281e580240055008103002d07800d00d8180301e102c3c0c10154020a040b0b0b003d001c4e010004142d030024048103e065801004c0c13001150500074940305144081c101507402104060002c4240322001344141e805110202c607440c0c40758078100004201d003c00c0c007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 423847257 1250 423846007 423846011
    0x20703030516240f0b0102010e3301090c1d010c1b0b0c0106090b0a0f06050901020a02060a050702010e040e0d030203061c030f020d0201020f090d0611040b0418060b0f0f0904 76
    0x10f088200c10551060b220903001c41c1d01003102d04614001642201d2420300b1901c0300d035004840b4500c00700000020310307000c0300c0380c0040344024503007061400ca850a020381040c0d402c07036100c5040d692041c2d400020100b060031007100c030601316500302d00041e00c000d101c035801030300c2101821300b03204540024400800080603500c1c6401e40c3c90080f020220b00070406402041c03417007030803c49600081e250141b244001d840c1c0c2241d0400c1414179040702543e66a1001c00c03454194043c0840520144e038400c0c001d0083d4a296850302ca94503102880014003040484110600c160b20b407220440c0d03220000100da0749204010708005a032a1500800070344158031141c0070486030442c0000501c1010b40c01581021440c209800b200d200d100c0040013a401d03801200000c807070340c81c2d080c82213411500e422140b0f4a051401085c000078030007205130024100e5802074029400340100044e041003c80c98040000e5110710402c4000c002407400c1021403030907881600c040c54841c503404590451387c122103400310703005030800a0003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 423848507 1250 423847257 423847313
    0x200a200601090218120303130c0812030115180513060902030408090108131a0601120f02181206010b34020f06030610120e060c041401020703030516 65
    0x1200113548045103203045034200700442c0d4a00d0410540030082144c040014509643c0d030b441080c030400c4200c000664102980110015800c03d090040c140c160000b025807554030341c1441d008603c2100c082d0050030400036040b4801c58180950401031041c0c1d901210b46852101d40b400e5428042c0c046a000680310350b100000380400c21500070010a144002070300c03110360941d101842e000b00c0c600c001d0805030482a61009080c20a80e110b050954072200505051076a5a900519102140e035403250301140b031135001400290f50240b00c03a408400c002c1c11107200d09090f100c0102c00b605c070301040c46945403141c4040ac0020405200b1102c0384000d0500c0d88140b041841c800d041c141040840360400d900404e460000192035003080000c0740e02c119005400c5485400c4088000c03521480d041c840f00d80b0031a60b43c3c480c3c20710307401c003440541d000f1244600c1070740d11141031888280046c40c50701410303419940000420400260010152040d50888000c0034400c424581485505054802a02d007401051451 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 423849757 1250 423848507 423848519
    0x302060d0e120c01060b070f30120608030405030715020f0d12150b03060d0203101401030b06010216210609061d0d0c200a031203200a200601 62
    0x81d24840a01c0f1000f0f200c0c0655400d9482030a00c504d000240241103504540c0b00440c4001e4030141341406d01200c00321501d880d10030880b20402c3c0c50010070001880d0704d43c00642d003050300d0040b8006481c807000a585007525000000343c0d5020b02e0710501080a0444002d4040c460081c080780b580c01c041d4134141c81043c0e1000c0c4e4020491a00c1000d0415039501c0c00003226480030b58840b06101746c4100941a5196840300403c10814003440c80c030890b41880340c207880701c1c2e20a85500809028060b012124813180d4103503d4404480c0e40c000b007200303045610030851800d120002580007011650301d415401c01c3d1800482181c03105489038640640244e0900310352070100481c2d42d10120031903007070040054107651801c0c4990f03280e180c2c3c61480c000203101405000085001e402e00705d40d60300028120340a5142030b03140450200100caa005071819400320710000c04254040c041d02c070070082003a2240c900511a00700d61961401000c4044e0100710401146c08203800d000c1995940c030442c440304640c0c40e036035601 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 423851007 1250 423849757 423849793
    0xc0516030507090f0b010512040f020a08030a08011403070320030303070909050702070303081b0d050a1e06230310110d0606020609301603030b030f06010302060d0e 72
    0x11091410042c07070420180d0400c580341c460880000345c1603450380e20b40114000c0030640044080c00c103450740112075013544010394a424004000b008500040d41e100c0c4c6a400014001142c143e0082010064590107914030fa0b0b004140700c800d80c0d80c8000802c52048a5505190450701140c031403d400d480300009111030140c20030781c048101c4014040a00c540d6966041c226115807040c840100483e807880302140b14000442204080300c040414890b003030a4001d810001a5031064882b2041c2a540381400024050449400070080c4007490081c4034242c6070003080e405240800040704c1c400e412440640104e82d030b050008160621642d6414400c0811891912419911000010490524150300090880e002050561144640001404c0792010074400d42540602010341980005012040f50310039801e07000241000c080700a6030100d049942d803038040c0c1182d8410020501c6948015035081d00c030300c80010840d05496041e241e058031013900b581c0d04800f83c60383c8001d816a900600186a104441e55 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 423852257 1250 423851007 423851009
    0x240a03060e07110a03080c0705010f0905070f0312030c0512150a151409030304080d0f030f0603020904032703290f04170f040b09150306100c0516030507 67
    0x40c0d00350310340d241c0301c50b1025a0342c1a80490310b06082c1e0440307070b441000b29000707140307155120320548003462914202e552214210707088010095202a5a020201d0a2000800c10403016004050241401c2c5086072980750a030002c0380e401404158131034800c1000c5502ca03a0131380d100d20b8101c40d00021981820b500d03000c07410f29540b004900070340000b40c00041801030340006403941d030656201c40788924110151012507038080106903406102c1044001080c80007040841c96070707a899a80c03c4001c0c0c440d0840101902d40c014041020076040410600250740d0b01c00ba01c03500664507007400b04144a0504c004101c40101901b210718116070307100000140032182e440e0200c8244080605000703070548520140e0354580a0b40c031300c0d405082c51030000e000a400e940080707413960102c0142d1800c00d940b00103441040d500c541c22150416402103003440392402c001040b000360150b60062242145001c40100b0000000e55020b1420000141c2407003061000a200c1c81c000100c008030b002e2140c0351a0f0901d03903038074070715 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 423853507 1250 423852257 423852269
    0x7021c030f08060a140d05060705040608010f03030f030c11011a0f030607020a0807061e06080c030109021e130c0e0a080a0b01030b04031206032301090b0105240a0306 73
    0x500e100c003a0707040d101c0d01400c1d11414000701030b00c1c0901e0400080c3c0000040d035030760b510f4203c0700d406100c0002c6030f0300b000000d03c9090150394441d84c803410040c000f841290103074004003000d030b0310704810300c002074102d402c010b00c61111303240004580c400d0400488006503403000024141d442c1c405c91941d224a4580c10480120f01640c40e000400b40580c10301d80d42e03850450310600180c11085a075030001d240840286180c5025100c0480c65150248d4100408400800c220356080d981d0310040121841c2440b490600c0403017203000b040008001d4010500103201d0b42a481a07180c100c0e003c0700c006079130b20022101c0c0c004850004001024903000094203864810704100d114600c020300c001180e075030000381001040c0d031000759044580d1a50f61340000f00000500100d09214020409840c000e8040c496600214040c0b45401e190b111040444109840080c80e0785800e43d050a42000114010001080c11a207054405184510340820707810184201445c00d5056a030000907404019981604034000341c0e00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 423854757 1250 423853507 423853517
    0xc090a08060a14010b0301062003040e0f0109140c09030709060305060411030d02030a0507112e020304080307020f06160c08100203010e040f11120304030b07050c07170307021c03 78
    0x1c0182040c0c5000f0034841d4000328032080005008082c4650b0311605a4039442d2110000b4102040540b42140c00681245d085008a00100320719400741400c41e41c014000c00300e0030401140c0d103501625509000a180d07105c40c000002e07151450340c608120010050656200411500c0d80340d2410985032b5100b0f5505407500310040070482102c0c540400c8031014030134240c0056190004400d401d48450300580c909a510310b8400e000c0460584800e41c0d420704c000f00040c04103e082c04905e000d0750002c0c1d8a46003810071903000384414007440000004903070540b41c040303406074409460100052900c0c40b42522125000c1c00c4100f440c4108841803400c5001e558800b0f0503940554000fa001c48200e0000344202105881307482d000c18080b50347d00c05210140c0340900c8542c0c541c0001200880c401601e05940c4403c030760700006040051200c0c2601c030507040001440c000d450300303100c481140c0c0d4900150155031540314003416095001d06003042140c0481c1d0f805003070003156180451411500e14480d107403e0340880c2c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 423856007 1250 423854757 423854771
    0x204050325060c08040518040204051006090605030a020408012919090e010608070803090f09010b03071107090c0302040905090d051602010c06050f1006050906030a050c090a08060a 79
    0x1291607101090710101841010740c0580c03510b01c0c2201d05001024050b030302000100b001040e00e8840503c020040000110aa28282014410b10046800c024019510030341440300920807103521080c003000701d444a180c082e48031388420655500a21580c0d210010030361074030300001c0c00b071188458480880c0305191045582e000c0d0240510108044214824021841f80030007801240103d5004e0035556542000000d40c10b03440c0c81045107040074940110980c1c1e4400714100c0e80c1c038a06101d0607104410252003a0a482d49440d40e4140c02c1d01018090710706201c8001200ca9002c5010040d03000240040c10080c0444a9075070740150096000f4003c4001090400c0009070300c2d12000280702800b01e50b25910717030f860024212100d0020b446880700403410018242c404c0804540316000d0140100725040c0d078078045060400c16000382d002c0f40e500c010244007040c044d0321b040359242002d07281e10068502c0089003584c1c9004030b0104505c580c56481d0f41c00b88480030042206000003940c2841030003210810002c3e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 423857257 1250 423856007 423856033
    0xa090c02192114160305070b01290711040b010203160c050103050108010b0a090b180109061d07020d2a0f0303050c1c02070305091c0201080121020f0a090e0102040503 73
    0x100300f081c029003564460810100319015400b8440310051030080c82c090341450210b0380c41401d411402e9001080e0920031030071004a2b07621144245100c2e9805810480c5090300c60380c1ca00000008180d4024411a9105000c19042e4000d0080707401602001a88000740c41c042d1038605000c0485015560009251038000b246440e01441861940100200300c000369070b14118030880a4a1401c20359500165081c40c00e40181502c100300902a005038103000c600542000c200c0445440b03400400303554405464180460260045021988040030f0724203d120349594003082d10b03900721040450741d00800700d0901901404113840c03807091042d00c69507007840705864444403241c441c060101105941003006800305482076442e4002c040046c480d003443c500341018640010444045103030f40d1768014070302205000456074010b07a50340c090700900c000859404000700b4941130304180c98200a01400d400150789800c0d650f0741840e9002800154000d002c80c0c40803410440c040d420500c101c034024802c80c0080909 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 423858507 1250 423857257 423857267
    0x140702061e070c02220614030f03040e0c1e0406051c05070f050d1d0a12050a0905060901020c040f091e020303070320010c1d0f0a090c021921 62
    0xb4520340c2c0c1e50900d411109400700b22100000c05040d0f5a21184812090384c072071101c1c01110000c058a4511111111160042c181480100c2e84817003003d402c1044180030100030054041c1e0002c3c1c0d20000701703444481c801d403045104103058400190244002c02c0000320180d00030001e013080850382c01740c503c900b03440b4070010090b944107440d00c2000ca911030f00038a8a03140b08001610005034280004140c41c28001150f02c14911440e0012019401040b40607040c020300018141c3c3c254807070b281c03041c03800c42d407003000600c410100e004940c800e080024040101e684204410744804800900401002c81c2d00c01d6103000400e4025421121400052001e50403520350304010441c0700c0d00513025515001c019501201c180300008840b101c42212841c0d11072614100348900c0e07402c01c0b034a0b2200041c41c1c2d100701c02c3c0e0072188004140b041c4070b4191001842105d80710301c0d0707038401214045a8040790203103642c00180e081c1078a140684401c0012850310109002d916480c01c0d03940800d0400d0044940900003086075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 423859757 1250 423858507 423858511
    0x9020103150b0409090201020307060c02030702120606010e060f120c0915091023040303031d0606031c0c0206030c0d1b02030316050702090412020f070f1503140702061e 74
    0x740754010f00007088480d085400a0b031440e4414030580303107041015035458080701e2850700040010303403002c40c0720b90440c18000801505205000002d01c00c0b03283c6040002c122070346102c9443c3c000c400118018203071201c00010b6034040c8403d400d90541600e010600101241c000d656050f129560032051000f1500c403a00c100d07554820060450101d0601c104001d88001c07140460010311540c0a00002840c01c00c0300006d070001e14402e980c00b043d0a40c112000003042c51406d484038a440e00140103101c181d5034002049100c6140c070300f40a81c89a0041f07041520034450b203001c0a90010360020801074104001c40040540c801c0b02441000819142e2034040d50f100507407084800580e0003040070580300100c03070707401b441c02600d01d140640c0b400b6615804901c90f40011b5904492120207141010b02058040c031a40c416400114010844649003188050074107819224503000c108824902c1d1515502c29040003010745280c240058403800d0841000b503a4000448075060203150081c1c1ba05074800015000078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 423861007 1250 423859757 423859769
    0x50f011214190204030809060702061b0114070f0f03150b0a1101060905060a23060703050c01050c1911010b060c06040309232107060306030213062108070204020d0902010315 76
    0x1905003101f510038007070243e0111f0000e0f0384c030000500882644940d210400e6402000441c0007062400001a10581e4840054091001d02c407503414149880c2d6807200391200034090924000c9001d110b00038171543c03003038001d82050b000c900700010000304507038100101d0b4aa01580400821149a40d0401c040440f5000c0c1c0b4465407251015200300400360118210184084c051001c0103c0001c1e485c0024240354045582100801d10101d001c40100000380300381940700c22205000303032625404c800304810260907440440c0074400742030300230601c12009500460840c003014103c2d564864100034041c0e82d600c0116011000100c0024000c282901c43c01080010010418240e9000c0f9003030308100b00061000044010605013a00c0c0c2301003103030000b041100c00502d0103072000a06641140188549003030305170205150701d401c010081050042500d19802c0720310002310000d1451541c0c0ca070040441c42503690280d400360011800d00407240c43d81c0d02142c4907a200b40c07820031000c0c107107110440703082055104030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 423862257 1250 423861007 423861023
    0x1f02060117030405011d09011d09010605011e030b100804051b060d02030408130314010b122104080a050304050a05180c0d06030204050f0405010507051201050f01121419020403 77
    0x2040076501440c0d1000081c680c0c0310000c0d0300d11b440100450840c0034241d000010820340c0111a03000441c8180c0c2480e009000b04000780001ca080000292100c41c43c000f44c0c10346480780d107140380851840307940034807031001c40185044510750302031400a000c5801610191000d0240400084100c44c107030406c600d0341140a4503260900c3c2d00f051465009410041044c2e42000c1c00700001e03400383e4003802d125401781d84100030307142401203003988003400c40d20310388100c0340550742c030350010031201c4400200b01030740100da0b140c4e9403a001c0215800d46102d01603940034032028031421075410200800400500180d62042c1c4140e1012030341e50040003480840c51040c25201c080c090041041080500700401a0305244000450031580e2980881d04503031041390101240b01485051000b000828010186c20101902c0d0103801d10100d800711100c803607010301c40d0390320900c003420091949900403001800b9201ca1003a00b00040d050b0301c1c100c103240c3c50044404581c0d10003822941c00d41c10b0f0346442550192070300b00040f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 423863507 1250 423862257 423862259
    0x6120b0604020706020c0f011a03010c080105040b0d20100e061b010209060705010501140f060307260a0902010f08090705210d0c15050f06010309030e1f020601170304 73
    0xd01000f988400410744031142c00308011030080300108031150220861100001c2c2045202055011401220700c0320752190341400c46d500e4000c2d40c800f1169055074800c440001d0a681c012002403020310030a40c009140d0f1042c4d50000340c1c0d072400820103030a004400da44664656418400c22100c10120f144140d51080e410321a80d41076500340c198806400d02808001880d2883c05000210240c0080300119800da459200500900e0301400c2e00c404440f9043d1401c4140880e001f0000d412400002c291310208508400f091030380010380c03d118a800c45203140030b8401400d180700d8003005440355200136030125142c101c00c20125031103000414481c10351038002c0e09105007040b04010355003a252481d03114004c000c1c00f4502208800340047d0b040029a41c0b10003034407502600e00304455000038003d0801c0e00b860203040080b01b14941001a910070824600001d0b49112854103880310340d9601c0b00c01d50484811140c1c42c1007407200c40d5154401622607001c54605e0380e0b0b02c40c6020340316141c800d95414560030901c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 423864757 1250 423863507 423863509
    0x60e060d0b0702011e0c090807050612100909060b040b030c10110c060408010c08070e01050931020306040e01090c0b030c04091113050303191b150e0106120b06 70
    0x15420340c020500f480080340051000f400f0000d1a0500078032030266070703540e45402c1034158101480e00c00034400d20b4080c1000d24a0314001175401e0041c0515582c00d44c2c00380707000591a80540e1140b402520181904101105550401c0c04c0149408000c65019034500000c1000030b250000d0074401c03404005008860311022510229900082c40705c03482e10a01c500310b801d4000e56504406040a801c000c4000104c2404003040204100c401401c220103008a5081c1d8102c0d42e60710404076200d001c020740703480211440c2d4070300c40741c4840304802056103030b185c2008007010010030340c4d0003e5000ea40111030900c220714079181c445007200d140c41e134014100b00004000308000803010f000796610a038194107250400e0740d1001030030241c40079501d0344554400300040809064001d500d000b0003409007540110309041c02a510544404452050401840305070f56001407403888250051146a9011102d103140e2182d400b24100a043c0d8a000c0e202d0342d500300040800e002040c2142d00302481e400103c45213242c2c44401c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 423866007 1250 423864757 423864773
    0x608151c080c0d02010507080108030403111f02250806040209130b090a0302070b03191e1104031502091008060310052d0c0d020c0a120909060e060d 65
    0x4120a005100c00010000818041e1010b840031801c050040c00c6540d45414000b400c5440c018404410301c2201001408074150010a580540764840741150724000e240000400d101c0301c00c202004c440d02d42400345641d1560200d00e140903840c0304000584030b240c084c0c00040c0c0c18003007405642800e1784550001005480d020a045402c103c00c0f410b0b00c502d40160342c45801003403408440b1062694004041801010b5040040750300805864620340c0c154148241c01e46110810f0203d41070030a5140e1540540540460f1610003214103901420020003800c061461101c2d0400d00c01a5071301a00545514500314550007103038003c03c0003c281c100342e10310102040d1068140a451582c0500c02c155103032034502e80b144034640c05042064906140d8040d10703403824091a154206081d41840c1038001e0103500b0b07280c50291038134201401000750b2038901c0c01600a1070311000d29009011550380d101b0031541c2d15080000381080c2c1e0b44540e0184681612480e208034407542c107071111504040c40540100100d1211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 423867257 1250 423866007 423866029
    0x30a020c0108040609021c05070806040b040609022805010809070e0105090c0c150402030c18060616060c09180606020c1c1205090f030a0c1205030c03030403031401060815 75
    0x240400080c5d1071000d802295105c51403281105034544144201c100f0303c142003040d103006001000c01045285410f0f0381e009013005004d040102010f45400700314085542e140a4071178400b01000070b030503031141c0140a2008a040b544581408174400001007030340c4140202e007a07070a8841c10307840f03011145d1801007404107150005040300390851060108000b03421041c0100c41c0c804804004076a49030906004040c2011111800e140c03054200400c42503040c5d01d100305456110380201d070318684611040d9184049004021002080e9a107000c00030000c2d01c1c0c1149d162400d40385800240440c451000c01454120782803030040d4005030b800205902c04620305503880301c1244e40c00d1650b000e18803820760348041c4205c032044400d0000c00c1c000f2451182602300310b110000108800c400601c003860031078a07110340d020140d001e0b501b4030a0418040000f4864204100c3d140491464100d82e42ca01e49420020300030800803d101000224007000010f456115601060086c46000d4010343c200c15401c00f008100451 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 423868507 1250 423867257 423867263
    0x60c0405150403022803080d090312140114010e0603041a0906100b0703030204030803070905011806080c0307171608150f040b030f0d03020c100504080a050d0b1302130503030a020c010804 82
    0x1712020000504120181100a03904003000c80c10412610b0301800c2d07801c0014218030468541580c28081d40e51081405044444000c0402d02d00c2400c0340048400d0328000016541002e40001404200712882c141c90382c03822b610541d03c3c91183c440400090b19000700b604c5851680c0c2a00c1000c0c400b0300b10450040201c98424280103140c84d40c2c03a40c40007180c0d007044031130f00003042c44428100850750300000d054080d0032198440303200c2c0b44c0c10044094018000074120b1100e1034030210001d0049401a50340e2403a118001280e00c03414505aa440540b80e00441c9000001444000c00729138214080d68501414000081801548000c03607018400148400c402003603042c858082c0d001d808080500080e010346034982d030050f0303482485a40092a0007100e450902c40c0034504000c10001c182070009442c4da51003949480d650340c1001c0c141e07090107060000d0995920207072007001070b00e00c44056030007010000d000b01d035405412a40d440415440b4019031314080c01582040c071003080d0941c0714500c010b501902c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 423869757 1250 423868507 423868579
    0x60f020c0a030803271504080f07080406030e1c081315020a0212030c09090a0213060e010f11100c02030f07050c010809031c02030a0b03060c040515040302 68
    0x9210000788160165a100781d42d128000014442c4001c80300e05901c1c1034901000c6990410140740c90b5190340c0b011105000d403201c072240307400705040050080488010908400103151508840d040c840d02d242d01c1485494082490007605036800407001c990580c1c1c030310b1003d00702c40b000c04400b80161000c05c4004c001001d808802c800302c400103414416654003040d100100181c41d16440302010b40b400d1091200700c07500e0031047c010440340d00803001c02c496120b20300713540f04a800e441d84080e01000e8020304454140907039810002007041540802082c2271040240c0e0740c0400040020f02c10340341075050390810305068002001343d0220300031a070802c0001c4169881160b15110080000003643d80003004c01300c030b294120703150100b420340c0c0c4044c0da950400740301400345190a60020000d41e001500e2060900c0c0c40e500400001d0340c580c05907005040402c00501641c40501d840c0540c5030003640070703001c1e0394480c0c0d480b034420801145801040e1400e0320b50181a94000c400440e4940da85481035024582c1c03919 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 423871007 1250 423869757 423869773
    0x30a1403160b100605040f060f0c05240a090c05060a1808070509011d040609030e090f010504050c07030e0910121b05060c0a06050703020d0216021002010c050301060f02 74
    0x905694500340728980a86002c0c0d4450402038807403280040690300000422105000521179a4002d00c980d0741100e06508000e01d2040c032070b40c402e035150160880003800c80e0280d9205250700c2c0c803040f00900101070780b142c00001c0598031000840c041310b0b22035201803c4005605014000ca04004c4010106c510b001d00388010140c030720702c00c84403150f41c2a80001d28585c01080d4104076900f001440a80940001c07240d5524105084030314042000c0001d001803c0c140e214040c0505040c0185554622202d001c1e00010a1f840c1c40118080415828407403140100d280c480024031141c2c16005449c58641c0c03580d07801c294441ca4030100409000007801d5424688103220002860036000100c50101600c15030003c034141990060301c41640c155a40024000c0200b0003954030105e0700071400c1104a580840e00080603210160304500034000c40000c3c8021510004100d81c5081c40100841134452003155039001d041780d5450201c2c00d80b0828145440401c40504c01070000c6c030f0198a020000c0c45242c81150300c51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 423872257 1250 423871007 423871027
    0xc050f0705150a0525030213240e0a05090c0c0604140c01030b0f01120f0c0e1512190e0307060603031d090c13050d0c18050105030a1403 60
    0x29900056084600c2c0d4041140c002c1d41c8881e48a4050740450a54020407039403134400b00112000850000f114840c00a450001d40e040f40240c0c103880d8450040507801466940303954542c4208007865949506200301d902c407081e005440ad1007074181c00301740500480c20b150b140c0400c1c40300780388024200440c21102405a42040242000850303c01ced8040c0091181403215280320909101400c0e100324101410140c45201e0754550440c1000280c40030310342250307000b2803a914039001f4407005504101090030080e0072100d0710b80c840104001000b00b1941071207040000c0c0411034681c41200401a00300d003800001602041c5003180690061008a034041409940f81103001d0541d8400fa804946180d9148028014561b22514902c0c4082a420302d003064941e034800011080d074002841603044243c00180401c4d0961508030b002c0040402800c0009000058501014000c01a00690922510b8034084601f001c150b80170302812283c0c098003405c0c0784000e5132108004029582d0410780c3c0d0b840100010052 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 423873507 1250 423872257 423872287
    0x30715030b0d1703100e010b03060906010e04051f060912030e19031a0f04020904080309010b031e120310090c03060b16050705010e03100905160b030601081e06040c05 73
    0x5140141c881c1c0703076528038005c0724429403014150010107144500c4030050000000394000c0b682c200000321203851150381c81000498028a41e100080c5e0424102028402a00007806000c03216030b00343c2e10075161003501c0700f90448501d044c2c0e11400a030103004c00d8822010a010344000c000300c19002e00940b0912004840801a841e6103600c210707288207102020844511562150700d4011120307104001d56030400c0d800190000c1030182001d80401000000300318045000d50100144040290540b180c441c0038286200340180d00300803a5095000c0c0d80382d1001d0b118502012244114103003c008c031b0b80981428440030003003071803001c0102859603406000c501c85074080040c0c200c002c0840d8030f204a410fa00d103440b50801155502403414404100703110b00701c80e5408240d0454a1488900006024981d41042483e084500115501c21954403034041609da80890045204071380c00c4c1c07034044164a170141c3c04170310704070a03455501c01c00c1c41d100e010039000e203480d0300a0001030180c0d1400ca42841080d00c00c00358 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 423874757 1250 423873507 423873533
    0x3030f090b0c031003200a0603110a030f0213060509041404050a0807030e0d110a050a270f020c031312030c03050a0c0606120510050c04050616060603140c030715030b0d 74
    0x1580d05a46d102840750b14004141ea4048d08441c40d00b8001c82c8811031408050b8083d41a000d010702d502e03100c103010665040c0d41911303514506e040f16010655074a01001d80581d004502d100d0140d0f0030302d041c000307091021003100c50060760b00c04010407080d0910344030100b10341c1180b44120104441480710351019074030325080c260813501819010310780505480400007010380552210f40204481c00b01006007408800c1c142c022048040b00380c601074001c0c0c5281900510304696940ca40d0b0384003041e003803515080000500300070b8009412a10000b40c0390082624016241da00050009a201203080c002031302c07400c06081000d1290502c40140a010740d6107000756207158006030004d030300440d0340c00b0602c94100320610007070300d0f900003c0240f07050034071001c0e006100b180141c0b03002e403c0c0056140d000d000030000000d4070640100003007001e0350f102d00d4810000822501e8611041c4614040034490b482c0118206080790760301d052040d03414045c08030a8000c0c1030109403e6034481e080412a9001c104840f001c14 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 423876007 1250 423874757 423874793
    0x2070501051e0901050603061305102c070810020c010e0607050d0605011e0804030c14060402091f060e030f0619050907060504120f12030903030f090b0c031003 70
    0xa03608200d1000602c52488009100c444503030305250a0004980b004140c0b035422a010b200c40c8148901c143c1056850880036419203245c0d5850144002c2c040f50070840c031042c130200c0341e81081e0501c41c001240550703945241e0240342d12070340005801e500c0711040e030b074000c1000310380400004c6040c84001e51007908140c4103da11001056000070345084d9000745e80b044501402d40ad0034106000200d6175140307141d00311300184001c00d0065140c046401e040c00b40b801440100d0340407203010365088100307000c152a80d00954041f401461100c02040a4190a0101c20030395440340800300840303403400600301c1d43c401c01d051141da0140641341600c0001e1a003881481c1c41110b02d490583c80e11700080c19801d0860350700811080b00d54001102c2480140e501100b1502120018072558049401600b041c58034181210b070b008050b545d41c441111200e1743c01d5040509072500940f420482d40d1400b56908040d02c001c03500c000c20100184002890f00c0e100c150107150003031134103191031000c16141d6480f1400070700c003d1010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 423877257 1250 423876007 423876031
    0xf09060509010f090c031b12081804050705030f0403112b09050a1503060f03060509070905100303081e0702060f060d0803150f060f0901121a0904060207050105 70
    0x40d070300c00240289102c004049100300814030458807000c91850503800014011190328003045500b181289008006d845c080c400c041c4041c89034540140383c1e500003c2110071000d00c8031120441807905201d001d101c0c4869850703240c6075655140707001d16482c200030822024401c8c0300002115100081180460400c2c4403c0420400140c0220303081608034080c0d0700c8005c0184200c1d0510264132241c5194040b00d01400d4a611050761001c000c0d400313826540c100381c9891040041c000b0500c003180d0030440c082d01181050390841d5480c0c60800e810b86604841000d910645207030300f000020f00c203c00f455844485200644240300d0426000c00c5a403c09031307900300043e8003200600c106645050072843c0c0110085421581c60031056940004500004045a0864410070700d4001c0e86d03243ca1629880d060300081c1200d42e02d02e00900b410a86030808100d5a0000e031503e04440c49051262103500250354800401070460a020000c00c40c1c645002441154a140c0900401001a01c04d00405005020450325 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 423878507 1250 423877257 423877261
    0x9060f090d0b100f0806220f0213020301030b070f051e091c0203151003020108090f07090c030e070308030115050c0d020d0f080f0c160c080106050321030a0207060f090605 75
    0x41c4d0307220350454020b008140c00500c01c0c0002c2d10114026505c4859001c0100c0c040c5144c42d045c000108604040040e401c03030304140d001506403030294001d5058900c602400141900c801000701c48043c00c21000f5000305008104107407030042c04003045141c0d141102101850034160038003090b040021644903c5103038011140c400c0440c0b03010301c5000d451401c1802d0503d0b00b8030f0419603141040d001807201a0501040340c020070540c0310280241c0c1410344061040b10450381c2d6800302100200404038403200082d140028001e80c1c04004610740086a4114928500f1642003403030f03850b418004e503024482807050400120040580034404050f40f040e45030090500d41c4103841c00901400303002d111090800c2520000c10403c40060780410f034001303070100d00403a150258003101c10402980310402070b00140401d100040c504105410032402d66006505403942c130030030344a141d1541d00100042003c2d0b14401c4c000129249010782c040d00744980540e0b004a0034020710340911003120400401030747e00c0340d00c80c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 423879757 1250 423878507 423878519
    0x1020714071d0a050a0905150603011107080304150603020d110a06052b0209040e0f10090b070c020f0607030e0a0e01080706030e030c0d0c0506010b09060f090d0b10 72
    0x42900520b01c450319010200044860342e00c000300d009002014059444003c83d0f01d9480700e500916071141c0c810126914030854855450052400b102c2e080c0c442d6082c42c001c0d017600d00101054840c099880000503041d9102da55039444030348150124010507940d40c500010160f65801e03124018030340200075803402d600c100d005000764900075030001002d00c03030308004070b0300c2459003001d11207041e0300080300c03200d1800c1030740311b44c803000e481002c03007a551060800b002001e24103000701d01440700191020480f484071600000d0039050361502d60000e04810141c0380041c1403607014031054625203200a02d803a00c00490300c000074000f908170200c294001401100703065000c0c10180c100300060503e82007041c1e010b61400307015a94a544c0e500500080640711444030021020400030f45110748091415102030039041040103100da03503844002c0e9400e03c5a50000582135202e07000b10f5141000140106281030004a0111100d034400c0001c02c2d0060600d0f400139001c01e0060302d42074000c10f9034500d81030406203051 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 423881007 1250 423879757 423879763
    0x15010312030b060313200604090605030c0f0f15040b13051e1507080412050109200102070501051c0507020f0d03020306100c020a0b030a0c090909020d02091801020714 73
    0x82d10080c0a041c041003803000c44050b01ca943d0003e01c0e4400e12034440750340420700341c11031440c507408042d80210002c6808948194182c004006890041d02158100901c0f0b004220809050758050368000448142100890903c0a903a14440c800380300340e2807034250384690002c02640004002400801e044c4401e0103030380b5061100074991401c90206001c0290004001405c450701c00d41310030b42111000644104005400c404d481c002d140241040c2c124103294100300e40a01401c8404071184c1590340c1031000c0c820b9030800b004600040c182d004000c100d0908005482d6680318954002c124031403000b9500151036a402881d2080130185e000d0650940c0f5101198a0004030421140a00d40144200711071900d900031441242003180c5000c101c070315001d00201d85c4503d0540c101c0c480d5401d002081209a8880707401111800c502c6960703860196554a80389001c607440044003d511103017034040c8202500e005079072141c100e00141c08407460b10b290440e030701d422030744a580c00b04c0d1100e40c4c0c12162280e03034a0034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 423882257 1250 423881007 423881021
    0x1030f020907090324061e0b0a03150305300a0305130b240109061b140f15010506091c02060c1e120406050406030c121107020301050106030c050904020702031501031203 74
    0x86020300c1d0804840d01550017451815000701c040035000402c0010025220760417020b02f6000303003080695025101c0c20200e80b03a80030303030740c2c580c000132a500090000c2c0d0302440c0f000030008107039980107401c0ca01e07212800c4014150203050380403020503036015080850702a40d120b40c0908400c50f00000c80c1d803c1c0d9101c0490301c8601c0c0000038140002403070208001d1b40c20140d070344c410b81e5034a4000414031080389000090b8121a826082862041441840305684002420889405000342c0d0b14660782c2c1e11010050103200301d1751490780101d035590402081c40b410040c007196107840108080d08000100d001c403446c02d21609221840080500b4007410040000d110610300401301206a9207090309200f400f800612984c8141d004140e41c070320000398058403c1500c074840f00200c0c00300340b00c2c00c00800d00c6220650441c40003640f080d4603242c000100e540c024070034040d2030f0049440d554104450707c400c100003904900c1d41039801d402410003400f4000d0300c0d111031501851090104030b00ea8214507400404079040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 423883507 1250 423882257 423882269
    0x409020901150e030c01051e0412050d0e0301060311010804140610052e0c050307051006060e0a1401110102040302090a0510080a02030709090510050702030a0e03010501030f02090709032406 83
    0x800c0019034090b0361301004441c4803a0303e5201140b4009648c5001410900c1030741d101140400c0c2c28181e000030000041019402d41c0e0762503454006501d080d80400d0300700c1342640320040c410b80141c224642c2030750180412943c4a070040d450359032056400034800e81004170031503c00090103c1d402041c821454001240c2d080e01d01660b01000c00c901e07103071004598002907240d4030030901606150410400c04204100d8200d85c1d44642a01d0004002441c414007401d01e6001d58408207038454444c080c1c50030484016000c5600e440d2502006043c40c90054422120890801340295000c11001c00035032035880d035041c05281c01400c00501c07898041130490186420303400030200741c0c00c50070680303025a800140f107000f17403098600c9c000f40400451400300e140c0b1035841c02e1a12024100000c1001c41c64001c00581203104c0651201d1911441000c00c260032a03009000040031b1034030303280300c92015042c490910f51b032002503802c082c450a0f8a94442031400d03038a50729007040600d4440300104421119028440c000c1072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 423884757 1250 423883507 423883513
    0x6090605030912070203100c081605120f06030312040b0406060b0703050306040b12010c020601030309090e120f0f1602040f05090c09071803060e1209060a08060409020901150e03 78
    0x189990382c5610742d031140314190f0721150003081c25001e541c1c0501ca000c0000008500811800d51540b80143c48900120340907140f00080b038a629561a020b901146c80c1c1d09101c2d50144025a00c08402808802c130103070800f40c041c401440807451a030005001107018901034211003543d40361034504078068803215002104040320621851000940101c00c0e01c1d00110207c40110700c5200b450081102d04400e1f1041e4061036007840c012130005a004200a0f050f00d019030783d0050090740b1040980243c2d0003200800805a210035a0f050901c1c800002038240c0d1400304510520b421076030300e18009260015100c070118a120743e0600303003c6180034402c00ba005482d070107052103d45004401c00d42c40710755801010f40100d2124000800141c890b1500d5044103000b81e01c40f0004580701d05110000b0140341d00f1940840c40b9618250212484020554080c02e8000b04078034a40f288501c006c607241e0102030b02d1075401945502c1c80c240140d0b614044c0718080e10f80601d01a001d1031003443c2c0108100c0180c851b06000303030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 423886007 1250 423884757 423884761
    0x81203010e01060c170d0209040606030903020d0e030a1425061d100813170901110601050a03080a030f1a030d230a1e05070c140108160201180503040609060503 70
    0x5280304840e4100e40382d0780000d854980c80886c030302d000a0310503803503045c3d0b1240c80c103038000c01d495415920030031200d4002c2d07088480041c0c400c030b82580d10901e062000c070351540c00341c89840002100340603000858200d081c161a144500400c0800c2d00ca40b007290400c0380410b0000701880601d9000c00001948003002c5601c01c240030894000ca0403914805400b00d08100004001920032083c8503090700340c3d140c1c440c940440c4d400301d100d094490b075048250114001740c00e64215042150b800a1101d05035000100040041d5246d503503204115030201000310281a2604a180d9031000c8620a40a81c954000e52024842e2050f20415080c240c051a84000740003484241072403a0480b002540c01c0c208042050380d0341c40110b080305403010307014011b0f00c80851130200e407050f18280d071000c082c0900610406004200e1b50310380c1d0f524222100c100200c0b43c00180f000d00040c2c006011646020b803080f510340000900c60910000404600010210a840a0f400000c04000c1183c1c404000c0d0014856850070354114 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 423887257 1250 423886007 423886013
    0xb01020a0c240f0e0105070204091202010b01110a05060105280305030712030c090b0c01240806070203070807020d0c0b030a14220809010e061318050c09011404081203010e01060c 78
    0x1071104c403840c15042000119005003107499903480070f540c094101d03d1485103900e480c44000c0c060028401342d02d00155005100710210000056517405456108020703000582c20301043c0000c41000c480a6040c2c41041000c46101d88102101d0802560084002e941d499840d820301c0840b010703440c0070003c20185070002c428880c9a00c0002c03001540d0303a0200842d61003840300c0503640946030150115080118071b81c0301c0c05222074800001e02c1190385032810b482450380c813558181e03224050180007070040300e8204100c400506e040c15041c20f440b84140301c80502b140c0c03966520340d820340044801e8a030150ba124000180303d01c0ca141070310b5002c1e0f07582d00c1c031101c0b1005010100310740d904000401480e184002c104040560b0041c0a444012540940243d071500071400c1d90101c110220700c540d10038600110843d11041e02c4c81c0c010715205007805002689043c1d01031004460a0031190401d1226203811720000ca1011000d104410154125040003a100e50400d40316005640040e401142403010414501c400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 423888507 1250 423887257 423887267
    0xd09321801030303050c070b1501090b04080c040f0905030304030c210201050a0b1f051e070305040609060201060302010806190e100503480a0e1e04080d0b01020a0c240f 74
    0x1c4580d0800220184030049e10060302c1c5c2036001d801c545c1130300b4404207020900e41c2c0d0010350600b030318500311003e1104c43d250010708021a410b015000d0302c25042000040c000c02e0064106240f1203201e01d15175100c480c401c02010a4000342200da02c00140d441d0014803403400540d014580d030000c005c54100041d40181d8003a10040f05040070520140100800c0012004483c4926491000420103130b0598551061400409035482400381c01d000c68072403440880c41c1881481035105681c0d061f102c0301002d8841904210a0301c1580300a07070b1840c40807500100304942d51098003801000512043c00d0003d0421041504006c00a8415190080d004100c2104e10b1525104440301c04c1c0c0f0000440c03440c20052a0354900c0038048400780760400b44040002a03c608802d00b0980309464518942c0a104590302065443d450141d40c041c021107020b110003c000020356020190504050040300c1c0120320075134942c40461426840050f1412900d02003140098945409008200d00c900e04441d01c03e200c0200540 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 423889757 1250 423888507 423888511
    0x203090d02010c0b13050609030c100209030a05070603150605121515031f1403120c0124030308010602060c2b0f05090d09321801030303050c070b 64
    0x100c1040001800815a40a0494100701c1a00301103800c03e980b8004903003085030141210116000c1c4a41c0c030004d07168185c044280c1c0d880c40710302c50240c00714010071011000070350014a5000d03803500a20001100086040103590b000b088551070200f0f0020500c04c119001c2d0301264400c20608c4000c00c03250182118000c405a0701104903502801c40e919032101103030050004404040c88554000103029408039221200a00c0c119801506031000c0d848001c1c050030700096808258141d8003024a0013800481da8001d456000c11000000507010b62130310401e906a0a000705a00e0781845026003401410781c490046030150a81d8001044241481c0e82d14405c20f202da48500365508440301c0b160303094600096802260901c6642d01400900745075400c04000f444240c0d401c402a10680103c401c0c0d881c050038903901201e00540006810040c90a03000e03020700e02800b4074200985514031106043c0c0d686a00500101c42c09108a0700c2560562501400b200c20181c030f908a0301d80c003805002d00203505d24501607 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 423891007 1250 423889757 423889759
    0x10605010e09042a060e0910060519020c03071805010e0c0d0b040603060203090606040c020708030d0f0209060a020a050105060418030c030309020402031e1303090501050c0c180106030b090601020309 87
    0x4041c1d00d800f507004c880c0041c010b00c004000643c60200c001540b603403100c580f083d07100c0c040b21101880d455105503c8003d90301481080003250341440036424501c01c0d410040b07180c108074016280d2501c41c00000908000c0f15402410300a2200e410304505840785200381d9000d400350480103003c41c20f0114512003a40a10802c121507a03445601035899500c031a000716000750b0f481082551642040c0c01d0140d1100402c5883d04e0049207840d100c80203140c4002040021a03008802035441c0ca2043c0c0c0200000e842400b8421400d83c3c0c0801c0788450b00c0e111000146020b01e07080c1d0281201c84418a401800d561000d0512403145007011411044810050661055998103081c0f0b9403404115140580251410401c0698040d2000c0b041003070f61110046030038231a80a00c4600c00e01e50391900c1074075035200d00700035028001070341420050040d94015002000c69940907401c0fa07050f101480c0014840c00010f4500340b0343c8507401d01c0100b0080c0c2d050f0103105584401207680160520f09400001e41d80d005007487c517 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 423892257 1250 423891007 423891023
    0x8060412020c0402040306060e06030a11130605060703180e1501030203090a061103090f0f030d0b060d0608030a110a020f090606041703070b090703050a030e18090c03010605010e0904 80
    0x40c10025008020030918414054003d5403510b9503401c0c500010a181c1c0301e414810102c80d000280e007440c0c00320f99075180c1c9600c00340ca8000780b5210801d101c07120248100648080c0d5072003001280541e9000c014140381c5203e940e1f040054041c580072880c401c1ea032a404617080100310814849403405845100407165000c1c0380041c0c0b81e646038202c2505c2c01c01000d6000c3e280c18030303145000d42681c1c00d0170021440364203503008171139400301d81411302a42c0340c2c03100c408039249070800c2c000d0a1182486030008000c5400c01032800341411250142c1104955056018810a40c00099081e000d030b0f80024181c52141c482a01800c0443c1b41c58010036100001b00c40c4c014030034004200020100da0b2400c0c1520003501e00004164490028022800d9403540400c03401d4600120803800140041e6000508401340ca40c894080c00881c0b80c0e641e401e4640021a03205a03a0190740006030300c1c0700700c949512241c8503501d444001d194001920050500b11642500700b1030407c00c0385010068251107c4e5040358106170711440c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 423893507 1250 423892257 423892283
    0x406143702030907080d0f09090c090308030a1a1c03122007021810092a0e0f040510060c0609080715050a0603020109170705030d020d0201050c04080604 67
    0x2030110345015003004800014404401d1110000740050300758252203034101180c10001441c0c805850b0744c034100c0c0c410380c000384811205015184c5550855041c02515013032512a0640769603031b44250383c0040350704c41c1c4010703916030645101c039a5a0801d02e402d03103016515050001c8450740c1009040710551800340902521400009840205510411020200a90b14281e4151002d80c00c5130550000105902c01e603440c0030002003440c46000c005000700c002d04007021699290085503005050254400001103244801c002150507620840e82c2d1504903d43d5806180124101048100075095811038050762408003000011100c1031a100166903881c28480b85030480c9203458005000014002400710300c0208040c0d040003c6e501c126614450b4000c8284000d540303510401045800d18130000e80000e0314200d00b0848000d4203154a4103481a0710182e0f038a441e141c8012900d04810702e00d651005034001601e484c001942841070903001a0700f01e1002e481d0038500383e14031b903888001500c09402c018140075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 423894757 1250 423893507 423893581
    0x71e0c060915030c0c120302122203140d060e061201090308150f0a06030203090708012906090d0305031b07020f190905010e07030f0209030a170c0a050105040614 71
    0x1501d200680c0c4860301b141c81440d03000005001e50010a28821300c18400004952840e152210111030302d040140d605a280019031011101c05451503641d10000d4070800040b10009031501038100a0f11000003d480c0e503007441000d000800b0351501c1903c00c00d03450079401c03000003640310b504581c00000c034800418454102600041c0759041c00f03403105600c800e1402c400074507107806070003462041036a0001c0d24041c0365924402400e07035038840c90301001d00040c1c4142c40e604040c50415141ca504000d082a4105040e21003c1080321112a0080e408100c011040014880c182400c21200302c0c0b590140c4d9042c00300c950301040103507880c9070940d480361012400401c07002940d030707004d203004141c402c80910195a60300e08425a4800685048002a003080c0c0b4401610a40c0d00840d0201c08000c0d00504503543d640d02c41d109040c03804000008200010003c0340c0c910b0000b0003440000320f005200002e41401e041c43e0801c225251a0401a001c000702c0c0100804480c5442c680481c07454249070003c19035003104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 423896007 1250 423894757 423894767
    0x2061320120d0801170703030807030b04020c06010302092a03130213052212080c0405030a060515090903030f0a1b0e0a0f141203071e0c060915030c 65
    0x2a40254100c40381d40c0d2a800d1040780062030754810350703842e100d80e95941d0700c82841104001000011030200d510920007000002c0c4501d502a41c41066441c0008200c5914030004090342d03c0f680620a01e540450014415858038400300742d00000c0c420074200f6aa2091103201750381200c840c030300c48a2040080700180304005410003185815600410004854004207010002080241c400c14480313060b9030908000c0018940e520f50310b130f030b8019100076410301005104461846004016150500080c40b0002c0c19440401600c0c40300c9100300d9000c1503c0c40d0540020784290041030f21507214003510000c4c41040000030049075081030366003030360342c0d141c0c0d4a22103048041d00c114a2952556250080f555901c0341c5c8c482c2083e100300000700c0b0140c103410b98981d0280d40582141c0191007590928001d00655031900d104403600c103850200c140c0e400c045098541583c100c040312004c0c0051103038000ea140410200c000131001400f601c0c00c010180500301803c8a5000103500b04480500d80c1d1079443c031500e54028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 423897257 1250 423896007 423896063
    0x607021902150c030d060501050304201915020105060609420c1501032310060f0f0b040b04062714041413060c051909031101020613 58
    0x20401550b505041c208142d0701d92026085d900d1681c6000408a1a9880380086a011380d410100c0c62400701070074400b203991130318802a113962103108904207074401007a522485d03004160380c80790003600c0284c10314081d003581c0e40105250700c1608100540c02440d03035420800c840c104a0602c10f11f821440d121041500f0a20485440c003a072150100005080c00c004001040d102c4d1910342601c101c200c0e02c68900c1014002800010121402c03000054520b81c18401040200341c88601111510311404a2500031079145400c218a2489140000c0c0440c4688005031001046004842d92401c0c1c42c02809203224002c5005440400c100c0c080e00c024813500c1c0c10444202c50340700700c0008903890355440d030700b0034541c42c2182c03002d0089040184244aa1030705068070341c41840000001c0840058a60303a490041c40e00c0d01c24881840f800780070042074034415030f40f01902e5012607155103140c103086082c5541c200030074101c828115440032040200b0224111240c1801540c000d9450f21803607461502249038500c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 423898507 1250 423897257 423897289
    0x21021c02130510081e06060d0203130c1e06080c040305160504051303170a0e0f1014070e0f060d021216050304030f12090c0e04030906020607021902 65
    0x81080310041d54914901002c5600441e181c0012424000381036800c01021121120040000074455220200d090b00b900d5000c4002400036140c00e8041140c0c1080741c000b40d8621418103402d1a220041090601c0f0003800b40038001c5140c0070000209414000100190042000300285180841d83c241880001d407406564132406666103685481c03d03200541880c0d10071144920f0a09010810000840788502d082ea41c241d50348048203031001c0e5000700c03000d00140032494242d6841500c003005002c24441510300c0c2c4d400c1e070050448800524505415030b600c510014540d08084014400715036004111400d483c1800c0d2100c0030f00440f80000140c4034003800d645003c0141c00055064104c102d01075619215a400b90581780c24041041b604440a0100722402004503015510300a00c0c24000d11581c0d021031035403400420507601c1c6c0d5940310394400c2c4580c480b03071a0040303807000d20041640000c01c020141010380b006109900e0701e120001c1d40c0c0c55100c078401060509085085055403500d550784405660703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 423899757 1250 423898507 423898511
    0x412020a090603061e020a12020f04080d0f02010c0f1d190603090c0801060e0402060705010204081002070201020105180705210105090705100201020901050403170702130c03060621021c 81
    0xf82d2800c110001d010b00c11804003070600a042c031403840741e800d442580c4403c11142d5a08407490540242d440095020841c41d1030281c20500c00002c0350390b020094480c01250940e180140c0b400305103006400c1d118915406014880342c442e422001a42c007200c041c0f0690b5411041d0707021881c080700818000c80c60b4003058050504601e8000c10042c3e0141c1145a805125800c003000c0c055544603031900300e415902440321041482d01c0403030094509480035244c054001e00005107000c5c2d0314004030786050881d0007148041038012442d84d06560302841507130b41c40b40201100780f0100b40b410504c03d407504918050184203a101030440b95001c20000018011180a040208214148903030b0351540c034505803160910031808142c1400003d0b00c18001d507941020180c4420f0708050455407560b0f06881d403160440c400310018170101c0d000d655001c0824809900c150320005041810340c40080a40ba0b440d0001c81c00c4c40542c144419130a0721113881d0383d0400700c4031a4016150020080d00c1c0317141070303004420600014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 423901007 1250 423899757 423899759
    0x302130f050f01080c22090e010b1809120a0201090618050f120a1d0613090605030f0c0409020109080607030e0c0f0607150626060f09030412020a0906 66
    0x8455409141038a1088514400b007404102c0110307083c03030040b03610070040141400a0403c031007905d094991401210105245217948482050040304c031082102d4500760b450340f845908508202100443c5064500d03154070062600001e15030f0350b5250010807419407800018a046c002d4400e500401000b85e11031018060754021100238009040b40b00c00c01d540360701555110241c0c0349400914010f418140c0442c450400c00e0f00034094412449001d000c405070f01e4000f60340c0320390342d0780c2c00003d003140042401c604460a04000154044411940146000358442c0c2021039403000700040341200c80808407804180380081788012680ba01080c1c0c4114551703c90001840055034240d00b000c840365171001e0881e003c640c02c0908000f414041c0302001a08088100b1503400490b4a0b4010300081440700e541c0840c0240e550354441d00c00b942c00c0d00282004640074481400c441e03000f44031060b0172145501c80c00f0740710f051003440c1c981c8910807440f80c00d100604030130701030b41103449000700c51006002451f010081c1c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 423902257 1250 423901007 423901019
    0x4080d020a02100b0a030b010608061f03020c070906140f2b06051026010b0a0914130b01120501140406020304061419020d06150e100e150a030213 64
    0xf240e460f03084104543c14280110304074100307020041c00b1640c101d11004c0207646010010344002401519017504218000403400118400390300b0b00d42a031401f540c2c0181c0e50200da00061b4201415500411486820300030108034822b881100c80b582d00340101c52005000d400500051541c40c0c1000e0020303410040c3d6040b50030401046800500c1084c041c940610003940d40c10f0041480a100d4000c892881401c80d25000c0c2c0900f400e48418000c034040800051040180d000103070410003294400c501a0341c03500b8801c0c03004080440ca03260064444c0e10240e0145a040e611000c10a205000f5407650710303c1c2c0004001417281c2504001e0030038078041030b00400d508050911002960003202d09030380e2070742003005844408181c400c6151058806002094112100300d0159001c1d501c101e208040c000d80b21980403074102001414200c00c000103403903040600710280280030800401c001001c0c00c2c07042c1c3e444102c110ba215264034400c0c1c0b032a00018165504000c0e40c094009000b008580c4040104295020540f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 423903507 1250 423902257 423902263
    0x50703050d091203080c03060301020c0703080a02160b0703110709020403060b0f10080f09010b0901080303101e05090a021c050603010b030f0c0f0109050306070e091003120804080d020a02 82
    0x900807540d81d450340d40689548280c440702c007840b00700400059840c400900b040701000e02654106070b0040000d4508030140509520300b0f14603800994080d140007a03000350480c0c041204a03130001d5400d140782000c501e00601c2071602e025201010f801d0000403452100002000e002280103440240411502c0ea5140c1c00c0500007084200c4280f40640f1030f0011100c4149451282042c40801c030b43d886000c50380d42d0180b0380e103e01e27001615094896499101d1040c1954682a18070b0181000400446d100c0c41e20b4a490707007410106a125100b5240300d0b860f488000c010f409996800e40e58141c0d0300c0c00180c0c03185c4181a000b80318040c081101005511900300038485503420441c01800c00310000c2c030420282d101050344138a01000031800035800700d05c0202150402141070380d0380d400141403088485a60340c01207401c0280031907540c4001210710f001c400082c80d1200b0556005590600c403080d5050666460302c09103c0c0d0f02ea03441061004460004003000500022280c071809540400d40d210440c240d0081d607 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 423904757 1250 423903507 423903523
    0x40b0a08090705090906070309082a0105060a03080717040902032d0c0711121903030c080408030703050a0605040c0504030c09090f021e0901032003011b0f090305070305 74
    0xc0790180d00000a6580b400e4410180616143c0001d4403194a468109500601d4134040845654205009074603c03079202211807081e1010780b01070342c0c00d40c10b2448181030071900c0044c11140f01d0b030070400c4c0900120341c00505403040950700038088145684040700320350071405140c1c040c0b4000c500010030420a124888059400c0e55054034404010303e07035a40c8546082c00d0121003001d250842031143c90701052034400035480301c1074040c2c58200641042c20303039681084000f0030801035046030300c5802820107505200d460495502c1d40303010b007020700b1f00d603407052503074400a8020310406031100c022034142d114581c441001400020400c00c0004121000a80107400c01c1c401a6480030b01480e0001e00d0b28242e001e0610010790100c10b69407000e0040d404c0040c04401112400c540032101c0d0550026901d07141c420038043c60207181c40850702d0701d1002c0d07a00d5441c0c1030f0212080c0031342d060103907140c80d4503544486440303145141e0405007420307982ca171f20803940300703e4503400036005100703040c400401d001010400700d0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 423906007 1250 423904757 423904771
    0x23040305060a0b1518060406080405060a060303020a020f27101202060a140417070f0603020c060406200304080a030615020304050904020a080d0206090c03010b011b08040b0a08 77
    0x803200d0362800c03804411507603c03491083d000768081c1c510a10511105008103907513060304246a441c0c03151100480c40355045a0004000720301c01070140003d100e000c0004944c4400040c0d07003404803909541d002500c810400b00001d01600211446501b642d450011150061854240307060615081d001080f0350340b01c095a1f0300300b0059070740700082010740686540309180c68020344503c0c07400a000c8411030712900c50140c0e5415102081c8001f0810600f2800c4043c0c992220300e0007440030700e040c4421404408060341c818014544100308000d0758400100302c50358015004480010f000f1030310742d45080c88404c0b10b19844011035002040008209400b8041e00080a036a50b04001140c1c850509103640b10071455034201681c4140070800c0703280b500c40ca10a90152010304040d04003a650701b042860000741204010242e0403c0302002680c020401100300c907807a00b20002c2c04250501d80020307007400d5081c540c00c1113072003000d0701c03041c01e000e40c603070440f001040310040d180d69a0580c5040180840801d6800c6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 423907257 1250 423906007 423906013
    0x18020904111e0109030b04060b0d03020a0203010c030203040f060c03180606140a0b1e040f031a060609180402030c06040e010305070f0b1207020c0a0f1a070f1223040305 74
    0x115030030005040b600704100c0103071500e054843c00c5840e4561049002801182c100d5291306104005403640101000311700d1180e0028251070386603104040c291140e10000034201481801000089956841c0030201d02d078114030300013165800340c0400c402070020b032040740d07000921000c4a141000140da01036812200220b000581186221040052503045480381c512220000d004100c80b03030404006c1c00540344180101c2501e4190784943c100c00f084e403154400d03200500f03021004540b6004074004c1d00ea0102c01124041d00d4000c880c0300156200c0700b4205408800101140050110345003001484850310006110369141d9546d40d04504001c2e809020480c2c1c1d501664500103400810180881c0590301039074921420301242d442c040d1306840004010608501c03c140004a054031240040030207800c00f52450070318a81031145101d10341c04a003403181d0402c00104210404202500c42c1004440c1c0d1103e1181000c07810510201d502c940800d8400c0307034030b44510004036600526000100300f145d2141e015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 423908507 1250 423907257 423907279
    0x604121b030215032e061107030c06030e0309041103040201021002030403020303040605190906051f0b0a0309030c050601091a0103020a021c0203070501050a09140714041802090411 79
    0x80608164035200094205985500041e44004800b0103594000020b507280796141400703415134102c50664000f001d010082c180b106128040c0d010b40303101c42003c031203002001881c1c915a100c031601e01c20340c81603008041d51051400c0d0120400e1088039100000180203002c04200b002d1014529802510102e001d8402d188031200e205411340256885103070103801950541c3c1da20744800b00942001405c2c3e4451481000b50252201c1c25481190b24080c09150001802c0c41d100071180d0302c0081840311b4800c02040c0c4030003006603802e440700b01e5002004600e40485c1101240c40d050f54918038001004015004805c00499480c5480e03200d40500301114a0f41040c80c000344c03005508a114111140f00140c003c0105051083c6034040b0244200ca01d520442c0e10300906521982c0c01c44c4d40990321000980c1d203c081d0141800350006444941c2c0410101030b04a1070b25041c1d40c1c5008071a281c6c4030500950300c5800012503080343e800303010340881d00544490002d1911f803800c10398144280e91818419185c0c0b0b00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 423909757 1250 423908507 423908543
    0x512010606170f011211040914190f14011503060f0b0402040e0708181e070512100b031c17010f060903080304080405040c200610060c06060302060412 66
    0x303955801400f42841c100242e90030080c102c009403918040c1a80e180720000c0d400802c1d5141da120301e2001500500d1007408400c0fa5010043c1404981c0310600c007043c130400c24107408101d030242042c0043d82d2010903440c101e007442a025000d1b0840f50205001290304400003c04e2085c0343e08541201c42d00d05108100e01c4a94408210403405103000d003a09240000c000510010301a03044260410724100940c080005e0017000107150420441d2010340d40c10312120600c04400301000048041c000c102c03902815032090f4148607590b141000c4402600c9034485400d85203940f824001d10000c9100380303092100c00b40941001500344140c40804c08101d1119200008509801041c2c14007610810355660260624645904610350000f801c10340c0d1580c802c000c001a83e075071364450001548482c1d203500684506452480240310441c40d440c10300703a04502c4c2044074504120f46c3d6681620210b0400300c05026845c204000100b0311a0002904088005000310b544a010b4248480d040e00c16214240d625007840 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 423911007 1250 423909757 423909797
    0xc060506090c07140c0406090c03110901020a03080c070b010608060f0f0906013c02151b031f0609050f010c050615030f07030308040209150a09050a02040512010606 72
    0x25803403102c8442c144000800550200071610611966034101ca48100340350001500300e50307040d4010000160fa950000c501e10b60140070f0015107400d0152200d041c5020708e03001039128003400c40300034100049140026202031810342031300d500c0368210407c0322056071030300d0f00a46524415901075100d18a410b0501c17400b1f02d03082143c007800c0200903028a940d40c948000669406a001c4400c0c1074006114a40704546414010380100f9891901c4d03603d1400060110040c1c01c10780f500825241403025081001980d40b0f1202842c003042d00700d4a5510356a983e0038964800f60401d5400840004071044000591a0781c030a01c1c150aa9000f1224845040600c40040d58403080341030000305141c1080000800880c2c1034103441c03000740006070954070000304400700c46084c5012074004134081b0b140c0d101030000b9400c180e074266a11a03108000003da40424a0016030001218030a07841c1103900c40300090a02c00301a01554014503001d09225460000898014042d01c540c2c00b510300010440075004001d28015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 423912257 1250 423911007 423911011
    0x402121605041409120903010e1002030a0c1b0807031101020a0306051c031407050102090a120303180203060609070201061205060412030510090b04020403170304050c09192007030c06050609 83
    0x13001070844160b45d0851203641e400c07224507103515558035000e1490304242844000c6265680100c0180d40c3c2c940348180b403040340c01240003001041800c08e1080e9440c1c0003044c080032500d40010b107090f00d980491400b1903200c00c40100b0303410194004642540107582540003a003d5480441e201e0000b40b004524070072580e900054060002482d036000c0040e080c20301300003000028013807000946001c3c104c00c041410b480f441d6000c200c800d880e6458410506901d84156074810400000c4c14070001d20075000a59074260191600d4880c0c000c00011400441c001d50048005002c0103a41c0307043d64000f403c115848170340840d802c0d9009028060188102407091081906c2401c562110844050500076030200030829402029046503007040b0100105204041d4908101102c5103103a69914161400720f084c224181e48072030080c8000b100b03115004480d4081c00002341c14004001a5a2004405220620b40c88085a50000900207400824503034415005110240079403002d014545a41741804a0740100b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 423913507 1250 423912257 423912271
    0x20a110303070f081503010213090c0201020f03071805041a01030b0a030b01030f0f0812061215180a0c03141603050705040c110d050c010609051e04021216050414 71
    0x22680c0000c3c0f034207000c4c2c4030746600500220700500c0c6404c90f45001c2030032640102c4000000b28006001004155510300403d00c0d00282da00c000d605090101c0b0303522a0600000d4442b03014000300614905224070f01d1480400100310040051040c01c881009140f031851402226a0000342042c481034a1420044105021a54410020b5910740e03e19202d07280007458126003103e80d20740601c8590f011800e42005826000103410401300d05051910030001d11a5414203120850b8104841141e0360400d0640f80951025001040f8052a445048801d0520303400c03e42c010400440e035017011003032100340f110315211441040d0864104c66642e40a449010241d40300040065004000c240942c0c1482d4005000d420107504000c20611b4592500781c5c10300540440b084000f813000f05510018410034040c045c001d2048140070130030303030a0054100d604070f4022021880c0081094021070119192803004900b460f020718140c440c400e610541480d15490544115845182051002c0a240f013a013648a405030f01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 423914757 1250 423913507 423913517
    0x11040305031b031c0c0e04050f010b1c050a0c08090601120303320a0507030c0507170903060106231c0c020c0310060806130f0f061e020a11030307 64
    0x12580712010010459210601e050b03000504c0035100d205006400e44850103109078000c110580315120042414020401103442203041505120712602240003041c1540c40312060740340d43c0c8008032421700310348511400062005240c901000100001a0702106110106507909001034444c0b400f45a500c1c0400e00a2101b0100090342c200e0000740640c2c03094403444800010840c1e02059001c10304103003244c44c20410492114071040040300c8203540705055101c0c0940c2010400b818800d80000e0150280141c0282620b141d00b0040c50150350038400d4429845005007200c03250744c0c503000000c240b00c400c0b505402808104500280e0075a4031207040e15034542d4024040700100e02c0d01485000504000144070302035015002204010f620140441c1c240b203e5421004240325181030300c0303030b840c1000c000c0c06005c1c00c03420166103070700248111142c4120725410515404020365a8100b0b0001080081180c4d0300c0e0802740d207400f030610b41d00da4020380200c141c10385820703806400001002752a840215100701c0011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 423916007 1250 423914757 423914767
    0x3120615090a180609052a030112020105030907031e12020d12020922020901120c05030606030403110106060c031b0b18010609050a020714030f1e0d06090204091104030503 75
    0x1143c0c402c19080c0380380340f16a0200300c950ba206101d0b4116181500c224040140c41c4d01c1059400782e02034044842040340f07915a5140d90b01d403001c070340d41103d00082c0007410003900102085008104001200c040c5030042c0d280543c00000000194811062140c1103412040b010100f80d0120f00114404040070400d03103524a4086e40002d52070000d600400030b59a20021a20211441c490165003c0311504880c48005951300c0311030300094030020034040704180607400e1924190506034048142c80d0006070645285480b03842c0c905d03080d038400c48515600090796190a5002030060350010b000c2200c18001d80346c00d20003903011084408604210007000d040a4582400700305944411242000100d6655000084150300d441440342940c1054520602594011076240e0a00140d0045002e20710503504c005c514000c00c800e1054a94010783c003c020001c1640c07501d4003c500f002c03004a0b00f100c5000030b004c00034030b43c54142c18402900903004500314145481000c0e40d860044004640607660000002c2d4204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 423917257 1250 423916007 423916019
    0x90b18090604140f0c120a0b0903090a05240a090317070b0f09060105061b070e01210302060c07021c0b011502070605040b030c1b011e090210030903050c03120615090a 73
    0x1c040785d40d0b1b41c1c8552095a00c00f0010405000102340106010303005155240850401c114000c1204c1d04031622580d024403d0700403207440d05403038070034960b0103503140740e1103010112090b0b0349031140ba8409010362060906503601010000300030103816219001e2903042d034a85413000c100c0d0307240844205070294002801408540340080c00380400c464810480301030056a900c880307051603c079174400e2007000310240042c040081e01e8441c094515034022a0f0912400003030310025503900028002005684000410380190744400c00c58503e65450455000d8881d900c51070201020b50007485469a10104540c030780d04150310214001d812504a40d0341c140c2418280090440203500181031080400b108001d5020300f0400c00e0083d00b1101f04520002481c1c04081300308060846c00d4041e01c8507400c0c544020000143d54440d400c40401d80e180c500007481003c00e19042d1114800c49608101610001c01c80c1e2002c0348104004034400c5409690140d41416108c040031250f0003103903541c561011b4244024003d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 423918507 1250 423917257 423917269
    0xe130b060f0604090c0c1101030b01020a11040f1109090906091510150210051501090b031b0d0f18030f08070309120f0e0a0f090b18090604140f0c 64
    0x7103000040009281c0b60f0b503542c01c4012989000078200200f40642d03a4201440003403404017003c10800c0c02d09110140162000079140d002c01000100f584c080c0f41b9002d034030394075590300c0044060515481080b540c1c2a05840700400e810802e01c0501c11803007400010500c00b40400d049005502401c001e03c0c80c0b0501341134a00d18404010402e24400408000010700004103500369001e1a00c640c0180640c3e0801c0603801050f10340040030107040c0c84180c0b802000a07607122401c0c104807007a03150050b460361a550b035855a805403180400712001c1001c1540e0707414021542c4110f0584c2c8115208204d1b0780781d0340f41450100c002800b00900415031084003a18041c4c00b420400f03074403541602e000034101070b550381d0f0000400b460801c45800074248842c1100869040184080036800417611058545d00c0c0c0218040c00388030701e001e601d02090301c4000415264455104c000100303255401116a946000e500581d0ba0380000c4071700f52903022250708000f004100114417035030260441c02c05424609014030902030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 423919757 1250 423918507 423918529
    0x1080a0902030c0910050310020a02030a034a06010302090606030912030403030203070801060503090a06021305040203090c010e01110706200102030405100b01030612020d08090607050303010e130b06 87
    0x10b0580620304a00d28141d0300c00f10400e01c104c0c3c0400b00c1755032184c10107040c03610b058881c0007181c0003d8810032640103483c3d0000240d440361000741c42d01162444003402081c2c0e08000b54030203094000300e10803003031010381b5451550106240310030314483d00007071000ca901c40d90380768288070294100f40c5100100e2901c1c05c01e0030041d940215140c00310346200c58100840310a9a03c1220b05800096010090090280e030042006004021a01d003450450426401c0035480d00414180100515400100703d08294244401c980c01020020421903c9180400a0a40700c0c00240b1819000035004401c64940b50700484060240e4000303d4001c0020724141074017502c00341c40b0100b00700c00d60503c819241c440d01d9024002180b103544174101070402c50b10700d54507140a039005110031034185070a04c50244400c17090307080d4010709140c04469a04d041036890030204c0d25171241d0600d0036081440081c400081c000c0c000003c0d812070740c4190850341d603075540280c044940340260304020000100b10011a469150600d449a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 423920863 1106 423919757 423919759
    0x30210230f0403030b030d03022203030801030609050c0d0f05010b0303040b0f091f09031b05060405040911100207050a080d083403050f1501080a0902 66
    0x40c00950040ca0042010900d10001e401e02d4820341242e140d950016099440c0d00f503d84800030f02a5120483e15415114002c2c9403142e00d509490701032080b2070300741d0341d055043c0e42943d0306c034005810390368420f03a018404e450702c01c4140e07580c854410405a00c504d07204900140d0910301313903003900c0035032692520981051008021150700401203810f450810f054603540c501102c00002e80c0c040400a440450481609074950724541200303001064038060501c80400000300403400b0044003180c007503d9040513040c0001c02c00c9007441c7c1c004840d0b2a2042100b242c0b003d05079008600d08100b110000001a44400c0003013005040c840038080141500b0301c050a00008074000c050000c00e009415038800c00c80d903140c00c1d020001400c68903041000180321418a1500c892002006803105442e00b10700f0800743c001080c0740681d07413480590741c0c03141a122031141e41e9030703842610000c0c840c0910176 = true := by decide +kernel

theorem cover : BRFrame.Cov 423741007 423920863 := by
  have h0 := BRFrame.cov_init 423741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 423741007 ≤ n) (h2 : n < 423920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
