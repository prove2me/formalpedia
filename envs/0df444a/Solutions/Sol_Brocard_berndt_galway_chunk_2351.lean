-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2351
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:26:51.470067+00:00
-- url     : https://prove2.me/submissions/a09fd43e-ab72-4ea7-95e1-eed31381529b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 422661870 ≤ n < 422841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 422663120 1250 422661870 422661881
    0x9060e010c020607060b09010f06050a030911041a12030403330f0516020c2d030102030c030709080d170c04090507020a110409030c0b1e0405160e19 65
    0x450600544503041c000680e034000003804118031038080030946402d12170600c400c90f00d040e0003074011301c01c5040040c07000030381c00000e4074002c4041c1d24011030f20707500703a0034884101404090b04640050608000c00300c00d0740e0154401c10700c12030a40b030300e000f0824031004c075039102c1c000d500000b0505940e080c00030303ca102c603c0c0382046081e204d03400e8030500f550700c40602d1800c0342c2000c542080040c4e19a000c0112114050440740c1d207030021070003e00501c0103100e00045002017140040008490181c0c0d450f0000f0740240d10b041020440a4001c41d664141455106ca29070400c80b1f1450010744503980101d050a404035400503d1012134940000d5244209180c0451003070040900324903840a220018090841c3e01600313020710141e40291000c16550b0070603408445060310101c0c012414410200002a4003010303003000940c00002e0401503840710318407141454080ca50102c100e04904e02840140180491880d200c0c2c0040b641e03516410381d4861804905c004120b0b00d200c00c10040300c810555100558001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 422664370 1250 422663120 422663147
    0x5060a090e122a0643020f0706021b060f07080c030712050a0801061b0f080c07180e0c010c060209030703120f02010b03030f0702060c1f05040302100902010906 70
    0x501c038181c00e000c1190f80c01c1d885100700f41c00b19502003424403917134403807811141620b0000071085482e48202000344000c41610701040113140d1000d920385a992a00c00d01c24810701517000c0050b11170450b5904802950f501c14031145850368840c1c2454615240752400440d074400e0020618103040c01007544403d22a5004000840d0050004004060025180401d124a44001070710b0b001d071210b20b2134400401c040e0050f080501800048003401a4024203180c80455882e070013001031079203159515101c1114003507070b8400c1d00c040c49408030100d02d000307404bc1e15a603c19500794003040704212007000550766445640f0305901040c00c01004a0101c0d100b50010418601c2c080c00f1600303081c1d540d44d5240751f40701c401811040041e42107902c5000f030319030a000d602c280b984100d00035803c01000035040c0c8003a00ca1510700a12894000880000e0b03401d00b4010b485115809a07035401601e20271221500280c80700f190308500500442074002c450101e0fa01c5000031598040c0c1d11010300508184040c1d540c0000d4000303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 422665620 1250 422664370 422664397
    0x6070f05060a140a09020108150102070306151a0a0819021605010f0e07050f01080709080a0f02040b01021501140117090d0801051203030c03190c0305060a090e12 71
    0x44460104004115050003640740c214001280c1d1044600300904030303405051043c0070f90800c000500940c2c1e101d14095040951100800e00c100580001030b80b5001d09603100409050820940e04005007145007000c1c00c650009441884018210801d84281e100b20307c20f035800724040f4004030b00846100c1c1410300c8102b4880d07030010300c1d180710060103905030100881c04582e940c1d1a0080800c2038a81405a80f5011030500f0040201904060015030428500780d0081c0c1004014800160450b02c140d4450300180183d00c1134070200000742c10100f49050b02e03c801031f8000ca08010111100754800507103142c280e03901c402151496401d01403414402c1c080300e1521030401c445e1611541050712000c0829003d041c90800800d0701c0d0707806000280040300141d0201c0d108444ca50380d07401c9080c40100490f540503c000c1c2444d5603a95403140007080c0c0e407281240c1410024a04005103800326059070040d4001e0b04110303401104140e540b48460141d0b1240300702c801050300248a00189188180d000d45190030440e42c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 422666870 1250 422665620 422665643
    0xe010b0a02120901110f160f06080a050601020c09040b090d050307050313030306051e19060206070e0d14030a120b01171b130314010b01080f1008060c13140d020607 72
    0x1071400d107011001664103401f034002140071050a8283c84014000b441401c070300c0d030b542502e00000600400c0e0700038205150961508002011688240810728401c2402442c8007910300b41410100450740e0129440720b203d02c038510b2825242800390060b00e100b40c54640da803c0c51941d881d0f41c40e07201e40ca103441e421010300da107a02000c03449984002c03800002c0c1449210841c80d0001c6082004283d901d181d174a040d41d07075442c6105001c441d41c00b00d100c41d07000c455828110b5039401c0010119100d9a20088050101820b00841495480c030200007014240850765a2010403c52000400101c4210707402d045c0c0400d68403480d003001c0496030480141e1000408a0311112240b00d400701c0642a841410600c2000140400030700030403201e617a850040361500c00003004001c15010001c1c16880c4090702c2c443c4014001c80020746600401006100a48400400e456545c108011004803036004222100c521920415000c01d10f60b130400103d4050103001040468408440d400744140c40e0710103801500d080c50000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 422668120 1250 422666870 422666897
    0x150904020f1f0c05071401050405150c030a0e1002070608070c110604060903051c1709030702030d020601170a080f0f0c0a08190305100501120212010801060e010b0a02120901 76
    0x400c140d0805010b9074039803030950100361605074104803464000d0301d000f82d18a141d001c3e890b40d00000340c80030f559090721000031403051403191002c680155600701d000c40c800041e00c000600d078010401c0318010401e960220500300404002d0361038180c0c50145a00003501d8030001342000d80700b01118010746005101e80602d208071003000c10203651054000f5404108076420400400004100c410040440e0501600011407a194000d02c000001c54174118030325030101c08518031034014002c80705801d50040450303010744482500a910381a09206076007004240a08010003a80c011030316030b450308e03800060705241282600403600c494010900003a50444240b018980f003140801c000d458060050302219112440303010301501940750038034440c08150a200c10300c0302011001c100d071002c1d00c00900305186c1007a00b000580c1d00a0146103803601025039900000681104c040d40700000340c1d14003102044950381c075250b481c1d410b84550600d083c016400510f6520a000080c0050400014145000d51803003156 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 422669370 1250 422668120 422668159
    0x30a060e0903040f060801080303061017150906011b140c0613030b060a2108160605010e0705090306070e06070b0106022a100305060d0503070c030b150904020f 70
    0x1158828520b0348002810f00548000300c03d44401400c040c5800d084542c104584583c980c00041c1c000713402100703903000b442d688074040e4508018100c0b81800100e2503191140302d400c03201041030320761400341c010940441c440354030900c03240c510700c8288401d00d41d412045903030304600340035021102c10490042c1e640300c0c04681c0d20000140490f0b2000030b8845000d90450500307040708100a040c86108581009041208010320b0150200150301030503900b40303d80311030902c2d007880d1141c050700030300d4005226501010452140e100354103a4800b106c6201055a51007010740d014031a0101d60380d810380c05500000c030321610503404440f14500140c945818145030313035910000070900380c00c41e50160f00446c404400812914403005000c0c06040480020b4040f40c2010a0707404481c01e155104040d122800250580c80c0c1c041802401070b03014044a5898005080c0b0042080e000c1c0011150f80d01001d010451110b130b00c0400d1b401c88080181011240d071103d600b00301c1800c2182e8030150304003031890f1868406042 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 422670620 1250 422669370 422669399
    0xc0311120408070c1508090c0a03030807021507031401090606050919030b0705040302100825020c0d08030601081005092e080105150402040b04140a0f0801022106030d05030a06 77
    0x10b0480d17440044100700001d45408402412180741d980070000f000943c1e40c0d50010382c4200c0b50141031107000ca40712601c0032814030310298000700c0100010424041382c1070341944043e048440350b244010980c2d072181d054606442040c4a4500028000c1c40504c0452800000a48ca442120790116515a580eaa1251a418030846955020620104040040d0304110040d00c070807098900e030925143c83c003904a041d440f00304203d00c4504181400380071041a00030080400854001055040c00c070b041440c00c0394030b07513000320307440c50000c0c2081021450014010204200ba52030090110780c080d501c84821210b00d00e610740c441002e49002d2402110080d080c2c0b00250050259400041014580404e010386109030480549014a00c1000308114070340140c4c00b0b6400f035556952081295080510009040341d0701c1d40c0000828180040c000034103040c05500030001d03030141580d801030a9248180000e01043e0803035407540c041d0040c44030700103814400c0000350350000446c0400a1655100e1f003203181140b5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 422671870 1250 422670620 422670629
    0x1b030510050a0b01020f15150d0c0609080f1b13021306030b030f210c0d08010602100c050703030c1b06050906160f0e06070611030a0c0311120408070c 66
    0x1580c800c184002d0b4141409541c1c2d41040a000030011100107034000d955038045c2c48603da1a4103d51408900484104000078403644001444030081d1200e07401c000908080383d03c40c01000c03854008000900c5580440c800030710210718070103030000303103c05501080e04118001e401940b20301d515603000f000c400544050a01713900300d5000521540d003030650207030071990700024452003603101006141d19010002030180c656014550070010041500b050b0184600640b03c64200c54014810003811107503001c2c00042c100c038034a50881780b07060128a401411500e800c0c5081c00040d508101510200740a50800c81c48050145446829807000e40940c02e01003071414401c81c0e245441d0030130320075095010880581c0007580300c58140008111078802900301010f4207217490034002c0440c10f0000c00da440e00203172440180c04c003074144a541011200340b241e50b03000b10f42032401c82e4a4180d006880c24801e200d11500b0340c1440c0c0003103280042d03081d40c11800301402001160300007000c005401c00250420380c56802270 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 422673120 1250 422671870 422671903
    0xf100b0a0c050f010203060a05120c12060f100e0c0a020a0203010e0709110306030601060c080919031511220302130203011a0310030204020a02031201080d09060207121b0305 76
    0x7004a1070b09500f41007160034001d5040e07005106202150740c44042070b5007200d2048030010070310031809803d9420111414601c60b0f00141c844240107500c480131804c20f101e601c40c01f0480416558070203100d450486140200d01090700e00a000915251080000f800f01c0786180c011944142c407980e00080c01d445503540302c0710185e04201380c20021210030f4040d902c0c850205d07801d01d0b8103510700f41b00402c2d6110030501c00d0404226000d99084e06001000c42102e00801024140202e404445e0000c602079071158070040b100020440d550200100d1940300e161041c0b045010410701e03000d1030b05000c000800d80626402d00c005444240000142d030390350000c008030b009040000d44c4071b601d40945649804602c844c0c2c110303c0f032010030410104440c17220788281aa64102c80058507881c131114105d1950065070b5080313422805007000811442c1c00040ca800004a550780d4459405132900b5049845605520071584027400402700503000490224042c45540394095601505c0c60780d94482c03902d002040480c02400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 422674370 1250 422673120 422673137
    0xf0a09021c0c14060301050303070611040e0903071716060b0105160606060e0a03080a0302160210020609010c09030c141206101e03030804020906040605151306020a0503030f100b0a 79
    0x44050708664809006011070b604c80c1590b242401194503032040c060010044d0369507102d25858015500140c602a00e2004181c0d0301c146049402169641e100200a135038940145c1c101e10344180808048400c5041d4407128000d403524580d071114080c090b800c54240c103001060151031240e008500c036200c0035038040c510214200f49800000340c20104410710f03950050800e100c061001c40d13410001c030f458018484c81c005a0b51413800c0c0d13059691080d01000258081e00da556059492a40011554040e0004800030051801c03001029a140c2d003052100920040101100b000217030070450307043d05000c101400c0c45052940403041c0c0e60401c10111440c281c030f80300f42c503000c2c00201051082d5890451103404c2c440d0300030f0300b5603c0c060101c01c4000c200034807800007003002030550745030354000000414000d8030b1002545444a524040340e00f00003000101e00025200c0003c403584001400300901c3d4000003c0d51854842d18181c01d50410000c01109100307400000005081c0c0f02c1130010031081500da640c4903038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 422675620 1250 422674370 422674379
    0x70b07060614031606180f06030c0921060e0115060801210c0513060506030c040e09030301030c0b070501020c061503061e01060f0210090b040b01080102030f0a09021c0c 74
    0xb028024118a000750f101840158680e8848403800044d21414144240030115120310014440d00b5504008036440c607000d00080c800350907420196040b0078940300e1460041d116043c448058181280303500024800c541c4110118260780d00ac0042ea8000320000f1507140b480c42078401e0070034095804031000601c10070041045001c02e5246514030b030713042020070b400a44035454a004181d0b07607000306840307454801d0002076011a070358085801044050502604e9141076401c0742000e81251250002e00c1c4141000101c000c0e50100c1180e05aa074070001160841d42880e0070920650010300044440c1d6600704080e0310750320b00c100300c410312070f07585082ca034003401d0365402c145030602001400c50300c2c1d40301c180c4c070035440c0a24640700843e06403101ca24240c425288a020200c0c545018104c541d203540b0301d01181841030240c2c0302d40d00d9200f20f028005d007a1143c0d98501e01c0320708070300c0100c44e140032110901005c20305000e095001079155a0008000d9a40548011003e01801251034801c07501d060800d41c0401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 422676870 1250 422675620 422675639
    0xc030b04140609101805070e09070b0906190903050303010e1501110a02010513031b14090c045001020c0109051003061203030b01090b090f040e070b070606 68
    0x1000d40607408080c15090034492451030340d4165940051032410340311207002002c0310020001ca030ba10740d089022101d0490303a0f1040362070703c1d1209035a907020b2030081c1040490891910303401ca404000340a40450325120900c01021400c40260075001c0400c1101540000801c0003040514082c190243c100c14140c1420400c856045900c8202941800001281c0c010850000300d030103c001c03038080c00c000d641c0301e404450071001001c0e503810081014000c844c2c00844904c16420150540386141003041125041c4410014000000c41e45c00f00700400c100014004c00310000035940d074624040c200c1103402a903000d0082d64183c000701d580d080e4001c00c09255082c42d056203606101e4481c0c2070000d802611b581c034000078404000c03405082e0007003807441e0601c91854031980c0081d00404543c141e9241340820792a000300078128071007204d800110a0310700498941000310481c0c2000c00010030101c20000b41703001b4000945245401e140740d41c0106d03800018900c02c0f00c401440d440340724410001d00d042c1441e4004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 422678120 1250 422676870 422676893
    0x2040e0601030603110135010509090a05031608090a080d1805030d0305100e0106020f0f010b060a0e01210204081207030f121104270903050a1b0c030b04 67
    0x314105410140b04002140340c0141d00031501200307107813118118218042180350702d0010880c1d80d50031405161011240d18000441c14140c410413150350381940c8030703a04050743d219240c00c03005d03005400800c40031844c03000040e180c903041846020301078200481a0000766649a16034055107941d04400408064a030340040c3d4511121130302c4504000300c600300f101180e0f0710100002c280080c0b40ea5100440c4100c1c0003008460020041c00002100315130b10b984000f0b40780c014490130031a036031242c458512f02d025010301078809248000f403c000d0800b860b080044a5002c8103020142c10301510740036440510f405901d61828a88030000c01681d1945088100d82c5070101c0c46500700480142440401c0000e9884135080240805038a021100d1000c1824003000400501c00d00404000c00000d00280b2031100484410400003000440c00c901e1381842d000e08103444030b070803004000440400000500e0390242c0101496141daa0041c510103180680c0c03800d141d001d503a0010b031180717070b0640100810007501c000308 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 422679370 1250 422678120 422678131
    0x507080a080307081003080a03020d110a020f100b150313050f070f08060402030a020105301005031b131d010e0c100c12031e0501030219030b012102060d02040e 70
    0x16905d0061035a02c031a00c440c0901c4241c003042540000c0c400c010342040b904002085600200d031180e8803e01d006020f940c4002502c51080240a040505907140c50b961195074007480000d086a99003420b480301d040d225900082811503c030200c1c44045000c66410040c00b5245403108009154083c14020499282c81c4140e01a80b800c5d4801010840161008224544120b50a0030150f80b1100840120920a900b014158a04140d20300071010160040105c10380103234001c0e0f11044a03240c9036001d054440d1030305905104240305842900d00749003048000c3c010001a018000101c4035000003c5e149410081c600101d00391703449080b20b400d030240500075904082d5044506c5084115050800303460341642c400058158482c507146260081c1c003d0b0444c0325943e41549050f100000c21441b50b0700200028082a4000c0340800e10100d03410b0559030390a003c2c0d0703030044004020740e860400c802810400c01d0101003240303443e140d591001a00c4480150002d50600c2c54096115400c00c490040e04a800811 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 422680620 1250 422679370 422679391
    0x10207140f0d1704030e151812031206040e012f040e160201060b040b07061103060312030405010603020a0b120901020910180b0d06080f010506060301120507080a08030708 75
    0x12040b110360340004850262a0b00701c004503029980303d0400340c84058840c10800c0d0414401d40c050340d1140b910200070720445102e0118180c1c040c103600148404a4203c81d000582603104014000741c00500006141c1e02c10710041c00429101c041c400d081e42581c10140d00d143d05401c1010441003440d215401800740c40030698103844c1098a401910a43c11070b01400c07402c212207403103c0740c055a40c801c0d00500050001c0b50f5a03580d4550703450000a242c0c0d407141034281d49051401c90035111000f4140102c81c0a034031b0090003000c05d00c0181320500d80c0e691002e402101e0565881e8000001a02e8030308141d80180700b20098039448a00385099400c01490041500d019a48100071520280d40d4104251030000140d14024944010690129036088c8070303a000303084160404500825802030941050064450100948111016006000d07082c2c1e14140c2d4400c3c0d01420a2005000400e030380c0007003558840c005c4c003c0301c1401d80e40e111100d0503e1740c001c109461500d0000100040c4036004103000da082000c009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 422681870 1250 422680620 422680633
    0x20c07090509032505070f17011d0705120a0c12051b01050a05071e05010f0c140717160303140f07090b03060d1a060411030907050409080c010207140f 66
    0x1d4504901094201000d4601c50344c031240380107229041080e40040c16034055064451515240c603012010f907185000c504035030070241d408069850042c1c01425041060f00141252800d1008002e003800c5805c500308158401c10340f8500c0400c011054000040034100c00e03560055049040040c10405d8001e0b540c10505c601100345540381e40d0260407245907414610381551540c94516280e9900400003c5c40c0c045008881030050038007406510a20348810160420014000d085a050340c180301c507503207200040241807001c000030034a01d00c8500c40321b15001c407055150100540054a081e00705903400e80010f40e0752070ba000c03d4101031044494011110800c412854076241d18020081465401030001101011012071425111407041c0e414103039109a40d1044c4909200c01020989001c0703900b144120b085c0241a03201291a1080301d00816120014114450410080c04003030412510100c03000c003420404100c81000038030180800c2c0307120b0850b0b040740220b2050101c1c6000c0b44003204103802d82158 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 422683120 1250 422681870 422681887
    0x26031207031404030507020f0d02041b0201061703070818030a0807110406230f0a032001031b0302070c24080606030907060e121606020d05070b0f040213020c0709050903 74
    0x5c050320b1080764110340c3c80c0d45149404001c41c00c0305001d6000250020704005801030341d030141c4200500c0240300c6a00800c0119569a901e01e8543c02c09030b400101a0400c01c03100d80420900e50091003409408440c08112031804070109281401c03424069556400c0031031040200094145402c00c045011a02403240c0d07814060b030120941031041c88040041032048140c1e1064840d10080c900d591401845074401c51b950341004c508145080002540e002071800000300035600034401c0100340e100a44607a8000701d03880100390005e43c0242e400b5180248c50070b070002841d501e070010700000520f0b00b11394103400c070b401c03000003602072040600614440c1c0d40030300c20002e000da80010340c10200d40311842c0c0080e1110b450400f2403040a51250140c60038041c0e00803521070400030b20f03681d50441e1000e900b05c43c40448011402c8070390380507404004007400a0f1201080100c481d103003166800600080544a402e2102e0001703508903031004100c6d074a80e8010404c20442030a5901c0360f241e00c500b5480182d8a4403800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 422684370 1250 422683120 422683127
    0x30f041409010b04090506030a02130b04050115080f040c0906120201080702070513020a051e0a09080a020306010e070201150e060301060b21070203070602120103020a1502072603120703140403 84
    0x141d01485c040903540d20005040c80e90100110b0b035203d60054112110007440d801303280050809804a40c1c0103d017090000502c1c1c000c0c00645080030765241d40d601e061900ca500104c0100342025205176150600940302241c101828865040141052504000c1c1594148005850408020220010754210342030400140c0c580d898580c001a9a4500042c0c0c3d9903c1400240c405000b1242661450390715a040744c0e030540e00320001040044495198109401d40d1580f005548072a6114021f40681005c0c004100810580b444c5903005062030001040595110000304050007255011845504007403041c030032031741001c1c8160000f5015107002d0b07526006041506001a01da201100208082043d000030092482401521181540100150b584400607401c0d03078160002030109034420b0700c1c003503c00201c40d41400390600c1272203100e1b00500ac81e507103806020681c1c9900e40301c0c01c0c901106840c09035000304c84d00b40020318904500c10303030706541810480b0f80181110f564201065020201c0814000400c1c0c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 422685620 1250 422684370 422684377
    0x705031306020c0a23010501080619020d1b080a0b04150b090604051509040c031e05091c020105010812090312030c0415110c0102061620030f041409010b 67
    0x81003070000d40e840e1814150103140146030700e0090302100c3d888003689200d07454040c80d0000010804000e001e280d881d156142d8481030140c030444091400e1000d0901000e2594015001c60308480c94001074100c0b480e400052702814200d100c4001039400030408c490b10706548517924040c80141d40800010851001c004e41450481c069100d17010000303d50405140d64050848002c1d10001d8054121401c5489404c03501741c0241090500c00c904000034011424428850500d80700e0509103100c0ca543c00211001004050140c921201c0717015114400c140b0300e0b04412110510103035070340001550361510480d58248003200d2100400e00720100914440313584c0015615080d0340d004880c8640d240c84480d002804c1748150f900c8200c003002581d80345400d05405c5042c00207580c448000b681c3d04104100012604c0320001c42d02c0302c0040840c82141c05c00c2c82c0c418440c14a544600907100200c500a06504606e1604102001d0804010000c0e0074014013120f001c3c10709005405072542c0c80c45504040d07401c8d60901 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 422686870 1250 422685620 422685623
    0x1103120c16061b1b06021c060b04030b0601020a03080a150306110706051e010b0c030d060b1903290f0a0305010b0307080d020d08090307020d0305030a140103020604030303052a0301050907050313 85
    0x1a000718441007588000d105101c0d031207030f003101f040025a03502c5680625940052000761340c29001da80015141e940003003841d0080d9a410f6641001c203030784d85044900244a000303c20b40600e0a40b85001c000101d9912640903805550b400480c1ca0b54401d16043c02030301d80050854060441a000103190708200b100024155901103100d1500d40a00c44a46441c60042c0c4080c80e041034186940060140c81c580300030100742e51800d406104000c110082942980c410f001017110210500c014900e1b4144c07030700700b140201d0030000c0543c04101c071210002030108a0310340003a51540d540c0d0002401c945001c00c418030081c00220007400c105a9000406500d81c46100c0041040c000c0e00300c00158200c00a104440c9403581c005c1154240c140c4c076050003800b5400031201001c0da00e2400c0344c0d0707030780000300040c40b58100c0e40d00501007441c00f819035030220f018001c00707010304220f6041c00c10445800203001c9100ca8800140f0301185459602d410b007044001c100103071105050190070400e000201280035107030312896 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 422688120 1250 422686870 422686883
    0x50403140a23100603050a0b070212070f060f0c0c110103020f0705010209040c08040507030209060a0305010c030b0906010e1f0c050a03081506030f060d1401060f050307061103120c16061b1b 83
    0x41d5542280ad07418440c43c007042911860000450b4010440e401183c4484e0b0340c0105810884d600840b840402180c0c880318500700400d501070258000116040e543c3c100205062401505004216242c0c50098104510442e840d075008101c24000d400d040c890340d10340e0512481e0942950400b40c90b0562950010300010780145441000605242c542203d0380e002168000c2c02044031030f100460003002000524903052003800188042912036204490210101078001d2000414102982e0315080c0d14610304d407041d06100080d491400811401d001c003045190003503c912a5900e4405000c091800315a104a031182400748184010900c0224100f58031007001c0e5030006d0500c090713003480e41e1215075072a0f2801b4150709000020403120010282c100455030190112401c0c40d407103690507500c10542812180441e4418400c9000410010001d9508804140301480c50180c0180d05008581074000064581030349a944040e91a241e9510362850b049151070641e010a1281c4c954000c0b4031010701015090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 422689370 1250 422688120 422688143
    0x20c0612070302040e0a0b01020705090115080603100908031e011202090901150801061e080613150c200c01020705040902131404020a080706050403140a23100603050a 73
    0x41d00d01940c111005000804a00505d034588140c1000107000c1e00c070103841c01405002c80010380c0341451662181aa0300318030448800c96050700302210505c00091801d42d1512070000419551402d62103a012040e018031041c0c2d5980c9051000c012120300720000c284060100040104400420040d1610b0159170450302813125844450344c0501414007401e142c0712501740e80c60006013000055005008a4200800b101c10700d1185c032101c0008820b25109001985c0c1102c0700140745c28030344015140041c0c2c0300d2004540e41c1030043d800c0c035085603056140000030841e40100e00f58500c0101181132641c68a2100520710041c1c00c400003521504540308503400b80351614141c00c11913588144004010041c417804210380300b0b183d003041070b460400b56403c1e8000c80c442c41c80440e40010114101d0150307112a101d6900c1c0c14a1659401d9402d00c01d080d50304142d0180300e10030303c0020041a005010a200382c5a881032454080380060304040604600d1403185141c0402000000c90104000181d250001d245009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 422690620 1250 422689370 422689381
    0x8030a051c0501080105060a05150d0b0d080a03150909050706030b0f0d21050310050108070507050f1e28060603140f10050408090d03050c12040510020c0612 69
    0x54184001045030401d42031000220303c480c8158001da100310740440e123001c04907a40d807050040d0340f0041e4040c0e0541043c1084600c150030000c0c1c001c40800316000c0d203900c2403e40305464000701c60f001001150b00007611800c02d4840000780380ca00d40c0280071800810080042981d0707405940301002d2040905058a410007201a5652200c404000b008080c00c0c180c2c8007001440e201002c0360103214071420354a001134142601c280704030240d078411008400c04454050801005490050004044e041048400c20405002403814400740070100b80960041807415280b010000424180d00c1d00c00c1050f0303000000d860480d4a03500c81c1c01c608142d100e14414801091410b0100c0038040a8101500c5004264200d004103400002c40040da03c03000720070b40f81d000300315184400a46906850280004034144050604d500d4494107003103440c4d1090603c103140c014590032150802c1d0034100b0328114480c0c086030410041c24000c5160380a50000c0c0f01174a1450407400000390640503a100048020f5400f000051 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 422691870 1250 422690620 422690647
    0x81e0a150216050f07140d0303110f0d05160519050705071208031e06061803010605040e1e0f070b07060e070b2206020309010516320708030a05 63
    0xc0c2015204021400b400c480c5080050380c0c0c1d010903c1e02c102c1c03803050400018080d0742e540b54401008a006042c4c0d07105190350788084010700b045030400d0700129001c114128044e45088020701c441c401569022615281984807400f005141a4484052140c00c02c088040202e0407030040300008414208280c641e6401e0412502d009555040001d08802c24103c1609100b012030141d485070340c003420021043c800400f600a0001d8044d1545c94001200384040c04c14500c0c40300c4c0c0c03040007007005000002c1d0075a8a07000141694000d00c0701140315082004083d50120802d600401407030216801408041041c8580503a580b44038480c0169034280400c08404001c030300d4100d40014029031040b1902c4030f0b180c181e488410340c00391041d45072042c40606e00000c41800283c11404995654018608280000d001910254000d000c41010601c528868200090300d486039000e0032040000b611011035042800200066544440400e0662100400300719050b4000201c907810b082c246405600c0d4110a403c24 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 422693120 1250 422691870 422691877
    0x70f0e030304030813060f0203090f040f06091a010e100f1403010806071b0b010501030b0604050307080318031b101b1109070e090402060f070f0804081e0a1502 70
    0x4a0341400002400000e014a030f5014200012050041d9408140d9901c1c0681e50581d040000c02c0c0542c009000c18901450f0104110001d081c0c09000415685010307222038040b110541c00a41e806036540e0940d071501420012a400068400e080c00e007041c0e0405000104280c0d40007192804000c00b00c0c100000491043c81a20100c5010401050320303543c40b01384039610f80004607100c000280c800c0d0088000e0b42c2c0c0c1c0c0e041c40c2a04581010b1007407601e90174400110040d0056200ca5900701c0c02c02c00002856442c00c0081c0c00c000c20300b11001c1d5031a03030400b2916881d80e01400c01e01c0c038400d91200001c0341000c5504190946655011141190100842541580c1c201401034090000c00c10030743c0200140911210f03291001142200d8200d920ba5500c5416201c0c1122140c0713403034100454100080060414000500e9001004480c03d802c0600750f40d40c2c400d40100c2100121007180380442c04020251003003001c500c000c0344000c041c00140301c3d109401e96480003000c602500039071901c11174034910b02c200d41c101c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 422694370 1250 422693120 422693147
    0x20f030307090608060105030c09092806140603010b250b0f0a050a0c0f1b0b07051305030a081603140307021b041b0c110a1401020c01020607020303070f 67
    0xa4940300d01d4001e102805098280c481c281c049210078002070400d61084040300e105040e80c0b194242802042000d02c9005440103100c400c64440c4015078054540500b4803074560aa9807060120714a03080011405642600741e00070f6004020a00041c45502c21034820b981c251942a003050161504070420f100d1f0401c0032500240c5611007203000d114261310010400b41c850942c241040c0b03e552503d02010046561651050740010703605026400e0480c404e40601081d041d600410018180c03c0f074031080003140d001d58614001c6080007505442114860b00000003c0c103048003c0c081d44080342c0c03101c1100307100c2c1c88000f544011940000030f082600a482c03000700207207281c10300b90302d902d00703484043d40e01d05c103d4041d88502107444001c00418905806200208540403452075031124075010300f0340388805010001c136407542c0ea580c10785078582c44001c8008020070f1402c00c162440071602001904101071800c801e4110740181c3d01b003202d09900041142c0c0c000c0310900e03082c004148245022103000c2da0a164 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 422695620 1250 422694370 422694373
    0xc030a09080a03050601020f0f071401020f010c08012103210219020102030603010b0d0c0302100908011b03110a32030c0306090610090b0a030204080109140c011d04020307020f 77
    0x10002011a032541c0005d1280d4000c2c0c003205c6003c0d2000c10865a100603440c5039550a40c450001800040c40e00080c981042c4011300482d6082c0c13502000107401d64581003130080018490b0001000506080010250000b04d6164190f03105200d6841c000d102482000c190101c9072051940300a400e007440d411680c072540345000c84600007007416002800b0f584241c401d0b6200c0c0d82011070f4685549072001c805003402d548007901c1450b007491036080c440c588850340310500921440400000c3c03101400c1c0607a64010143d28980c4540003a8014040c080b145040845044e200007400040c6195400447c0c008128a4841014007503c005551003820400200101080082d006c0180701070380b10918003540c0218401c884480c07485c3da4010920010340c40100502c00090b6106108020300020074004041002c464980545883c2d1a941c1c02802d4580c0040202c40c1801200703aa000d500e4000e202c07101e42c202c002d1070149a006e1615403460203201a00c008207104550000108074524001c01004454010400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 422696870 1250 422695620 422695627
    0xf050a031a130f051602150603070e0f070212030c18031207150c020607140304030c0f141203010b221a030405010e120414010c02040e010e010b03030406080c030a0908 73
    0x4030101070000d003c0980c50346802c18020504015100303150100041d41c990050038558a4010214401c243c0070b060180c0500031080045280c59404840300d10810380400300b0070260406040081c0f60071190041d0314201941402800240301c203e0040711040350110125203d51a1220b0002c2d04089050708454858540095824104209500c3e000b96a80150800f00401c0d014440d00b40d88a02040b2445c500156001a03162681030740342014680250180c58010500340300d07982e4603006491105020313542490070110414410004004d08060030310300b244000e0840d403408a48101c4ce00512041e418a8418050040fa9504a2003040301c01400c10038803090800c0340481c0702c950654801c0c1c509030717001d50070b00003956800d2200140c69608000100845171405103409a43e02072008240e4465040001544081001d80e60741c0c0140c0d4400301014000080c00084201c4440c01c4983d5081c60038040e4009010030041c41d500a0b149592050a030b206440da60383d05d0a0300d13a0003c2003825002440c03900d012 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 422698120 1250 422696870 422696899
    0x7120b0402040e19061a030634270b1914030412081506031602032802070e090307030e010c060f020d11070f080c0a08030a0e07060f050a031a 62
    0x54194131102030180030700f0020402d50594240350010480f200c0754055000c1004910b41c003a00b141c1c0b00325a05407000e4420806051115007148840348601c4400c000f403510502c40780911110780400422403000986164198940700c0840103e0154184c0454522114609840002d015031900c110703180740e0028580c0d480c60646000681f2114400d0a840010160f00014a02220b007091a800c1c0c110000d00c9981103030b0340c1e182c00c80c2d44802410300384000c5003c00d01c09060340b103160f0154917020300385084604600d0518524020300d001c5440e44420000e51112050107204030003c011a4440c80e0182340c0104000150030040c3c03003448111034010030843c900501003070f11403440d50290070301112144080c0402420803038082d481d07015014000c1c14075840d00f2031207000103400d4802020f44020f2081030744c0546c00345454580940e0006c84080c6110f0f91180c40701100b040c0c003801520050001420840702c11000309500074014028421981c1c10305a42e01a0030002800d000c61403500d69000600605030510302 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 422699370 1250 422698120 422698153
    0x1306051801051006110f07050607060209040903030515040b0618040e1002120708150d05011d06010807050d030207090e0c0a1512020a21060b0301060507050c010207120b0402040e 78
    0x141300300d20014040c945c2c941c0c04451302090030b440d41c0c0b0f280d500408006042a040100a503c9008200c1d0041c0d420480700d03246d91914024003440d00d0103038400148616041c500660f10705c2007000e00a10451603d40b80f449681c0d0f510040d1060194444198200e040c96100858010100c18107105028814580c50b0100400c0039002004012800107609203903494008042d940700c1300a5410240100a10800d10a141840f44d07018100b81e0040c400401c6800e01e00c050914404020920b00700650040343c0140f09031041041312000405082c0c4070213100001c03c0c3c90081d190002c0e402443c50030b41c0ca80c91190a400410080d6100c2c44900504c426002550380e41080110410b5a20100201d20306904081c1c0c01c910900c256015182240c480081000742e088038101c0c0780081541038801c1c07942d00c3c2000f1400ca4000005940a80480d80347d15583c2d0355075080186c54018450b54a5045500c08142441001c0c0c5c0e5a000440c119842048107038192194800140608032400101c0382d0ba100345540c00d00c90004d07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 422700620 1250 422699370 422699401
    0x409050c280801030f032c040b030c090115091a04060e010e01051e0c010615080c160b070e03010c03060f1d0105010f18030309030218130605180105 65
    0x1c00c09844503401c0d0780c622040385a06140c0c16500410310307030340042020609013050041840c1c842d240040050041504c58100700c0d04440f46035007108031a4500e0440e50625200340098070200701c00402c00100d4480010314603910500034607080071000c6c10032008080c098200c24004e0b000e20004541046407604050080d80c00034401d1500240300521200404d50042c115441400c0060351072324a030841e680c102c03d0011041e40b00442c003004003007007a0f04400e072003807060340090f0100100600c040c841030440104440f0300500541d50b921401c11400f51450200c0142101a99100d41e280c03002d41e030342800607078114000c028031942650800003c04506a4160303c80c10a443c07021300300d02c05454450030000601a51040341c450b44440381e0300181f119600403618003811960314540349203030458400000c1c50801c941e60046001c2007804100b8030031440c0510610f0524a14800d41e16258503083c480040c0505400c0e9004d00210b50b20404540c0e904101100700400d035038000003d000a05209044485545 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 422701870 1250 422700620 422700637
    0x240c120513122d08131401020f0709050a02040b030907060305090111070209040503130f1404180f060204080304061d1903031823010311090a0311060409050c 69
    0xd08502040c6200c10621080025400144102d2000b100b1800440c40444451a084902c6643d0020000046440c0000e162011103a2082000f84d841c3c800c4078510456520182410348d04054070307010722000009400822100058008609500c81503800b60003031183c0d03000148030713607000010000e20702000a007400403951a1303981044540d50f801e401da803c07219203880e9010203d40801111000d440c01c85000703a0414001d40640380f804281f03200c55684181d155000b03a400c285100c030304111000902d03603841c280c00d909031420b0081c03d44070110000302042078000100f01815052226061107142d50544000e44604c038112a601d944a070310242c903e0100c005210341e4415400f07200b0205040400d0b190309448018520700c1c48844c1140e40c25903400031400d82688901c3c158070400200300c0341e4540e080398210f100401030b810005282000506643c240301e501c480c1c0050800505c01a07480704500202201c3d0844180100064554000f512912070750340204611400e02c0113110410b10034800a05111 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 422703120 1250 422701870 422701897
    0x901080105100c0f0c080d120c0801030c0315060b1303050115030503190302271801060f0e03071d0f0a06030203030304020f060702100203041806240c1205 68
    0x1a81e03a01d00700040c10454a040d440040d041184500014000440c200e000e148100103c000c03007910b44e42d03a9840d00f01c207a070101e00010401c41240c085440e282c13250105411007403030002c91079070450325480a55041413100510300b102c0802c041080c0c4410b5400400a00b030b010b280d00c0c1d500d02d44c840c0c1c003081000c1c46020948a0354a0106060100c000c0100c0500450350702ca0003a43c140041100800c02c44410b0042a00505d6001c020510702d1307912100740b035954041c01d8404460151115000c3c486208014400c1c920f1820f507200c014480103801401507144000b41d490105400d107640408241802002c0c0d111003c98140b8aa642018410f04012980300300145c2542c030780903981d0051094150344140c40007075003581003000070174054100b10064060781400a44040d2030050503a020480d48a200300c00300c0010f82010074140010690700c080001c0f00340c3c440500307210b0380d400c005c0c814040800d6104a1070000ba1080900c01e000d9004107a550510b80d04009500740d840070101014149920980760000c02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 422704370 1250 422703120 422703137
    0x19051c0503010503120a0c0b040f03030515030618070b040f0512030a0819020705100509060a0e0c10210b0a06050406020d0c05030910050706140c030c1c020f0901 71
    0x5a00c550140c03412107000078002d0040740c980484900d01a817040c0b82c06810440800360500c04254011404da018030b1050241004100c09410010101d54015100407070f04000032000b0039481c0d900240c9540c011040b8420315203040200da000c40c1c0340031030543c0f0401e480400460001500e1132412801070031502c042d542c03180d101c1400105103841e48180014040404d1415001c81c50a0148000083d8244107183d4014a0482c99850303840c07a1205078514031803400d03100e008004004105000c43d0f03400011404080c003c24925032021925100030804141c042e0803881080c044a92081449007040c0700541d0082c0320103003e0300015405803102c0005c1900848088000164070fa2040080300e0444902d40e02802512901000031504000c0304d11050b02d4a100038403801c40c0030b0356103500c1031703565081c942c1300c10390303907620901c3c060701600d0842c006030104241c100100b0004026580031a42d001000705180303580c07800c0d4660044c09454000401404841c03011441034042e07803105004110030f84d002d03240c8955 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 422705620 1250 422704370 422704423
    0xd0614090c0303041e03020a1203020c0a05030c0d0204020702090709150c12050703030f05090a0c05040e0d1101090c030b040312050114010f020709050a05010e0912070210021905 78
    0x540e4070307042004a8250348108410030610382c05d441c088041c24488620010300696030340000345001c9213900418070180c0d003000980e080540400c40700164490581d038400c1400e1600c40080e882d081103481c3c1a0081c05000320000455076264119407442d0342c010160f1000307051603040204500304601500e4002c6040d002c1000003107000e40c107000c0603903a200f03800c0d96042a0350381007194603400250044084c96110030044030445024001c25220b100a10300a222200f20b905201000841c5940000d00031440c08410281000c008030ba080b003110b407103045c1030b003800c807420480600400e582c0e000a00582010f84e80842040500000140501d00a40e10307140f5401042c0d020740c0465400780f0444120169050650b10383e5401815101841121030050325202650b409400050328000c0303400c64895581c45005201c01c5440c090225001903400006014613800385503440554440ea0074080d20480c5d6182d00c00c680343d0f10070000050321081503240c01800009510340aa540c03800c0a102c24102d8a07072441c10503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 422706870 1250 422705620 422705623
    0xd020309030309061b09010309030c02031507030c05071110090f0303030507080c09010c110310110403030f02030c0706080c07150b0108090d120504030e060403080d1a0906130b0d061409 81
    0x28015181d00c409146001701b40c000550081c13100c400d0440c207000c4036518000160307400b4405512828031303551081740030340b0380b00d10010120b030049002001444414455107003c81d4103081c10704e100c401e05440c000003d5482620a5a80b041180d01034200600c09032400310405903d80c01080c0900e01d40e4035582465110107a480c3d180e8011703800b101740003c4c0140c41e4800070400031003100000c0600641502c110300e00403550b140582c1c40d102e00c6840d40c01d60000d003c0080540c841040c021020885c409181000031271380c0180d84030000c501c1600c0403c04504c010912a0320301e002201c03590b40e40003001c600da00000d0480100680391a83c00980401c0139100007400500c004600904445d400d0b43d078501d04210302190700c10042002500960400020110348245c60b215000104041c5004403517054a030030b0301d6005901070351a610741072507041280344510714083e103075140e5003908110b080318181a0070480140c0f21008000c0c1c42a5603901040d80b11800b000e0100c2c039407001c1e008081004c07444009540301101117 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 422708120 1250 422706870 422706901
    0x9060b0402030610080a330806190209130905100b060408190501021603110106080111032208030c13050d081b070807030602030a0c080601140f0d02030903030906 71
    0x560410310b407590340520541700ea4416503012003004c40c0002c2440c90501c1e035295280c076048400d403a028401c2c0315460000c240c1c03800319000300036a0380100900d142c02601c142c40c1661b2145114602c1b174000c40c036441aa131700d01505a04071207040e4001c015241407070034259904da0251640c1948289040750742d01c06810910100c13001e440040c1c004280d01c84085022a084174109d00041c1c60b2035509000c007a0089501e158151240344c00b0760342c0e44c2c4842000b8000c007800c460710b95002c551181e241ca508900035000c20800d407035001c2d5246010f03106802c801052500b920240000c0140300090000401c0a400c48000103444040040c4110600d4075844800b030150903180410301401d509801d200e105248449402003036a81c0b0300200984200380d90b500c030b06618142c4a900202d49058000c42000002c02003481004c0700c0384440d1800716500e04001c800030307090400842c08924070000000b491a1103d03442c0e41142c00d4a501c3d650f0031503032132600d5203009460360000c1d2a100f00b280500b1300816100310305030016 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 422709370 1250 422708120 422708131
    0x5071e090b0a05011d0d0c060503010501020f060f07080702010905010608060a060611100b1503070c02040b030a03140307031d0a030212071a07120905011b0908070b090d050d0309060b040203 83
    0x200d8400c002c1d0303001c001c00b19484204851b6442003201480a0000300304000341001424151159500c03941414000781c100800604114182e1303010400304001d214107a4101504900c05050407412521421412030247c071b40038002800c0c7e5800c1140c0021010710000d03020344030344540d0004010b1162500c4040f81d450411180791402ca80c0030108460030b2544070307070002180c100018032401c6110112500920325410031906e281c080b40d1540d0040c030940c00d180c002c040c80c15200328090050f41c015030f5000f4180728580988041d00c11400700000b084580660701c80327510600c10140d529881000d407610035a4607402c3c490210014040d240c00300c5018101001600d84a139805200d001354012000041400d06400410b0341c403c01441c665060708160f0148a2080030900a50022468540314202c100301000e0f1540c2d0082000b026031002c1010394404190603042c0d507001d1080c699112090300c0081e0048640c203401502c82e005426120310b5454055203c450a184901d006010b5194a80e00301300490004440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 422710620 1250 422709370 422709377
    0xf06090f050f1207060e04050c0f07060e010f18051e03030a1107150b030d0807050a0e151903051f030b09011e020702120105060d0b0405071e090b0a0501 67
    0xd001d10b2900b40301c510803216024007814071034000894914982030f581c0e8801c00204424003550482411b040c00392a0740509040241c902d40710040d1070b246131038440c0980180401e903423003d950140c00020741140d901031f15044001c5c4140e80c0d03090740c1804000e40d2840304030b50324402c0c40c07080d00e0189016060b103070141e200c2c000958110396605000d080a4110f503203100b40349240402c0003a00042c0d1190201001c1980c1e100c0011b2800f00c0c00741450724290403003214000307000c82e9104022500d0351000841d00c01646616100040241da5400b0074401040000c000211840206843c1142c101c00e0380c4440d400321060350b080c030080e114541a042d004501c525802c05440c880002400400e00901045420451000002443d00c01030400300c007840c0000000c80306442d400041e00015407400f8a007400d018000303440200301c1030400c0341c00106142181d410060100f00d4180000b01444402d012460040c050300380c0381000c03070b100001041c030010054095844902d1903c1c0e003013a4036043c407036140b105031a0181c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 422711870 1250 422710620 422710649
    0x1709041a030a1211070b04170c1003090c0305030304110310060e0c0304083105040b0901090e120703021005150306040b1801110304230c040c0314100f0609 68
    0x12a48240e244040000505100100d031a07180180420005c01c8018901304150a4540e82000303405407400c1c0102949a0040c1d11041c851202907803120f1001a94031800c1c1030004e00304000740b81210158009070320140060001104210500c04803000401c40b022089054412000406608804441030342c041d4080c1e4a8042e07002481c80d0401000960300075000b0381000341400c0c111109101001a84001e52600c0004100700340110312a941508004c0c1008541c18040c9580d208045100d17a001449000400c82e2681c08880e8074610600040340011003504078940d0702e017210b040c080d589171300c0943d2511a2628080c0003945600745081403011400004024200c41d440e031740c480b84010b480280a0820014550020203d000c00920031003d410740e16143d6940c0340e290500700b12180d652600b01d60010801c00c80b03100c4142c140e010071840e80b480c03c2200c00141003c9019000c4004040501e680c8010448074014003445c00d4000400004907000d284540c02d180c1c3d184c81040703030700b14202d00c142d100409042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 422713120 1250 422711870 422711873
    0x10e0f0108060c03070f121d060c040503120d09050709050f0708060303070b07020708100510060903020102070909030311121501020c18040f06020a1d0a0501050a05161709041a030a 79
    0xd10480c1521103283c41d20010714035082040030304072403145240c1021078001d41c0c1540700448e030900001c0d500000040c486800c15150401080d1690501c00c0c3c0c00c050700e000010808070030300c200c0e448007499941140c00c6982c05503c1c0c400400040c075040e1600e50074844218001070300b8911030804940b050b50b010700035504082080d5186031400350044d0060095000f00840820015010400050310800c002808203013400c11400c171156440590300030204001c0c050805002503600055030204940046800085003441400c046004203002c1e12001d2541100180008900e101074103014058a01c1100e041c4078130031030b5070040e83d0707507102d03042183c0e04510b80c900c24083c91004a001d66a1240c0250213402c41501c8075a900d00407a4007803d00c1d1000b150300207050054224404480b8015088107491442405013000d001800e035000d803004860402400088082d150600206240b1442e54041c200340c501007001100d001040d0000020240562f02d440322039496081060f090016005014001e004d024556 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 422714370 1250 422713120 422713127
    0x80c0d080414010203041e0c051017010f030f03080414030318190b01050d021302071214030405070308280305150a050d020d050312070c02270c0d090803010e0f0108060c0307 76
    0x7d2005450440d0b41400005032074849107100c1a00822560342c4816401c8001901000603e060704003c03491007482c102440012000ca42e02400b15400d4100300803195914502031090039030b01c132500030700b5010200601880c0881d130702071000a0420308050f5000001c6031400501d650f556408080e10f800c01000041055041c5800a100000c0c000781c0061089032071100c0c06800c0c0e074403400d400c81d02052000e001d011001e81c0030b030b42440d580303641c80d199600c0c606003500c8069881d001030101904100000441006504080e003110b41112000c081c10242c1d00071451003d401044222110b0100c40c1091032402401d15103c1460000c0c1e84005050889850709a02841354480300b51804940d244410400080104a251070b20340c4900a1552810014000740c41800f080202d8001c40c0700f020b151494040c074001d48140c007095400591690030548940540b954000a0300c2885005401d03101e002001086d05016511312510422941d2515001c990340e5004841e9110f804617140442d1080c01d1001c01c400c58030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 422715620 1250 422714370 422714423
    0xa0602090607061e0e0d020a1b03051009050f03280306050d1b06080c030a05061f020f0d09060c0f02041e0903020606030309010207060c080c0d08041401020304 70
    0x40c09010181046816a9010115080300d511044940c40c2c220485488900d41d0092011842d84180501030041155002950f105035040c4004e182c1d403c4070701c03507010314408081d8a13401140c01104840f440305000c1c003040010400d10b002562540580c0400c1295640d0020480b0074407000c100030261966130481d00204d80c400503044020030503864a400180c60703602c10024460941c014800c01080f15083c0c81e4250310b100c2260310890601c00c0260411035100000010350b0b41c4018042c5001c20950b5514000400d4203080b40490f203091764000451000315a03002503081000c080d0315040b245016080788060300d40c0308452017101c0024140a40c1304000605d4104807001c050f20140c008074501041a048989e101185a0b01c1201d107613584001c0c0c01407560401c41182c0004050703002d5464003e6980c0001e48860050042209000e400406901008990740441d403070600002c2c25510b244c1803110000f402c402c0c090b6000da500d424a40c10b25489c02e181842101d0103903170b00c0142000000d8003002040c1d259103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 422716870 1250 422715620 422715637
    0x901080901020424170103020a0506090d02060a12050c072111120d0c0e031b031002031e0c0f090f1309050304061d090604090c150f030e010507020a0602 67
    0x15024040004c101c0e03a01c0f114050f50300d2040c00d07200d00e4070612410050440e003442c903055541c840000010030250300c030329111009550043d00c1490b540d1002501140c112000464000c0d0040c2d00001c03002d100c1d55001c03007020070400400009000585420080c114103014181000d4241e001010004070200074545052040c1344140c18180701600304012130301e04081c8048101040000b0005800c0c2c040b945070f12444682074064140b1511400c901008603680300c45500b01d84100360a030404916284e07504109a050025100b241555645440c40700071130b408840349a0f0f00100854003001c20014105002035510030020144d0b4241403202d89010481268501365036190084004131003413100381014007421703880c03c1c003800041d50380c2c0e403522100a011480c25690a06c0b940105440c649156440ba000359400041c11a800700303600540741003900810703205503c0085269000c0e0003608003507801855000407146582c50070801940c004041c1404e84a04551001c01a041045031500043e0294080d21601 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 422718120 1250 422716870 422716873
    0x510020309191a07021f0c020c06030115091706040f1403070303050117150f0402150a03050105010206131119150203071e0506240907120c0f0509010809 67
    0x32405202001c2404001042541c42200c400e404480381a0f008180b1a0003415510040c058440f40046201000561117511050551034203c05240d00c2c3c0301701312010455000401c0c49030b81c2c0d60340e07211002080140800b9200420021140040c41c401c21015a408010100d0b020381115607071982c5803031110b2003103070086070500e40b200d050122640040000d049011310030b8600013204d5042100403000e0103482e416142c0c06610451204d0203000c07401021980101a0682c03448194481d4400281158080300a071240410b0102d010726415525401823030484100380c09941c026290740d94010480e2049600150003215413200750451402c000c11aa019980700204181080303031100003e0f0b207152900d00c1554016400452803100b404283c1c115460482515804404c2905e11580d0302929180c000340054140107072810044040143c0340e0b81e101d00d0f408000c0a00c00d4500e001c1102622013400084091010380c5000310415203180100300b03c940103407503078881341d0a0100e07c8004690b081c0005296400a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 422719370 1250 422718120 422718133
    0xa0f0338040302121c05010806131106040801090f060c051813090c09150b030103050d1107030204050a060e09070305030313050307120c02011103090901030624030326040510020309 79
    0x840104c00540200c4403900038100d00a09580c8105041d5101130b0013042461308882c0a0003851541e1482030360000303a00100c551240754020000450303502442d0310070301700c0c3e50a00b03c40604006120510410107446214204601800d062080b07455000f600d507656030503131104242c105a450454a8a900d40d030440f403000c00d020b1f1490399880c0c0303082c50325440081c50507110606022560b0390700048034003031b00700620100d0441d85107031256555103500800304020b0050340c00261060f20801d00507040915000b4100788610305150a5540c0104060300c250695050114080388180c1004241c0d0070890b030f041001581141c03660513140b4160b91021008650a110411007040007441c8100c40c403034000015202c400c040481400054011031203800741042a42040115045903603a0001c0300c1e0640390010400212401014200c0142c0f00748840c80a5070216590300000800d0b6003c403200480c1031440c840c9240003182141021109401690014500e800503806641c0004c0d01e540a580d1001481c41200e82 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 422720620 1250 422719370 422719393
    0x50702030406121503152a200a03090f05040e060109020a21060e0606040303082805101505070201020303060d06091a07020c01080402030c0d0309050a0f0338040302 72
    0x32844d4250720448410301c6401e4081d400100750320981c00e01c4200c698103250740031049000140c0b003500c034814800074050300703420085104460f4241c0308400c5d0314580c11103215010302e09001c0e050b2905442b814810942040b8041610b0400703000301c80d8251404002011141d0900d00054083e40096000e14200009181000e4008044118620300e80303e03403000014216003009450381c9401c0d802040c0c03902542040004000099010b21134030390248540d40000e440e5281c194680c00d0f8004001050040503040c50103200705400f041004400b00c030a0300240c0a200b45810704d00340c0702c0380244003020b8056001031001134202d0910000601d0750030302c50280002e2000c000d9859503001d03100117001511030703031900d010091610303010400340d20b2000c1d090034882d4281ca82035001070395690900c01c1803401084010034510805009042c080c001c0c240c014000101c5c06d03244d5406040903983d03031100b1341d080082802c101a201400c005286881403401c203a142d02c4c400114400341c801d0801030001c80c110301c9489003100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 422721870 1250 422720620 422720651
    0x60903100f240306050a2a020601090608030906070219060503011e150e130e0307021f090b07030203040b12010305060601020706021b120604061b0305070203040612 72
    0x600103011050300040864079003891000729030a07010203034840301080340e80b03103074151070042444102c07540050301090a90320140030801910006903e58118140c0511210003840b0082488a68441d079600f05ca40c80da03a00e4030301c070099841c10311a1510b2038104210f1052203003801030040404a001400a0004011030f00118400000300d6100c9000100080014008401d5010740c00020707580c0c5004d82d5030441d0a04a07801c0c1d0b143c950f5042c1c6401e0012044010100741c50ba041d00300c00d1000b0140040114a054040c0d00c2d44035881450203c1c810100180881c15038a0042981e02039440c40d6928420712130304083c041000c56101c03150540551009110001f0030440d0798009100102030212030012552451400504c0e005010300500c4c15500a80d0303061203c60b5000841c001c2031812001d9060f5040001004540848c60030f00046c18a40a8141004140100394008e688440d8507800d4803009a29840c104500b2185e0a455000040e0001c0104104551107860346000e1a00500c1002030649800200d24 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 422723120 1250 422721870 422721883
    0x60e4305030d081006140d0c0e040507050a030c02030403170310170d03060b071106090a0305010509010c02062410050f03090c031006050d140705030a080c1204080318060903 76
    0x280000f00c031042000301d150b8036404803100412407800c00c3d03100d03012000c040708041d0103030744c20b052542c66a4611096401c0e00c501005902c41401600c03c01c864202103e000344180d1241d03115402017402c20300740a03c2c0b030348000304403401c8070b41203003400b6503800c01c00750003002c280d2010300500e9000d2410100030884c216a98520307100304214000501d0161039118018043c1c5045510820700d44405002040c081910300d030560340d8140c000c0350310503030b19015000083c64020b52a080601107618000410203030010550124648891035022258280e6485041d4a4200c514088400706840c88481d820622704141e40c5c110418101814000d0802003020140340c540d40041f40c03282569803150441d51903500701440f28000c8042803480c00d015860420780402c425496120b00200298140040940c04000070301c11103014280060590305003c0250030000d00399040038000c008113004408501c181031001780e089404482002e009541000740c0ca1a10300392100030042c1242d0046001c00403042c0581d001e0040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 422724370 1250 422723120 422723143
    0x1050411070c0e010315020a020c1306090e0a1b0f0311010302042c0a0c02031b030403060204032004091212090b07050c061f030f050712060e430503 65
    0x15001c3e0b6141d81044c0e000d1580c011091200c81c1c0c810442c400f82c095010666407400e400a454003003006015a154070300410741c69101202c1240b800240b0401c0040128443c00624010126040d50f0710707141c10144132901881c070940c0c0c48105010410000150b030048080319200381410f0060909558441d49204d10b03c0c0c2c01011101071301c0001d21a00302c40c08000301507030000c42c003072010044c040c01a00042e59a20450820400176a00c46803078043d440010001c0368040e5a114005640b2541e4900d030a0348222614a8030303440c00d45480074401d0441c00c3c00c1c440c0900407904038000d00c025000c0c114090311a1559018a22140744d00d404120000c10501c08030716006440c241c1e81c01e55211000880c0134200079016180c0001d860400020078400c00002505806681e08501416400b031441d2030b0844c0303000025840ba1801184118001c8140540c0c0d40c043e4440030214800c0e01e040c412513511480000314001c5030340f2441140008440c540351136003c40c1d201014403004000039150340381c0000a03d818504001d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 422725620 1250 422724370 422724389
    0x510031b0c060507033b030d05060111010b010c02090402030c04060e090c011803140f01291009090b010203070b041401180b16090b0d060f0611030301050411070c 71
    0x820004000d0184605503001c1d140b41740410104240001c00080303a03201040c050076042c03520b1030311005203445000f92201c00b4038003030440c2c0c1d540d51040c0b92440070b40782c00c1f0f840c140841c0314020f880c202894180950816400e0507510780c0110742403642004500b40000d00309a80502c2458601c919540702c91040301c01400321170485450354074210980500e8500714000050420a91019a290703070040000e074601030325030150b035180029408200307480c5403094507910907c00f582413440010302038410003103642d0041007201d0840c0060b4401805e2000700101482054005050680c0400c003020643d80070b2601080d0501c15a0710b054104c3d00d6240d100070b41640d080e0346210207031038014a02d280034800c81d0160b180c910700400c03409005032144071f0f840e10010440c00080d142e269031803000b1172050581c40040c0c0310000d090380c0c80c1c1c0a502d503e0401400e1038028545143c2c000303030300440c1c401d01414081e1400c2140034001c500d107a0030541480082d00721106200a140e105202d9100010910101c100183c0100b08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 422726870 1250 422725620 422725637
    0x14060403020c0a0812070b0a090b01030b06011202041518080706051c1107060f09022e0201020301050d060923030c071a09010f0c1506090506030c09010510031b 70
    0x104041d200e404e50004115500560150860001e8101951007590300700305000969581d5a08035405028900401420380c40844004070401c042e84c00e15602a280a9846501120090203024102c0c030a40c05610062901b111018a03824807a5502c1000c00f49181d20261482d03a88260080c40c0a255400902c0844c1c40410441012101003022814048180009010480c203000708641c16100c0e03900c0190607191103184083d60094180c0003030192980c0505082d1007000c4c0b0840440f0300c4d0300700110403465074030102d840c1c0400510500a0b64103031200102117081c60940ca0b6148401004024000c4680c0156900c00f206003400f12595202d05904110181d81d80c0d020000c03000f401c1c54101d41010120041c0c0c20744680362600400203a8a88010a00b00b4082c02d6071400303030955802c01d1328130300146804140120014155001d421003411208044014003440c0c4800b402c0580b5005210616908151160010402031602541c85d644141d51401c002400e4910101c80040d140c8907040f4903801300b42d041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 422728120 1250 422726870 422726893
    0x80c161502041806060c0b040c0f0e0f0708010b09041a12010e0609070e06060c10110c0c0a0305100506190e01031e0506060114090a080105010501020706050a0e0d1406040302 76
    0x10f100d1010648000101007003007909101000c1c0492045a40c0070b042d045500d0700040821940040490241c001011500c000a583d00a0f028000000b16440d0504200c00320105101601070311100341030360074018100c0e041048820600004081d810501d0503030340b50708154400c44e62202118950b200c40740300d00105400b034450b07000515181d0041e000344070583c4002d10402c10f40011110482d0040800c07070740596510841e003407551401c09000040203599103816540401140b003d401032000054410554034642206001c02460014501c80588181c10201d800b585403070b50340e070180d907102d00d0017050703040308544202e41c2c0d4940005a40044c940d608110005005019015a861000c0070480c0003104201c00c2c0c03070b0781d003645582c030240c00141441b411611002c0e00c441e40b030058488103400031707000c040c106a441d41e00078081c080c00c1c8111800350003940e90200d04540b0441c201c13034484c8219251102c074024600240105c0000d2100141d800c1c441e0703120014421541070052038000e9002e54020710b00034080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 422729370 1250 422728120 422728139
    0x702010501060206090a0f0303020d0515041b17060a0b0d060906091118010516240b010c0f020303090918070519060e041d03030417030601080c16150204 67
    0x1a0008025940b202c1c1c104174008200094002c003495120a103070800381064034054010b030003080c040c6c00880342400204295041c9903110607103c1d6908036014080c88600d0460700d0b8040d01090384100c0014410380c2566032144403c5440d03a0081c2d005881295455a075031503041994102520b0001d0301034a40700d0400c4942143e00070207000d00b031842c10400c0501e14402c1d00554510984d80c944070b6820300b806030780c4a282e004206841c2142c407042050b00e00002e0603c1c00458050040546890b0f40d90381c18503c0c4c0325101244610741380040e06031a001388440c0103071600700103e046844100d0341884108030a114685500c038103a0300451400c4c10201e107400290722a9401c0400903005540112180702e1a140c0e000e400300c81c464112496030604500c245540c0c030100d0050310180d091104510f03c040d950010885001000314421402000e01004800341b844a8158500c010b8860500158842c40032890080795540100252520035440701c0308070035113503180c44083d60000c00c22030229a000c80c081181f0140c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 422730620 1250 422729370 422729381
    0xd0305070207050604260d0c0b0f1b0d09060903030507020d08060a0b0d09050a0c06090f0302100806031504050105070e010305040b1305030c030f0d0b03150601140918070201 76
    0x100360001e04509070070b040100740325000b00e01c102044000c1d5001c14043c4018050805544960613505403034121080030005881645646804c640c135171756510006024010381074919006111800c840d0114560a101c4d0604980080c081c0341e004e142c0e101c18410000d8054440d82d01da2038400c2d10041214a400c40c2c004e8106441100100d080c0022401000000d5543d0310054003910348841101780c036421186410070050420000062942c407603030100c04144070340880d0305812034900781e42d030360344460311021260346105413844004e4200417411901855580074500d1240e000d88040c0031070b6036161500c3c00d008449042950151401d9640b030b0309102c403440d400703030441280c01e03001e00b400c0c0000d051a503100d4010801c010b280e9030341158101e40710803c104052080700c0107020818122500c0b89030400000c0115131000d002e9540341e901d0099001c1e5141004100e45448010a07801c20085645504c01501ca054078600c0c8242c0280c2c0800403107000e95200d84011002500d4014290a9442d000401034210b50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 422731870 1250 422730620 422730631
    0xa050f12012f090d0818060417010501120c09180f0c03050607020c031509070f0602030a1e0c03210e010b0306151c0f08030a02090a061d0904020303040b0c0d0305 71
    0x39402c00180003103883c0c2008540189505c80c3c80183c0d04c0d00003508400881c0303d05642560310003400140014018203060301d07143c818000c04020425070340e8840001454442c165801008400200b000300300ea0f80080c2c1c001c0800304104561084a0301060b5030300301200284100c12584034141c08005d00500c541000402c2d40441b00b0b00040c10707143d0010001903070b9000b42c4400301344280541400611290070a001050061043c6d20144c207400741c0b28900a91290048090180001c0a5008041c0c0d500e07004c2c68040005801503c41208071800ca49044a800120071070100c0c86401920010800c42c0322807141003504200f940000030551007103400c2500304030300a8000001188a05040800f907a241600c0c50113121866102070000044c81c42e0070114840c000038060302221011040181940709a001070054480c100c40800d112904c07800d00f6035020802040d07821840341c00100d074101500b010019a60013600003012281015075460030701e00584c0c40880c401e94183c000c51070390512541c040c00703415000b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 422733120 1250 422731870 422731961
    0x309030c1b1503090b09240612010e070305060705070c0b130302190503010b09090607080a1104030b010819051b0d02030303070e15031303032f0a021b0a050f1201 71
    0x7541c1150407100d5010b60603905408249047c408282c80e81c1d1110b141401035007070300009110709109003030419201da20f5444161079078000e00340040da5191190049540c20790f4814001141541800e00f180c40d680c2146030701080929a620000c00980da4024a030402e15224180404103503040c88185030030340700b030b1415060182d1882810300680150200b00e041d40010071340740c401c40035a034010340e000190031011725040c0e0300c04000402000f4005010700702416202c4030400c0318400804c2d8204011102042d1401900c903401210301b2104800042d2040c00b003c010080c2060085002900080c1c21644107a440002180001c0b081d0041800c02c0e011130341c48002d2042d020750440c41c1084411040518a040090070183d40e5591a001a100050f0f601d281d80b4601004c140c50501d80c408240c0a83d014802c2240503104042c6002c4010f506050b0740e010740a0050a0300d66298a44070a02c40e000c03201403803050340070b18680780c2c0c0080c0c0042403141201c103a025149900441d024500303820468002c1c5004585035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 422734370 1250 422733120 422733133
    0xf1b032303161d1203070803040602091203090108040201080910020d0f0b03030c0a02090a020c030a090317040303140a140f0a1803050309090c0405041107060b010309030c1b1503090b09 81
    0x741405a141c503d0080583c0c1350b400c01c1c200001c00c0350031480343c0301b0700506054021050000b4001d13164080c0c95626400d44010480074a0b004905a80e070141d020b829002072a000d0025005500c03500ba2141c22800c00c04c00c4a21001681381010181e0b003141d061000b441c0d035941061100c07ea0703240070784504504c00394003440c540704c40d80f1900f6440e1066200c1c00383c0100d0150004c601408105e504aa041c2c8007403905903510b454030864020f200074034a2000342c440d00f030801542c1c1c1c03803480311500700c50481f5810380390740301c41e142d02004000a5400c140c0c06081440707039104c510309108900100521400c4107004c08942d079101b0141c00a45810b181055500c51644448000e200254000003114406081110030f00c25543c5c078980211b00c24410380c1c0050340c200e82000c0c900f801040c03410300607000d400d01c610740034030601351000011011981044800750001d00321408a0303011980003d0580c0c0b00f094050651041a40c8601804005d4600c0c1407000340040d80c9d502100007440b880b07020f043d401200d01d9000d040c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 422735620 1250 422734370 422734397
    0x1020705061e190c1b0f0201090e1e06030c04020408060403180e0c090a0503010c050a11030a3006030309180b030607050904060e01030b0103120f1b03230316 69
    0x114100344083d4240440c0d4130301c98110780703e01031714180d169810500e8a605608226180035060700d0610a4124046812800041a5081c48003da039204482041e0b00030381803201039000b0b05411101403d11601030141070042c001548942c00184064000b0030000c1a06080a10b030040005034030307000b50382d2181210703402440342c00c001405054202c440c1c69640c40d1a450360307000060802025a2040c1e40c19841c0150343d40100da00076024142c400a1038564100e00146045420f46038401c81103000000303440e03444d4026006420341602031500140211088099902215400842d44141c1082c2c0119071005030810803034066000c40080c2507860b01003840343e8000c50022980d01d00c00903098070240440882c4048a640b690780c000380040210a61a19840d40d69041a842d00c880a0200b9a1240c401e91201036465000340c00c804e01c558110b80d40c0d00305810101c8004034084540d400101e04000e8008003560a0000302030001000c1c104031307503546a0342c2c01e109581d070012558098000003404400340e109034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 422736870 1250 422735620 422735641
    0x90804050a1401230d05010f08160b12040c0803030a020d05241003140a0207030215090303040f06090807050d091505040b0706020415090801061428050301020705061e 73
    0xc480761a03184200d21071403504c12203050315000b0403102c1c00d80c580c90b040000907899407240c8000d048030361841c1aa030445512105c2e00950620500074065100401c2042509000f406402a42d0041c05980404851511901d64a04507407050b19030308801900421811100e80350383c410b503a0004c00720181c09034841141c0340c1d1942d41c0d03400d45002c6031042e0350302c4200740280d500903080220361400c0703078041d00c42c6481d01203495402500302010a80c01031041c1a81c070b18003840da40d240d040c0560784441c0110b00f15540c03035480c40268058002c0485103540c036841c031980040c0341c0c40c2c081c28503584558050000381451010040401c5500e51084c04025401503e28021640000441d01030301c0c2d1414940307550319241e08100b17000e841542c0c060560103540c440c2c45044541c0c44107030300090350025030090100e5513032841d10184c0c2e10040e5000b04d910101480d0039140114050303495400d01c507020481d600140d0764035400682240c01001080d41c954000104114900400348801c00040901191322142400e2099481e03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 422738120 1250 422736870 422736887
    0x120e0306060d0203030c010903030e0c010504030c1403010b09090114090105010b0406081f03050303090114010f05040b0118141f0206060127060f030509011b0c0201050d090804050a1401 81
    0x10b4011540302001c0302c1551000d000310f410307440001b0001d00c10301c00d0a00e8020010000c0100b80d80c101e003e03046540d0007962040c0115812a80c100040100c443c0c01d210f58012038410902c07020794190f6941035521110303291400d03124400c2554000000300d10300110192100014002c000c0080c90740b4041c018030421070402c0a98060b00c0301860504281e64a405240d00070601d8500c4802d8900185200003080100c00002903105200c140b00a001010402740350b6030b41100c003801401901c06040c1001e01c29070034954010041d001c014035201510850314880306030420903e82003d061a00003011040a40c1401643c803c214031800e031010304ca0aa070310b4030094032880c010b04914104000405010050008150b541c440100d45140e0021f040d81d0340c800240c94510700f0f80c112800701e402c0400282d170035003040c0300f404043c240c0c0c4c0c03130404030100700414216141d8904031030480c1403020130b01400361241001d110307882a01c3d110701e1000b40d45505040420948100691007112304401e07103c2c411820740d0380300243c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 422739370 1250 422738120 422738131
    0x11040518101d060f011703160f080d050903040f050d2d140102030a0c020604050a0308190614040e031c02030a0216030e15040b0f0c0106080d0309120e0306 68
    0x10303415040304618003281e03569820040d00b0388520320500c084209210701c0d181c120b17410003043e0300141454101250f02c90144010020b036490301a40b185011500d0202080011480380464a1400003c000c1c054229102554019039560001c10b041c45071280b402c04003400f40c0030480725480c0703c0c40c03269034110704109640d0000b150102c48100c2a00b91444404001c8203090341300b0701400c0040240c0c1d1405001b50001ca8004030054100391320404130500220300c0501641c3c101001d0500317031000f43c40613a03100d00050f2852107060b002c90700190500c0700a20600003d00300306c0c0c1e40c10215040340d100300310903208406034507205608100501d65404154400000c20006800030150310780d07482040000c000c5c010700c01c0c18841004040c0c184003c141c2c4c40382440b400c00504540c07000a850a2010201d024056406041100c00701080254000e40c0c0680191203801380c0c10002090035a02c486000f0309010354410b00d83c0100307444800c0c442c02c015070412400820a0540b5041c10180b04902c002952400041c00c13 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 422740620 1250 422739370 422739403
    0x120403080c0403110f060c0f25060f0c081b0f010f050606160c05061210090b15070f08040b0a030606050307090905060a0f2c040c1a0705060411040518 66
    0x103c0001e0351b01d802041d64800c3c6201c5094960a10104501540310016900c40700041c1191012003081c2079000006101070750806e135110368882c00c02000581c1c58100c04c000c141e604c040c2c140500741b402041041c82e02d0711400d001010b0309000c2c0b901500d0700d00b5140e08140e11100e09042ca410029191641000d8505511000000080c0c503001030419140c6110550020364000d2000101448000b112060b4140990007200c2004d0246903180c03110304c1261003000515600c400005801758184e10381d24040d09015001d5813a402d480d10a035076924000364030640c0007000300c40003c1013a42d6241e8161107068002d0649080c054034510b4000c60042c0952800d000b00d0781c4240c0d0740d50104100380c5035060070740d001c0d004e0ad03000e60b40040c2e2103a003400507418a4443c10805014120064418404841d4106014680c0300d580c00c2e08480c20010417607821224104c0c80c41c03940d441804024089482004020300481c0a02d200c081e4084608042c4425a940100b1402c81d0310100f034a220303191400002c1c0110190310801 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 422741870 1250 422740620 422740639
    0xc09060801063321020a030501050f030609030d0905030c0f0a021003050105030601030b0a0212010f0f0f140f012d090803070b011518030b0129090112090206120403080c040311 77
    0x20780460440c10800a00c425162022030080701e81b41d09a8000c6050319011211002c2c088000e904159407800e044981c0b4010303170018841000380400d660003489105128200356400c0580c8442a146400b038540c3c4030790031a038070103000d00c01075081c01915070113010301602d0140010340c1031030302084e6a00010700c07000f4580540072002580d140b40326810b40740c01d440c080409142d156590800d0702c12546e046c0c010200c0ba186601d03c00100100107111580031039220b030031b24902c5100ca00e400c102541a00600c542d05204445940c104809542104084a1441800d5104100c01060001030000140e900900d020f0b90081000e0320100b050302480904440d501001e0081050818004880070310000c444559807200c1d044001c4200403000c0d644078140e490404000c010001500c49100f000c8100d1444544080382c2002800c2c640c0d44100002c08140400b0040424004d00e10740c081071040d40017458240d10408110140702c20990306c0300d41c46801c01c44101001e818141140c4401d0079044094032103a103e4040c24 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 422743120 1250 422741870 422741897
    0x3140a0f1209050910050306070f0c080d15060c0b10120f03030e070803070b0912040e0a1d0a020a0e0c0a030b0f10050414030703030f05070c090608010633 68
    0x1080b8460151034003400c8030700c0c03d0a00084400c1014924019903200380202d10011f440307544502d91052241c415940d5040ea1803000362280c032107540c005840c541600b03803200e00311190010741040c10fa000f0f01c540d544214401075103082001c3c0030368014015002030108034000300b02d038002e42c100140c4142d811000c0d00c14041141d01c0c007640180011031070001c20380910200041c1001011028120440c000c1c0200300c102d55035400301a0701d414510340381004d444420300c0240001d0b41c1c41042e40754813103500000096160040404e0050000940822645035800000d61100f1801c110b18660f0080c0410f0549402a042592124000340120441d52080580c1e50f9001c050780c0d0744107110f039108144090041c14001b110220000c015902500408044907480c200302001802c5c00503180007101d406070780d1100002e0240c01d0841d500e86c007200055404c0406d2501c042445045441450014a640720000400d45e20340420103a0818107101680b0304d101c15041c10209111460110940580c1c0c9031a0909002c0e142 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 422744370 1250 422743120 422743127
    0x1503020c070806150406090509150702011e0603030f092117120906150307210204110a020d03140103030e0d0c0311090a0c021c111603140a0f12 63
    0x603804440244a01014419484581002c0c00140740c4d040d6814000b40340c849228006958042e42c4424456010300c0f000352400d020805e81035000360180c0300115044210407560490f0688080b402111550b540f2000c004264204140c034042118504140c041c403442c0184c0d0401c42424500d45003020340b10644d45508010040c1821036000d40a070150030b444070800041880000012280c9010303903c200000b003005513648101515070480700900402c0f0f80381c140000f09a8011002c00c0d407a00110f40f100c444001030307070780e03000e11241000d005031000c1d00e42c5610480207103008144a12601818500f0b004038044451400c2c00c941502d400d41442e03d0018222008a42e001c824180003038014400864003004020781ca22032041d9241085031a42c04603100c1c10f10940c101e900110400c03016a10040a0800074400d0022003c1051142d0620b0f0340c2d20949001d40c54107283c503d03102001c06404503541407040186010349400300d000c100009055941141d034598410800b080301c007521444102c4410742e180c0c0d20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 422745620 1250 422744370 422744383
    0x40b0d050a0b01450b0904060204030b0108030403050a02011b14010c0207050a1406180a030507080d052502060c01090302030306041116081305040204030f110306130b0a020f1902161503020c 83
    0x801b804102c41490242000c2c00250041d000071504014020300001c3c2000002040c0c074140c1c0c1d0001e014100094a82e030043d56442d601692944030800c58200640c0414944448519040c1c2007030000300d4008814400241054425040f15100d60b50f040b8040c801e440c044904142d03e02c00c1510256a1a20003444000300c001d03d00c40483e07408010ba4a010081202c0400d0340300c121840c450844044000400d002e8616020300d10444140000d200980c1c1230101018807440d880e10700291901c0e00d00f41c502e01d13801e400c0d00d112010a4001d640700000344a014205803240322018202c00389164213102101212014500030a0350180002c0000310b68800316044181d40711009286c002e0045585aa4030301d080100c540a022050342d80b022210015040c5040101d08503214030324141035104642c00d51380c0d0710210040003030010f00304141d09020611a4075150350080c00c0007584800301c2100b21702c032000c00a18181c00444003a118020750242000302d224450780300c02140a550a015071500a01c91140c3c2c070b04038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 422746870 1250 422745620 422745641
    0x130509030a032c070e070c02010c0f020406080303100501110c01050f0a050c010f0c021b0901051302120a0e06130b0628032004050405030405040b0d050a0b0145 70
    0xa03e9442e20045032070b000904034088580401c01207800340c2c0e4450040d10310303010620000e404a2480030990340000c141501c24840988000c10001e41162038402c0307540703503800446004811800c20074081c485580c10284610084940b5001060041800030000301940503460030700382c00b030b0808036494081031300030025103a4500417000200300e4010005950005460540002c01c094000c089100301564105913600a07031b4070001d07010301d026910300018004c3c2c8010402c0c86004d41c50f03007480800400b845104825000d11a100d40110f4a1610340030300504140015100c80c044450042d601030000d8068061191b2002044035010064009450801640c01d43d0342401c06111f122000c0200811000208221135910302c001d40140300e96118003800211103055070041d00e181c0c81030204100341d140641040780c80e0a4003a0000c00e0044150741d442e8505007004c41c0480d11940044d006021104107140b6119080038014424100c21501c0c4414060342d440e8910501e4904040401d80c42c44488190811030041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 422748120 1250 422746870 422746931
    0xf0d0213030b090109030f0807090e0a09082d07030804060c050904090c1502010204080c0d060908040e07020d17161112030a110301080714040f0c0509130509030a03 72
    0x43c50b04940c0306001344980b000850101c0c598428248903d032003a190b03c0d21902e00b540382d0030300d411b090284030721140c0700092190190a0b1140740d048001642240600102039090980383e080d00b080c1850301c5083c8401540e0301c80401c505200380404241c0c417000d41504107030082c00004015401d4942216588103260903950864203001442d01040540250b9408480340c0040c003241d400003400c022401d034401c900c10059143e020100141302481c0c031090b0708050600c618000210255280d0702d03074566400a80c0505080e0103e44100186190140088511070fa00752030b00002c0010710345241103c80401a280c01c00c0d80c021945410700f040e0003000503083c85030b00c1c0d00c2140c18084501d840c40810f580100c0703540320018242410092204022011f4a041c0d62458000c0c22015040504441301d4800147d0307140e03031280c7c54002464201d500c40c1309040d100140780c4e0b01da41e511402070090001c40c500812007004824504800c002c14400084140c0300100b825260200380c44121841c0041e45000b9402131030940c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 422749370 1250 422748120 422748143
    0x20604170309030615060a0305090a21080601140304080a02011103010801060f08060106050f1e030f04060b090402010e06070218011e0f0f120201020114040b0a0609020f0d021303 78
    0x400320000094140350108500700c1d9802d50b251883c5001c0403001c00b2000360800d1040c0103031800c06009800c0b041d03100008604640d000c060545034090304041e80c00080c60110f03440c440000360140d2201509612960a08024003c0040440140494400104041c00103070003ca148400c1500c01e4100552115180d010f064172940c44400050007880c480c4107010403c1e20f01c210000d070101022074a9030480c0d201d40c6980c2e0412540c20340b111301c16842800026003a141110040080061400146001c3c22280c1da05400c1ca203458a4400c0807a09620b14044c41403240208000042c1c1c0d204203224900842a03814a80343d6440c0e10100302081d42540c10f01d0030042070070001107401c60325981c0301d206201c0405c0f40001110b94800354072100e440c01c0d0042e4112032040803014130851100b13150a0501da4810302c00000c5940107080c3c040d0310000c0c05c1e14115180c000182c10f220381d410040c0a00350141540714800c51805036108044a002e201d17036541d43d0030080d0080f440386400f107100d88d1004021500183c0e00742a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 422750620 1250 422749370 422749409
    0x1509020901110c1804020d12021c180513021c09020306060604151815031506110622080a030906060914070822030c050c0105071e020604 60
    0x180d00448a8940001d4286034001c40240000811075594480a8461200c036000c099820b10000d10003001a600401c14010160001e10740b452004200f01c03c5030f01400990004404000e101044505500c0c100503038240e8003401612900810703801c8a1048403041600c0440454880190042c2d130400c90b840800c080101e6180710b015040b82084c00d1088041d0b501550365076040001d180643d010344421003d4007082c00741031500554200d0000c510801710f10175400d580e0302180300819499254100044d4848100015860080c203420020b08103e00705074050f5021051070340d5981100401042d40340c02402204942c0d07082a10b91044a5a0402c102503941e185650380030300a40720711241113400c40e00d00750000900c240c081c455066107980c2528007401e15114102c04950640700985120320740600030b007080c01220444c0c01d05121041c401d4440000018142c20400e080007602548641030240400c10007000550503020003031040421040301681d4107140c004034000380610703000581410418001c003030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 422751870 1250 422750620 422750639
    0x316031a1b160515010b07110d0c031407060201023603030a0518040612060509151e0a05060f01050d0204090606080906250e010311030f09060f090709090615 69
    0xc4000e004030104d59103400840e00305080c000c801d10440040300402d00038007000030403000d00c410f042c10f4020040c1e60052865251101002d02540c8106c407441b070f0801c0c00b040021424000f5100030b020314002182051003030080040507400c1d10300d2009041100129003a000f07030b05410382d0b4040d14400340403691074180001c4040c066601c840e031074802120b480310700030f01c40307281c28091001035407130000222031804d072559a203c0c00340c480a00b03504180e02580500141c482d03003403050780b4420022044814128640f1900e0368001c0f160140019024500300001c114176078590342040e480c2001b00b8a491545d4411002c1120700901880d00214829410301c0307400a81030b85e120078400e02507802102034800f80e444203070000f02021010340441c210700380c0517840128014020031b08084401811705010030b450721000440b102d140c3c01207604504004d1402c05200c407400d41080700e00e070300455144900500d1305200404581d110041e2081040c4540c0304c4e070207482001540c2e0041502c074404000d40c19420f588072000c54 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 422753120 1250 422751870 422751907
    0xc06150916052101061416080f090d23011514150a0201050402010e030307110103020c01060801020f0c0d08010f0e0a0f1a132901020f1203060316031a1b 67
    0x60001600d0815905170510206c02200c15610039a980041165400d541d10100da400c07130005849460130512841465880d45883d9003413a030701c10301028400d0044030030080d9409914040c464440d030b01d450350440010700600c480d5001d5420343c112005440e1a65400164540300d4284105500c481c085400748445405401a0f070043c0c0c802d882c1d802d0845680d205042d0b0302c0c02010700161803000e24a45090107940a1f600400540b503c480001c139074980c55000701420b81e071245040d0910071000092120395114107000a502e801441c0c91f0880281d494582c0d10400680e15000c1c1013241c0d112200415014002c5902580040100420602c5540744121102944400410072035000b083d013649414810051886206040056207c505141c540304d150464815085811100c2c194840c1d032041d1014039400300010f00e03005801c2e1030b5083e81ca2402c801414107207603e4018541401407221000d000041149403c010984c2038035104590996400c0e03810980c3c0c1901900d84902c2c1c0300c00180560305000c81c0c1441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 422754370 1250 422753120 422753129
    0x1514370b1c0b0a0902030c0d0812010518010603051e011202031e0304060c050a0503070b010312030219030905070b0a020a030206010e04120c050307020405010b0c06150916052101 78
    0x103100c00c5502803822800c4114a801c005011220200009100b03000c1c2e58400407480d8006000c0341e1340f90780c8800104800341c00601094821a01c08a4003440e00ca01c030070022030140c04150360081c4a0504072075041032000040c046c84c0e06040d01d642c006440b0a6800305081100c1c00d80410b00c2d8590b5035551042d448030000040264000d0207641c44041c3d201004c92780500200c102480110f141c2032401c04220342c80c040000084820b400742e80303550303404160708001070141180102c01e130102075491071400d00501c2088000da401814014030510007014060801c0c07186108150401191100c9141791850501d030158002c5000d1650110322042455070010703003070081c0b034404d408480701d598950740290400c180c2203e000b849640c0a8002c001118418801c1c1481240700d64103ca040203681d50000c0c040c0d4000740c212139034241020035641c050b58030070041e0540010102c0e105e41d50540001010501007080100740da1284d8090840013580144503100300c94040b080b40c820260215040d14807011444001e00c20b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 422755620 1250 422754370 422754379
    0x602040e190912051c020a0f0207120201050301090b0d05100e071202130e0f0102070809180f15060f030901020a0f09180f02070516031514370b 63
    0x35611404014800d9200380e5410030380030f581c1a00080f004640c40c1e070003102d226207000b00120085a860580d40040c006213031858980248011080d08000d180270b025502521504964090144c05070740c00030112810342d001041c01062002180003c603501203009480100340f1b10444039202810401c650103018480074070303001da400c03c550f14400705004009a06029500000400010710020901c2d8801c45020408030182e5010000c5060213500320303048500b0580b1000800503028040345090b940500b9102e4000841100a040c80f604240301000b00030484074214103040b4014445950b10f400b40d4819261034004c2036075901e00020740701c0c040d400c0101200040b03007110300400401401480003409545000d500c80005450600c80000a4180c3c40c501c0300005508111400203d4001e103d5009841c0c3c140d4540c4090a16515000150200c007a5080310f10a182161079003d00d041d03154003a0700141c41d44c522422030102000440c071580a08401c1d125003990768408140e400410341c003c2c80300c815040301c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 422756870 1250 422755620 422755651
    0x70201050a050a060609170703050d0e191214030d0f06080d02070515070f02100c14010209181909120f1e0c050f06010f05030105010504020703051e070602040e 70
    0x120f55000c0e1501e5009940118580c01403e01042d6440400217412240c2c130000ca800c1d07503940345c82d240c0c107000d148020400000c4400128026500f8400d404030102c1d20380d002d0100c0094604001c4e00b09a5080a00080491030301002083e81400f00300107441002512050404c0045100c0d49108010200d502c00e080300e5000c0c8030b00c0780c0021400481d158007200d001604105040400301d050004e1940400c10440e01110229007240158548490301200f13080300780c5465844030704600302590300910302043c0b41c0040c3e004200c2400300e40c03500d50428030740b1103101c0c07003046a070f484507141c00000c2d038408603068064a21b000141424091408d480c50380760b00712519809080d001020040700c2c2006401d0301c49000c08415202044c030107103e10140314005019609a801c0820040d00c2da80c101034082e40400c0030303845020001d200d00e180a11840d401418116011490201035541c0a41180a1544140d001400c102d6140c5843c0e00d158045030185588407108656654441d01d403406a040c0c01d1740c00000e03d01108 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 422758120 1250 422756870 422756881
    0x1e080c01062405070f050f06070c0201080f270f010507170702030f0708030403050702031b10020f0a06050903190f0f0305130204050c0904090501051608010f2c070201050a05 76
    0x316000089000b9030f43c0c641c070f000304548409140c09030f8460222080e01c1124803960110000b0300465000d88000d5a5041061440b03000041081d24050580c0491070303a454148503c900d40340035849030070800c4a1300701c00110380c40c4a401c3d00340309001300020059420f0208001016620101400d989603a024900015846008040781c0d039010307140e04c181111104021401c04034cd5000c0107941d116110345486440c0803c1a4042410001d044012140c01e045001082c0107500e0490b004045691483c0700070458440c98920302e5540d0000d062001c0c000c15a66404510054400d00844002001040c07001100444a0304010410a0000d04010001f0640307800036400910a006107070040140c3c49030a00002080c3e000c002c014034000e00300203404042006041e40c41e884902031051303000e02502c00066945040703d0700107a48004840001c01f01b0008100601c0010340d20107800701035541c1d80740f003918444844c1803c0140d000a0740800000c2d070588008206009505410041c412203182c10140701e29101c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 422759370 1250 422758120 422758169
    0x3110c0d1b060f02121b0a031716020309190803040803030906010e09031c180516080102070c09051302090103081e040b0f07060b12030a18030b041e080c0106 69
    0x6460724600182c0007400c4021140d1241006000c0004c0742101c074901001c1004c50707881c0b806104000c11230110712a00382a03119001c458144548c800d214030b02014681a82c004025200c0c0b250110041c130980e480403400710851032070720340d13003001e01a030108580d0b9070340d121040e03580e0701d8004031401003043c49140f0001c110300e0043c010550159060790b005509082c041c0013602034414000c0d0620111555540841c111a8811400105d03154083e002a1888026030202c034880c119568015030342c1e5038010000c2200203a07020310b0920898030380280c0060241c0b00c0001c09d02c1a4016110080d5000c600c40307001000780001580103115031b00c8201280108050300780310350002400f4520407080307900024490a8440c80a24006002c0316100e1400011855143c0c000a00303220240c82c1406915800843c80218841e08103103407004030508404809101841d50342d03189180c01000740f004160f400e0f0151001204103180c03d0f140c10540d0301a1040e52612600d003c224000c2c8414842c0c41c024240b0002c1d0400e80704039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 422760620 1250 422759370 422759387
    0x203070809060916090f0b1f082a070f1b060e0901060801060513120305040513051b091f08070e010314180703120e090610020a03110c0d1b06 62
    0x410413100e5036103484c002e2800700411020791000075054a07800c3e036104a94801482c20122401c403440c4044480300d07580e0081080324001d001d1080c41250080030f401c0c0036690716803400e40c201480c8149603507003168a00103560724003100c03000786100c64081480c040c8815500502c170585409079256101c0082080410003c00428403960010030642c1005100c010721817001803100e2400304c600b424041e43d580e50311280000010b0000e800082002c9024480e41c50008002c052a9910748014000c5042c07030030340b4a040382005104003820b01d0300000c00c0b0310343d511002c140050030134408042d1000d0444284c0d0250201400f21100d0340025000e40d4102219070282c80381c240070110f400c034401c01c1551000e50074100b0188104c22002c26200d4101e0003c0082d150070480d911503900350b0360b000d0f900c21038034040c0107003848054501481000131101341680302e540000c0c00c00390140c052906507100e80031014850f04054448031141c1c0c10084402400781840801a1810780c06020754445581066603044100c4401d803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 422761870 1250 422760620 422760643
    0x151815010947031f02070605070207030c051014030a0e010e0a050601050d020109050901090204150905063a05090c03010c0f0804061401060c1109070c080f0d02030708090609 76
    0x50b110320000d01a080034400c02c801c440c90203012528084400103080344c60070401007000c105076400041c2d0204004140c050180c015070140000d0003101d0031660f5040742c07107103580a46809400d03248140440300344a07011060340d032031904160550303e0421641c1e42c00a403140b046940919804c002c819040325030b00048001090b90804040c2c01c0d5a420602045911074041c82d0923410000081004034481d038503040014000c1082c4000140d50303d1800b540811841c8a10a4070301c14041c200b282040320351106d40c11903152140311598840051669004034100001204100035104e640010200010441d58801809000c4410032500900e102e00c04140c00c3c2c2e031003012130318002001c4100c000040750041c80c0c0a90800d209035400701c4c4006040b0020b5022030800d901c007034000b600c00108182070200b0701881490030383e82030320310408610308118041d010320440c21004008540000740d0190f550705450540b200650845000e41d40c0307060080b0011315080d0141c842c8881070050001090140c00c0005d0404001c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 422763120 1250 422761870 422761961
    0xa050c1504030206211f05180c0a0c14030c010510030c0302133801090609120206090a030f140610180b090403110f1518150109 56
    0xc2d0950303003400601c0d009404004100003075035190700c3d110034185034000e00c25401210507a1070901e0b146840a00369907a0750000380904000c128400e0b041c41c6407046d0a5108a029800035540c05d5003907012070b82462200805000702c510302c406081165000700c001c00b810220403000740034a860340c405003c000301d0b0900c00140f091542040410050908010318840d010b40040c0015000003c060f80e441c0d54012400c400401000070102e9140c1100e000000d2600c2480a10340700800d00d0400c0c1019141b0019805817008107040d4804840841da80c1e5000ca410441c0b000c3e00c8510001c1d901d1606042d01c14141c107003202e003008682420300941c0c20024006108198010800b2541e6250580c0121800714035407601059940756082c225064488643c00c5009600c85d684a80b444040c940b03045050088000b009240c1d5003201100403048610401d140340c004600b205103604540030f03152041d14040000b4002da880c00310780c4000003a514440d83c440e1400340300c0f4020311003841c4440a003548400c00c040d4200c5494 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 422764370 1250 422763120 422763127
    0xb03030c0a0308060114040801090204110a1d0d0f050601050f0d0c03020103050c04080a0b1501050a021507020703140105150402090d060b03010b1c02030d0c020325170a050c15 77
    0x1181c03043e03060540180d4181440c02c0414003182c074a403400d40c000d070040c01940c0c4d103c00f464000c500701480303007281861030124a40d0500704e0580d0018005040c07618882c1001c4608240d43d100c554070980701c205107551008070740d100103819240c52034440c2002d2003010300ca20300020000c229810311904000d032a0744d015051380410307402c560040d0001c01001d030800a5514007488003181c00d1108000744100d00b0b01a111080b441d2801e5514200102d040080c054108801440b402c108030b6000a040002004120402c41d016604d12204900e0310303072141e01c0603001c0070382c03c00034210021046d40040e001325100d55146008040c00300900c0f05a2140842c2d41c0c0c2c008480c1d4840c10040b805c56485050402070060011a18105a0000407062003502003000b0107144102c12200461504201104407005a401c00c1c003200d04060300080c6d1180e2103d810901140c9106000380340080c40c56003044040c19517643c11b4a04031048540840d07450303032030303c5e411103040c800c5010a442c03034601306641001010701c0d0350740d4518 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 422765620 1250 422764370 422764373
    0x1e0105030a080c010204030c030602031b0405062a07061706101205040501060b030c04090e010608031b0f0d17090705060415030e0316050607080f0402210604080d0b03030c0a 76
    0x10b240d48907940404103554240b2001c000134544d400008000e5000d800701584900704a50b049010100745121481c540508000411054460310161000e2006005444914030107680210b0103028001c01321000a0040326030100340c0c650884003940d490202c040080c0007980d1180c0c01c1c0076001e52031603007460104000390281d0b543c0c12165040564031512078000422241d5540345a41c1d210342043c1c409203c0e031140070406010034405441114442c1440b036000740030961030f10341e200c0e4482c4501044684400100c0322207a0030701c0d20801080c1140704055085a1038031007100d030300400c1400b44501800301c0c00e084070081507042100044103020384000400c00f502d01460840303202d041110003141c2d10700381600d80e102c42e44101700c01d0001e820285103000040c4030300042d0f07207031550400000402600c1400b9807141402103101c084103280b079000343c0c15207000350003c4026180d5668907420313149a1066100b11000c01081140b0000949982e40f0036000c28040840800304144c2c603030003600302a54450340008080d10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 422766870 1250 422765620 422765633
    0x3050702040c110a030f2303070324030602030114060c0601270f0506181e190c110709090213021e0403030203070309050d0b06090903211e0105030a 65
    0x41c1d185064101041c0381c14000030b0b242d0404d0144841940400d10402c01000c04503000981040c000c011504a04026142503060307840d1400302408403410950769410405041602020748800e000c0329030a680720150340c1389800f1020b0f501c2405254072000c50b02e90050b6281c203000003640c41c802c600501400d5903a0910350701d0b0112880c20140c210b5141038440c20030307510100a20900d03003890410384000c5400d16220041c01440c00f140d01844100365200000c0200480440000040581e904610180281c89004258212409030200d80307030407910b04564003041d00d40000d0307507008201c05407058070300841d922502c030000c07201c0074503001c1e4100050140c1c01980c031599500078010188002c104884600344181403001c190029001240541d10016002c6d06143d0007400381002040111106620b40350a07607600c0c14003d40c040c0c4442e00614104000c18405601031095802c80081c00021055602030455042c00b008006d0b03601d048200d0303c0f1501e07a40d01c3c0c40d10b82040f506a80028000f0998113020b0750300e07035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 422768120 1250 422766870 422766881
    0xf07140c012d0e06070609050616020d030207030512090604061d0c060927070909020a1407030e10030605090901090302030343021005010501121a0a0803031603090305070204 76
    0x3074003088400f0b04101e0441c0e0781e10028002c158041c140000e9504190315100f490480080c00c82d41c0309503007200e0520842a800075240041d0406841c3c003503280d211901c0c00751407a00981d080526910154020400c4160000804a1080340a0a010b020100c241401c8281480d0304200d01d0085411000c03900756941080d500400c90781001404c0b441544180101c6603101042610040108ad0110400c2c0a13103180c3c07080f030500150400c05011440d080d06440064890062140d208915403404038680f42418050280003502d0100641680500122100010000e04407402214800c00c0001c020900c4100d05101b0308046983c150021840d54680318030610715041400c40c148400340d141d070052080b10680c88006e0301407200300701d681070440e819401c000c6d003400d00c4c40380c05500d0203251400420143e07a118400040d0003246000000f21030072200c18000d08512000b9034250009020b00000800c41e00c000300440c8221000c0081c0c070b0307040710000411010780320051801350000c1d40902015016281030b5111 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 422769370 1250 422768120 422768207
    0xf130c0509030115080624011b060614040612050303070522080102030f18070e07031812020d08010e060f010c05100e0c060408120d020f07140c01 64
    0x440e0514000c039002030b095a919115060101c61054005c00400108021680e005030180d0283e00e00500ba520040d0b01804446150134104072452a0300c44091440380c0340f505802e60040d40602141d038036860540181144072100f40e01891402c0c20000e00b1000c107040e0009880e9114016518546491004895540ec400a13590a070b0800c4e03019002c0640400000d14014104074001507140e20b000d1303d0109901d000284042c0d00b090003240e050780000310106103001030341c2c1094040040c075100e103001200149103880e0560300103452949510300340820303d0902d60b0240c4869080310b0038400d81810441c1c96040a108881241150902080c190b07d05100070804502c810705d0300145401d09500c07014603001010017800301d45070342c0d01008542c4442c00e00a00450342c0081e24142c2c60b25151090540c1c0d58401c43e00b10000d0700c2c0c07000c18203c0680400d501215100510301c4070710b0303446a18504088807a040c0809210f5007078418400c8170049075019200b044000200500d010044003035251650901d901c01600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 422770620 1250 422769370 422769377
    0x2070b03040c0b1c050a02070213050c040f08060603100b0604170c04090b0f10051c021504080f010c0c1109070c0606140103051b0415170a0c0e0f130c 66
    0x2c5105910f1001808000b20b400310381c19030154440040708100c9001501160106004200000250f103500181240c2100e80c483c00240940d01c1000c000c0103405940c1081681142040f000038503d0000a0384c940504801c40548150100141404040b2424030030141d402c44018001000004442c06203940402410780c203842d6040907484c001821500309410482d802c00058061181404402c1071980d842850000030f11422410071001a03090351740d0000d041040c1c04140e001c0790464503100007102c440001c403400c031500e864481c500c0c40e881d08041d9104102c95031a0003400344c0710f9841564010703007040d007109900422603003010078080b1517000140190240007210032800300240030340c840c4c1c0e0018000c109040c031030380032494001401d80c2c0c0060851800740c0500641c0844a900080859040f1007207801c04403540e100307088080d1000705d40c2c0b240d0111100400c07002c0214500b0907030030181d0140f185036154005003009004014400886040140d000880c1e40203020b09802c19900c4062244120304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 422771870 1250 422770620 422770643
    0xf04030c080c1c120b1c0606180203092b08070201021c0c030b0102030301232133011406040503070803041a03041a0717040f2102070b0304 61
    0xb40c0d96141040003c0c0e2a051480300e8034030f010708258400c12480e0403503281c0605000c03000340c0c2e0001440b0b0504440681030121036540c0ca2404010703059100c0c00041a4410910303c0c49644044032400940007154a801c0c0e0380208030014116006005801946d9080800032000305003008404950310703034004006009540d400c10400d000800007030b611032103400790120042800d401007000101a5807801c03420070705650050006010303440c90440c030000702c421807075100d074080b4003200b0000b00ca0742e01d1041c2c4024210540c4407202c2c0d80c40f80208040020800e031840085400c40d250b070310304508510003c100803956420034014032032402c126003202d4903618000d04007800c103a141c50009040c9141a4031a0030b95600c0020104041c10180c04080a0b980445811508510f0a621186a800d0b0119400e0500050760b100084085009005504000c218039918500c02c3c0f8080c40d02d0414100414019100c401c2800000f480380031161041011601d81540039040c89446c10035002c0060308090710444d6500d6050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 422773120 1250 422771870 422771887
    0x3070f08040e0f070315062c0603070e0a050f011706040b030f0129010906031503061d0c09090c041e020708030a0b030c1e0d05060a0b03150f04030c08 66
    0x916642e8015a5400700386a018248440301074100c940d25070101c0e01000707090804001c0349400c0303401015240c0340c0a00c8685001c214240e60b55a8008580b80030703500120100521620b5a03100e00f0310a8140c8043d07c4002103103444030100940300d07105004290005580002c505940d0405060503600000060804280f0f40a1680024100303500d0324808070060303540c2c0a56454500d0640140c202d07200041c3c80110750020400c00081c4031000301e004540502da107464442081c54005858407004640110040110000d21800c0b0308581a07040680c41c40740c41040c0d141d01007840c111080c107000302c04a2008120810040c000d020241030070f03080d0f12a01d000101d040b0f01c1600e0850004280ea04e05c5000d8407a03480c54000406000c446101c0652406a0303c5800300c81a0342d1620600103494416000703403911200b4a98000401d4010784400c024000d02401003031150054a0b0f80005400b600c04a00352008041e61071700254125030115031000d0059680c10206010038091400300322580c0c040c022403403412206 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 422774370 1250 422773120 422773139
    0x507260a110f0d0c23040504261c1e062601020d090609031b051e03191d04051005060c1204030b010f090e1f0f0e030d050f0903070f0804 60
    0x1d5002c8807203481201e5041744c6110943c0b0724a850908216030411060a054803400e140d8400d01c5111405d54072801c01c201c080c061003c09841c000310800e00144490900c81d071100028040b10b0360400ca5010010483c40e60f80c4c0d4a83c0904820354040400c00c0402c41602b9a10000c064140700b83d03402c2955081090001001490042c8101140120030115a080e8585801000c00309034141c107070940c0c0031818840d000118045a403c454034040790028180d030214050182c110b20a446070760a5042d49640d08211094101a800860554a00c003002c0e20030100d10501003a144116040006c01d1400b00e07080c0054074001d03016100341c807810703011145d2201294000c580705508c580c10a0711444001d00040000f020510740080103400180028054400c4401c42d05079250141100030199045034030101d21855019840340c4043e0380031010600c0002086032a140c3c40340e01403030f44803240c942403c00048040e001000001e003300d20700b100170b43c503003103254030340c8216041480000c5400800030030000812002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 422775620 1250 422774370 422774393
    0x30f08062409030a080c0d02031c020703030b09040b0a0c02010b0a09020f0403021e2e0e03030913320a0207030e0402192a0b060d0507260a110f0d 64
    0x11540380f59a552120380c080d145000f41041f8048115031040014034004224184100c3c0d40c0f0303060b0380c000743e100c81c02464284c01a01d00d0510003500b1411001c01c01040c4484481d52500628801c41c00300f00350300301e54104909a410302c010140e00028002d07800c00ca1100d09500800b900c4070030118060403d501ca5000401814199440310044800740c400c00c80d1500e0301001101450940204801d120b001246520140e086012070304014445410102409170b1000e00c01c0750383c003000040c02c0c260300c06410141c2c40000d04070b464a94005080701161001002d031088440030701900c0310307114840540c2c1d440c040f00c4040d6025900446c100b0489215420341510759001424481e1100504e4a51b01c40c03105000034003a884100405401000b01c482981c50341c074465002e5465142c100d4000001c0d43d60300d40114020b00e4404100411074480c049000542c001803090a082070f661129000a020500c401d0301175031900105800342c124890303107000d40700c945040c1d0004010354130081d00001c4507020640310321030050b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 422776870 1250 422775620 422775623
    0x250c2a0b0c12070c0504200c07091a0102031c0902030703030f082401030b191202121c0e0409052a04090b07030905101107030f08062409030a 62
    0x208010692500c02e10220065098404900b802c01c4003a49490710341c00d4245c480d103400b40b0358422600700501020002e41225175426448640d54040e0010b0455031600c041c4140b410440c5050705000200b43e00139041c90201c10140e0046081c12058419000110311a00c240d1003003d690750103070001a01d0030311034580194003a071550701c00d02e56112006807147c14002c2c0014000141031090301c00d16111403070a42c15906081c40d0010340c5454075400b04845c03180c4149882071007800c4250006106003021081e40c000c0d032091300c07807054103104451207da031340c40c109016560340342c1c4880c0410156841441144600100200301044204c0340d51a0ba905000c945010498034410f044c2d400c00b555a0b0341c0740c141e01c00c11f405031802c01c400e11264684040700d104c09040101055190014001800b0701041104c0b20440400c50402901c1000400281560702181046021555a00381000c242e40103041d4a84104405000c1c40a64555121450707074034200e103082d00c0c05850081c44903150780c1d18100719880c100d130b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 422778120 1250 422776870 422776889
    0x318050a030816021c080c1303110418031d0f0d050124050d020603070302071a0103031205091e070b040609032003030a030b0303040312030203250c2a 66
    0x90403d030003c211118446050b02e010f55001044e0500a200f00c01821142201145400721144d01c0d4600c48501a00c10000c2015518110b03140200a0000e114a0800c10201c2100c1c1003041c40d000348941004810304901c00f5003c80c08e20781d480b505903803407915109001d160040001c3c542860180004502d4420288262401e80d034440f40300200f4001c440402500c3c0f03c0500110045503d807a002501a00e4401c00c000d0003403d0110129110718001e40540e8141607000d0348400c81e542010602c111204001d01c01540010800a400c0850480510070f0501800158000e4886540780b01c04c0c2d11400c01199040c0c071001e1040082c000780c0c12040320058400b0b042680d81e20001c04e0300c0d40c1082c11050000c0b1860007440a81c0840441803960000100c1d01c40c106241000316180c41d03803100280c218000c50f407000e441c0100c03284842018070b40c59070066200e01c490000c8001c5181e0315150442c082001419010045101e45100c6808134803031300240b00c01c80b203072011045001d800b05850820318044507070100c1d440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 422779370 1250 422778120 422778137
    0x304080706110415050f0f070f06050a050105130905120a03090b090d090e04060216030801091514060906041a03061002030c070504020f07060908030a060506190318050a03 75
    0x8010907402000c0401c0b0060048609190511080b100c5402c8441d40d650180940000c240004100c03c40598004e5030010f5802611405141040925442c001100321145441c1c030b00020020500352140fa030580344013503e00e203032151205818400a241da00c03030549a80c8101244e00c4901628500200482080c642d00030440d000a481c1424a6150140c40c408070341e0032a0916a00786541325000d6000c40308011180d035103680751400c00c03034000e12811040c503540c42601d9581106050704280000d0489801420402030142d110f0b0018010f04840c0c01110300300b03540c59000b04d030145014406003441a00c010041850569180200200415420362402c410368000c001c1104620b07000440d0409040389001643c1340c68040760845440f900940a041e21540d40490724900c0b10205605641105601c1001007010411340e09120542e50021580d40c000d4a09200010a81e400c0080684020b03008080c1c581741c4138144408180c000d0031003102650b00105c2103000d803401141c0d0820480c400c141c0a501c3e038500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 422780620 1250 422779370 422779373
    0x1091b061205091c0c0602030405060f090f071802091c120801081203180d120c050405150f0c1516030612060c050c0d17070206280603060203040807 65
    0xd14140d550741c01040c52034081084449100419600c01100c076030115080404660142078078003955089020305014404802c000811800040300d030b005500710182c080340b65441010b2655202d18220070f000980d0040a0304201c0315010001104032106070400150500031014086101445035016010b00344a01c2100301041c864115074004442115103414007056042030740659907444801022000702c0c40000015400440c0e203145a1800e00e02e000648070780765201e03400140a4943d1a40c4255007a1500f1801c04c0c1060140303040b1000c580d006050340c1c25840c003104242c00d0681250341c080c10740203410041410424420702c646101c2000c5000c110310749040132208228a01d0070070204109061070250140049036000e41c04000065000101081280360a04122250701a15000003032600c20320054414080c0c0045a01000c803c840c503001074540e4556100301d13501c8070300303985a4940300c0401c42c40c40c0194019000740a400c3c9158200400e001c0d54958400c400c990007254103841221002c00c2c480c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 422781870 1250 422780620 422780627
    0xf0c020709050f010509041101050f0a1706030601080d0c050f06010e010e061c241505091005060304080c12030403031a0409080a0e24031009180b06010201091b06 71
    0xb50880f03003c450001c419810300000c9410460060009001c0100e03900d0762500c01e1b0321a100f25410803094403003250301c920b01c030b50019041c20303281d80009840d03000490000b555818005030290480b56100001d00341c0e0480c000c000d50b211b0044003020350345c40c0118466100700c0c803010095540203044058499603a503150150b0900511400703001c540c8a56270114080711408081c040f0f0210b4240c1000f1940300c030407645c1c4d01c40b80d10109082220843c150a100300420340016078022441210f0050300c1c15031840d507840d000c40c88044424003074540c1c4040140003007008a4444c001401c20301a074134089415645100b0f00d403004e80d8200300e40890002ea101c41d40d181400503100318404100c41c0a4074144212800e665500015014005070a07041141081112940d5606e0f507119442c03140c881c042d8409034106c149050301050344200c0e00c80c902000582000100100f8610420341050070021046000015a6403914520390002c2c1200b8119034841d00c0b000c4c0400c0140003d10b6140010008000c407480c130b070a5018 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 422783120 1250 422781870 422781881
    0x3190504032a0f030f03030b0621090f0c0901120212010510050a0902091008100b07050f0606010c2a05040f1d031c020c01060b0d0917160b06040f0c020709 68
    0xc4000644480f00708009a034041222841940c14103002c90318101250101e0103034000c004e554009424400349034080c00200790000c0380100c1d980801d4620150390990890b540d62107403c203503500715923190010040380004004540607184020b100c0c100010000e000e03103094034001d51303141d407615045e10020001b070302d04001418028901c0f01003c2d41000100000209920510320200c01846100300001d51102e08125049010b0900d00310120749404560a00f80da88840202c6154400e00c180c6011034581c0d0f0080e1980c280803644500c2600030300e90036000c1c0e40610350340c144c3c14120082c403165000ca41a03456015911020a03444400500002e2065000450410300e0262418981040045103004071700c9010301c50082800c0007002d6600c00e140c0301c3d10340c0102826440120403500100d49514411059005049100d0158160300c2c42c0c0c4c12503104040389485502c0b01d408450f4904048803000039000e500c0c0e254407820040c00010034205209600302921000034000006801a0400340b02c0c410580c03055 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 422784370 1250 422783120 422783129
    0x72a080712050303060f040209031b040f0e0604110a0e090d0306060302040b07020d0c0806010f081c080a1508030c030a020f0c03150a020f040e0a1802010203190504032a 74
    0x1105501001c0d1121a1039204c09021103009038925071030b601c03054071a90111050501e0107011100e60044183c0800300b8240c0007415244510305001d2004904850750046070140e40b4600094045915196181000510001140c1d60403181d030400005103140400c7c001445519a01c0c0642100c026251004084420541144e82818070510080c00b000d0281005d881c01343d681a51421080702660510044811255000d840d19114440020403080d02e504150ba044402d80700032078542003006000e00c009000091080c8002070700513400100600b0750350b00308054411800701d441600680721840c080c1154046806003900d036200103a00c80810398108003040c0f40c3d13040701000e080352481150019480706000000068045024804524100c1c8690304490f41c0301054402c032130f03a55a43d0a000c10000c001120202200741c0f030241d0b03112040f05c42046194240e0f038143d019500d083c02c0c2c10704042402101101800c20010b0a000c08000282507041e071401c400d0a8010481130b24000841540b01039441e40c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 422785620 1250 422784370 422784389
    0x602070210082703070803100302032b031e06060305070e01030905030a0c0c18140a090f08030a1808030f01060c0305120a020d0c0801060e01091a072a0807 68
    0x1004400c3c550b00403c1e03200e20901204003031401482c003200624502410002504c1c4500020500000b00d1184c400d041c222480ad805607140d082c0d461070700c0d01c014034045c0c0c2c03000c034000f808200300c3d110303d4425800704101c030070810039140b48248485103010072101c039600a580403035990001d001d01190442140409050246030a102c10b040386e80d52242c0303a02582a04000b03119400080000b0000410350280c0544a80010547c0c80c1507008400c001070594040c10615407000e18020410a40e540e0117030640894010350710704582d00403681d81121030f92008049107011070f60780d14007000303c100c09100742d204140600c00075a140c3c11325900341c151304c54042c0d11030418402e40c4408000080c0d002010361746010b2800c3c200d003101e40d035103020110191103003032960038a00d45018041d039289034009208906039501981d0346040005044010b59402c00d060050f800e2404c0103c001c0c44802c513403a0001c00c5840d124216140000c6001d032810b810907480d0071090b0400d202e0b80041404030040c10808003006042521 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 422786870 1250 422785620 422785637
    0x212030f04051302040312170703020c0a0f020102190c030b13120302071113020a09060305060d060b030102091c0521030604240b0d061a090d110405040602070210 71
    0x9244039503120764810306001c0c1518280c850460300c80350b03050782c0085401c60760a02e43c01840030801400d142c21501280003d42c5a071001c510061702c0ac1c8255008160030400400019403142c84503031484c510b40d2412411480b48148800f921701c4211150054588035002002c2e40b1821b5141c0704c003554600400c0c1020a5424400358008035002e80c803980c0d0354070400e0800503559041030030030419040c402004250070002c1350710382c41d4146000b0350050600704c01c1c1c0c3e80d50400258454001b101540d02c2500c1d21903000c2c0040c3c02d01c03404540b842c6d100034012080100011300c0c0c440d180300450b291148019000008000900625060000512602210080f426080c82c1e4101002d0b01507421800301800550046030380da5503280601080700902185110046681c411941d80e94580e82c0655000b90103110140e800c00000241100c90b8a0000001074400d0401604200c5000c00f4400318003c4101c01f510b40c0c1210b2105030016448501c690b40c0200d01580b80541e58000340e0051090ba2407036040180e08200c0300d43d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 422788120 1250 422786870 422786887
    0x30c010b2106010608090a02030d0806040506091603020a18081c090e01030b15040f0506040b0d150c1806180509090d030c140c07050a2418080a050a021203 68
    0x440c0c0e503415111030741025031060f1031b0658050302d4450000300083d090300c55012907240080e0415003161280000300d6007403103ea40ca83c011b000c2042d209443d02c41c8030000120094480d03500035000f4202160581c50080d4101e11402c00004220510f03038003c01d46600300c00010240f0140d0039030560440309160034210781036460443d040c038000c0414403010f013981e0b91000214190003111640b40f010800000c200b03004101e04d0641c02c0c001440b0503101644524600031094500d4200510f210b60140e0300812009214100040440c015011405e002020046051031b1583d0680e4042c0515020380305650317403030240307200105140303013000019000710f03120b07101003820003001c0d4100040645a105280c0741c0450302500c90b06082d81c00c07030700d805000e65040002003100240510009a00d904944040702e46404090352801c04201c0366001d500205071520700c03500600718490003160740200101404400030141e83e941e615981c03c000502c0c600329142d4011207071000641c9410081c0c20320750317a0300708041c1d40b612029 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 422789370 1250 422788120 422788123
    0x103060b0301140f060c15101512090302120d060603060f0b0a0e0a0f030b0406060501050708070b0c070c15031a100806040b040509030301030302011104030209040809040e030c010b21 80
    0x40f105103078410024460828626200c3c0c00580741c41441d0341c4200c6041e1034514050000e60304041b50604551000312130300140003044405162841d1f10b690311000c08201070704004001501c5080c00a03415481405099446245204020800790222040c0024000d00340301d0010705645055100d4036401e141d03404140700500e5514204c80c0080440c0c1048000483c1880100d58a041c80354024a0407550050b400405c0c4044849828030076441140c0c00c005058030b480041d03404d4014040003901e003502c24402000003d042c86070558001690402443c02d0811603a070742c80819450740c1051145018610000380541c0c1c2501030f080e100080d80c00152004c013005404540c0003505041590204440c09010031407984403540004000c1d0005441404649000e0140360759a03407080c03004078019880c0503009a840b030f00d10005e9509695004207640290703100c985844035541c1109400503405a51150060210f40c001c00084c03200c0c141030400031400751a40b43c100100904048035030122801c00d0308001808220 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 422790620 1250 422789370 422789399
    0xd030606030614040f11040f060e040212190902041b03050f072703080a0203030105150f030402040b0402160c0611070b030a0c17010906090e010218011b050a110103060b0301 76
    0xf402c0c0d40c005004540f80800c040608100341d286040d0b00000100464005202c20110043c1c80701a2140402c9000d0740090000300e10901080b05140100240401e5079885070200d101c1c3c05261104002ca20200680c00180c225aa00c0e0100d00d241d900c604030141d2110703098000e040e409564030320031b880325141150001d0300b00d1000356250740400c2d050b0b07001801914251a0128055904507040b1506caaa03103400196580d8028020b407441081100449642d00040004441001300d4030039109040d03031510b60910016024003901c3c140d10a0302404440c6000f000c805400c5040d5008980702c845161507d00040c00f012010301007204aa0040c0d10248414185d8030304880d0092a030322800101e905030801c0450300028080b00c0d14090100c0c0a0000441452a80000d41998841441080741c00403d0900500700d105a58900000e240d032645040440c0d8081c541080310f8207500d1a480c04440050394407181001194103040f550541c0000b00d10342a564035100c0c2034042c140b6600d400740303076505144421070141c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 422791870 1250 422790620 422790659
    0x151810050405130b16140f130f03030507060203060d0f21030e07140a030b0c04051306031208070905040608060a0506090103050714060f0a020604170f0a030f1103090d0306060306 78
    0x2200050103100f5103115030190700c00b00c00490b840944a00e100c140c0f05480e0381c0680d212300e00d5031450510200304402c40708480000c0380d42c581c1703456161084d1a62110040c0d000141010303800070800700c00e1000701b0341c502141501a842581440c101501c043d2040044141a14541c8101450940d1003521008005500d4080e6180082142c1812421400140039142507400082203220610b0a00004520760320280c41902c904542500b0b85151120746601101c070b50344000382015907090351020000340110501a0814a070b8507040000a0300d40c004102500d1050b404503515610020030407080446911039580c118030122409682d6515684030380d80e0b104840e00401440200e00104003515640d401c0c2151205e1401e20000d50703d030046c003007003e0b458050031641034076028410003070303510a03c16840440b01c0104507032a80c27500b00441c090044004000710482c0e68055940d40c0a00c0f102e002900b03028501c0344c40384400400380c0f010388100c000c3c117503100c0d41d010701d0506007001d81c01e200000ba100c82641c4a01d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 422793120 1250 422791870 422791891
    0x101724060f0d020406050d030c060e060403050403080c0f0d110723090a180f03120908041701180c03031403010303050412050307021008090d050c06151810050405130b 73
    0x1210f0000800520b01eaa0000b0741c0f000c1c1c544410410950441e4203100a0b0380141c80c1000400d0900801c580c861200b100c000380051400c1006200146101c0301a085103040302003224840c1d400b2000c4130785800700444030507000c03440101c00d00141010400800014008944994210b18000000110a080b804040340c1c41400d40200007080140d41d41d203e520b40c00d1000c004250050790508014051503c820070030740000740c000c00d10600c840c0701d5004603402c80d688903911030314141c50710700d00380c0415500249004440d500c4200308411060030450f03141800d4001d04250113418650714024161541d056178007072403941d0a00042011a820905031011501440c0c100c40ca0078219150950851041e03607402940070fa160b004110419a2043ea028402e0003103e00700d60001051102c01d582d2030003145880c1003154040b0300000d420104184450107034841c05005140e00c0301c005d111015486008036074002d41002001400c0080c1d24103406001d8218100c80c103003000e001c0c45904c450800180003070080707004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 422794370 1250 422793120 422793139
    0xa0513020a0203210a230f0c0d060e15010c0b041e0b130611121504021207030b01030b12030904091110050904050a05010b12101724060f 60
    0x50700d0092007240d103407032964505420700b5070203207a001a6102c07003510503000c01864500e541e246868a4035000699040145c1041869640c440d101011900020701c0346a401c0d0084c89564000500783c000c0e40b020304004000c0c030105180185d40c4a50b40c18991000d039042111825080010803003101a07150803d03003004401d4034180c0714007040343c1000c41c180740040103646660108410402a204101c0100c0d2190505000c50a0b010342160745034051040c04100b065040004aa14045800c54038900c611010300098200400388032400e021400c11142440826151242c1c0344040d070741481030340003800c81110007240c80c00c0351254050340e9000742d03143c1c5402203507129a0101407094004440e2019140102050030754194000020072981100d107076140114100400304800301030358000d15050300c3d40e05c0345031810181300d400301e01d0003640083c0841d580c0c0403581d84081101100440c045520b014140300601d8800c00100c6600c6810b207400381ca00e00c280743c0500900081d44e49015a007484280121144a90b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 422795620 1250 422794370 422794387
    0x60f030903070c0e0f0106181412070f030b01050a180c0212044218050a06170f222d0507090b031005150a08010e010b0a051302 56
    0xa10b1007400070140031010901030000d020300c141000641300300783d00644000c1690369910103640f0400028541b48070460881c0b400e000c0101c8a10000c9140c1030010078aa0350002d1502c1a203050030b11a030400000f116403c0f509000740818101e01ca40100000c4e0356603800740c0c3c580200c05080010100c201c01469480d0a044444a4070812800e9180140c84074481c0c1d407282c0c0c80f00315200b006400422002910b650341c1203000e0480c0503034500c240396040c0c2d0f0035603943d04075a1a400c441d02c40441015040c0c58042a00c0858551104118180070b020b50381c803002c064548030b89036112f0300c4100601251a008007442000140c0d070f007030f00d483c03c5094440313210385000200c17910701100311a490341003240e61101c101c005101c0c0c90000c0540310300603d006100355441c403074461341c2d081c09075250b0903591a015032111107121002206070703201c0d9038003044415021600d0b0180000103034140d00543d01c148003581d128160b80400780828496558100c90480d0114007091424021946407420141c13000c1404e940451200b1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 422796870 1250 422795620 422795623
    0x18091e010b12040b0c09030d030b040c14040603050601050d0c080a0e210a0201060e0c03100b0403050a02150d09050c0307050a0f05100324030c09021c052a040302040e0a02060f0309 79
    0xa00d00ba10040903912300880401c40100103001c0c10360554440e03420700c840d28070401c0c064040880841c00145031185803601b0124194017402014081034108541001120010220752245104400296aa140f011b00703110076030710250340c00411000da00d90085440c480c000040a003122003501c0c40804450384440c1928416030040c20b807588483c0c01085108200144181c8201c01544200c1c4038600c0094902e440c0c0c3d030340f00725a0086000080c62580884071582c09403600c10700356107444504010031898541082411000c0d117901500c200c03210745c4541d20200c1103140078000780c00a44001d40301e80c26428505032900074190107a101d010702800780c200000394030a101c0d801041c20381000d400e0a010034110003440014018151205550110b004c080114854001d80200c0e50310016440581d03440d0b104842552004000203092030f072002038072218007d440c0001d5424800c1c0740d480c00070050f07182d51441c0180815554040e0310411150407405a9000580c6ea00c4c1c20390302502807842e40c0b26200d654002446 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 422798120 1250 422796870 422796877
    0xe06040b0d050703180c18090c0b030415060312110c010c11030f061e0705031005040c02011518050f01150f030b13020a1701051518091e010b12040b0c 66
    0x45c00b4403014540100500424440703810440e5410356554408800083c48107045a095500040500e0342d490810410011754402560304240512280c00c0504100158003007218140d510840311143c0d041300082840d40c001040b40800602d0034040c103240d80b14500001d00620034298010004141c400c0d4a1000b910100b09026424004400302d5111b400c15000346440e590a48004505180c20000001c3c121441002a2030140404500781100103041c041080b024024020080046650340c0c0c030689160400800541c0080004180c1c12160b140c031070ba0342c0000e035100140041c41c1c4850b084010000c0c050200008030103c0010702e440c0e15903001e161011000f402d050902c00c0e51050182c1c41c0c65001003026030041911440b0b6440b800101c403030105845003210780034443c550b440742c104101e544000d0f00c0c0c400288440010100028512030301d0400042c00300506071400203021011086030b8810602144501d80980400480c5a003416254101795810100090008244241d44808581043c074048280e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 422799370 1250 422798120 422798141
    0x12140903100e102913050a0209040b0406030b0402060c070b040603050f1e040206030c0f07060b090106170c07060204090504150507110714011808010b010e06040b0d050703 75
    0x2540d19201d280d49506000d0000e88042040c58060700d20780c0c00550710b081c85074190400c3e02030020341c0d5031900c11462043c030100d20111250021020b900d2262a0095845098401e95120301c00684405003141440119080c20403041e0285182210a10100b0342d207a52103503021341e044440da5511a0a00003280c04c0440661042035406000300b0701040844c0c25070002c0e449048032154110b529500c040181054442c81a5103941c50403100c3c000c01c001d414440019a0710a03203250a03249001e0952000c001154410481030b59210350700c50740300810703140441c078490041005141084004148c200c0c0c00f6134500d80500b4803080c4a00004180081000c07603010384000700b030000420406032900f803d2880c1d012120fa90080a118601000610420300139100100800344060003062954100640b1a6140c50003402d03e90600014994215210042c2c6562801808200700080341c2c0400c0c0794005020480b0500d08540310b03c030203201c2481024600d034165141031004c0480032445464a00c8154000c2c04d49210 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 422800620 1250 422799370 422799373
    0x1e051b030a2f03040b060f221b02060705090f06030c0c0c011e11010e0a050a0b252f0c0a0e071719020d0507020f0a12140903 55
    0x300308469016a00c4154450001d07554200e18802d40301d20700d01c8110200c07081e01c420100a001040c00b0410400c07000368800d0003c1c140100b40c501e50303000104800002451041440110070341010310b0080c60186c0480c41100d140303862182100c185003e52211340c010201c0b001c0141c0880c88022a59400c0c11401c83c841000d80881d580e07090501c40c0112551084104003094420000b00c040c0d0765105914002c3c1884c0980d06985110300403400c01c580c0344046400d0314a0a649410410380d8001c4184030681c2c0c850300c214000c0442405500e012a0103d20041520303001c10045001c56404200540603007050713520b586082c2c1c20160a50143c01400303030031100200c480f0750000c42004003810002030039005510046410800842d07441e940301480c1308080340c3e500b001448000402c00200c5680c16490f07001800c41002521181a485441c1c01703e81241d0710000350726458405001041d034041c00f01c6800d54040101a19044900d0344440110b030032070202c4101044103042a010b810310400094803041e200050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 422801870 1250 422800620 422800627
    0x2b0f081003061b1803240b100c140601140d08120c04061205040f120c0501110304030306120201080403050c0321041205041d0402040b060a0804050d031e051b 69
    0x344000c00b02600b9003c076501103000d021051090b880f00f8110f20045941c002d280d140c0703c00440c0300301040042e280b80c940c5901911040905004d541e40c07500341035050f030030799500d941e000894141000ea91170385010340c04503a04164014001d00303c008141341e172541700984503640c0e01c0e0f845e850b080b415072084607e404400b82c6500240413500717450400a000312030091b87c1d10714808d810090a0307011200241d4004003a01484130b5910001038901d0390240106090b030034008035010f000e0300d0f05070960300410940c00c4036480000405c010190580310720340280039101200b078042c0c0150350020308116000741c009814407501040e01c0d001741c4000c104442d910002c1c5421040b06520320714440340e041d88280d8003160002e40108810144a20401c1958219000c0000421051032900c4140120f03c0300039000788d030410384074290040a038403242c0003130803000020780d51a441440c1505046003040501068101003500b030150082500b12a2200321400c0d007040540015503442c1c41d003144111500e9031480411040c00031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 422803120 1250 422801870 422801891
    0x1a15030f07090f02040e0105040902030f060c0d1407020d1206050d0b0a05010803073804080702010e0f21030c0706172206090c0302030f2b0f08100306 66
    0x118100c800c42d14002014050401081c492100b680210f009000c01c0c070340104010402850290459520036002405444040070100301403414418200c4241c0340380b250008201d04030300158410101110100f0350a80300700d00b880340009403a400c201c40750300d00308035110405495940c10703580000020103008103c0207212010349054450100110303104c81c0c143c3d00e0040001400c0034040120b44221f6804007070b2030a180c4080000503010b03c0300d05040405811022261344200750000f484a02540c00340b00900d840d05a06c3c8001003d0b01008064180100242d51440101d910344081c40d40c2008118403600241e0609030302d0507850350181d84100308292182840000e0f0301034018203a1041c0307480c890740c40d09499071924041c8040d25000c4500182da400a8045000031900d50340c0810642e41c850880300758201d54030740010f03103403242a0b9400603064115181c00509107000c1207008411940c4140500741072000010b014007811401c411901c24459144002040b40f94015a00c0001d180d002100b0005502302 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 422804370 1250 422803120 422803123
    0x804020a05040c2c030a02270a0f0b031f020a0c02100f09120803010905071806052d090d030519020106051804050d0318020d0b0a0510031a15030f 64
    0x91030403d5007104c0c181d000851883c040340c0a00114244064014500080103a00b440561003c0b410300078880003446500041c07010f180b03e61b0600829404401069032138000e092202100e21120049201c0d074800c16080551043c41d589903256121107440050700d48980302c10940c1c08442c82c2c24002e50200d102c19050903441d41014400c0c03030200072650343c00002c5440f210b552075100e461503809016008240010420440c040d008603070301980918050200418420b044c0550980703540040000c1007001c660103400c2c1c0500c10403919200190011445038000c60442c003205441201c0d07141d4000c40d001a102c030141801501141e01c0c441b0b464654581340421440000e0013440c0a004583c494a00181943c4030924844100740c000c0e07070400058101c54412160030380080c80c4065203140300c040700e060b8280241c1c1e9010118901c03030380200d540c0001440c001707600200701d480c02015154182010b0304148041aa40038110107000100702c000b622903100c0c5518180c1d8440075080d8581e041c401c100072034184200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 422805620 1250 422804370 422804387
    0xd2001140a05090a1a180607170703060b0f03070309021c05011d03090d1b0303021e0111120402010c020a03150c02030405030d050f070804080f0d0314070804020a05040c 74
    0x1201c0410449600c030059000e03224248114081d0640c1c100c54501d0300d0b0300d02c01c80c16040d0004501b01c1041c0032a41e03000b031058103006088854101045060403111141c510349828264041c44501d4204007003424100714609a00a04120482c11680400041c002c0d03802640107802042c0c0003003281807560045154043c41c6404008111003c0d420000304002c00d00102091a807824007a070041c50401c0700b078006108030031400850558004441d0304d1500e20143c4001240c20145020f903000e8201045500310042d40409050198000c0d07a240056401d5049048815148980c0c981003c03070200d610303140012a0035496101c806913014007070090000422419a8080f2041c2c400c0354020b02424005c200181c2e101c1c02284502601030700b1441007140350303500c95402030078459008510079003050056107465400c0d401c41e40005a65502c070f409401c22400e010809048158110314083c81030503e0b1000c0c1c01e4103078201901d41030a00001001050031551582030200180c10050401c000c40002440c00615201c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 422806870 1250 422805620 422805631
    0x303070c0807050f01140d1b0c02090c0f030115020705130501051903050d0309051c0324060f0e01021906060f05030601080a02120a0b0c120703020a020d200114 70
    0x4203840c40041d030703404c10340c40c281540d410507110700c5d121707020402c4e0480c0944d05c034038142d0080907a5101240790542098110418002c04c0f562040e800c02d00724814000c3c03165025081c400c406105000c0031000106000c03c42c5c0c1900c040000b40001c5000780002a0303d030003929002558000300182d0348404c0215030394040e034100d410803100d40c85000d0140f8081400806c140c00050300c0c40e006107131214a214002d070080f840356441603003119070a100200c01d000d517124030740300201c0001b41c517580707844100350f456115600103117801201a60124604000604499100d5000c0000e02000034110202c81c0c0c024003000b1842e00c5840d4034000c0d0200b04d0714200000b01040d0249100218143d0008190303400d0000c3c4450680e107008000b0200084c46400304449115062080c03071103407044030040000120901c029900070f14422000c15141c040301000141002070040603001014810f009425040d980010031f5a504445400c0c86000c4900303020311400012032003910191150300b4010186200002c1511091142 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 422808120 1250 422806870 422806873
    0x18050403030c050c0d0315030b0c0306030705060f030f0403050f07150f020a05030118090218090d1b0b0703060906120606080c010f30020309010e160603020c010b0303070c08 76
    0x34032828010380381d1340103c064400c0c00c2d030300ca440120400c9000781d114850b4a00f8841c2c00601d070700c1e9203550740482c49000300c40005041c4c40c003005024042c1010000040941811145075040142d01256202d840c040100f041d40340c000d420000c1350074540a00121440d0020550720310750b40b4609e6040003603041520f65030744031419181501f42c414001d194425035a11008959460f455079191800606c2550101d207461456156140b41c10001030343d8020f12240000030850b00a80c080c68030440e070600f0600d00341c2d5403506111004003807400700c04283ca058291541d20001614258407104800c034001e1205070080c0e44035600d090b0b008165140c091001c94000c3c0e00c555014007220740c0711140035440c0c0c00160003a07804241d20729000614580295040d48814001c00440c1c102842c64140c60b99880c1f680b00811200c280c1d0000a0001000d400c4c0100030b40b1007030040c0200b02c0b100384600b071080041101d1040e5020554042012031408100f9000031342c82c9100101140d4a44001d420486074080142c85140c503d03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 422809370 1250 422808120 422808131
    0x3020c070f0503070608100f0e102102060304050a0b130506010b0a0206010b030403050708030c04090b0f01050910020c090103030824011209020409050a1b0501050405030c06090a1805040303 83
    0x391079408518058075030250140120500c0c0060a0f10480742c05004001d22120110010540510f1707413444070000c0c030a032030f4414002d003014040c8009106039500710512190024402c2c4221700b040722016000194190740041ea13a55071802c0c05404c050410f00018044050081070001b01992000d442c13070b0171030040c1c041e50180c2c0d0f42c07540c49190922034505040d015070026401042540304000203190300c1802420b0040c6080560b07681c1c070900b43e004070b03056600d10304089410320200395140b0070040c20b03281c1510704440440c21400080c129009000e4618030401d90114401c8540307100380045080800054555281961603140160069100b16400700d14504000c00301280c040c0c03c820840c0140c034041e102c11442010405154010b060b0744107082e47c0294031004440c0002d40304201c05103d45000e040710054120201030b001e41007008951029040140901051260ba5808504084080003c4901503030310030888022800d00511548030007280d8032844440c001c580b180d0b42083d03202c0c900c00d80c0c08004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 422810620 1250 422809370 422809379
    0x603050d02070e04050d0305060102030c010207050d030608030a090b0904230f0c0a1b2a150509030303060f04060308030403020a02191206110c0d0309140106060c0609030e090703020c07 81
    0x1403e00701118060704603400360711040d654034001c0d4881034000c0c1041c4103580c5892a41c104003400d90f030190000302c805500080f00203a00d2581407294502800c4000c000d0b61911002c94801800b2078410700404001e4040080d010718282c1e074a40c800c40710b02e900700302c0c403881084420010340d4031800304443c1d90380380042c00c10000318029140d0080301c0c600d18941e11500080003d0490034070b000000440b0483d424000782030406000741c6a2502c2c0c00001426200070710300c060400c18503545a81c41e10211074140241806043c0842e84c0c08000d591707200304160340307440d100c3c2440c0340064003400031540f018203191030000500c0305040d40840e480354142d00a580258200c070305c102210b05184000d10405c860741100640150010309650480305011040c83c46203410400e0800509003016180d40d000408240e885414070100a0100000d040c983c009800170024940741c041c02030103a0315003c0000b0b150990b81d40300141014003e41c821038100c88007500713002080c600b026019009500500440c2d0003032051a10025 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 422811870 1250 422810620 422810639
    0x41a04050a20370207080303010b0d0b03071518120b010302010804030e0301051003060f0c020a1211031b0c03010b010f0f0e0d0309061103090607150b040603050d0207 73
    0xa20b80d1912042c03800c03600e407442d0000e201600b164100c01010741d8121203400e07002e42281006903003001001c0394151030011915001e807421405900c042041d030002c0c0f00403c01024a4015600e25211f00400460b20300c1d14000001d041846907003280e070b091120316035042005540044581d09203840081c501346907075101c84262543e0444140001e201040b036400504c01548620040c0d43c02910a0500041d05c04429000a0031b44c1c03021985100c0503120002c0070014440140940c010000f01c80204100380d4054040007901da880031200a0305c20b0b0044590316032500d205070740303640d81c00c0c61a800b5a074403034044810141461181b0540d041081c40703802003a50031841c06204401c50450f0584171100d44405550090714080384072600e04092001d4590403e03001c0d15042042180705200307940c2c9001040c18650b024108848110881425a00900c00c1c40100d0703e42004540c00180c201d104440d890388649941006444441c4926800c5030070400000200200041d02e000260706a809440c03584d0340360400e54 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 422813120 1250 422811870 422811881
    0xd0c08010e0109110720130b031015060516080c01061a0306100e0a030f060b090906070504030602071103011d0c06091c1403160203010605010801060807120b041a04050a 74
    0x41045138041001c4400a42c00c031888040c40001480198200c103c01c600044004020308000c0d6000b80c1c032040318848924081c01412104034080c0c07005c100707a00307031200d41f01d0742a00d0b940035041c24000d00007480b09802d00640b4800002950002c0003580d900040c4500323a01030b2840c0c2c41990708a2202c030682d08545101881602d01c140d0000c0c025942c213100201d000c03644d4030051051070341c00100b400307804404070701007550000d60603004001c04a10708601c001400b000e00d90060045035590001c03c14080320700c0e4000c04a40c101c9030008000358641ca000d08201050104612400c0c1d030542c130b45402d090300c000348203041c160041143d4099844e0303202c2c480e040c8481403159503506070740822418031285c0200c1d6441d101c00c3c5030b41e000d2680352004070f202020981c45c552080242e100e820340104581011407400340940c0c00a06030a1920380000c1d450300c1c901038111100505444280701440c003c00c0b1640d88250b001813406400104244013050304200800d0a0b0304004401c1e40c0250704040005503c2402c5020320b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 422814370 1250 422813120 422813141
    0x30603030210050408250b06100804080306030102120720060c1b121c060f0e041e0209012706030f080c070b030c030a1a03061602030d0c08010e0109 65
    0x10b071520740307035060019004100c02031048840440074480030100d010350402071500b003182600190019526800c000e2000b6030004c1c5928171032608400d00413000f0b40d115a01582082d80302195640b2602c6810000740079005d0682664406c1090104002080ba409041402a01510403040b10b90f50201703502701ea2a840100d41c0d0202744042080f00201aa41808221035a03040c2d250944824114000d010603e9902100710b461000104800e40c1c4008040c9200b0000103210f0220800d400915110399400c10820013040507100f40e1a120001084551502200c500513a000301140c280350703141c0000d8040100044085109048041c041c6294001075110359429a504514403440600d459a42c10705e0303030340c00300706211424001e0100029070326001c1c1014600810545d10a1074891502051034030032207401210003600d44c00c541000c2c0040d42c40109031103030446042c02001c1c03481400520203900c0d500c204100c42040f2890100c5103142d0380e80c454034650503929480c00300e60072039980d05607040c00c1c1c5150951 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 422815620 1250 422814370 422814373
    0x106170106141318020a110105010f03020d080c0723040902030601121718041a13150b0304050d1403100b0d0603080a0c0210182303070f080705010306030302 69
    0x600c1218041d403a0281440d42c0d12140c51062032034039884903000f003003c00300340d0745100d9170040b520001d02038004100444d07100b04800200025031503c001495a0300b40c0784006802581180d09a0080c4104107003200c1f010f00c0400100c0d040b941d903135140c0c46401d0300017251103007081a21150b441034a1400d0b008202806070010300600a60b4205074807951451800030088804a1000c40c0321a0044880405011581480e00c00c00100800040612041c0d80c10380400707902c0000b0102c0d840486c0e07590705141962245c202080007400708021490341841d01c1864002507000c04000c0300708410010b0005103035010101d6560784038400c0b400c003031031003605010544100345007031002d0009120346d00545010b04212505200b0100f01c440c1d403a2075000f00ca0b403124404c0c000085038800400e055040094511603d13071002e02e0172070181c1c410000c0c50400408140034040c1403940340d8001200c2d11480c0f8500340da602c40010207442c002d6035110480090b07451188500c080500034060009070544c0244203d10880b40c1540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 422816870 1250 422815620 422815637
    0xe0123090d0509061b1e011a13021b0c030607030b03030d110f0d0506041104080303070c050703020a060f0207081c05030603070b2b0209090f060d050105090d120b03030a08100308070b0106170106 85
    0x800b00043d049461000000d02035082c0b240320bc1803030300c0c030240403801c01242028003001014903060504045006186005150a1458a42e103503240041190360000002c60b0015201500d00060007503482580854000188007180b1030300b117000c483d48482c1c00b410b0200d504000c1c45012000351441c9000d24891049190800c1c00000d200502820911550a100b0403d0300c000315101e0340011545511500003000084100082e0240d0540401c4420040e000520041818540110510b05801c0111341e56404020001c004501603490070004080030300200c00d00c0b82d031100c1000304004146a900d0803c00c0380185840480741558080c1d108a035a4900080c1045690b9942c14a010302c50a00240c4115000701031181c1d030002160003803044601405244001c0c0418004000d001420b080e20640880c0d6540c3c50080000410340c1c000080726810540d03400d09110564940280c2c491500941d80060082c040c001a041d00704880070b00e180381030f15025255a0500140c9602114040f5400d008860218010b00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 422818120 1250 422816870 422816921
    0x60406120605090c18010206090c011214090a030216030201080a0c0c050d08100b0415030c0c050d08070906030509060106210e0123090d0509061b1e01 66
    0x34180440c0550352550041292503884020a00d40c1c00211010340100c1c40106a036a10144c05049420302482e092004005505091031010b80b6600480c500505011080301c0ca000d40c03201580000840340f680180501e054606031080c5c64641c00d030742401728014010810f010302d40701e405011490507680c041c0e6514a941d500c3d6484030004200b00320400041c86002c00200c000900c0c1004080c00c40d080f640d85040c000d08202c804161b41c003009400540b00300900f1701c024003c0c54104603005c2286840d601e004030764600c40d1001610a4030700114040c203140a4100c00d1039940c1d4005c50528095140c82c1d454400342503443c0f004030704440040c0d03601c0806030051401000401d1003240b0048840311800701c0c84503041c40030800b01040380d9604000d980d10b80d440b8080745240640701440400c6901201c3c2241c0e1192901c80411511703202c0c1e2040d00018024003103900c0c4800d0701c0b020140d480040210310011000e481c42031405903514480c040240c0300d56020342005100400c180500c060316861503101000e80c1141 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 422819370 1250 422818120 422818127
    0x12031b03250606050409230c031c0c021c0c090501060f030f0609020c070e07020a151119052d0403031d03030f120a2306041409100b040b060406 63
    0x70140c291010303500d60101042c2e99445100c0e01a0302403003900d1005403003650314171402d00d0020001102c411900145000049510080740b20344403000200d103038558a0000f05010740e07025080080194000c142c90300c0310104a0010034140006d0f0b07004598000c1c03c03641d50000902511310034091080090340e0300703451546a601a030030030b5034038000000d0081030160701d400c00c007003c031780041501040543c03241c80100845106100d84071340241c0107101803c8281d11030740310540864103201800251540c5c4100061b0810380c1e12042d40d041c400c041010a403e45086807000381941c101084440200c0c901001095400c14040007200f65502c03002800e0342003500d142c0341071381c2e07134521440c0d0108280b103002c2602d6a5031364140010404c0b020041c20f00b80d02c0f030440350780783c0c6802d10000b40000030b590302c0c0000c0012400c0307040d06820f00101c807004c8114900e954410102c0e0140101ca0041c00d510008203081c0b00c400580490201708208102c07400300030702801142008103072030389d00340b2164200740100811b01c1080e12 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 422820620 1250 422819370 422819437
    0x402030a0b040c09090b060901090b030a090f1a0f01060f0509010207050d0506041506300b04030819090b18160602031c050601170604060512031b03 65
    0x1222002031980300c241c002c9000d481450a41400050356500240051025485520302003201074514604102e204400030b405400e030340c010000e0101c004000910642c10540190302c40c1548221117601922661421556514080a02c038400b401c0f0000069a0b1401c1c00390400d04a4005686000d40799038802016a00c5074805401c8a0450045100c0806c15803121603410b42c1861060000f400301c2e103014107001d0000078504801d40052401c04108004d03a00c00500400c052011440740c08506401c41c640c00c5800c0700500c80e004041070403c200f00404d160300709081c60301c1015100042e8a281c00940c04a1088400c0584002d005019001c0440d400c51444800040744001410486e1440000c040e0444110009680144d00513400040c40003908100d15001d0f50050034055000e04c054203000d4000b8080703c8902000c036187c0500f41d00010000c0e5229044003008245c068618446026040240d540380d510807a201c040503405040c100c0c22110307002080b02c0580e002e4041c4806030800000c2c5810000c0e1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 422821870 1250 422820620 422820631
    0x303061e030c120d02010b030a050d0e0f1905040b1203041514040306200c100f0b060f0315030703021c02030109210210051b0f130e240f040203 63
    0x22401d00069490340f00ca18100b08941481c2006100e941c0c25114000d0944035500e41b080d0082c0c214200107030005030006000070b41d403610b41c2402070044800d1404502169122044c1d40c0e80007a681c0142070120340008552001e6036411ba9062103410411003c2c02802c1c6040c00e0b081000c0d500c1008200b01c0085071121200c0800c250740382640c2080c4412640010035000b5401c141c03105507441ca083c18030b8030000a007142c82440b03456084c9050030348038120b1079264944021020b40d410344440405c50360300318a5011803180e0300300901c0641c07030b0201c8014484481d04112070144180403070580e00307406840c00049940403070f9802411090901c0314848500c040d41c81141c01203805649403990000020074015411030801506c00340c0e444a8054500b00902d00624204a04401071920080c032905c41142020304002c800f0240e149035840d0125a5004803e03c610300b03043c1c1a1088000c000301d0000465a10103009803807001050141c0c440d41641c401c040f01c0c072350241c1035011200c0c50703900c6154206a0007866110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 422823120 1250 422821870 422821873
    0x6040b160605042f09070f110304060c06180807020120030d0b091317070312020c0102040f23100e03060f0a0c0203040b040512030f040902090a080303061e03 69
    0x194415a220419038100740c43c12200000c00700d03030818113002c110b441c02c2c0313a03850144100702440e01e405000c02c031041c1000e40004100040142011043c50080c10a0524500c1d000216030b6100e9445400401030310f42000304841450411410150a1150300b480c0d495054201120300d16180c095401501d00d80b022030750010402c000e00d601080624014006454011060400802c080d500702c001c0042031030300101405000711940e0b00e03030000301300c1404500512100005003030746e03258038a00301070b612940441c00200506000190320010303d8019006001220100e691025025840d4030060001c0c40381c51b02103200c8038a403d03202041ea4504040303148100002c0381011407113001d80c1404207041c41c10846525a03411888401c3c4119100701e0312500c4582d5030300c0c0c0b01460810341020a1120f040c422131281912402d0000192840440184110f030000010300c5021030351156250804006500041e603c2c0b40701e141d0a4000103182c001c040100e038450b41c4018400c0302480d0304440c0e42c1c940c0403060001148c15 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 422824370 1250 422823120 422823157
    0x150504021804060c0f0f0207030201110a0606030c090e0f0307030806011101090c06081f031511040f090c05030606090405090f01020f0309010606020d02121c0501030f05010e0303010506040b 83
    0x206407801250500890080e40f0118001c03410380d070b014100d400c181131150100304c1450282d500d42070380410144166a42445d10441e06001c4412491a1400314800500020f103030680010401c035802641400711050b000f03060040440ca400b406481e585001c10402c040e410401c50040000e100300c400c0b5610141c1410030781961003004c80811301b110841d2004682071203039950288016600010b0607640040c02c810104280b081507540c0400c40e192500c0014001001d0800c00341d18403420750020903050300e002e980d06491311750380c0940c0f070403c0c12a0311074401158600503103a0590b501c10b4040328440c1e00007515003440d080385241440020003000300458054000c244440348105801c1c001080080c1e41100000e4890905000366403c5403c0b50f44100103650154584001540d000303e6040d802040c2c01402944070100c240605c500e2004101c03258007050725060000c0200911681c4803844203001da0000c200880c4580c203a5a50f80c8028090298044414042001902410001003084041c0301650125 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 422825620 1250 422824370 422824399
    0x50601020109150b0a0b0306031f020c1606080c1806090f0307120b061e09100e1003060510060801140303070609230601031203020c0f0f2815050402 65
    0x180c3c1414070b01c4045920b9520910442c903040038884054030b030400308180340d030604800082d620003541e107000b2610401c00249004985107603040d608030303208010030303600150300360810360491144e40c2c0a42004110268080740c40002d02d903003500d00c1e040d030b4120b580845681e103030104001e542118050710343c0302c014100c0c0e11589407800d029010080c010205103086030000761801c4404810001e21240c05011014030002501074141180440c0c041c0654000ca45600c3c1d1490b400340b9031183d500301c440d035646504140950224214850400c40780203560401040c1c513241515011413905108507800101000018051180d0703408500450020040440f1b140c40426030303480040d80d81c291003e031a0301070a4094042c80000310b16003052a0404038018141c6581140d4541c1c40202c1088244002c055000c03030406401c40c0304200d010700c1da002440464012109180d042a44d030780ca030f01da2910346600d40b41803680c1c50040740360404001c16801607240c081d51031001d00140040c40c000f0400e0f41e0242e408110b000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 422826870 1250 422825620 422825633
    0x311030c10020c040f0902092205010204030b041a06010206010b0c0726121c0f1e2906070204091a07170c09010813080405060a0903020a06080402060d050601020109 72
    0x2803181240342c000d0910b1648500811046440d0b5032145164070342003100c0400180d581030b2041e5070050b100e01156590240c0744180401c2c9841e1640d00904c25840014007005001030b00c0400d40c031451003518000c0744550748040b408008202516114050b0b4410001480344540ba07001030548400d03444125810310f551410305106048204840c103444004e580c507202c2c100007090008160402c0d0b00d80b140c51800c1d8541420b020b1060541420414441e03507003040002d000e880c1c0d00080320911000020320b82c0d1030140301c0c000005040405050307155018803405c104000c20003081da40805813000f04801e0400c080c0b40c007400301811100301d0440380c40003281d400504641c00c0c45440c030301404c0d072641d40080c44051429010082100640b1030002e40d8001d0151304001c3ea8850310b59540300003449050000c10503186803000890007940c01c465804040410381c4148142d0145180c811a0700031207040e000250f6030401540c8076082902d02a41042081103910b94038100ca40085800403418400041c4a41c1d1544688 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 422828120 1250 422826870 422826889
    0x503160605010f05010809030406030903090306050405150a1a0402030402130603121d0a14041b052106030a030503040c0f0603020c100506210a06060f080f160311030c 73
    0x48a0302a519001480703102801501c0b14080c104c00e09003000740c1e080c0519859502d002e98491001015181c40c00c900c00c05202e04550320003980e1101d0244000c0c02d20386405600c1d80d14035200d40607481c26250018204070035500403940e51150170310078a46540032580c203010183d803005000780e03080505001010207540032481030000444c01082540c40000881600400d100c1003250300c1111103c0703075801503596039203828481c1c0c101e03400b07001000498801c03080842d002c6c028050b141d54402680305520341500d600300006081d5006100d20500c1686200c21462a000e0016150035030107902103000800000d0180006582183c002c0c107000015564030310000812150f190000d400080c0c007c03c480707484150400080b03100e091040d8050080d0301e048400300b0352003c2e00010220704442c0c11081c0700740410b818041e82c0300c0d154002e00300b8040702e611000059003120a51140718000c2c4140220b920388100041001c1c5c0d8024007a995000e05030b8074588070b00e030300300208249440c2e141c003031180c0b4284141d03a4034058 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 422829370 1250 422828120 422828123
    0x31b0403050a060b090a1a010f032004140916051e0414090105011b0b280209030606060703120203100e0403020c1203040f090507020a05030a03020d0513080304020d050316 75
    0x4a400071300003052103180d010103419203114a007030004000240403041e140600a120a20345003408aa588100310054094098103040401c20701c00317006a091261f200a01c00e90f43c0710b0941a1403403039400700340683c0b01e400311840300415690a440303000c0c440c81a4001c0494a081001c85c25800302004500c0d52580c2c40f60388000c000003101c0d025100d0909150b05030314014042401c004081c107280b03011000079503001c460300510000c218030000c4ca82c00c0004040422072400d007462014020b04100705200258800c0300000d2003407041da8001500781c07030440700300d40360035915540d1200c482000400610107500080c086054400b42142d01107a814003204601d480380d4043c1c0c1c0100014800d000500c501c26407a5000d075071841d002000140243c4134030001c90011240554000a4207584101c012810404004070043c007502000540d6003c250f0301d074002d0b140c2e10292a4040256032201e03c00c003030350b00210400c0200403c80520000700586090609000b0041c01101500d01e09048045030340081c21703501c1d00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 422830620 1250 422829370 422829383
    0x12150105040b040609180b01020316150603050f07080d050415030b131509020a1b061107050706080a0603030c110301060509010902121f290d06090b15031b0403050a 72
    0x4042000c1d00c0c00748031007021b00000b15010044003211000003501c0344151880400b41d6a114010b61041100104580d034200b2105142049402c0c0c0303d107445511150303911040c0640703100d801004214613401113246410241c03d0b840b554601031030801138004e8400041540b03014585d48208110032078036040c0400c20b0305071465800203042d08003008084d0400c4466002403103854414407861540f0b40e00030810008418174401d21b101011130902d4500c000d80b00220050404480118107181040000100d2100f41c40345611943c4955130307820185c80445059100150006104800345004114180d400303444074040500042100f40e103550210f484980c083e886003103026400140c0202d0318007011b01480e0440d1094500c0d81800f0740c03550841403042c2e0076024044a01c0001c01c0b80c0b1855203c0c8801d4050705000d0450055265603640781c44800078052403269540789030402c000c1c0700031464003000042011b6010000ba03403c0d0b80326404060f500d1850081000c1c1d0f90346040002001148007001011001841190f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 422831870 1250 422830620 422830637
    0x2402030a06030317160e03100e0a051509060a09050f1f0c09030209041103071509090501051002070b09030703060e030406091e030210200a0c05010512150105040b0406 73
    0xd0010461100c2e03040d442d02140c074030000d10852011840d000102c41a8500c1c100841186c2240040e0402e80000694842d007480c0c1419070310702003800315044050500920a6489507140c0b100119009001103c0f103129036049400000c1955250340c4c0184902c5000e0421030344104a4184514505400c0c00107480c410217400c0032400e44801d150040303900504243c5401e074055851580420728070400500014040715041780402d44644040149800500a55010070b41400b8603000181c0210154010200c2c0c0ea410000007003030034109003d00c030452100c950300911449292400280554200305400c80d450300030f440e40003001c00c049005207101c852841002e55500d074030304000a04940400d070f000648280461084c0c000007008c2c04000710449405440b01c0e0102d0b90400070407a0120b00000300030310b202c0c99010201071080000901750513030324400d070410300c183c503120070055032140a500010501800e140b400159a2010700d6940034000030107062142c2415243d030304044064009401050000e034005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 422833120 1250 422831870 422831873
    0xf02030f0a060606030c05090d030c0237081f110703020708010c03050903040b03090109140f060c09030a110d230c060906070209060112050702030d0b09060901032402030a0603 77
    0xe103d40c400420050a04210501024a010b0a075014650465206118007840001818001c42c1401d190b158002c180c5940002cac50000b0395100c0085500c0740a4001c80d01e81c0c80001900c150300c01d001541e2036a002003400300801c80d4403408905c0c041035a601c1fa00d4581100d658a00300040c0034091152003600544403c5080200761070864905541c02d03002c041c10325007804500c0c14080212010303124994006660b980d1044c0642c0d001d8402d01c2802481c0341c2007298281c08440c0007091070003d4a00d6032040d0b544a480b000c0d50b07000540141c21402e40c0c56005624031000281c81160301240b0301d1000b80054052000e03e849052000d15080142000000000070100b080401400790226045040f80d040c2d0428803500c005c140703507006400c0005e00590f11070000c50010381c01b0320701103000300d005030400340414541003034000d449400070b91304104182e0038910302c42c3c0903143c403840d01031043ca00545244947d80c83e58582000d06203a609407119280859040c0d044181e10300c1c0000c520a055a000200700303117155 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 422834370 1250 422833120 422833133
    0xa0207050c0a050a1a0c060403110f06070e0d02040902040c0203070308130c091a040603050c031e03030f1803030f01030b06060735030906040201031503080301120f02030f0a 76
    0x4044585105103100503092155580303181800b401d403091782440c4054040c2e0040240e0841c403031860704003407038441d05040108040d0b100d00071811150070705040c2c03047d85107407290300c0380e07506000c0d80c0c4440400c4103080070003443d0400c0100c10400c207000800c041111080340e004a021070700c6644803000149c02c0010610245500020080d40144540400c201841c00c2a190800c21091500400108941315440040d03042d50551000720100340c014010000326030303680b40441c2e6072110700355241e0281c00f608510105107945500d4a0002d522141c3c051407031980d40310462152090001e040341c01d0745642c000f035a241c012041018602c5842c80718071200280d41181401c040071400101031310300c50002088102d0000303218850581400c151281d485101c2c04045614201c0c00c00f40c030b502c0344000000401002180c10f40041d00324000d500070380b0100841e01d441000c45c011030215002c0907042c800c0800040200c50031480c0c40441c81c501aa500e0010b40aa030303030019081005031031420460340d00c502024402c1c05034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 422835620 1250 422834370 422834383
    0xc03061d01172404060e1c020f0d17090712060906060e0903121510020106091104030b040f0213060303020d0f02010c0c02060f040e070f110106050f060306180a020705 73
    0x110500181208100310b120342c1c0411050040c3d4030014900a80410100201c030f0b040302441c0351078002a41c8032441924000940c8401d200403000041c0315201d80018180408140c95a1b103083ca0340c2c90307440c40110800003034901c24014044a10034071840c2000180704409814072274005105520210361030715035060504c256402c1d81c0145440b140c6103010700401102c00130403241160300840c1170703042a80e200003d548103401341183c100d40003404c07002c2400c040d990641c826019140702550422041010b59010400c502072801700404000b00c48000c14089051724107080315a034401420b2600741e11007500c540302502d400d50b10890142e40100d82001c502c6800104100b4024103503c0200b2a041d200480100180c00044000e40192800110060850406021100a0310405062080034102100014010340f04003003c0300c00a15145484100e588040c06888111640103105c03191200c214010424254800351890303a210950720f28940712850041070540c854040700200585643c0682400c1c0e041c40c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 422836870 1250 422835620 422835659
    0x3060606050310140103090605070215010e10030b0901090203030d06031505090318130c11212a0706081005031207030c140a0c060f0305190c03061d01 66
    0x1000b40104103c1c00c40b21039510382112070319034104000c0303900500142c0041007061005040d413400e080400c1a03050b00080e0580f102e1001452000b6a030f070341d5201350300320307614203540080220071640410404240c004030341c55004045031000007a0001564000b038070315808001104251900c6500804c2403040c0642454044540b1010038492441c0c81c16001e91a44a54001040000307580d40b942107650300d0b148a11244030309000003c1111110818010300802d409504da42c3d56489003000a0210851102c001050043c460582c0b0b4180300c1903079106070004003040003c07601c0e030407400f0301e810610004015070801803103a03454000250910400079505040d10740c201c00d0003540005c00d4102c03411f070740c03004440da266014546808606800d00c0c02d0865504c40c94028034140c440c103515101480300d001d104008403800381d2204e84040c540fa060176815900226081062070b81803a618180b1070501e5045070550000500e000034003262220f100d402020381c0c43c07100c441005200340040c23007503442c02041c0c41c5002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 422838120 1250 422836870 422836877
    0x6070c03110a1101080c070f050105090c0d1a060f1e011202090603010311120706020d030c2d050f0c0609010e03070c06051c0513020306060a120222060b0403060606 72
    0x50b4070f8420300c110052410750304014228000500c078075100d50071303581d070b6542c00360910009000300e00b0301030b020300015903294090b8080e2032505030092034600501000c10b0741c040c00400880040007001c01040350003c01c050b420048480000011307580340054401c1070010340340d0742102170100e600010a0411402d42d4928582c2c410004403400d41d80e800147c078110390388900144004e0f0702c06004a141400e02c21000e2180717101c0c13034401007029034001c200d188125000b03540802c110b411034034040b550103280c5021440220020041c0c0485200c0c0d42003690090860350611501e480c0c210044c00f0001d51261609580a80014003032100c00b0900b80160b00c60b81510000850501c0c4444e150904801c13820702c24079003407010000d21100c8541e02c03846402401c0e1201c0100300124540001e5080c041034007aa0f08a01c6801500e00144c92441d1004501c4140c801d049104214141b0590a0081e100c0f00700310549900e0721807801d4001c510707180d8000c60028107110b010f142e403a0b40c610314007081039900c107401035001e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 422839370 1250 422838120 422838133
    0x807060e0c061e030a20040e06010e0a090207140f010608070504020304030e061c06030305091815010f090e040c0e0c0f0d230406050105030d05040e070e030f06070c0311 74
    0x210781d8003140302083c0c1c0d904504115505d4603441c1480c0018100e5108580340100030795444a014441c01024000300d800c40c80030301110ba95803000442c2c1c0803c0e03901c2c01652109404005102d904000c2d80a0188984941041417401c4415015207140c101c1c101e400081603919104284041075060101c0d40062405071010350960405a50103400b100d2601c402c107000f00000301e82040942c030307a810b110740d070030305a41e07010800141c0368100206903030b204202c058002d000740d5640c0210b007904982c0a0b0312901003000d041d8003c9807100011101c00900e6203001e400c014606101261002226001e2400b03039104648041c01c0034a040c80b003010b14080140589000310003401804561600360089802c51071284030001106424060818a00f02d88280d20448074800e510800c8104819944420305a605c1141118000b82001c07404803658401e0b806158102d522820100300024000c1c4240e0b00104c134020181c84200c20601c0e4480c2c544507003115240001644071201c00103041e0008d480324171010142c00039241 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 422840620 1250 422839370 422839387
    0x9010b031b0130060509071d1003020c10090303050f090705011206090e0106031506081e0c0603090309090105010e0d14070b210108190803040f0807060e0c06 69
    0x4820356003441ca941441412914078205040c0c500c2c0481c03014081c00c40060300900e079101c480000389030318011180180094000301e0003042c01502c840700701c04000800e001c040c900150030700c4501c032251120311003416002d101c81403003442d013441000c000d441e80d840c0014003181513041c02400e40ea40070b4244400081c1c14001d00140c80004a0039906441d82802d0010303180080403242002030203d0307444890154505546080d41e002d06400040c1120f0050304101d8654001604c0041245d040744180141a4848030030201d05014220760109014800c5e0b080e174074144c411101240140e8000c40794014590400500c4602900e44001c1050141c10b080ca80024008007041c00b2500d1080103581c040e04070782e40c035001c0c1c0c00c40500401c0182e01820281c461705803140d05140b0003110840320301c4144c0c0a403000070390000c54506070004003076140a88004064104c0e041c540c0302e0941c030f5440900140c030300103501c04c40c1d10089008c640c01045a203218000020340b150400c0501800c100f40d0b03810441c8a060208031142d13 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 422841726 1106 422840620 422840653
    0x3060b0307084c0b0405040f0b1206040b0f011a070c0312020c04110c0a2006040e04020306090a080306040c031401080d0909020c0d0c080d060e09010b03 67
    0x84010300e8030180b450540c081c3c0d0050b165007000c103110800c900c1c170f0b05401c980183c0d1100c200000f240c080d0800840d003000602c01440344268000400c9c0300820403002c40b00c66100345444420000c42d410200d0328440c0880c0050004a032010114404050001c00300c1c4220045502060120034040318100180d12807222980c124030075454450900300007048403003100c03845074000000e411031328816912440000b250340c8910054550001100d607484c2c035031100620181c41c00b081c140140d840c092040500c3c203e00180310410913006282c030940003c0b80941a00d400510480e008034401701480c00840080c0410015103c03d0312001d400010080c10100e4200e02c0c0110a0340c0f07000c401034039a1045000d92141c0e8150b4500e50340300000292019205051114a480c41103403040d00c0c12400b11080c5040c2c5249800400440700c03d14203000c440c0000340b003035900c9444181c000c1c040380042d40c600300c07 = true := by decide +kernel

theorem cover : BRFrame.Cov 422661870 422841726 := by
  have h0 := BRFrame.cov_init 422661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 422661870 ≤ n) (h2 : n < 422841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
