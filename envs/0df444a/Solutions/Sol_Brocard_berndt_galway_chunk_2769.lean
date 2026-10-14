-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2769
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:41:05.933329+00:00
-- url     : https://prove2.me/submissions/42dcec72-5d7a-447b-b758-8ac8eecaa05e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 497841726 ≤ n < 498021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 497842976 1250 497841726 497841731
    0x3070303020d03020a030f140f010503010c120216060905030d050702120a0c050106090609020705070b090f011b020d080d0f290f09150114130e13020a080106090609 72
    0x40000940100b00441c2202042c100182ca0b14503440c02a40170b41006c0c00c100110500c4c040c4c1c0b80c01a4000c4041d1540131351848039a5620b607a884009042c00c84100011180c04101c480019000c0b0b0302e403a80003045018035451821480e650295643d400380e1b5101c0c0800c4075107400104225020b242c940c401c01d80d02140c0307840242070380b108440e403c4d041441b440f8250810401c3e454072050600509401101c0104400502048541e03a039401c504029003096078215524066128006100ba105905950540300020f21071080b4080030303801507940b080c09200402011b40000a0140541d4a0962191401d80160220366032240c104502004403052800b40d10b85052030503d5000d00c0752482c2400c0e81c249014002c07585010140000010040c09607040c005e1341c4504484100860f01d0341c3c0c0c80b940d081c184000c0e00c41036212260100d03411120300034141d29981840380d4100800900d90000121504482c05030060a407901072500400c405002d585c00c00740081c0e443d0070003008040140e10954000303140d104001c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 497844226 1250 497842976 497842979
    0xf0e1302010e06091807081911030f180a1a0711060106050c01020408030f0408060c0304080f0a09080321070215013f03020c09060d0b0403050d090516050307 69
    0x3800c564040c002181c060240072640b03509640f2080c003202d0341411031900c900301724902400001c200300811a808511224038001c1000b81e021a8000e0040d110101d11000d819680c403001e17007071a034020040c0740440d500f6400c6030340104000706000400c0c0300d40c000c0c6002c806207a500c0101d03025a6074080e00389002c01c009040034a807000741c08924a4199091803a08541d14548803940d02c0c007a010340c3d0003032960ba02000404900000180c1d0040086a4929080d2501a0f48201c40300042c1d0004542c040c10703690003041620007110a51004201c5901c80c1d01f09081c1094480740316528541000030031080b14211281c05424100c8441e0361140c1c407514510090000407030603000f81071500c10610580c03d081c1400041461007606403007101408089a42038020800020903106988404001081d800f5004500951405007000031985104210140070a02d10003400e070740304180594014820703420032009122040a801c2203000b0400941e02036401003441510b40708615807590704540c0000d2007175006060 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 497845476 1250 497844226 497844229
    0x605040b090601050d09082109010c02010b061c060b0f030a0e0106060203070b101a12010e1b0309010f0509160b0a0c021504080307031e0201091e0309030c0f0e1302 72
    0xc642c09011300c0e07040030a06c0040c6103040c0000d0701904010829031146c10007100c0c540c4140c800050301c0749281400038059121071140581c01c07030708186081da402180800c81000e503200d03100784101c030080d8820b0001501e95614210780f981c1da082240e0187c401c07a03001080c01420000c80c09040360001e1604004c0181030b142c0403020b9070741d218941e1b00904a15449001849072107001d158000207082e00c1e07010309a0b00150708021880317644020302000441025400228054142c506158030a80070030442e4800c0c403066084400103034200406c050f41315902e92190741080510b42c0211070140704024018010086000900d460888c102c0d0400540c09806010040f1065070100f0f8045c0c080f0740503102c00074407080c3c1c149548090701c030740e8012202034400015210201079008650b030031407080240c10040280301c44070040b426150404000b42241981d940c25200071031015202403800c1c0d00c0303400c1203038130306503a40d44802c2c6071425075004119010308100b041000080d8490384661208110440302da01900560 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 497846726 1250 497845476 497845487
    0x40e060903091507060f0509070e01060503011802090a081e12030c0903030c15040606241404080f0a03020d050f030103031d0d0c06020f0111040e070509090a0605040b090601 76
    0xc607204184050903480c20010003821134030281d40004c0107128036102c40d015070015001c16100151580f0800c0300c0003842d04490b2058605840083d5905480c41c0d1a111010221001110120706595070800150500b56076141c40d100c01040c3c83c0d4050203243ca0b525030030b4000080c1c80051000650402c09400072100c1140007102d40c0324810308440d0b0b48880e024004240b071805010240c40403842142c250180388503170100c000d031086210f14014892241c695003075007000c0a21001400015610a08244070940210038140310030030516030307207400c1664400c4020f241101c10b0152845541280e070b40c0005141e418001c4c1140303d00c143c1071030303840d002804000782001d101c144005030800074650008094003900350a4600080c8000f03042803032410807070610790700d20041d5214510151003121a254034600d011b004145100c07180300b000c00c1c10301e86003505008403075000a20490803c601001102016643c0b17102440c05000e421000048a42c2400305000403240c19002d01846a800ca004125042c0c0e4400c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 497847976 1250 497846726 497846737
    0x10f02120304060c23091014090103050901150b0301080c060412140a0609080c1e0d0c110324010918120c0b01090c02100207051e151302040e060903 65
    0x518001036004100b0b1040740e04d580c05da00c01c1e5403691410074081c00c03800c0942d4090100110211810100d2844800040d9103c000d00b0700001400c000900001e0b0556000741d0040d68810302c110000b08200c1118a64003039409090f400c4050248004001400005010000c80e5050403041c0c881d20710f01814207044070300c9507904000003095204083c83e906c0c2204405c0c01400e40c5a50b000c00107110f01a0780389803040c42a0450400c420361440f41d8103e01900d0f25811100309028240e8070054440105408403c075000c4180500544110a540081c14910b440c200031003022610900600f95501440401488407284103074400000d481c1003a030a0b0030040c0a5182c640e000581c850821018030980b00004d40d46510152409000d252a603400041c40e40c2c031540048081d55002e9084d81e0001540e1101d0600300e005020340135115502c1094140d005204040b58101c0c9c0d107080d0012500c03245420b40481208910032514804100341001d05202142054051142040d150704041d05a51400c25011583c0b40500d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 497849226 1250 497847976 497847983
    0x160206010914011503110a2006060619020106030f060507080c030405032713060812030103080a080702161d0606070b06010e040905030d1401080601180b010504120506010302010f02120304 82
    0x1540c030072283c02c0340240e0050b0240c0c4021b14a0a468185094000e80085a81c2c0c8080548148172170221805503008940c030b43c82280d0080007581020b030140b1405a0580705600118155035a40360040040b81c56582d28100c00b9201c1c1700c020410b8a80700400414102026045801881c010b01c14080028404005d0711000901e42e01000c80204c2c1e600c802040e082c40f140c04194010341000d006100c01b103e5500814240c0e150b4404403082d1150081d503040052200348409000d2203018005000154440c0006540141c581e1044507102560078110a081c140b240d0301180024400c0c440036200780d40d010f905660b002404546d40e40c03d004081d214586410f8004042604224159089511682d0b07144e001502180c0c00c0021070351034400754590600201440300710160742805a2000207406ca0002425038181e0340c4400000c4009403440c24240301800840e40e0741c81c14000180700201d14126119600442d141c0a07000801c0e655146000151103446444490b400315000300031158034100701041100c2d0000d92 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 497850476 1250 497849226 497849249
    0x315040e0706020d08070c081204060c0f020c06070309030c23060304030807110f011401051903021503040c0b031501030b040e1902030a080309030406030b06120105120f0616020601091401 82
    0x150204200c0f65100c611f84000c156220100e60b00c03814070740000b111071046110358410002480005002d0341d6201d000c024000042c0c0c012420441d01e4140100544449440b0b030400d403858607126134035800f0b0060103400403050030080c802d2000c03081802c412101c100002c259005459400c0540380100b0205008180f0b5051005c0100c05002c0c0440420042e0307100d015480003002180c800e00070b0350311507080c00e05c0b91912408900003507654091003840d408003142e034000e0003849054026565070f00f15400007002901e40402d01d510004072004014000d61145100c1e620303201910b400000090b00702c0c1c00c1451000c1c0070b6803410f0301000c2ca00d40000340c114001e0741a6540c959038800c86100003403600350141b500420311400481031112040c0700101400555405460500610300080180f040d1030050243c8050040842d0004100340d0070007034280018000c6050aa80380801405840d92500d94165040208007101c0e008201c3e8441e81441554050f21404a003802506115039a1102c2c552042c0140d0f2408003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 497851726 1250 497850476 497850481
    0xd021c030c1217060306090304151806030506091807090b06090406030b0f010611060a0b011707090501110c0a090c020f07031b09020c06041104110315040e0706020d08 73
    0x14040c2900da581164000192a080c0d400706900900b660f082c01280d48480c414031012030070034640458403600c80c1e0f901c02d0003142441e01c0c0c00f02d0702d074603403c0810031181480b85d50f0071108440702c450043d03000070300041c1c0c03000700d070380d0412105000c0c0c040310040c69010035040034403811550702000301e0b003501168940d007008038003000034a00151030382c4910382d43c10390300619001c4000100203074250340760721805641800c07aa00c0e071798031031090b84c03a200844801c2c8025001980002c00c1e40c19184d1000d205200c040c50f1040418040380e450800e01c50055941c0400700f141200c0401840d03a01042e141d0701803444001400000c19540d000ca055a0814000c050045860305010480248200004c45101c8014400c540302140e4905100c00104042030308042254800758010401c1411070088581c1c81b01060002d100c5662291200803a50406c0318040e58865141c20740d07040040b142e2009540141d030030f0840c00112030310403010441200c8105c80086115004984100701c4c040e008544006100d456042004095 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 497852976 1250 497851726 497851733
    0xf0f020c0d060506090f0907060c08040b0c01140109020f0403121b03110606010305071b0312020a110c240d0b0904050a0606170a0305070501140702100b0d021c 70
    0xa45844520341c012580ca507142040c81036542100e40601002e50b42442c0320b40340c030f80d604180d8404c100d03404000355004050401ca01803040b0420701004c0e0248064500f42621421304984a0b030184920301d0f1980c4d16500300008260411100a00420010204500e059000c1d0780c091018021484045c14180a803503031083c0150041c240d40500140d6010301e02403102075881d0160a24007542c00c40b0b44548200d0002400350350192082900030f128684400450380340c0d100c01040142941c580450412130302c2220050540070b2800a000b9025807600c9001c041c4070b903041c03e1441d0035103562100b840740304294040c4c155026145512140e0b0402d4070006584d070b0200b05101d5010f0300c3d10403c1c1030f8102c0c10305020007040c00030100300711000c2c0d4400c4405000080d0341c0c002c508042d1419009043e416041081600002030140006001203441303940046209017180c2c1110f000e20104894682c05a000120000500201ea1040602c01032040301c9461807540700b0380106241d01075040505004011310700d0600c090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 497854226 1250 497852976 497852983
    0x2d050901020904090510060b0301050904150b0a141201050c0f0d0605091006180503030a03180c0b032a07020402070501090209010b0d060b090d030507021212070b0603010c0f0f02 78
    0x42c01c1c4042e006203c41c040c24900207603201141050440903618040022511042440031039048400050120346291038030f48821540107411104140d503e969160018429152040210000c00c11420680651102441803000340403400d41c3c01b00e25079141008201204120b50151041301301e10000c2645c40740d590300a464020281034101e513900a2910b0200700780c0050f034007054020b03138030969208d402e42c0021905a82c1101d034140141c0740d0540090004da0b19540c8a0b900a05850928000d0307421085015100c0000c11200340e0042038291400004212007001c0030b54810f1040304180c03140400b855181ca82205d06409030081c021720568000859100b41f050940044070b00710b030000e0901c205565030b241c0c46486039000c4060f000c03403a803c007080002c0e40041c0704180c0d1980b040140800c00c41685590b02114640e0180b2400c907405000303013410b007400c42400c0000c11010b6078461100e41da00e120070b0400c01e00c8007000034444c40c4603030b040c0842d034440194480c4010401c1c076000d061030904465244802e904 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 497855476 1250 497854226 497854237
    0x6030a05070b0a03061203170601030b0d080403050606010507050d1b1a070e0a060e0402070501150b070201030f18150e010c030b1003051b030402010212030a090203012d05090102 78
    0x2607485a00000715401a0000050081e00c0c03040d00d04105642d076980300c030444800c0017140540403424000c1442d080e440340003041039003e80705242c009041000d030b00c0040e0714503508510a4440310f202160034010003000300006a0800401d080c036a042846e580d4179940e80d0031540c0341a00070082214840b0004500b1400b103804041c1d03104031480c40b0880051039440a242003144c0305000525401e2001c509400d00d18952003e48543d03540303034107200000c5001d00000c0d51200c04101c031030703640c1c50110795500c600b0a00f00101501184401c945e89080b540001019102d11400d03d42c925072400307046555489a544071030880039401161110301c401c00c0700e010300c02403030800071584007942032048865204c0c1e070641c040901d150085a01134186500e05074124101c4000b1504114041922038071594070200300c402031980a84148116404180643c40d112090b8106440d400080f0380c5400302c0600310f150038010300880105070b800344107500c0030a0520090f403810700c10340d11007010707900c2c4080b88240b03070290121013 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 497856726 1250 497855476 497855483
    0x9060c07150e0f0606010810062001151d0f0105010804050f0d090f0b120106050c0708031305100f0f050702012a1203020c34080601080d0c0c090506030a 67
    0xb1800a030524991514810341c2031002500611001803455809003000d91700400c06480383c40782450401130152008103582d5079219242d00d0034038005d00d001c0c03008d000d80c03881e04001c0c104150040c1d1806401607842513030440390141004820b001c0050209a0440b454111007017403034034a0320740d1164103100c1c0c200b8055100f060164010344161036051b81d0031001e090300300c4800d010103130b0f64a075403011007a00c28040d2984005e8000d508400400540b4440e5001d41800c00190341030b10f0540b9584c042c0185194803020111aa030800001c0400c518075180c078080300408418185640c0401140b28010550f01c854a000000e01802040000642e445180c1c0f0340da018200c0c0500604103402e80083e14034541d000d6400310398840314280440c01b041d04c03a0080c1c1300d001188000500312414400d12003d2000b8201a05404030030100c0c0e8900c1a090a030f042080007041c005004c0c0801d941414406414442042c040c00103100d04071201c1000100c000c400c1000b21248500d000880e42c8503100003074240041c2d02400b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 497857976 1250 497856726 497856731
    0x5390304171306080126070303050715020406090f06030c0c020915040e03031015080105041112040303060302010f2a2a050406050d020607060b1507060b150309060c0715 74
    0x300f0895040400c0505a0f1030410302070f1310480c41040b4034410400c2040c8032480f640c20001301040040c0c001c0020f41a03091190506100c80100c40007a0070498225078015000141a51010400d2081c4a6090006052036141c20b0000e00f990300c43c0034002a0300454000c0c0070f00c58038400035840d01c0840c80d0103449a0340017441404048103903000281da0340c0007601c000030300c5900a94005400d03444085044440b0820392685081a844c1c8020800201052000e8540e900d004105550a80903c00009842684242c0f00050141d04500005164040c04200d68050107910300050444800e94107182107004400e190040a0000c1480c1c4680c00c8a10040781120036486190b543d13030420180c88020042d10001c2d207040080c15035400400c28408081e60010790045420030080c00803c40c243c01015a4210107440d903101113810104050302640050010b54400d5136030300c803500080c038058000c12a4075010131512811400d00c20b00c1340c0e45540014000100c541c1c0005050400c00c044182c000b801108450400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 497859226 1250 497857976 497857979
    0x406170903091504092307050703022404030809011e1104091e051e0406181712090307050d1b170702040b0d08030105150d053903041713 60
    0x5415041e0018000c8004031400c02d00121200884909100d00307490904480e46c44a44421304103a8240d4003850054003117004003403040300c00004091041c00000862200e00ca000d140a0500501c0108050880704160741080c41c44807107440039050007400400701201c00109441401c1d01c01250348107661084200a0902180190205031031814640780110310f07006025607500c929407080e42c2038400f080b191040c0103010101d00071840d5940050103c000880446441ba102622287d5064401039000000c84400003075003600280071101c025000000c48005508080d42d03651159120401042072070b04018211120400240741c2c056a03005081d0000c4e100500c5411540e0305e400c041e80150780a90140e81803148018490070002a07403c00290043c400500316401c0808000a4842c007038486088030409100e2a11803d04c0c9120707aa00814495200b61006404144101680d2040114a00a502101c0c0500c0400601d10007140c2e40290300c41000c0b00000b0300c02c0c3c035640203401036a41404070800389000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 497860476 1250 497859226 497859259
    0x1020c060a060513110301060c080d060b03070215060a06030507050d020d02130b1204080d0915020403050606011b08090d140a0b13050c040b0f030d090f0b040617090309 74
    0x2144058030340070b88501100c00e211381c41e48015607403c6114000c003198200010050301b0b1241d200c0c03c00710b62007034500b180341c444101030100c1501c110360462000c000000090100f02501002854242c20718041541d00d00d00e81400010640101803007000305041d220380c002a4424071600858011520f0b508045444181c4d402600000303400c00f041031841d52408000219480d002c3c0825650178640042c1310142603036450342d0b4400385400446c881c5c00c6158540c00b21800041c1103030400c135040c0118800068540d403850030414a0301001412040c1480340800780c000542d20310b001030b11644d5810801c150f40d92103170000072034103016441101800198146120120081020408004860141e140c0c032240c3e45503e90401c555100038007000b4416070052005503000d08141d004000038001c0141800031051003407010030b08002048000200103402e824003445020480400d100180c100254414207190030240064119020541540c8101c0380c034000085800e40200b0840e642c0c0c0c2005000342d94910f120340e5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 497861726 1250 497860476 497860481
    0x1605030c0c0f0706020307200d02010e04180f02040b060703050f1602090f100e0c0703082a030403090801090f020f0d0c0f08011b0912030e0301021602121c0e0301020c060a 75
    0x47c0c1101c1c1c002c0d5440c01c114035081c1a81c402000140010101310101500364019161400f03228109070300b1580701c908118042182c0148880201d025030442ca0803901148108022101304444491150000b4800c070008a0380c04000e4844101e44020180d03540c00c0580100d4210b1000000d009612141a10400c600308803030310000c81c014010406145d16040c1c840090320350040d000c8644901c5c0c4e48050000c500403c0c0304664203500704008d01c40c4400355144801e5095002c0c200054180c6c9041700000074882096030000c0324a0080070f821000304100951035a5002d00100d2000000c0d20501e2546075203202c581d2480c0d0341c01b508940c0440f80810345076503001594100d8095101c5d02d41ca6510740070041d00078000e60b04818103170b03136001d0351030144490910210030380d0440d05070019010810700c1459407140384c4003440240b116041d010342e00c80c0405410310401220391840205a00c0d030380c00ad820303241c400d180c03201074030407000c0c5a5040030f038114400000401e0090003051088030b00c82c40f402007480036429859 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 497862976 1250 497861726 497861737
    0xc1b0b04140f040b131505030d02151f05060702120f011d0c092205070308070b07031407270e150105040e2410171605030c0c0f07060203 60
    0x1541c00c4041d1080d820100302c1100d0341590b4480d0818280201d8174501e5200d5484582d08182d60130b6250b20031a10f03203002c24582074000d0b5202d03002d072307002004950601485171a41c5500008044020414140d003103041d482c00d034618460580682c5002c03802004564884c2c042002c907020030030499042e4001c3c080e180d8064100e291409080d4140c0b040301c0b050b041c201290f040d0b07556034003801e88007062711680590340b420310107a8009005142440c04e02400207409112900c019030246c851103844446a003040507003004081c1001d414945041c000c2c1c52440c2c44050b11a51000c4030341001035203840c800505902c401c8000f040080170343c912007004074859a450300304e1806003183c46156000800c0800c010b440c244101d000c1c0140c80846080050040901414800c0045041e0b0550100d00313807441000c02d0b1115400924640410600e1304400483c0a4030b0b4103083e03002e0082109085030f1020620003800302d1002401444a00c01300184056102200700044024100100c0480307440b9550f84030000c4d00e03600031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 497864226 1250 497862976 497862979
    0x402030f0a0605010c0201050712030b060c060709090225060b040e07140d030207030605060303040b0a11060c160605040204020f13080607030203010e070e0a18060617070c1b0b0414 79
    0x200341000c12954440d0b01600515071b81a168646400c0c031607110810044c140c02111420507890f40400017442d16114054480e41c05924010881070501c00b201802401c80d035008040090b205000c100025050b1158903c0c0146210390001640318140c14100064a1790105854101f8148820300300041000182002110403a40c494000d40b0201c404105150440d640041d00580c00840240045521360b803105800600c0102100d1400d541d80f01d81e40c0311b80d00085100b0380803401e0003045c0703c010b00302482001e510181a40c0031758506610203002501a940f03004000d001d0b95a518001011074940d80e040300c0c00081c003c00300d1603e0380115120342d1035003d024016000c3c140601d01c04150014000e0003528180c1d050501700152039070f14030b00d00b11070031066108201c2d88101701000019012441a03c54400901c5007140401c46504040b00905040441c2658840c42e005000030040001d6014020414166100640800d80104d00804100001c0c0503000b411003820005000542d4011500c22441201030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 497865476 1250 497864226 497864231
    0x70302010306080703080318031204030915080c0406030b010201020d0f02040f061706090c1911070b070b16091a0d0605030f070e0a06030506180f03030702030f070807020402030f0a 79
    0x4803444850b03140d1340548401800302d0024804114031401d411600b42192203080122410705603500031080c12140140c1342503000c651000e00c24402c070148080d46e0303a50b0034607034142180c15081c8080360791500e128a00c130b1081015610740603410700d68800e40484401401c14001400891985083c0400075801480f94000c00310320100d0001e40c550056413030b90284000c140c3c0f1982c2e04c0da10034060002d1088000e20703500400e4801c03c01d256401e81c01c440e61075072021031755503035a201202c5652064a010722075081040a080c2c00d00120780001c404042c0c180d8440400201d001540b91080c100391003008184e005030038026501406540c02c0c00050300605421421400c06224440e45c48007415103945590744d9812a0342c02c0740340c041c03100502c004d413640d400a401c0200003885036542d841c0e40c0d04014050307500450381d00d0b40b01c01c0001c8002041181c441308140100142d481c60400d484041e58030b201e4490008031b10360020400340c040c03040440503100d42d81d4020b8025580d9140c852400c070350020044070100e40c51403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 497866726 1250 497865476 497865479
    0x102072c011a0a0503151306050901090b0d02040b030f07080d02010612050d0309030516140c0609091f15020d0f1b0807082b0b040c0e0d1112070302010306 68
    0x403010018400b00301500c6051628003034814400303d440303074001800c01c002e0445240c2c001703000d504c811441c142220007503100014110b0406042000003078040c0d05c180811400d00c03a0b1010907a0310b00c64140c92050741240c0000740310300b0710404a410710440700c072102c000d409080350006800d40e011a1030b0026901c07540c003c00c0410b0f1200d80405003c0558031018005520900f0030701c800e20b00a44c4071420040c02410304a04010007003031030011140f140d40c800c4910b510040c0315609981c0c0c081015043c0c940c802c42e40d590510400c2c0303001c01c51008004041d007000c0010440e195103198201c0c1c0c400300240c034000700105102d56054030041e41c1d030100c0940c80c40002da82d246040700300d1881034003200c2e60215601625541020780d511a064190400f01c0e0582e0000c0d02003200340d80001d003e011005036600c0940030080041c1080500400b181e0905202c68010340c20141c480281c29404030604801801c1201c9164068580d410100704218040c030035203400000503c030301e1203038510020b2660100c0740300340d8007404002d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 497867976 1250 497866726 497866739
    0x52b09170a020d1701061b05010219180e0417130e2d060402090102120a090f090902010207090c030e010c20070e070c030c0501050a02070218061e0102072c01 69
    0x20380010442c01c00410f00302c014030800d0300c20340c1d807400307004094003140d2035047d09500c41c54220f901c4090fa1054407696003808040300e0307070000540d60300020714070031108a051506107816440c01c4001d1000304628554000701ea1400c0301001520f4040d01e03451203e044003521078001c0ca4040d00c041e1001c0e02100c442c10001155042e484841d444c0030b042d01100e410380f42c1c48150602c4080d4021304c0095055024040482c00300c10f818102901c121000b980d16003041c0c40c03400d51514000300c03454006191700c1e401e203420500580d80010311202200c83d450000504000358200c124001d140d001c502019a50910911010b241c0d0b010109601c1c3c035107401c0588030650322503001c0d07650b00c28292040b5404500c001c000101100d0081030b0003028603020f0704280a0000030360b59aa821a10115240c040c01640401c07158290300780781111140e1203250440007441810510005100386548101030b0300c518107504c28400c110792080c44424000e01d98011a0ad500c107041a4099648501340c00704503900365a00030000408 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 497869226 1250 497867976 497867987
    0x60303120207050c0f06071b090b3a06020a02060916210c080d08010815131103010b030d030b100c0308040b1e090319052b09170a020d 59
    0x990b901c40000d1003c40350210600c071030b09a0600c0c410707520050520147c0c01103441004541e01c1101c508008102040c205010341e01103d0b101480103000d07811000305502c9a15050155800d18180c0c044200d00022001304e641c00b01d00301c100d00081c031150010400804003030300045d6160103040c81506940031107104017004000c0d0103031440b03070001481940605406c0b604428031617034072942c02004000c51707464480c9200c510b45031010b40c1c44400281e0040c010480001c0900240d03810f905030041c9401203040c4146d50030300500002c14003030800900c14000900a60f001d5100107440300d03004e41035a800203140383c0050300034004602642c0c0101c0e204030346800c1d4680715644105502347e2544945103141ca89880d865048080141140400130501c00b81608449035011210f02c80c0c02020011682c6009504c007168007400108440c0c0180034051003c044013942101070040c141c00000c1900c100c5101c0704402c0d41c0504503006000d401041443e00300103500c2048001032654030640d40849013406440d0600301e41 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 497870476 1250 497869226 497869237
    0xb1011070e090a060509011103042d0309060e010e04051303030e0303010b0a050a050d090f14070503280b0a3218010b0a08010c0905120a0210051204060603031202 71
    0x2015002803400e0f0f000501554022608200e000d0000918100c1100250300564400c6d10140c901c1401060b0054800786880075070851404440954114204107982c058034541090244d1401c0c00203050450080e80d10030645058808030040c424050303400d100406256000e60000c0030340000b03060405201f9003044c0001168101c0e030540031964a04100a502164190003680d011000c0000800181c44007940600650003018010540c0c141da114040c0b4049101c00c000880c010300680000344208103d9401160203000309200c401251440070340d0151000c107600c868000280140500024425034003203550124100100c2411441c1e50b0302045035000519074426030340211907101c4c2e28002124080c50112403040300120703500101d40364100c0d00000e0454203068002a0340d0303a54904da00b00d1090790101081008020554031180462032103050b80352541880c940280c0110b00c42c0c420b800f007981c800c00403600340e55051800c0c1c3d142130402d80f80c0b15004d40014070042d800905281021f100d40c020324800c660 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 497871726 1250 497870476 497870491
    0x604060813061d120f0f090a08030406120c030506030c240c0c032e090c0e1e0604060302030327030d03090b0609070c0f08090d0305040f120807080d0b1011070e 70
    0x141071000d1003800206c1a4060310b481074100640400010300c1800401c0904090415034a407400701c0c0c0552580d800880e680321492604050404040c0030355500c020036100c40e0310000f030300c10481054003031110920286c5402c0044ca075652001500c542030100c04103000703104150032001d03910801c20300c00441d0eca1502c2003514069480d0300c00c81d440441a295440324003c1440303081c1d00141e142d50340d0400f50304a082180e0400c03410702102031307104c00801d1a03c91242c1c05401154100402800c40c0c010030760b01c0c003580740510020340342c9950100043c402c002c031840c010300000b8121412801c0700400180540a551011203609010001040c054607280075100d2003860103503605901c002982d01c410700201c0003020705980759441001500d50a4170ba00000304115802a1074055842c1e151194800c143c021039032160360200c00d03031448403000518240848044a4001e58100d85645101050307000402c0c9000c40c19521980740b074103400066402c45000d80c8004082c80580e0010bd0382d03076050f02c81d0030300100c940a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 497872976 1250 497871726 497871757
    0x25052802030f07030312051f0305011d0105070c2405040c090e0304060e0424091a0901060507081b0d0305010e07080114060d090b010311030d05090604060813061d12 72
    0x1b10300310a6030140d03902c0100c00500700c106123618999504036881a82094545945030341e0700c1f0701c0713840e074800004800c1d0010b2030081210340b170907080c001e1041c09040d0000304070607070160608a0844280d10300c0b00080d100c01d0010003550034146031903510700349148280078810782001c2020b4111840813040d80e0890380c164075030a01da500d102c010480200b034004640b01044250304102103502440b100001d0143c00d11000008030045c20f034a82100c4500d040c200300b4414031140006200060b448002d550241d0740c85150b25840e90300b510a002900080101e81410750300c00c40c5050b0442c2540b6401030f40c1202c441c415002015203030110110341c00c6009001b9591003841200480c100c031f082020080500c0031325154001101c038195507812445c10342c04e07442600c0442c003420842d07205240030b1044000c1c0490741d003007807885c03c080396020420ba800389114100a000d2600300103150042c1e034409840300035a0100081104807203862585004c0d84422009101500c00c40c503080c0035041e080c034215466040e1181c000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 497874226 1250 497872976 497872997
    0x18140106050a0c12023a0309020a122003011407120b09040c090c09060e130f021306140a12020a050f0a050304110625052802030f070303 60
    0x19038440e80310b50a61401c01000c940060b0100e9800f08903042c407400c66902508410b890001c1408201d0012002c03004017005240380c580f46c0440081401c0c28072042810089000a070600000704203000b20390002030107004e102d410394100001504035041960640d80c072065004130200030302d42200c0c0c900490148041c020be01052060b40900d8a00614a01403000411060650404551041000d803011aa02d80301043e080c0710b2140c0074000c0c1c004051440c6400c03100d06142000040400141c0c1c41c0a90140e02c07008d90030b068804164100c60801500d032003095648441020b030f103114071344440c899100007e0f07203108007508040001c02147c806018039a036a200b040020f030b0164000354044002c400c2449810013911604948120240c03402d4242ea4440c60388901d0329052100300c0103401048284646c2040010000b02c4d00600fa1b81da08114201c2c031084105895464014580b05030111150300e4003580c03800180c0daa0051150300c0c0c0560f88281d054600c4c07041c18808a40d5550782901009010504103c070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 497875476 1250 497874226 497874239
    0x40f030b0601140a17250806030d08060a090b270a0b010908030a030e0c0d030c03020f0c01051803010b090108010603060e0c01050a0c0305041d24010f0c02060904050a06181401 77
    0x1100b40c0101001b2110700d20045401240450064100450b10100305504d041007060b05e4280084502c0405504005c035841ca08170b0001140481c19000c3c42401030b5171040c401e905a107031100f044040b440b80480b16409105200c2d400d20004100712548221681004c501441951003511868222007480c802903040880445064002c0c20b400c5220b1405e03445402e8403410f540d50348100701c612081c002c0c0c642d242904840d0600070b091071f80300c550305410703544a549501d0141c1d0744042107c614009030050b400e50a441100042c1c0074140d89024113500080407400450050810f500800c02c40c0d01c901c00c10041c081e85a5202500d803000329499a0115406214080100d40204091842c951003842c01519150726845405a0614038080b1070b0100c2145400300105007815241078180d21010411002d0041201c5e40000c100035401c1104e0020420b08030803110131074a80d4011b607944100010414002c0c0d01c3c003003008130b00a03d11407185038404007100c074005a80a041d4800e08220392110b5400e84002da00780388 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 497876726 1250 497875476 497875517
    0x30109030e060d0b0301021b07060c0804030201200d02072108031317030c040608090a211103040801020c07050a1203051e0304030c0b010501110606090a02040f030b0601140a 76
    0x220f0841c003507403101003000130340d42c0a02c02070520500100c980030342c290411501c10700c0c2c9020307500b28a00b801084a5803902180d056030070b40d003c503542460000304800600e44002c9141041c1c00a2030201d1017100c0c01e0701c2d40c0d641c0104211041e40e4080320070084d042d18401d04802d80b02c480329009810a80100081111170f10921a40070501340100185070140d0700c031403141802d59108a880040ca407030045028400e89520003507103074120744400d0081515040ca0b840b00c0e080e05001c00c1d81c501d440408401c800c00c00a0041d5905000038071000240c94030303295140711300c40c040d501c8005400c0d00ca01401c00049800d00e03082c035000c2e05440d01c100002c0301d441c0e000d40d01628940d1004004c481502d141c5a100405040c1080003544254440c1c1e413204c105040030b140012101700103803c9a410311500465141805400103401036001c40102c4641000e5102d111584000344240c0c1c10090846071a10408802d0140d540c0040307015030800e9854006860308007030010b10500400c900c51000503513100da503440102000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 497877976 1250 497876726 497876737
    0x5192004050f010306080307031d04020711242701020d17060f12010f1b1b110d0308070206131208060a0503030c1e0703021809100c030614030109030e06 67
    0x1810000340780791300d60121507e10381242d441200003490342c0c0e9602c0100280c1012060001505980550400c45565140041c9040004025000e10212041060741740c402d6034001c1c80303000c000c8050329a00c01d0704200302203088140050440b00054400e034904c485510000300e03018000b020b07507140360302410514205140d800340580541d900150a0740031551940d40c41d680e0b8451002d01d1400003d40000044919091f152045007003070589941a160b00d281c650070490000c0d00108540b0301d1100104646404d08010400001c100c1d0070a04c0c4081d03400803d07030001e0b2198054017181e02150b4641e43c4400860042100340307080107191580810035007036201e00407081c50307800c0b4000a010759065629140464a036401245620fa5030341e01203211034900d030750300a0b020500031b4081e0010744600ea046802107560740004c01806200c1c541c9400c00180008424000120b05030b02d80d034800d120358812250002c000e040c0314000c10407525030101000d080c5190510440e0001d9926454451141f4051030410206030441d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 497879226 1250 497877976 497877979
    0x6150c0c0415150f08150109170c1c032c0301090c0504061a0307050a110f0c01080705030405060601141c090303051f140d0605192004050f 61
    0x40c6403104405985078007440100060903103180d1041460f00300504440248400714406002c2d01450707203e21150300034a00e1740e0085034441e42421a00d00d800040310a0078440c0d0080038207002908041c801030201043c0c43c40c40100131594442d07459001602d205003181c03031000040100341d483c2903100c6507808580740c05902c5003106803610b24040ca242c0110b401d44801c40c0e411298050403040611191905118000c0501016407000c000c00e0030554910721030b403102400b00c0d0b0601c40b003c20618281da218000000140418030280c0d065402c1e004c102550b541045490079010983c0035001860f100e10500036684101d8000b03004002980f504070056a151600309094841c004041140b0a40c01907469000304600c41304140004070419503042c01000c40e80090680750048c00e8030b00d80d14154828a41310f5505503000110701d11401184800090483c240040b40100b003142080108000c00070f0614003028650100003040c0000c0078001c641c490320a80e460402128420284001c1c841810040d4030030340c0b0b0640 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 497880476 1250 497879226 497879233
    0x510020d17151008010608150f0402070c030c03051011070f030c020a05031203060f030f06010b1804050c0d0f0b150f041d10060801120b190e100501050906150c 70
    0x400102084090b8103883e220400b042c0d44a004001569001143e48d902c0440c80c42800d80c1941000e0004505280c00148107100c1d540208031203091010060300030b0b000f5a0300048100c40182d03289440c503140c840e80004114038510304030400d0092b042940440d1451540840701d0000ea8032299416030310030103185030580e00031100d0900401d10391170402011034041c000c1c1d0700c1d2940f0b17031401604000a10800c4070002d0f00075081088000000c81d000070f03d540c1554619507555403603402849100130b4060768041650351141c10031080c4500e4850080040028490201c4240120411402484192810350441c241c01168181e261060384141d8030103031004802c101050340c40c140da10100402d0f40745000b04812031003103200061003403a0310100c545400034011410074200320341c9010324081644503182e0b03019001d5940c00c40090000015400c40041010000c0810420800c2d82244a956044500c100c6181e140c40d04001196901d00041450b200e50700061140300f030310511000e1101070382c0101010390464803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 497881726 1250 497880476 497880511
    0x5060d0905060c040905250f11010c091d04170c0a050714010801090510150315081b03010902030c010c020303040f0b0d0632060f0f040510020d17 64
    0x9409201050103100f203011400c1e2160304100685045039405041192000111034a5035174540400048180f4180c0c981460800080c2c050000d6400d90008054084103501e4130410700401600f041480c0161282e5005113800c0080000c050381981c04107480240c0049650840d0000b2151164000d02118001c20203541a0384429600c2601d40b11a581000030b41418504011045503440148a40144128074091009003003006045400703000c10f00445004c0ca400b8031001d4400c50007904984814464140302198003581c9224964a50044000e1101039014081034490705150501620450300d400a0240c50741c42194001982c4000c440fa1342203800d400103210008184d1441540580200f0758012030554860100081d14125107003038111a440d000e18180c240d4000e038681f200c80011040105800409412440000d080c80c05440d4258512135000504140b840300640c0140c400c0351822785000041e01d211000a0f600c1c1c5030612004000209101c1d003056072000342e0b004062700018980c50324185c44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 497882976 1250 497881726 497881733
    0xd090e1b040e0f06100e010c030e030d0306050102010c0f08060d060612060504030201050c0a1e05040f0906140402120a180f03020a030207050a0506070602030a11041e0b040f05060d09 80
    0x1030700698803071205030340901c08000201a0000003541d01060459010b5264402c00e03d0103052840c40545560400c007081e07040c0010580500009c64a80310001c0864600ca80c5403030f030040c0907003668010f080c015400d0100d020505801160341502d1800c09855918160b030718902480310f9041c0e0740e89e00352070060b21204001a4001c4012000c2c445c1406400d0200320762502e4207019081d41c2e00a003071146a03070f004016150fa0250305c00107840c1c69010010b801850b01000310070031561030080f50001c10b00080001c0e80016404490350100703048401142c1c1c0003a131403d40c45c00b08001c0340621540d01c14507100400011b00c01d080c580e407191030b41c550707a4603007251484010345030b56585019980c0c085015078480c078806014590100007040c0144000c880035a040d034141400b00d80c8600808000030541900030010851141040d00500298800d6070b0010740c0341c5540c1c400d2114260b5040300c060212440348803020074101e00d01c0040b901a15a15501d100f04a40780000740041c5600c0021a100c1d8a55142000c0000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 497884226 1250 497882976 497883031
    0x3040315061d04050c0f0a0303030504050c120c0a0b0a09060c0302100c0815040501181e051005120105070206010506220b1b07031218080601060306030b06030d090e 72
    0x109082c20103032082c54180b41581c41c006000917098071601c856000412503648036071a0340196581450080380d5034483c0d18245150210001803107921410f880e04500d8003250004189a180104444e0120a19500c0403644564032400020800081c503a050500102d4000e08420355460301c688100c800303075440001584116240800c4400c0010f1080003446550b111701107581c109001e0071241040103515100101c8944c5048404003e88151117a805105000c41c103c29244450480e06040c030480c64100075041c2c040840b03000e064460f10340d26880c0200001d05100b154414020f80d00145426401d120401c040e640081f1540d5144010600d0705030b403076481700d1510308010820754440710b40b03e403910f000a110f0240c0e2441c203400e0541c050705007000451140c0f90b03030304191501d40c100010f10001d8440f0302180051141c10800340381c4070350f00000901d50380c0340c1c3c410412240104140d07141911400101904d50343c1203019000080c1e150031b404d012a100d00d02c907442e0051202821122100c5030f814042c5030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 497885476 1250 497884226 497884259
    0x3040b030601120c081902070c0e07080c070b0402092d100603180602030903040e090c01020d110a12020309030a050a1e0804180906090b0405010e03030601020304031506 74
    0x10220004424840c003540c210b960040c0300000b40001340450452114000c00f891001003d0400c07500400c488240442080e504035407003e40c0100071030001c0364039858000b01c050420f4900c03c0001b510f22002506003841c440642e10f0041d404041a001c5444580030003d01d401d002e407a0200c103140c0902011f60910380501c41d00154500c8d07407040c001611740340c1c415010b50b01e4240d22100900d810210035680c83c1c0441400d03024942d81c814001a241d40f03c00f0440b07455030041d03420103041102c000041c0800c24000160104a41c1826802c80303400240008080b40c103425580080242a4000340b1700c0e1000402c06006112490b81d144110781c140030303091001901c3c1150114040d56a50820b804003014001e00204924403c14640031040b503403041c40d92480c12a100b94443c0c0c491030500082c1403011200d8a81040c0400c0350041c0d0180040c6015081c5209145000d5074221740d29071030904000302d0f044000c400d50303108035016000345007450310b10b0721003c0038044111860300c8115074500010820501c40e0001c0381 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 497886726 1250 497885476 497885489
    0xa060b0f091503091b030f1203040f120203070b1005010e040207141b040f0c05031801060f030b1e06010e04180804030506220c170109170d140c030403140c0304 70
    0x3000103004500e420b0301040c20031555000f50001c01424410b09400128408c20901d25040f0517601c2d5250706091018a240003001401e50001d11040410719030300002410307055014800b850495222420201c412001c1c910070702e0702040501d150641c862400b58054030109016203100b0944c20307818502d00c0d0600700d445041d061100c0002c1c131454618106407107241e100004904080041d40d0100001400b0b81c08001c154410258881e020050203440c00e401a00c010840c50b5000754440d6100c0c038201b043c0003812640c4400b503240149070075840003049010603020301c206844081805580400b031101400030300c0c2d00c180070007009a203080c0004001c0c400900003140200060300e21800c0200a40e42040c8065040c05d1004034040c0190004c0781c1c0d81590481152045020b5440180c901e13101a40500f01407070000d407800c1e4a841c100300c4c0b41d044540061603121081c0600700f0000a5001421200d19400d8400001e0727682d0500002e00001d0007089484a0321a5040825081662480cc0705203184d00c90380011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 497887976 1250 497886726 497886733
    0x603060f0a091a030c03150613051005010311070c09020c0a050316030306120b010e0a0e01020a020d110106180c020c030604080406020c01050702060711060906210a060b0f09150309 79
    0x810b46194040202e4810803049005e0501e06008400281d95441e0541d00c041c00308403000042015075035100400011f510400d20309002d0361034802003140381000140324050109003030088030403010300c100c42140c440e994000040402d0034201000c48000f074007c01038240301c2d48a6003000f6408200200081c5c09903050344035445801e0b0a10389002001d8030100c0e8080500200c81c090726000081000007801e054503103010f0400302c40da44800300c580103040060001c1880d0b51000a5030307480c0d0f95000c104041c2030030351030301e82c20b00060900038100d00301d030142d00c5920480342d98441e000d24011b84582101680c1c42c0e00d481150080303907248001a08085088d107045404000001c3e00f000255014002c801e1102e000b400c1041c00c044039900455690700c80e501c0002c00d582c101e00180740696580c01c0c1611041480645060b48458002e00d100902c0300c6003030307201c00340341a4100003c0c0042000b0f02556054821182c2d4141c00c01100702e5001105801011b001503010010341c040b0742101520380b000e1446001240001c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 497889226 1250 497887976 497887991
    0x5060c03040f090b0303070b04030210050906060406060912020402070204020f030f09010b0d12111c11060a06240905090a060e06090f160215010303020d020712050a020603060f0a09 79
    0x80d100c1d2000d03074031580055080c280c604c070382c0742d40c00700584001030b030000000d004690f81c502d804c074104042406045950b44c946003c1c0500346000082c4a4410242640c04200c2c1d5034541c141641c0c030186074490f80d858608002d5082e801030403d9005080914406000503040c030300405032424868104880c01241038400d00204400c901c02401031a800000680e04800540042d0700c8100b1030030903a21a0303006001c42a062080c1d407000403c00c1c49007401d62283d005030000c080480040c0807682e516441d001510802d004181268054410700042300d0356141564507180d109086415015415a444410300010302c0000a80d40c6800c03002d140710710020384000500c6410140120580c0300080c0c0918090a410000c00079040c046640154010b8560400802d01d01c841850803840c15141c00620409062144000800c054002410303003c10166502961501500c8030181c1008401211001d40281d01100c0c909015003412001940c211802604944e455a2060b0100362044519800480b42c00d13654035a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 497890476 1250 497889226 497889239
    0x4030f050f040303030b190305010c020f07050303090411040801093905040e0a140120030c03010e13080a020a0501050a060302030627070602011a040525050405060c0304 74
    0x8020002550a000e030a280d8564420981409207000080a165803080c0035803460b5510b04001c80034010b80d00510b10060b840303160403400f03005030741c400c1130140c4118000107103c0700020401905450016005508010020f4100b0000d00b0b2856030407040c11604110120328034500707029000c20b41d8062081416105409412445401e5102d048003404218210b241003400c50703014010350031644100c50100c0e2044010080c2818081010f02c0204540e01c070021100d80c072141900841c44140700701c01c0007050024641d0242030244402c036454103046000700010310043d000a80c10603000190030107103204054580d0754082280d48801981405a401143c1800400409024075a03102001440074880d561840e404669902e40240c04110004d007110101d02903c0040f41e100c0320008505130440d8460340d0784040290017000580740b100000000451801181d04160040c50300540207074840360b010b01001d094046240200860b1103041200c20840050103940700d1019010800c040c101444e0b94524045 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 497891726 1250 497890476 497890487
    0x70206010815090a030f180f080115320607081201060e010f030b0402070c03240203070804031b0c0f2103020c150c060c040608060108040c060e130c080403 68
    0xc008401c04415001000f08103040031810504565250501c103d60342c411a805550030460010014946404c0003800500100d00c240c0503811640040020401003064080d403003102c404501400250f41c4102c156211050900304c80700c81c041e180340740d1000c901500e21000030041e80c40f0a0041e40d00800114000c0d412800034040180105501e0403c0100c3c15a00c00018294503d51041a0241036540da00000c1c683c0711034044400701980201d00041032501c0b803030303c088618007001c1c100040c0c0009092500008641c0d1089a004007219240d9460310340d990b607004ca8902a0001c0b400040b82c82c010003030800100c5031a401c002401100c000f203070360f00d402c0034048414685103074a0102005008008580420b401044240300e403607003960302a6444540e11140c001911504a5035503031403185c01c2c2000100d51100b40a003040c1d60f603960314115580c5481e001110641d00a0303034090506405250100510f82c042c00c26a1440c9802900840c500c40003801e560044580d00304081c80410156402c2104055210 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 497892976 1250 497891726 497891743
    0x406030506120f060a1109300601060c14010b040e03180d0c090c18120308070503190f0f02030a05011703031009020d0209030318041b020303130c05090702060108 71
    0x1d4000c2c41c1c6041d0b590f1a0580d2070740040d2031000a40c0e070351020540c0b2a0300140032a640301101904200380d088c1a40c80750042000c450014205410303034621001041c04012600f2812035039169102c004900841d111a00c04480c080c82c070b007056641c1c601c80181c0b1601e60340603100d10340502d0400355895841c58040c07076444880407140c16219102c4130740e0f5000041d00c40314100d07055074031040c000107406c000d119040d128003203034850018821100d204001080003006540102030f601c29551680c40e070b00c81c22400c0e00c6034041582c55160030b414500040c884010942c1c06401c000c05524004517450444441c4c07134089030f00544503011003d480d2401031015258002c0e418100c1a00b100003140b03185002450f40395680024000d0412035074000850807000342c00358040da9800342000303094070fa55005000200351681e05a81605004909040000c50401880d00c03825001e0710858001c1c514654034200c0c850300081c403c0804464142c0c000d1004109900c901c46420f00c80c14890700101741550501c0c03070951505c1c040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 497894226 1250 497892976 497893009
    0x81c0e0d0c0e06040b01050f03040f0b010305060907060e010c11220605120c090a0b0f060a0e0a09020f04140d0c0b120a18081e0a02030715180f15020406030506 70
    0x2c14031040038070390303001c0c02305c0d41051100020940c4988a600d86415106039082c0c010300000888400401842004a0030324011b15020048400c596500d400503101000003180d010701241404107001301117081c4000d84d00c44160002c2200912001824580344541d4007148102c643e80c0d030300c4006008a0a00085050014100c2c1e00103203031050010b4001400f49100400a10304039848030080ca070241ca0307040302e509070514001d0103d600d505180c00000d0001414100c3c00d0b1107610f00401c0024000c0035442284c280d48011000e003454242848060ba01a5001c820810b410100c25400000401c1904904802400403c0030965031001c84444442441c6006443d03200f200f840e01d00c00204e0385460503140c0d0382c050380c0140720b5500c4003d00c00a00103140e81c148501841c82400140600487d40c3c04002090f26a101e19005042440011031001c115851600349144900e944480c40d0081682030780100102031154625280020002d02d01384183d8200e41d10890210b41c445c000d200c030900d000080b0f00c61aa22 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 497895476 1250 497894226 497894231
    0x6090b060304080a110a0b0702010516080a18150501061409030714010210051519030c050d1506030b01140d2105070204090b01080105090304081c0e0d0c0e0604 70
    0x201200140d410300c00604024400c01001945078055400380b0b0004071041c03042c4094030040301c0c103414401000c51044851a00551034180040e00302c500200000303500c4801691384039015070700e2184501c01007105514410200700028a00b00000d0500d04850b04100000c81e030204140d450030101074262104000c1100e035584040c0000503613a01c0c00106c0408469060041c3c205492038030740141d08280074a0791028100d8141810001e082c60718001aa44c07080301036030003410448220201c61303540318003030000412844a08204020501c1c00e40c41100c0d9480c0a5041c800015130031159510460300c0d140d00848120780004010440006a40b000ea868100c00b40e172441044141a600c02480200940e840b002e5000c09611110940340b141081e61301095000c0c2041210104906011644060034440d040a941c00e04001a003014004416902140c09400090080c1c07085407010301280f0a034103101104000d001000e100701559800f8401c0421030295062140180c107000c11404040c0e00202494022030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 497896726 1250 497895476 497895491
    0x120f070618081801050f13170309130e0f0303010f0e1b0304020114130932010b0702010327050c0105030601050406030e010b0909030a09060306050f01030903030608120901030609 78
    0x64403481100d2502c0f0340030100c0b05a05010100603100c902601c5c034020790308200031854207011030504030070b98181c8607001c02c85000c091015804590b6482203c042c2c542203007c2c4410440d2041c0c041d001a4001008501521000c0e014547da442c55a0070076448810070410f5031108200e0651020020348e04425840c0e010400861007510885044c8800f40000741004030800e00a03151400c018140c0b40124040c000b81403d40b076807805248041c2c200c0308051082c000b05228000151201072810b4032005000122400c01a86080070745c2c402900545002c0c1d06140c1c44a8032150381c035400e400312044241c032040d403500b50202582000d501e4200c040c1d0b82c0c1c9050020030814400941c0e007040944040303a485140124401c1038004046000d08800ca80b0240c0207008542441041c410200c090150242030f595195521a40e5040c120103450b858491181c1041011000000c0307540f00e60485054103000342030106029540d25407503403410b114034208049a020115201c1130769030f03250141c48018078604405000e040c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 497897976 1250 497896726 497896733
    0x3100519060f02072c0f0609071407020907030e06070c111302070f0506190b10030f0b0a06020601150e0609100c050105010f170d17060102120f070618 66
    0x500c664003880003071000350720806014034070800c00721004e02401079911205c5030b402142502e40075150003081160050a000013007005124400081c45120000d20000480d01c030650240c91000c03105101944540d0200b11190150302ca0f102114091400c555000490703800030200982407400c003821403010000010700d0342001c907080c1100e8010042c01100c4081d00c0b0352107800d50000920030765000500b0a0b031120550400c1c400080350840c481c034800c00108417040e05a00c07450f4200e070a4618403581c0300c1f41e2010911540707842507024a285885003c00001c2c03901807900041c0104a25600840050b40000e0040c004000c902e100100380c044541802c02803e034400e40096490b00440b56440d000da10030003005010305120b400b0000c0455007001c020000d55848492943c840d90260180304040841a0031030458564005011100700c6d00e10340d15100000c008001d035102c0b144e006400181140718045004803102c02580c001c002440d02a103c0c00d6449440b4034140094131540854880b140b0342180c48035020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 497899226 1250 497897976 497898019
    0x20a03030e0102070906030804050901050102070605180d0818040b031b0d0602040b030a021e070206220801020a050310171207050115080102071704140d0501020d090305031005 77
    0x2a00d500d414010802100e00c00100c1c58005540e011240c458101100003080c040c1038801041515000e4411a60306d0303072503900580c1c1d43da071288620000903a0070400f1001340000034001070304440000300014803420309a100c5001c540c000380d40610b004600c0d800079078000e182070311400401c1c100a502400b0000c034411581c842d40425500c1007030040300729200740420003100d0740c1218094150181c00320b880f41000d843c000029049071800e0b0781000e071212034040d01b0001c02000d480507180d0041c40280360412103015003444622071003008040d4200d91401247c548006c3c00501f8445c00f480e42d45d40e0b02c1c0e280142c510134a07040e0f281e2110311782e100b01d541e0030b400003100460800200020400e885655500741e107000c038010680c049010f5680880d9910114654506400030250980244d8840490b00355200c032001052066114044030424019450b1451341400d180014103140100001400c0451489288003501d00480044000980010400c590280f541051070081c241c10b441b4610140e4000f0802c0c000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 497900476 1250 497899226 497899229
    0x305030603120c16090b2d0307060f02160f26030a0203220f120311010908030402100807050d1a2e080103080f0c012c0c0301020c19080d0e0304061101020304020a 71
    0x400030001f041c1d00c42072014540b681c8100030006c2e04403042c4d0341c2d82d2040108114155603409006002d0380c0c600d1041c001e130311002c05054074038841c15900c40d01c1c0707440b6545800aa2540d000b43e42805141d10150359040140007130301c4085040c0d001388d83d0361460b02001c0d12140d1407120106100d040c80400c248081724884c0c40142c10b442206a4245083c05607080c00d4076480348c0000300d179010703600301121442001910307405103009920a80300040b0403c02030005807075086003220301c80006442030040e81958940f982101e05803010260f04e1418404405020803603200d10400454072150b4600e40c030210403e400e40c88405145901d2900c1c0c455941595501102c40c031401082c12664a008035641c42e40b14029882021421411041300c41e408100c80840850f0386030104208120f03001d00e41c0340b11a14241802110491034240b0f0240120708141d42c08030654000b07040c0c003a030340ca03602842226020051445980b4002c40321b00300031074590f85001c0c002442c0c410036007101c110990050041c8001031300e800402d5170 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 497901726 1250 497900476 497900509
    0xe01050103021b07030f060c02033406062903040c06080411060304150507020114060405072a020a060e060d0e0c1c06061d01030305030603120c16090b 66
    0x160f884a45084400809a42c510080b501e8050340100004010410601c0c481e428419101440394100140046e80c50307000308035082a40c01289100388602022442c00f071608040c5442e00721520350402e40f100c000700c0c0c0064201c143d034600c2d43c80340d080352401c42c010500400c00ca10307801c0a10f54035007551401140a400c3c4507080900005101040c2041034503000310301343ca0400345c04c6d81c1d100d24240c140461a540103c0c200c1124914090108101c144113004003842100d016102c15181d88034072080c03000509004201c4c800f0007403000303d01d0102d411002c40010b01100c00454140800401e03004004805140380d0100040c4003410070040140d0711080260b450100d2154400100d90103280c002c2401c15030321040c44c50340204901440301c64140820b8000d07000c5405000200003a5441da03681484807265525680100f450500c010000030344508011540030070047e00b600e41c0c1d011107584c008010b4115081c4541d807500403440041705000d040c4909001007640703c8007480205080b001048141000a8008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 497902976 1250 497901726 497901731
    0x9010e03121005040e0a020a05040e190203070f06020d0212032e030507060c1a1312021f0f050a060605090402071b0902070308011e051e031204140a0e01050103 70
    0x140403828280702c0b480061001070424014811051000c039202e52007100c00302e00c150407050010600b410701d485110140b03c04c100051402410f88a0722008900700c0d88001ca80c94452034501250103487c000b04d910040c06150000c1449001c21100030303050031a5003180100e1a40d0510402079482034200c0c0c111a001044002425070003403250b09019414216040a4400d204d40880000c92a611a0260803444e008000f00c00122466128010442400750380000c0c4500c0d2010740c45010464042e1a10303090081401224207401c0300309a560282190b032001c03132000d2a550420121140080c0c025540c2c445003800e000c1020b00e041032000703095805481662401150f010407000204200744090300094070010301020302240d80c4044440195000321001c60006540100004d0701820810301d038807200c8075202c22a44c0d45800c2006000c0e440611a0340318900f040305407800241d544041c03105800198030700510903919802c201c5000e4200b64080fa000d409600705400c2000b0081c0c05002c9641503450901c1c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 497904226 1250 497902976 497902981
    0xb06090901090501060e07020111070803010b0c0a060e1c170c031005060c0d0e010f080610050f070b010905010f031a0c0c1501050109050604121101121503050609010e0312 75
    0x4681c01021002d100501a6192801c0400c1d48040505014441c01c07182d8000c2c01410341c1081c82c0c40250045030340c020030118081c40181320b100c496a026000842e010b804440500b40651642801e85441702001000350700048115030306040318811007402a2a80d09100000b401c5500425111100003402d1a5510314080082070340f1300c5402d91520000c210083c48030707440e40448210940c48040040041003c20b00d8074030030300c1d501d5006e010281441c09151300d03204056a603c500384089080c00800342c8003008002c2184444421501015180c154010300c003200c100d6040a424004030742c41030b0065030030503814060800020f024940c1607016401501d00303202544c0c480a214000f1402032074404902401844504400780c1800408281212000d0341c0700580556203e0500c201031160f400741c01d070f80354100c5942c480801c40c501503810400f4010300d810500307800400d00071011203000a2081040910709682013080c072404001041e00070040c2c10007044041d02c90003000703a4a01c030b090199640855802e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 497905476 1250 497904226 497904241
    0x24040f0b160204091b031a0a18060e120703080a15080c0105090f0306090a0b07031e0203060a09020f070203010f020a0f08130503030403080f0a09080d1812030b03190b0609 75
    0x48012111900d01c0e1041d0203e80320318000106240107004000d0808004c0e000801c0c80c0307005c1c02780d0010041c1c240118000b0031a00e0319004007404170a40c6c410503912401c00009001601c560007040038600950341c0081e03509050000b502074a109841c1e07210b42004003041401000c0000c40d1844c142502403c009585081300000708900400b0318450b103034140604010841c01c00e10110304149880e01c00c20388100d40b643c804c101941203410b101421a49207125003039042642504d6401160491030051411030095035659102c82a68481587c056076007a021500740f00f1400e09019810814034000d409500b400c981c40030060807070f9103480407141080065004503600c01010780030f0400d60fa030084192580d07454203081c082c04000301920031200084556000456184103441075000f10b0364010905442c01ca00410b0b260060200e22400280c41400c295000c2c0000d11201c105604910864070013145c2d40c40480200f5041569084100c501e000301c80d0f081200150a03a820306030f014100703c03003800e000e85901d031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 497906726 1250 497905476 497905493
    0xc110604060804032307020405041109071116030206090402090a1208070309060e092e08010e0d1704061802030a0c033e24040f0b16020409 61
    0x411190812400203020441d036a102c00414400c03402a192000c81d00c0b0000b00401c0f01c6801c0c2012510010700c2880b841c40180780c86d402c142d4029000e10300550340f400c0703c0301c00038241200035941c0401091100d07441c42020101404203480b080c030004440314681d80382da00800c00034400d4405e49403149500040e41c1119079210980c2202420310703158103203044851480c10035030540c052403069010032590240007036494840e02d241844040b0142080c0a1a21208540742286100e820110000c005020a08800313900489521005010303840000c1540d000b22142c2e58104182c0302070301ea0401c02c41469070b0007104101d11005800c1988080c00040040d030300302400319200c000100080d0f260107850354010030310010900c60010359014200c604900408010710102652014001c128000c4102d048143d5450b202031603075100340c1c0d0107840c0d440e210480d0741c0b54003245907100d0178004140c0000b0809100d05207010072120003030106805200c1c9411a175006402c007816190000a12860b110700c03a0404006422 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 497907976 1250 497906726 497906753
    0x405041d120c0139031b020616031b050904060b0f070309080c1e0a15090807050105070b0f044103071a2d04110307060504060c 56
    0x800c00e860064844411140141e40008920040381d820940f84110a85003405880065110403c2c40085581c00c03a908090040740d00070302070249076a030504100c141d0b040c0e01382c01c1c1c06504903501601091810456410b02801c3d001c00a404040c640924101c0400d542d0031451880321003410a2a1a00501c034002000ba00b80e0f5000301160413004101c45c3e51001802019040c00c5220b501d5540b01d25807a000c60554402c12640500e0b0301c40041c0b50412002001c0c121514860f48000e0310700c0c552152148844483c500f88401c0030f900240d00300408000c1c4410600510000c5d01c2d0904c0d180346010810344550b1100071001d03150035180342003074000c034003004002c0e020240c003100c5401050310140c440203581000c001905422181c8200300c0c25400a80000c0801101d6056a04c038100011554410903100004c21005140340400d0001c50302c042c07a640d40f51800c104205a017a04050a0f51910745404540342058450707850096000c1f41c0e00f40310b09070b0032400b600c040d0361380d600d44884005d05c075003403110081106 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 497909226 1250 497907976 497908031
    0x10b09340903020d3002010c0206060f0f13020c0d110703080f0c01180303020406021204080703290108070512060915060616061416020601060807031b020d0206160203040504 76
    0x8554111043c2d03401d0b0f80c51740081d4400d5400820000d008c82d48103a80710181140c0c4154015554595641c107803610010070100300c07034050030150309080d03100144c404a9110302c069410545c41800f4070300d80180d01c240818000c4403088013619003240307141c1e95641a8003e600000c81049004911031101d00c0d02584000812400f550051b14060041e080c060001e41c00790003010018092000c00d00c00782001c5004890440c0c84080040c814985951189600083d00b410a403041400f0340c000d1204e50b000105006010340b40b1100601405840d00080000e912a8964100c007030390022400c00441c02400706100c0481c8105116a40f0550380c0d110001d41035103d07110408542481d07000d0344a092100d9a03000070b041d02e140c10f02070441604c400000b500c41c1056070202d480141d01100040c048a8031420340c594014880d0f090100e503060100c207621248100c164003403001a0300851603600742550400506412002c2100d1034080e0b0b81021900a44070b00c40c50150501035511000008900701c0620403013666000d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 497910476 1250 497909226 497909273
    0x80702010e36070201021e07020103021e030702071505270d051b010201061203030b060d0c02010b011e1706030708070807030302010f021c0b03010b09340903020d 71
    0x7a2a400700050b0000c501e0800c4a54145002544880c0148211107284a0805030590182051403c1c101c0c217520444040b030402d9000e02c292081d2810200c044101e1020402410703490703280000000345444100d0b03008800959440c000c1c0d980d080e8002c03044641030080c000300c540c0074002c0803d402408503c2100a9500290200d6600040c44004262009001180c00d40e000807060750320012420f80c4c185002e007012079010720f4580d200190280c0c1c0954a0804040c1802d0308051610b4281c108450f0b8404812000d45d44494601c0d00640c0d225022208200044030212058060310000a16109500c2e0000c862044c80c4c101040031035508200690081c480e2004903105151034a6075241c81c1c500364401100590308080b03600514804da070080d554000e11080074a0302e001e4600d41c0c208007810842d40180c2c2c0555035180c8a8403582c07101d00c8024840c400c101c40e0403070212420340f045002070110081c284850100c182c1e101d80b100d6480802002100d4040301e5a541e041014142401d1141c981000d2501400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 497911726 1250 497910476 497910529
    0xb030f06070306030515070807180b04030c051c05030d0209040219020706170717040f0b0c09010e04090c0308070812041b08010e100c0215180118080702010e 69
    0x1c2d41a00071030140c910503002e40c1c0d0b41804030340c3c1c01c6418601c241e410b04045000d01c000515076074481c0030180c1c841003038070682c80c50095807001c00d0100c070762040c1c01c140d41f0101640c03c00e10085c2000d4211040c0b0240750440b001710b50200fa1140350322030113040c1ea03040400e600016085260342c1d40750199140211039007582a110103e50038085d50340c01c001e10a0401050060540c0c00c6030320350115140b4441d0b221511030740c0300c0003100c40c61400759140090044852000340a40e21012401c9561309510070142c10032140e5460f2100d81c00508040d680c01c400c140301c0c81c18002143c00003008044103000303c0c3d07806844284c4a4103985006202402014600c0310603680344001c1000b404143d1141815001020500300b04954942c124503081e100d03500f85048055201d00e041b0744c01006a5401702c41c140085205a031004900a041456101420745040c012014641100c211502d428420954040b0b00c00d62881541081c03651942c03594052a8000b078140051111405059101c2c520f529800810755645462240c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 497912976 1250 497911726 497911741
    0x504020301120b01051516170a0e1903210302090312090906060301051e0a090e0a110616030302160f140c010e0f060c210415050f0d0b030f06 62
    0x146440549583c03042200005050402d1144045c40316410550300e441d010345605000c0b924580d0141c115090701c1d2400f91b210b040d4a00314003514002c44a5070701c000c146039580d030030031505c0c43c11110404625049001d04000003202c24900c0c442e281c0251b0900341821000d46011b8009004401c03215800d80280b50511240110300e40040000d42c800301c501307684507120302c424000940801d0203099041001d4941914030b9111a00303d40e40c9140c0001c01d0350450640b211921004e640303071141c0c00361880c0e02c0300507503500708600c0c020b041000510960f011428540d0008558031921020703d405014503a0019000107406100c0d040c5280c1c1c1074000b40c000e40310148601e04103044803030501e007908960160040c299055846481003e008038070040030b100d6001e02c02401c000650780420744240c2180b24202d40009031190100812000200100704680c0743c82c40c09880c07101046101444200700003080102005a520000039900640320010002802da0302e0440802e140a036107090006143c8600e20810020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 497914226 1250 497912976 497912999
    0x20a180507030b09060904061e0b0a05090f061903021801060e041a0f120d0203091504080a030309030e0a0b1c1407080709031401150506090a030206130504020301 71
    0x96999454080116075203420045049910303a03980300b6441000c0c1c201080052411103a026005130041000040d820b4a01e045908141ca2182090000b5a00c80580070150314060007240014002601e2079400b070314000721030b40c014140003070010303201d200d811520711201c06c882c0c44038002941e0b001e4203030700d038001035041d503880c13400d80034825031001030143c000c0c0a040d41800e00800301d07507110703030280c1009091400041000280d01d08406a400900d100005070050404200b00e110500b2242c01440d40c40d0761000502000701c40e04100c03208224020070081041e91000200894070680510300003450b11000d26003101e94074591344406a004183c004081403410903140101401800000c03110b603900c9544d42c50380c054500b11400c25907403034032540014004602070142e0350780c80007a6141000256480c0d03a11841c48010a9617402c09030780d0f50340d02c0f030001c0b2511410f00c14045c00c0c0c00c03507403d400c0804120014091407090f0000900891000c102400c4000d41a454007004e810300420a644030340c0c691180030750 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 497915476 1250 497914226 497914259
    0xa0804030b0f06240306060f0403120206090f210f120603010c030b06220807060f020106121e0314040b09040b0607030504030f2108040512040f061209020a 68
    0x900d03201e10008601d00340f901c0d1186104804541d808204013000c1c040120603e0703040108140c1c1c1107001000168812000c1c03200030070203140702e0b0300704175000c08903408000e2919030020900310b040e5006c02c41c1500c46000c0010411802d80c440300f6000e4a45101142044580c0101c00a51040e00740108135500307a18a90220540300d5101035000300420340240070210140c2d007100000720f400460030000c6001d01d00100a500e40c8041084440003400c0f981d0700c10b40c0c0e00c0c001e076540c0408002100921135108440c1d0a01400d0000c01d01211580c2c42104c85486000c102841c80803203404003000341130368404160296019100740d2b05203a00190711241d48800c120455400041d400d0700c00ca1034005000d49900d002015a0027540e015968981030074110741d900b600c02c4a00706029241c9025002003507100c180710703a080c007603103001c3d43e0340701d02280c201840e2540c5810054001409488400d2000748064042104820126181d500c0c19403070840350710719a01c004101c400c0c0040c1d0850b00c01c0c1000700b12000407085401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 497916726 1250 497915476 497915491
    0x80301060c02100212090f030a0503040605031008011e020d0e0105011d0c0a0818030708040f080633040608030f0301030311060c0703030905100504050f012909090a0804030b 76
    0x82d0f0032500360350126100c03905240207402180007400084c0e078505210078180d841a1020b011940c91f9010f0f612100c4c1b41d5040b42c0c0c03117100069800000c1000141401c42d0340002004a44000e0014211080403030007816401c1404405003640800c4510f10075040703070410011050160020005540c594240703020b01030840d401c481c9104e4105001c2494005034904840103401e040e55815103c0d1500c81ea0403292072a0064800700d01d20062007402d010617100c1d401003005240c0e82c2d9140e41c45900c0e140146042041c000d02051908050341450001032034448003080130088450f25100074100d00c0d1001030010840c0d90862141e52201003000203c040c2030000950685c1c0c001c0d12040d04000c0e103c0340da81c1d9034403002c43d0000c061180c181b2032840080d00a8200c00e035000d203d07a083d00d0102110000480890f40304070750903200c40d4441e20022424001c207204031144511152544450141619900100b29040394642d50191801070002415048140040c481c6d01d13074007041c015550355aa0030030f1142040240e5010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 497917976 1250 497916726 497916739
    0x1201170d05040e0609090a0b010e0103021008060d1e050106091a0a030c091a0303130303030c020a080702100c080a02010c0e010905030a060510091104090501090605031b0d080301060c02 81
    0x412845000e0400c2e2801c46901d0204a4039a644410511010440180550303401d84a005031007000a0407480185001c1d1510103102400741d0b140d401001744a80815184805000401c0300340700d007030380340c254032004040c0d0030000307603599001032083c2084c5403a049100a0801d5203002c0011400c18841c5d08095483c40d200348146100448100c104184a581c5100041c00134524403c100a010450f401c1041141c042c403018010201812010a0079a440302c42c0d9500c1078406aa418030805800d4480d1032a0a15184010202a9130f9030383d5901d80780c0b0500b0740203441000c0043c0c901117114031550100030f600d42d000c40215127a88c4404c4010340030340800140710020074415414a03c19511030052401105c000030028451180b00d5114000207000c00750a1741103041000c0000314892040c2d0007501120584502499951480c0030b868108442060b000524224104041000750b0f6500180c140c40154134809412581c048135000110101c0c4159401440c00801000008900e5000764003504c1c0380d4002c0d60407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 497919226 1250 497917976 497917993
    0x50c130f0e0312040308100f0608060a0801020c07172401031a25021203100f0e060a150e040501090b132a0e040e0607090605040f1505120117 62
    0x1d480f4050310207040400112a40040c0c0401d11a034005500004100c10102d1007070340b0b0340750504000c055500104081f416000c24000c1d00c0c1820b4620303a00519030302000314148048040303200e440740024030a0344602c1200400011120109006c2450300100e9401c0d034400c407441c00c040c7c0c4010442d091000f6503c0a80f55941c800b5440110000a481400b91146103050001c00b450200a441d86940c000b808510a80615401c0d401c64803000b14054003d00d0604081c940c07402402401149507034111141008000c0c0500c055901c5030b03040d20b41920004ca94080c105c000300c0740d040381c8560254120310751023804c000c000100901300d41c2c8411044003007991804a0f00da0300c1c4208000755035070b0803c200405c4141e23482d1400000cc0d04283d05c00d45400b6840c2044007071684034002003c3d10764000400b5025003080d4140504c2d140c00010f250001c01190610604041c80c2c888100449520f174810140c8054450b001c00100700d1140f0125003414040c000740c0f503090358440d171700071a1810700e110002c4010300c104800c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 497920476 1250 497919226 497919251
    0x20c010c0c051908011d070b030702030406050f12091e01090f240203040f030e0108041109180105090105070915080a05130602070c06020c181302010212070b060f0901030b0a0504050c130f 82
    0xc407031042d5a05cbd002035150a02e4040102c54641c4241480380c00981d09100507807652418400b224080d5000100400c1c802407541c3d0b04200001340c14101d0304150b03240032960f20000d400c01c1414031403190440c0c440020348001e10190a0b0307a800c40021950460b00c0001040104035490048050050090b602c0e500300e0ba02c4040151131900d810f03070380640444807a00c01e0400602d0204851a8444540c0003001584030107005581d0035101c0903200d02c0c0e0640d4503003080000310796000e10000e00405010002802c0819604400b92038508080e045003141900c0d0400682440c10301811010b10030b500c03000c215964880d034180104000d1250240301c0050280c43c45001e01481c061180090b10500c900c1d040c001c0303840b1741c06e18240072070203840c00700d0560051040140000700c660001d130001c0d601230502c1c44981d14040081004200003814024400c0320700038014004078a90b80c09003035100c0a94500000c6548490038140d140c03241c2d01d9101035006035544800c1e4408003040c1c02c030303407081402250107114440c207082 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 497921726 1250 497920476 497920499
    0x307140405011b110301060b190c080a08040f0b0903030403030e030a020d081e010f0f06021207020d0302101118180708040609020405040b0106020c010c0c051908011d07 74
    0xc28607002542c000340d02924004018902640780c2d10614801c5644c0318042c1c0480e09440301a40300000091000c01e0b02003d00403a0307074044c81031101516249002124550745c10542c0d0041740c2e9450204215540090f0411242c0c1c01540c1c0c61540180b440d1300030386401032880369aa070040b10102c00090910b00035002c15040013054546640742c0d0340240c21070440701c440444070800300400e0648040c002c11000307845d449031103200074060b02c5610072011013a81413024a0885903007550084003150300c152801502c4030340c24400d0350000d035811180000015164141289403884d10310200b52924600706c1441c140da8040c800400e8103107502800c0002144a820030004400c5640903955403841e41d010000703540c1803245003820ba020f842034900140e0300900383c001c2400c6400c01c60341103400380c5607500144507494042144542e601401d1a040e022403229a0b40c000d420040d80c0b00b00b038060740040e01000e0b108148000c0d401e010b070150350020448082d554000e9030f004001d01d1009070403070207040004590a00e902 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 497922976 1250 497921726 497921729
    0x20f01050108030a03020a0203130b040303110606010804021e10020d030c020307050604230f072105100b040b0402121012050309061308010e06061507110d020a030f0803071404 77
    0x240b01071420480c0901c000c1c1d0107540581d04610443c0810015010851b4010203044098281d104103613450b50b0461802800e08080c1d1f4202040980c446030422129a0f4400107240d4890b605880d448034039214201c10096a9200341c84030348d03000c0502e2414800d00c0f40c3c0020005d0f00d036007007a901070000c04005003040e600c030b20a0070381c00340168004200041c0070031110090302c0240d00507000302100c80003e81d01d4113400d11410700c003a07000707503003000104202c20078050031000040c02d0316600c41e001906090761510b03900d88085c140880d04a8035000d04804a40d00c0d50f00c80c000050001d0001d640c5d50303c000710000380444040719204590401c40402240752002a003510542e2603201c03000714034000880c0c00700815500140b03c044001d00d10240b01182c02c19080c000c40f420007494a00603d0305042c10410003d08980c58007280c8046030040c08100c2c007103190050b008039484070990781c54a00c03020740d0004c0781505689070009014500380403421400c012880000790f20a4400742c4d917201d09060020955004c1d44200e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 497924226 1250 497922976 497922989
    0x30f0b04201605030f070605100b07142815050907030308060a15030f1a0a09020912010207030c050606030607080103020603180d050901031401031e06020c07031101020f010501 77
    0x240c0d15003095041d8a00042002500400810704007103955a225491540018400c11440402145c138404000e8a40222504141140054010b0b1800c14242c0000c034040c8007c06070050000f4400109145401e004401e05500803071241c4180214000d922040c1601c1c03211308680c8152444502403407140d19104207409061b003540a030ac1010f02e1a241119046405080d103540440a80f00020340102c089070b444081010f0350b100030980700d00d83e15003d0708651040c3c0c5540d0750301518280d500300340c0c0e072a20700714415100b000d600140c40d03440990105540e07804400c900184d643c40040d02c4014140c02c40102c3c0b800c1c0e44500200c803041e50310f01d0189030b00d9035005d172440004075442400600041c60480e01441e8840315501e2034a44a0308580305280c0b4040d100074440d408118005650402568580501d4075044100346080c0e0080d451a03960751100c50b0021100743c043c0f412018120308201490301214850f82d450411034030940d4481c00d0070340304480901002030241c401d04600034a140018002c3c01c0c100d402 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 497925476 1250 497924226 497924261
    0x111060601170712021606180b01150c1208220b060907030f14090c0a080303060d0f080d0f0e06040b1503010209090f101a2a0d030f0b04 60
    0x3000d001d0100e0010000d80060113000444100c11110241da20191240d8150403140f4142c45002d03081c00e1040b920388240407000003441441c85408540745d02d806a04407152000880684080100e0803288003032003840040c0300300841d100b0312071042c0c2d1090310a4054400c680082400d44600060300d41c2424442a00401801d1460005102c0c1e190058403154480e6144c20046040e020145104d41207a2404e8030403100c200c0302c10f0611a6401c82040b030091806415612029000d041c840c12aa0b0782c040144001d10807240d002e242000c04c860080c46e1488181e201c6480c6440398510850440606910910300c5070040c81d2180303002c0d01841c009090b500813030300440703410301940360401c041d4209211311103550f40564007005201341544030648407031710501c3c00076140002800e103e030300c3c10f00c102420f500c00a513140140d0074440350180403400322180f02003100720011104150701b01000503004403403210310b15030107444040c0d0390381d0360540c001d699041c00301c0e04200302d1740861800704030032034102c401c002c0ca500d078 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 497926726 1250 497925476 497925497
    0x60c06020d0209060d150504021303020f0f090109020405030105070c0f03030f020927060109030c060e0a0e0c031e0c09061c0204171903082d0a06050111060601 70
    0x1265940241030810103904050310305030108001c105203034801c5135090501503492013012040f90380041240d0281104980c194541940302c4410820701c440c030300019104030907207440340019a41c0c2e020565501d0802614042c00c969480360100001c0d0460701c00c881c003135400d010024080e5442085040d920b5070744100c0049210140b43c03801c40c0181011000f00c480e6680c00c011040b05a80c0384951086000900c1c0003d4100c081342d108000107910024000c14103100350130900f030001641400e0b00c90240d0b1000d00c0c00030080c0d5001000200e4100c00c0e039001c40035980320319003032000075005500214407a440410b00f14444503c1c2c0742600004000454010220280a01c2901c4403803803c1c0006000f07034800c2c0b140c042440640b2a82d00c100b2603100b81c2c852401c03014258881c242c1020180324241c4062581c50300e0281071089514040e0440c040101030718190041084609201101c1c2c01d003441500c0c1c3e10f481c0c0d00d2034600e8201e1103400108440d00603240403030303170766407200d1040348002624074401c042c1070b5503261840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 497927976 1250 497926726 497926733
    0xc01080f100515130f0f03030807120c0c051c200111041d01080f03030a05041b0605030a11030603070501030908040b071b0819080306011b060c031104060c 68
    0x11409008403281010040001440d40e450442088480c480114419502e82c0c00400c00c0728001402c0d8800803501004160800000080d5203101003100d408d82003c40c0b4580d01c0c441d04842e0540c007542858849850700b0010031000d030380032005002540c072501c100c8100c0040102d840d000c112441d080c84001038020100c2a02a4480824000c20039010130f00100b030000d060040c14280c0d81081d0480c0e1414019610701284d020300460216004082d80d4014001c0030300c0180b40c0f65120302c002030a0184040c0c951f00032904010803c1c10030483d2103050341080c030185444001c0241294030035100c0c0403070070b42408004444460307054101e90180d180240104481450b180040d4041c0061901c29079a10030180070000310700c0307a01d000600101e84512400721924503410608199000039410204199000002c03001d40f200b0101041c008003034100c04503d07240d42d91a00100c41e944c0003007840e03070b00100b0b00358522410442c40360007101c1591840e407424008100e0340126941140210700c14800080c1000b01514080b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 497929226 1250 497927976 497928001
    0x8030411040504050a060e071802130f0b09190803031608220f1716021c0b06090a02040f03200d02010f050a120221060f060409020d0207060e06180c0108 67
    0x150385c00300c00d9582d0f080e983c1310042400c9c020740b0341c0da5000903000101803e201252640302c0b005070041070700c400c68460804c01c0b1030f9480d028401e1400d0188000c45000c60190741184170040042902200304c950700e20b0706a8040021040c1c0300800c9000c22128804102407145a00000301c4e1882d4241641400303850a4455014407030061006503040f40101c504800e03160b0064000b00580003840051401d181d07024030500103501404241c50f20680034041446000800382100c080d000713481143e404070540c41d541500c41c001d10603503000c01b41c01d0b04280000400c0011148600c000102da00e0080300100741d0307032014440142c250102c0240040e0580c2500b00005000d100540f0315500d0905c0c2000e0660504490101268840f0058944644004682d68504051600050f42c801001d4540b150b0514404001c14002d005a02480303103050780214841c0c031400c44079816201c10795000702c4107004101d01441920348400043ea070755446999103074049400e440c000030780c000c800b01d0181e5800007295110f4094440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 497930476 1250 497929226 497929241
    0xd02011b121809090305032806120b0a090503040b071a0c1c06060504180212010308340201030b04090f030201020a12060f030609020105070b0408030411040504050a06 73
    0x450201514944010403600c00e04888001000c2c0c03034007025260080c00c1c5010400c0c207903204102180c100040c04002950200c103603034025030400c221705800e95611954604050302102200fa07202d141c09000039800001361031b145091801441070190302e03150342840d4810f4651982c00580f40ea402008200011220f0b60300800d8114041c546241c15120007041e00c11030141c1c1030f01d4003081d040d0041444166501c0f180e010100061301e50307004200d1350340340030f4000d4440d006900c5011a40c110005440c1c1454406404807640402c04160400c829a121f14184480b80c00c070f10011048401c01c2103400101e2609112104a01c0c0c0210321005c0c061221940110003810760400e8080e082922042c40000051404901d40000340c801c1c0c002584486400c14010180701e025040648030508001c420410044401e40300000e4079001000407500c281c0b50f0005032501d1244050003400a05100104810b100989000c0c0d4016445030040c0c844030b54010040000f51141581c0181098010040e4100001c1c541e602166 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 497931726 1250 497930476 497930507
    0x30c06040f170c0318010305071e03140f09070b07050307060b0a050607030e09060a1a21040312060501050304081b071a090901170d0e0f040207032c0d0201 68
    0x441010105102c0c9074242c1008810303201580c40030034020300b05411480ca584001c0c00a1804000c94582014002c6c101b00192101550f03080c0f0041000510501c030f81c20080f09403851580302c540b1410a0760000c00c50001c101c4504100740101040800c10881d402c0441e114140c201c0000e60500e00c079a02c4010007002980403150b4031070f1103008001402d840e08406002464082e41b10000072240410600c070740d1820080c66240b26030951321051000d18480625079110303a90704613040c1d403285050400441001d01d003a001d00c40034204002000304141d4004683e540f04801200d0038490159280010740303450201707660003070440c102400030303002c580505148294003440d54001c03901c00980d5480e1030030000d000c00c08200c491200000f0b00c0f005900309105045d0050242e001a408114001091141c4644605501c2c004005d07036210403d43c1a5690b508961069000410465850090749005060b00165200015001003036032290003081090001c06085208003415030a9041c650f540112610b40485040300d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 497932976 1250 497931726 497931743
    0x1506220b010905090109050a051501140702030304031b080d05030705030c0c0a02040c051b0a050c060307170106091706091207030306030c0f0303090803090d061d0a1112030c06040f 79
    0x3c0d481e40c4025481c0e0003080034140002d65814151400415590010448000f0083d400c9040600e6644040c0c011680b0385001041602c604003840042c2c1584105c1e440644041c00c1c4240c07918941102014174401c03240d09108880c0c030012031600a6550740411904c20b408504240b001490045200c0c1c010a0034155500070b4a500905c540c1c0014100c45408211100103403021034000c0b4010303c4040e2005040e02c100c1c00070845c010f03139643d40c259200f0342615950700540011000c03500c01401460110300070840c4183e1000c0560f101c03d001400320b1b555116598615842e52100c030800b501c0801c0160180f00312a011f401841074001d51a11294401d0780103e04059540c840003000c1034107510401c000d88500c09032601c01519505005011150325080300221fa0000c100c1401c01d40c0d034140300500783c994400c01c007084020b402003440145802c0c40071021224002c1032894000c002c0e02035520310300e51500300d51000c599401a20703926a03034001d14051100c1036003c1000724001c20b00c10b8019040462040f03000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 497934226 1250 497932976 497932979
    0x50a1101021006140102070602070e0a020c1618050a0b090117071212020c0a0f0e061318020102061e0109110918070806010e030a02210f1506220b0109 66
    0x2e4200e0702c0d281d01429250b5002040400150390611841c13004009500c007c00354142089003e46120301d02520b10030180b82c1c00254040ba00409010328001c81c20058001190a9aa80388502c0040314180c40502500d1410000440300d022901c00c2e105000d0f03001e080345030075a0910151079008040d00848021030300c0f404000041d01003500350160b40d014829211580c1c103418a001c01303031030451007444052264014103804d00181c13484d0481c0b40102c5001c801d4141903610383d0390101e1580c039541002841c445051901e40d041000e1a5112000c01038801c0c0d00700c0781d845c1c2d40ca0f0b1b041c4840d5140c2c19007d9602d1041440100140100e58000310259410310004902d04110000040d00b2500010384800c45403207524104140c541d00b02505590001c000e00344003030814207100c0082d413203000100000303104e006000381001c545900001c0d40c11004103505c0842e64440e081d00c1041d40e0314012003071007800c03491611000440e00d0030a100d05034103001180030311251519840f54040b024042c510346060400412250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 497935476 1250 497934226 497934253
    0x1906080a0f14070807031b061409040213061815120902152a0a0c060309150e1f021213080906120105040b100909020708070807080406120603050a110102 67
    0x2da000200000c40040170ba00d80746190007007045e0a5021007a0000d03e0901c000c100356500401180c00000c0551036550b03440c0c0320400010024060b98001c0c400560580001060340da4001c0f5035110860740d49541c00c0003c1c0e40d140d20070f203a050380841d0074078005040f02e4000d040d98130903a0042c0807014402050b002040b4003450704000b80c0c1e08246d0344954135405103001c01c0f4004e00e00c400205c500c029008080c2001c44aa625203201240e01880740c401003640d90f002601c01d10074007000030030030b070355811b14140140110311140b01c1d5a01e1640841507126440c4403c502c1150703589200719041581d031900300300303055a928040c41d2003444071071005a41e440d5040240198940c1d401c801841d103103e14111100c22541000d0a00c02110a16112540911201141c824015402600b80c0b000c80c0c080c954050f0307a0f0400c0d031820ba074a81c010898001c0444102207280700c20000424090002d13110143d0b2410f145141c510b802c0d03402d4820521000c2c01a8000702054404500c3c00100d0000c01003040c0103c501002c007040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 497936726 1250 497935476 497935483
    0x11121b10111911120304080c060c0414041a0f12030304030915020d021c0201091e05060609250c080307110c120304181b081906080a0f14 60
    0x400d95031440718005580d45609005008290b02c0388420310300300072844000da808503965910710a40841c0b00801000240c10448900110703009a40560182c41190500724450016074205006801d8002c100c1600c0810500303081c0310b198014070700032402c603403015030320414088034041c4c2c03d10309a0408aa20070550400608100945c0501d20a50301c00f02d1031807614001c007407002c510035189411508006010704420ba40003403a03200d40c100100340c0c8248030810440a034018000440300402441018810b01c1001c001800c0080703c0341c1c003071000e4030326640e80c1c1400c101c0d022000303e800484e8051000c408500ca00004000c420190314982450744504803c1c0d1106a01504102c07103800c0000c2040c1c0d00034000040601c49001144010340c0e05042c110710000c0036a450b8010783c0204d2014041000396a40c1c440119040140340c00340d810104074843c4a046402031400500301d81c2d111442040341c2c0020119100d500c669411607409902401c90710345107980b6804030030000030098401c400220541017080c003003030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 497937976 1250 497936726 497936741
    0x301120c030f03080a0f0632030a061506090f09050432070503120a030525080f0c0403080301060f210c02060a050906010b0c01020d0c0c0311121b10 65
    0x213407108551441c1c000c1484066424055011903028240a070411001c081103507065840d01c10340e0925900e41c0d03c81ba035a02d041c06113242c5d45540c50300c902d00300542070060a621400300161404843c921403134854409035040d451510a01040300c01c0c00508108805103a40300c141c0180c414540410346115800c01114482003910100144050307080c40d80f50840002c0004900030030f415009000007000382c3d81585900d000d5184140107160311440028002d000d030100c0860a444803241021000c1c02980008104800c12509402c154006202043c50042c8001c1614100e0f58000001c030f10316820068202c3d021400c1324046802d01c20703205440180e036000100d1103000140d082000280c11504000e000389418805064015458039000900200c0e07480450301c541542c0703c504900340d0362602310460034020301c664814001c80a20785500d400903070b58000b08004c6141d010303545591801006040258461100b103110080c0c0140400c9010340c014000c000006480a5a90a0780c0031a91181c4041040d904034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 497939226 1250 497937976 497937983
    0x7020303012d240e0f0d0f08070f0201090e19020901020a050f10060504020414010c21020106060917150606070b04060603020a0b040e13391a0301120c030f 68
    0x1802e048601c3c01009011200c01004285405403803c4d2180740403030043c0c04081403160040320316200000070f011903d590f0707080c20396105540ca6035910007414218825050341004070f00050f400840002c40c000c900701801e020306401724030600e141c02c1c3c0540840c001c0d030106048030b066014a200c0040490024000d005083e40e00c04040d03d14001ca104d0f8007000c076055500100c0c0f00e10300c10701003480f0a40c4503104002d1310103001e0030207100c00f420a0030503020b842c180c4003419010441641d0300084140c0c1c1074000000311403290312000942603c0d0345105040042004115819a02030319030040b0800c03c01b4240340d00504050102d81c0362641c152214603111000316030944000303407991010011410140810001449485000c0b4102400d1502024094038090b0982034070301050700900c0180000340c400e400540c41031116030000c101a50307807103008a0a046584040c24002d0b80c20004849400e582d03c0e859a908060049195030700340b188081241071401c0d0107461483c52a4004000280d289040a20b410b00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 497940476 1250 497939226 497939249
    0xf13080304150506060a12050702011515080a270809030a03031b210504030e0a0602010c022503080717031801060609050105030105090406110315031507020303012d 72
    0x81c8241c4141c2900e030041c0011317010320010010010103950003048540c003030400040228160326554000c90250810004407a864401e2400000f900c0070f1030f440c1140a00c5a540f50300710742d9520110074a04036140e8a60f001c008583c10422140404204802d680d0900d115541207801c000c240c20100780f80c188581021008207a4848440682c4c915810000c1080c00342807400b1461000242d89002d140740c030171030b944002c054484020404060284a944400502c003030315810b5601e9807080000e0207460b000b0036070300260003000d002d065201c1c3d050424080303003a11844c00c2c00c505465551000101d074800c2c0c0c0181e0340c0050f081d8004160b00e003400021801203503281c01c6c04c1031803402981c02d1821283c140d0b211070180803d01d841000b050343c001c0150390440d60100c0314401d01d03980b18102980904002260004c5100002081000d04511654103101c8280d0980445140000404644009041c2030355641c016a00520040000d038015031050040c004188050406914001c14480800c80c10340d08080b00c40070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 497941726 1250 497940476 497940503
    0x6030b0901090c08060c0a11070506070c18050103240b040f14070816050706140c300412020304351c0e0102160e010e06180f13080304 59
    0x100780404070f01500c88400078221030304040d000c5001c03d10850340104180702100643c6000440c080c403902c00140f00192646a03601000e00c0c115030801d220740034000c0030b01c8e05e180401d0b94a80c1e031803040c82c0c1038907406103555455283c0284a034110581d02c40140303400310b0321004900241c0d100c80c02104211284a64040380d10007803012880d03803401000340b1400c10850728004020f0302440300d400c211044100e504205603500e02500740480500040b2503140d104994076003e2120206800004025041001c0012210300c100c454a40c80d1020b80000000c01014404022a01181f01e080807003001200c203004036403800c2e40c0e8003a085800d02d4106d442403c0d6025400081502c0411400f140c0001040d900107000c0c1030104000d924008040e451b41032041080503001c030041a4000c114142c00d0102d013078502c0c49103d0f42c176108501c3d4940d00b401000d4a80706c12030701203002d50038042402205c0e807142074a03100c1c16650f540100c01841d5401841700c0a00c2c4220101e4401058010b0000c43c05207003d00030010b81078 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 497942976 1250 497941726 497941733
    0xb070c050312070b1b04081b0301050a060302090a0c21020a080c0307020a12050c0316050709092004020f120901200405040e0c03011b030f0204050a120606030b090109 73
    0x12540b0900309480300c01c01c1408000b803081d0444030ba000000c80e042c002042d6900c4140d007801e00843e0484a00d07807140c0c0100c0001942d80410602014800f100240003d03555a02c01034141d40c65440000d403c450b052000c102081d6094000003644916490702c91080170740a0b20b000c0f20558901d807280100f540c0010000c40b5194480b180561000c07000341491300d9401c00c00d200950303070040002c0c0500b10110400754001c00901c55000c94550740c400d03108403074440114090f807800c240390103e4101e613a84a80c040001e81c0d000c040c054451465004056002085081d04820701542000c034501c1d580640d080000c03004003184100a0030641c000380c0c0a001c0d2501d8581502030841341c824617102d05000394000d8407504100b41a0032107058030703400d580106000310003200b500d24125103429050b9140d424074100030f0b42e0504c08ca1903010f004400b5642882240c007901100800c9200300c1c081e46030007010000003400400b821140d0b15030b940d071081c000020801d540b1f849680c0802000e543c103c601e0394540b114601032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 497944226 1250 497942976 497942983
    0x2041503120903080a0507240e070f15120e010504030801051e03060705070507031e0c090b0306060105070305070f0c05031203090a110a0b12070801120c031b0b070c0503 74
    0x300019040040e80341d0f0854440e001d1078010011900208100083c0100c04c121081418055420140c80c4e00e03100c2c0a8200343c00409080128412411403042c2d24002070400440f024607400c0318001d80c01c1280481300c00c2411112680d0401842c2d440075102c1030030b4950901e00340300310f41c46140030303640d900440e504040820400000c01c0d0003029040112041d1707410240e8020070030741d400c00c0c0d036070a10795585e00b01c92800c281442c030a58005003054104841c4031201c070f94201c1109030304034070a5860054260700c0314070160480b0700d500c19483c2c15901036800900503500510092802c0786c000c1c1860303030514089079520054002c81100403140004000810425800c0c1040316041406012244504519107a44800d40c0c403241e0900103850880024003c50031030300e5003100307800034046c05180544d44a44020010305040429144800068480ba000041c00e12224540d4102140e1210100900c41d16640711540c42041c2d6520b00200381300303001000640c0200c0394005090461007142000085481c2c40304050a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 497945476 1250 497944226 497944253
    0x303011d0105180a0b1c05060a0e150c070303060315060501023706060807140306060a0303021507030b0a08010902090c13030b090a021c0210020d0203040902090d02041503 75
    0xe0002c42c01c066a18400c880c8503268041004c00340040e40102650000d81c8030b07091041d8070b4075140e000c440300c401880300c04070343d0350311035101e03404113008402134a210310b0f9550500c5107070160356043c000e012801c038258440c001c04d42d8070702924010804580f1780e103950b03480c40d95000c41c195445070782d55400c0009580521850072581e0100000302074100c00900c6041c43e1506000745400d12040f41030300d0340108241580104080c0c00c40030b04480845446403150741e0600b01c0c6400c1d80c0c0c841c1c443e07000020075a2420080078400d40b075060f07002c1e003d2a00940c602a9200b0030207030104d000e040e1070380c10a41303484d1940300d0b484006080d0400081031007400390041c888040405000620340c500b04006040050000345049402c903607002d01500395541e41d5481e45403d0040b103c000a44c04058100c15501c4002c4015200081c2402128485d01035541050241d0b41c40300010312003000741e0006d02080044010701e0740a4030f145a03000d1300f5220580f103641c0c00074040305d040960058503c14140002d0040c003020b029000d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 497946726 1250 497945476 497945479
    0x10e040608160f0b0d02071e030804060e1c080a14070e242205040501030b0a0b04091119181b0206100e04150e3003070e120303011d0105 60
    0x100072401c4c940e4a601a1150640c034946064000480004200b000c016040702c450300080300003019000d03880d006106240584040c0c5445040640304002c03280d020603205c0c0410001c2c0c1290500002c1120280c0380b0203001000d4220042c0d032001c44070007806410224500c20f00300d541c1d5a481c1d0400f078904000940101580340c0b6940040c1703c28044e031982c000c03801c681034540500017001c0e2074041341c0100c01f101080e90300400d4005060400010070065040300040c0030300d14000c0300340314550205c014001100e61141e00a00040300440c0c640c485420180d69503005942080c5290112a880364441c018907404440300300a000e5a81030028004c0751189000450748603548042d040d18244150b074008000110301482107060240004641004a854001c0e1a4078000704c6040c4040c641080d41280c4070003142c007151201456101200c1e1800c980d2215504800c03e5614610f810354840705c1080703820031400d48000f41c20550807404001440400c20103540205440508014801c101c01d0a012907450306a0003607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 497947976 1250 497946726 497946749
    0x8030406032711060408011103070e090601020a0308100e0f070905150301050411221701090b0a1808070b010503071223070b040b030a11040f06050306010e04060816 72
    0x35a82040b003607500c80442d9400240345a041c1e0180000070345144503035441803010f98a02007100e07800004510140d4491007160310364908007403036403052255080088690074011b8000100400021340144000d84c1c00400070001c600d0141d80b19413041071a65001c3e503c0f009480d5420042010040d0710240d450003419090751a003404014030302c00507809001c18040e0030700c40c2d610780e0801d24002c003110040e20b241407944c2c2750518112002882c1503c0491032406840f0350540d82c00d442020f070031414002c04640f079611068260140c0d4810807020300500500780203000021560f8007807008140c985010b090200c0c01050001c815526000c109403801078250721000c2d080d002000c1d4a0003180e04043d00f481030111043d5003007007034444000d4940c00c0c084030750840520140d0109012071090340c20000f65102d0b00000e941048000e01aa0107102580034038821b0440d070340740c00c0f0780c207020b010700c5400a550404010304020308017490503c0018241c81050300002a55888096402c00c54452038418200401402990 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 497949226 1250 497947976 497948021
    0xd210e09060f09072a030507020907020601050a030f02030a0c06080a1a0108060105090f060f0c1e03090d11041406040506010f09050f01050c03070308011e06092d0803040603 76
    0x303c2c180400c02000001071064504045821215003000e182d4050300401081e0b05000302850054010381003114140e000f8802da40c006021507000180f000c1c16550000d00c2806607a01c3e55541070449151840b0480c1c150142d02c5036000015501c82008018092940340c440a42c9003032041c207030461302c0c0c102d010810707040328444a01669800c4000c1c907030802400e103011603440244101081007880c0081c5170a800080015450103521420f0020703103000707000d00044c2d802c907814210564035040c0b841000c0c003003190802c100c02d030341a00c1c02c2c41540c0c40561164040741074110f01140043c00720b40810011080d110802010816075150a1064a0340f2070424200400324071484800101498144d018940c082c6890640d0949260300440642c0d0504110b40c003125502c012516004040e500288104c4000382c500c41c00d41c1c507030f401c5905011416147c083c1d45041c2d40d1031a007001e800d02c5210b106a82902c405507401030500c084040e110100151580000031540c2ea40740c000028101e88698244d2251000d900d40c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 497950476 1250 497949226 497949229
    0x30207120312020414030d03021206210709020c1e2d0304080718020a09090f0204030203120a0801060219081e1602010e01230717210106080906060d210e09060f 70
    0x1010bd4100704141d6030f8444181c800f403510310400d100d00f400481c9a1060110000d100d081c0e640003400500c84e0801510a80c1d03070060043d051001402010401e01c9c0c00c484849042c0c001d00d28410314413a0004126445800030420440303046900641080000b41c00250061000350f092503a031079660003200101310b1074403068050003046031025014880005407500440e5590003201c1e010742d4003464008003514000c0c0f0092000b5066a400742c018000860746180000515070300201d4044403150503071840110b10079180c0d031018803680c0319024208443c1c0155420341805072400014000f86a03003640e0208404846000240100c10102c5117203042049400c22590b40d0010f072a081c030f0740c40090882c02c949690081c0307000d070700e01c40c922120904074403004188428900301209141c0a45007500300c92695590300c80c1d038111404101100d45000f86c3e803142000c1883c508043ca1150f00083c0078244649403880003004c00303079145450365081000a403410700c203400c452074540400780e08007008542c1d4150180070b080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 497951726 1250 497950476 497950507
    0x1404060f180b0a12060b030906070305070207170609010e120f03060a050402070503040e01060c03080f090a06061403060109061217040305012d050103030207120312020414030d0302 79
    0x3a040c0030808a0850303495100011075148000d8040e520340a620b5003000b00c0000c10000100c1100c41d480c504003000080c01d102e00a086900500341e00300506071035665035070b00f54050a400b5140c00704500c90a1000144c41e5009501c009008543c0350282902c0d040c40120a401e481d003c21426a0541185044642c40e401c030600b180d42e2200c80701c0b00d0701c1e100c3d0748030f00005180d4140c40d48025003140c00007408004002c0040010f009544503903240d0308440c0d8a0748001ca81c000f440d60070003004a8030b2400841c42215803e03108a5210705000201c800c40c0b02d0540d0b512040d100950f01240e20341c0595a08014540703004d02c1002e01610300b8203001c00c149840c1400060700310a8950b006410910f043e6508110200c54104540c041c0d90032a00038420a0380d2840c5d1296401d4840401144007141001e82000c8015680642e82c1221382503030090030181e0808007162590f0035002411810b110302c540440c544007032180060401813005030b1420750005140b80506040c503410b07844036400c041c070411244142e000d840 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 497952976 1250 497951726 497951747
    0xa0e01140603061605190e18240607020d0302011505030609060705091207082109150a050d0f0b030d0c0317041103060a1d0a0f0f0203160b0307140406 66
    0x204e0603074552444141d429a514402c010011032004803007032104854941149440c0c114120944011003040c3d4141010000800c050703c680b401d00010380360121464006a241b42c0c0314034402481e051800c2e9403a40059038007250200d085000d84d469001283c4842c80d40c42c0c1d07400042070113802400a42c604010000d0300c400000384a8410301c54081800c1640b5140c5840000901c800790301202c1e078080e00c03076005551f1030341088021307014a9403401c8109100d001d04000d5404064000e0306410354010700102e40d00c00b0381c000b40c007480108001409940c0003495980502c0c1080926001d00140d007090807418503051011901600081c030140000190011740c3c002c000080820b190003440140c2c0e100c43c0307046124490a081800e9051203448244280100580d0010202c0c4203442420080001d80700c03e940e0316291881d102510302e1540d02000f03004034205480c1070f05014230040568001400c42079144e031a0701c2d21074100582050012040207031060704a06e52007424151100d10504185c034040c40204192a070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 497954226 1250 497952976 497952991
    0x100605031c030b060706021c0c051902010b0a0b07050c010215010905061f02010b010f031505090a020c01020a050c060702060103022b0b09010c0e0d02030a17120a0e0114060306 77
    0x3041d5904469109a1015042c3c440c001d203100da6840007801c1040180d04482d00003401c0c10003011803014400f62501c65100d401c0c2080d00c4071420700141142c86260302c00b00090000030355498540c0d14115580e640c0b9440c025150540b1400c2c2c5481c403d0400500e000c000b00c200c4c0341554420b20030143c0c184403022906044507141100402d142d9109004981c1144001c208150850050000b00c00e0381d68040d00064416002a61554002c1040c100101e069500c060030041d601100b260040c08282480d600344d50303014402c90b10240c030b0a00700c07401d02803ca90081604200048010907103604e005403d00c9107603003202c46807005002b154116000107100540741c03100300b44a007000e00c400140c840300594246120a400c080954814034122480ca80a4440b070380680000402c40070b0700c51f445181c042d0100c0c100c150007800420280c0360551790001d1000500d03170120311191040c0f0907c3c02c85040c0c05410381c883c05442001090408121400307509480c00307406034100c204e03014000c116546c4c400154107a403003070a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 497955476 1250 497954226 497954263
    0x303210e21040324200306010e03060f0a020a021207060203070f030525020f060103210c080f0c190f03030e0a02031b190f0501020d140f091f030e10060503 68
    0x1507004180000d0288041000101e04045d0030b8224000c1070300c0c042c610802c420303258880c610000a040540b41ca101701ca801c100182c1c00700104103a1981079000d002c5407200382c011601461003074040c06d12240c02550b0b04540c0e9640000421550756402051200c01c0001820107002c01c0c180b503542c00d0f002d04090100d40080424004146a01510030000b400321500360a064800d0b03540c4900301815807018601824080721003566051800c42d20481402590340d030401e44c140c1c28401860b81102155004c44150300f0140301d03008000c40c0602207040044c1c04948580040610740d001460003500303540c440c451060351508000441400361301d000c5070500c81c202200702404000401c480009815035940344084590710020507011961000c0e80e000305027503c500760212005c0d540e03120300c102c4500100300300c200200c0e201840401000c0ca0498082d1520320030040c506014003c0300004448052610301c20840000d0f1180c0c2502640ca1050040081020300f041d01400145d0504001c20f80e03a03107070030008a90506 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 497956726 1250 497955476 497955533
    0x61311010c031d041e0905061605070f0c081e0601120f0201081021110405090a0f0804180f0c0206130b04021c0311010c0807090303210e210403 63
    0x16103590240064020480d40344984105c081145401000045803c40b11481000007040c0c51081404128000789203a0f61501c0c5416500d503604000301c200f0200848011000c01c0c2c01040001d014441c030292070044001d507440781c90400c07010f1032a1502c1a0302000d601d448490181d00824490429110b2040d028200b004054036200a2200c0104196016242d0100ca25032b02056000e2802a5040311500840011700c0b01c0044004000484505880c20300565001111040014050884440c110f82c02003040500309585c0702072400e03480104080914046594078030660409900d03200350350a40c0e00920042106140c8005c1c0044510b81a0364054564102d20f80000d0031995080d05900341840f0071500b1110b040202e2401800701c0b400614951495402c1a90760290140f042400920494150b0f44890201e0b03e940c406440e00ca1a0380500f10002c0c0c00c480060f00680d0450050300081c02c4d4000003800c070114602c2c4000207101800d24142c820304400c010800224504080108042010755450010318 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 497957976 1250 497956726 497956729
    0xf0506040e181014010f0b070314090405070e130603030207060e040b0d050c01120507022d010c08060109080c060f0a091a09100234030203061311010c031d 68
    0x40c5141080c104036114003000303901e034070501380c110328004030541d00d10307558690700c80c503e040c1036101d1402210000c15082c0078072030209115000d050b942c0a60700700068600b09207100810285d400072103841001c50594440781d041420f0100d20084404040541001443c0c10341d90001d4981c41e544c840d50080100ea58003002047e0b4450384260010725004009415900081c40d050303459a1141100d5400308043c106d0490400020340103245c070901c0b00364003400d10000c1d5000d84c18405801c1d079420000100c0d1150140a01680912481190000750380310084240b404a00051049580f5008250941c001e5a06511107403600000d550405000350301064076103060010841e1003ea040e488440c040d00c0ca25a0b11008015201c010411090305945810516160300026680d9807552841d05240d00810015032003080c40921619000a00c040040818030303950381c002030318140058071803800c0c1c84052100041001200e9907106140c200070300342210100c41c41e84001c0c01c0e601954800410991141d882d41469 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 497959226 1250 497957976 497958001
    0x5041e0b0a090f0507020f0304120210050705010513020f0d0201090e04050a081902011104152f011b0215042409030e1905330f130f0506040e 62
    0x240828500030000c283e490f05601018007400e032400340145c0140d01c0300e59880000401203900780e49480c1010a80361403942e092009020700205420708000e0140503201c00104207000c0e5501034175509400070070225490041100804407500305520035210502e0b420010f0340c10401400407684140601940c03940c45083c110300307210b00c02c28002c04d003100005080454900702d18401c80f441416600801038400d007071101c0d099510841c085d82000301c0c1c44001000005106d045200d00d203441441c500c180d8013240e90f03040c06005d810100030114694440010701c1039684e0030f9062a201010f80e100078200c1580c0343c4504200e41a001d40098a290601500c0c4c0040c001880d40d00718140007100d100b00001415818020b0032a09500141c1d0310544680b089070510412044c4800203403003000345049614000c0e0265141d40052901108403403402002c1d0f2214459101009403600c607100201895803200a0750a00300b052007280c10124107000d03450000e01c4103440b4a02540c00b500c2e100b0643d101540c4510168500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 497960476 1250 497959226 497959229
    0x2913080d0221040c0510120c120f06090e0c0f09180d050301030b070e030304090e010e070902041a1c02030a18060e0106050d050d0c0206040905040803040c05041e0b0a 73
    0x1400102680d041c20b203601d061034807a106a0041c820115125100d804022541030244040c1e000100b10b180c039101c0702181030b84042401c40d60f50825800401c4009041001c0d40c0000b80d000d00401c2e5106410003462030365020740e14403000904040c0016149400002e1900c00441145c180520034940000722281040d02c0315049a80307202c0b045408011034940000c0c0158001d00040750301491010200322401d004003103030480190004d01960030075082455001c014050511601250342d03d4030f11103e8a00e4050040e600607081c480f6015a860b4201180417450031490144801206010013446403030700c00340310a1a601c9a44000050303604e840c0c0310900c60242100080514010341e0065000041201e25071080c0094081700c0000d10055075034404100441c2008000600141c0014121142c102e105100785050144020409801c00340c6501c8288111441142e0480e030801000041c4030a000141e00c0040061404a40500040166005003005e1002d08a900b668003034484410401c10b45d6048113160 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 497961726 1250 497960476 497960497
    0xb0307051c05131505101809060203090a1109010f0302150705010509060f09011808030403140f071e0206160201031d010b120601150f0c0c032913080d02 67
    0x80789051901420400f102c0d0104101c60f070101030041024040064041c0501c101d40c1e940070700341417503d01410069190000100880415500c80002000171903a10144d40541d140e0401811b206549203041074403410001c070740d18030074100c0e0001041110403119551098030340c15161000d8440d201c62030542c882c010040000d00302d50829040052a0340000380c42c502c20180000050850b4a41103141c6007280c291507409444036202c00d48902c0403440103401160814842c0c64804401d02410700300c0b000c1c98003c05050810b0701030018540b8240f0015000786e44c090308041c030200e0412540c0c1c1d400911140724201110042c0801c610346c82003568000e5001181c80c0c0d00341803c000e607901186510074000d16102591303d1240207407066000d0141d400003000d50694040032240b80107650303104000e45403082201d03d41401c104c0c5225012001480e82c1086c0001140b2400c200301c1c5060781c5112110201c40b4411003601040103001c1008502da2211b20418003658000842c90f0781d0b0644084140c02a00c500b80905 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 497962976 1250 497961726 497961731
    0xa02070204020f0315150906040902072a0915050d021011190605090604030522030203070b2503050a03090305090901080601180e0d03050c0d09080d06050a0b0307051c 73
    0x1041182e0341045c400070780c4a0868482c01d00103001e03620026140070f403440c3c46030091801e05c8244000506a4014814507000725486142100720f844000c10361000d00107007079956215508100300ca410180075032681840d00607203000d8110b08010100d612096030760400b0303118600d454044e0000702c0c000c0c071881e224441c0c0b030b0f000c0c0d849940b486101d0801a9010050469400d0b02c2c00307000900098022031a20b0103954140d940624184840344003170075141d482000c00790a503040a41c00401130b0f41c10000308004151a8400c103498602140e1054107000e2070403134504004101a14642c0065442000c4405515841c00d001400c108581001c0710356029021100740c006001c0000441da224000420398103c400341e40e024000305061142000c103840c1a0b003c1400396038807490240045078000d41000c3d82c0088501c1d0614206100d80c8103800540b190102d007a901850005060300440e43c40b4001c403005400c080d1801151341e40350410401182c0300080c80f0350100000880d18036041c3e10083c00c04034140c190140c1c10b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 497964226 1250 497962976 497962981
    0x2103070e1c141b03010203010e0406090507081f1803080703020a020309090907140312030109051b070312050705040f170712030504140906061602030313030b18030309060a02070204020f03 82
    0x999140440d02002c10f8900d40d15105070742c10325050089034180d9500350140311482d1120750718103001d0901d032002283c0500035880040b8020908205003d0900108000940341b09801e001c88000c03290624614920410b20b41856404240c00000c0346030440c4032840c005950750486a400c0742580502c02c00d2640c000f80510601142d00d4000821340141c805030003244400070410010036030b8035407150ba072540d1101c00074801000302400325401254030184690300d400004410500c140180e5024017022404100c5006946920407000e1007242e500c1416800e0a07460300c0e060405c8812000c86034800d41625105011703443c0042c45042c80640c1c000e200c03003207404003403000074030f0302030a590051b000d841c0034502110510306031813401000060003480080d00c00d61814603500c00c18118a44169020b0f60548010454007450b5071035075401800945c040d00300c010300f50130b20908144403c0303d1184000f5495005205020401c040402c03c250041e140e08001030b52101d1034030200e8040d001d001c0c031000924002204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 497965476 1250 497964226 497964263
    0x4151503170909011701150e0f01141518030303072c1302090117011502010e0d08061c0c0b030609061503060d02010302040302060307022103070e1c 65
    0x44010a480c4074000000c4000c5080070003500c9030040042ea2640480d00c000100701640d0b0032072030400e0400c00f140000c10199920100c0402c09031155020074080e611890805c949a80382a14280c050300d014601c040d404c04080b80080d420400c40084244103003000108005d20041070301601344070380c3c006030a50382c403440d0494003d0003610f5080748050001e50050b282d044e0a0401c3c42030902907100c0100520304540458401400079081941450305102c00c200c182e96101041303070105802042045c203214070070380340310344000c0c207541c04540c50343c1103130f8410882d000344190010407041e07002d0800c2c1d03500c82940c90b41004600c15054910400f070301194810001280c212a2a0f0007184038107411795800e007050710313a0740609c807080683c8100c0307594a880900114141b0320f040c0c080d021a090052402600b4180c603038002450560098480c2d40160f0b00c80c0310b01600700810804120304055100740c20504600e07060310040c0003c0f180750400c2d442440e0b4145060300f03444491003d820b0381504401e00040d071034541d18 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 497966726 1250 497965476 497965511
    0x120e07061d0315010e2e03060c030f1d07080111120606040b0307050a0f02060415050a0e0304232725020a02190308090405060d0f1214030403050901080415 68
    0x720344403a85111800c2840d402c000e201c500c40f011b80714507030200c01c01900d180c032203030020300780203c90004142c0c03900420140d100071800f450540f4400c0645a0214003402e200700742c94044554441c0490764101241a1441c0d5200c0095503822141e0980c4020f4540c0d921001920074440c1d6081407070f502c280130040c000426072004c084c125403402611030718a40071100398140d81d10070040728018550780b203489548500690039000190000b00503a00400c081301c00c0781c0100d0454115030442d00c940064182004603081c000d0440d00b541110584080140c001d409408004c00800d000800d550582e4540200e480b0511801359419084040c101c03071241840c811400030b4480160311026031080035513010007051a1020401d00c0216907201040c185000f40d1301040c071010b484000c05031a0300006180b641d1001c50201810081d03080c1c4160000f00b00c001035040043c1031489030602e60200040e042c010007001a41220448885003000d0038983c0041e655454410b030440c082e182c0a0704507a00b061468124440344c40d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 497967976 1250 497966726 497966731
    0x304020f010c02030a03090915031203090c050d200f01020d05070309120812070827100c090e01060201091a130819030b06090306010e0a020c030307120e07061d0315010e 74
    0xb950034000000e0007040680d04080e10300022381004130bc1c08281400c17600a901070a0b413148a01c4845140300e40e10310000c0d414641c03904d01524080090315240c40c0d11035004008141075001110b0f10841c4144101c0004d40e58101c10100c4414001d0020721007007803500401c4c29030000c0c80e8503902281c00b40c40d01d10706261030740c02500c284a12003042c3d50101d100580906240381c07080340c041d4007503802148004407011802030303100f140c1ba00a0065074183d490306e00e0a400f0313a1115103016110740e0003051030900c965030200e005a001c041164036200c00039000401041d8a40000000200c141d1580c1d00e8032a405202c4c82d032441d00050030928006081c4007210071200404290790b4070303900d0030020b0000590074440a8440d40c5009607150308580014800791012035500c680120540340c00606102c40c40c4901c030f29642c03050340c140c00402d034801c40800c4000210300900d501000b504000c2c01d0064031780003010f00a550301401010100300b0b42d40c02040c40c0d4604024181014080240b000e0701d55035901038940600209 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 497969226 1250 497967976 497967989
    0xc1002041403011e150b0310030c080c03030415111b0a0e090309011419020114070c03140306010c050102030c12010b0717030a1814010c0f050304020f010c02030a0309 73
    0x142801c2010510b0180701d80c640c2d40708820051514010000003060040c0064003084080c01030011010a852030701102551107030140803c0f0301c00e070354150b0800100701c40465001543c9031f4013031146074800303450102c03d58049441c1070400303040c0c1c0060340070300b41c030f0346820340c03a18560900c0385c4d4a0490342045201011420398500350740c0000401d440e0309510620a50484040500340d01c100000000e030351240b04401c0141e02156800c2c0c1c03c2c1910300240d80003e2415951141c010f079101c2c40e003511b4414048407159041012401c25084500041c0c0d0301500c0c80301a04c0302c4015a400100010701d541c0d0040d40704000b27403035210000715520710f086400c4140603004007540d28028200c0c5400480c108004d20300f200e0000c3d4110500200b20403a64a0080c52540000e10100d040e0f074032000c0300e40024501d81082c9005074401c24000d03040310110210242100d001006c10000c0054415200c0038140c2c0000881e13810076015106502411421001600d8032008884029058401c1c10484402d040c4d1000a50065580f03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 497970476 1250 497969226 497969249
    0x170106090b030c01020307120309021216060305040312090c09091b1521180302010507031104060f0c2303040314010506010807080a060302041a1f0e01140c100204 71
    0x1110820b140c2e0310b0710100c460602591003042981c01003041240303040c0d4510428600458461080c4c0c1c045091020394440c4525107a000401580d14842550707259005810980b50400c03042c5000d84009040d602802085e80302c0e00c0c1c0e61343c0c00030140840250400c01500202100380508041c3d85003d101003021881e00e8040ca200c4420301081c000d114041c0c0b1881c1810995640580740340d0040b0884450a91440020039a640c480c00c403d00c206103642e17100c402c107001784c000290300d29003080c02400340ca2115507210103a000800080c0b2009410003171520b1403030024900440c00b10034501d806203071000340c2c44050505040404a0b801c800f08000001c000b40c9100b500307100c0c0016107141c03e80d400e0300c8d030540703015002c10910390004004a00c18044c05501008490004c6000c80e604e4012508655410351400d005250304841c40310541080d207080c410b00400103040304d4416440c504010410f00d40a035a41e030406c120880804024490b504c15202e241019900f40c400000342d03c11944000c2d0702034450851000c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 497971726 1250 497970476 497970491
    0x2060c0c040e03130e070908011a041d121b06010f060f0804030e0f030a0c0f05011403060d080703091509090e0c01080103060b150d0501030b01171b010917010609 71
    0x19001c0700b9150700c080c000550254581c05c0c4592803449107002010401044507000000603590380034022840900914810301c100072a000b800d200907907605190100a18410040c650380a5200084070606940d4070450a9295000c1c5502d03c6c5030750900c4032000650384a104000324600c82c0113007140003290210388800f45080c1202c2c9082d030340d000c800c65024011402480d0400c0041c200074088100c030210003000d80b640c120443c0e580064240141d003000d4990380c0715620070700640d45c002032241c88041004042c18203600d400c000040d4480c0280c04010030021001c183c010405006848580140ca0100c06034800c0c4500b00710014807102151040010311400d0010004a0030004900142c812006960f822480d030b0a5440b21000350615400c05c54000d0050700c00c4210040700700029000f0b00d182e00c40042200d52450500514211040c0c000d00c1036411070500503a00c0c030000190404903400f0043e0742c055a10209001620b071444540c0c00303411003d01c154900380c021003041d4070003015100074210411811 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 497972976 1250 497971726 497971751
    0xf030a050303010608040305091306090c172d0a05151f0f05041802030103050c010f0203071704050918010c0e06040b030a200a080c0f030408090d02060c0c04 69
    0x2a40240006009a00100700600500c0d104482c034642c41070090606e5803801c080c00f8041a02500e11100d04032070181d6070001809400c0d914000c00340c80c88480e180a008586405900c2c06080310043c00203c102c1c000d07001904819024481d44480d10342556491a040b4a0512821030145c00e0032244140d070701c80c07048040d00c1c6c540b0b055030014081c0900c500b0030441b0041042001d441c1966100400c006205080c40001000c1d00360f40044e00342d108003401c0260b201e52441c5045840c0500075518281400f034055000030701564004240c0700646d411245e0351123002002d04a10100c0e100e1604802c2c0c0010040d0b04004550301da00f40c81e2281884c0c80802040488186101100c0c02e81d0136005150f0300c00400c0000304000d1348000c001c0c40d00003004400000b0b4030101f00388030b9152014040300c07418030300070040f8200c2444ca400611060344601a5400c040c50100e20f149020450700c001013000389080700105403d421512003040d21200180e000c0e01540d61880300c41042542c410256294a224500300800309684 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 497974226 1250 497972976 497972983
    0x13121707090b0403020f210a03140a02250e01060807170f070513240f09050f1e030703060204170307050a230a03180b090d020112090c03060b0f03 64
    0x1242d890448007800c00b03055600708000503400945060303106d4250b1a091000400c801c011455504901c0c0051034a002c652030b018000340341c01d1010f070b60546e0301841034420f070075004103049000501c01c0c0c14207000d144104002e500942002d0300302940c6202a90000b1880030b401040c21405680e19403151900395440350b81c800b20108044400c00100d201001c04181c00070300943c06030803015050b2945150303140d1903420714542c0700b65580c0c892105003190400009820303000741418000039064a41640101d051501046500d10307003220180c024081115480d144203e025607241081030018203548041d80d0341e080c80d101942090180d5401c00d902d40200301e80003100001118030295100014107016451134a690000b6034041c1d0904442d092904800d8410785414405000380511a443e072401098490509003d42da8094103c0c000d04035080003800071980d9450940203000740d09103002407401e001400854040c265800340202030401e601004002c0010a400c4400103100a85061981e6200740382099035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 497975476 1250 497974226 497974229
    0xc0909050c090a03080a350705120115120e0115090603020f15090306070f0806010908060f19060b07150c0c0807020103021207030507081602151312170709 68
    0xb8032a950f9041000001c448a01408000440d420403001c405411081091851072040000007152030788045808449410098240c00143e0340c0b800d41d003001158101d20104020602a4010310b000e110007c503003180c031480144186c88540b480910800d06c80e40e440a01030440b80c42700c09000e003030040e404102c1500b10b1058008580d0020300d180c29a00f07000301480102030780242c510030488400c10103004180c40802c03201e809041c481d581e1004030b0503c8980140032078030140c02c1358104608010100320410700000c1040d0000c028a0302d000c190b0701d4040b556805a6002c17102c0c0d80400f030814800040070808900904042d6000c1d0f02c081e20400c1640061a04964031120010041049804441c000c6404800907180f19441810018942124031a1031042440b00700d40e11000291100304010801d544605980e40015416182015000305000007039180c004540690007c0b90301000068002101c14100f0b411094001001d0560f807220312000812800300c4c0c00c6800682100c0d80080380769188250300000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 497976726 1250 497975476 497975479
    0x411041b080406061a03100b0304030c0b1812220609030822030609060c0c02130e19030507050d0c1101030c02010207150b0a051f0804020d060c0909050c09 68
    0x803121803490000740c0d40814040c20a0b104a552000c010500781a1401e11000c61640d505400d034907031405e291078002c5481150401c5100003020b00502000a4200c0c1d559003c1d15400700c081080ca079544200601d86030125041e52602d44504c42c3d5a00d103090168008141d05190030b07103001c036038441d100307a030b000c1c1c1600300d109050000f6802c800c10400b0a000002030854120703001e00201d4500142c3c540040002c81d59001516400d550f800a42c0400c5400e1040d040e40c1103070f80c100307800c0c0304481d5000217000c01d01c0b91a040c4101d40d150142081c003d1824050204d134540101d1501841e40b07010b007402806030304404012203541c401c50355140e4907540503024143c40c0c00d0388007801d02d5242c031003400114054805e008000301035640a011504c0001c100003e4804100c42d0b14000040403800390b002c000541d8400e6204078010201104110003000403100c021007020b1041c1824440784c0c41e02e00c04601101c0c0c541d10049d0403540fa041e1071480e1182d218106504892040d0001d11003903ea1646004603403082c6903006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 497977976 1250 497976726 497976761
    0x16020a02031504050a05060c1309090210050c0109020301020f120609090d051b1b03010506061215010c0b070504050f010503061305070233010e04020901090e0c18041104 74
    0x102401c1d00408005500503c642c0c26034070118219a41c0524003481910388130f401308e0000c5851100000e007201d00d0f000504c01407105200c101442d802144440b10f104106108000002a130040c0b04403094000c8440c46501500031544c0e03d18420646030303150483d000900340d00300d500012a8031890700390700031070040ca285c5001d814643c0c00100d054071180e000151a40c406450a07950818103401481200c100b821001501621304144004140c00c40b1402042a8400d00d004d01c0500c030068003003221158021a65801ea14100c03041c0c0740141da046000d45402030211003924101b01001c2e62080103441101c800f5a941c0a01c09504001502c41e4001240c110f074100300700203010401c40311036070003241d0000020300540d0302186c44019002d007082c100b000840c407000b22110100482c921000700751801131400c14051041030510b5400100540c0040c03180c08402901e030308a202e0f1805080c04a2246501d00a005001c5a060f6022100d00b400c0700702d50544d104600000d1460302424580107507007103041c803007080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 497979226 1250 497977976 497977993
    0x15040b010b0423011b0b0907080303014e0b0105030102030403050d0c170702030a1706012c041b0305091c14040515032e031e0b010b0316020a0203 64
    0x3251040b08140c11860420a1820182c004c04c16803105c03401c4624000c80b054402490100d8081e441d0115690040c1060382c000c000400400102d0402c40038141190310803503031100744200f2221a15400070b14200b0040403c041032104140e03401e82050b8a2601c6103188034842d0386c0e0b8a00301807c030b0104503030240c041603040200c00b03044c402a91125560038994100034002e1015902d01d8804244112144809680005925815035400c004100446000c594410285240160000b00302101c8246132203042041511300d5483c50011035490301402d038010304100700c403510308810590050301e00142400170900e4a0040b070400d9a0110b402c95151100590020b807444c00c0078030448011012805802078a401800041590740d03030601041c2c02400104001a00d82c2003407503603419004440c164003190050291165220011849a00b004aa802810345441000c1c102603840c03c1d0980b1484c01002c44100b1400411a41c025501641c0604450308038003070740200c005c0e01680d0350425121f001c1d5040e80030450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 497980476 1250 497979226 497979269
    0x5120c12090301090b04060e070906050a05091009090c18050714251505061f080a0207020409030207030c0b130e090f10140703110a0e1215040b010b04 66
    0x3422080000b0b03000060b0740d46280c69503001e211013a90300b120880c1d10b072540c500c02180204401401740455000820800e4500707030000750310700102c0c41030600911903040000c4009901c400c514004001c052401d108841142c50104101410b5020f83c44888888059041d5884032501c0340318492603d50312500794408104403501c0103904810302c20160b0421445440f11040c0c85c07450b1100364184501c0d034122600060900010070381e40000c00640c054407030340e0411200c00301c42d1181076540c1985420454815260505d100e0080d1103410320280d04542022015010160b001a00d0b2003224003951100c00550307190758003002e0a1250b0000c44200d134100a10038000e9107035203c412608000307481700310b80c101c0191b01e805d0350070f01109032001c11456689801c6401400b4600d41d120390300101a15040114040154035031600d401703202140070401440b1248034015482c3c550300c52800c88040b00498141c4583c804410014080849040750224450400020140b61041c15103083d90306410750100450700138503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 497981726 1250 497980476 497980513
    0xa0f1e0e240310060b0c0c030f0a03080402040b120a1109090c0111151e01060318060515090a06050f030c0607020d0609020a180e0a12271205120c 64
    0xe6030790600400e1400d0800152611407000107001064501e61580d0506e00101c0c101135421081c41c0c002c0e001071402c0707050204046180c84025a050500a01c50380310b500100b8001c182c40d010082d0400e03003005038034454020018110800358440e0380069945c0100740240039132004159400320140e0b0040001c0d484540c003030082000f901c103161080b203403841200701c03980c0e0340408180c654034180214106540c00038411808541d0250081e0308050041e04401e11282c201c040c0728000c050019a510000702d0105c601c038000a00c85d400d401441d0001a040c0a07001c00c000346507501c00c4501c40d4a04020043c1c06d410085030482012200505080c2003031410b4007404440200c41030100e450701c1e1359140510050351001c0491001e04042c00030320050381c3c07004180004684142400c02416070004c440c1f100003940d000004000c2d001d0900e0452051001039200d00142d00541000441e506000390000c110400e104060038030040c00b5004490105200c010070b0540da10074032621103803642212036685035452249 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 497982976 1250 497981726 497981791
    0x110705060f09042d0b0105120402030c040509010c020118200312070302150a1a0f040b040203040f1208100504020f0c1b0406050a0e150a0f1e0e 63
    0x714405890010003400241c11112894400c9039000307000580441c035103040044007407501c202c2400400c0a0b542502c0060014003d5080c44c5001c913641c50002821920140000780b000b41c4054001d000c0d504084400328003030000c44449000561a101e0000c0104010400080c00150042220088060103030420134848150500c0940c040c0f00352801c1141e040106002010075a0190303001c9c00020392040030004801c0400741805501c04d0415408180038035011841080d41007040300d805040c9454000814040e0020b0401c46611901c0841007105208070080300a00f00c81c0706401001c00740300702c4801501c0643e0195a84820412445410b0041303041682c001c015541034100302908250900102c2840d006038030000070500c000114090304241040e010703510290400300d66010903d4245880344d10b240c1e10007030440c00046000e441c0100552981e142c00c0c1b01800c107081d60811030303d0310754614030b40454a22544241100444200140c1a01e0340ea48050040351041010310b42e070442911101041040c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 497984226 1250 497982976 497982997
    0x21509030106050901030609060b010806100324080105010305060c07080313020a090c031e0c1d0d050a0c0812040521070b0307180914010302190803040303051911070506 74
    0x2202c101140a40d22010158000c40c82101c000c10300e03099501d401d5040d594500b00040c140820300042c003050382e684007518580d07007106140002d280342c40064a200040c070951000710011416400c046016403040d0001410f881c014001c40d0f2040c1c8a0b6030080001d0b200b54500581103000c2400031901c00940480c00001ca6400105440310080e1a211a80101c80c441e504000220340c1d1280c40031030b603d000c8640c26800003100102000711042d4100040c1c0401140700180a4884210019035102d64032280305203103c0b5007200440301d040702d4a14080c09105400c4c029840e0610600900f000c01d06515011202502c8000d05100c002c048a00802d4040c117031400c030038807424090002c020a1440001c00a10b12a05d01a03661200051001303411009425840e080300c205181440c7c4c3e141e0300d1000900d08541140e6060b01c030500c0050303045403901c1004455800c1545240070005000040c9a4014003070001c010000e0400f0300941c240741c406981d15541d0380c4c211a0035403c00141008607161030b00203001075019 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 497985476 1250 497984226 497984231
    0x30307170a0b1f0807090303022107050d0206040b01210f0f0b0f0712020705030301151101060906090605180a0b0d140604140607050412060905030d0e010b010c0215090301 75
    0x34180c0015002104050f2150004000340c40e4000805600902c401d42110841c10080d20613425501d0081d16503100100303490004012510b118802541da008440b000c6801c442030b0390b07102d02ea08400a40311801520183c42c2c0c5110710f00081031001030311007400e07060f00114203050140d8065603a1400c0080c0c40050940d1407000c18002c480c0402d00c1c0445080c80b60303000040d140d0107032410060162404045001815a00c0c1c07051080d0300009000108481c191180200491350074100c40100700e40303c0310f244180003055401d0940002d940c41c099000300e4152001c1060a0085584403414050b1800200243d00315400810001c100d0803074055205201400c0080c01a030032442d15501c96440d0100150500701c0554020000c1206001c580c0403514200401c86028024a0402a1009040c0d005901551040d1000b24007180100482a48900c0486034080140d0b0384411b0a410b81e00c1c020a59100054055420411400c80d41d40c40356a0380c01d55a540200070b260107110504121540d90025a00c0640566 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 497986726 1250 497985476 497985491
    0x180902070b04020a080a03020307060b06040b04060527130504020418081b0114010b0d1d060403032f0f070c0e0405070504050f07030c020c060a0f11030307170a 70
    0x10414002844080d01515140c8031a052500c14090001e80c550311a20309508a0700081d000030340e0110448404540180010405c0e14803103001422620455000a03800080001c0000c3d9080c0c00a010307106c03060845920319040055a5140956460000c00e0030740d1085101400303958154482d84504e03001400604001340e59041c49448c101d05000f141c030259060344002c10310b64408607440d807101c0c0c1c407010920028400c58a88114680c1c07005c02c180518022620041510409100780e079124041c903012001c1684e00c0b0400490195413a80c000b5101900024104200d4080e10900c902e40d420006003100e48a0b000522009417181841d0440203045040f01d0003040418045200166891f010b0244000400700508051070002d02d0a1120782c0101d024506100801004028481e01e01c3c0e4402c001d42000701d9404400c4030100e003000311000c56140d00c07440114842203105c3e408001e19102c0c0700141c0b110322441c00d94000c04e60341c070f010803038860000424890f402d940050803038400b40c1d0031a0b160076020403100e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 497987976 1250 497986726 497986739
    0x130804060f030902042f0906090105180406030309172b12020705151b0706020c010933060b07080901050c0a03030b0f04020a12240e0109110f070318 65
    0x10fa0390301503625001d1120f2001c5403050b54490746d254902c040e0340d14690b440c2c188035101284050089056940c18840003140301d10700d41403203a040a90b00741005104121541d200c0c600500b07034580c1c0380580721440d09a072158449986001483d03540070700000780e1b2200c100b00d40080c038031b0254981c0807501040144e42e003035642114090340040c02601d886000909010005080c1404405030300800c10b9103003c03040301102d00754041002c00c031008150000c17005a07980416000450251074601c40040c40d005400501800603161003820005a110101001015210100b12034058070503e0040300e00c802d10402c199000a5040b400600c3c003550181001e500b407800d460140c83c01c001c2004019000b10340c448021040c1d6141c1442c0c0780e1035105045404505041081170001e040e00070181c1109002a80c40a58666484125408696020244400843c0c06450b589084a17808081c070070b1203a400d040000341850340c1c1ca524165622100e22115060a010060b07c04132481240c0a4080000101c901c801043d00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 497989226 1250 497987976 497987981
    0x6030103050d0806030703080702010f0509130911060c190201091503050103050d0f0203070f2607020906030a12080703021312020901080102041d060f030f06010608130804060f03090204 81
    0x29070040d00644814022a0406003020400510651098001080600000d01d014013501c50540d020b02c0c2120410121500554081c400e07030308840d910420703403100003810408a401080855102c2d810000c00b940340e10090084c0d83c040d091519100350041a071210107003d4024160104038014586140302c1a80d41d408203810070314020328000000d4580380140140142040800051101c920b1301c09007c150b5400000d4590103481001060030190300314a905000d000c080b129510030580002007000b080d018201c5800c1c1e4042c900403801001604002100c0303181c041124210250008002c1c00201221441101d1a01d0300a1812080c91340c01c0c000c0740c440c0d116242c40000070f8441c4840b00340b0012002c0c0104800c20300141c3c0000640c0c0e00401c424840c3c43d014086520225500e0500c0b800c01d5103c210005003210284403000e500341c407604805e07080e400c0c00040c80c54103c0d0740d50345a1a0b400d85a0100c3d000c010060010f002d00142020442000b62131b00c100d0b0740040c00c0d0724a2030001071607803e0394002800e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 497990476 1250 497989226 497989229
    0x706030b130204080703030912080405010e04061701150806010312080a060e1801050a0605010f050f0403050604030314090102460f0207061803020603190e03040f0b03040507050915060301 82
    0x3580c0980000d008154005038044060300d049020004100c20941d20030072b0361b104500442e810801d003298000111b4036903400800280c01e80350840d84480d03440e9015640204050049034038950110a40068000c4021800b18166500035001520401d0408410742e003103400a4150103640c0d941d0f020000f0703541e8509440600440c54001c0c201d032000710780c030101e500759400541002c1c3d4151409e24104041c0e81c01c0303001855880d0b0203041c00f50315071644252154443c00b8a0740041c10304d000c0d0008000800d64180d102c04000c05411813405c5158403034040e03041c200e00603031f820840c50306201282012003d1121308281d0000008104003d0365031041d04a143e08212100b4402000c50184404806a640c0505c080c40103018145021010703c902d5030490045a9114032010340a594000049503580c19241c81d407032000c03a0404400c1c80440c1514011b60369a5100d80314080040c1d00003900856181c0c1d05400700c1740181c0d0070100411015040c0b1041099802000d86502d0800a403818500c2c01030300c6003400f450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 497991726 1250 497990476 497990489
    0xc05040f08010507030f020a170a0e1e011506020304031b080307030c030305091b1203091005250209060f040e010f1506090e160507150c021605030706030b130204 71
    0x200f80c249500c0281c10398907a0740034a0400c5005020461314140d105d1243c2d0200e0f000b05035003420a0f207815007504000c118a00c0342041c140079a02499145c1c0b200204a090f020300004020018200f0492140d070b9040c0c0c0d83d005040040e001000b040011030058034004500c1c40d080714001085030b0f40c41d0a100e1460b8000d01040300414050311f504030078181c0600c40d050780a5803400180c4020b141d0041c0c407404030f6610b504060310a00c0d96080610b000381d02041501d48108015009060061420b04040d0241d081400d42c1d040003401d03503030303d1400702080740310740c9081035401b900040403500c880b0308000009100c02509030704507030b81c1e0160586015090050410902540400149100c0c6007109501405010b41141040c004c00b01300402862204500302c5a100c2a043c8510b8843c0440603000c6400d03200e2101c024107440c000507400074940d50b041d40700a028500f107400b1103d15004100f0f030700399582d00b1403003000d9154125080410900d4041e4021441000780204034110b0000d0201040341240c00540000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 497992976 1250 497991726 497991731
    0xa021504030917100b060936010e0405060114060a0c0203010b060d0209040608030703050901180305030f22150f03020d18120e0901150e09010803190519030c05040f0801 74
    0x646107900780e10508503594010b13940c0c10b00d8000d581f8040340381030540c4072030f41e411403150641a0b03500c06480c42d51460009800c091142003565184e1703a00d0450241a54141c4160003000d0000840c3c140f031900e00000044007501c13807420000c4540056440b03e00750041660907540b15000d07046546d450f2401405181407900380103031030740c4aa0050004072031580e08150030a520030041c580200ba0403d0a4405010003442e100a0410040030680d914030010b9000505a01c408038160552401b020003400c0403038511500400311054038a202d1030403450301d105e2603540b20742c80c00c00b800d545403140440074180500b40c1800352400d1175400496003140ca03000850b10300072072001190340420002605034041c1820b14540a2440e0f55181d0004100c41c006100701c110311002e116036980e1417800b90480c00300510000b0b010109940c1c3d1101801d882e80e20100441d03140c01924414041c0140c029420b5a51011482421150070007103880140c00810041c0c140c1010301409000004040f2401900d1201030310280c40003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 497994226 1250 497992976 497992993
    0xb15120f071805041104020705030f0403110108070c03090b1b071d0f0705120709051011120f1b120a020d030f090f02010f0318061508030a021504030917 67
    0x201c2c02c2d40030303a6081c0110203410a0240700100c1d60100e00202a03079802c0b603005a864a40d0318065140d40b0800003400000c502c007050000030300130003c030300d003080000c2038a680c6142e9440c180112041100d000b402808205103150034801052844007401551308043c95443c02e01c0c1d031052489113031001c1903010b045201c81c0162080c4000090000e01c82d0030862602900b0480d06142c200076080c2d000b00c0d050600202c0c01e02c40080c00c40e61080d0203080003000d010b03092441346c400003200249042e1000011082d01d100c3d00b0010102604d09a0403101103000600b203040c20500b40251003050318200c1601d8081a2040c01d009101100c4080000d015044043d0010b05241801c40c1021b03040d40c0988554094079850041c504021513607075080b00340015424030708185041c80042c0142e0040c0045101000e0608070032820100704041907100e801c55202515040e882d90b96105e0106941340310b60400c0034016000500d481c40c5840d84800441d0b0010702c0381c140f03e25031503200c800c42a070314844107510b96915408240c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 497995476 1250 497994226 497994239
    0x9110702130e0a030c0f0f1b05031908090409080f03090c010302031b070317160306240c110603070806090901110a0507020625030f03090b15120f07 65
    0x14030000100c0c600d802840080403104000d51240c10f010340150500c00c21006950400020b1044031854540c4100c44c1c89020b070702820b140491030b54618402040c40c1102c0b10100d66480d002038031203004041940c20441662013959184110380000c090f0b00d030821344401c982c00004002002411700c40d058000c401d82c903440c001000c9840c0542e01c1d440309051600c10018400464416420076005154480c0a2070b50740015103011070700a203c03030008007240d015010030301041e00d10b20110a010074211f5135040c451541c42c0c500100c1c01c034040501010300d0598500c1b00402c0117000f4a04410707022301564600004806131000700c1d50039403003100c0100002e484001041494a808900c081e081607124000300500c1840301840c040e07500c00d000585050100200d2020110341c0c1c0c050445103540b0b00c111001c40684100380700380308a01004002100442e10103507942c66824464800c40c11040e8000d4102c0031075072981f065074803801c1e0700c1400607500300d10801c4d00880140300401401e4410b030007100c02040c07074516024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 497996726 1250 497995476 497995489
    0x30106110610050607062a030f150b090d1a0408070c240815030703051005060105120c1806030f01060f050a020618010b09090c0f090105090f09010609110702 69
    0x406000b0800c40e07160007480141c4520003078682d1207501c01c00024031309000b40210b88250103161030601d6403a2980c41c3c0c051040c0c0e8982c1005000500840c3c05200440c0704444129031000a4011102d10f010140044c0b27155140c409410301041e4050340b91079288010084c0e40034940901100d0686a8040005040d03082059000e004401030141d011200f55a1115030882d02645941f90180010002d00c0d001080c200040b510f004841d5800c02021145000c2c1e483c50016291000014144140b6141000007541940640d04481c841c1303298401c2e6891395030380c0c18a1584a90000480d00c1c1c06114848a202450b032680340c0110300803000090783c1e944540c58024010079161112455004211060207031440107900082c607160040d80c01c0720420003111003134810b503004011042011f41c1c010004030a019100030003040c00144d010043d2004024241c0180500c6900c081c00c0c400d6a81005060001903010601c0c2002c0640055031078002207209590360f0400c0040e43d000f042c4190b000c0c8000a43d060845c074040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 497997976 1250 497996726 497996731
    0x1080706050415110c180405060a020918130602040305011b0f050a0e06070b01060f020f010903050712110313090b18010b0a02150106050405040e120301050d060902060301061106 78
    0x280740c03482c5420b09200b0f440c0e004008a40c0004144440e811651007803160a020749200104013808074403000614000303044440b581994155600e0082501240d1260000c1c002c452200300c000d0001c00b40414003c0254185550050800081c04020304541b00043c90398001030000b140907000200f0004821001a1401c01c0c0c2d1407401024040d410503603080c03054006083d80c0c04100541001001c0c20120800b0404a11170030000404441c0c0c0000045000f030f41010740c0e44011805a8215a244c03c003d10459080f0f8104c0c4e5030240210b0000c1c407501d000142071b42d101d6070342884545403a4200c4e203034032240686550040c081002001c41c1102c0280721910301171040301501001290929140e424015100d802c07540113000c0c04020090000d0b242c12050700800090a211008207205580c940e51008000c0c0300b60094020284a6410915500c005800c0010f08584540c40400c1c203e1841e4079040801848407580042103403d00c0c1c8a016503c0980c0d00d200296000708030346c0e206c0c9011106000005424603200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 497999226 1250 497997976 497997989
    0x111091c02090a020702010e040e071518090b0409020a031214030c0301120512030403090f0e09070b181f030e06070e1302070204050915010807050105031b1c0203010807 74
    0x1803125600541e446000658001081940069680c9251300040707868100c20805940c1150800c580d07811000c2c0009034603012a50185040c0c1d0b0030101000040f50282d203550b010340450001c400003400080c01c170368402c0c0e465180003040000c001a080c1e000c500307004210b9000b40d41d100600016882540d400000e548201d03810b0341103191442c074050243d1401c0b408103000d5040c0c18402018010104001000003200c00c600382100f494480c81e2900d0b00905e4100140600b404407440184c0008680340c0e01c00c0e0641c094400440917042123420040d0041c03060b0040450802c481134522a151325580b01d41c06039880705845a14515000101171350040e00b610032640043c0d020341d200604019815509c280120340b04403040724460303610011956004c01034001d00d0006940540b070182445140d01c0000b4901070035260724285003150340c1e0307102d016507125221446002d0105108000044411071141500503059011080700c504003070b240d400c041001a01e00c81e941d06240d60010040c41800b03010080f01008204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 498000476 1250 497999226 497999269
    0x10c080703020c30030f09100203060303090906012f01110432061c0c02060108120c0a0b010f031518030302070203010e190308060a060e13020c011109 66
    0x4030195103564500c1c04203102e003410300011384c40743c481900c0040000318074070309580101e46a0800c01c03002100150180c0742c2c000e0318414108810b00b401c41c079000741c80c07041d17a004001d14106035881d0b061102600b00148018108003091390b040c06042d2079001d500641d00d0004044c072025048901c0000d0840311800984c1c4d0603140180f100308110303d80f20059651203d4000d000f000c10f030005c4d100c0443c0c007085280c04258014008070701ba00202941c502910b80c2d41242050910181002820590700e400c820301541000c0d4100901040344908000c000341000c881020840b900032629803900ca210803c00e030020052003020b04400c001344409841000c01317100c1072040403c00e40550446404141031102001000d068001c00c9800a640d402c1d0311002000c56501e00b901c4004042210400e1062040107048010401201c0841c0c01c07802c0181c030007410385001c1d44403034240c00e900310104a0b03c0c61400350780318070700c0d0f0f001c001e6541280d00a0044030790480746007030342d00d8441e1400000c0209030480c901301d084440d076 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 498001726 1250 498000476 498000487
    0x1a180402100f0201060305011406030c04050108030a20010c11060702030a0525140c01090b09101413080604021815010e010903020925080112200d05010c08070302 71
    0x958801c045180c0e5000350802040d1512125800da014100ca0f80c000b5009500c1c1c950f503c40301c009403460300303440340d48110141c2c0e544c1d40130f400401007100c10a0041881d1540207001440005015441480001c1124180140d1740c0c0c04050003a402e42d40241a8100018500722040390805010001c00c0c0c0c1040380740c006141001000c41c0d0040190181301104d520103109007420b407181e40110044554043c1d04510f40000780801514150380d2501184812800241c1d21600014404005030035104c0b02e0030f000703041c1c8080200d07900c6c00321130b8007400007042e0340303840400c0084002c20084070440c60005c002040103007c40b45014010000f50021201a4202c10f4454104104031003201c2c030000c0e0880402400c1c482c41c40000200102e503542c1250301f0003500040c10300140415001d0103201102510740c03179250122107001e0084100c450240078829035441c1025044031100180c0012091821803110880100b034000324400040c0d050b006036070703007507401c0d035500c60b08809601e0f03006402c5580040a402d0951620 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 498002976 1250 498001726 498001729
    0x3060608030a084006020a0e21191b0311040506121f060b0a0e1005271c080a080115050901050315030319091d0109090203101a180402 59
    0x32401c03506041a1045020320041c01e0044080c4013403a0307203030000300840d2219104035000e0040010380c1c1c14503224400d08503020601d80140340001d2031460074030010348032107100001c0d0384900006010003113802d2004144003200280c0c004039010003c1d802079105000780c42122040c00704841c40074280b83c0c0161400c03a042c200010b0006403400610462884d8008846903001c0a03030014004c0360848002240c0c0042c19280642c2d1101000b000a1811505e02c0110110380718203440611488116a2101040140111804c10007003c9140d5560024280c82000390b0050352030716403400a80400c6500c180041a00c580150f440602e03c0c0c0075092040c109048400c07281005007444c001d005074141005000800a140c00620034a01815000c010301101c0e00c40000400c1c0c0c080b01d88440d00c26400107080e481000401e003400e0b400740d49919610002110541e4207100940014051601c03050340c140c0b25040300d0b4500d03043c507881003803a00501d4068500005551000b044900c1c6807c00d1604800007a00040c840036 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 498004226 1250 498002976 498003031
    0x10f0302060f18120d02190b01060f02070506040b07061401030308061306050d140d050a05040b0c0109050a0c051e090a05041e120f03020705120a030603060608030a08 73
    0x7003400da4465540c60307107484010480c19a616103c0a504100d10400c44040701d500051128410384550b003d55010412403114860079243d00e2001803e01000d8000412045000b9030000440c01513074130540e00c0da1a00ca002180b043c0c2d005d50303c007807201c400014400301444124450010120903846443c0ca207035140d03407401071282401908151054040c11400300c3c07442030b5540b000006280103031207804100400e0800c00f419030f000341c1e20020140150208101198032035003c40c0e03001070481e118142464104400c0300c03002e070041041c0190070741d039401c41e44010a10402040584c0d40c810010284203605040902400500034034111402c05107882c9002c0c100d41d1401150b83c1d01c8106a0000140c6907505c1c00c08071814400041c81800480d980070451060045000341c0c0700d6206140d445070708800d43c03805000ca049205040020b00250402ca41184090702e060004040c1450103103004140c080d16500d80004441450f8406d4846901c0000d140681030740182885501c6050700c0406461105449141e000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 498005476 1250 498004226 498004237
    0x90616050a0e1c02130207030e0d0f0308040f051b0406060f05160c030209010b0306010206060f2103040b0a0e0306011a030c0a0201090b0c0901181d090a02030f1005010f030206 77
    0x2c01c5000c440f2038031402c0d10106061401c950020035500c4d440410304000c0c0000d41c0412025000580b00011079030750f82c02c0c107400c400355035580100d0807014089192000c039030a141c00703007046451680034400c540106000f000204003d00d081c642c0085800c102d0410042113941544c00b610912403140f9000c0402900b100688083c0e2400c00c1c0101c000d00306503e060020b04207030fa08025808902e001c00072448021040146115030820307001c6032600c1c1c880c10704001c07103159603542e016440003110003e5050a50884100d140d5013040754101c030b0900d83c488808000d65080881004c0c0029800507040e0868502000103900501a2010f03208212943c4030364004548401403c480403d180040e0b40c3e00428400d520050b00c141d0482c001107254200700c1220030a56101d010000d0010b4084100304010b10355201d45e00007111140c104501d10701640512503070100d1002001d501450090041c1880076072000c3c0f01900c01032107404060b1000b0388800c2c100d0700031544180c11030b8028021568007400107072a0314003100c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 498006726 1250 498005476 498005479
    0xe07090b0711060f0a080c0f04170c0312090301110c030306010507030905030a0807050609010501050913032607021b100c050c150306040608011a09090f0303090616050a0e 75
    0x25035401041c14441d070216100100a0f80200001580040c610030010140400107843c2e0b0b03500d186034032600403d90080c080e60380e01d40b0107508100820803003050b0040160180c404400d080c0c42035903a41400007810003160000f846031313484000403440c48038507081c810640301104422010341030040c040d40859480c00018900d9044c40302c0002c003141410300039103070100204801000c8030403040c040d207802121600608012502449843c02040d040c40c0d060003514140c800141c001e0040da9034500d1001e00164404000390b080c0501c410301c00c60011500b40458050581141074680302c2c5c10040c00092802790320017114000c405070700080d0a00382e91808a003685421061400058648c19030510b43d040210001c5403a50245208403910b80e21001c10010f944284001c83d4108901e0344d41e002c0c068241d5128006003880c18209203026591031610000703194119035150100d960100341c00c01028a5540195080d90087d4015020000d2007030b0741d200380b1000c0c10030034500310b07091a01000e0090181000421040e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 498007976 1250 498006726 498006749
    0x10e190c030f021810030c06080402030c19030209012408010b0f1c0903020a0c120c0e0703021204050303101403060a1d011104051003050f040b0a02161109010e0709 72
    0x11040d90b46513521000c0f0300403c015154071900f403050b040e1010740c0d5244400c031900b100d00d1000080c05da0152040324800e80d00500a004c0c1d030031400003040704044080e054815528100d0070040050f840c0c270341c00d04d406000c4110030b24455201840141c540c01c0c0c4550308070b40c20096a08018070441d04400c003500d0f4000e40720031031144c0381d540e021110610851041024001c0900d0500e900c424160b00140200d505c50089041000c12a11f0b20101c43c0e01ca22901800f5210301e0510908100c0480076010031a407001d030390720b401400c2c007100c1515618a88002c1e41c040d80caa9101000b4050341080c410400ea0051100c0b0360140207488500300400d0700d842000307006843c02c950703404107011141e480c044020b0f0700c144008000c1191189202c0c4158440d04180181c030300411703c0c103200707204c0c1a0081c450b007070107503088100144c1c0780c3d038540ea542d81c00c846008180400d403d13004d201c07514807030000074401c018044c0b046c600005000440313814401e01c0340301613208008036800d04062081e816040f0640c802a40c4450305030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 498009226 1250 498007976 498008003
    0x10e0a060b041b05030406050c040602070302120f0607092321010b030706022512020904050304120807031707050301060c111207240207090507120509010e190c03 71
    0xa001001d1082a1400d05580a0f0071088019880b100a51190344241c0d0100540d8036482d00c0f02215001d80c0c003880c00507a10224044c005441c02d9003c3c041d40d214401c0840d0091003010352058240401a40c032200820f840e443c060001036401044032a96540000c840f602d0141002d000482541c86151541d01c0d20404103010305241d0760a4001049101e00941220b008580ea044c0c000c0d5901a4540c259189654414890300103580e1482540300722004007007113481d00416a0200955040301030800c540c01e02c000c01c0f001079000c5040440603030080c016001103407a100c2d103042c080c00c950401008a01d05042c10820001c0058020040c1ca040d200c10f850944c41c41111450b01c10105580411030340c0c2c1c8a050440c0300103400d00009410410340e01c43d444100202c00c507a940b0300e071150440100c5040980c224410500810a80c1c0d400280d0205680c40d007001c00c004901c42580c1140c02c00d40d00200545d440d140041c140c40da0802c001010b013041c0341c0001c0c04010281c0c440d80300c003003070600000b070204194420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 498010476 1250 498009226 498009229
    0x403020310180602091903051f05252120030f01030b09010f0203040503040311030307080a12021b0c03070f051305091204080f2e1d0118060509010e0a060b 68
    0xe40750704e003130f030743c1b40d0010703030203840382041552000101c0246000240c4591a90819240ca0003100e0141030500340c0c1f2030300084911000190b00c0030078003d22041004084218540b581400c507500c0c0b030200134100000309264607440640c803031558101c41c0d0031000810800c0c0300c031085180d8403e81c1100d40040d40f1582d1500c40d400907a000d000380c90800d41d0094000b00034082400b0021005000316841803010040c141418414941c0b20700683d880030741007000912843c40fa40d40581d10088105000c1100145070001c0d0340ba20800700440100254410360240340418024101006183d015002000311621030918040018100c40d4100003001502501d4802103a8003003410490301c0414102800c2c55603d0303c0d210001c0d5662140200c0701e40c01c20b03119040c0d0440d00c030800c0d0580307410400502c00c03120805c00010100180904113010004801a540920b5240713400c6080c440c0140350024017045d80c0010700c03e801e00c0030a482d4050507030051645020542500304000060f40e004003944140c020a020181a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 498011726 1250 498010476 498010489
    0xe040303150906060e0307060207080a062d0e0601060503010b0406032f0a02070605030705091c120f031d060f0c04030c06030e011a100c14030f040302031018060209 72
    0x6000c0502d8a0070403030b000c40d41d80c2d04074a005030600b03415030848940b55990f06040340e07074814500c640d844a4200d045182c1c0441c800390400d4262907207010030301c60034180e180c00019000528000d65100c1c0c541c0c45491040540f000d00440d80102110725180341154101580030440d0303ca940315580506276101a0b074808113002c0081c9045041c00b8130000041c0006600078080c8691200204c0300040c060b8441c0400e0090060301564028921640d0315401c1540d42410320118000c515280c01e0000b46040907038001640303040c002c0c4150901692910b000f001504405000c3d2542e01c1c0031f00e18550408400320300242c034005480d50707002000250b024016160420060700a108a40000d451400842070203e6129019008100c1c0310130440c0c000c00c1180c17105041c00100c82d0340303040c1e0580e1110010201514540c4143c030380840d180d00030740c01c20402c1c092400303905103103911507001c00c0d80010002c5420015441c0602a081606011103414486007000c0038420005404080e00180241e5010a03032a00d20703203c0320b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 498012976 1250 498011726 498011729
    0x5070201091e141c0824040507051b010c0f090302100e010521010513021204120311120609090a05072c0a050402151309020906071704030c06090e04030315 68
    0x81c1919000f81e4000c4d00205203842010401c00030420100110301009001007012020070000c40180c1041681601000f0203010094485010003106001510724915a08139243c2141c034401c0000034403448549024210020360701901040c081050810000b40e20340400c116401ca6132860300842000190005a42034016641e1194844812407215410721000000050503500e04031034800003003030a03440038400e034424801d544014003001004500042e40031485e40f00300c0921410085554070003048c0350803040c0c1064120113070710b540030024031401d403c02903060707508003005002030030001206850710740d44d9988600c0f98003807513054000d841152124110919011030030402969000e42031014410b40034240584090740700b600806101c03a8185241011034090350045210301c100c2c1072400e5281d10080d000100714139003002042003034800280050403041180b00ca02e420240e200d500b14200705800300c1c4160089001d100202e2418040b00d424045004d50080d89403a000c00c594814020810402005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 498014226 1250 498012976 498013013
    0x80d020c0f09070c140d030f050405030a0f0e120610080c03280212031c151a0c0a0c06080705090d150603061a010e04052208160609030305070201091e 66
    0x552984081c51701c00b088420704c0da0f0065a06002e8012211005411220140d500901962041044078403950241c41d010520504c07030304005402910017004510413154410aaa403c1d8000c5010000b0304407410b03000e01c000d411f0000042680e40030400c0030a94400c610328800609032a8000d259000c24004180424819800b50207440e002c00f4404400b56643c200030307070600c120b42182008414841840c401c02c0303107449016224140041c038001034203c10440201c942c0714154000c100d0355003011410011186440d02c6110400c0d140b5182039002800c801c170140100007004001c014180b0300e03556120041e51215007200c65440095101500c600007041c07140d200602490510003171010968400301d1080c8442c0082c0c86010428101500b08812944100c80754000c030311100d0b00c0340d502c40b01d0000c08040000d126141c810b103825203031440c40c1503101258808450301610390050504140d40b50045d107070050003d000a00847e49541e5074010f210001175031200d04482c0ba131603042c042c42055800000342202 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 498015476 1250 498014226 498014243
    0x312150e1005060a0804051e061501050d06030308420103024f09110d0f050601030f0902030a08090a0e011223100207080919080d020c0f09070c 63
    0x4c00d03150190214104039400e40e094001c2502d0360000c030120141d404c0c01400300c0006441c0a5843c40c10351030030080c811040a040080c280700707140911071644540800f4500039250b00c1060f241c015030100001407020210b091170f03d020402e90124260028100310520b87c3d803084001e51440500040b0002d0140300704800307414010000c480030071032045c0c03000740110400e85c0d038015802214004100341c0c01c0480a0112450114000800c102c980c20741c465200c010001c2c40b254135110700701d5030100070345016402503080c1d16034601c1800b445607014410101915002c02e400d01008c8625000a51074011100c00600014400255200d8543d80c101a86000c0c005828071000d00d940c4400c48a03403001e90641007102c0840c1402881c8041c0c1c1c1240c0728800e006440b50009002024012040b00065001640100c800160074400e684c3c40307603200d01c20808244040711002011919000101e43b4184840703210b8010742d00440c100c450f0b1511800d151410030b4500b43d91449164884100c111440d4410f1000503141e2741 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 498016726 1250 498015476 498015487
    0xd02070305121305010c0f120b19030b0702010605040e0d18050a080606030d0206091216060c02010905010b0415050f030307051911012a0311010507020a0312150e100506 74
    0x4480c007600100fa0161000b0003407040c3d10310b01519100c40207000000455500020040100d03000c1d0040810040068010001000c0c800b0038406005442d400071a08911058204028103609114110062100b11420302200b0700c000c80c5143c0f5442c807200d92a04200441210319004840c04100400612020300700140456031420203503190581074400754824041d002c41642214400503039240240001000341150600c03429000764a54003007104142c2d409640c8508201007407030362144079050101900040303101b00240c50580c0c2106c44109400e07215038505205940b04003881e07812071041e18010f0380c89003001d00c0510700091847c01075002c000e01e1445142a5100d0f40480c18441212240c4209009550700100000544091440c00c03043c40d580c0010810964003088240345100d82a802030034502c4070f403901140000c0c00d664045440c030300583d008140003002c140d07002442040c401c512040800481500350744480000490b8410310103101c04480203e42d56280c200c1010001f00b000070403059952 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 498017976 1250 498016726 498016741
    0x9060f1305030f100f0603050c120115060f080915070e060f0c01090c1a161a010807061103040f0510050c0d03320f150a031401150b0d0207030512 64
    0x10342138840840905400c1072241c1204140314010081929405809429807480340b800303111205210b0140c0c0c2c501c642d00c400c0640c1c6014200d8513581b01410359641c550408000291000d4408070000d004200c1d40c1e80000342c82d6a280b111460b90f95041002444c01c500005030b004000303821405109001c5552040008d11307144101c1056201d00001480307241020703240c0340d8807204601c00c030302c0b909038201080308100400723202d86a18010b00c0d02550302c1080d0380c1d001e041c0028050381204d50240c104035247d6000c0d01c014801150000d40b001803290500f4000c2d4076007401c0524896000c81244034180c000d4500b801ca8000d00c500030815074540354821402c580c01000d4108000700608804105e441d40300e04a844210211195000d800d400035980c02804c941e11703261a1040801105c009110740207200c00100c0030030060360340c014038100440c090a01c5071174400c10706540c5400c54104000d44190300180e19010828424044141c4600c1d80e43d8480040e201d12041c20140c4051041040c0b03071041064600811062 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 498019226 1250 498017976 498017983
    0x150c0c0b0c030f070f0c020f04090813050f0618100309170403031b021008040503040510030e0c0a06020d030207061803110105150d0b060a050d031e0509060f1305030f 73
    0xf0300d11a2001141a46500e102aa001450707211540006100c100c07110003d803c03c84802054204094400036118600e62100301d01d503000380b024070304464245007040141e45460210fa00c10070320704a414034504403103540541c807601e800303104d503c0c0030781100c1c0b056032481c030700950100c15503e801c44202152800c801e41c0304042030b841404100c1c04035105c40c6510f145070f5480d40e0342400440d4090f1490340d142494010558552400400c125554401080041000e44031071000f00907032052601c0102d400d684159946080507030000804d8000d0700510010445a0f42c0001d0585088401d41401039907004141403000240070200b04945000c481c8147c400c0405600c0040340c141c244100000700400c0d1508a4054904000d80080b180d01000c0401c020000c5204000443d8000900520003103003150744038045881d42c0c4a010090f40840c2800314140b001e540940342c84c0201c020207241051038921140c000441138021a0609118144045070221104034880603600207030100404841400148500e000c0d81c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 498020476 1250 498019226 498019231
    0x90409380a020406080c030603010b100201060f0905070903080a0c022e0306180b030c090403080906010b071509050c0d080a1416120207090905030a080c0304150c0c0b0c03 75
    0x18000e0400001480c4881a482601c0c161026aa40d89070b01d41c660500d18101604041e00c140e03490b540c4d0b000c103400180d440c444074510100654002050507868029082f80c1c855165101600d400d0824040041c1a648100c0100560340c0c0010001d445440f011012105124a004000d40007a20745501440d02e480c0e0541d04452210700c009802014003912100320300b41c5105106103410b40680c00030480d004412030300005143c650180c101d9420342c3c1800005402040f0035181500440c040ca014090184002d000c11405045010ba09031301e06120343e644e0822800824001113001681c9101c42c1c0e04101080c88050f80140004292a05402944c2003102c1d031740e44100c98030300c0443c5201c0b04c1004112028010b88a2694840c1040400350409850305140010544200d10440c065808013040300ad20601c10b840d1414041c2006640314041100043d15901000e80748a005d0b0005008000c0020000d81050f054107100341000716240134030400540e5809070144000f446868140c04000d100c407542c1001e9132 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 498021582 1106 498020476 498020573
    0x90506030712021605150403020709050414030c100b15031603020f0301092403080d0c031d0313120209181c0203090406050103050903090409 62
    0x1003241c4c408150308001c507039520402414800c0400551300b40880d0f2540101260600c1d45002e50343d12858814070030110f4070b03600010100528202d00c9003110504000b140c0c0c840140b00955620f8030081844400828034141607001c036450b020320005c1c2402a02a5400d255032211721840044008110850f0189034080102080f8040c0c1e2000a500802d52004002400044208041203629082d140801130170030200044c00443e4040c81154460500c4200c0041ea2000c3d41000740c0c05010034240414072041040040d0502400201c000e00310082001d2000141548540c0c1044500c8908100079400c0091600014091402c13044a50418024001100c1910302d00c00394100203c1004025400142c101251500b43c41c200780c0030314005010242028410b40c0b4190070300a569000b5251954819134442030702c0c9051049160a11843c0c0c031082c1c0201c0b0000e002603e01c40540391b10b8034080c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 497841726 498021582 := by
  have h0 := BRFrame.cov_init 497841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 497841726 ≤ n) (h2 : n < 498021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
