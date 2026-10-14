-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0610
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:43:26.89973+00:00
-- url     : https://prove2.me/submissions/5a9312c5-a20f-4f2d-bec7-e46a96b37c9e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 109532374 ≤ n < 109712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 109533624 1250 109532374 109532383
    0x90303050612031902010221040308060d0c06030e01141312020601081903020f010915110909040f02030703140705011e0806060a0908030f1908090a060203310605010b0a02 75
    0x8103191160030038501340d8008203d009006d1824003602540301d082c0d070075100d030891086651082d80320b45c0e6501c0041e0341d0141031061003215030308010103400748107200b03000e02e80c000e07044034943e00c101780d000050344218004101d00c1c80800340c2c2da107900031400f02d01c0901480304000c1803040c0d1480034001003411394904908a13a450b1021405d4900070851911800100741c424003054080e00c2c40900244200c540c14100b4000c105580d0316099501481d160b820a442910350054586244c0014031001483c0e6071510780c1c0344580034045c401c90341805804800b100003001c0200c0e07070514040082c01003c101e401d040014104003404a01c400300f03480094441d0254a60000b11103600807025a841c0b9110f15050206840c2d000c4640c019080500004c2128048000400c1c080c0404824040ca1030241614021080d607400105403100081380e00324041e80000b0074402d800a41d0042040c4107d09040483d00c240a40c2d055010a2085806551200c2020911120f070180074003400a9606552503c070304100060340d0b5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 109534874 1250 109533624 109533637
    0x51e0108040f02030f010f1d0604170405030303070201020406021204080a0f0c090f02030603010b01080103030206150d06090303020705011d210408070b04090e0307240f0f09030305061203 82
    0x1000100e4001908009a104070704004640c003a088408000d903999001e0b003c0c00490807103070141c1d45030505512900002c54150319120fa00e450181c4074903283ea407111304085541d11080303251607000300320000342601c04000551180c0155400162107030f0a00c0d00003410111350501030150b4600602c014805080080380d2200210b5201010f0355400c3c0182c608411080c20550040010324540410b81c8030101302c030340040d441010110000c010354980d010040d00c81d00400c2c0400b4005034029070020304d141d45104010b164412004140f0181c1000c582d0311a019503000c2c1100b20002a004580355082003400d008910000c003034082c2001a03450301382c54941c0c0d14103000024030320140c5000141c0710300d185ca40701164003034900201034420164480f001c2003250360241c854040c4003460104242c640070004015034500030382c090f048510040220304048002c3c4030381c1c403001e1000d5590342680c0d0114402407051040c80140404045110352840c18003400303e4030010485c500403803100110008110012049810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 109536124 1250 109534874 109534877
    0x507110915040b040b0307141206040c180f020f1b15060f060c0f070512120f2b0506031002040e0403050c0a1401050f090102090a0e090a0b04080405030601051e01 71
    0x58003220f850024028000c81000f00c0d4040c000c00b01c3c007041c00f9800000c0b00d10850070660b904001000c044443c55501e203022a0042c3c040c00741d0b02000d12103044010300c0400350042602e40030460702231001c2c070342040303900203040002403030000516640300303510301e01c0c1c0c002c1044289006001d07a10006185010900b01c02031880784a1041038078101c4087e51180b050b40d07142000700702220381118409480a545030158080d881c0304981b03540d0070314840f103070029005400100100d20309041c0300227148400c9582e042a1b2001d0340e180310300c03100441c003554420385600c0d041d100c0c0c20010403242810301c241410105001700d00c00b012401004280821070701c131103155800c20751529045d81d0312004101c459051280c21480200321001e1a900d00f078108405401182c041c1d540f84402542988401c43d0741c2d8200d104030303862560480c0070130f9402c002c00380600745400e50002c0e5000c19594204026600e04219100c00c507402c4809400110f428086410100502070160005988010a698082040d0404080b04885190 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 109537374 1250 109536124 109536131
    0x319180506040b0613020d0903030b0603130305130806070207031e030503010e0603010608060c12180c0907050d1514011b060f090209041103010b0102031903051f0303050711091504 79
    0x145140c440e0018040c1c0007402c80b404644a9047e120030b180505030f0304006070006414000002c0306441c0810440c0e000703400c2d000090500b200300765410741d07036500075600785070a9035000c1034000b405043c1804824441e03645076000d86425802c501d03240303401750002442568000000301070480043c0d00031003164152041482003002c0ca82c0d445d00040e000d07040582140209026901c180040300034914050490f0f140303000760740c6402e6a1a02c1525005014400504916910145101c0d9050820b080115002841468160326100b40103040380c003036505003001c1648800c8001420001480c41d110030030300c150130920700b01a4200325038160038031034001c0c01c0340501200c1d81c507101250040c94550003684084d901800c6c0c081e0520309420601c40448442d9031481c001d50134002c80c00f00e01e601c0841262008103100300d0f40e036007a400c00d001c02c40003000020703c0091044540e56208445200b522156401075101c0e84d5515070703503002c9240c100208544520280c2c020b15810051000d19140801da200e41500181c8001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 109538624 1250 109537374 109537381
    0x180308100b250c030503031509040209060907030f0606020708060f070806150418020415020703030206070e010201060b03040b10150e040b040f09140d050336030319180506040b 77
    0x42e41031882103000f880111040d000004021021015504c2540001c0c40c44c80d4000d411800d00038540d1003120025407000d44031001868511300494115040340e203901d400640050400110030499400b034000b00c015a101140c00c01c2014020444560303c01100801c201c000c0c100ba04000d00a0200074068601c1541d8040d00021007460b8002590b00912040ba003006a441c03444060300002c0d4401e0003030b4140110000f4240d400140005015801c03654158010241690b58a10849111070303030500e814115501c41000040c035001740406140a140507084144e09400d001408800885031a4009030f400d481c00a00c88840c0c1360801400f40300ca030810345011503001c1d01700c0b00180080c502107a0b1688401d1900c2c41d18000d01102d08000300c40c202c605c10031141042c00010701641ca5010447d10743c2c0c00e180c19140c0c81d40605803491803068805610301d013202800e4108120030340c15a08202c6c2c076012083c9424600d00c2103916107005a40d80b003207641482c09018a41d949440740c4071030300104090011504180030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 109539874 1250 109538624 109538677
    0x1207080603010b010e1804020d08040905040210030902031203060f030327010f0f140c100902010e03121602030109150e0d05030f04060e0c0411120c0c060106140d180308100b 76
    0x9c01000c0d640100090340c1c46880700481c0008110a5809074018008114507140803406031242580c01d5030024000c140c0ca0042c80c01c3c07103d503684000d10b420f4000105022121090310100007a02d01840e00c021050043c0c0b60120103585074044214159041219101c1c2e80141d0542061500341001c0b154a045400d40c0106100e4850a108091906000307214001603240c941c106030380450b240354400d03694104c8100c4c4200c20544d660342003d00d140e0f04980200280f45048900700c18000203544058008203440e9040e07100d08844a1644c80600e07400b40e101c88590a03204414031051701d4014050400c2415401c2100824074400d80080004005e1a5200c141d0840da610822604000882c01030060200411200704161142c1060610001e1540700d000803600491b1071509a4030018400c000804080e86481c030211161100717000301949403001004040441a000e004410111103c02503551441c4402e203001804c0c590700a110012405405030240310307100d11003044884000c000300071403c98a028108 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 109541124 1250 109539874 109539889
    0xa0c090302090903030406060f180b04060e0c18030d12020705010603050f070e010e0103050a12051e0924030a0b120d090807080c01080c07081207080603010b010e180402 74
    0x382d03010a04600704901684000002c5105500c00d50051041703e540d6446007950b41c080b4040c10041401d00f040c07003040e0003440d51104440045c011b00c0400c6065039061f060400b02025204500454400075203a4803038504d80811a07644403040d0010a46a640380d00c005007215040a044401c940d00050713204240202500464041c64101003609c0c45404805075582c0c0d80d00c85480b03008811000c4000000340096840d0040303040f01e42260143c2937400712950342c1d00c85c10b409600302d0001d002c401e022501100303645011840301960b40203d01981c0d5036241d000c22010020030f0b844210726460001c50304c031000e01c5910071b5a821a05500b0b0100b81407401c0c00004007940c3c0320101350750142c440c078064105240d5000c95140200c0340e01c3c40c03d9400c4e40751101c91154440040c0f07a042e03800f080c07004c004588909000c13002400260f000c0c204032418000012505c451095040d02d03210b00240b185d03420700030f2514081c40760b0f90400b0401d09101541c0c0c4440740c04103d440d035900700c00703010b540c07d0780c00024195114100b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 109542374 1250 109541124 109541129
    0x30c040f1e0b1003091101081e0a0b0108060d0f12020109060207050309041104030512090d02040e0c01030f0e0c10030b03030c0f070f06080609061504030308150a0e0a0c09 75
    0x40a03032555107656110002010354140382c40c4182030001003141c0203406481400012500403202900e0071100200642d00940c0c0a407442c0340703803424081d80a0400345500365031405200d1000020482e406850300041c40f04502600d200d04c42d0748004841800608540c2a40403100d030300c100e441801d01740e1803500f45c0c0140048180a400940000381c800300f0000048001d0030b042c5070480d000c000540314046840f2060041c2d02005005030f0003c0200320940e904100a4541c480005000c011161202d40c0403c0a80d00d00404460710f56005850a80285d80c0500600c05042c403811010441207484111041d039030042004d0141c05181c8440020340e007540f00703400c5401c01c048040c080b0fa40c3c501441d0300003940c2e4141000000101d014614021800d034801d51484401c40741036541e20003854072803a0030042950000380040f5031240e51079113a040c40c4810b00c000307400114000d4407120760a20301180156014854070742210b1040003e01c00500c1303640300300404260000042803000a100410540643d580304181c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 109543624 1250 109542374 109542401
    0x51327051204140a0602010903080a02070632070203030c0901030902040f0e07080d1806030b1201150503060a020f120403140d0b01030f0c020c060a1806022802030c040f 74
    0x900400c40211081c0f01400d000000c1d18001125503035950100c0c22680501c500800160140003c50740ca004290041c000003070081800080c5072812401c0390b82103054040340a40504000801c0c141110502500b040d0b100700c0a0000c1d510b1440c00e1516480c0302d204081c001d81c10b0564a40f8080117540351a8056041102106000c02000d40409451940c4642601c0b03008150310654001c020254820100400343c0f100c80820f0300d1120381409415800390044420550300310791500b4815130420000d00500784185115103003004903e003000103040c1005001013541d0000e03801000540024800f40040325800018482da02c80b540d1514035040311094803480020022030b202180031500c5042c170340c2c082c2c0a0740030245c80411100c00300b6400c9600380c0e4407001e00e10002d43c001c1c00407120942040c10007004041040d00d090550444940e03485605808070b03400010059004841d030800c0801c03041c0b1001070001c0d84d0b800d601c0745507010341e0020b69290381d0786005074052a21606854a80b11a03130b0000d80342003054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 109544874 1250 109543624 109543627
    0x612070b130f030f05100915021c14070917120901021204030c0509010518070509030307080c06010e010b0403050607140405040504050604030e060f0304020f06040f0f0513270512 78
    0x100c0c20300c25200154442c0c1603071075000b20719486e09090b45901c6048082544084081034803c10209408002c1d0000d0180345d8895440343c540b0228803115204800c4620701001d03009a01c0c2c10084401021251130b9000042201c4420140107a803141c0000c01440a446100106948260341c0700103c3c201114040824000d200104012040007109005502540c100b6124604c550780e13124100102c070410308030190201c903080004a10607034403641c002e20a5060242c04c50303290841c29500c2861940c0000b072060000e801c103000602c91511004010707401400510412818107045031106500c0340c101401c130009221140c0c0800e4030204090003600d0090500a104006070700d02400d0854607480110740450019100034011040c0780307030420940d803242c042025001c4c2103541c1e40d8248021010307111270701c6500500c284000908a011005014041c216004840018038509802d025a80c1001a08512484e04080e0ba12841104042d6140200d0a0042030400c01d0090390070010305210b04e460007403111050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 109546124 1250 109544874 109544879
    0xa0602070f120801030501050f070c110616081306110d0e0a03151d070812030a0f180b070509011403180106080708070902031314010f050403080403080612070b130f 72
    0xc1181c403e40c12240210000c1c840d55071603040003c0e10781012600d00022a040502c4a004940746048040380c1c04c0028000c42d240c2201c950103103280c00410b1074104d80320800010b10b440740141c03e4180c200108000d0802c080e810b8606078100742c4510105102400704004035080000a5540d510198021500001c294821203911407881001e000f40c040c4101c90100207508922016200103201c1d01261003040c06004040105c006400c165030002d042c20a03056101d52408982440b0781c82004000a943c01b0840302e5018145850780a03041d0003001c4006000d414845c101803a46c1042c01c82180d056015601c5c0d6880ea61070f404441800400800c078210740d071034500089144e1000140306825a184a0110b81c1c0443d42d444c0d20a00740d21040751a00007c21010110341c000440e1041c0e000b00c0651440300109820740c40c006090b00b00e4004a600740e001508007002d1009040e04050a190002070544504520858501e00300e0340c0d6810074400c40740f840000049400e144d056560300749003d850000c0b0000d460b0755 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 109547374 1250 109546124 109546127
    0x1213020d060c021b06031b07081303200a030605060607230c030307080a0e011b0b060a0b07050703021c020306010b0309010e03270402070501140103120f020a0602070f12 74
    0xb001c5007082d8094495012045685000035940a41c0000010700240c80d41e5a040d26103d40902108203403250100f0500001d0700041610300a0320b410019100c2c0c1c40c103c6441d5040c012000c015004c0844081c0310540c44010703e68a4100516060700d8000138041584c2d00c4400101c2d01e5441400380203030400081c11030641d44401e1006a29a800034102d0444031958182010140c6922034400b008060710350030030400300072a015501100b04800141000144540c621101c0d048200141a040743d441d04c43c54108074041c500019084090302070208014181016680c0c1c0654648144c0006072040c05035050b04c0341a660a00401c1c1c89040d030141c00d031030041d650b5018498080e0002d503100900c45d420981707901c000e0300c1d001040d650102c624a40409102010010400d100301024100c99041602004a034000c14800d028200d07101203100d80d000308540c994204990100701801c00c180402400d02e1030000340c07560001d11090f009d0b400810059440e00f29280004821609540c000d100c0481d8440215549 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 109548624 1250 109547374 109547381
    0x903030c0222021b0f0c010c06090804030c0303081609030b0a050c1b0304050306060d03080c0d02040b030c030a0e030c1b0d0215030a06080a030903060903030e060a1a0f061213020d06 80
    0x90741300304503040030450040164079030145c040f00a000551500c04040460041c0d08410300c010702032542240342c60f0b00d0751144121012150001d0300441c0da940140a4101c54000b801c100c4a00a0300c0c1c810f04103421561120220200039040d04100340c3c50b40301081036110a0300880d2824025008004040c503040603505859812034494944240180c0e000900141410100c0e807421300e40c1940c17034103155551800c4042c0030f50420710840c00079607070074000404c030001e5803401036001340c0e03070742a82d192a803030100110700030750b076a501ca0010709810034040d09503484c00010368141517408401007004960407481c08036081091401019500803440c3c2a415000c2c0f40c100001c0d070040301c440405111450711101808d585115030310300200041c107020400c001240080c0d10038521140f19207000710344404082011031504e041500c0c40301e003003642c0707500c0c0f5450070b080301c88814510882a520076000d4a00f00300010b50a0151001c9140c010401c60002180f500c1c01ea407400413030940c020301500e440f100c07d09058009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 109549874 1250 109548624 109548667
    0xf0f03060f0203090304030201050f090a2d08030a0c050a0602070605071b020f040e1501030b0106020d0908070611070905040b0f010e15060a02151f060903030c022202 73
    0x1240c030701031821080c400385000303c0f440b0f060000000d500d440e01d140e00440b4182c2c0503180c54034800f0014400441150b640300b00351001005128031980442101c1c0c50703120520b003844030803040718001502c001c001818002c01501c2480d581810881d08040341420f000d424480b04400c014202840015030101b0060b06512050182820b071340c1e001c10f41e640346060b05281441d0540e02a5101640034109812444d05401c088403500c1110240c032452540f06008804c10030003a002100d401119000500c103080d8100140129644036240c240200d501c0e14140c1925090207000700070401011102e06514440c0400c0440000e0007d41c4c010170151502c0c0c14029109241524840001c1a429000103403960b07000e60514060860600003c3e04c49000c0710030001c050384180381c84000d601569040c1c40d298500211240c0c0310f1101c4aa41d501c90380124081d603143c00d8415080701c2c0502c07400f46014004030b5440b00c50460013130b0381030714a5a82000510801e0100c03030315001c07000b4039980c000035021012040e1442c04141 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 109551124 1250 109549874 109549883
    0x306110912031b1f020d0e010c0c020405070906080112050a0c080607090e042301060b04090203040203010606140d0f0f0608030d0509061315020d020a0507030e0a060903080c070f0f03 80
    0x4109201d1140300e902d4810603c883c1184c001c0003c0030004800c6280e0051440385491000000c0d0394030381138405820740d0209100500404c11485a8006500b0107000d500d52091851600820907400c011001d4101c1c001030090020842c3c40c41001d004000003000345200f4150444180300201e42d03105202a9220001c4862030000b03a51007900142d1040d036107180500482e4004940030b401d40e00540100c050894800400c003e5648510f0001880c1406d0001040500040303400965246020f005150075100c0591106c02009101d840015189041c14243c441c030100c04d0101181c41030020421102030400d20950226003440c0c002c001510380c400000510070480e00703a201703200c6035170303002412515a18100c5403100707800c2d003141c0c020300050b14410764010088071060005091100c080d20000c100d8102042c508003062002643ca001d06402150350359990368100c0710310791f000d070070002c006221046621008000107804100c0081d0701005000341c5000d00b540c000c40202555803908400f105815601c025a0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 109552374 1250 109551124 109551157
    0x14160807060216150207050604090207061b0e0d030e180105010f02010b0a0501031d030f070212060c070b04060b0d061a0102280201090e09060f0a020304030801030611091203 76
    0x307031140045039994144030645080f4280e6031521903500380b2a80c0010902d002c41c000ea42c80458280c0e100b002401c0600003000380141ca5241c00e141410807284102c4040c081d504203500301414459000c0c0d001c80303090703800b5241616641c0092030141c0300c283c4541500340e4090018400e40c0003400500c0ba0700c47c104d44090313840c41e2140e0000482603080310301e458050354201c0e060320002c0c001540603030806610140281000302c41141c061607a5070458100703404100044000165080541c900503903907180b240e402c04042e00300d900b45041003a0040c1304201000380f080f000c00c8006014001c01e9800441d000e40050a00d0100c0c0e071841c075002000b80008100ba4040b03080c1d035017040c0d0003540300090320501ea030115008107a52202c0041d039001403a080d11022030401115990115105103280310380350103011008000d0040f803c0a0314496481c0d00001c0506102a02c14001c04c00480e0f4005101030440303030044400070382030301070040305980345c801c00101c2500010503421800c0017446c004000c1500ca00030300300d140b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 109553624 1250 109552374 109552379
    0x10c020d03050c072a3302030315011b0204140601021c05040302060c120c010207050c041a04050a0f0c0203030f0f040203060a020f0415080609010605031009020714160807 75
    0x4016002d803071380c041c081182030100403000b44c03800030560150350583d280303840c00e1607038942c12610030340c0380080d440b64410142040741d20040c41080110071310701003d00180d410352501c9240e01c1071603403040510504120044413914840342d101c83c00e400755160080e109100c51044c40707032421054541951030500600c6090407a0b080104080400c4081d800c0554516141524507020014942c22003a0303040c0240c000d00c0303004900081c01c0720040c2001c00a8900140e1034a46ca401c00c00d0422003a5100346014a040c185944010884901c0b01801000110381c0010381c1c1c1c0710340c84000018940046010070b4985001410301c1c503160000040c601c6610180d4062100d45da6901a070611030307906a0340250158401c00101d21500740319005040160703444c3c0b07a5907081035030310b17902c1c41c885521003402c140200700d604041c4003843c2003003a00240900703a0740c01d0107480c60415001e2903000030391520608103100d5000c41d810080101110350080403500320022140c0b125003400c0c0c0040740c43c8961081c00d4251081c180300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 109554874 1250 109553624 109553641
    0xa02090a0f230418030804050c040c0f090902030f06011d0306011d0c04080303070f0315090504060b03011e0c05070204110405130903050405101e03050603070816091d010c020d0305 79
    0xc4c101a0420794501441c1a0441d94059521b00d40c042c00480d40c0d405080114105910386124032091a0a2681d504441145c1c2e24000b801050103600015001341c0100304101c003040b414101c8641101080c07801c4002c1d090325010f036122280641211543c1070107a0800040d80402c0c61081c802071400c99000d012440d2505601c181c524070592080c21140e07001840042da81902a944c0343c015010113050125500300304103c402000401600201030190340c540034081401060b10400d1190b1806074000c00c000f114821a0f004140303e894401c5143c00d858981c1ca0281c140700d501950b001c10340c050720a1020860b004525211034100740505402001c428500c03174890718181c0154066180c044e20740c903107442e007880709210001c030f94000200140000709900c42029526541000d40040d2165000280d50800c00109400c040903a40885a558005103d0b0f2609000d022401000c4503540400086c2118070027245880420f543e40f1740c0e00580d4a020050f0401c0394021550203c0107045907420030050741c07600716 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 109556124 1250 109554874 109554881
    0x601060509190e06190b210a09050705061e0301080f010513080301031122050105011d0612090f0d0210060506040315050402040e0a060617070803030a02090a0f2304 72
    0x24042c0c4003041c0d10224145042030b031030205140340f2406091100d01c0c0c603010381b0740055001040d40d2040ca1035800040451503005a9150b4100b1800c5030184224500c5031a42543d5603514000e845c410301c1c000480c248290315814850704c1c9a108003503241e880c1c0d0380d100b100c2510303549a803510000035403c000c0007a040304041451008041d45c001e0307205013140d00b1038075880c0c0440c88138044a07412101c1d40340c40e1000f1018031040d4055607542418007091560410b4001001420402840030401004100403401650751009403506503450201d5501d03903a403586034043c504010036042c03480383c0c040d00b044244c06542c0402d0003504c00c0029036007448826a90700900c1120b100740c2c4400307040e0015402520903210070030780200c1e03001400140701260702051079450302d0621980b44c204481c1140c1d80c41040000003184401440d200080c040a0300b05c03d482d103085e85840b8840100f00380310f0036500041d954500d5507040410409407a0140c0301e001e070030362100500e40d0001030400300a43d143c1000120321043d440e0030700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 109557374 1250 109556124 109556129
    0x2030d110a0210020c0a0f14010f0506100c020f0d12140316050c10061706060d08041e1d0105120d02210705101e141611060106050919 59
    0x500900c4030101043c3c03010b0085d0440c04954915003d00e010030b40129502c49180310b903482c000c828842141d4017901141e07086440d0200c3d0455505d0514080000719079911251503000755040c01e200c44c070202035100240b846803640c80c605600c90007140422080c040340c002e0807080010103403104a401c2801200009035804211114003a141c00c80c4144407543c0d02c070714003a008045d0356500726049400300c510b100c0252035158200f007003080320540e114840900200007194002170183c6102540d1121034480c1a128451130051441c130f918030420001c0f0403162043d101c0014900307a0f40b25044000740c1c0703240803180700c4203219061007140e409040005100002c1540d0342d0070302d080d80050a16600117032604103d00d41c44079034201d06580510112011075003d2010000a903075041380001e030150910985905060300d084440340080c9030442c120040c8000b4590345800030705101c4070424000c4105402c076049038400c007180c5100d0142c0030000507901e42100180030980402c6402090444001000701c64210349031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 109558624 1250 109557374 109557377
    0xd09140a05030f0a030212190b09010b03040611120c030105011d031506040b04020f041e08030f090d02030f0105010509060301020c07090b06090607030e041104140103050a0b04060602030d110a 84
    0x412294003c107040ca001000016020305015041608401160484034400c0f00d1080454140c2c4c00c540c000600c05102d102072a00003152081459418619240b00602000340010b000300c0c0ea402d100c1c6482004501500c1025903c459200941c2c540f0901913400c0b60000c1c4a8203001c04c1807804010307200103e0440200c452003015004140420680340d4001210402420b400c2e041a9108009090342c3c6643c0002d1142100da00c40c2540d07100e01c5c00ca41d6200341d03000395140445106e40c161080c80b6820001c0b00711404101071007500760301ca4640c6c000141e00c86040a000a50510072601c1c3d045503050190452412508212038001036960b901043c1400d038828044401500d8000f294140b18040040d03000c0c103030620003d450b10b410010850040b8850754000007013540801c080d0780802219240c00e0152901440c2d21003030242c00c05150a1320b0140c2c40c000d01640358141516000010040101c035405900b40840c000d00c180552582c402c006902c903407000f800307140d4803401c0407040200c1c8804039080703d8252000e0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 109559874 1250 109558624 109558627
    0x1807020606040b01180f030c0b04080703080706021204060c121505121608061501030213151101020412050f010b0a0611030403080414030c0103050609060d1103030d09140a0503 77
    0x88500300b00c0102444126103042c4005d269080300325035107860640016019450410800700d0850600c40c03003450140c0d101081e001d40c200004d110403400440d104044a9118480c5074483c1c401d881c2c914060700800c01d0001012a2441c00c11080c8481600b122070200310545451740c40003007003030600080e111800902c000d0402000d4081150b4100140d03100b08003011407058414118411170100d40c65403440d4003d00740c613400a0b09000c2d1084c101c000a031040d6109003000c600e030001c15066405c1c985698450b24001c0e02c61003081c1c2078203030701880344019840b00d8080215617071500c92500854000c641e070420343c1c0900c00c0310012603140da4140718000f0790030740090041414601c1e1607422212282180d5885005001c01d100010018404101410250844c3c44084111284c894189880c1001547c102d904160030301c0309124194440c1c0345141d030450416659a1111001400d1541d1903903541c0c490300d501071100142440704240180e11006000c0e100705038100d08251014401c694603100d000024209800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 109561124 1250 109559874 109559881
    0xc090f051002012301050108010605070f080c0a05070303020d1205010e0a0c0c050a0b1605070c05040c0912080304030e1009121a070909150e181f02070218070206 71
    0x70100ca68100007801c9200104960182c03c003490740d03020b000060841c80004000060050b1340c0c21038240e50161600c0e241c41c500b0510152148404495541c4019002c018005051120b00b402031203200909600b00c01140c00d100da80b480c0085d42c42000460a00000b60911001e00c14980b86024143c1290b034020b142c0c19013a101d50f540304000344001e0100c030080c440411b11060001d03406000400400c3c3c01b0b40140c00705860b010200b400c003401d0740354207401004410003e000000b07815001c1d03941668016580003409042c02041640d003909240c000a200050b0a100a0100038060009500c154420baa4440c1009500d03000d1040091040f004100401c401d81d009010003084640568052400b40a81c0e244800f5000c00c41c492501d41a660701c0002401128140101d500b0b80c051911404a8041401007079403502c01100b0002e2406040c0c1e0320820802e0803c0d400301c420400c00d500c410440504c207804d004040900820096001480480c0204840300c5c8460110002100492242a00e82c002c0c104c5540c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 109562374 1250 109561124 109561129
    0x6010518090601180f06080f0c1e0906040806090f0106030f0f17070503090f03062403071e08010b04140c0310080f101404081204050f06040809040c090f05 68
    0x340c00030480c038100640501d9400f4034603013086840c030050245100413511203085c000010100e242c01000d918a944c0020240490041c0850807600940300060f121301e2080c01c0d007901030b0820700c5940d034031340d6000401181c0800e1799180072035142e0142b01e00d0b0003241c40c140c0c1c07980800c50a03183c9a21001e813201e10030042000c0468002810003a085201c0d10031400c01d0b40040d0751000076a080000306440c00d5001040000c8075003080f10540440c928121b005040700d00d40341d90384491000c0c80c007404800781c015903880504603880400801c0090720401100001d201555000000d01e40028030400c0400c0d820000300341041c1c00e1601c10b41d51009101c80410075540d807240c0514000ba0b0014140c000201001d180000300d5050a10014030b881321204080d00c41c1c181c06240c442d041c2c5000031f26016003908000e007400006010b0408071801500c0c0107101c040180d4807420468286800e0b922274071040e010388400c0100f0440000c009000d01c1c10103d80070032041c420145e04513038045442c058400310a070460300900c104c0c0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 109563624 1250 109562374 109562389
    0x91502070e07030f022106011403010b0a05070203070303030b090718051c02030105090601051e0612190603030c12020d0c061a06040311040605060a02101d0d020a0b06010518 76
    0xb0908010034003c4040c1d00340000c9074000920300540841102050072004004074840350480800d1800000c141601e4050721041d00c0184030348a1003e41c000341c00d03e0700b24040c03425150307070355001002d6890095907030602401070450640b0f01d600c6017014000150032140100c400c840040c00440c2240603890030074003800501c40b22108100d407004c068044150050343c090003410311440340800603000651418061100300110f8800c1d031420414040020240c075142c000c00e45280802c50391001203251540301c1d01400c030311400e49165140c1c1c2d042010200515030004009140d1034490b07041142410f004810882c0c80303200c0c3c103107500c0c000340101c145080420300580025040000700c003c002840b100040c0040c400381e220b81c1c021548201c3c14000d0034000c1c0382c0780c400d4a004000544200c0e161101c414802500c58440d00790003110147e8940818103000510b440360700c104d424000890b0604014288065900c008500c011118100c1c11070000d0340c15441541500c02401d103003414014900f40d10700810649 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 109564874 1250 109563624 109563631
    0x5091308031501030501050303040b07060908040b04030804050910050315040510020d0b040e010219050f090409050a02030723060c2b031107030509040902130509010b01091502070e 79
    0x450541500000110308000000d6009421000c0b1510300c207548040050180c0d08164401803283e0400d1000300581300f07a070422070b11001d42c001c01c000345401c890b281940300341c011900000c1c084140490007104002c807a60040041d140d00700c0d04040d81365601540f0030803901d803c1c081c85404da0031522190880c014155481c1f0340092152040d40c2c011441418100221780241c4035001045445034820002d03400e1074070401c6400314a841c020741c0380880004103028002d189005c0784080080000300c1c1c8030302c1c05c4400d086e90340c00b1030003d00900c528045401c0c80c41d40d400700203c040e4424060206d00107014840c0b14000350b400c54841e508401d10307c8902080004a41200802407068080e1080c00b8804040340503203030300080e030b104110f89403411032814020122010042e078041c0a08040003a03102282d0080d046d19070a000413100451203145a1022941c1d08940c01036401d40325040c0824080010019003007960f0b440400c0c0d883d80380b141d50b6084940c0d0751004c3c4445c050007580040ea000e100f201d140001181d40f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 109566124 1250 109564874 109564891
    0xf01051c0203072001020307020d050703020a20040f29040207020a0609081203010b030103061e050703230606030601051b0d02030a030e010b33031806010b030705040509 74
    0x490302840c000240580e031040303400400041c07a40c00c0d0b4105106218402680350001c2100031802d506c0c141c40042e503190281d160074414440045400c004151082003110250750340110b106402c040d028030424600208506400c0c42a4107000380c440704e10030170b441612400c3c8941445800802546050a40c0010186da107564019800300011809a00e440d5035450040c0705071350341c5e16451450882c0c0e450800c1d84405000c03030301c3d0000300010005a2294002d0381d0640c0d070480d600140342e00c6144e0440580324400ca02d4100c1c4142404d003007005064041e8007544084040b40c0d01403901d06000c14001c003c91800b04d64480d480b0a060003c07a4203548550058841d420000070300100340622078049038a80295090a40c00581c00003a280c01e80b02d625000b281820300454000380b001034140360020b03204c03140001c007004044800309007410302c0030403190761018900c4100f040180c0c1d03801e024580c50161101504140050b12500d0000920803044a0850344030b07914070342d00c03142458100030030080c0d1490302a10070301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 109567374 1250 109566124 109566157
    0x10305130c0e040b0c0a0905060307030609150303090807050901030b06030c032a01030b06091203090d060f050f010b120a0603150b03070506030c0403110402070606080d0e0d020f0105 80
    0x200040c1e0000021015000014039542c0d00c0c50180ba05607403d040083c070300c80380c020041c4800d40f140c0e0b4020543d2401ea69040790140d07201d54804008400034100c0b9408000c915041c90629004080000b124105170780c0241d45000a0648134011156510759600c103440d04131441c0c1c001040440c219500013504004001c0030b484070b000113500041c0c5080c8105003400025528200c0c061204241c440c43c003810320070b0030308061101000040c0052254098442c0b0140212207180d02d602d070380c1c2002d000704c0b413603e07500420324592040b00b401c1c910020f050700d1043e24101d43c03800000c20340034401404220304031803240003000c0c03512010101ca064414806480c60020988070b5402100040740700440c0c03203004000c1030001400c1c040c410704240c540315280c5e102d203008060030400d1158004020003110300341c0703070805c21082c109608000850001d10450f60f000d40500c0ca0400c000c0780000011480b030100038000d90329100102226420005a070003c80b40003544030024100c00c035115405007001c2d1114000c5280c011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 109568624 1250 109567374 109567411
    0x3060a0308070c0905150f10020a02040615080c030105100c0c050306040b0402041d060705220306090b090105240d021201020d14090705120a05010609140711060105010305 75
    0x541a0b0405034040700c08545001060244080c0c0d44a02540301c040400610f00106c0a072000c2120511f21420083c007810040404500540c002c00020500c0361307010b00100205551010310701c0c0210880d00508000600c1400072404e04024030701541d0507500001d00d8000d034884180030541c0c141ca000e000032101c419881c100050203950070b1001da88100c0c002c098a0185141900c100822540d24050781302d03801540c04030100980e10b0000c0d4440d80302600f03017000303541c4000c00350701420b91380d100054030003e40303054210100400c00240c01c006106449003e00700101e03210000c1090982c0c100f115010352030809040e40c00700580c181500c81000d158007400408007000340d6000724005000ca0756000d18160740010340700118009031b11401d1140c080a4a460500b82001c0c0d580715225005031050b24483e01c0e200d0b900c0000034a091040d040d080e94002d00802ca00c503a18030b5420301400e00d0365101140c9882c00e20010380564051006401c0c0e0249030800b80030f0503070038080194020200644480c24035141950103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 109569874 1250 109568624 109568633
    0x1e0f05060a0911040207050c06030a020c0a0f020405090a050a0206070c080610170a03080103300801081605010203030703050a0b1002030301080d090b0a110313120b0106020607120203060a03 83
    0x1100c1c06070140d5007020400c24401e0a021003240300d0020b256024910400100d4049280071646d2010100100c4081d0b82d25150002c43c0b0010740900713428100c06024160307280342007007040c0d01c0b04200203101342c4084c00503541c4c8100040d02e954104201a02541200040c1001031900600031308000b07226800c4894001e44400b0583c4c6413000480c0d820365403058140c0c05012200f02261203980c280f211740d004028200080d0340003005030a0621000700414080200c45288203034000780100d460002d003041c1c42d40031401c540d005004041c01c3c0710300c0a0b14001c94456030740b8400d4144011060b5201a001149181c8030f4200850080038000c00c0d610b103556903640c100301d50ba51450290b91440d020390340251740303d505240c01c0c00e0038003884643c01d00601401c04400c000c0e02c5100000c0d158a10b04c28140380c12140d220f11889410362055484000c0c1e6405000760100e00504906000c2080c103002e14503502c442d83e00d80d80c060341d5411064400c040490700200c1c50b11a1044035030020740d40600081c2410800c3d40d81d0760350b07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 109571124 1250 109569874 109569883
    0x5040308061f1b0f02040203040812010801060b1917090a030e03010501050102070e07020705061201030506060103050c040909050703080406020606090a09020108060f04231801091e0f05 81
    0x504400181010050020360b160100d04040c400001a200c0180801d1101c0003410581800903c41e4150036905141d405001c507001400c03c00b1a00034000b03542d03034a842e1500e03000c1580322441c00f801042c880c1e80080340315601440f81500303442107040c074140303802c42d08000c0107480788000101804120003405103e8103014003500441c004e40310319004004403035944c40d02904095120594a000340c3c900401008242c1e8009040d8044500b03c80c4054496100c03c04200d080410715085070342c204a000480d040c0b42002c1004003812280100151001c54480000440070381d1000e50390301c01b000c0e100780070078000c202c2e640d8002c003903662082e821542c8440ea0b998909810750465844032026810000420a1900307044402c81e521982d00b4a0400070918903600103030030392601405440c014449005500e100d52034591007007202032848440d580100303055603040030742050122406080000415450040d03210f0500482d54106d62240307046010082c0c250160600d281e01c414140c0c0e024036027149070008190b0610 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 109572374 1250 109571124 109571131
    0x103030c063306140a030c05040b0a020a030e04020313080903030c01090606031a1b0306060904090605100609050d02040e0a02091618180507030209040626070303080103170d05 77
    0x100c0c05205a007982c0b4850508500300d030720010a0086107850201400002412503101d0403042c200003800c02110b0400301e80034069500582d4905d600040c1e181c455680000b00403083c9442a680c0103110f25240091005a02041c3d0700040880b040c05051800211604007402000074003404890a10200030b542c1c50a4811055040c3c0300b15541e04030600a01c10003c00909450707020000e041814101051112000c0410207000d20710014003101203201952980126608248010300034031604015050a0300140300c240e42c2c09902c2c4180c00000101c0038043c90f0590102c0380c0042542d1940350440d000d10024000a40d40c0101c680520308c0c0402c01039541d0150030f405290605603001482144c240007400b085015100d8050218a40c1402c1052903844d100010320a80c04610100b899122440250064020340641a2744541010750100d002c01c4071a44003a02800020000259801012005901d500c032500001e4000b4411030014000300b0310314080e2030102b41c5d002c080c5e20310b44000914180100c420a5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 109573624 1250 109572374 109572431
    0xf03010e0a03200c0105031303090302060705061005010f020d1202130806010320090601030e0c1e0a0b040302030a030f05071217090705011d0103021902010b031e060103030c06 77
    0x1888600c0c2404042008071000040e000c0200710f0300858000180c01b6020090440341000da0411071070080520955061000b55405003100707498060501d8080d403129000c607251200341500c10070003d00d561207140444602c1c1402d03000b801094800b00d0302141c18190300380411141c207808100380c66810050110420003011020041c0040b5419460b06003100c10109800d07542d0154802020f12296603084080c582102003403c0004224903400321a909280e090a40f5540c0010456440c00c12a0008000801c003200110388400c1e8050319415091810b02481c00046d4056000500c5640000d01611a140d891032490a025003011035903075480d200d1103c0000504e0001d1140d1000c1e582c03c110091850743c000c200e1101801c0f901c0e00f0f14000a0080c001c00c03030521180404245107800c2640603074100e0b40a00c46441c644410501c0319003019001c1e04001c10514000c2c800c0c100c07a8000e45400c49925014190050f0141005910f561011110ba10f04481c060310400d0340d520003001e00240c0400410683c6404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 109574874 1250 109573624 109573637
    0x1505120f03040902070201080903030f180f06040c06030c08010b0409051b0a020304060f050712050a0c0503030f091603050c0103020d0f02030a0b0a05061e0d02070c0b04080615030c0f03010e0a03 85
    0x102d1000401c080e03000750800f49e03154424000e004811408080c0c8651003201c40c0c003800a55503000c4042890b002c0f6282d04000e00f030141206000a0028510309001660026241808032070300b1000c00325000c550921030a180d07200203000610518449400164002c0a800c21401151150500e84822a171000c2440d0000d640009410800c190300508011111451401d1480c180852526007400c1c4030400180103040100015084101c04c2c0207600c00d440c580e8000381280d03207a00c0c02d0883d1010350403044c0c0d0407031520b100d0582032554002c05c02c44210103682d80308020f4103101d020500150042d411101d91550381c0c039115080105506950310107180300d8032110101281440103001448a80402500701d030340940001c000794070281496000ca412001c80600f00995900e6650712010001d006080340100090441c4400081403000c060184c0261451034040c2c4000c0e8441702e441ca1500e102c1c820a05802d07400081c02001145007040e05032144c40e0024001013040c44403c822a4102204920114089400c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 109576124 1250 109574874 109574887
    0x901050a05060406120f020a2c01080606100e01050403020607030e09010801020a0f0c141203010303030f0207020a060e13181b0609180f0609020a02101505120f03040902 74
    0xc98064180c10880c151010000c46040c40505031810001107005400400564103e104540310340e042d1400904c1e05130702d40e20390040e20b54600201c444034048007008200c184030012542c0344000c6030460160070010000c01d80d14040c02400ea919072a03000889041c880180300010140c2c981000600d0a14420b41d2101000900d80c010094194010703000418960300c1402211102c64002c8034001568020342802402100d2134036201c5d600110102d8140390500030348501c3d0ba02c448585016505072480780d1030601900c051921201e0132802030000203980048070750030800ca110b01030100002c100070060900d1001015503140d100a40340951801100304982484000a0100480440c201d044464540c21070140c989000104044440d0090b80c0d84d40400da01c6544165100c0d170702c40413050304c04441c103021195030340c51504025000400c2d40009401810711040030b040b10380c4940d1078001e0081c185640c01c50708220910003400101440c1a803030788281c00f0142011503003003001e00010310903607802513603410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 109577374 1250 109576124 109576141
    0x10c05030a0510061d03010615050304020a09020906040b07021c0b1009050114090c0408120406080c0915030702010e1c031b02070302040f0605090a0608010c020f0307110f0306090105 80
    0x48000b003158541a2605030284140e45d4410b01c00e0154034000002801c9000304400000c0c0104a140d01c5944130707540c0640e98801d90341d0808082e42c032940c000c07139400510f55a01e480501c103a114034902c1c00e5001c9010001070100c1e070740f00380280914500140241702c560800d004000501109000161054016402048500c050506240025241c2090144420b5140031410120100c0c08000188281080b50005000d001340d002038400410340c0c003040740c840c0c1c2109181d504c00b41d8031a01880340050003c0e00081c40b4002c00741f08a0305d0402016085804c090740c03030800d1520580018003142c2c119500c400070000315400402641810300d000c0b007003000710100040030180895685c000b09110b2481c80d9590114100e4010404504903601a100403507161103055020008003d181c2049070b000140006100d401e1855610a00c2503036141802000b190300c00030010390f174500c0e80d580b16000b1503008000306000120001c09074040340d007000c0e06a011072190040000d0921004940504041c0c0d0365004102445 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 109578624 1250 109577374 109577381
    0xa0209220605040213090e0a02130b0907090b03040b151002070918031d040f06080a030905010212040317040e0106210504152016171201050d14010c05030a 68
    0x800b4200d5045180500e051440514602e03c1d02c511600240d440e200b414405005020500700c00d5030003480440d000b015200003030010448680350070b001d03205180014030313142e01425441c1c0680360b4410072682903943d16a104000400000d002d05034031052001400b210b52100c00300e400d18240d96401400406003084843c50490b20301d142c502e030040400e00300b072601080e00148c00f0307180c41090f01d030340410b03a6602002040241400c04501d00e107582c42e003240000c0417007001c19500f40da1442503441000a590320801240c0e03031284546203400c6041c08010030000a2110062400565904222103082c10340e2840c0c010980a8244e0114010a00080c17001d40780505a00d01e52902c61a0143d040000c1c1c1070a4581802242c281c0e14140869603440400310f245055035080c4550500304407254560b0303158030005078100d0585090307041741c0c0c4850342c0f1050340018203440207a85203c08002d4484006038608010080e85402025044d01c0500b00380903c106c0d4880c082c0641612075001c1c0d11071650700c3c248403144c030003103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 109579874 1250 109578624 109578629
    0xb01020c0634110d0f020d0605040515010803030a020c210403020a08030a090b070303020c0d0e0a0614070201050a0512070302070b0c070f03180e09010e010c02060106090e0a02092206 80
    0x44010551018005100d40890f072414101c140c452860410b86464002e40d0900382c000080d62003d00032851400f0400107402c02d0f44038600c113100303440400c000040034400c02182800780100641092000074404201a130140c801c0e10909011206003c51415910034820086820005202c46c0050144154140f09204d070f8000e000103402986403141c4940014102c40d100d011318242080e0003c1c1e0541450b01c02d8043d00c200d29034417004c0c4e924403020480041d03c40d000c800c0d500d60084007070840004032540501010350052125090f4285407100e55401114517070310502201090010a0045802024030320912500c5416261401a81c6480d2800e001c82010801031441000038020081007001810103000c2c481c1361545030401d01081084248005070044440d04400c80700000202000843c19054200e01e44c80705108000300241403a107a4100c0c0c4624007405000081041203c04104542c040c403140d543c81079580c038006040403141e1000407903441503404c14961240700c4140c41f50811741c0c0e51041000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 109581124 1250 109579874 109579957
    0xf0f050612011e03060f0e060a060602060c0a140a0e0a05060405061c020c01022709060a0b0f0f16050609010c1d0f120601030308060a03030507060b01020c06 69
    0x2001a03101c18000070001c140229080c0e191407009002d0881c1c030400d10000074583c407074014000d810b0790b03001000090041402216040c4100c030081160040c1310311480d4141c83c3d41b0b501408041e9690240030100d03174000360001d4100328520840c0340761a01c0e0080541000542503440100c0005400104529a10242c2141d80316180c104420401c955070682250010306800710703a41164003211081600901402c101d0f0000f40d4000603200b000d083d0320307031210031603c0c0382c00306840d001c9100b040c04d01500303100c2210302c6500448601418480b01491902620145a81d0385100d490140c14040d503e031950810340010b00c850f24108801800c1080a00810354006103042c020041010300c40c20003000103c549200d10781001c42000386851030340350070100c411201c1000c7d14200d4a000801380c1d180c0d445d5024401640000c0c441d00100e0b192f464174440e0034040766099030f0340604007800c42e00c0d4040203002c0490900e040d4031880500c000c4644440019004010240c1c20000b020107031005108410301503003d4018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 109582374 1250 109581124 109581127
    0x80c03030f1005011805010807030902100c02090f0609180304030204090b040303050f09120c160e0f09060705070204180c0e011703090d1b0308030103050d09120f0b06010e09010f0f0506 81
    0x141071124005c0f80448200b40391840e600d8598550030b500400318224081d4014100481044103160044903410b9030324400d80304d2407001d0340d50100415010809464042d84641020003241c40001c0315400c0b503c100c12100166851310b130b900da00050484080c00c0b0100c841d0a008000c000a00d82c051003140d42c4107500c840055400d191090f079080c0c444507132214900c6c00000100d40a41803031000c02c1100f0080e0301d0002882c1400c1d4956010b440f60181c00c0352a100c040342c103080010101c0502182d054080d0b003440d150203092001c182d0800010304510310407460f00710602d25070300c00480c90020b6440014902c003600070026506098803281201190204a00240d00c1080707401301545604401c1d4030100c0d0480c1003121372400001541c89006020f6001520340302011001205014010501e00d407511501d071100040141d4588030205549405032024001c1f40c900c00300840440e1100e0b0f61103900c48014900007074800c2c0000000381000300d080e01b20349403060040c42d080c0840401c000024003d04012103195 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 109583624 1250 109582374 109582397
    0x15090c230a06050a030608030d020d0b0a0b040e060d0204050f1909020a031415011401020c0a060c140708250501050c07090c020c04180303110301120b04080c03030f100501 75
    0x28060000030b01c6000100f00b00041d42c0081140710742d01c0740c4040e05405084d20355030000440c0c150065041400c0c00740c0070518000c00000b80b4a001c0035a034044541c15510b8a05291800b114642401d000410b5560448a00410032005944074441c03580b0800b91014214224180591202040700710344059034401880c1004210160751500b04000489030b025079901d003110400304805007041000b00315204440701000000c101c80707800c1d440351034000b002a82200c140c601501c040140003c114414480488c0b40707400808041000b8501c41c03140514400c00720b40e000e45c1e9034076146240c98007204d0303075a0440b011010b0744d00e55000340140050051500346003036070030041c40c6056141c4800c401c0c810620103a1381d511032445054001e105252140100a00c100100c0080340e140f000c0000030182e044000034501206090860203400c140c90580c1c0f90319140f5070f000e50140c0c0c0c4480c00c0d480007501c266a640c00c1800031041682c030400c0114401d24600d00f105401d810701380c00d25290081c0c140c01c170506008058105 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 109584874 1250 109583624 109583629
    0x9050a1e0c0c0206130306050103080309100506060d090611040f050406080715050307090302060304030c14011e020901120504050d1407080a0c1e051b12120715090c23 73
    0x142d040c2e02d901114540e9441c03c00f003051402244040d07200030440ea0601c2e0001040c4204240910f200d5030b0803109070703013000401c41c001d0782c01c0351b204031313400784e401030007400155100c1880360f120101280c0304081c00548107400358002001d0b42c03c250300501c44500c0040090180f070405020303071030050900f5001850386074140200e600b410807099a4480400501000003107900740300391202401142c0180105a403401c107410002c09001c01024241ca003442030841801086005100f40700481500c0c030342003d01903140001390030195012203810b034104080001c40015500c528850180128403540041031140d00b42c14014141e164040700d02c9074102d0381840201c0224071300c042141d50b044824075103210144100d2811a088175042040c41d51010076444080c401c111000841105840c0342181501c80342c0403507000c1001c1d00413a050751025035004a800301c0d8101c9406006010070a11814040c11010100b203101000c64019120540d568040280c041000d4080010980001c80040108412410000c0d02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 109586124 1250 109584874 109584887
    0x4150806030a0305031b041211030a0c03150b040518120a140a09170a050c0d03023c010911090112030822031d0102150a05090709050a1e0c 61
    0x41d050050010006e8084000556441c0b0ba280f400c0c0e10707003a12141c4900c10400000c1d0b80000880b0781c11070806001e001480c00041141007542d200f0342c2d00307019900b1a0740d0368090700c4100f0001c1910b0742d1039001e2181144c0d541c0c042c591242e581072817210080709a14458070319000d5159800118048108901003003103500c002401c50542c104c501180d982c0b814000210380d001100e5200000044030141192020003010508841c80e0740110126002004400c04028014070310079801409a405039580d4001c401001404c3d031080403024010501034800340280c02c0c0d15a14411041405075902da1030507041155000c8039015140041d2010724041d07040070000c002d01403034088094103100c00361000505200700351000e40000d01501006000040c0c852a0103030558000e00701d41c0a02c0146a00c00544030752000980031113984c41c0e4408100b0f19102c2c036156500400b4050260702d401d001d00301c2e001c20408100d01600c2e0141c072103c032000440b5290f03035800381490401c3d1110440071600b4115480c1c2e002c5e6001d03d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 109587374 1250 109586124 109586143
    0x20408030d0e0c04141006140a18170a0506010e01050f01031a120c0901080109020f090c160c0e09070e01090c05090d11100507050d0c060e120415080603 67
    0x380009a40140b440c0d020749040c8038030324075036480741c02c0c000841e0803103083c1c07140140200e1a9000325000d0703a885807401c0d01d000081d04040d2840d8401440801c08a503c030302104512410248105a5016210b1307070004007105071100e11420f254854514103040010400004c0d00400c180d4005100e19418140003403e1412001c81081c105911000304501242c0e41d078000e03898910000f0891404c50704011422511445100d0b80103100b0380e102000024600010f01402c802c85d41d00a10b0441d80c40b50450030802d4403480a400003d80c1d4509015070042030a00402c107240c03450042e08101f808a290100050100400030202c80d000d40020104120b448401b9070543d05480340c0000201d10010145000c650384d00035000d2041e031104400d50804244001040f50365800c540558480d00c40c07101e440401e640c10312509000600e19403207100346910f2a4401d0556a0103070b4442e07040401c1807111442c0707103803404c2109800700c00c520500113070401c40340c200d00d41c0d80c3e00f1403c41414074540918012000940301c40c1e810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 109588624 1250 109587374 109587397
    0x5031207020313081f090f0605070c050d03050a050c070209070503090a06091203110f1801110307060c110a03091a0403050a0c031a0f1603060512030c1002040803 71
    0x640100340d90500034816030ba1469414441c81104a560f1204c95640e4007200c0e4451518081c000d8140f00003280900810b4016600301c601c482800c8560348d1444000c00004040108100034010f0a4001600034880b04480094681e0045500d0600f001c1d8102100c002800b6601500070810001c001a110a1106688503400e414002d841c1e960f42d0500d203041c01e1440c1401010f2501e8000200100510304850030a000d20310f40e004c2180d109404808031a034030a081100c406054213014601001c8070541014074454011314ac0600c5244484d0a07040c40d40d0070001e02207820ba80c60703001000c5490707448800403500c04400c3d030040070100003907200a030005407a8025182c1807400d0080d84001400c031103044030004c65002c01254209140c82c01c00031140c6110b404121914250f03d50001000080c154913903004d06802a81d0703265035102c0140300e00040800b01e07441c0043c1621403800003490f40d188440c550f5a444008081c544c1c8001e940e03c2c0e0340c108011650303190304091040c842804030260000648110308041c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 109589874 1250 109588624 109588657
    0x14040f0f060e16090b0405010807140102010216060905010506010e0f090c1204120e030327010e1905011e020a0b07170a0204032303030c070c030b1608130503 69
    0x3242408000740c1810854100b151141c001d400b100308107403801600444003021010850350449400b04030507a882132240460540c0200414440d59035500000200107505000051401d070030000c845210010b00c1b131082d14200c0c0e50f480020240102800f45980c001000d01c0d02a0180c110500065001c3d004001502c3c09400c05000142d000c6030088120780141c200412201901e2509180c8412907a20b080145c1000031155440041c3e103040001c2516a0048040e900031102050364540000b0f002010841c0e60412140b124007180944a116a0806c25064000e40c43c241e5401c00c000503001001034444502126038000d505440c86078045090040198890800c204a4542850444903c1c00700d203290140420036005002d0202517950081048900c03444400c01100f05e100c035600c111500181601549400410008841d10160001001e100344078120102c1481d8490f141e051a40340110b915015007106103440d545030a8120b503800f90f00443d00c408442545c0380c1965050785030301030314900f0030030089c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 109591124 1250 109589874 109589903
    0x5010501080c0c0304050306100302011d03100b0d2a050f0306040618080d05011d0f0a151205030a110313050d021f0207030b011d0412020102040f030f02030114040f 72
    0x3c0c2402202e0080000070111762042c1400c07078080d04203800611040b400b06003038034900078100e00724841e00d400700c41008004d00040310220b403880001c0c1c0034868805a10000c0070f0384120000d0744004405d224000d16020262010188070402891110617800030741c03040c41904100e025582e4000350a69005600800c0810f0150154130141020455610010041c09004c1450008002c140d070007141224441540c00081541113100d008004c28160340c03000381c0304140800540b0014003508004090148403d0b8000030030b0742c44054020f0310507203103400c4070250000607100b000d4661042c24440710300542c00141d0300d01030341c1c5515061007085501c1000e00030100800c0380d100f9955406000300104080780210315071080d0b41301c0c009440e000cbc5070000701c80340d9000c10004507106100d4482d03000300c0b1607802c3d107251032178895498400180000500701c81c01c640d0200f00128001c03c1c141d002c2e0009520880712104d04849503c100740c2941e10210140d54400366000401010074010804401e401e07421103840e200459 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 109592374 1250 109591124 109591147
    0x70f0207050f13140a0203090c010c05030d151a121e010909060f0204090920030a0f0206130602030d0e03070308010608060a03020a1211030703020303030f0a0b030703060c0f0305010501080c 83
    0x4400c04c00c1101400c3d10020000c1540310358008610991548064542188403280159425100d0306c0024010b58010310a004c3e5983c1654031142c000c907035149103503000c942c3e03507014652001c100e4180380c14040d8003c14a42e10b0b00e00d006560580019208411080c5804010200000e2840520895160740d44840b064024050103510020168010010965440b42c4400080014100c0d1100452300c4aa107003103248114080016002c0380e545008010340224035060b2200100c5280f030b90f6040c2d910a008000081e048034100c08040010070080e006540c0f202c070902d00b6001290240254104150402c00c1b90030002548079118606403462070614613520344840d40401d600c091307240c10007904030200d100003061050080c8003000140d449100c0c10100440a002816154801840000d40540c42400815400081100c00581c040c007160710003e241d9500000180c948011544180c80140c0e030b8000c21802d50754460b07640e12003a882070809003c95450000001d289500003014086490720101c0c4499101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 109593624 1250 109592374 109592381
    0x150803042706260c040b0306240612091515060a0e0301060b030a1104080a030516060c0503040b0a0b0a05010e060408160f06090b0d020304030c0f0605070f0207050f13 73
    0x600d51500902c142c0b0350700c0c0c0b1000000301199140c03c4050300c104800d08269252078010a88116009006004161510003103240103024074100030b2640c14004d40c000140d500c40030041c0120118003050142c450808a00550418021041c210101c1d208081000803400058107120780e512410f8940960b0380d1070480084402550705003030641d055080c507a0008803201c0c910080d50003441040700c1041880f043c105a00f5051081d88242110394000c40076001c0443d028030017030075945450007411000519142e40700403c6401c03100c1c256021403004800e0100348046421603551001c80d2400801007130300204e00140f4081003920400341008442d9024140a03103a4005580060140c0f03400c5a02139400c00c480b08444003040c0c041c0c1c000141009600080300751040c0c0708a011200310b454600c0c070308185003a0000280d40010300640520a0449140002072344a00040c87c3c021f006d100005114217013610003d1486100344440000c40d404800140300c141d54800b5041064042140c450900989403843c00010307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 109594874 1250 109593624 109593629
    0x60f030d030606030b030d02071a1201080303190501050102210c0f0a12080103020a0611031908040302060f060f040905010b1512060603040b01120203010608060901150803042706 78
    0x140a00000303004240e4058100b501541e6168505004040d103040506a030b4201400e020380c010703444000c0410003840e45141d54404100c1000f4803074a09003408060b9203d040c805c0e8081c8165a000104000034801c13016a8a000c000c56054103000b25458400000c4d940e0340071001640030300110110010303030303020140201c409a002d20021740c1c50707002d406120300f034491014020070344020401982c008000c61040b404541a00d500802c22050760f801c04800b01d0b50084040e07540a403c1c4030800810344241680514041070220580e2401c00030b180514000341040c5003c1c06029018014009100899070390440140103d807080d503001642c00384500b00140980180c654854000c444541000e8080c4c00c410700412481c104e9205d82030498480c00d062004510049034042d11122100e0018000c0107215503920900d03600060000c0340841e2074621850900c0426110001c0301e030364440c14928a00304043c61100144003202c06542010f240400c8044944120800066680c103150b012016a0342c141d4041c070007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 109596124 1250 109594874 109594879
    0x1020c04061205060c04030503031b25062003010b090a030b010b0703080114010e01030905030c060a05061507020303030a0b0a030506070810140d0b091e03091026060f 73
    0x1500d65800384106181d0302c40d01c099400d8050f000c0014900a59001102c00322540000210b1842d52001c0a00e41071160741d4560002200b410004400c904907004801c01704151703084502c5440d49040c0c545a003c4904d4140c0d00e04000990560702d550242c0c807101501d044a100c8504075a03903400030000100c09030800c0c0c00080150101d140042601445940600060b47c841c8d10380c0c414070707604d034100500c0081c4218041400644100130200095119410909a030f0b44160102c905042101c00703103600340202250400c6586954008118140c038052001c10851442250700a01c0c1843c02c1c4c01080d10380c4001400308040301c2e00c07260b20340966201c900d80c010055404c1000d862442c00c019074010011807055941d00c9510010000106011062183c6078440d000000c1441740c82507682d940f01100e5490080102c02180280309850070710081c2900741c0d051000c052405186d442e214031042045890f041d00d100130412140c080702e9a0060280308040d10505603005080480d9507601c07000540801010403200c0c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 109597374 1250 109596124 109596131
    0xf1f18080f09040501150809070e011517130c1e0902070f08070303140105121009051903110607020303010e0406020c030f07110312210a02040803040609080c090417030601020c04 78
    0x94070f900d20380305c204128000e5515040547c50305880542e44040c940100011a030a02b0010840c80280311380381141c02c005030030301c9003140d10340c0604241c107024202c0302c142a80b494070419100704441148080040c1518002920b0350305056030081c40603240e03c1c0110460643c1c0060024180204da9000c410225801007403507070b852001d440e000f070160141030141144100c484002080c03e00d00220004000300601000381000317030700041c0540c040d190588054506010f101c0814624840702c03040710b0700c039034001c0c0c660800c808c0d0800100c0c0e1506000401c201e085400520041c000d8840c0340382c01907001600480013585a00d01100711700e007184103003003440b00d000c4800079880f0200b00240e000c419401104409444120700c444465899034411039a44514a00000c840d8881502041020799082610381100604061b101d984d241e145502070b4001201090088004010519040203000450002550b0514023401c20b40c0d06c4503156601441071010f0024040b0000304241d20801191450980050051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 109598624 1250 109597374 109597379
    0x6060e1c02091306060f0302012c10020d140408030a051803150603060a090b160212070f0b010807030503190c021305010f0801021c0c050c0f1f18080f09040501 70
    0x920b00e0b0b800082040728038a003084800a41b041940000300c0c1100c0e0107848040c030040b800e490031024414880c0c0103102c6490989410101ea413901c1c0e000c1c40c42107400d900144a882a140000360062101c808031404000007000140203407140882901d00d1f0310f4250918544070f00811060350320014aa18800d40c05205e0a914405449071855a05005950503001e40d20103440f000454002e5580c000800344c11040c070100030924022560314443c41e8000d891056a401c60420800085030341c0c01058241c903d4089610004280848800c8480c01032032140300601c4424a1541c54980303134019499400c40c103109100020304490b000759072032404140d00600300802c400b4a142142c0041a080c010b10394000c2604802190300e0005100b2164804042e0298144200c0d01c0d41d010300152295540710800c00c40b003407010320040c42c0108034810b0b4025668001d007110305800041d080034915032440d065580c40c1485045460032117540400300d1203941002107569542c0815805021511440d1111508140707400c000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 109599874 1250 109598624 109598641
    0xc1005070201141536100824100801050117010c0c0c030303050c1204050f12070201050301090b1f030e1605180a060b070804030506070908060f0406140a0b011206060e1c0209 76
    0x780e0321900c81d441c450041144c854240c581d523400360300c3c0d6104203121405d003c01c8034240e07003501c03540e484030b03450041c2c100084d124a04142558000c0c0d00c80440f01c2200d60048190440c2801038a45143c01407812400055460300d0f80303861400d0903c8043d06140e62040442d01074117480381144c0810001c0c0045260b01d0406140c103507070300c01e03602a4081c01ca0280c440345141918241040315440f030b030141d44060a590809a1160042c40d06400c0c0726803103030411410601c0c8a16621610321804260f4600050b00c0311941621410800c0f200501405c44411002c184400e0b507500d414a0000901581501c84503038584403400020041504076230b0581f100070450100304000301c8024000d8921800075113010341c860740c07070903600070999000d0040036802c00c82c0040c0d6a010f09800e2241d2040c003a40300401e010845c0d0183d0b005000041d01d2940d03a05803551441c11103560024100304450000030000c00907140f80100040203a044201c00380c1c4218603190304014048101240c0c001d2035030b001410100b003401c05090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 109601124 1250 109599874 109599979
    0x9060613060803090402182706010305160e01031d0a051b06071205040b120609070c03020c190905070801050102190201020709020f0c10050702011415 66
    0x64962040121090880d08080e0a0040100312a0003000450402000004000107034006c8000e08085901e50602e01255944890794540c074440e1548102d01070010440194038030a4004141c1410f0506144c01c0c403500b18034070342c0003420810451400d8040c038141000101c000e8200c0000a500c0e8031314100e400f0040e503201083c842110b41c810710464560360002d850b2440c07000008000564800c5041c0710003c082a20030000d017584001524005180c6510b803505281c6a802001210491103080801c00c4503034144107460642080450401d40c400a9655600940e92489400c1e4075020b040800540c0c0070f16102208801c0107060151820311951812002c010b0001009118a81c018400c055560142071906140080ca4a4060380070f011018245010303d406988042d4200040325420042c40b00d601c02c05009400c078160000b40042180d0034130500c028255082d022425100074038141c140800c02c44496440b40903d02c00340c68004102c80e80e024200d02d0101c0b14021900d0912220042c1c1180c4010f11a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 109602374 1250 109601124 109601131
    0x1080c1c0e070e06090c0705070e01140f0108040209061507060509060405010c090305031210030f0506090c010504080a0b0a020c0604050d12020406050d09050309030304060804140a03020709050c040306050906 91
    0x20440e039400d681c41c0c3c015160701a094444c03e801803202c4021a02086510b0010022540940111030600b580c40442c0c122411090f482803005180c0398600030130358507103042020680e04003403030100507605050700080e184000c054540e0f0303c074080041803190200415000e070340503142c000c02c0c1045107240c0348410507103662045500b01c07225403a040740d002c0114060300c1c034841520340041c01581480e60706141d10556075000b400e81c901d10907015100100140d50b400100d5919842a80034110038289400e255150140c0629005c1c103100c420b000500c285040002e41124668011b16001082e485820002d0001c0c45460280101400b6917006c0009100d27000032502007210380b503540e503140151000c503480d089000b180941030001d441040002101c0c1041c5e0403004000b8000e6050b00d182c0170011002901e036600c2b99121b035003c19112800c210503c110011482d40609692000d46a0405d0039507000b5141c1030240603905030291b40c0c40100390310704100d4083d100910b41c4414100958200082046d83d0b50b00100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 109603624 1250 109602374 109602401
    0x70b1912151d0f161112040306020d1104061d1305040803070e0102010c05030a1a09150111010606090b031306060308042408060d0609060f020415030501060e01080c1c 73
    0x5000f09584003c414109803242a650b8140d45025003145001c58601c030400c1c5000019218003109402000e00c40300040005611070711b00141c0d50b400d50100241541c40e031041554841200b48420041c0b00d4004c0320000301852001c01181416400c440000d840038080540c12007407a00c4d150801c020014034500460090803140c8901c1c8540350105e0049081e540c0c54001000058800c0c03010540802e85600401c0f04580e6002c118808803441d240460618601241d4520843c03040010b550036558020042c104003411890080c001c4034209100640000154071a42902c440000001043c1710826103c114a040e8011028000c59680e42003030b81040d045401040450010082c0500c126000c0b0700300881c1d0307000e85859446403a0382e03040420003074010f500415941d41c1e0b00c98208a000955520580b0301c11500702c0d800603115400d000d00e0708200140190b144003414500b0006004240d08074141e04c0b50b010003441c200d0031980d150818804d4034050b000460511520320749161071502119001540c120002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 109604874 1250 109603624 109603679
    0x61b090e0112020d1e0615170303010302180601050d02070501150e0f0403110115030b01080f0d1407140a0308070809030a050d0b030309030a03020c03070b191215 71
    0x2d03890849491901d10078025440034402d81228001064002c41000c0428580c00d04401e403141d43d00d0718801d0320504c1354100030011151205002d42c85103000d082c0c4a09049400440c215811680401d80781054803965074801e04c1c4940008480f42e02c1201103511742c220b0040c01f903483e0a4607107412070181441440801030300080c900e01148400301c0000c49449020106042546502c458906541c082000845c200031552546a030ba00d8086000d100600150b11840229140750b00d8401d0107814210440c40321031aa030000351030606829446000700c2c180039041c1020565500039450081c0508412003102860b0740219060071341415009a54607100d03105a40b1043c00599480d83e0103503c0c1e1166410070000319400703000c05500c04005030310030481c001001e0116483c201d020400286000380907081140141e001c11b0301c21601d42401d0100d04010403403c04070600745409012840300d0034880c03d40c20420021007a100c04504a8203810980101c03101c0701d100606c1326246c151a001d100d0407110940e038907003103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 109606124 1250 109604874 109604879
    0x501060c050a0f05010605040905031c0c02070608150a03081201090204080709150b07150c05040f0618240e0d0308130c0b1206010f0201050f070c061b090e01 69
    0x8a420450141e80314010700000c074201d40c0e580b0901449901d05903030a40d83c0d07800100c3d094035076124412496010700300464a07461128560501c0b20440e11102c1125820010300c1208150001150026100d450420803141c3d80c50411040041c0c440240f416400444603100009100000c0c0c02091a1100c00903039480a03030300c80340001e050307204500c82c00750550b00c48001002a07606c15440340340f041d070b0254076003889250b49400c00b40e09034022841c01c3e90827021000805800e00c21030b2082d5070b0182c0131410800c0c00c15240401560f46403082e4482c000500c14546803000c1c00080c03410030500903007824040403c5003000700e03000d001c001102e003503480045a00f40500d83c0c2649420030032400141c0c1c0c1036a40c90b60982d500341c14890310300c0d0404d1085890565000c00418910085405000840c40c05914841c8600d8190300060000b0141d64020080d0392502042c0030418a4003040702d035100c1020700f400502c95940349024001080300800d68160b40d440e02a0075404075921802c40d80807500c122015100998 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 109607374 1250 109606124 109606127
    0x403120f0b01031a091501030207051e24040305030702010e0a03020c010f02061005060c0f060109020d0b04050f010e0c12091c051603030f090f0b010f0909021806220609050106 77
    0x301074900c0103511407503100c0007541c0d4005101c1846e41100701850098100107150780c80e1480e00d076140a902d03280111702c4010b100859020800c1d02490312420402c502e031003000c0d80f1344803811000544043c04000b800800140402e00075000b1001c2d00079a10200c0c3c0f414000d030b00b030003500c0d200c0012409000450501114942c0341c800145030740100140c10818815500d4181044041e900c81c0c90f82d14280e000d200b0b0752104021080c40343c03500a2015000250390b0740c402e81641800c0310b01080320144128a000284890380400c21121419900d1308007184401d6200c1c1e180654440c020101c00003108211002003000014020910001d8080300d2080069000f006c9841039860303000301a5002042c6c0c0d0070600840201c1c3c400c0c4c02102c2d41c0000c0000000341c101c2a80c681e0340c9000601c82096800d51a454010048002e001d05203c00400741078800308450b480550008403541c80403c06039400070032010106041ea65a80300c81c4c0707580e040260000a88070f1022112601414a92082c080c40e203140c18000a61603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 109608624 1250 109607374 109607411
    0x6030209091303180603050108010f020c06040b040201140a170a0e1519050a0209030c030609030a030207020301020f0a020a0c0812030601050d15090207060e0d090308030403120f0b0103 81
    0x2908010142401c030ba07500c407040040b40510203020380800c641c900540707401e100c0c00480f0304050702c40e80d540440d25605281c0460300350380e4141880c0450500c100710050400001160b0650807680c450300700c40d01038a0f03500040b9a04080b44068091115000441401d0150844190000400c010348101015521440d048007212096070100c94035800c440501150004905405e03540a880758171051040c0030380160034001c44404a4680780b005a0020f9544442d180800204002040c00c400410062800c07011103601e9002d110b049205040d0003091140c215a001e40689600d680b501440c42d80b942c03119800291b9402000d001620502ca90000100341008046000101c2911030361015165850b014011242640036045001401d0750340c00460700e51860091a19006100d841c4001d46c80e4045030400304100c5481d43d988041c103603c1246440315003504244144100ca40001210340c480d5250304003900c001040c2010390311030510f404001e603100301c111760058006000a90301000805501d00030503500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 109609874 1250 109608624 109608637
    0x81809010e0c03070c08070b0a060305060a050103030909020a0201020d0203040309050111010606140d090209010303050d110c07140a03080d05011a0307021513050a0818010507110103360606060302 86
    0x10b9801000058101c40c05040300039039681c81581c080749080300da42c860000d400d0003900c1c00845142c07030340300401c01d220b804c000383e903049041c0d400d040206500d940d80150080708544501c0c400a50040b828907140c85c004c0d0f040d50101400d08000350355916151030020905040d83c000c0a01007078800d0350f450b01d5140140300b0740c0192405070712039590f46400080c42c484d0031780084400d2590162558551001078840d103880500961080d00c0e0139480e045e04098103c25680b008541c040d5001c0d05003c04520084002036420450b40c002d03e00c981c408031983c000c50346848840c0c0000c1c1c44808000382c5258900e031150f2050f4101e034011030050900e8545c0045c0e20307855110a07208440164840700c480d0301403900c03081d10103400040012003d003468100b40c1d201c9082012448003651251008203608107003080700440001c1210003440c1240c9041002d49d6149080380a00081604150762411a070464581c000540c200d61090b540d451104104468800301250722005005c690303079410b00b600040c0c07490083c000e5918 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 109611124 1250 109609874 109609891
    0x20c06160504030201031d010207060b011b200d14030703090b09090a0b040209031f200a050310120f140705060403021c080a020304060206060a05090c090a03081809010e 74
    0x2a243c51500110054891147e110555501041261031940001d100400316648a81c50105402410500142c0694104110820303441c01540c00e00c000a40045520011403c0480308400c0a004a102041c1020100b400060502e00e0030f9031044285600000a00016442559440c0f59942c94039060401401948402d0307821070810740c0405c40710340380c540003002100e40c0900011300f03092103480060720300314052140301c6e00407881031034086c6807150750300400381408109000e104000b50307a02101040c6200e0004a40104040800420305103000100001c00a001100700400c0c003400e6410070710b02c0000c0c52002200d50030390400c0856002940807070504212400208000c5c141440c41d001d008944034400144071034030292079210400503246001a002d451035550046880314180f550103803500401603d00381c41200720359410400c683d601d80c801540101c501d4410394440c11014041800034070745800090028802041c0801d040b1080b081401c950201219030617640c2e645c0f0705904401c43d0003030301e101a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 109612374 1250 109611124 109611127
    0x100215061f030209010e300c0d12020c090c03091501050306060d0510110405031b0f1c0c17160812030903041e170d0f03050603070504050406020c061605 67
    0x52000b80030b5400741c6000c00040c1884c1c00b0740044040090941c25054121054210a06c3e000000d8100100e0002c42c948140c0c1005000007002c80c00014a40d005500c0028940d034030325010a03444a2003444585c50200014088900a05054042a103690001c403a81001449100045042416a2a1260b0403100c01038090301c00360b15900180540756100e0041a529071084811401035184d040c0320b001041802401001d44031400c09041506000b02034115912409a41c6000310850352034000b0184028400c0718800c2c015803d4003d046420308075080c024049840c01c15001803a5011207a816040080030703019254155640c00003141c08010600031002036901064554200007036940045404c010302108490416a0314140c3c080c13541c40300003007412100e814031410004590702c41164030341c0c451040040d0008100d6118001c0111404d8280d08080603101c001080303c035101444424083c11024000b4003151400c2d040c9080030707600c0714030840365a200300d00028054039400481301141c1d41e06a03a030507 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 109613624 1250 109612374 109612429
    0x91202030703171f0e0402010e010c050613020d0b0f09010b10081f080f0c0102011505220e120909060a06080a050705040b0a080412030b06160f0210021506 68
    0x1e203403918020704260a002000c482d000c0040315118130400180410564142c003071030a4400101051203500049050282034440080000d03c08508a0b5018102c44000d41e10b88130309000281d40380342c030260042e182d00c2201c0203000301c400c01140700380c2c030901000000344800c3c10381d41c0600c29020744203040400000c3d444c0d00415412030a11411064488031b09000c101065255441039041c0b032200801b404180d4040814004e06503028050710300a042a00c1480850500d4000400c4208241c0e9601d04c0d10001196031748180290154042801c001d034120444840712481c8031041d209038883d903130180c0305030200f000240e441c0c80c0c1041c440c1c00303607405035803025031540b04c0c42d4841001c0d0002901801c10f00006010101e40648450040c0001c101160b460000b1801d190034020200d842c8140035104140c10004000c4207a220282280c40070004c603500c00031250400e090214a220b4013010003540143e00281800541381e00141020b122220310361410308980300e00081003d84100000100074402d001c080d00b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 109614874 1250 109613624 109613657
    0x901050f090c0a06050d02070b10032f31060317040303020a03050a031e020406030b040515120106030c09140a0905060402090402060706090803070e01020102251a01030501091202030703 81
    0x1b8003041c03038a12001608029040d80d88080751201103440c00162419054104103210700048070804000052841150b0b031b880e19000d5078003c01080381e8581c0142c60b0410390308003041e922205c15041210a01c0c03000c03002040c186510015000c00d00c01540c00c03809030300c01200d89244490844045136030580042c501c001e41070741d00351415000300d40d0700e100385a51000c80c0c43c0000c4040e64590001100b1000c01640ca90406001500715011904c80502076883c09040001c41000c16503420a810000c554000407404402c50007030160150f6000240011050000002e12400c00e82080c0744c80c00d0020059000303982c5000031142128444140600280c0c080f1000c90058101250001d4010b400a010a407078403015865034000c0c0e80a0007021584144004208101c4560088250a201d00e00b44000d43c5884036100b040300204085015041020442c0c1240c582085486030700e4845450070103a04480075a920706285d8001c0108050950b4900303202d015010b0194030100407982544d516407528450300080511 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 109616124 1250 109614874 109614877
    0x15080f0c06030a1e090302100f050f040201030e0c220c0503070c11010e0301020a090f06020a150b0d02030a140106060c0210030518010f0b1201020f030f04030201020708030901050f090c0a0605 84
    0x2075808a054600305004820084c5004d02040e5078001d1300200707541c181002c1c001d8111840030112403d094a40410b2051030185158426005a0246404558006000c0750a4140302d41104041d03401084112503900c0b50340f82c400404007072001a6420029040c506100b55414841250000000313144204d0341c20005101201b04c0d90941b0301031500c0411880f0700d40100303003242d0150740a003001c03905c040d1007048041510090080a85142d1003d012082007a40d9000180400c40c0c1d80d44002e0b81d11840710a60301c0d00c500c0c50210680d03070010b003141c980e280b140c01c00e8481044841c0d541a5603509200c80030900602821940d07110690251902c01c0b8501500d5007103005000150a41c01d01020f0502000c581d0340c024050129600050300c0009040e0981c101000314544681081c0c0c001a4010322840261030044003e5a600518200308100b25036107a01c1c0c101d0091080d444024448280030042c0407800505600161007000307201761200e501c2d250b540c20541da4500036840c040d031200c1000400d005440c481c50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 109617374 1250 109616124 109616141
    0x30d020105090d14090405010b0c160506121305060c040312080c0a0f17150a14010503070c03021218030d0c020a050d03030f02120702061302012f0115080f0c06030a 72
    0x213855909103c42140000c1c169002a444514840c40200d02e06000240501c01c840181c10955000b9402e40d03c1d002c00b00c0e80500424101100642070000020441c03e502c00100b29041c1e80706060340c20f5441c106074070b000c2640040c04141e415800f01a0540c2035203014165090080d00076000c0c0300d00301800c21404403103c03222504084200045250300c2507046c1100410540176036030a03c0020406015802400b880c2c500310b0740500c882c00c4d50b040c250b1881da40c11008032a0052011305d803140111440c0c3c1401e034980721640c168404e030a00009810742e8a19a40d1080d003180c3e55007207058070055600e1b00b004842400b5091b1000c0c0d03002c51129010032051030022000b8007154803c0c100842c09554200e202012071300906074018a00e2400010042000e505010069010a10003070400044555400003090911030341c03803400080140013558400080c1c0e00ca604440341c4045002809076100621060b202d040300d51003141ca2903c50545803908150011910010b40900900b62504543d02c03051007001600564 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 109618624 1250 109617374 109617407
    0x1206050a020c06010906170303060f040504080412030e010305180d0e0109050a17060f0112110d0204180201020c040204031e0c03120206010e0c28052106030d020105090d 74
    0xc002d8142142c0d02800010b00030070b880d01001400e2482c2c40a1880703960002c4110303043da90400c1003080a60f6030340c19114854000180e40026960b82d07680380a0080d8032a0350005406091041251801c241d4003a000c0c82401d0030a030390078081519110061a0302240130000c40840d50080c0072070f214034038440c182e0044445414900103641da41d03a04c0110301e5204442d0490303404200b8041d00c0b907074003c008002c00340c0c00164840180c003c07980b400003050039507102d505004107080816240c0c904c45a0f00d900c040c08500350028010450b010200032446046990402e080b40580603031000f8409900e0704e442640e0450b90402c1211400c5200c901d03203030488103d4120220398550200c800807001c80c800d1000c40c0a1410190020f10255062206000180d413000700801d85048040000c0d66401c0601d491640203a12007414030b60300540c00100984031400303540d0700040c4485c2102d204055203041e4041c01d5000b080305500b0f4414000c1ea1030000c0342600c8044a548a140e403001800c004444c0c46580e60142103c0312 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 109619874 1250 109618624 109618627
    0x10e0f01030b10020708010c0c081204030c020a0e091b01020c0906030a050708061906060e01030207030306080607120e010204051809121602030c0102070528050603010801020a0f0201061206050a02 86
    0x80002915901c3c000180b1005070b000c00c009000d9103000b44100311001403682485c4a03640c2c41039403041094031603030000030b0710003a4103c040750805009000ba00c03101079004002ca110716031151605010603404070b503280c80e988611400d8900c64454440e01c45050301c03040c0d000c1c0184040b20b8052014015001d010035406105004840d0080340d014000316010704040340142445040200707a0f00094030f82441c402e16071a160000401c2500d400c01d0800315400302c00e0a001d80c5031140c609040d001810341e640401ca090182c00200700d085940481c6203901410030714820801001c415140c54200c1c01280030b1030f40c000c540702401c150190f100041d050380c007110782412503e03080344522141d4815001807500002c100740000c03280c000c41c90140042940050288006c3c20b00030302c0e003000903403a00750f07a0030fa03000e4900c0c51312440c41680e940c4540b140b01405002d400c143d0740356900c40c0c695000b5400b003891840041e240200fa045001d10602883e021101310083c421080007445d1109001408080c0140c0c0d81240d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 109621124 1250 109619874 109619891
    0x50a020d0605010602120a0f0e0f100504051009050904020f060d090b07110f060c031306020c070e061801031212091101020f070b03010b07050a02211209010e0f0103 72
    0x3596409000d00512402002c40c01e54508100a440d0507008039110f0405001031000d0440c8a6000c90105154046071408481c07540c0c0a00200d0320708030f0040b03110340e080300b40c419141c0d0f02c0d0b940000042c070445005441c003403400c0c0b4140a00f12240d0346135010b0ba50340300d2240c101003030242c40c00140d0078a84110080401d40350548410aca2000c444d03048600b11501c02d19070f0100000e2680103d21002070f07003030440180415103074009415858401c000c3c079043c0c504c1c1000c000f10740026400c1c202d0052066120070700b191b55054401a1075500c00c51407040b614032403501c100148690400700b0880044a40e4000343c2c11040c0d0850b0740301504100d0441c903400030421003550010603d401d90203550f0311140142c250096003400c107000203080c4a4102d420300c017583d001c0e40040040411010403a41101d80414030180c980245250183c1025007a5201a43c00043c0c03180310400a0810302045002c1d0841d6000c45104038100b0045580078006c2c1c010840c042191062a80b1040c1041c42c6420714107038052500090303103075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 109622374 1250 109621124 109621129
    0x15032d29010201060501050f07030f020f25090e0d0f1403070e031c090b07080d0204081c0c170904150611061003020d1502190c0501051f12050a02 64
    0xd0890032211400c460000d601620758080c42141c014003001e01c0c1040c0303003501582c0e983e50030780700d4204014100b1050301244021a403083c850701c1e20781e08055080e940028860b007510000211302d000030480c1304060303100028080466201c1e4007680416280034041c0e003410868190307520501da02400040c4031142408031189084040154403610701511105000030710801072500d043ea070701c080b184017058031055006c0b0580d00044a02c2c1110f0b101c0300c800d81cada2142d034030300383e00140a480e6043c0d400c0b82c0041404550500702140d4071010300721a200090032684040c604443c161502c86020f410045e0811030007805009440c0200dd801c080607001146824041007008140c0000b82d005c07030b0006000d000b1001c03c4050034420190425809081d01030b586055400060020b102014014290321440840c00c01c0002c0c11b8041d0740300c001c418800c400c0000700c4400e000d0501d4401e0f502c01c440a507c0c02002800784a613140c40015804121681421850704104040704221400710341501c2500c102000030005a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 109623624 1250 109622374 109622411
    0x40305030a060f090e161404020715090b0601140f03070305040807020d0308071d0f0907111204061709060406020903030c06101d0f04030f030b061315032d 68
    0x4107409031303001801c0c0108840003030034290407882e0302d0320a8560030010801038010350082016144102d40050f580e603540d15189410b81404502040100e04155a440602c025003080c0b9124400070788510b880d12443e031130794182c0c610038890700781c1cdc1c0c40314107201007805988280e02c000d9015102c2c204080c50828160000f0323400c1092840100d0020b02a20100000c080c0e11039000c030740300254a84020340450f1240002102081810022402011040005a04540b0640c2c60b4000080306405449642d9642c242d5051980d00a0151b080420708802c0603001e249260f0240900c15021540138001d03030340b51955050007a500001c002c039414801404105001082440014040c0854017449004e007840c0c06001261b0b841010154000c800e2200100f100744000070ba102a8000d9051038840e00301c40180006400030000c820142c0c2d0072407008603c00307a8184a606100e810350300f0400f40c10038803884c0180d048003994180605480400641624440081d140d884a42958030002d100032608801140702820300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 109624874 1250 109623624 109623629
    0x11b120510030212070501180807090504020a0e070c0303110304050c0f0303040f06080a06050d03020703060b15070b041b0f030807050f0102031003150605091501020f030309030408070e0609040305030a060f 90
    0x21070708220820000c540e0001740f0908c80c864191a200d08607494800f805445140e607111b00e017811501c5000107005c550f103c410020103410145407807042d500f0712040041c007030000003008038003003842d16902015000200060700d1265602c04020500d400c124000c0c05202042c8100d810380500c0148008146000f41100301c00180c10300303554200503450715180900030740da0a680424007030350f10082c0715004250b01103400d5060343c0d005140812034020740e4004c01c280c0c18111603003100000000c2202d00400841c40b2b142c07800b40e40030b41c4013801104003000340480400d20f10310508a100340004002c0000840301d0700a841d2403401a000d0b1100c07209204403072820381c0d208942c0045400d0040f41c0c2441000706004543c507945118003020480b00b81018003050441101510b40b0f9107c00c502d840d039804580c03080140d0075114a00400b52030f10b0b8100200c0030ba680c2d0304a406040911f009012000c00c0d0009102c0a06d4400c1c2c4000300500c41942315038a040e609940044c240f006490340700e100100b80b164030f94158200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 109626124 1250 109624874 109624909
    0x60e0a0b130b0f0c090901090c0809010c0206070f180f050a090b010c080903032b0b03010b101115070203040e0c070f02010324090e011b1205100302 65
    0x414854a140800820350300600032800a440e03580408007144440c04800d07484800980f40348100d48901c03600180c203014a40349190300130340b107100104a85140ba000b0700b4401020740c840c201d05032220040306084c0d610300320380032006034000c0c00050010391241c031303160345a80502d0804550714085115040000700e0a03420407481000000c00c20041401c01c403650304006c05a000d030410204000200003844000c081802a1814a01060a40f00360f60240120303002c402410354070921038403002c0ca40c00c2c440300c590b14449203c1840c012a00701c5a04040c012038803450300c0104460075060414100383c0711149030110b40c13240381c4138040f0030050b8422702c0301d2614010f4055030000d40d01ca40c07620400700702c40040200761404017241481100f00069261640b0007019909080124200c10120801c002e0f1429034a500001411b4091002941843c40d50041c1e10420030703900248100640200c03001150f200040d03001e070018140c0740400d030f501c0006a0200d03401c00c02103504910503c1d501d800040e00207441420320744 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 109627374 1250 109626124 109626133
    0x8040b03010e090d020d0e0103140a0c0906030c120f020702060c061512030a031d0307030909050108030702010507140a170d14090307060f020702100504090c05040506190309060e 78
    0x2081c002c60810b203d60001044005007460051030100940300d807800c2c0348020901c140107c0720160f0741c1c000d41101000f4010003c601c0d0251070032a04003405000c4880100011404030107010031024424003803081202d040e5120b00103003040c824080c40080c000720f0b5905d107620354240b040c00300580e07603e0000c25120804100800f058186104101e05aa4194003100c2c811340c003100001c5100d80d0044160341d5441e0311801c00147d42407030701c1121300014812240141c114000011040304054101d01c101065440400c0108496030721041c0d031436668401e841c00a40410403d01c00c0e24001022908525524450b00d419940194490341c1d41603880756905203900748100c0c01294410b18020305200320000020608a13007905070406403e240d0300c901c40c19001401071074848040140c42850f0790115414154080d142441c1a6199000108240c03c50700031240a1030074143d1015920b4410710640d005e03524014003140c0b41c07160901410f212905070301940f03000e1548400c140e0003c10030f5481190303800b01c2d0400141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 109628624 1250 109627374 109627379
    0x6030501050406030209160e15120c0c060c07080c0a03030b030c0301061a070219090509060a1a0126160f0c0803040f0c030f061e0c0e10050708040b0301 67
    0x1509844058100c00c2c000c5141a4041015940e221101074008200300c03000309401391a04000c0b900d40301c2107030034140c00095124048190031209070007001d1800042c0d1745405d85884603014242030b4802c00805000907803182c00400c0f15807a00c000180701c031340d201e024064a4940ba030342e206410242d180b030095000c03d5844103444c480381400e00c01c40d0040c0000b10700070025181020708420401c04480c1c134541400c1c00224514085458002c0c0c0c0c200c55038014a41c149141e41e5400f00c4a001d81001c44500101d8015400441e1003a051402900d83d1500e440b0818000030001000440705411181c400b00d0031000822071081e041401c4001c0180524580c580108a43e086518040c005104c000c1c014000c000404a03c00045070156040c2d0750003035401040b070b0901b40030900b0030413000c941541000d0103070800034000504000d102d6001980844000344200c0340c00f104030070b4050171101400d4005010600c1100020a41e01c1e0054009000b41d860b424140d041082580700e036041d60f00140c00441c843c13a0b000006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 109629874 1250 109628624 109628627
    0x102031b0303100e0907060809190501090c060c0f152903010c020d05030a15050303120114010e01170a020408070306230108190618030e01090506180609030a06110406 73
    0x20003000c4c03c1c4000c18828a8204555200d9980410740308000c00c100e0000c2c0450680b80c42402541c001d0a95103d001900902c0c070305000e8004c022a03642128500316030800081d00718081e0b11070b0220190400c606200c0c2d20283d85890030200050511560040c0c0e0f02c010700e0786405034a0307001120000d616000c420844520005040c2110008140102958001c1c1489075845a018045a5000c481580d01050a4810314544440300509030000340c1d150001140ba8040340c104482d0039412250400d0b101100c50490704015106840b0349020b20b13000a86126040200080d200d041c6900314000001c01454265a1103019007000a40c6d0400c039445a02d0340044e1902c2d40f00300000b00c407865a500d182c00310f0780d407504600d640d1794804a0012401c035843c0086080500c151940899a405882203d4121184191078014201003040e5815400b040580402003541e041c00c08c2603075010302000035a416003a03d28010400c440d000146980d40c913201e400c00000001d21603000b08400007100768800342d1a542403850 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 109631124 1250 109629874 109629901
    0x9031204030203032a070303090804030503030106051c02090d11030c0a06030e010f02090f0d0f02090c0304031b02010f0c23030913090203060606070204090b090c100306050306060f0102031b0303 85
    0x41714402100703400c02d1914201010b4040352101c0754541070015000300342c1e00d00b40d1301a0040350b0019020740004800015899089002421014000c1070101c030200c1c00d14203044200d005801c0400c0c1c00c0110400314000042101a040080710001811501c1221001d00019140181904114000f0b61105100f0112520174014511100e005480c15420f1003080e401084c06515407a4909210712440301025040c40030408000340301d01c0c0c02a15440042c40d0030581c005c460307170040e0b80c11800119000641c0c02880303040f4000146040c1d05a5034491281c2540760b00b1503a07c2d22044094641d0594180007000896440020104e4404014040c3d0385030924075042000884112101d02d0502e4104207070000140da01042c403540c448411036500c2e032119164000301d0000c110684004240d04000d41c02e00204910001301d50341c03452001c5034055044000c60100f20103441061040e41c0c0c060744038030040f620030729285902021040041c41101d04020000c101d00100c032804120040443c0c10000c02c0c01400d034480c89 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 109632374 1250 109631124 109631161
    0x1b0e030706090305060403140d06030809090105040209010804080901211a0a0303140a0509130e0105060103020708120a1401120201080717061002010e070803220302030709050903120403020303 84
    0x2c1c1220800d02d5503d030141c46150080c001010801c0400242381c4d20605201643c00c0300c0d01c584000c1140319282c0c40c2c020003030350010100600c13380d00d00000149610b003e0003150420710041e510524a61102d590310701c2160000c81d0118140b0694034050324403111031403002641c0e0481f480002c41c19140d0b00203070251020030707108540c1c0154102c030b0060000c41c1d0030003405481a80001c4140b641c03403074181011a030360b000b9900f9950b84804003d030f01517508001a0001125551811300070421038440b00015030403031144a02c001c107448001e01c502d10340184d110308401c0c3d000043c0500460340b00305610300c0b40c1030030100360480c82407182c50100c5141556449032400d6808501c4e41401d20320304042c204203126104000b4030891144034200802d2100f54400e4002c0b03a0300d401500103c44030b01d0345500d4031a4590300b0032031034034000107841c0e41c41c0044a18241e003040100c94000e005400e5031410329001101502004006001c40d10040254454104802c84081d200d24020381c06141c40b030422040706038a004441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 109633624 1250 109632374 109632377
    0x40510080307080a0306050909060406050901020c190503160b012c010e06010c060c0914030c011b060605031005012309010b0a0320030907080307050304181b0e030706 73
    0x181408030840c000201c0d418190040c0e00d03203855a4280320114083c0400342c001542100e004010300008134000961b49000b89d100e1142800a40d0b900ea90b5903080340a0a28074907101d03404a04e240d51303500002c800c2445014000d0041e42e24001c0d1312820841c0003a0132034000c641d001e540500411900300d2640d902d030051480e0500711406641085605607401e14103000d4800c1440f045000320300340d070307014000030b0f0b01c83d540c030000501c4660319400003e81151560b1103500c4001f01c9a0f12044118600414104900641611124281c0074140b2030359050503188801103481d80d5039110041000d41d41003140c0042e05042110104281d03040c4889512800328901c00f01c41400070030320755090180d89083e0840d055503041d644064a6000b00141100a4418007031090340070181000c10802400210000f1803140b910901142e1615554410881d5a032103003940c0941590806d0200784040c00d02d1504145100401c600d0104061522189180302c0e4084280f0381004200d212180202a05081c8403038402003006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 109634874 1250 109633624 109633651
    0x12040c03050607020c0d111c050106090b060306180615040b090414040b010302060d0902090108160506040b09040f0b03060a0902041a060d09031b030903020411040b18062203020405 79
    0x2801c08500d29241e40c0306c0040041c03005410103040c2392200c0d40b502440340c000c511200880100c03420994020712140c003c501d00311b030602c01784030b11604040c802c40e4010301c00035040c0e5241041c819040d58031804080c0c00b0941c800001400f160401d025200980701410100b50500c3d0b49604060401085074521114040346060200400c400319041c2d11203981181d8068909964030007003000b04000404104078025400000e603000424040c100241d145403c424a042440045460b00d040040303a00131072080e80004002002400c0d100c1c00e19030840c05d41480c4803080800d151403030b480041c0c00c0100440ea80420959520740e40d00c11740c1750a02503403e00301c0309204070403a0210180041011417240b19881c031043c1351510980010540324103040301e0010b0302038001405800e05850004c05000c03481c88180d1040d410280001008000c8100b160b0031207010031041850208847c1c0052400d2070103242d040d52005061001058040480c41901c84110b40c01d10380130603040c254410442140c0b0b01030502c01d0006403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 109636124 1250 109634874 109634893
    0x9020a1e0609080d0f020c06070b01080c06070b071d04020f0d0614060a0806060d020c0307151b260903040812071101050706090c0e09010e0a0309090c0512040c0305060702 75
    0x800c0349200c040e011702d84450680355440c800d0b460020000b07401504121b0010b5000184240000e080e410384211809032600521072000708010b80c058030307801038640b01d04c507000301d400c441c0030f00342c5000032403801080e0340f0340702c0c000e180020126004081c05085050b0001021550100541710760009400320f00343e00d180c4034940001180090056200f05000e0007000408907015940da1002d4030000e4807031110a56403101d4664030350f512500a0030702111a0b600c082c00c800512101805094070980400f014a0400150717100c0c1115030301c03121004007400640321560303012000b10b030205242c86801c04100131603039a4941660b1900c0c204008944154030881449600001a00581402448442403a0440d1200c0c05820240f004003204a8020003046001100280f1100450307003503072142c44440020014a10503140c02c60300c07100a40002400944240401d01240a82d80c2c0050390340b01c2c0a140c40c07800c00607000030915101d40251000c2e0340c1c10074060f10800c2001070400006a02c02c031030344041d000c000c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 109637374 1250 109636124 109636139
    0xe0d020d03021305030708010603030f0914010e010e030610060e09010e07081914040201030b060304170c0703050a0507031211060406021e0a030f0e010207050c04020c0109020a1e0609 80
    0x1440e120108101600021164819954111020050040141612032142c4e5502002d4002e00580c4004c402007205203012519041c01902117100311810051a003a240402400450300301e240e20901c00d044c400b5032031240149450030000640314580d0060541c0304607041050250030a50b5401855100c0d81804005100045041043c0d41e001045c0d810404200d4a601c100012801c0c001030300409010701d00f00c0c0d480d070020304400405000328003e882c1000000c10b60401d2207010b20040701d0261080041030000e44903640c3c582c000700507244001c0c2c02d03101016242d80c2d1707860030145040800e455070b50002405106010003a9101238403d8142e08000d082c0f009100200780d1601001040a04a41c0d03000c10707010004416460f0302590001168905950307003213140304c090010000c4175140404689441444c81c0b071460140f00311078060381c003c0024007d500c001d81c20017004e944101c030b4810481d5265010480140c03501c0d003100c00506518010340c2c00301400c0c00080c0e40702c0d200c0b41d4000c0d0100b2904074410030400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 109638624 1250 109637374 109637383
    0x60b0c07090c020f16050a1202060909220602030411040603020d080309120f0c011505031b19120b09060c0316030608030a030906060e0709050909010603020913060e0d02 74
    0x8030070040011034030742c100b0348040e82002d43d6102450080d005200341101c078841d51030056015201c049540c9500140c4490144450b41c83c44100203401c00000c1081e002e1a103440ca145543c03201e04840302c80c00ba8118003c40c04021400d000c0111480b640100920003004034a28818903003980650b410000340d40381d80c00080d00c5000030701d40a41100400008a00742110601c070400d0207410b891641681c40c19040003694407a842603003405619483c01003c4400901c82c1d8602804841c0010000e02110081c0c00690303503e0b403060304145034020360b82011441403a5a0542e610300400c28240d0882d000307120350901403011a0000d01c1d0b81003541005080200c1400e042044d02c0d040040d01480c5c0c1400802c60009400410041e08041d5aa100119100c841c0740d5154000050311442900140002c5640c0c0412510700881614083c2c00301b003100e00c0600171414681c8042d81d014107a900003141c0c0b00e030741c2d0f0007142c000e990981e540241707080b94408510503c80b03240a820447d4102d10000e000880e40084001e464 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 109639874 1250 109638624 109638629
    0x130608011706042307060f0e010809030a030209061b0102120903030601080415020c060405070501021b0a1e031a0402100503191503021206010602060601050315060306040f0207060902010201060b0c07 87
    0xba007207610109011682001112921044c2c0b0303048544c169129000a4100c0d01c25100030030000b080504044503d5100304405030084981c00c00560034400b4900054010390407080309250041811f1005105d2074801e100c2d00307800b41060a00045e510100c05001c541c40300c100501205d09544100240885640e000d620f4580c03164011020001c8050500d1001c0c0c06032140c1c00c6009294418201800f080c0a00803a081c4c0444009130201c13103100c26400141d8034420006c250b9036902c00b0141800b080f10030410200040f101c0c0e80442c520a0064a0784c3d00c000c8810f195500315402400880d04020450a18500060307000405041083c111b01d414440d00305801c189c202e10200701034580340e904030070f610301c200298059030303008004403c01021b03415a980e0b00e02c001d1003030343c0052240c0d001140b00741d405803044901823803540340c0c44030450607403800380f00321035002a080c142c0080da9403024032000c44040c4040c08540340f1920700401c2c0f03000c060000a003503070080e8010700321000c820865142541d4001a2a604 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 109641124 1250 109639874 109639883
    0x50303010509100e091e010b0d080307030e030c0a1205030c070303091b060503040c0e0601050d0c1b03050c070602010618200f04060206010608010b0414030a050313060801170604 78
    0x19980303640c007001c200c2c411588021301401c40501031000b001c901149603c00320192000f4402950003102001c0e003a1242824500c1d0800850703032982021602400055901c09011f00300411001c02404025103190b0000c403c49206800c01c5212604114020800b004001070703034589a03003542170180b070160351481511801420f00d5a00c0400d02d0030030424050b03401d806810b44815070340583d075605c800352a41d44120740842e85c900504c0c0c4089a152040c080380c500801e0103a4419052180c805c0c0950003d00c0745810710814001d55080418010403461160305209100c1c0d522203448498090000e85005559040306041d0390512030706014920b0000000700550608200c003007001224010010308059007440e100b0721203a40015405510741e0180014801c4529903804c64500d030780d82c0c000c00c4a12034420700403044040820001080300710391500070404140002025a003200c2006c1c0da400c1d2550384250400080b1030401c5c1000c00c00c16030080141ca00404000ca415141111011941519100000c00040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 109642374 1250 109641124 109641139
    0x1020a080c1303080a050405040605190e0c041e06080a0c050307030f090204020d02041a120609040201110706111203010312081e090c0f030a02010c1115040e090106080a0503030105 79
    0x940d0b402001145600071900040c4069451005640041441d40180070722030040d0300344a000035080c14510460520b050341d0f0341d01d105a15040903000304440304081e08503075003a0301c1400081015040c0b404c00c00d0f0601c240e06940e407162442c244000d08103200051521070307a20314003130001251641041c1200d83c05401ca1900250705009404444010516824040e41103803000c109011074101a5000384140d800d1103040022142d4801e400c1c07081807162007500030502801c4408144a42840199203400520504001c6a01a00041114a00711099021000081c5107141482100c4824002c3c030180e000e483c40042e29542c159241c48d0700140415a0100400c812000050740340b10a40002070103200d030460150289061406242c1e50b42d03446070018501c5106140080d40d0035140004d40d600c802541a110b40c074041c0400d40b158900403000080c22900240380407041c40c80700c4580070041000c0e1180c00607030025070418544050071980d00f508280f051340c0c4050354000c042100001501c0c1151411988107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 109643624 1250 109642374 109642387
    0xa030803101e081510030201030f060308120412020705030309100203121603050708010e13020619020106030c120c09020306040603080f0702010f2a140a05071701020a080c 75
    0xe8035000e4580d004211001e0b0042c01580ca4400680c0c1801c21642c60340f04039140311400c000c0d4a02050800c1d00d503a0072441d03d00c0400c00065010342c0040700d011102d038400088003950307910f4081d125802443c0c10300006641c00c0804c020000c0d848500440c0f20428030041049600f0030021990302c0c4a002c1c1d409104c0c110074001100414420011913200c07640c00c03200c0c41e06034102500d4944c1c0480b51817800c0b0001c00e00307100015140320300c58000c66040f11951a40119076485244034100c00c00f021070003e0740c00c403208226a0f5031010540115094441207980001607941c51400c1c100150a00f41e0400030824a04d1a0350030046450042513200b43e8464010040c0d8a4030350300e000070300420055100500000d008690a0851040000034151a6000b03890303510341548040b008580c841c00c84070180c007100000748004070503030080d074585050407032207401c2403000300114842c0180b420803030000482c6d150344200010b0081842c61043d0321400c0364550001c1d8102780c48090007810000000303007516000000800e44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 109644874 1250 109643624 109643641
    0xe090c0919110c010f05060f1009080d090503150403020a02131806020d0c02010603021c02010212030a020c0706020f0a060b03100f0e0f03090303070f03120501060c020f0f0a030803 79
    0x305100603aa00d070800011100c41140c0d90680c205107403038002546000241100c0d41c0503809614440c19005095200d242100070070041c009101079061070410100900c007081d1032204000c041030441440d00d42e204024070b07004c00c0516000c402000201e5106070041804006038001417001d501d154100d07071852145c44040d0a803001012078440e40701e5403000c0f00300454148501c950080c102d040e082c40052007401c0d01810107034240c84451000030b4203c20b03030403440c1410242c1c01054030001403051068501d030203055180f04401d030300141c0d4502039484d400184001c0c1c0312003c00029000b8816400030384000140210440d0b210100710102030151921407902e65129a03080c04070041c00c442704003041000010440c1c0000041400030b102031000d00c140382c00c42101010002c2038a020040040c0150724003180c179903501e50034030f406403011010b001070b542000b000044c0500400c1c0c040c241c15560001c0f100901c2c01000441005003141501404000e100c4c1552522054083e1060720b40000081c1d50341e4544614 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 109646124 1250 109644874 109644901
    0x6040609020d05120a030e0607022a04050901020406181a0a050c1b032811060c03040806160302040810051504020a110708070f14040f0204030b0604060e090c09 70
    0x401411400b940c1caa00d5152010138018204000300d80d0b9080058074041c185507951880d040d1007460140e40103400c8680030540d5040c82044000d002c80600c030800c51081d011405a91040d1070411090b500030409102040e4070407140c41505a400e070840040d01d1520344a44e070030104800c0e100c0e046600c00140d070140c041c007403030444000c1c8100c0b00840b1440d001c0002200030030000b280c0355503c24010784050200342507041d92040155445040c060400c4405035461022404101d40742c0c81c0c1155050024800b004030600c05840282802c002034030040c40d00b180c850590040000c4080c046c1441800180003220300050002c403000720701d03100080c0c56151001d229240a0b11904403070b034814000036110b4141c6130b000e081940d42811340d80c00c0b034041c1503c1e8200c45c0d8841c004c0340201100b2072220203040002c180585482062a00d0140c000a141a07050841c44107030fa000340c005840d01c0c20607505201580c00c0501c40e01e4002c0040c210414000d04103800300d56110003d18540703d00c00e0000d680031070181041c1e5403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 109647374 1250 109646124 109646149
    0x9040605060f070203070801061d04210f020d03090c050103020304110a09020403030207080d050a1d0301051e090f06060d060b0306040c030b0c0a1b030c12091a0c0604060902 76
    0x744a00e440d001d10140d00c0e84940e01c0f41c04204d02a000e84000020450310502804042d5001c80710303012803000c42d81c03052480301000280309660800481030a21800d03003050b410883c4030102d40d9610380c0007041e5014040c0c508102c4462031010107203017001002c04a5000440c410a9800c00d01e00580d0f80d80b141d051110a803070010541c0c60784511400300c00904d82115078003d104591207074091301d52040c0e0302c22045803150f10003040032000c01c1007000401c1c0417511803070303a20510424a04a0b00c00020b03c2d0b130b0200b800c40f0011a071000080304c41d11900c2d11070001500b9059808500040148002500c1e984040d403900310241941c2c2c0500e088400b40e80410029401c103819160015003269290b03c5c09081001003240c0c00d11081d10f401c251400815a0445078108866030411680c9031528003456107599002c07902c960390020b80070040c000301d0800000c2c03404054507200b07480640d07503c041e00b81004800b0050440c65244a9442a010081c40f000c0c00c40c08100345900c1500711100150034052800483c03407510b80c0a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 109648624 1250 109647374 109647379
    0x803060d1b140111010515040b0a03060e030a0905120d120e03071a10030f0b0c07050102031302010809030c060c070203010e0d0206010311120309040507031b08090f03090a0b09040605 80
    0x9030082262250104604030100090342c1e80e5502d412180d04d201c0c2220300a86081c1c01000c10021542094141078000c0380c01d00394090104426141c1da41c8566040301d041d0f003c85080d940002460541c1990700c941c00342e01a00c400c460903a08800c0c40b04481e0f82c0d40b00303a030701c00c4000e0001c07182d02180d842d01030742d00806820401c2c2007565078900880c07a2031014035070609281d885081040340402d59601c91140158280d9034002d105082c4500e0544a48003081001405503610b00d00800409001550138000f80d401000100c5c0f0704015402c141c400540032000061281110380d0003070007a1050300b1000107105412482c1d0b541c0142d61100c840c0042809850252301c1c102d01c40c41084038207204107070700103a004d04983c043c80f03581c0b9080e0704210801c05014800643c050b0300e54401d102078116031030305900841e0442c9081c10002410312028a540c0205680301c1545800700e00b03507508028002c0e105000014031000c80354041c2d0303c6c042680000445038452405080711005002c904840143c855034440805000d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 109649874 1250 109648624 109648673
    0x201021e010204030c0608070c03110a02040f020c0f0c03071a0712020f061006080402100c0b1e0906010e0403051308100603060f0605130e070302040c0201020909010608040803060d 79
    0xc58a514080d6001c4e21003280c1c01040c68000040e003921881000780940582e90700c0442c125100d0320110b80700c0c484074201160038000d0f006880c00513a9584600da400000942d40580c8a901201816040c541300c1c22850078282c2102c0196440d0390790128800068400c600705100e0030000d0310304040c080d809041d9004001c0c40c40c0100b83c9602c6c0707400007110030920b103070402140e03410340e02c6030381416842c103070b610440021a0b0b901c1d001c0340040c50b241d04600c2c4103c0d1140b070710010144164654401d1110190740d00300810880d251940d5400300d081101540c0040818010b010079450300d003055071a000300a20141c05c100c004a5a03105280d08803006000420040d000c580240c00c1035042507009180620045405501d030811000100603e4020350b4100c403002040001c0b080c48100c0c0798009006200c00c8210140541000400160340c0c078480c0c20084107480d4001625000e0040074001b480906801407824800c18008200004100e0703c00c4a030b1000302918035182d654207610b004107954070b440310008140103d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 109651124 1250 109649874 109649923
    0xa0f0603050d081812030705030604020915041505090907050304080712021b04090b22020402040b090405060a120609080405030a0b0906010b13050f0312030106050409150b07020904020102 82
    0x14880141c0c0d006007000c00c255500580ba9503002d1345d071148135203e040401c2c202440000c01c0580544080e640c8980c1c042c0c000340c50010a030002418010019a40ca900484049001c0c89071141072002d240b1825894200f40307281120400018103d00c2c001009030007040400400901000104420303a40c245521480b400390a464810000e03445107002d06120400c80044250000c0c039290038003e45003400c1e000001602c868a404010065440420b1300140328074501c100d51200680315407009000030110801982e4a8a102004101c261800a0800c620070444850140710072107a8405240d42d40b540b12030006a464124a01059240501c0d4072055042c0580300c02c550910040e4001c01e0b01c1b8a4103a020385aa43e0381b0307130341d01155a0080c800d2420b621403146030140101d09216605ca20408002011520780246000f095240d50f40709810a400044c0301040030890101140a420002d90b12914440304071030901401e4010f030300410754042d104030f4500c8003050640e4020700600c90840510302c82248500b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 109652374 1250 109651124 109651127
    0x12030207050604140310090b13050f07090e0105010807030201021015150804050c09091f14010b04080f0114041e05010e15092803020c04051014010306030b0a0f0603050d 74
    0x704c1a5241e03001c1e01441c0500b4840041511840f000380381c2c401c00502d11034403520820000620700400840f92403203000f0140101080401c00640140b080120218402000401080c02d4a4040c1d20400480d88041c5003480140e8010500d45520b065032100003500c1a02c5034180560400258403080c0b04c00c070380300c100d500260741c0001c5d4280f086000380c00309d9052034040020700000c150210350810300c58000250803419034000394011240d00c08a4200440c42690b411000d98080c0000c0e4008a04800c00140801c641c800900404c1032021410000300915034803088010000708006100610010b0400080c01d00c07100d46840c05510b09030404020840030900b544c50320381e83e01009000c0d080c0c96480703000242c0545000103401d900740c0111105d401c561036400a40d500d031000506021001d5000345003d540303154687c5e00c03c4e50b205103610742c80001c10910300a180ca03040c48070401d8150406003401e0040c40413079228100341c3d0b0440000301000481c000011051002000e103504003c02c64001c0d03000704440d45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 109653624 1250 109652374 109652399
    0x30203010330050906090319150219081e0405010221010f0905040c12030507020a08010e06040219030b15030c01110a06020d060b070507090f1512030207050604 70
    0xd034814070074100102815451080075041899010b6010408220004800b9104401030712590310058102410200014006402d00503a404400c91000610b02c280c01449104680664103180320300c0218508142541e1f0344140307a502885c1941801100b00201c0c04000044556070608050800c1004050034103282140c042d52000c0c058025008000011030507003002028554100c500b03002c036805000c0c0c40c010603040a044000c005890001007a80300045402c101c5900645c01d41c80383d51001c3d6203082e203104000615825030081e0a1030b0b0314180362150743c014000341554021f07404880d10a48051303040040800e000a540000b81100301761401d2004129410803030f5030640c20100e0030b03100341642c1c400c0116040f48940d030b07100c0a540e0109180601044155004002a150400c8041480f07034a40d403041d003070b0b54094541140d02c3e80c000c8408110036a40391260300070381940390700c0034441c030100d0361981c0e034003090300b07000d14020000303901c199800700750080204000402e0042c0025488030303611107007407521 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 109654874 1250 109653624 109653629
    0x30803070f0e060a09031e051f0f0e0604030c170a020703170a120e0c0d120305070e06070201031d0718050109061a0706060504050c04030507050307080607120f0c03020301 75
    0xc2501d06040c030541c0e140040540304c00d1416075564443c02c604d5038071000303603501591941294002503941500702249041c002c3d050966000701080d01d41d24052402081100d1028500011052511403000220800412010307009501813134000d0000c00d1500340011100d023284007102580d000002d00100c5a034001c5101012a401a00da4699032240220009154890508408006084005040e040050552040203254101c02c200c0340d52140c580f021510f05002540103550140a00f20304078869503060141d994000014039240d01c600300c2d00004200503000758a00203043c1601c0343e81100034500c661015403004403400b003c490a441e51880d918440a80c1c0c2101d00d0351190400002058681590141c0d900b03c1d10440842c4003888140d1292184030b40000404440c12030300e40d100090259601c0c0281400750100c07100f5a0741c0c0303d14500d0001e1404100d0b50156009801101d02040701c990081007070381e4000078500f401c0d190b1411800b562002040700c400390740c0784103107403102100c0d890f54164050b505 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 109656124 1250 109654874 109654877
    0x6010e030d0c02030705060406090b07080c01060b03010e090d02060601260f0f1f050409150c05130603112505060405030a0806010201021911010b09010905100501080f01050118030803070f 82
    0x14146d164403d12803036104e240105408281507603001c002000310702c002801c0e40c90040c40c00e40e00300003802d02d0380d6094620592200d85480008001484054810481542c1150800780104034000c0b9655001e501c0d1035000344010306001c58505140101d0248041f80107070060321050752000c9140030044805001800e43c0c1402248104800040340208200c000c4914807619480034070540b807a0804000281402c1401101d082d48003103030081001e003490052000210381c0d034071900d40b91128484810f00740c044592005041500b0240b99140c0c1c010788004842e124001415101d941321807007141581c508901d600028000e1113208100300c140070001c40500700702480f5a503525081e4441100480c00e074002c003041c10381e51804400000c0340c1b00c0c0c06052203940302071031240081107151005000402d1090240d022421050b151010418081c040049290140c00242001c071014103001c203445038509014014a070511200d82c03014000710030200c0f0a04025503100d1009642c070701d02508002d00840030110342c0030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 109657374 1250 109656124 109656133
    0xd1d010c02121303020603040303090803090105071107060c0b061912060b180a1a100201060302030c090403050d0209030307060e0c09010614120a0e070e01080c0a14040506010e030d0c0203 82
    0x2c030340c1c01c50340494081c0380140c0210005281141c00300413803980060022002d241e95500030200047c0c07118043c5200741c268200004052600e00405018840c01e8004480c881d007140078188402030f040b1021040440d040052000325030395042c003242480c2e00f0848001c000c805c5014001034612808051411030501c280024014003808006001202085441201d5081c00e4007001860003c0a0741c0000b2501c80700c00c007040c00042c1c0e50f101003041e4012544920006075180e04040c011b6003010040c0c1090b5000039920840c41307180940300201180500c5000c124007903000115030300d16560800c21783d00b00940299082140c41340071004190354440511589003d000c1100000070000c3c02128a0107400c0c1803020010304e003030503c07401020b003540000c100d400711503135030045100104410003521010b800d8041c2030144079414501258600b50040410034070030f40070401e0a10014600c103100300b0036040d0964021882c0d4aa54005031001003040841030303003506c1034080205003281c0c0300d404240c50314000e90588 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 109658624 1250 109657374 109657393
    0x50a021b031b03040b03011202030a0219060311030601020a0210020307080a110d020a0210050a03090b0a060e0a0b01020d050304031b0606090b0405131b0305010906050a06050f0f04020d1d010c02 85
    0x360303d0b8000ca00c0b461000d040f0500c010000071048079a04d81c24184018152860b0a940d0383c0042e2281406d48181c8a22030106035041c005103825100c0e030320028850400a078158541600001d41d80e6040c0030000b0300841c41e142c86100114001c005868016a101030a29250107418400400c05802010906001c0c4500b00340d40c1750f1180080740d03050525030090010795424401c00025a603952294204008140d5034254410100d08036803e083c3c003074100224049401c82c130f0141100300b00b000250003031654616112600c403c0da03070000303018106100c890034a80c1e140d5880f81420f41f115401100340c541c03c0c1162160a00411070a6400320013642e201510800030b180c040c00034001211021508008003183c00208540030a03a43c0d0285004000764181c0c04006039100da07151400d4446201d4111081c580710801c2c015030481038045e11018000585030305001403038890025004050504945004541c0010741c2c841c07018031600b0141100c40b03601120341030038003000c6110b8020124190041300600581e5002d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 109659874 1250 109658624 109658677
    0x909030e040b0a050f060405030303040605060a0e0708010909140f07052701050618030a06050603010c050f030a0c18030302060604180b181629040602030a03050a021b03 74
    0x11401c0b0101c001d4000811207040005000214510303400340d0750302c00b00a120004042c0d400b0030041d40304611840010910b4209034080c0074050026803ca900c41010ba03200300504a640f0034241d50440d00b00c2500031682c001503051a1500e411203403a507104500851100d62741041c00024a0000c0715010790b04a00d890196070018402510145c044d04101004500100040d1a1610161240003800d03000b038030300140e89200013441c0c9500c078007044443c1c86d00c2c0c9040100341c0c5020b01c40c11004501ca401c0583c6460500c0e20b03145603901c4003e28500055a4400c03440140030700c50910b81089114500e88505015264140a95100b2040325030520450070301a9000c0002240825000c1da681d0003a07001d042078460b00e541e4081d00ca00819140c10b90302c01d171a600410001c021200c500241040062840e01038002d41c2c542810100c403580c00384911004000412030280c2c004201c40c2c100b0703524640004c003601c6000e8070313074003900c102c40c40c42d40e0782940c040040d1031480380070000f0140d040402c1007101c90308800160 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 109661124 1250 109659874 109659881
    0x102060f1906030b100828020604050d0f060b0f100f11030c0f191e0503070813031208090601090c0c0501060e18010902031011090904030509150c0d0e01020f06010909030e04 76
    0x7c4010518414140f0500e41495000030013034034900c0100720343d00345520360f404507070ac492540030199801c0d8407800920042c01010b20940008030816540c1400c0e01c44200c000c121040b82160102c820001100d10b030380c0d01c0a01c41d65007209840080020381e5504d400850890b42e407207a030910f80740410300a007007640682d00300102500300500d5208882d0b10b1044807520100700140c60703c0c80203442c24001042030340000b8103a800106840c0202030388002d0800d0031800c08110000001c0360340018003d80300b0502c41d018000090080c1155030742000410300401c0c0380c904480c12500420020010b40c00c100d408662064540041e07446107442c412a004200600d100c86400e0380d078407c4002e03402d03030440500454286102c3c3c2200e11100030714035115161800e544081214000111002e0300001c402007480700c01c40ca4080404410445820005802e1001c2071002c0342e00c4140c001806024845000d624070400e074000d221040030052004103894081da500e520a4001d040d13923080450003c0c2540c000c0720302a160910 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 109662374 1250 109661124 109661143
    0xe1302030a050d0e03010605210718060e0106020303190e10020d05181504150204051c02040b060c07120204240e060405090312090f0a0f0605060405060102060f1906030b1008 76
    0x1040c041d0007904000d100000c10302c8400e41017086008081021501d8030b83d030be841625054101c00c001a0032440e080c5007081b00c1074103800980071500304006000d14151400341d2078080c9040850b001691201a008452801c1a000e0350bc00e074282c00403511141c1021154001441150f440a104103144010581d09490781d9075024040c5a500007107000c0740200d0079040c001c126211449000600d8140ca03540050340c80ba500044410311464030b20440d4007142498007905180b40810f803080b9040001c401e07051030b100c820301d00a00b54a200c982d1000c201b590b0310340d00b00903405010030040300b00900c560f2030140900d0885000d00c0c148801c201c1c0c046506400c00e4460544240300c800013460500311410300f800c1122001030320046042c42050000025110180000303518188140b032000402c0d401407821400380c41004210030300c40e03403501c03082040f9a60045003150303016102c0090350040f42e603101c0303101458128064640d050f65140140100401400d50505e0f40100d221162261aa81d59070f20380316610080903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 109663624 1250 109662374 109662379
    0x1e0f0e0615060d050604061809030f02060105030a0803090c0604030f0b01051e0108130b01080d0305013c0306060306020919032d0602031f08160e1302030a050d0e03010605 75
    0x42115000003c215445036800010040010403299070320030150041d41034603100c0d0786185a541105104061b080052030300541c406001414603985050006a2a100c1030036000d0000400000041d409040600c0081c10700c102c000c0035181c030380b034403828a82d415041680048440440c448000724040c0342c8010036070300c4080350320424441380c1402030045074009409030000e03104484421007100060981c0d0380e024041c0101400908410100020050039150180d00c04e00d000c1b50400300840a46600b90508403a02e00780303020210b5041002210301d00c89410715800039104030f00e044404010083c05400078a4a010104c59000d4003850490728165011400d1100410010740305030f135619040d861441a000d101184c1e40c3c80031401d051a10743c0000d90b40110389090300391583c4d042148100110703c0c00403015000c4100200f50707034104a602030a6407030b5140118903042c2c4100c00000d05842c00c0103032380d80801d5405400d0314107a811a150603030360f94007204240342c00310f109003503d40d02a05051250b403080f01c3c3c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 109664874 1250 109663624 109663627
    0x3030606022509020703020a050d120c091a0903030408010c050301062705040b03190614010f030b0c0f070218040b2206022a060403080a0204080d031e0f0e061506 71
    0x140303ca50002903100c000128194090341d800700d0045041400236014040300341d120004214030001c807210440b01103030500e1382403005284042c04080c1ca280c1044640c0c00440c2c1155943d4015100003a2a5004a034000f800d25801c0190865009a011000e181240c94035115000e02e0301602c2d0081d0141ca40a811030524001c2c002d4040050346030a40185003040c80240036a460010321502618030a440d5000a0b0389007500c0c1e403541030283c44440c1d407140c0108200280584a107046a0b20100309250280070803420f403c010802c00c6905198001b214080c070342c003c2ca074050400c000d21589050001c00c503003d8070300c4843c0714000b03100304101c009403401b0b8031480241045030381e584c1e43e81c85000350400c117031140800ca4081c7c2d9006119450080b0390a060081100038000d41c43c10b8503008002c007200801e5010414018801000340d68000a1443c46480007410085030021000401c8041c001c865401e9188050400c0300b01c90120090b64410b0040c152208103444d926581d1b1090809119101066280c01000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 109666124 1250 109664874 109664879
    0x2070b0903030d051f08030702100e09070c03020c060c010c0f050a14160204180b07020d0e090603010e2d03030405030a050309070909060c0e090906010b1305030a030306060225 77
    0x499200a500c0000b20000d0b586517140a0f07503041100304c1c507400180e06070380001034060940c40c0100c40e6400390881850f20f9211042803c3c0800d00005000d03103048144051070031708004050086c054035107400c101030500ca40762844941c1e102d02801e09801c0d6003000c524086400311210344200209d500c1d000c80307a15000e9030141c80d00401d80180d4005003441c400400b812000e100181c4d51401b890003030b54214801c40c00c03201207904100000c1d10018014205640c014a4664900c98121031030700700d80003084503401c01550b9100c0c0400d0140001c41c0584c851405030b42d0410490b00c1c8440003520102c42e241161740c0400410242040e03a9100a179005440c40d8418080d20441c08d11402c011640a60380d00203640030103035625544000e690301c0c054100d03501a21a1010461140c1c48440c45044030002c1350039075814200fa1070701544900041c0038038511500005800c0051030380e1070160034000d18000d0112040d90700d0b1828000c0062160f40100c0740180602e41d003803821414590701200d550302016031101d00291 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 109667374 1250 109666124 109666147
    0xe0a020a060e040f0908040f120b0609090313170f01090c1203140f0414040507090603050901090c030c0501080c0f04050d03030906020d050a1d2518090302070b090303 73
    0x1401c00441030b038840c0d15031341d07020500382281c01800601c600c511000c1f0b4686082284088a6246641000e07080c40550050207004c1020700c4803641d040f61081d0358400c0301c1c0d00c0d04100e20f42144200801c2c000451903510f00014a01d4042c103405410442a009450300100b0401c055801d030307640c245c0003a1440c150641c041c0b01c10300000e811952102c0c8030b410030055106070040b0f03111a94100c0501c000c0040f40115041000321481c0e491420103020848080056142101000e000c010701801004205a40e66002500c007000c258024203095400860404240c0e40d83e1515410542f030502aa81c00201d0640118410003800002d45400346010848542868140030a0195940303943c1c00940805444800ca0720200c4c0d071610042006031074810020480b450080c3e4604160340d0088020410744c010404d000341d0241002c44c2101e000c444940c0c0a003004850b5411a01c3c02d0151500440100101d0b41200c40d03003003185600190049110343c003640c019a54a00110034a4020b246156415400801c501010072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 109668624 1250 109667374 109667387
    0x507110d381609030c0806010f0512030313020f04020f09030f0f12030a0f020a030504060e03040f09020708090301020307050703020105060405060f10031509020405030c1c1b080a12030e0a020a06 85
    0x1503203032520b0409144c0d00d8803404803550076940411955081200140704104003100140090081900c29040c1d079461100c90329641d100c0102001e5a458024014004540c0c0d4007505280340341d4010401d540b13841a61120b1009135102008043c881d10034000755980c5c1800c0403600c58404c2618102500a4803682c0c81c1112044c0c2c0024500a82c945daa194410030101d02440502a204081e543c001218503042c0340250444504c044d20303a806138020700c020001c103135100e0706001c15580c4281d009605c1c4e41d00d502d0086090301400e48050317031550012003048801a403100144c400c05000b83d0090040703442d807000b408200c49050380c8194105400700c100d50102d00b4107491800d00078155180010310600c400710404600b44843c0c000440e070a0300054100b01c685010010341d694940212180c1800010b2008049003c148490008044c3c4160a4a044d40e504845c1030010081800000341c50b18107040f450180003540013801e90324040707850010b038420030080008030600c201e64040c100d011054101441074801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 109669874 1250 109668624 109668661
    0x3080304120c0602030f07020c041505150c01053907030f0e030a0b0a110315100c0b10031a0f060405100308070602040f1e05010507110d38 61
    0x91040002d21480000c0c42440210300c20501071202d01c3c120f003401c110007420a6401d1100500c69400c103125840210084030fa00350803104100c0d010807500d4202c207030034501401400800d2825500c2c001c200071007101500400c1050a51801841000010100040d2560b85648404550900c018402c100002c0d000b000c40d45480b425500307042122451440000b4a0001104422a55201c1480c00c3c4491905607000782c04942c7c1a20071200e09520300320030b030b9a050801c12064103100b860f07440a490445800b5041c0303900d00c1138002c480c0d03903141c0c0340100740c40960380c420744002c036400503070001c1300d03c43c1c048500100c0d80a4200c4091078a240d4440404001c0500406051906599981140000005d16010081802510503403025848525225440600600c00d600c02e44100783c8001c00d2044c05010100700781d003591000d003010303a02d40781c450030100310705500ea030241c0d50010b544510389401c0c0140c44e4041600c48003421034510b444034502201405902a00343c101d0855002c81000c43d6080303030038100f000074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 109671124 1250 109669874 109669877
    0x7050105130e1303020c010903020f060906041505071106162a1e0e060109180f0504030203072d20150a030e070332100b010e09010308030412 62
    0x32200d80b581500c110040003528443c00c4220100d1442003050740520240c86044001d0074224601031454002c601c0b54815014410301c181070009808213556140401d0360094a443e000710808002000c0e0301400030380c44500c05440300f0000049115203071030807204450340c0300040b14125101c1c000542d140710303441801c592007a090582200307454a0b107140d54603048000700004c006410396802c3c58002d00301c0c0190242c00116010b42044200002d07030760424090000c0310864600c0f04118400359840400822600a42000c802c1c245030a01c024142d0000142030b000d4041c2c6a8400b20700140e0a0703d44a4151910105000590481d0710707501103201e51780102c180200411a07008190f10000000e1032104845a840400f4840800c0c0c1c480c1342c0785d240c0b1070410700100b5000208620390845e2200300c01c00c1c00f0030b000012003422207618503100407000c00c81c00760101401c208079100f50403041c5c64400a480495480340c001403514200035041d207480c0030020704070307500128180d145031205d4442548514003e40b80030b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 109672374 1250 109671124 109671157
    0x80405090709051e040b04020c150702070510090617240111060a020408060108010c050d091a0405061b031603021e0304060f0609021201050f0109030203010e0105091e07050105 77
    0x803d034441c0e82c00d01c043e00388182252401a10040c042204072401410341c03038000c600c10b2008480510000a0322001c990180d02042e003141c1e14280101c0c5000325030340000c0c0c1c100b0300d445007841e5401c0d0800401c81c140da140340c844801065174000304100010702102c5103c00145444500c241400c016820070501c1501172401c010f4034041d2410480c0381803402d90340b202900e54001001c0182c01001c0c050349000d0300b6248000e000f80d030b0030940e001b0b09900800c040c080d81603990302841c8003000107459281d4941d02921039840054505410501d445400440310b100030078000c6d46003441c1c410300c00c5040741d00c62100c4134100120784280000490084d00040701000c02c3e4507001d800c800d4050a08806184030758802d84000c0f1b06500c000500c00c06980f002c0d032000c01000e0052026451800d000455a410355205a8621103c8410200100e82a621681c0080c4d00741d403030840c0c10560001d064220724072500110040310304400320700482d451810728140f110405074000b030b8801e211561003078000717240104585100c1c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 109673624 1250 109672374 109672379
    0xc0106030b0f0a110f0409021b011b02010b0f01050301090e03040e190c080705070f02011b150c0503060102071403010b04180303050705090d15090b0906040311010603080405090709 79
    0x810a030301030300e10641c08400c00080102030f600501458008011522110b42000e202c2030781142c0e140140d000d034518098000c901c908040c4040744d03207031040900719070090168640520078600c3e90384100002d44010350070451103c0d400e0070310144c421a0000180d5402e440c4da03180c801204010f06a2141c1449903001c00c2000044015820744841e00455000f1136a40c01d0104111922040b10340c286100d00500200c01c1c01c0201d015080400d484829800115030140300c0c26900c0102e4035110403010a11414589512900a00c82c1e543e8182c0520510b2030400c21418102c40c030155400c0c002200d500d40180d0010700180b28030b4100c0701c04aa01c0c0d0402600120740c40d0f506c10000f070103559a0185407d607400c003041e030800078581d00d4081d10307070410840e0405070314040d207620110706803041e00b41011340f1820b030301400c1030030090341c0d80d001d42510b981012255032142000c1e01115115901a10164000303451080c280c08030100611a210071260700c41c0082e0304d072030320f0b250034050100001006c40d014001c6101e0300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 109674874 1250 109673624 109673633
    0xa0b131d0a0302030307110120210c09030f06040b06011b020a0b03240102030405150708030903030910050c0307030902030c031b240703030203100b040b04060f0305070906050c010603 80
    0x6403001e0354800e030042c50301d038034028000501011400b40041c000d0382c14070590910000c0303440c0d201011420340e0903007282c2d42c1050010500048040c00c180303803e030003210b40c10030031200c2c1e004000e851341010440c143c4e00220500600c0c1503036040251006080171104501080080d8001d425090342d8a085445420103e070003600041d01c1e5125550114111801c00410000a4492031002c0c58524044102d145c42c10448480000e650380280d0180d5401525815040425101c0e83c40a4403403043c0d1111103241d0380d1800200a90b10781c0c1094404885520980d40c200c164400c4901846104a00007845182545c1d619501103001d000701940507600340c00b60710b0364070f2050b407000d000008502c80c0401d000d03134055403048180300c5d040886c6c03c00b40c070100182030400d29644040324103d507104c3e5014580542c492311800741c4071048140591000f40760480020300002c5e815800f002401c101d604540fa100d605440d80c17078059054800441d50000001c0b6044414089540110090000e200072003000242c00c0c1d8580e0340b0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 109676124 1250 109674874 109674883
    0xf1e0306020d090209060d050601091508011b0e0603070c0f060e0a0f2009010b0f090d06060509010e04080703120f02070605010f06110601061d09130b0a0b131d 70
    0x104602e800780c40e5450f020542c180000080d8104000f520048000d8080380c0390f040d20360006001c3d24072407648540c005400f15415100001c0074010321402008502681102c4100d5412006c5a0700d0200b10154500c058510b01072090301c2c4241c1c0d56841d012002d151568035080380540b034440490794145c0d2080e0710000618204010f01e0958450a1f0180e5040c0d41ea040c040030a100d60341400403203015010492103540c4400c0707100d40c110391441b404503442d0b0824111000481c0503400c1c802c3c1d0020340d9030900e50180f0100e070b00810111503050720500c0850340c0b20813902130b54202c1158054402c0741c003040000b0020740309081e0500b484d1003440001451418503503800d010f0360712594080c0d403070b9070b01e0b0401406422202c403001c00040106040ca0200c00414000a0f916840141300314018480c0043d0075510369601808449010103004140605074644481094a00c848040080d1011103501d0f000540f001e10920030805200300091441c21141d242810a40c0031b00b2241000d90030504840000c6c0c0c414000410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 109677374 1250 109676124 109676137
    0x2030f0406030e010f05060d02091308210115050711010c0c08100b0405070206060108070e041407021c05030627090309010f03020a0c0f060915020a020c06040f1e030602 74
    0x10b81c08250300c4481e60810342035615814400c00782034501303000d002450303642d070840180080c0e040d181100c00380e0b18450380d0085030070303460b0010b4410400007404404040340d2000c03214800d603442c0000801030741c85074580d42c0001c6560554074081441000b850340412003849044052040c14503015120100d0340d1748074200c1d072000781c0c00011580d02c42524110703100f0940c01020941d00095504008510300004e00940e22980540090306011042001c58a5148502410f0002090160042c4588507941420840c1003000300d4070400140180e9204d0702c427240222440382c980c148240d845a045488a070f08000801c0c5003503642c2484510342d0010710b4071110074a100726100d01c504001458817640b8010024110269242d05642014410001c3d20820340d04418511715064202d103108030314501629007035005028042d00582143e2000d010a203100c0c0b8190003d00c41d0031116400c0d5440010060184000c1d80038074043c1d11000407168100303014200c008130921120f40542400c0711a0150740740ca41e00308a03070290 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 109678624 1250 109677374 109677377
    0x3050c191125050f03032106040501080619020a180e01091d030a080402280f050409150e01061d010302011806080414070f0609080105011e140102030f0406 68
    0x1c0d40d0420442040c8000811006080c082c1102c0080e221040c5502c180b06001c0c19100c0c07074803d400b01c25103850400a4030240034080e0340a000000d01c81c0e43c0603030400c808650356440756007072000100b00d81c0d0b404281180248a07c0c0280ca400c0d991800600d0042d4100d40c80c100200710701404180e10a02423222640001c1c4070318180480b083d4101341642050b02c40c1e4100741e0b0b040c030a03500c1141d0103080000003160290101c52502c0d0a9170b4071644001610500e825107040380c9118030081e06020025809525011166252a80f400b25940c540600043e5200c02c4409800c001840c0300344e07403140046401c2114440211701c000a412526240d1584407083c1044240b03030740241041c01030045507000711a0780c030b02c040c0c240e07044420302d031814100a108040080c00201040d00d02500390403141c20410600300540118120f1150031912114010000c0703090b407260003441e42c280710000620b5002c0905030341e03140640c907112240c00c074105140d070240650003004250440c8010409481a051010003420140255 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 109679874 1250 109678624 109678637
    0x7060b1f0c06050a0603030c0f022706010e09060a0303030b060906040602030d06090605090a0b0f0303040909031e0e0d030203070605070c0201030b03070f060c0501020c030307020a021801140103050c19 88
    0x2070802c48100e0301e000380400343d00c900e841014030100e80c0205801c511540c0c09605101e90030307407500c086441021407003150390742d00ca0960710b81103000501d0b0f180c4601c01c035002e03070311010118103080401200541c190780c402d810690110b42400420700c203030018030b4043d001810941c43d100d0780f07201180980d0b002d58001e80040e00b004c030303c218a040213409000014144028180310040c10000083d1850720040c0c0030440482c1d0750300f481681e540310b444140c4060003004042d43d4580d65904002005440800c90403030000e0070340d607189448a000009106881c44a541c0e5001620320b008043c8008403040d001d0035019440203000c0700e00000c00501400384603a015940f0010606554400541940c40c8001074034840c0d000150280044640c0500460480f10149080c036281ca0041c1001030085c811260003000c2c9010001c01c10480580006080418510a03940b0224400002c008421801c3c420f004000b207032031452085070311350b600caa00401d40001c41191202d147c0110940300f6544900070107883c0340031882 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 109681124 1250 109679874 109679897
    0x1506070507080610031a040302030a120b040603030509040606030216030804050a0f050c010923061b1204030201110d05030610050408150106023a050408030412121407060b1f 76
    0x48100b8080c0400c03986e580700a6090510790740107500d034040c103603002c8200f00c45a0340061240405030407000e141c20010f04100051500ea0800510560040309558055401c4c2800001e1070791091003150a8000e0b0404145044003280d5004c90b00100060b1080d1071b1886202d90a034086100020250000ea11600007800c00041d84800901383c005158084880c0c0314410420050304404101007403180c020440300c955444017080d0704c242d160300f05040c541c4d94a11645c180441c0c3d80310348400400640707000747c0b1a800d0100350a184181c1d100e289210000c0050703000e002181480c180065013074072914203420000d091507220540d807890324020540c2c1202600860300100600c0ea014072945083c0032424880b9021160741d200380b00c80305207001c40643d0a654007011070000070b40c840e10940b4080e10192065a60f1103960711240740ca014800d840c2a1420b150225080c00c03103034007444045103403680020056081108a480d000002c4c8140310f08250001591003004034000c0078140007518070501034803844175094 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 109682374 1250 109681124 109681133
    0x909011d0c0406120f12180e061201020f19140c0d030e0d17060d3503010f0e040c0512010e010e01060303021e011e0b0117150607050708061003 63
    0x510b2540809840c0f075002200ba00425a201600717260150080b0407040d18030b00c16041100c546015003182074903880d030301f5000714001094800850141c07030212400e101091101c1401802c03442126410030626030100100746500070380042c0350440b80300c6030070a210400c07564100510590301400040340c69802211856030801c2e0140314150304c0d400036100030001c0c0c1d50b151a001e0400b503402e0510307504c00b0701d941c000186240d0700c0a0782901019404807100e03000d6108031601280540e6080d1400f10041745220b0450000500321090b039040303814840c58040d0301807078043c007000380c1348000d4401c3e036030b0003030000c1b001c1200e8844c015880308160002c40005500d2061039489400c54481042048807641892010001309600085440d42c0002f08107034107071100340e10303030040d0300518203007030b034823103d42c3d02d0184200c40881c2039802a043c00c6403c0e00c0d003040d0505604a042580d0a04130f07490328000f042d07400404000c3c1824805410858030541c100c0c0c019648aa0046290480c1151649000c4205030000d00411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 109683624 1250 109682374 109682381
    0x1f05040207150515241b0105071205070207050f030a0506040813080304030c0b09010c050f0c10020607090311010201060f170c010c03050f160803040c0e010503070302030a020909011d0c04 82
    0x2c18403c2078596804642400100c1c0020403600345c07011000d5040182c0b9620f4480d800b20b0342842494401c0c406e00420b1000307084d000e0501100d409002c070b0391191200203a1800c7c1e0040310711400255000c0c1162900f0710b0304115040268040a64062140d2440e050009408000300e03030080703000707801ca00d0300c5590301040707860703400d00a40149100c0e8100340010000540100003607800e645c19080d60584803494803004881e4070610810180042c4030f4160b01504860000c03a00c1c42041205840140340c10955020681e640d800507211500001c45444080011940c8000c4604c04034205100104400360b450303000000c1d08480303801c2012050b80004048041e641c0c1040142c0420b10282031140d01040039440c05882402070303e00e44203400100081203d0344119810340b11042a40c4480da55840341040d090103003043e034880c01410a901c4004001040d20f180006140044990043c01020135200540c00c0c0801c4603005860410380d5905e40070100000482400d40f0342c503a0302d941000f084620406030410003034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 109684874 1250 109683624 109683631
    0x30b010219240212151c08030a240e06060901020c010809010e150118090f0f0204090204060308191107090f02040504020403080a0212040b030109090c0b13030c0f0803031f050402071505 81
    0x10f495400d141c1c841095081b80e0071540d0325000024541c0301c0d0384800300b000c081c000c44045030710707001102c1034060407a00c030750480c1c4c2007517035204d82c0c1141c11030f0b071b0f4541480003520540003294007590002c90007503602d610030200c182e070012401c40085401306607403941500d8004102100342d078209001c0010700c0b513600e0013514a40c188079180428441c1c04010303107a09108214100c000b030f00c00724181a214085d9162a00b01c00041da034042d1003002510b6803810008850380214402030300943d080c030030f0204698490709042c0020200c00000d40349491425901000074400d58142c254410380a120001d039a603200c4c8044d01c01103010b11421683d03101e400c800282030241e4804c40d07500c000d1051005202d9112408180c03415241c0e0304000040005050500c10b41c4c504d060341c0003050004001619400c0780e103c240100d0b04480c440c0320181d0032691124007000c08008140248a0701d9402400050125418540444420103200c06104039042d02d82d0040740590b4440d01040d22041007025490850010501c5030a90 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 109686124 1250 109684874 109684879
    0x51e01061d041a060703050c030307030506121f0f090c060207171204170a020d110a0e0912090a03210f081b0c03091f030b01021924021215 61
    0x740c140c224850b4045401c814a004d00030600401c2c41010580140215064a41c6c82c1e42101d0701d0b0328000d24000c016103009c4030494040c01d5120300044040304001500d070700000d400401030010306c0d50320440000070020540350000182c0c0f144071940109414080c04c0d00540b42c154080c010b034078140390310300117101045480c80c525580f000c0761944c00007020400787c90560b152140003030f0301c44586482c5507142c4803240341301940c804a401e54100800440c01c0000542090175150190300c140c1c0ca203900348541100302d404480c00e4001344002d511850462004040d071000080000c2071080d01da4a60105240b154000341e040d00240410381d1011680015496400040071310b0711640074500081c1c1a55204d10410b130f0200c0030080440c80310402c1505100342c0704c0903a8094101c21200d541c4840c044402c03c0f03c0181040860b250480f000c04c03035440032524040213500c1c0c020307513001c0d25a03541c0c030300b140c503103420003a070409011800d09401c409025000500400074090344003a51400c00d50804000b005030401c0240c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 109687374 1250 109686124 109686131
    0x9050709031703130614010f05030106030206030c0c07080d020d0207150c03030c03061502031b0102071a0408070609080c010b03030301050109030b06060c030a020d080f0609010504051e01061d04 85
    0x18040ca0842c011041030041440c3d100e071221061030b81c0c2100300d58070040a0a04001e1111002d0001c91100c50484a43c00e01c0c1b02e4000350380d0000d2600300c03900d034040a0b41041c1c003000041c0c6101c04000c01000c07036040c282d0031105403035940c0c0c1c40c2a0030f0034180c8802400681100c420348940b5981000724001800080c038a03000c01e42d0804601401100b038100c0001c00f455204d62170016a24040d902c03200041c04503100d148018640701c90000e40302c1e80010003a0501c3c0c1040d0b400e50100388414801d544d840c40d8040c84502c51094a40e0038228503c1c0020b0040302c0440c020094900058002d02641c0c1c5100e1084905a4545400ea1641c90a40b181600e8980c0617a0040c001007100760781c000d040303504503504406216800e0720341c0703000f08103d446040000c41c100e100004400140960005050080c0340e02d9547d448100e481d02d00c4060500b2509441c030540c07120000f0700510041c90542d000340e8005000408031115060651040d03101d2407424dd00081c0030528048141000390507001807a07410355012036041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 109688624 1250 109687374 109687379
    0xd0221070e0a0c0e0415080d050901122d0b0d031110090b0a020702030c060708030f0106090b04060f0c060f0f0e01021611011b050105070906021507080a090c0b0409050709 75
    0x1400081c036100068416034441c2000d44c00006d542c400d9401805034001516942885030b02c010380580e00000d82c4074005401813420010005861040310306120210071045a201d440040c107240300b510020b1028000360352241401003582d914400301d900b161080c1c54600d6030070020144182888003006413203115a040c400c010001070b02c968030007940043c1203c0010b0b150b14650010926100c5080c2c10701e90415400500182803244d1100135511807014040460043d0380c81da00203c1e501250343c4a5901d1003101404180300c000e01070722031559030815602d448055a5025201d00d03080c0d402981d400d210540d62142c981500c01307854001d0070100300f4200000d43c5091982407009155180150014002c2c410a50075510b642c4c1c4180344400d03182c5841d11184001c0c072402e041c035500816040e580e0102041e850000040c901d030011600704c00d40031100403814240d58500c001514441002000d001c0c2d0303195a44045000110140096030140014100f81d644660604104408032000030f01104203221802104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 109689874 1250 109688624 109688627
    0x1b0c030804080d061d0402030120091014130801061401090e0a0b09090105070314070507060c0909020a020a050114010b0f0708120a05042105090d0221070e0a0c 70
    0x290415801460b082d0f40b030b900160604000c0100f074000d103500d1012611042d03454403022070824000d0380214000c000c000c0e07114034503032032036074110862409401003403142e01e0403464910341120012280307080003a04150200b07601e10340383c0c2c00f581c120004000ea0b1601803000301401d20500001e000e084c5142c50080d017040001826468151094206070801e41000614060990300403081140c405004003105082035501c00d4060601292070f200080e01d0b04003600e004012117406980542c010381c5505241c02100e88525002d0011024244180b1000d0781000850300c45a00c0280f240000c0c03640904a01c0c00189025170a6440003c00116004142001808904002e030101c4840c003540b00d000a0f0b8541003031518a01c80e0140800b100803000413881004020300e944e8018500c214464003001041e01040308807183d1614259281d503000900600502d501c81c107000f20402c40c200d000820030741454606203510031024282c20200a036035040301c1030030084c1803881d4445c5070b0496144d0b0407c2c002c0d041c40010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 109691124 1250 109689874 109689887
    0xd0506090f0f0c0613030203070b030a0f0b0d030302071403220801060f05190315020403030206070305040503030604110f0304030302040609090e0c010f0c05100204080f0624180108011b0c03 83
    0x1083e9100d45400140e026161140210400c01164043c0c1900d0b805039540030725010310b800807034184d4155810131892010b50a0188518004814010f204901010203a10200c00a4000c000c04030b600b40507034001c116220100704041e00d2040d031030554104030808112015419009141e002d08404e80c100381043c403102083d546443c003900c1c4280c8106d4040011640d8101407003800354400742c08007001c1030302c0020450141e0000c2083ea80a6021241175885d840d90840840d6130031100600241c0089c070102e42d05203007981040c1000d4040040647c2820f00104002d40c00780e0080e1011404654002030400c000c54000c410f110040c07403403aa08200760540300600c1916510351320480350400c10a10700d100380007030254031103454858212045490b00311401d5141d074000c0d4010301601025104889010b01206800141207210701c416108580c541e64101058682c501d03c501d4010354007000340c68102050707040004205000700302d0200042030340c0d00700102d040004044020b08a0402c4041014031001ca40c1085 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 109692374 1250 109691124 109691143
    0x3150108060615040b0c010c030e03280201020d0f0203060a050109030807110d050d120f090c090b0f031606140c0c0d020a1505030a061d0a0908090d0506090f0f 70
    0x36590720003043c1028200c1a94030a6400040610790041403817481d61005500c00c85503810162070800c03202e003108032403641d82d01940c0350510740c2d21809090340d00041e81282d00d540e61550240000340c02c0c81c03004414001a1203801c1c003042000c030390110800c80140740001c006401001d0a00303190041a045480b00c10741351040040c007500101c0c40c2e050100c925120795105580c10382e006000d6420400e0300f035030004c003d034003000b08600c003442c1014505001120548262030009500004074110186000e11880141c88080c844035806201604050703000e40b002c0c851410801d20100b05034800c0b40c200310300502100080090b0303990b40c450a002c80c0c04191000104c44014900440300003094010920000e10800b2842e0450b5155000c0d40400d49125034000024500500c1401024040380ba1101e801100f210341d290b84034050341407100d010034043e00465110403d0103009201484c42c0074240300c007044c84210000f100b21800e070b200700704100c10f0030001e001800700b104040c0003078014035000c0c8104503500e06004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 109693624 1250 109692374 109692379
    0x320010912030c05070e0405010e07050906060417100203160206090610050103050414030f0d23040201080c0708040b090111010501231215040302070936050106080606031501080606 79
    0x101c90303c000e10200308a40001000b03c01042a070610386032810074003a2000140200c8184600e40c8042010710300500c01300c0c4a602c024020905040c03421906100c03020030340b00d0b121028002c1d0020303000c401001d400110710a6003180c4000e61040e41892009190000040c100c0b06184c01c000c0500c810040000182c0e0116a401d10b0085034640726421b1443d81512908941b181922001803100d1490070060050031100c08901c04c100046010420000070304030491406034902e00340c00c6e0000e001507010b040c0954206041200d440d04214541e43c42e803100342d0094001c8a032803440410301503010741c1d02c212502c0d61081200c0090209514041042072480c0e003000b8900100c0084580f60380e0b642d2207800750b0008580c811812551007004400c0001500107044c0c4095006000d041d00208990845008950b5510a020614503000b20408a802c0c2207058851040e40700780030780c1c3c020700003041d824043c0e131000d0000e480241017141444410946000b00210060505204403001082040784c04a8281c1e8480801e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 109694874 1250 109693624 109693637
    0x60608010e0403050909150109050d02030304061b060608030d05130f1101051215090105180703020a11030d1d0f060406050405010605030609030d0c090e0402010c1b032001091203 78
    0x1e43c58103071014000c50300f078103400071403020411074441d958940c100324151007a00c2c4d40b43c1031610b0b1014481c510558000c007030f4040d4030800c000c0003a14480c02440c0301c88005203c191100c55101d80d681d0342600c6071076200c00303240d82c4041001c0d030b5130b40d840d171160941045210703c1c054010a0590390f4041c06c460544000b9111200550a9100c140d00134021a4814401e4030415281840d0000c0e0700030240c00c030000c58a0059080300004213640c01c0000e000c00a42c007a00303c04c80e00c10707919032074210f000e94426092041008003040b084140c043e0200050030b0745004d614400704e03282c0c46610fa9880f88190b2800c103104a50711208480500b10f4011804540090b044040400c0c581d07a81e04000740074020700c1d030140d60544980c1c0104820514044090100003020300c000340004044603008a44110240c0a006110440040420b00641c00384031201c500038810701009001202400300c4003841c1e80355510a0314104c4c0322000c2140945001e900120510381c0c24209046d61500300117000c180c802e0940801004c1c04507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 109696124 1250 109694874 109694881
    0xc03030f0f09061d0a091401031205070c1a0910020102030702010506150906130f03030f020d23090d05010e07050301060f030308131e061e0606050f1b07060c1401060608010e 76
    0x8462040d1740c040c08808401340045040303101c5c5004240402d10055540c607500740811200301d44500101c6642c960400e0a4514503414296007400d4000c05160340c400140041000d691140c603022500d49039016103400040c0c50740303403210001e402c6d030364014140e074400c06000d0710362103082a001d41601d150f16000d642494561442e1400a101c954041c4c11802e040301640381d0020030035a00000f0350417100e28907803c0c2e90005243d584240c1d0306a10070840110030304002c40300070761411119800340c010b440c4028030340201c40c292915240c0c21a211034046184541121005004905003409032400038034002c034543c44e04d5451610f00808905000d02800c08164400d19503400b402501880407125180080a06509000314902100200648841034400e13101c1030038850070758420f80c800e140c21941c1e03d807102d074500740e0b0484203264035510282c0b8030b4104840705d042c0138030340f445c080114001504840c1c031156905201410504c84102151041c0006607041c07030030911086a0145416044900b2a40851807645 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 109697374 1250 109696124 109696129
    0x210110309060d09021e0d0b060d0b09060924070302090a030602030708180105090d03150806130605180d03020702040e060f0a05010518040b04030c0c03030f0f09061d 73
    0x480c441c03035198003080100d80c20384200381c0c070707032088020501c204da88900951440084000910344039881a60100301720114002250f14003900507030042c030003480411b410f049681c071003060000c203480c1c03800d499002c20200101204100044078281c2c04005c5030055030100c0000319555203000902c1d6104054000c140c0c0890703500d8003040040230316400300d0150f4513031504400c024103ca0b41124004010030081001c0070fa1071006205540c09140d02802a1100e2405114190041e0425400c40c1000024100d0300280c1344505100300b5003d0744000e4241d2020000c0d81c20240c090b02c0c800b03004840c0c05003210000401c0c0c04000540c000442c0801e040242c1c50707404038000207000b88000c0c2903514a40c01180e0070000a400045641446449004000c00040e40c903038080c80f00b0407400c044d150780d42c48001000b20380420081d4640c254082e10901d00094107041503522041c072031103181c0c0103e000c00c2080803004003150f0085c900030030411240c9416a58246044802071028801300b4962100c0c01d40d481da129840d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 109698624 1250 109697374 109697377
    0xf020a030f0305090f0a0e040f0201050c2b030213060f0207170a05100509030d02070507052206060309020d060905070515070302060108070323031207050d0e0a02101103 74
    0x940d04121105095400c5040c0034090f54000c0c42030501c03c04640784c0181e991b1401c400d03038206803001128402119580c586d103003000c1071601c01e016814480c050092125a100410540d04650214000720501c1c00c1014005140300000101c0c401c02d142c0140402d020305800c0121b40350884001d0724007107400e440820021fa00b0840690400340100d11900042e0b014007900240034403030988101d040307903044070007000c443d403c1324420b0303d119055070001c0101c01312880140e0060b256003401501921055661900003d981100400e403c1381c1590007080c0204481d8003d12645000700514282809045c01c2640054594a8501c000034240c50342c0308600030502034100100c1c00070f402d01400c0d10b14804004506103959401c03518044006125401c00803da4807000b007140c5003280e030300040010700d2303105c4400140c10618000c040e0050f144000d025098180c1550307880b1502651032615019641e900c0c244050041c3da1038442c0d0303a81650f000b1200c0e8001a242c601d255040c03411149840ba0b5900c0d0b040203003e085 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 109699874 1250 109698624 109698629
    0x2e02280b041b030c1404060b03060f0102160305011e020705070501081509070203040503010c2c01050f0f03040c05030a0213020d1d060f071d01030c09121109090109020303070f020a 79
    0x1100c0c0402c000c410080100c00e5002640c600d4100003a080d8070f41c60030442030f10300d41d02840203000c1d0700340003141e03260501822188844505005942d003c40302070328001545071440e8000da490360344941c90b6400d090f4003030013080c0d401c10309510300750b03e021a6a00d982c0d54401441c4901e0b410048000c00042c030842c0005503401500d00000c00b004c20b039040580b0002d681c3e80140c001c40340301c2c0d464501204030450050610b040d103258482c0c0c0c2c288250380d624001000c15005198443e0600504004180c00c50107250010711031868a41c0c03545840f8249814001501411504000c0c0207074010150103001da543e400390f031207415550000160f43c81a084640300301a18020720308071136005003404150201d240121b502da102d00460b6040c580e084e0782c2e260048654000c4186150031000003818009119440798115a49625403030528005031139031a0b030360240b030200c11001518094800790314100d0310310700042c0719508282044028000700041e130b0000fa480340300740800100300c00414042c0804545454050200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 109701124 1250 109699874 109699913
    0x30c0210090e101202060702010302070503030703020408010c0f122d0f0b010c0b07032004031b0e100b07050709090503030106110d1403062e02280b04 66
    0x511520064074080090081c1040500c0007000180f40c0c903071406484045802001410009000d0780e001c5c0304a0342e11107003090307042680030403800d00800c00820046025000603500140d54078079001c1d0460131a01d6054142081003400702c1d0546a0740e90241c2110041d110801000840000d04100204403000560344954411100d11040d040103260342d0244902018200f400e012160500d00119401c80540c5001041800000082004c4e1840b070b074060103074040848000890f910120b1801501d0b17170400d83c02180d44004c081d00c1803d80203260306900000b007105015a20b0b803805c0107040c000210425011b840c604203000300d41c5106101c0c04100324001040841d504112522981c10301c65105d074024000c4c0408141d440c1a8a40001000549030b81a08484d13a6032048464104605031000e83c0040c20f503a51158103004550388420003503a0004800280c08203500c02a03215200180c1494607004611201001c20f40d480c071101d40032045411422548001540b0807503030307245440005c1c140c0300742a511 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 109702374 1250 109701124 109701139
    0x12120f12050a150f0b070b040f0215030601020f01060b04050609040605090a050402030708061e04051c0203130602060c18030a06020d0501030b0906090a02040b010203120f1602030a080f04030c02 85
    0x541d6141d920001d024503c0c0600c2009003900c0303034030351004118039128804000f0410050000480c500c2982c4070f4000c0d1040c0d504072101401600040c1103501d200207440e40c08000007040c0140c66030100028001000c3d800c001340070652078002c2007203460240c3d01c0b03400d0241200090300c0d5030a40c0c4a41c4810042c000c000c00c90a20303810942d4040e0300804048130100c1c040d20074040007203074120000410611526003108c20390b8201c541d1004107115500701620840c1c2070312070360640e2640014010401060205654010360729964494400400e4181550004080d50015828440300700b00c0300c0100d5000c141f64411981034680d003000400e02c0c01e03140100c0501030510100d10410300101a400c858101d03800398080302c1c12920342c02c007101d807208070130384440c159940034030b1071140181083d8001e800c5d60041401640e04181c000074000920610403200b610b4103104420800618902d200200700c00005980300031400d0102c0e030400030389412000f6040c82e00c1d0140700c100003420980f14001c0d441121b5030242030705 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 109703624 1250 109702374 109702381
    0xe0f13050c030105120a0803010504020d0603050a0f0510150308030c130f0602010b0f060315060d0c0201020c2107030e060d020d0b030606120d030914010c110712120f1205 75
    0x1c1129400130301840d440307111105680050ba10707001a10301c41042e008543d9a142d0303441d002c20031000b5070041003000f502d65240c1e0300000100301c0c14400081d04078054429503481e03040920b482030904a0707204984500520704400245000d20030003160054a034004800b40d40c070749403400f006002c2d01403800d007030612919021001c500d0b141d40c200704074116102074000340308003403c2c0740400009809594402e5000b420901c001189400303030102101c21600b0142080f03240001001030700c420b031940464118050b1790009092401c904042280d650700207890488038407840c0d981202c104040c80b4480015080009980007089c0e2591072030b00700da075040382445046640b0307003007610550040e2441d801054840d009400c00101d030b0341496401d20a0401d003042c0600030140884d201a0011301c00741806a401c101d00f03442d8810010024440e28007180401e4403000402440b101d900c1d4500070b081e40000e55803c003000c41c0c007030028946c0007940d00018540d00780782e0740340c1c0f00c2c90b07800315072001011074103100c03660901050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 109704874 1250 109703624 109703641
    0x105070807051903090b0a0c060914031813020405030604080c25060806031f1104050607050601050a06020109050c0405060d1704051507021509130f050105011e0e0f1305 74
    0x5901c1e21846070725a105c0007596901c0710b00c4d15028034a584c8010844810006000904a03070010341c0d031134812080125010b045018840c61900701c9407259440c40340942ca501079510f45071a11100c034150106040d490942050007182e101c40d0007800007040c160300401ca40040709018410b5840340d66031a0081100c04001440c5003103068458403895001c40e41b140d01182c01800c5c041849160049134914440d403505000b40003c1c02801e00d00201003207910184000b1800c1c1c0d031440c000740b90b000e000d10004c0c00c0ea9414042000700407903030b541c480403d6a00d051100000604c1c0841d000311107400494000507280c1d10940410346c00f0404250041c0024900c0140c4801c2070340e424040c0003542c00640b0f401d081001141d554601d98072070048081d46c0050029150251402c6060003490541c07005091a100c0d0a02c43c100310742030381c3c01c107512500c00700d48074401440345581c0b14030219a078049415003003945140d44080038020001061903d40114072881000c0c26545600c540e03095054100c1600300300a1601038038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 109706124 1250 109704874 109704913
    0x50304120f06140f01030312020d1a01080f041a10030602030702100605010203070c03080315060708180d08090111120c150705040308030a0506040b060408060a05160905010507080705 80
    0x400316020761803c80074076034100c503030010244103400303104d03041c1016401c50f01c041d55110030318407020401540810055000f040707240511105205d001000792540c03007450340054403104d0014a460048401740c001c11012075001c3c1d0003200500b6042070304d102d058685a0781c0d190800a16040070340481d0002081c0b1442c41d0740002c500402d41000303a030070451251588012601c0c1c0c403c240000d0581c080003201440480c00b000000c581003030819003607038003c081d01c40c0458035503008154252201880800c40034072950b09010140d080d900b04690010b24035030030342c0c1c654103240196821541008042c003101c02410701d0400c403149071858615161034489503c01a6903565205840002c0d0700715003940c0101d034900e405401502c050340c0d480741c1c0c00c0d41590b90f1001b0440041200802d401e0340305031030303141c1c940168846000034000b40600c1800b904407451b003084440d041d2040a001d2100851040009020150780201080e0a8990910306980d96450508001040d4056164040c1c040c1c0600450309414004600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 109707374 1250 109706124 109706153
    0x816031e051801030e0f06010803030906060d030912022d01030b040203070905090403022514030705010504050f041506020304033f050c0111180307080304090905030412 74
    0xd203030324120000c020308031418015007648002541444400001d0703980213802c0800510146000c035061010f55002c1e141c5009000e0380326080c50340001043c45003030007082c003519030703c50400d8400122000155500805001c1c0a201d41640c000c20b62403e00c0c00c664034880e41940b16242c4408523a43c160394501208005415601158042861b251841400f400c040c004e581c41010a034036555a00c91600052000f80500181304400f140100120300c00f61031480440186003482c0c003030404048038144007a0b840300418140340d02d4801c0e4030a00013000560790060440d010382c0c40175902d4210503038024001c2000b0713041c6800b000030200352641010885136400406441103a00800c03425030580d80c0441c401008143c60420780c222250034904000c0c0000304400c0c10a048650352400c5841e141c1030255150858040003040c0076206c400041d04660b0f2502c1200d005c0001d803040300900a11482c01107415030300d1059104035015580c44d40642e04c1403100601c240da0040c2064030050280b54114940403201c003002d907 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 109708624 1250 109707374 109707407
    0x91d0601050304140a08090a0603050408041412060c0a0e030a200a09020c030c0d180302010305060f060315030c10050412050a020a0f05090a0522051006060503010503060c090d0f081603 81
    0x12310001140b42c0300b80145400780b500549100e28143c1403440c0d66014005507583e03541c10103aa040f82c000c1040007003003c0b07403151035114201c03038848481000040c4040b9000400364880d500c8040142c01140042e40c079444903540407842407045200d488089411400309034000a04240701043c04400a00080000d0920480d80c1041d241540c0405c04103881c190050f4515000941400d401400194000d5101c55003141004001c08400703200c900008009520440b00703040900c1c10300ea41c223042030608201010a641e406c44111601301110701008001d0301642c400c4072101d680e800096000e200e001c0c0400e041682c3c0241c90000e40c551242d170301d07400103101441418020b401040014424048a100303203130186840019652000c4039115a18800415104043d40c8a00a244170a92030b40c0361845068003d04190719a00e0302c0398501001c15007461401400740d42c14800c20440840141d0b1154803011141e0342c860700c40414483c0070f0402e00185c2c000e4142d0b58400502801c103442c00d05400413140598407046 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 109709874 1250 109708624 109708639
    0x20601080f011b08041a150901170a020d0206070209010e010e09070302150901181203081006020c060d091506080c01090e01091a040501060807091d0601050304140a0809 74
    0x4030340366282200d0610360306000c08059000000d011501c604c070103d40141c010712030264000791904641c61480300c02d1b1a102035250706104003511354100034248500400703071405e400c2d20340c1c45003a000c192a02c0d000e040003485041c010510508654560090f6070700941c020380302d00110343e114401912850030038042c041850f89071500090f0700040006280081d240d002d40035800399000c0001c030340500e803c05610b05051140351150f0380400b00003152408020044170340101410410781c240036040c25006400380d0840b184c9030400303006d207540020340c0f0a1084419030b20309680300b84030040f080051080b00300040444d9444901089519003540000040e541c4410540e0003020801d030055501080c180700f4044444950310040014481b01c0e408940030003e001109103d400c41c01e00054201c5900340c1001c00072420a03001c1c014040d51080d001d10150101c40c0344219945c0c54810121401700740100014100320000001a00b004031492900340030200c1e0400301c60b2000d94070300d01910181c00290300d850003000c6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 109711124 1250 109709874 109709893
    0x60906060608151003020a110a060203060f061305091906030507030c050316090f02040b070f030809030a0c06110918070f020c090612010605090a090209010b0f030609091c02060108 79
    0x10083c03654200342c401482015800305400c003d81c044c6d0809142e02003403001451016140050500888200d684503080060fa80e207405d80420181204a85175140100703c06e204c1c04248050511510003502c5048a00403200e503168100481040450485540380c3c0c1d05040c0c000040000004810302641c0c030803401c103880707d034494050556480c0c010003500d643c0c4548000c2003107000030759440f1f042071700210320300540350948030780b8695209d610000044511014000e828024194007085039a046400c03400590f150581c0024002c1948200100c09466690b8a460342c15040c3d2000e4215012520041c00c0504c4004940a0400420004a5413a008a0904007040481620105000000420040021b003041c2c8904080c02400c070050160444299699600410243c0d80c4008c040d20500440001007000c020700e03c184074080c401030384042c4a1000030f00c4035406d20140c4109999004400b520300500b5540c078861030b40c6c034065400305180310341d903a0301341580040c030350200f0030905032460401107030042c08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 109712230 1106 109711124 109711141
    0x30f180f0a0813090b1e01050712031b08061008090a060212040c0b030c03010306020c07051e011d0d0b040606080303070c150c09090b0a03060906060608 67
    0x40d002c20003c801840000400014250903c801c1c0714981032800418681c50f140042c80210500000810295034462401d48404603000940b810b4040603444024004103001f010800304105000204e00d032a0b4000e802c00c0780900d001802c00785090403140021a51444040c01c108282c1c000e2000180100703c03240040e010045400c020049c840c10f0521b00308404040c03540c0443d416100a10401c0100340d164026281102e03000b880159a440324100d1482c208403258008940c000d0303d040c4480010704400301151030b6003d007a02c0d80d0859505000704000e4100c141c03082950b00070152014140015100f03409190400e02c2018041b50550b20740701c074542541c2007165400700050f0b05465200921500002c5404c030f62503801c404200c01c43d04a0401440508680a5140140d40301e035041c8085440314a8400010344d04418108803003042c500c0d01201410b843d119100025412002003604c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 109532374 109712230 := by
  have h0 := BRFrame.cov_init 109532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 109532374 ≤ n) (h2 : n < 109712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
