-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3056
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:31:59.785917+00:00
-- url     : https://prove2.me/submissions/c33f99d1-b1a0-413b-8a0b-0ddf6d940b06

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 549460431 ≤ n < 549640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 549461681 1250 549460431 549460447
    0x11070902070201120204060e060c10050f06100809280f0b190603020607020103180b010b041a0c0705150d1a01030605030c2b0503072a0e0106050d060506 67
    0x1503401881c5641c000d0325050050009802548144d00c264010707400007800d054005807030f81c01d00070094a50102c454058800382200f0b0300c0c0c40022500700321103005080950780706000590034000040401c043c071038603152406151040300d284e40e4400350280004204010f0047c0e20744006036030140c900442e4408401040d00c406406c04018081046d10210013129981c1ca95030001c0185104540440340e01a280c40d0510507541c00640007460012940d88482d004030110000280100100a020f0128508000e031213a0824412489621410f05680300f0303030700c08210889090000103401e0044410448030307142840c0b0402c00e0183c107401060031549095040c4034006840e010310340e049000c064406c0e41c081200303540d1101050ba40f1802100b2440d00101707180a0011001c0c075040000c540141000c00d40e010390764003581d505295501c5500c1c01e503801e071005104e101c00044d040e4441d15141d58900041612030b820804482610141849240148200000ea810072440290030410040100078980c503110010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 549462931 1250 549461681 549461699
    0x81008120a030e151321020624010504051002010e060a14070e01050306040b061608070c0f03020a0905060a051005031e13020616050105041a0601020d08161107 70
    0x210220701c02090605490300440100000c8081c00110902c59001c42c64403102d40b82d400c24083e00f14107407000000c85952580c104080303048000b4401081c2d0050140c0d150108010b5000458002c904120310310740040499107a0b404411b660030755408840c502c082c481040300680c01442802c1e407203040307402030a0800102200c0c40d40000c0c40da07408603407201c50030f81d148481100d000070106441804114140049901410305600c81020f078040074110070f1030a2060300010708001c4141004540c1500005000810007580001000040c040c03100d0f4101c1e12400e40c1d000034210b681c140070380400380d80e8810010b290303a80c9410111000f400050900c4185100c4260014038550085607222114001409030762076411a032a22648240041040c460102e4010742c02c1020950000c20b0301101c540c6140b076080040f860a20806000b54030840c912070040c80c80440300306000c8001003501c0d0640d041075074000c100030307000a1010381c0702c01e003000a030f40303d10b569400c00c0c4c8903200f89040701001417180000c0811306001c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 549464181 1250 549462931 549462937
    0x9010e1c1209080d0c0305160b100810140408280305040303050f0411061e13050102060108031303030e030f0f061f0b04090c051b100c1e08100812 64
    0xc603602e4101158462a43d90756440c0c4104404000800300186000440c0c03080c8040d20407102080d9140d65100703016143c550045038107a498003400b503101c1200f044401c0080045a425140b42c8000f0f100003400a07007404d80650300200080c0c000780c0c001030364482941450100c01360000428068540110034070f9001070003060215022000f084ca404c001c12402141807280d944a258012400785043c210071081c883c15422840c1880425444180309890b00340101c40540382e02e800c0383d03c200a5851910b000246820b006038040c1460f81c008205400d4544282480c8900341c5e9010708026000321300d01c00c0400d140c400114100e4081f80940c2c00d50312249040803c03020300580b0142a1a440141d41c031520100c0f0100034860042001e80400080081c40c00e80e81080c0d580c2d401904105003880e0802e503d000c0c08602613071840c2c005400c14800115004610f109a02960005142c031240001c1e10424038034502d112540d021307050000c0d00000515134400c40502102800841055a446208501d51048a60 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 549465431 1250 549464181 549464213
    0x9210303041104090b0406110f0415090b040617040f02090907091b2003090a09090b0f04081c0f0c0c0c0602030c07060c0501090b1e100b09010e1c 64
    0x21080b1103504080c0d03d4a4000c004410742c001d0034181d41500c89503141c0008101001105010010501232180481103a1001e003000300002c090900a401007000000c241071801c1d000038107210800d102c148001c50348050309480d11f040348038000e011074643c4e01308038402024100c0020f500c01640403c0103452100441d5410441c5c0c0300700014030103800014141a40800c0d40b40f20700700020400700e000702c100303603001c8140300e1042001c0040d24a4a1000c10104c0c80d80c0e031540d085060401d441d060050108600c1da00400c2d803001c401d202030000380c20250340d0550184501d6601014072401c1000c180d50805841d4801c03250391a810f001048400c1e801d88000c3c00c5100c5410003555a4504c004c0002840781c0080201c5030324004d400c001c3e280c25410080180c4031030710380300700c281c80c0c81d9aa40c6058000512041d00c144c01000c2c070014403050383c0c0502a00b50502000200703490b05204100404020081d05035040c3c5408000c02d08180c0c11071206000454914009034810600c20641c2406050900c0000070703e500c58a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 549466681 1250 549465431 549465443
    0x5060f070c05090c09010e0d0f0309060806090417030621161502060610050f0f18190612020702030610050315011212110105070504180e070303050921030304 69
    0x6550b0360b00c2001203800045452040444c0b00b0003603400598884d580f42c49042d41e00910807140c550030740d00c0d420305c3d080d80401c0483c04514103500a10030203030130602040e40040308580800041c0b800740c2d00d80a0380a1a0b07131801c0000780e000702c00705050742c0d689045010800d04890b5208021140150344941c4c0d030303400a801c00d1541041c0300c0049101041030440b0003031035070b89400030314a6885041c2403103c0807401e2050074040000501003010031094500040483c0c986044020340c585556000da01c80001c0040442485105480001d069901940904204a4405050510b030312114800c1e02c001a12918400950500075641004000d4101d2100c00003aa8004d034115001550300c6010030340c0a060a01514248034080c0780d200c4009015010108c03c0226189001032521783d40c1010242075401c00e41d031540200320041000c1c041d0703010f45000607400d113070550303400e00105840e500050346515080c000602002000140010f160310f07294002c4140341c01e040351002c000344a061013240c980e00151002c6802c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 549467931 1250 549466681 549466703
    0x309060306090207020d0b0c390f060f0c0f0c010507020607111f0b03010f0506120a080d0b010504050603040501140f0910050703230405011112011a0405060f07 70
    0x990b90b014030a803403020f640170780240c2c00b41c1e02641f640c1c08100307002400000c0c104400c124058050404012015042c40d0700c014800b03034000c9480c2c0d6505260020520324940794041110318042da0b00000320f20b030700414a11610030391038507000354040c2c003031003080110380701044001042c11400c40150b00042c400c0f4840d03802e40701c594503902c50881c0d80e00804140743c003a0340c1c803c03409144481d40c145001c03d114000c122002070707840500004203007540c903030007000070390103589100700b145038245542400174440e0a480070344aa802c642d900d4001d10301841c80c0c3c1c01307482a91441c81486c1a4059802c59002d000700400150f140d140628115010f0302c040300305145690600d40114400d80859003c1d24000c2c00d008018204412900b001d1100900d4010002810142c171444d00e480b034a21108161080200c52500d840c4807444c0c1030415070b0958240340710031072404908100701d030501e0f203210781c4490568070780001680036240b60319a0b04584d801107800c150341c042030000b8440317500d2080600605103203110300b03c0c0000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 549469181 1250 549467931 549467939
    0xc032601150801050d11040b1503060a050301231305060f07030c03090b0a020307031103070e1c1101050706060b0d24030308070e130c020604150b0a03060c03180309060306 75
    0x24001001384141c0e90080d80e282d1020300069948542006008006800091804d0500000884a1004c0c1d0815011041c0000500005051012210019101c01d600a00010817a101600c13038034480c00c0c00400c281c1004070040340b0301d800a08007604415801c201152040d052052128000010503500c000100e4a000340c52200750f0f01074099200d400c1d070407000424282d40c0c0d0800000280d031000f041041016a102e280c04c00c0e40ca0140c01440c0222059500d0104d2000701105001ca4460140d0040c12041c01b10f0b9000f200003001c1c1e00050742001020301e8520740303a0304a49003071b60280419400c202c821810100390500c611641c1d902181e0441c11034440070102c0118411442403003189404050000f501c200c001071a0540a031400c030400c6030b070152046901074070030440038086501c40141d07040160004000d100c2030250220301c682030000b10070000c000c604410310001e01502c0c12403000904064031041c0f10915103019030301c0b026a111098110f141409a5454000c19925031030241002003490440302203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 549470431 1250 549469181 549469187
    0x70201020a0219170f0c0703081903020c0604060e0a0501062309100504020f09060409060611030a02030301210f050a05160e011a13060e032b0c03260115 67
    0x10f20581c0003914013152807100303090010035034801901c6100076681080044c5108008100d507500030350150425a0322402c051501c640d4644030a6043d0303081500610281d003602c1808120b4680099200718001070802d64804003506020010384082d0040d40f800070300207100103800140c6900c102d01c0720480d04402d00802c3c208000e104d02a01c51060803800c0360000c0c0141d040c01d500810f220340c04418614184500040000c074180d0258010398203154403607801f0820703c3d81020b0720001e0703404c41c01c001d141000a00c2100030354030300051203003000c0d050b403410034135000d0710103003a21401c256004054403200e210f540c10210740d10900b6100032a2b0500c1403088403001110007a441030183c42c80094096550303440c10400c200420320700c4004100d046010404014014054800c600c01010781da11006002240f24040508090329613a014030147c41c200444180181214001d008645060522541091150404661088074941c40c1c1203032104940c3c03840d440444d040040c50486050342d41d4080d80b500300384411 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 549471681 1250 549470431 549470473
    0xe130606080708070e240a020c150f1606140c12150102070618080609060106030c050306060406030e0a0602030a0e0c1005090d15150303262205010203070201020a02 72
    0x48000113403c48880c0d4018034140c00c0f0310344490950181780d0301b802050400b0381510340c0204071941c017590041d407441a02d418040b2060030300b0b54280440758140700114040c01020300ca06101520004040c0030072104101c181e6001c0b022450085030705c91041d242140c01c500d0180c0c805421000354500100c00200c1c0ca2940901004100c02d060307000d0800c00e46800d10070b54504011101c0205144600ca5000c5102a410403000e40309601c010010650355152060183c2100c41a40380c8ec002c20000300700300100c649444048404554492030000b031042c4225640e6400c02c1101d2000a0040b4000801d000114583e5040100100d5000303003030b5201c5c0f1a0510800100c1e003106100480802c80c14850309901e86400000108110300038006a0011a11040c001045461603980414002e84040b400c1c818154041441740001c4d009031049120342d290360f1401102600007c203204541c059400392a04c408000f008a040e85a5000000b0341d03c1342050300c2c002c0d000c2d40041401c01700600c5010007070304c0030340c2210101d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 549472931 1250 549471681 549471691
    0xb1b1b0f0409170f16120906030908040b1b0f0d090b070218180604300806040e0f070e0a0c08010e0a050a090203030c07030309080705031207030e130606080708 70
    0x24800d01261030ba11101464012588160150b0400d205000d10b030803501941d00011485804170030b1101c0c41c140c90187c00030440d904a14101490620004005400c1004950503a800909071540b40d04030598907400c05403076903190504a00a90b6108141e41e980050b4107200be81c00c87d12150106070b15003180d00000d0046890181d40801c1c10030864801050202d00d050300a00006030aa481c074a01441c060b103170810a550444a09136022550170045002110100600c00389400f217102440d842e01c0c004207611b0001e46114825551184c64070b40190341001500c8420f0201c006a0300d0403039981e100401400d000300c40c5c0341201400c080d400e4241030311074a075541c183c03070500c100d481325925403540c40ea004280041000b002c566450907140b0140e50100058203804100000034580181545070041c421a4180d00c142840e1340603400520996501042c040c0c0985c001040c2280c82e000329040448022260440d01c0e07410140110601030380c04090342148042c4c038420b0300c4400258441c900c0450340d60908640c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 549474181 1250 549472931 549472943
    0xc0e06180112030302070203120309100501060804020907050c070f090e0118030c0f1403030a0b0a060f030e030d0e0304030308060303090d08030703061e03020910050108010b1b1b0f0409 81
    0x602c540c4006400450010b402032800600707081d0b0340c2e40032034a4000b4040000c021244c000c001c100700d0381c6040080d042110896041407109500d4244060300d04800644003d1042031090000745100f03104000340d81100000a0844103115628002d00700c0d84503c9008074501d440c01c15034040c06000d41401150424828440050600c21585d20b04032040c000f460000c450300e40d90000d1407408120f540d08103d0005528801443d6a42404d440c500d0460b045801454061030440c0003c000035a0050b4080764804200c0c280030450000e00c0b10403c2c20b51003108103580e03c2c2850400b14201c20364000010b070082d00e210340c89454a070340310340c010160780340503804c03030103502284421078000040c5040000c0c2d500310300941008100c00f03443d0b000341d100c90703020000400c400000c544000c10543c40c082c418540c200032040840e484443c00e00c1c2c0000d00841d41402194245040011079021108507070b8506124000c022082c2c406c07000801c8a9149840c900741030280c4201c3c0520a109140e151a104090129074006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 549475431 1250 549474181 549474229
    0x303030c09010f030f06090f0513051c0201141611030c060c070809090106030e1b0334060f0e01050c0a1e020d060f060b070510110409090c0e06 63
    0x10300444425941e441c40104041e240e06000040c08114000c40d009840c41007800700f01d600c2c008044504860004000702e0b0603d070812448400b013040030944ccc0c0d2001800b1600d03d850610300007001d81c05000301940c407200b8192104204a841000107980c40300c1c01910355503003c4511110381c4a90b989001d00b41ca01a900d801c00000703d041810010000c1030f407584983c20340c0782009000e400241c04041c2c26403150004c00d03220b8583e10148070342409030341800105511811140041c45000c20b03075540360068141d130101c081c0648544040042c004440710200305c0c3c03800c00025074503803c2c02050f1781000082074001c90b50a05207901198010004d480000c07001304000c00310f0402644a210310388070f4221005201c45229402030300076031100030004500901461020940380c010a0491007280c1003070340442c100030320174060740e000500041428001c0c04038441d000309201c032405c1c4c3d510103140b1842d0b04c000d191503e416413207820002088080c404407a0f01c84c05440155503444184019030a40a207000c851500c03103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 549476681 1250 549475431 549475447
    0x1412071202160b041a10212f04270501060b030c09030d0306150c2d0b010501080402010c0f08121510210509010e150f10141003090c0f03030e0303030c 66
    0x811000c2112040851f210201024a40c4843c4116012485400150002550107180a8408280b606c10f540720a03030381046055010800c0710a031035045034078074101007010080481802003d411240142107a0b000072070b0386e41071406440505900000c1141e01034000c0301e4005d480c00d40244180000c0710f000c3d41501c40380340c0e4010801c4036202441d0200300c3c0c9601820518100b50800c610303241c843c0f020709225056900b190780c00c190440742d90580c04181000b003040200030060b40d000c00160342e40b0f9801418050035207890700d081100b40c09803d09410035180c000e0208401d618041c54950f000020985080f00a8085200100c4e991102501c960880380c9849184662501d40d031f50210b07510951850002640034944000e46003081d0a0004550034885080140035000c1d92140700d0716002183c100c00344050303614041c03148490110011005105401c15000c1c11031450180d04a0704950b54000300314040710b602d9200c0c4031041c20b26030100741d0000303c0c9610030b142241800002c4034041c401d1211003505120746 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 549477931 1250 549476681 549476699
    0xa0501080603071a0406080f060a060f0c0b07050301050906090402010503071107080d170f15010806010512040c0602121305040b031204151412071202160b041a10 71
    0x3000c1c1038a41c0611858800084400411180c841c00840408040e9652460046d0042c0400c80c081c04111003001890144036080e0f807444040011285c5a0400c05031805042805039143d035010000544000e03d80810412919400300046060340d80c116040207594171102e0500909203001c44000303000c14400c10100750301900843c3e510080600180880341c106131030303032102400c00c00744034902000b01e04a0600000d80a01c0f58509030780c031410034203407003d840c5480d07903201c0205420b00504905000b803031404941d041e4402e01c1161042d00b208203026059050a142900c1140303a18410b40c00180101c480c0304103002a5170302242e00b80107403c8410561203013010100001898240a504e5141c0315146094400e0ba001201401c010400a03008505440300c13040081d00101e2180d41c0281561801c20042c3c2d030319003904017069040302051400c01c2c0c000f911034500b14024411174802078060901c10503130504100004e00207910540c82000480100c41b100d81c0324461280f000d44e080c487c0c4684000080c0141130b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 549479181 1250 549477931 549477947
    0x904150e2d101109040608100c0f050d020d0605120709050601140304060b030c03060405060405070f150806131109040f050118020c160e0709080f120702040906020a091a0403020a0501 80
    0x105090914507213002000001d00703c0710f080d0b000024070781001d202d0000101e03042c4610041ca00c1c3d681810141d490050340020900e124905045e100e965001c191103018007841d41c00318015103400384c07152008032000c0040f40d6490300326106281c10141040b00103a07440d44111401401c6000464200b801c584440e55840040c140900e0311030707003503c10388601201c25602005481c2c000ca020310091304c118149070034214180312064200955051901000b000304240d64400315400040c180303040065522440e00090b0900300074001140340d1802e00c1d0080509003c25030042462032030485e01004072000c0020042e0982e402489080030310350a12007804500403081c3c000f864800da615041c1c501d00c0c02d543c02c0401c03d0003c0d5800c218080340e8060304200e2501d42040d44000a400e0010041c500d000802d001140e46403651001d6040062021400c8000c40d190340d0050707420154060815901d40140c0b10008100e422070340300d000c08a500c02d0016502140244040300c050340e4011f0700100300503080c4001034403500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 549480431 1250 549479181 549479201
    0x2031602150c0601120c0603090305090111011b0215060a05010509100903080f030f1b161502030f0702071706040b1f03080a0e06040e01050904150e2d10 67
    0x66010004a00b2582c803d01038a4081c0c00b114003905406146410b15032006600c2d038100401f0703d46040015808260044e090f61040c030001d01e040355405110440040c0549604042c0c1e42e12818003a01e0140e1103500811061131040c5048207105040e681d10b0b0801c05c000b040e510032280403d10402c06125182070400381c0e1580b0a1072303414400442d80c0c1d40c0d03440f01002d034020b42400340103600c0803007840818106031610035080700c1e0562000c640329030030320070049080c45028820206a003c1c6540d2008001044c621441904600242151a132901c1558031144107030846901d4014001d18901080c80e4240f82e5102c41c0000265000784420341e940c0d03480c14151103000d4480c04140d005828042c107041d12418440025610408800707440754801880581070045c107036840c0784645024003091014450104241e41140d0301100c8001c0c0b43d88403810046ea640c032698622040b080d0600b003020124010005143d0000403910110340c40300c0d48080c0b00440d44100d800301a074803a40142ca40240c1d00381054015203000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 549481681 1250 549480431 549480469
    0xf05060d2904030e0f040c0905120c030604050d020d11060703020f09030d171e0a0b0411040e0603120711011d030a05060f060418173702031602 63
    0x101403001e01d41c50341542100d080b4005100d8011241003402c000030004003182040c0c6091080c0c04403c01302508442481c000d0754000c9451060307624030b0460070444c05604404c05402c1d11864202400c2540c3c44500030209400544500340780c1c00c0c490351050400300e80035030b5a08040c2c80991101c6504401079408171074185001c901c1801440c03881c3d5000e00c00c00d0200403090312003891a58200004104821004050004940c42c1d03042244035650b10b6287c090b8800d0500703000261703161a810025000b014a180302c826051030105000c0b8a03124500181c501421080b800c5618031021484d2004291141110040403c209201050415409292a5041404910074070107402d0901c00109203000040b403010307155035201405120540d850034400680203401540c044c018405401c0301d051014414000082c08003011804686c100c84610040d075803452a00e0145150601c00800d040c2d01100e1401d448108105080404182c46800002200c4181414450b1300c81c1c2c8440c107801300080090824644a10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 549482931 1250 549481681 549481733
    0x108040b131b150f052d131e140f010f14031905130203030703080a0216080403020405151e060f0415090603050603060103150213060e040f05060d 64
    0x90200b106031800c000d0030b035402c282205480501030003840407011041e1401404010010500012850854401c0445001c1c81d5400c09041b0080e204060780b0415904141d10452002c000c10580031900c4070220038518120100006601d070f01840180d0400c0008550b4800c60f003003540c845a500070740400040001c1810034101d903002d8211300341c403164030403903508802c4c52180140d17482039049841803d03003151a0304d000f400c0c600510360110b40d41e482610030141c180f00e903800000c2c5400180341c045840106007090140a220750b5464580400c3d006070108904c20703418640000d200c016860703409681c07554001c0005908002c000c00000c4c2c5101c11000c0f141c1c010703804100c000c0c11440036100a0008044441c49920320504c507000041004007244c0041c0101030a20050055590b0001403060540f074202e21101030030800301e24400002c4c840d080d040b906581003400001115500078140e20382e02c0130190b40078048003510204134800c1b65812100c007035016221035807584c08181125190290f0054140e18040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 549484181 1250 549482931 549482963
    0x15030b070206131e0b0c130807030c060302130317070b07080402031c050d060f051f0f03110d0e0c041506170a0605120a23031801030605040f0608010b0108040b13 71
    0x400000100d0302d0f0146c1400010788984c444100c603400350001c200e2130300501003280c1990380740d070850b0149202e07410425801103018076400c4002c51003e0700840c0c0c040740b82c1c1c0340f00348828141034183d0409102034407140244000901610301500d23046110b43d500401810100e03104d00c290224040501c2c21141c1004401c0c07042018040452140c80007504044160b50b400d5481c14003040b4070310805040c0007038a42001d01c1910840c60b040068034508000c0d40c1000704035100c1d84860603940d40264900100c10300d08025001f00302800100f0310180e661402e60301417046c04c1e1f41d05280305401000d40700340e90000c0e040c1140204589000010960001e000c0440807807203696030000640303144504508540a608807460349020890442001d0803035600355103c032134000c00041e18164507806160440750803088902d0482d4916032080c2e00140140030010400c0103541103491401c0b005003d5409110b00b2507280220305403903980282e0595204e80c1c0e02076815026a81c0340701c0d60814891602100700d45410010300d00380 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 549485431 1250 549484181 549484193
    0x406180f0b061b0d020a0f0b0601170c0c060901060506040308090609061201090b0a03020f09070c1401020a02010b180118090816110a0e010504150915030b070206131e 73
    0x4462000a14480e0900c0c01c03c01c182407040002030002954411010540050150010344001c0f41d080300c00c1000c207944840c0140d4003d900501014a00341d002d00030403101038180d40103014900d00040849496941d07150865003201c925004544d40b2460a00041000071032030401080c10100150940382020380756004502190064903100790781071030f250010702400f585441001c02640080703810381c82c0e4500d1500810b4000d603d40707480350300901e81040001c100300d00500281840315403102d410140c03070324240103060003900050070350310040d424004528400d00e003010240702c0300a0b0f4882a072030143d207000703000c0035560898501e154000703460750300800c0070440d420060803101540e400f50f403061889074645403007090b82c00303c0a40d00c02c1d51014014000400c00c03102140c15180d0980e000a11040d41c00d200b02d000d47c0e590ba00c190496410184c1882c049440e880500c5e0450b841902228815142ca00085e80c89020840300c4009903084a015100415000b442c00390b0b10403c05100e4016032007143e203c030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 549486681 1250 549485431 549485437
    0xb0d051c03020c010905010501180203060906010f020c03060f1e040803070507020a091e06290a0203090312040602011407020a020f010905060307110615060d0b03070e01080f07050406180f0b06 84
    0x11b031703443d0755904010080c002c040c0c2030b094000c1600302d804501e1850420b00252060310090540c9041084885008032220b000308441401c03243c0040407100a03252000f8280303c2c840e0704460254403000f036504010704d01410008400c0c0625801940e80b42187d0304c150080303c0d107800105084c4da101000c2000040d0220036842039503d01550102d510140b611150b00d01c00c01d0710b26aa04c0032001200c8800580c003007046901400c10740d5901c07030318003940e52110326000f24030310700842895540c5401400138541c0b0400c9651300a10444a03241c0080c032042e03542078000c0d184c41200301d03070340c0000d600f040c0c80041c01458030140344030701100c0505000744080d8441c1c0201d441038108403075000115408248003000c58104014496000d05c44d01407106c038031f50b003104c0880c040e0301131907055002c0039840f80811640340d41d042c0102c801400008143c42c90a6030b56940450351506802001d4a06029032000480d09041c2800340707005031440071b0500305108501c6001d80c07000301446076154111035920031800903503a96100c02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 549487931 1250 549486681 549486683
    0x50714010b0301050709051309023d0207032d06020d050618070c021306030b0c120a05040f02010503101e08190b270307030807030b0d051c03020c0109 66
    0x1800307445031050500310b5002070604402c0c04800d010030011503030b6a25a41003003080101d00417601038100d2010035212200030340a400071100f8a04800d0040001c0101c0d00e0040540114079011000d002c242079807521074900000e07041403e510068003141c0300200300c0c0518890846c03071451003010603455800072600805440c2c603c81e40c480d800e100b024548006c29084403110070041c80c005042051020b46001c120300d200078014503001e07100860350100c2c3e50200c0000e42d000303101289545003000b102c400759408204101d030909820004288a81c0d254070520b88580d80c02014030350000138a80055031190030082904601041144000c074900041d03282400354803004003000103030142083d4003241042d00c4103104503041454165048041041c207440140c0081e010b104501c4400803083c1d0142801420241b840041c0c440058484d08040d4400c007440e20481e038944d0100121841e4004012800040c07000290035580928501d502545004040d64003c3c511420018542100c02c00c100342959402c40d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 549489181 1250 549487931 549487933
    0x12120c07080c01051816150e040b0d0b010e090c0a06030504050f0d0503070210020f09060703140423030a020904060b0d020d0501020408060c03132612061003020a020c0d03050714 78
    0x18515490004002c4036841511b00c1060f4008a800d04031840040c1140008030f83c01c00601c046110016241c2d03a1000d402d0728405440f04540b50301e00d04000781609000e1048403203101061000440f817210110701c102e0003071001041207036494980b0030110041c26000d44182d6071801000c03813201c00d2480030850740d40300d004583c071143d4491810b80301c040c0c1840007650008619900401c0343d11380620058048466000049420381d03150209810300311050616040c1c951011038001a01213504e482140c0510b01c01580840300d0b92000d0081e1061540750070f19038000030b411400b902d000c40c00248180d0406800c000e005043d0100301001030300003502020380301006a4041c2d5001400b80018901841104c1c0e100d1070703980c082c0349182044c0034001c0e030040305050060420310844d8401c000c402c10840500c41c50320440c0d0511500d070000100c907805254419240c5a220703c0280000c040464001c0c002d0320007103c0da94011303024204030117003400341d02002942c0840c200403040103078000140c0781070044e5180c464008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 549490431 1250 549489181 549489211
    0x10050a0507021909050901091709090103020d03180b0d0b060a0503130623060a06030b011b03171e0108060c0f070c17030c01060b0702060316030f0f0e12120c07080c0105 74
    0x10816000c134041811074409c240034200310003e010b40310b86011504580e4180d0301800002a01c0c00c08076811401c4007002480d4502000d0001030444c0f80c40d001e81841d1508110820000e0425030411500d4891280e801c0040f400610000342002d05807081d80080f80d0240101046001c03a1228010000d044000365580441c104028008181020320707202014124a050822080204400181c01480b10510140030021240d002c41c0425108400901d000103a001103044e50342451640c003400952404122070302c42814000008480c140096454014140700c000103290045140b10a44c0780d0380000d500340c580a09040001a03915022480c0500155115028640719034440030400d003595031642c410100c0140034011100503940c4c003403ca030b03000701409040e0f601c4451521420340182c03e103101400c040c0ca25001101901c020390380c11501d15141c0c40e0f0241c4e03081461104928509000300d88261a07060103443c0001d0f000f015510003480c04030300135200e49042004100382c0030b094400480b1105101c240340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 549491681 1250 549490431 549490433
    0x2040b0a08010f03031b0c0e0c0405100f0f0e04060b030403090503210f030627150a03050a030c05100f1a0609010c02010e0d0209040c0510050a050702190905090109 72
    0x20542d02400000040030344551440e03e00a00800014140d5802c0c00da02084220400126008400051050081c00c03041890400ca04131001d4000f4411180564603850100d106e02c0d104205034a2003c415031142482c0f4402910200c489881d00c40c1210740203691110082044441200914440c5119588042b00a0b0802d0181824074079140194805580f011013410607035601c0905881212a18001131600d075565940080c800b0405400c0c20303c464901c1400f41c185070030405081510403e1101154200500044188400207030f00d0310001c0c085822111403080020701c564a004003250141003100d44000642a5046c2100d811004030b4580c0303a59100025104a40086200c4100008a07041401e290740c000000e40b0001855a000341000640800241e2560360b1820003e2540c5e005803205c13000f49002c4c0340088154109001d4184a003032002c440504e800d22a81c00c958910030f055a4075400c20740d5a41c2401603031035a0000c1940c210080460104004030b56209203072050091400100310340c403c07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 549492931 1250 549491681 549491687
    0x18051506030f030f1902030f0405010c0609021314010503070f090e0102130f030b1608040b0910091b0803030408121b160605011410050309010b030304170709290f030102040b0a 77
    0x105d41c103000199001400080710f001b45001c140c4040301c000b820010000000c91400800901102500a610100c083c00c001c883c111694002a1070030400c50305c1c0542039882d4410990395078036a20800c1002d1000010600890a00360420b41c107010139100003600b40f06032088200703e4150940c0003021202c040a401700140198440b0b2075400c400300400c860705201803500c000b40021001000076210203001008104038100803c2003010204080c1c1080050000340c1c5801c2041c2d0350301c00400c860a10000102060329140482203d00495220500c10714150613400c0c1c00c000c1c9000204144054241c1409030301c1d020f040440100048021808910758020342c915140d03007101c80c183c02c061303561882c6003440b51081e268046450b084c00041d04105032255501e000007409042207200f002d0309800003080014425900100ca003012254200c19242240d407245940070848180092100b02000384850304e804001d0414603294103050701408042c41d2944960200b404da81c810f0780700540d20030300001c00c00382c0194 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 549494181 1250 549492931 549492967
    0x1e110a03110a051b071a120c0a0c0b04060905030d020703020f0105010506041e051504030b0901090203060604110c07080d0f020f070614041a0a0318051506030f030f 72
    0x308481507400c02c52510002031039400354050305982d8503a100d0340148400300800c0990001c210301e0240842d044007200004080340c1145100481002c403100101701071061100c1a10900d121035070b600400c600b55138442101c24030024200f9070b0f10943d0f9840e0b21020540c14402003446580314980503075a6551490024501071702da01010340356915103001031161f0f80e1400122170459000e8285002e480740031900306500a9159880b4540c40780034010398480d48840d030b10142040320300400081506a0310b1440c0e042c03d0310342c03c040003549a040703440003134110b2400e40c3c0420606010b501c585424a45406046403520140e500701400719480b00940800a42d07000143d0b64414210748058006034401d401d1080d46c40300d0340c0c0581c0040c002084075071004070b802c50094a008051510700042000480421581550b2040741ca2100007401c02071030305030100509094042156000c00141030b8182504414071000354090038070341d49030140800013104160700b00041e0400c40d0482119981d07a03818a181030031854 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 549495431 1250 549494181 549494201
    0xc1b0f0f200f030a0b1b040909060e060708070504031e150501140a0e0a050c07020607260702090a110d0905011505030f062a07150f0501181e110a03 65
    0x240c130800c01d4000042e46040200c0d00000501e40700b4403900d84503148080315002d0307508010a140d1401c140e000911805810000d501c2c40d21009480282e00c0d41c0320704036200c3d28221414008100c0410003000042c0058a1104241c080c01e140b0b50b200c000140d9980304042e514181c2480601c0d2110010300900b00780062410100400b04e43c007105035071a24100090b81e110051094180d181d07500c0004050059600c01c84610513402024580c1d106802c1c50441f076040214010b0901054481d01603112403640e100498100c540c005009250326902c401501c00600b8040e42d0720701c600da0040c0004042000280101e803840c900c07038000814206250319a5a200841b640d0105220b640000b03602042420003003a440d070407210024000c04105000141c43c9480c0d03c40b1801071595410000c1e450007071119404128500b00c40c0d017101842420507628032181915000e00403c4007450f041c01001024401360b920440d001065107440601c4035840c0310448080340d207440700c241012500003900c40d0038641d0610a41d1900c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 549496681 1250 549495431 549495433
    0x131203020a0c1b080f06040c0501080c0708160b0c0403050616092102030d120513080307031503050303010e0702151b211008010c1b0f0f200f03 63
    0x841d8400c402000290b840c0005448080c100e40b602c00100030030004030001c4d269034000c403001001d40b98900d50f5501d03000c45046da040300300300c40b001c1919886503100c0b03802061040c0c4080e052540e90b413520302640d803088841c00005e072400112a0000b440284a042c464500c45038980d032581d2560914904101c2c00400c240108054090340702d00e45600508408103856088c440360780904001281411003121940c1c000e945841202e5144034010f91044000494010462062225490f40c00b4001c40040800c0c00003800c2d4070003803000a9016100e1780c015142c3c0c020745031224168a54039100e00e81150300a030000290b259203c005c1048954040040403801010344c29000b10b64a8100b03a0304e11544c140d81405d03090306000185400c0c0038002c040d5840d125100c103180c4003a0a00301604841c080311060b2040314241d50800201000245c018000054295003883c40b40b24002c4940e0f807050035000a039802212245c91000c599404900c40c1c010790f40031000469200c02509080d0006c0004900d2070090301486 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 549497931 1250 549496681 549496687
    0x21b031c091a09070305010f1d0d08240a0306050406060b0301030804122901030c06030c09150c170301031707030c02040905072117040b040b090604090513120302 71
    0x40c0000d0b5048049000020441001d8444402260034036425500242680d03080100200354000154030480402e80b0381f2680c1109040781c80340b02030320385240002000100b01c034640010802402c1e00703440c0003d403846072102c92444a41c400080d508190503001551007549e100200000c1203c3e5110310009811400e6810382903601d1507440c5140c92041e401001e801040d10240030b400c1288516100c5400e408901e0900c41c3c505a50100c15120315007444241c2d6120548000000c4190085c801c018401030143c1d82c94140504140e0000040995440d05404010300c260340716002c240c0900c2504101640705202a40d25455800d24240280c11440d17201d04440040100d1390009401c00a02280c02d507058a011550980505002d414a0340c03a070f205540b03802011446e00c030040049000411910320400207030498003201c00708110036000741d01034540300e088100420f000041091025145140f00104840e241c01e440e5046201680c905895035020350944260020400c0808413035024910510302d0308500b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 549499181 1250 549497931 549497933
    0x1050405030d031e05010801050a1103060d1403130303180f12030c030e09010f091119050c100c0503070f0f050919090612021809060a0f021b031c09 65
    0x51258000700b412424159120500c1e042015200708602d4000d00042d002c000035a07440d817515002c6d000c02c542400c0344c20310700358072160790380046d00590b40650000b50080391410f6495561109482c440030b004034044c482440174403061198481000003540c4255900660000c003852005010380568103c0703400f8640c40758061081060f40002d2007501c5400d4500b892a0480a04060750b5002d040604c4a0f0843d0080c400807400c25036011140c000c960314100200700c2c41c06405c1c0003400c50301461114250800c0259480041248940090115034640c4800d4170030303c0f0359840c2e80c20219480a802600407503000f2041202c00c40e081000e00f01d9010007400c2c0f807800f00e00a10360081291260014462040c0b21507417004094010a09289003e07203090141084566101c0119284014480004030b201d0b200d023110300508103410100c0369004075480c00040a16843e4070444ca406049588030100c0e10303507820f220301d080001407032015001d501868000b66550b802205111052060b030342000c0c42085090802c094 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 549500431 1250 549499181 549499183
    0x702120a060605120718020f0705070b040f050a050a030609020319050d0801061e120b1c0204110f040603050a091a040204060603200a17012403091a06030f1f06050105040503 76
    0x2060922106001070360340340c0c95003075088e803070183c60005046481003070000305e45e82504800810944da00002c170700b20b145640d00704002d00f480c441c0c09980e0700104102c50400000340701c2d42000041c1840107055407200300c0c10807440c510407002183c017544c05030301030103c880d02075400495032805400c075403504040600281d640c030000c000007120707410200103065504204091845d80001b12303000c7d0052001e005040101105000702c400b44d00e0030391241c0d2800409242c0b1541c1d407000c9480050050002e14205480c091080c1c0080bd4002d012000c441d445252030800504040108103559110300240c0707a55003070a00520003101c90302e4011000b031500d40f00405c1d026981c10413031034400c403500616059035462406c00841f0016125a6000e842c00240d20000c0b440d02080c95208403c1003150140d242c030310901e0b100807001d4662800019003810000304d00881c4c181c0305002d01e648d0100020381242c500086030a03a06140158140c169403006060310b48c03024600c50700b8020040208000d02c3d0240c141801c001c002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 549501681 1250 549500431 549500459
    0x3070e0d050a030804030e06070c050f060c0703110105041d070f020c0a03080d1b0804030f0801030b01030b1e09010c030e0d080f0405070503011b1814060702120a0606051207 76
    0x2900380421030000031704051244580180a203400f0302000d03240d041c1d0b880c10344003850082c01400c0c03241104c02c42c500c65a041c40d0068901c0c3e103004030010b0a680340385480e0045401c010314035503410484200408035200c1d005102070180c410001821440074640914010051980020348030110b403c01c0c040309a295070f1b16400282540d8100205590b60038600a08038000c20b8481c80d01c400e41c910181c0155200c9411900040c891400307034440c00b514400b089002c5941c40401d000041c0054200e41c0140301098880f060300e9408582c1c85515201d4450000198400080440c3d800703000741c4d100c0c0f01d06400658540285000f91010100504404c030500c1c60244c00213100900500952a078840010240071041010000908001e8000c1110846251490015414100d01d03900800d05c0c040380080088100050201140c0710008001e003140628400c10069902c04e400c107982c002540f8500c804400024440208240d10907200080c10601e04000d001003800c002c440f140040c0c1182004100b007071001144 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 549502931 1250 549501681 549501683
    0x609050913080a050913060602060f09030a0f110f1f14060a0306020304051e0307120f0c08090109080105010e06030115080c0616140622020a211703070e0d050a 70
    0x407603500c80296101040e040d071040c21034000c400e170402000140040d00450280d0050050074410002543ccc0c840003190751b8864020840b00142050b00c072444480e200d68000030038050aa410345510620071841a03140088100d10904810000860300810340001e10403000092401c104c41d08c03180c030302403000505502c010310000d4031a50300000043c007080024040a40e40c40c4000300d48441070151540380554030b4020390801c0703816a41e00c141e090f40c002e0041816449000050342c03499034500e031030303982c3c05104d810020300b050502142d950080b84004c020302820b4040d010300d00e072040240ca0244101421748058012101e03580d141c4000c01d01030b060010994200a450550368182e40c0d411021486080841240c40948046683d50001c0c600d07036408541540180d4506402c0c3c903200c807d549008402903903d80009602c1040818200580740302a418041e10300d203e10410001e100d41d41d11492119500314072450b641510000400c100981c01102074014540c003960440180d4001d41e48640c1c0e2902100305c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 549504181 1250 549502931 549502937
    0xf0106081b040902040b130605090a0212070c051c050c0c0409020603150a0b030f040302010e0c100c110d1505010e0106090b0c070b0a1115090a0308150a0609050913080a 74
    0x60780307804e5440700d40008806000241444500190b5000000001c054034010103100300c00300f1010855402081c000d89270128590440c1844944420b1001d03115142c807100700f2109030003000040001405244454003003140c568540716500d5103076100d0641012202130a5034402c40c903115410001da103618050769031003021848101030f455000b03800915034880030340c40020560310010410600d103c241070320b40c3c0124440d800071312400c1d8103102c469485881d00782010750400048400f42411622901c1d81c00e810318021803460400307100290209600d00c25005055402c3c049520a08220754a98441c032801401c180c034800714154148034006081413054420350305080008181d12000d5103041c091103000f00041c00016503146045107024013004c01141c09000c081c01244480c11119804c82483c5114880400c0540699201564192076000c40038105c4414686c4d49007103550070f52a0242c15030301408060701c5101d80c9500c1e020400901100c020710b44040c41d10201c46520020f080360059524512240c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 549505431 1250 549504181 549504191
    0x2010617161a0c030301060309020111010b09220b010b1e27120a0606150215270609031801300b041b0905030a121805030d020f0106081b04 61
    0x81e02c00d03519401064110f00310760000200014070581c00d507014249543c401c0e00c50303084c0c0f200e110306890b00300c07805007149940203007410b00002c0c40007070a80e41880c0003103125280c06500c101c60740c44400c1500c0742608000200c0d84005001810141d04080100d00740e200b040702286001410b580c21440c0d117075480700304e00d06004035404280b8159592601152801d00c404119452200c03503090101c0030f085240300b040c0300758a42003020849240b01080780c0b440020204102191a120040310021150181c0d0001030702d0321070b60318240003071030050210341c0c01a10346900a40c1c442864013240c103411000802c0e03071410720140070032140700345096850142c2041c0190480901c050b024180e590060320066000355401840c0c410001c000c840700307080e030002c0101141d03512060030b52a8400c2c03558400305a5005404450440b11031355806200d10020040740b00c100c036001030700a1341c58010a1415400c6007210740981c1044c8000302100e80248a08001881004001d140d00e04502418010203c4a2801a0b00590700e035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 549506681 1250 549505431 549505469
    0x30a020d0c020a031208010302040f0e0a020609030c1309210c020d050f03161502030c030109050c040504330f0e0c090a0e010e13020603071115070201061716 69
    0x3e844154011504150709080110090000820f004400d002c100d2003a031400c1450f1450415621585c191066204018a854107440d000c0000300d4010b641050703031501c900d2041070243c0d1074043c580110404503842c0032540010320700e01410a01000301c43c0c58048442d00c03040d00f19542c3c3c044a400c21079601640c070154000c909042240c20b1842d005080c2c4828840043c5603410002190702d121144d9010358502c0301c00001a008240982c40203840c170110b50042400140070b001060380c0a150400080300100b40382650307900204040d03ca207070b900362192210b06000c4840c0b1814038500d03003003a2072030b42c0c0720342c00d03030608058103224103da590040c0b00e00b002081001034080481101111214000104500724880e80c90061600c004c509014408950000f87d010404418200e07500d100035680c020708103419691480800c403a41c044604554050348600b9040701044564004201d0140303046034000301e130882c1401120040043c0094000241d5800006030310b04d60f441d0044100e095503990708849681d0000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 549507931 1250 549506681 549506689
    0x6061a0d15030b0c090111060c19030b130203061201060e1501030605060301080a1208091902010507150b030c0f0a05090c3c1908130b0f0a0509030a020d0c02 69
    0x810b400c000c10800080041c040c004a005000c0d1440400c2641d409449001001285031100750175070762480450018050101c0300c0b44440136170382c0d9140091a0025841e200710001420404d140e01002d6401035002040c04843c2c105003515100c0071154030000e00c88a03140c802c9a41c160800108404401e009203408040c00380e120750010001000010001c4d522941c49404164580c82482011960300b0b0128402e000c58500400c0481c0c070418266010744000b6814018002c5402c03403140c800c03410050304004d0480018191102d009040365030100c00a0072440c12400c0c1450804203d0714031b4401e0300c0381c004e0ba54440d50340005840585405440103541750316410b800d03007400d0040390403000514811240306085101c0d80c5107140390301c114140448420904203180c080e00c07841340031540142450351181c00580c00e406500455003010f444403844000060383d40b108900b10750159200e40c0d4040e00c2d40c4c00e010302d00515000ba035400200d150003a5180c01400c11004c3d40d950354a920002c240038802c04079000b9952 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 549509181 1250 549507931 549507971
    0x3100315060f0308090301200307081008010f0e0d090b180a15170601080105010804120e030109110306070503010506030106080a09061b0206070921060b0a0308040306061a0d 76
    0x150390340341505454070380c6001d03400c4e5041404468000d620344032540462034840c0b03281000e15030b1100310861071621160801c444e42c91005180c0860407400b083c00285490091042060750210710320001362006980e038069041c5104010f4403000c010b40441c0502080c10283e003124550014196a00d07000d41d00c10005c01c4400c0142e9000e002c003a4003202c40340d0780c0160811112040c004060100c0741c3c0c0354cd030728401900c00e48420302540380015804800900000e0001c3d0045152008c241000c3d60300300102c8001a0948850100031102080150400f041504040140540102c600d040241c1158140004204d20703000500c01c0c3c0f0100b00307640c0081000b2030341990000720b443d608400c00b4803000a9400d590010410351106410040c41000009031204e4031a004003015a08200c05130b41000501c262950901040200144c500990740c00070080c00307503903180817680110b220b1044207840b5880d504010702101c00c2d07036020080e1083c82e00b0168402c000700008440302418441790010b4401c0c02c04050502c041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 549510431 1250 549509181 549509189
    0xf1608120429160c0803070507110d050307261305100f090501030903121a03061b07061e060801021804060e1501022503170310031506 59
    0x620001100318200800c8031049105034099641d154040d03000200100b0001d200b00c01e4151199081004140303940e65014081d41c0c1d501e180e2510400685a54840b50b0b076940c01519a0004039030300007807143c2080501420600220821110101044403d4450680300d20820000a100510407000c1d00070a500080d196107040250000140e02d4001c001500c40301d82005019042c4124a112040030015208503400f0205002a644440c4603620300001500039180196045051020361080c41c0c5c90070149219a1300054802c8555005407030300b481c14075003031040c050900e501044400c16584c2e010305042d0102c5c0c0b0072a903c04400241c7ca9101110340e611850700c5c1c0f49980e031603801c104000625201c150094100c104200c400403070304010303103810442203800c503226078403003103090710005000381000040502003000c040c0107031a002c0642c18030740034007400960800120b41600d40400e20512140350768503004864204001481c500704125044a14207091000400c03219289420080e241e0250f00400300070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 549511681 1250 549510431 549510443
    0x60d0c050f030726042402070609051b09010e0f1b070506010f1e030204020915030a051f031e05010204080d0512100506030703020306031914010e010e030f16 69
    0x905004800409451202105001e1000c000981010b42003a0582135806654810f0100440d4441010f92901c8285868041c03100715030700740100e2011502e80c5c024001d1040c4140c001e0a0704400072301c80400038085140e101405410f100005118035004c1c21141508030b040c0080402c5075940c0da512100b2141c09a0b2011003030000049500b008206000801c0d40c16201e107003560b011b20644a9108020b1000d104101400c28030300302e241000036081c2503000340010800031f080d82c400e13803100c038454405540c01a40c8000c2060f03a12000c002d8510b403103c50101c11564000300c1c0d2030409140d502c07894070b42e443d030304440c80741010718034072075820403d09504440050074141c003514114010040007a1094100018000c50150a000040c011001d640f09400a440004085504548400d14103d00035000106051b405209a1021903901002c0783d140c00310503403080810a06170240320810900f981c6028010386d029a0615031181d80304007001c000c0da01c00c100800040c0c0d8440c10b00821040070182d81040c00b41a03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 549512931 1250 549511681 549511687
    0x7200a02180403020c120709020d0609060e040c05030a11010305060a0e0c13050307030503040b0f0f04091b092402010f320606090904051e030a0201060f05060d0c050f 73
    0x1000040e0700792030703104a0080e002d581c8544141c83c2401640b85030a003014000d90000441171000780240e03800b511001040c244002074054442e00c028080b58041d0700415010070400040104000803808441c0140c10182c001e00460303400c070b0350303000144030420071064141501d03180081c0d082d48039801c88200400001944560742d050800d02080300358000c11084c054000382c0f14002c03965060000d83d543c00c41b07034014000c51916181090124403900245080089140108085055451408041c1002d04480040003c1c3d2086112000811a040000391814070001c21005c0010407c2038400105151388a070910310701d40c1d24070408034014050507038104800b900c0c00310648144000040d0114084408064206440184510300d1044420403204c640e840101000344038014180040b0300c035080340c0300e10220303034801e11441428028106110030150380ca600109843c5041d41e42400303440024030035406003e078a0780c01e203000b0400a2050125121200740c44810b846100d6108030111100004c2d04c2c054a52 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 549514181 1250 549512931 549512959
    0x9060504030e270103080a050c0d030b0901060c020d02060903030c01180201140c19030908030703020d0305010f0f1502250501020601091a1302130b090a06050307200a02 74
    0x480140056200d0044622074400000d41e0000d11000f182e10071000190783e103503840c5980f0603155500401c6100b04002d8184400c0900305810040203c0581441c1c801160804c10303078040c4801400164015003c0007100300d48040035071150124481c6003501aa48103554240b4500403900c0d600c41d136204240c440d03207402d11828010083d1000001e540c2c0c400d07600c035042c007444050751489a002d08000b0010b10b401c15a080a4111700d100c944071181c0380301e0700b440105c20340e41c3c80005083d03070070031081900980c01030700300000956454481c0d60f0241110750001c4665500b0000b40c49113288541c00b035144a188012903201c0118001c20203000c00c160325240d560180d200c030304003812111110b03100e940e02500c44d00c030020861100d60300400c10744e0800c41440140072180c11040155138080d0301180f1546907400c102001c200b05550100501403c0400d01040d60340984070184021100180e11a00421000f88107004d8065802000d40c8280041c052075407440802014581d8240000c000c0020360104091031904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 549515431 1250 549514181 549514187
    0xa0b120402100201050906220c031104110406050913060306021b0c030714010c0c0803160c17070506212403120d23040302070806070306140d0201030906050403 70
    0x140c8600e109403420640d614104070180e00343c40040d280001540c112800060501c014a010441d201c210004800c2c40000380d600d4100c0c28690a4000f0350300045558101c1f500f81c1054000c42c22510305e403100c09840d080c64500001c01c503010b174099a620440d2400140400720809410a0000d560007103411940c0300250301c28a04c05180c0b0704909a0300d80240510a0180e25003c1003480c100c8202410140515880c0401112026021102100d40d800480400300350380504002500f50903503c020316600542c01400e0035900d45040760b218070007020602e1008080e003103021982d20101c402c19a140d0f9240d500c5040001107500d119841803101044960800c0040801c0b11001012092030b00705040c403c0e40010185601c40400c1e80040c5006c1c4001c11a005203013000b80c0c40b01203a4510300303003603801002c004141c20301da599003038509070300590184000384080101404601e4211b041410f08210041c0303442c40c80d00003030000f005150310400a0174440d1041da4003030340040000342d5100d0030400113072400e440c001d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 549516681 1250 549515431 549515467
    0x20105040b1b040501050c031603031a0904081b07120609030329010e040e06010e01240e1302090d0606150e0d0602090406050a0f0602060708060f09060a0b 68
    0x5071054150034001ca112541c0c0d5140c801000c0351442d001c10320749814500152520781c03000600c907504d84403c0200684003030700d040c10307003020320f00c296804180384940ba44140780007070307030544000d21508060050100003032865040710a82c840808401e0300d4450128103036414044164032140c2e0109041000702c0400013264001c0c80600d20070b480820000c400440e1409004404001206000000c500c0c00c40d482c0d8010480e80100590080020030140d148244141c01c00d03800303034042c260000111005000e0086004042040d640d6041aa501c1c62000950020b01100b41160b0b0107015980300d445080400c6620740440300d04400241c40c40c0d04842007440d01500409441c441e102c5451b1401c40f00c001d505104104613410000018803031101e480080d1200002075104400c0c1035845903440b140051251510524007009040070b4048995403498100080e0803c980100303050100210101046010b9075250401520440c09503002070301075403003001040d030001281d08000c02144002c180704440d404480d02e2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 549517931 1250 549516681 549516683
    0x4110d050106092901080c160609060e0d0f050705070f080a1103030306030c040b04020904090b07090602010b010c062003010b04051e0a0e04030c020d0f1b0501050d0b04060503070602010504 83
    0xc10203101d1400c82802d01300314250641d2081d900e14040c1c003400798030074002c85810929046441b071400000346900c0500d40c042c1c0c41d0880d400c2d07460b0070b01031080c0a002d110354550031b003107031000e0990002603400040110920403a83c0f428020f000c1811010b00030108980000740084d001003881c0282c03943c07022540c6604210382140c030b1504074072080c1d0f8107060220650f801108003500a116964100c420003014111700d02146400c140c5c00d000085440e0759a0083c2e004040c010401c0c00000e0910104c020503010792500402c095a043c00302000e11a41c1c402e400000380d41d00b040000a107280707000203a0f24058000000f00359248070110001c40c84541c40c0005000b110000c8400c9281110805d048001c20b0300700c143c90543c4501004000c00254680302e0409134020f11900e44424808082c1d40098002c80c4048425180e101400101c241041620f14021111003030300380c0d120541c1803030308000901e40c2c803c0e5041c1340e48090b285d10b500d446940350b68104074017501009003a680d00725200c9038024020310048034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 549519181 1250 549517931 549517949
    0xd0f060f180903021e0f030a0c0311030c0303060409140105010b0408430e01060801031101080f06100207030f1208070f0f1407080c10110a051204110d050106 69
    0x20002521a910321684a41c0e55054002c5c01c480303444001031a1044c222150140d00c83d0040e018201106001400104010300b2143c4528000700303080c2c14000c0044c006003600b58210f40c010460341d000c810000080c5e070b1340300800301d07000f250304402071900c000420b2041c0d811018640c207020000c124030000d1303000f410540c0c04002c03c49080b102c4044107a20030500c403a070046280d01d03d00300c0c07112000e180c1c0c840c0f0192000303d051602c10626921071982041c040d090f80024001600300c401401041480c60050348070220910300010310b824035071070408402c40c0c06080c0c203200e1014600e00310f43c410f00a002c03003030041d5040441d014125285c3d007040705041611043c0040081d010400292840f40980214211800c40360b903124004001c142c0d094500e001a2602c041201034240401c1000651080080c20400322036005400c604407802da1a000b910fa0000c3d2442c0c0b0940c040c0180b40c4113507881400c1e03840c80c443d001c8021105d520340b428100c02036a2000c0b815600700e80d00802c40c4041c00f01c150084412104211 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 549520431 1250 549519181 549519209
    0xf0d1a0601020613030903021903080c03090f0907021009051c02100509010c080a0203090705090a0f06050a050f060904021b0d020d0c0f080d060b13090f0e030403080d0f060f 76
    0x106540400c00130800100072407103400e802d00150821525661b86021481341d68550b00da1a82c40f2000d030703034205108034202903100042c0103045041204504400401c140e40014141c10309810294441c1080d81d00803a44c103070b64160480c1423200411401c1690508542c0070b103c03030184004c0003034644c9001c00d10004800e00300301c0404d240303030414030030b811021001c0d9450212940350781a4010180d0304c0070300314200602c60f44101045a5903600c044502034000001e000424600e485c280c2026100545c0c070042c8a110742a0301000141c0b101c41004022090031a84555911007103000038000303003e144155400e0346040114a2240c0720f0028005a0300340c2c150b001c45e15044d1101d04121140140310b1801040040311040311400100c20b800038100303515038050081511074407080c40300e40d207411140e81c4410910400b00d0030490040b540c440e52a64680c0f0040034000000aa40e003142d40c2d22682c40020b18110700040c100300c5041240d0300540380001c007030005104a40c1d407040000700603041c5010b03420b4102c1501c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 549521681 1250 549520431 549520441
    0xb03100c170c0c06160c050d09031a0f15030f030f040f0e090a080315030d0207090e01090503041703040b0f030115030902031e031204060f0b0d0b04020f0d1a06010206 73
    0xb81c2668020b0141d90020f15555694109030f5000c1d0150034140780505c00c5a0500000143e0140b003140014134455440c540d0300c4e0300c0c40c20f01512102d08005008540d1000394148140000002c141d41d9101c1521590640d010924a000c00d1600caa002848140e902001c9084012400500d00510840b905140000061030b00c81030485032400d019101d00da2580d225101c1d14000030100d01c040d50744541000840202d220740c000220f400c2038400000a0300603080800148000d0000388a000d100000c118020408a44517a84040c2c6c0d030312840c01041136004216508140c0d96008200f101c02824201140c5916903d0341856100d41e90420f000f2442e005001c9145030403010303ca4400e001c0e0085d0000c0c0104ac0b2500c2c026049100c41216a808401c140410011440c4003100f100700113004a100d0b040003e14502d07401200001c90b400362084900c20001000745202140c0116041904690100c2ea0080c0d031029400004110003240100100b4100c250200458080306c1011054403454023030702510115568 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 549522931 1250 549521681 549521701
    0xb10050f120d0305040206040b0d0c0201062913050607060f060501081519080313050a06090302010f031503060e0f0601060509060711030c040e060106260105040b03100c17 75
    0x1c01071a00c00542d0165600d07208540c42078012a8000340050251840c013a120741e04500300340d01041c562001c1580f0b0b5801102001e03424416a0002c00300c040da254641b040000504160340c807180001001d0f403801040c140d03041c034101c3c54020000c00005280c01d546200510301360340a0240091880115071500a000446c0c0d4050462603201c1c5085480800c95000c0203c02c2000e03452400202000c0c0114103d004602108100f00070b1000c844420446100d180c501810000e00c46420b030000e00030800e54140420060340c202c02846465181401e002c141040c4060703007028401c08640c0081c0030981801c00010681324003248a480e030840301400d48031070341e896000a41e480c2c45030003280c1e50824810070108000c42d000c6011402194070003800d8940f148001c20005064852084442d4082d800c19001000304981040720090030b0040004002d1a0038080036443c02282c2051040740d0183d030715a5106a03003558141300c801c4400d007804804000e460041440144400c0c4c902881c031240440c000082020420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 549524181 1250 549522931 549522949
    0x4030c0b07081312020f16050a090c0e01050d0b03030703170a0e030a18030b0a0606021506100c020f0a0b03011a070f021c050106090207120e100e030a0b10050f 70
    0x4103103c0d041d001d103d5540d209901c000009102000f1409401c10070902c01c601405030340c00c000500828000d00500702010080800e0f8194016203400745000c0d01c050b42d0b0707900881201c068a50900344a030b204e02403000d03040090000c655283e603160200050020805810035141d101640648880030602c1d0b680c8050b40c0122180c000074040c03545c0c003d129048000744245983c900110514001d031025a95960350b1071203500703003070f80d034490718a441c0c0c0010f00805504101c0060003070301d035410b4000c80d0b00341500402e40a554510b515000c12100c201400103640b03ca030340b04c00d1401c202a0584100981d144d0f41100d80e45c20a0080d02c003900184034114503081d55400c02d980c00c66800650801c0306004550800194401104006902c24100d9080d000401d00c28403494004042c50900513a50786180c2c5020243e09030341c501043c4c1482200c2c00c6c040c443c1e440f0000007915003241070401c0d170090301201000034901084d0f03c40c010071340c904040030070810420580442e01118003e41c1e903540c00f100038104106144e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 549525431 1250 549524181 549524191
    0x40f0c090b0904021002010b0a0b0406030b1005040302150c0604030201090b070215150a030507170c0406180902010509031e06130314130f030609140606060a0503091504030c0b0708 79
    0x82d1103802240145c64151508030017584140000544002c049022410a48084e40b000704ca1000c003160800036113070503010b50841d000044407410000c40794175030090402d0140303000190250200c40d00c82e03080c10742d503101140c0182e0900700c1191803500d040d140c000d018003030146086452000900c0070401203800002c00705010182d003450030030940c0e5203004d041d11010001d840c407544004e02c040d00102180d814426900030b007104c4903281c0200d01594104c0c528105041240c2c502640c50507000f0001901c910030703c3d041100060b100030824410f035000484980c01a418801d505009440841502000300a0031322807840940050b54010368030410f40040200d08004040e0104040641d00040d0301c208000600040000c9d50310b80c2251501c0303500100481d0f8268000f21920b03555000041e0034007103002100601004004003c11041c903040c00400ea1074000d41c0a01000d000c40030002c10728208041c002a54060000070200282e864141001050480140c03801d55202444802040800d0b1103600380a1003a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 549526681 1250 549525431 549525439
    0x18080d09260f0304020a050a080601140a06050702041505060c030a1d1f090e0103320c13020903010905032502090f04141c030b03010e150c12040f0c090b 67
    0x21441e02c0e522020b03568030082c401c03684903004c010049419070700c541c0c55102400d8207034001c203655814181c81c0d200746200d0240b600d129034424841041841c1d030010407104c4040c0c0c10f60700450b61040213503007618241c9054200c10307400280420b400c0b036180c8001000d812100c00c50b40c1c801c204502c7c100e00003082c6020f8100b8258004141c02c03e220a1040610581024182c9600d480c100b65959100400c40815080c0c004480300038620b07080800045e02c07001e110304628000c10254801d150289400c80d600c4004100ea0b82c000c4620b036140e00103d101c242e05031079260b803002d0002d2080c00750502d08162240e0280341c207040441d841421080e5602c800d00c071540c12103a4007804689441c2c480c038880c0c0640f001c006004460400a01b04103120304402400041003050700c00c2e40440d498800340c880501075030a90860680280e15101c0c1c4811070000c001005e90007060b42118501140c0c42d1040451420303c24498140c5040c42c0b034034244400c100458a90010640c017400da2100c905844000000a58210003211030340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 549527931 1250 549526681 549526687
    0x30604210c0c030b090f0a0b0a0506010e0d1103030d020c010203010501081e040308130213090b090a030503010b09062506140103030c03142505060703020c0604030318080d0926 77
    0x4c807041c02240c2c012071240203c40c0c200020060251410030400310450310041000c052103843d2649020780c40e00441d00b400c1000d030015607003001c69000110404083c20708442040114039a40301070049075800da40403002996a0400c1d001014041d5100384115400202d40b2400a268052600c4001405c40e03204504550705031034a49045131003540c00341124803605001e80070710700181c0e40c1400301040f620140d000816030f40c0d090300f01403803c080028884011500051114000258054100c80c1965640001c250302e40f616840400d0aa000301400502d071040d80380c05103402050080d8041c030000c2e100385820b0218065421035120900020f100040200f00540310301c0740040c0c090070b240c4030080382142c5001e04214406401c02c4030580b00d6907550046240d2450a4402d20030244491544803029040a40c680911040381c0707550fa0310b00803c0a8101540e8040303011040061680c00d0b1849600b0006c4241c5070a007002a00b0010010104116102c1c0c01148501d441000c6160070900641454151f56003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 549529181 1250 549527931 549527933
    0x2070e0f1e04020f09040b070306060807020304030f080c01060803031603020901050d0b010e130c110c3102030703020415030509030d0e0115030f020a08011127030604210c0c03 77
    0x1a488001600c03ca0f071010b130480310500242c079994a03c1c1c0c480c0f0b01500f442846030600742000703400c4503030036048038003003200b074000b001a4142c0000413602100d602045080c2c0611301e5061080c46802031294195042d42011000100a81c00101940c0a242c41e000c400800b962818010743c1244a941e800da400301d4024049d0000789819940040e60820040c1400351000c00360348009041c0c5041030410b007a6241e500d4030408809a0f001c1074000006003101c0c0140029440ca2002401281a007a034408464070070320504808043d0710030002c007400e0b80c13202040d174a030b00300b40320054080d402c41c0c0121005c018400d00703d4200b140c440c0c09101e02411030540030b5850080740140703000c05444e4040e0105515900c031051a45528503034102000114004c004079088003180744104010b101c070a6218000c20380c103006140368001d4000044a01903001020f041456850303070a402c070000900750641030381c980580303c104001d200d44d9074240543c0d0001c0d0b8419843d090044402510030318540c4d0000342c030b24201342c50284 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 549530431 1250 549529181 549529231
    0x3120319090321050613021b07140f041509240f0509090303010305060601051c090b0a050106090b0f0a090e0c180609010509040f061502070e0f 63
    0x40d001440103680016261003904003505441c80100100c0002d070952411a85486014402020344092a5400c0c0214200b43d400034030504c0e03030701c1ca520038610b500003901076040c03144040c1e02100342000015120844d640d04052180b0b04c1807188a1030043d07050700705104003032a2500c02c048442102d110700444803403c200010004100703407007581103003001d18031106100e49003140c0b0150090603c01c8040010f5410302040c44900c034009080410706a1080c401440000c0c40440c0003540040c00b032030401c2d11070500c0b03800380c4007216200740c00d080c441d071803d0101401c0c0702111000b54410590000300b0b000c10391341c1d007000710340e00700f00e84c0300711115242c09100303218680d90030310001c09000c403052a11814080d11284c90041d605416900c0c000e1310600010201c20740300034080604c096000444d5018100f14031040080c0151240303a10080c46aa0b4940140c1101d00e000d41c00040980884003c0800301e00d480000655140c440d0302501460106000001d440171428004003846011121060624040144515 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 549531681 1250 549530431 549530437
    0x11202060a1d041508012712030605060c0d1103040f0b0f070803090f07120201211104060c0303050f0411060a0e0d03090e060d081804020d020705160f050312 69
    0x142007002c071a81001030a69650040070050500d5075a010030f0f0038034001095007140d4840c0d24181c00d00a681209900e803140030741100010682101c0b24460314240700038200d0050801303405c4140e100038041a0100701e030303000190000d003256203a180d01760300c0107420103001c0d56409144600340000641c0d000038415842400041c202002140c46010704280d2155285080b07a0011560104c0307583c81703462440c0880c036081203080020301415580207080c408a0b000241a00e0782444032030360075850001a580a00e1159203c01c04141d64101c1c1c0b5516207444000040c04ea800401d020b40000c3c2c1410041280980d203502c41901881d4000390f0386030661020405c2c0611a00f0038140700382482170000300720301c081d2600b154001c0468465904e120a0b5810b01c00310660ba13080c090b00950040850400280018102c071003100d0b031200005c0c00301140c0c1e40403400058040d101d001d490b003c45c140040b807120304000d80000e0749130302080c3e5181341c510031035110300d103003110342c0514852243d0541c0051052100b00f0709081c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 549532931 1250 549531681 549531707
    0xc0c050718140112021507030503060405131a0a0b030c1c030c12080f0a020a020a110d05120405040e060906060f0f0909070611010b0a0911160b0402030105011202060a 73
    0x10205004a150352000b110328026409800389046200300310702140f40000a2944202c8402003003030070400a501c004100e0f0200a0595000d1540c4102090a4000c1c0081d02c1d031009501400710154000301c5200807081d64001e0b16181c4003103051800d195028500419807102400c8007412010a0302180c0f40c00c20380380d100044080e410f003e0340e041000041003e0340f82c00c851b0f5010030740b5886820f040201030710b02806001402012000c1c0705005201e44581e01092484040f030f00702e00e6150030700e41d8a8001130180803c0c1c660060551042108081607050f502000c2e0003281e50441d02044104d640c901400e40710002103514080c0782c0c00142c0060f2036490282000c51890b140540740305410ba039207002007001f84c0e07419120f028203680802c400704407a607804208600c5e95030030f5000900c90b20a01a000c95036100550050030480b40d120001240c4000c04c041c143c0f0584080c1c10700d07004202d0a50b00f88040d0150045e00c06a010b542000000711301e00612440a40e94160b01801861605444440807508040d001c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 549534181 1250 549532931 549532979
    0x60a0612180f0f0516030201020c100210060603050105100c05060a02030903070204230114030304060c050f030415030501120c0302100e060a39170d020a0e0102010c0c0507 75
    0x881c0d002256808825900b2140b0071142c60481d0034030360801c1c03842c0004806140e40188103078001440141d80c040341c5100040002d0b00c005480c1100700d0380a81c24466140041c0201c14a40b440c00503800b980350b04003034101e400a4880d1300506000400403550400403903005012039110a010801d000250303401580e029204030b05582c1018200c0d0300090a4901000841020f012502d07204107000b80400c440600504525070141070448281002c070b83c41b800365105000920606003044028080240040c0c03506940388002e50780e50f581c0b80e4145d4094035074035149400c0021301e000008188403010340d0f40d240a05070021300d05250286190700300a0010100800b4508100c0d8011500140e501d48801518000441e40c9841a58075a5100d40300c071012401300501f03000c050a00080f424030b2605015507001240c10a411210b00011f490320790381e081c85210398807040c0c1c51000602c408400d900c1000781c08010400d90003407122445111007100e91441010000d00706421507807080050b1034410004203014602d600c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 549535431 1250 549534181 549534221
    0x181c090f03061d060702070605070305191e0f1421040b15010507020d0206090d15052521110403053004031217070215060a0612 56
    0x3054000382065034011a07181d512900f8032400000d00d403850400c04070742800244420302e03107058020360340c02640c82070109200e000160b00301403502c01c00841d0344509050101b080307984c4000000410581d001d80101c2c2c0000c54400b03030980543d104480118414549580b00c030046080b1000307070402c80e400000c031520281400702c904540c904112104510541c0200c210101618000c0042400da038428807901d81040300800c00000142c3e1200805480303da010f4400702c1d01c62882002203000f28503006009807080c1c030a1803250902804541066209828903202e07541d6202a103000c0f681c3c072040b4040b072035012030744070301c0c3c0385800c80110200000440341c001d078082442c100b040d00500041d8000e80040d2410780182c021981d55100390302c3c00038650950301404040d24100d010100507030703000741d01000b03001074886e005695041d4414a280301300c0d080c1c480700b4007040d03090440021307542c2d250340d51058035004a41c10000c0e18500c0d1584084003103a00c540c0f2101c1103400002c003018001e00f9904100070101c0018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 549536681 1250 549535431 549535439
    0x6090e0705070b0a1a0f060f1e0f07030f030b0105070f150e0a060510050d260a0203030a050601050a200127050115031703090111130e181c09 62
    0x803480b02400381d2020300c0001941d0f4000800060f000c0d20701c4032101d0041c0030704800700c0482d442d036500b01c038040581c0452035500c480000450740308410107820304c5278100708040380002818030400020325140c2d1098803031001400c1e000c803040d403d0b95038541900340802d030240b10702404504071201c01090749101c0c440044194148200c00000c07111300400c4002d050f40301e007042c032007007000c28455150000c0b02e403503501d901185008000b412840c0f100c1401007001c3c401c2c0940d901524010040000310a60702c02099485030618500203659800031604c1d550980c0c206804592554040d100301c41c421480e40ea20344101240140c86035101644072764130000c1c1c42d1b50f10820b50640724021400b000030000000c0707151240d10304504020b030030358144aa00e03e2048428200800019410030411145003201c1c2d0704031502d079a242c0a0190050000d4602d0f004100310001d5802d000050300800f50007940c0c518420710403240c807840000c061841d00905aa003135548034080701c650000c0c4030b1100d400b4040b442e04c0c1031060a0b4407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 549537931 1250 549536681 549536693
    0x31504090f0b270c120601050d03180302040c080a05070306080607032f030f091605101b061e090f060902150a0519020c0f0f010c06020403080304030206090706090e070507 75
    0xf01c409416865005003800381038070f01c0e10140c0090302130640f0b0010031040d414000080c0c2c03007400040c0c00906120300c04d40508c880300b0b200f400c510001c5030024070400800e9060040908060422540201042e15000028048502901c41c1ea006d6600d40e100500d400e5913491025401080c0340258041d03080601050b015985600e40c0c0c0e120120059038140a0310b0b03042c54500281412800740c0341156035009400005d42210445940000702c400c00c03107101600c100002420780392082d0110b091403940715180b0302d1000780542904002c0b5031404894491a03110f262005000442d028610000c200440d2083d941000c40c2d0950441100140000c102107130785035030010040d4280c2d0240c00b0520102e5004a0141ca04a20a190100784000240007400a0803a01d03000508516110285217108a41e442c1804910341d20440d500d1400c2903005404642d00ca8903410200000c1e0011141100144118400200080d4000c59500101d404d1a1a0b0032422230406a031106166002072428041250900500001c035070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 549539181 1250 549537931 549537991
    0x8030a0b0306010b1809330d030c1101030c08060f060c1e07060e061e090a030311070b04080607052107081509010f0b0c01020c0d05031504090f0b 64
    0x4107003900320355031040712605e417121191424000e803250003a8030802c0650b9800035007842d0500c0c4e40030302c0181d14801e01030350304180c070420041c15600700a0001e903000070160022403005809005580e040c0600c0046001101a00c4a00b40b107940055a003201045083c04c3c00406010011001001c40b810084014005440c01c049820107a01c0c886020300e202803c100180141c0024081c1440c050f4078180080b00451450710a00c142c0b580301c0000780f22040140c0401400307561900000624020b2405d9581c200100811502c01c0d15110380c0c09103803400a070740360a000482d012074040f640a8062640e0344d840961b041d0b0400c91240e074405000900001600c0d00700e1002030310901c082c2c2c07107040c55424014814000e009030900414000c0c0e50b018010b214140380080380030b080783d10903605240c0ea013040024184c0a03008005035112603114816100031080d4120003c3e500c9036072980a1202c0015000f020841956144c44018148903200070f03114000c1050040d5030740c1d2155002485103902400020700d200700c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 549540431 1250 549539181 549539189
    0x705030a0f0c0602030a080c09180910110304031e051210090e010c1e050705030403050d30020901170907141f0807120e010504110303070f08030a0b030601 68
    0x441d91020000704420b075845040035002510007181032404464018101c090080c101c0ca001c1c11001c110b480701c40ea100000c20b4001c3d401c0c000b00da03051b420843c01c0c41e40c1c0ca44c514103046070b41c2803e11031520f580c00c164805403403190717406070b5684480c00782c0034a500c80301c054580c001034100003040000142882a6030743c00303402401d40c103000c6e00507245040b00d84021510b51403048446a4180350170341e490749074024040e1150241c00c031032440301401141015100751085803402482400082400001e07c40c02080400c10303584c1503221180b902d045500c00d4240c540e04401074205240400151100d03030200d038cd01030b00c0c02403018100b0300310700c00c05254070130844a0111250485548500e83c1841031021300200204030460581d070701d003c10644d2803160910340000e40148010002180d000400c1d1a100344226007113a03190140402a028003010054040d200846003039408c020040500f0019040010803194203c2d0407083c8062046815550119580e0014000340c5580c0e0b2a403405010030754050200398020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 549541681 1250 549540431 549540443
    0xd06060507020f010f14090a0305010e030408150412033b010606032a03090f0b0708010e330618040b041b0c020301180305090103050a050c1b0705030a 66
    0x1e40c2452041001c03c4240e4462541000103400d460700c2c003150824000d01408403008007030707900e428454010030110041c0390b101404540c01c1a665600902000c0001d01c144c1d405c0c58251044800103040c0040186802d0310700400c0c4040340e407001030070302d0b01c030368042c01048404948003150100340314030055050745010a8015400040d007e590f00d000024800e080084c40345081c24480c1395030090404030071280b801042003056000010b0170401911a503c18019030398407900c0c07600c02d90502e04002ca80300e0001c40704800482d034640004542441d00d01400c5200d0a5071035042004403403a90341c92095100e10140c2d6421440716100300c4002943c0e00c00280603241c0c41c0310520740c214403c0d01c08100035104188015406603161145e1200d480020107c803031820f00c040c0c10f2402c11407400303101003070050264141c50002074820107460020185d014000b00b6100b0f100360380074040354036944c250030226101500c0e810b07a500400c0042da0080140c640311064421845425681026910030100341032803c0c2c02022280 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 549542931 1250 549541681 549541687
    0x130b0319061b0201060506121b2208030f0d0c020c12100b151207090e041202010c031b0e03010e060106270807050f041d0303090f1c03020f0d060605 65
    0xb254490329030b04031400045200038095545880003103000da105100b050802a80a040060f01c41c1c550b040985002d0405403400707640d207490b1444400c41c20080d01095131040c2885000004004800000317071801d041c4039500301461301c4400741c01c2000811150110000394000c0c0400091590745e4418160008411180034104411450427400d00b1a52160301c6180310302c620b03d9096181080001c15644003464005081c1020780b200c1400752600300c142d0340a810700c105240b04000c10007038810341980c0e592400e5002030014814500040d415106101400d90901c0c05100000d4a45071280300700307510000c03014000051000001070043e0a04900b40c1184010464204d81d04c5402019401640360764280f00b942007031103d0030150074a40340c882c2846450301ca90452504180c255079250b100b080c940c2c88421a5142001c900032aa5450303810827101d045a82c0140b44994090510104080100c80c0301c40c180029584140241a0700039084a014540c07950410310040500070320b5481641c0c0a03041c0c684610392 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 549544181 1250 549542931 549542951
    0x207050a060c02010c0f0c0506010e0702161401080708061f050f03091e07030b0105090c04080d18050d05030904020d090b0108060a060f080a02010c080c01020f030103050f0c130b031906 81
    0x1507141b84088410081004604004103001180d035034190366040300e85409984542d0400c0789840034641030812a46100f017000202802c2402401c0500c900c2070300c9240f52039458620965000b43d0803201581c103c13100903400c0c06c400da4103560102001990781010f0781402060640480d40b0340080390311180300d62040349100010000e184100803081c0200f0000c000041c115503540c0c82e02101881480c0c00798841c14085400c40b20444141c6018118100031510350307011159000309012078404091780441e20808000c51036040c0207031015286600076004510f4007868209008c000c0d8020744007100c4050f03407040400001000061002c2c02441420010012401c0000a0000b103640d40d601c8181140010310341080300c2540401e00b01031564090a0100d40c030b43d070340c1c10180400d200700d040a4000b5440080c507628159101c00c00346059900440c2100c0a980c00050090b558030105403500b6480910740c404031042101503005030341008805030a036010001055110200c0d0713203001408840e800d45501d5080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 549545431 1250 549544181 549544187
    0x1902060d060f08071a04090c0504183306050702060d051003030f032c010f110a0e03070503060f0a0608010603140f01052203091203030e070b09090a0207050a060c02010c 74
    0xc000f80810b2445e02000c900d100c80300c00010700c1035104c0c61501c1c1c0c0d1a8000e003011b05d0701410581703000705070340c40280b22181ca142e00090002c00058000c681d140c10611103c010340103025101004140c004200b0112250070404207442541050b801203a1280301003001c0983d0321700ba0300074036016840070350940c0e003214214500500122101c0381f01d00109031502c0c0f611503441c140880b142043c45210300c0c80c842e04804410256002d420842e10604556042c00e007106924264a00205441c0d85a0b0781c501001409074002c1584620f61072050f554103a005401091751004180c80d40d9402c40403803000001d080f66281070160a4070302d264400daa4000419100c103021301014020720400e621000000c010614240590b104401c2c0703000010040d41e20760119800c100350098000030b0150a03501040e04e0701240030300d030060190004004a0086000c0c40c2000940a40c08e141610340119004240071820358494940200a40040c102541c480c400d51000c6d0012464502c14403280c03441c543c0c004110f5180184002e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 549546681 1250 549545431 549545443
    0x20a080106050913051305060708100b03011a13091503150e060f0a021611031c09090908040504090c05090c2514060c030a05010b0306031902060d060f08 67
    0x1d000303110b4100308910081d91450034200103004e403010001400c0e00c0d05603842c00f0b107441114008180e072042009204605802c83c00080c0b00e107005d110304005c010345601004100d40003c3c0b040306210f2140b844610b423151103800181132541c7c808034100075026074601c1d042c0240c0d030880c03150441c03003003c626040c41848040c0b04400d040c82803024040c400e55441c025001d43d2100002d0100308002c0750386020a0b1405081d804580c0d0040d408001d10107008110b05181050f071014071500383c480c0c40b44c940010015580c0c10036480c00f003000c03a10740c5103940d80307422a4a00907084075a02100d1200b01048041119601d40c840c0c1d09141d0300641314484124209414010710001c0500300da007658a013405005007107034502181c83e10320301e0b00e074860322009066443c02d15207100b541c041618170fa000e8441000940301c1000c01031740c803c05048109000e00e0f60b0341d070f02c429485d100030788003640c150b00001e040b030106104003281c3c00e82880c8060f052526168005c01c1c62405caa000f41c00c000c0141c5000f5000b000000300c10044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 549547931 1250 549546681 549546689
    0x5040b310612050c01030507050c070303110607080603060403050a031d0604050106050405090c0409020d0b04080711011d01110c030d120f020918070e0603040c17070303140c0a0203010609020a0801 86
    0x81c14524002c26141e03c0c0d0b0710b42086140504140d107840024401c0c3d4030aa040c1d4042c4100081101d01d150744904d805015501a010f5a03910740c440d610009130b0080c844c0d41501d01908028000d005191901c1d10101d483d5440702c8182c1c07041c0b58031920b0f0400303803032603c0b4110300101d003d003800b51907181014034050303081d2811b40c0c0c00303a03100b00d091178188141d80201080180c0c80350811500020040068408070740041c4c0c075044064504010141000248030300311004003100e52003555403102c4614044015102e00070310000c0020b65100e00a02c0300c2d0350794040d2455603181c0c107511040381c0000c0d003080c0010f440d00c0c146416880010302c3c00c0e0032150f50040c0c94010988650341d00c000543c1480c054501250340040e541403034032080010341c03004c034100e0f6014298818540e180a001265a864035003880b4024280c1440780e043c1c1000c4103008418006004540740059079455914801c01d41503070074a40003da0007000d141c0704940514082d0000603602446024000c240003500540c4800542c0f80141c070040051b0300c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 549549181 1250 549547931 549547949
    0x18060e1c0b06010309111306050a0e1504020306190323010212070e13050a02071a1e100f151107060203070602030a020f1305130b060405040b3106 64
    0x18400d00000e040c50750090b4000c10a10b00000e080305903007442c003100410810300607003081d07511a050600042940150041d160140c450a2200c2d681d01148010682c0486040031005100000441c9501d06030b0015038110030300400308410311801990000c00304400d039004860030300d8102d0b03004400c240c1c40107c0c0e203403210f602d600071806c0150030190303900388040061541080044001c040307411642e40c0801a0820b040b402d80402c10b9140540ba004000c0d4401c4d003040e0303a18060100d520403d510f003d200b007440f6200c08240070704481c1108654424a500103814402c11440d40c12010403800140ca082e0030060100003000740d120402e00c0005845e0030503c0601c81c00c01e4000345d03c14800142c0000445201c564050030050340e0350348428022000780103008003c01c20700c00000361203200f510040b8412094403001c80d5152090251809400211420003910503040141800304006914250340000105c8101800241f0710182d101c10b1076466140b01050210003c00642d042014141c1030702c070702005000c0500c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 549550431 1250 549549181 549549229
    0x190504092f0a09051c050303090a0c0f0302031510090903020c13050603031603030b0607030e150310120609050a030f0806090c0301140f040c1d04061401050a18060e 72
    0x1c00c00030910307085070103018016000340004c2c0c50030221200000c0341700380d0880203030b90316424821845a00c407418a00f054540707031940301c404500025518071180483c0d40c010f0007402d42540c542d2404184032070003090f2944607402c5070000240500315000303808110f44a54040c0200603050410083c480f00c000007111071503403600d001c01006441c000110b403c40760051344c21074404a054541100606110480d19400090102ea0b074000c01d0340101c02114274040c02c959800b0400e05030f011803c25404119403ea904c0001c15104002001d040300590440600601000c18040c0c000c0d00c0d00d41c9400c9154600306c0c0010101c91a608a144e4020a40d035000f41045440b40050b041401918070b050106000d10228000316003c0200144d981800d200784c1f064001d00240050404042d000c1c01745100c2071846401c60400d010110400c7c54903104950559540610903561a204a001150960850b00c084000c0c005203484c240360498820030103800416256075800e0402001700705102c41c91582d02c1140c2d5003a0302d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 549551681 1250 549550431 549550447
    0x17071d040b01120f0c0e0a1d060714070b010e090d050406200c030708100b03070f2706120303110702090610140c0d0806060a05190504092f 61
    0x301001c1c6044035581d001851004030a03041800416540c5100107044a00602002442d5003031025118031070400100e00700021501061206c05188000b051200c01350045c60000d824140519481c18828003020070301402c1c5603142e500c40c01c44181c20717041030b05054000020020010410829884001e01d60b1500e00d042c42d1400c00c002d0100c14660350007000c0ca103055409000055001c1011542d110340c000c0c1102c203c1641d5419554a400c4e0009110b9011418200050010704000070154103c1d1490321040000360f1510000100c10441e03403e580511703403c80000d6810300750003800340b000980001d02000c07805c0700d21032a000e000c41d00c0c42003580507082c00510150f00981da0381c6030001c1c0c0c090820b50f00b015400c20070b8802210f00e0040e603031514015400c04110f1f1004104002100c0b01c0810315501d40d10110740315902000400d004401c1e2820001f8020003941074000c417121103000c0c2c3e544183c1040ca0400707403034141c0041075994a1125985d507103111030001c1c405141420b042ca80c00111504018601022 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 549552931 1250 549551681 549551693
    0xc0606181803050a0507060e031602030105060f13050903120903131a12040602041805180303010b0403032d0309060f0501140f060d090506041401023117071d04 70
    0xb480d05418140000421080103202840d000030381180703500809d80380e0740c8a5603134412036600d054007000e0b8020b42c42c0a0005001d810440015a140e0200900c2d60040101111900025150041003150980018400f01c1c003030f259852035150042c1e00c0d1402464580035207546000485e80e03a5440000701300e220004820700c0600e00011140380030b5400e21110f015036158207201011b48103982c8645446003802400f1300d8a000d590b8001ca010b0030900326082107503903641e20059924042801071000b000400c000030400240a400c103042031100500040382032400000c10384e10300242103803840c00441e403604103044c108000b030b03c184204a51100d00c20841d235410b100080d0484414010414040c00314120309010070340d40d007000c1d544020340000040c40702c407810f864460f4a502040d40c3c111215007043c00240304020301030080d545a0304101d01c100390440184180d9032101004803001e910081d090800228083d03840c50b40410399201040b0040c0341961401c1160310303000c41070384110684070103510300b44000190 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 549554181 1250 549552931 549552937
    0xc04060518040905062e0303021c09030203150906070c03091203020111031017010e15061f0504061412012c07080a140708010302010503070c060618180305 68
    0x7241c801103108016108011900401564074041c05500c01c4408116601c071031904c1c4c807503031b45007042950701c01c264080b4182d0000040350b004c000d0150300915504170113032130b082c1c082600040840c42e009414555a0f00130905182130008003492001ca0034007001840102044669002812881c1008843d649078a000b40801d8040c080c0300341040c00c4c0c10350402454802d4204030411140d40801594a0505040380407040c1d50318450044584504480c02c07034884030621904d4500d03020f40d000342c0b600c0c00c0c018061048841c00100340c01d074000102c8001c0e0301c00d24918000040031490329118155034038105000a00403031510125031040960421428507004541c00c2c0e080d04448006140500ca44c920501700ca42400c02e100091145103030038820040751a030310124041c05400c5d00c40c010403400103429802d08100c0c44c22240b500214205100400041d480396008540c001030714904140007041642e103107800d49510341c0c80110441d08080f80030100003150322421441a041650310070800510b60f03809001c0340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 549555431 1250 549554181 549554197
    0x1c02010e1522080601061d0603060d0506040605010f120c1a0f120105042a0e0301110406170c030702100f020d0504060906060812040915030b1e0c040605 67
    0x41d1100d06074034018000c0780c0950701c011018508503100d49a0380c40e00c00e4034848041c82500440d01c1103800000c0c9890040c0c1c03080d8456440b24400c001441018030a21134164030183c08260010071810058000c1041071020701d006505ca80c20200d0759500d000484a9a000550014600041d0301c8192000181c01d03000302c0801c40da20306040820a038614540c0c05170078003600124001c0981c0005082d000810511703e03a078140c49044604000c2d050810500382a40614120703803400c101070401504141d14000d50030f480f03000c280203001040d005094107518107203400582c41030010903a20301e0210148010100703415840461020000e085103840c040c000d56800481c0b0700a40302c01c0e0303500340c0000c0c907464640440d10442c0e030040703082c4054101703894400024200650240c43c501d18200011400c00e1000c41c03181b070310318400c1001d281460300380302d4054000e0943c40342541e00080d000b03070000000b46010070f84501c5250045021010128151a0348a298000a101a14070441000180301d5950004113440d450 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 549556681 1250 549555431 549555439
    0xb10030902030705030d110d031b0e130e070302150a08180309091e100608240a0305060601172502210a1101060b0a0c21030203061c02010e 61
    0x3646a0002c282406526000b46415003c3c0140036450b054105c49485072182c002401c840782041d4080c8110b080b1000107800e01008235448401000f402d20840105401d80c40041c07403120444441a00b00003100c02100d1022a150840d510420135450146c2c0041c15005001010328030785a0355030b00c01040802c0081a840c100b002158a01405500800540745c00e880301500703004044c10001d01c1201e1158140d440031030707040482d00000300e07a001c01580c44d104442a94a03980c0c1c10344c03103e85102e005404900c04e541603881045030500c45c1d42d61409011802035000f2005082d040c2000000182100c5142c07144506100c400824041c0c9402110811015840c0507140a01c02c8100b883c0b080b070070000b007403028091002c42c44501d41d201f0017500b40103000c03a11554880c2800d24100c0708585003640c00910941a00d0f40f824400d08003143c0c000c00509124900c60540740105c0d1074a00195400240b2440b00200000d6012003005402d04081a40c00c03a8005107041208503d945035000034401b07a0a810760f1401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 549557931 1250 549556681 549556691
    0x60302130216241a0102100b0102011503080d06050a0b030109020a0c0510050f060a0308030115030209060f040501080a0203090604031404210203100507050d20070b090601090b1003 79
    0x1070820180c0310382e0205a400400c83c0703110012000c001c0b1011101d40c0f9201c80c5580390000d404e00d4010001c0004001c801e040c5c01070040c0003160075442004004a880881c159500c3d00c04a103154003d4503819406184192030a940303a82000c0214000c5503400e0700311340e0069400700410b1040051a1082c2ea0444440ea180543c1c2d4015444086440c286522001031030391150180c1c0075140e8209404c0b45200b02c2c11440700203c195122000c014448031a4407025180d40b204100503c5208441d10018089800a007005841d0421a0000c00c45990010b40b440e041403030089002e000940c0d0100044d5001142481c0075030075400d00c1012141c0318400580b00409020140d00c0910003c21001c003036a00402c0a004c082514561409407101032600303078003040b480b9000f41c20700011000e200f440360741c1c0580340d00e940700c0b4241030071440341c039000303081d0311080d042c8501e42818141c40102d02e6a0003440014401e01070780306030341080d42c0490300e4804113800503000541044c4002016072a0181c0c12100c01401e49404a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 549559181 1250 549557931 549557947
    0x20d0e01020723010f09051e030f1b03071b21020a06080402010e0909010204032d030c05071a0a180503030a0e0406120302010b0108010f0303120207062a0908010603021302 75
    0x200400c41090f0700c0c80c5e014180900c4005000c0301049110289020440c81620741804009540d200d100301c44514415031400d00c423904080c0b010142903262841c4a03401c0342d107400c406440360401c0d110006c918a9003600e01140034002c4c5016a401d03030800c501e8208001c9800741440d0b0020b4400b2049000e4041003004803c001410b6a11130691401c0c0500007606060740c6084c10f2a459003c5d610074002515031403a62103400040480200d041e2800c42d982c800f03001d0394594165021120806802c1040d6a68402d070400800c0c174003028004021901d080b4103050750344000d812406040c20048442140f1030102e03c41c41000641c40210031502c1a03111860100c4140298500080c010052500f00585a005101c120401c250f015440007114036001d0700c4030170281e80d90350340b44110703450180401000114101e540104c4010709801414201d442414081200081d0004142c1907481c40307501000d0201030211182660b50b009025a03000e041548000c1c006682141c0103c1d501d103c1c0b91010f210069130019840c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 549560431 1250 549559181 549559183
    0x601020313092702060a050f07060f0c0e0103020c07050f12160512060739050a0201080a0204050a030809040603050712020301060f060c02040506011803030201020d0e01020723 77
    0x4041d854a01101881c140e02d5001190040c041c425208103007001403003034255240a0b980f42c500301560b00400f07091504004c0fa80480c0e498100c14410f01c4038800c02e02c10a00011024000ca800c2c03c4444200061a460841e500510081510035040e052520411080d00d407850081400410b0700d5007983c4000384241c8100119030502032486c4903503414001c0d00d9100035000a1079880d1000c03941d049032042c001d04505450280c6580041e1070200114081e0340d0860380c40048104080f105280d0f24000740c60341104a0100e0183d03201010742112240c01030036500c0b0443d0380200200340c211401d00405c6040a041c140820180c403001d01001d0002c00c4e01103840304071507645030094800713540d100c01580c020b5582e407910070400f0144143e04030b100c1d508082001c90000c074800780a03400c40e8134036500c004882e1626000e0100400e000f1302840e04000a50013070400300304070780c00300000440c403990005aa8803007503019842150031000d220307945640104003010110740005010785180301c2807031400c0c6407465101030309 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 549561681 1250 549560431 549560437
    0x705100501090207151109030a1407141807051201030f02040e0601150e1912150203040305040504020d06090501081e0106060828110702040c2115120f050d0e0603010e06010203 77
    0x1f903a061207916200000c21148850300107000241104403880d2540b00c041c0e406501d928844c40075040f41950301c13080e0a42c40d0141140750006175900b4464074240342003c0c00750366260709030400d07280500c4141d03450045042a201e031020704d0002201078a1154108280f1405000c070007052031081110407c9080d140707548a80d03962070303d2000b5800c0505180d945440014203c4450002a0b9100130515800b0003024058002c4a12507581542e9891800d0705103001c01000b500a09102e403c9a5039401012408805030322455000c0c0448070010328a00c2c0e03444181e0b88100801c900f4586440c0d040210420a80380c00041c2c5a030000c8020b042c8e00d0001c00b1070251084000307204403802d40014180b08002962449010080c003885000fa070307090201405403541501c0100020003c2078018202c500407924000740c2c2c0d030007001810f1b605280d807125140d41c0d9aaa0744448440a000c4d1000b600540e080c20030010104056114070340182403000b581900b280015120740014480d00046512440000ea81d0380e00c00c1c030807 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 549562931 1250 549561681 549561697
    0xa08101e05040b090f06070801060c05011503060617120d0c170c030403170708040303020c0c0310060f050d030c1101030912020607080c04030206070f1707051005010902071511 77
    0x411030751800342040c500040d42500c2034211401901e1034440c02d40c8001c952036200b902a9101e900b0b4991800c00d0803148401d0800c1e054a59560303030b02000100c500140e5440b8000c50044002042c61810003000404c4619140380241c0d1643c0141040c1d24102220001d940006481c900300003014a865402900c1c14070b00c25003401031550100d000c001c424440d24001e54003e40c0039543e00100403481160078000c040090340c2c024003007200e0b030000a00203403082e0018414801520f068400381e40c05a00032a21b84540c64900706c4c610f9484090034003842815401d0713070006202c01c860b8036044032100c0c0c40142c00500c0304140900245481260f0030096402031300a00c0d10154011300c5a40002d004070300003074440030180d4081002440c2d40000c24410806a030613581982c1d0010580742ca09005596002646d6910100864000b402c03100d5800c0021142c40143c40103c0c000c1e0054024844100e4404d000c607030b0141c1094841e1403040c010f040115181c0e45070012011440300001500015010440c1c02600840e10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 549564181 1250 549562931 549562991
    0x20603040f1e050105070509180916060c060c051204080309161202040b011404180b040c0f18030b040f020102100e030405030c0a03031403100f0303110c0a0810 70
    0x10142c0c0300c001c041d100c80340100001c2210b9211940b040342d0350b100700d238082a80490744030031603180e00c8144018244c20030710301021a4004540e06a1000e868800c9a200700045200380f440c42c030520440f4041e103c40541d903807403c00d18100c045c1000210b03480f0003070009800c80501200003540700c6000c003d103528404418000034078999030351f9a405000c0b041c0c1d20080b40902d0130a074500da059401b946103c0f04e400450700ca1142818285683c04070b0540300075501800060300d41d41020300c15101d45c4580500c1c00072035503030a0200602c80340090071a042051030000440011101040030030081d000c000c0d0450741c0704245081030306044c00100d07c2c1140c1c00d43c822aa41e4901038080d598600000000c1088907010f1b41511010b80c01002046006d6071a4400500400e852082201e8100301e0000110783c17012a081106d02c1c1c094580040344001d4035540c10460200b101003611855084003000070692210701151043da80d541000a9151502100000305103955100d035090101c44d00c03442e64005802008403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 549565431 1250 549564181 549564203
    0x605191206150e03060106020c33030117060f06040f0209150d150302090609040201020a0503040308071e2102010f050901020714061510090e04030801060207050105090a03020603040f 80
    0x1c4000184103402034030789000c50000105043c480c04c002c210581201c200f90042d1690320302c18014030043d840c4008182d41c021012511001c4080c081c02c41e044003c0d500144041d481c0d60516880c03401d8001c140103e8a200d5014004119840101c64503003a8411030684001c20082c42640c02c1d4006401000d1180343d02c807101001000d4a014a00094040c5030301101c428801c00f94800c2d00340c400b4034090b000c060b401419480000311f003800c082103010741203441881181c4203404140c4400d410360b00700340c1040f0b400720300003c2e01c0d10921068010343c01800c0e500e01844100d4a1890743d4240322078821651440e110001081900c0c2400d00039071143c1100c2c01e1000c01403000b0302c0e11340e002a00030340c080c0c0000c4800460324008034106007400a02c4034407031560b111700e010044600c002005076201d405501d00d0100041c40b0800308488030000c1400c2c0c001c1d4400e8558401e81d505145019041c2581600b02c541048401c3c03201a01f0303660b070014407000701ea40503500e40f5070fa0749917401c5c042d1188184100140c0564000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 549566681 1250 549565431 549565439
    0x20a080702070609030309050405060f03100209100f0503130c181e020703170a0f0216050c03060601021e1002070b0a11040509040201110f161805010605191206 70
    0xa484600c9800c465003500c0c49035403141c5082d034400ca428040a030020b81030200501050400e0740c0079640140c00103102020510f85080020b1030286001d001020554001c01c1e648203504041500008400a9050229816004910040c01030200500000c029070365104070405000d4401c82c0140901070f1010380c8054102c04200c1e041c0030b41028000d2007000240e03000341040c82c0c00d0510030750380300c2a410b0741d074405e00341d989800380303d035404e000303031400b03522aa84404050440c001c5100500c180c5d1103a80716246004080e04102d410514041d803800d00a1b0041c8042101a0b0f901040b0040041c907841e800e42c04801628524506d094a1920b021403960310018902c0d01380000180c20328403e1007450024489201e0f40c25604545001e1031050641000250000c9001580a0340441c00da4031103200480300003220362841c8900e02a0b0041405a000c0f0b250b8905002c0b40b22020f541241000003520140102d5140c0b2178024440d214211414a10054004041e02503501c110155500c010080000307100302516 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 549567931 1250 549566681 549566687
    0x40e101802100807170c1209010b060306010c0309120320210c010b0306010e040c060309021005091306090f11070807020d1a04050303100837020303120108120733020a 73
    0x2007d1f242c06000740d40000000c0903080140200030041b0000303003010742152502c9005507205a5008011003c1c044042e0740860198960864a070f0300038040e50b00c40781d01c2050214004500306209079484010303003103410202c0b4454550050f407402d4608104401e65641e180d00c07011401811014490780d85801003900019075011640d0000d80100d00502460300c0043c0d840744182c00b2200300c1d00c002900320f4660b80b240760301d20b8020340260842c08405000ca145044145201d09c0c2115070640010484960b56005032040b0f541c54454041084940c42101d07142114540700c9002078040c602c0d00134032429501c00bc0108000c0b220035210a0841c8814010b011750410340703007003512900200c6103219041141003000030346070000a030f140811100041501403044c00414440085114002c15070045000080207000580b0100014004d44071110141c0d12554149100b1a050014840c0300740310082e01405400c0c08994550382d24002c0c52a03542030003814025a01080044000001c0013000703591020411760f0017030b50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 549569181 1250 549567931 549567937
    0xe12030c0a050f061f03150f0c021e07030b010b030601090314010e0d210c0320030a060b070218070e0a030f12050c0c01120209040e101802100807170c 66
    0xf1005940310360b07450300c5101404a900e910144041500d00d0400c1020070100c0c081c0814803420200045140006180c0503c1507580c6602d041d00181e01030081855220f14500300b00d8030503d030303007130207030402c980b65464081300003d041c003030443d4100c0e002010801580c01150110001c40c4d00c028028051a920840c150090200144014a44c01614002003441d441081d100b5401d24020000060640007690314100400348140c881c41031650f92a60519550304004e07540b801050003185055803490304002c0320042e03c8440c0d202c041d0515080c003100d80142e5035803000550030401140e0146143d0b50380c2d0811a200020110269002890220302000340910128000c10481c0141030389a403218829404454034441e9401c10000d6030030081c1c260040350310404549170855013000700541005081030005080307078030300e4031007a0f6154030240d01300c0010052401495241c0d003042d800c1c40040019a0042503030303614181140030400c0400070008009034028815038800041b0405015030341d140c54580d160742e82d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 549570431 1250 549569181 549569203
    0xd0204111e03102909030703150c14130b1c090b074107060f05010e01061b080306060c010501150e030705030d0806211b0405070e12030c0a05 62
    0x402078000214420080c0200c42c5044034030b85801301040300b403c003026030760b0b5085650050b905000340d0000202064042c0d410060195448100042c0b5284008000e40389100c243c269648076401130000e00400361400482e40c0c12110b240000c1d07555071111a910801c000c18102e801d26220345492500014429940c12440c400c4801d0340303c44d0420781c2c00c585564000750351031144202900410100340440301d50305100c8260441030358049400d0240c5680e81000341d61f8a1420748407583d680f4001002080700c0c0c01c0701140100001d09010784443d8100e0f6845c42550307800700707010700410700c00004035209840b450210748551001100802c5956191500a03007031480c8c584440740041c09410b0103d26615000c2084412500d00800030304805251036000e84014000400140d03002000410016080740d4070b80d124103410340d804000c0c01d40182419020f458540b40c0500d003a01440c80c000401c844141c01004410101d00e0803201d045404250b468190f1a62080048081c82c40c0145003c0900700480011041d0141d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 549571681 1250 549570431 549570451
    0x303091b080714180412030e030309030307030b0a0b030f1b1602040c14190e0a09060f2421020703030501140d0201050403030e0307051503040308070e0d0204111e03 72
    0x1046043c00300022400c070604002c2103410306501080c000740400d624020b60440904003c120020a5803550b8155007046580000c140c20000030801100e500d44601d107a02001100c000d04c585040c1810000d041c0401068442002402c40100304d480d1466000410a1200701844694811080c04003031001e1424a100724090ba0414091001c92806001a0240c41b84980200b03424810070641100c040e0340b1415000c824003180d01180c0c121506c0b250b40c0e11001e4210b036003001c1803407454032101554016540d4010007001c502803019611010500c0e1000504d10001d1400d5917000c42c8451401d18090308074102070014601c0020200708060700344e00254129110420300720504c1e411385003800800b2003044002800580204400c0c000a40030310780b440c80fa031034068100c0c1c0e01581c40e038000c81e0b03140c4600032200c0c4104001004210415070f00c50328942c1d010750340e4500b09440d800b2500c080348483c844174100a01c903c0c4c4900c0e02c0c00404a20030145c1e440721258100541010001069803003051f401542c1c40c41070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 549572931 1250 549571681 549571709
    0x3180302032218090206070605010b03070f2c1906020c010305060f0105041e030507060e100c05070b1605010213151b140f060c031006020105130303091b0807 69
    0x2088a5103030b440e401c0740ca41000f40741c041d04210f500c001c020035001c0000c03a0701003428031401010481c00d22405010309040300c5450340d41e00f803107000a443c4e180b861424008110548850300c42041034901d5845202540008415901115000090003400c500c40301030190204000c0025466900090410400d402071701c040100351102c8086c0101600c00b01061404500100400c11607031000c040c50010194507c80791800441e201e695031410401164412000941c07403032000006803030141038181101c1d0070b908080001d85055600c1701d03100c0c02c151081d488151800b15420f641075444003070514990b54088000c6594492031244036001000305d0040200d031800484802c101280201c400188a8000448042d00b403009a070b6910114120141119454020000c060680a0040050501599418082c0d540300e01e03210f1141e42d2111000d41c046021a8140020b00111a84094000c48010741510307020802003e1420280204801c4003284c0c070300d0450348107002506200100780c2c101947c07025003030455 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 549574181 1250 549572931 549572977
    0xb0103180b2e030c0f051815030a05030723030705120f0904051003170a0503010e1005100c02031c120e0f160f060206160f0318030203 59
    0x100340c40311080080c445501c101c04900c1142e0602c000c8889610300c90401420442d89030030780315440781943d008840c18030696a05000b880440c5544402604013503e0a214013614a04150702c00f42c4060112101e28040c01d8910100d51000c0c448500c100c1e170804100c0756210301c035181c514005820fa0101e556600501d007001c42c0103880101c110b65166401400801941c081b00c0d9594009a000024000d40070b0403c000000c0c8a8840c1d00440d88510001809040a9484c0d030422031407200d40402c907000030640404c0410002078100c1c05aa0643d420380303118200c00d5850b20120b05404c0e0854004940c003000380c0010461086c0d01c903818000841c401e4040d0340341c0071800c0d5120380c07510b00c501500c1000300703141d07400f000c0c2d40c59019400b0700d2007010501700f00d90444c0b0010006d5820303c2c00143d0300e01190603540e0f40c2401309010810034107001b01301a20080515142000e540c401c1c3c0a070302c44075075081002c81c02587c0131680c0b194002040c00c240b01940520242001d240195680d8018034144200c1400c00d00000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 549575431 1250 549574181 549574211
    0x7030b0105010c030824040501061e0201020a050a0c06020f0c07180203010f030803091c032f030c0309030705030a0816080405061305011401091508010203060a03080703020118060b0103 81
    0x20b21a0754540c881c2c5d18a80c940509898004021031441c04803e203000c0c84858590b562805500d00801494445084110b041d400950700d500088400d00c2c1560b0040004405050307104c030480c5d80d10704492030314901c003000625003880a40f19001c8070440e030a4010600800280c4040741c000e04440288100e81c01c01c4182c4001c9400f6800240b01ea0361144510301e100b080455000002107038008c0108042e02c801300d0740c241c2041c4058001d4446100000e507241d2034403203510358540500303840c103103d201c404842042c90340081806105c02041c83c0701c404004000700e0055901001900c003425800003e5a85500f145000240104800c550b01c52b401d034410b00c800d80405014140490140790084090601340c0d8440000d61008080080d040725a59600c3d5990060142c66211841c060316201030080340f903801200c59110300d000c0c65041681c00341d00c10014400d0541da26034031002100da200c0c12132625021a030800b41c2c0141003848080c401ca61650140f0303070801c041caa101d80008a4249c0701006140c039105804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 549576681 1250 549575431 549575447
    0x40b04050108100f060f03020912061902040b09210304080c0108010e041a1f380306040c05070b07090f17030322120503090105060904110409030e040e07030b010501 72
    0x704c01c3c06802a06110441c400c03032245021030004e0802514015841c1c1c046000803030001003661b0385030404400d11402d031a070b101403c880e0343e031100d80c250300382030030301e006810188507001c006c0e0311a042c40300710300c005410705c040b034400303484c0e070500c20741e5222951150303910389421001c400c0c41d0006500b240042180e13103002025070302440c0c0085032080b1040e042d504a0b441064041c100303100a142d806c141d421405940003280010380136007443c03a41d551040404040301101c1d80d1003003600d104800c1c2010b0388850141c0701982c0e4010000c90f400300309183e8a0b1010750b20342c1b040d01700c0030700f03884804000c2008142e00400400125640381584026060391010404040c101c03400c60160b0756001000403c0113003020204d00000703e00d2122040e800b508072640c0da40740c5e41c444445401c0100d0000b00c20044008020702c9805d0b0700a000751040e00391841c1950b00c00c0710095412002c07a1080e952150804107040c071030701c0489620341c80540200310030704452440304d50b01d82e207602c0125070b1602040c001181c0c0754811580 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 549577931 1250 549576681 549576689
    0x8030f0c010c030608100c0e060711040c050403030f121e091401020301050a0b0f09031504050c090103210e040c021b0d02180a180305030919030f05090102070308040b0405010810 78
    0x60211b09090310141c02c0a4a40301114004200391801188003030f0340c41200030944d80303120700c1010200c03144c1c140c2400143c1d40320700a55414070009120420110340c000e20301a0800d14180780454045124045140c000e10045041c4407008000204031030b08241f05510110409001d04504a440d1181e05100c500380d10007402a5078002c00c519604111808998001e001c2c500074011007541070620800c04a890408002c1481480980180c00e2000b4860203218880401a060f0344a91040d170550b00c0e19049070505521000c80c00a603500f000701c589100c0c401b02480c01900810a0011403e41c00d0002d6030f402d00ca00400e40e41c80c000c00000c0d94245000c61900624070303400b5010240900720003080720545a4001c00d0b0300034660b140c600e45020342030400521800a8801d480c0c0b43d03100d0800281040c0f800107040100c0700301d1200304c401000842d800c040031400090b6035140c907030741e240c504400403820450706030320082c030305000410041003180041000d03006031507080c1d81c0c1038481d5640020001040029200e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 549579181 1250 549577931 549577933
    0x2101b1808030f0a0212120402190501020715050705070824010f03060e0703051203100501050315120705150711010f050d0507032c010b01031e1508030f0c010c030608 73
    0x5082d0714001c410b0b004d04008545401960017558140c507486050b0340c0541d01e60024042c0303400801045203002000b1109141c0e41d0704036240701509080001c0d5a480641c000d0050000402d04e0411545200b40c0c1121011548401541d400395610350800740e50322400510000a090f249080742880f1145509207030480d061090001c030a035186803542c01c001c0400950404190240c0c81d40440441c40c20421040c0080c2c0201480c0c1c1c2e2481e2441c81d0311468600b40d04900d040000c2002400301c40030b00c50607a00c00460040301c0d0980722030b911901e680d207041c805070300c40340c0c12520407800440c0c54400500606003403401402d00c9000b01504030011150410030202c00404980d0503c41d10441210f9940f10a603c00c01c203080011304001580481030081c0c500c030003119110141c410921102c500d00780140e020f900740c28201030001078007551580035284c0e0310f04840700c003403503540840b0300500341c0d43d0142200401214069079030b40c1c0c0d0100c2c0d6105050340301510344a4558242000e00800520a00c541d4007204c802c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 549580431 1250 549579181 549579187
    0xc0206090f01151e0b0a09230906042a020c180c040306091b031218050a030b040f0206030f0a050601050418051503070b0429160302101b180803 63
    0x1303802041e8160410001a0249070b01020031000c045000400c00901c980e21040d0501d80b0b841000e08074450440300c800c850580300450074040d074807143d102c5a045003045a01003000e099002c0b075014541c40c0741c149402114400e081c00c400f1a50040380703015844009032883d0f0301c0c480b601c140000c40c1083c159445020302c1c000300000c201054241c0c1c4694034107441402a40f060a0030b0940070070742410f240e041581c05049007140b00d40e9090b0890f801c0443d042ca50f040074180d00d40f406001688000309403002030074211080740041c04104120041500c03c0d54000c022503141d0a0007110389516410480d10200c21a00c0c010215815600403002e5404440c80e241c0d103c0200c03448880c680c0301900e40035101c50109204400c4800c1c15560a01282c40038080c0f402d0329a0301d440c03821382020009208a89000360301074800344544c0721100310004450a2004861140e8004900d0f890308074a820900c0d1560351159140c14460058424800c030460000a01961440100c00c0c01031260301c40c1210610801a02e03034010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 549581681 1250 549580431 549580439
    0xa0315140109050d03020102090409080406080f1909030509040f02031f12201002010e1207021008221208010603020c060f060a030b0a0e19050601050904020a05040c0206090f0115 78
    0x240d200e02c6029101b88000340c141520100414141d81d60950308840d44031010400b88409980300d1106980944552a10400780c2446481110b40102d10884005560384905044c0306160055080b24200075014100300082162510041e0081d00305840310b003804c82401c4800090801281515015100400d00040c111155507484641c03110f003007085120300ca0690003200403290b0365112020700e0004280c00100c2c0e1800c1150005003040f030003c10f9280b03420800e20420001d40c4882c64035058000e014100306000f6100c0c2009400780c540b1881041003103158001c40c18041019a400143c0f02c00f1250716000900d03629000e081c0d01340c3c02401590f030791aa00034400141215841c0031002d421842c040c000c421001c0d10390f01c2d9405215811a0542c000589900402c00002010020f51188039511992401c982d075959458984800b0184142d034441c14155000c642550384680b0a0801080d00510801c20b084074140040d44404c4100e40c082c00c01c0c021401350001002c3d041c01030760450800000000307021410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 549582931 1250 549581681 549581689
    0xc0306030d021b19080a0506041506032f03060103060219050720210a120f050307032d0b0103050c040f030b19020406110706210e010e030a031514010905 67
    0x202000462403440d213400000c1c20b070003d011310601d0300c2c001d201401c031501e05420806d40d10404100e81c00901c512b008410000b0882e605001c0c002d242d4078030110004141d43c00c984421a8048801142d454000c1c040004104903255000341036140b14041140c0700c1a04c80a010f40703490061041c080c0440200c1c1c03082c04d1118244500b50896040d00030302e044580810140b00304940c02c40b0041c03c404540c0210103800c01e11441d061150128150761a1503003204801d4040182a070101601180a00d9120401e001c0c2c4c0054029003002034034103022400340306010080c04080075051003030070f1901091a040120300b04800b00c10459040e00c10b0b08000d0300256156984500001c40010a0f42e001000c0c102481c405149041c0001c000030041c699420442a08902c846400c1c401c5a9000c00e0500207617148031040e003e884681040c408a2107400025104070100046014107540501c440b01400001510111281c15520210070611204d0482828503115840380700280355213200d440c0800c0e4510402c00c80703868 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 549584181 1250 549582931 549582949
    0x80405100b0906190b0d02070c050f03280803040c061d0a061d090405010219050c0c01080915270c0f10170a0c1b031707090305060c0306030d021b 64
    0x940600c84c40072a41d80d8081c3d100c815085400c2003034003190002940300902181756008070140100700d0301d401c2048044400a0f0b998121a07482d140c005100c500100c20800e02c00b428022055004441a9602d19040c0b900030b000d941c0f14020b10340465108481420101e507164110141800080c0486089600301328007518600e0303107c034007900c5018080803001d000b501d901e40d03618000ca10842c005a101d0040c052071174100c4040000c903c08004043c0030105000b580042d204150034420309101251361540c0b0362060074000181880c440c032041ca0400c1c0804030311070344440b040c401c3ea50b03d454011403031411075064031051000429503002d0525412407155140c4017150b40040e0400e4204042c44101045001a403198110342d4090482e81d01c80807410700c1604a040b1100c103c1c92440d10080c01055960050035110700c1c031030383c0c0030b24146010002d0307402d50150103c98050758211045900d03626000b510303c021a0310448595000b8043c2110324045d00e400016034020403207900c048094402d0300da41c20301c01488 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 549585431 1250 549584181 549584209
    0xe041a010804260d0902030c03060f01050d0c05040510080c0609032a0d080a03050f0906070c0809030709051005030106031208040f0c030503090909030a0504090209030c10080405100b0906 82
    0x1d0b420060300040183c5100c010009900540800305000c8018010542808040c0e05058002d4205104002c03001200ca48280e0640c0c07011601401c150740300d41400c0e41e20503100d4000940291900090000d05041c10881d90100e980701411107800031003e03020300c8054000d90b460300d130305a8040d4600d83c1258442000f81d006940440481c06c503174444c441c001810424081c0026101e4990005004140992502440364003a00700d2000c80350034104810800d40d0b0341030040804080041c0b0001b00c03410840300c8070845010140003011150303070303940b9089000028078040d950181218010400000d26040600546045030f030020600207030300c11600826100100028030841c2e03480c082d11170400002e404041c111000d5401032006580303d4010800740000782c407004d8814401a842441181c07003c0c0d600c40112002d95084010258880c140000801d00c1c5c0b452590030188e1107400303202c15030412a88008100d1043c0d01039400c5500c0b4030102d0710018215030071002940d0300006040001552403c0558130341c0c40c0c01d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 549586681 1250 549585431 549585473
    0x606050d02090411070b01081c2717030d0f2c1002030c19031e11071e05061303020c0d02060705010c02060a060602010204080d030e15070e041a010804 66
    0x3000c2413811101042c1e1060390100c0b000b58002c070040c82986c104101c0401c0400a0620141d0102e810001c0035001c900c029400c48001d010400701a0300f2140c0d0310a0a5005120303585407c8480342c0403800c0719440b43c202408013a03001c0e2520000036240741803030040503401040c1c40c03511520a58a0b000b80c10362034582c521aa081c1e4421045c5010845115100641c495015110017a88802a1542810010714081d801008260030070200481e400d04c11030042440c1c100c95403001810000c032902011550007640d00203400b8000c04809611030b01d450704100d80c28140b00780c00fa182c1d80e69032030480507001d034400c4c00f0150069002280300c0c9450b041501c1160480c80c0010640c90034400d06545903802d40c1c140e901041d0060f0011000c0c0f0041c00b80900404010384990b0009600b09421304072259541c80c00c52128200701629518080d1100c42d09212500c6d2426009041c10710703d2070802e202a101c01501003030741d07008a181c14543c2c0321144801890080205050303540d80000c1d01c030381e1107983c4507000f00300f005090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 549587931 1250 549586681 549586691
    0xf19050d021f0206010608061017130c0f140105040b07020105030a020d0e0a03020f0a051906110706090b0109050705190504051206190501062a0803040f02040c030606050d020904 78
    0x184460300c10700c02c08000700c9540204855070501500410240000d03210a0242e03c8000d006031101e6081103d1007202d501305124034100d5901d5919000b900b0424500141001d407440901103481c4241200780e00548212090314650010511f004499910461250803a400400d000040c010340c8135100a41d00000c520101500744400ca060080031110310580a0103240c0c4100c148004054050141007070654140e405000d4010b442d46840d03454a011018403a8540a924420002c00042d50702021b68010349011141d2a155546005402010840d2007a601032410780300000303070b8003e0340c01594811902681d42d9414058030040400b9207d00c124080301c2401414000401e031a29010346104200001d07134024079450a0440e00801203400000d428002c080c203000040c81020b07004056106e0440c020010070300b8056194100300c049981d620f5000301200c5000040c0300c103114896a24001b124000c0390108481801c0100681c00c548040c42803002091052100380c2e00400d099000d09903010002c2d0000c59 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 549589181 1250 549587931 549587959
    0x9030513080f07060203090105070f08040b1218010c120b12030d0c140a0e060310090606030902010e1813060902090106080405190b0604020c01020c010e07050f19050d02 74
    0x1100006421140701a400428003000880c0d0400c80385000f003640e07001440c0b5080b10380d8002800e904c9410b2018101e460703040d0b14642000b032900111802450440d0440c2c0d201c0b503611042d0070456800b95001100d160a85600c0c200420f418801d045240070301761989614504000030304000b41c0020101254002103000024103441d0b81400202400f802d42d520025414002d0040541840c4c031400c0ca2500311842480140041c54000c018400300500807101551290b035140800055031090707800840c4203508040002500c40d070540c20000c101e901c00d0b20744900b1901541c06001c160344500c2d00ca40c101c05a9900130035104624413006a07641c2c0e004050129884000d6008a060800280d20660001f05050700f0041444000e21501543e9920b1401d158010b03a01c544410342141d4010b800f0900c683d40c001303403240051000354101c0328400312600091201d400056503a546824642c030845001c0d40c010b0348110300b10b1801c41c20400400e46c484540140b030034100414000c1d2145009805c03078000d404100106 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 549590431 1250 549589181 549589207
    0x8090a020d0305190e1e120f0703033c09080a08071a070e06090a081c0801090b01021216020604121104060b0d09020102120a03150f0513090305 63
    0x202a24003a850f2290760b4006100c0b203100015400891a0400204014071080f5a131b4003520040e07240400c40d441c51020422000003480d8141112104241d4401e00d00c4035000900042000310850303029464580b54803510580e0501001e42c2c0d2003020030315140c83d500603110890031920b45a108e0050785000d020756600c80800c240342ca005014203a860640125160342084061202c005005200e6036074542582040140505000082c0a05900c80e003008240c000d210703121030451800605202003194081d041d08001c421144000240707070700001d0005000031500c1c6409001d650045a01a070040039420079031a0f000035079801180c80c20300719484940c0e00c1809aa82c00c80900042c04840e69002503103011450020049441070910303d0240b82805404c0000d165030405841c140c3e03140780804602181303030b0b200403424410500c01b0101400e801240000006034560300141c1c089012103850048951541c4c118884125244255a80004118484001660250848802c40e4803a06001d41001d00d244481e03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 549591681 1250 549590431 549590449
    0x60304021905180a050105060f0d050415050a0c08091b06030402150c03030a0b0307060903030810030c06020a050601050a0305031b120315040b0411041e050306041b0e0906010608090a02 81
    0x403c4030b190080c801d002c02400184240b50050a080318218604040704031403160500841e4010302119645034001401d0003d07224820071205407580d010032881c40d01c44102c0006100c1719081c00001908000012030101e03001910046906900f510030003507070304820800109a10007002240c11a1079080c5071650710b0004409030100c07150400c01b40da203c0c0ba00131500e408440764003004034400da000391410009540c00901003000d40c1d070140f078200c14647d1210a059034001c80c603030004000080b5481c0005020740d010425610041c8140207075209640e80d4801c1116000c0103010145c4190004c201384040c101007243d0600018203140155039181260000452240e0821038480d6061480c0844810a625062090b5034145000302c0b0100592141c14a444d0302901407401000905c4514000600d0090580e100200003000010115600c5250a2500840b244903060104c5c4480c0083c0e803020544000000d0740a00c42d203241c400901c000d80c41c0010848030f808010703000300700c07501401d48040e015072240618 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 549592931 1250 549591681 549591709
    0x3030b0607030905032a04180c03120909020c060c210f0a0f140a2d02040e01060207140405280e0c0616110402091c03031109060304021905 61
    0x4400503d803801c0241420040b107a40e00c010540601d059007240c21020309034030f02010909480025440070140118061100d040d04060150384000d8000010002d18056944004109564181e1115521190b100c241e0049000080041d0030800000e2000710b03d04028044c2800350076101514008280080044258180c0f801d010a00c11001040000d0030140202084a60481d40800c55002230302040c444582e4007400030511207484500fa1303501100c8040f501c1440d8001889690b02550b5080303010b8000b503100e0710501d0805180720000040366070002c0740e180304440c891340030385404075085010030004000c0100050000f2102c010264201c0c2c602c4a41400038181c00f070310002d481030340c00f10340a10381101c04261510410301040002203440c14a41280e070700940c01440d0408141c40300c1d000502034001c0103102074101e00410118810b100c812450100e220307010740c40403c08103004c10050714017440fa50341d0058005004001040060600856003404a00c0403004501140d494000103900950314441e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 549594181 1250 549592931 549592937
    0x904050a18052104030515250509040608010b060d09170408010b030c040c090504020708040e041203060b040e040b1008030313020a0f0303020d1404092a030504020303030a0903030b060703 82
    0x80001000c48020383d4112101107030038400d401c05146594680e510a180c0c8034000c2c038004070802095071802c2c80705400400c400c1d0030f840902500680394009280d0380084c40a01c2c443c900744880014018410300c12201c0c005806400107240507044001320b07014091240d4100c0d196a50031030000c8444441e20040c0000c0c00f00103002140004620040501d4400041e1170702c2d10452800c0b86085140c2c0d000601c1204991081e180561541c0d885e0625805a000380e41c4401f01c1020140c08010800580d40c50f0342d82040402d0b102080300d030392034000590050286004403000c100c9560040340c0840d0091200503880078081d030501c01d105490b001e8481c1103400650380b002c07a00300c1501030102145406640d02018265004c1100603192841c7ca00139503510b0072000c0c0b041802204290200e0110b1a0300440380507180d104003c1c03102484513105008103101e404081007000100185600e0703600d00c03c0c0103150003035400400035410740c1c5410b18644000c0c95004400c4050655604a00c503860b2100c1010307140c0a406a1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 549595431 1250 549594181 549594193
    0x4120c0312060617060f0105161b06090501111501030201211a12030910081e01060c12022125080a0906020a0305031311040e012f0904050a1805 63
    0x601303421100341001e4003d138410108040e040c040c60b40c0c000180e419140b4009100d04503042d5506020500c034044c4400d50704004040d40300440c829802026080440d402070782c0340a0380302c1b5042c0e6001d490f10340329070083e001c88038003000400242d03104c1d03c8c2022110f05110f00c55041c0103112942c10b02111500d04480014101402c0c0b04440d61608113000e81589030307620042c5240071180d4001880380b130f168000c80800c3c0540e020100e0700080d40f503004494807081c017034841106943c40713a4001d040b8034071101080700c80c1c4c50b106409040c0d50740301092240921320703a0b40102403003640082c2140c225400184101d10801d054510058810115a011100040c05071901c2696860427000042c041b01d00d603000041903500460803040021f03440710131a580b1011710350b00841641034610382411180d4885100d0340d405824051070800c940c10641c031405882e80c10260380c0400100d010804180780d9803980b1010241001442040c440303040c1904400da000b1160b90b8001f500318908a95040c0032055180c00b03031541e510170 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 549596681 1250 549595431 549595457
    0xd06240f0803090f09040c031202030910030b0f120102090303040914070201060f091104030b250e10031e090b1509060f060c0c060307020109050705060304120c03120606 74
    0x1500036100a84107501c05149002010408149609030031506940100300900006043c080c004199102450b0b01040c1200c2d01c0880402c025580d4011401462241e000c1002c0440568017034403600031021380c0504090b86c071680070010098055002549120207540801100d4642d41d0280000d00240c00c004000043d8a034141682c01c400440c0101000e055a240401c144104410070f06080102d814034880410000103480303a40c0d085002e01d600082c80008020240024a549103901903042c9401ea1483d22030f4425084003244c50640029103550803411004542071801c0c4241c1110f116000b05c0c81005200688508050301181d01c0c9101c10740d20501041e0a00801d0300000464506420b000c40b42a422405c06500184400181071100742c0710f41c00001d10b130302e422030047c4400441e015004003119100c0c504554041d018001e0250111124007418a000c0307600e2501c1070036240a150041120011503202d03404c1034034503130b40f10340c0c0035020300c54080303c0c05040003080c0c000c03034011701a107650780400d064403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 549597931 1250 549596681 549596699
    0x10e1207060f060b04050d0305040f030b0a050a091e0c1212020f070803181801032004020304050c04090302030c0303090d080123040c030b0d06050402090906040308060d0624 76
    0x21981c034440c160f080079020030009800a09403415501c0c11900c18030031188520382070702c55100e1a404001b070710000d4000001840301e081c090701e100700b03c140300a116660713402000ca800c40380102c50007800c201070741115002c40741c0c451040c1030b14144215292000c480e01e80c070b1243c1030706950110840c0d0260305a043c400384942d041c00b07a05000c0050800400e0100d081202060301d17405204070103c1c0b101c03c1c0c2102c0640c166178241000cd24610240c03210425540c581c101480321180129180f582002e020709180f0143c02e092084030711854020002e0211aa1000c1c1040090121120241d00b18802882100b142d40c4090000318081c01e890001000c1c044200034000d4100d171030503400381c900340900000340d58040328034044141d06508112400955010744a50a50007002c011400039001300c04404000204190f9500840c001c81c000c481c100340d256242c1103819a0340301c00301c0700140000e65120218036241011000641c0042c450400030410300307154031440c0400d50f00d0442844030600300181c20011066 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 549599181 1250 549597931 549597941
    0x618090309010f0207290d0903030609060b0403020a03020402160213050f13120f12060608041709060a050f210601141801110a14060f1015050705010e120706 69
    0x4100e001a001171440c04508501c0600203000c9480701d00e05095801c5240e0501a04591074013207080b03010080500749060040040c0140d00503140224544400411050300740b10030340741281e500806040e2940d0035507090001039040000e4101101c0c5442c0c8000340182d84901120715496442d4a00081900c0d0401e0141c0301c01c2c2c0c0280c078031b00904555602243c003040c0c841043c04200c0516003066071205a084000320b86255100505290091400700042640e562080029000354041c2c40d42d4228141c800c0380b0030446224490300241d1160080050703110300b6000b0701c081d00e080d11400d03900a00b0882d5021380d903942c00c4c550144035a0a20500d604019156030000c001810b60340051000b141003082912002162011207a42d49041c40080b03064044070341d07410014081c02c1e0f44e1040e0301070101542c05640c15a02d800038ac440c0e91112100200150780104140f0002085410300760f0b1521010790540000c1e00e039a07004c5041580e02d9502c030700108000e0f0404101c6103114074000b40031180e44101c6820404100c1e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 549600431 1250 549599181 549599207
    0x203010623180402011d0a0f0e01090e0c19030b19230105040908070c03081201061b030302070812010f090c05031e0c1e030601091202130203061809030901 68
    0x450b01d419000c400401080c80c2c2c0c455820b0804030044050450341c0d1401102d44a1403561004d03813681e000c203542104079230010484001c1e1008034156601c400f0030700f003641d80032500e81e052588500c0c0501040c2c60071040a0403c20207102c86540b103907460741c45280020340100e40c0000f0082c010030380c0305032120261103000c03244030000ca142440241c03ca40d03a22010403061091610858607603c010003480b039403504407206140d02c0494103440301c0e564034040505810036200c0c2c1c000305409000016050740541042c40c1000e04100c0b154421601d6135a00ba4003e4010180036910080d0902420b0001d00b40f1460103800f800e5645081003410307191074080c5080d14420803168013001414002e200e80d00060f15038036a40342c1d00c144810b80301a91142d80c4d60080740104011700702801000c130320000f0801c01c0071000b18000c50007030303035410b00c141c0e100c1c145060044d5281000942102101084003102280307035000d1a0041c8004003100441c1c41c241d510b10703d05002c00d60f50001030b0307000014540320545e084490382041c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 549601681 1250 549600431 549600439
    0x3040501110c15030a0f0203130203060708070f18080f070f0f03020a0b0d0e0a06050f01090c050d0b01030209180a18030807030f0204030606121520160203010623 71
    0x42c00030804995411003180030314038009400f001040c0c01907038503005075405ca40c24400454a0f03140c00b031841b15030001c441209a019008002c0407400f0107109a490030b10a945944070322045c43e11004040b100620b02281d00c650355409080f0225614405010752205800c003240200815801d000040c088040694490a85a4011802000162a0f2030400c000b22082840115210380d04030300604050b0840c078079094018081d80e103800d0204000740e0302ca14040c0c003100401006583e00d4031180230803200218101c6002c900305001c0c0c841d0362f94180e08110790b49030041c90090f051859601c045000d0002000200868040500401c04a1540c84c801c907144143c2c0204840340d0b844003a107025110b99405000c0c80105a00d620006e00c52030030f01e4040313500640e8004001c001d00c81c1d0364004d1084606800c4404c42c0c81ca40c00200e80c0704036103098002d881058003008503481c500342d5151000300c170307a1384160f0382200c90901420105005d0b980a20910005045202d8100304500500b80d06000c81c8105030700107071003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 549602931 1250 549601681 549601693
    0x3030c12110c010509040609181e031706030c03070602010c020c0d2d02130204081c021207050717030a0f03050702210d111c0e06041b0801020406020304050111 70
    0x400003441c0d00e010482130800310756510242010401821444d0080c4100d07600303214070916202c03120030680401301d00503203206d0045503503440100c26000c10340002600081c070184110000201080c0502d41048005048a42c1864140d000c24103004050344040d000d41d6644120b100e14680510044c101c41c034040b200c00c0f89040166807080b0007007503e480882d01052146103803540410700c1c00c0d0a410b5842e0010084400042200740d03500196200f0700488043c1e0040e01082013000d030b0b4004200382c1907071054000d84411504000e00c07800d40c1e04000001c1e0780d14840c607000043c030500d2144054a5542e0b0710301c06556a203503940005002d4503407540c000c00800d403804040114050f4007140440741d00150500405000722440107200060180d40903508500d40340040306000d0308445030040021901e102c400340e01c1d0900a002c1c45003200d5031142152010f0308000000360000d0b00c1981c0440051100c2040780f070140d92030304442801ca0700107410140140e80001004d01a540c1c00481d0102414a10700017060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 549604181 1250 549602931 549602957
    0x8090d050c1506031207050c10050c07050f0114032d010605030109111b0a0303050108010b0a03120314070c0201170919030522050f1014070c030b0103030c12 69
    0x1e50380d2403802c030480540340d040e000319a1665090219000b80d24000000c55101c209070700b0450b03101e185000049218544012a68000718002e0040e00c10903501c0d50003824885150400303020840304229032503410001e140054145031b2003030101441c080d00c42840703030307140541200f00700c121010b00d900d81840c070445803640104061540b00f405c41e4150703204910003158a0b01459030356001c9003c0c040c40c4081140480c2000900d8180c001410800140244d034281f285980c0d0b80210b90032a910b0189580e00050003c00c14070106124079548004004030f0301d40002d208014040720381c4c80c1c1c03005641d4480080c43c02e810b060700399030344a484291980110440d8220505009a1140e034604001c081e20010210b070014010505003d0404d640000300340c502119502001001c0002d0801c1c06401103911842001c44042a1070138038406a00c8400616100e100c000400200e10400c580c014080444032003403981000310010740c20141050082d4800d456100150780541f8000300700308110082501041400f4400e11 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 549605431 1250 549604181 549604183
    0x16060b04050a0e10110d061d010911090613080313082505010f090306020a09080f0601150c0c05040204030827030601150e1203130602010b06032202090708090d050c 72
    0xca00c0002204d00000c100c0382980084031036006a601a03440740d071134130300005030000316070b5511550b0741c2d8004240030f001d03a01c07030503000c0c111041011000e4041d88144001c0c1c4990400400a04508000c80404805035944620b81031666110f061103180c0c262203070710200200b200c1080b01003007006001820211050a4801c40c801c0c3ca44030303100362810002e203103c100388014080c0b07140c0c40c0a55080307a030640d0745241281d0b01500304045c0744109180f80c411000c6d40c10005e000810414161600c0c02160280b07403502c19021503203155065030540c0ea0414100c40000d250f62244001e10081d440b4150391034840442001c0707500c90801103190b15030480011140884e09950104045040d43c1c4c503810079000304410200112088070b4400c4c5415005210f03641d0b070005081c0000054144603070303950184d000035500c40204a00b03032440d140301140c01801c24000300e41521542c02e055914200314002c01c1e10401220b4000484851040d0f0303e41012403ca02c1c10b0004402062080c40e000340601d0030903a1400c00118811 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 549606681 1250 549605431 549605443
    0x303230f0d0b0d06050a05010f1a040924060201050a0e0607021507030b030114040b01150504031203090609110a0b040303020a11030f0a150f09030c1716060b04050a0e 73
    0x204000650310704180c0007964404101d483d110350400b04c200801c2c170b8405d010000600c800e0180041702034000d94002500c041080070001d100b11f03170484050410f4078201e201d401401c4800749007000311a441018000455203072003008000c00d0141d0000c900da080c1880104211030344805506180d4101100b00100d80381c001034030a141c106900d1302c4084650703a502d4110020b21b085d006242d4035508001411079a156104801400f50340110902090799a807031101c1c904903541c042c950000305a00b44010004240101c520058000c02400c001c68008020b64880c030031a500c5d0b010843d05a607540c2c40c0b443d0282000392000014003280d060135484d1504584000e540c800340010010900d005401ea55000382e142405940109009013007216408102031610080302d983c00b000b0140020f140155080251440f409014901c0e90540c0356a2400340541d10741700307641410324084108881d0f082007600203000e2480b0310304000600030b030360000d2409000c00401003600c070090815400c803800c150760321a030380b0b20111f18 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 549607931 1250 549606681 549606697
    0xb030408130f150818010c1e080103050607050a020a1718012a110306090303090c1c06090501200403060f2a020c031006030605100b04090b0105130303230f 68
    0x8401d60580d03441d014080345d42080720341c0d0759995081080b10088a034102c61601c42940d0070425608840007600821a03c0c4102440090100e501a0000ca82280d00400003010150043d1050b144803882c9a04c0c5c5c6007141040c0035050344580400038104000c8104c10f483d061481c0424600100c075005c681c0c0c46410700d241c840803440042040e441c5400d040105003089540212000790564101d8030705941c840e40c4a4000304c0380380b0790501800d42200c645151420b22400080c0080c06520000c0e102502c41c02b001300744001040b1001d41d40c0d41801d00c0f0140c040d240d04501d139210007501e565540c0c1185070039019180c0025040d0140c0c0c0c100410100c040b070201103030f03030b1110581780590441300d415140304920303048118142c00d41601480c401801c117402c05411250580340582400e200740d445201c01c2d4000001c0c54480c03c43d21500c2408148402d0b08a5040f83d845100140f511608014440010b0318464000c0d6100710082426440b003d0f2a103094584030701041e480a9034032600b054420b41d2104007601c03134021 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 549609181 1250 549607931 549607937
    0x181b06051804020912070612020f0d050606160c0807060206240d150207170903101a032407080730290f0a050d020a0b030408130f15 58
    0x1008400d480382d80c180d403c00100204014804000e21642684411187c010040011004ea4079546009110f008940f18901c032041d0192519960a504400901c400f13020558085000c01aa104040c1c42400118005024000b024415880c0c860050300e014000d510540c1990084410000070039403c2d8840421818510003903c401c0c00400c002803041c4052050080c41c0744c52000b0181c48054031580079000c0d96103d102c2003a105a900e0945035004c0c0039080c011a070692020b045140c25007203640000d0455604285d1401c100220a40024200010302e60504159508411003010020f02c0e00e480680050140c01d207c803150802800c020b02d21040d004480441e0b80e600d0b890300ca03c5822007a0080d036449120340c0c0070040c4102418403910082030400c40c0e00b0030034205000304a01450310104a20b0301c6100103002d00e5080e8600400d000746540d941205aa205003400000181641644005c5200d2880341da60980d0b1001004407450f038030105034000c0d1400c0b244809007800790400c6e404460080e914641 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 549610431 1250 549609181 549609217
    0x20d080414011506020604170c0c0d051c11010c0306050a15021216030809061504050a0e1c090b0406080a0203060d12050d110f070f050a0501181b0605 66
    0x41e0440340580314901c000544422068400603040b940030030228000e030720449810340c103560400350b0f0184500401c607080183c1d400c0603004c02c0152410b800390070b8002c0d20802c10350f11074200041e5000840f04900000502141c0b40c2810a6502c95003803181a03841c42e110704040008078101404214103030114050484203e812510200b800c81c000c12040b150102d1162146640b2015003d40c20081d001c42c0300700301c010684120203d40d80e410003241c028840c0454841d0003254030a20360800002e0000a0310301d1085c599034a0310b8220981c01444051030909500842c1c00c00c8840c0d0b0071008242e819654013201c0e00010911041c07103034030382c81030039a900201c1d44140540c880d1a40e2000401d1808801002402000c0f040720351801039811001a003000050010304101c01408404c0002e050b1045c0300c02503400b404c041040e04001130f81c8005c120b070b815002d0030440b0401d10060f40c0f44d50841e4a054002040910340091050410400e400a1503c48106e2002c00350014980380c40500a40501880f02c94025940 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 549611681 1250 549610431 549610463
    0x80304030e1f1106010b1611030714090f13080c0c1f0e0406120f0503070b01120c08190314070206120702010c0203160201050a050c030a0306090507020d0804 69
    0x4003029001d81e9070041182d2042529280300c2c9074030690209101021844000300d6102d50000440c01c58120340444204074580298003038014010f800c5554101c42c07a000c4404e06600300c3c0c0301040b046020b001c901e640410005601820000114030081a541749a01c050341000547c8a4200b2800403d82d0700148494840c6008020380342402c0a40109642005440c40c0c2201501d50b040f00381e201480ca540c0741d00304084001c0080c002a076210b400b230702400021016450700050841414404801e02510940f8244001d5945031060080300381e000f019801e00440054090100b081c02140082059000601075080c080d54000038078211001c4c0903080c01524920000c0554403d81242d01b9954000c01065850503841d03039600c100300040d02e80500541c030340000b9010390f900020031100c1110040e10183c48610f0140d0045456901580d510010000203014200984400300050061a0082c0d01c0209070581042e003031104031800148201c086501c2802c03400c9140c0d800c00c42c603a1300103800c1000003121070a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 549612931 1250 549611681 549611687
    0x105090d12080412030c0203070b1012110f010c0b0a0f2c0705090403090b0f07060f021c020306130509150709170111120403020a020a1d01051503010308030403 70
    0x2114001d05180c10402001c046140d002c1111807041d441680d2003500d45031a140c00301c007100c000000010269004001920124074001c0c1d045610076038900d105801a9102c4d19107411107220010220340c4119001242481c914040c82804015902031030812500c441c140c039290038503030020305802c00456442c98403000b800c4150f040601200603c00030040582070301d90401a100c0140500700d40d40380500880402c1d10310340003034400d00407909540c0740540740b42401e807080e01e59841f03114409094201004050001001e83c02488150120140c0043c2c45a14043c0120b0310b00d101012490841c41c070400c1042915600c00750031000e00030381104001503c0e500c0174178003440c00e0f89138180c5a440000b00c90030041031076070004150302550404d0000c00b03424500e483e0a50309035018017588a01e041d80c24018080309404942031587d1180c0244112011a105500483d92804881c0c005a0801e11030103e001c0342140c0c00c4504500500c006e4600042805002c0c0000761b080c0410f000040c0b0540c0000080790500d48 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 549614181 1250 549612931 549612949
    0x1c0f1d06090d15110d1a011709160609030506060d031d040209041a01020d0e0f220507080115051201030b18030412170702010e061309020d02040311100509010509 71
    0x14034202c041142c199180b05070130040d0450304a2a65140c00d015410f143d0740c2e00f807168002d5440d4180c4480e04103060310700d4030f10041c80005041c4940d0340314990000b08441e0340500c0071401030040b80c5605d84414110f041c15810800b00401d8a0301400e01c179a1100002644500d40908413400d61102040701c0f0b459500050192041040c12640075052011104c400b440f110018405403000341c08480240d207807024295070510500400b42d078844a600400e00700d40c28009110032001c034240801c001c4000101d001541201c405030381c140006041000188400850240d110f068840c2606100d418914140300483d1b52002c1400000c014412103408941d001c1844044000d000000c14140c0e51100c0d00c8032100d5000a941c40015901f5200c01d00342894201c81050485603515010380d1044455000304040c0300307040d4801240070305260329082000136111a50710291002e05040301c40940c1c0c3c0c074a90f04000e88420401100c0074450380c8d0039420f50070029049011121001d90a0801545510a400026030011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 549615431 1250 549614181 549614213
    0x52511070503071d01050a180902150a09031b0e190b030d080907090509030a0e13020c0c18090601060311070b01260d02070e0402031c0f1d06090d 64
    0x2101d09003000c140c80040241011401515040c2410586c0e0303928104202d0704210712075400072007000080001071100c075400c09081035001803c0d0740001d4009d10301c0c030309841c2e0000044c500010140c600500400c03074242c4000c0c15400c0d0141c08c4020311810000d940756100b601500da0341c0307a0007039040740104010541c0c00590110300000c06503103540301d0000d0080c000000488000b00c840c041c8800c0800c03844407a00c02c5d40c2c0140800b800a45c2003c1c0070020580c1c00e0307501d640183c0d40c000c0302100724620a07013440c001040c00343c4414001e4032495443c2c400384039100e000541c0d40ca003d54440400c005013060005565030440300f6519021800b8249007d1600ca02c0c4140d2602400b00001c210003c81c6023200340880052040c848200000c007041100391081c0c40d0713580c1034180300c01a04182c104000300c89881c0e48a641083c0024140c95959885410554803070100303031007007000f2503030707013400785410a4000c0900103159040c42c00c28085c40008000040007403160b00d20b158070815000e00c102e420b000304041c0f000028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 549616681 1250 549615431 549615433
    0x1c06051c050f0304083004090903020a0b0a0b010318020f0d080904110901020d090311060f0408030d0c1206030c0302100c1505060a05040608030304170c060109020a03052511070503 79
    0x15684030042d042d00c1d03c0c00e01b602c0b03404060100180c4a454510700d600200700c41d000d820102c7c10305050202c030101800d1030403410b070300318072649074800080f500071404036004100c0b06600140004031000050700362550103500500c11f8420711aa9009a1500005407600c10422a076201400055203080b002d00c1c080c0c00341040d08146000240c69a1403010b50051110710380907022145d02c1200c0c0c3d0030403078004801c1d0000820150149007019a82e0404001411805181030382c2907041540b181c3c440e501d903801268800410503100c800c0840a0b80d000010100d19030b9503904180140340c256200c0c0362610007980700017801903c1d14546488070754450300c690403d1a0388901114149a42451400b003c1c0105a41c990711a501c070003c00180b80c0780901c1010100c07a0700360042d600310b59881c1c440034030745201c0750300341208005c00300103168000c10140000b6000e0304190500584440c0003400040032114000d00e045589107140d5080107030340b6491802c940322600c90f454820801c80384116154200b010581c000b6400d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 549617931 1250 549616681 549616687
    0x90907150e281203080a1410090b040e0102070c05210718020f03040b01050109050414010e0606040302150a090e271009030905040e03130308090118030303021c06051c050f03 76
    0x101a440785c1c0b50750069001001c01c0c0242e210320f01c0d10329400e40d0280c404550b600c448620070011541950030030305042400801c0041c00d40710311058030f82a0707880b1200c1210700e415440000d224030b260858600c5051546910385603100c05410881c40c0d0354682074044d824400304260f00304166042e80780c04460b1850081a2401c2d100c0c18285060b05880e00d0a006031401b0501503000413035a0b04091181d94260103030445001c4d400e03403a1511158401201034034182c1c01500070040070015803107250841198003114036110303990700d400b82e2000785404003907001000e5410084060200315240031100009051985244c426410303201c00301249080e50121300481030a003401d0420341896000500b5900300c9a094405201c041d0684000e01d440e480303049110b280d5601105020300220304c1c400c0180100c44810b040c1400e0403100d044c0740e68900907481c0c4c000c40003e50005080360241000502e40c01038298820400c0c4896400c00340016100310b6842c184c1c1c48251440b03501481800707420401d50900c1e080c0c50041e259 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 549619181 1250 549617931 549617933
    0x170304090f180b0c1e0d050901110a110c030102120901051f03120309140a03031b02070b0a0c0503040f081504050303130206070804121209062c090907150e2812 70
    0x1100303820503201900c08507d000002608000103003c2e045042c800346040501e0007100c0c80c0e081c1c8400712007a00751071051084000c04452070302d01b44005c10041030301843c1032400d803030100511820b42c1c40040080a030003840c084403900c0340001214500c20b4035800b0347c50401b0750318610030031801803040c804043d08403821003204900869000c40c0c445100d50007541c0c2808414200040c1c0c94004d49161a00703401688009801c1006400c020301600c000031052401540030710b1941c881c14a190440d80280c4034529800d801080050300801c6944003403401d95000b24490701d4951501a12070200906400050f018186640c085507103105c03c036031480d41c0c443c1080d6102e64480c0007080500c4255001144c0d81c00c03800c141c6003803150082d44a641155400d44d25148443e8426403801c08180040d4046020000d40c10018012580d403141440d01c6203201c000141a030f0b07490b041d098128041281503007001d102030203800c01100d444140b80025298012000e02c0c881100d101c1c115501e0741107940c86400c0040d00188280 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 549620431 1250 549619181 549619237
    0xa0b041407081b131b030b0a1404470915011404080a0c03060509030c0a03120f0507020d08070e0603011505040b030403050903060a1a040504020a170304090f180b0c 72
    0x30790310740d107a5901008208040014404003230054007803803803034070764000c42a84149070540060540b100c041c829221a01800505003440d01d0340b074582080c240c508003103012840001c01e1041e42d02284112140c403542e0501c0c0450a221000c885061410400412200d4030a484d44608981c000d03c2d141c1c086480401640c01d102110008600045513518200400300b10101340c00000e0350300c244a414042c1080925a07607080d03038034600c81007090110035224965801c00c1c440c0f610440d8802c8510703070040d281d003500301c0301700070000b4030f0050030030b41030042c52040c4101945444003a82d05440c1c07407403804030380c4500c52a400d9a060107076a00101552100108200070164480c0207405d01c070310309034100c0344a51220301826050720b01903400c1009800c58110b00d40c0c1d140c03070a40c100c0f1303404ca0b002520600c2080d8440007400c2c500403100a90052a5200040c104039116072032107502c00c0300d00a0001084055001030181440d802d02400180846550b0000300d090010004119040342c1800b2040e550000c1c0c070403101c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 549621681 1250 549620431 549620471
    0x1407350c010f02040303020d030902010c08070803041103071203052208100609050f1306060b161e02010e010f0311040909140a03050f0a020f0a0b041407081b13 70
    0x480341650030981210038811050098509595151b0040d00040e10007107030440c024900410144d04101c41ca4074030b50045840b2034000d000c00c82c0140f00240e0750745800d08010b2140305211600c03034000d07070220000b013007081c2d0144002e0034116030502c2c1195403031121a043d04240404a00100e007180c4d00704d00c00042245c0006017100f04108002c400348102a035030410300080f100200d56110402c500540042e00d403940d00c125082a05100729000030329140c03200742d84803080d008050100d4104100c0e000080070300c06040b0200d56a2886802c1c0c00f41140b50640c0020100c5440b10703031181c1440310345081800d02c14000e82040c07804100300d40555071556aa40b0f100005130400349002d407240413141844504018012038120b80b416013580329540340c0610240d1000326030340206c81410450061464001c0750b03841c14031034000b0040c055841c06000d8142420080c0402e9074000c0001c1c40e41d845840c0410a0300d80106560100c410020b2030b50b00041000030128040415032103041d80300d00d107040b480e1084004200304c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 549622931 1250 549621681 549621697
    0x3050105030d14091002010e060a06170102071101210903050d06060e0306010513020d050c1e25030c0506040309081002070809060307050403170910140735 68
    0x490307203001e03010348055444003003003c00c900d1040c80411004190341425508240608020301c00025015100513080d401d28000313581408145480700020412800380c4000b0081200002000b14600101907848000b0903102800f01c0f0306000005c0042908000c00c0303504150f0380621360605010011261030014515030241c151800754074a00f08022550510910710006117920140c01404280d007001d0401c42e2600c04240c4250b140752302003001c6510320f0001c3c0101406459000ca5568403212104a42c4001040410040b85039550502840d100a5801e52011407001c0020344055060034150404481c038864040c80544948103071418842016400f0403241d088610b01c0c0243c0301e003041900c0f80202a07105040d13015007514014072540d1103074507044004680016082c1492860300340d40b81c0d1403007404991000c03c2080204c011540018504041500003503c0599141c6096182540321803c400390003426070181040000c1410341c1280b0580c2d00008060700601640000c1c0741d891340d0004c01c190f81c02107a03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 549624181 1250 549622931 549622933
    0x3180306070f08040213020d06080c12030910141b06060906030106060c1709030607110d09030221010609050a0c18080312090102070c0e0423120c1501060305010503 72
    0x145000d1284541072101820340d43c030342d9003589072a02003010095010b030640c14003a80c20000b40c3c1c0074024a11030140105501800740428401040400c2664a041000c0c510313a5041000440b426a0701c04a081e0a440300c9810b00813109144001c2c080e1044c0107990081c080d54021031181142c3e000d00013103c80c81031208540e00c8031260b80c0c1e4014142640c44a105060100c0d520010002c005001c05d1042c246007002850030f503050592581c0002d00c1e02c00300b95500c201291805c9014442620140a90130500490741401c042451442c1d0114680b546030800c1200c144c1154426410168400c0d00f03d10000d1407070034400c0c407090070010880e07001009a05c80c0034002c07441c51800e11000e81186030651b000c40c2c00484c061800d14690780e80c1e000c05624000d040401c0b9541c00c1080e103000a0103c4400d0018010001ca600500d19051405d0300b0040e81e0104403610003040d1800c0701c0351903000040c1007034140013100e9151351119035950030549400400c4505e254508005400400d006034558000d50403264224 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 549625431 1250 549624181 549624193
    0x601081305070905220210031a09010b03010623030601031a0d080c010c03090f020d03140c0a12230f0405091302030d11030d05060d05010c11011a0f09041103031803 72
    0x1400c1207400c5c070342d418000d410500e02c940241c00c9070700030382c0720b01d00005684c200200b0000240d170000b0314181c426002040c0c070000c0070006100c3d880c1d0154880c0b05c411001c03010700026028141103d14140001041541059112100c001500c0c0c0400700c0002c04000c09040c40e00940302e6440c04c0700070354104005181440d80307003c50001505d03200740103032082c40c0d800141c0c0d44045000c503000c2c4240035484220603403d100c01c02d40e4071079007a140e00005280d000821b10144c04401e105180a200f0207060784c54910401c4501c1100010804a000d4841d0b0a4040080780aa4510a94800c0c10742030250340c0c0034580c8641d2400030441e114513202221859248201c00f502c500c10002e00c41501c400c1840500050f5980c401c1c85440d0b1403080d40c1c0d03c203a030061001090010281c005036075072829a640d291070035001929040b203128000500b401101e250041c144d41801031301d501e020118041c0d1030503410705881014000c01040a00607290000e580682020303054990b41d040300c2c0300c0c0750a2481c0e45601707a0b010380309903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 549626681 1250 549625431 549625471
    0x7080d0b011805180405030909090a0605060a0e0a0f061229131212021c1103010501021209040e0109030507050709060b03060405041104060f06020715080601081305070905 75
    0x503680b0101660307001801e5900481c20100000c10100c402002101d8a12003004684450703620030000920400d410402031000d42d002d4500380c01070325405444c0701d000b403605000034812102d11440d031591241c1800b800040c41601800b21038040c00241d4072117200901440c01c91410b011006410b54016100c840d02000150500b12040010781401c44100191240003048500011f04110007804664a589000310701481494400030880c0d00040140800070810300184282c503100b40510b9002c010322109542c02c56140030300203511048446e00c00600100005841e03400703030340e82da48941c00500b00c03400200012100c1e490040d01ca603019510a032440e119405001460b1000c3d402520140c424648081d415074940c1802c2c080500f00c003238022200001941241e81082d200c501c240001000d422190001c0286403cad0302034200191900568600754040014559068109421a401c07030020701c1d108056075981465050340350380304213004080b40200100058207003019080f0501074040c0d540c1e050300013111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 549627931 1250 549626681 549626717
    0x302030f06010b0910050d0c05041d091c021f0509190f0b041128080f19080d0903021b0301020717031f0f03060522110607080d0b01 58
    0x2d1041034443d0000f00310015690518561446041469051042c14504440b40203025100b802c414640013880100741001a000d250085c1604141c118581d071030682000d80080d900c9003502e00000140880402c040030342c1c0c03882008400d041001409400002c034002c02e5005c80904403d0302c0801861045401c144c51840710030448541a0740e00115114215a8a998104200900400584d40c81c03c44103030b507500c0307912099103d8103403800c074803d00c1c2e01c201121049403429a28036003104100b548072040b8001000d00c00607011080d035640e0a0380c0c020380c110703614084806204282800d00040d00b00107030034080540000c0c04076000202c1c2e4010050140f400d00501d070803401089009000c8614a03198031104034240001990400e040c01d000101c00c0028600d4000908401d91102d082c0300d00c11b44040060042c2403089a400ca481d03079004000a554940200c040407404001c050142011102c0300d10071503031000102c801d081e80c80411a1b446940801095000f011503805481c0490700000c1c3d4000c0600b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 549629181 1250 549627931 549627943
    0x30e0a0f2a06051c060504020d0f05010602190602070609080a030501030308012c0901270b0709030209010905221101080f010b0a030207080c2a0301330f0f0302030f 72
    0x302d50740e146403c006502c081c280340000c004094440c5180c0d643d10106298a031400104106000842c0211b07550400c1d00000c012540168445411504810100381c0d4008802003501511a008171000d6242e1040c1d08100000b0817029800902d1004001070700c10300340e034044e0085030407a406500c900b9500e0707aa585c05609806001c1295640000010407101400040304001d00d0b00308200b000002746980c095401c01201c2266505100070400301e21020700304018200c0c4076580e02c03420524001403c01e1955020402802e01030080344200c507114000034070644140513480c00440d2001ca07070040a07200a003880c402c2c142d10242003d000074405400162100401e0903980d0480317405401d654a0300304483c0b011030013500f04901c102c5054004001c0c600340505c00300484202c1e8500e880302c070b0b024000711028901602410303072030030382c000d074108a41c82c0701074104842078044904d10440d01400b23040e02c40c1d4042034030740b407070f60030000f4410101e04021410a04140c0e050081d68030030b40440720320200c06001d40b81d440b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 549630431 1250 549629181 549629189
    0x506031b0108250c050c041a09070e0415090b041103150d050303090c030f010b1f1107060305190504021e0a0b0f0306040b01050a0807030e0a0f2a 64
    0xc003401040200c039481140500d602c060a442d4152031864003081c06810440708000071000903041d141820140a410f201400b41018111070800114200000e522682141c8040d9284501c02800015405500034140720000c02c0009104200c085d411408501400181d070103505021071400c04855454182482074807034582000c3c1c810707802c40e980c8076040c40b5072001c03488285400c4100c000d841d500147d07040014600a2042c207001d0300e000702204003414540300010714000413580c140100c0c810182c56012948448003900361401800e942c42c2101652520a000302002c40751260101c00540a03502d076009a0054454034890001c4840309007c41c0c00744e131001e640c0039600c00045030920880014540c125907041d50058546101c042e900c21505120f034010252402014030b0000c00c06ca440d03d028440c9800b040170900709a4107003075805d800188550402480c00d01815502c04104064141c1041100c5c1c180c1d0340201800610440780c540320800c80584007104c80c4030106a406c1000084040f542d0384240c07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 549631681 1250 549630431 549630463
    0xa0504020a0b0f0717090312040b0409051b0a0c0b0105010c020906091f09050108070b03150f04060503011a040e0a050307030e0a0e0103050c0306091603020d05010f060f0306050603 79
    0x100d402d041201c14564000050001e4040c01002110b0002d060341c120806442d40c00c503041601c030201802454208503c0f148915100c1404100134040c01c802007081d1015601401c1c8001460703030700c0341001e03544000c000d05801e800c8400480c03440d011300c2d4001c0d10400c5a51040c02480c9007641d8820054845c0c40741d00710001c1d8031051080018006040004100c1c0e40220b2218600d40740c002002c0e50613021880940046054545400050203100c02c00c0200c0c40007402800d918500d10320705141d284501c844e40d0b0280d40c0c0709007014845652170340c0d07694010380040c0400071b000f0000c0e43e07644040c1c80100c94503821400d014a04242c403035a001600421420340894000014510f043c0807035800b01d030380f404810441a0f0282c15050082030300304000d81c07c14041d51151009000342c840704001c140c075202000308960180d600c07a005140510302080c0880c4201c035410b490000301102185081c0d030140c0003c2a0383c2c1881c81c80c100d4001030406211170904212409050100842e403248800d058581c6000001003142d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 549632931 1250 549631681 549631699
    0x103061e020a022503140a1202240403020a0501050915060f01020d0c0606090c0822021e040e060c030105011b020d02151c0b010207050306064903080a050402 69
    0x12500c100e9149040c4442521030203014540b40c0c0d940d21081b54000424128542c0104820310802111850824400d07020b800100140c0d00050b00d4070b5403500c4d014914000c40765800001c281014002c100c1c5440b2640d00400900c02c030716240f00660b5560b001c2c00b00700d10b40c40e2052000301780c65080c0042d03e02c01e9210180e0180c5088080341000b0380d2031500c00e184c01c448a540c1c4510001d094a1144900d00321007000b070b035400a080c101840521818020101d80c0e010103184080c9101c010780d1a10b50040c4440111400001030240c40c07000100103054110b807445480c01850b0403c80303200d0805009606030345090320b458131b107504030a200056070041c07040700a400c411420303003d0f40549820312a41081c2960100f800e07203410b241c61504100a03820018410307229488198041240d130b018002080038060507001800e8516003000000d5210100414424a640c00c40d06004290142d442c0758503142ca084440b480c150765010170442110f9040d04800364001100200403a0711300d40140502401950020a6102c0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 549634181 1250 549632931 549632953
    0x11030f010b090307030f050714011701030605090a0c0e06090f0c0d0b0d020301090302012c070306020702010e190906060302030705270a120b0109060302090c130e0103061e020a02 78
    0x4a940180040d55040c49004000400031b0041c840706401c152140014142083c60024104004580803da00c1c0c14805010141811403407458030380740c11680c101d04045000d454101c10035050040108015226a840c401c0201c0c0c0b0303582c0226014090f0400b91000103055881400d0010070002c16181000c02d03003810403500e142c8004580005500304030060520035003030000e81c0041e0840e4141401103016035101c402d10b00b160014140d6042a07a007440850a00c008408113001e5294003d50100506c100c0d8040340c80c01c01d592188500e00c035807050240180302c034070180126010194909101d0050a03d041c8040852018420300036039000308001d484503418071a10002070000001c0f0306803c00c0c611454130081055503540d00c100100200015102d400801001e0309054507440d0058121840c8141041d00800068540d143c50076400f404450303109850740001030116484440c41d034400c0140ba9140000442440410351120302c015100d214201c07414080e80843c0001d9004408004026800c5804540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 549635431 1250 549634181 549634199
    0x2d0602090f01050f07110a05130f06060f170c09060a05030103050f01090c03020904170d0e1504050a0b09010902060703030c030b030d141308160611060c0301090c120c0e010311030f01 80
    0x6e81503240041410b000c081d11880802c0b090364981100700d0819480d400144240e4160340704079000b1b000c192800c80381014107090080c0c80702e1940c2c540004180c491900040da8980ca4006a5030f06401c0101a103a5980441200a000360020300003038800d4010001160800d540500c1002c2c0010361052510a40c0c40ca180c08201140600500c26503000e4282c143c01c2040074008070090042036086a800641255101c15041c0b0304003421154a1810740e1400c1400b010401c00690860362603401010140e841d920701a24a0142800f04402500a240030030303540e0406801d9000351814040940d020040500070004040d51001804203c002041015591a0521000b00b004019a81803c4904d036040b0b90b8a4901c1840c1c9050200130a0100084800501c5101d81c020080b1006980c1a80142a03d060541080f0480d11040c400d417031a90707540d0020a18224000d5600d0fa0300a070001200f048000144d0002801ca000e006210300c0c006481c041e00780c03400703915040c01c0d40c1c000e0a040302c210725070307038208403045c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 549636681 1250 549635431 549635453
    0x1005040b0705180d0f060e0607020c12060c0c03122403030315010f0309020306040f030906051e1b0102130321050d0e0c130f050f01030503072d0602090f01050f07 71
    0x517540400307080d003040045820b0340655a80e11070030320000e04980c44e02241c02410080c400314207074402e017401c044101350001c0000341d964106001c6484140c1c1c4081000c040d81c45c5201e01179070200b1201900d4200102c0c0301411000600c42c1d10011a42c0c811460250101a1248012078034102101c401d0070400318a0752103146c4150f4203003243d003000100207540d6000a0324055044404079100344486920f03101309503020350424003c00b00c5003002c13820050301000c3e0f820700300742010303801d05086c1000c0703001906c02006000900055601c14001c5580d034040c006a1020409180400e07500c0681d8042d81d42041030541e6000d402d00151070750b4050612084140c0350b070207806e1202e03404040348030b95403504006594806040d441e51084040c0001d8844c11108038609842005200e4800c1200701c100400c0400c0004c4121007809921624110b2421074500c945e50b03081c02401c0004004003100181c400400c106a03004010005003160384501030183d0500445a0703100b03120b012101c201c01404002c0000301d002d088 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 549637931 1250 549636681 549636683
    0x1d25060918090813081b01031512051e0c01110f0d081b0a0f020d090e040b07020f010609020408060f01060c20031c1b080a120e1005040b0705180d 64
    0x4540e28103168404d60780555080c0e40c2122410360005240041e8021420041c00c09a18080c03e090001c00c96001000728182c00520403904407442e0b601c2400200300c001e0065000c4803500c0c03441b03414446051144ca40c0d41d540071401440c08102500780329024000d00142c01030307064803250020403529030b1880048400440282c06114035001903406a40e0030511b24007c1c2040c0035440e03458441929410700004d00d032000380c1e0000002d01007110740030300c048006507914552190300141a0719464464880403071819a6801c0106c03195482d00341d0100b8a100690010310440c1d110704100c1e82c01e511504c4170604420801c0c0f00302c80100d254044400009003410700a515042d4034460b4200241c201507010a003810300000d1201441d4580c0120403140075084220303130000140e0000d040601012a64070000305200f80e01c0140240030810210300705c140101d2f0000c15604c0032010036540c6160f840101d0301c02501054508850051307903000058241da12500030388181c01283d10110308000340060501c081500c3d4144 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 549639181 1250 549637931 549637943
    0x2c0a0b0c130b0703020a0c0e1312020f0601030c32011823090c0a0c15060f080610050306070914270a0e0c060d1d2506091809 55
    0x2100040b045441009068042d000c0d4000e090010713010300d8110540e52654003d550070000c86018010034228580b20340907da54070000c12960a0041d2009a1400ad03003008005103d2065100100801c0903088034082113500c4070234504c4d64595402e000030040e440c1c01c1034003154071030b041003902c0540d881403103059104000030003c0c28103140ca41c1d845ca80c09100c50000b0144100da07143e4401068180004419071003c04001840c1c145408500b0091000c0061080640f40c400800580a030b529480d9000c00300502002c0c1280d96100c1e0781d03050007900c0d804100c680700300701c0080603000503031401c00cc90301c144504000c0d038030040d10500744851600c03030941c0034881c241c10015036481c40c0210201c500750800c143e0100c40300c1c0100b82c0b44c6284401c0c15942814a01843d94000c031510b44800d407101d000359800a08428804100b5101001051180c0c1d8003408841a8605c1a420500040002c484410a03124544c9c0c0300008042d4840c04240c4d0389410710300c2040b03000240555400c611ba50182d001c00a624800c034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 549640287 1106 549639181 549639217
    0x61207060c0507060f12151706060a0807060906120f09030c0b1b07020409060209090c0a08010e0105150d0b0a15091e1a07062c0a0b0c 59
    0x3441142180c7c0c48480c0303c12144141400d500c05000b49200341c0d9441d8510103040c076030351241568214020400264080381c2e40b1f04c00705d49002511466203ca03000c80b80b8001c0101e1b132007100350a25160b403c2e902d00214510004a000c3c0c25003107030281d511184000500d003010160614040d00000c0e503280304d00c98005800e01403109036061250112000074450180d400c10f500640303e04080168010304107820060320311002800b6080b490f04d6541c60b42d00f503030388501c0c80c01d20030701080c01626840310314030140c514100e8102008040180c1c1c1c04401040c2041c0e10004640303800b8054000030b5a415042c24140e0350349903c000540010310352841c94030400100180c0c400e01a04150251110745451003000480c8000e010b07040f10b5050782c2c0150200000314040200003480c0003007894030700b003002c800a4109003d07500007404483c09908500c0b43e100640f100a004084c580c40076401d119424091 = true := by decide +kernel

theorem cover : BRFrame.Cov 549460431 549640287 := by
  have h0 := BRFrame.cov_init 549460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 549460431 ≤ n) (h2 : n < 549640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
