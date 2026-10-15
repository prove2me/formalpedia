-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5360
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:36:55.103745+00:00
-- url     : https://prove2.me/submissions/760d2dd8-a6db-4636-8820-ae928071656e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 963848920 ≤ n < 964028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 963850170 1250 963848920 963848933
    0x10c020c0d21021002040e061e06090f0402070b0a0606080901050f0103230d02010507170f060d1a0f070e01021617010609150e070c0803040b06010c0b0a0b1c 69
    0xd201c2104041d5a101c42042202e500030002e0f48002d54003400150f5036151039100444900ca4255070160290142c001d8100d10100e40c403090054282000d0005030030134029504018a00030003041a41c0c1055003048101c1c00b06204658107445005540c10100d5a507150031001024240003c0002c452649040d061003003e074400e0400f681101e800c08480c2c81036003607004100e20445a0412185024455680306000440d010b410181c8200025181d1a615030031700395000d001001d00b2226045007401c0000040c80300d1402d41c10004c078540c01603501c01802e820802c6032003031921003501c2c0c0740c0c0070700b026000f0083c1060380326501c0c480300d98082c40a03005503031985141d240c0e141072a000d2500300c1c1150405448080c182544544000c7c00d14001c240f00f489008056100c1c0c0740024001d80700ca1a45441c0010115402541e030022666405400d182c0740d035886450f28040050003400c16410080c0c2c078005c3d2300105100003149802103140c190002aa101c02030308200250300000210010131000700441d4010520 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 963851420 1250 963850170 963850193
    0x5010906260c0903010c0e15041805071e0c0c05100c06090819050d060603050c0406211a04140c0a080a0605060301080f061b2217010c020c0d 62
    0x261041c0314985038031401e03941402401840c48054156190802c981c0109a220540300c5030304c801034560043c042c95a0754030f040307a4030440c0902c8020f03641c12040100c0700c08442d4030040d072110440c58141d41d8002c18165056803803542d86030013400103c01d03868000034080c0e6014540014607048907511000041c6c403601074052140c0c071002519055603107407010244040101114464581180c070665140040c28001c2c0c259001864001500f134500100072450303500030710a50f0b001da032070418258180b6241000403500b4400104800031500410714031641d840c0c0d454001d4950504070202030071f030241031800c1440100e41d00d01113083e41741014481070000b2038401700704031400c9481c0ca18050b402950b0344090000030348220b521154101070004000030b918500803c040035401c42060542f813180d07d0b00010001111849009052998010000030742d00d98440802e000d00180c9000d442419103941d80340100c00e2020030511801d041e5120a10640310543c10f014103a81150b048030704001c100d405071a850541c94 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 963852670 1250 963851420 963851477
    0x10305070806330a030c080d202806021b0d0c030905130603080c1f0b100521040302010b0f01170a0e2503031b0f11150d050105010906 59
    0x100b4180c2440c4407900c0d40c10680780510317003101d0f0a942c450b51f12003001c2c2d5035600041245000800c400c5005040303404031482c10301d0b6a07926400900d100c2079100080c03407003c44030300b49070002c1d0807188042800058050007e031009140c6045034081c40703440d00d01600c1c1855070f5403540c4410411042109000030fa0480071030b00c00e440c0190b03440518814202e4110000740300f290800340c0450030100e6490f03119031000504a0048801701f11410354864408926170030f4030784903031f00c80e030b4000280c2c1420751040b8032135405001d0725258a41e01c40c8131009214251428100140c4041d80180d44500036840a03091421a0600c1408d0031701c0c00b4040049a5643c4807800e080c0030b8103410885440d02c039806101d4008000300e5035440c507041c0c1c00310410b080c801800d0404c0312552000302d02007100e40b00480348001c080f4401c0020a074002e1021643c6071007599030f40c20740c81c035284242644140b140c083d110403404204060300c0c80510301540040ca55060400240a14400d030380018200f02448604400c0d000804003200420f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 963853920 1250 963852670 963852751
    0xa051c05070806101115131403250804090902040b18240112020f0f1c05100302100e03071517090105062b021e0a080d170c070803010305070806 63
    0x2e445014040350141008400a42812030074038004400500200082c92078060350a070ae032003031007954080c0c40015100640c018140e040240300c100702c4500190800d045082c801000050b400e40104001640740e519040c0c030380e4401c0300d021b08000d10b240f0207180701041810300654a0f43c0410780540020178030481d0004905c00c560b00454041d038246503400036a01036104032500951201701010030319a2410b901c14500b00010304100100300398154842c0420b06036078000d0320044d00307030503c182d085d030780d03c0b10340c6c0789941d05440341a400042107144a00803000c916145c0e610703210078500b0040c0210043c0405809070805902d0034061040d00ea030b4200180e000c810200c0403004400402881841e00310944180c0a50001c03030142e418548459240c05004248004450a1444c0e80e140c0020b66504c6455010410100311341c40c0e65800c03004424001c2e580d2107808051618a8015103989072401030b0000e03030003110749505c1481e0a01c842c8009200040c1c2c000782401c5400b41c0c94002510103d24840b00c80c090b030050307 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 963855170 1250 963853920 963853963
    0x708100b09150f0c071e2303030408030c28300e01020616080114040b040207060203042a0b0f070c180c05040b0a051c050708061011 58
    0x45844144a031070851120080b0310303846007440074094249502a0401d02c0d41070203152008a100c08250750350681c030706c02c0150405070a43c00d004c1e0301c042411501c0701d074018055800640e5590703550104000c01c06040020091900d408807100e0301c0b80742a404000020a1443c9061180c00c2003005000c40c450498201c1c0107404042d41e5281c10044c2c04070040140e030f1a40c424501614422070700300003070790701e4404203a085540654840c500c0d40149000042604001064000100441e52240200520301e8000078000039607000c0e0130000604030707485820200c42103074011080100780004410402c0c4218040504440c0344005d201d10090440440e0084014100b00400d100d85454590400d8450142d80080245096a03e52040040031184c54820450140c148001031804a1103502510104d070460f41c4011300f408003101c01940d154000000c0c0040185c03103686044021491401418000c0d255511001c4a9007495000d010126101e5491001480196a4010307030805000468415202e6000c001500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 963856420 1250 963855170 963855187
    0x1608030f09010c05062d04261201030b011a120c09010504051905150c0a1b0503030c010608010f06050f040b0105271512061909020c160501170a0906090b1e0708100b 72
    0x2414009e424004a454452400100410030404a0b050594004200022888810f42030070395030f902c00c1414000c01c02410300d010800169404000c0d15800c0d1050419508198498000c0340071006a0384e8140d000c1444128104407074105482405079250000a10310f00d4041c0702d560142d1b9542e00c40000401008101149001c041003540140d00500780007010303a0366a00712041320318040d19581c010002107500e0407854100b40c881a20480b021144098a80076850300741d002080010034040c4c00840c103106d0100540c41342c806414051126121400c66007440300003190b410b1000c2c110f244074400e200501c0410220b01c9211401010308d0340100100c995030442082d050100c2d084501ca603018411240c00410602604040800c00c40c03800ca1000708054200c0350b4035001101c0b16111521100c0c50b007402c220205004c5020380d0040c01c4602d0141e0008204542165183c140c0c11004445581d035035030320b02602c000c0480b030364040340390001442e1800c50600c1c10260042028901944182c170302100c80018500d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 963857670 1250 963856420 963856493
    0x1a040e0a0f150f020a0f09140f09091603050d0f0c1502091f09080c0d0215030a0b0d12080a0e030a0e030f0f0a051608030f09010c05062d04 61
    0x1c85109641c1070a649174074600c50b02625000e1100c2d8604040740b0405008911000150804166000001c26a25000441500f40103400c103021384004200d0083c04600c00551184540c0d1100541c072a900401c0a031914080041c002200c0344d0b028410800d4510709100403039100015140b480e200450016921282c8800054429648032100007602180d8120000040e0700008240d013102c008070b060364444003401081200b1103400001c02544828041c009807482414140174660003842a400002c40d00d0340301c0001483c1d4400b10400721050640008001d40d86035000880c0b0703400041501051008451000000e900e82c000c4401e004100603030100760300384c960780802401001400403001d42e4429400c02030b41035211050341c00283c82d02d00c40c40090396240300d80d00013140100cfc2c00420103503051400c01002d07601039034084065107040044510407203000c00c8041c46a02e000f00f8504020369002c0c941c220061130035414030011410980904010071010907003260302c0800350b400c80200306003000c541e5030307208 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 963858920 1250 963857670 963857681
    0x905090a0822240809030f0a091206020a0306080102091f03020409111305011814010e1e010908011509150803040b0307120216020108191a040e0a0f15 66
    0x1c20358100800e000100240720b41c0c0d0002c810800c1804050f6801443c0b90f040c0d4a414003503070070342d100b40d204100084811107a1030181c44000c10702d180110006581c0c01180c12800d50b9101c054580950000303400c55840c2e054880c503001000307298020f40c1420104000070704030000c0303804032903240320001d03185940c82ca01c00c1d4105c0f0081c2c8885202040446410800b11407a0741001d1040d150703080c40a0004107196000d18404407255a8602a0803201814540f00ea641a81015501410b02c111b0b802502516500e222841521050403c0004001007217074000502607002c9500000d400d03454034803007040e0020300803003410588400300008a4901c00c42040b03015585000d0788611000c0c040401c0c0401c640b8420401540918026544c001c149149144410220700c26401d06500541d500303410342c80154050300c902c5901c204020403002c100c19801d00c0500644400c041c4480c16802e8034401031025140134400e1503c01d135000c0c001001c00541c0ba999034605890b1100025100c680d500d0481404007450340c206 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 963860170 1250 963858920 963858967
    0xa0504080d0e0318420a050903010c0e01050703030e0a061404030801050108010e01030618060c2a031704081603080117120a1b061506090905090a08 65
    0x1c1207800c0c2c4114080d0b45a401000643c10b0200080388003040b030789031451905094610250480821002d0354400009036100e00d4a41900c0f01d061084052401012801a1034030245c181c9444da666207441d0304240c2151101c0a01e1010301148911309442c45c2d0348442903969403a45814000340d0400d91418181c500f407884400200041d040c00190b000e681c00e454a401d00903842521071110036600c90006550b050424040e6800740d110b0040100301243c0940c004007440c062400e9213132000c5d00b894543d1001d40d1113504001000c24084501d5080f201681c6140c0c0440c100200145102d04c03030799540c02485411580b03102047c0320440008a000e1000010440b03840823002d03143c44d149110503240c06043c1c050240b01e070112500b1080741c07044410034041948041450070440281c0707401210a000d0701d0102080d6000030300d040d0340c1080140003800a01c28440c103852445043c82d585464440010034404081d003052004d9828030040c001d510f040010710001c1c1c03540c00803140d92180d40352040b0780000c682c507818 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 963861420 1250 963860170 963860197
    0x708160e0d030816171f050907020d080c0f0a0e1908072102060d0b010215091b1206010302090a02070c0e0402030c10090302130f0c030e0f0304050616050705090702030d050711060a050408 82
    0x9c0c0440103400094101e511a0b250f22040d84642e00e0000c10942401aa90900c0d140d503000c1119804c5548110810181000002d02c140312940b28a28032070104c140c0c641218125500c0003105001008141442d40103001c00c020341000c0c42c0301030b940411000e001c0c100422460301d440b078507540d1182c0e000b4032251490300074500e8241250b103400e21301e490360307094a0f02c0003079071848000ca072110f09401c01d8200c0d028115041d00050050380d11f90742c280200c00c030000340601d400b1542800780200181c03c000c54071000301815112a40182017038010103042c02c0d801194030384121680e60f0f80c0c070222134000c0300c1001144d404a0707422802080a40e845400303000d1026019007114034003011440c10a4241d0b104400e0a2600000c1b00d04441801038202da40c1c1c400c034080c05500c214180420a05c501070b40240c1c8100314400d0b002d990140f0ba0381c802244d000711050b60800d0160b0400324540c0a030300c1e614411640c0c001128603080041d07190091056496400c05409407102d0340d203a41c0064148003841048038610103403241c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 963862670 1250 963861420 963861439
    0xa03080d0902040515030607140f1201030203010f090c060f020102070f0f03171b1b03040f060e0901030b04200a08030d050a050708160e0d030816171f05 67
    0x9444000900003004100c0c0b03e640b034000881c07043c2c501c010156404a40141c02044c0d6038640302410b4803040c4812905141400007040980360000c1c1800291040d414103d1011501d0b5045204050941e1000910a1107203464070303c0d8140419441203c1c5070460382c007400c00355610f0420010032400f9119043d40941020f40143c8000c0801903801c2946608601070340d03e43d070000800070f000402d2440c082d14240880c0c000749281401c500000802001001c031080510f03000c00202301e102a085400c568403441c0c5560346500100200750700001030f1030310b44004071900344181d810740d511810007100281000e800d00c3e10490010768882c00815000145140051842240903620400c0a503203a1114114071103043c00c1c40c01040d59205076000340750040d80f9503100e1190a9403403000e11416414440800010800d540044c4006a01c1d08444c2c840e07160700075030700c0b0074482c5000c041c04035185107072000440410a80042c00700c1c034280c3c051005500a007050107080304130700003041c00002c01c2c080c64001c2c5a1200542 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 963863920 1250 963862670 963862687
    0xf090515070203010f090b27060103111003140a02030415090b190605030a02010813060f1a0108090a0602090d08270d030f18080a0c05090a02270a0308 66
    0x203028203900e901c210000c1c800c500b52120032400ba01c6001400a24080b0070740c1c00304075a0303a401034910510b03034032110319500b00606078203000745441000e0b4801da49401440d0800d255504003000c0000660809040521170012102501041c10070000c103114011075002c000f1804001c22070011a01481d505102844403d0050074040c650307810694030301c0320300703000700c02d40c0d48508005e07004200498200030060080801b00f50019510204002c0a0562140300c0344070880015081c0c0c40f03480d2074090102e1000803201014451034540b00c40d40300d901410322110204214090000055036162036920200250301c032104480030070400da80c00803000301100c5c00411900100c02c502031803c110601440e214400310360800c024840b41d05014031002d03001031200390301040d030f403130003056010340856401000d91089540c540b1184c0c03d01031885800c6034610140c24041050b0300d4413424098001221990442c0707448600d0306a0301280411a1415403050010007841003282d071200c1211004642100000b80e840f50403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 963865170 1250 963863920 963863959
    0x318061a130e0c040c0c02090406090b0f2a040f090b0a050607121b0c080c03060f06032a0406030b09160e150d021201020a02011d0d0f0905 61
    0x9150800d4012034181c600310111a21601601c698010100081c1161500b00342c00d0002400d040145076003801003d00b0381b02c0050700c450640c00d102d81c0c09050300040c280501e00c0c2403032208401500c045000318081003031201d903440c0c1441904d010300c01000d18072203940401d83d50502c2d034015984501104504541c2c0080c283c2026000362202c038600715500f101ca01d0310741c001c10056001c0c90381d015040e49803140000052a008661041c402c0c4000e50400000d02000d58880303182c428260860704094214407141042404c0c20040f1a40201d161400c034600391a112003ca551004c201d101ca004d0700342880312060482c696402104652140640140499512424500404170064403020040e21404034038030211102c542400069890300300700d03541c460300c1d540003102100d86c0e00c160b140c0e4010011080000181c2c1e41840c0503460100c0f81d0000760b2914211030001c0e084030841d500807010340c610040c4030340e952000410014286130701c0e4141094a018081d0b01100c11a440d90401a008003500309c15100c060758 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 963866420 1250 963865170 963865211
    0xf010e03180411040e0705070203240f010e131703011403100c020a02090402040b040911010e0316030204050417030901060311060a0c1217040602040f1d0106031806 72
    0x2101822507034084000d000740030807210380f507601503010354052005021161000c201d081e04000e03589005800e00000340c000038140041d00d100401200d0504460581046040c2e00460f4010784609075910150714128189a1003940144000307820b881ca4101d50040280044100440702d00307900e8550b8581d1307160081d0880302d40f05940707403338840c2c031030000f000d20000301034019a201540250302508600050340d0900490140181040ba070080d00e502a42210380c03540e11805c000c0900407000c03643c2c3c50b040310b4009041410b100000e40e0003508480710b601480300310a60700c082200d9042c0c0b000101681c41f81403240c00d9103454a807189401d64000700744030108505400400c16240201200c9043c1400c2c1c1c0d0401603580309881e40840414403103945d0300003040d42e22141a00040d040d0900f0708400124031800124050100c0d002c40b072055000c6001d20100d030469410300302402c12450011591541b1000e01c0418840c140308000406490350220011b18580700d000001c2140e000409101074800768066011040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 963867670 1250 963866420 963866437
    0x2c03010f1b09150509091009090303050708150f0f0604030c0f0614191103090a180501050906150703030b1f03050c030c0702010507230622020604060e030f010e03 71
    0x21180301c0c000c41c0d00344000c0c3c01d4402c20411038603a103140c061518240480c8000040003811b16540060f80010212028098100c8c1d552182d41c0026552804c03030701c060000a005030014000300c0b050b620303842e0309441c0c02e42e4600d92054111f4002c0343e013640050008451b8490750b00700401030650a43c1c0050702d0096030514a00340d8005454003a4400c0710362015296500404044045040c040c00e09445403074010900c4070100310000095a140080d140302280780168039500c0943c002140b0100e2008840301403107000c3c007614048070f940b21b09040440001e8160101d418808900034400110802058000d9200d0fa03140c0101810070ba41c0407501c00e1400211603842c103402c1d400719007000c00180d04c03041d9180403240718122a42c00c0b1420442203800465040e0400c250441c1c2803110100003440741c6410041d61601c00a50070300401c0e05141c05555184d26050072180c2d1b40b10440f107101283d00503a17a19042e5010303180c0724901081e080a00c500080c0c901405050032401d20f503e0000000c2041d90301100514404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 963868920 1250 963867670 963867677
    0x10810060c200604030f050c1806010503040201020708070807051f05040620010516030b090702190501060506070c1a0702010c02090601261005010801081b03120f18012c03010f1b 78
    0xc00c0782102744484640e4622510403a051810002440c2d5805036004e59089801841145d6880c3e456200711880c3c02d0094212000340d41c0200380411041c90280c1c00040420407840700c154001e00d45240140140c06140640c01c00d00132815100d40d90602c4030031181d03241d440d40ca0001d106d20306003010058245141c606a070030000341410356400640c03c1481115010780f186038020000c070031820b990208840001d42003100c0554a0340b00000e0a565a64094001140100514030503140303040080001c0e0584420303034860805082c0000c2c000750782c000a03400241c0d038041c0c0f030700f01c1d0360307510b141c0104d8114000c903809098040340075024080c2c84040c82c00d0b07244596100c0d288541000c0e1240b00546142a0910484e101507012413005130440c128801c20000106000d8200c4890040b40701c0c500c5000c1d04000c03c162207c090101d081c444040120000340313034920082c2032228000031403030710031040d007120044141c524021030341000350709441c00d6015148141202c44100401510303800900080b6482d82c0110000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 963870170 1250 963868920 963868933
    0x1113080102030f0412050702031b01091719080d02130e0106090521010e0601151205040f03030c2a020a080c030a0b04020105040e15010810060c200604030f05 69
    0x1a014148226802450540c4103c801071381c030b070b40d103540c5a0072201040c01c081000c1800240011784040100030407040e1105440c060941541e000101710b400c0c150300000c0156a144c801c1e490740300d008500340b8441d0b85840b020000c945034a06140403140301b10115002070701d00c002124088800c07401d80d02810b651407080041d0340d40c1da840c40100c42c0034426001c1d060780320802030136400841d00341c2804140000100d10002c1000b408106440b814044264800d0060300f2440704014105036002600020b0004e881000b00038a0400d5281c00c1c0c003607160100014281541c503150040346a014a64495481c42400044050160700300c10351a5101c020420483c01401d1380720303012400c841d01080d601d5032070501600400b102074060321182c00d460800f4000f40d0500404101c0800e014074001c804601c2a04036164007240200e000c0001844074400812203981030020000601c492030380a05480c0b0740540244c500d55200215003142184a0046030a041d0310660004000007008a00c0004100050040003504d25 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 963871420 1250 963870170 963870179
    0x6040605010e0109060507170a110709110301031b0503190303060905010b03041b090c0309031d10030c030b101e030e0d030c020c030703110f0102030f04090c020a05011113 75
    0x4014241501c0180866102c4c4824012944290060301c883ea01800c00c001e040e0001540300c040b9503009020b01800244414034103000d003c020061103004003819074040008001010101003103010602004001202084120700c0d200320714040782c80a407000034140e03040a031048682c1c2d500c8032142e8000301c010038108040064038480343d224050407141c030088140c5c659540c580d5610425000c0c91205070681c0c05002005c00d4107c0c50f84a1030070f03240a25140010640300314103018120b04005d09403059001d000340c0c44e0189a8440d004044007206035428007040680e51414140c002d000ba8800154001b25400340d5551019484155001c6100c1d03400e000708800300b0319040c210103035010717061001719542c08100070348056440ba602942c2c001040b40705070b43d0f05014220000b8185241035005680342d0003100074035000742c6024210440101d00c2400210b14050040000352030900651240c240f0031a5103a1406012a000740700300040039611500810030f441000140ca001c03500b00ca040c0c080240d80d02440842c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 963872670 1250 963871420 963871427
    0x1a0a3e0613020f060d0f091401020a0c030807020c120706030b01110307030f0e0d050a05010b100c0f0c1503020310090b03100507120c020304031b0515090301110d02030604060501 78
    0x140a0162100081103000007074091148101240c1d00720303501302d0001c1040d001503001d940300300d80750942e06000100e0010414101030684c085440407090b001e0344100b020456498015407034070342d001e6041c140310440f03a03103640c1c05030304000c06107440c0c82d004440c10a003204803250115280042c0c401c181c80400c1001e0100004582c0802c1e400002c044552081020902080c001c00c41039401c180e4500d40035841240400100d5079601080c0ca08440a50012120004200c42030098601c4500c058911140b43ca580c40c0c80203081c0f070300410b40507211403a101c44410a01c1011803a4101078403c2c1f07c0d48802034008204000c000b0b600c01c60366500d8580c446000444c450b50180940d8082450090080c2400040602c1940c0100b50142c40300c41804001c0303049101e025950f000d100001c40392030300a5500c80345181008103450822031090410074072038403801d0001365101c0c4d100d00c050025010358180c4a003e4030011900514890030444021a804181c40d081c0610359001103200719415103050108036654030054 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 963873920 1250 963872670 963872683
    0xf0f031608011b03110307051e0f120c03060d022205130308010e0c1209010603021c02031005060603040312020f030a09150c120207080d0603030f181a0a3e 68
    0xc1c020310b00402c0400e01f250b1040000e0003400304c6e5002003c0841507400c032080c0655000101c4075080200100e60107141041102d075442e070140340d100b00140707035160501c0018031051015400900c0748041d455030350074200d40c032030450b0701502101e8020050390070103010040400c9030b400e404400240654002240c9441c00f400c1c501e015441150109050818040c0d4083c40b592004003600025941c4000020141c0c6c2c450740f100135400d500740368020417030340039005250078140040c11910519040400380041c81c0c680c0003c5070f070700940519090481d8071020340604040c3c8580c810314450b454000c8240005403540d6840a01000e1242140701d07600c401c080510000d44002c40915408a1118441c03403102c00b0f49500208074141c803a000e03039480c2200301004502100c08a402c294000f40000b030700b008d00540c0140002143c00e0610420580d50b501e411400840391162004d611841d038008a01020203500480f503090b040245417420213400040702002242104800304a0607402c400d030310b02d800318030b003011940 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 963875170 1250 963873920 963873941
    0x209120c0102060f090a0b0a02030901110705030406140f0309010b011b030c02100c020603010905071404230d02060318011803230417061b04050f0f031608011b03 71
    0xa056039542d8400c0e2030146080060440d85c490092004450018042089152048500010040c1c807420100c104501b1140c08447e1841032400412800c0c02290001041d034044402500d0051001c02030600c0302e506038040e02e40303090494980441402080607041d0484101c1d9207080c0d03120380e5590b04489041080c03402c0c2030310240104088110440160516030708044000c030681c2030560800285c2d50100e18161700c240d002d0710402d50750310180a04a03902052440340c03e800c061041d802c003400c0031080828144100710380c24106291294038030043d1144003d1404403900204096120310b0285403120b040c6110b912108015443d2103242c2d00c0d450000e0100016964042c1d65174005040344550307c06030016401c0c24121032401c1408000780302d06e611415001d84100140180c0f20354100f14442501031500c1c13400044c0b0b01c1d0710501c014881502c6120400d00c803482e045482c0c414410007140800d0409055003250715200505000100e00c1d46015044440619141c40c2000c0503040416402c07401c0b02c41c030021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 963876420 1250 963875170 963875173
    0x17070318060b03010635071d190903080613020f0904020d0e0d090e010b040b03060f0a0807061d04021e030c0d06060806010f0915050f0705100209120c0102 68
    0xc086000c28480ea100180c00d0780c0240000401a4842a4619001846500081c40407122142010000120862000c040020200280502410f00348510b040d1284200ca031048070841100003401003900600f02201c8201c0703814100600885420024807101e000c65030070340602100488a5502d210510840340385480b94100d09042071600c00c00c00000c0d6100a400140c0c50791a44c139a000706a10038000c11584c039005e034452501c2645402d0f14642c041105078004110f401c01840100f10160840301286e600580890f142c0ca8040c1c204400078100b068640c1003000300784036001d80400d0580e041803c2c0512221003003401c604008495080100742e01c20045144115695100500b000f07455280203503400c044603064003401d000709046c41004459042e8010400a101d52050154558000540003030640c140d103041c00c02503081c6507241901342640c150351000c00c00c00154281c0b2440190081d01c105030780c04400d81d48449400ea4000c0042d421000000e0b21801440807008103101c8002429561420181c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 963877670 1250 963876420 963876461
    0x702030a110c04050f010609090515270708011802161b23010e011706090603071a0406030c05130303050d23040519020312030c19170703 60
    0x18030448403040304880c0380100d031046000045581d41c95000eaa8481c1c8013880001c01303698980003000304403070840c1e400400310500e0601441030323402c0003400b00b001e800d0060743c00d000c641e000601041c000c40c0307800c1c03c203943c4101410700f841780030369004561b14101c488100c403841601d01d035011581d00320300c1040030111102180c0200d081c00038424503404814503803207921420038646d0351212211010141c1c0c948445403000c0b40c502c40201d40e048804180207900030701c0e2100c01e8a07001c03059081005c0c000381070540328010f1a800a0380aa508125941c0900301f20ba50340d1180842610034440103410078002c90740844d040100c0610220b03c03410070740f94841001011041c801e482e6440c2650341754407603010308a5058848a0030b0725200581c0c0450000d820256403000c42a00e85410800d080803030a200c4007038800785000c02e034809070b5400101c203c100381076013019070307500d456900008149100d1515942c691a1004064000305504280e003500c02545403200854140e580d000b00310304554207450f02140020144 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 963878920 1250 963877670 963877687
    0x30c08031215031603142118060f040e010f090504030801120c0512031b030915090418030507033002360307050307150c0c050603012c070203 62
    0x440300740300680d0b0050103443c0607a1111440280e01c19142d00b0a8130400c042280075075905008005841180e05126001d04202c050103007804601d01c10010211280424020720003400c1c0d80380003c507055805c1120aa540c0d59079101c03002045181d00348511909002041e600003000c00003406114400d59060396826141c0e0308008000c00d201130040402d0b80e81000a16000c2540d4403000016258400031200540c2c590201c1e5000d004465001c02e412002078106004490f915150050140e5510f0592084c40340c9031b03d0f4040c042401415001313100d60600402007005c400307140d00b020080c80302c0340c00313580d4050070b00c4013150308070b456607400080c61244202c1c0d0100d0141c1c0190b090740900750748a001101d0705410381c0e000d549019042d8692460090840361601c0c80007480c501080854018801034005d13007c0103140480c034803a480c90607044041488214907041c4104002d2868035030113807000800c07042d120f503100c5811000c103041c481120203100f00000c8505070310180303018000d885402694011450800f12 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 963880170 1250 963878920 963878941
    0x3030903061f05040c051801032009040b0d06090317070905010c02040e0717071406040e040c03290906042102160b09040c08010b0304060b0604090213030c080312 71
    0x7081d15102d040c0003411000c146a610b0703019910100c0100d03699541c0340c3d03010074002030118618107181d074103143c83c1a030490399208824a1310305544614100c034681710f179181c50204003e8202c01c1b01980e0710401e4980010104800e070f80c000f044071400f80d07590200e601050202c0701c801c0f050503180c2101003030117948104813a41c032418146480603c083c10200319401e5102209191141581204c0c80c00d404004040362410020011100140341909198941c0704400012407043e1042d03010f40303c00d00b008107001a092000c40320440009551180030912500c2c144681030003030005807001c0c0c1583c0a043d9011a0b17105a0001c0c1d90b5000741d4211002c00e1445844143d00034614581d04050001d5018400e203c401c1031507865116001000000385243d5604030b003108200840325101040c1c02400f8000d001030040b000600f060341e034070540c4034400040540501c0e0000d207040c007a030342c17004107040c1c00041c140880000c03682401044904c42d1700f24a062176210b000244c3ca0340a241d00b4100c94070350700b000007140d92a8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 963881420 1250 963880170 963880201
    0x25030503040e0a09050f0a0210020a0b06040902190906090b0d0201080703152606011a0403240f1a0306060f131b0f0f05030c0d020702040b0604090e0105060303090306 73
    0x6100c3c0c1c00036000c00e60b6510a0300b41010316080000a03044199204250301702450039154401c1c00e4030180000040a5a8050692801a0003280203c0c2d50f40407072021901ca40c60114030218400da0021502c0760740d00e0004016003564050607540600301030200000d810045040d0110301ea0507151043c41d59100b000840c0103000d030400c090a81e90f40c5200006094041c059070100b22060100e0003076064807085200703072070309806038860001101500c121600c2152600203841c2581d0340f01403204015000081d101030345000e4416445651450300162200340d84081d800000d40b240c0c0c82c4001a40075801500300b646030355084810301c4c2c00a514070201c00303491811a85400e48101c265000003a9281c20850540d404407130704040002240c0306040810f201034000b0581c100040c10391405518500d0204c3e0003002600074880406049600803524074110359894100b80c0d0503800c09041c0c0da44665a8142020140c029411300300340e40d511705008214141000300491301924000b40040030a40c540c4100d40c108100c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 963882670 1250 963881420 963881431
    0x921010c0c0c0603021c0c02030912150c030702030706020d050610090501090b070203030c0613150c170c0d0c0e01090905010e1314100903030509191e06060825030503040e 75
    0xc120751b6414880e0101880782804880d1590700071030700d50401409001c01c06c0244000d5002a6021886503404d41400c0c10610b07074400001070b009510380c0c640000c00e902d14060302800a001500100e144003640c10290f1005100f200203c607442c4646034a054241d4105480e03000f02030014200300c800384601ca8030140204000752014088a1820054029030f9040903030954100d840141514043d00a0241001c0c50902201840e00200042211100007900c4446032000841c08160b40100266410351100f0a43c3d01100f808841480b1040da008402440501c1d6101080d0108d005182e0204100c02035124041c161803030001d9070415a103a80000070f400306009482100c0e10803488540d10a103034014041c10041001954001c100105903190281c19100001c01d18042c903400b2005155034000091108500150080004a0320404101c09840448803060000c2c0010381080000100c1000000387c0401d2424400c1034144190450500020480c210f4440540720b90301c14003050068103400b0294a401c41c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 963883920 1250 963882670 963882697
    0x24030e07060509120f01052a030106080402010915200d1b02040e12090a1508040b0a240306150302060403030e0d1e0209180d03110921010c0c0c060302 66
    0x400094401da1070305c07101c42c00000560751604140701360a000380c01c001c140004010300c104040452003810011078041442060100700604c00440c0559010b0402d002c041c00240781e010b4107121007050050001000d40c40c0c0545940e03c0d903200c1090b1020301140c2c2002c1c82c501a0b50310170140418030f40c680d4100e403101400703a03405561a80b0641d4106410001d00185003610106141ca0b06d000c0000c01510f0160f9a10180e501d40030a070240c48900d601008890340b140e800f080c5000b490316484000c3e8001e040b56000014440703000ba01c013211001c1040032180450788a80c0c0103114120060700b19803500d071902e1100a42011042c401400020700a080003442d101000c0e10020604c070320342d290041b003001041548009627411340405415400c0030580150f1180e80307011200750581040034525900c00d48040c0b02810140d076545030310081e1005408891007403000420b803420200c280788141640b000414205c40d80340d0319110740c4100a90003108410070641d00040344c00b046a14005042d0041c0d4071000800180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 963885170 1250 963883920 963883939
    0xe0c130e031c0b0907050901031a040c0509090612030306010f12090807120903111005070501021b160303120b060c0a0602040801141b0906070c24030e07060509 70
    0x880420030290100d80c8142d422212004000c0c040481110b0314038030024010362250040040441c0c101044400702d44080c40c0c000b9244441c80209582c0e4004d080d980303a0f0140c00e16101021035a4002c025203504002243d000f1501e84507841006040d680c4150b00c040300790070070310000303440390b005010f0319000070b40504011454082052083c000c42d102d5035412140c551010805e03d00b4070260b000c50541caa006410580e01c550309585522591101003000c0502c01e15490070602005441107042c0c0d889a503210703009545600e54104503140680d0300c00a900046e1054441c490047d000090640c02100c0d01520b44007034408002000b070001d024413948140c0c000303501f040484281079003040070701c001a02501e80140c03100d0504001c00d003500c6066401100c070940e000c040c0074245500349010400100760124150b952a8200301044003401a001c011b01040b400303540000e140c10101c4c4580c1d42400c500d2014036004a030018080d0200c910701041c0384041d81c8848020701010340104001d01c0000750007008042d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 963886420 1250 963885170 963885191
    0x31103070506091c020309010806060c0705090c09030c030a0b2706040c060908070b090d0c0e1014011713081c0204170d0503040305070309051807020d030e0c13 70
    0x60b14405540144840e4014540c0e80d0110310310104c144010750036032028500e001e00c1c0c080001c00034032014040d03600c00c00b000244949140d0040141c14001e00c03000c1e204041ea4500301d0400340e80768000b0780c03400e400382c0501041e000451a000c114102c10991000081041e032301c0d00340b1502c0c0c10302c0024004111981081c550134240460402106100b9407080340c0c85400c00b41020001010f4518551001080b60f2140d03005100150b40b4500b6a208808262901c01031070940d410807150100340c13540070070040d031904014001102e20742071b0f88009403441c1140080c0100781d403100456803403400c8021000c04182c2e41001c030b075510110140c084150b50050141c50b00f41004a10515021888440c4100c03510360b0000d010007200b00162452802d4510400c00b50020150080c0003130603600c40104000e00b003040010b95102014001e0715488060100504015004c808120309510541c10541c1c00d88058030a01c18a445502e10074020307034200081c0b10700500032420101d014400d149204c1034021440d04c3d248c024100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 963887670 1250 963886420 963886423
    0x80f07080c2b170c100f27050c1f031802090604090c0305060709060e0d05070e0705041212021e0c0d0501111602090c0a140d0f0c05030604180b040311030705 69
    0x40819000c0282010a802030400011a000100030f10b603201c7c00d04c0103c15549280d4080881c61b55801d101d02c20306c410b218178107182040083c01640d5807041c4840d103080e013080441d00b0014103076031041d05c0802005010107030f06030242c03202d501d00a50220601c0001800b5081c02e4000d0014240b2800302a113410b516942c41e18140001180c045000074403010003048250b03444000310b4424841502c0c50801003000781c03550380c2c4130200c500804241d90b12810104d030959114100300c3d002800502008002c0c0c80d0140b42610303120382d100001000500c0717a82c0311030740c001c007001031211002c213030303242c01009402d80407828000d50f030304044c406442955859200c040c2ea00f030140018030712445640960b0f001c1d01d14501c100310300c0705005800f2040901050180c0b6030000e030072808103001508100070076a1542c0c850450203004d40080e501c203021381400c1c0050f54108070741107400b5600509041340c0030301c408076020740c02001c1d0103c180f43c042d1401240001050109018040c21001240668143c0e80743c010540c0343c1e036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 963888920 1250 963887670 963887677
    0x19020a060f02030910021806070201141c0b040c0f1d120f01110703050a030914150f1e01090c110312150906012007080f07080c2b17 58
    0x840c0d202d4000041184840d4203004510a03501d0a8401310306041150410f447c0360794909203603501070f0400242c50b00a5a002e01030440002c0c000f564070f01d594014000001900843c0b0a41c1e03103034514200304139070910b441e10340035819a54120b42d4036800c00f914008000c070f480e0b0f402030810041445001ca000f40582e00d07240c4144440020341801403208035160b04606003100d2000150241e60001448a00c0010781e00004443e00d80140d80b81c041821880360800015903050104c803a440b601c0b84108000d05007841c003204502c40c0c091a0310036455a61204ca5540e481031044464081801c843c0005002c4da842540c01300d0613460701c40c0f07000c1094100f2210040d1659200c94801d07402d030b090300010410900111041810f01c1070b004d40b00c030705090a1840019051030351051520700c05040c0c05030381c3c06050904201e03c0c3c00071b09811080755100010b08200c1c41d02d80100c0d005039001801224a40805070a040c0010000301c2c90039501883c0c4a010a00d180c28900f80d11203003198854461085c801080c02030501a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 963890170 1250 963888920 963888941
    0x609010f0509040606180e0c040902030705090d050d08060a0501090902031009020c0f0606150706050711011a13060e01061202040308030708060f04050606090d03030207120e03060a050c19020a06 85
    0x212084c00d1b000445001e01c02aaa078414079204030420100010080d211042e030f02150312018016840f5116a1410340d40c0340900305000d80c0094003040d000d410b101c0000f4840e1551101c60b1500c00c1d480c0c9440e407d1041c040c41c2e80c091240030803c070440422030103089600642e40650004840528036032611b1005051342c0c800107280c52541c0c07022130b104103031400c14894241c02840440d003905019420f554000d005000d440c00182c09242e0f52030001e41001d001e9100540c0c5544080000c00c400301220121808188001c00e1b403a000c0d498400b034030310045041e48142800e070340d4403040c1c003c1c1c580e18055003115081a444010b07400c2680074480040012951406540261465107412001d40b50170400c0c060000340c02c0a40502c01e908040038890700341c907407404a80a4400581c1d2500311943e250601360042d10540b440201030f46403402c200212180d0040320704030070510071805c0d500140c85140b055000c0d28800d0340d080504034010085406199180c0b000d01541280c50300540d000e41090f0380340e04044410002c1c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 963891420 1250 963890170 963890177
    0xd1a03251701060e010f030f11010216030818010302032509080609062215021305090406090b160f0806130e01150b04030b0609060607020603240f0609010f0509040606 73
    0x20b013031042118002e561400b6241596030360220a1454807442e00186500c60080d0180a948140919a9100b405004011507041c00f400740c0581d1f4916005061782c0c030007504460303298504ca8090020750302c81d000b07e074040d01415005040902d000048aa4080ea40c135000c3d8082c804580c038002085002845024400c45510028008919080748101d20040c2c1300c00c10070304410305207105040011a03080e40003282c00160f540050f2a107060a24114036801903400c441c0d841400f2804100401c0250303003161000502c11024001c5c80c0c0c9035a003c0e0340980403c00e002ea0042201060b400c4606440342048542c0324600409548802c8661b0101008403840303141b03c4641651600c4808001240401e9180f000341b03d5a0409451319141d03458281c400c68010704003500c1420340c440481c0b0703156248000d54100310340040403a5500d0422100b010803040745010b041c4941c1031000c0c919440707464411800e5844020241c07840345030110702d000454944103089408800e22009000082a44c2c482e8401c0c200a402e0a45 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 963892670 1250 963891420 963891431
    0x1e0c0506150901060507050a0b0603120d050a0f021e0a0c080a030509070f0b22240e0303041d0a0905190c150c03320d1a03251701 57
    0x24140540b60324143c000c41c042c04002c0005000262001540010494110b42c82d58459103d4000007800c103000b9800c207124001010032082c07900035540d4070160160195901c04c02041500700b0b0041c0c01d078003c100c40801100070360412120003824400040c030b01280f592a040c581022946e903140d43c81d801c6440c1c004000b80c0c0d0f54040103600c000403c01c3e10042c0a06200703130440c90b460884052424400d214400303008840c8002d449045045828400000d00f504100c01c1d4049540142003401d0414140800c500003074680e91031400601f408000c940c2501d4294001074404810041c0d850384e11540034004130a1a03a580c96014045902070201142004e40705480000300d80d20f03810440b511030095009000796207022208807040b0f6030170504005c045585810b146000e0740c1811009040e542c0440040304582100111012180b0003010050200701c4410318100286241600c1115000941107009038141e407104110b40031880c401070005549500410310452b1664962150521a80302c01c14802c0543e034440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 963893920 1250 963892670 963892711
    0x80903270f0d020f041503080d020a08071110050705190f0e04061511030708281d151b010e0c010809030702040207113a031e0c0506 58
    0x5200d440d54841107846100b40b2195070000b800042c2e82404451281d540c0b1101c05a4050b00c50440000035600b003460030391648205040d600107503000c02e031540001404000007801d41790190944045099882c0000c09a041c6440340490040c1806080e2805003d400d21082d0841e1500005082804429507a0f000786488040405001000b846000a2280b4101101884a0b22035817944401c8803004c0d11b40301c540c5421200b43c1500314031490b48042d07c0e8000006501400c0840b08881c080f810f00c141c01105407484c402042200d0041a60b1518640c00040d11202c4440b4600203150b94419040315220a2800205202807140304402c200242001e9444404070050f286040c820460115028203000d40245400507282d03441c0d11030250001d12032640495054180846501c10402d450000f9100003164030280c0781041040301c100403040400211021481001c0c1004a100d416140d4140c98101007074591034407040e680401e0103070301820442c8140050300881c50401c0700718001c001342041011a00303940c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 963895170 1250 963893920 963893929
    0x311041e270528080a03060302030c0a35030a0e131b05030a0209121005090c0d0f080f0412050601050402040605090d1b0b18030d0c0308090327 63
    0x80c6840d80229000d6800140c011540103c0c40e903400442e1019828540c45925680b020300c03c1100303402a051003004a580450310390994424400c1c0c0b4002c504440c01f13090320b401080003180303075405601020f100141b05640c25401c00504c03010040d840c010100300b42c1d25590034051558021001c9400001c900155010b0a810180d00a41d480d00054009002c00002c0149000c02c6140d80c0c6c00d0442004000400128000c00c20b40c1074481e10a4002c082c24001d40d8801c4900e075440d91902c5020712030602d0314000c1000381c03100090400e80400081e04520210f46103407035500d0380b0301a2000c1a07841d104104810078100d0f08602c0208040d1001600e440164142410716520301a4160052806984104401d1240540203001d454114901311003c2c0300d83c88952410030b1074540d010074240d517500c11014010031100308000c060420003501031801060f020342034040680d50488001000042034102e11601c010034480c49806602c001e480003244d2600308008122500300000f2140c0c01024080391103055500c2c0351 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 963896420 1250 963895170 963895211
    0xc0e090a0204080a020108070507060c2006090c010507030c051e0f0f030304060b0d02030604060b0123040509180307030203040611010515060d06093308070311041e 72
    0x300410114106400c242000c0d648680246001c0d043c02100c0d0009800e191281e0200c0d075210307500050a001c0b210004002400c41c0c43c0240d10030020a056100a60046c81c001801c2480344800000900c07042503c20010b66643d0720101c0180c040101c980b40d03c0b400706004000e841a403404042040b0400d50b0030084490518080040100d420780041009006081c0000b00340c0390800c1c0c01000c00118509204005002e41031601c800139054040c001c2080188509680040d8182e0401e032142050090700c504a00c2001c0c010581e003004600080c003050007903082c02c42c1d465510155000e000d01b00c124403048034501d0b45d00080000c07030059100007402e0051070360207054090504031100090011303090158540f81c1c80c00b180300d10300c0e014401c00f181e513840001c0a500320400808803440d003048001d151410704464406906070689850085500f0004c042e000440d9502c00c0b60000005084445e00316540e00d104d211040c2010f541c815190000c41c040007400003110032103103104090009404400f81b0103841e0300d05 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 963897670 1250 963896420 963896431
    0xa080705010917101a040903020105070809070612090501061e03020406060302040b07060b0f220c082206140c030a0f02040b0711060d0e0708060a18060e0f010c0e09 72
    0x2641041601c20a000150713403900d074044100c011410980007150312101c0d1a03414502580320707080c0705400c0700349038047d40440d0240d4011741d40c064913503840d000a240d580740d442c400c0e90009100c3c030105010407440380d40300703420643c030a40c00803800c0da56a201500a0640f0401c2c445101360040c1e0080046107403a00c240030090400d070800358201482c05e00e02c80102e00500301c000d09000d84a02e00740c0c0302951000151030101d00d0003468504d0074803002d80ca070320350001e60000070320100d071500d048072244a005221040c40707180140300d13030300d4071100103a40c900c4d0050b44440300321507231502c40000740d102c04a04001e81e88074403403250702c0c1910303440d20601c1481076640813004c2043c9144100401e12058940c1d60803202915084140d8450303001002e00801c0e80ca104c3e981030114414646115802c10607000b2070440103e418030403c40d034007619050b001c4000c46940d15420310003547c4614140000031283c1d0401000c01e2010b0040e01c0c409103801d0011400e40742e50004a000144035031b0150fa00318981500c5094210 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 963898920 1250 963897670 963897689
    0x40807090b040501030b0c0c0f070b07061a060304021c0602030403030207030215040b0703200409060f06030b06030a09080c0d0e0a0b19110a0804030b01050a140d0602090f0a0807050109 81
    0x652664807582d10745540a481d0391f406140020304015004410820964122031b80710455014a03034604094041d03401500b42224840d007030000300400300c07034201c4605042c8180140300b00c0c6103456542c01c0001d0701c0041d82d54165048008209240464040c0c40a1803003a03000b501c2c0941d5927903c034a4002c2c248644901c3c03010380007100c10103120101359039522140e0f01a09a0800040d0a0f4028000c2c201140b4404041d40b034008000078080703040e102c1030308408222808648101c42c110f0321840c0c103405031540f4901160300b00d282800003540c10907a07070308424030241c0124101403506c8950001c03d800d00c51844d0755400031904d907500e141c0d028100b24141000802900c4062424040c5445051005500142505080000b00e00454034803071014000d001801758440c44041e0740c2d5651b440e00c3d50144009100d001e00c1032010403c0015224062850010070b000d0042c5550404461a51484025049103e0280d04a80c01000b41050b5456040d07006028020311401001810f18140c0018000d17100c540046008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 963900170 1250 963898920 963898931
    0xb0609070206070509060d09050a052b0c0312150816050108062b121403071b0816061b020307050d032307170603010b0d0f020a0803040807090b04 64
    0x21a4040742e403503084110b91038855510007200e400513801d4090700344082402ca140c0369403201000000581c1c43d0040740300700181e503e40c0000004040b030001d01d40c0c49005240c0710315148070f01614860301c4000400c920034101074481d041106207280844035010381d034803d444c0c10b5031803e1090800070096500c0c02065240001d44450421000810704400500094041d00688000d580980001c0340d211922107a540b032006807000171400c120901c3c1100101100105030321a41c40030600891100712071048009403035a0003441078625044444403282481a40d00c01024082c03070b52000801800d030015140118004900003101501000d1641d8000c40403105541c800c000e95000148046010b40d810600d03414005600c24281907401507400140b0300000380e40414108103c4025044000040308142091048110785d444400713043c04c0300c04406500d0b501204141d42d08002505030403490300d146101074100700040d540d41d0303456465071f000350300401307155000b01c2c07070074010450300740b050704199101103070705108 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 963901420 1250 963900170 963900181
    0x31d070f05060325020a140a170705010b031b01020c040b01081306060b0706140907032a0f0b120f040f0303180b0a05010812070804140d0803010b070b0609 68
    0x50003499407241600400c1c0c0480003540203c607007840516009031441492600c0884000029111441004c04448002003840e807814400e4001921290003940043c00d150081c0015110f2005908a117000f16440c3d9256051100c090f14140800c040b0b840700c40c0045201200d0040c0068200441928841e000e40c2c07520b54281466a407102230140c0000015510388a042c0c1142000303c083c00070768114903041070340040c00c001080700c00d9020003007064003c100e0345201c4c3c494045641d110000742c48007520494852450201242c41c01c580c00851581200b11010002d550b14113441c1303021a541d001c1c3d16000808180004a800c0301600b140e8440b00300101c090303580c0b500d07580310060680012400390805503a0981500d042d014104540d00140d001001c44030706107031100e030240160000f4029001980151230225030b08050380800d80e040700e9800f14106040c07600b05484c0c400824080003100e40e102c840c8064074004605d81c1c400841c041e06500390b0040ea02c00050a00b02c4602d031014210302c2c040da501108010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 963902670 1250 963901420 963901439
    0xe180c030c013204050901060e0d030f0e030f0102181207060c0213240504111e040f030809011805030a06110408030d0b0f18040b09031306031d07 64
    0x201c44039400d0811910350f9881a11603660360354035880a02503948000310b98503207424900c02404c100d440445102401360388a101c101c9080c00c0c000c80064000260f1011070b0300180c020302c02c4a40da19036620701204148207442c0001d207010001c61800426950018000303d4030521240010f0700c003c01070707810006000c0c44500255545001380303c0c01e820000c01742c1b4a9011581c3e490319000015651003014400800310201480e03000341e4882015a131f034880b0f4400010241098000d054070410300180e25414200f0341016400301a1001e06400084102040049030092100c40ca2501840c01410242d444d81c28000025022095920410030390f008200703010132855400190114105902000200c1c0300f041d40f10402c01d060065070000b21203808003150000440d0645c0c2d02000040404542c0e03507050321110014414000300d403004255a02400c1000580801c0585c1000da4001100d07200322403800c2c11002c0c19282039850b581200340043e80301d44a1500c407400400804420a070f0040c09850707168940f01c48030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 963903920 1250 963902670 963902683
    0xe01050406081009240e01060c080d02040b030f010305061509220507060521040f020d03111009211b02011b08040314030307080604020c160e180c03 65
    0x7000300902200000c03007220a0b125044010440c070b0b60148004d00c0c0004c0140341c01462680304a2900c0001000011780a001741c5002c0d04960007519061801b21044e1245a6664041819104095002c00000500c240ca0340011403041c4a0103a045000c2d5056140c018104030015005c0d45006c103001d003101501d0b903a000302280d01b00007803101070b4a0340221801c60003140644280302810300e0040100c00240c10750010018104548184912084030512264086404038292400303082c081c40d13031702890014200403424482a900906007208080c0c041c100301450a0f0b500c265a2009079251009102041a002800d0742c503c9807210701c2c3d034400b4407000030040c486503040b5038a0100100d032440c0302003564016100c1c407622542d006640001200507080c0203405510031701c400c0b9000c20140d10100440c5c800402074074020041c50356225110f46400040001a40052a01d40c0690003001080d81c900070103241a00d005014140201005150140c0101c00307402103008100000d4101d03100441c0e0580c0d0200d000b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 963905170 1250 963903920 963903929
    0x10603140a0c03140106120e012310120f0303050105060307021b0d02060c1e030708120622050610090303021203040c03140a120e09060d0203011b030504120e010504 72
    0x30b420540c18204801902d010002d078000078102500200d0344a520030301d5105540e2481c0f40030b12940000c1515182220305000c100d0400e0145da0006908070101800c1090b008010b0102c0c2c410115200d8040303203000701e8100012a101d10001e07078244105501406410300400b012903210741917203080c90005e510b49800c845102410490242881e0180da00c0d00f40c4655100d4002c2c5c00242c85111101d0160766071a40c5115802203051070300b240d0344c0510b00010458003070036172090503641480034164440e001c1c5000900b1066007c0201c03400b008804000214141a22000e01c82c045010b04040040c84000c7c1f8900004200f080148035003800400e40003c1e203070700b20501d0314407081d5803a034950900c03c480c0d403c0790708010030446403d14101000740001401860307503400f940314201d551881440030b8850000d00c140e001c1d0440d0040300052640c0c5404240300240c01d001074000b0418980c1d940c04003607a0421400b0398004607503503105000a00500202e113108508540c108101607a54403400a42140914800c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 963906420 1250 963905170 963905191
    0x609040c020f0115050405012903060102070909050606090c041a070203121218010615030b0f060a03060609050d020a0e0408090907120c0306050105030c070519030c050601060314 78
    0xa415420340c82002a90b408240141c000c115241c0402010340100d0001d02ca102c0c4a9410900080340c07030714502d00c4410f00141410200350521800e01032210944d00002e090324198020a4400945002c4600414145600c45c001504451405004004021002800c1030061200c1400140004000d441c0380750503010180c0000740d00d403080762001a00c5e005107107000c034240d44808a11101c0241c4982416809907080d0740001445140d1840c1150881d050351003080001a182402d660101c1e000c1c0d0310200160078040e1030307003415000d1500415215130000e83c1c00000030340d807008104540b580c0040c144024220484c1c04a45103c0d8680004074803031414050008822407040210341004a40c00c121500c0103400b50403010340d4a05080041c00880000071010087d50601c0356150107288288107032420340742c0585440741140c0724000d00d000150440303130781280c8034480c14080c1c114103040c00407070300c2a16205c0d82d20804030b544545802820408180e000105140c14500711200303641042c40c04030742c000041c01c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 963907670 1250 963906420 963906431
    0x2070506070219240c050606100203070c0e3301030c110607030605040b010302070201080c1b0105010e0a1125060623010905030a0305030c07030e0a09020c1b060904 72
    0x1a41c80b1a03024840300803901003c070001007010703029500d1150031a00240814039040400020745242c0c146010051107500400c002408078502942c902000f000c2c54030403641004a07a41d40c807040700545811492134030f107001c02040004000609181c4941003880d510594001d517401c004040c86250031007250505803074040354200d8038403505c1c4102c001d43c42d400c110303512801e1040c4060020141c9006440c05a400c000004841d035000b070084400786a41a540c1190654a00325203c0303c68005002005c03540303007180f10700240150b0074010103000c1d140401c0001c00604003083c10008840c000f0012045043c1c040c0001803400c441c0040c0260050703000d4080030780300002d0f031400800030189500300c0c00700140001d107000e000641c640000c03404100c003a01e0740c0b0911515201090fa0b00c401602c1d0040018108100240184080340080d0074241e21904054021002400003d044100e1542206407500e0740031440204040301044403080c03420981c400000d440c00c658000c10f0062180340c024034007994440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 963908920 1250 963907670 963907673
    0x7080f2a030c19030204050a11070f1e0c080f0f100203090705090103050d0314011824080d230a03020c0c0a26070806130c03051e011a010207050607 65
    0x30b00040c5035103240104200411880e50424000b00f0002c0c0c0000d80c011403030400015000350f007600c611030b401100c03218214180b05240c0e47c0d403d100c1003e19070840750000c040c040003800510701d40302070100368441c0c040424900c3c01c00c035404e45850b865011440c07070303540700440c140038810020403c1c49a80707200741c90160703590361044981ca150a01d150b000c5030300710726850000003e100000c5807405c3d1801484d0b4051100c2d0403402c11003100d400e020b02411014100c0c844190103103c1080d441808080250b2544001b000410741c182c1c64100786980c070564103a000303090f00142c1a07500c045003900224603441181001e0390401108441c034001c40100b101416030004a00c00144020002d11200d001e004041041c1607440d1003841081502c40e2404c18120503c104403006041ca0110301d0106903280040107140d03660f00c185601d40d4141c0c10280c1520043d01c1e454004c4040b51051101d070405800c2d6500040191182000103801c444264a4500c00032121040810b20307603901085a90450700308480441d1100900e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 963910170 1250 963908920 963908923
    0x1d0c0d0305090d0f121d150306061e04030b010e07020105070807050903150a1a010c050c2202040803130e070c020907020f0a050703020a080a0807150e0f07080f2a03 72
    0x900d00042c041c96072454000b02c2242e8000410b29510984680301c0950701c45138411f0011084000b010885400414400a1028242034014147c61110b1502528406014140302403040e40203030400c0ea003c0450000612149486c0b00506800100c588001c1100e8a000c030401451100d01031304a40c100400052070303025560f010005440c1c001d01604420020b8100408008010f00d026201e19403266015200d10701c496004040780005030ba0890003034800c0c1400141003040801e0100e030a56031920106d1012926181c041c4054005002c05500445d5905618600c00e08820340c558031600510050b10300b005030cc02c0c1e00c1076080d02e28590580701c2c1c01d03560721146410f034109107441f40340c00e103244505512507040c040c0028001080740d00999444450740d88407459180c03903d0030910058102c0504200c004001000005510344070300404000113070b10780703124500360705103180d5007440e08407039203c2c07030044c0203c89040c0844150081c1b003100501c6028100d50300400c00c4e5400c5c480550316a0b2441d003100202d03403030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 963911420 1250 963910170 963910193
    0x1c02030c07051b0f030114010b090303040e150a0f120b0907090c02061f05010203220b120a0b06090312090d14100c14180a091d0c0d0305090d 62
    0x501c00c00b5243c405540403180010620842c04070f80c400d00302d5680b00c2c8111308061043c5901c1d42c2c500300664040303a007400711054440c1c2c010020b00307400d84001c02000401441070000030f4019020b414810302850b803c0d0782003202c0742d05580c001030b0703072410140300802c48070a1405007041460b51024070035860ba0f840c519800d00345400c56220f048160705100350b00d58001c6d40441d4031486400d0300c0c050888125045442a50380603407600429000d40d0081000c443d1080942540303646c24840d2896048985403941d20303105103500300d2401056019046c600b801400701c0715010b1b030a131401080c0c403080d0406105000013a91060014840f100d40c03180012030300301949400782a808074036003081190542c031560b00303507981d52240d087c1c445441c600d00c1d2549100000784181d0114150b200740b000018200082000100c4036200d490f81c4036640411b604000150a00279030080c201904c4104411749590094a1113803800c1c040c006a080b071082d40801e55031000650007a0035544000015244101e401411b407500038034900d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 963912670 1250 963911420 963911423
    0x2070b18180c04051f0c1b150804051e120d020403050601060503091606052a0601080d0e031501030605041a0c0a1716050d0609140412051c02030c07 65
    0x30740c42401c000c100c0702da0b00024012a074099070461040204064559519420500050300203042c62203200c1c0440c3d9040315a00c0003041141c40c01c041195604855884035a0b40058100403d42c3d441c01c00041c00810300940c5400481d02c0791004440040d500070f80d48802501016602c180400b24884648141c2a4152005958424101c45195031529000b8049400807030305005030b4403a2028940c1401c011031105012513031076031100f50400d00e1003100320540e40100c0000860014001010000c000800c001940c000c1a001018261000004600501c800402c0d28000d00951014140c04051300740c0f80d2a0310b0460307400510000d01501c443c80d0150090030f0a040009000d8040341c20311041707241a00041c0114511900c41c0c06103403c1c016120300d800707030003180c04903408682518141c480328069402000310020106002500c0e80d1105204d1088aa40314484d0000ba02d0300360411041000880e550f030201d43d01c50414600301864003140e01d0403803120715a082c02d03058010011032070a00c41c1905071602e29 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 963913920 1250 963912670 963912709
    0xe09070e040f150b0a0903020405040f051b1005040e06100e06030408040f050a080312071404030506010f05030109200303070606080a0c051c020906060d050c030108010b0102070b18 79
    0xa002c00c0a40041c00f0f01e41d2000f1100c0101400000c0c0b500c81e00d02c22101c04110742d88859014a00c0d6030204001020b00034000e543c8001c0c215180c10014505000003a1038511010404210505210a00040b841d03561029014494100000d100b0b4000c042c0c4203651152040701ca90b400880200300031034180000080c020740049007c0184410440f2600207002a9402d14880c401c807140d0b5601001903a0a081c8100542c40e0800c002c1c0c007900050040c40c190b071100c024100100312182070303207810005a206900075105900703c14014007601e842819110300900048009001e184226140d03400208000003001c906800b003200342d4507098405006803814250081e1080042990303814649460794040d40c411103900741096008119840e108135030300e250310382820441c085d491030b903401d00150301b802a0410368042424090207c144c10320740983c6105079103820450303450b13500d007107082d41c25150051125415504181d0061101c648400c003500e1043e81130030080042400400c01042d550b00204100c200034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 963915170 1250 963913920 963913931
    0x328260a020105092e1b320301091d0f0a061415061c0603150506220b0a080d020c0a080a0206070b0c0705010e0c13020909010909030530160e09070e04 66
    0x2030300708040803001051081c0036007e0901840e00689102d00011504003824000e00060240724070315840b03101000c0c12030769118030713151054011600d0440c0c021070800031984035020800c10007005000701c81456048091110705828607200d189a991003058096000d6200824031083c00c001042c405100c140380725008010030768403814000e10195070007001004450030f00f070200d292402c0c040d00d0b000d04040000920751b4a014030791f00340b5003d007541075145540406030140101c0d090009100122407911107800401c107248070b0800313003e410185503105100d0340e009004013a0258451004072010941d100400082c01c0d0b0315000d0b1100c40d80a4076601824540c40c0148652041c030001401c50355003c402c0310301d0401e54034008580e1059200e4061040d030404039002c01003004d040d00c3d403c082c804600c241066400c04003190184800030b0061341210102d07000444102c10714054950005400009004070366030f425042c550044d00c4400100f007028001d6409a000030071482c030450300c0c80340c001c5004000b80907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 963916420 1250 963915170 963915221
    0xb032703120c071e0611090a090c0e03120c120f0a050304060608061008101a0f01021f06030b070509030c100504080f1501050328260a020105092e 64
    0x41200c1321000c4034540e1606042040706001d501c00d0b9100210018140c8140c1030400b031202d005440d01e03074003820a2000d5031a92801b9664140703d40410180c00c41001d58035582030040c080e280407510480940f00110400400340a41c008001310390007100d5506196960351103d1400f04000c0840781e1100316507009880500c40200094006c00080710703a11030840d0000640c88030f94100b2210000d402c02081c8101000f4413a8904202541e040c0b484414010b850605041031260311034501c40e85664600295105404d00800000b4600c042c1c008080d4900700c1c1c103181e60980400d60b070748100b2607114803588003111502d09842c4036800b250060095007098403000c4000440e03da075100c820242c1403c8004101001091500700025000218540888094029035540c488142d0019264006441d00540030f04070250100011451b0000319581c070b080980d070707452800c50007401c41d5405802c114251700841c0d21852140440c1506004a01150000a003507625a0741150000c0010812108520701c640d03101e00f1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 963917670 1250 963916420 963916463
    0x1110706050711062a12030915160f111204030f031e0e04090c05060a0e1c120f0905180601021504080f0d0b09130308070801080d1b0506010b032703120c07 68
    0x4035420302c62724000b82c45880311021a04054003000c1c2d5800094548a18020910b01c83c0d2641c00440103444241c451070030005034281c0103a031054005072020b01e403039410181015841031030350b09180340300d80c0480003800c040c0318021301403002c040c503e038815616400490280090149c41200500e00104060342c0e40500040180c0701842007c0307482d02c03502200c18501e031640b4004048004e4640d01c2642c040104003110020340700418a0070400d0204400c2110100c0c003074450215046030120b480e450300d0360502d050400240340070105001d044101c2580000d2000203503206080d141112004208a910ba19060203034a0042c123440820741e501c14628001d200ca04c00d14041c0160300c440c0280e407102044d5503828410b99010000b0310031400d25034805404c02041e11b1213005402c64211302140b4441040303903603071121803900c402030f040038102070400828812088603811440d03052034040c40d160202c403404e01c2c0ca0b41d500d034054442d04155a800f1440001e40c04200101211a400c0e48030000d01c484205818888 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 963918920 1250 963917670 963917683
    0x90c07021305011712070b0a09031110051006020d30050118200919050915040c090605040e1807080f10050103020904020f01110706050711062a120309 66
    0x415030040307010b4400f1011840e012105415000700503887c454482c942c000000300840c103003d60030000030480070700c0032030018040c0240c41a85604c020840e0b040402d070b105d0031031206a10035003d661203040385040f040e40000c0c0c1808200d109c1c4410f03042c89a9100c21032900040c40842d14130b0030354900000440d904c0d128100c1c606000b56240d030b04002a40a628071040402c2518503070103122402070001140e00c3c0785c103082e05550010030f280040b00340365944020850709002560088100100b0401211803402c00c0d02c21440880030314941403e8040ca0a803019240340704601604601e421594001183c01c03a403c0d52518141a42e07004445d03072942c1d107002103900d0b0000e910b50300003280213803041e01c100f403045802860b0580e07130000c04003501c81d110340e0b080000840706440607a05004c0003514115401c902400884024105038884568401c0076250400c1d8203008008454030944082c031100c4448603491803190300002c01c2c88003e141e083d1400180c4c0c6d2130100d141e4001d9103068800001c014000c41c0c0400d01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 963920170 1250 963918920 963918959
    0xf030b031e0c010206071707030b040504201c080d061502070e010e010515030901150609080f0f032209020a0f17040201020c0d080d110306030f0c090c0702130501 71
    0xb80c0b06200184401242caa501c180e5030500002c80a4180304840000c1400840d00594581800211445800089401d5501c100e90030781c0c002f034101610441d61010303101500f044046c02c45446101903100c101044d9855640c0b14041c11002c00415044071805580d4414409041131541c40588240c0341c40f4025514a0309009580b00b0812440000030907494040b070281c1622801481604078142c080c03131040382c540004160607144d6494156150000311540740b00c001a240d299038031000d4604000c1c13500d00e000d44d107407140143c0e50300070600400d40000101c207480403120304441d07040406c0303403c0c01c0303c1043c2c60042d00420034551000581c4000c0c80e8000480c11640d400985414084000410703849000350421500a0302507007040c0725440305440c007011010500c0d8031401495041000600d00c01080714001c0202038800d00000090011900d000c10002c2102201c000081c080d4905400c041443c0c00c902501e00380d201080490104110340c3c03048101d1801011200c400c000359a5a001e1116011489244 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 963921420 1250 963920170 963920173
    0xa030b0f06040909120513090c02010212010801050a060e150d0218010602010b04050105010f0816030f09060c030e1c0c03110d0801150203090d1b080604200405040201020a030f030b031e 81
    0x800200b00342c0198180c1f03280001e04109095000d2030454440301420f80e1039000e80840d5401c03c103181d2a20107a00000d40689415000011545840e902039401c440d031075001400c4030a4580300b00301c0703008002d0406000c00002a190001001c08510100b40340300114130401407080c029a0020802ca81d0551242c0d0003484111003c1c81540d07a01c0e0300540d51200392203140f000007414100007030100c0d0000b4081c0140c018440c0b800050a00b40003000794212101030000702c0319542c543d04c600503456414012400f0020001c8041c152130352100c0b905803414810750b200380080c42502c00c07001051500903030706459400c10903800e64841070442400101098000d0003140c8203034400b0b1061920162002094035454280038195103005140c0303403614013081404c0a00c407101a60040000300e511182441154082c80c0319041c0c01180a980250343c00c0c03c0342c013207428107016070314000411000d81e0380041d8102c110349d0181050b0400c0025002c0850141040750703001c58141c403442c1c1c04508140b4001c0340710b511070380b012030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 963922670 1250 963921420 963921443
    0xd020c0d0f020a2d0615090b060304061e06080105161d09060604050315180309010c0b100f0f032006040b0c0a05120c0d030902060a030b0f06040909 65
    0x90940d41419038001e1040140d12511081000905401108642c40450b8180d4200d020b0076040b418500d503c1e0f110116100b540f80c454044035128108451405043c1042c01444405125404584180001070001c3c10990311500001c0518241050042d2640c03200c4005000c641d8840807164060481680d1041c00d040d03e0100ca8200300b4802d405402c00440000c0840c0025924a01001640a8090540d035800f800c1040700040940d0704104c808240c0101c083c01000f1450010141c18901000d040030340401e400400202c42b440c2c3c3e001042c02d4102e6806007410205450f01d04455150b100c551300729091150b0419004030f4901c0500e0310744011248122031011a58046820701082d281c25000e5090308840c0900c400c0c007092020030302034510f14800d001220700c440226207465107130a100740707028a81c81384002422a00c1c410280b07d5100704514605050040e81c07400d50104007103124904910007016900e8044c0d1b1010350780c2081c500444000105406d840783d0f01c81583c000108030740315007102c0c1c02e070303400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 963923920 1250 963922670 963922693
    0x111e090c0a0e01031e0902181807170c0114120f010512010b031b13020a09090f02130603050a020c0a15050112051213210c0918060e01110d020c 63
    0x1e003e400717003040c1c510400b00c0d19028030504072005003040a1040740e011469400b1441d401004c241d00a104008407258249032010750280c150814111350040840b00c02d07e00201141c00000041210100b4402e2910301031101a110f100202c0d401028109600e8a42d00c1050007180320040294070f050301c1d07041341c0c02c18040881d110804d0884d00104111a0160044071321103051082180c4072100e4140c0150503440030030701c5c40d03000c28126403018030500042501c40318144075144552040c00d215000320081103141000700c2102074540d1501d8420700081684603800a00001000d40681c0c1040191500301c4210b00118a002419060000d02c007030401c81c9004000115441200c40001aa82e00320b4090303e040001c065039140b0b2580041e00c1c00229000d0348400080d0b40e03498000352241c5840030540c0d50740d290018904002c5048840e40400b0002c0c3c01c01342c20702101401c6000c081c21322507200f08000b81c450b040e121550301602c025440307500c4245001c1688468203189800821072403012a06070f40c07a80085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 963925170 1250 963923920 963923927
    0x201020705010c0203071202011e090e0a0c080609071412060405090106061e091a030a140601120b0d021c060c020d0f120908041d0105090103111e090c0a0e01 69
    0x1816019606610144042120000d4002240000c030f006141c6001170f2b8040800d032444804610248100241c1804801c128074910f80e040c55800051640d030901c01c850740500000c0c244040a0003a074482c50740500032500840c007428810391f0039441c0c40f18490701e615040d000c600d40c1800868010340200d0400d80000c0244206200799401d844050312201d490254020303040402c80415546c02003400580040416850601304240c450b8000c0c103209141e8a04d000c1c000c02c01990540d83e100c5851044201c213014460fa000764141015007241d1400140c80e0580c500011003004030410041d4106804041c0c00c0100108143c200ca4541d0044800344401c41690b04100c0e650b0005107007500000b080541203c10441c800d05c080303500b00d02e05a00108003998a5150784010750b2150303103c400610107000d00c0a01001114210b035004200c00c4400140640c034503242c044040c5e5500301e240340304106d900700c071030704c00d0311040c4040304411300290071803101c0e203040307021406198002c000300c0012821100c082015581b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 963926420 1250 963925170 963925187
    0xc080c0408030f0304060e0604060606021c0801060c080d0e0f0f070f03032d08220503040506071509030c03030f022a2404020a05061e03070c080a0c020102070501 71
    0x10078800440c03030881640e14442031600050710460f0459140d49010205c05810440c440c0558064040000c80c24031f040400303441c0c41100406910b00d2001006101e220542000600d03045034520300b411445070b405460884120b02c200c0a00c5400b031481e1a4102d8503941000516400d110b24910450341c0d134468442c86160f503035440d4800d943c11030b0120142840001d104240b1550803256201800c0c80710800622807441c0300340d0610341036001602000810207a600710802c500807125060400c10781d840d1242d00c40a07164403903030107400d000302000038030307a410041c20312080141110706800401041e04185001003603412004c00a41c0005d060490a140f6803a0501c201d402501c142c2e20521101380d841051702901c2c21450344030342c0302760046118108080e5444082c020b18007180f04184e031140e10340351041125a48103504801d0090000b4001043c0d0071300d024504140f0ba009080c0c1a644079580d807201200c11107581c02001b804802d01161085600f80c120000c4400540300f602602d080d04c1d2240c004450b03825 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 963927670 1250 963926420 963926429
    0x312011d0f07030903030f140609130506012105070f0e07110a12020f0d030e0d050c060403110a02310e030f1809100f090b09010e280c080c04 62
    0x203407408085480741e030003980948034035072103420701003030b01c0b19900c2c1080b04440c0400412411480304004200180c42c2802e07000b40d203e98494903413070b111885d13526100d5903181d0500409402c18075603040300c0c0180c00308145101c420382d400301c12500030315100d0a84910004162051403640000c00c800b00755003d008006c0c568442402e07000400c840200b90b181e00e1520404c0803402d00c01e5004141140388101418061911000441c0d07c0104001c8411001549800b45290440c3c041080078001185c0407240460324036002a09031a280c1d50846030390840c10f00f00908250001e510404c0481c2001703400d40203560300040b03100128010054181078140d090191881345a5201c2c1581041103251720f030b1440e00780608110300c12007003d100250080d50210340041819100344d05440607001c01080700d501c02c41c0c018070140a41d10410300110aa8002060300c03900c1c107014044405240e40c00080c030640100e040d075000100910403803003640c0c000844003401001281103450008248070005450100191b044034200d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 963928920 1250 963927670 963927691
    0xf03140d0c02010807090902032701050103030c03200a15050a0c050d0e010b120f1908090f011b120201060f050607060213080102070302010510170606120f0312011d 72
    0x241881c1d0044444c010010542e20605c06c441c04049000121480030318840c1c1c00310103130341c030885019001c1c3c040210114004074089030705002c010b1000940c0100d040401c5030b407606003110a840c0035400701110100002208030603202c0c4800c80414801a0440303200c0c50708424000300310688400c1410003d0740d404401041c0400d00030080b84203c844164421281003c1482c0002040c00d80b440002d658650b80c07900100c43c0303a008030384d017070f6440d01c0901c1041007421821150142080362030352818018092200900e00c02c0c40720000462099004455443e000046041d640901d001d0514140e4500e0116801610040d860301c04042440d14440400f0800c0c0c0d0002040319060544654482002c1d41c4903034080000f00c2c82401c1c0c006403416003400640b40043c4a50002b2a01d032410a041c0d0031000c000f5804610107211910110100d10030204805070007070300547d503d41c40c0c9041e09011030300e406680c4c0c441c28014400040e2810f0040c1c1c0500300241616220801d5000c0543e003070490504182081d0b480308203d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 963930170 1250 963928920 963928937
    0x50f0a060b040c0206271903031103070c0602180301180b010f03050c090a0902031002070510090321330519090e0c0a03050f060a02180f18010f03140d 66
    0x106c410b0418003814030500040714018903144034481609000f420b04039102c0d00b5200001c1c1703808054150044007000441044514254900303020020b0095003031060213000b4940c0001e600700210540e1700301000424024000780004104081414104001c108013551052900e10010070f80c69164800c8030102c940100091800c400b00e20704201c400f9101808400f401c2d42d6401b11100161414007100b070828038100c0005803a0404c0b8200b143c18503442e40d08650249140070503850002e0341200d080402c104046400c410a02c00314a170000007041c0c402008004101c011110301d0303a01e941c02c4419030400b42c2200c07103402803039540d2060128080c0e668444d5240700e90f000900348040c070050350289004003501c400b141c11100344000480d09041c203035041540e15420407070750340c0c0c2011000c20001c0c0d00800303258070444c940007000015003402d01069a40a100300b44124800351a551800d400c100301008100c000041941c0d13a080c40d201940041c802100c2c054241522a442c2500102e140b03c514070705038450021 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 963931420 1250 963930170 963930181
    0x2120906122a1b013309020d0606030e030301052d060d0903021c0203031906080d0201090302101104030605060d320303091216050f0a060b040c0206 65
    0x752264000c0c0b0803007a200788000ca4003064949007001c4400002e65090322a50751039034440e44009100d40d0803841c1010fa04145d017018040c200341c00b603244000000000080c010780400e40440800e0b44903485004c40c58004102220320b071040780c0c0440200c4559840c01c1150702002052103442c3e0000740300d1150b1122000f4040d54420030311721508217050005070100001c001e0560009903aa4200a188003102c0340d0702d044071007c15404000100b00001007442034502e84042e1507000b581c03803100401100303c66840d40301c40107100c80c0c23941004c2c024000c40750546180800c0904002c0c001c003000305040e80148140080c2d040032100360321580d10005503080d962441c003811521607101400d80940b40703d401500400056004c034015100b0710012040c0201a1003041107855605e90018083c1c000c07035010703034100b001440340c01000041c07036424614104480b00d40310070710303410307480803064a00201400c41e0091917141e10318480b000c24507155507480342c0b004000030045403081c030007200d401c00482c03405a80034102049 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 963932670 1250 963931420 963931447
    0x515010c02060412030801090e01021903020903120d0c0e01080c070201030b012a061b0905040c0e03070305010e071401050a0804022706040515030a29090303060102120906 75
    0x180c0c0e2070010740500d10306680ca2a0b240032802d10454140c000411050050013050304900411844c0c400ca13030000d50031b00b01c0c48410420417000081026092560005c0d940da00d03a2000d1180f0043c202102d218542c075001c00c0b408040140448048460002e01590141a1650f0041008602656950240500700750f0682c1c019002040c6280040707041c0007400c0381c0c2e03840c7d5030100b060f1131030404518034490f1201c000340c0c0f0708482034030020041d4908061140320810001e65000f1104000c0340e20441d0085583c201c603040076a4145a842c1c4c185400d8050410040140841500030501d0500c402040f80c0000b6940d500561140002c1c0c40b00341d001480030840044072a216140842e00240010072054168a80c44089149441886c95550581c4900010020f00e4986441201e030311080f014065120140403200281d1104241800104403000201102440c4100001042130100107912000640d04050480e55500e0f0011240b0600622034100b5004011944209550b002c0f030002e0440e0b820941c0126924 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 963933920 1250 963932670 963932687
    0xc0f0f08090313170d030216081803010207030908070e07090303031e0e0a0c0b070506040b151c0b1014060a020c03120a091508070c1514070210051501 66
    0x5041500c4140101200c01605040c504020301526683c41c0c0039030b44c20900141844264800070040c58414450050ba480c51035032180e210a1b40080031035136401c2c8408462026011100181c0e8040d88080b03401030415400140001c284c480940480e04100e5940500d0b02e4040c0080307401d6000150030100030000a8000c0d00025103600d404443c580001c1e0140c29194100ca00600d811a6280d010384080300c2800700300c0c0a04006000701c04081484c05e426074542d20f540d210301a00042910701c0a50006400641c80111045c02c0c101c000c0c01c40f01c1180b0300c580491000a4156410f484150406c0082544201a002a041201c00003550090b07054112020440b85070884001c14040d03010718840d0240030303079050004042c51081404000c0d15018011001499004250480140103045109164a85070081d21030b5510840520300454100013518001c00e4000d000707012024024200401d404103801c884a403039200c0c0c603490f0300302c40d035800d4100a12000c0c0c5100780c1b2100d20644400e10044450b51003041203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 963935170 1250 963933920 963933931
    0x121203060315091207030e09040b0a0c050306031519020301140f0904120e010212030f0109200301031509050d2a1109040c0b0c0a0c090b060d0504050f011802040c0f0f08 74
    0x151200411f01c000caa102c100840d002c95003a00902e003040003a680c1840707402c2001f001c6241690540c41d02d400442c1e07480500900c580781000b407483c00a281910344c8411440040c52542041d500ca59482843c42d2615110b1018036108040450602c10f00d403d042c0c0030342d84501e4100520303094a09804c0003d03200410041c0006045004d030464201000c03407124021400b42a01903070304011036150282d64000c0703074192131443c14000400b401a400d0005610b003603a040d43e801241070340c9460b02d00d008580c02454001e00041c441c0c061070716000030b1745411802e055942e1070389908482080d9004a04869420003082000b003001c001c041c004143e500348030040d02e9200b4031509001d5a642d80314003006100740c10944991515a0040000204000744224140d000301a05041805400c54150000720523000e0a541c1c1c0101c241d0303907800a0b0230300a0070444070000948a000030000c02161030080e154040002405a0140e400c000005403c103120350561060729520780d1700c542024040340c3c1d08640800c8017516 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 963936420 1250 963935170 963935177
    0x3040816090b0d2a081501050f030f060118060f0803030a0606050903072108190e0a060f0503040f0b07030f1a090622110301180605011d12120306031509120703 70
    0x3010483c40c1e0300300030319040754242c911006c00b10b40c5070108018521481440050181d0882406800e005c8400a03050741511302413082c0310400c090301c0110303100509041d03010001155411000144c10100032000f5400342e507a1460600c0096181c4e01c2c140c610344030301c00040e40c140d48090001c001d4000d4019510300b21150300032070444402c1c051b8842c604660800d4007180c504e140a40032454109401c114200c1c00b5000646240240c145080b80281040c2d083c0e031185018064000005420000d244030b051000c9070340030581203040c1c100b007a0f000740107100c44121800a00c3ca00040c0c11165000b80c11024169403001300812525903504041c4034500f0651594404403282c3c0000308884c00003103002e80045c00c415011a40e88a40c5081c0c80303820000195900304000300e181c54820300a03640d01201c0403075045c1c040c080048600c00780c14089207031903509147d00c080c1406010644040c00141c01e00450040c0402c1301280c508500130305403d003030703180e065a01103035585c8000480406141c481c0f01904009000c0d08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 963937670 1250 963936420 963936503
    0x60902040e03040807090b0105030711150108010507030b011803020114041503050a050a091214040b12160914042c15090d0905060c03040816090b0d 65
    0x140454103981d024401d00c01a600045003e02400d88108004c3c4002c080d81d48060100c03820600010300b031880090f041400704051036418800200c801c0041100c015025460100d02d9030303684582c40c1c020311080e5174800009040c001072129641c030603000b0800681c50141e040d42901c3c5161700542d00000c0c2c0c469545e44e00d446c00d010006107680d034615404030100d0240c4010174185840c0f15044110b490060080c0141d83c07412004101198503094016519142e5040400c03505000194424150090303030300102c00c282c40000e6451412400005050088a0241e110031080d4403444042c0c0d10964180a0424000c1003050b031b4000302c6c0b5003a000251034600c1c0384408000c844c0d0601c1c0b000b01d41040711590080d10f5000c00720000e40d202c48051403e44c050619006008254503881c030045c5801424812980701d600042500c0c13403400c0040c01150000d1203220304a51024012088481c0c042010f4030600841ca0314101075900182040c11160b0641588000094001d1542c030200c0d4500038803100320542801c0900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 963938920 1250 963937670 963937673
    0x115110709380d0206130f0f08030703021009030c0c08210405030c040504080405031f0c0f1407050c1c17070f020d110d06050711010b03070b070609 65
    0x50120030080c0021200108582482801d00d0b81218818020081c0c140e815800030040300c03228458002c02603070200d0f01e1440c10045030000070044e01806a004a503504400c0001074902c60b504449411100505032036011141c3d103101c281e4690081c4000a030142e08080e43d2080001040d0340140300c8503200382071550656006844000c60440300e0b42041c0900c6e03010303100d052542613402d0034210940039841d220030724241c24030000c240c07074041c0b6030101030085844001240800c1b442070161400b80c03030013a0481d840d80541c020510300704002c0d05d021107940c5141005141c10944510351042c11082d107611100d1942d40500c2d4543e1043d8060b02068421340103581d03441c2c0083da60340350008000900084681301076129810182c02500080c10b0310541a4000c004a10000c1c09140710140b4230781c1c04603010901200035040c40388014050540f82c0e90b02c8008941c140040010560080703000b00041d9440418070348075440c6a03804c0303c1c291000d8990641c4460300400003070741c8240041c00b055101306404a904000e5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 963940170 1250 963938920 963938923
    0x130b0f041712070818030405010302070309120501020406140406020c09091e030406030b01090e180f0105010e22030207030b1f09020c0d050310150302190f0809070e011511 75
    0xc00070000400200c1020f020744990b03c10090b03504425800a1541085000100c3d55a41d204500c241c0707041c140c021a1030310074903010340707083e10052108650209030a04180b5005000354024000e00300460040107c4201c00c50900b01030781c00359840c40d002044844010001c100500c48018116010341c40b0b45910380c1801c1c103034481038003001e00851000f15100d5080c040080c080c2d4074208103c1381000741100c820417205002d8004180c008108a44156000e099880821f040c2450358809880640c00c000000852085401c6213038481d802e011542000d10890365045050926115400380059200c3c1c1418000b250b000e218140c0c1040000388a01070f04004800c2c65205a000d030b42c02480c401d5030115420b583d180d0103000713240d40c00409213016851440c249080302c00c0d0010300e00900702d02482c000400c600d014000e5040381c1900c0002154000c04900f0300d4401800d400c902032080002616080100340d4004002504009a6170035001142480c5e08080b50400085418550342c020082c0403904c3c607000c00310 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 963941420 1250 963940170 963940177
    0x115030507030f2906090c2d0702120a030905060c06150a050315010312030e100905070b0414040605040507021e0c0d0c170604030e06090d080c15130b0f0417 69
    0xb0100351380c100c0c0c6405802c21840d214000c001c0200c4a13020490f16010012400001c88600c1a80805505491000950069501821800a41104d121980c2c00d00c3c1140024680071420302c2aa220f000294403541400494003c01c16900300c1c59102001250799135049210848488201800700d6512560720400a4689403e1305003a5400200b144014428042c079400c4c18a2018041e050511200840c0010950b8510801c1140d60000b42d5608012003009004e0104200030201e040401c0c0d191900c4030302c2c00d11501021022980714030b15001c800100b40c21721303008072440b500f45500074109094948440c4240b00e424201740c0000340c00b503e8424500ba40e941e034540c9185500501000c40a84d046c04458030f1151059216140ca40d4072490070400069880701c07114043c0310040d02c0850703e407480000403880404242c00024240e60001c205118043c10008213071064151501c2d10030581c2e01d41c0f444003800c40880c10f07400703000034800c02c000a6030034108910040e0407500c030f442007007040c40e81403001411640 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 963942670 1250 963941420 963941483
    0x204021803241303170403090902040e16020a05071e030b0c0a0f0e0a0b1c0504120909020915160609050604020901050306091f0f0615020115030507030f 67
    0x400c0c006807000000181908030f82d00407249040001802010b407009010401c0c1d0400102110754604001404c041c450400342009124441d0155111505c40c40901c40c014000c8511480300c0c0041c0c4407a155043c030014100000c0d41c0c2010142078410300b8800c01015244401140c180c0400b0810f00000c000351350300718454812440d49050b180c40d08900c04000f01840d00c00c0c1d0030707182003101c14080d05030a0b50711111190304403010184102d03030346d103a41808800003940b418500c429040c03616003040140121800b48640003003043c7d941d135107003d458801c040e00b2405080078464119070740c602c1341301000000038020104000c0c400052506c059a071340d03a00d425241c20311400c94003600104117200850070041c51140c05451304801a00c0c01381361900da842d69134403501c2c03004429000311005110340420581e020203030801d05520240945500d8403400d081e003003040c542d410300541c0380204280642c685580d8080580f80e000700030300042e501c4e6498550f00061001c50550b1100101c400f80d41081d02544800d01182 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 963943920 1250 963942670 963942703
    0x1803070b0a150b0f030708040c08160302031c090506160f0f15020c0c04090c0b0a02031804020a020706030e03040b031602060105042f120403180b04060c0204021803 72
    0x100c00c162110b5501507540d078400d07010a01c090055504101058050f030758030501e1031070700e0003c2da030340e03810000b04d00420ba03400b00070140100900c5075040d1801207a40000d6134000d1b01200e46200030310030b450041440c000c00c10030001d030341e01d0814007241c6030a2005101c508410040c4840200e62501d8024000540540c100c6103202208008001c0210b040c88681d500481c6610450030700f40e003204080e41f00e2803652102b501c0b030307696044008104a841440759015046600404e41c4804800001956a038849964080500c0242d50801080d16081c002c41d00f0b001400c1d405003148030314051003034019244116091440e40414040841c440d00c2d00301c09144104000c0b8055661b500880074041c0c1000c00c1a0407560040d81481d100815594100c80d83c50500d801500400741c0130403c0b4000c221082c0210715541c0310649140c0b05203c18140c0c012108000744207410b11016a41c0c0e07031003a000d00f1030312880c882e000100b956045c04002516140c0e0251145070711140741034080001c03460000e030400482c8000801034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 963945170 1250 963943920 963943931
    0x50316050c1c0521060a1809060c0e010206093d0f060e0901050c0414370b1c020f0903010c0f0e012a05100513030f0203121803070b0a 59
    0x4d102c0003400510311a00301101104d4141080402d04960040c0110944a4184c0301843d4111400d5486045a1500000100203204006c0d9004202924048029005200d1301c008215000703c040303103986101d50034070704c0304e6128080c82e84410009002c0b10403c01041105d0344400000409030302680169035088400003450a041c43d400b0300b007c00014006030742a0b03140004000d440c95449045a080c0d0703c08603040071610b502580028412117408008180c2400c24050307940505c1804055080b860807100d0341000c0d11034a608000d02580283c0301030700c1d40101078003d0002c82e284564014100f03c1c00c03500840c0c2c685207000004c2400c6d11401d0758500000b480c500c100c0700f21640c0c04001d8103050582441e01d45100c41e84161001541034590014880500101c019602005005c00a000d820717070049200784040d1a011240d24106604190140c2c0071036081444050150b10120403902d1040001030b0150007a22485d459130080d0f00e028510f130038503120800c201030124518100c01d5209401810012a9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 963946420 1250 963945170 963945187
    0x615030f08031e10030312021c05090f030c120a09030f03170114060d02130e040b04020f010f020d1103040b070510061d160302070602030f07030507050316050c1c05 72
    0x43e209290a801c506440314424082000f904d1030b481e0b001c82c2c2d01817411404182c41585160300138030480d0040c41c00c0c80310481018643e052141c00170303442555464140c5a54031a503500035a200c1c0b1603111310400c6500311903010542e4104c0180688030481e81440c0c40800117032260b840441c003000d08502074000c0fa40b0443d405c07885028040000d030140c290b034010603e810354008089005400303181984884039402060068075902122210001019100c0410210b810181421107100d4000c1c0c0b001d0340540c0d20b07803412007074950040783e80c084185c5181e8028014810f1164045850448907c2e15003450300080000040c400c9044024000490264002d080c0301d940d60803002049442c55448903030021082030b101c042a0707030071903643c0c0c1d400b04640039074030071511012508400900c500e810003841c051001c02480030342482a0407944c450541c40e1010030158580d00d8064459000849184c01014004000f000640380314101924100094408581ca0b182d40780c000d4130110254120224009600440c0b040b0b03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 963947670 1250 963946420 963946441
    0x711090a02090907091404020d020c0604080c01050a0b0108060f011101110406090f0f0e1003050706031a0406030519020607211e0905040e030c0703030206061e0603040615030f0803 79
    0x4d03004041070405a01c2070303140c0394017202001c10010589200700c2c0c0c04907500510310f006404803007003203030300e481070341c0d203526103407408201a03001601800e005602c7c0200040c641103043c40390051030b60051315220000e54415040000c0c13a10007181203810031501600500245009018a07003014081d17900d21621036051880c02030081001c1c2e8854901066940001c10510351100009c800307448081d800050303c2e03a100041c00d4804141540300501500c20310900040a95169000300b41c056454001d544a0691110400068444500003e40360750420b100300c8180c490038000d859010762019086e90b08042194842d01d05410005145c1c081908100c18049101544202d07030010490048c1000303110f40e094040d0083c007100c8103000e200d01503071303542d42c09160f14035080041c0c0740c1080b0308404607000c00d030b02d919009480340340c1913498a010306070b4044031881c091403003440010404005080d4078110369654941c1009001c03020080b0a68040050001c00440c4101c803084003141c0c0103070250303581ea083c54066074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 963948920 1250 963947670 963947689
    0x1805093c150402130b0d0e0c06031f17100e0610230d0507030203060916260d120b0402040b030c07060e1603110f090610021c11100b0a09020711090a0209 67
    0x241d030700348c10011000b0419515002900d4201c2042609003a030102111030701000c080c030320b40002c6540c019950b195620440000390919101e16695001d05c0710086d030402059440000352039520006615400170f101e144502ca1369500500c0385109441c5111f402c02000c20030540c164003007a07031076401c080700900a50130100417158005860300d0003032143ea12007000e403030351003061400364910411441400310f18a0704c81001f03800d680b81c460016550140c08010340501040c444285022549091034181c6242d8034092082c1d83c2200d4020750074614559030348141c200c09500025045070025968002000ea500c2c0410001c0078409a03522041a92811400c014064005182c00548680c01248001040d0307180c0d0481180c00203426602082014400c1e9016424103280e56007148044204c0108580256401400c840d8051020821385400b8844d051219081d80c05410186422504011013080041e080d03600402c0c0460041c00c41c10550000e80e0300080006405490107081e6640201e6007484030f2030000c0d80c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 963950170 1250 963948920 963948941
    0x6110f34020a0b030403200f07050603010f0605030901091202060f0f01150e0301110309010c09050406030503091e0307030b04020f030109050705011805093c150402130b0d 75
    0xc50540365a9000403041d81e00c0d030140c0d2542c503c01101040c101409102082c403404622070190f0790b1407a0030190142e1340e19a01d40b5846549c800c1203c00038143c200013049030305035050400740d1181a41080760544203075101404500a945d41c0315101004140300280d0000312402c81d5002c0c04890506002c2c104540c0005030001280f14400801000440070a18118001101c1402c00507094040c004c000b030300401c82c2d41d08456900344000200680c0c64019445824444084d494a0508581361002e010445015001c001c165a00c1081040c1140c9042c101030060100ca07519900004064003020a081407616403040303c03130010348400d10045141540c1c003010f90000a0f8020007449400303071602c654500302c920526040c440c2d103628a0700c2070342036500c030b0401512010740010503600703115a0103110711841000002c014284000000e4544040000d564841c213900d50701c1241948407210744603408658404000c0d03229070308111460000321216004401020030500c2152100c9131409400e0540d4500c50b0f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 963951420 1250 963950170 963950257
    0x6071b0e04031e020312070e1201020d0e06061c0212070306020318010207020d03030b01180806010302010305060d050a1118101502030a08150406030f0b0901062106110f 74
    0x143d61543d0b07600200352079a01d99005142130054440081c1558110200d00d40241c0280b03a9040e1000344880540041800700d031043c1c0300700103500c0484001c54481000365502940282110a02144240186883c3c007047e800100503100c0201c2c2107031114903110081c0d204680c159004010007030b600e101c072a50603030300081010003946016056070001e00c2c007103091031000707052695410b1500c43e40d91080d402144181c1c0b854901d014000c1d01ca00035940c3c1c030700007484106d002a0800340020b034a400e10f82e04c00149681d000004002080c00c9030342d0219142420585660000a400104510030355a200c25902038582c2556010f24942003091918010920071070b0761040d1743c400c001c0400c0300d0b40c1c883c004540c40240b4920b81d5000004035000540500103642c0040d200b40d00d1440100c0901c5941c1e8205800344c40350b100200700f01c1c3d95400e03001d80c200310380c204030203280b0401070540c00c0403070311a4000d14050454504010310b80104c461007210a0b401940e0009000c0800340d03094404071340c2209a10306030309032504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 963952670 1250 963951420 963951467
    0xe0f0703381b0a021c2f0c060403080306090a02071709010509060406082a04060809190803071701030210110c15070507170a14070513050a050f1506071b0e0403 70
    0x14240880206c80d0034102c0c4001e448045001c101c07400501041c124914001c100c169604d941c0e060001550704161103641c0f0858221000c29484211792003126401603011080710220001c460f03840b5500c2d007000d940f542c184502000706c100940da4031001000900b400352180812424041103680f0020b048034100000d980c1284481d001500001d0142c4003140c0e69482d1000081d55000742c0d4030b0405810007040401c0010450101d410842c141c405144106242d81d641c07802000220152202d050b420b210194000303810603c690704a92141d4240c04c0f0700f501c180200c0742c4c03d0184070082a401901e80c0c098403143d031008602d1a04108042c40100300410596101d03207494144004900e840d50080e80005140c1c080c0e4030350062140c8000e100442c0140402040411b00c0a11086c50b50054a802c07915081c465141c8070005904901401400380150010011100111040c1091010310381c040070040e603104011140c103155003211001ca0501074003c3c140c00e0141401c00d45406441518060003000c1c1b01e84005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 963953920 1250 963952670 963952697
    0xc1f031a0a150212030106020606120c0907080406140108100f051e0601200601090c0c0f08162103060f030503070602030a0e0f0703381b0a021c 63
    0x60360380e00b0b0b0742c5148402001d000c2100000da1070a0140007000d40020703000b00000031070b117801041c440d11070f250580c1c1880c50302845042c02c07622000b010f2407440e0310660582c04119010711450529600501c1482d0000e9a88000b490302004440e0903480007200f40d201072140300000100d80150004481451001e01c41c0d130400100640304c03841000420008a80c80100268040e071040e0001c00c806403031040400410200206160340b921400d01698200604024079041c05030700c60500100455000705070048401c1ca175036181030459100c5003850403192100d0320141d000c60bc2030b0000645210301c1c1c3c0700550039840e00701c0018094915950050b0102d00b586001040401d8000c012200711580c03010f40180c0d2642da01c4042002411504940415485980101c101a00001804000340d034094200090340e800801d0300d100100014840e01c0c124810892160030000180210f03181e00700140802071030582140039200041500305010040050b0701c4040c0410a54031058120100305595280240040c00da0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 963955170 1250 963953920 963953929
    0x131a010c050a151503032f030a0c0c090609020711030c1c1b06020a0605090105070914062104060f050103080f092101020c0105060f10110c1f031a 64
    0x4400c0c05461221909501100348425500460154404002413558180c070b03410010000418102c46054401c030110780e548503030000e140346514074610000254a403120b00802110f400c1141071041f00d440c0c880f03141c0401e80d034285000e0000500b641c80c00068503000c41c0d0078000042c050300039056010380c00003000651b440d22102d8400401481e1070400032490006464580a03940240c000a03000c8041814046141c640c0400d000310402e009950034401c0d03843d00a00e00342224400c2e20000041141c0300410081142060704032088800000c04090070092002407e91507a00218010001303980603504100c01c05c60944581c4454108282c4100040d60440c0c0c0c0b42101c1d8030484c540340008981c049051107855540c04007414030b00300882ca50b0f640035402415483e02035045042404503650904000802506001d40d5400060300010201c00400c641d0306820f8034400604888864280180000680c00741c0f5154103c4020320303090380120206200c104001021945203100809001c0d45440d92544103544 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 963956420 1250 963955170 963955183
    0x9081611090a15151e09030507030b0105100e1f121b0f020f03031305032802010b011b020120011b14070c050f0103090f110102010b240a0509131a010c05 67
    0x224085e01c0c2d40075032400d90596140c10a039100500620403080007104125482900c0d604071081900c886070211200401501d25035810481ca0b50030941000710103c0c1c21400c010644242001400d10340103000705104d129042d035815100c0780303000751100315603049420342c030089134502c018141c805000100d00e000140798407888040c00c0101007440590307442051010074000c03244102c8030b080d00c0b40c1c2e41c0310110b406c40610b041681c0c0c0c020003551819240c0d80c295401000e26960603502c0100d200c82c3c4100c9940151654005240d4140780b4203888400303807490520900c01c8000042c03000900c4e440e50180f80d04010100344c0d650b0b506419159003448240e00043d0301140d2a81501d0045502808400c00040128000d2201000c050002d6503041143e00521602d1015440c11075403e03030090000d00504004c1c0042c41900c07000c540c4040248225a020500780a80500380305211072601902d010403007000070310300d0052502819012990f0b03840c00454240404c03080c0c180d00d5000e09044009020640311180c4410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 963957670 1250 963956420 963956447
    0x5150f0a050310091e0513020a03021c05060106020309190803190e030a0b0103050d05090d0b040c0b0a05030f010e070f080a06050a1d06030109081611090a1515 70
    0x81c000c000320303008005034000800545440c100801440c94107011002c250381310081c80c0301040b481c160204616078a1817940a00707154015001da0106440c582c24030040300c410312032145000860084030000680240101e03802422035a0040d41c4442038003042101103801d09060100c0420020710810400401105468104400440103850620200e2054507400b90014101c0d90600501202204102501c24010b06030b0f8021400c035800c0d860040415100c51149c1c00c08160f001d803081303821a000460301c80d5200c0c0d00c14804d41944044030781d980503000403030300510401004200003100b04003c43d45003040b000e0040c01480c850042c60b0516403005000e00701c447c0840d604010310346000074620f104a0700050300411010b4200061166035100b405018071400c041c80030030150401c0416054a0140100e00b01a030b00424618a010036440641001c11404101100d04060701028071101c0e80d203401000d8410380f510709012640b044d20041281100310707031307401c581d203032a8080a403074011603806451050402d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 963958920 1250 963957670 963957677
    0x30c110609090f13080d200f03061908060a0f0c03050c1611031e06070f0909050403020120030711031e0306030703060c030b150712031a120705150f0a 66
    0x98032020071901d080005041c001d060004000f8124101c0c8607203031f01640096400801e0103208009003052640e0758440d980e030303120b6011000d01c082074061402d886c0707a020000500c40781180d8130747c2c1c60740300302e08014003102c0d640c110950701d8031200d2242070355025203400c3c5008d6140411262900c0c0b120040c0d0781c0110b0410040000b2811024401c001284494403c1d82000400f00c40c0c184014030320a1289007802c071541071b118001c1c40042044240540b14040c0d110850752200b0140f503080a0154000b040300420540c115900c5409030341118150400e00380084020404075a40c03454023100c0500711204800032005694010084848151503004c0924907001c800c08140b071380c9807182c0c0c002a281c9181030b0809003003613251400c0b660301d40f9016440300240c2c50741556020700c40d0160740740542071801100c10251030000c0461001c1e0150f40310307600c114200340c0f0390603a28990600c030074046004081c8c12008228203500801040c441840c0130441e9100703001036240c1691030407208005da00b0384c40c026690784c001031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 963960170 1250 963958920 963958951
    0x40309090203070314100602010c11071514070f05010b030304060206040605093901080103080a030905030f0f0d20120606040302150d0501060207050d2409030c11060909 74
    0x5620036004050045c452013210b03c3d050030f100900e5010303141ca80c031482000d5882c20100c03070420b50040c07240d003020007104000f43c61a2450500d8915111055250450400025040c03590009640c2030280c90554010341000c005100d0b24508182155640354034203201ea4014070081024907400030301d0a9102d43e1085008c030380390702e44d440c01e10324051009129400c802061140303040c030b481c10a0403030641202612501d400a28095006403482c0c10b0038000036200f032008008034043c841c040d070000c034607140c401e00840f0302c2d0070b085400044050f0400c8036080d1040000141e01f000d413410501a28141011101600c030a445003480b480380103208000403c0c10058259000800995401042e1001950054420344401007242028031309a48505010b10285141600100e0203a200103031a80550f074020388820b000b0416a210340b0700d0780324083c030014016210804106041d050034022040b03d02d2003920b0701400514075103814a0401042c14a6a00681051101068a40c1d407842c00c560445244d0744603611 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 963961420 1250 963960170 963960181
    0x10b120a06090206120106080420092a0307120f1401030b100e0a0b03060f092817092106010501080703090f0308010f170c220603051b0306040309090203 67
    0x15217000703080309050451503060000a0840d040090184202c5c860030504410f040c026001c101146284056290888810710018003007c1b03201080200d8002c4003070000080b01c80c0b4a8000803c2e520444400380018000a20090000581c1c05a600c2400318500c0511582c2c81140c0288480101448084c03d00e406000200740340c50400c11007031001e4000d010103a0000d1410550b6900a808003004003800781c403c4a00048480b02000c01040c002d1f41d51901038517402012002d40500c0350941c9001704031030340840405400140090800390619803001510944a5442d07008028954851604800c80000e0440d41c0c8040740c03d010880906488003400e00c202c2c0d603150001c0c00c41c0104482507000700682c3c008149a0b00785600f241d482070484a200030b641c0145926820501200300102d00e00d62041e80c01100200020701d05090808400140304641168000e00d102c03032182034030a00c0d0301c1a0b800b5045403081b80911a0700340100380c3d00f1741f401e400410041c01c069600070b003058803d2240f00707244d075408404100b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 963962670 1250 963961420 963961429
    0x60904032102071b090e0a0b061809070602060f0c0403030c15090606050405010b0f0417030c060a0b011404140f040b04060303030e062a0705030d021902010b120a060902 74
    0x72400080c940c011521648146084021103901442d15251810a4000083c000d496070060100b64060703e405480099055600d40140d60405401541e001d40305005c0010300b20740c860381c1180f24080306002841c035207161040281c248040644201d014004400c10041d0401d00c0c982224210b0b5890310308410a0301440c01c11888100b010402c2c0c0b00300301d081c480e02906002e203075080001a198100c404006903642e4801c0e0324158072948010300003854052100b0402110403014041c3c07801282015286407518021703925081840032151001002e0f81d5102414507135031b00c6500448910415148a1710341428100c005201500340d242c05880381207aa11902e00a48543e000a50648400340080c009580c80e4600500606400c4008903803034802c0e00002898500c40d2203008014084000c0c0307030707640c100000810084640c0001c0c403e44c0c030392004102007800385a0074401000c00404511124119041c4048024203458840016901c940d000340d01c0700b001004081459a0021b40c400b40010740b007011440800c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 963963920 1250 963962670 963962717
    0x1b0309070e1305010e1614040e0607020304090b01091a0a12020c030c3f0c070f050108060a0609050103090f0c0b070b09120304060c0c0b04050f0f0606090403 69
    0x181400d565503818003001140c10800740d800b040c42800207115440c40c003440160348200e04541d0256100480004100c0032280703154140040344058408640c10700100c48072458180d058449000507400090208000225841189408e134000d01e0900042071509030003a0291012002d115002d03c1c00040c00710f0b605014071100ca0031b24550b174005540750b04480301c03c581c503a049003071101c1050181d1074440e1001200340c0360303004062900e2004400741d4851a0400700d20b44184650425070880c0810410200d0304c01045008020011074022400d4142400001405250080c06050094400c10f00a115817070700b18911f80b0603160286800944002c450505044100c0da80d00b0140107160000c002107580041c4200600c2014010050202c2d0741d1907844205036100c00495440705a0013051002c41e0018040740c00054801d4140c2c980007c8401e419107032001244801e40b01201e440c1d00407800d0715080681803244a507031079803000c003421540c5030010224800c600010401001c200807003904841e17140354107265 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 963965170 1250 963963920 963963929
    0x130f09051606030b060f1b0a061a0f0d0201170c07061b0f0906020303010302090622091b06020a080c0f07180b060703020307060515361b030907 63
    0xc4581440755000c90300340c40c060a000d03040001341003040c0800075080c40e00c02c454a5401c20341000c0d290111010794010052181c41802e00355000d6012190086021402405201500c0b40010f0a800b8031401c1009440da01c1c0c0000305000d45264141100980e80240341507803c50010403c1d292150743d000ca00314158801c1d1300d0020300451401c1c180000d84e03690300e030b20080c2c0800341e903c411910b120085401d6604501e98880c443c0141d1003000140010300b8040280e40d00b164001d01a24146d00c0e41c4030000c07000e04d4124042001050b81c0e0460070051065103084203410040040f4803900803030828500944805074001c02614081c0002101004950308010080d580d1106209503103080d03444210f10800c1034218a0080181c0b07040032590201c51410741c01300e5100c2d6605030003e51403c036050b0b44050140c0b00080c19404510f002071039024103030b12009170a8400d03c0700240009004107100c95058883d404800b410000c41000700d0811403007500e6000030704495010030b5905522070b61140c0c2a0752510481e50007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 963966420 1250 963965170 963965173
    0xf141e090426070212070b03010902090105042c0645040f031e0e0112090803010b0418020903071806050406120b25110c030a0f1403040302130f0905 65
    0x61180a20b010003a00ca86842210128071300c41076410b4050b0b60320071034021032038214420001080384040030303401403940400604000d400c280d515071449180422860030344170018900400b1500c25591080c246a1211046078100342403035038103011114100300381a0001406a0301044503900c200ca245403010f491030720b010750703540514092078407140c0c1d6660a070003180403c01105000b10f98440d01001c220032135074242d6400020046040044401e1049940d030007102ca543c840b480c0001c5280040254064440f90703402a6650340313010f004a50040340d512032206c18a206221490840c0d86c00702d41c03c4201c403030030640c48a02402c0d04000744020450342d802560320901d48100015699112180c0740f0840e4003c440c031040aa541954038001c01c10000150440b196100724961200d9000300c117410811100c032402c0b01c801201550104e8901180c0ca8016504220f0102040c010408480001c5040c01107002c00345080c149141d021032607690041002e01d51958540b00d1520b2440b5295009003c03c940200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 963967670 1250 963966420 963966473
    0xf070213051e070c02010c12170103141902060415051908070f0203090108011502010906020310150f021207020d02030a06050703060807050a05040c020c0303040f141e0904 75
    0x6010911442d2980c0d220380000185000548010f004211844000342c042e103440103842c1059595182e0303200c0f40031444d420b010303203100e110050201000605010318814107556144000303070a4560b18011030590508209810b00361440010384454055404645504000c400714064100080d40c80d07000d40305081e6481109010b802ca101d503800010769001f0f40a545440703070112001001242c88c1d1140382c00280c0031031308620040140c0c06421100700441045403000040078011980d64005030b90040e10b0700c2e88170198a000a010091045400840380c1c02c043c11305c5002d00c2500c0307201a480c1c81c49141d2100790101c011444006648032030a1619410354024203954070940640f41c1500202010360320700001072b242c01b6001c903902100203011000c0d81e80c000d10041001d0300d01401c00015020340c0340e003841140600b4040741c0858038100046c202034029440083c0600d4184101042220130034220a489400301600c0013001503401401074515010688206001d540c0c0e90905c0341c03101d001d81c002c440f105204031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 963968920 1250 963967670 963967681
    0x5060f03101a100e18040803040f02040f020c0f070b0a02150603070909061e1a1201061203090806070e0a03140708030307090e0f010312080a0905060106030912090b0f07021305 77
    0xc00d07140390b1440848030505244521045d007080507a01b100c1c001c01c0810708001103800b00b4010313001c10704142c2c801480490301c0f02e00c6220310700c01d9800ca059441c04903407008208984100080c802c0002a04c0c072201d06504198081d00005c0d5039009682c9842011040310000c98005c1d10b0034041d480c040e02060f1f10501c80c8030741901d04a00103220541e2080c8200455a26201301c440e0703203002d124040c90f924000500b9400c041010418490b00501c00340e241903584883c0011842107920551007554000c0c5c40d220442e91608c00040c0c1080b40080218041000c0c0a82640721551110030301003e4a070005c1080032500f040581d282c0c80d059180d00304078460702c0040100800241c1c469054015507044c0d20354940c164030b40c1c1c51510140002030000502d40380d42120441002d0748210002980b0903d400700c0410f02c0c00d9603866007070a0082c01c0c0c011400007600c40700d00d403051000c40200d844400c50a407030201010707031415590550a0044c00d211820b60240021000190750300c0d11500501800081410842d070b0400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 963970170 1250 963968920 963968927
    0xd0312020f030702010c0f02060601030f1b050c06090712080a030e01060b0405030c0a050306071b0c060e09010510080403030c110105010909110105031003080a210f05060f03101a10 79
    0x480720702c4011742c24100b00101c1c242c0304145000010007070381c005001940740d00006501501e295404070546564a482c119260401d00b00c42c40401c0d040c0340c131110b940c0d0181c15250f03410880001c202101641c8078000800442d040d01e408514415008240c4070703210034080340128050301020907407040c1c0f5800c00303001081c5a441c20f001130003161001c504403126118442c080c042d10700900e11540c1e505421290000d80058002c110300005680d044003d10022612541c800c1e0424150307810500c0040e100d0117048080d030810341202e502510b4101c59280d002201c4842c001d040305002403000342003503103e9030203403601030040b0418404504200c000348019a1174240240c0182418002511101202d0721018040d500138006c40740078030039802e00300c03c1c101e0440e1100c20299102d5240c0d030080044645142444450921041414107940540442d07480c200100e508259400500503d00c1400910004c0163340c2c0c00050101e00c424064030b010030b0032400460340150303411820700c502e41c11030004e41207200050350 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 963971420 1250 963970170 963970177
    0x5030703091a060a0501091a0f0408150109050a02032721030906010e010501140f070b0c03091b031905010608070f0807060201020304120507020d08180109080c06090d0312020f 77
    0x405131100071116580d2001100c2a10726440f0350b0407444a40c500c0b0002040740740c0010541007851642962505a071090081d26040c4d6000010f1042d8144074010300080a02d8020541c00c208040415401c50070450b4441c4545580d41c000c0401041d410f2540090400c2d0a000f5030707802901081d00404101440404082a60310803152940703140564800826614813040301e06050b1801a91050100c210f51510b560440c1c1c8041e000c00d20300e1005111100004090203251340c4a01450702c070003900d901342916568589100e01051101038100540b0201ca079480000302480b0244c200c8180380200103450405c01e00415803a008005c050140310008500c0050744030a03807084402c598100c0b40c0f444d5560350200d08074042030b64020440302751200c84450261085001d809040c2c0014a5009183c46603610703e1002c0c1d000036500020b2440300c080c03c0c081580c11602150042c50201c001e0929240c10400080840c401e480125215540101c11442414401d007200322064004000840da103274000c20b5040c88031740 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 963972670 1250 963971420 963971431
    0x108030a0314040b0c0f0d110403020310050103030e131d010c081e04020d050f0607021c05040e040b0405100218040b060a0816121104030308010e090c0105030703091a 73
    0x207040001c440074100b140041d007440355401046141594544500c4a11180e206890149001d403003400301d680c00320f10910810031046014240d00d503031180f0350303c149420300090500324080a4540b50040002ca030b000110b00040c48400c8505040e00d07440e0450141c018100300b16065031407032401c00440074041055001003c5115030343c9951596a1311690f550010600c2070340516242082400440c005060a44105090700c0c4210f055402c0720326801c18041c40d10404440c294016409000b1500244e102480312480c14421407500c28074007401d041540c0070456010f40700920403028800003809011084c080a103010006078001d6595074005c5000030220640255480e100b2490440c4106c160304e0f10301d044518403a855245c0c01055900c0412103520300310702040c0d04062044170200c10303015403054462541000b243c05045c45c0c4031802d40c00c0c0207081086c1600b100010070443d0041c441480c0300060f002c10603000134071f8056a203a5501c0c00031406000011001440c03580c0304103020a4801d4003e103864400e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 963973920 1250 963972670 963972677
    0xc02240402043c0f050f07110c03030301031707201305150f01021222060305101217030103061e0515010818030f0a020613030f180b030108030a 63
    0x11a111105180c61103c51a1000c0d08804404202d8500d6100203a00141d011200b00240316032040d402d400030303035804071419940100500104090760750031150480c42510880700901d04148100d0201303039240710602000e8191900410301000000d000c03400c540c04182e100303512541d49194078171050140661081090f101c0d19828412014001c810b100303182c424280c10442c2d943c4030302c41c40d083c40f4614a15041882c114000e0020481501c00395400500307086108014090422620081b00300881d001c5800c00c104041c105024041490001c0c6403403400c2e11401c50382034080001c03520f0810806400c40ea25000d64240c040300010500a486d03002c0d941c1500c14076280c0b01500c002403080d40886800700c2d260201c1c144400a136a029503c6114040d41c8075408008056217015080151071660300100261140c03005c0c00901c2c0c81c0f0300d5034107124050b00042c1032410b5065001c8030303540192408003410070076400c00110094032206441a42095402001400c0d40f5070359070758440a11a407698051503010010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 963975170 1250 963973920 963973931
    0x2a0606170714010804030c06093903020604150e030d111b010503270102030f1006110303040b0c1b01061505070203060a0c050c03040e0105010e0105070b07030c0224040204 75
    0x4074859602c003540c0c035a0050b0b4540000365900c0d0b8042d00c46100b042e41c00d44d00c169648650000045803a20100180c10b100103480c811502c0107207541a04551800300500d904550fa0360800041c4c030b0b42d9090300d0654001c6240c10040c2600c10004a40d01004841990350500c00c83d54454102c0e030f0407000c0542100340d0107051740c2d0394103000080b0000641046215078005601040010ac6810102012540f02841101c00080c580602c882d81801d90700f0907243d69072003009803818841002484440c3c000240303218104a6007144090304055164000100040c01213210503000484023a201c0c011641040d4284400070702442900841c54001d01160048a401d0303106101008141da001e1400d17111201e074000c004082956800804101801c8030101600c00e1100500800c81c1c44401440900040d040c00d014618940d03140400040c40e0207100c41030541809403c000c154041100080b0440e8826050300b4041114442c4940c101d00e000c6500c000e080d92144845510281d848140504500803402100c05001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 963976420 1250 963975170 963975179
    0x1b030c140f0d030c0215012c010e0a18080307030608070f1206090c050a0905060102070506120402010e01110a03090e0601030e0703061112070c020103050702010204062a06061707 78
    0x566034060100e00846038090202024071900c039801644c040709135031042d01c12980314040c0401c5075800c283c001580d500c9000c01484402c81c41c42c0949000c035208298034000e85e5241031710099800001401e031900003078a6101d0035080c1c02d2030050901078558031404543c0d40f440d10290080040060340603140c7d1501440000080907408446880d003038800c03041c28103d40c402c076507035800001e045176241141e01c4140c07480e0018441c0ea6212202004041c0f40741c011549140000009050070415000070344511410300224480070f40b4180d4a40c0c1c41a420b003000c1c1c16500300031006807401c03074041082d0061403003920f0009080561001c00d41044911843c0b45c0b0400781c544000540c203540f006080f03810694009281000412069000714990407400c0b100a03181450603000e0303c4603244100e8100e000305903106080000c5503810300c00e0707990080c03a5100031400c103420083c00600c01031440e144e4020030340c9580392140001c11800d00c25006113a008030704000d07030740c4d403603030080d000c00d040310721203000c40c01109000207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 963977670 1250 963976420 963976423
    0x70309080706050a0818030301031a010b0304031b020f030f210f1c0605180114190501030b19150f090e0a091119090f090f020d02011b030c14 62
    0x80580d00b1507202e10703080c280c295400301c1c1c000c400202400d00c054002c141614841070103000071406036000b907115030f00018149025101c4610107a0240d020600104108008690304c8900a021b61310740703024014680c0013600000d4455002c503801590315001b01d00144003680400a018200b00301c0c1c113034440304441a00d03a0043c8480c0184140c0c100d0880d410040006040082c512042e4481c0a6600c00110192580041410080c42d0400505681e184200610002d810038400b00d0000760121a400000507507002401c02e400380314894541810b4483c444001b0582d900500084415070180c101e0324034981c0d4002000641c139940a071500440c444118484409100c1c0120500780e807508140e18407580c48a210002c010161940d041c0d9a4603500c0c1c40c02c400300d40d2003c6d0300154500e21081840c0500342000040e502b00c440c0c0d10300940b03095141014180018400d1111594080d130100e40780d6a80400c035000580d0303150440180000742a000c09520b104241d00f10103001800b60040c2400404c065242c3ca003103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 963978920 1250 963977670 963977683
    0x40b0103060b2a030301081b030f0d031104170105220b070e0114030415050a0c02120a030603050a05010c080601170f0406150b0c0c0f010f0305090715020307030908 72
    0x5030707449034100030014402908001d00d42010300f90140c1c58a841d0149015107085400a8010030031030741213010b950350000070070090740351a80b03800ca0141540d4440e005940d503451100c040d00e02d082c562a00840c0461911405c140d0f070040000300807200001c401b00030003500900c0c08503094180745800c0d24101c0c15603010304a0003000703158401c44021654440410a450355440c103003120381040b040114402c0000c03c2c990107940607030b04c00c05003801030003e00c5042205480d8001c101203129841c04000b0002141c1c00101110b036403c030307140c944d07a0b6040840c10460287c201a04060010311460601400f0800154400c8080301d0b06651a0012919520f00454101400b5a500e128aa03641404101031803012010302c0d8000d8440c0d903000030900d541c428040c1406c4034a5200550100700410a9140440d0620108648000c110b461a03d0140f806d0001303071121903001d00880070540e44100080188004000310000303018881004071008640c003000940e6684050390440004040750000500c900b00003410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 963980170 1250 963978920 963978929
    0x3051312021e011e0203130b100b0d090302010614010c06020f090a0f0603110316031d01050a1a0d170a0302041d0612070602031b1e070501080c090109050409052109040b010306 77
    0x681e47c0030700513498005040b8406004002ca80460f0b000001d08905c40c0c0700101582c1005410108001c900c1e81006421200700e03602411102034011506c1010f0ba9100261034039455000f42c2c0182c80d90400100c4c080320b4018818042e8000c2101c0c20045030000410008030300b11800350340c0c00d2100c507849540c00c400d640810780f00194031821482000042c9400307500864489008990402c4030340c004010280e095400503581c003484256035040701542c2000129540d940c2c02d8040d2440440607180350b403030900c00d084012242c80c3c41c0d480483e000302074501c05d4040340c1c01482d20701c608945000402d0f8242d5210f04043d2149803040090464a0200100c04074014007202c1142e00590709103030203a00c5003401c1e46d8401420700f4041c0181e4003030340c641c6104003094207039201c40c0c2002861118100800502071075400f5001c80400da03c2031000f65216a440f501000c1070310400e44000c55006540c4c80d00c1480d04214207603200035450404402951802c859000c1c1c002003508032002d101e48202c031001503040b10031034001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 963981420 1250 963980170 963980191
    0x5030f0f2e0906020d090818030606102a06020a0e0f130c200109050115080a030c06060e1515070b0609041b0803070b0703051312021e011e0203 63
    0x900e203007103000c03541c0b05900c1107002c3e0002514100c494400c3e4022115019400c580d4030320702150803500d1010000d592140090142d0007003046080c200000344000d00003402001c1041f60b80c000703241c403000d407180301007150b00c0c0400505041100c0a240c594080d4000144900009043c980e4a010034a0a6448980c1d03060f0090b022080c0711116006c0000a00800304c2c81905005c00341c0e407034411600c0866001d410045003000006603040c03051800ca4250340961446015510b0140e000340103010740401c494415a0b032500740741c0c044c0c541925050004c0d0580f03a01001941d5500d07401c00c1030304c440350640c16104078800c031000c40c140c8103a090503140d14014002c0c0a00041300d494000b546c035050514482e034100d070007015102000c184000550605000d9508407150642000c5504010842c2521106d41c110805003010301c503924114413008119441c01c0350150000404251480500d0b0080c4a2090025046070003990002c80d502d10450180604030701000d0030001011002041c1c1c800c074401d89009021000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 963982670 1250 963981420 963981493
    0x90913080304150b15030f060409121b0804080a140d090603020d06030501020f0409050105060f09040f060e1503120a0507140c0a120b070804030509061305030f0f 71
    0x440e40c0050f80062124910b030070780e0300c4110303044a646221914007500b84951031190350f89485402d80006020182c035075030045082951803c0002d2703480d10400484026880d040c001d8060500f8140c414503c00103000c1c10304180000e004c900c0c0f000c04109071516038010444484d499940501c1720b540d560f01151040c1c0010320740c0c84203200e840d00c640c00030148121181d101091240d1661a0300d400c85e80040d1148200c5003000400f000030382018000c503801080304846481c00c0c0303410540458043e20a8070000c1f40700b2503894014a04070010365201d01d005c1c11041c254000d01d8642007505070030840c030b4252240c1c440e2189513152442d20700010120350000b4180c2e40d6581c00c24150741e4800c0c000f240b24510701c0b0355034021000312000302d03110200f8040041015680203171021303010303080c02e94171036070003400800c104040c02c400c0201007a04542100c250f40410303582d041d40c0c0c55200c0740d0000c0724840e507084130354580912201d0000c8140b001811050030b00c45003095038010000300810340f14840c040d8080504d0fa26844 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 963983920 1250 963982670 963982673
    0x301090b030715080115110703290403030605032a0f03100e0d0f0806240705070b1822050a02040b1b01060f0e040b0403110f03090913080304 62
    0x250400403210303201034201c48000d5102d4034441e14401d546040340d00020540c3c03004100340007842001e020746035000d081c40305010503291100c0b5203844642c00040c24044c002d5040c2c40000c2c0810000b00414114481070703601c913080c0340c039005002d4111440f03110320178882c1c219030304071200700d90100801440ea881c2c02d50341415040d01c140080e000403440d00d00d51502805c0f01c4c0d010400b0040c09900c010151900c040c00e401c4002c80e03000b424007048854054204100302d0100002511000c48640716891500340d4038190106c0300c04000c130701e07214501c03004002e0700400600088101c4003601410800c1012100302050307a0440c41801b19080f2151052054442c40c5c644803201c194107035001c6504038251074005443c0c40d03100c8101e60301c02e500c03002039040112048844076070707150000c0c131074034001c1e050844440d00043e01c1c00100c16988000940050418654480441c0405008048035580410020192001259120040ba450f5000240c0d5180500780030000541610f001c0103040803656030100d1803c2c11078486 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 963985170 1250 963983920 963983939
    0x50f1f03021c08030405010903020d110c010804080910020c091b0a1101020706052d0c090f04060e01060809070b0703050711040b0913051504050c0904050a061803020c0907050301 78
    0x282d1400307410805020451402040c0c0002c0258800ca00860001c6140d9680d403800910304011303a540710040102c1c14031400f03640c3d4070104075544807840c24a010543c0d6161420a01290b128400701c141d4040340c3c0c048000d12840d004511104e06960885100c01c0300d0f42c451450402e0124501b2400862a008008080100e40101106c50f00c0c20314402c001401d01402e07545480c100c5030240c40c2074000b083d0582c1048030800143c00c034954a9000c40400340303030b14107100d0b4140c1e0007070165118682c840d10f06a054040d458641d544940001c0050304c0119866507569030001e0800d06044e12082558081ca040219104040004607a1a958540d44443c64500c0903207412080103070600480fa8029121801b120050380c070701200c940240341c181840100b803041840e20515006041d080c003400b283e200401c100c003259002c940c034852298140d641005542d140d01d0031608080c0703402d800514547c0f07800441464034640622040745070f84241c080b02c030a10f4002c004c0040c0c5903011034100f0002030b420401404100c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 963986420 1250 963985170 963985189
    0xe0a0b040b041509060b0405070c0b010b071a010e1b0a08060f19030803070e041506210906020909130b06120f0a080a081b030106230706050f1f0302 65
    0x4884081a1020034000740703090b01c0740400700b526941d854403000c5806d40350912500d03030040c000c0d003044e1a01515640c0c0c1c0c003c505905104881c0f02a2000c240901400113480c085078034528000c290780c04561310343c840012401001d54510344001c1c1e994034010000032000044841421054403079070070136a81d90080080c070192401d0b003540c2052505000c4500e40c01e00c906008059440758440c03136242c2ca4401c0004051070b0b020f91020b40700b00d062281041e440c6a1076031580003a551586032010704c030054000c540246100c2202e01d050000d2030400c1341c000b4000c450b4003400356010f04981c85103070368440150b4428218040c2d84007038054081600464960300e4592070302003440c00d6000c02c2c3e8a09015a40c049030a10b060000265141440056401d04680e8441c21507a80f01001059060401d40030080d030410b0380c001401510103100c44004002c0e6003142403051040c0482003001001d03079800031340c034042c1c0242005540a540c900404804601d0803080a1245042000400b038100d020500d035808010b48100d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 963987670 1250 963986420 963986423
    0x31c090618060b01030f0c0503150409050d170a140a0b010306090227031903030c03110307030911090106020d08060d080310060212070210230c0f010e0a0b040b04 71
    0x9554480d001c410600001994003003a01554001070300c100d80800250950f4450310901a0051a1544455005d03802c203007501e80140121005c2012906c031880418028401a48003510510420901400a0394020500041c00c0d080c0600c0b4002c640303400000c4800e84159110000d04402c101002038040c00f010b03408981c4c640300515002c2600b5540d0140300040b644044510581a914a00c4201c0340320b601140030303012000150005d240e0100407448041d8000c100040090805441c0c10b200700055100e900b0001420003550301c01552400c08070801380051008200032210303d60b200d640e03d9847c1c03070586066412108507070060035880c61259002c460210340100300d181e0180e84120200c0101da40100034502c589520130603210040e0401c0000b925209501c100b04d424100e080050b0401a12203e1400d581e0100c076003807202103143c0820742e24555601c581200401e588001c40c1503200e08800090701802c44488400804c00c441050b1b4030161900002280a8055100140810001403c20f01400c1d40305 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 963988920 1250 963987670 963987683
    0xe0a0501050c0709020f070204061202060304020d0f0210050c0c15040506072303041a2a01020903100b18090a081608161e02030706080a1e0e0f031c09 66
    0x39484a04e060100d0300a000812256040415100b046050078400d40340685481103682d15000c01c540e001858510000b800280240d00c004001030800c00c20001c1d51010343d600070000440041280030007083c0b50000b129903640780c03090b00d29504041c1443c1c082030b4141071500c1c1103c0d01d0281414284451303640050700489d40d40c0241c8052101100d850003641c0c6070a00818060f44d6200d02c8d1410080300001c00011504200c4010040c0416110034424602031200f0341003042030000e125031606a0082c042c1d921540c0d054090101c1c040a82d406540c003518420380300f01c4000d0012070002602c2006110704958003861540310904500125400d20f0260240c9a03510040c04214241c6a136100040d800a80d03516901c0c5003032100c80010032041d0200c0006e04a01640c40802002c17060700040c0d40c841080c456103082c8001e20000c03948250050700310030440800b030780b8901c0c81d52001d00007083c01404208141242c0b805000302c0708880300b001000700c4c3e500e0908104a80400e001314540503004140c080307400c480c003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 963990170 1250 963988920 963988933
    0xb0105070609050c010206071e03180b3c0612071701061404020705030d151a04050a080c03030301030b090309040509031e040b04030335070f0e0a0501050c 68
    0xa03000c2c000c2102042c07207107025201840c03a01002915280c8040e1003042804200c9281c1c03c19041c039148511044001888d0100701801c041310350b03108094880380c0c094102c001000400002d210349030317114000c055213543d44050303c00d004010585c002c209401580140900600841d415142c03424046403828041d9059521841d030355204407211a01006143c815a51980000c00841110030720200342c01d0003d41c0d040d840c000480c1e903102e0300c920a10050008050742e91140c145030070651030068002e086030b410b0041101d024181c0c01e6089400c24854544200500100480c0005011400420001000d8015411039013136a4543c46030000080054800c4d20051201ccc840070307503480c0035060160079218081d40ea51849200305103d02c5103064560300f0540d80030002000801c0b080c00c121030841c6c1d0180703800289828002da801143c05c1d0312104292450820803840c407101e02061f0b101034090141501c40709031654a145041da40c400c6a404451343c450800301040080d5401080180011403180068034813 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 963991420 1250 963990170 963990173
    0x1e0e09040206040905090a050f1605060307030e0f010204081b1c03050f070b01031101020c010f14130902090102060f150f030f0106090b181012021807050a120912030b010507 76
    0x458500306c92005071640928000d130140181408a00c0d444510300c0050700100018280b4842c41c0d00441c829207025400c000001003610f0b22a0780606040e4002c982690034540a0141c2540030350024090b529042c000c030800780b03c2d0040300815000305c240f400303809061101e003c00d00c07450518002c2030040d000e021042011446420000e002041024440c0414000e0307541035041171026901c2418865040d5440030f0000d00c0544e800480d000c01c00d402910f40011b6580b540824201280244180c203448135401280114901c0d4094014022a4501fa421100c0c1651641d2410719403030029900603010320a440d43d121003606007846200200c9002a0403034580b41e80b189030543c219203040d88280040d41d038801082005d4508101c0c00251f0450428040781c0ba818501072880111030749100e840403400c0b000c0c07134143c110340b03803920044212001c0e14a840c481e4034003618060f002c0e600515107840040c040d98591880b5600074403030070300c9040d0403102124145400d880281c3c001c0280d0004241400b005005000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 963992670 1250 963991420 963991439
    0xf080f03070816021b061602030a0807060b061e0a0c0b040b09010e030a080f04110d140106170c0d02060c070308040312020601061d0409080a0503071e0e0904020604 72
    0x107019041c1aa5074450340e03d400700801c101c0c0320540702844219040300b00f1445486403402440b298a910880e489585c0f0111403010035003c460045009400d40110039802c424411400044c103c114007800b410b021a4110b03030200400c510650144400c80590101b070b03403540748019806020001c0903428800c0034010103468240100c2c800b110101e80c0c0c02c0100c0708010103100c00b03009004188408000440c240b03003900a000d0300424005004140d054403002c0000d06200c00404012800c0cad401a2242c44e89200f2820702c020074072445455090103600b084000135008400c80f000b4140303904003070301801201c108442000b074540140301c01a40d10020921001028680c01e0000c500194460100141d0301c070315510301100c24509841501e001d540104004114454015449a84e030040081150361140810400200203202100000d4002c403c003040c4079a0842d0050300442c024011512900342e2204a03040f08030201c508120000c0010b6003c01c0000c40500781060b40b5038000d4401000542001c4d01c41417501d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 963993920 1250 963992670 963992677
    0x30a0f050903090a0503060709090b060d141803030f221e030806091314031909052809020a0302070506040605010303091406040b0901020f010c181d040f080f 69
    0xa10590000240f000040c0b40c04010700008080036005030450340703400d01000d040c050709445203452300390300c45418008990300c0c1000c461861400301c00800c00c102081c200d00a00c444101d54061001c0c87d20541c1030a05035001056a200c0c0320025500032480ea03549064070804100100030040c000d82016000000900542001c01c02c2d201503075518088460b03a0500400050300900424043c0e250300c2c0621103034440800c0740351a03283e0446071a900c414044041c5511314410701c1920204020fa1381d1051581c50f034000708100440d001102c5915444030f80c0d42d0141e203804404411540d4010000700c040010a00355005000d007042141401803d0403020b41300c26040c0f03941100c00300c03000c81e650300c01402015002101407001d490a02600784070000c13560040348051281d8000c0d400c0040000c52071025076032003080703446440800300000303000010300b00074043c12a0380114407103000d21481d0903010401403c00d5600e000100c1b0b1034041626151240e03281c500c0c20240a12094036038100800103120b4042000004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 963995170 1250 963993920 963993931
    0x1e0102030702150103021e0a0b031006030b190303080903041e050a150906051b0a060b030c0d1e08130b0702130c050d0e030405210c030c0108010902030a0f05 69
    0x9a80ca1034a41402030428200700c02032035500802d60014009a203c03400b07080110420400c28801c140007000c000b0354541c50035406100840c04c00000c118040c031085d0820812955151000d103e40300d60281004a1900c12020000400702c4505040000c03030711541d1119042540c29040e00d01d4581ca4400d0640e00c1e0810780010019404a070b0810010360500c40c5400c0000c0a100c04c03050345a8252510042c418911446a802000000b04071a0b0394418040741d801c020911130411901200721518080b0007030306030020250710a005003012509107003010251840c80c03d40c08240140e084010050050024181250690b603041060100080318104078041303c001d08200c51500d900c440d118810010000d40c3c940c1428444c500305005084c00681103015100a55101d070008070b88400034120b194a58040d50703005541c440318a0300074a000703681d2561030280d0030014a0a40c4c0307204200300141903643c4650402c560000d03881a0040102c09403c3c0e002d181c10072855040810304005000401041c4e84d01500d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 963996420 1250 963995170 963995173
    0x1051b010207120c020307181506113c0a050304080f07060f05090f0d0203031303020406170607050d09061a0316060e0d150908130e040807080c1e 64
    0x880b0b605004402500080c080901d240549420703c1d80d40c0400d4446c000762043c11204402290044999a1503401099800c0401400d4820300350313591000410600c1c60210000d13182c0501c5503001d20700d0704190410032852600500c54544040110641d0421003030403403900c1500d00610380e017200060303000c0c00208020729403440103141d000f50b01c20752241082c0841d4001c8040c000d001b82c58118568015041d40c0310fa20040302c915100401c0d500214050701c031142d5000350316000c00188012010041c8130b0000c00d490098604000d82031f1161000007401084504558559020b00002111548580001e040c4504001000b24550070940e8807081580c14920701ca401b02c4024503102161303403d081010746180c69910050007402c0e840c0003806081e611909a84500035000807111f1000c0c0080500300300000c0d9180d01007081510780310308250b45d964001c4110381c141c02d00840e000040c0c10030207032104d80c010b0340c1080d0b041e440e058040d5074400030755001c550906254061200044400850400b4140c12121040c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 963997670 1250 963996420 963996427
    0x2060f0f0705060127091a070302041707030c0e04081c060303030c1e050f070c080d17010803090613030204020a0f090801140f0903040f0f050102070509042001051b0102 74
    0x10b0200d040140513000b0001c00041c00c1c0141030036450400c011400d95101480c00134034030b2080d0a020015070041e488a0084986980c280009030382d0550041003101c0f40e885c502506060b9035420b440c1c4030340203031001911100c0e8404051100c0005241840d804ca4441c1c10800e280c401a900400e40100720fa808480c0c8041e580d40e070030028141c060141416074074039407400d940d040d4801449000080c4000403d507040010204d0141001d03403540f4200c034006500303c1c0d010108541d40c1c40349603070740300364400c03403c0c0024000c0141d03c041c04000294003416241400055070401080406000d40c50304000e42c031200c410f000c0140000076840d18802071001004036a50f040e0001d412210140c420036181d4804c10307031617251420540101d042195040d400001c010700188079503c854a041c0d10b140215040441501140d80002540760083c18050084550a80030341d80069914002c022101030202c0d0301038220307005146000d9162840b80b0150140c2e080506202d41072182c5182c860742443e00a21312a0f8440c0e5000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 963998920 1250 963997670 963997673
    0x216030f0b06060c19030e0406090e100516031109180618130204051314031201140d1211061810020c030f0a1704200103060b090d02060f0f07 62
    0x418516441201943d1581c9002c048000345940c2d94103602c03030201c590501d01c50394402c140c0b00b0488011268070040042c09101c0d1508001c80041c900c0c0303881010544141c02e40c50000c0a190b004d070300e1043c00704000c880f44002c1c02c1e40e4140c0c094114001502000c105c10808801c0c80c0d030701c200984403e490320074800105450410288455074048800080260b00404100a00b401845140101d195415900441e20340c84403410326169804400d00100001000c82c3d1500c54440000040d04c4100c03804000700c00c0999952183c880c40400500700d05801405442140700402d0030181c2d04210080380789030803510445410b04040c282201560a8013506001c020060495082000018000b01c6440d42c210310b004644000c1d10743d43e225455001007107000c04a0003502c0c1d0340c05102c281112201d10120004c162805107071021400b00e8a52034400400c0300b04040e100c0e603501c40e210b04410b131401c03070340014904002402080f0011603913030012640104100603e54280c888140a0100a06882402c2d921440f07036 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 964000170 1250 963998920 963998933
    0x806090a06030503090411070605070c050d0e0109120206070b0124020303010806010302190b030c030618130b1801060b1305030325030c0f0b0907050105040302150a0216030f 76
    0x589a403008500300708051022070000700848442030130032200016406a494601d00c2280508600503242900d06002c201e0015000440d080e8150b1140050b00c803807400c1da11041d50040c40324900c0c28000341d54220144085156281480310440c0000c0130b1030b0030030210380c2c0c0b03070079040109030049992009282000c0b1900c0d0f451030004464045e00380080c0d411581854102075580302c051002a12900d00c0d092507241022101001e4406400a84a5039580f0303d4204010380341c0e0f501c04e4038120300a0795400c407080061030911851500400c0b08030440b0004405d139031a041e000075805844101d00c6400d4090000e00c0040911030580200580700146803038448803145100c40e07840c25406079029800400134160050701c445500d520700700850050286d150072502701140d03105465140207000304400c0c42e01c001801402c442e240e204511580483e040d2548400046549000b984402500580c0d214000d60000c0c2400014103082e034424812145e211125203000e5a0041c2c0f40c0c0d005030b0710184440e10070000d03c0b90 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 964001420 1250 964000170 964000189
    0x80408270a05101d0f120607170127020c0f06040204050a050c0409090c03060c0e04060602010e030d02220e040302061b040e0a0f02041707090c0e010f1107060806 71
    0x4841d058449800020060080000c01c07285500c041c00c2241c4104d0700740d403008040c119403480980741131000d5903043e10041c0d490005588050104596000b071000344200101a0b5043c1d60000700b1000180d030b070600500e481c10405540d0314402c144c00340201e15071000e0400030103407401007910040c40700c1d0400f40140001c03a10040c1080d0103150500e070410001d968904100d400b1a000917400003007115050404503004400c1c0d4000078046420100c825a059501210990746100201da04100480d034500c41030342241d02409008200e50014401081e00c0d0b030095020b0849000f0300154134541164401c00c05403c81e107a40c009a034072048003000e1006140d4104013180d8068034200c00c128001800300407080b881d0103944030396800c640d0b602c03000030704034003498100302504003514805548079074980c58400000300b1100303074103d4980725040c40064110102e0241c2d005411a03502d0300a40518401c00440ea10400002080180b01c25041c410106480420080e0020718256840d603040703007414420054080d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 964002670 1250 964001420 964001429
    0x905010e04021603051b03030112030e010e0307050f040609050928050303541609020c150403030b1f1d0a0b07060b0f12070501080408270a 61
    0x24410f01c0300b4640c20050340301c0c0a0034540c05042242d00c4c3d140d00030705102c0381c0c00c034202540d1042c0004000000c00a04004603090b0581c80b980381c000c5940780140044a07181c003c00b940951651050000700040d007810307152100140f80142002c2081c503242c2c0356074025107206030b6080d02640e011014010410b02d2408a108241d4910340c0c13008000c0f10303030b0f4403050307501e000140c03064008080310407099030421a0740600103542da218040002d0162541840c041405a1742140b4841c200e4034162690388100000c1030050b0480402200964014101080c0c0c0009411864081c4c41a1040042d194004840640e07074a10039446542c0200300c150081041c04038442c0d84040c60390011400125001c28550814560340040310f100700d90f5010750100c03000045c01640c40e03030700400c40100009003980901c096504036000350f00c01a10251046e00f424014420031442c8000039010755000b0080910147d8807810107190080e00440c1402e0a14001e04426283d001c5542982c80c600005c06602c48001d0502880c0c0c0d40c000c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 964003920 1250 964002670 964002679
    0xb0c0309090c12101a0a09081615030e0303160309300903030c02010c06060b0a12061509030b040222020a1202031003020d021504171b0109060305190c0905010e 70
    0x6900d44060040040780c0e215907604d241d40b0204020880030b2141d03082d08000c180c048d04842c44a8444099211030700344500a11441546194041e00098040c1c0103100d9944400e0300190705e1665141c03143e90f014240181c1c04000c25440e5055100414240b08001c14800b90007085001000300800081450700c213052884000e0110800041010a81242e88409440d4080c20b010603c6403940c500040149060f0f0000d403c1d802008c00c04116055101c8814040c002c580c3d602004070545039402e4188403402d508413100002d2403900d0600c00034040b0710700180c10600c0074010300040a18041e01c3c250010000d02d4901d421540842d203504804e81c050140c0c455040d5811086155050128118049030701500010340903c0c1c0d800094400c544800a4504003000341c108029180d60300e48035400d42c0490760078078001440c0304c1c190901241000806240b004240145c407407026407032500600341c010300b80c01003500c00c01c44101030100a240006d402242c015048955800b03a416003484009402c0d0504240700783e014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 964005170 1250 964003920 964003951
    0x601140d0309170132010e0c041802040f181404150e0a1502040e0c160b07050702031b0406171b060c010603050601031205030f010b0c0309090c12 64
    0x842e40000a107400c0e030302c0607010151492a0042c525014141142c141603614440c000080140d210f0003c100140c4210240030b0314080e41d03946009481e0100c01e590540b084c020400c1304101c8040e42c00350240f0489200d00000d03043c00d03a116050950f81c80107a00c600041d040324504120031070642c4c45121018002e4406400d000d081546810101e641e40403180d00081d59140301440480310f00308058010f1582c02019040714020388002d01e0040c0d000b40c8501c103404103070703e008501e80007080313420f8032001c2c02540c641c0c1c0580f00c4540c5070b45c06100009020603091240400a039409030714140314012040c100803003d01c44a009410501040b0f845542c04004051012000c0560524012541c540c3e24a04a60324030031450399940000c03224455108100455132034488000b08105000c05c14504036402010a24111011028169084d00c01120340b5000350581900501039404284003a081081903e811281003003154000b2803c02d4605031030803c02441c01080b4007952520130f503541c507485100508c44020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 964006420 1250 964005170 964005173
    0x34030804150219050f09030724110c0906012d0f11070b213301050304020918030a030e0c0301020c0a0b0a0207080703030b0909070609030b060d0b090601140d 69
    0x2000070000c4041c3d82004000501d07080159141d02c00d81e80321100040564414640e5407025100d226410241c2e50109220050710084460207800020316403464000540001c1903400704215040c4001004107040c403c1500d000d1404041c08200030703046078075041d40e403c2e19825580010301126051502d13401041000c02603034881d8800030500c14121100261040d4071010802c00840c40c0305001c61541c0702c00e01c04801040040c100c3c42c040520400d0080210940790f455291031494900380020079140490810004600142071203015964082c000044440314415100c90b02c60031548140302280001307890b0078191000701400c2c011440e0420048008500d4400e40d9500f06071690604030000e460000b1050000300c40c40700c0c80c4c040320703840e40c5c0c4501c601d9610159403034068020910142400c3c004d180ba000001c00c032a07400503802058904540b1030034085840c1d9910100787c078600519454018040c580c0200000d074114906038099620071002e07040741e40c1485400f55001101030009445400314194010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 964007670 1250 964006420 964006447
    0xc0901050612090c090412091a091c14240609010e1b0a0503091509070909051f1e020403080a2d08070311040803340308041502 56
    0x507489418118070510341d40c1e60f024901d080c081e030400000d401c0000748003007100304200203480c0385840308140c403109040b07031f111044008513a68a80846480a200700807100c150715104541e24848248501c0d03004232182035179103480034074041a51308001036100811202c017a004804102850b41c1e1048924540ea281c000700003049460188684600b20301c504000ca04000c000c010004c0b82150354419a50740d4510651004100d6401155146c145000300000320182ca0740385400785004003020310041030744d54180360402006090241007213702c0d12a035603d001440e500c440100b80785480804000510201c1120800c228480ea69802070442d0300c100320510000740c000c0d0036240071004500d04804580410a00e0081d4007403000c4259001020a0848650660f404000b0512440b4155001c1c0320b40da01c0342002e00d00b240228064680c064100344900310300104444464000d1a80e180c9260003e20100c184060003154100d005900188041081005122402f80d60071802c0314001021854403d4004680 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 964008920 1250 964007670 964007677
    0xd0b010203091503090a0507270c140c03040905010b0912030310060c021c0c0503012430030305090105160c0209061908060103230316020a090509030901020c09010506 73
    0x300f90700c14012003c1501210100101c0000382e03400011200d0b11a21034110120701c018103d484554244002c400c034180f40170758000c482e0052481d031200d400d001a04412100d0540144c0424040e612082c1b0000560784441d0090034004d10880c480395598500f202d09001c4071121083e040b810305e07402002400f03c2c0c8641540200b0450700c0525040c400300c105440019002210030400c0c3d90703240307171084040301400200749611040f29000c030020403066281100c0c03021b40c0d0b04500c03618020100100400c122900ca10b0040c070003900c0000c40000a1440540c00c0d0041c40c1c24510b03015070002e43d680040200445091240c44c0e002858040004c5180140344001081d02140580090268070341401140e81a00c0744161401c41c041c8000044d040107444101d8140d580714244030070386050103049030720b003e10600c1c507001840c410300c01310103140b82c2400ba10742901d443c102500c4c1241c100d0192900050186d04c00e2103010b02925002c0c003d582e4500e08031000a02e060400040c851086a40c4001000241d444c50b088 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 964010170 1250 964008920 964008949
    0xe030d081f091d01090b1f0b12090c1909020c070f121205040b0a050a02010e19031403270a02090109230c04181803020303010312030203281503080d0b01020309 70
    0x203000200d074042c0c201e9800020748d80c068082a030000c40c1d411544d185c0d07103002c14070912021040b1800301a14074100120000154058645281c076082c00f440a1340e02900140003403124030381120401c0780c2d60346091b0380d00e03540c9510515803d441c800541082102e80101c80005440328a0a076081c1424080e45000a00c1a01e0070300e0240600001c92010440c000e4100c1c0869107419015102942c1d940b25807442c50301c0d00702608030002800c2007614046030825005032405900001041c41a0b05440c002101e80403c48100d041c142e4403892501390016600c250240e406001140000b060140004810003044400400c6000b094061401003000d003004100a9604455060003031025070466040f00c4401020007003100003040940a200340185a00040114100c901c01c1e84403450f41500603208608034001654200d4640036903d954030101c00100c3c1c640c0c07100241c112000030380003d8080c0f032640000400d6100f11224071010624410100b218801d1141c40402800554a800c0d064070000b8401c01c00c1000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 964011420 1250 964010170 964010191
    0x212a010509031504111c0b0a090c03060c020d030f020a21020d060906060e012a030504150801180204080703021908060103150c0e030d081f091d01090b 66
    0xc1c0e0315600c2c0e4040121a03030700c0900396410344040c01c150038810211740c3e202c083c2c64021045101d08100c0b03030600b41ca82898003600210301000607100c001c400c1000c1c1413142d45c03d031420280640040b000c603001f44100115004c03613030002c062040d40d84002401380c82103c0a18222680306000300320f50385402c203a00d40c0411140903071241c0d040c40c007070b10100c0083c059510094086403a101d000f049036803c0313034400d03420340c1c0d2580c0350050030001d40001182c8030751140d81ca4440c0382d2017030700340c0d0381d0800c2124241115403846400c2c40360a094031642400082c0c6a002d1002c0006070f900c0004004021038881c6d10082c0c048001d6096180904040c0c44c0765a4001e50310009002ea040d20b4104004405900012000f604402c13082c0c8406581d2414407014028410155004180c0783c031008044182c09603003107580404000c2c020300042200300c01d05460845000f080ca940c0d0f1000c3c1d030400305031040d407800354801600c2c00540006400e049211b0b0305034201108606050f5036803400c240c880126890f181069400320b0b9144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 964012670 1250 964011420 964011427
    0x30c010e0d0b0901110a05070c0b04121502071e1110050a0509030a0803040f030e0a0513090c08070609090e0607090b0a03140c0c2127212a0105 63
    0x83c555401003850114038103840782c0c04500249240c1d444030080010601138a0b200a04648a28204405116a100340107550104901c8000090400b890045034024034a100500b00009030711600e0a038440c01035007142022591403004200014501d144e0f030694400d4850030350800320880003800c4d502c2804002c405100d00841d0403200c6540801101e40a02c5e0b00c4026a91030b41800c1c5000040d0f40c0c80d0355403c402103001440e50311043e003000c4400c80101c580052071000b03600300c65483c80e0001d01403010191002340c03c49402044055080100500800c41c6a4850905514200016085a46030303c8203481c0c98214800f0b00c41840c1e40140050140c0b030410704e03120340d941c411420550080c8041c00c5044000c00306030080018000701076000c0d021511484003501c4040007070401f11042404040103444494506000052041000050241d04101d40c0c00c110a1700c00c80b80c20002d0070b0054040c0b029078588070640110300c140300c2c3c180b04100c20042c40030101c500302020051a2103800c4a41d036001c604101011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 964013920 1250 964012670 964012681
    0xd0c02061e0621010c050c0714010c0f030512010f14010206010e1b07170714060f040b1504050408090a0501090f030201031518060f08070b120403020f100506030c010e0d0b 75
    0x74459140f0b81e00700341000f000300b031110340406000340d0020030700702c009401441000104c10541c4c0b84400340c40d1805945400100a00380c2e40c460140300c2d410001d604004041c0490f415035000f46418074013900c000415045400d14001050034108002c0c2051811500f1260040082280318412203030044030008400040b205034001e00d503417500074004042c01604101049415190421004244190142d09041c15481d0584002d81c0c0c3d5130000d90311820341d621107000003004140c1556a02d90040304400d94043c0075040c2000040036681c065900740e8840c03400042014a91605040c40c0d80108000e00340b080b443d034901030150104000501c0040d05040d01c81249a8180c0c0f0084441e001400311041d000d850794404110200041529003e60140c41081410101c0c994000141c5da00803290f001d401c9615010001049100315007019004805510407501c00c1b80300080309210b690108070031030f4000580c61501608042c50540c0107115103050005080d1980081e803200c0480c581c60a401421a000a803a003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 964015170 1250 964013920 964013959
    0x2a070e0c070f08070206190e3d020c03100b04140c030705090627041a0d0204020c010f020a0512061e09040c15020312010e06030a1707080d0c02061e06 66
    0x86541002051190607417008107241c21100b44180c8070800e491274062400d41c90440c02019181b807030800d80c2150602c646880300c8544a42c01109281d8510503125200300d1030012a02e080da0000100401e591110500b022505140c4183c80c0003074040300000d0603030b00f00a18428103d1001a04840401800062040090310365030304941e940c1850f450f142c00354403480188000b11101d80195188030740c1c14903480c000300000300c500032201e00c48020052207902d513090b0b00308802944507070941c40e11740d500c0d60340030004a02c55101820139a603007500ca0f00e64514508666180840c00140031a01c203001240b804640e12400d81d00c2c051500c14262400700c10340d20350f41062002c0307400c642e0218003031072034612584102650110146c628034000002018250340c0712105918000800c882c0d03a174265200480c11008208200c54000300e085000300c12904e010441d80b03424001e030f840240c8818002d9210b14246c811240e041040355401240e19080300030301c0301442841040304001500040c859001808040c1c0360340c80 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 964016420 1250 964015170 964015177
    0xc03051303052512080610020120130b04090615021203040803060d14010e0c120a0201030207080c060408180603060d080c010b040203040b0103020109050111060109022a070e0c070f08070206 83
    0x7002041e10b0b001603204200103120350b00491b03000340a851000144c500242c014010b410b2241c9c2100e2038003410b021402c0040000303402c216150005002c0840000801d071040700014000f82407019008160103080284400d405c491001c1c2410865010440807a041d8190300187c0390840e41c000c1c1c041c0d59984510002510314041c5000242c2002e071080409216403c055108015420050b804c1e6954004641c04120001504a980c8407080c3c10044001006600ca40c3c02008198032071100c0500346681e900d070305450580101d034211850407000510086e00030310059080b820500840714280345181c41e001007018049400e4004062280204807544461420340245800200240c070840d143e1404c2c0c02d241403404170a2100341c1c04602c0c10780003c50194407c8400c1921101c061000340b01c00d0f40390805036002588040060400612484083d0070048808840e45204e0511500180903103802d20807000c0080314094490352000c07500b005503500007240c1c103108030030968210110544502c003d00100d2124031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 964017670 1250 964016420 964016423
    0xc060b040203150a0f030f021215130c0b09010509130b03030a081009020405090f040501061d090c0919050c2229071b030804090c030513030525 63
    0x14004010060501d000700070710f1025010481d105070249035280c42a580c3e00c4c03c0c50001900320110103401c03001600b0846045d0040c111054100e9803440d000074800d000c809019110142c230b07028064514000d04c00080c007101d0181041c84041c9203061174000002c2d1151040c07100d410f002e1a41d8440b400c060786c03030507481940c9190019003a01c3d41c4a051180081c050241140d442d55800758040300803c40c90054030070f8500359072004d001d136509611805004908000002c00459640d13480300004034006070b80e0103e8003224910400c828240c2d0070180c0025040410300580f450042e580c180c2003100d20707026542070300704460318080000f42d03a490700ca80440b210f104801d441e000240e00300034810400403440748000200c0d40d0342814100d070011a0600c40f01c0c540840f0310f1481e0071042c18080c20b40420320f003000f405c4070120400381400701d41755070360f603a0300094000e03502c100c002c0c2d03590300341100405400d4014140e00407092560703091122103994000d4942d010f1503100d84c00011100c051900b400e91071403103550169 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 964018920 1250 964017670 964017679
    0x415030c05270d0c060e3303090a08070308040614040302190c0801060b07021005090904060b041415120f0604080c0703050708010209010914030c010f031e14010b030708070c060b 78
    0x11501c074030303003e8060403050031000e0049656140700c7c000300050701c12066000b4107008840e500c02c3e2070305909240541018201800900461345000002002c800c02081c680e44030352074002c0c440c6440e041080880b0b45a01c41d503c40002060b0030040040e901090720b081c0c4800000c82880e4541d40783c1041c0741242c0c80307904004419881c1410204200500c034000d4261203108440d0002c465444c12821200d5000b0100000e0300454180301150025055800000900201500001d4880c02c82040c0c0022074000b59803090300c020b5902c00c003419a050902442c000f03000b1110007400020003c04205036100f4008202425001d008071394100e01c0719041c0000e400031138019048880300c58851940c3c60003940460356943c003007003060320001424084c0d400d010310f441c000200030305003050290006581c5c00311103240303108c05c156440105003500c0c8082c44070701c0d043d8280d8846c0040d103103410301e04800600702d040c0c00a12039064180b04005109038042c08040d80048545022680d4948514080003e0a03d002015501 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 964020170 1250 964018920 964018943
    0x12060305152a090d08070501020714060705090319060b060307050408100507120b040605060c0a120c021f1205010e0603011b17061201020415030c05270d 67
    0x1540c00d100c0c040e00420601c44580100c80701c840309011180703003184240b129400d0500c8000781d00d14102c00c0c5200654001c0c9156440d0510580c0e545089a00c1404125184d840d0704c0411600320f502048025030020030350401c1450013407002d000030756074100303034070303c00184022160301008200550b001044c4011020f0801512402e02c01006040d80d0441e00510103e0320a010000c0a18840303070040c18020b2415407922018074003c0305828000e040d904a040e40c0064480c0342c000760360f4641000405108401c2c8000e00b81d4140b56140c20000041c40306802c00070031a403101140090f0351003201c940c0c44e00701c0a5000d265803828010003664080004204000c4d207904d800000192110241225481408100d008205030b801035910100b61001e800088400500b4456100000ba0075006800f074100d80c0040c00810140d9411071346a082e6803044c1c000d501d610b0409000f8100303181d0140a00310419400b800d220381420304c200c145202c490592001c2100b11803102c28012283e4031464110b00d4442d8101d03045944 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 964021420 1250 964020170 964020193
    0x5070303120c080105060901320d14010303051903060e0c09100206040c1404060b0a03021c050105090c071b03030806010f0507050316020a08010603231c12060305 71
    0xe2070711240c444000c071038103003180301040512507036100741685d000a0072030341418072000044504820710403a03460b03000c0c0c10b01c01d65001440140080d030903407120490784c29620808400040c1c1550a84032a900d214202103006100294006082d60f10310456020302d200100e180510480280c8125030158046489070804d029410007580c004104061080e60f045510203100182260703200c00c01c0324043d084240c2c1034410300c89400c00400c103c0141c5001003020941d1038684508284070351007a180321010076030014145441135805440c2c105d518400001c200000e48c902000f042c030310500100070711a030960000d01d0004116801038061300d000c180070a22445141c80346405030515405942c024080b60004014810300f6205104071042254008003031420110120b0540425001c224001c0347c0c0410f0f020700101c0e002d03200341702d094010740c01112111310345c0c050b513620000c002b1007407101400e00c1d402c4001040e402030810b0391101041d114928041c000740f0303400e41d41c0000a0103590801007090140c41000c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 964022670 1250 964021420 964021427
    0x171b0a03080922090605013218091605190501050703050d02070c240c02091008060c280f08061f05030a050c0403030c031101140c03071d0102030702090405070305070303 74
    0x844d07403207041c0422107641ca40601c4040d80c80c4000c088144015480040003200b01d400800701d240f00da024000d10008019040380e46440361003140d4058082d44400d2105a19808000b00e1900401040d6070f0125000d1000303ca0820b50800b5015950602c00c0008042c000c040c8208111a45454030400c1103480e03450a1800d00802c003c01d100302d020502e060607840300362052504214180c648981c03030351281200c0036424440c90b00d2004041e202c503403480c3d0b0400216070f0428001e19210380348001c0c641c1e9803100710040307407070602c152403070b10030050300318418005c0c3d00b07039046000c0d18040103050a00149035503401001401c29036207220f0780c01030105400c06c0b00041d25001030186000d61007400091202e80d49042290201d40981c0c0f00140c006440f4485602c040f0340103d0b81d660400c107512002240074050810300d520307450019180140c06110000400428681c0042c07054110100e00798421003280450000030341e43d01682d2800b902c0741200c04003240402608004030340c011903209054036401070781e904014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 964023920 1250 964022670 964022681
    0xe090103061505220b030a060c09060311030f040b0a0603020301020a050406170f060603040f05070303090314120f0a020c10200a050703140c0406171b0a03080922 71
    0xb901c02103004004242450020100d4000d543c000301c10100325821403034010302a011941c0c00c140c06000e01d030108800b28000c1d010710551070115440e43c922a52600798010120354084c18443c40c01c0c213050003030050851005e5102508183c201d0596034113034682245070401844140d2000794503610004109001a401101400c00c850042d111091005400384920b103189600300d402803d214104400609945071030006190403034050003500325500e0545d40d03010f01d403092980040d0040b4400305410801c209060401512140620b00a0710b5181c0709041c0300140ca00a540034109071240111300000c00300e20811030840c003907a004000c140100d04d101009480344034080c5017842c0740002c009451000c1900010900e0140303a01000829030740d4595100c3c08081a094107520081d0f01810340e144a0580e210300501c4003600c010703601c203141d980310314107042c6c40c1c0180c045141c1520ba140a004220360b54450300c00c0c008a0360440001c558030341206001403042c0110120005c6058801c09060181240341d5005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 964025170 1250 964023920 964023941
    0x306060c0b0720060711160302060703090b0408010b1017010302040e0f010f0608160b070803190e0606010e01170105090c0c1f0b0a03020f01030f23190c080c0a0e09010306 75
    0x850b561b401074650b503241c81d052004410b001e0380c044500d0420050404000030030321103020786001000f0780d03120010841190310503400701007030307039101c00d441d80c018607010408103415826410000c203190031400040024003414030001c0e10680e0342e1054160000c1c401d104240820354500020442c82041711403d800510780c0d8040d0304010b00c01e45203400c480c4840311000009a41c807810312242014080c1d6034000e410740c001020043c4005240c01040100000c60142810f1000c2c40c0c0003038940c502e0003000040090342c1c0089200e0404c80d400e1015800008035100140c150b6805588200c1a981d6440092a0620600f192a40d0034410051901412400d0300444021152040350911410707804100b042100d02075800081c1d4003c066000002e00c642c025406450701449010010440090500c0d0b0300000c074460121a602c1b201c5c808040020500007040344040c02c00c500301042042d241541d0004040170002481510750403800075081102501980c03122002050040445280e5038482c0342280113400040308 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 964026420 1250 964025170 964025177
    0xf29040612032d0914060904020a02060402010807050438070507080f01110a030903020c1309110303040e0f09030c061008160b0d110d05010b190306060c0b07200607 72
    0x1a83c460707880e0207440007207882019030340c40e010b560425540025000808580e590303c00300c2080400702644490010342281c604036005001e0358a0240005400c50038002d00c0e441c1088810441800000c98451503508000f0302852151844200c1d8260740d064100d100d40016400f44000c60b1040401500017240d0058400700c106480001401d00305950a03907001840e4550b5000c820300055413a14880e81c040795500d80a441100e090f020207501155600c40400d0107106441d0b1212800c106104221007007000310340050740194035252410540c00300900000e070030960600c038001e011503405581003054a808062560941c0c0e42400e000c440c00405d21510f108600541c00340d10207000e090949a0250b42c21a0f00b8084501c1c9008a00e4035548014060106c405030603440a200c2099000c8640c41058082d01c9600801d075070740ca1452503500c5100d002841c0140416080440501c150307540010441c001c60b602ca0342106141d260080151094801e050b00c640300001c5603109005284000216203010340c030340341c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 964027670 1250 964026420 964026467
    0x70302100816031a090c190507080702011404030c24030207050c0907022d0127170403050a0f0b07030e1911060703120f2904061203 58
    0x15401d03204040111401c11804202610300500e590098200d07900c2c18648041082c000611540010013282084d141601911310110705c41c21200c603a01501010401d41d030800c00e080c90440d5a42c1c4800b48100a0001e0403c182c00c0070f8001c24a400c002941c0155178400b100108683e121110640584458020f03840f0820034004000542800384c402c540500341c1010107031020812402c10310418980140c051000c52090995600e03114001c507000c0740380f50704281101c0d840502d0f00400329003075038695540103c080480e5202101040759458101140951200b4424600b2038201891407040c05980d002521301e002e45150030080145003072814070414802c0445c0c25032500c90007021000c07903030b141d844101507501c48242c42c40412030140300b00410b14070488003607444500c07480c0850035a400200c0c0845c04140c1c0c02041f65021001401103c010b009803c00c01c01600203081c06117012041e1a071400d0100314400074041000ea00e694104801402c100c1240c0710040c0064074000304151002810824180c0948 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 964028776 1106 964027670 964027699
    0x7050c01170f06012a0221030a1202120f06090f07020a030819060303120e030a05090f0117070e180106020a08030a061d07110c030304150306090e070302 67
    0x1c2116004480441c414420460441c5210b80c071110180356100c0c7c14000004165601c2e103070f96252000450004a02e0100244070740c081d80e0001407400010002e00c08c00c2c80e90068015041918414202d03610f400c04c5040d0680c00340c0303002006070805552000030074407985801e508204180a2a03401176139081080088030002c0d80220085443c0003902e02c0480c0e09803145652518144c40a18a0700072038a0009000c0c3c4501820188a410807040d00241644140107410010380c00021012582c284000064400c029080d078980c0b10340b001004074800280c045115504a40e420340050042c030b43d0666500c441c41d000200343d0043c2c1592050006440c04245151414051904040d100b690034031240042034000c0508580c0015840000c2c1010142c500004440c21140c900004804485440004070b01a10140e07000038111824034043e2500328201140c0f203811a40308640896036400071 = true := by decide +kernel

theorem cover : BRFrame.Cov 963848920 964028776 := by
  have h0 := BRFrame.cov_init 963848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 963848920 ≤ n) (h2 : n < 964028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
