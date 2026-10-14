-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2209
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:59:55.161759+00:00
-- url     : https://prove2.me/submissions/b517f5a7-0ff2-41b6-a4f8-0bb63110db4e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 397122302 ≤ n < 397302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 397123552 1250 397122302 397122337
    0x20405100c2006070b09070501090e010e0601051c051504181718060c010e060c13051003091a06040516050f031315050a0b09160c03050903190b011208 66
    0x700000f803a5000e001005001006103c1c1005886503001440f103060720800d890b0b050324030781c1c1c031160346264034002d001d28541c08140d2408250503500583c040c240c040301c0c01d2180002c90302000422011168226910350320381d0010b95400c044c0303041922030204410140d010200b4000c8498440b501952170510300880541800249500c0440308404010001c41005000390750726400c0355a070742c0c060161071103450349901400001c60801d64a980481c0c48040d2082c0140031400c5c034102c00c124580d403404240806264840f0f601d440001c0103404031000300c60806812455500307044062004546000349145100000c82444858030350700728040d10015026058082d0b0350342d890f506507851159040e407000340401c0058161600308007040d00618803030b18400604010050802c420416051402c3d24640301d140c0b079000042505920400440650900904003c3c1c82d00502c40701181c905076080c1e8402c1c12000700e41182c0c4041142c580b030782c9801005000c6885100d80a40d885072003282c0b04101c104498003409 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 397124802 1250 397123552 397123613
    0x929061306050a06120608060907150201020906040b1b030405010c0602160f0506150609061602041104080309030c030f1c090302030109060f1b09060c080405040f020405100c 76
    0x12038114801400e4082c2c43c1120443d41c41038054401071440c091001800e00f00340d000300300410300084241c82051000010300e080c2d40750102a00400e03a01015610440d502080141071607103842004000030100b0012695840c0a4099401c1c40d20b00368842d16031446e081000100030f240c1e8020148044c15400a41c0181d880305118414a60340403407801c0180b600031112160300c107000001c9180381c4a101c20204282c0549003a000b04000c0341b25040c85164804014000d0390001104111403003e814405440010b2003a55600a00c001d5009036020305410303400001d0704010340c20f0501801100450035001410700f05d50352080035840d90b8a840001a0030b610b4402804860380c0320b440035000558018000f04042c1c0010308103040605441c1e0170401c01e85080105090380c0c011643c8100301c20206555404030390a040140803129040a00015600d07003a041c4004541a600e40c41640d00904030920700594540c5044107000105089080c0182844291141d00d0301003010091581140095540c07203031020a03c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 397126052 1250 397124802 397124839
    0xb0d150b0324040633210e070b1b070b0405040c1707030c0f0f02150a091b0504150308030114120307050a211d06070503030901092906 59
    0xa01c640041d0b0b00130308104c80001d217400251104c05c01e100481106101c6141c02005400001200f08800350010786031100504140081c0c21500c000c107410000d01095103243d0411951800c0d11580055112400c009100e40780e62032008034070766540c528000907110f030324580003400706203004900c11180a1601c980a81ca080ca00c0796002107076292050061a800d4285108002e005000e0344541c0c001280261521100080c090441c42802215550040c0140c1c09464900b2807041b13000341126103281d07140d1365401300241040001c018120030f0303002c0480740c103071900017008241c038480c0014825605442d081800440d0714902100d0540751781c03004030000d040d00400807400b40034841c90812128000402d15000b0000b000c140b4040190180d9110001403000e00c810483c6101d90a20810104103050840c5007540700013030b09002c28a1008241c6ca007007101c41e07240e2500b035a10803120300c42281d640300065000c000c40c2c1c0100c80d0700d11754402d0b20411418a81c0c0c0000d40840800740200c0e10841000e25141d03030031213 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 397127302 1250 397126052 397126111
    0x102060604020717032a120402010e0111150f070906120504021c0f0c060f0509010c0516150f020c150d0b211009110d0812010b0d150b03 60
    0x4c0d2022041507891600c0034940d0030210802642600c90500039a01c411030200c0242600e01070302c540d00404025866660041d1140740c8500092414410501c006200c1c00710244240c0c001102c1c200a503c120780391005c07520038a014001d01000900803401c40520034a41e2020540042c51803c01c40065941c0b200e000050300f0060064074200320089807668041000b140d03502c00d15200c0d01c2680f1007001180c8404064400150680940300011740c01c1c4a0449190300c11410304407414014400d6403900e5409005001d801d4400e41c0201c40718010900003a039500d54454418a8080010b00c00381c0414809e66001401c141b01100c40034001c40303000b20303204c807014071180e0150341d50010040c0b1041c04440c4845a214400790a000d00f409076010340e100410321b01085010342585154031140403030402141d1b80c100f142c070800b4040103640000302400340342201185040c02601138814448156210788141054405a0f051100104015941d100040003010307a28815290084100c1c0c3d03d042002c0031440c08810030b036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 397128552 1250 397127302 397127333
    0x1602030703080c090a1205010e011a060d0e0109120207060f091401051303030906031a03101d0307060b0901051f1b020307120b16020d1b020409030206010602011a01020606040207 78
    0x629040c00140a18050500c0305284c7e10840013031120100d01d1002c14200d5844c85010a0062a050900001c515107400140030443e445080000d0344681000070f07a086a160060441d40340d202d401840c00c00ea40c04200d140020070481c900052801d10300c4000919440d00c1c0c0c842c5403401b141640030300e2003e83c06002561014418034007000506a580d0400030580d003018842e900c00b0074645500c0c9d40482c60510164129107601400400361141c2c11a000c00003484012404150081640d0800752415000c0c8008c12001d8028807003c00c111038120100690024183c0c0700c188247c004000d0141000c4110701c41201a03111403c1120f402c0c05002108600b4070610100203615014901d00442c084003000190900140030b120200215540ea4000d586540c0f88901010b0169001c03419503500144590662403030500a01800340302849180c2c00309041e60441c1c10114096040f150050240d04d50903c80d1000d40e118403070741c0f030881817603040020351902400340c8894003c2e030700000d0b00c0c02070000c8038045c207608 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 397129802 1250 397128552 397128559
    0x603090a0803100b07120e030309032802091009060e07080f0415020408011a010512010b0708070b090615010e0a0521031603020c0f1003050a0e010501120b1602030703080c09 76
    0x840507a03240206148071b001020038080f4107101c110f8075280c2400000d591103a6070160003070428a0440c1c044070440341140520705820101c0100a00c0140c40d4008070350700038854140e598080c04c1c18000e5400c00e58980303800c0314450551440c200010250300c20311640c1c20440340c80e02c10384251a00d00746030741c868211801c8070100c40c1c00042d00068500c01507110388100400820080401c1c000b8900445203481091030a0107010010001480407102c1140104803d034030034200300e460019580d40d4202511130031618000d164010004010091048080300c2032081e01c00d103010340f24800d078000015286101c038020a402540116424441e045458031002c00c0b4606013030440780c80380a003140e0a00301e003008080407401402003a40d2140f840c24003c1c1501a01c0e4030040c418142141d40000403801400002c0c80300c40c040d604d440c0002000034080c03003018041c146640d01c8503501000703030800400c0c2d018068955a03140c861004440007080e0b02000740c40301c0d1130b810315180410352a22030300b1040e14091118001d0f170 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 397131052 1250 397129802 397129807
    0x260301030b060a0806070509120304030b0408030a0b041107020102190825140a1e0c090207110d110a050901050907030525020d080f0f01170a05071805060603090a0803100b 75
    0x5140760890040c0412080440c0c07010180c2700c60b0503459440340074501c401010412154042000200c006020b0b5510140d07203c0001030300020070303001900b9908d040c4080d124005000400c035040d075a0510107807105000030005540f90b2689980c65100701d10842d0302c3d16443d4004210a808050078100718440c0703890704030b00c07810154185600c465450f0003541c00101daa03016281c1180e0b481f090700e020040109504500300e01c0c2c0062825403894040d520984085035001e1a00351031035100e50300c40a5154045000d160700c1e560785400802809044541d980242d482841038000401032941d922040c0e40d8082c1c018640860700c2d840e40014140001102d60031080d16209403280040c809900040c01d040903440d56079020f0540e00d03100c0c83c18a0b00c0c0000d0720700c044000c00e0b010060244000b000c0400354050106012038110040a81f6150704099281d000211b081003140c80c519902c81660140c41e0700013000320f826910303608000419554400e2001c800429180300440080c80003d4101103c1e8010f000b142401355 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 397132302 1250 397131052 397131061
    0x10824040f0218010305220b061503071707020111030c07030306030f060b040c03092121061d011d090a080703050304061505061b0f010603030c260301030b060a0806 72
    0x7504211030803240c00170b85400d001504000b0700c2040d20713800c00410401c48052510300e03110300f24100d400900450300840b04044003409030503454015841030f070b011340d44c201d4000c0464034100c91510303028001004580c100005d900c1e40c42c3e85802200c1d0000c5010002940c3d03020186420b90143c8019170000d4031000d102c80c921021b00c44640c108641050781120104030003125240c040c0c0841d003050384040c2c0200d0b0418000011345001c500c038009090b449050488810504d1524140300c2c0500350405c608068641e0360401800403000a004405800100c20300d01a604100710304221518100341d03e9040700e4030402041c075142c001e112000c0e015810001060365501c190402800c1740e0f0042e80d04440e06860b2588991100403401007801c02d5410051031035280001c0386402c0c28004a043c040b2040c5030145001501c91104240702e4031000714880e8641a40492131030421060b140700a0300ca00e4550300c174a078525400e00f102802101d0649922550100054031a030740071804c040c0032900a224103220f898140b2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 397133552 1250 397132302 397132327
    0x10b060c0f100915050a090b0901090201021009050c15070803040b041b0302010f030b04060f081f05060907030906020919091a03030711010c2f010824040f02 69
    0x8074902103050100c034480c014108400302100c1ca04038018026210920388116a022203401030740c2c010032200d0b00822003a00380d445034003600806859103200d581d5680789038011940c06200a001d103041108c410060a2265250180c65518080003944100d071a054010901d45e41d4600340c5001d2a0031002154480c9083e10349032104800580d4140c0b059048010490285180441c203801660341c182c0d42c00440e07071a02203056000c2d1015804040d803254440c4004525440c00b920f243c001410881c00030140c810342c8030440c41245d421f210340c59101500700b00c10401240c0342c0c1c500c1c0f10341004061a0009614ac2c140c10460020f00030104a1948101c1d40641ca20684040081110958000300070410152074844c428245156603500204d030950070078401c02d400300c1ca0700300d0340d026000810304006000c8190340c1d8a01d4508010a0982e05480c034070705807005460740c1031800c1a6001e000a09090885090030010018021405d80315403428010801503102c00740c0715504110074a0750184015510358140b41c508 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 397134802 1250 397133552 397133563
    0x6070c0806010f0b130b03072102030f060303040f0311150a03050103170a0206010504020c0f0a140d0f050d0e01020d091505070305010e040f050c1f030e030f0a11010b060c 75
    0x5080160a8205010941a0b03488040f00d07450031411205e11440d61914040050075000101050103006e15030220740d680300b0210302c41d500c621315030100060307481c9000d0804103141c0360040c0001d40aa8410700080c80201c1c140303c15103040d282c102e08000001a1a41d0000717041110840c010314460001165040700c80750150082d9042ea0710900e592000a001e14a00b101d0b14090b1441c29401a40000c00401503824142d00030001a50340360196407209100001c0245411000401283e4210507214085510038050007000500f2880d481d14040e024440000140b0f240907500d60301da0415650543c04a032800250304030364414640b01d805025000040c11b00018090582e21071620301750906000a0a4900c03920605050301c2c00d10481c80180d03190380d1603109424030b142008569904c0303000a4a40c850380d6540d9400d5041e01541c0107186003024050008050341c0d070910181d903650b403003409500079084208054900511305858030680c2c0d85000b42441c4e0240052032684c1d900041c000911102e190404961b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 397136052 1250 397134802 397134809
    0x7141009051b190509090712230102090901060f090f17010608030306060f0a0e181f0b1b010b1206070f0e130908070b090f12071101080606070c080601 66
    0x700c0c14140c02c40014014004403e5000405145003000300340000d190102e01e1a421001c9002280c0c28185c0310000103d08a00e080b0050b60039020f8040304c4102c40200c01e000610114002000f9803c100c1400c011900c0d008042c0070340b4051020920702d440003107118030020001480426112006c465480c80c85100e044600c10400031a5401c01c000414580700c00005c40340030319805013140b8600500b0200301d90b41500b003012041c007008010100d40074190b0721401e5041000c594002c0d040a0740c203100d41c0108400d180202100740480a6003c1041940303c0c8400341c81e28481140000f03452030311899115401040310100c02c0340e0201e4070711002c181908000505522170761039922150448429800c06494459600001c0303a40b0241c8019180c034800030642005041034450f01d1001d0800316559904c010141044510441c2a4010601805104000c02066500084c0e01d121039152a44988940c0e030110035143c07a00341400100d8000c00c03003039100c100031201a603030003040389030a00b40c48014040d01e9010130b21 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 397137302 1250 397136052 397136083
    0xc0c061103011505040f030308100305010204090213060f02280203010e01091a040b010504020d0e06040f0c0b2505070320010e090606180406050402220f0b0714100905 73
    0x901c04203d85000b0400c50b01a10b0f44112407500d030030724507a0704559010004200074030301c9080c18000000590300340040c0c405421002c20141e201c1840c0380c170004044003540d03c40c1c82084509170090b80650f80100b15207102c015402d01c001c28440c6000e85503201040d05c1d1900a40547ca090080c0110b8603042d0710444a191040c80c00c240140d450b024117000c542c2040e603000e01040521401008249800c0d401886c00074800d0b440492103034013103507600382084001c44090b0b031001c080c561b03d00200305140c6001000f8002c5065400e0030700030302043e4030540391000d540ca900150050322041c030a003c8100120030085602c0043c10074000401c2070300c0c11030101d4440d41d00d07000c1924a0805075030352405c010014841c4502400850800030a4050401c2000700404c035190480d0752040d000c83c503034540c1e00082c100e2a86d003090700b00860101000d11400c4540581c0802c440b00039000040c8580741000c0c040f680c1080d04200403041c0d40c1300c151070307180c20140c2c0300e5500d500d86440c04a00c40d08110011841044400c00d01d03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 397138552 1250 397137302 397137329
    0xf0519030e16230409031b030c0c03030c020109060201150311060405030d1e0206061804021503010b071401020403110909250e0702120910050c122203020d060c0c06110301 75
    0x1041804192080e46400038041800c450310710ba28101520700c031550123402032418080c4014142c40e070001c6030165400990000702070581202c01d650f0071080c2000207000c188020404200810940d6850080d1400010031000220580700301e9555500700ba00c0180200400342c0b41202a5610090040095142410140c90710f0b41c1c959032000c0e00100d5440c0c420300020f03080c0704411400031520907160a0007041264016102d000300d4035a400a0030145010340341281078165242c1c00380c00e240c40241c85071440ca0b245170f030040100740001210142d03214800c01c0244c4222a103501d802c52094104031501c0025081c00c07985220903403007a81d51036040030840c1c00c0f590032043c4e0358807031140c03c130386071540000072405120041107000e8031170a044541c0c199003500d61800c1820000320308919400d06100c0c180c0741c000aa00460129009200040c80c1b6050070000030891400c94603503400300b0b9100b4840100600f18513561051010000c2c05403403032100941e0301c05030410420800402c0013030755420a0250850407450f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 397139802 1250 397138552 397138619
    0xf03031609080607030b0d0b0403081807050307090e1009032003090d083004050106051f03020f0403020415180905070b0f12010305010c0f0519030e16 66
    0x8065850a44200b0000b9128a42c1e540714140c01500e203840c6140c0e0445041020100440c03c0036941c103005a203e640c40740c5c81c608080402c02080c7c41c0703000c1c10307000c50740002004000b66a00020101c0c2158162100400c20300c0744130200900b00040e008280b40100c0c00c107003c0070101980040c42c41d11003840490f42112180e125107909130b80e4040d610303141350005051446000450f903a41301900c01b801107904141c00750f0807000c00040302840909140140045208184001c200d028082c0c00081c0609461000114000302000c1d45110305d507001980c1416400160f03110801542021503008e10b4018005021480000b400c800180340144980104a0042d100e08440a02c240c0545000c07141c100c03000b06840d40c00c1c405d105646601161240002c90b40030082d0342d4110310741405c200c0c025402100005410000003501810801502c0c030840c1c1045001c10a62050310105451006060710a10740051560203180e115890b207814585a0004020045070000d2038842c2911280040e05034041200c105025 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 397141052 1250 397139802 397139807
    0x617150a020a05070201030f020d14010510110d080411061c0509070501090515070b010b030106030c02011e05040f05030c0f010b1c0813030b0f01060f0807140c010603050f030316 78
    0x2d0394441100041040041002640c8243c001c8000e8a0b107583c0010301d00000303018481d0440381441c0e00313000407104800041055150429059807025168100641500b541c8040f0707035141e4500414407020f01480001107802e202c25001460403060010305100d90320b0402c0b10311013002e0002150503140c0e4500305400208800004601c1c04110342d410b0311180c1c441800d200c100800c4400010000350700e02c105011030070201c2c2154070428001e1003000900c0750f80c3c3d41481d0009041c0c4495003000030a40e8105608002c01450b4044100401c81222000041c9038445251501d0b65108007200580790313102c04160300c00158004500401d094201600811000c00a2002d001c2c0f844420310b4014480c04600c0c040a01140c0c8601c000c0840d13407201084100305070f490380d9401200c40025100030300c0c00c41c038a000610030780e60400480744030000c080c1080308551a080340000c007401082002d9828120010480100344202500410b0181d903122042c0c44184024015099484d0404c55610541c085084c844048250 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 397142302 1250 397141052 397141057
    0x603090b090f071a0c0a031106010e0f0402090a0e010c050306040617060103060c0207031e03080a0b0a03021302091c0201081003080306010513030b0702161d040b0a0617150a02 77
    0x20307004000f401e9000d282500401d0400384d011412010408104a8201008070601420b41c205100703445602c0c440c80209081854020141c0128102640440600c00700c5016203000d503502c1031781100d81d1949942c0d60720f40500541a040b01101d840d40c02d2030b140307810190f040302c0514402c07007050307804024240c3c0e210365602c01015540030b29034640d0840030060000c038001d40c0010112120350700403242901c0d0b83c0d90b55841c0032a0038130351200c043d5000402c2071003059802290290070290018003440084488000501680d45c50b2100030301c03590000001c0e459954003901554045c00700100b9071102e107a0000c02d2811003503140c0400301e00155031a0005a180c030a0f032174000d804d482c4c10000c510304650700d0303600542e000d500c0f5114451800c45c507044d001001501141a180c03045205502810014001c501220943d454503005800b11807441840d098a90300c1030349030241e20581110a036401034540d03520006c01400e007908200181c848030307210403006d00000580d01d803110781000700c82181070340c551405d0380890 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 397143552 1250 397142302 397142323
    0x6050d1a0703020708190212030a0501061722050709020d020702090a1107170906030703020a03110a0f0c020613080d020606032109041512020a0905070f081008070603090b09 76
    0x9860038806c10000884000c1c800c0258030340c41c0100c03032410000201020b545d81048803014141b58454005001040d840380c0801b104456480359034105003401550790000710700f0403d0f46440041810b90290600004004410007070003010000c550743c86201d450b00b00a544642010303402070303004801061241c02148140c565101003c40528106031007984c40303203048040d40d0315001c201c01301484145080e6480100a50141d01c0d00d80300180e550400070070160540c1ca09411071107940348240505000c168211805a4101c0d00c5882e150280044520010f200c6006019011101511030080810038580001c2e03102440c5485030201e410580d0cc44040603658140060320710b800c0c40c44288204d80c407126a001400c4250002840800c898449141002c0100d1981d8840a00180707045410009c1d800c0407060b201c040c084a036014003440c9042c03c40a4450122400d4060400c00319500013a5425175410403203000c1e005003001d581400b640c43d030006014020140045d1410351680000c2030905000080d1302164 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 397144802 1250 397143552 397143563
    0x90a050f0d05030c1c0c050301150e011d030f01020f040602070b0f120603100507030c091d0c071b0f051e030c090a0b0d0506070f0206010e06040f06050d1a07030207 72
    0x43d507640200d04182600700200800740d402c9081da002d42c0300c40c0302d0b00071040032070325540c2c070f094136036140c9442c407109100d21001d1041030080980010900366482000054400740c40038405200f0600300c0c0110b17140600b00500d08040d94404540000040c81020044c01121056400c88000d15160342c1050014801e10045440c01141000002c0e03540f1801d1041a91001d4010155600d03c400d140102041d21402c5408600117981d45140c591855041810036028010016420010346181d02e20a02070400c081d040d10410a00880c41c2c00400010001041d1440c81c1c84183c0c14156541d5020711368103804a005441c41000381440c50420b13401d0388a91224070004c02001044a004800103014003024060090901310b0380b2142d0b940301c681c8562042c084a01d1203100280b01d9480c0c40b100042031040302426138021900210010401182c501d11019001007040740d000070b00c0705900c24060010025903121030740151000c2c21510500c0251042841c4030b50ba070361000001c694840004400301c0c801c000c0300400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 397146052 1250 397144802 397144807
    0x1c03020d020718091e0c06091e091d03040902121302060a0804061b0504051f080403300b0f1903030e030a061805010f1104030305031e090a050f0d05 65
    0x6100e1442c0e00100281401940d010b100307401c0d50141520210000c0c04207641140d05198100b04072603210088ea8014400205e4040321545d401c185042c00408a11850a50a895051085e00400c100c00c0e10700c0038100741e5045030380e01d9595070204006908075813211139054031000c000541301302a0807075128125500400712860f2090301d020a50f9503900c0a00280c9850342d46040c0902d00c0c2c2c003420f81e00c8468038900d4488076140c5107002c041100303c0311550802c1c84540f078540c1600800f6a00b192059400992604029070f00d2402a640800c100c0400981030070105590b9000460360500703607001c00d01c5001d0a940c003451988090091103040014500c038a00d00c00800780041011910031036a5401c41840201500e480d5062500e9a4060f2035460407074226029800350441d007040000d209070301400194010611190711804021001030045101c05401c0c804000006021001090f1000136241c0301e0703140313481c020304001094581c1c561080303e04a64a1107640c10407d8a81070014000840403070b607580c1c507072 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 397147302 1250 397146052 397146089
    0x12020d060e07090f021e090f061c060603051603060303020c040c020c0402120117010905101d060405030c0d0816030b06070c03240e0c06181c03020d0207 67
    0xe0841c8030191103580224800455141010301072400c60190300000503840d5030241c440d40700d04100c5da82c00700910980801a40c0d541e5103400c50004500c8208403650707030312a40f1900f40f0401c0110450f032004a84d51424001140e22074155000d98000c1c0301c1c2c0481075035040000307281a4201c402d10b000190169110b90030b0f00717031a440e09400001030895244142c4440007284004078050782c0041c1d14441d040e000072001442021080260f18008001d0710000b8085204a5200d660311104040c2a41d9112500c0c1c41010640040c0e898040e00c11100c801e00f1600c00b13241c01e0030019101c1e00300101100c01c1d4001c04104d403100c4c52190200c40d004140c00701d802000c0c03000c5150280c008100900d0306a0f0800000d0141d07901141aa0aa1000860007000601c0044544607e4542217418019803002041d140c00240c898201001a5010403060140c3d407843d668685940b4010340819a0280580e0014240c1e201e40020001100d0011001f4802e808440403400c0500302641c4540346030040702d13040b140c514500d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 397148552 1250 397147302 397147313
    0x160e0a14011103040b030711190312111c110702031e15090705031002030906360c040608010603050a0b0c040f0308090f010806060f0304152412020d 65
    0xd0406680504000100d80403100035541036421562004494843c04420404074903088040d001d0b000000602070801848044890401d203501c450014007044640c1d14680c0034506640d014805c00304449550a4a941c46680b03d14100c0623480c0200d13900c5403c14058210421070b00003580c4001d58020058118250320454000b83c1d8400d00190350301601c10b42e0070b051184503c8a42c40340c010a0401d004d8010b8604100c2030515042a4101448600384104108042c200d00412002d80141c040c4079a00c008031261365815101c03000320946108820040880034098502c0029009010b000949050282c241d480c1809400c0307400340d00c07001d00365410520401000a40441707070240d200f005c181e140c1c1d051584540c039200403c4061b4108550201d00001c3c515454607005204580c10b40707003440c01381c001d4581100801e0041c0120040612011400f00104040200020300c818482c80304a0042013040800041d507003c1c040740145220740640c100c1d5000c6005004401002c450317607009090b000c401d4506503101e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 397149802 1250 397148552 397148579
    0x1081b0c12070f030212031b1c150302010314010e0f0a1808030402030f010c05041e031b0f09091a07021608011d160e09030412060203160e0a 62
    0x1849068003490a048000300d20001c00b90010a002d4070380c00b01c00040c80e160192070411440ca09044000c414010850038165598446803845001c0c05040e03165444c000b1246024507c01803c884100d0400900030b00c0c0090008290046034000d13070702844412034401e6006c540d648203010f1a1451102100010141420081c0d626007200c0104400210b50045c10b07840c4e512941c4003078040750520703400814042945001c000704007030303003144100030421200751540c041c0080c46144110b8a03800d034003942d00b006104144000c1002180c0105402c21080780d2561032100e91f50b82401910302040441402090b04c082620071820429440b2440d4031450b0b5001c640400424002801d8908601c241c4004086100d00010650014410200081180003090008050b00030030911045404e43c00b084ea0f00c0c409034901c80c16401201e6000c800c4e01c4140d221201e41e1030a61140e5040301b0005034410014108000050340298860100c01000940c3c074200b03c0c10840b031801e1200394040e80419000014812807506284 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 397151052 1250 397149802 397149817
    0x1030b030319050c01050429060108162c0a061d0105091f110c03010c1b11101112180f1c0f0c081204061d060d1a01081b 53
    0x1010f07803c0610683c803060a642044604031002d9032600000c00e02841c080342000f04c2c007911602a10818540000000c1c6810720060107820070854a070107003480203001c0c104d001c00281003900343c01c0c00d06100026100040e1141038406004994143c000070f0010f01c268008125260f00020511040000000440d404c0c3c004400319580b00b03500a040700400c070108403410183d202607841d52446043c20161082c1441e41500c2094001e074144500c00c6503407035100349001150441c2d4588110084001d0500d50a400103030302e0503903049089440d92030741c490742290800d0001c0002404850040c003c0d000c444016004814400c8103400c920800c650007440c01c43d025020129025200c402d01c2e00786046040b840808104080c0c0d034850382401484c0a10003141c0a9030b01410000c2c00420055404403200c2d1645d01c41c0f03102d414100140c00d0341c82065a000140c114291a000400c5079440f010303448010402421800c10f560f21012225584020650003000410310403100300f0404501300c60b280403088413a43c400700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 397152302 1250 397151052 397151057
    0xf0e0405010b0d1101180f0504020f0412081c0c0801090209040e0d0e090c21090f03030f0a1d25030f0f020307080610050d030e0306010305060603070501030b030319 72
    0x540e48a890346540c46001852400f0b41060000c0da1384042c005409481c000d03000281004140360148071090781c07107034490211030050382c0060341c86000007401c00e4540255080000d44040d0a507042040c0003502d8040e00100350580484803410364000241021500f03200003080c00b065090004121070656580a86a900c034003400c00305000710b1240d4214106100211424045200c2e403c4280c91403c101070090341c0524809040740c0b910280e1030340711124407492101e01c181c8560680002d503082000344600240621403c04403501c0b030401e2135001c004000c08071903d02c610740c50040c200644000b000540080c1031100405001c0c40381c3c400c091140110540c00700311000c581c001d58000000340a00b070000034140d00035141d50b03c0c0100d031072040508105155008040380c0d8401030520100000030305039181291800c03103050901001a01e81554802040e245256141c05000c00000602002182030303407041d081101039810b030584410054040321526102260542c2c0148a090741c0c1c51001484c5510b88009070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 397153552 1250 397152302 397152311
    0x31407050d08101a0702060715180b22020108070509091801060501050307090504020a1205040b22081b070f03031d12100902120a050f0c0301060f0e040501 68
    0x352280d51512182248260004035400200030440301c0051211024088a52000300301c1c05612561800d940540c001c0a403240c0d20000346803003000b10aa5520035141c01d440d006020078500342070010940318691105413148030003280024440110302540c141900601c40101c009820207800440300070400500b42800d00a0130072001d016552414200b0340301e0107035030068100201c101000c260949010740d20040c1445001e1060200d8070350401c155600707503002554016155914401e003120703200c1d218006424000e15000501c8203120407031590358419030446090400200e8220310349050011a4403025125450501c0006103402401e0443c41401d078103441160812030b182c10f0080c0500707400358002c60124101c4030120310220108802001d03140000c440ca5008425008030031900c0b01100402101d0799561280084110364400c240d001e41702400c4030885065284614145a580c4100d50410b4110304c10100010f210307103014011103064504101c4621603062030108041401c1001034003c540a5484c0d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 397154802 1250 397153552 397153567
    0xc0b0408040801180c0603060b0d020d180b090601050a12031803081207120b0607020f041d030403140606010504050108150409210201090b1f030804030503070203060705160314 77
    0xb40500c10b4440042841d0352008134062400d030245800c2640202e0a25040003410812000003006590b09107441160160ba41e48100641d01c2c0100013606403d0002202e00328048107003d2354114461084032000216490b80c0d0300c0300100605034000744200704039140e40204030000a882100155000c0c8124600c2e10440340e1a561407040c50303088204c00503460f600910400c200264002d040041c0c60742c007038208020030403146001c29424400c1c40c03c064000c2c00c0040303003041261110742c02030742c444c83c042c1a602c404402602d151603d947c014030056607040b400d841302c2c0d424a007020881a014410507100d0078505444c0600544450b9001003103490034441c00c0907080d95584942c05400e0807a84241540c8202c42029400c002030032150a440000f16850202c11000142c024000290010b803c082c10f4101080600c140300b030402e2080d00014241d20340400d00004026002014041d11171080381625142d9603418000c0302d0901480a45500c181c1c3c406e4a0383c804240544400c1da010490880c40030700c0c1c08070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 397156052 1250 397154802 397154819
    0x42306181006030503120f040b04023f0f070f150c0b071707080603070b03090a08070b0f011703030403141207020c130e060c031e0108031309050105010c0b040804 71
    0x41c958815102034000082e0901b106e80b42440359588030070306030140d08517030410f070b1500c40017540c1c0240001c1c0128880311041500650442d1440c00e107e40703164190a4480302c1c00c0301c14045088101c000603d0b8820006505841840462004141d840408903450410710340310280030011044143d01c400d00815007454004186c0d002c3c1d03101e205002640b1070490401a8a40302a81e4034001041c2c807041000040600100b5603000c00c03600c0445507400340194490700d55140c01c50030403c42c10030080000070006801000c0103100307210140304546124050902d45e03600d446100c00e009200c00c13800b4458104100040c0040e00600030b5080000d4828541c505001c640e149003580d1080903501032015a0000c004104d05c2d150030840c0009d01e1a000d2014090b204800b180d4550707510015121a0454001000180c4c004000721121008026241e100b5001c330b580d240d01058599100c0c2c0506102c1c500402c1e80884d003c000303401182c1c12580d060351a45a03407040c0303403112881000040d00c1210461000c1100080a41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 397157302 1250 397156052 397156061
    0x17060a02091516020f01050c0d0f090b04030501060306050a180605090a15050f061e0909100203010b1b0304051c030309060e011a0301060608010605070611120423061810 74
    0x30544103034a074100a0700410105c0d110320340d0800e040010400c0380149100000c144a20289064245045c8aa0365004243d0341407145401030f045000b008280042030041c1500304000b01e034000c013000c010ba03072501045102514041440108442e2008240b0b00011781103601045d03000c1c4818050300c40d00d50650361002042903010740030f00030712074a0b01d0502002c000d07806046604007074101d40d000045004045a04454107041070650f06c9004903500103a5031840031b011507021407003c080c04565960b150390200034643c00c81524000c45407550201d241c6c02600c008219000d40f44004c12002d0083c8916075070118202d80c900341141051b40301c0c05000000f9207503020301c000b4001d940002250040d0400c29500b080040079460500c80da0520404001044c9c102d070402d4107681c040d1070203580e500c91604200740074064401c45104007940028071081104295003141e40940e2182c08058802c11184001181400803d0204402c640098012581d656443c0d84900c040007840c20940340c00103050700741c200844 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 397158552 1250 397157302 397157317
    0xb18030d0507020906102102071416060f0203040905090a120509040b0a1d040212030c01090b0105030d0f030e070b030109020d060512030d0f06030b1303030617060a020915 75
    0x60004030300c2c2d070b0451070b0031003c10358040310540340c0301070b602c609240c0101001c90b880642071190b2540e00c40b0203480720b600e070100d0350502e8225071100550410704a04907502d003528005986056540440803410300c3c0300d0000301601984a900a5007440e00b410b100c0402400060840c03040340c85018214000160003800c1c10712610b095441b4a61181d020030284002e448041d428280f04000032003050020400074407054082c0d6606800030301d0b4681d01c901c013280310540395280001440c407010542d40d02c0003905420903403c042c0f059116500a076aa0700a150b92090b11804440200d903007196480d148900c0f9500a000e4008203030102c0b40c0c00303590f031030017080298001e0704242122900001c004071240020f01554000f040241d5101c02031135110045541c4a01442d0300c020001522548000151180e42d00040003030350b0842404001e908002900c40c02e641c5c6003034030483c0884d0401c200064400214100001e148840c03c001d0015135803003c0c441ca000354030140c000f50340400482e0711040040c413075201070580c4c4c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 397159802 1250 397158552 397158557
    0x90f1302360702060711070e042402190c020306130c050604080f0c060f0d1509061403060a0509072d0e0a060902090a0b0903210a0305010f050a0b18030d 67
    0x11402c15650003130605000070140000c0c400d401502c4010080001280d50481c2c3c40d500b840b1580740c680345002003015030080702c0494a00c00d21003110721005407550041c892855960003480da101e234511f406a400308260440a58903400041c0020204803106140c03514031171251001010342c3e500d90001904503001070300541807543c0712010903002107100f00304007180b1000c02c0341c800b400c14442c40301c0b000e8244112604601c02940720b0500c04d032078102ca103400001a201e45c0e00240100c41e1030700208008080395070f4401c0c1c030038410030021904c0c400781e80c4074650003141d6110140402500300b4200203100c060344400140051584008048844070b2500a80041c064445035203089040c440c42c00381c140c40700381e0803100c012803040280c882e42d551540f4a20089841902c442603c0f41200c0740000d003042c052030255040c20710f14000600c1205c00c04802020220b04945042026980320520540c2c0007106008040d0800c0b4002010b000011045018141000703a00c071244501081c1000807904040c3d0410700c1901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 397161052 1250 397159802 397159909
    0x20907050705010b0306060303040303120204050d0f02031e1209010c150617150a0506060705060f0a11090a09051008010c080601030c0e01020705010e0112050114090f1302 75
    0x10440b0030302a00750222000c800400c030303505140c8000703a00da21a61100800b840642c0000ca28040d0b29901500c008100062806028400904005800c0f0f02d003410124404d004600088a000c0d07288142c840c02455628018001c000c540b84603040315074004808241804400c54007a400264440340444e0302d04405840400c406151003c04014800300d980411402d4110030b003000d00420060030b0780c3d40e01080031000419280c81e00f501140780303031180388c4010300140550001c000e107010803141c0c20f074013880340050100f000c1e03040160420228090200e2040d40400202010410300c202500440d80048101a8100c0001da175a00b259013101c04040700a03020402c08420081c056805100fa40480c1006080c4034501440080000752580c1d424002c05041c420f480d0b88030208c9912031034100641108410041005584441a0640c10712040026074410a031402c0010001000380e10300c2c0307004192035451800902041d40c00c0002c20071340700d0b0316411050b2426081c44852410214003040c441100c030790403403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 397162302 1250 397161052 397161067
    0x5040f080c0c061909170307110a05090421050a05030f0601030e03120106030c0801061b050106080304060e0a08150a180206120609011502030915040506040f0810050c12040f02090705 80
    0x104040c0d41c41d4031075910186071b45803955002a0100840b52880e42c021410032030181d01000280c0e01420301d80140e500702400f00200000c2100d2401c040781040c05140003088010001d803404c942a200700d198820004505002043c4034904c05003509402000505001c01c0031035980f030000c3e1554106500788130b2050b90b0180101f0040e0b405200707505549443d4038280c00558142400500320051602c03580604101610b0710005101003036119001600240055a0783d0301d40d11500105000d1410f10341600c0380034081e200190000000901e100e500d045900740c10041d940300b5403c40c1c02840c80c01580140a42c3c4140c81c0b00040c3c0d030346c400a080c070560a417410102400d1a40038810652016000140441c0c07008141003c0361b50008140c5402c08001c40d80b168840e060404200d400e0300840d40099080a8040350214900f4100000401a82c0a100c01c41e4000c040c10004107080d0342080c0c0e883c0500d55810420802001ca40b0058a0b50160140e55042030000f071940c0030030b040c0b0104480c8140001c50224001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 397163552 1250 397162302 397162307
    0x30d0c11030c191e1d0403020a0813050102060a02040608130c12030c0312050702031e07020405070206011703090f04020d180b0117011407030b21160905040f080c0c0619 74
    0x83d40d83d1310343c02101c90111405d01400d035044440481d034041c9100c224000103010903100b00000716050340d01180391030704d0705a20414580380130a9130003603034098058540011240c071901d00c00c0c0d07000c40d0f003550f954a0321501c07403e41c00804ac0015040c2950304440c2e107540400d880841d5079690911511aa60300c030309140503801c1c000c0c040c10f40c0c040b010750a0750401c1c080c4614640d00005907800c403c0c52412500350b21100710420007aa01c6a481d009401c1400c14041007903043d000325419048072810325800c4181001c01c19020789912500c203d041e80700b803a52600405506081d07000d032015000f03000d400542500e0075450081c03440d800c032404503018071b01c860041c01202d40720550488088003484c001d200c0d0070030360600160f91000007403015041542c2e5892008084e03032519004559018411031000c0c0c500030a40300103465489941d1650780005200c680000d0130120703031042e18451900203400703150280007656401411352000d541c19240c2e2041000780c024964030800102a0003000c02da00281440d40940b01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 397164802 1250 397163552 397163579
    0x2151b1e010b0d020f010306090e0708010b0a2d09051f09110301030803060d120309020f0111030306040e0f1906140103080d021c02070b1005030d0c11030c19 69
    0x140c65a4180840c002c1152650250701903841d03030440356030002e1018a001200185120750000b901142400b00ba00b00941012608030182c80341c0c94001d005413080300087c0541240345200d1203040d0842082c5086940040c240d81d03541d151400c0340000c0c500340c1e49e030b0070080a4820654038041281e0070b2154085a041d606d510207001800300d10414403c040c1060904082030005200240c402000040021043d03a1283c401d1480386510420140d416420301c00020001e00074004202e000344040441d0700101d41c0200b25112450926070300031071950341d800052102505040c3c80300915881000808131014405208801c070819042c40401e2040307280341403820a80e03805400c00749890781c040c8014008904600111581c4c11000b0b10096601c0e1680c2e407031780d821546034a41d04080c4a1012034030784108007241f802d0310b014070241d03004122030070380700c01c10907445d902482c80c1100840e00f500c900d02d00203800d102006400c000024107603900303440d800c2c011138184a2281842405c194007280284510110406d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 397166052 1250 397164802 397164853
    0x130303170f15010e0f0a0f090e07030b0c13080706050a182405041a0d0b01030e06070f140304030807081308091c1703060406050301020f040302151b 65
    0xa914105003403a210840c0c0307445081d0b02150410035903a1000f1801d8541d40104144a5406001d004406a42c2ca040f003035106114002c0c400c08905000c100c40009500140300e45c10380c0d030800c842c03101a131120b44a00c00302c1d134040000221a8284200c001070841c205214802c010300340c0361100d81d500c01052030010810303041d81a00359103002c0054410321013509a45001e02d5101c506414101012100d6042030740c0c0c600481c0d016030f405a0200103c1d02e005444440908122030341d940c400e00c054010305005405880e00c9403929086540604009a402031040c80000c1c008251800c0440303400c070030b0030750603412640115400c0d408900703c1c00c1030040b0141d12200c1c0a5021680085d04084400c29a452242610400580c948079010702009050343ca020691500380076584001802e000c4c0404010208181e0000c0710068412441c2280005d61803c060084032608044403520501d01800c55080005034400c151511225240a001e4030003c1c00c82126505040f0250000a000300c0c035040c1e0b940e0203102c01c0e419 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 397167302 1250 397166052 397166071
    0x6061b050a022101021303060e06240f040e010c0908121e1605100f02070b0f040c030b041109060f0603041202030c100e070614070b0603010213030317 66
    0x2041400810404560307040d015504036100040d90019402100b000c1140c4404011a0f5200041900140c4000100740049030300c14141880141811a041d940300c0c1c2c0304135008000d00d0300f4610120035040840845247c00c00c0002e000d608282c0d1140041400c0b65548150018075a55912020320f280380c00140e103030b0003000040c00400b80344d0746d42c1400301000d00500407031b410030711800c20072421103404c40c40955080f0205100c2140c040c00250404a03170303860581b003035004a035150900010210b4a1402155440798000d00210450307120005211000c007001401542c030042c52400100004010f1403026000b039018040010b5000749150422a19882c00b41c00ca40c0300310002480a0416140c201c25039078840d40004403500a0303242c07104141d055105681e982000c0340154242810030b001164012a0b04200d0784c0d04840c0312070340700c02c1c00b6a8a0f1115441066045201b03028460000d00c1202280e40d00c100054000750610220940081c3d07005c0700c03070b002100402d6070b01d032200c60044082c5400c030b03520000c3c2c81c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 397168552 1250 397167302 397167347
    0x30807140303040f0f0302030409050f041203020f0a0e3105010b12132d0302010605040e070e07030b060d1a0f0109090b0d0510200a140912060a0606 65
    0x1c2e0f44d1103032031581041000b070007107170204410400d040c02030040d54028155140244090b181c02802860040b104840c201c55409402ca1890700d03261191080d1611042d20303003481c0d4a000360301c21054411a40065030789034094080529018441c0c9480814514010190419110010300098034025600142c0104a08440501010703240c13001d0034203687c0d004100304d41c11440c59101410035503152902000c0200704480316040510103080382c0c07a8051003940c000c2d8001c0001c15180c004000070384e40303580c221105590100c00140280c01d10f09038000d030068001c0c100022803000c1e10380400c071150000300f03280607060307500d07450781a01107080030b00b81105c0403044401c4800d01003500d00203801040d0b0350084103552965011688030702e840300c281c03443d0681c0e0803008a525001035050704c00b01601c0c160305a41200d05c4501d07190540300c051a4290b9042e5055130700c409030740142c800c49174441034100550841c1e110b0b9050940d0f1140300e5050040311301401041501250041c1030003005410b403c0c03030090544420300311 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 397169802 1250 397168552 397168561
    0x1c082808060604030204181703090d090305070b1b06070215010608040f12120905030310050102061e0a0b100801031e020303120702250e061f0c0813030807140303 71
    0xb000212015280c0c11100010710510b56801d2514400328400010404222888490b01c8814000080c42c442e203805421640841c0a803001140d00000901c0300414580c0849030a0100380c4001d005058408003034801489480b40c1c0c6a035503482c3c9441902d8a01c0540c2180c0d0001d084105001c055501601c0300b0704010006041030b5682c49140f4030040300c00350000005001e0240302901c1814800307286400040107002462450800e2901c90740140c4440c65600c0c010706000031349500201e500c40c0300f00c034080041140c10402130f04021030100d00030422412640c0d901c803481324581d14a0345885070014a83e83d00000c9605600e0300c1120041d8048550648050200c0d6520041c0c0c3c00004440182c40314400e45082901c987d01d05074500405084841e010035403001112507040b01c0f81c030521040318016000102240c50380400d1120701480804c01c0c0c03451001e07800301c11010501412040d104a03114010749440d00c620001d108120015a40040702c01d9000050700354140106280e15540c60503010028502c0c40c2407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 397171052 1250 397169802 397169809
    0x507080c0d0f060b0d0212010e01050117040201020c0d350d15050d08030403030c0f0507020d050a05100209090612030304021903020402040605070501050a06050a051c08280806 77
    0x400740c0310900d0688442c00035064400b0360308103900034000300c1445500d50042c2d50340034000c0c1d000345482050b8207085000000381c0001107110b5904035641078488240204001440c04840030008109a0562050488146040d219030500302612402901c82220b88807202c21070100a0303602030084078083c0c205155030045c85c0000c40132110303204280800003407409810645c5034140e540070740c8055480b04104000d0414065180c0c004e41c03159100366810000f1409807001038404002606400001603001e000340c00c01400c1c039100d10350149001c0c408490344500560360f1285010408900003c5068000c2081c4080d42480c01c0358a820040c05c4034040907045901442540d81d020042002e4811050b218a0144014003540c01d0000317190058000d540d5240c80c2d14029089900108044407998645400100d0301503132481800c081e41c100034003c081161405040114011418800080e9810203403101c0e4006004140140405014426151084440541400c10580a10b42043c081c0500c40b400c0080303030358 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 397172302 1250 397171052 397171057
    0x7110c030d0f0e030a050d0f180b0901120c02030415080f0406110c030a030b15030609010e0601181205060108030406020312100e0a091106120115020c150901030507080c 74
    0x1410b280c640e1000c0c0710000e0031254403e162001c1501400341407001014002d0205140100414680352000c9103010700300104c4145428802e249642c030014501032211518400080203a0a414500301c800c0d403104401c68800c40d0f00003101c1001680c030000303041081c410500c0e11a443c40442e41080e041d58900f002c3c907a43c0352180208010901580c405c1e41850a030225400d0f1f606201d130700c8045a4a034008294043d008107220394038184200d0b0f1120b81c2c1000c12114000b203078850b82002d00a03980503460b04102141d4040d000d48194103000600016111182030b0a10b000000c00c840300c8008540842c5003412800d001043c0c20082094004000c180310540e0000200c9078580350001305000c20b965001300900094a09070042a2521248403e000d6000d035543c2000914070700895840c0c21200e0354408005c001e110350054808113921a0713004102e00c940c070000c414410181342c019142d25402103070015000d408640072241c01c4100101e03520310103582c035125007070303100c000c174240302015082c2400d01d000b690 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 397173552 1250 397172302 397172323
    0x10f090207051e0f030427050403020a0b0603010b0d110f0d050a0314041802031902090a0b160602120a11160f03031e0606030b0a030b07050309010e03070b07110c03 72
    0xd8501d0243c441d10345401c02c0342030301a044d9030050f29101d68440303003204d040c0400004c41034040c8461400603c4048014802c203405240e058009001c3c40141e55070f6001da0300030090405d54595078801001f01e09450381140c1000b62441a545052070002410801460303800c7e07480c5690141081c145204c0c001b420000361006c3d02901802c16048586004800c2d408501c1640c020441c62610340e00001c2c04024507030083d601400200040d10345806821501038200e004011007150f10040b0760702d0400c00140b44000a140c443c100e0110100801c00548560f02a80c0c81b182240040b007201c0d40400507510201e00c200c6241003803640845d49003010000780d5003111071303580030050201c1502d01a080e003098020340c40400b54642d03402c208042c174030340d150f41030004018912980010904041c5961054902600c41e502600d1380405032501e545c03154802215541c03c010680312441d940c1ea070341c03000c14085c100080c00f403540c45000082c01ca4600035000a11001803600030451650141c04140d00c10380d13002c181c030340c1720 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 397174802 1250 397173552 397173583
    0x8030918040f0f08030f090d120f0213120507140d02090712090c05010905040203010f090216171b0f06040209091e0c011701080c0d08040b12010f09020705 68
    0x80d600c80707040429084045400040902403c0c0324000b0812110310040c502c1051520442c2c02e0b50358401102580340c0340400c08071400900d19650002031401d5507800303100c031a0b4028100605001e0046441040414150070240b210000041b003402004820800e100c0a00410700c3c0742400600c035000402e009107010b9000a120710840300000f0304161003040728221001250106002460203802c112000080c14014907001500b2000c0c0407610b4141402220b040b108620450a40c641c0341603040f0000750000301400003a62405880e80700032540c00c3e030512010b40068010300380e46041a10740b90000c0d01c130a1000180d9600000040054441d0100c0c400d0380c02901541c0b81901030390382c00c410a040c000d81480c0348141c0582d02e06404070314000014041c204220030389070b00807440b6500c00f0100700c0c240700340301d200c07466809016601c2460500c00b4286c1c503d01e101e0180d440c1050345604440e442e54101300c900e4038840d4451001001038400141c429402815011411460141661220380c0c0390703131450060205 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 397176052 1250 397174802 397174849
    0x90102030a0b06131a1213060b01030e0a02040b0613080c0f010f0206190e0d110c0a0f27020d020d060506030c0703031a03030f0a02070503191506150f020601080309 72
    0x1601c13820b01c007220312441520300c40030b01c28a0b05401404041750807c40581d000ea1410740c0302d21503540280300e00442d03060701000802c0d400360b4940c00c0101910400041d550800824403a0440011036110301c0005031000401512030054100700340701840c2c2c5090740d0141001004c1c209059480c0d0003141c49608000da410007a241019134014610240c070086440801a1140c00554040181d01c07403540854143c800060315800715860703007002103582581c02540d425040840d0100481024842c0b400c110030580e900490b0320316410007201c3c0880c1c0003243d80c0790206400045103149070200c0e1003220f01070300301101c807076040d820300d1020840780d806004401406c0c035603100550301049002d80185044901c3c010104d954a42d04034041090a40094400c1c1000d481050008560f52502003110140c0e952000c000080401071a10341c0c03807542c0c0c24906040b448a5949802041d181941c52154944100d5a01c0340021203141301c3c0000c0c9080c41c164031002c0603400c203014010007962504110100d4001e038449a89 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 397177302 1250 397176052 397176089
    0x702060c0714210406030b040e120a1103070b061002010606021b030a08030106090315020405030c040207060e060115020729130b180f010f0206040813030b090102030a0b0613 76
    0x2490003001450b1a001d10611501e041410300060f0700510554805641c1440400f140340288410f0301c00b0013510711480d4111031100c4901d4004031026209021292801074070310120302d01031500b941d2004400f80d806600b0700042016038200844040b04104413032000700506460444000d49070003100f445205103444519850300301c0e640070000110425000445a992540e4494018190250a11045a001800c1c928800b01001c540c400c4d5004c45401801904440d00c094041000a60000004541c41c0e9036034031680d0300508041100034040d04154140350300368100c801c4041d14140075540700304014900c10308500c81414609d80703d0207080c1c5400c8542902e4072000c0c681d4840741d0300d807508030318001500840c5081c24524414140740500c00182c804801f400101c100468060618148000140e44080702060010748104001e0207058a6000703d0002c0949a64036482081d00a030780c01e0710720740c0d0003200344030030600188610449181c0c200d881030f02d00756520400b400038060360f01c5a1003400758a0613220 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 397178552 1250 397177302 397177343
    0x9030a0f08060f1831081303060c03060305060c0702180a1d010f060609080a020114160b04060b09100b07080415020109030f140414031c020d0201050702060c07 70
    0x1103d265400401004039100b40c81d290703142d405030032102e080b151061041900042c1d4503002154088100103618800c505145417a05000c170b41c081e4404881d011301207400080800c00f5441082c07106103103030b81c0100d00585141801c0b407500101a010691803e82000b0305001030b640c19000482c0c41c18291f50a60295840c1a01c16005000c10b14041074400048486418900c070198840341034908804004c01042d80c1303544045a0170780303190142c2d00c0164002404c1e030b009503024031000302c94083c1c400d01d2245041c10405107401c040c0c3c200241255490140d9081c0f00800645016188600781e054515000c585042500902c2280f000d111722201c4250005019007403055500854014245222000c01c0003810460000d001b029510313030580c0007858041c2e0008400303108105006203200303414032283c01d01e420141000360150501501d117034184a0f452003204400c4a5141000851348560060010781502200281c00d44800403e050b0031174212070108030384000c01001356515250410785165510301d1070071700e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 397179802 1250 397178552 397178569
    0x604210606063b01120b030d050a1421040809151216050f0a090e0f01080f1f0911030604050106090608010209060a0302130e1e09030a0f0806 62
    0x40c01560030104046035007a00021124040c004040204454668640c01480c3d04081610041c0c5540100000c42c112903202da1003038085c40603100c400003103010005000a24140486095a01089020030103155041d0860118105002c43c20169490205040c0c0d102010008192034480540c0c25170001c6001c0c03100e0101a603040c604041d00281a40c5c0c0d41019510b07503a017250419000c2040386000041004040c849411034604a588546040c140482d51040c06074100040200401540000003e0041403841d0b182c0d0040d2008008400300f1350400114030b090a0207903503129007035031214040c400c400c007038002000d07001208480e00040400c100d140000c00001c00014190b8903101c2c60f070603c01800419800402294001f1608021040e80c804646091340034001b405da50014042c4030300100315010f900200300c1030700280644024181c48241c8850040310039600d120500c2c12205400d0b000701c00c981612a000410f42c80118105964058010704405000380c0c1d5804004004012500c651a030544 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 397181052 1250 397179802 397179869
    0x120c0c0127030503030a0f020901020a0212030f0d2004030c18021606050f1302090117010204050607140d1d0d020a05030a03020c15030105010c12180e0702060105060301050604 77
    0x110701441680ca04045a980e0002d4495200c820b180c00f0310000a65007d108865003980c068010700201c40c5180c0801540e1032000401c004540010841c2d9051000e485005102c1c000740c20340005803652181c0460b07001c1c00c5c00040d002c00030b000100400d2001c1060840c43c0411212502c140340e2500304070701c1c84071001c0c0c0288080e840d61041d0b802410010400d0030740000744541c09070026542c456450601c105062210444060b4003c0500c03030040c0240403085c403d0000300e5008500242c501035071480892400e80c40940c00340d4103119004034458540c0410b00030820005090320b030640b0100000503c10510140e0003403024495120802000215111035994400501004046d580c4110450802a4807111042241841040102049004d18580c0b0050728182d401c1a52844030320715007a95203020b030000b8070920000784486440c6081c540d0001c054a14003034416040a15103600300311601910b03000b4107030800c606c2120b0900052141c0c3c0c440750195800c440020100c441b24091035100d950103040000c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 397182302 1250 397181052 397181117
    0x190206150402031b0306032a0f04060b040e060f090103030215010905160c0f06060603020417070303020c0d060b060a09090b240a0309080f12010e070e042408010b03120c0c01 76
    0x11218500148c088a11640d120429507d00681460313441c2000105c1e081030003941032074a8240b00c00e02003042c11a210543c007420103804618030340c059070001819450264402c5005a0000a81080c120142c80c03150b40100b041031000c0c0300c5410004140700c070401d4444550810002d030410384c031060000121000e450903800650411105803601c00c0207000e507105005041c4440b60405600b4032814001030803d00301d0b41c050f406400000c00b204104103122201807001d0b00c0e119151302001c2d4280e601d00c0003c01c1000740c15111070100da0320307100e01c80068891140e05a80320f610800d001a8813039069401069821480c54405682d62100000c1540140141e0070050081200030524015505801e40140210b1003005118180c6030f13079440c40620003001c225403442c00120000a4190142402c0d008200f0344025078032141c3c400980c0d00070140e100007107580002c1c8581e455810682c00e5080c18040c020300c101020300c8052820000181c05940c40c500040d101c1e0400042c0000e41c900800410003000e00001c598 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 397183552 1250 397182302 397182343
    0x5090d0f092d06181710150308030106030207141f1e02070c0501030501050303031302090402060f0d060608070c020a140d0206040b0d05130210110102190206150402031b030603 77
    0x80d00000c100d550142d2200701d101300c00450200d2400d50719804800782c60000001171000c01c0340800302c00041e081c443c3c2c4d007045a0002e0031000c40000c4207040518040c041307581d001611015103050502c0301c9512060621322541000ba21350201440d1800d0b582c0c2c0d800c481205c0880c220001c03004041e80d4005c1d5940254040f88003040d00f004000b82040b446080f1002668107200c140d0700c80c410036417684419103520f20350b10340d00448200103003000e1035941d911600081800307041c1088282188880c0d80410035040d04244c1c0c459092003225009406540c01010300c3c13504148103241540403031480754403801105441b55011541c0c071a03641c1c51445000340a40d0140110351100c3da12421610150407201c0d9010700f01d41040d0003c2ca031080c031100c881060680080156030301c400c2c2c040081c0c404030000016013a8a54007004032141180700c003030260301c504161340d004100c5483c06407120112198416001032142d0700400500c1140a0101d40420700e0a01d0950301950ba62a2000028a0114400442000301d00325 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 397184802 1250 397183552 397183559
    0x230604090c1e020304211a0a0e1203091009021f1206081902010539070e04020901031202160b0904050610091505040b0c0105090d0f092d 60
    0x1400c04420072000c81101c0b840000d002d105907140d0295000c0c1d003c0312103c1d0314101607120484036801d0992405210800305400c8298070501c03810343d003252210f02e101d4803000c2c103403014001004a1103040d840c200c149070841c213250000c2c50f2204440418400d84a448010364000d55440f40f481e5001300c0180107200350f01c04c5091340c0c0074211044180d0b000444510340314000079003080204042944541c00c03050003450302c0c3c03213500560701c98000c442c401650b4800d9201a004910290b200d120301020502a08141500c540f2840c615050258100c1e0024014210a100060316403402190560f640b015030203405001003c401ca191007a02180040041844030780040c00000701e0004001401c0259414007840d9540700a00c07012801101144001559464040150140c440865550300c649840d0003840d0550700e41d1000810b03044425489140d0b5500c50a2018a9800b04240d0403104840d09290310b4200d030003040a021000b60b445101c46401003280c0400d120010269401100303100415600001e544 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 397186052 1250 397184802 397184807
    0x3010b03011a010f080114010f030b0915190b03040b0702120307030606090e09060c0306010c020a1707050a031502031518060306370207021305150901230604090c 71
    0x46142e00d50101d446004403031601442070110324142d5200c2d1180f2125a1402c000440d030a4400b84489801c15549200c1c8075900d50301c0b040807d014003024268034a11055290800c54049100a0a0701d480716440c682001b11121910075203510039000714205203256129182039080c15030741720b440d80c80300a0000c10003c0707442d09035000350f0984455594020b00b050721000f1044503440f040d100c20700107920480008006d0100700340103503845503062510820042d4268080f4141c030f135071034000c170500c440102c840112506007008600001c103c22140e40140c14519100c1580700340700040c21a031900d03000800984011145507034002403070b4000c1c122100248200c040c0b080000b8056440c28800c2c0070f903001145002c0307100702e024a540208ad89000954507207214189405440d07450700821500d80a10907003000d80d40b03280184d010b0350942c0e880070400f8917008540e00e000c54000c030049071040d4401001440910004059800c070900704140d6145da081c850400120303035010320b50100d01c004d4107010408042c1136 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 397187302 1250 397186052 397186091
    0x1d30040306050f0f0408090d021207060203030a0b010201110414190305010903021005060112051005120709050717130c0f1202040f060e060d141006080d0914040b03010b0301 76
    0x80c43e040203c200e0300e03049008055200241c4001d000c1400c18001405285400341701040e06600c0101010301e0b4243c44d0320880e050804562101015800110402000c0720303a03405076800d081024130003000942028021100517000c1e42c080c3c030041114030900701040d0703102d807440032003000e00b00032610200680d07903d48580078102c0ca207403c50043c0141207214554034030034000c8070301580d0140c4800b00408541e80300c000040000031b090300b0001c0c0b520232000070261240c1c4c1100c5059480d010180c000d060400c00900f06490b00903101404012108101c46c0003403112044650300501306181091500c041820081c0c035084003a0130228107c11100320000d9603e400080c10314480d8400e0b2024880703038031079482040c11910703144919641d00010b00001441d51412a0400a0072881040154054a02d80711002d20f807401c001442061a0364070441480011000c01c80d40e0b1010340b881c5442c60b41709003030080c40d601c050aa995010f001c0c5854503400071039542c00f90401100014040c000300300c10411030b00018002c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 397188552 1250 397187302 397187311
    0xe100c0315030818040204050d0602070201110607050d0203070c050d0e010210020903120c10230a15050609030709110909130c0308031005090403090305011d3004030605 74
    0x80c50040320210072200040c0c2074049030b4006940c07506200d5182c034a410300303004581e8540d91055082201085aa44c6c80c1e1900d29101d020700c000584600c243c0c40003400c004080655076026034002002c01001a502c141101c411618180025840380c0b90044240c0703507500b4420b4000c105004140018103032a034001c500b1940440240e08490064007044400700403403050300413603038064012801014070744111000401d03a0891440c219400041448854801c80321204520640504110403c008404009d1180340d041080048204000240c004500091042511815004000202c3c0000182d50103000c4403009040120052180c10030340c1c02c2e0303450164020901503128000e070002041e00911000040c2d0074842c0c1c00248610110f04548482c3c0841e0801061000d081825010102d5252078100009008520a8841d28805030461034403e003550b0040071262925484000d42c0301d1003860010b01481e440402d00e80ca1011020620b441041c10440803680c04011100040c0010403c00b15501c210f129 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 397189802 1250 397188552 397188557
    0x30506070c02040902061210141f051b0c0a17060402010c15020409020c060108070612091b0303020a020108070219080705010f02030c040305010b100e040f0e060901090501270807060e100c 82
    0x2d49c0e1501d50b2900250744642144d60094440401850803602403030900c08070b064541400c07800c0154451041d0008655540c40100036009400030000030b084c0b1210740005044946000300c0303554004d1441c1a500e81e0000c00290400001c2d20a01050201400d1501c2003440c051800359a52a26801c05001a50011181010a1140d40b000046541c0c1c04244901a11050307517441709514240c040030005811345040c1610f5942d10001039007803004905803000c00840c842d4000c0d100045040c000502440c8000b41100199080790368521640031aa003040608030360705c40d0680d61111024100103004020740095800501d10000600410601000240049a00c507000a216002000341808132413400300e03a040020070506038026500c0d14280e00704100c0319040e00713400110500d031004140c0c0340c04810764004070070383d40d258000701c01c0c42000c0c001c480e01c001c48020340e201d0404000c50b08250036840f075071018107a200040350410401900b0780000404002660458503d00301c0c10002600900800c10079102 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 397191052 1250 397189802 397189831
    0x7050906013f02120105150406050d0b0307060f030c0c0c060f0c080313140703081c09020904030305220209010b0f04030b0c0306011709060601120b0604030602090a080601030506070c020409020612 86
    0x85c540360601d06038483e4845421068205407402d10192b4254100c04800c0b20401d403207400351000ca032001c00c03100c0000e221a0341d50160b40c2d008144041e0407503000402030820451016400d0000c41d412071070100403544646003004d0304105d408400c035040e041014000781070007400030501c03040c203484000649100d40181080186c3c2c4042810749996035801d0b20004200c04414085003010405200102642118804020bc1c4401c4680e00144400e00215012004039540700280300c400346002e00ca001448a11860700e058008841d00000c0d08500c0c14441e43c20314210014162a180d914581680d0086910402c10040c07400c1111041c0c550b40c00840c4d020740000c00781c840c1f40e600c5144c070001580c01004000050f00080e2680c0c001107902814105500c1005515207400100b25103c5a00130b20085019610042e2210b01c4e442c03c01c5035103000d95100d403019500900040c800301c0c03004030788581c2100341030800f100c1012941c4086406460f079180080e42c0076601040104c030710b08a450401d446400a0500e45a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 397192302 1250 397191052 397191059
    0x1a030601090518060405070c050a0506070305010b04030c0e0703020c1203060906042702010504080d02030919060215060d08030a02070510060b0d0e150103080c07050906013f021201 79
    0x183d4200c034400000d10307005040012030b00030b00740340c1e2240c0d400c454140342901a0388556211a071800103945002c6480758007039801c00c40f89542c14401d06001d088000101450680780d0b03168070b944420709015115200f1044e1010582c40f83c000e6040394181003046080c1c50340c294411100c00c006e604200e030301600401041000600d103180034810623880b100c0002c15140152500804d002c488820a103040341070100400000c101c4040c2000070150500d0554021071750b40b035040090058000c060b0340b58280c4c0c0b91300160140000c54021590300d4200002d00880c2e901340d03a0b00000194000d0b540b0001518100d1f0000902442e40710680050070540e0080c1c00f1101c0d09800d40085604071080c074031802c3d88030326040c072807070740140c10b150840018550b082c0102e600000428040c844a10800e81c8101e0781d0705000140c18800710002d011004c020003048503c0b40903481c140380041c10481d50100e011041076860f5400d14502c807440d1808441280d04011018021414201110001d610507600d84022800c280b0000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 397193552 1250 397192302 397192309
    0x12031f0b071b050d150b0909010603150504030806150405040203040b0106030b0904110d0203011401060903210903030f02160e1905041a040c0b0a050d0c050310030215041a0306010905 80
    0x6040303c10180c01c90180d40202d8940b010f0800c680503500045c140c649140d90700d1a030310400801c2c0034000341d03400020600d24501c4e01400010240f400800c1aa0a290400004c80d800161031035000c031301914080b141903030402400c05184103e030041c40d817003480401030100f44101c545031641a50201d0302c040050300186402c22094140869004159a2089840c2852070030921001803060340f0240020510003041d068040c9042000d0b0000000a2405d44c420400e0044d1000c015200610304540300c2d10b04188908010081c00b11800042d060018069180c80c2c81c40c420000e50800d0b0760203107002500c4a40700c0080001d26030703064072074140c0c0e055480032420200920f03100703460189920500c500b1500a502e0070281c8441c034010030940e207010803048d00041c040d81c004014400c0004a80c0d500b6074400c44000301400b01c8249516100402c44140304211080800035030380c070140d03501164500c81e80046007450016500c101d03001000300c1381c081340c54000c0b0040c0c0300001d5401aa000d0301c4038201c103030f100c0d006d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 397194802 1250 397193552 397193603
    0x9090c0907030c0306030209011409071715060d0507021608071d060d0f0302010207021804020319080408010c02030c010b06030f010e04061107080706110c12031f0b07 73
    0x60640c800d1600c0c01064506002e60700400c00c82501d401c020901e00d03981d0b00064252102640452039801100b400021580380000b18150b2164550401681124820004030903c0500400822104d0450000e0b11110758620013a5001c01300020381c1407046180c2900025194120311481d400324500801010551100209029003515544801440300c058002038050041c08090201e81e00840c1010b01c0b400032454421240ba00c29009800159580000340306010301e01e50344012030050064480d09000069070049004040354101da00c40d41212002814054118030a940c4a140550310b04a92400c1180e004400b52952400344030082242034645414040c091100300c0d888038455900e90018045004498080c940140c000c0c040082d08230f40403c0700b95072561220509031500c0c500440c00c00104011409124174204010200c2c90500303070a400425070340d04140c03c800c0281d240200026440d5640f0a1503112008014080760100e299108012002540202400c1c2d802600121700131920318019000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 397196052 1250 397194802 397194823
    0x6110d0c1e0614010b0f0d091e080a110309090109020304030e04150503100203010f03170403020d0606080f07080319170103030507050f0609030a030e01150f05010e0418110105040e0c04050909 84
    0x6007c0c942010034030008000d28405004403401280c0840300c11040950203050f000076440740c0c9456070791340d03d0304a01510f0b006044080d0500747c0c6c410850b1500507152641154111440c0e143c002d80c90b501c4a1800741c4804108400181d00540307881001402e54506001c2030741155429000d95001110181064003680306c24001da210300602c0c5d242c01c100041440e42d184a444525100da217042c1922580019182c0076094002e4a01580303c0000340a0340c0b01c107009405691640340010b01c0920300d840e40d4140c49000c0d8410301600c21101c648400341040c060440042803010240c00408030f9a10b03440c016200d0341100d502980c107403044030710b510200c0600040c240d003c0d003140070085040604540040780540b142d40c071028815503d40322050780f45404a5001000b520250008240341814000010310144003104010310407800c0054448080da20311021050181d0082511940500003c0050380c00e8811036000300401c00741a002c02030300d011807802030010b4990031201943d15440d01ca0a05558820090703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 397197302 1250 397196052 397196077
    0xf41060603131a040311010c080106050f0702040203091005090d270902070507062307060c03020403050604050d1716111c02010b040606110d0c1e0614010b 68
    0x40825028600440516440030444500401810040d034405460100e00b00255041c12504402d0100301900000c94821416400c0000c100e07058201c44001c00400d018420001485000108844036003400c100304c1701c0d8103070050b000b556242000703844c1e2030f91589000e0510710f01e02c1c40c02c000f10314a80c0c00841c032044603580350b82d0b402d0059424100c0d0b100d546e01c45e204590341080c092010000e40d00182d8005419030a0191019092070392520030301520001864009035101d52000861224440150058440c1640c00460000b42c0314400c44068009100b142c0000d0903074803586042108011002030706e02c040680555452890400c0d05400d4026560103031001600c43c581200d518181910030051000c00407040402c1305d4403034203461a41700c403256020842e040142d4680003000c085003040d0003000c00510f80751801c500d0b48240500d00d40d032540d90300d110b80030030800080d640d0000e0100303845041200f0200c80058190501e030714680a0020007075918520783d4140800b000056012442050790842951070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 397198552 1250 397197302 397197431
    0x8010903021e1009050c030d09050a0303050c010e071212080105100305100308040b0d05011a04050112143102010207150c0f05031309090c090507030f 66
    0x1080300c1c00c0040749001c8100b81c034820400c1d4200f81d420240901007000d4005c101911100c540e280903d42090440880d060078800c4a0303008000f29151180050222170b09442c1854450210080250150240c00350f101240d100707101d00420000e001908100304240b10320b480a1111003902d800366198a000d01c84d0300e1f8090090941400d544c1c0c001c0d040395500035031402a1000c11503c1c0e0f6030300500d503002904800980d00e0701080b01101d02c101f61143c1740c090320101821016159000d00d1031030703942c070a5020341810090300d29110050380d0055005900241a030104002640c1781414224041c00c45441d40c0c01491141c10003500c0d885a17554100c914101c0d0107a02500034103007002c81c03444c20040c441011400f0007084072a000d0126965004101c542031190000d165a160502120f070030a98032a0044d030203480c42e0a4425000618503c84c08049072555880400d403559000000d80040510000142c0c400341003003c9100746400b401c6122010b06015080c580e003084401e00b50350104070b02c0e20b4020131800302c00c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 397199802 1250 397198552 397198573
    0x1c090902070f02031002031e01050d080c15070314070e010c060209151c1512150608010f0c020d050f07061a182203080a1121100801090302 61
    0x265002480014012400400541141e50110f403626402c06607480d040e99020080c404a24200418501a0b40d5003c0a0030b129504010010b14216500b00c1d00410b00c00001544400c0b44205111201203e070740ca85c03110426103000003025016100302c44e00c3d82180380081d8002515a8040e1900b40b1007940d041e034500c4560051565040002c2d404510003075400140c060030005281c0713510000341000b0000c40550454090f00c0000c0005035041c1d1036500f6103c60303081100303100900e903da80c07444c221500070702e030544a01c0310009040010845ea030032031616542403c1a015003c295500f003e0000d003481d50859109501c0381d00102c40314050142e0150070f070441044400c003c500c445e001500b040c0a03521401e28142c00d540001501059090011000c0584100c00c20681e166070600c0c2c4050402090010005c00c42c0a0f50003c01c1420000c21455100c4c0e9a05d805c4030459401806542a03120182c51440700c4c1422890501c1c00884200c2e001410061520310110741d1240600420045c01c0d8107800900d0300004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 397201052 1250 397199802 397199819
    0x140414070f2001021c0c020a02010c06051b121b040602030a030207080d060e0a0b03030a05030708090703201302090d150f05160201050601080115200312010501021c09 73
    0x600c00b08910305108a4a182e9120b002031008103203141d04a00c2450180d4001005282500d000319100d034199000f915086003d41d8106902c1c8407081d5101000280a03034420f00f410040c419502c01d0582280c102058004c40d000c0c400c00300e540a801c0c0061945c102c03554a83c00c0c1d28891085001c0c0c0001600103000b0b404289000750040d0001a104d1041030f41400300060011040f510191300a0320740c480310740180030300b03080e05208651a175001034000c4c42c40d100c0100380c080c100f8030014003a00c1c100003d400014692000a02035040503640c004050002c4420081c1d4400c1d032010780b404998410710581c40b40540f0000148219a9000f40140c454929200141c0300c03501d0141044d801400881d44031020200c1000c610710800344100c0840300c2e2107103c072240440080c211540104580e06004104006002c051507007041400c07950380c00e203480440800d240340d00705450941c1d02c00c40602c0d848040b502c024542c015070302c076506032402a800c40722020049426030108243c02c145231004500d511070300303200c043c5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 397202302 1250 397201052 397201067
    0x30e030c150a2322060207030b0c090402120411010e0a05030607030e0f03040605030a0f050405070302041d03121609030809090402010c1e0303060503210a09050901140414070f 77
    0x3680c1550a06210f00926004809507000d04080d590003e00c0c2660101c030b0a11010741031000d00110b10050040504595404801c03e1000c1c2c02d50390070031000705800f0041e44e615011552650f8456008041900f040d1808195030028102118040303031030b080c28010300c2d0804c02404401c60703d0080060035070703482d0160706400804104203810001d00440b07804444140d410001400108591f5881580d60b10b802841c000480360055a403044942c10328061001081000981000740c1e0340481d0300140740d4401c40401141d01c502e84209800a000100345500d10885200000f0f02c100c103040100c00c404003d200e800c03561203555010050600c5000c0c02045811b0500400c0c041e0b1061041c141400c03100b40d1a1184040a82002c41c5680d9202c0328140810426a050103110010202640141001003403e6804c9059854064019528200100710212194850075003d801813034050212640c950711165040c40044441d8440ca0289051411056100300c28140941c4613880340d5440404070701c0300040459800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 397203552 1250 397202302 397202327
    0x1080c090102070f060908060721050624030609060909030a0f0215010b03060312090f040b151306031a0109030201050a020f10090302070b040f0e0408070f030e030c150a 74
    0x62040e0500400d040c0100c06072000641707055299156010310345a8540c0c94008020010b600700164564590960400c640d00d10341c03031601e1102c011440313a450001103280c0648142d20490041c0c07440380045c41c100780c071400039030184034265042c040c1640c540080c041d01d804143c440750300c207074410010000150301c50350410103115180d105880745000d00c004c265002510a0b003214a50100c00410301581e45000c11030302805900460040b81020000b0300020308450418410f103005680b02c102c8911555035026444070b45803944105107032190040e5031010301071384240c0980000300303242c6a45200712106440e004130440805958290b60b86007076600449080d040721080303000394481d908690b404040284600a60010082c3c000103003410f203030600074035114865100100c10107003007000f88203405844424500752011580100340c180c449203000d0065204140020303110a2070311540c14101a44000100e810490403001c03200c000c00c4600030402e8550600f1001e03420307a1030410030111618054030000030340 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 397204802 1250 397203552 397203557
    0x7080f0405030a0605090f0a03140c070f0303080106081003051903111b0f0105030f07030b0d1505010e0619170102042105070b1e0d090818030d0e01080c0901 69
    0x2401e9a5202080c504841508119071040c0c80304100680c0d0f0000b0803000706200528401080c0304900b40e180908100c0142d0b82c2081c0d10343c80010f008000900070030800c802040e080303141140440e5039050042c02d80b0028040d9074005101c00700829070300c0c0c4090f44000280ca0700305010300f10880301800e140d0f0107002d14800803014000c13074205580c5440d0040c0b000d906008031404852180000310401c100000c400308c103540d418071200b4001e00ca504003c07103040ba9409500d9040016000d041d200014940c2c900d1850014110561050812040c040072b400c80d5040b038410b002d80c0c090079200c40c0204505440c4003903503c5000c060426040101a0308102c841054400c070200062030b05407645e00341c000728001c1240100ca0b41070740100400c1004000c100d4540201000c0304801d00b82100e41c05441c540600b082c094600c0c41002080160b401c0c149540300c3c428096021078019038503d224903a628650040c8140320f0b12034016410800b42d0103010b2900000d01e88016541d08a007070362030707040d400050b400c0b81410504 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 397206052 1250 397204802 397204807
    0x70509060a0509091005060103020703020c040902031606020d0f03060501050910050c0703030e0907031b0513090204080a050705040b0f090c04030212031b01092f06220801020f07080f 80
    0x14180c40b04200075003c3c4280d0001350041c450717071441d81001d607070015211504141c4100710304000f09a001c901203907006402c5802040c6034030503000080c5821461003107800700e20303034000c0c0008115070009003604402180707496004400e017549405a003203a407240b00d4280440c10802071b000e41480c1c1190000841c404c503007080b03402c00c160010340501d0200c40e600110081848900e03104d04a10b84440d456a0001003032505000880100041e80d4954030a0448001403141c041240b11145014805030f40282c43c4044c800c5440380d60714855541e4510500d80d080e00e20703000f4000081840c0c14913000d10509201c1c042e182816900242041c000d4a81c401840c100c40c5907010300c00400183d0780d84411800c40b01c2d6240003540c80b558076080d1080d54a013008040401c0f68074000c0000b00080f003098500545049813284107440800d1903007404140000c1d0004a0341c45a80040c1131401c3e441c5840800c0400812079003030a2605031580a0390f400c070311a00040074054142880000b002440000003400c020106030042030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 397207302 1250 397206052 397206059
    0x90e0703061806050f0903041217070c150206160c0c0503061302011103070203070605030a0e010603080406021b0f0418061103061f080c0a020109050313030b070c05070509060a 77
    0x421900300c0c14100515095219040042c46404d02940d03401c501d8084440e0034a0400300725942d41da22552240c200410505200d01052112408480340e008800c0c100361a61007249240c0800039030010700504000c11180e0348103800746840003600c5840b58200180002e50f181d1007003410b89428800080c110b0b0a2101c88501040b203441c107102c500c0c004d44607840c03540c401c03581620000d03100e041c02c02c030b00b090198070920409025070f9000810344200e4040d0300b07010b0303942d1722070014402c00781040281043c125800e021700082042046402003080b9a095401c0d19050714001c4558000d0710700d24040c03668000b40a065142d00ca252540c4045004034402607007041000c5642e0300d0300c084d1000d8400500c50701e000401008140c0c10980d00002440f11a00410a420605608080c1c00c1c00000382c191000310b840411024051030003540144015034200d400c4a03120311103004184403101403030104a44030030010020840b2540111148004c40351300801034003143d07040038203201081034010000d40d4000382003107000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 397208552 1250 397207302 397207313
    0x90311030c150a0906050f0d020f21010315061a160b071206050604120f02040e030c061005010f0c140705040204060f110c010e0418080a050a0306050f0a090e0703 71
    0x40002c0440309954480040c201d024041d00682c4c0d0106041c0041081107010756105401201c158004811006881d1026800420503c1c01a101c004094492500082034222501000c0780e0481e40702c1d060f1000d2003a1955a1041a1109440703407440119a82c280002204003c501415a030b403940420407400d05003035160480107030401c2d500040400c980d1081e04074550450b024480c09090152501ea02d042c5c81c0000b031100341325120030040d1184030b9410503c400c5507a19041041b500e95400d00b22611000c0c2c254066444a909030b6082c071701d241c21004005019401040c3d141800c50443e00c0b480400c41c990b850b104201e1a00d0003580034580190040844d007070340c561001c1c03c0a401e0075620b004400c17030706c001e001d024182c00d051403100c04c3d8040004002c5580e0b0003540e00e01e42d241c040d1000710350a001aa00b1400000b88084010800030010649500740c40e40a0060504110269400d00c8801e5071401400900f039100940240c0141c4480014445111a03800ca28000141d120860719002d50b00d8170b80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 397209802 1250 397208552 397208569
    0x105040b101413060c030e100e09100e0709170a0203030702060f04050a1403013b010f0c0810090e0a020609030a021002010e12040b0403120c06020c0105160201020a090311030c 77
    0x4e0310101e07141750011070925902ca00600920070f070907543c114140c4041200509001c2244005600c40d542040c0012880c031444865180181380c1400000300c54240604050080c5800d4000c00011801e800c1031040049400901858250313000b90245180008030f07005c0c0409075001c080c0d51a00303400c08010004454a480100000804608400041403d941c1c0e08142c2500c00b0410003904102c245048151840c9001c99400c046192005014148000b058040341c09403403002242c6a02c03503d0941c0d444c0c9401d401000980c480d800802440b290541c03036240301001c0b91140401051142d2010760301d0001414004010486c1c8080103044410254690b07001405504140d481000141d44840380c100300c0c0d0100704000e00f040310042c9440e90070141854400c02960043c2c3c840076204284042d007290705d950003412000c8030243c0200b001e640e60404072008501800f810740e1004c2d01c00c00c81d074604500c841d20620945020780c0b80d560312005054650f844541c0070078090305615034075001c4c40c441d80101780c6c1c60008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 397211052 1250 397209802 397209809
    0xc12062102063f15060d0609020d020901030e0d12020706020c0f0a111005030c22030f02010e06160b0c0d0c0206010e06121216021c0b0105040b101413 66
    0x1442c900385038400b014003000300d0364441c0d8848420001032003c81070011107409504c92040d00c070035850714100c581070001380c80f00798400d00035144006204103005816400400740144282c80c184040244c08200d2036071605401c10301000500043c114a44940300741d0000c01c00e003030081e0009800c11128274140740c20000480454805540180c0000040090400902e0704010b4100c1d200301c812a1007c402612074840207118816078000010594900c11812500c18501e81d6100c940200090f143c2c40c010410040c2c4000030303400300e03451409020181c90315104450010480c20709050312404160390725200003070098051100c1d55002c0c070005601404e02d20903080448500da0051415514042c802e00b8030b458090401d40c058401b88408151566000070031469461106103126901c18925a2050310701000c800001e50100e00c0107240c2004142502e1030751071407070250903202d1392a40d031001008115601c4400f400d400120240d00030700c816000328038217208420300c803101c5482e00c081d1341001008a0010781 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 397212302 1250 397211052 397211107
    0xc040c020102030a0e07060c0f0507030b1911031510090e0c040906091419060308071401051005150c0115290a02060a0c0c0203100c1206210206 63
    0x41003820b00440c099800c08000b0340000c0d05810b41400710003008e52035075182c040e201d101c2c480010740800c54100308050045400404810380390801c810801e600c08043d202152485041051420580c01602c045030300603000113088075041074503042404119021210700105101103213100050038403292400d03d20801d0404182c0d952941401904411038480c0d402245010707140502c80125003903214201c64014a0141128094154a03003c2802502c440d400040407000041044010070030064070b0303401030044500c000d202c550350700030b1660407041941c481c803035010803071041500700510300d10020503500341c1d060004240f481408003003d000c00080e0b8056043d8004204040c400303443c103284034440459428406502e44201c0c008025629140900044600759403001061011400b928400840c50b0740901543c50204820010740300400d014400003020603200015241d1404a0b4071440040c0c6001100d00011020102d2914a03c80811442242c0021040000c03042d15024a000c0109850350744 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 397213552 1250 397212302 397212307
    0x519021f110406080c0c0102042709030e01051c0603050a020f090c09191205010504140c0607061104030507030507030320150702120a08010e07080403080703020c0c040c020102 77
    0x3040310441110303105000c0604507140c00d0910380d80391140307801c031001c643c41894013165685078001d020655200e40d80c9a21419840014002106078400e15408401c8c0c00b42c00307c60718007201502030081501c1458000500003a407184110000b90b02035009003402d60f40600400c0c00445c521000745088801942007a9840e9110504401c114500010544000c00c2c00740c0382c2e035609042c08107403d03d40c0d014090303505100c1c4803101d481d03001c0740d21088605401401500f084007906c3c403150a02c24000d01094809403441010b0485002c003080000844d03d003100000780489103444c080b500d070b182c0100180170f1000110710b410800080801c0b01000548040d500030307000303000c0c203900d1860040c10401d0149a0418a51404645010a110086000583e50401c44c64111107070f80e444000b01d081810801c00381103850400700711118426800503d0505a403441d0030b1004035a210038500b502c0b246001c40300140002c00520005400f14402c0c2c000d041c1c0b010704181211400b640020015050740c8060040c00c0050307602 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 397214802 1250 397213552 397213573
    0x325120608060f09010213141c0b090c04020915070c0e010602030d0c0e010c03050d1401091424010c050a060207060209040f090203210c070b040e0c0c1507051902 71
    0x1c0c0700103c1e410443c940002c62400049440c002010f41c038510607242040d421401001c00e03525a10340302242c0010540383c08108000c90300d420343e143d60041e10840c00910810244c20f0603410540300302c0d80b061100402d04004a050400c44a815078403070701044880000c0e0010014481b03800940c060701030708858010b0f50f29a2091300c0d00e401100d040502210401149642019050341c12100701d210b0240c161030919640c50f000e00c810b80183c050340c4035800341090404000206601c40b0b5006500c205d05003e88150b8645aa400030310444c0d080301070742c2c062034880500b41c5d202507008607002c40c80c06108405035100000e21341c44220898010700d00135501daa0700040c1c2e108a6140500c281c118030115242c0400000803143c01080c0e590340507555150100c0080c84000641000e07003c07d0f10a040ca80004079282039071540391948050300603110b500c0790b02c00810007082c80c0e240f45034152030b10940500000d0000c0d1212454101d9041c2e0301600060600c070080000001c507040808044440c411182c000b0545183c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 397216052 1250 397214802 397214821
    0x20a030207121e050c150403110f0309060909060a0914070e03030a02070b1c0603080c070512031215090f0f13050606060a030e03070605041106032512060806 69
    0x907081c20790400c2000141c00340c9600040750084460b41e52042c03130280d45680e0300390100362404900310954400303410400d041008040e4052510a501c10888094800305202074280e50b42d40d004024510f540b00800b846800442d0a00380180755121200074a07810381a41c1d9400083c08455031445503011090025080101d9140c00040781005a071082d401145050710348000251186290b004020340c01d000000c104c555010901c0744801c9400d02e152003042150303030301c1c0341c520120b40c0003529086860051a00c00146440c20303030310300c034404810180954a8254200c028217021080100a0162001841ea0824685d15200340d60ba1040c0503050080c030490030701001c100d000c18401400c5110000c0404140d100041b4007151042d0010416551a51120146c42c0b00364080e20000415004922000c2060010b0091540107a40120300900540c8000e40b010001d0003903a1100725001141682c0c404c680c48411461487c0a0081b4001450b085d030700010901842d906540e112f601a000b658803a030700740480001e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 397217302 1250 397216052 397216073
    0xe0106082401080f040203010b1c050124060f1206030f0203010e12040e09030c0d0207090e0a0201080f10030213020c06060a1202100c0c0f03050d020601060905041e020a030207 77
    0x3003120220040c603402080002c003d010020030720b1003400c2c240400304003151000d4200425100c4020424a400105000c4150001483d04001d070307065803d2040310300d50001925605103c030f19a200711208a0342c207041e0b043d900e2240d00110340c010444c0701d00650710660f140e445141e02a5110704203045c0c040e001801090301b900d00401041090b600070340c01070115110010110303000c840a41504c10983d989414807036055003d242010010340c003a2020100400f98046107003001c1d50310945080085070701190303c0719036501010000a01064020f03001c200c40102940303400b540031100382c50540da13180d20390380441c03172081041d41c03035803031451b000b1903002504041030004035444403080c0d50301c0302107500e4890655850110340101900540c012101121481d00c105602d0042c580c009030030b038214503a202a010550501440241c50602510304201c548a101113000b41c100c07001580d4010340e141c00e10041100900d42d40344107140100c1c401c0b500200c143e4881c0081c142d0060541c80c01612065a801c0100c12030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 397218552 1250 397217302 397217341
    0x60e040b0f0d03020a0213090c0803070b1503010e33040c050108040807050106081c0f09060809030c190c05102a050604120f03060506090f0a0e010608 66
    0x5505010122040740c46640300c00c0c500400469070201d01e6010b608042e42018441c91000c0e4018082c40340e1004040440d400003140c0b28840c50304c0c0f05000e1b0340c85400c0d603124040c00d88004d001818090200d03a41c5e81c4403003070b0744419a000a00010314900c039800030301d1030103c0c0b021480700a03503900c406000400e0204003406688114500303200c9160b2915035a00070310b004aa0060310305001d010030118040c018440c05840b1501e911500810100342c840d00d541c3e955105003080405060768131000c04450511035902c1c110b905d203139515294242c84c00c040091760307022030080204190344010b1102001643c0b00700702403103242004d070001000a01740740c02c2003005208107410040c040c00c001e295284004c3d45c041c04c40381e0400380f941c05036400460b841e000b01c5401c00c031040c07001d0528880d01d001c1c40705201c040800403508400c140c079483e140344c2a046040c0c05031403641c854980e0214040c019030440c1e0030300040d000038980e0000c180d03a10302c54131381070001090602a00076000241510081110011043d1800390340c0c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 397219802 1250 397218552 397218559
    0xe010201090302031204081c140109021216140d0506041d0a0b100509090312220f06112d070803010519030203070803070302160303050a081f090204060e 67
    0x40e01002d032006581da01c50005c0b510b02001c00300000405000e804001d03a201c03200203400d24900c0e51090030f0524050003151000c03404403c40100002591120340c821503c001c45001034403280756441108c0031403a011589050b1050014620000c0d502c41d0785da00003081c06e030208100028181c10441c040c00200e4282141d885442d00401070654481c80c00000e880310000d81c004800c12490b1740d0090510bc0074440c1e944215040000b040a1200405000c0040e00c84440712030f4003040c65590383e5040342c030f03a10202803020002c0a0a0010040481c5603c0071484001e8040c401c081400c036600c403c13a01541c1c5c020f080d240c1d80c0078203408420b44800b1510448000000d1000000d60505046441d00225442b041c441d1034452061404030b03c41100c040c8048900458006040d110f69070395038424a9141c0e440088118010301030724031000e0042203091006020b0340c0d0581e5940342000e0101d9002d030b46a00015000001c0f900190b900c0003c000c4000c0c3c5008060440c140c03025071598604800030b42004018090a4403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 397221052 1250 397219802 397219811
    0x1b09030c0b0c070e0702070b07060501080d32131203022e0504050a02030a050d11070e070315030f051e010c02331e07050a020309092509060e010201 65
    0x2c0c03920001407000c01e4400c076040030851919001001da2804690768848039010302c0c0803495005003c5103034880c50407914510300b0350b50010207511b400c4503080400303941c066020030040044200240c0300105951a00b020100f4146000d450b0392000c1d40154951340410000110755040404050381405188030711048440004000349140c0e100c0c1c0448294181040ca2107a07403140040e05200040100c440d483e034000d01617406200190904075240c5103682843d00c04075004103806408001c00040f260b08031404540602a180c0f101002240984821810070364a80300185011001c1a00e101c00414950322900045c00a80d400c07108280354002161118a02a4036283c95030703020580119000580007410702000c0c403103015607070504080304140b06c80300b0b00e020442000c110580d429100c1000455140000c0005503548454080325079104440072040103802c140000005410101d6100707421505882d40d44050840e960712110840d584240300780e00050341e0081c20054290081650004480284000d20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 397222302 1250 397221052 397221067
    0xc030c01050a0807031e020309010c08011a09040b040b06040909030e040203090d08070221090406090e0d1202070215070615050307030b040c272d0e011b09030c0b 71
    0x1000803d0041146092503192560700c49141c6c0880c280312455444c91a0864490034510040c90007801c40d08a00004104802c0003c0703025800c000c80c00c0b1039981507051552408045100b440050601030a4660b049038444609107020f0303460201600240c0b5018070f00141d0301c07500e03081c01446010044142c0340a1441001800b1803480c0208130b28076245414100003909880d110340880c41c06210311150300c0301e4070100d800b000361204410014907448100726030500c1099121140e0400302c4031610b54008071a813004000e6041c05024086400172510700704c400604106054010640440040507803c00c80d4100158810400c240b51145200852800404c407070013034180404287d070740603580001390142d800d80000804101d82c002c1c1d10307800340821802c0c101da0381590801144602c810b0700c80c0c1021983c240248900709070b070951040c144d00121900c401d104400708c04c0240e002440050844420744d522030036a4816003009242881a150841c1d032185151491030800d070140070b82c50742041300e16060800850b0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 397223552 1250 397222302 397222307
    0x3170c0c041823030a170a0c0f210203010b09180103031b0809030f0d140306010804032012130e01230d0c090504030f051e0a0201020d05090c030c01050a 67
    0x1070003542c2c8100719500500c00f40890b000d00c2030384401c0690a074803001a58600d070581c0503041000c4402141c079601000e031145100c9070161852261080000303007144051300308042c8684000e0080000360480e041101301c250803114183d03070090f0800e03810b8900000340e20300c050604102d08191528803048a609a504542c0e00519070f403001c2c0c18aa1786c0c812032000d46c4050040a5040303818458000301150700c1940c103400300c1c1e611000a440c680001c2160012810070041d283c07000c80b4490f1105941e210216541c5135010f884070624262025599480040c03c940e10000030046407460300c185581d02d80c2c03a8005130006000d00b9880f50400c02c2d2442414004112814080c0030030a2000019030429180e42140404500e4200401c03001810001041c540052500a96808580114040e076204019071103106070039222440f41040702c0818140f8540c0880307054035503001074408062544005458003a20210500c1500d10680e5040001e402900b0000c0091400308011b18407440282001400c06600c0b4002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 397224802 1250 397223552 397223591
    0x307020102100f0b030307060b03010b01230a0311030a0603120c0308010509090c031c030f0501180e0f0d030e0c15070602160b0f0a0e060105060f0c0703170c0c04 71
    0x3000b030b02070f142d030040141d18030107070084140c1090180c1100d4032050603003440b501078040001030500035440d00b0000b008075440f940d40c0b49a660182c07649000301d40c00c0d03101d50500d107910603004041015510101e0542038001c4000840c0502110000440d08505504001d5220300c00350080c0401d00032030030440c900007030301f002d100c604440c000c551803240c55680070083d500301482c2110107581401101034440e04011081303000c4082110583d01080403141c062075110440e00c080c0203504c0b1000d2622001004400c00fa00a03c0e041611041a01c3e10401107407205c51414000e0401c0c88040313511400083d100076020400d90032240001c82e83e41103c44100023100400e072103403c0300900820380000e070400d81c900030524581070b0300303610a910a14030316158414805040080d100c440404d4100a8000b92010780068024140d03040100300920700000d0851081e0203031321182078481a030140c51000030101c0c03011a030f0802405c0d980545281d84088410b040ca003001003e079042071295142c22800051244950392 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 397226052 1250 397224802 397224823
    0x40203150108090703050105010f0317042402250314060c030103030c05161805060909030a030902040b1306031202070b090f01051209011505060c210f0403230307020102 74
    0x1e1610309500c2d442250340c186892a0005082507007040000101810106800b0b001c481c0540033300c1c100840410340c4203125108a203d80d80c44503401102254041801c0b0302c0b01034003a0b40500454155800d0146e1240e11800071800721039419028040030418061800092a1040c0004011f00101c1c604000c60301c240340410300010303042007842421b007000c00c4010490320074882d0000001c2549176a48180344508024403601038181981040301242007800c0864150b03005145401c061418984e1884040340107191480040e80c0c81611215503031015228940117200000b132085001c00d40c50300714141401e1031501d480300401107600040040104400180640b41c00010840710100410528070040b01c2900400014441303a00710034003030041010f415070010712040010841501916074840c2088018018200c0c80485500032124505804102c0080c0c40601d0030f90141d003504002500c0c403d0003031364120b5041201c03007000c0c414240761714800360124014500e403040000c51420b40b81c0d500003500c3d03108a08 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 397227302 1250 397226052 397226057
    0x10204080604031404172b020d050d1409011b080f04020d0c09051510031122080a0b100f030206120907051c0b100b2502040c1d0402031501 61
    0xc80305540909584205c0e00207148507400310141d82c0e040f210395922605c81d1203810f490460903c0c03e402a0011481c00500e0161198014041c04500100c050310641d0024406403807041e40c030b800b0701c540c800c040106180100c940700d00004140303c141460711002d00007101c4180910420404024910002102c04ca03886075040d10702403d44001ca2808d280d107000c0c3c0b41c00c260b00c0182003504000300140405841c81002904403802c2d41001000c0c10150b088500c0300008682100042024454500d2540c02c20310f45544020501c10900f0b60341e5a0103030400e80440c00442c1c02c120004148681900085a22005005544440e40c146803070750303000805034070450b03044c160f417440404000380d242a400e01400c0020300e800f8041902101d101c5a180000d082482e20441d800305000000c545840c0d010286907055907014100d07245010034011300d107505003444001001040c0508040000141c59a000f12117001150762038120910115a440402a0f0322030110580228070501c00c01120400d401d40d101140203003030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 397228552 1250 397227302 397227317
    0x8070507050a120c0b0a02070915031703090d05030114040c171305060f0610082a04050102060f040305180a0f082d0a080a120c1d010201020408060403 66
    0x246405030400e48694012940100e04600000f6610007400e40c2d008850301c20000d09074071540b5000000c083d130144001d0400140d208000c1807003000000e5100303c40841c46c03035075441e40c0560b40b0354990459600440e03811002076008810304c001c001082006903402c1c034a90410034290f42c1003484045001242e080d0f003910550b101e81480000d24007500d101c50400b110815a80da5600d000b8401c0d402c4080364503000ca0719446220b0015000c05103d2a0071405044000d00f15014001c406030f0484142e48058407103102c6012403264035445480030170030108011b2000c280310751290f29100003e410301c0c500810702c00745020403d0410000039030040c1111322090228031031a06500c280350105a100285410030320703014405440220f1108000280803403109003904c5000700501449201503d6540c5581000c4200d501130601140041e011402428001d156450b1100c800c58410070420241c1d4600d00c0003201103822440c90345100c0042d481c112011500a0002f545002c1c40c3c0b400d55643c03000018005010041e41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 397229802 1250 397228552 397228567
    0xf0303070c0f020f03060a1b11060708040c1203201f05070903141c0903151a06130303120e0325150506090604060b091002010e031303062708 62
    0x1a0320101c06581d81c090704071086454440255001031075142020040c078402c1c4440e81441c230313202c0c0100410b0000c0c2d01018080e25103800c07200344c138040c4015004954100d0344d400301080110741001260041c03400f960318900d040b103a182000c0001078822082c1c0d8030a4211118042e003011904802070303140760340004001400d6440f83d604603010555034000030019103503491040c0d41203a002600da20070b100100e60004000421030420341d00140d691200502c040700d941c550304500d0705554040388880c1301110580e5100d034035a200140640d40440c0c0826401c800d8000d0900034550f101805031280403031580100140c4860070805c0342d69004015003d0723504204000509a400c8008000101c0039030700c03822001c03202280446603009000100c9d4818042c0980d807000581c40d24040c0500f6044402444c0c0b04e0780760848032001c0c80b40b45285400c07044190f6407103c041c000601c1c03040000300751540d0902c2400303200300d0451404070302362800da00c074003d10400b18400c495000e4680364105c826603684861400d654001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 397231052 1250 397229802 397229809
    0xc0a0c021203250204050903071718150703120e03180303040b0403050a120216050f01021507050c0705060405060307050d0e15070f02070e06210106090b01020f0303070c0f02 76
    0x500b2280e4401d540c00e1003401c9403021400707003c50801902c00c803028040c5a4030000100d0352809809806004480450380711b10104002800410f040703160b00000f802003150080c040303101c2c3e80d04800d5220304c102c00040c007081410782c00300c1007501000c13082d141441060210034005a49004401c1d000d181d03d6420320b408003656030304000304c1d8020032092412945495907030a1068a42e0801c2d50151204589448242001c51021640c41035034981240c0142c62a41403606210000f8004601c00d0b05610601019403082058510401e209200c680d6495580780c600f01903d608101540d40501d00507c3d06200c24409940e804d001d680d0700000c14030b0404d40380d0090022034800741c051030031002518019200520051000f0b1600b10380700e0307442c43d02d070203402c400011000c982d034520b24400c140d05c6840090206405103000c030001864402d581100f003401e034403e060103500711101540310008044d80c0d00c3c50002c203540c05006c40300c42c00c0c0d0203001541c207501d01501301800c0940c126000800344445914110115034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 397232302 1250 397231052 397231057
    0x7050603190b0a0603060f06090b0301030f0f021e03250b160602041d060108061e01030b130501061e12050705120a0b0108060f06041a0415020c04050c0a0c021203 71
    0x42d001005018059070340e02010f40208100d000e03540031540d4060b008503d060203241c1100440e03892040031441c503840e546589002d00e9061074100d0740703404980c1c00c1e400941e403044165200c1d810f0915040c1036482242040500e011400d85004c02000304804500450902030400c0c042110350800801d559081e0f50f407022500030404100080840b03201260200340174402400890700c8500e01c0480058a4450703100650728139408940c115071100440c200f000d41c03c5d01031071481c100d1803810304000c121040303800c0004012141101c0c42050f00390741c4000403c6100d80c010391a821800707007112040c0415408d85801088074490503021110700c0e4803030740801c861f0b920a030111000e03615041c0d4003050504051420340003030910005074500040b40b08000c0f40b800d20340b01031a20601c0c0c000a0115280c00c0c07a269103000011421041c280c0d4015040c0000201070161107110045080d04d139024204418800302044211140a04903914120003030080046207038000d802101c00766012a1807202521042c035290307183d403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 397233552 1250 397232302 397232321
    0xf0609021f021203190c12020c0a020f01082505040b120a320c04120b041209050f240a0908010e03070201020d11030c0319110705060319 60
    0x194140c4400a160000640107801c001c1d2160b090714035514080c00100fa15010940b800c08441182c140c001d07001d08040d40c406c00c060041410202490362416500070101d0300141c0c4107000c141c1002030840304600e4000901080000242014502c07402e115088041000c0c0c2e1075150007109036500841c205060040d8103032801840440030060b580c481486a01e1603125080e40c40361181400e02200d028210880309500c14150700302c5800c41c01e44940303840907502101015100070101c2908200124003032807071443c0001039034010401e00d4240d052500d0003000c00e03003043c000c0c81c08100141409008503501c00c400301c1044c51040320003001d5038440c6a017600700240d81149912613110300065107402190008200380c11201c484000b0040d40e001d1589072901d910440000900580100400008540c05100409844140041168142000e200c046483c45e4003040c0b43d510321681c5503001504940c1e0000e20320811242c0031024000c0075203400003090003408007038001618a01c15a4001c0702e021401e9000c080d21 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 397234802 1250 397233552 397233559
    0x30d0804020d0f02030109080c1504080a030b0a03050f0102120705040305060a0b0f28230405090a06050106020106031e120e040f1104030501050c0a0503130305070501051906080109020603040f060902 87
    0x10b6000ea45400b48c0700b9803051707440704424020180000703401c803880c600c1184510307041118189000207000d0304070028140c0480c6180e010b0304821010012640070800c030700100c03c0c00c00005907a11001e00d00c100300d018005001d4410090200710610000d0008101550401720415011a00700c0c11400040c10602841c0d60f000c0e0040d004404072039804d040500e0440e40000c22540c106215a201c00600402d003951480301010001c08400300005410158000d9034001c0090058a00303030941562803c0544800382d0146e001070f03440341d10a005010458500c522401040e1608404510140c1d07100e41c2040004102c50080c41109a0480d101b078865030030954400c030741441d0811510300751031750901ca2030700039010540d03841d840c02c400625070011840c110b6610381c05c3c40c1c0b141400d5941d08185100010030000c0220104003080c088640025403d008084c010341a040345131028000c0780013603100702e075000d0f400039803240c0c10701645002603140d240440381c1180c0c000c01122800e6445c0d042180103440c02001c004e41 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 397236052 1250 397234802 397234811
    0x40e0108160807270e0604060609020f1b0307080a0203040504050106030b0310050709080d09180506090f0a06030b0c07020102010c0201060501090605030c1e0307030b0f10030c2106030c05030d0804020d0f020301 92
    0x410b1000c00c1b124412803180204000031903c076110501240210034640000d902c0402945c014010f120014011400c003050131030385402c0d030f156149100e9030000c40001e00542e00c041024813051825000719405810b0a00c0c0401c08903503100c0019688082c1c0c0303038403100380d40c2d40c03200800ea43c00d201302000b1002d402c0340300c110744a001c8100f000900c541d56a11411896002d240550800c250300f0f8001c0b11f00510340249041b00ba43c503802109000504c002e0801e01c3e803541d540c200000040c0130a04c010740715080c000582034580c1d1b518000a401d50b2103910b01a011649004024000c6a07041892003003694514500a9180c0e60303060000c1e00c15100d4407845d054041c01d080811011094144000c0d441003440d603a00740400340c00b880c140a954031307601d4144c582c001c80c0740c80e44200d4184640d001d03040b0b003802c52414898007501045480c613901c079851420400b0300d4440100b80700f80100b42884c0b070024482503000300054801d8220042209030003070002803081c00000040801d014240440da07008a400800800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 397237302 1250 397236052 397236071
    0x10519170f030f041e03080a050c0a0b0f2d130c05030a0b04021804020105042c0103031e080108060c090303040b03010b07170703080610020a08040e010816080727 71
    0xb03403076070491710424103c0380d28030b20304040da080044444000c99034028016410040320f075030700345e4807a003041d1a096078030300c5001908000b04042c0030102e40580c545d203d20101e107040c0002200c021200c548150200200403030039038a43c0280314161940c0c40368001001c4c250403403803403618403000601a031005504d1321501d0102000e201e10144107074001c9108031034000c001207800190305102c05040314081d01103441880704010401b031810208000d01490104075150100418801000210a030000d800042140d60003100340440444c0c10380c40c00880303080c280c4c510b625045e0f03402e0307036a500185a6100202d01080c115115102001510302070541e42d0f540741d4a03580c40c1d80c000c846940000505581c103a6184100d00b4055074120112454580c05030b0360304a182d41c80d207040c00220b0050385901030031403040d182c0d40c102140000000d0409819a06486c841a500d00101503150002c403034400b2941c80910f00c0d0401040000141950403202845545161a520a0341c1a19000b4034042c0713091034181000040c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 397238552 1250 397237302 397237327
    0x1a0303070614091506040216020d0b090d02010207170a020f0d03020a1701030206120c1c02090909150412020319030b01080f0622110f040905010519170f03 68
    0x1402c014418002684a07a602e120080741e6070380d8540b009200c0c0c0f4113941c01003089401c2c550010326240380b200a0101c00410698080390340c0410080041c0c3d5481806c0c4240501900107014507149040c017440250708168003030b04c0f8407031446440c0c214103c000d1400a50200c05c1d5009200494420741c1e2442500d01c5001900c0024019601c00455980003803440915106c0800b6008100c1d416280c0140030241408000000d18110120241080483c08000d01800c641103852551188490504002c09a00c03070009005000030420044c00307648003604441c200003140c02640c15550743c01030704103058070700d0030a40010603411071080055101803401445e00710480660540c0080302203903000e80e2000b50300d60300c2003440c82e04c441007901c03140c3d03110880d4408100c200301d00d0409451800c106100c001843c03c221aa07280d201d1340080003c004140d070104040080341e9003032050a00501003034407500c0d480710320710a04403603581840c0203004070900c0c0f800c038081c002c0d003003080504911010381c01120f5450350788440b034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 397239802 1250 397238552 397238561
    0x1403040f140907081302010c06020f04090b0a08280204050c07151506050a140d0608070e16260a021c09020a09091502040f030c08030705101a03030706 66
    0x10000081d036890300000281c2081401944280c0d20b541d0b03034220507285c1034400c1326084200c100503410880c84200c42c0010820510040c1011541e601c0c105503550b24051044080d02c0d035900c4404c0c440e1107446001c200c01a00403a000202c2507045228031a260324900007150009003001021b50081d1500e000c00c07244400400080000500682422030701c1040007100394140c0f030451454064507080c2c600e003000000d0203000500782e00352040c240843c1450600c49501d03040d4200115041b1150346521081080d603100b80404406840340710700e00c50007480e2020003181203400c0101600b04101104072400c00c10b920900c001e4242031701d032641f40f21f060308100401030040d401480305910380c01200508034145181c3d52241d1840c1590140810f11214038280751030009188210b030544030070249100681c8640c02c02d1000384003400f018084041c085095040204461540d50405206a40204001d4010400004842c2803002e6100c0010800410174840c0c00744a1030a001b003203415105c045084010020355400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 397241052 1250 397239802 397239809
    0x1020405040f180b070207090e0105061203030403020a080310120303051501090311061806040609091b120c02032205040e0c130509011d100f0209060a05071403040f 72
    0x400303200c824110030001c41102c5420340c8451980103d244148009501154065485041d0f801a901060f94a050071426110051541302c016503450741000510300c0c102d250009000d4040000354110b141c107a80c00b075550150b40300040d00b251004800100b95003134912080028014045460307281441c549000f40140c2002e551317406802031400d00031f400651003400d10404590700300904214001440040c05025800206083c1a5030642032a8500c0350312108010401003440b580c039950030915000b103001c1107030311483c0c3d120510020418001901940114071500c80c441e20200000c1c180f139a00d000380d00c1c5100d190107002d80300021211302290404600f003071000300c8406a40600060a03c22500c0f51500c400d207000d26407107100c2d807850b21101c40c00390340207a070300070006000018098018480e14120418020032021154403000a86e80031441078000d00888a100610179070410007030302d00003001030203072030840c0d010000f01080100602018585da079400c0947c04081d0fa0741d55445000340035045c4402d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 397242302 1250 397241052 397241059
    0x150c02030c0d0803180c0a0b09120a2a0e042a0b09150c0a031b150c1101060501050d1a1c020102060c0702090f0711060a0501180605030c040b130e01020405 68
    0x10203480121700124441100b2100103010301c0f020350401503041225045007025940000b00d40300d1100e82903c1c01c01c0f005030154008c000c0709120018000c0c10350312092000c40b4180d82c0240080e400c0100ca041400d8540c2c0180e4012070030450505900300b0303280d0945a4940955040b51000000100c400084008004da010f003901d000f00200b4450a8080c06440b40c0c3d40200c0705548620710350b0001c01e1260420304143c420030b12800d84400402d44a03c0e1401800300290201141e030745500055160300503070b00c0b4080140c0480240005490240081c1031801a903035599409070305c03409640c00c11b2501114100440000501c50b01080d040c1e5141e000c4042107480040703015106040c0031800e000e203003000359440c00d035000300765154642c1e6a84100840610140c11042403080504024540c1c1070144805d034441d444c5800005159032404900d41c4841c0080c8090843c0185030810510458902103090b500250068901242c00c00c280b00200c0e41c1c00c2e001c0b103800790a9902e403100301c40d103110064004004640088 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 397243552 1250 397242302 397242331
    0x7031106070201020a06060e100801090f020114130618080c010206070305091e070e0105030325150903030c020d1103040306021605070807050a170d031a031504050d09150c02030c0d0803 81
    0x6502b40d900300c441656000c0c040c6803103e1400801984100c411b422080c1840000a051001e041d04845031103249401130008250b07464100c0080340c290001400c020700b0303220010582903202000103901d841c3c0180440c8101134941002403401e89080141c00c0904000c101030000103001d035109581c8072116805072602c0c1d00507420000a151a00005440f001020702c0c02c90510380609412100b0200c8207100308542100c081c4a560300e04c1c000c2c910428240e14001d450209814440040007800c01200c06c03401018058140c488000e582030010603a41929400103005945903c0b444030b10702c0d517135480d080007807452003403410200f01d0707003030210300300003100c4080d564000071a80300c114442620030086203010169000b11800c61a6600c680c210402b160000c0c050010300344030b180013103030a0a410020b05002c1505a5041c0703c10032100f08a00b50030051545003407032a0700d0800d0301c51000408030b0300c034440400c140317030701d90805642e01409030100e4a00000c2103120407060303e1400c3d50b200c2c0c204468042c3c2d4000d08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 397244802 1250 397243552 397243559
    0x5070b07020625030902101d04020c15040c03080424050301060f0c0201140301090917090108040210110a0b070e0f0a05060714010c0e03060907031106070201020a06060e10 75
    0x2103a0707004500403038054840401c444072841c0840d009850f81070405485003410405031315a2290380d4100301da2669100790b08041c42c03542c0355112403045c514a01842c4100400c049208001c110443c1514214202d840d1580300c40c18842500d015540010303224040029000850051103442c00c03095000005501c50810700b0f2006c03d0303a050000748550f202094010320001d540e640701e0700b20354200c284141042246030005590009194209070020704945540310b81c41d60620080300c101402c9410480c0ca880d180284c010300091481102400090096011040c24011603019000100701d07107460004807039095501e4102241166825600c82011840b840c01c20301503818094210b1a0205025190b45032841ca084103110790fa81c8000f0066840510301c841206d0b21070028011702da004680f0360745107290044240b0406040080c0906042c01a0740204010030005100d0848030304900c40443c0c099440c1d644900050b07040000781817009096a26046000c1200721440507804d00030811481054503081e01c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 397246052 1250 397244802 397244807
    0xf0e070b030f16020a060527031b0c0a09090203030d05090106140d0b04120905030a060c0201110c0a23060a0c2c09040503070222150b0702010f03021905070b07 70
    0x50740d6000f840180c103c081d090000c038100390006034000c2d030304c4c049075044d10301a8080e080e1840c502c2c40f07219802c0c1c0c1000400401c40c89124071003600030401e220191075004000d1001922401c03007442000d43d41c2d500c4030180807e664083c404c0d510240d03c2e5441c144a84d02d42041440d0081000703004490352102d41c4510640d5500f0408244c24100e0791140d40c003480380d1115101c0c1c00308003a80c81011000c002c01c030040400d0907142031100e240030a210300004114050600000b070700f9500e40d504410010f004c103100e514201c860002e1342089840d042140407100c80c84450f04102103404c4510400038070321074801030280d03400543c0d00041105a103941c1f0b0f203400c400c0c1c000340c8a0010110303003101c08980004030302681c03044c5000003030140c10a02c16400c680c504101a80402c080d005141030500e0800340c904440b012600c2c42d070040000f0701681c820503450070790030803c52412601071040c000e03040024070000751120741d0080e4100c40c1034401c0b400d1a042c810589082c001e0140d440300d6030880b6145208030200302d00303e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 397247302 1250 397246052 397246081
    0x301050a0606020a03230c060a050a0b0307120303060f0e0901050c0306010210151a0d05010603020f070b1f08100b03010b0a18091e060b010f050d0f0e070b030f 70
    0x782d0a5010306070001341038034120303590000071540e44119031134200304110400000004040180404014209518054501c0c3c801c5804c003c0040b08002e003031107400f0b80142e402180c1e500c10790312690035880d02840d076410110007d0002d07400003103509000101c080313144050924040d104e821042c00a001c40c2d542c440340a1070600042d0f8413103015078414000300b240e003802da82204c281c05661014a081c9550380b02465501103e0707803080d14011070340015801c00c4081240c000c4134090000c41c05d00b585455610031a2180600c50280c0152003c45040c0105801c0b820b13204181e001c4541078203051200c0d40d16054500d07169000d078501030314241d25021124140c0c0c24180200850031000070141c02e00755103000150300000340d40c8140d9850b04c070b0340c0e100200001030300f0021451001601e505034014030146480d021048880703c0403141d0500c2280461005c2e259480412142c0300c41310260003003a040e0316040c0034000f4046072420b04200c1d000300d203004a180103255000c0c0d803003481c40314804190303034480d41c01000161 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 397248552 1250 397247302 397247309
    0x90b0a060518010507050607030e0714030a2010050d0f061206021e0703020c01080f04050705010f02010e060103080702010806090f15011209050c0a060203091f0311040f03020301050a06 81
    0x1481070059a1442c04003501d0b001c40d00d10b06040c44c911700341c026642d590508004071001710120741d03610b0501051402c2000b82ca0042c003035054030040030314021000a80e54150000005050303240e1020702d454039000e40084441c0c660300281401c5166a01b05a02600903040064280c900078580b0510a1072801c440c000d40e0112034130725040309020842d07922410080d48c0f000b00c00500c10220700158411090b0810f009004660080e40076105640d20070b8001081d001d0043e00341c2c00c440e40e4141c01c0c80f010960200307a12003101d0302401c120292070240d440aa001d0700350030a990181d40100c400001c144a83c001c02440c80718400d980f0658165655020400c68070380580e041e10500c514900001d0807401c10018040c1e0790720050604031007141c582d0754000242ea502c180c0858840e0010111042c260410500d510040e00c0355002642c24840c0140226284a0001107901c410606c3c44140c0d0750f902d40a17a00501c100c0501c091410f44d16500c0750588504141e9030311049000307600c0d00c4000b030441c00d80d511801058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 397249802 1250 397248552 397248557
    0x12020c060702120a0c120209060111030a08041e0503034008070804080a050c030601060f0e06040b0c0a14030f030423100e0c09041119050910090b0a06 66
    0x40c81c00d40d0b000d012007514480c000722540d100303026221012900e006800c0c801480b10704001c00c01c0c5000c80c4188410020050301c0f0700e040c4a80420070040c208404000c1d036100c01440e01e0f050000c1d68590a00c000103c00b080d04201000c20741520581c1070007000b0000307501ca80643c81c240030080c440030301d80c80d10041d4000219008880075040d00303500c8443e49000300c14414050041e182c10704925441f422038030780c4103501c41e4140b50700c0b00815508011040c42040003001044000c2d0400d58074080001c1c0c804010014601c0070480e24010414643e0b82d000240da02030049444110389940040303c0c0701c0d0355600c240300c040da01d01160301a00010203800104403038000301004030783c0c4d055031229610500200b8004520f112510000000021000d8042081c4541075088110103e038007907904032214180109903144900a90780c100410001c229070814145140d401615a1000c80c052140c1e070640160160700400e500c4031030101400030041c0d210f941c410545001c9a0100010729600d0208085140d140c40703140007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 397251052 1250 397249802 397249807
    0x140a0e1e030f12031f08240703050c030a0b01050c03071109090304080c0d05030919090b0406030b0112080d0c0806040c031a0609010309050102070c150516060f06050603040f12020c06 80
    0x120707051801c800c000882c03220350014405034075840300c2c0d82000d4039401f0902190520300a000f03e001c680062103a0000010704080080e410000a01748840c4001451489034544503049041c00c2d034030a20450b400820300b001502d86031030107850914150f00368040e590b8130074000762011881c62100801150200e404002c0209440f00260007840b520581c90003060f80c840c0020f2200100d69102d50b424070b225000100c40d40703060203007807400940032070b50b8140381c543c000c80c90b25000b40005202c8000c0b1a040d242400f0040c80410000e152000d4984280010f02d00c8079402e11210b82004c035001818036000d00d40449040c04200c4101138214100d45000c1c1e61203405801e403a001c00340070708141008154500c0b040c5001705108031075488841c00ea034044001120900400c10013003000080040403010307118264600b061a080035050540710842018402030000c1c2d03a100c1449004100c11b6011000030a07019100c141c51785081d007007a10480340b0146090f544401600e51482c0b4861000c40e1003184080e000b00b1050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 397252302 1250 397251052 397251061
    0x90c010c020f040903021011040e06090a2405270f06040f020a05030a06120206030103060b0409061b030c030c092904030f030f0f140a0e1e030f1203 65
    0x44031504500300607600207007040c0d140107140e1070742e015103003119009400038541c1d880c040f40c0700402c0b9a0b003540c000c0c40c0200b041c030090000d5a104040c1ca07400c000101d40004072030b124150500000c0000c2000c5400c000d19003000c9000c5da51245070600d04950003250540703070014a0361482c072a51040042c1034420012007800141c01250408030780c64109101400000700c1260b040c0d0310300120303030002c41e042d008100080104403400145010b0040170b08070b000d0200f00c042d1132a6010410a02040c000207021075120402049151a581d00c00321000da000360041c80301058401204050384880c40c02040040d003440202ca1109d0b000c0e0080750320110040e9610725440e40703004100c1c070302c02c519102051032034000a17603031042240303808020300045e43c00390400c003039110400e250152a04260304512400c0c01368006240055541114001000401090303c80b03684182c5601c0c1114a00c005c81009a4040822407506044024030000b10306520010f81c119140c0c02104410980da030300c0d005500c0403c45000300000b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 397253552 1250 397252302 397252307
    0x12032805190c2a030c05060f1b0a0203070902371110090c0e09160302010c0302010e010c0917030f0d020a0c1202061e04110906220e0d0206090c01 64
    0x700301441c011503e028112905440b40f020002030103540460050036a2410700c144804000850000e08044843e43d00d4014502c08016950007a8403500071030507506500440480320a00013032203100e038004d00790751610780c4421906001303400040100007115a03620443c11030201d48000c91401d0191422690300100714500111800d00b0101703502ca078240213403129a501c4400501a15210394800c40c00007401c1e47c10880c803400b2950009040303071600c0d48200300d0700611034000841071003542e40a103803060101c140c500381a03002d0140804100100d6203002c0700510180c2e03000c6508400e41d0f0890104000042542080c0c550361300803c40c20a01c43d020230448100c0002142d40140f50f40c4c8818203048092405a07211441c1d02d07040d6040140158024008000d640d602d80c0c0c5061044e510519032a0500d41820b803248001541d8401d4100d0254030014082462503503508082201c540c403c08a4039603440241c8081c4003c3c01071640c1802c20782c8603440c1c40c03404550000c9806445810a88000d03c00f200880004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 397254802 1250 397253552 397253567
    0x110d0816030e070b0d0f0e060601021c090509040c0b03160f090503030d0509160b0d05160c03120204170f07060923041d0c03060601081003111203280519 67
    0x440190a1b50344109001c1c14101d4011a81c500984001910040c13502c400064180200280c40310030010b1941b02cac0c20f0030305070802c104200362802520010f450b60303030b589005410402c50f83c0140706e52000110070041c11104000995882c1c80d619a11100345100b580b000f81c1d12102d050007407940c160030500060b01031004070303030000381d001d40c161040b40e03001086103001e80c0312500c2a401144100d4000a52240118503a016071500015401030320b50f00c444d0044002444408059402410061070000101883c00160192805080b0f101c221040100000308403ea0303c04801040c908680692000069000d0040300302900b01e030100c61108140c2d00c14154039500d68181d905034030f42c3c400d82c1d42041d0030010b550040a02e09038492a0028000c07404807600b0540b0b01100140100d04002c041c10400103220000c104081c12203a2010003100400c1983c40000e0340035803c4240c280c02440085100303100700702080c20f8030401581d000b240417011070484500b00d411744564040d1004003002140640b04240c4034091 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 397256052 1250 397254802 397254817
    0x60c0c040e0a021002030d2004050f0d0606060c030305010f0501140a050c0d091d150f150f0301031a040804060c031704060506120c030a030c03110d0816030e070b 71
    0x982d09868025800902010f05190f0340d440143e202240040c50550780784240c00100443c454002c0f245050f60201345094030650107858054400c00381242042d0721003140d0520015030060040c405a82c80b544000d015244512043d40001e003030000016690041178110020398030182d44006400e1014a0741c2d801c181e0002c1b41c0113041200030041041071100c140412149811a50348048000d480c00c4c603402d50303030505000c445600201d5201401515071012202101900c800c0c0c440d490301070340110000d41c0c4150481c24803007076003400144114105072441c1c02076041e00d02c541e2854007462500d5040c02c1c41424101d8008060400401c42032001c103000310f00302d080e0b0a10a1602c81e8024014000303000540f142914100c4d178080e118000d04c040c0f8034000c2c5001c00000101001001201c4000c00080d945e5100d8460140030300c0307000400c1000707040c45511407001c000c400504480428410b850f0060569408803001207504202d40d99441406200b400354100d1500c081d0005c0902a003000041c88040c0e20040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 397257302 1250 397256052 397256081
    0x601060e06040f08010204050a090b090a180b010305060702010c020a050703030804060216030c05010e011a040203070311030403020714010509090a1d0106030b01030b0c03061c0204090c08060411060c0c04 89
    0x200044183e022504a405807000718005a01d6a00c2c140521a4200c4143c10590405080c0f10f00242191201103085030b200c3e1080c070001ca880ea01440c0032004020303051802a01c0039020500200c14000700242585c0074581343d500810142d18145402c0380c071006402c00c014a80d810161081000c82e114090b01074000303024620061a00d42c6c400e20309840c860840344210040354100380d170607050141c05c2c841d4010a4180f5402030005101d103181605680e01d440e000c061103507034040080354059100f5401840754940021413180d484c101b82c18007070340d2050503220300d0400e00a400e95003a125403040003a500c8810011f00003152580b100b8820030040e000c1420580755689107a000d071158600e0900941c0011806154044c0e401d5040d810700b5101400001c00d61400360b4070030001e0004580301d02c01c40f200c0c2d1240292031400606043e10008024103061034000d00b200480b40800308800300301184181c0140d201b03000c00341c5c0b080324030001d104450042c560100080d4210b00c0ea01010f90419404c0702d447c0c401d641 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 397258552 1250 397257302 397257307
    0x40308040b0a0b1c0309090e1f0204050307030f0c0f0e0705070f02060301120302191707151a010e040b091b2107110703020d03030c05070209040b0603010c0e030601060e06 75
    0x110208510305400c098180d00303a00c4c1c13003600d50103064002d42d404001d00034803103050202d0080641065525280728440e04103042e825009103413100140d40c1a1000380c08001c003030b1400160f59080011544071585802c0d1000b8280e0840051585d00c404c90440c00c84071039501c801c045030380300c000c2a00c0740e420104050700e182050784041001651080000d502070300e42590b08140031031190400a01c6c200001c00540c900c6e84441c910f0300c1c04151405a8488a1307206c2c1e0141c0c2c0ea9502c00c45c6442110102c0361070031002d40905081039683d10004140c1080c445000070799403c1c210102490411068841c840111a04003a5180104410b0031800d00310070000d000401c161481c100342c1c10703030480824241100850840c03c50358280000d5652124048590610000c0240890340c2581c0000302c407030341480c00007006d2595904039260994021000e941626400030070001e1545481e0030b20380a4039074212002d41c400c0d440c0c5844030010a000d285241c541080c003034005c2007a0783c00c041c5c0598503000305030302c401c1e4040000e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 397259802 1250 397258552 397258571
    0x7091a070c17101e0612080f0a0207090f0f0b0103090308010e061c060504051608060a0c0c05030c0606400b09041a0703020c0c211b090906040308040b0a 67
    0x160f004d80c1091100620081c00d100900740304c42030407658a60030541d0507003540d011081c04582c0d6030f400c1d15503120705d07004070a41c1d95a54203416450642540c6c07148181c1030402400c090041031b00d03030046400c240c18660a1004003900001101126040500100402c9c0030384018000c00c0005540250b0080c005003203e40700109031080b45948102c02103044a5294a036003c020070864240000d10b500c055101c50351816174103241d4030a4130740e500140361301405c3e40e407500d078010b100380300e10551840340d038002d4162a590022102e1294072200c08948003805100c1ca900c2000d411594900c5c4101d1119460103030020f020a5080441c60005003411a140b03a02d480d55241c2c10595101c1760464011403007199201109010385d4501400101d0043c407a070107052040c010030b00702c00d40125644032102e00494031040340603603001007403000f40942614005144160034048042c0b60303c0d5030106218403012940c0c3e900329525292070340e80e521400c440c0100080c00303140110700043c070311000060701303c1e0110794049114145d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 397261052 1250 397259802 397259833
    0x40506070b011707080a12090b042c13080c151305010f050408040e06010908010510140303040b0f03041401090b0103120e0307050d1a07091a070c17 65
    0x8038000c25124010000c004019034044010003070b0442001101800d0391502d000d00c49070315070446c020054100e65900c0e0042461510a206080c0030b413001e192915180e58498400c102400c032010b58031100340c1580862504400c11450040744181081658241040825981d5000981140404620324807848080301580d041070b402e040d20551010384c045001400790304206013515621141c10120500d030005010200f6681c4003120f081d16094100d1138841d481d0f410040307035051241d622110f055480c1100707001e8000704118a84007140c4002d20400300f1340194400301a241d120b14801c0f5810701d40100074410030741c8521005154054080e00d408088000100130007420b603118414100d8580c421000144100410a0406280702c8001e10b0b0082c0c0040001003c00d58a00060103507074031401d810302c0f40c1d804111064031000d07003e517a01c940042103401c02e844040c040f86842d00407001c0b0a10525481041801c2d0f142c2651035283c1c2021300148281d20704480e0020502505031194000c0c0910300d0224130244 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 397262302 1250 397261052 397261057
    0x3060905010602030a02150112140f120a020c0102063601090503070303140412080a09080c1605060f0f07140f0c0901050609030615010201020903060906040606090b100311040506 78
    0xb0464010b1a61800b4070300c4c0c02400c0150702040b56000007101030050201480c011883c007100d41d80035803180703526060010340310710b4080d03604402c544500c60018411826087d040291003005119001c90703400e400b80500680e11084115070f03868248048155203045503c8030b07a84900111540d0400c1030f1260300d010700203801d560b2700340c0d015680c0d6031000034050105503152044038000700a018403803d841c01e16a030703000000c0710100d1030141000006030224008610540c8103615003035020070038a84d55000a85100d07201c0c03d500c00030041241256000240e5800d0900840c0c400c00c0c018000145031032180101c08440380c1200c4416540503c50380c100829081e030401400000d03c0b1010003c1c46146848010040c4200050304414051402844880b58030b40340002e00703a8102410201210812881c480100d0080c040c54000f140e042c41440c017880b03001000414007600a9020340414040700342c64007115020384c0c41c81800309030408131600040c40340c94480d03070010301400307403400d207017403800b41e813400096800d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 397263552 1250 397262302 397262309
    0xc030b030d0207140a060e0f010e19053a050c10030f0f021804110904110c01110702010905091008010c180e0903030c030411030307140c0f030c100306090501 69
    0x1030b44030340400d1004c048500100051480102c550300002818120018240c800d481c041d10b009410000c00c03c07025a00481d18001041c801420011409034103c0c981701c2c84825510a8070700910800407501603001050140d00700380310b48005022005180700b042464406506403041d036050151180d094001e607100c001010841e1140c2ea404a0724850b031001000c00c8504020101400a10401ca40c402c00c840030403001182003401c450004604690340480d904620613042503d6000340341c1301801e03549880b8940545003a500b10402040340c002da03090009464840c508001c2e0115940704002c00c418a0f00119040c2d0003203c00341c1c1c00c85102e0f52647c9441c2912030490000010401c610700e10940035040358035040040c0407549402c3c080d0b0030f003240e000c2c0d207a100207005800c0126000000a052002c107030360110103410080d080321f81c0c0f8100ca040000503441e0309a288021405014603c0b40c040c6061403042104982c003d0151003070410120401054480380c2040340285500c0d41c100103180c003400d11640d4000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 397264802 1250 397263552 397263557
    0x130306020a0302030a05151e040b13061505030609010306050405010902030706271a090d05030705060a06091407110a0203150106020114070903021009080d090302041a130c030b030d 79
    0x481c01c0c16111202503038802060480c0b8880d401034089415030b11002900003e071002c0e1a2078003c01e4048d00402d0141c480c0d42d00ca50b070441c8111000003000c40d40d42e400f040c2210034801000905d000000c2084500b48004ea40e52640100c06200601c01700d0b11651000703402600c1040009410760040c1d000c0781c00c00e82540c1c85034010800320006a208211050349072924002c1200c002c1c00150b040c032100ca0f00481c04074084001802020038109825120f140001a1072504002143d4440c2660720b0040c1d1b868a003252605d20181c1840e0780094041000d016480ca03007800d10366094413558a9000c1103600051001640545100e607820440160710244042041000c0548205c1010340c180706019080d18805010861244802002c01c08055400120441600c0e81202e49510b00f0600100845000300303e034211a030940036100400a08540061602c01101c2c420b45e400e01450544141c07a0084010014081d034000c00311070013008001c15140c0c800c0112051031b050009200346000082480c0044c1125039002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 397266052 1250 397264802 397264807
    0x406260d08330d06150603090c0e0907030506150301061205031c110a120b010e010206040b0406150b0901200c042003010e0f0609040819030617010f0e011808130306020a0302 76
    0x300f001070b000c02c10b001d8074103407d0904c0590301c0d550710807070880308a1048030507188181c0c01041070510140300d44001550030108803138040c1441e03d804041c0d81400c0301c1040c802c2d80703071410001d0f892890b54060b0140b190004051420003140d140e030800002d81140b1b141c900c0b10394074101c0c20071900a541c080e1035078402981d202d801c075084502d0b1840c03c032003800b20824140002651040321a030303400101d450b40b056000c0848074031078403240f13480d10150800a8801c411031055020220344800120050000301109aa401c1220102d40143c03018580545940080c1c40e003100d0103249941c1450707007041d05068110804080c1a2510551299070b40d0000e0b00a655100384100c14418465842042c440e0086070880d544100750926646010091142c803031020b41c50343c80044042541c50103036100720b00030050282c1070b1302c100400204803402006210420b00317170300d0325150705405644414400c980e19062070030a80b0024103065140e4035400d030070480c00c80c400800082c0002c000914070b0b0000d0888694a80c80168 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 397267302 1250 397266052 397266071
    0x10f09020901050f101d040f0504290105060c122d0a0219020f0d03020609160e011406130b030406050702030705060708060406260d08330d06 62
    0x180010043e405540709401d1240300c0306595542c1030b007009843c845404e150714984103001e8000b021188404402d03a1151522402607403104440d08030500c514412100301c081c0e0a401d03607068401044c3c00c1e07010740581e0780c00001031206043c6000101b81010140e801c4505070841c40c50152103e500004400c1908081c4c000740c100d02c0c0121040207102030500352078103820300d20080d000031340d10000c242d00701c0c03d41892104100c0035074851303400c0c400a200c000f0340020116100c5090295441c0410b40d49800c80f40b28003500ba204192290001701c003940c551015001003a442c22681401400311482c010358850810010740524441381703180e0700024030945400540382d01d000c0c10100b048030300080206055401c10040600094400710318294404a207042001c5c0c50b8640c0c00c007160043c000da03040220420b03880c0001450307140000181c0c0780e0282d0494200c03400350446400031105c11070180daa08001d100300d000541400d0740c0b2148903003902900b09000080b41c50780f400c00079103000d484810584249039200d6051 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 397268552 1250 397267302 397267309
    0x161e0501061d1e1b0c0610031b0e0103020d0201020f030307030609140621010b03030d1407090602030f0a140414090a020f1209191a010e2401020f010f0902 68
    0x202e078007800007814a444843e5000e0007060445008120720006841c00700d103100d150120304181d40d13403203e0080840301645420842031140300745502040d0360b10180744441103003241007680c1050170703101c8413a04084981d1a542c288504641c1100040341940a1700d5904c0e00744050030005144582c0c469640840c0c000d00d4400030201b2180641c99007041c03810302c0010014a500d40682d115001110140700a02907040a00e0380f50040c0500310080d40e050000041002024030320f03030081418880d05900000701070300e415500f41c5011082d44600c0740944c0040c0950302100c0003c0b00580440c0e241410103601400303840360580e015074080d07080160943c0c0d80141e40305050401000083d4491920306085242400c00c408420b11801204041d01e5221004400580a10014000c1d00d0050403201a01c2517480c516107000c1d0107400060040c190112208400002c400e10410f0f03000e40100c00e1080c2150000103c2250841c0c640038504120b41540705084c81e006481c0710900c03488404a8421800040020301751040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 397269802 1250 397268552 397268609
    0x2040509012a0f0c111e04061d0a0501050a030201080a0212040c09051503030412030207090c03090b07020d1202160f12030e010204030804050603130614100b161e050106 74
    0x3c1010012100f10354000541c40201a00000c0d400316108820310130038030000035030000c80c40c01981e005400d050300040c0b00d401b010800c030030070410407200450641e41e46000c0742c121202440f80f02e43c04503221000304059400740d60482e4008101d0325016140650256404404c080d09036411505060864410800080380c4c2c892941c0054020840e125280304490001e5941c0c080e901038002c3c00322800c41d2080425008005000040180c0e00e818000d06141c10300c0034006110812064880800700030000c0c00203440450003405482c400e441d683c0358000481030110083d00110001d04200b01c039840c0c400082820b603043c075240144550381d00d4440e56a0000020295550b0100d00905a030040c80203000181020382038038107561050300e15548950710618400d528811242024041c20300c1c090509207403900a660b40d5101e01020824040a1507a40391204039078451101101c54130b154401c0e920b0005801510301c4212a008039100d540080703510b8a800c5c0c2152041d03405010346002494018000d0605180c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 397271052 1250 397269802 397269827
    0xc0c0123060306040309150504170c030c18040f0809060304050d020f190206031f080c040b0604352410050a0e090703080f030708060a0f0302040509012a 67
    0x50f0066082654010706800d111f40981d42c0c1d200700002421006920507806d80e001071011103a00c03030601d0310401c1403d44a11451548a020740a4503030b1a41107810143d01030f080c1001c180140c0402541d803500e4484580c00740c1407088030000002c01202c152543c0b0039002d1402140518080c2441b6080301c2406442d2034002e010210a5801000c041d0441c0602088502012a01035401c65640e90301c00c0030080c103030300b054079a040c03c00a02c54401310700e1b08000280d905817100141d50070051602104101b1081340030f1485806103209483c040b45207050260750301488180d2030b0041d4103180b410b81d0902142490807018410005a050250100040710452066504a400445003540042c1030402240c02044580281c0c1c0c082d800020100740c14280404c000c0c0003d43c0c019449030b8a60501380102c8459a100703541031000103136840b01261a07072416201d654101e40c1c0142002c1540e030b20350b50900c800303000002e017131795080d5580300d5402c00320325410b580c100c088480c1c405120304035414145014045450400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 397272302 1250 397271052 397271059
    0x2060f07081e0106081e01120611040e09030712020111071b0902030a140a0603030203161a0c07050c01030605030715020a020a0305010204060207060f0801031e020a060305060f010c0209010e0c0c012306 88
    0x401082009401c1f1200820780d274200b81d010481f590340180c420b00c644030741d52084100181c0c08040121071040072001c1c2100520410b45c040b6070b00d0604904900341e50b21145410340110042000c10f00040200d0342c44c80301a45000c1076240221380e40c10f50f800481c1c0013110f40800345500c5502100b61300007a5409a6840080780004002d6141142c4000395240141200d07001d8569006a0190500a42110140342c1800c0036091000d81d2405c490b0300000c6030422803040340c280c800e2214044040d0b009010341c0054a0000e001445a10b103042400d40c19000240400c0081d401606c84040241c0c8412001001440c000e200260f40e80703142c844020314180b500e90010303040041c50140b128000354000603c43c1101e410607143c40000505040c038114840314200025444202690b0000340c094150700100d10030201225422140e080240c0190388002074118020350228043c0014402d41c44018041604030000d020540c0c20424042d155600f1900102d034140120b56581c0c20b034001c9102070341101584108142e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 397273552 1250 397272302 397272361
    0x121e0313080109151d101b110607140c0102160b0105010801210602091905040c0c0c030b1012030c1e021305061203040909050d02060f07081e010608 65
    0x1501c51804d007110002524600b591901826003c88100b5001c500750712201c03a040d500640d40154070080213080741c10b000c903070081d5201c0d411000311703001d48440c035919030904020301000d80e00d500701191410b4011144201d080014050940142c0c3d09201610030f0a02c40b25041c08445514203045040703c805900c0b40e070421100b18014170010204c140c600c00400703440291a14580f001d0b25000c40640124a0301d9030300583c803201c10144515001d1201411031394150340401c41e0488102c802c0704e203044c80c641301802d407034010300e000c0001030b80103460582d000208100d00c01c0300e0b580f00d03240f200c0c507681c440c2401d4001462103008103060203c02c918146074258458240d207031000c0c0136404101911581042c00f07580a42d1035000074899100c210020842d401840d0540e651580c4440d6884001c081c000c2d0107076041c1c45010f00c9115040d000260007030003802e201110001c80e80c1d41020490300b01d10014141d40a105c0380108034003002c070542c00082e001e032507035854080d90344c5840f4407401d0680b01210446285d400300c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 397274802 1250 397273552 397273571
    0x20f340f052b030207030e09040f1203050105030a1b0e10060212210406090c09020a1704020a15020c06070803090606010207060801061b1401140c030103020f121e03130801 75
    0x3200d15610b060308900740561504003504081d281c400d030f0102a650071401e010100020085064070f014036880c231500120100b000c2a00c021021503009000d50340d01540020101404507032002e07010940078a44044144034261111014450b80c075056547c41001c40d0705100c240728140d010b00008100c0d003920b45040d0704203410080c1c0c217421201c01c9079901103103210748404107061040a400018819820100a0441070782d0352a43c0c0000f5403101d111240040d040003800c4034155022820300f40074680003414110042d0401818062842c3c03081c2107034007548103402d16104070b512000044c1c5120340c000c002d003503220328103030525604007200201158115000000b003803180340c3d045499030381590141e150240041001a00c0403440d80f20a440140c600e03d18610700a00900701508181c0450810380c81d80b1074139413100082c101550200b800020750040c4003038002c0010303003000764501c05501d0001c1c048404a50b43d11156000100d8040c10441203034000181e2051214181c0030baa0b070003001e040b0300030007100340ca = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 397276052 1250 397274802 397274863
    0x906330806103003090f06140d020c03041e030c35030d0608030d0c0512010608071202030a060602120f040e070207050a06020307020f04020f340f05 65
    0x2800c1c018050030340c83c2024080f4480c003115038000c10b07403100462080c0900e101402c0251a10340701d84100c42404806150102e01e044c800c440c080400d002d0382c0d00c1e05040500d6000b402c0069045000c800309680300500002482400301d004c1c0a81c5031103103c01c7d15103c0d0307081d400d008000e0354258201c528800d1507001103980f01e01c1c446156400320b040072101c05a55100e80205581984281c0d42454451400c108002c40d0440020009002e41411804104140d80b41d40380c1c19104c41c06802521480e101d41100100300c0580a0001c0d20340c8200c0600c0c1105400c010b03404c080b81246c00075505881d5140d070f00c43c0305104c440e404110055480112991250810382413031604c0d18a445540150409014120701041b145802001003001404004003020707132103515220025540d410117003080c0c2c802c05071000c10481c2ea06051086501000400c8545840d00603000c50040080070303008080b540c082d08084490003a48000968942e000303210f50340303005440c42c071030512914010340c42d43c07a000b0115007071000341c150b0b40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 397277302 1250 397276052 397276081
    0x40207030e1e24090409020f0a0e0f01090c050a1103120a0c02060a0e07170319120b100c020103020306010905030706120e0d0f1803060501090c170402030304090906330806 75
    0x4d10031100030400c1030031031002c0784050300550750241c2c00048085000c20380c14030340e040d040d101d035000580d007440c00d0703a844190405641d02410f04c0004039000701b0654000d14031500c03c00101c00e03802011280380035103203003005900b180c0888a20588070750728004d27118416414000f09411983c1d0500510074403907140b140075198221481041c4884209403090750100d1028816140300000108032040c00d4410817001411454001c1c0001c0c464503d00300c00861185080059690041400c0c0e07201c061480c03281c0c0c0150000e600140400d8140050b092002465035000c10100000d000d05988010107100c0000300309003607421200454103a81c02505846215541c811040382c4048054540010004032590503a02541c0c82508060081d45c1494008640080150020b000b1900207070381d070000b003a88400701964a200b0070f1320001d42c907400400c01089000c0b44d542007011010300070704002481d4104411056208000c914103c48030315403000e502c02e151f092400303803240108502006809140351170b424200c601e1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 397278552 1250 397277302 397277317
    0x8100e010f1502012a020a05100c1112040608070302070c0603150b03130821010807030b01120b06090a0f15030204061e030b0c07050a030810090608060402040207030e1e24 75
    0x320910805c070440c3c10710030003e90b00104e4006007035030030900c50017140c8000342589032840c00104100b41802c000c64100016590200300345543d02c2402c003420300f0300803100342da0040c210504240e000d04c80302c80450b900446642c0104506d4070b0000d2103011072000403402945a6000c1c4101c0300b030034810000700c0c9100d0170744101019408003e1954460755101d01440d02c02e201005500c00300c1000c0000b040c1e5140001b4000c8c142d07800390b401544079a0740d40e80030185000b030300000101841001c50124815040410301d40313810a14400011804035029001601190503c42d4400842d03d03c5200c05c0041d07050511405002e400700e00c1d980002c1c4280d0458800c550000b80c4030042c0042c5c03003040050b81a05101007560300c0b0705c0d80801035501040d4181401030603442d013598261000c881e034031030000303820510340f00300402c0300e03c450301410f029074035a001c000003074029a000750306010510752295000d40d01d045002c10051440c50100b20304c080c0d81420b000c840f901581804c402c0c0781094182c071030000c0c0c2c85001d88620 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 397279802 1250 397278552 397278611
    0x3070b060414010305030315040218220c05030a0612021c020112020d0c030e06060a060507020d1e050712081c06090c03090b130b04020108100e010f150201 68
    0x594403100d0215000300004803802c514001200e00202c10454040b0046000e8020361213001210300501c01004200c4c8100740c11591100450485501913091007081500b10500400c8441340c40f402c1440c07a2800d540100fa021000654000100510b2038407620840d00944409030144500c44450790114001e44980c4001c6260301c1d0071110400110380c420300004042950780f0b0381c25500c0d943c00c503100c90040c0207488041d901180c03c068400f61440c200250032480341c1c400800301c000c001d14055050710705503c0306405a8200302d8101328000031400e25104a00007407018811440d0000c0035091840c28012140c01810b056500142c3c40c001050310f8074103840280303070192420102214400362000040859610421640b400d1004035a6450b406500c0310003001d00a0f40c60350710f55603c0107a071080d80d030b100003002007404120318007260240d4491420194001c01494824441584603c07540c0301c80310090b40030030481c5007491001c0c010701032444014180035580b03000074401844c6400703c0c0b811b220500c0814400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 397281052 1250 397279802 397279823
    0x20c010b01110a080f03250503040b061f0c0f1b030203060a113901050105010e030105010803040e070c050604052b020705060c10090b091c0c03051e03160905060c0307 73
    0x1f01c800c0e004900c01100ca8241883c40b01d080b003000c040d110f600211000da49a001d00b000144040c01c1850101d107425001c4a40b80c0c40305c4000c1c400a82e69011482400d403030100c031a00e111000980b2118110740740104648880981a1031441094a8585c0040c0045640c5003005024400066a0000d032213000f03026601c03580c0311980d504d10f0080729038103c11008030b0301e650f00c007002c802001c4190302260580b10b00380c2e510215850f44009050a80d2000c0c868010f1641c01004100022009038003c15000192850001110184c2d600d515240640a40d4151815004410490000411592148088100424658100d903006100607445400c948240e6005200008e000e02c070b0b04100b446040c040c1c00402c3d508204031303c41410044400c0c031003160100300c607114000c4a2110310602c15000c082426043d50751510078031896604490540100c0707500c01c2e182e100401c10707400d02c0290b20059841441000090303001d0010800c40181078041c282e0195000310020810940b0648000c0100e44909070004502c44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 397282302 1250 397281052 397281061
    0x1a04020105120a0e0f010b01050412020109050d2004050601020606010e03011b120c030902030a0f020609060705010209090601080115230a0906021501050a050f0a0504020c010b01110a080f03 83
    0xa91900c900b14000d01516141400c10107484010390245044c416100100c2d82d2405050030980d080b81d035200200c03030105006220810180703031800210407005206150060840c0d50f40c4000c243c000d206440110303842b000414000183c030341140402a00b15038200c074280031074240000040d46501010749401d04000c42c4400006042d142504480d110110000b10302c00d000b810448000c1020100c500a072079181d00304002e08012503c00e000e0842195002405800e12103d6542c03492004041141c0880e00b100703040c400200030782d84540192100600400016a803041410100b0501d50001824581031292910040c8103044404a000311512428240101c60b42c1d4400300345001c0c00800c92003031954000005807034030354a600000b504120343d000e400712800219002c155240b03200d001d01a458014150000800a518100751840c100c502d0240003120300d5034580002c2020707640841ca01540c561b4440046007082d503400345500800c0300d048000303440451080d5943c036041c0d11603030240340034000010001c01d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 397283552 1250 397282302 397282307
    0x20d08130206070f02121605030601081f090b071d040507021e03070203011d07170c01030b060d06032f090705070c15090306050112050a12050d0515030106121a040201 73
    0x118415001481c03164461b2080982c195145242d4400a0f0b0a060b940c00008030f90030001200c40c140c92049010b4880341c034148050007807441f81250f60101e02c40e1210002c0c004a414442c055004813a19511030300001404180b6403000078002440302d01852405003044212640864609240250044000d100000c0c07400703142e2950080800203903240d440e210f070807a1144a81010880800321f00000c1da090036650312100507804072003405906494202003454442584682d0001c0c18201f002010a410302440d01d2a000c11111140c00803120140b0a0310021004400e04806064000e92021281702244580c0c0c003107013030000050022420700802203600741c1009144944040507102c80005509050b004400041441085110a540b41403903c070000c40c506003006518104a42c01400030600341301c169456a847d04140301151b400c1240034004500c1000c000d0091a000d42c501030944514400c034079080500311286c40c0d112264140e03d01d00b00500080e4103205000c010080c840e8511090355850005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 397284802 1250 397283552 397283573
    0xf080d09080408151602151e091f060b0d05040c1a0a090f0b0a08092802120c01090b090310110c060c03060312030a021603020706020d0813020607 64
    0x1e010100218000c2841200000d4000c0c41e00d00044c0110016203c080d001d10320328104d101c3c11001a001501640c0c040b41a2140311908140400f80804030740140b0700c03d02801d40010f6440344040e07000400c8140c0c0038001c0c001e20a001003900241040395034908040b070a0180f00303c001a10340c1c29103400000e4107001800751200020110150b4270803140712a106100b1040c0e02031480714000c200608404100342c01d8181428055030309800b14070349428140001507880d010300404001c590b02c155111105480048080c4040288142c03030f409101c403c03903204010086008000c4a200c56108004510081e80d0000103101125070040d505c50742c80b180100400d04103403088200403602410840a90042c120a10080c007428401000f40c89903500c40e00000c240301c0c8404d88a0940c10342c03014490310308501000005603041030900308014a8880d020807411031842c035031360080d030140e0064881002040d030107003e1800790075103611b840c48a070f00d460172403d0720520140f000a4002c6d00f01140e00d40c1040340c940d0b403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 397286052 1250 397284802 397284821
    0x4170309090f0106110c1c021201060f0608090f030a0c050f031309200a120e190b0108191205120f1012020306041202030f03010308030a05090a0f080d 66
    0x52060b10703202d041c5420150080c820f1900051040003404111003002c190110315584c020828440c59070000a8080007541c46003090340d101ca03183d1480d4103074840c2403140e08001c0c822504998902d034034203040507000d104010b1002c015908111642c0c800080040b0843e0202031150808804800d660b0900c1450b042207141207200a200000d00b104c1e0f40719203e60503900300c446500b0300f0b110b440c0b48116111001d41d50342104610044042c00a40c080600641c1d88502000c1868030001c0c105089400c85482d000303a04400c20991004d40740b0a50501c251404840c0c0035010701c0b0f000b44800c0742c030345801c503a50488800003c0c104046100114070a64801c40442e5610841c10211150504155082c0714107040c003034401a500210321100051401041c0505140582d0020007a080c20384e1035845180205000700c01490450008010092010707000d0300c00f96018600401d4155220310306201903c04031107001c2d041034070b540d00128500c00011031a086440c1c4165010030b220f600c0e82081c007002809401d9049 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 397287302 1250 397286052 397286059
    0xf030203040f0905181504080c10241e1527060e0102010903050f130e070f090e090d0e010e0607050a06050a09390801091203050c04170309 61
    0x80001684420f241c1110380100d007151042d00642000f001c0b1280e8441e80d0000008044518000007804207000d07602802980d40642d0640e115801c18101c030308111342d5140e1030348500f814140c0980c0c849141e00c2c2e4440307014204640364003c9680c101d0300d0f8089000f446115400070401030205621403288264000d0b80742d0601e044a080c1040000070040800c08218010b00c8000385003258a01903035841402400c2c00c280d0541c40f420715290038100c1c0003241c0d41c00965911007410798010002142c030710702001d440c841d00c2c8a80d103441c950009001e004002e0005507103c021400034540c18080141000b050310703e80d600d160704108580d254000010303602c4050601105500c85804142c0c00300b4443d001c940b84400910400301081103681c3c10b00b03500c048589240e0007600036450740354100c1c60344841d0084e440f480340a0005c0d002c0304000c0000100020601500b01d00c4980c4d4448200d02c042020300e4212000140290600784203d161043c00c94490f8040c0c0d00c0360540d1b00301d00b03042240c450441030045600001014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 397288552 1250 397287302 397287329
    0xc030b0405090c03061005061c02040b0406120506030616030b0d150218040c0e011803021903020f010e09160c0602040806070207081b061c0603030819020c0a0f03020304 74
    0x4480481e1070b8030f84120010f000740101000034400200e038000704002c0e14030040c481070402c030310550890280000000c11600c0380d80d0030000403402901f1309000d44007c0c40c2e29600d1002d02e5000070100d2094507400743c942c0d4000c0e0b11000900082c02607007151074100c40558a00002c0c105a441c000035103069035100060000a42190025507414a03500280a81040b600e00000d07085050f43c280b004860030fa0108000003055882c4500407580320364000880e041e6210040000f03142c40340c0010f00c500004038220070510814010400460a09000303100700003000742041d005145400002c610082c00041c20710f000341344022503044200380a6a90131081e2500514115111030319058001d41d10881038601c0d4000d885400c42c0054500c000081c20344c0d20010f60f0414402200000041c04050b8214000000584203200710b02070404038184202001075000341c2d20a5a81e04005842007421010403000b8019039004110468081500080d0511070700e070721a071040a070580d80d090032815405a50013442c5440c1d440c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 397289802 1250 397288552 397288561
    0x4090204150b0a020d0903120804050f03160201141206040c1b0609061121070509060c1c030b150705120d0b090105010809190c080d0c110913060c030b0405 68
    0x205400fa042c0d4000580071580354055040058a04416501c00140b00840e580d06d900f01481c82018400d400c58840c1d422181500030030300b90325086801141c280b089640308100114150b40c0c1c0070104410286590100030b280c121000940002854000c105038011625400e819512600c5201e120010090343d030010040c90079a032800c04060000d0a0040d01c013a800c103040990b240d051001240e8036900355a1000851110100c103120001c0002049201800800c1c4101000d0340c682100504140c4040c1c0c0140c1b0381030050f100c0d034450b40c16202115000701850b1080e200d16644a001510a440c496080140d40300c01c0c151519616000c61010030707a180e07030400700c1d02070014580c0d0b0f0018030070742d00219800e0801e88e0f01e8100445000d8803c94802d441d82e802103482004122980a0720004140100381e400111505c2d0384485207424401440700f4002032031840b8980a00150304402c0411950071111050b5038201900d482d9440000c840d00a886140d071a000900d0320350282d481181c50000c0a0820f20a40c0350 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 397291052 1250 397289802 397289819
    0x100f082403191b0b03190617030a320d0603080412050f0c0f190306020c03040501020c0a0b0306090a0e0601181503030818070e130309060302070b04020409020415 71
    0x2c41c40c108661080c445007a60341c2c80440e803a180c000340c84070004190704546e40c18000c0c248862600d42c0a50f08296983e801040d840c0f000c2d41d9035a1051000c2005594a404808006104201141039141d040050510320401e00801c10300e400e03505c06c403210000d610b6030703041d400b10f41c0103204e1540700400345207001034000f03600421600c0b4a1000e901a00c1030350040340042c0503454580380c076594115884100c9442880030752400c105601e4500c08204200c98250344c03240e81d55030032a40724200090030f907400447c00f00015a03041001c072090000950383c60392254581500741c2d62a000191901d032180450300c000600206983e4408190030690208403201560b41c0c16140522944038041074602e80d00301a440480010780c0c540e0a03088039890350316101e2135036a4030081018903140c0081803c15018201002400ba651016807a01410f0791201418003409640f80140189003d40c0c8207405040c0180f0400c404182c807480c425520a03016180880c0159240c40010000c00042105a0942080d400042003101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 397292302 1250 397291052 397291093
    0x3020909071701060e0a030609060917031803120403082203030204051005070b0f070c140c100c0506011406040504090b0106090f03051c0c0c0e06100f082403 69
    0x811000c10820b031640c9640007155941585040540c101c0d1405604200050140d0300507410140500e00c00143c0099558404080b411010007103801c21030040b080c0a8120402d01d0100203c110340c10003035180200b038485c00700c01c41a0007000502842400d50018001c5c4900719210000e404d440700901c04800340300d11b0081c1c001d42041c000c8070300406014100001d071134050422a031849030414074003550707552444a03841d01100020580c000304100d0121003000286140c2c1400d48001c03448014242042241c0e0900c041c1c003c90f0f505240402c42804198008a80b002c50384a054440660300400025104800300f105032181c0c0e030100b42c00138548202c80c020300c4180c1c10a28141c5a036507840d20f04d807a03500d065a0240c00160702000d00b041d00f00810403400491950240e041600035402c00500c40b107091b4407000990712460b8000c058030102142004010311f03006240304418000360030030f0343c041c000c5038000500e20713000200421400796001448000d90380380340001903003801d80281210309501c1c0c52000c2807500e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 397293552 1250 397292302 397292327
    0xc020a0801020310050904081c2c06060d080307110309090f07030506011112030613090f060b010512010e040215040807030c05041a060f04120308070810031707030302090907 76
    0x2424040700403985c5c0c44d20382c09180c080c5401070f4100d800c0510200d08020b030381c205100c400c0655640c0301000b00f811401000c002c07803806034907100c00c16604007a4042a081c413070020308551086602c031080400050303840342900e41004030f519000d81d01d103450085031072441c4185942c041c0c0c8242c02004100c06901c0340c0345064801c02c1241c0e828089502c3d04401076540505081c9007a110b0f410481d4120000d007220409190301507002094030b212000c80d50300c4402110301d034150681d10b00402a600d0350070312015028072114001c0030f2800d85d141c00032920480401d00c0c818083c030b400710710495000c54295580e12410400d02c08940c1e00341580c881c1e80340300e4565169010f110032102b00301100b40c0060240b400303106181d162014506103114a40d40340040010541c0711500000c0800018007000c11114280412007001d80e200c2d40791103030642420b59000e000b500c0020034850640321240c000348002100351000c0910344944200c1c1036210075042c0740650203405030390009600050503c0410040039848681c26016 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 397294802 1250 397293552 397293571
    0xa09031b030906030b010302090a091514100e03030c01050a050105030d11120a020a0b0a0207060e010b0f040b01050c0105092506050a120612030909051302090f04030c020a08010203 79
    0x800d1039a096958880d2282000340108002d902c08002481c0260440d18008105150040c0740c100841c0014100021603000012010ba035102c6012454004101000251564405004400040100040e0510080380b10f1000f003010f42c840b00040e54404109407020b0440d1440280100c0c68803e1045005281c01d2107a00e11070721401400da220303180124001c210700a0031402400302d414000341c04100307035800608030a04511802146070041103502190501a400c85da50242ea142000c0c240322082d2440d09213400381c5645466440040e42d5600604414074640c2614040341070b201b4240161454000d010403c0c00b13a50070941001000d8002050b40e006240c1c450340c60301d10b42043e0f5142070344001260f0190340d0100784100700e1206c22500902d001c0e816001a08000328001d901c40101d00141c4c180103c1c202c0100311020b90900140c0040e0250030751040b04072140001030300042e000180c220300043c20f240c001c419654007140505100b5030040c034a40360003401038003000e6074420519000b98000c41c0c01545 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 397296052 1250 397294802 397294817
    0x9061602011d0a090b0a120602090a0b0a020c0f04111309051005090411042c0d050c0d0e0a030b01060f0e09130821010b0c1002040321170a0903 63
    0x105010788105081a00c41c0545540189410009500020039003c17514a510500c0d03c003001460050386002c18440a108403030240c1c40d00310203402e2180c0254245c0082d1020181030240d54601540050107a0740e030201190b007680100e2070040424010646071030803824aa100040000f600380941b007500088450001d82001160b8440c08222803001c0c007401001d030b12004060200d4045201e5040518010400400005551950a640c01d514913501d16202c0b003c1d6200c44840c003000e54081c42601f0f802482e5092640c94031074904d51242d101d41c2c50442841c03d0160b41d0a140d1540d440d5903440300b01440d800076900c40196101c41014010312800c800260001741e90802c15196801c207450300d9400740055030f0181080c1e032665a034074620341d00004414503c7c5001102076000200c84204828001c04615031403944e502c45840d5000d0801c50002950b245a5004000c04c000241361030715500403507120f42c1d91005d491886000b045803070350304040070200a60000014002406c51b50b07400000c209110313480c0c052 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 397297302 1250 397296052 397296077
    0x70e010b0414060703050d0f05070f091512020d020c031b0307030c020d03030b030109080c0d020c211203011d1e04080d0603080c15071107050609060906160201 70
    0x1401403049005100421800c102c80030280c0c20904090240944641400c40c14600120411340456000c02070030410227445200384045250031400c03100380c0c25603500c5e02600690a14039a04200c07942002c0950400c0500071420705040c0e07080e410313140c40d201005030541d6100038030358060395250401ba1688038a0342404180c3c0783d14240000c00c94510075030640b02c1c481c00702c0082d020408a000604030690030705891f03603403000c90341e94284143e10025114001160700c8000e0031a04510344800e00001d4010765000841c40303102d690741c201d507650410450b84900e00c8250320241e04e0506040000444110344200440003003181543c40c4490300c0203041c070040410855444034441d10340000840340c4101c0030101d00012070041001c0500402c0c0c03d60400d2004908956260b68185240d404116581c10b59005204800080f1b0100320703041d81c120107103103410790419a0038044e842d214a081e100b5140704140000e02c43e0070607207941050f20784900f001407d00340c079100d00011892003400884800c9001803044903060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 397298552 1250 397297302 397297319
    0x10b040504270b070c0503030a050411030a02010e06030a02040e070c170f0703181a0309060702010606171909061b08100302270702101103041502130314070e01 70
    0x30442c041008900c00d0701826540c69008408402130310305000c1000041400000c541c08200550194400c090001014500303418a40b1100c409010040d109420400e69000986e0b809103592407600710459055a1740c0e2922031940c0024411540030104810b910000c1181161704180e940c5041401150002003040c1c40030440c08142c4601020700409800c14402030010a114009402680c130500d8a4492003588414050b40a290034040072028060000204180c1850a010468000001d400244411800d00801400780010301c00088148071412001410980202d01001075025015400700020210b030b06049005e0401c0c5000c141108039a913000c5042035104401d102c0c030892203004c5070700c41c841c00c1d88e00b007261520315465070000c266a940c1152488283c405c02c05402802d13140c0084c82c140032894850000d0301c1c0100000040e24800b0300800c00030640040400385c0c0c09030f40c1100182d640c44015600c20540d09076810140200c038000880c0c10803101d00103000c0003914810022030b1080d0b81e03240004d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 397299802 1250 397298552 397298591
    0x60206010b0310060c1406240d1703040501060f180507180512012007150b013c11070b27031e030403020f03010b18061503010b040504 59
    0x2009140f2500e000c01c0381c0c0d840750000407590391003181407012440010030b1a51074940c0580e40350b150315511205218801204281c8016030620984882c07907224000d4803401240d2031005a08880c2c00c40020003e82080303020351004003d03205030700b04184074684032900d8440340012074881c101014030700704c003044c20203008076041c404207103003910441882800c15092203114041d9040800e650340d20f6100039159811a0551090a1200134542c0c544030165400d02c850f042000c280c2c1844228a000455090b9903072102a0b0a04001d800410291140305481003a100e010000d085c0b130340c040d1f015032801c02c000d5444550504940461002c4403015074480d00b02c00c0c15481100000401c0d140010004610301c00d00b24085007038010009c05990012a089c80d8a030922459041c4800103070704001018003c42c58010240d41407042c050f4001c004454426003c9005851a0b41a04141c02906800140f160f95400d02c0107002e038444807030094503543d441940c80865080382c05254030440c2080d0000e003500048494 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 397301052 1250 397299802 397299811
    0x10f030516050f0409060e1012030212030c0405040504150608010c0507170c0d030e0115060e040b13020c010e1504050304030b1021030e010905030a080d24060206010b03 74
    0x10085005401e16500b42e80d0380d400598000d0030a0300620000a0380f103c54030600000340344401541c0340d103180880404543c0c00803a08140d041020200c03052010039030024442d040c81d00204482543c0b070311111600b591901550f4401a403241c00c100810040158520403c24100700140c0103200003034554400d41d007a1030304050100d000950070305c000d030040f5194840340c00540e00711200c440e15109020030214100450501d5150110361070381e01c4094400303800d00c1200d01c4650584e015000f12401c198004280d403a00500b441c1c415620350000c2c001d15981c440d90503000b4120f6103001c40d901d0003100c4c2c030b0a01805404c0f50740c210501968814646400400805901c00d03584040518901415540c400c001c483d8007038004400d451100c03502207513a1482d020003050300300e00c40c152207624594500d40140300000b1804090304000c0c17482c90070042c40c1c80001e521902d241d8050049a00c6110070070b4104010b1250b00141698654503088044451101141c1071058400315402c0d100c01c5ea1303d0b20401d48413440240c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 397302158 1106 397301052 397301071
    0x2031215120d0f0215040206090a0f0f0518041212090c17010507110c100e0d0615172d0708030a090501030608032d0408010209010f0305 60
    0x10200382c3c0c2540300412042c141403138402c10f03910024200901800022584d51015940e2004000c060302010504006d8a9503443d50700d42803102d5803054034041c01100b80c3c00c0408414a0309814030550700030b03e42c0c1281d50310307002c000c4a0001590f19005a00350343c8016840c00030f5045125400103007040035a80c0c1a000d00802002c1c01c4038800b901d00c0040c840083c07006c50140c03c0109603080034130803c4451803010051142d050300c00801022449030b0000400480c1810000c40780d0096030700c007002c0d1a245081c5910782c09002c40401c8030002041040d400100381e000783c0080c00030700d01d14140c80b40740705050080140b1411490040c440d0001d026030b800c017092042c3c0f29a40084146d008010900c0e09000103450401411b44911172030205028681540450050002e81454081c4898032615092966a40c0e1403103164000e410840200e4002114682c4100c5454424080c076400385c0d000b034 = true := by decide +kernel

theorem cover : BRFrame.Cov 397122302 397302158 := by
  have h0 := BRFrame.cov_init 397122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 397122302 ≤ n) (h2 : n < 397302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
