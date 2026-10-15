-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4508
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:50:48.344251+00:00
-- url     : https://prove2.me/submissions/8357b40b-d3e3-4f28-b3b1-e8ad6ce22558

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 810611510 ≤ n < 810791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 810612760 1250 810611510 810611539
    0x5070c0305071103011e05011401050a08130201020f0124081501090b010e06180424050d0203070314030c0c0d030f03181220070305070510050c010c0518 67
    0x4000c0d14280c6500580000368007103583d001c64010903c13010507001d22007560f85c1c1401950800d0f4010b5040e0351a02002c44002148580151260f1003401402070005044200180103007041000020001b0310520684000f00d6040c0102402d40720400c4e013102d5000021501010725945040d0480c00800380503002c1d00708010882580120200144a140c0481c1d46a081c1040305a21403801d40c415140300402842d100c9185554030340a0040800240340594a0441020f0948040783d1030b68850403604102401254200000d110102c0080e1030226090711400c0c9002c40010840c0c0b041c441c03011440c20081d51602c0034240e05d5407801b20302c682214081c1d0030414202000c25400000303004000054200800e42e0300c0c02600c0c2c1b040305c181038072000c1c0546507800303074440205a00c0803112400c1060015001400a414988580c45200d44d100040c03242e440000204210b0402c12440b48002c1c04c1800d02d0382c10442400489825034051581001c00904002899501101c902140340d4441605558041d290343d1203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 810614010 1250 810612760 810612767
    0x1b0f210412051c020f0a0f111009020409080309150c030f01090507051b070f09020c070e04050a21080a1e02090303090d0c03050d0206130206090f0306040308010905070c03 75
    0x150160700c08018000950402002c0910381c07040c03078030180000071507807050804120400c98200841c510009a040d50086003290302c6441940d800c411403402a020f06101519405c008120f10074040760000e0305c400f601d6000c2805035014601c03c41289000e018654682040c103560300000600c00c1036205002e0042c0030400341002c0043d415100801800110364480403401d5400d400340c62243c04138070a0702920700c0308510f40403c050003160500b1424408080d03c0c4e60201041e400390bc031880c0c250741c0c0f0801e41040f04800c807a01194106024409030340c10031060b030b110f217000e0428511016429859003450820b030b8590251070b556212008150412988040d0118a0347d4002c00141d200f80060f0007103105543ca5405100322800c0d82001400310302d00c0403c524124010380300511050701c81c0e000303500079202118004615644140840e1004c841c3c0c0740d585600700304c89034100700e010035001044142004d02d561003c01c2268021406038035524034940c9000044001d45000909a00401c0b071049040c00000c2e40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 810615260 1250 810614010 810614033
    0x10201230f190c0e0901080c01020606041104181a01030b010206060108192f0304080f16020a09090b060f01170c190c0c0509010f0b031b0f2104 63
    0x841c0003803140d07a031603a4158101102952003003003403042c50041a0541d041d08800c0c1440b07509816504046181e0744d45805e50788480b2100e0f030039400b60300150000b402928003684040300810300c03d07464030b0034503460300805000b00030304800944c403190760386c01d0703401e0f025600746202c01d8280070922b41409071200b807a00003503c5031070180042e41400750f100040b070401c105541d203207884410138038010403589008030510007601d14404841e514924003a0f5040d18149541c2c004c0b01c0c03140349c006d101c1c249080355644206407194805140354040560181d504401607840c041c90000501c0c0c1454042400c141c03070f0410502806019103854851122400c1d0b0310040c0e41c10003824105000300c1c0036103e000d40c0da00b500c2c21006106071101c81c40c0c0c0950f15810101c039141c00014066489018003000101c41d0384800c148840700c2028011000700c038414120810036100000c005580c444da4510690940204058840c002038201c80184203d444000ca00c1e52280c10100350542c000084928441219080c41d48802c42e4050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 810616510 1250 810615260 810615271
    0x40506060702060706091b031112210f0301030308010303031407080112260301030314040f2601290103061a300f060301090c0603020d0b09010e040201020123 69
    0x102041c2030307017400120f0f844050456042039010b071418881113030076042c0700c80c030b400211010880b19a117111039080001000080d000c140780100820048070075005404001921148110f100c200074070500703403120f4405075000b1442521a110f01d54118a800750541e487e01aa881c0040ac1d040200840103511441041c112007484640c001c4128960400103410403510020840088107040c000c4001084074008504a900070f170382d02c0075103283e0080c5d2403001d4480c45c810b100880d01c42042c140012809030890082d516074020f4040400f241240a00f03080d0f41801000081c0c2c00c115004960203d00c0301c8918500100302442c0c10040e086c1001c800c5082040b8080c03407016000342c0400d007400084903140b47c10f40c040e0203403109001d15010005a0064801e41207078008a45222440860a44e0605000eaa1500c0b94080200000941000800c80083d017160116241035511128004403030344414054038040c10740d18003110054501760001a080d54903034041c0080d010103500e20704c40a11070340c60100b900310 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 810617760 1250 810616510 810616519
    0xb04140f010e01080a02070506010308030f07080403080402100302071e0201140c0604080c030903030f2a030912420408121302120102120903031315060305070e15040506060702 77
    0x41c2c40d0b01790480001c0c001d05400034410301c205070010051181c0792010314072820000c0320300c09066503101c600320384d001405c0d940200861040310200d0018513090b000c242040403035280060524155455014082c16600c0741740c40c1d40da00d40c042407820341d60b1240b129030068117040744261600320080d400541e100744c0100041e1421b00049000740350b82c5024400c0b140702d80002002c803519150a400b01d40e203968002942030140d44070515501010b4900038100b0b020315854070001d103082c01d250005100e00c01000f044001c0e0326001c0d074241c80d503400181907450a407418440e42d0101400149a44801c1c418806c841540e101171845410000002c42c0d000464011801c21010000c1d2900c82c00d44c116804004854002e5024200030301102000c4815405402c00000010341106143c8404034110703120f12040c0d840040941e521160100070a4003181000541941103e000403465502e403036003418001c0c81d4000711421060401444840f11050041c8800e16500300d90811042c10000c00050541c4079903140203001c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 810619010 1250 810617760 810617777
    0x6040219230705060a06051c0b0601090e07020a140c0a051302070218090d0e10030902180903030f16093b16030203130b1009060b04140f010e01 63
    0x810000301007070382120020140480e103074419450955202c000858940b80c0d031520b0464002031500c2c20b42a8440038800b28082c0100d1420103031511445003100404850500400c0100060024080307491144510520743c0503224100951034482c040118540c0c02d859580c4c0042c0d0170030950380e944610034080303440894280c09030f04a103003011406030042c4000654884010055003480c0d0200c2e442c40d070711450b42d8605840c080d0b80010406d1b1005500d0041c1650004801003290803418000e5000104450000748a0380d800307248070100500c800ca00300d0303400510390000301c140070f4007980f600b0886800501c03001080b2008035600e50000c09000f81d41c801e0320448801041d001c440d81c0381090506250540070a034407032864240b44a1a50f1a140c15035041984030451400f50b9202c1c0c2c0b103413007500c0c0110b00109035400000c0b400d440700300b0b13881d030080d104140d80507540000046070143d40c403884000300b410700219901d65190910032824844a4130620b40118403034281c109144c7ea0002083c0c80b21082404c02c040c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 810620260 1250 810619010 810619037
    0xc050306090c071a0a09020109051215090106120f021f14280e01020609151b091806151908071101060b1e12070e0319060b01020606040219 61
    0x340c2144c5201202c040c02040d030300b48130b0114429000607507824002e0b250542c0c002d95507001c0c0003e200403000c01c260303a0303000041c14943c19203a100307046400410303842c00494403680300c0e20007a4a00401c05400c40303408010000040442c10708055950002e142942d00300c5092081050150028030607000b544c003100c00001c1c618034a85081030f1003c07040030910050488607000c400f00038242c0744844003070601600c5154000340d41c00c00001a0300c404a0352298502d174043c0c4484030241c0c1079403100311070031880c800b06106410036500d543c04100e03800204040303d0601e46c1000003e000d600780040352980d04600d0100034514580070240c107401c9a4032503528068540b550f0b10710084a66000c5103411002e55400d000e00007400c1828030010b04110031504001c00c4000070110b070800124804c0000030305440300f0030000500300c90701410070340e03207445006402d5594070521091008090030351110704980d5141e84903115402d0b540c1c1082000c0d8070640a41c3c0440c5400741c0c803800320780d000141104200411894010182c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 810621510 1250 810620260 810620273
    0x706050c12090d110303010f05010c0807061e141e040302011d010603170307090302010f02070b13030506091b1005070b162a0f021206010303050d0c050306090c07 71
    0x80e400722001000e40c00906169901c141c55010400407040068880900c0a51120340402164122902c03441c4079885d0f40d180400646125800304070549003580e040c046100818914040c680b00d4410070a440d0040c0e505040303850781142c19580b0081c030511b55407000c005482680c01e0b42ca1005410307c144a01c0159514039003280501f0342005016480035203c01c18000b82941504901e003524811210003a101d01c42104400550004952000000303079000020405035000d00c101c00c01102461060342c0c0b00c951141890072056014402440101618007000c0040c0072043c01025000025540075103000c401032072220382c4400003032603100c0c4611807100d05d4080c198000d4048503c2680e110304c039010035103040014890354a84102d010302c08a0303003c00781d0030740f4412502c0a01802036140d400082d122102902c60141d880c1c00100126007128a40c03200021907030080000c14000d600c242c1d42d0075500c0700490b410300180c034103810001080c0f10003881800403598401140c80d601000380c0080d661524081d04109 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 810622760 1250 810621510 810621517
    0xb01060302070f140f100b0a030201051312051b0103020909010902160f050607020606010804030801060518131a06090a090e1f320609091e0102130801060303050706050c 74
    0x10600402c00f1510825008042005030f85c00d10540c05980030284240990001d80d20302002c095481501c4000610056025202810030b1018481080a00c140c07120084610403003200740584140d4040c641c007020314802c0c82c3c4407502e604020b103415400c3c0010318007c07034144607060040c2e859454001c6500c182d01c0c0c000ca080d0f80e985580146072640e074003145090094440170252a4039005006000018040754002d0003250f00076641a66580983e83ca01002105c040d0055000010400000f00c03018100355503c0315582042203240c1400116a01840c130906481654011034a004084c10301c01034540350380d1414143d00704c8045c1d010105024000848046c10010b20022160b90540ca500512050545560010b001c841c00020702c11414043c41c0d040c2286c00595010001c00c2c101c0400c001442410a80482a00a51501c089520841c6c042c0403070121007220300c0440109a50100d0fa001d40e00040c80c603600000c01114000f0002503007103450003002803007205c03405030100c0d4031100466183c02e130305001c6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 810624010 1250 810622760 810622763
    0x711010f0c0c02090f01060203030c0702181e181207060f15080111070f03110c060d0e01051602150411031f0b1816090812071e0b01060302070f 63
    0x1c000d5109600307000392041c510030000364002c0c1618400902000c0302c40c0e214a040e14016001541903036a448101c2d01c041e400704e44102d0b0824080c0c0c5010304500038070040c61303004011a894811003640081d0309119640c0c07005040100f07402c4441c850717488101d808542c181b002000c16040c59590107a41c02c01e04060714552004000700c91402844610b11403110004906407007840d80203002c1c1d2017141244203c1409a07402c040c10400b1803070013481c006130261030001d0304d07042558160b6061086030000968150090400c2417071039602d52020b046660001c0c8a190b500028541c0a40024200180002c0d96880c035900c8038441c2481c0903012600380449800c420120040080858402c0942581c030f03c520500c403000c100da0454208902d0f1489843d00c282900c00c6020300d0030710031419a891111184821038081800018001a5480070504003000d205070780c510900104042c2e80c903046440c200d103810079500d01d6000030082d003415500000d000c036078900c0d044465615002da142c1007142480790204010020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 810625260 1250 810624010 810624041
    0x2060405120f12090a0608041a040f140d1103030f160207091503020f091303030c11030705071707211712070e060922180f02030709060e071101 63
    0xf4018503503806030020418610255034012109654002c00d403410f01d01910024202e081130b080c4001400a0780320f527154042e006141d400300000494440003810f95419080e5455908050159028070b41c0040200c0b0341000158000c5284d0b01c0d181041501d41c5001801e04007425007052104040f40d442008010b000d00381054007080545542c06044003284104d201c01c900410908200542c02d00d040c204140c40748004003040d0310000182c1da03044000384a14604001400f02800803144135400c100050070b2041d11442c000c0c0714a9040c1401c0700c07001ca0494009a06c141d021700c009200d0344610306891a0b503500c424000f86944c407880d15254070040d0f48403050182e01640403542c4540100c041c030703515004480395115900e1866581042c0541441501035143e080082084180c0d40c190045069102c8407100440005805a16038035610140e080c0110507101508a09603070b100f0751a05111110041c001d03c6d03420070480b0b15004400b030032100c005141100348503001652510701c84081d0481a0101840071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 810626510 1250 810625260 810625273
    0x51207031d06010303080105010c080a30021216051e211006050a0e13110a210c080f040f060501060914060405010203030c130f0603022502060405120f 66
    0x611a0781e02e4909120540001c0c071540000903082d40240c0503000140d4011881d5480d00004c100140d40032003104800e25401840e50301907110010070b0a40e00d0005021540015940d815612041502050040c20021552080e1049041702c55000b000701c41940344210745202110320320803821059401501c800c00d0041414850310380c040d0140d50801031198460f00321440700252200001c84141c0103444820300410f0a00c1c05941040c500780d0424400307565543c0700400c030265807070032004650304003449500206041c01e15032840d41007008d0081d29807030b9400800700304807160710b10002c001c00340203001c0da41094113190200307061254080010198540040b42803000356501d0400410101300c0e07105140c0b003101164110301d100e1401c1c6003260200d400580c01513095480d0380c0d4190b18198041d500d8160b405071800d000003074900c00c0d41c1c0248010051a10016141d140c010b507645100e46001e000300f595008071820354001070b551081901c05881e000e454501c1c101e8030555805203407500c03a540c106071510556 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 810627760 1250 810626510 810626561
    0x1080402120708120c0115081b0d0503072f0901062607090513090b0109050c04030501110a03060801051b0c0c0a0305030a0225090209040b040c0e040e0d05120703 71
    0x40c008000c4441c10781d0081101e01d1407a1001e1507a09200c0c0a004115080014522914504c42d03d1007400704c9d4004000c407080950300d640f514a1070b80150002c40d0044027820300038030318540d20541d10f039500400d600c0c4014040c0384a00003c041801c140142c000b4042e004031011605054943d0f01c12808002c0c940c0c140c00d43c201550040e21551f55071240c180b04140c0561b0b03408503844a07001c1c100450f648007074030042030707400c1520000c0a860020030388945d82e141404004007141090061030f44000c90520300941da06a401c9000701552042e410800240e0704040601c0314035028041c0ba124400003403000d09485010f054200c03418410984600f03a4031000d036407000b00a2050100041004c50710a40895030341c81807500c0c1414000720305510580c41207448400c00c205010b10b5400030300e25000700030000500038944038001011500e004e4480400aa05806c0812440c01c042c410f808059480c14000c002814071000020103d101ea03c940b50a03209401c1c01080c003290180d008210b135200300300c20f18101d07481c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 810629010 1250 810627760 810627793
    0x30415150f08010e03041203111203090c0a180c03020c0a061d210703020a0602041203030b03030f070f08121f0e150d0c0b0a020313090203010501080402120708 70
    0x580c02149482110700c20001500a4144a60700740e00388014042d6003020b103465502d1507440312441c419418040418405000890280007071030003098200c1d462500ea045c15400d03d450000890070304c500652400304140a040c0d82e41d40d00c607200a000240c0421160607881086001e030060b0700400c0304d04e21580d03442c1020845140c00001801740c038290b02d040901c3c049800d641d900c6040c200d44c224004244c000d010380e44e1072401c00808429000e0700484403000c0d16a0354400481c0e00c0396010940b03035041d000c02041019814001c15064010440c011414110181882d509510800c08020316005104030100100480f04094a501c0c2d031186100d1041d619100609400c0b1088030f0f007144440c0c401212020548103504014503000b100e9541812a407001c10301c0610000d080012015910a41c16a10004e8031403c1d20f80205207004c1d003a4003568941008440340d1b82600026080f110a6600600050120380d0b0b003c4d00030b59010740c0403900400400114840c807402d010154012000f035008004c15071107920704 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 810630260 1250 810629010 810629051
    0x506041b05070b0f13020d062403020102060709060f2019170703020309090910060f060f140a2703110a05040504150b0a05090a06031e030c08030415 65
    0x900d140f0402c1d035581c140540c941c0404980803c1594100c04840c00503062040040c031140740b10f030b007000800403194013506d121300c0340c080f0303c82c032000d10311400900c21940d060103c40d42145880c180705000e541455009400c2c04024a984010480324080a0b04a03032000304044080c0302ca80c109a4058510102050320310103031005c0203440381c1c50100c0e040b104d0084100111510f07250150b000c1c40c105a200350402c42c00c0600503101d40f19600c6403031140c4000e840303076100e0340e00288682081e4107551071410401820903090302e11580b0510029103082010544802c0850780030b41d001d450003da450120414440303005040090403400203047d41000300c100800c0b01c60000030341c541100c0c0c2c0389010b692017003080169101190300034646103d0088400100c001600005d0340c3c180d0081c0081d2013030703803542c0105074440c40c122028038002e502c40b0710400520061203c075902c1405018180c0d00b134a501d0792000382c448948084014900030000000405011032130321007444450240d2030511407400c04207401c0d0320703605 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 810631510 1250 810630260 810630263
    0xa081b04050612150604060e01030507030e011505030d230f040f060c03021516030b03120d0506120109170711041107060f0501050a05120102090306040b09010e150a0506041b0507 78
    0x40021403041300c600e000d8095030112049950f0310b10030291f604004401402c1c000e08280145510341010324941c0c0001c3c01003e000d0010182c08013010b0345002c0c1010f00d0250070700b40323100a100fa0744a9445007100c814151901c03240c50311560640d00c0a1007071142c0c1c00c610a59010a0414440282c080390840d4004009000240603a003210661514414407000249003500c0c000c8003490440f03414640c5034040d8201420381440202074866984420001d030366158401c41191010a40d182c00b00b007034512340101c00184205810000f048140c0c200e5031142503503580c0160022105001140d1402080381c10711100c3c482040c050300600115240d05005c1e81280c01a07071089404504082c00c102d0140d01d80d21815040b141c0c0204090401850102802013101044e01c2104241d5020030003403200c0e460800c400b90003548203414560140c80c0045a0a0843d48998405403454000314404c80754503008004040c0c0001e1400301c00a000c3d220031001400402400b0031381c050444c940ba400342c000d281c00c07401904146 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 810632760 1250 810631510 810631531
    0x1060305070e0f0c0d0c0e0306070f0305090604050a0209150307030317280207022b121d01050d0905060c04061b021305060105070b190f020a081b04050612 68
    0x140c5440c190102d02d83d5085a0b440d907550014081c00880350007603000380403101514140a000e458000000c00c0c10203804403002c1c0082074060914100c0c6d04e51500c40c0b1580001c81c0d01c084d249030b0810740c1d241e9032181360710074000c2d1003090000040707480310301000c0611422280003000c4a282c40e54903d03001e8503040240b4404c020b040070300c1002940d080b0012110001d000718001d100000d65500c080384800a400405081c2c0c2c00828080d405104d4400340c0c4160740a51001400411030a000c42c81d240802d041450300364030400031805003a44c07000b20550840040480c090814a444103000001000140140080139280d031241c541480a0502c05000600035a44165202e04017112100c03d400911014000029004002940c03031220841d8240d12a6410440c14500740e46800303c02d0b1980030051406541200b0440713405000840031380303c80d2042032420f2584000550820441d400041e000007801481d0403c0320103604500800d407484481114098840101059140c07074083da8000d54950b0100c13040340d640c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 810634010 1250 810632760 810632789
    0x5070309020f0907091a131205071e03151e050402040e0f0a080a02070e0403090503011a060d052a07060605030712030e0409060e0a030f03051005010804020f030106030507 75
    0xa403c14011a601c1401581c41e03038050240743c070502d00122040c0702c02035510080113000400c0c80c850350610f18070052003036a42c00981500c4500340301d41072240c0b07540302c101c220707601084038014801224504800c9035000008241410246400c16000c1d00801c0116411107180c0d91880d256030019511145c01980292001c05c910407162860a60329100c9504101c60741c0e00c645082c2000a4080d00100b10700303021441950301c83e50750b4900c98030101d0001e85003103010503498802405581030900c00c0a218010b260307900080d800c1001c0108906209805050303000340d03168000180312040780c040c04a000c0d41c0c110403080d007040c2e0302480b00d09682c00c50501180c8213400c107000010607150004da1310041c0c502c180e00d42003014049607820703110380700d980407080d400580f103000b080007040062080c00c99000041018141c041c8191a0041c5500107515540040c189408207000e0b402c0d01074000542583d10a0900c2d030220b840302d000281170a4000c0072210362660134803001004002006ca140d80880b521401c0a820 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 810635260 1250 810634010 810634039
    0x10315050f06061e070b1305210403120905090718080325030e150c010e0d1b020f09011e080c0907140702040f0e21040312120507030902 60
    0x10004001d6603201d9100905015103d40b100c106154135202078801001c181c5003003402e81d68220049400c03940c052001d240d1007407030400c0c000d043c000947e0311055100310440c4c00074590401740242c0120b00010303100e4500ca900e14900c160040b03240741d0242070010017111031890245801441d50074850800c81005442c020000b03004800041610710720030780c815103120310f200b00016803000301c110008158100070340340e1401c90312a2030312480d21851007070103003031603a42d0b4001000c176a0a40b00070304000c20b000d41c0207104d00c01c020340e441052015020154951845415201c2c00080c442c0321125404076030140545d0300000e1140260301c15081000780d9054091000d0b40c0d6001e00c543c40c0d400707030602640c0040c100030004140c20300c144289000c00c2518503050b4240100c5030003003011a03030503505804946942d6000c008020100300082c20103001c65020151910703403038200d1181c8a01507440000e00100e0221b0186001601401d4000c1440f0190401040075240086008014020f120002d074050351b20076a9404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 810636510 1250 810635260 810635281
    0x3021324080c0a080619030614070e0108070807090504060b0d0e070e040206030a0e01090501151505070b10031709040c03022107020309030102220f150e03070e01031505 74
    0x14031a8103100000c6003048400f06060720708000081240d0b911410501d0140800081840c4850156000f040001002646692400700e002000b41904050121084414041d0f0780d0025000b607104225180c803403295210b112042d10b422107035030030241c1d10a007014004185003c03810080c00c868222840305008800040081a4485440b0300648101c1a1000c1c001400f50402030002c54000c424400d0004003070b06580e290070700315400288201c4503651140808400d40c00c0358907084015040c0500c0b500b0380e00d103003100302511034030445c10000c0c0b56540400c00208020449005400110340041c601c03c003540c1401c2d814941980440e40742e51140781746c1844a28803038800c0c42030b01d4004d511021000002020888000720b420b01c010841e40843c80100101552514280040c1c0031403131050361140f28091002c0510507820031075402c88801451200e03000c112203000a8600d082c0c1005508016a1003085680803034201040d581246441861a4000004101501000c410b0510581c48100f005842c0c0c1103200303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 810637760 1250 810636510 810636527
    0x3060c1303120e090103081803030301051023070c0602071208120a0f06120507050904030c02092a0c0f0a0b1906032009090a051c03021324 61
    0x211049048034030034400140b04203442a000d08450421050503070303a00c0c00103401c14509800071a82100041800c0c1c540d001d0100d1010300913030048001e5420740d0304100110b5020b003c0200031a0070020200700980500c4085e04001a0100c0e030b96005503601c100c1828940184059485904014401e00000261901d04481c0b19601203502c407410a241c20050051002e0ba044068945104a541c0700d805d41951041c0e8802c0700c1c02001c10180101090086080581c20702c060350380801d00600906040000096200e07064030385040e07040f00c0c18002038607100914802240561035011480d0700000c4103075404040c041c042c00ba225501c0046070790700c11031404a01c0c3c031115540b20040c0742482c1017012038000b00f80c80079040c04425992600260b00d82d62900c502450000501d00b0000d07503900900c03008020700b040101164803001e1200101854140d580d14a60745110020070b0152420b0000c10028150b4400e404862284d82021401c03030b059a00c801c060354008840508001d20750f040c100b0500081ca0140606 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 810639010 1250 810637760 810637777
    0xc0c02131a1302090d060c0306060c0f0206070f050f10050c1207110c180a0b01090e01050f010c210908120d0e0f0615090a09020f0f131a03060c 63
    0x4440d60301070400c00d01454070002400801d42d00d800b440002c0441c4c6034044420645400799801182840309208080d04891075500400c0800481c5d00620004c5480c81a02c1c03a01706074151a215683d80490600201c039150340000141203004210b900fa4401d080001e4400ba50350320002d04200a0310340c081d85050030712455581010f00c4114000041030b9500074443d0099075000503041e41c2403085044001380d026480c03140300340030041c0744800f4418010301ca4442c03500b04560a091210109040010740620b01d1014800c56210f20400d0544152a911442601c64500c0d0f11a08200c241c102d40c01e41191101d04845481000600542e4005200003000500b032a183c0d4400401d80c0c43c12180c5586440a001e552181d400275100303150840541c09000c01203203104034080a000400001c814007004101d91002d80080c003600d040840b501c0140c0d5501085030382c000070440d4600c0c0300b80080400f15a205134550b809072801480c0c0000e1503000c0c4194451644107000841c29038a20361307110300d02c40209000d040b00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 810640260 1250 810639010 810639041
    0x305150a12051f0f1d0636030c10060b07120c02060c060a0b1e0409170703020f010e0102070b010e1504020f0a0e0a1d1008010c051903050108210d0c0c0213 68
    0x207c2c2103243d51007403050040d044d00d034032400c00e44001c0e55214401c003c100d2484c8101da00014000100600a20a00b146144084014811285000c00c0c02007180240c00c00640307901281c0c02c90300c0c1d009000d0100c00707092a90103418592078004521681b0b40760b020842d52089013600345910142c42d46011241110000c0d0f0740d4101400c101309000511004140480703040756402010f100a11030092040e000d01170103031280d0300614529105404044c00c0d06d06044058005a00501c902000103a6001045044d03400100f000d41080c3d58448200d18029800c0070300c0b6401c03510019162520914140081440c85a0340d240c100e4860035410034001d420f420f610924080f044141c0040741ca0380c0d92120070340e0700720508400348843d05488005840c21621485402008240005500036141c0211041000c1c0348805042c01c03c81036150640484c2c8840485c007003c2c8002149020081c20000c1d400305460541e0307103506041040c261845000381c50315619501c1644107224010703406083c41001c3c09000d0703080d02c0358031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 810641510 1250 810640260 810640273
    0x9032b0e010b131a0d0b100b07051b0f0a0b030901061415030705070614070801053001060305010e010b0411070f08091f0207060305150a12051f0f1d 65
    0x49440001c4c4402d060a5102448001c03208800b0395980312071400c2d2038002d055150b154104000c6600b00c1d2185680805d009840a0104c0c2003c9040803d10040c2213204181c100115902c1070006210407146421443d4007032192000468030003890710185114055000007040030a803105814000c10715500707100c43c1d110300c1070641c606420116001945c0c118a45050032401e2640035902e05081d2144a0b00101100c0441c00c104004160b200030345a00400703083c5ca060905a194410074156551340b400804031481512840741d18807102548000e000b103400c0002004042408065075018051100f02184614240300044990411030300454140c0b9900c14009940d0303594030780d54010039802500b0740d107610446240d0300060b84544010030b0101c4207425030140141030f003031520140880700c000c0c1c000c8001807202007800c1d00c940c03207000c4201c042d52009400700350f40b5004e91422510302781070307400b20004410303d0303008600301448250071241e080da01100301030001c1ca410115401c0e501d010000e15000c5540012b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 810642760 1250 810641510 810641539
    0x14010c03110f0f04120503030906070503072016090609051027140a021e09100804020301060848010309050f0714030c04150e09032b0e010b 61
    0x20b03008201d5184442d081900f0695035a0415191400c41e4809071103541000003000b01e1600240889a88032a10741006820340c1007503140205801c020b1811000d0340124985007101c111800c02611003148024098001d485071103aa245000e09140d01ca6800341509000200345543e15500c42070303003a41c10100d90b50a20503060700746000f103410f1039603440020300c0c0d460135070f0b21f0071000b080000d52107120340c500c02596031920100e1000904031140320002814030148407012040c1d641010400002203240f4161a96448500002c0c0c0140b410350b211001503c02c82207107088007421035031004a1440d0f0311120094000c1c020480910720007103403149041071403501d210100c441d0300942c0f009120340e01070343c21140780c060115913030342c942011600112803040142d6034800d59854100051006d040054a062002c03002d44001c58a004800d401190546088440084c0c074804041055071640094070300106007140202c0d4440d61089040c64025000500305a810440101c050160b07d8090501400c9a0085000e2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 810644010 1250 810642760 810642787
    0x40501020d1b0f0818040603200415080724020c040c05130303080a060b16020402030402030a0f0c06080a1515121410081506040c031814010c0311 64
    0x82c90400c1c103240c05400c21042c00326500101c2403046900c640241680d4265120058550002130304085110b2410301400b4400140c441a01c042c03104410b059002c0035091501c00a00904244112843e4024011000103001280041c8000886520032000c000442c07000c001c035801012030318240c102687c072001c001000d44c2415403081d900140286030103801e101c10000c120703170084c0385039006400040441d400d1208036040c0d4800c0070020300301100041e00e000c0407d942420080f5100c2d00281c4100e03070101c005801d6480c240020b410039903000700c150034403616600c2c7c40d41d0f12100c9801180700040d060000a14028400d200b0300d070042171450b901e0a0348629124254038480d0034141808104849202800701400003409200004000c0010748040c9141c11490a00c008005500c1250300d80d000d40c0c014016090303402045c030b0304032501f65000f01e01c4151f100416005000100c0200740b400010140c03e00a100e400c40340440f01854200081c0084031a0200440c10f840b041c7d00a08003107401005001000c03103c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 810645260 1250 810644010 810644027
    0x3240402180f0105010e0409020d0807030302070b0f0411010c030e0f0a0f080a0210210506030c0607030309110f0f04050901060b0c0709061e0302040b0d02040c0f1103040501020d 78
    0x40200554070246004907429020042035031840c00740a4100c0041c0003a682040100324503610070350742008501202c1d0006400d986e581783c40540500c0000948805140c8a80c04444442e6002a203002d00350810807050140d05401300c400f40c0c1c10803100e00c01740000398490300c0e00307003070a5400d0f668a4240750b62000800804400d42048030b584072084140008240c041044a9001000c0000c081e180d90051401031042002c0c0100c50841003000026440c030f6090308141c10082203820088000400d0b0703940c031020038504080c2e1000720b9406400403a103082090383c076400240d5070034131405c05000000400002d04c0702d0100101882c5500a900010191941c20554040d03988890788a00115800303a5482e20800a070380076038000e403c140c000c06010b210020300382c041c3d40002c00300a9000d552400001030050800655400000d02c00e42d114201c00c42d16649100c9030404543e002481080707090040d01007d01481144682c40d000f040c2012184280301c0300c080b0555084030810380160404041002e81218000c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 810646510 1250 810645260 810645263
    0x1a09151b0a121b09090213060804030e09010b0a1b2d0c030503030402011d060a050c01091203021305010804020306150102150a050a05060405090c04020f12090a060b032404 75
    0x5480d181c5a00944483d00a1000202010403c1e1403001c001c0a0001c0150955401c502c5a0a0042104031b4050254000000454249181c849109d444514044983c206070481e16079008040800200300c1080c00c0000b44840043c80e100d40300046c1e142221050140c1c091035020300500c80b00304100400503021010036030201d041c040380d40709a41301642e85070580819a001503c1700d0344080b04202c21541c0000e0070841d080601c41c00c1c4150124214000f030154820401d60204002000c40e880e0107110f802d40203141481d522881c00144000031190040080d080328100080150520030b0016155004981c3c5600841c0c018000c0c0645507a08800340d00710b04000150316045220701440804007000c0c20b0403030343c01204054030100325420000d0b0404103603900640b206c0d01ca84d18110a1043d4110002013100c0e4020b030544026031680035062441525008400c0344070040040030003041000103003c41e03030340d000c01e1003203400300700c1502d401c1d09050342c4103002c0c90b144111407084c07242c2d507200d03903103d280495005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 810647760 1250 810646510 810646517
    0x3020f060c0a05030a170103050c0d020a03120806030d05040612111c050405070f050117040c05040207050705090a021201120215070b07030e0f0d18031a09151b0a 71
    0x92404121490150708080940f0503400100c0c52411140c2d00607507154510f0002e416414555040d506c56030f86851051008038032420101c1d424a0071034640040d00700095401c1071000c2140c560f40b01014281c080b017210014400c1c05000c4900e00c4a5000d14140c0e820344030380d90750340c14104600c1d41c1c0080c01004100c3c0b842d00e910b030042c401c20854070090f07548003403048120700c00401c0b54202858001e241000f244c100382500b000108041c896a64065407803100c4003a41000c20042d521203003480c50318141e241c2c0001c0e4100340000f40703080910800084000860301c2c00d48400c0070a58a806a5804a0040300206801918000010001450051100e007000d5000130004044403050340d901c0509680800c40480325485030f8400c10200a805115081c0a9007c1202a09640c3e59003840b1725180d00060710704001f4030003500160703200200c0144080b0059544110607100380e00c03030741c0016510720004403100714a62103402e040340d14682003030340070314061380309203481207008562521414415000200b0300e0080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 810649010 1250 810647760 810647767
    0x123190f0209190f0801020406080c0307030e060709030c170a080a0527090a0e0d0c031107030f0507060c0312050402030a0f061d0303100524190305130c03020f06 71
    0xa59035101d00300121503c0803c0c1c2d440c981c07480c003110500d002040da0700c40103a43c1d1040c00300300101600030030610303030000f540c2010300d51b80d948200f010b42c001d100b5031050034114404c444c10030004503000711031003058038000c6850580081d41da48082d1640300f640880e180881d080400310f200054040b0028089a40d11406e119081040410588590042803200e103590300032101100d0000c0d08001500070b800001e55101030040502340408207646003100c00c0c890381049080521007092606c100300c2008103420110555003842c0e0b480c2400c581c1151150420340b500d004001300000c070f40e4024202400f426500d42c17213051600402c010048003e100051041c3c1c1c06010354208000040d1034030a03002907240c818600060140f400b101c550310900707840300e20080f00303070b1003082440341d03502075001040201c4004a400a02e07280001d000a580c1c98000381c1441c040e020041088201c10390703010301401441c403481d0380811450750b4201606400510b00d034009040b41828040a00140c00c114008160300000500a0ba25 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 810650260 1250 810649010 810649027
    0xb15131215050c07020f0306060a0b18030114070f0c0c1208040905190e010c23120f040201030c0f121d0d1d010e0a06081312020123190f02 61
    0x10758000700c41d843c50680e400940f0008501d0200c100031305485c01030380100900c2c60240081030014415001d444900d20000c14061a105925070b6040c101c05000b4000344240f104a0101e980261401c0da080b401180c0c01c5200313513549078801c560912a9a400c1131194045130710f00b400203d048203805c04140d906000800c0081204902c60007554014222059400040d01d60078100c2400c5401602940744582d0422010461043c0d0211540380f81513040d44042500640c01c1c40014120312a0721204281d40080004000207002e861105903c40c5000380c900b4441c403a800c85041b150b40303a008107050702003140e80064104450199120301d4081803020900350800030381c407041510385903800042d03c00040302c090b0600b44071180d582140384e0402c002c3c240309020f400f141000030703405101d6004403020000983c001540b040225030b80c0e140060342040494940d003480c00d0009018001c10394409034138040c5901c60405955580001030301c00c2c03d900b9005a24109140c0d600c1e4042d0112018101640c0d80a005052 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 810651510 1250 810650260 810650303
    0x70f091802150a122d06080a230a150c05090d0b10030c0b25030e10050f0708030103141c0e12010218031e03030a0c05120a0b151312 58
    0xa80681c030031010b201c1c00305c41c038840341098804500a03e2102c20b041101c1006200d034005000000180e01c0300300c882c00c4880c203001d421640d003138041c40710000c2d01c561000f074406d014030b00305107200100c40b18a0902042c0069001510280b04d078402c0140c00c000c50640d4140419a046034180e084005a040440c455907240c440640c012001d800840012400141503900c0b08202410280303103d8600075480c0f81c041d215200500031a002d4810700d0b006660041013042c1e258030802c00ca61611034034070601c54aa9940f410098165002400111030140d044040040f110800241000c1d015800d42c2e01d00b01560b00e406001c4804044000140342c10006003000c410313242e8800e00240c00b01d000040103001c10658400c04144c41d101503c680f1030b030004948000d445015101000310390707201c0a00c0310041024001d03100210f41a100d1403070b02a44410b200d10a1000c12040742c0c011102c40b91084443c10340c84410000303041c21900c00c003441041302c15201c0c00c040066221a882000039640150400f00f828071b550300182 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 810652760 1250 810651510 810651521
    0x1c0209040b090c031c110712060b10030209130c03180f0b06090702120f0d090f050c1203040e0402150c0a0203060f0108101d070f091802150a12 63
    0x4451001c00c1d00c041002c0184100880c54110904400800726191419900400401d12881c0501041410111020066001c010034001000720305194590700e0110700f009001003005a00b440d20503003040e04003030455403007030080d0313012807070020155804040c88402c0b2000421030041d88800307054640c0c5408020403140c00c850048103008540503217000320180340140907607030000c0942c2c1c400c031100b10038000d5140d030000707842d00d80400c00c200c0315503510b41c04c0c20007004074050007907088245814082d113841000044c0310a01c007000c0c8a01e04885807030070010300f044861031300c4499001c0280e0051100b00141c1c24502c2d007140c0c10500252480c2d513161000144420380303a010300510307011940310b19034800450900f04410b640c0007614000801c11541400741e00754680740c03076090851009480d803100856010316000103000407403414041302c41c241ea0b1403104143d81e003072901c59a4140c61034100d040ca03490823541d01c50000341d9402490b0b00a42458500b0713210054100d40c4e03994080100c01141d21440201e1481030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 810654010 1250 810652760 810652763
    0x20f031002090a1208030705070609140d0e01050405010215040f020909061603051501270f091817160501050a0b10020106080c01050a021002030c130b04060903021c020904 75
    0x5a62104810284602034941364840407900308a0241580031581510a4a401500a2801c9640d8102c00e05203d8003400c00d9180180c006882082000041c0000040c005010413145c1c64031003000d50300d940192101d000342e01c5400e02503048111042800c52240c007031103610512031a140b1403804025004180300e00000c0b40c080007594003041c14007000311440f10040449034801d1400340520b140c41d003d4031041000b403820050500179030a080540710b60009112181c0f980780440d54001031039032000c103084401c40034810400c0882ca0706680b10345080502120803c00e9400c2110660882600400c01e08a58401d010400d003000245c0c0070b0030001482030080900902c5071140c04207803148001c00704600b64041071407100a580c505001005080c0c00402e10f626a05424203009403169801c00050b41010315024015407006e10000412400030180006442c65400c4207504100540d01c0e03080f048460302c00c1d405118045151583c0800062600c0b2590340c0d60601e2148500742840980e0380400d62540017501d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 810655260 1250 810654010 810654043
    0x3020403020102070f061209050c12010506041805030712110a0b07030b01110c01080c09040612121d0613090f050f060a14040b01030e0d0203030a050f071209020f03 72
    0x604009560781000074802800c42c040e0030b05003540c0703480c8000c1d00c2440503c140b131141e59180d2166805201c01030003010720001001e8240d140c00c00285070428006c10b0103c8560b4401c45ca04140b540000c901030400c56281e039070080c0118906607181d110001ca070039401c081403080104003002003154036000d0207042025445a41600c001e801c1002c0003505a40700928101e0420208010402c910f50b03000480414050007800e103511540c03900b0912100512802c3c2e0b0280e0840d060100c00550341c840111a00881d1b4003507010700c0c2c08800c500008981e00541c03055034044150820104006c0d40c2383c00b10050580301c081c26284d291143d901c0e1004030507200c002144c9601070b591441000706020914040340c1d40031a00302c0342001d049080c01a103845035211100114091941d0720740350701c0b2690181d030101e4030f000200c10484842d09141e41c0700035034a60003200c2076000341c1c3c14000071405402c2805600f07405140f06403180c4010074600d4528100034030005006a03400a4035445001080e241400404040e80001c81c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 810656510 1250 810655260 810655267
    0x1c060305100c030507030c02030922110301231f0207050907180f0609030807020a03050a0b1b13060e011202040b04060212070203031b071d0a0c08010608190e0a030302 73
    0xb00050202c40c0010b250900341401e0103500202a0750200c01c958210000710b03a0031181d56518141926040b1990b080307040072600d401e07420a200b02e00b80003e18122003000012080001d4551084542040906242e907044203468500c180c041c0d1489446281000e01481203c25065880001900039801900c090011801d0036039007034500c544200041001d0003030035a222514601c0e191000740369030710910015040c3c80c400b14000c411580c0d209403510045030040201e4070100705c54107006180385425034150f810600c40c10321a90303219411406a84018444d0505540c1c020300c0c001055071002c0700485030700e0401c0f004221070b0359104001c0c40a00040d21800e0f62031a152410094083d14100b42d14600920006080c0024001a50000115894600011010102c40d004803d1280c038103416a0000e031104001d40326140301301100510814400c15107001c0c01d00c081100140705503a00035080c011080050048000948039450702c0c640201a03141d50358000502000d4490224242030000d40100e00198000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 810657760 1250 810656510 810656531
    0x150d051021050303151302191205011d07020f06090c0f0409050c060702060c0f0a031b020112052215060b0a02031c0b0d0605060a090606051c06030510 66
    0x80416451290a00160440c1c21400c0d8480503a03030300004143c0800c107410b00c800d990054a905050100112450005540b40c00d48110012000c1c01d550554400003005d000d4600300c0040d00780a058120380400c142382d41c10103503108030140d180790002c10300c00035441042c96090480504102140c403400300c107009411060001010042c0003000709100b24400c90901c6802c10224802040c1d50840c454202c9140e0f59030007291000c64094010450038030598003500310324240103e404580c00c50a80d00c40d6880882c4d00c001e0b65481e03104040311840180c0007540040301800304159580c0003a4101141c41c80d81c1c000c00c0349800752142c902d481d4510403071f90000c6241c1500b50382a81350044a000d03210041c5080c1c104803030250300a5990003004e00764141d00610001e000c1c25456280c1c040f0b040402c01504c503071b0320b41072503040c4040a0300c0251811030041c0100b890000d5402e089108910544015070380c0d951400b003008220054841c1301c0d1a200d101c10343d0782c0d40c0020000382d0820003000a9283d2000c08501c1e80f180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 810659010 1250 810657760 810657779
    0xb0d0f061a180103170c0c0409140a0501140109020703080412140f09090906010305060c03100f0b031812090906190303020a1203060501050702120f01060b04030c0801090c05150d0510 80
    0xb2003522507101501b071095030444600442d0302c0e160441c090710f00180504207030400c01c40301840e06290b01582c0c043c600455042c00010341011103501070800170441541d0f03961504504902c502e913009070000700004042800201c0e059658220a040d5107091210041c0c5c1e0403402c00340358448440846d038141e002403d82301c01c0c10310251240d403055607000904103d40c07550b22400d0702c489000300320300200c54000000904501c0315a0b041e402400f6550f21036191103860b050781c0743c3d05910650303218909000104104480c0346002031400d1803080f89161881c1005150070a1000811025020603441204206500740c1e042c020414800214041d034010440078007203040c80c09010103021001020182051010710003640c2040868114650542d0000d42085c01c5210b49401e2040c40c2d440b00900f5401c000000580b00c442c0300182040c0c0c2c3c0185421441141e0314038000d401c9416268009050b4540c0c2c040401003450b188a91500a02c18640300d03038500210080d40300110b80041780c2c1c0e004c00306a03005041c000c00e0308 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 810660260 1250 810659010 810659033
    0x2040e06060c0303220c170f070b0901030c020c10020a020910030c0b0307051306120e0f0a082809230d0803090109020901090c030b0d0f061a180103 65
    0x1660744500d080a200c0c0362948900c402040100320903500d40c210780c0328000015098411582010004814036110303c0d941e04800a030321008940c0f07104800103400c06210100310a01220b0165034060710b0134145000540280641501200130340c0981c050413940c07911107205900351650307164040d01c1d440c24984104070080101408101034804d403000140000362050501d0000d4403440c075625900d03540d071810119868440d150249451555890300081d441d80c0000b800500041c8041d01801070000c5d50305010340d0b481d110444500f1a0f4000d8004070007060f042002841488a000107400184880d07080c00c1450001c14508140003138014071013000b41d1034000ba03102414504201c4100104500140021720101c191140500305000c000042102c2d94825880100c1d03c99015080010640c0d40d5095400241803610140021074201030120b44540380c02000d5503a095804046149240c495440d007030018141c105101c0c6c070302c1d40f0f01048204140e60348202181c01141940381c2581540c11868018501c20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 810661510 1250 810660260 810660271
    0x708031e071b0b0a020705030705010b15090901260304151205010b120a0f060306050a050708040f0f030e210106050105030c040b21040b041b050105180f0a080102040e 73
    0x5071081c1400503101c2d03000d080c010650340000d992540b540b140800340c4000d100d080402096440005807080401606402829940d078044624217a04900b13040085601e22418981e41c0d8008141401400744010750030546506038070b64580c81a080b06900c2c001c5103558040d40281c080e034171149640c460035a83c001c0c415404034196420a00c500d51403c06c2c005258002c2c240b449180c100c4100000d03c0440542d03209046040d040c0200b8446182e690420400034002984c51401d03141c202000500034502404d102d901850f480381e0010204070007030319160b105d261410b03022410000000c81c40710707a690b24003043d442e008080c4082040210511701000d03007100c4850744494103020082c07041048088059050f03c04840b1a500055510201075160546503103150120302807503c160302c14041402000303a41140b04500c503503081d40c1c1d0101c58a200201d51482031007820300046007048080014420f003d8004001000503100e800c1c4003940c4000a000003065411250060b0750100d0208001ea8a00e0308654201 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 810662760 1250 810661510 810661517
    0x4110d021219020a1b1401020409060e0c0313021002030c1b01030e010b1e0d062a2f1603050303070e01030b0a1a1204081c1a150708031e07 61
    0x42400c0310050540310b404c0c4c01417080c10403410600002d0200015818080740b41e1072000f1507071103859a02c0c0340700510080c0610007800d10011b0014507210f1002003207900428100015501e842c00320ba081102c1020300b200d541c021070000307000348868003104204201d07004080805140c0240100d100040c129540403800c003100b41e0620a4084103030311480c14204c2040c1c01d1200340311010f1501c1012942c0f095a604004002901e40403e240325206078030100318842e0a0780072300441c2c1d681500b42c22030b01d200361160165046500400d01300702c660503c6e80d860100d020707620161040304c5092643c1c91205085980300b50381d143c100004000c0c8046d8410070f40c0840840900701000b1645810010070300c2e20380365015101d41f05440c0c0701d90158114201b03043e11402108954031100d03d1800d0302d0210b1164000c6224020030408480c1403004007045070181408281240c4514840d207401c41c810415514001c1e20443c1002808100d00c1c008225001d000350311660380383c201c4020034000d251003402401d00003007820040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 810664010 1250 810662760 810662767
    0x12010209010c02090612100209040c080103033c0f080a110405040903020c060c0706020c061c0f0e03070807051506181005130f05012304110d02121902 66
    0x216a0030441d441c14483c1c054a000c803040e038401c0c1c082040070710000a9081c007072148010303e014400395034008060036131040c1d034241700b403041e40c84061f20402e60a000040c0880c0d00305907000c52200341000d011901e6002c295080c0e400b0010060a1110f407442c05a0400c0094020142c40c081d40c0e800034035854205e51108010401c00003041c0e40d0702400d001e140915841a40c6400715081031610811501c1901c04000341060303a6841011160b9a86c0e0078280316450260083c1a003802c01440e200701a10648441c00031540e56807808048448010840350304040c0030b00d6640d0000e14106d80b000c101400c0041d03c00d450710b82c1c1e01e007200e04042d86840c060b600c5440144400c0f40400c685034585000380b11000210407048480c540301d250030030365160456000b041d00b1544260508070b8440041c0c0100c2c000c0c081c00e1008001c5662100043c1d40ca50650740203ca255028444011910b820158041031010302002c00303031070a00c4403000403034040e030b446100380104003440a001c2c021600ac580000901d54126280d04625 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 810665260 1250 810664010 810664027
    0x807030e01030e031812210307020f07120201030b0a09020301170c0402030903071b0302182202210106031e120f1706060d09060f0c110709090f050a05030702120102 72
    0x11280d90f020080d07130040d4070340b6516411b056002c000005240d0020f6140603814140038440120a030001c80740d03100148140c1c45060b0304040003007608001d03103030020500300d04440d29800540180810044a60b049030500500103180303125803028501802c200c0c490118130031040905c1a00e800074502d6128800e40c8100140700f180d940000c21603440c0ca07840040340f100070b1141000c1603d01c900960000e500070030301007a8100011841d51200384181404e00071405000c00070642c4106184100b48000e4015843d80c505086001e03804990301d132100010b50003c031303509480e03a4514000003603080506800e0094070007408100300003d4002c01003103c1a04d000d940c1119212001400404445800c240308107041c0042441307511031074101e0300710312125003044c410030215107042c0008240d02d41c0c48444e031a00e4003041894880c1300d1811038400d12100c1c401405402d0901403014000e00c0c038401c0884600440795080d80000340309002c03c2590303500500255031100c01c0e1340140034106045940900b0141d00c104820503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 810666510 1250 810665260 810665287
    0x3040f12110f16031b030b040812090d0e0103020c1e0102090f0d030804060203040201050c030c0a2915190609050f092a16060614040c170901090807030e01030e03 71
    0x104a80d0064100c0348100720b0141c043d852280705e5003018011802803000c02c0140a0084020300a0804801c03101308265509411641c07101801c40d9580300080e502c040041c6150300c2a0040c0294405220944480d40b43c01001c0d1000099010600079269401080184c3c0902e031050f0545840e500540d02c2c400309042c141c0c2c00030301c0c41500400092071541c5c040003140c156403140c015281c03011910801c695540c0c480420090b42d03164403600071601d0700000c00811410f03000d003203000c0d002c480103140c5146550300c400940508441c4500303002a0004102002c5200030000716140c1d10042901da00d829603d0750034241404250800000414094000c450610141c0080c03090b0807414070400c082c21401840300f07240d151005218000020305010b5000d5695001d001c10396008100721100c07070000e0700044040c071080c001a5042c0584400208060b40c00f0410400d8a00c2d200c40e9012480f4400040c1d8103a80b661180700d503401c0500140c0003c1d107680c0b0f004500c0d58052013141000c9106400440c00d2000c0a4103c2c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 810667760 1250 810666510 810666553
    0x40203011506120207060612030c17040b0904052e151b0609030c06150f15020319050c060a020a0305091b040b010909020a0c031202120c03040f12110f 66
    0x140f00198000390741403d02c0300660010015081a1071000203141c0d15040043c402c09641f501905e01400303540b01c48640505c10400c80b400c95900410941c140700c015000c0100600000300300d0007211340c982d00d84884c160b10524000d20441808001447e400741410104c416481402481d0810700c41e56059002c12000c505000c00a0142e000c04041800e440524040300d50180045000744003505050442c00b108890700c0c00d04007694403c0e4001c080f402e030717158042074400c044840e1640140e002000344801d807803140c5500e0f81ca1b4a1442c20315034030340615442d80d180350250440e41d107020349a01190016078161f150140540150b03a0f0b0b0000c041c1c40308220601c413003034004114810311a0b9514100780762541d0080075441c00501010784115210010848080c00e820003500040700000c8040c44a0001007401d07100b40c40304040c01c00481c0100d81d8544541c0740841c0c0c0050825160f000340e60551000054002031b40b04038901c020303500c2c0340080d407490303440510f44101d00c025681c15820038181c0d640d10110b0b10711032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 810669010 1250 810667760 810667787
    0x120601260a180524090703051908130801020a110a0b010b160506090312010501020c1f03180506160903050703020603040807080a170705041a0313080d091502090d060c1b0b040203011506 81
    0x27810071440316140c8151240700300d0440c00c0020b1031032500042e8508041d800342500760210745070100d95840e041e0089840790351001004100300d240000500036910418080d180c4240c6c07040d510300720000191103e41c500301c000c542d800030a07840003880e002c130702c1e541011f4507004020a000500c9000e8100001802d07943c5402e01040e04180141803a0988a20030342100036000c0c02d00d0080e0043c000030f03050441c0c5a0000711500341601010036170b2218824860030454045076009805080e40354190760802c52250f0000c3c00030740d0450b20071f00004010524030002400c00204a80b150703a861040d0f40581081520002c002800f40706040c0010401c12030520010501031102c122050765a94624402c0d800d41c07a030035a0701410b116004555840d842c14036a02803070b03615014002000440081d00603d00a030b129500a2503080980d0a8049000452030b400104203116079043c00540d200303c8040820182c840024155010900c4100b030206605081c441c4034025410441600c2080e03040a1000e030121100340ca1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 810670260 1250 810669010 810669043
    0x150c021c1e11010b010c08040306091a0117070506031909080d020403030f030614130f0f021602040f0911060c12120601260a18052409070305 62
    0x10500d90920521055052001d8101c10306858440c60314010a6010704007a000d240d0344c42d0035142d50b110742c002d9012036611580011740350314040c119555072010782181d400c01c031403021052004102115035200c0c01030103042e10041265518481d1480c5034074151040e480742c0e000381c03804c1041c40820b206900340c1070382d1920114404243c038020762810103003501c43c00c1c0c421403000f840440c02004059000b440209880502e940900601d9160147c4d80c58040c580e90700268441c0c074590007000c0c04040d50700000c12031108400e00141d0000b4203880c14040e0782c0039450122401c00720012010440c540b52042402c80b5410f440200800c180f030b03941d031728403031a035156071203114202c08034017640c82080401c0007055041d540e1010726201c051041d0b14401001051791002d02080540000202003c6140d076181c00b01035601081a005403036141c0e0700703801000620b525090880001d0900e501281040008082e45103102807111050001c544000d60240702c0600101c02c5a00401002c101081c000190b040a41d01d1108 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 810671510 1250 810670260 810670303
    0x3030e190318030c1203110d0905010207081c142a0d1e0503090307050304090c09080115350a060509160603150504380a120204020c1009150c02 63
    0x20107484080124103c2c001c01d20441c0284800554000c0b1000c0403072b0000e13000c454409890342001620b81250b50545071219616180c1c0c4000d03070b031098000c1020540c01d04241d61a10121507080007a41445485002e0b210405011413a07111004000b01604244546814488003503c40c4802da4018900c454440c2048808030210380c20800520407180325641c80790890b82d44942d110b007500c0240c070038541242c3c007151110030000b91b220818003410402c0c00800ca514111340c1e00f054142c0d03002500300c3c4040580711001001c0162612400941c03100e03c0340300c02005084880451403c8401c0d10802004280c0f00d0308000b60300c00005002e44540020360b0003c0c20081601d4201c0c7c602d6801101d4680e01440e030080c10030942d00c0c4060041c4002d030094910340210307000e0401c9000c070760380c000c5a2008001604113985c03000400134207aa401616070034034130040000d494495101c81c0a498145418024050185e4038403ca408011130442720303c040b000c81a07801c1c40100d0041001948070010350301541314000c3c849 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 810672760 1250 810671510 810671513
    0x608092404111915080712050c0927060102070f030803130803070507140601051c0f06020f1c0501150e03010e01110c060f04050c010c03030e190318030c12 68
    0x103a849000d04000e880100301c203a002e0f00300030036040c00d0f104c0c08480070420718424401c0381c450f0b4401e070300c1390842d13440301e250039103450380e00388014940240389110443c42400b01c07202580e6646035840d103100f4269100901414140b00082c040a4003528860640d400070000b0400a030082458400f200d800000507610b9070350700d2024006090100304001c00b5080004204414030790414080c10038240a420b681d0343c840c01909200342e0304c1e2005c2c041c80d58028000d100c96001d501c000d15080c414180310317810f110380314141507485400341c2c0c00c003540206050002040d03102845055015480b0040d0f91498184415450b0035030a552070102842d45030104449541110010780b0700350400c1032040d80080081003241c00415004803103400c4902e07650218000d0002151380ca00700300507154016074120000d0322100700703400015580e004500c031007101450b03140d8000e0982940180103500080744603800401d94160b05e0b1034024000004546102c4203030783e403514280046804c0c080400283c9081008644058129 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 810674010 1250 810672760 810672773
    0x29063007050d060603050c09010b1e09030a050c030d0201151211030706050a0e03010b1c03111b010305011d152d03070e010e06013005010608092404 65
    0x1207800031a00040303940c10140030004070740c0c040000c4a0140095503007801800301001400e131310a10810384500c0b414840f100c40c00f2030403480c200126100c1ea0b42d03640f0b0b001814000c0ae041402c141070076106a041702c6c0c40c0d4541c130708052002d1400da0f0f02030310080103000c401c0f40000c880324911b4000c44104030848941c100800c03a4500c0646504d0000404072503846540d00c6c00100740350704c0302003400001034009103c004113090500500d0b240d100002c110004101100ca080344141c11340c01d40a03010410350b2030806125034414820101081c010041121481213408009000d840b01070344452146110250310080b690380d031740300b02031b00859596100d08550034170400050181e040c0000550807188891056152003040b281804103255050b400c0d41d10342039684e20442c01c0e18174240314000f14443d4580003d02c49611031000c004420300070007038034100e048503030042000020a28100b0245140e840b4018400f158004c100c8580c4004c0010091600800031800005c49201e603d02a015204007a0b0114080014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 810675260 1250 810674010 810674023
    0x7260711060412090f06022a0d05030901020c18060d030207150503060f0f090c0d060308030c1b010c09030f060609021306180605031909290630 63
    0x520104440840c201420410200100e1042c00c0002c20b44c0c5000005003080141049021107209401511000ca10b2108400c500b0215581e21204118041000d03491969940600e9440901031001035880c3c422900001e454109000503541c402c01000d408007402c13030740c1083d006500c0b00090b1154100f010640c80c003a80303400a65080250070765001c09881c005258480040c511900741200c0e28000d109403402400003114414200680109448000805400d02000205410081d2070400600166a901c3c0c0e02055041a20000e070080f500040030b0001c1141c6070b141c000e40d60201740007045502d2079940060030403075080c80010001c040e41c00000050081e240d000f00c00522605105554030000166101c001d03280c1030007950046089000c2402141c40c13a081c5100540b0441e131030385451a141c1c0048a80814410102170101d10344034511517001840c1c0c0021101c0c00300c14072142e14001182c030304000307803031480050a481c02240745580f519045020301001034500c00044103806460040408140e04081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 810676510 1250 810675260 810675287
    0x210d0f0e01020a110c04060b04170c0301140a0b030f0303070e030703061503020a0b0906071103013c0b180402033f03070e090c0d0e0c09072607 63
    0x51001ca00c1550312504071303c4441502a0070400c5e558000700120412049a0b09401119074455003400b062290b248182d5408050240d070408039072406409d60006401e46c1d102e280c1640c4101340754024402c0c02c1e1502d00881203a294210003800100f681011100e9803404014251010050300c21210300842d1001d102280180d600b00800307106080d01c4074400c103038403112880300700d010744141c10000414010311030669a100c84024661441c29443d5100c803032011044404070340d819581c54051042d40c1c5582c1703c6004511003036407510305840d0200043e2040707401d26808042511b07030400801d151700d0342c1c405244001000300329100480355100c074004a86050301e41c50001c841b12034101032070b900d26014103240907000c400e0009214000781454401c49040d0205481c0c4801040c201ca10246940c50005a42503000c0f4603140b149081c03074000c0300d514058607802e8140721096080b982c00c00c20f66081404000e5808906410035161580e4203249095071401e880200151584c1c83c00081a5001e118032040660308 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 810677760 1250 810676510 810676513
    0x60705030c01020a021e0d0c1a070306050a060201140a1109031b031e0307060903030b03030a030e150423070e040501050906100f1a07140609210d0f0e 66
    0x405080e071100d4000c0d03221607041c001610904408020040c110104280e45501d00c1000c1c2a07070348079031001920761040d4420215078001298288442040c1c2c68440e4500c140520754012a043c0c4c0b9200a0205080303050f04100d046905102584040c500011072080c1c02003000a000034190f03010454800740c0740948410b40350304d40642400c00030700b42c00f002c2085c2e4074134204900f036030310b0040d034501030301000e6001c1c000000c103c0c0c100344041008513910340c4c0a004040c0c02810040341d141d403007400090844e800384610303001103541d0301507030140f80c07008020111002c00c40020b410307000d0600d5258030115042d60701580d0b01c0700c0100b04612038051814420300000b0b0821881c112180e0501e4580700f8041c1c4803c56980080d42b0400700001d40d136144111148045801610180700c100d428401418081881c91b1000c004400b030401c101000690014445403a520a0401900c100d050031701c0400d0030400008a001580c1140101143c2d59080c00000c076010f007850880c0000d04110458103100c0a001c1900142825 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 810679010 1250 810677760 810677767
    0x9121806071212051b0c01150803130e100b0f120a020301031406010e0a0c0201231605190e03101a04060617070e131b0e01050a021b06070503 62
    0x1001802c658802011030340e41c848820b46451210303d20101ca0f800c584a803442010701d4411103914034040c0040007021042d034008500c1300d460404d5031300391400d180d0003880309600000d480510000b00404850140910780815859410100e64075422941203000c1c0b205200c3e400510702030000303200000c5a040d8115900000081c0c90a500190025002480b0607138954580c00b000c5c1e0034000d8042812416510100e454010a40704d4020b100d009001c54000202950350343da1a5804503201071150f00070b119840c2d9800002850901240300607100c100300b510082c0001408141d40e44100070644100c51070380c6103082520810b000002a1809000d0421280054907120410300412070721686038128060654043c0300060340c4850440300c9101d4030007440000e08001010a580c2440362041c540201002040d0310500c07007015190204580150602041e85100e602e21803003115000210200000d00c2420100e007030103520300002e911034188550f100f814038001d0400ca1800e075200e20513681c02e0358124048945 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 810680260 1250 810679010 810679013
    0xc0307051c0f0e06040312020f040302060f0c010605370905073906050924010302013b060d150503070e06030d080c09040207030e13050912180607 64
    0xb000d044218250441c10550740882c80c4200007039007030040e641a9074020f1008040c0d801b5100070b40000440a208010030000040542d0f10407003c0d001d10209088051b80c0c40c6001a40d00d800c56035580e025030b00814202c03d0020040803410300380c203d5a01c0d030452482c00e00d130100d02c41403280e142c141c01500d400341c505030501402d254003041189042401074058003080c22020750403030300d41c40d0a281d0406e0000242032401c00182e210b4202c95000840d020840350000344c1988c0c010707070840740c482c2400e4484001780700400656902410007142900800e40d0061f12414030010303109400700300c044800501c6c0f80d0b4841f05c109501c1c0c0004440c1c9640803080100009400c41212221205140c030a041c0b082c0b0908401103004400d80708058045c10000380100401c422100c0c0640c1d102100030808100700c1410b00c11541140c8460000f48441c2c0e2180e40e0b415040c08800007001f04401c292102001007174905000c01040c0580000e40c00b40000640a5032500d0701c0310510b050440001d031009994110300003107003840 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 810681510 1250 810680260 810680317
    0xf090908071a18010b1c08071a0f07030b130213050901090e01050a0b03031605070b04090501031406040b0718030510060807080f0709020a12060608090d0806090c030705 74
    0xa000e02142403101400500342c010013400d03912600821540644582c2032246000340440310620030910800e05141082c03815111000441d441b49080c1c49070407252810048416115400d4652011507418104000c0102d00082840b4101002103c2d50095002660f01c42c5035055045034001404002c1c514481d56840d40c11103006016101e240d11140c0d0300b04800300e00718214034001c007000b13808043c0003141055400c050101c151311850320103030f4480c041c0000201c1c075458550000d2020b8802900d000c2202e500d9403404c90007041a14801c001540c01c11824480041e008809070390b006080c40c58203480030b058108103105601c01c50340c401010780c480c144d4030304a217040d5500a00115400c9105842c2c107955a058083d4170303540f6144400f4615044014140312a590580c040c10600d41c0c5481c104600180707443c6e034502119a59080301c00403650031400c200c54007101b000f0b031282500b00b5240080c06810500f01090800f0005002d04920400200010315218465002d8415881e40e912400c125140919481d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 810682760 1250 810681510 810681563
    0x10b0a111504031d090402030604030f120905010c120b1806040e0102070f020a050607080d15030f0b04171305060c0f0d0e0102062815050a0b04140306010f09090807 72
    0x2c1079030196108080c4445c1c94001c141c184160380250140c0940c0e81c035039030221402240c040e414800d2080103d4416100c200314852681100e108600008100311058000b0b03100075050301c1e0321041c090400041103040d071504100d060340100d81e003210385980e8441400040c050940880401000e610100d808400c0c0169414200380d20350003641c0800c1d0071a03c440500a403403003140700242044c882003104560001690b8011207010217208007185110b40c580d80d652800a0855400b6261000f402046c0b105100210700c2d0318140c90b640107801481c1c9040561780c1000d038002841207138410f000c00310303000c0c21009080c481300b14940690415100c00380741d1840050302c49044149010700511030b4000241c10110b1424500f4101c09254217510070b14142010b10034007412a2000300003440307183d2000010240c49100d00c2c1c0002d000c0c0d03e20640d440704d090180c03030618080e0310801d6901c80d0740300c0b10040000350b40c40c010308003d551424202103052041402c1805217446054002448420742d131082190712481c1d85001d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 810684010 1250 810682760 810682787
    0x1e13061103090a0f11100522060212180d1202120901120b060d060b1207020607050405040b010c05010f1a0307050a0e130c060e0f0102010c1d03100606020c0117010b0a11150403 77
    0x11081364051005401d201c08c00c05000315005640141c0301180e00e448608064030710030410355928565004888042090009504c00840c0c85c014120050f00a880e011304c0300b0030041041080d4141805c1c1894002060300c6444181303205041d42e60f45010b0915201e200c2218000d107684e20003401030550300d000f1072149a00010012110240c00c1c0086070007203202061860155910781c1c0c9050609003041c1c1044001d06030005074a042c001d461050a000940c00c0c05410340324024401c000803000b030a403006943d02c6c03e01c9892948250400c0c1010302172036848500c650305a03000c569000301550748012020072100042c10000d051050641d0000031840c0d8001c1d4000c2203603c054032442890442d940040e0300780c500744205c100c0413442c000419454601c4c422100c20320b00000904070303406043c10004440495209401c1500107800440701a0860750700702c98800b05415440c1401e0003a136141c103401031142d004400402040000d5084e048003205010414006422203803408085207003000d01c0c000e00b00d20540c800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 810685260 1250 810684010 810684037
    0x8070f080c0c0721140a1110031e06060912050a261204060c051204110103110d06080705010504081c050405180601140717031e13061103090a0f111005 66
    0x17041e0343d03c080040b038030307260459105c11417198a440b482e0801039100341f07020302030b010140c0d15042d00120429140030200d49051080d80041c2150a200c00108208030903080101c50804003103082000401c00501500f42c190480400040c03071144030904290441d50080c02d0712107500200f064014110013204540c01188510810091403403106016556400b400c0c4030b8500000000c800070300410030070402c1890340013051400060500803041c02e04903607088808004580380d40d6400900c20b203030040001e440507110074206241040d1030301440950702c00c6450740904003054100e110b0181d0030f0046003982d0142000615020020460800c800a40706007100d0b0b0500082c5441d80c44180021080d0895800d0383d0442100c3c2c62445a80c0200d10440c0e001074805041e80004840c0380450407441da50150292110440c640d0311240e03581420340540e040c2c4420140b0f5007178208180300d07540d50b0005514541a030300055014102129007070001119103484003803030b0000e1401d44070324455503008006101028942d0b4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 810686510 1250 810685260 810685283
    0xf0308070f0921020103020f0d090b010b0c030a030b0d020a06030b040501090c0509060915071a1f050d0f050d050403020307120305030609041506030b0708070f080c0c0721 75
    0x4200c40c1081c00d407080e5400d07403109490034143d141d000d43c003003d4098010304000d4500820b80ea2110002e50240180003040c0356690900c0c1c3c10440c0410510f030061801c600d10500717180e00e10385d00c0740d200d10070b40d40701609150751920314040d9910349541004090340c0081040420b2641d43c48d014001d010040c820911a5251030004034000403640304020300c0031016559242806428002c1c805950300c40c01c0e8099103e8a0010421480d1003941d000b005190701c9041c2600310544c440400c2048040043e0a01404520400d400168401c403a00214100c60048500001030045810003940311032441c003015045008413a207100200341c001c4004d000700c9100380c0490751402e80d6209072910055400c20000c0004200304041002c43c9484815035401900494125040090301d101c602d04481c0e05910450302d20102e502040026504100d2090f4050f1007400c00c00d00001c0001f4008048400051000703140d00004514034441e1581046501c001e003148070440c0308050140710030b1140741e10b4400790484d0320345a544e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 810687760 1250 810686510 810686537
    0xd0504060510150e0102030f0a02030903071d0c07020f030a030207050a0e1b0903100f060609120b0a0518070b0c0f1c0c210309020a05030a11040b0d0f030807 69
    0x182190101d401d2030078803c0000c0c3d5540411036401d004034000d85e04502c001c0c0074180610001d00c0050103240802d4004640e6003102d00c0c1810f0070461342f07030b0000700903e4081c0345504428440c0a00c2640c05003003507000564450307040c0f0000300e584410f503000c107415100c0c2402c12000c2507000260b110a841c02120549062507a40039030200541088070f2030049103075211117000c42c540000d000341041003001010340303200d07219003040102116418100c0394640b9803104802c00c64584c0055410000e0100000c52381e0b020411600c2e030294498000d00031904040d602c5c400982800d031151048580d000320b4500f65071100d5a03a0803600c510390860004c04030340f030182e40655500d4880001355170081c000844030345400b00c240036000780c484107001c81e41610028884c1200500d81540f1800e0080c007090152030009802d500c900600c59800f0b102d4004038001d510560054022032000d21070b4019841c41201c010820515400110f840c1c0c6540780002040c6404c07050410040581143c401031040e0f03995a611112444070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 810689010 1250 810687760 810687781
    0x150602100902031903090b030c031f121b08010c02010f0b0118060f020102190f020f06060303090607050319050a02160f1e080f010e07051e100e03030d05040605 70
    0x4000083d4140e02204106014464541d50212444c4c080c1c01d202401a650702d405000030381c4100c90851000000200704145c20504c1113001e8003096004132003413102402c185c0044c0c0158441c400141640021716454420852a0383c03815000c0c2c00072400900514409042c003034041d22040d0a825003036030030311810801d154440c540c48021140c0c030b06400c8501c2480c02500b5241405060312460441d5020480c4040c0e41704410b90040c04c0c1d540c1950f6440d034042074150300905040f20040d801c0306540101e02441010758001054a0400100b01c0721aa42c0d6402e03450b15628511a048404114490034411081c2c15a080710161111030074a03000c0d60700808501030001080c0f6910300800c0543c100a80c01408070b003144946402c0c03448104c0590501c126125010540740c0000a9035003500c6079100d03e01c08282c80e405005d068000d0806960303258606103000800e490708440101050300811820020707031711041c80b420051503112800b0301076a031f0b902100c0b138040000c0e00040b0b50a8070403e0821012800001c003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 810690260 1250 810689010 810689021
    0x703030e040b0906010f050c15041119090b0111010c0504031514040f060f0e0c030714090402100c06050c0306040e0a0f0605070c080309010c0201202b15060210 70
    0x2002485410f29946050042d28088500b00990040040500080f032588104000034030120005e1504a250f514151a101a11004210880e030041c8001400d100f4048440034001055451104011400c0c21010300106c07840280c00d8214403166003007084000d52184c004000f0700580f4065402031408178a8041c250041e40d002810111444000000113004558890b40307802d440c52107900f000c280e00c580300302004c041d112a482031180b50b070090f2641e14100c0c5400c04c4a2001040c441c4860320b0700042520014600102c010301c081c0c0103402c15941c994a242c41102013a00c2d05e544480c04100e1400c1c84132180045410480344107002d28600410200d0020001810f0030b0026800000541c0c01e150a5645901810018050720300307000d9103500b02d600056021300a144146500f4000195503110014002d003955600c8440c021b1400d44a403528000008900c1210072154282c0440d02c03084c0f03004988980c82144e02c042c144c102c98504440301103a20110444c007070440d0310315400c0310084401c940255040701c1c0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 810691510 1250 810690260 810690281
    0x323041b06260601140a0801090f0c020a0f0203010e100c031404020913021201060b030406060510050f0715320705042c0705121501090608190e0703030e04 68
    0x8140000307005080c0c002d1203298045418901080d00881109001d034064219140d50004110780328018020b683c2c4038843d1492111100c0d900f0300a4130030200b00a911034210120240500c0c40144030364065440940245900482c083c04075984442c0413091b1400800101f0021400642009806080800c0050440d0b000e603030010884c07001a00c0b032207c100c4040881c41401c0f41c2084000110301e00310442031240900600c03a440000c0c6d82c078645468281c00300c49503604403d02c100c2c1005030500c2e01603403081c1035800c0803a450340c230701342d40d540b503801e0041011380c000e0040c0c1e4100341440800400c03d40000f400b4110700e807000703144208003074088491200e014000c490480001d0700c284004c00c550703150396800c6080c0020350704d5809111752820112810100048420b880441c1001400040c1e00c0d08401083d070740500b04c1562842c0359002d01000800108051040c1c1c0d04001c1e0810105003414003c2007981110491480c0c1046504040c840e1170382ca41e81c1c1444281c1c0802c8841160a1050825020f400e8284 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 810692760 1250 810691510 810691547
    0xc050d1a0a0603051207061b05071707050a2405150118050301050a0204031b0e0402040504031709010606020706020f0c0103180f0804051f0801060323041b06 69
    0x5529a0303101a005500528900c1e8054590300c0010100f4000e000c01102d210b5600411542c0c1c0c03005081440a036840e81a00c2c010001c840c240e0308510645c000295080140d2242400c1d0b01c50303800e1040c2507041d015510700a012070051a0071030080020011807280018030f0400c03c07100c00701c80c00012604550b003ca6046d41114141004507035190700c02d51004048182e18411500034a407210082403c5482c112108501154002814400d00001017110020110b141914991980c14203002c21071469020340300a00998650300400c0806015440c0b041202c04000385d14110b519182000e84d0123072985100c2e20015009404002c6409031000c03582481d482040c04c010841010000d0044000304811460505528200d54000001070442c2e40080030303060080124585035400c003410004810400481b42e0307440c135445102124a141c011101341d0450b42e00741400507011804a03480c00ca4220301521103502c80c100e8004100820900c150303140d040c10b0240748603440140c1c507414180c92890304c190841d2642e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 810694010 1250 810692760 810692783
    0x6011517010e04060b0102032d0d0218150f0a20030a031a04060b07150b03030301030c0504060605070b0402042706060e0912180102011b02010c080a051911120f040c050d 74
    0x14a4030144902700b14490900341d0b01d20300780c5401c142c2e00c02ca03009000702c1380c16031107108a03000c0c1c0c0d40f0b01120b00011200c0c030b503600700740341c210b500401c400248502070703c44003841101c080030008104c81d00742c04088500c818054a42d148500f000040050003050044081040c0d0451580c01e03a05140c45110140c51000000782d15090003074885000c5020140301110003241c440c0c2040e081510240082c40c021842880114034003801c140400c1306440d0075820030020400240008008107000c000226006030301500c0c0001c4c400c0007541c204041004203d140b666865a098200081080b1342c0c3c0500100d0f420940103008640b9038007896611044840c80c031003951001880100b16003401c6c01440c041c1108140000103a1441406000205241daa4025000b603555200a01042c2c0d0308005a60740c4801240340401003481c142240001ca904e404900c140c85590343c014000c2a05000c00480e024466546981c503072502d4515141c140c250001c68003180c00880c04000020981400e451000010b50700c001038911 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 810695260 1250 810694010 810694057
    0x4050d03050c0304031209030303050127091407060905030f0c101101200c1933090602040807080102030609061c0215130b0c06011517010e04060b010203 67
    0x90a400802c803601840c00200030002c005100620160302d00e60031a1941c51078286141009000c0301c50580c0840700b00b0710946018004940019101c000c140b490840000e02c142043c10115220350080b8403c5105101c0d0210125440d40c001720044116481201204c4054040020451300c522a440690f034000500c0c00300031005078091f00170081d0b42d0685c50000a4256580c1105940c049442c81e201c08034540e00042480c1411010700c400d044141c01240600e5481e00f083da035003003025484250a0710043d013600044100c01c442ea42c40520900c04803041400048031600741040254800d00c1204901d104111002880301d01c180290707481000000c103c04101d5448005000d05010300300010341c01e610b01e4080b104010f0351000c3c0c160030a0300c0c141001e25203400c1300300c07000415100c16402840c1e42d42803d00094070385c00310004a85064890a500c0d441821038400001c1e41d40003a00d0302004048100d06001259092440128500c52030040d8800d010480da6031005903200c1c0701d0b08240c600d00c1c188c05485080e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 810696510 1250 810695260 810695267
    0xb040f02040302153415051e2a1308060103030507060903090306091209140a18110f0d0f0908070b07021c080402180108061303020307080d0c031104050d03 68
    0x368140d289005141140d490524020082c9420506801c032580b100c2107205004600c6c0d61a1011404030004000d2801c200d146000711090401540502801540015407030310241414401c40700e0001d00c264060340020508010680c105891020038412242c0c40055000030005039541200d07010303240c0790324084450300c0b1140a00b0a034081901817100c3e81c2c40010021b2070b01d208043c20540902080c480c00f10194000802e030506680c440c04042149004180310343c0e4400300756408079000e030381030400e00c2d800b0480301d0b6000c1c2801d42d44c9400c10020100f540c1811807004001004400d0040008021042d01d034400f103422200310000142200c40f05001e000001851400125001420742c0102ca20036800016803581d0402070a204100158050050208500340b105060849101184040c519581806009580c034074004040d002003003804003503d800c1c1402402110f00311508070400701d42c2c0e580c1c101c0c004000b90940c07100c28000270b0300d09410440c44002c05020f603019900000e02000149080d510202c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 810697760 1250 810696510 810696517
    0x102040b0304110f0904080904110a1b1b0b0304060606030c0903321f0e0c10091a0c1b060d09061404050715020303090a0209070c060608010b040f0204030215 69
    0x3a4228100c0121440d541c1da1700d103101c80c0b1840c030a4003195600c0b0716800900c4141c030220344c6a95452a802d1290246007900031164648021354051540100c040324107144064942c980c00070030390740c0d410101c0480c0c4181a80001c620a078060003042c41003d17a071f81400c03802c13244825542d800081c03000f8404e00000300c002c5103084420003940c040300281a210010f501d11041015882c46880e880403400d40c0d1810001030308419812032410041103107120007555140c4544001e85428490307c00a6070300c44816014001c000054009840e90402c0c0020f564a52140755009d546040110720684035490342111080c6261200d0070780150070710381843c00c9100d098000c2c00f0203007002c6880940380c034545403420905c40d000c0d074891030060005000c0107281c00341c201c124540d05003030756086400820410500c141d000501c42541581078031288041d03514000d04a0b518010000c00030416070801e400024442415002a460346800701c804010021101908000700c0c8111b2000a4002d030011542c40141503c40024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 810699010 1250 810697760 810697793
    0xf0c0c0b181011010b0a18020901050f03161d0d06050a0603051510170a08030601030f090f02030705060421030e09160806040b0d0f0c080a08040312020102040b0304 72
    0x84030006800d05001842e00e2602074840b0000844107000c80381411001d008031001884140c132803610032414505402100748034424400141500065084c9007079105400300c0b010400d80c0f1440e10380301e05210718240d4290110700800e000040e0340301e540d1128445259140c1054641c001c3c5140031390b08903130303071800003030a402004a08909e0740c4e00304c000081101400840d8000550034000c0c0701920f82040345000c0303146242c20030404440b0540c10b40d2641c2c08006084100300d50441e03c55a00ca603101d0004078060141a001410741d182000c002c0d808010b00c10000d407400a03c00c409541c009600c1c1e1040c42054001c500c1030018440c016503414081103442585085194003903c0c042103004461004524610001d544054810248030504200e15a11503038a070f4000078200c0c0c1c10303c01000b5801c00034100c841f400c100680001900748a007010403240e42e0041e0000c0420034141d0746001c070305040031021a0018803054904011074003ca6503183c2c41842280c003501c0c2106469401c640b02c503100c143d10700300080c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 810700260 1250 810699010 810699037
    0xc050a0519021c02150106210b0604030c03060b030c1e0405040519080a02060106260a0929090d0207030f06060f0b031501020708060106120605060d020306010f0c0c0b 73
    0x40a018a441010300e4940318041e034000700211140a5400602844140c0c0030747c0070454900c8819000e4801c088081044010b41c40300131801d24519000140e091241d136100422040030f030100042006515000b0702c08080c82181030304c42c09a50501030001144c45c3c00d540640050050800541034a055480240c025005104481117025034003120405046621820b990b54100810050201941004024058100c61400d03010303403030041c2d5203a8140030088000d141900b131944000782c1c0510607640502d5100b41c1003440802c0003035403103d076800528400071140340300078070300b00004640010018403584040000d40c001c2060500c4e50f210b042e150440d90300101c030455242d00340040c20030043c0481d20050401d8815490392410081803040d0a5141c0c15007c40c155001072508004580c0c0224056046941f242441d001603a4440b0007074000b40055000241e02800219890003010559405184203000c03c0c3ca4000c1d4904e11b1090035078401007180001007502400010038095007070404090613040c1c40030003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 810701510 1250 810700260 810700273
    0x30914090f160309083705310b030126280c150807110607030b03030f071b05030f0712020406050d03120f060f051509031b040c050a051902 61
    0x90b242041a407084450051002ea003161115212200c980003059000859280200020001402400600440200c51230612030315921540564004042454107506002024a6103440d54400703000c03a00300b8040c280c0300350003061607401008441c0040d2032040c8510401801d040c2c2710203060040764210700201c2c84d501696400c60310300141500580741c01810352007a070807180700d9401030024210300009185008102e0b0314000c020240c400403442c04d411810a1501041c0314080e400803d1a41c8602104d09150000c0090440c00303001c0c1213641e05490b0740340ca04160080c0e07560740c01056554141a001b02e5a00d4201c0340041080c0c6041120740030b0341e40e20107400070400c1c590b510f0000e8074842460506170003040d8040d00c03034103c2c01d40921402070804900b400c01c0020b10300300020601c40e814140210340c010805484142109482c100c00c0c0c0d00c40c05001000c448021030000c0b099400005400350f0301d40240d0908502c800364a00034400d48206a0700366032240e00f0030388480f040d1a01e14511904900a5000301c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 810702760 1250 810701510 810701513
    0x3020703150b1c060b0d02090f06011b030504050909010c050d0b0118030f03030e0f0705090a06260f0a02060d0218060409020a0905090103170c0316030914090f160309 73
    0x81000c1022666041c1c80846100700a003012401c0c1d50568282c04e00c00c40c6c58805100040c0d40740c0300d0701030f004501c1c04805091969440c0060700c041c4014580e108400c0740c40c0550344101940701c0018010b455040c6c40d08034658031944030355400c0c4e9044401401c04510700744050009942203900c1907080030014540031071a0f03407980c1c10480c0c181ca0941c01c00c2c2c421140d00800d200c24035405003d0303071000404a000030503107810b041c816581c41d654035008040c80b030b0000c5004103990742032a4118001400700c50f41210b0003038091120200c000c082c0c1d11041a2540074401110a400d9000300c0c0c00c0101d140c028000031b180c4154030103000000e51180300a03641b01c050b018100c40080e1100d4002d40080c2100140059a684c104180034080b91050303070186219108210046c030000d041e2480c0000c11000001d082c0741c036084540c0d94281140035642c0c401004108840f06401070652100f4504211042c1e201040018501d21050000c4490b04880941e2001a9880469480e9124011525204601d45000504480381e03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 810704010 1250 810702760 810702769
    0xb0301021605071e270609060602240601050d0e060f071202070503040b070318080d030b0603010b0405191e050a06020309030604020f01020709050109060e070215040807030c0506070206040606080a03020703150b 92
    0xc6d42c10030000c45964031001c0c0035090b01089210002c1086110154440061040901c400940144154100b00e40451082d118030701d20340140d065480d43c08140c1e00540360407601d03403443c48401c444a40c005625821174010001c400d00c00c40301d120350000099803030700b400d1500507906580801422802c20400c40d500306007908451540c80082c040c418060000d8003441000241039030004c4004078072070703101080100303e004103071001c407005c03520161007105d01801282c217060b041032401d03400204c0c8140382500300000c0314048041141652030869010b80b030103441d8081203a40c0e025450100341c040e07200c48007041c094900301c1020186000144103c4009a848010305d406884d8282d0042140c5500c502050101211300b0922a9010b6268402446611081200c1040e004030240c409045040001003001c14184513405051034190000119002e0741402400290356190856003540d140385031900c08030b80300c00b01166401750944c040d030040000038103540b1a00ca084801000344100310303945000c415165200d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 810705260 1250 810704010 810704021
    0xd03110d082a07060b0105041502030702040507030e0a0f05030d0c0801030203100908160206090607141b0307090e190f0b0a0b090406020703030b0301021605071e27 72
    0x1541e40c014a6082a4280765080b092030b00c00d60b000072124180b0201110040015203ca46422681c0803810280303400c0140d95500c201c2d08001c4c1780d00752000c10a0b00440d00000204a1140300340d6040009a0b10410b04408680031006c040c002c98001100140201312405480300c82076019030181e038642203494401c01c0403503180749000000b1a104200410a6281c24040981d0041c0300880603c8240880d64800400f449190b892510380e004c030240340000d6444034003e8482000c005481640d4495041c1403d01d6144000d122440c43e41c41801c4e03d090000c11000c00790b01e48544050003c0800b2411301c4961300c050500c008401a46203d1008020340d40291202c500782c42c18002c0400114840b41400c294070703070603001400c052000342845d10310007841d12083c8240d07a009411002c0161581a585000c0b0040e20a42e4080365040d070003c90202c001c0a41c901c012000c0e54420000c03116020707039a050f4005242c0e544120f01040c08030b90042017000b1022011004916030400344d007070040004d04104002140e5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 810706510 1250 810705260 810705283
    0xe030118051204080606090901140f01031b260f0106150809061015020109020a141002060903180a180204090e0c130b061303050102031012110d0311 65
    0x20312032051141402800d001002100d5040415540703010f084c50340c0103558000c0a0280b9020304401d60005a04000a60005007800101030803140542440c0c041c46000c003d00f80001c0d00c0d081d40c8180c070b0002092548a8900c1211038009224400114040600c0000c406192001d940b90142c0310124030800020b219020103803680501101030500324580040020304028071505d1541e200d48244800308020345800790490704850700302c4c0c11003034000c14100e01510b001200250400c114820104440b080602841c0c011030080da68514203034449402281d0303a400560717000c0b074a60400c00036810200540b00709110f40f10000752045034507558460705000e108040c40c1d0040c01c01d603030102d0f080c80700b0b6030580100c140c0c1e5038403040208200184000080c0091200845414200c1c0c2d4078805d41c4042d031201001d0300c101240c00380c0c00400e52039490400340c1c040d52040315032401405101201140e061a50706c90541c4150700401c101303003640d00780c505000c08290405416424800d96a41c0e206c61800108a0801d00c0c9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 810707760 1250 810706510 810706541
    0x7050d060509040521040621020408011d1902010903020f0a030c09020901030b013b03010c21020a05030c0703090302040c0e031606021f020f0c2406060904020a0e0301 73
    0x10410361054940d80ca0250505c603140001000104100c5902c40000c82048607604800010400809583c3c0020b2049034003103407031542400c401800001c0c2141c080500b98008105844001d1840ca00035110341c0003040300240818000041400541400c109800c407050002c0e100f17002647d2682c0b139001c048007059000b410b5646e000219041d07d5603160140c507140a0080c2170810402c01c448031800300418480c4c048501b03005c00e40c01034121040c091104a01424400f400800c945180313000001d041e9060000145035400c43d00d2842214031840c1c1c42120710030603440e83c4041c01d5460790150046a40c0c00b83c10103130200314580001001607030f035900c524503034503110703464000c071080000c0c1c18103040c01c2d09038040a1807c0c0050b08100101c42e0081140d40d00c20044034105d00d03501a035034426000a000f10003030340c00c080310080351000600100040d0301c0700200242201c445080c0101c4d909200288040b80c855800c461b042c070554080c5d0400ba000f5082c03031081814040d0741da0b110f68022908541c102c48054007034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 810709010 1250 810707760 810707773
    0xd0804080904180c050d032a0c120c0e0106140c0a02040f0e10090312150806011203120509030d020d2301090b0f0303040314030d0c080105130b01020607050d0605090405 74
    0x4c02c000f51400b81c00421080c0c48000c0500c0d8252405001c0d0480c80f90f800c41034240e550248030000547c404540e01d0340f5407100000c044d10361160a40358402c640c041048400105c142d80c003203007650310f00300e1b0181200c00ca503591482d9039505840002d102d400c11a00440b061240529420059459015841c5102400000050b01c0c1d981003145e5440c02c84605181d84d5224644140348020990081c884021051444004901c0b40960600380c1c00c0e500d80d941c0614981d0003a100045100d528002d200c13616039020b0350724124107012040c01d50040383c2060701c200d45103900c00c102000c4044520b8002d04503c102c5500002210f02c40030031802001d4604240d60005501008010300104a040c800c0f02c56859069480070580701410000c40e541c0d20450001800c100c0a0324074206551404104641d03000c504500140012103101201500d255020b000382803280000520200100069109000200c001640100300503242d0340800e40b01d41d0300603546080340c50707124000450b0036180c65102a000f82d1160008161 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 810710260 1250 810709010 810709013
    0xd14100b0a061e0e0d02031c11060c03010509180105090d231204050705100c020f0f060a030b19120b0f0c070b07030902090f071403090d080408090418 66
    0x240344000e800c901c06101e055880342c9041110f8103104064041c032402c1440346142e50354005103404882d0600258980708003410100300401d255150010441d1540315240101c254a45464a4030011544401c141c41d0a00040000d40391a508558000301c015112844241c0703014030084c2980c0f811245100254495040e40350a554880700c0100c49405c850b1091121a14151380300289120f180c0380f0030b088950500206043c418248801801403400605000740041c8104c405409012000c100364440e502c0c00740c83d050607082000b60b100103440028079491402200c83c100354000c0c10800a07a940103280048480b0b00044003c54050240c840942e6800014089240c0396900b100004c082e80c01d0440f98000b8006020700e2a0165074031240c0c4402003510a5440040880007081c1c0c460020f544860000140464902501c00302401500580c5c0c508409410690344d44006100948507105554825400308805a10076450700c2c0c1c1052103016000d25100c1071000007000e45160045018100121141100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 810711510 1250 810710260 810710269
    0x905010303080708070206072111120a050a140406020a0c020a0f0f1e030807032a02031005060f0f062a0d11030f18030604050303011a0c06060d14100b 66
    0x1580524a84001c003041d1900f088009c18065080e012181003038458000203000c114150440d01746c1101310220240c40b00e00d016101540e5500c00c0c1c482c00b8190b45820301080061159005207056405141274452150319242d5170000258042c408810802480382c00d4000140d030345042d440006c001a0402d440c03568105013482a8402c210f901c0100c0075101c000e820281d000f2013045940c00c0360b0700700f1a2261507000c00d0a0940750740703c924980044460018020840c919604801141c0c40c3c1d0003036045030001c25041400c3d40c02c85009481e40756015000040102d0076141615803640482d40241c0460705100e40d403a400e10300140c807030b0112402100401a000e6214000300400700d8500350a28240504190140942e6213a02c00c810600e421001d00003101031141540200028000d0805022601c052070310b404c00d0f68898000303006829600700c41c0c84a0300300910203001601c0711401c042c40500041e4031144100b0503a0403403061b01b1260444240d407407120202c130178072503030000c00600200420066001310401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 810712760 1250 810711510 810711527
    0x5070201140412140f0708120f100b0c0f01020d050106171003030e0d020607030921080d020306010c050601230103110a08091c050d060b072a09050103030807 69
    0x50340044480c104070110b0b442c000f042034206110300300070381084944e44140d80c07140300d103103141101340b01c00003086c074200b00342030300280310381c140c00007521065480742e1000702603e80040c1c8041c09281c410076001e004000c898001008008000d07030031034008e0000300d4800b82c207980040e401c109081e5981c1d0010003000d6004105208001c0f1551034400e050300d044800040d0030034650201030100502c0a40d8a240e91300c50220b0405070580042015403603001c03514008080c0e0a6a018034844100c00003011400c415120742e2445009600c900c1d00c905001d00800d0310380081d000100b01c141082080000394000c540e060000c1800b800107000d51001c1e406590078001944151246800d0400d0f141007184601d03c80440f055940c0e00345145001e5815841c4d00018504e0108480464880200d07040c1040d45282d410500503c800a5102028001941d41c0c2030714078400e0285000281040c0e160441e00c00301d0b80c0c00880f00403800d10030030340c00d054425211040c0804440e400d070401c0700480c140070180200e2907008644e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 810714010 1250 810712760 810712781
    0x1e030106080105060d140114091b091003080708041e030606060e061219050a0f1505030303010b130b07060204180525030912350f090c0a060305070201 66
    0x1c1c800c605200000ca4070300303101305c0009440341d0207552442030f50320340a40158400605010500c1090700b08034403110744a0508000581c1c1042c0781c1c0ca642c4086040c00b9014a1203450810031400905156807110100d42c0c5c07080c4001c40d9480420480400c100341c1c11030098003055004125803110381c2c2149040b004403019504008180300308905020002c1c0e40340401c80b25134121080c012100380c0c480b000044c145002c00c01c3d65800d20703812b01081008000300c0780d014110059040c501480750640f05c25045500c16900c0c082d840c1c15410410040c484080400000c6c4a2809840e248180141e03460004000d20b4110b40380031101c858000804000480000e28202c25164002170100f0041c2130401001024001c1c1d94100001807a024854842544c040c0d0321404a5030303000006513000d8403102a0090044030103841c2c1c8030000c4ac6040c645c0181b100c51410000048900b6030955145032164422144075110041c43d44541c2d11030410a4019a200da51245006089680380485c490608000c0642510100c00a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 810715260 1250 810714010 810714013
    0x1c03020901020d090315022d0c15100915031406100902090a03021203090604141503040c060819180209090c01020303060f06070f0c09060f05030607031a1e03010608 72
    0x130a0001c150f520b02d00d00342c2c408030901c005a445190940742401300e943c01008441c0c1d5082d40c3d1440c044049450020000f842000f419a420480b07a00e440343c0010b1002c0d16003503441c403801c40c006d00201065503c2003110700c503010120100c4645d41c0c0d4440844024a104080864115009001c8940300b1903a03880e0181026500560070150305d0780100e01145602d20010f44a080b24036248480b0070818070440315141e5006d0310041c2d42d0303603c8428158264280201050103080882003503501125540c0130307240034560002000190a01c1c10300300701c17030400c4098030300343c0120030790110060304c10b003244100d0000341038074400201507400b40d00400001c0b010040070408582c10072060150240c0e401300407241c0c008012140c0d5200c4050050124010f401803ca009250700d040314000c005003c0030010007001c4074004602070000a480b088800402c04151140c142c15134070400204903040d000703811a9010700401880c3c66a0074061500050b86244801020f00c1e0201c1d45000300140790600303003d03030400f5010313000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 810716510 1250 810715260 810715277
    0x1f05040807110109050d06060e07020309011205040312060303231606091b0b1b031602010f1e0e03070b0c0601170a0609080a0f0f09171c03020901020d 66
    0x840c0c4203414464150010700c0c2c2035040e52000466030040011101600d0003030400b0700080d00b949840001000d003401b074280d0440d0440002810300e0300c000102d03580800d040c2e42c2c0720140030100d604075010f0600644106c0510284064880c4421280e110345002580640c1d2350b00001c15041024034419450200790b400000010004a000881c1c18205021915070041300001c1003181814000f00c0c103a00310f04881017070403400000003a1104840b000d00344214180300d60b02080c0c00400d01081e80c0c0e1054141512844903007000300000340d801410a00200d192500301402c402d420381003010341204024010402003003680740008400d0404108000180000d4071103d4508102c90000f50fa494105202d5108080011030582110841c140030300f8503101e0f44031390180900c000d249440851500f018161900064001c44401c41d16403203440d41c00d10400030758a80ca640da904003c10550b03642a080c54492152007145407045c025200030f0b019064a02156400685070010040024140b41d01e66010401304000c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 810717760 1250 810716510 810716513
    0x9110306040206040b0c030f0f04080607171302040f050906151206130c08030d1413021e12160305160803030c160204020a03090b0601090602030315040e0f1f0504 71
    0x500c04c980944200204181c0c80f04400c1c2005440e6100d108520b942414010500a465020060181c0107407a011007d8400541d14110121040d000c000e8104213044421030204140a004000c1100c91500242c40400c0781c08030402c1d5001900c409445140c1182c1c882000c01c1360070608400380d2441400101e07490b40c08106070802460f61403d024001d0540b510440702c10342c04110842d01030800a24440c5c068075192100341074080020110000c18032008140341c400601c078003070118440a031059004000082c06146030740403d45000480d940703141c001e2005040030908000c00c008240540b030304180000d2440d804c500c0c00c50b06003481181c030802e40007903600090018040200075242e1150700300c5006900c902c00c0c0402e00150341c0340030070302039001440080c00041040e031540024012900a42598145803115801124201d040d44903e00040c1c005101088560080c07401150350780f10010404074000018002582c2008403e1400c40c00702d034003002d0014448421040c0d0540201d550407801c10852505 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 810719010 1250 810717760 810717769
    0x7020102160b060315070201021e0406051e0c0109060902030f2a180109051608071409030115080303071805150c10110a1106060604210b0406091103060402 68
    0x2481000b00b411446400184041c2ca042040e501c400c1d40f961500f29507814440000ba0003580b2000064520300c144904101104440008480848040c0e5a07004e24140d90440c1b00541480c5c5081401030103041001081c0784c41009001310503c00d4064400000c03c0f16092040600e8464044800d1946800040d00b80d041c0d50165568880c848922818190000145100059090300403a00c40306a20340507000106200006500643c0314400040010a250316000c40650305114202d9101300002c00402001d16a0200040038080d00030000d4000b18001005007d05071700703c42280c0001041341d1020041008450348202c03080410070200508007882d609007004560b4801c4404c401c090001000503081650050400c40d1394408903c6070810042c030443c12407038048590011018000080c111400d0610500002c507003103020f0720008001d20300d010718040000c40c100c0051060700d13084039001c56034034001c00d0030810178510591003207400040b001c0040c030b000e40d4880001e0f9510ba00aa20001c20080180c46 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 810720260 1250 810719010 810719047
    0x6050d0305030c220602210405010c060902030102070803040c090203060a06080618040c080106060e030705101e0e1e150c011830020a02090c2701020607020102 70
    0x105403a1141c1d681d0f8035800444058401e120b100c0d4840026030100d07a8a0348051841c0d01306907400c0f0760039136000160040d550150a040c600c0c0e601032039138082004010960240d207001d42c0c3c40e07204a4011440000a400207400ca1b04890b109981d04000001004104a04030341d18401801c0d103040c0440c25401d000001ca440c0b04c0d40c500a000c14800541d0104e0b03c640c0e01c02c0004400c2c0703028024110924607107860503140b85030452042c10844e60a00e0800305006025804540404070098002c0501c1c82c50301c0b0030055003c46400f0728030107010b10480e001c180031042c0444465684899218a04412418414840081c5600503480caa40e01a408400f51950345c40382140341100116044035124101180f1840c010130502c00b10420340340403000b16800300500305034041400c1c03070040720914103030407442c0000700c1c9440c000003c580141c101400c0100145055541da90300139148001d45801d041c0c9401d036101e00704804101c0081800d030503403080c4449682c100b007244c0d400b07141072000794244560304004460f28007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 810721510 1250 810720260 810720263
    0x160207050d02040b10031a030c150a18081605010c0b040605093309010912030905010f020309031201150e120a0501110d11040b0a081308040602150a06050d 68
    0x504a20301d210541d62a5000b2180c855001030406800360b00101c2c02500038400140d460280b60583c0300000e1030341c41e02041c0c51003007850140807607039101441d0186110660207134048000380050310380004402e8114040d00009000144c0c020444144402440000360751140d00c002d04005154010b41c0c00500700c90880c58200d90300040104182d102c2500d102d0504960031804061400c0b00f64012440c1502115001c40158403805100c2032034680c4112507003a200589806440074074031591001b0580c1c807a920510070140240700000d04520171705900f0082c1e1b130095900130550750000c00c4520b010b2000c141c540e80100007000c1008245220b460000d00700211414a941c402e03007813280c04158400e07080c007a15403520b9000300208a998030307005d4000e809030403100028522a2500701c4540354070404008075416620a8001281048a00c00c2c040320790f40c41c01440d04500b180e2000c4402c0c000780817071001e003000d40119000744c9480032003080c010000c807038020461100a81411030401c00c4d921034411160844c1e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 810722760 1250 810721510 810721519
    0x206090319030b01090e0c1c0e06070c06060e04030c12020f060a0f060305030f0403140a11040504110d1514011404090305120103120815101d0604080d0816020705 71
    0x200102c0058442c4100750348175100446d101010851a400408000c0503011052044201810340c2640d00310f00303c424818800201d5030000e0301003071200c0d0080384040481031103181c0100300680c5131090500300070000e540803404194800120000c1001e4588030340443c400901c020841011040741c0c60b0b43c3c490002d006088070b15510044400380c894607401c0100910b4100d800c4a0740c804002480c600164405d10007510905101e0040c10440d07038000c2141c1d21895046041e203042c0c01854005c0200a10014104030b84840c49115201055213555038034020b403034010300081c03e9440388222041c0070313164504000000c0c840c5090050000c0e624259031500500d4040d100040e800403c1d18050358548a031440c03841044081d0720001040040010405d840007416594542003900c82c1c0c0c209080101c000510598045c5081c0f10700800d55100314181411032098120454400580d00045a85a44503822a00709c17078016440403104a60000031682d0400700c811540120f0f080c40305c03002902da2541d40a00c0e8841d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 810724010 1250 810722760 810722771
    0x20d231510020f06010816060f08151f0305090105061203040b030408040825060f051c0b060d050604150f27020a08061e0a0b07020d080c0d020609031903 67
    0x1124400c103e40c01c0e0302150f9100302d90055071900e6110356120581690801100c81070000814505e1103400c4c2c0d108000c500f86c540440c691207800b6951403150402a5081c3c0202c3d1802e036140d154000f90942e18040441c945000a59081440d11a42514801400c50307000319406880d00410741c00000072901240c0290152a40707a0300e80c0d241c101042e1040303500c04040c5104403176a900006c200e45500d00d40c4010444910a051580c0c1c24013980e0010b12503004030003203a800e01010f01303650100d0429500316400c1c2007000450a1020f00020100d802000c00d10390090340e01d20401400381064407460b1103211707400481851980c6030101102e0304200341c2c0a400220b11a0302c0441085014011401c003191414640642d01c4500580e402031032501c0c100c400030b1051301420901a2407101804a50100c0d64000d0081190707213003000d00640350359001a1003241c1103182c0c111b04a0204100801400d01c1214141c0506100703005628001c0c502000509100300716002000a445c0b50b2034902c001e50740034019800c02160 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 810725260 1250 810724010 810724039
    0x6040621060f1e0f15080901060e1609050603010f03200603070c0f0c2709170c07090207110909030c0307031b061d0f011107020d0213020d2315 63
    0x80b00190b01031150403c01d80c8010441700f84d0000214550388640d0340d5a1070f26503410041c1401c1c3c8100780700b4070000c45c42c1c1001040181440d00c001d400da411103030800b01e0002d0368503408901c4987c0240d0049040c060551000c1c8108403a0102c640c40500070303a64a0282d020074100000d11390311001c2d1040050000b0104484100070b80002c11180c016044034007807040c41d5807104044810550801c0e0030421107600380351011029900e110300c001180d08400c1d06940d0034549100c01401e43d02003e6007140500c900c00000540c11138034001410340911820410040940060611845020142a0f202950014094416010400010f8802154262406040d001110201950603000184001d810301d403d1a1490310340b031001a900419001400d0111500d454250413000e088400b01d59030f0310b8a00104021003405071034144441d02489000a220024034001002c818080b40d101810003207105441d006400032025182100203450705103051081c5081c03800080e03c83d000710712901d220744101c03510f00b0802c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 810726510 1250 810725260 810725309
    0x609040c031a0402010809010c0210021b0105010f1e0b030c07020f0916022103010b0904060f121505061c06110703020a0203060124110a0206040621060f 67
    0x80040d60481918500c1d0509030300c890b484950201c81c01da0100b070251020400c1588148140c4400820603405454081d40400d007500c080d60200b26030348104078001030815418503081c81140d0081281e02c07100b000081c948030b90540c25080d1242002e142d000114020040f84040c4001c0b00e42c0700c0300b0240c0c03466442c5101d100184000138942c0078907400103920410051103540008020b100c00000360200d9807a0300364104048444004c40e04c0e6404021010320041024002c08405000400c0740240041401a15250710455440042d0f001c41c040d5070240d0402000c4c004c8100c1000703125110860203028030b01e00f850104201c045140710424000e0041041001444110350101c6441002600c8503a070b1481c141c10000c0d42c801e4002004e9100e40902000001c4131003001c690501c0261100181054849072030300c099840f40301e000312400c15401029141401a5100c10080018044640b6024880341e80d0804e144803046000c0742d009a00d034500748040c801101e245040030121100c00b21f1040741100c9904424 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 810727760 1250 810726510 810726533
    0x60504030f030c06180b0105040b06070618120203070b060102031312063c0515100e0a0b03011401020a020112020708120702030c0f06010509010b0f120a0204050f0d0209060904 77
    0x180480d40340c41805c5000011054051112500a124400d0166200c00402c02143c540c050087e511110030004140066410341000c000c0c480003d050608144d104d850b05200003095680500058100180030340400c040d84039002d41182081c402141049d010b039002400c401840c0c021004a090420b2020702003101603040f502d09030301c0548002d100b03c806079080011003905c4a25450032588502001e0020718082e20810303100310b0143c4036a0001c07040c00d00c18846541d1103095400e08000c03800c00035021070b803107400586c4020821010300c03903030340e44c540100d00d410b00c036404d05a0390464101009441c0541c0c0d001c03458000303d5444a00050361400b191030300e0946031080c1a40f00020384d8450003000380b00c94020003e000b9000890341624003034100b030701d419521038030700740642a40040040014000c180446010309903204068007142c4c80e222038602300422104046800c0841d5603000501400982403031349400300c460740b013954501c01141d03a950008401c10310040c0301601552000d400981806290711a8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 810729010 1250 810727760 810727763
    0x1213050316050f07091b0e090f1e0903030403030e0307031e26011509030c15201e03072d0803040506010e0c0930010c0915030501060504030f030c 64
    0x40b40d00d1135542e0840213000c0c182d5402c000c090340883c0f0903c602c5130360003420b14000e6148020013030207103940c4481d01c29802c8940a4a03131402c405107901040300c10078090a04c103000b0140d10b00119143c0c501481d0080646509074803046168100703111103000241c100600e00b2283c07110100d50030583c5024901198030300c420182c0910740744642e00c40b00c0005086c8240c080c0c10f0b0b803204401c00c02d158000113000e44036010607100060100c59509010000c4102543c6412200e424514040080c0500442d8514000321640c480c1c500780d070054a405c1c403260401c0b106c1344010f02c81c140003070f504100c81d070b80394806150340072012202c52070310b0311341d20b841c1c00f05d1451035000203aa4480c070119128103050800640c5da5600340106028407419501083d0320f981141c080d1050040002c200104000302e080c003844089094210902d03010a0002480031800420301890842061581e107489900f80707080000840080b030120081c041c1450040140700c15580035040341c2c10340e0740000b5070000c108007030302d822a0b00c0025240d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 810730260 1250 810729010 810729013
    0xb040b0d080301090e070b0f090609180a1407120e0307060c0908121801121104181a010917030c1002090f030c0a1701060302151213050316050f 63
    0x34208222181010b14140e46407032808000204802d000541d65010901a0029080342030102c40348a404002c01818900310141c02c1e20304007803101005c5804000408400040041130340104010000030703101d2081110507607228a2410b08201e0005813840e00380034420414691201d40454840c041002121030706540b0850402c03c200001100a1050180d4000c5801c81c5c0078281020780c030b841b50340040d94401040100b0000c0e00000b29401542c1e04002003070015007140d01c400b0030744804400c0c00041c100030141e40c40060302486041c4044011510188901c410300c040d408e211080b5641d210300c03c101030303038144042c030068030070a403949915500449071b50088a114610742a11050415000740001030400e859420010307480d40c04154591011401c120b0700a101448208808080c1000d501e05007408440006252900c1e0f40100b030174200031001c01010000e0020740000c0d14540c1c01072080e4400c0c02105880400d001c19910f407603e1344188440d100040c41900700c90814403900348403685071402400d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 810731510 1250 810730260 810730279
    0xc0a12080405060f09060f0a2309120c06040305091207030c030b01050303030f070503070c0206070b07080108030a090306020d06150e091b0708070c080d08160f02100b040b 75
    0x2440144034400450701140c560050380c011408002c1e030140503c0c00741e0000005818a90b685034840810000f0003411014881c0e294400c0304100c003080c2d40c11100c0ca108281c0b41102a2804000c413501d0a040261444014041007101c080140b50124089402580c5864142da030380c104100025451000f0582000080c01070040c0001000052004102101c4c0f2404400e03c090b1f80e1002003613102d01007199845201c0d84008006241603100f04010740d84100581401c004408094001c00c80641100c00100d9050320303e031003032155068211210f140185040c1004528042808070014400540c41c0720091590342c0100d1145001c0c00103400a001404140c02410340302101210020000221207084a01404050307001c1003403c10903110000c8641e03403452010345410480d81c1d0b03500032a406000251400354810b4404035130700805001c2c01c4104200740d61900c0303503410001da0202843c0700b00103582d424041d1180105220540200d021503610101c80c40c0000d010b524500482c019251900150303500002c42d8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 810732760 1250 810731510 810731543
    0x90d11091009050a11070222060902040504111e090a03060c02010c0305060a060e060310170f010c0507170d0906061203170609040f030e040f020702090a05010e010b0c0a 74
    0x15003020100c40d14901e083c015900c8402c00e0364101c6001003208944590108011800340c2499412000040d0148003001441065170105508440081d08048512600040d04004030701d041d00407110200e542410062038504245050b02902003800c000d80d00650011801c0c407102c5d9034948900e0001c54105105108038820200024000c001851160000c00d15100200d403850038111050f409440075900c403644024081002c208294000505451164000400c082512300c1114038060042c0c07a00c000405148907251a03182c00d546000720f040c000c22400344208808a10700c500368050842895400175692550020000090800301401030070342e41c1807400000f0740307041040c006000ca40c001d1b9605000500044c003807019096080d42c20661148a07607012a003c6001d1344007141d40c82e40b01e41030028000303d40d03c01042c2507909a44800034095070100c2e000c4190b007001c00100340d104c46100000c206641c10080380e8040d01d0011702400d0b2030b80c0c40105658961503801c2048039412500810003d8008188 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 810734010 1250 810732760 810732781
    0x9180605031522021003020d02070c030302280308010501271401200304051203120c0706050c031b0c031e04090e0f0a020f010c230c0a0b090d1109 64
    0x581d10380760140f8008100c62002c0007101c0280380c0183d802010b0742211500c1c88401c4010b504600100000d4590030400800060305a0000d803000707511940240c141203607a02130180b4101a140482580b0003054205440002e80c8103c03658152403003401d05440d03248a000c4550608030200e61070100c82c0c5c550349004180319914108100c070020090303072001d6203403a042c3c4084510344c00354a81c8450650080c0801e200701c0c82c041d0030a002c0203410a04503800c01404006030b840692058a580042d0720001403010244000e0b4007440e680107580140151450400611070100c1c811702510345201000003003004042a90b081c011030b503001c40c0d000f240b411080b4001c0303169040c0394010311501c032091b450300c8912510244040b4414041980030806840c43e80900d03001e001160902c0c40c40c450410140c1c441080c0000ca1a440e034048841c1488007400e000d258a00d01301e442c100048076500d21924014400700944480c80c800c8500461059540d005511041e00d8007060382281224401e034090f48001c10403244214 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 810735260 1250 810734010 810734053
    0xa050d0f021042061b0204090314030703050106020d080103030c0b071e020601050310060b1806040504020403110a21060f0e070617070f090e06010903051009060501080309010918060503 81
    0x140d0010f80d04182e914201550400388016155900c104042c0140b005480d0641c494170886004c0c0c108034100c5080d41c81803842c02d6204503039200c042641c0310010f0000c15030401517030121402c43d050031f03070055040d61030240c952010008000c04502428000500d10742c0300303182000e10410b02103d040c140190000010751660800d0107140e029108198200000c1d90050080900b16240c9540f120320b0b160000c107904418000c1213181c641c11190412001a55407198401003008500415045c0c05c0c1c1140d49041011050711035001030080f0044003a00388214521a0402c0e0744164400d00029105140b0800b00d0080c0c80c2c04c0c28450003501540000043d566040140303034241405200c079103040c5a40b0320009451a01640c0e07500400505a0300050241400403114241c0000c0141420f995984d9296901d034503041c0320510b094100303031720780c1000010803d00e03003c4c03e0301404451014600309815207000800031001c61180744042c3e41003801c0d101d0344a026134006070190001405649140900404412980c00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 810736510 1250 810735260 810735371
    0x5010f05031501032402090901030609020f0d0809010f030e070303050a080106050a020a0f0548130b011b050d120b0f0118170a050d0f0210 61
    0xba10503a00c00c0c41c2d05001066040e070341e015026058440006003d4000c3d42050050411065400c001410495440c101494000d520810012428030784600c1804444d00110f20418020011105c600740015000002d0315003402080c42e20a10400e0711160480c042c12107910002d0481c05480408024194013000500d4403d910b511900000e9a039000115943c3c46081803800040e0021407590000903000c0440c0084540a64103d80303250041c0703906240103410030391841c0341c1d4800718080b0004200701d10f0b20608480342000d0360b03440d01080d01004180300810f0710240c2070841381e40e2015072189070b00071210440b4032219210140c940c0f1001e4a403555582e01c0203440400070130041d40008858403114081e40203e1070001d009a4280019030005461050590a00c3e40a203604240007040700e012803002030303d16802e440000d0400885604005042100320744030700d01001070007840706411a800260015400188460000d600ba88005080765103442060b049100d981c0200030b035071441c5840c4022100ba13103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 810737760 1250 810736510 810736513
    0x20403020319110108280e0f15061c0804092a050a0315050d03181e030f032a02100206010810110412030c050d0311090f031005010f0503 60
    0x4049040e2007150031030024400801aa545544151042d44220003203500442110800c226419441841000c550364800555640030b5a48070000b20220381001074415608051014000402e509e92180c024501d0007002d0301d0140514a8000105515a2800001d500d4000300070503225621040340300e014150f0b60001115800b000300d00c5000c6070300c1d112030401000b80381d500c60f20b00d06100404280c010b00384184503c220a60001c43c001029101c0c43c040d42082c510980c0c40404110181100f2244810380350080c1d40320302c5c014411031044001c90010b00041d82d80000e4885801c4c40783d45812220724200001010042c10343c1d0031034048020111203ca5001e5108032004401c1c805802022a03a40c5000d1081542542c09600030350301d07412142d031212210074002d0f000140381940790041004020011a400c0b0005280c90b5048014054140700e81004c800061406000325400f40030305103601e0090b5440203208a0f0700f220b41443d160750420180d4483c2d1007540701401950b03907400c81440400701506c1014001d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 810739010 1250 810737760 810737773
    0x3010915050c09060d0b030c041806060b0405060726120406050603010c1209020d0b0705041a040503070b0313020d06020415020102271c050d26040201050306040207150204030203 78
    0x4280d034202c15901c1820f00500310900b0070310401c903940040e26940c0c0000e5094054000d081445861714000c110044807081000b95414140f07241034000c03107625601418900c0b82c140004d1285030b80d04402c5400d41d54021291803141d01d4014050354070707482c2a8909001800780002d2021043c43c0951001e4130990003240100f14907960307034050509a4151449010000d0340201c15100c617950b20303511100d03025002500c0d00c01c00d019690350350b240c0c1e400282c07003000116101103020051101e4034100440c4964808800500705407508000c65522500d0380a10840c4020100c0080d0942e403000130b0712400c85800130308002291071a030604000943c020302440c082852030005546040d8014000c0380c000020714462065824414034800d0848542c00c58034a07405464080c0025035041640380d00c04400d8001c101810a16103100030180c000c50b0361404099003440c0d050355460418403c800c032103501c0390b02802e0080d525030300c50000a000f1322a944006200d40c4024009107075020141d406001524030903030458a5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 810740260 1250 810739010 810739021
    0x3030d0204151b02010807050d11070b16090806040807081c06080d09060c0807060603020607030206070207060f1706010201060f14040b0402070b160507081219060f0e040503090301091505 82
    0x2d86203c285010f4007003808040440c44452144004201d1415140000901c40401442c8008a0303440608165460032862041c0f010a152800c51089040040e06026850624020000380c44540007800a02540e80220307500003440810740c04c4491684010f608010a007103a40030080c01013107030f80030f00070703a510a00456044081c003401c5060f05498441d1140b10b80064690382c2c10400c1e51021000301c0344180c40703845c0000141c5401014000003440b03034018055928112070300a02d0b2031100e50003901000b400159940b17a16410022003054000c40070710034485603443ca00180c0c0542465884811684c0d0b20000014a01c81403811111185100300d800f801018001c82c108420381c000c800001e4070100f40103012411035000e454074504070500e182409400c08100d07842e402c84541082080007242202442048004909030401d50106020750130304204450920100fa044c1c149180a004d0290f50014042000c1c071408000b43c0c4e80407c0c00800a0020000910f807400140d407080040e8000c141c01e020100c1c1c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 810741510 1250 810740260 810740297
    0x50a17010e0303271005070507061a060702041a0306090706021203100b03090c090a0614030a0305031b0405060a0e0a060f08070e120a03031d010203100b0903030d020415 74
    0x9026002c0c1036052030b10004440250900364244e0358051110b03101c0c8002d00866070b0726502809100702040e072645034940950342083d0f02a10420b581e420b6200b0302d03141164005542e00d42c02c1d1a2a21340503180043c08400b0002c5030325001c191401c90719031511840c000c0041d6804001440c8040c0c44483c0e00f560001080702d01340302060b0106035082a20301030059401c3c840c68081401440c0d004943c2022100c240005601080c050201a00c55034071068540005118801585040c0410190180c0c024000c0909a8500070f00d01d00001d81441001c40c4c48551802c0442e1144041da00604402851280e0381c02c94544040c040c0c590101500d0300807010705000041c81c80c02281103011406854a82035071569550400306d50000b034032921140d01c00303500c00d50303080d01c440d080008004251198070005440382d03e40c2030781d544000010714a01701c9a0300400410082007800b81419080340d148814154980c0c88160000382180681250b400e003692022400040ca0209440120302403d1148c4828610642c8103d007071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 810742760 1250 810741510 810741517
    0x509030a1d0604120302160807030201030b0607020114030604060506030c130608070804172506051003020f0d05150a0506090a09201903110f040e0a0f02030304050a17010e03 76
    0x1160320820500c0100074801402290f01005482031042d1005680503080c0c8a03c05c4140d0b0700700800e81d0327004600c18401c550b003500c02d1800307030744084580c1400c0c444282d0008205121010510000c9100400070038103a8480344c0100d0040d10004203038076128070305a41c1070304654000c0c0c06400e145180c40e110001e44103002d264020b00444890fa6411410755888e201c01007058103804004d80c500d207041000c030a4007842c8000201521403540f00c10f42c0301c54100d060041c1074450140c0200240c50f042c0e0000c00c01665070362410040b10109580221100c041802c01c03904054200000c82c40036440e04040120065065000e00c0c80740d001104c003000e0300e45501d0000402c890705007100408e004a4040d80060040d4885014941900300905880c04005481d2018001c0e03001a8003c50384242e1620500e425885d101c5001c0603110340035501040100c54100b0390540d01c0425000140807141945013100940d1414000c403009070501528541040c6d544620083d5401800525845035518052185107000c1d404000ca = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 810744010 1250 810742760 810742817
    0x5160f0305040f0e090618030304080c1f090606080313053003070b0f100e132301051b090d1103010207120f02010516050a210506030f030a020304090b12010509030a 72
    0x1c6040d52b40d40c2c0e0b00e11446901069959006100d0040540300b41c169000c4201c5400c1e00b10040400c4103041860a141503800c0c503084410a60400c2c0055180351107141520720880d00b084401144046a05441b28081000358908840c0c41e800840182107a9100100600d601481014050390a40d182c0e144054461010756504890b00003599007000075401e84043d05800c5162a0741400500600396a90280000e0304218074141e5840c290b982132011a0a00c145036126000e142c0d5000c0719040172190510720f01c20070010b80d10440007a002e010a110800141802d949400740c021955203180b400c01c50340c50302941d5104400034a00050b284c214501c1802a28003804207002d44148038031502070290350680004407880100059201d1140419000c60781e000e122254a0701e0001d0982098010f0509108109001102a600820a03142c0042e800800c903022202d2101002512180d1400082d1b58120840c5152509609107824851100804801406021142d45500c210118025810540e0003c0980c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 810745260 1250 810744010 810744013
    0x605010801090504050f0609010b010f140d05070207081203100909241113030209090a031b02011b0c0f080a020609060d060519090c05160f0305040f0e090618 69
    0x40100914039080b244d0018492000c2e42d8a0008a1445a01d442d0003103c680107141c4d11038590366141d503017010422840340e01170310700080302200e441d0122800f4403a80c4e0150a00542d20780c001049030b03100f405848042c10044090b241a2130901180700802e800c1910320039450000040001058517161268800c1c0070b600041c60741030540408684a0f003c05d18500140000e0703200c91004503030f400d450001744644c2204460703e442d0743c0d055005100700c2c0300d80140b06c90300d564001c041840200f6000368803025800e03101e04a02d403440c0c84500c01250308c140c01011324412080b690010808101d001c0c0d1494050311812640e044603240e80c0d040d017649d030310b0034080d007c0d4000d501080b0500c1d09081c50350003803498400c982400303e40c1d65030b104003184140080800700f4184090f004024001c0d203105024080d041001803410605104040f04180304c5030309413890003440104410031000404d40070302c00303640062081e084c0f28403481d41e940c21541c01507102150180c8490040a00046156a1844000807414800b10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 810746510 1250 810745260 810745277
    0x309010e070918021311042403020903070e070e0901180e030a050a0810080703050303041406010614070501060b03090102070302150408040303110703061802041514040c11010c0e13060501 82
    0x3003e00506200c10017003811400c1c2c89181321500c4492690007800201000c6880620b04442c2e104444000103002c00a88105401001011865503000a540d01901c1d0350034901d03015a180e01100340c0b68129424010354001020380000684081c1c41c101c8a0728901c0c2000c01804444840b641c115241d128502c00c1c040800c8043c000083c2c1d40f407150843d10b52048a00916462460b01d0310034042c079090003603004881c00c0d40004100000c01a03145101d1680c010044028416941000e202409100c01190002801d4101189503c1800800d400c102c0c000c0000042290343ca003007080031907000c2e5120b103000741c0140c4140c0f04821031789000740014074030541d0011074882c1000c0c1103a808136110491400c072003c3c40c0c41065804008501584900000c0c40c104c1003c2c0d1000e1400c0b403040c0001ea0b841928990302d8000010b204203c2000316406019038518116000200491550015140781c50700c1c420f01c04056103860000031200c1c0d007000344414841d00c21954500c2241c5205000402da40c0b850080c940041c0300710 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 810747760 1250 810746510 810746513
    0x10303020d0f080a3201050102150108100f0212040309140a030c0510120e1605090907060503220b06090f09030a03090c0504021305040f020703050921030309010e070918 74
    0x183e02181c03040c050b55441c4940c8812903a14004c02901c0342c18050111719030480104015a0108069110118a07030304008080d1701d002d801c0f640701c5c2007000e07511084e19180d04042c000341055a0440b5186904448003503482d003000d041c0180400c44034021b40c0101040b040000e4150b1402e000b42130f0803030b54072100102d030541c108818007101c0403000704090280300c44650603408801c520302410000c00c490340005c095070f401c00d50070340c0340240b4140d200d14020801e80303007071140d68900400d40c5000da0318141089030f6262105015401315a485504801c5000b011500c820200951344480710301030001203800040a481d0302d141081d915001f9036100c2c140e42c5c410891104a03034065003003841c465000380a0030382030a642c3c20104d81668041051001e000b4850901880645407034842d030003c0c0c85106108500b07004050390050054070071540071170b20450fa501e012110030740c8240c000300026242d040c10f0300c0e01c0c0c0c10700d002c40074040d20718042e0400c0036004030840841c0c41c441c0d62113000c0c92040c0e24400210305407000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 810749010 1250 810747760 810747781
    0x90f0f0601210b030f0318010305060f090a110417060f0603030c0d1110020a030e07061e08060609030a050607030e0a0c0e040510020307230f0f03070e18010303020d0f08 74
    0x500302d41d4260040b168004010b00043c1b01405910b41c1c9040001c0c0c140c84810001021aa402003805100c0c01000350010000d860700300c0340550021003000c001444100c0c5000003445030040b0360005000c44000200842119804544103000d2008182040b0720354665108042e280c5c001d000502015a11124070780c4041c3e0f10401c06c0d040741e60f02440c15100f6141c90300b42c11409a03441000e0740320100352a02d03a070004031081040300c04002c115230b1038500032040d091034649042030100040102040743d80d0000c20000e0759500f00b121b4807814000c0c03c45142d04000d140c125101c1c0001c850782d5011034a4800c6c4503009600100c0c0c00300c0e00700c0c2e010301404000b0341841d803846a0f0b44000740c010368262142c551076600705221440218012090741d29191002c401203000300b8400140401e60150000d020310010220381e0124050321108034041403050b840340d540201c21209801c0d00002c10790b022200c2c040c500d0302c5040c2c54140701e040c2c134003a500b030714095900034805031182001080c0c100001506c90700000c9100030b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 810750260 1250 810749010 810749021
    0x180206030708220b070e01020706082e27060e1909050d020c030d05090d02040e0312130606090e0a0312150f0f060908030403031409090f0f060121 64
    0xc40502c0860103280d10109201d0903c9201401c80b0300780400810300c04000d0308041000c040c40d03003d2000b013416a0401310000c2508102a06554401610b8400c0d00202c07a1001d4201c441e442d80103007040d02443d900e2061865030b010950a1507860b13606942c034130940c03240390b0140800362840d1900741c400c940c40d20391460f9801248404081c00c501d56603080c2d200040c034184803402284580768024a1a520751000301418000d40b21040001d215042007040659258007058201c6a50100c40018400200182c2c880c01c5119017040002c0848240c1d0412504280b40045840e01c280107420800000e1340303983c07041080b1034112004da5040e502981d41300c800248900c001d43c0e0388450000e0041009002c6602103103a0208680029046451069090003031500e4609100001c05903403401184140c07030003824503280e100343d010140c100b2140d0f250b00390381801004200da4441d00c1c050040c413103510b40b810f4940c001d4801035400081280c10100400c0d81503200c1c4072104c141405c0c182c1d4440b0828080d080c1200100b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 810751510 1250 810750260 810750271
    0x50c091e0c0a2708010c020a0b0c03041b0902180402041412190605090d09050d260309010c110c01120e070510020708011b080f3601180206030708 64
    0x148411803d4401c0005008000000703a50984040010b06040c1c40f142500c0420030110115400740b03071200c0101d40c1510502d6000407200c1112036032600e881c2880c0c084c0d4034002108206d10100c01d00005800f00c603e81c02000c0c298103200c824071010082100300001d82c0b00d00d225401c04074404002c80d458500c1c020343e0b8030815004d014100c40341c0440b01a002042e80042c0031041d01c6055482c0204038034000300340015542242c1500d4401c0d1040e0900002500c0d051000d400645a50412990b001140e6092b00c0103040045038002c0702c1d80c407841c0060915010b009404603100029016a004c1400c104000404103022030050711100610b90700310203140024541201d041c0c10724403c490000400d40c44a0100c02c141c0642c42e40900401800c21801c1030940b00e0740c0c240520100c0388505c1022200c0ea2040d0107942001d03101501a11035103d142c01110300a611014190340408003080a0340b8110340e1401aa0152003500c0080c030280e0040d4104400d080e00d00480a50041001c20010300c41c4d1380710350b40c45540300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 810752760 1250 810751510 810751517
    0x806040c091505070312060f1503020903060c040314010b010f140919080d0c1110030b100816020a080403020f0112110703032a08060f0607050c091e0c0a 67
    0x180e540ba8801e40d90148400c85042c00300c2d0000030302c8010f0503884141c0d10860784c0d0151040c071450346401c490700810b401601c6008035142c2c106200d458018420740440340000002402c0703c000e0b042044c40d10866a116120440d800d0300036048880902006006210129005840b04c90166124901c16034985200e484c00041c04002000300440344e0783d803500d24003010000a40442d6005081c896001e107810010548a01031010914030600044c2045100c2d0a02c40015070f0300b40100c2c449910103801800d0b04c03040d01c07a4080c107840c1e03d031500c6560001030300d0b1052b8215070070007101d45d0300503206a896402d0000041d100c280104418009810b010200d0001d850041c940604e4404a00d420302d0116926803039004c000410004d50141815031600a900c1d03052161550405d01d0340c1d03420004144603080049840c00d01804100141d19645c40703110014001c0c6000d820156108030340e1411640301e10309089424410b01070080440e6061880350040b800340c0141440703905145e101d01c003001b02580c024000c0c000c00c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 810754010 1250 810752760 810752777
    0x5060907300f0f15120b0c071112011e06030201170c0f130501030b0103020f161e29010e040b10120803061008150f0607050304060804030215070806040c 67
    0x100c02c1a10039000c044403c0f500c00242446284005151280035901c00c40c110401101101c01168889044a8000010b84100c556a6501e49444019410004091907025021041840364080103421071b40b5130000781100b1a80901146003100100c0e80180006400903001409100e200d1481d1050380d500302d5111030590b8200801070450b8149503000d800e120b100d80f095844c04111950300b500601c48500b200b401d0540c1081c103004950302c0507010f80000f144098040c0d981460070701c822032064051100e240045500388080e58200410644111003080030311000072040d0318810b00501d6002c1c4d0581d4100c800700d440544694a0709651000050003864864120150000351103110b001107400091048a980e901ca2034a84204018050302c1d08010040c01a071804000040d9241c9003626071100d0115170441e10000d00b0000b0510500905030300818500c40010041900c3d81c00c9030109100d28402d9080b903000d250345906080c6100425545c81001c640300c01d02291013841c0c1500200c09400551409544 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 810755260 1250 810754010 810754031
    0x80115120902030f1606120b010e0d0c0b0a030e10020c030f0a0921050105061918061701020909090a0201050703200a06051008190b0c1204060506090730 67
    0x80c12001c10105105c0380440e00104042c0e500021420500f03040c5000411084a018001910740e0103c040003d20400204880100b0014030151103005000310342060f0b5103030301501e00301900134000c40e99250054803071003c0c100403040c2e480c02115400c041c000b01550500480f4100a00c8507003040c0200c0090017a01e0b100852020801c101280070051002000f00034035520f0f06000d8219007000e00340ca401810400480f10116001065000440c1e5005c445000f0482044910700024102904080e01c6000a004110950b22054004c3d000b91242200c0c1c003d0643c8425402550722600c07068000d0215005000c0040420b005d00f0240038504201080015140d624110035824440d041714100c5407a07640c0e0051008d0084c0814201d805005084000c10411100310726004a481003802e00401c2c0c0441000040e41000200003a11000c802214000b88541420b01c1d0840180c0011541e1a00550010000502c1d6500c00c1d5180c001481d1500303000c1e1108134101c0c01c6140a115101888044161a600700c4034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 810756510 1250 810755260 810755263
    0x1401050c120c031306020109111314090c0312042108040b070302010e28080c07050d030305070e041103040b0a0e0d08150d0c0b0705010f061401080115120902030f 71
    0x4444078600241d40d65007402c2c10030000024268001700c0446e07151203c070000188841c1d400c168006800c80d8407004481074175810b24090b124115030010354640060074858424800900041c42c09011401c1c1e481e40d0182c0243d0280a024601c9500800001c01c0501342d0081108038100301c895000304040c6103080c0d242c6940440303aa12460017100180e54540091115902c20b02604d14405000c64181041d03000d0003009410403c869440a811940001541c0d446d80c541004141d00618002c0e2060b522450315040c084c0003410111580b402051171a4044002031600b442594800700310030382000d0442d203440e140c041040000404a40415940315041045c04004100700c20800100b44c0e2168180c1c80c00148404451142a140d1030240390242d10f907800141039020288207a840c01e124098031003a6a0034018050245594100d00c15454040013080c0d035a02900e1441610741c1c20f0300c0b45406a43e0300c42c90740c0c0440402a038a20000341007a550f06112a07040e070052040d0a00050484000c10684072099 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 810757760 1250 810756510 810756517
    0x206040b03100603061805061f21050c1602041401082406060304020d08070c090b03010b01090e060d03120527010e0d0809160f0501090905011401050c12 67
    0x410390260201c10020b00e1038000c500b51016094500c1e043c4000e80c42c1c11076511144189000c0c03000c0494031100040e00b03984a08010021003202400004001064020050080602c0b9103802d01b25140100b00b240d0b20000500483d406403410304000d525180140140e03000d41e80e403481c0101e9106444403a925005042003400c6806403a01c031029190206404003031240307021820b01c8008600d43c000040002036902d40007560752050301078400c05c0300c0c02001e251442c1c3c1d038800e80744002d0003028164008a072040706648007006091040e4003c0250030211001540d904401c0c0c8101039042800c000010784508111384d001810034441d0405202c02c0c0c40c004500002c1d102c0865040207890040415080000140000b0802281d500f100800c5101208000c0d00c0c0c40c2c1c841c410260303040c000d203040400c0c5402405c10102a0341c502050354500819222032240c14012a030f881070a0005001000100b20204103110711412550a4070004074001100c0006490a402070a803080c460f0113a807040440e0f00b410032004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 810759010 1250 810757760 810757769
    0xb061306080f2d041a010f05010e01020a1505040312050405032710031e0911090705031e150907080115030c05031317040305060a0f090b06043b07140a060c0302010603020604 76
    0x647d01762428000010003203030440c100281150310458000d80131031210301c10000b81c118100c03004203a5944900f02030350481400e43c10400c1152524040109101000c006842074110038034003148008089015008084071040c401a8881c031201c81c0500079a00a0348254084608071251040e01884000000e04641d004401a100a10784280311600c914090718069404003050600343c1c21410062480740342d10000b0916441d403007000801207019401d4100108603500c00091a0300000c0c60500c600a1440c031085c400ca688012070a1a802e0505000703001d0250081100c0c0d84941c03d40d500e51501e00c501c03151080081d91600710142280410364a0b9030018800f550280d4000c00060078035900050880d4004481801c202d0320305140c14000907918501103402000403500480c42da5600b044c400300c2e04802310030705000eaa401071418030003c0710243d581800c0a240d403080d039102030f0b611104108118a0750040a604c80301c554024001d5038000c0f0261010f15000cdc1c80000741c290b0722a03002c0303070413580a90270 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 810760260 1250 810759010 810759029
    0x103021f0e0f0f06070c0e060d050d1b14030d1a1e0a0531060e0c073e0a051039060c1d040b061306080f2d041a01 50
    0xc0c400310f400018604c1d000f05007034840c01900d510030385034282c8901c0e01cbe8154800304051042074012003139901c1c010000c62034100c0701141d140c400410585540750300100d51040e0b1035040c80c5031200600701118108486d610060954104228400c42111000d0040402240d009521101c0814191613207400260100010000c030101007501407820112500010103510007241860824000c41c044451802d03000540c1802190f00c400c1a0b00d01341c00340000c08081c445d0014001d0143c0076080d401c0d9100d03811002030f120303035144c2e9140504003441104d2205003e0140c004071007201c58000e2501c41c00d20515a203d280030181c0d20081e03015690b41c00016001e800e820ba059074502c1240900059100341c0e10f80c00040d013850050840705507001d13540f100351410618455907403400216003036100c450481d842005000001e090141e10780d0009488210140d440003640450400043c00e400340361801c484089819102079103403420301c0207203d814010010807c450400581c140d14000035002c00c40c1c3c5020b41ba1121 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 810761510 1250 810760260 810760283
    0xf070302030c0609060112060b0105090409080d0f0203010e01150c050a03210516050d1509141614030604060e090601061e080c13030c0303080103021f0e0f0f0607 71
    0x505841c43d0100c05002c4540751342248004002030201c0c12641c1c240c03c1d6204801250100111300107907124040c04240d190000c3c180002c180c104a0a07400074214a01e42c10010043c80100c407042004070300090148110501007007005102d1024a080f003424031404510305030708054100d94a1038107002e680003003140410500384084c480a985800078404512921004101d2854005081e003a00c060525800c000d0010024040c11014002d410408170090143c02207040d96541c3c2511500819078070400354000f035401e501196a07841e10003609441040240c0d17410040503520107120b43c2c0c5520241c130755540980e48e40c5000030001800b03a542407189031080040c0c002507140410103045142c880c0c000b80241c1d0840c442603a0400c3e0841c10041d0040c407404070407912103801201089846105801c00740c030583c2549400020994000d0409050720f00c04c1d00c0b61920240c8036101441c8005001d48444007180c0c008130b83c2c002a042c102030301d00c000f00d4001c041059444290740443c2d83d0f80d02c000b1090b9844503000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 810762760 1250 810761510 810761527
    0x30703050a0902010e0f0604080307030e10050a08150f040f0b011206120f02031002040b0316031a061c0e01091a04020604030b10240807140418020f07030203 69
    0x5100300c070761080502600b4840c4080300d07400240900041d90455101c4c071001c00480086403031300c4050764040c00070380d41180e65410903030038050101c810b005041889038001e03c612003174440c0705009075036000000d40c03180369080e200c0205190341c1c1805200d00c940c000075041183d130a01c1e91940a0795220440403c40080d03400602c1c2d0004184001c04041420464103001d010028250b106482440d4590014006030100c0e43c98400031b0309014940890000d1180007260200c5e060700385400450284141d007128400a1140e414164180c86e0101c003051600c07519910300000303504100000348a840140e01406000c18140810745040350307824061340105a640b0b15400003000302101d800c048181d000a5079400601d841d9000800034850b80c000140f20fa03000c140400c0c25107003584039075000740008a402c2035074125003407540311070058120302640005207009c012a039214043e000e52001100304584181c500b07400c011352442c140e1030101c00312925507400c100103001c5080300c001800c4c110348203601860781c1c4c0130603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 810764010 1250 810762760 810762767
    0x605030405190503091011060a05180d0503061c021f0306090b060306010309030c050105040503070c0b13172d060106050a0f03150308070b01060219020a1a1606020307 73
    0x10007842c1c2e155010044240004110008180c80440c0002c4840803c0c5091094080300c1034044800791060920803607051080d111003070341026104819005101c2d03070100b030410300a5500d9400c01c010902251007007000c00e045040080d98076040324020822a220b000640d0f001c1604040c90352048d1842003c40540d40b1480c0794140502c17802010860002e120100000c0005000c40c030000c1c111034189555103a50a0401d030050b100020069009002003100d45040d00304561245d0002008503200551000c0101e0580d85800680710500d00100b90884000c5c105108030400c0400401501280d1140ba5020000103050040254175030418400c0f1040d00e0904403400342c0f4008060300300c00306011040c0400c81202c2c0d401074540381001c00c03524001c41c494000d80c040c1070100141c1c0d0005840010000707040c80500c400061100d0484005500b00c1d400c1c6d8400d008240381c40409640e00070b6100303500400402c00010260b01c0d81e00185441a045881d00011201650101703440b40000c5403990380220801c04100d41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 810765260 1250 810764010 810764023
    0x1060e0108072409150314060915120709060b0c0d260c120c030f010e1b0304050f030c0f060702060c0409020d110c010f0e030a050f0c0a020301060605030405 69
    0x10038004004090038943d8030100300d2107070b201c40100d00010310443c110710391082c8032460082c1300090305116220300c031110040107003803401c0154400700207000200d80e06041c619031140c42032114100c0702d030200c0070700310401c2003a101d0039240702030781d1184440218201001f88035000040c080c46040340d60310092a040541840601c0740e10303205010903861802203030004480480301200710303000c6101584c0d032001071405e018080c80c0d02c400c046075400b0302040042d606440c0118040d40c0c070064001c40617a6103003600c0741e42030421644800525020f003501490400381e40c01450304284228261030704401051511031450304400003500780b41d44030382d00e103004e0050244049074016000d440904018039100e4601c101b50300c038500c00c80c040399500054907001f82c02540e015a600d24a01c0844654400980c02c02078080c0c49a501030415030341c40c00000d41c140740380002c101c43c1a0200354855909114108038003085c1c0d41c002c05490036590040303095500059800b881400098040798407030175241e0400d0b05140e881d241 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 810766510 1250 810765260 810765269
    0x6020109030e040e06011806090c030b0108090109021309030302040801051609080f0601120302030c0a0809030f03250309120f0b07031808160f0c03060b090f070e06190201060e01 78
    0xa1401c8a10413020303001041881c15a010b80c02104080c101300c0f21150000c2c8002c1e0b0102110a16000000325103551581141c46802c10980e16070032145c035200031407400ca54180074025030250301c249000310020700d150003440200c3c0c0641401410655503003002800d41c5d1040303400c1d40905002d66000403c1d0364000c1e2f00000505000802855615914030403280c1e9140c06000b2111048090581d210030136100300221002520101c0a450310000380b032414001a170014203245100f40140010101803040c00000d030303144080340004200740b8203466034403414041a83c1c0310a80400000400c00320b10109000c400a091910400c562480c0345041d09180e0040310b0003520120400d810811087d0f9180941e04050f10015041502e0681e00d01d805020151001c0d81c10380c00a14107100e0921000c00c4c800203101203170449020300805e0103142c0304139080100c00401120b02d0f010813101754010601c038511600200e51081c2020b0805e911f03100c0382084001810500e043c1040040c0e444001c18045111680d14003401031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 810767760 1250 810766510 810766519
    0x1104110a08010e100306020a0f021b0f09061c0f030305070306060c06111909080601080309090a1a061602101b140a12020706090f181a0a06020109030e 66
    0x1100302000500c402018440e983c240c914a501264005910000c500700641d401481159107481d040000380404c4000750406025008240140241b00d8058140e650030381c50007403440c0607010a00317040000d10000034040d9904107600400c2c04150001c007148840742c150198282c4440b044052034020151400189080201030414000300406038010f003841806950001c000b02e02182101c114051901034592112a115160400f80740d201f40c10525003019640f640c2c0c162141603880e103108641e6842241e59040c2c100c0301c1480081d0644607a82d02c0000015031303030000d042020540e200000d40541081c0000d03c03103010710002c0c5001318035001c0c5007060001d010b81000c41d02d400350902800c0480039001400b80460721645c41500e6171210900458001c0e0b640032050558043c40d084001b9911803140c081c0b100403520001010408080b14400301045452038070180409003d41d03129880a04048041c05501c0e840d1249140760070740e03c50003081c002d00303800d50001494072a5030130028400c0c00c0030210b0341c0c0113 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 810769010 1250 810767760 810767767
    0x30804060e160e06190f05090a0b03030306012102030a0b13090b070e010c0f050f070e0c0702150909150102010f0509030307081e010603020d1d0619060801050103110411 74
    0x210b0801640c0d800444203820700c0c2c8101d680d1400b002c50b401559100110400005414000c629135010f90401001e0320800e4408004603900d030303042041200c02000200d941940180001032031988130300613545040c500c00480f00409040c8000035000d90b00706951150b00640c0340c01e900000c034240b106000038503405180e0140000140b40d1a000404100070300040108134a00d111034011382d0144000184043e4051010310441c001c80c00d01c80d4a500f41103a010015000d034160010b07840302400c40b081d000e10b10441d82c140c07074940d80d6070800c40b0380002c100d544452040144840205543d80000302482280d46201600034151590002800c4844098078620007600e000244085404000b05480d800b04036400c19608130b8031524801217042069012000c00048604000b082c5203a054010388282c3c03075541c0307003444400310148403034035812903005038100c240d448100012101c014001c9010004980e4200014405865103490342c2907803026042541c4110314401d100c5102d040ca4030079a400d900140266508 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 810770260 1250 810769010 810769033
    0x22080d11150c181c020405090d0f0f1101050406090b01120c0e090c1c030e06040501170613020403050309130623030309041a120105070203040b0f040e04030804060e 72
    0x4101e4800b400c0250350260110f008800c0e00d040d0b4445003901d420052900030301660b081c05a090384400710500b01c1c002e41c108004115031080020f2141034642032615200b02c0159000070031203500c2070300c403a40400c0040c2c00030a080d400d01c0a1040c14090b5000e000041080e8000341021000440180d10080d4030b40d600740b03100710109421803119402d44284a11100180e25000e0010b49000300c151400c80d4800d5400c808030780600e03414090202540d10039140d0000c0345e0346c00810415180581e102d02c6010607040d494040c80d1074084000709500100041440003001900156001260032a8008441562000810755640d1512203411001c41e601c410301400040d0030f212400c0001c8450101c0003c608084405000c0195001c0c400d0f940c0e0b41c440a031003081030000d0305409a007080c03410318002d80100b100381c40240014006004880c80b5180c240c00440c54207152410420165000030003100440c0c9083c000428a1000d125840740543d001c3e0740d5050700c070704140c100a02110b19034019141a5404048000c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 810771510 1250 810770260 810770293
    0xf091209150f070c230103050106080604020a030626120a0c170405040f0603120c0305161401050c1209011404170d0f291522080d11 58
    0x906030421114816240c0101c81000b0301a8010442c0c01000d06190f42c1003c1001c498400d090803030010f084051001d000b0740c65005400303d0380207015240003d051140042c0003410660000c00d8444414a80007c0da990348100800740140300490303981c080301190122064510381040480c131206034142e8211300c0d04102080103071959a074010010301c06000d41101e0300c0e03000040e03802d942c000d240c0a0818052120b469840200a05460100302ca0301c0e48030001440c0315038840e450618400343c2c19200c952408481c0703018a2440b00b546a01102c0a0525101031610302e0020301a02e4000c060384044d00b82c440c041e4810904071a100100380a03810380c0340108181d200100300305074503042900b11030601c0e20010910354000c4140700f0307036070401e40207424000c0e20389a24855a01c0305200d07405901c0c01215152030080c1e03092002c600d4107040c0e40d0051785d49800c00705c4400950000d0101d104002100c0c41c04080c0064110b495403865800427441e50882d50b03c400d400f68000c01d1822071112401c0180201420810041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 810772760 1250 810771510 810771529
    0xc021c030612020411040f26030304030903080f0913150501051c0c050c0d09030209060d0c03020f0d02090711060c03041a040302070b070b011e050a0b03070909050f091209 75
    0x292140345c8030304070703860b03100c4400c0101d03000f4108482c140403c10307403580040c4508041413200300100e9001c90f0700c014000113000c4152401294113954070a45d00d071858403503250580207030104c00030121007005813202c07643d552036500c610ba00340341307201003141540304001c0b1000f0310f0640d0010b818000d04000b660380c85040d842e401000c08583c050b00065000d12114104d9840c041e490490f00300d440380315a03500343c0e141c1100c0b1000c101d920895800e061643c458081c00310764624a40000d04414030b0220030b2005280002481c00c262a000e001c541a20301980c00042c009102541d5a2001c02c504001384407032a041488940e912000c944010740c070394106513592400d810900400c080c0c442d09001d01003410580300340a10300003881c001080503180c0700706003019004400203210b00050404004d064082c0c400d0880d68110440e80004d203400c0400b46480029040341e4401402e840820100780804500c00800c1c2c0704003406440b07044c03010141c03840c00d0202c5d81d151200e08850b640c1c03c100140641270f407035540c4d0011b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 810774010 1250 810772760 810772763
    0xa1104060b040302181f0b1803010b061b01180c080d1701050f0a0302032505030c030a0b04060f02030109090209090f07120611181e0d0221010c021c030612 68
    0x81001ca9581e0a00710b405c0700c441903445d00400a00c1031b600051010708503001d0700c50070404900c60b02c0d43d40d041004060807104003400864200c50309000750400d44000c40d2403000340303c1c1c00000101d003400200f0110245440385e00b1048505600702c0708148841e41007001624800702d03e41c1030940740401c140d20540c4d49004c0510a1500c958542111030840703484003600c5030025903000c0c04807401c1c4018250390407a9101270244c180e40411b8602000a11b9143c00036281d50b25100103000f8052100c0d06441e00285244020410707a406602c030709040e441144148010340c02072030f1280e4000b484016034030400a0400002d008900e50f684046a400c1d004680420120125403103440488015901840c0c040003622040d280442b240790040344c50403800c00a81d680b01d003207442c01c0f140c880c19061401a1948031071404040709400900001c00e00006041010982205c580342c0b01e82c0c0c0b014910280300d007509442c1c584402c540103800070903400a03040c040c0e40d902c078400c80f02400d00303019450a00c40041000c0048280 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 810775260 1250 810774010 810774049
    0x2060304020d0609200d0f12110d0f0e04090b07081302061201051801060509101413050901050312091009032306070e030a0318080a1104060b040302 65
    0x420110b680e0b00c0700085410f548480c0501002500b42805c04544a80700c1030504200c030524036a000c20715094118034121607004030011070241d03141e10b862041c2603854038100c041c824038249100541e14100f01905e007502c855a1000c04605100900400c484c0305005850f00403030a00c00741000007609030100c103502409a2805840d00d95912503401e0184068000194210b00005400038980780d8054178203043e03070004e5840180c090030310310b40000c40b0781c024451000040d80600022000d8901901500c10410383da01d408a0f040d801e00b01d80820681c8945a20f11402402c038070204a08d0624541f4507006180c110068070100b0302c89102e0004a2040200080c42018041c0082c0d03009401081003802868108450200c2c1c0307001440c5000c00700030490070341c800c00d1003090000b503403989c0b007030040b00700c1c0004c003a000d000c6490255400b42c1c2c0d201d00c0c0c000e00301c46107180b00101048480d010000e0a105078001e07201118000e1019090200320703401d507084010104410002400561110402c2502040d5400c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 810776510 1250 810775260 810775267
    0x1b010201230702011104261608101b09030308150907020607020d1b02040510170f0c03030a091e0801020c01020406090503010e0a080d110a050c010b01030c0e1909091a070305010b070206 81
    0x4e0350b0800d40691810400f0304008d800c041340c03012000507441d90030006418100024501c92441130a6082c0d0310003041c00041603441e003440084c0c420005190804584030f100c01402c40041d000501c03c0b40100d640c5001039120804103d80968104180c5d55001445e0514070503105100588144802c1c102d00040c1c02151200085441007500c1840c2e040205031b0541c1070026201400310140d211000d00300003a40b58801c04105807400d10340031040b01e03002c0d070050311680c5000d407614a420203044003854904d200740030b88090003d20464203000804560404500041c1d5460401c0342c003414035095038200320f010340c1c9049040f0f046440000746280c11140c00940391030319280d044c5010400b4141350600502900c03804038420304255040b0024080204000b0002d01c280c0c220440110200da040410400000342c05807101e5074030342003009181030107588424403040041c2d100d12a01e41554003020003100d80000d524500104c006441441c150031240e50314040c0059490052844428040c1c0c1c44068410701000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 810777760 1250 810776510 810776579
    0x1c0504060e010212210c161502070501050106030617060c12091c0e01080a050f07030c23040314070f05010e0f130506041b021b010201230702011104 65
    0xb0800c20035180712968a5607545c900e0072000440c0104051540803c8944607030128810803a0181038400c100180821801070f445162507400030101d00036540000c445c0d0030041c181c0403d100b03004850103071405403070118081d07107060980020741c0643c030001070154002c0028812180c55100c00c8507080480010100d0b200d840341c0180900b03002d42c8002d6a010a08544401c09055400400300310282200740c90f01a0103950751a0b000d810788000b1500c07010104140c60004407a18040d6101200501d01d070714010b030103105082caa50404007028464031141080101d401c01c20001d090000b401e040414002500c1070b035180401060200307150703010362418815a50702d08692510368640011252000410380713030f029040e926012000304016200c545c0290700381061005104000701d9200341070b9940e54003c1008080850510399a400700b5403c1030704554071014900c401c200f000001d08903241c83e41301c2200550901820103401c6800c036507556441240d090000300001441450488650000d80724071500c5240103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 810779010 1250 810777760 810777763
    0x40e0a0b0705040b040609060906170f180a03210905061504270309091a0103020f0c010203010803131a031614030c040e060303040e160504030210050c1c0504060e0102 73
    0x8540016a101130045400a903987e03000101038219081c64444205031922018200c4181060451400c503400d1048003290111002c00e10b035a5101c1d0a007022202e98004640742a41841d41d000020703000502541c1c0c8205016140c00e020301d038500741000b4100008220b543e1202c2d210300c801070a00300c850340c062031991a21317107403a00106820400185a40e6624541c0010741d84c11058440341900001c000c4040841c0f55035a61249a000004846c22a00c0c0e1144840046022350700078648111440414004a49080424006580a4a01040610303100c0c031045035810000c40e002c2d4032014051120b504810b520446860450b078101c011060908030640007102c0c01e881808003000550340c403182c00402c0203201503860014105403540c0100721000ca4071000101552401540103410416071038a011604148010b100402803804074180141001d5070382d000201e4041e5200e881501040e0000780c164038001e01400400f0800164614603240e40d03403896401040d47c000c42c001c03d020300100d0121192144e00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 810780260 1250 810779010 810779017
    0x6050c0102070515010314010c0e040b0103110d27110d02010e030a03020607030f020f0901030b1c03030902040b0d03021002130806010b0c06060102060c12100b13050906040e0a0b0705 80
    0x80002c200c07036040c0d458502604001d013091105440e450240d01c10a07290340e00c103000700422135072142d0711296030320306050800004006060a1038140341d170b90340c03110f40800ca8290142120419410002409030703013482c10402c03140c2e120005401c007903400b80603200000b0040c0320400d1b2000816a54040d500042e40700580d1288004400550b0611480344007408056000805500c2021603a07814014042515000c1c426406072a16048280c030040c040748905500c40d920860000c0e600030501c601403920355001c1401c41070b1400d4260002500e89601c8410741c00c1034015203814a50644084000304401d882c001d44441c52441b240c0385103034001a144004084008101d0050b02d0380d98107460381542c2d60360300720340c1d60f40c02080c402426006160000341c4660000c940e59224803198045286800280c1c00d405102c2003004000410030381803000080380307907a10580070707000703251b01c074881c030280c0a040c4400c014088000502c0248582e0600403400c124034070104441102c00d501c84410005501c4444050301c0b50700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 810781510 1250 810780260 810780263
    0x806151305090d020c010302070209011406070b0f07030b120d20030408100c0305060919021911100c051b0114071e020607050a210609020d060f080706050c010207 71
    0x38244010b2020185010851541d40007642c1c0849004500c144010f400742d000b191f402030740c882c00ea0300040107009415511000e100100403c498a04216039403805a00d800039102400d000d901c640030443d0f5542c051090000b43c00b0100c030390500c1003440121241d61244c482980c08104801c01482c12098034658000c5aa155840000e482d10359031102603541d07403034220b107051001c80381c01c01c2c40ca40441d40c000c0c0f15590181d100a411b1058503516548105075900d010f504980f0501e60030014580301d4107150f09169507201140d5101480c440103170010f10b01c2c2c28411041030751444c0c07401c4010301c0010380000460b07c01c00c00811300d04070040b414060250040c104400100e01c0003031000c08110380590300001241e00031f80401c0b21803290b55041102240d8070581150b1041c0444d01c10001182c0a5001e500d062401d040c0902c030f0308003010038003c1c810003560003a03800071140c140c01092071580782009004010140c41c01c1d20303d030108589007410030765841c0e20620814040c000f0026031031400350000e404031500c19 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 810782760 1250 810781510 810781549
    0xc0a0f1a10060e0a18090c0504050103050604140c19051831020607032606010215150a03080c0f0a0507060315170604020a0509070e0f13060f0f0807080615 68
    0xa4141c1c3c5c2440c40640222201203550b80401c102c08202c81c0361511036541a65040002405559100e40c0c401144000002e08c00000c0d11400309443d001e81d0340c0b952440a02c412410610709458600f800340306460910300350030742038180e00d801080090703420032001284074462251002d03207642400a200400d40d10780100a5080200019000140741e0085400c0e28132a95240c1c0904a40c101240031585140342941c0c66030042e0898000b90402d4000556500d40040c1c1080c0c644220640b05ca00280119070154001c4030349035004100034a452600344030001e1001c0749400503201a421711383e00e060311280c0a00801c014182e032001e510450b40569079a80000e0400100705034080c44180305410342d00d03002101c1c1244104407a6001140c0f5082c4200d60303a01a03400c603100d03411810011003c11442260b03c0044030381050009103540c0750010385000d214018035800e003a4010290030080d0301c441171500c80d04800d42c654810402003181000004200c0da02000c90030b81d2a5801030800c4c0041e080c100300ca6a500c800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 810784010 1250 810782760 810782789
    0x120f0503070f3501080c060310030b0a0b03060f040302210415020708030a020a06060f0e060d0201020f0d091a030721060f0303030b090703060f060e060c0a0f1a10060e0a 74
    0x451480f402c0e41070b107503480100c0b608214070344104411480308960f04c2d0320030200d80710100001b440f20f646881d0806486080810346940c0c5a020900e021400c49081020b9031100b018841416014001c0a00d0b1012040400e480c062080398151400e21075071080386054800991200c907040e1090183c140540082000d6961311940208029902c40c0d840d0810303151649003100002e106905042e14004680c640d640f01c010303643d06c440c1042801440213500b68103501400005d40030100061001d10000e582a03203c0d06081414100110354561541c1502e6a18410803c1032102ca160441700c100d0340348176000b2681c00c47c886030421070b8024207050713403145011084030782c00802015010740240b405c0d52010350341c00c1480e9032103d400302d05880c03c910420000c10650b090601c0072070f12800380340c002082e0281145141c0704100410034600718180000341c5503204400001010490541c00a05244801042010290511f5403410340749810900c04d00c4144140c842c042c90ba141c0b0349160f0700c4009c01807801c41103003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 810785260 1250 810784010 810784097
    0x90a051603300c050109020303030a02040f0e0c160303090b070915020c0609010c0602040f030620250f0c030507090b03010905032506050103120f0503070f 68
    0x462840e0104460070481e08040780402d421600d6a481c85140b4805403581c410103000c010f45030403510040c1a00d4030754862803000090388040008602900142e800180c0d00c80ca060782001000319940c00903103801c40304100f80718801c3c0d00e90782070725402c080480300204001d5440c6011b500412040c40020042c114000c1009510340e00f0605041c11203541464075402449142c1d0101d03205c00b819680554030210601c08040e80703502c0303010481e0140d44621001460542c031136407078214004251b801101c1942e01c50f01d15011500d20402ca104411a031000c029003800300144401c20b084150500d621a90510031590704107001c01220100f150981201c6541d104540b40d040468841045001d00c01c01035040c08401078050805200e03d494041e000000342d402e00b103988a00352090002da001c4080c50818003010b044c0803400e280701c0c0c42e0007188101c4650071061030500015060707441240c1c81030248001801082034a0750401e4007400181510f00d8400b0030040c1051084d00c02400300c440e81008981c80000003903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 810786510 1250 810785260 810785293
    0x122405010b21040512030c13080f240a150b0d0c0f0f02030315010c0203070605090108060f13050448180908070f1209050405070c0b090a05 61
    0x805034121406540000c800751000002140c040c3d5000b00313103502a82010040340018005150001c042c903031160700d00b604030001d0000f079000582080b8180d030080b032400c070b240c08410841600b0403880303510000403804580b6451180c4090003404040e040d034a4100140c00501c054002101421a0074034041d281c800304c5803482e004200c2000c0403c045808021500c441e00d01079041103e040318164002c51666607161404041400914112341c144000c40901000682d070502c07098020344865510151a90841d60005201c02e02c05005035000c0c3c95010120402034031041c0b0304030024821801d000c5103c1d26030345003051b03200e01c4512200100903807034560303c801c0354084400d100901c50b9100c4491448810005411910b03503c511230700848800c0c0302c80754424400f02c1e03000240010b01a001c00e45c28481355071120820020040412075500d50742d400c444010641004108c0d01424082d201004203141c41d0201601103c4c0c00790010f040940c41c140024401d440400840d8603003503000c41035a000c801d8500840 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 810787760 1250 810786510 810786517
    0x90117041b050102030f071407080a0302060a060e160302030415060b0702030c09061c03020a060c03051f030c05221109032401210b0906010816122405010b 68
    0x8003007000030100280940c800401d40740d0300d00c14440c4c0145841c025580e00c407120b08541d980c840702c60090507400504e908081c4135000805e0f000741c0191002345400c842c42e20403076841e03810481a03049020240080d05e070451a0059241c8820306005a4a45507803e1042c1040000641c440d00d9906000010850499030b0015000d8140b00307804461103100c48100b04200c1c180100c0d446504880361282c851600400e00b400412441d00a0043e180030001a40304c0703e0603036806403005000300743c80d041440046a03203d0f00440c0c0c4100301071200074560f030035507883d244420828400c1d98445ca43c8940307900040300e0380240200039044040000c001d4000880241c8541d03030048414280700f409894030002800a442d5807851070503e0000c0300d001140c2c200500d03c002c2d03a441c0b665803840560300c13032944000501c0085000b40a1031443c13000704507942c5004042c9203010070f641c0114801c2d0422140800c2030860362000700080d99880702058864800d02003034582540600c0002400b00ca00b071000004420203048001c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 810789010 1250 810787760 810787793
    0x114010f0e090c0f0c010e0a02210604080c1608070602010507050c0718090605091b2e03110414270a050603010b0a181a060304030509011704 62
    0x844460214551066604602001d4034640008080000441d00c030241c0005240064103c40c14904100c0100c8506003100c0e003041c0c0c000d80070391042011405520704400c0c501c4040d000c00c01c00d0350b2102c060114042e281c40010304014905103021840a54003041400001c0721100071001da80d0a05a40e000c0701c03943c2d41c0c8580700c2c2d00095460000130500c5540300340100c6003000101401000c91524111403600d4442205090b0b01c10169652100c400190041c003415015074032000c01132103207070780080800c031100c1100800d80303100305c488079807815075181544c141552414408200800040880e0000d50103070100200703003048500f00040c0031618138260070320200400e606943c0001413010301900441102e171907101d550044840540054614601904502d5000704040c0c00840c03504001004070b044003940e07402401d28040035009000c1100310520502c16054000f6044030340c1e40d0000300100b031140c480030b0005802c209000a078251164002d4001c5e000315030701d00301d40c1003640c03510b0308103100480783c000319 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 810790260 1250 810789010 810789017
    0x2404090606021c08071709030307122304050304080d18060509221506020705030616080423070b2d03061e061206120601150503040614011401 62
    0x901040d61880043c03000c10011007449100b19066101c101a03902d100b0061402042100400c1e084c0b910018800405010305240c100558685c144600041d005502c0b6811803000313540f8000165108041c00321b04904039101003403040c6181c1d100c50030064118402c42d04540420310588180481d1290700104012240b8101d000d002c0b002500d0b04001c65140c401c802c04180c0c80911030102075403103846400e00040e800c507000400503240d800d034800050b08800f55070109003d81c202c40f804000e503007000d0200c0c075070100504c5a08640e0088048019003c0c070009030020f030800d215068012065002d001c078410190403501d04850090380d460050011942c4402c0c0c242100e0008605002100c540e00354502d008640c02110160a41e51145e007401aa80e25a01101d100854031002000c55500d910f001803c0203c44151a600c061a150090002c80d40c0000700c0a0707810b41c402d800400c37101d1450009285540701c0c80c03034856540d0300c540c02c0640141003918100784005101d44000100c406048008000102d800c0c1c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 810791366 1106 810790260 810790271
    0x120f02150a0f110a12020906070b0601120218120a03080f061804060c08010f0303090603090807061b0315060e04020c280203060a050403120b240409 65
    0x41111003c1da00014480000b030303440408403624006600c07007540b400c031040c001b0404034814000060b000c4400d0070b01007042c90b813248a080d1404008030000303549031041d2401540101c500071200d61300ca990b207a10740785002d4602040e5003030a2901510b880006a0358a24081c107540c1006000d668050b80d488568040e003400a403c4600907030081400090000f82140701a00248040c1c114030341680c0d02340c0003000001d40c0101401d0560b9411b140200d020000342c6000d202c58016098010032503414060955a0700d8200101c10000424540c0c007813121200030161016070f00002e0041e400041c5480e0415215820950001c1000b914481300301d40b0780a0f498a02c01208072130a1035200716074040003007403100352718040040c643c110380c2c006000c00940c1441d9501802843c41a1003500302070752943e545200aa0741d501c0e1041d594841c1c6059565941e0340300c4900825640907000e455203081c030b0704 = true := by decide +kernel

theorem cover : BRFrame.Cov 810611510 810791366 := by
  have h0 := BRFrame.cov_init 810611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 810611510 ≤ n) (h2 : n < 810791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
