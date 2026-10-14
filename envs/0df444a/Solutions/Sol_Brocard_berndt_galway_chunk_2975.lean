-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2975
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:17:57.134241+00:00
-- url     : https://prove2.me/submissions/a5a93184-df2d-46e7-bfc5-456d29fe67b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 534892086 ≤ n < 535071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 534893336 1250 534892086 534892139
    0x5090603032808010918110f040207030302070b06060a0c0314120a0e010e0601260a080a021e010b0913110a06120b060918040f0218061008010602060a1104 68
    0xb03001e15804080e903401040711110510400c0d01c80c2080034640d00c18120020010744000000c641a51118030307815843c0500140215110703811410043c01079405036404983c401c07445c4001441031b00d00081078500340d00383c0b07560b602d50800540c1c0d810391384002c5014070100e9801301030025159400500d03c50318403c42c2203100101e45c0c00c1c0744425003403d4404080e41528543c01450040c8a40306641d48280340000c8c42c4c11040707004210100081c2d0502002d544090b10000d0b0000310b8545580d00011601158400c140d158560010300c0c00c405030890b04540143c0f940150810007103000100340007500d0000500038008841042181c00c0014441d2500364040030210710701c11003c201100e590b00c1980389280007580c03007600d0540380500280b000c0c401074100942c1e000d0a24045014080b606205180d00c60740a8402008000c401c20304020701c07041128228486d5420241d220085031050320388038121070360f0340c00400607510f078003d921000e80741e0012a00c410f84000d1000140c1151842811a0803d0645048 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 534894586 1250 534893336 534893407
    0x304060f020d0615030c021b060d0c180b0307020a0b06010e0a060f0311030c07020d080c011103100902180906011b08030906070c110114040e0411030606040b06040509060303 76
    0x40c003801c841c3c011642000e05182048450421f6000b15a14850301c0301200034024142031040004c02501521ba1000042c519010a440506800030b2807903c0b418614508030180076501e441c0c505580c4011a00c020041c1c001078180e00c00a029408a2608078070141000d0a03a0917040011130003451242d03110500041181030506100340d09441945841071040303001c0c0703107549000c0082c4401403082c544001e0003030000d0980399041c850f0032400e0354908012040240486600140c0c8061700760800d403980079170709001800008038407895100300c825100040b80404000b8115000300304003200c0c014002e605201e801512509500b0520b00d1600c00b4500c10b008954403810700c2c1101e5440c10300700034042c00c14403641c00c0541011130061480e00b450498246007604420500140139007850185034444003840c141201484108600008400d130803005c15030848416035260010001038540c10001d01d900b1001c100000e210130b0400c3c000d4503911003c043d0846e85407013500c1c441c2c1e200130740c14416095200c0c81d0750080d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 534895836 1250 534894586 534894599
    0x302030f0a060c032d060b0d0f110a0806040e030d1404050606030601050109180605041a040f020f1b0c06131d10150908030c0a170304170304060f020d06 67
    0x3d0002c0b40d140c24901006000031641031013030030903076010504401a181d5980100c01420710780010010302520350711251162262000d41300502042d90f2403800750ac0c107000c5201c1282081e6815140512641c1d41c8841e07440d100c000c180801056810404841400104001060703661a03014800c00d210b2040540c0c011890031f41000d038140403026180b80c4c400c1c0c10003c0100096a40710202c5816a40e414001d0b02c1c00f007541c010075000170991350707010582080c180141e001d01e21348290001039501806540520401e2078108810049100710766110000403414412048030b50690012210700100800c116200040004000f84040d001a200c8130014070414005000186114100e60081040c0c988030f84028206071580c1c0d108410180501c81c080c00003441c400c030096205241c0f8100420300642629592400708440d81d032501d84101054820b0501001045030440c0420226442181c000da20036401c10040102403590303a20140c415228680c465039030f0144030702203100402c020854100b0001c0c281d0f25065 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 534897086 1250 534895836 534895841
    0x705010e031b0910030507260c09150103020909130c0e072c09100801060b03150603060307170309010908151501180e0601110d020309010503040303060302030f0a06 72
    0x590940240c005405040300007042d9803030184218030443d03201140d03a9440d840c0305a00c00441d0f1018140d481407160006075004800081400d008901c1489241208071400c25641c40711001e0b1880d40041e15500081c202036030300c010420ba07040c014503000d840d040b075100c00603008100550321400f400101c040d0800410007104482c80080c001d00444050364980301c00060400c549a406016030b004405a05081d242c1c03402c40c0310754400c000205480000e040901d00350b01840d01e140200e14040d03180607008102410f954041d0ba114080d01c4110b00190b000032130500c840fa0b00f0240c079054142c401c410000c07070310030040315088426a020000030764852904800050500e40d49901880c000c0d040070707001d0750180f0b1014555550084020304002d81140030600100d400405d40030114411401c0d07a500070501c0300034500c3c6240900e100340d03286450003204003c0d540d2280e10050007600075a000b0040c84217035500500c09543c2c1710b030080c140002c85641d2038020078140120019594669000000d004040101c6403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 534898336 1250 534897086 534897107
    0xc140109050108090613020d050d080f01050a27110a2d1205060f06070b240604150201020d090b0702100e15040809040c2a17031009060602070501 64
    0x901e0602c0f01403e0440700503032100f10103440000c415100300001400d544810503030500103a40901102c08009210760010b1400000b50340762452466604000a8280f030324244000075aa0410040385081a401040000220100c662410460389685507008091082c42c05000309000c6900c401307540c0038400d0903103040100b14116124000c4410749500500550114030182e1140803140005155100d0000051060015190b141e5004900182010810a0700303100c1e507006000030100c1500180007112480c42020305140880d4219005000402c190080c644c404484c4144034000140703801c03440d0781840e0907101111010364040c100117081c40442c540c10007003c4042441104100000d046e8a29030b2601d07010003001c4030204610260105080c030074804100d03140035100500401c220030352141301804401c40b0b0403240c1c0c414844104408045500e00b000d00c0c0303800c1c0e4006030b025140d0103200307081034217030f040908024034402280601080c400224414400034081a4004020580c07801c000103020b207544 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 534899586 1250 534898336 534898339
    0x90f030f03050f0105132d14040201020303060910031a070f1d010f02010f0e061b070c030605040807060c11010c0c050a26130905070e010207210c14010905 68
    0x402e41048040003d520070710381034540480f88207814101d24185031303000e00304c041c0e43c4600300304813500c0c1c0d10ba4030540d01000e007850381c21166040c00501842000c0c0070981c01d044801a015820410000d18640b8042d88855481030f074803031130048d6a5850b501e400c05940308483c3c180b03003114612018491000e8001c0c0c85403410044602d041d408000c0c00c0180c001c3d420034128070160500c8229806507141c10b00079000702101400c450010407490b0707214668250340e468183d4000c0b205502018020038400005003c544445030030003c00e0080b00e195554400050000801c10344101e80240411710000742c0500070f040c007a80300343d56032078500d621500a0500316102d440102c018003420a1498000640c086a90300072180c122326000000e004000045804100014544800c1c1200140c1a034034011140d10801c16644141d2040100d03681d415419180d000c00c0c811118096030000c2400c10140c0c040c2030300b01c0c287c00b614001240b074809480d900c101d0416109c0c1c0011010034556950348442d941d000000c0002000b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 534900836 1250 534899586 534899591
    0x1802090609070e01030f1e0207061b09050603070309050d1715180c070c0e01080c09040f11040b06040f0821040e1b07051f0e1f0f090f030f03 62
    0x6000714060300d6000070f40c05460505494641c0d0740c2400c0c045078040580d140e0555400d0800c820347c00c00d03c0c0020b5203c4a41143c42501c0d002c1e041d454030149400742e040105994443c03042442c204802c0008942000700381c54201501c80d8040c40010780144025a10b00036141c858810221513182c510446050080601c40d603c161610702c64003030340d190034060300354034407000d80d40f009515060500d0100d0b2180b920090324500074030310002448541c20038240c0c100c403585015228810f07c40c004000c241d000994010700420103c0f400c0da80482d0034500300c100421b0009200058440000300482c0460b00f00d64032203200705a60101c02c0002500c10302841d114131079216550364a0003105200c0302154011801110078602c0315200250702442c3c039400340300300e0900122000d9221502850b29640c0c0f070b01060503010480411220840020325140254202c801001c806840600b0f07414942c0328201e203480c0d2a481040e0303150040b242442d651071140c80720080c080c000801808600e0308001c1d0100380700000f100b04161 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 534902086 1250 534900836 534900841
    0x9150837080906040b091f050a030207060b0907021b01022a180a0c03060b070c1a09041401090c0903020a05060a030b041a12150103030e030109051005010f060c05150405030408011802090609 83
    0x681c00809c68040c04020700f801a12495641454001000c1d204006904a0120800d0118182c0c000841e407001d040c42112002070380301c0400049882d1800e1140016203180703001c0c114240f40801c1898140d030120050039020b040100391030140c8042d502038400c504000da446d90f0002030f00c0e034140244c001070600102d11518101166403100d18000f0507100b00e44004002c2c8081c03102010214045400000e4000c00a000c01041104240e9407800300788242422149821050080e290081c48008200d94009000c011164907060a000ca2580640d241104140d078582107a28256030701d114600441c0401c0c04800d40d540358407400d10441115990035206141d00040220801c5500ca03085075044d240d251030804000342412000c0303405400100002080d500608003583d1111030310740d0000303040b14a210211502c45a480d90305641d602c050301005400b40d080000d940c0008040d001e0717680c1d0004e101d241242c1c03405a655242d030742100c10301074000e0150703da044030704803c0d441d01c44210783d041001100c0d8141c190 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 534903336 1250 534902086 534902149
    0xa090b0702060405041e1104051e090106080703060504020708030601020c0a120204020702120102160b0615030a02130b13090b040501050108060d0c09150837080906040b09 75
    0x10300480c4a13292241ea1a42000020300400c10316809110702121000d01140040000d0001a80c203d400f40c030b03005928002d0a00070194221018524814000e07002408c03a03420307d5412501c00750028040001d0548503d0006400d840f10300c0201034190045a0980e16818008002803c0400d00c224080c881e04540710305000f84021713891a1100c6680c116001079451065201207a400c2e00440c1a10300c140d480440d00707000a46002c1000d00c00640715440c0d4242c1c80e0350b03140400040c80171010524480340e4051000586900c40ba6005085412010040304041503441c0d0cd403c680e94400220341666085100f010000082079020300a100041210180155070403c000240b501c2d000500300c80c45000c0218543c0c0c14401404221000f030700645a052100d0a126211804817103840d12a00c401c0c3d1142034645080d184014181160704500d0001c0c0c25a80360008107030544641008205036502c107401c101c80051036641c980140010424030080c252159922400c000200c00d0700d030443c09443c548581c801c03a2a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 534904586 1250 534903336 534903349
    0x100f0e07030c171603060506010e03010e25031b0905011217030a0906020a050418090c03021203040819020f120d1209053a0504030b04030e13020a090b0702 68
    0x960f0300b403000022059a6065803a460440c6002a05911300100034003c024821503800c0301340300706d80070f07214000c21440707490a1508850242841040c50780103035940340c0002d2840140c100700e1441045001d000b86e601ea80700c1c40e803010a01c5040c5441d0480c400c0c0c041100450070b0144c680100b01c0594040c40c034902540300c0e098005030607101000c40000c00000035401c1c000d0365010032142074000c1d00c11901c0340c02807100070b8031543c003074010044104044c0c02e070000710a480f0700410840951180510406e145550700b800081d0a0b00c03000c1d21083e020038007012500032020002107805540720081d00c800d010850050125a844902040c0e024903101c42d40e41510713000000e100401c484c454640800140080c41c0404018901c400f802003241c0140c844402801590030340b401ca00ea00c8e81003107146185108400051001c5c42485070782c000c100240010000700d036290f850f8aa0140c040e00749100607082d01400901010380142543c40841e6012401c4810298802c0303034032020b00b4030070041500c0d140301600000c2c00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 534905836 1250 534904586 534904589
    0x60212030c0901111b011709120a05071e03110a0c0b090d15270f02100314070215090706020a080f090303040f030516060512040311100f0e07030c 64
    0x2000000a040c0a00d80d00c5441c10307410103028032080d580d05c80c0010041003034980e011511540001c28207040f50707030f56080102c2500c4c000c00c0410b00038424620008040d046507080f040224007805000e100d2040170480d00f00c20400740350551041c44800c0912032070f01030180e540c01a0300c68000e074013412804000500f1201486c040d1840c2d00060364540c085400010145181c0f41d000034590344071102402806030309034024110606a01c42d01007000c000841f9200e1141000c1c8070060302181d11050194054103100e60440d11a075140c2c039001c60048000110002180e070300303171034910040c4e0082103c001d2030174510b42c4585d00310341c80d42c0141c010795140980003551034149650241400c800015004e0b50352458908940f0b04400240c10360381c80704c2ea01c0e840300b403c00f42a8031040c0c405018a0024080c4005907284101c19a017081d11040d0a201405a55a5880100500840912801c50301500c1c00c80400c0003404091600341c1c40202d002c904a48142050300c0c1c8000603804540c0c4201ca0510005070068038180 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 534907086 1250 534905836 534905851
    0xc150a0c020f031e030c060a0b0607080d0204030c170c01110c090c040807080601060906050703080a0b03010b0616020a0509060616080d02130e150603150f03011803020706021203 78
    0x3140c060b440001900b010441e403411250941c20440200600d030000c03000d806201c1c0b90308151003135036850100d25001d54901005066209a00300590400112004058903544c1078030507006080ca5181d5446500c08000d542081908486125a01007160010446041014400c0ca00012010f004d512115981c4108a0b030451150000200250890b102e40e0141c500515129045440e9169155a441c0d2509028003074a400101e06031130100b10107029008550300f45038160f90f814181c0e5200b02c0800010501182e95036410f541351200c00c0c0044c0d88050103030200c083c0c03041e00c0c5041186644100b103880e80701a03000d1b500507010b000420501d81e4900301a40c024440e00d00300c4000c1000140303805000c510030b00b10010080d910204940064461105801040e00d50b000c400d1161034894500c901b01c80f500020039035134084003c00001d180e00c0d0a50843c1000c9003400b40107030440718480c40000e0b00303456410071b00d503c0d4407402c1460807040c0366042107072000a00701400901020355203c0f1090885110080901 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 534908336 1250 534907086 534907099
    0xa0b0d09030e0301020a080403110a0302030a0c03021c020601051311030609062805120318060f0408071202031e030f070c030206030406090c0501050901020703061503140c150a0c02 79
    0x401414002d0881a00314280107008543c0c6201e039105c0034081c03034819503044d0005500030030710011060380090b1151074640c00d80c0045051408805c001c071103d40411f41c040302180130b01d100040c01c0080c8220240410101038010780b85660402080c42103182066450710091420501403141c1d00d0402d6040f0b0f90800c0301537420404c555503000c04101500d0000d1620425162241e0050028a982164802c242ca8080baa40d6500142c4242219aa03000e0003085002003100a00010801d1606034001e140008805695505140e03584004ca410039a09500290b10000c501000707000714a014410b0350a00f0043d0303507a030640f101101900b40e90701c2c051050024265080000c03032206010781d20031503c0003168014941c03540c0307141602c1d1440162072264400c079440303d5208030100d643d600030780a0700d03154203041e030080200f503256441e00d101034040300000e0103c40e44c5008000c0302043d04110101a4482e6910052100c04d5855041c4080880d05001c5400c0c101410700049003481d5000001c0c48a454044506 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 534909586 1250 534908336 534908351
    0xc080c210601050f070c0515283606081608060409210207150210050a142404060f030f1410090b0609040b1902071b140a0b0d 55
    0x6031071071320820368145141c0002140d1401048401203035201a03501c1a689a40c451020001d14040e03401002450040c0840501074514041100c0400d00480f8200e480d06280405c2903504914600840e1640b030501e50b181c00030844c52003020030400e0382c02003ca0349480001d500e003141925860002d01d020f018104a180030200b6180e0381d803130b00070000d141c1c5c02c00341401201d408585001e840942005014026000e032040024002c205030626074040055074015000c03106040c5100c10007064010200310320700d5515880d1614a1880e0401180f1840322224001e0006104030300b803480d0000803071034984c80b9505100043c0b0583cae280f0484d240c21603510200181601c0750b5841c016282180d1512245028410812803c004880c01c0c1c1203281d07038a008414954aa4469000340003008004440280107800c3c03900201d100c0c900241070520038040c44000060804085a4610400d00d030061a0807446182540040c007040c0f40d101c1482c49140300894014030306d0303494681602070314001e40c0d03643d07880c03541c1c0c4008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 534910836 1250 534909586 534909589
    0x1080903120705120f0903040b07060906141009020405030a0609060e0a06050a0608030c1e0a0f0c140913060c120f050403030b0111061f05090a0c080c2106 68
    0x640705640000c01500c203292510081c02016504041c0c10300002c80031044c00f2521402001e8415400b441011003e1441c050614108a007294003101d01115803035900d4803090046011881480280c92080d104040d0030304109140000b0035255810484140f44104020030055600140340114180d0220b004912450789007082002415514240301940c020540c00d80100001544007621910941c07404100180e21141619a03a0045601880d95a0310480ea40b000c549901e0407149680c41038041140c0c581c400c01d5030354000c0c0c0550001d08031125000b0780410321002070040c01381c0000740810788040d01c01e132070903207200c4802c3c0c00018009468580d80302c6caa00c00e1588541a02d1540000b46081844023600b009141002040c007242c084c0d0000707242844418566100d142e800062894680c01424180c0351603d2254804444400003400c0c404018800292600e82040341c0f842030b4206540001d84040e0b1500190600388001c042c20110780b07041222942000c000360009184018507200a0350a41d142d40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 534912086 1250 534910836 534910843
    0x9061501121409010b0301060b070305090904020604080d0302030402030d0809031b19110f010305010b04030b09070909060203070e0604060c0b06040908040b031504060e0f15090709080601050d03050405010809 91
    0x26202ca0034072251801c1000c500c005400aa19050003600200510741d03692035032407414090103030000c00040e01009807a5844c0390001440e070700301d0b00050100d8a07055441c50210f1906c0450950413010a40100c200030551406200c1c211090445050540d06480c0511340c1e5501c0c4e200307503801100040d401e02500405100c0030052040c20f21004041c0070080c00f03050a00c003d0629404910601c20390500c0411501035211b030258a048820103040d0604050942d0b450074481840140301d0481445003100000b40d658040c0141c81a5a001d0305005a4a0910f002c0c010000846060031030702803501007004000540e1b0000504d543c8a400c14140b0890b501c90724000341c040c161010000d0200c05000c607020910200c0200110b019100802c5840800c070030940600040c4c9030203120710100c0701021800240c0250181302e0141d400b2400312000700a50180d100019801d600036580c1c2e00005881240c1402540c4c01040f0040c050841100e107180c10041581c0c0091452083e800350034100103c800200c0e58040c003c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 534913336 1250 534912086 534912101
    0x30f1e0905160602151f1802070503070b1e0405030d09050703020303030103230c10080a150905160512220804030605060a060c0c14060408060a02030f0906150112 71
    0x1041102d4020303550b1030000e55440f0983c0054281c0e8001801052613071502408001c0c0032201d001d40300041501d030000072810302c0c1d9031055901142c4d03000c00c00d090002e0000d00007010b40c44d11036501220307141000034141c64001c80c1c1d800c1a829074200b101c14400401c9000054510780700840e0b00102d108030640c507245080904982c002901440048004403c0261440c0e0800b0210141c83d5402d0300310400800c030030760f107070702114055801030107804140141a200384101d44c0d216201040201c0c54900b111b11482616000350310003071080d603566041c002c03c00c254002d44000101c65150079814201c055285030107010f005090011441801310300440e100309070150310403149800070226901c0c0c030b68030304017031028150841d0043d00c01c0e2802c170070102d80c560081d140c80c1ca500b070b006242d00d10301038107010104c0c052200000391036900c81414000002d00c1003041102034450404110096100d0802c10030b902c03a2008098584c0110742c01c2141003240c480705041e0740c180f0250003440c150a0842c481d0038a00c0c000d0001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 534914586 1250 534913336 534913363
    0x103080c030c0a0501140610080601050a0302090d1202061023030c15131502031c110c03040311060304020303030a050a110406110f030c0c0105070203010f050f010303030f1e0905 78
    0x7072003903c405221043d40904140e001051190000341d0b541ca0070041e40c140280c80a0000c40c150781c022461651080014240880c3c490070f005152208100014094000c126800c640c0c2070700f2000c0c0b61214070760500295030000800703910800b20030300782034083c4003e290580030300395942810949034695035400c0026a940c2310010300248590320524400d0700e82035101055003c0c0d503200a000001d00420000354840064003076502545c20301410051103017442014054070101c0a8807242d0701004107820400072b00600c0d2151004507503442c91072a00741e61200200d20b002e4800c4000b44200320268070040100ca0b40240700036000101c655440d400c8034014944040d541201c3c180114020900c1d64102c0c0448040c0c2c50004100d03070900500140e01584c80c8604102030700203030800e0f6820300f00355008201804c4076a00c000c00114202910040c400d00300d6100300d030b140000082c540010018142c040c46042c080050001d0140b0009802a03c204600d507800850182d4240d551001e41e8103111090141d015010007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 534915836 1250 534914586 534914593
    0x3080f040902130f060206130b1b0406020a03020c040207080f070303061d0f0f160309141b150408030306010c020d061409100b03060f09071e031e02090103080c030c 72
    0x2c01801c2c4400d0f480481c014011003944e200000309256000046062103000503002c540c061106c1507984140b1081d015200382c080503d195201c440d080500406040640f005a00402d18004603040091130f240407800c11501842c030400190340821951001c0ba000444c0c09600c0f244e80d000c1e00e02e011001401554446141c140400e4444452507004c40251402541b07041105a62a212180c0581d1100400c0d10680034070110039051006150003600040c503503c5c000d501c060002c00b2106031503414141c0c115490b50402c10014100c0d00c10b840d2219000000050413800c80d828a428444055580d100c06480c55042c46600c400c1c200840d918084e218071010390050701400355059102988803241e81c2078510b441c1d00e001d041e4040060142070300c0780c0c507101e10005000381584e850743e103c070031500030015007442550b000308680401e81294241c1c0001543d8890860064038501d542021003407201e0601d0843d00000a14000201503690501e01e42e054a8001102030360f0346c100c00c05943e103103104900c450841c500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 534917086 1250 534915836 534915847
    0x603190609020a080c120a0f020904110a0315080307061109100c12030905060105061e042306190e01021f0f06090c020a03050a020109021503040c1e03080f040902 71
    0x250140c001d0840f403c0741c3d0720303240d41d191130750402c5a010703000c1e46940302c0d0300c01c400300c000411941094100c40d85460940000624000c0d9950100301519807100c4403100c150b00c000782c2c03c480264940300b800c883c0c0c0d04010040281da401d201c3c1480c4c90348030f9030202400c465203980980007210307505d4048131a5408001c01d407809010306060040e1041c02c1d100fa00b0364850300740d14080390b81a8041d025032002c0d650702074003901403a0300b0f0200704140d80d007002540c604003440c4e0300e8030141e01a00c0540100082c00c040d000e031070368800c415a807210700104002d5290f4011207046c000040301074000c61050241134840e0520742d03032441004004034036001070b80e00d441c01110041a40c00380001420380c80001d4514a05030b040c0921902c41401d4002c1c0c614201004005038441c4580300046032140020f015104507070302c0045400412030300010a0740c1110003040720080e41c00000d00040101035100c500042c01c01140101c0b8014040d02c248003015038030711005e011207000142e1940b0181c002c804440242c000e11408540f100d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 534918336 1250 534917086 534917099
    0x11071206230105100c050307060e060a050a18021017190e010b090609040f05030f0307180302150703030908040f0303140c0309040905010b0a0303180e011406031906 72
    0x100784000d054020719034100c01903102004440c54040c180d540142032228015408242216225100750007a02d103400188a000c000410500039000384000b103400800840c14001451000c4410282c1a501d0b51443d040325010304050005c5446e441e2038045511699408400c007080e680c3c0307058004400b00180c070660070001e00700d02c141001141094403040c200942c0011041a6089405038880154404006c40001d5103910306000c0040e0722030310031004034540c040c00da42c0b11443e5410171110900c0342c510100c1002109980030881d001000d511240c401d21580c0f4640110301c00c104040c01a044c040d000113800018507010f030300465074240d408010181d40b59aa46d10580250307102d8041240080c011121000f40c0c2004001940c101d400b020340a141341810150030130005018a180c1100c1c255201c00050350203070f80344a5680b000354020f0704e0700c0043d402590160310310102c0170741003a492050346c80c0040c420f502d102d5001c80a404001d40344603940c1c0d224000d540036943d802e004405d04407800d107400030460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 534919586 1250 534918336 534918341
    0x20a140f1026060d060c05040b12070807081603050a020c0618070b030114090a110a020d120c020a06020a020304030b01080a0201120203010509130c1805060907050a0f11071206 77
    0x2d07241e00091001008032101d808145200042e51201d5000014410210106140c0ea10164401489050083c5000d81c0c1c0c0f00511309a13004200460f52402000f801c02c0f007415006200da0354461b406191580103485d000304c42603250302043d82d446041640d61400601c1c900d030154100e0354944041011940e05150410349082000b58159607a046809000d0001629007100b0050b07e058444e0b05509124048605040c030400c40c10003131455000a442e684483d045070b14200041500384219030242c04040c81c9144054440b09404118014982c03030010840910b40d40402c0c03803942243c0c02400565601d0170030508a1850165420150480d0200b2000081d000000185508914402e0329020082d0884480d000200e0001344641c0b034101c407002000504414196050304103c0b4801c51529000c60b4641c0f46d80500c6284062060240903a190240210f925040741560750003116440c00528080454000410f800e412180d00341c00d000c110407407008005002c0c800400644100b40c81e1503940e00a07420320f00b01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 534920836 1250 534919586 534919607
    0x20c21091c051014040f0206070c08030a0f05090a330c0b06030118110d06050a0207052802060309120706020702130608210c19140604020a140f10 64
    0x3514820741405103c0c00d001c40c02840300709111a8043d0a07103944035142d442084d00d099008030703407200307007044503074005202c140031000030300640c50055442d10070300280600f18050100e0a1001e000092081c401680d89148141003542d00c0b401d40e05a6407104400003008170142d20040171811310003682540501e070741c01608400902d005d4921100b0700c1d2100070070305080301d085480b5581201c1070800c0d450041500d041d80c10b103c5c10f8024142c034156204903100e400803114156801c0c817410381c0002e040c00c14040304100c0700c1090400e0f0002c07004030079001903501030400700226009016003c04000140070300001e2040020440c4901d02c45661040d10b032514000a5021103001c80c03194680c40d0740061080310383d1140d513055401c00c100515454101c0e20801c1120100040400940300080120307001c40042070000301c0c0c03000301c0d00382c005000194520b031215042c000020155120350003001000056500c3d003981130f00f200c501e401d4070001c1c81e401401141c400003218603100e41140440c140507000700c1d8420348101c4d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 534922086 1250 534920836 534920843
    0xc070b0c0a03021e0c01031d010507110c150405091306090501060e01140d062408060106020706021b0f011209150c0309030e13090209040c06020c04020c21091c 70
    0x80e403501c101031003084c0b030841c0010003200c10380c06845d85010342d5000b40e001c0202c000c500819504007504e034200c19800e6540407103e010014a8a1b48103540e00c0c5400c1000c1c03451140100c2c2c03903280e0b1b0120565100b1190240d80b207103900c550003800100701007240c214804600190000b000b4042c11566007080307800380c00b541c030075041c1c005e20741030000030745184001600c8030b001d1000f440c00991404a46a4030040c10074007440c0803840015240700d60044850149400c001c20144020701020340c0340610282c145500f9a1040040d90810400b500c0321401c081d640c1400107038100c2d401c0c40c20301d02e10380c0121404829140d040c0766891034240c1c0074044c01000900c40d01040c00180080c0940c401c0c10500b2400d661301c1110040c01b08100c100f40310300c0e0745081a50f0045810360440d0014200720f00f50005128aa801d5400740c4c0c1490b1044028404e40798140800140800161003c0d85000c5c01070802581c1c500c0130030044030740350814052280c00b6900b210211034600c1d8005215001d5006440b4003a0101c2c0340c20700044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 534923336 1250 534922086 534922093
    0x30d0e120712080a0204050319051b0a0621022d0405150f0d230f0103020d12091e06090509010e132103020c0f070302090106050c070b0c0a0302 63
    0x49025160820449001552010240b451070b030740da0005030394102020380b061003819000e10002c65291400c01c10300880385100c488071840352030703d41441810501c03502c0080c110115900c0c900c1003da16006440411124281f601d101c1600251a48041c1c0c1d41000f03110200c01400082c200c966403200d911000081c1030507582c8543d1003000d440c05002c60b0b20541c820650000d444606d60000782c080e0704042c0090030702249100e8a48102241c0410444a15207126110350703290401c403c64101d440c0b03801c154000e01d008843e244550542d00022a400072201004140090140c00149000d00c2100340d00001e0040100540303800312010a08205031003c0d0081c0b0b0009540002c00082505e4094180c030b04135000800c0030800c070b440794070408000400c400d50030303a07040114203540d4880342400b041c0d26501c86c100750750041e02c41c0010394a403030426a45103080001d5500880c01803000d6500c400030701341141c038075044c41c2c0d55800003641d1160418029501c4181c3c00000421a90342d52500421550711140c82a8240c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 534924586 1250 534923336 534923353
    0x30305070e011d010f0201060305150f09060105150a0c0b090d030c02150403030209032e06080a120f09050310060906080a1208060414041202010e0f060a0b12030d0e 72
    0x110f5070110380500303200490107100c09a0700c50707501071282c40950060078400895403e880b600c2b602d00d403a00c103040000580c41c094040081102c1052040380d041864040074010725458500011b09200606114000d290f00000b42041d11070700139003543c440d0302d80c40760000b4541d00d8031154140d2102c00d403400d6400400e05015550312040e102040c1c0c04004024058080d44075200ca48044000b9001800140c2e010b20440b16034140807048107c20700b44400e80007940b0300f0300c405111200b000341c0f041e135031103004940d10010a10000802d07000f0000c850305003e28000148607032409040750640217a038032168041c015544400d01526031508204150b4190040c2845540d0707a86030019a9800650717005045103a10f01516000c4e144150364071900904024004500c0c40c124010403520600c0a5804445030003401d03100301503064081c020a052001807030050300d00041e00300c1d111511110300400203103410384e8038040d40d41c555a8420403422840012030417642c442c0724000c50b440050003031a881070180d1003000d14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 534925836 1250 534924586 534924589
    0x3041e05130f1a0102280c1205070b0a020303040311070b0d1d0a05120d02090907050d0c0f050904090c03060e160f1d09010e030f0904110c0307170906030103030305070e 74
    0xb51005071030300603401032113a101ea40c060032008800450040310011b42011110002c208810741a4010300b10400a10050303d215190003458000e0540c0701c44401c00e0184008000d5903008002d481d8031070b4050401540408400c42d009080100c15008410602d0020406c80408040343d0f010300303c5203009801c0205041d41400310f0541d03075004404001c082e640700c100740d683c080c0d030414054044141409005410f1500c00d400083c3c45090071900742000500120301650844c0f040d02615004010904180c100d4100e81d140080440c03045241e064080d9403940944001c0200c0d61484a00a540000003040310f9100072800d55280c0f4980e60201d0608a90760074086010807101850400302c48a8048111901c6040c580700c2c480420010002900c5560710301201411000c140000d00b50010816091542e07080d4820421007190541c2500c8240751405000300c1054000000417152050b4000e60745022940c40c40c5c0408019124000340a138018002000000815070035801c80c2d03009121644502000c00078140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 534927086 1250 534925836 534925871
    0xe030f09150903030703050a091d061e010e2205040c050909010b011e110a03021e0a12140706140f15010903060b1c050606040b03030c03041e05130f 65
    0x407509545074000f0003a1742d0000b03008000801c4428661304188642c0c566640f0a8400307881004210307a000032107882041103900c1c006001c0056a0380000c00812000541d100003481c2c4040e00490304c2c0254001501200000c1d1407054085202001d01d070700b408507242c14500109000c1d224400d650107a0310714404a043c00d50180550002a4010b075201199911034076101040c00d060081c4280074031001c0c01001410110902108480e03d0203600107007a0096400c000d5400e140d40c4094071080342d040001d0311400075405504950113000c0038580030303108001c20740200360300388210b82000b0030142c580b80000850b210709082562049103800d010341025a118030f040e261040f4050b14440c0041c0080c04140300041d071aa000c18030785900609402103d0304a032080a1915442d40030603501c5a200c0d00402c410351605003c1d00d9045c140980255060403155104541c0c1c0340261f01500c90304c0800c40c4100d140c5811070396907610091000170401c81499503031021640040c4154007255164900307001c0074981c101e5811 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 534928336 1250 534927086 534927097
    0x20f0615040c02191e0203010516021e033112020102070608010303081807050d0501020702120c10030e0109022e050301080304061409030604031706010216120203010e030f0915 77
    0x6030801513801d0101e039112040a0000142012580040424000562024403516100b51207a0190402030010381034060301c2c0842e51040c184803149c40c95403044450300e021041d2010000c0120f654145c010704000ca4108051801928040403103041030000361814404c014110075034001e8080d0b401481d200c29084850b201c0900003d00072400031000f16a91040341045002d1102d10002030310446a15400061411808140309403420307900480e0701015460b1459000e000304a00000401c1400010004100280e203810a0f070010306607611500031074440e082d002581110f5009100d103ca10f40484440001c084400b4112503c20f081e012071504094041c90031203040c1c1d0440d03c0118102032404d901221103808a40b0099078803c000d001900312034500304442c90241d032003603c940031455a500d031225003060004207558115403180d02821081c402d00010072042d14042e10005810101c2800441d01400c244003400b1054800010041504200103000d00705800c070807104041095440c0803081ca203402003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 534929586 1250 534928336 534928363
    0x307110d0f0e220b192105150705031503010606051912090609050f0a0b060d05030c070308090a0515040e1e010b041a0a080c0a020f0615040c02 63
    0x40603000c0441c2401042080b205040080840ca0001110f0391881002460260b0b6200c465072031300c149680c5440c100711030240c40501c2030310300340c011441c0c100759440310b1070f080c101925a0144140c082007031100c180008200401d103044112450308103050700034907540c0221007641031300c0c005030601ca05524046c0038040c2150f0380c0d03540303450400e00072441e00100c41c1841c000f40024408070344003101c4000d0040c012041494007076040020340d2000c6041c00c1c0d007040115044000315400410f8141c000400801c10316803c040b0a50300010000790600e0a41e2640c0f09a4040300d0062040f15800000c10000302c0c02000c0181f41a1410130784541d807203050083d901107400e2143c2c5040000e0100303000c003d880e081d60039030040058078119481400d03100580180310081e08a040d000c03500040600c034000c0346600740b0400c40b1003050010b14140362204010420031019040092103140080d106501c14400c1100800840c151000e8503400d0070320b0304d41207078154406995207000d14105408106640d002007003141c9007000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 534930836 1250 534929586 534929597
    0x306100e1302031008060c070204142a04080f0615060a0801140103022209051302060a0806032409060108070f090b0102011b050a030506090c1c18080307110d 69
    0xc9182610020f0342000782110342c2506107100009952204204d0140904038421410340c4d02c081500610090703450107034950700f242c0c81140c14489844010030406010502100540c01d03a200502000d000070721840e4800380e0588180c400b4140c00b040003052240c020b40b0300864801070022081f00b40611030082ca2101c201060b40500104441200c1c0d02c0907040130501403500628140840c0d07a82e41b21821814031160156990110030302c201005441241c1d081034840540c006450841d50020740c2600c603141100c070401810001103800c5850420440c4042e800050840c100b500702c0004c18202554102c400d00024441e6600002d0780c04c4011594806680c52501e10300301617424007885030050b01542a120341150f42c0c410f000355001822410f00544080306542e42a62a0b005450040c265803011703022900c1251150305000c1804443c404540268070501c42d012803180030762124200801030103140301e00e040024402c150030840102d00451107088103480b101c0d1440c1400b0505a5107050b0114084040340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 534932086 1250 534930836 534930859
    0x317130b1201091107110a0b070807170304080f16060e030d0b0f031c09030606140103050603010b0907120603020406030b07080f07020618160f0f0801020306060a1110110306100e 78
    0x611014501c0b01a590103010001c50955a0308ca80105500032501981c440310701090040410120f40d800a1029010710030301030542c105522420560302c01d0981c0c1400c48203002a201d5424201d401800c0b107007541010b41000051080d080085c0c07282d00288001f0021441c00072000f40d10306d000c00340000800c0003d0000c00341401004102054031403d003402c0b6081c4080d1a40000000314540505070203800880700c1d0a003083c020500160586501516043c071a074107000c000c03400b9498a9414642c000003e24100d5003040d000e0070381100500140c0c00194000f0f05115000c01404076403101c050080c0000c0c1e0f14030101d595003465903407480c0c0b0b041e11309900582241d0702140c05200d0503400d80f94210b404206075400c3c1c290300e040512009003a940040030341408220104a0440003403040c00003092030b60000d501d9071828800050007407040345041e4060040034001107200980812242c1206000304004000da015000a040f0141d081180c40d02d110300d8aa482105085100320b5034100c0c1d034000944005440c0c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 534933336 1250 534932086 534932093
    0x40f05060a02190609020906030a0b07080c070c0e0f0f01080604060207080d09051608031206131103070c0b0a1e0e01020c0a0b09070611070317130b1201091107 70
    0x1d51001c0341080461040b010410000c031030300e503100d040345807055000181c0e031081403061203081c120040074079100f900305d640741c400401c1030407042c1c6070701510710f28181107251b8501e140002e00c1e01035424068420814030001190388203041c070445014507012000700000750b980b071002d0740000c207090040f064150042c002040002d0140d80140084a1103032802609000f42400600d0445001c1281900d490b800045800d0220450f07101200c0640f5690001e54030b4141c0355800001d00c0003020700791318052601882c04020a07001c44d40070000800700c06983c80c2d80da0070719500003409045001d509852001013040400c03071881d0a0f1203000c0010849448001203411912810301c02440e00d07001400c0d01d55001c00c460154400107000065400b8440c021040b81e50410742416440c1c910303107400400612079680c208082288002941c602202c0d41b00c82c1e2040102402d42c4040418099100300036403080c040c210101e092035084010385503103890000700e241aa0307600c0b440041565403000540500c3d100800200021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 534934586 1250 534933336 534933349
    0x501060b040605041403120708030609010801051608060a080303040c14031c03150b030a060303020606060306010206040f06020d0f060513110904150510030c0207060c11010503150a080c0312040f05 86
    0x1544001816078011f00503c441c0c1f800590320006040310805000420003480d458400005409041200020400382c0b0305000ca65500300d41c041c140d0001c8c04414030000b4005e50b03440c550704003d4040d09007925144c0c10149411108110b0314001c22201301940400807000b4240040d143ca554001d004070030490b000040415001414441064400405506808140500204011409038070100300000300a072860500a0400d400a011548241401c0081c040a60b07070010b100d80d000b58200711410b490382c00510b8160002e1150100d170032002c41c18094007104400d42580124100e804c16150344004240c2c0010b0802141d5820200f61944042800752901170304180c0c0c826401c00010420340788050740c40e6800075610f80014600b44d400a601c0741c403035005059050280100800082c181801c0400d101e6603005030803200380710710a0400030b0100004a909650043c00002c03240d001d000180b4107919405410389440d05204490700078410124803101d03042919048400f1100f40c824101803490900c0e08101c107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 534935836 1250 534934586 534934619
    0x150711030708160c0b0408011103010f030809011e0e09070302070b0a0c0c0804080d031508030a050304081209070906170c0d020109031506050f0a080d03090311030f04030501060b04060504 82
    0x144180f42051000155021503c0f04c0074159244c07059031a140f501200a0035100d14400300c4807105402e00040042c200d00041417001d480e80300e00c4440c0c0b90901000100c40050310140e960950814459a14680316000084002c80385810754900c152a556440150b081e4403c1800003005105000000780038880903500c0015042c469241c104034541c101d40b203888940c1c0041e00900c00341e400940340300c3c1c0142d805101d01031074803141581030726030743e450300a00540f00e024441645050240c000001001c010103801254081c99501400b84c200b03081054010f990394505010b00040c642c80c095011070380501c0040b80b00781c034a20802c000c00c0f9160210040c06540322900d9822814040380c800040300090300c81131601206241071200180d002e2901c0100800118820441802415824400d01c00c40b140854400c540400c182800b080b03484244c942103504045680403c0d200d0f0001184101229412a0003002140d00880c0280310054840c070200b48030380314511900d00070910800c010070090340c05c40e1355000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 534937086 1250 534935836 534935857
    0xd1101020c0a030305030f0a0b06220315021207050c190f0c0605031504050c091e0a0902090118080a0b0a0f1b0206070207180911060c150711030708 65
    0x4005000c42000702e280c00079690021070204d0004010460928124200e86901c1541c504050040c550b0140208040744510b00f03c029101403449581c40541c40004c1e540383c010360b44606440c00c1c40c660150300e0402500a0300d00500d00318260004503691921400030b5402c2500020060051607010030299412012410301c100c80b030340c40182001c408140d0340b1103c44020a100e4440e80d80d01d18003070001d9107087c000301ea400c0b445076150009104a5801c4038098520b008030070784188012000e42000d00d80510368240e0300d039610444520021403507041c1c64001d01100c1d00f0a88960b010b03010700b29400448030003540161190380e40310060101c04101207444944d040780c03000c8800920b4405141d4000144c80c858a41d00406079008200c0d0400250704201c00d83e805882403005d8820710703003840c6003900d144209030b04c001c0300c4c2ca0320b0326004010300c004540f43d8084170400a00240c0da07488041c1c0f545072507055581d5042801e8500a0000780040c0c0581c40742d80041e00c0c600050351400a04d40d071070800c00d800032403001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 534938336 1250 534937086 534937093
    0xf2512031a0f1c02090f012103050d0e030705100b0109090902090622060b0a260403030b040e07091d15070c0c05090f01080607050c0705040e012c06010b090d110102 72
    0x101c01681314154050b0181b4083d125445803581012900c0124001102500c00045404131440d00401e5101003034031112005407401090180a0b8641907245004e07841d0054202c3c02400f42c0704100c6c0b01785034420010541300381c80e8130401b155910519401c0356501131010307400001c0c040000c4c40314a404034420440040a031048101c201140d15450300701c8510b80c00c0840c10910000f4a90300d02c540002c4800040b6070360b20303000408824058454004104003070402400e00d52524041450350b610b9070070140c060b800c4c41045568240d80c8101800c0600002c441c030002c03c41642d440c440c030b411808290043c0d50304806044100a88880d54201c5035050070780f4041c1c0b458650706801003a03030f60712160710f14083c90007841c41140c99410080a981007540183c0300c0ca0a0080c1007240c0c580310300f00411070b1412a802103c0020780c5068201c02c990140011000f100038900e66001c500801090034000c0c0003614004004a8100c0c0c0e0b21040320001078450202a1544043d04d1001d840c00545010908042d104041c81034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 534939586 1250 534938336 534938389
    0xa0b090601181412150a050a0b030a030807110f030d0606080c031f0b03041b060801120605040c0b220e1506160803070f1707050f2512031a0f 62
    0x2c4508017001260b01c4a855a04071045c00320b002003a00030250031880090f03003082a00224000240c1e03038050044002e06016620000400d0b041c064581981caa0581e04140da90304130340d42c05415101c1d4051200991414504840440c0d400e21130340d00d40f486080c26003409851921402d1880d00603148521501e00c52030100310000c134040440e0005103002e1481500001c600341c10030300c0e91085240041d000b100400c07a42034010000c02c0c10102d92851810342113900005e13291590300b00b05a80c102240c211040c04e001c00210000804011002c00c0701c011001114a010207488030180b8155500642d50903544003051a614101c40c0341c0b090040840380300c03210012224a00c255107011007030f00116101d20204543ea08940807068010b4603501e120464100000c80500d42040043c08901882c0142c404d4110041172802c006035041508034494000803264900000183c41d0500041c2059840d0710f0001f0309115801c45041d20840d020710400070024143e0800040071400c1c07200c641507a104084e00340944440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 534940836 1250 534939586 534939619
    0xf0b0a0c26040e06030c130903110114010f142416080301090609020408030f2b09031d01020a0201110102040302040501121101020a0c061404030b0a0b0906011814 71
    0x40686051074038159407200d2a01510043c15203004003018066041040b4059141c3e9030180e107000c400c0012080010b01070600d00342110b08480740c2ea20341d11998270709401a8900b02c40940c416048814441e0b031428126210607507200711140c00c0a040d504102003070412040ca140c2d00074404080743e540da500d241003030821000d004a00664001c140c58210000005001c0c00c0341c036000b0710740a4542c000040d803a1502d0010b51696910503400d070503491f00400716919216030f0031918024169070f80010700c01405000244010028030206404802042a808404044101508040c6150a0141c01804095400e81c005581050707401c500e2403019582088040700594981c494540a0610824100c00e00b0410380350003590054503074036950541d0b2207486560300042c00040c80d42c00340c0e1021700d4035074031a03c0c0851100c4810700803504014a100c0f40241080405242c82d403202451140844401070070342c654034015550300101142804541c4a0384006001e00c50041700306142540003d045641d6800580c0c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 534942086 1250 534940836 534940883
    0x207150818032b0c0507080903150c0c0105060f240904020708130f0321020717010b0103150510050f130611060a020315040903031401140a0f0b0a0c 65
    0xa94149010030180c4600320030b03114880d1080f0340156664000c004681a410340a0501d00800100501c400307000503800d032180e1418003141ea2250702121103803042d41009000d5050741d4000941e10309466180c500020550700c1c110945219010020304400190602042014032a003101c1110404801080105e800b150b1103610041c880b003409594202c0d11a541c02a05944e61000d9510600c40c20340c0d03100040c004100d950f2178844805e1004886035840e4907031404240d0030922107074051305403813101005a80e1642819009150b0b400401d80e020060146030b40b01010f41041c2c035000e22600034a80c1d4261880c802d0189000f8401ca4842c443c41b2410441504041c55520b5001d401c00000500b030a0099010b060040041030742013825200250308600d460100d194441011498940c841d40e200c000740e00c1810b02030741c4a500b1404114800070340641e12400f4039107000c00d000f0001402000d42d80e00001d99901c403105510144c410105549203404c481450880b03030312418070416200071140e02140c44c00c052011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 534943336 1250 534942086 534942097
    0x10e04060e1f0f052b02030601060c05100e060711070e16090605030105010518041808130602030702090a0504080c070816060c151d0115080d020715081803 68
    0x1242c0990814290034000d440c20500d035001d02041e1001d11000c2c8a50f640e90081008449003441100e2070341a2080b05130382d10354081c1d0388040d4250182c0c0001089c80c603400031240c1e400d14002d80071204c242c01c150341c10340300710781140e800c0c85c03200c1d001000400c00f180d1041190110184d40041156181502c03068500b04011090341c41b00c4803840300b2808003100941107000b28000700b6140c14070070700719894540060254807820b20700308805440140018519503490384039507a41c0000c9242c0c661802031500e04200b269021804c0c91000c1d001c807490000e5028030000846080a5000c0c120346403549885007100042c00c009042101d5804080c040e000140700c041080400030543c040007031000b4171030564004d181010942040c020018100b400340d000c0780b03129020400790011035000164030000c8a5000c0380c9030301d01c507540c3e8140e542030070140d0207200f24000c5107070155014076041d106130050008003643d846440d07101d41819080804c10740c0600a0207213209aa10500070003010350340c108030081c0541990300c02c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 534944586 1250 534943336 534943351
    0xf0411041206050601020a08090904210207030201030e0703020a030206210a050105091b0a140d0f020403060c111b0303190c050c1e090a02040509040b01090f0b0a05010e04060e 77
    0x1d00420100b070104601442d50000001c0c000707001c0780c01c503548861026109071031381113001e416100c0104042010029000c00001100c1e1080b03030000500c0c0380025124440d034801680028141401513000b5100400c412080b654010400d440d517510710390900c40607800441c42c80c240d240ca5190784100c460010740380b9a110b02c5454400142d00c0d8104000c202e180a0b020304000c084022200c2c5071809601e035071040b01e9000c000c0e810030128041003485410390341d2040541900d0854144240100012a680c0280007503a1040c0390a10404a640100b00ca2040c03d0359205110342d40700350000406402e01e040e5520003040041d080e0703441d010030a1842d80c4249068040c00c0d000496208024081c00b60034080e100301e130b0001b01e8400307606a002004c03141e0b05003000c00066106e0840c41c0c4c08141543c4041d4125001044080c00b00e00046c501801c011094040922861545a003003032050081e03201c0c68400c0030400c401c000d142800c0b080c00c140044070400d40c800040b80d0016070782c10b8042030704464003900b64440ca1a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 534945836 1250 534944586 534944609
    0x709050f0906070305061e0a03142a030309010f090323010b030c0307172109130209060706020904020706050a0209150309060408030603160906060e010e0f0f041104 72
    0x4107045440c0c0340000c0100305108052400c13007403000130380c0e55410540f8040e0f41301c858030009040a60000d890444c4075400117014003903d40e6088007006022610030f045a40b01e21054824190036040040d240d294241c1c045d9154004101c0b85042e580528140c040d01016032070030b404483d4690340ca080c0500c1c1041908014a861385107017400d122400d028682300000d058004d001181441000320341c0d20002c5004030a4290705000c0f4000c041e120070007034031845003502c181d44801500420b010410b6544401803807805141c1100c410700304811280201c072107080b40540094907001c0035442e11002034105810a40d03003e5020000703400899214040c0c20b0040030314000041c0d9548500b0304100c514440340b0b1001144500500401911107000301d200ca42c001e4000c541a03550780d030740c00000382c10041e920942d000f00205980b0f02061004003540510283c5245440b003001110350400103449411014900682c002e03c100c0201440d41440a4040c0c01d024018002180b159448054103d26402681042a80302d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 534947086 1250 534945836 534945841
    0x30207020406050f0109141302070807110a0b04063e0115030f08070303110a0905010207120b06220221060906030613021801081024090e0709050f 64
    0x2400303202e244000c01040f1030481e9441016000a0300103c400e226200101c000c0140c81e42503030b1208a1552403200d840d480840d501c9445180010b090b030001001030340c0148032180e02060f070303091500208068030840d650890800385009805c69007000e011407080007502d1031103840d1050f20346c10a0790a00001c0500c1241c0360550b5481d11040c00c444508401301c0030f200f030b000010400b0803a5031240d031034529013004040360b0707540d0641400d40c0504440c81c5a103440b03100000d03840700b219600600200540c0c0003607080c1e40c0c00030703a201c0014070a101d00c0321010708409441d102141c00c41c600001442102c0060440d5a520321f00c20601c20b0049800c048000d4901144681d070703407900c0c011019081d60340f02071b0890380089175080c2580400c1d0b55000003040d444022514000d85420744d941c40f0000050b0784120b42c0c20000d41d60f11044619210744c1004500d03a41c050520705c240c00d50010200044a541240c03518824000386442558409080400c801d09c11900581c0d8012170000c145d4028988540350900d1545040e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 534948336 1250 534947086 534947089
    0x2010905010c0e0a140a050619030c080c0a030e120a11073f02030706050903010b0901143d02190c06030b03101b0f0c1e05031903020702 60
    0x16103448400000304803c0741c50314000781d62412001400d44060032140d1441c82e22001c0881d1031820960000359212002040204448401c07102e801c945821980d01400791000c2c2000075200180306440c0c4110400c801d0042206003440f903400301c005094030208540965400d0041407000740e01040314039000030001a1001b003d00c9080007040c0050040003070101002012903404110110440744036008103503900c0340074448960030700ca40ea00050b001419501241d0744d4941c0a81a40c0c1310480d505e02a50a00d0a6456186400e9840c00d040710303051912840c0c0c80c00c3c50020482c0808454042158541e1909040b0000383c0141080855903480404141c0108002e51406840c0101e04a1303000450349a0610600008170791607503000885481c0d080c0481c821480c6c90000c0c0c1006601c1c421700c030043e46003001c1e001c400c06010b9807560141c602506ca80d402031650720000c40c5c0f54141c40c91702420081480c4000a071414030034008200c40c0707000304142c1e41030460040f00182d4030b4041000c4180000e07004142401503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 534949586 1250 534948336 534948341
    0x902010e19060314010e0f090a1a0a05010b07120509180f060a0e01150309020f031903110114010e04021f0203270d030309020102010b04230702030901050d0c0e0d030201090501 77
    0x41c90013541e0300094541c50200024240e5400620119640e1100000704030f010b1420884241050391000c1c161500034211078800c581c081d401c03955908460305000000500da11074030201c902d030703a42009140d00744a44441003a10740303178444000e4941102c0c45039440b091104002e90400e008800c100c1c0307000c5c0b40d802e01c8401c004412146400c0854a90080341c01049001900320304a0582c00c0d940c00c01003a06041400000c0070800e4680301560035008100108000e41040303102c2080e11842911640200742440c14801e08844214813a010303400c0d0700360300600076a010601403aa02a00c01441d807420100c0c81c0501c102c40326103680040c4003682c07010440623102c2140594001c80ca600c0b00001145001c107034000601c036854802d0000e005c7c19070b2801d2900669100790412281c40201078000d1140c5105017940e0a00d42160102c0c0c4088451450041408140f000c800c840240c1c00c140c0d2502d04000c402080407004115450984d01404280140144645c58100d80074a545001c1e800009107000542016403e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 534950836 1250 534949586 534949601
    0x305010c05091305090304121b080d12020d060f03050303160e0904030c060e07140301060902030f0f091501090209120a020306010611070e04061b0804020a090902010e190603 76
    0x1405410700c80001c0c2901c4105101000c20314040004c2820381320000c040d8194850754000d07580c0000d480070344d40c0500c2035500c00201d421036154900c148495407456030702d840d81e0b08041c0c03610006524117a50301c1c1021041d0007400f1554800500010b00d1644e0b00d81002400c26258021601038002204104412035620b084818030303121420000703000031483c00043e0688900900c0103060159502c01c82003402a1540070f805803240100c1242d003540c0e112600c426218846607009482982400404142844580256400307030348000680125500e4064038980d44000041c040341b0240704584a0014404e400f50300a402001418001681c456811050100e000c10030102039056a00909244005840000c0c021341154020326100740c5c40340c0e1821265080c1074683d4054a5401030301c40500c01030144a0344001d103901e0000049082040340c0c110107075040402103a001e54000380d1190100101c501c00d800c9071898510500d0002541d000410002d80000407043e0410291000301304148051a014400d050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 534952086 1250 534950836 534950861
    0x50306010e090a0f03031805061519051c05071e080102070c03061d0109120f0f0c06020a0c0605130c050307050906040e190f030905040c020a1220010501030501 70
    0x58040c075007482c4031070340c0d401210401812072141036a24810f05202c0e40c8981e0f00d800100400c4800300c1064201644c0e62032098030000700140c00494003856a1820a8010320040075000000c0001480c0900f0020500700c0030800e1000342c40445940d6002604c00e00c400c501a0a01802d019807205182ea403102c2400740c80d402c01000c603032040080d5808102c01500300c8003200c0d40610042440800c0ca845000c4484500c600c850556003024480310401140301c414030030200d040d69603851401e020280444150301c840b004880401e401c024071501194881e001002040751304d0504081c41c4405590b4201150340444a400820340322103402c004102901c1242401080d084000344201410000080e5803810041c0043c0c0c400c680c0e8850100c841c0c0d0b03042c850703040e504198444070540c003001410007080070141050b0031000240e1060001c0b809103010320603a04101401da00415500415a8580e00d01103220501002805000260200500504684000d030100901f00206da20b5245290080c01d5425005400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 534953336 1250 534952086 534952109
    0x170f120a0305100b0d09021c03121103060a0b0d2007020f03210309010b04091a0105011b03112b12020307170403050f0a0c1208010f140118080705030601 67
    0x10000548800261517a1012a00000800c4a02032002405c00b0003800941c60300094424801000d05402500507400708454090a000451141d00b41042c0c03071000310340c055403110720044280144a100006015000800d1b500000c4100c0d1070442c05214a00091081d11191000501c07401182403880801d40c0f400016401881e02c0b40003c00380040c40400120a43c0c140d55000c000518103840c02d4024003802c48004d4403c020a102d01d04051315030120001c8030304d40d401c0d5100700020b4035500c00c020071108505045960030807290103030350465100e02ca0b0320540086106a445400b1041c81e924401040601c1e031441c0c00414085001d409407070098568440e581192050080140746a001140742c141000920070b05c480580d00c3d45402c3d5918090850680c01060002c2160489943c01c0074002c20001e012b0020182d40d0707510400120f81b050800d00442c28008011103080003003100264280001c041d05050104030b580c0342d80580c02d2092015486070202e90305c8008200210b05007171240501404640303080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 534954586 1250 534953336 534953339
    0x7052106032a10200d14090109050402090f0a0e060102010f02040806041e080301030f0c14210c180109050106110c010507060906020c150c0a0801170f120a030510 71
    0x4802c4509500020300d0203040340b160310740300161050300101d502e042c2e01080b10b20f400b99200e49003030b90b4503c03448580c2e0214074100c0c640c0512111000945001c2d240581d03410021608203028440030703400800c5015044860961103003115a00d43d0701c808064030141da051007139403801000080c20344240c00095424248100003d102640380422201d44c4a5085095040d114045160741e160504088101030302043c0040004001c0011810282e100325019207000f0780c0440e01c42030f0010711142001c03a6107910800701011141e91889041c0c41301c803c010301c507040d190062182e030080b9070611030408291401c0c000c0d140042c8145a4a40f0a00b4050507040c0b40020f203010400110302d076156030100046040c090045a41d00c1004401d4001200099004c00c0943d00da440d5a0a5507039907111032080c8055080900002820000003002070340c030030b064245d4900700140d18020503540e01c200e243d6030009082c020200d0010192100708040f22045880b44807990b07650408002c0102165009810903c80102c002c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 534955836 1250 534954586 534954643
    0xc1c02240d051b130b030907031407081c120b03010b12010e060f0606030703021806040b19021f0902040e011b020c10090905090c19081006030c0303080705210603 71
    0x8440c0c041d50150000c490346c90321503280b120f25100b15640020b084400300896800001c6000c5141c1c402c550106084075500c010024828080700291b0480600050260302e858007000020f030041791640801400000d910411a004101004015445090300f6911080a155107800812029a000602c599051b00c0c5062200002da082d100181c884400c00d44c0106801c0140031004c6402202c50000500d00781c0e1351591070012902a410800d05c100302c890510384208000c07030001c0f420300660304810700c030a00984103020800b07004100e00e050a98000350340300052981e1040034440c41d401048241500e0811300e80d00b040081c07405840800340d43c0030720641d661903070415400807500070030355600d008042a44c1d51460070b0289804d03ea0b1005940c000e4131110300034140b1141c4041303807040d94101810b82e6640c0d00c40a51000948846200007000810340000800c0481d100307500c7d80f40c101c0d00c1d501e0301e145019440c250342840c086030f480b21005980380007404d02c8084d1408202418503803455600c3d040d0b840034bd452 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 534957086 1250 534955836 534955867
    0x1060804030f02010b031902091005010e040f0b06040311120705010f0f0c0b10172116171b060411041d010e0106080c1c02240d051b 58
    0x100018140140c0400d80510b450013900840c4d211030002c1c007100c6100145410050241c0b1503100c0681c0140c0c907503400318122502500d8010280d50040c1c68140c00d2047d00810320009065881000034503940ea0368400c1e516a80300d03002131004501403048099a000003038104018502103030791030700d41a03001040070000b90760800f005e415000d407141089161481c0008054803440d80c4040c00800b020164400c010745040c0a004140a44400401042665001481c0b441d602d03060b05001e00d001c84443c0619110b981070303c5004216084240f00700750f035199503580d1182038020034407005080812010a150380300e10340c64030100b4514903890340140710764142174554907034140404400500845e08c0e440c000350749007020300c50a04807000500080220b4548100164024420b40c000ca0b5402e0007101100349a42c070342104c03403c480469000040e0800038081e0708005011021044e055110303c151110151113455020150041c00f0300740c0d6000c04c440c0f0700740c04e400c107164040d155581c05910051090000c0d204640c0f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 534958336 1250 534957086 534957091
    0x7030f03120b0402120a0c09082a09090309130216020d0204060506070501050633030a090c03060c02070e150f0f0a2d030308060603040311011a09090303010608 70
    0x14108101c001414203600c40142c6045407040f50030070700014920500d04c140030b00062290794210010480600a48811a282d04d540e10807000076502525080d140e0400c000c00e54030701d61100310559a000b030103590101e8120b55080b16103002c2ca13013012a0001160402a00c2c048039108055000c510307190300da220a2010110001000c1d010b0070200d0b50b0f440454031a039200c40040c040003000c1325242d074004d1070a903002e040c00300c4a490256000880545110048030001140188242000907400034120302d00011904001c10303038605185c5980c0440c000c10100007102d40558011130021074022248200070b440d04141d54080504102c100e4100848000300300c850051440040701c0101d0400313032400000d00415901f0b003c060380004480f00014560480605c600d00d407000c3e038000d1042c0c9031900785680c03010340203e2002602246040c070014426241032002954014440e08240011000744981c803800c40e110700010402014150085090614108000650150030000158515814204001d1164102 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 534959586 1250 534958336 534958343
    0x10b0a09151101020d0605040b150307050310030c090212061906050a031401080c01090803120106030e0f06040303020c12040b040e07140c0703060b030f0c1201020f0c010b03070807030f 81
    0x100309180038aa200300582000642c01100964444200c5030380d24004040c40e21a0358442c600c0e00300c3d1104581404480100c00e103030700b10728a0b8110ba450403801d035103030b40c8010840002005c1c0390101000052240c004540a04025240162950302440e8551002c50002d00201c0c86075800595164018680d03480c07400560b200380c0741080e222203c1e900d0a4000d0039030903848181c48618080082200b030700014044288100c00da8401007990303501e400d51910ba201b4203000443d48142c20005210541c003903045030310700c0700c3c03690125800b41302c44903d52410003070160ba00302c000a40000d004d81c100ba4041040211403480004d106140c0381c42d00c81140098401c0d88a0302d0294106000065a518020070b1a892140c4519200a585024080805440d82254041150ba5a10380340c042d880c01d0a00003849a050301e42d4100034a00d5540100820404645504104203e136408001c0e01c510000f1035009400c02115034800070440070401030415003080340a0300300e0710060740050300030008194640080c1816075003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 534960836 1250 534959586 534959609
    0x105060a051f11100203010b0c070b03040309121e0615050f06030f0a090507060206010f0906082d150603210a0c0204021e030a0b03030c07140609030f060a05010b0a09 73
    0x198030b0f031150305080703420341105151480800001000001c00008005244030071003940c100355202d8140855a010949001d00041c0200c03600b8402c02603150040c1480c82d0103020f9080c3c0ba0070350800d035503240c02d01416089030f4154441d091800e6100c80c0c0300342c16000e0f100450308141ca042c0c142010406034040100045461550350000c16103505203a4003551030560000b003512907540d280c1e1800380d80c840f828411021034142d00440007a80f4003451240506481c4a20050400140c020001615580e04640c600e0b401500600c4807904242c8200a0180e004041001d107456502d0020205410180c0c03070b04045100c00b800e40038405a0f04214002c07140c00f02d00c2c604001c101841c0d940003043c0240191038040042c4400450306c68005055000694403a00c801d40e0103125040c02d6206040d01c0780145041c03481140d00c801014130080b281c103a070404203030750041c00d940d0910460a000038548a440520f8103046d41110b01800b00b009031074041c9502406280006500c2c08910315070041201c41284201000e00c039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 534962086 1250 534960836 534960857
    0x601020a11180108030c06010801050610030207020103111602041409210409060902041e060503072102070b0711010e12090409052a04090803150a0b0a020105060a051f 73
    0x1510154a0800c000002d02500c455684600d18030355280c0c4441c12842c0380e032180000001d181d0205000b031922590001e4198030343e0b074218075025000b0750000c01089041c5915078001445000320b810141031803240c4800c0d0481d49034014010302c400c480b804a01c441d0304085060411100c4080050001c0c02d03100c4411941701c08005666001140740501d0704041111400c2c1b60000a0001d92a0090815204c262074119000d10034041200c00740c0c1c44a200d25004620180006048240104040703152000400c02c2e40c0c1240042581d42401c1b0703808140c0444194440d4030901c810a94040c0b80089002c1c1d041008002001da403c0000d984c9000c0d82ca101c826034500000c80d40400d0f00e858005801c2c40e6842002c071000e9604080c0d6804911070183c0e8580250282500001842c0c0b40601907003980c981c0050700c0524540300c10b480b07825032020100c09581c00c02200f00d40001e130004c4010041c4081d00d06a40001800c0c20f05a04009030901640e001c64400c0410358504450544d07071004691107a0007900b0004000d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 534963336 1250 534962086 534962089
    0x1404110f0109080f060103060606020607080106030e0703020301020c071401090f05060703030e0a0606030302062d040311030c0d0905040203041e021906121d1f2c010e060601020a11 79
    0x242e219820122460103084040701d40d0070340000b442030503a403089030280806500d0b0b000881c0d0b40c12046864400141c180300040107200d0080c3e104442e05c0c4c01d520140e6155a441e42c02107801ea03407090000d400b080c1d129a04c10854440754101340d11250790700b46030440c00d842c640840c015100ca0b55000d1726201d040001142010980642d0058217a00f03813800548561405904081c001015148001d60150159500080c036691088403100480000712072508a01c0c40d20a00d03102c1d840c08000c05c214248001403020b038002a1042010300700002b5048010141411180700c014001a215480b16029070b00500501c4005001002c00d000d00000c1e00003010010280b85c00083c0c1c2c00540c05040f00c9444c260b4490215506070b00240c00840317558590300c01c0c0309890743c0c40e01c507a90342050b2a0346014590446070301c640c440050039041d2080782c1d404220115124072a001c1600c0c000058030844901f2a0803e1049140c101c02806245070020404000d0501403030301c600040e4035407003011401010b6001280c540c0070507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 534964586 1250 534963336 534963347
    0x5130308060415080c0a0e060a3b0115021209011817010903031413020607170f0304031b170f1303031701080109120807111c031404110f01 61
    0x56415583c00d0203481d40c4d807540d4040e01c400940c1c0c07006025000c0c01134040303802c140241c10309000d0360001d007800341d006140c004d004001c420f8158445450348505041c61011800f40580310b0600d04480100d058903500d480030450144410f40380300310654000404030380340c0c05850400d8840c904403e09090003c00e150044603442c840c0250400202040b9a8a094240100551107034122922035201000004402d50103002022421200c0c10140001c0c000100c0043c01c002c1c02400d1040c0c800d1008056041b00c001e010501500712149030b5041981c044200820715600c110b00320600311056841041410682e1581280c03140c128a10b2014014000782c103500e0070140b481121011142400c0024180da102d1030003c01e0b12800b60041034080080400201c2c160300c040c800c40c8041a406188580a00850325041d254440001c04490900c044c6144000340000240545501c1c10424000f462008150a101a084030b031016034461202d650441008001810244204400801280d071460913640c0400100e60 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 534965836 1250 534964586 534964601
    0x30108161a0c1006060906020118020d020105090d060905160b03040b070f0903050a06020405090903040b0a03050601051603020c040e070b1803160b18040923120a05040315051303080604 81
    0x70080c0344c0328002400aa00482e80c6d000c0d41c003e0f5009100c145481c0301e91a00846404401a40c0401c001250600541c05440244640343c00500410882e00e4191901070484501110903940c80c0c01c1145102c8210340314482c542c002d409208034103825428140c98400420900030201414402120303864142d03140100501d000465000d0201c80e1121040c0c44c01e10041d40003480b829004c0c1d4503c00116003440710100944d400c5d60032008060f0308100384440100e0103880080c110a040c8001000180040079050301f4010105000750001c0010015200074070048461610051585070400d80782400f410040d03e044038070791003006844201d104801e4000a083c010b41c22440078001000b92000504454200003510303a013103000c14240303044403a0b0420310060303d50341c0c400202500c8861300301c000110ba491480d401c07000d441d841140c040700d0741100c9001c00c85d84824441d50114001040810400c50f19060365560703422480010f0000d4145400c00d6541410001c0f8000c042c00100c2c070018a484d200d0b68407112 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 534967086 1250 534965836 534965863
    0xc040303081b0a1d0409051c050a0507030c020a092a032d0212161101150302060c070f060513050301151701110706090201030516270504050a02030108161a0c 69
    0x403151070416618403141152100008002c094480034030702031002d8681c8c1c108180c07141413330301d50f06540031038141c1c02007002207a010032019004074200c4002d20519140141c00c01816400c0c100c3c000c81840800c2542c42030004242c2854000d018507002580021034a80313406050b04d01451001080c030010b4000e6420190101e03c12508002050800803a03050381c20059489d50520b14201c0744d8650b00b6101a0306041c07044001c40c09041006090040080c0750400c07058043d10889901c9080c0356420f401c03203500440024001060047c2c075030041c90451001448120001c10140031103203640035072807200e4030401194441d035001d807a140010a4102e2840e9040040449aa503500c600d002001002800001da002a20303207000500740c01011a13007010014001c0e143c1668a401c0c0c907082522661090034456804000b40c500002c0310703200c03405614003540c018000503803258100b80c8d181d40f60400034048205100c480400400c40500f20070681703043c104420842c1039813985250842403031302c804036002c04c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 534968336 1250 534967086 534967091
    0x31c020f031501120504080a0c0f0b0a061404090f0303090503120405150a2903010b040204121e170a200715140f0c150c040303081b0a1d04 61
    0x1800c0420040c4140d8044000d0703d484c40604000007018040740e00860303008001c202c04014240c042030007403000b403111500c03840f900364034a220b07940c8080b00c10400303035628078943d515480706103c0b0640c9609680e240702d500342d4003004207080b15100c09002a40025015003410f5944081c0420720109000f01c42d509428007461030403d041500e0255501c20740e04405040c174511010119032405298001d950000c43c02805400407403d80c0101d00b078880d001142185d915650b507040840d29a02c0d940007400c0201505270090f40300000ca81004940c8a4901803041d645404984510000514814900803840e01d090b12250b2510380000d801e50345817200b0145018100c003405d40140e0205e0b0005040030540300c09894059600c1a0746109484187c141103190421a03010f02040c201d8004100c00303800c41201d110212455104c4203120301030b5940054500c2003950780700203010b1080c142c0050038107810000c4c81c0044204141040405e0240d401002c511504004c5d49102481407518950a01200740c40001c004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 534969586 1250 534968336 534968341
    0x8090f090f0a18020f1002010e070801050a0b01020c01021005090109060e0a050c030606060409020310090c090e0f041e0c031403121302010503071b06090803060f040e031c020f03 78
    0x41207103054216480c00d8102d040c03d241c035580410002c0f1030802d071980540900d18840040c03040140d166a0000408115981d851040860400401040000307000e603000000d21820a02600f1040d240e004800d14155482043c0103049641d001645400c904145e50000806031a00c414441c0940a5003002070016810401c0c20b440610300800c0000c50a4421421200c000f05400e0a251701d8034070850307540c2d500510900081100c1c43e500d40041d81c3c0000c1c50340102c0a11620b40da005002c885170b00c411180090124041480070003c0020840d0304040c1c41c1003420310034a415902e03603a182a80314509040c1e901aa20000c0c2007004002c0d401002d036038805440d645c42088403607000d5880e000100d0100816144101062240c0b84110042c0c48031078060b074035903103143e44030748041e2901c0b08200340740710b08400e06074441000b142b00c1e8803426403510320078450b40341d40b81030600c1001241c00c44002540c3c41103180200e130940d030980000440d07000600254202c0c0502d6200a0400002e02465054a1041d8000002c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 534970836 1250 534969586 534969601
    0xe03030112110603070e18010303081b0c06010807031202070803090d0201020309130218060301030b0f040c081014060f030a1e150c02071502030703032a0815010201020c060408090f09 80
    0x24070340034070029501c41f807560120341d205c182040c90a12000d0003080c01000418000701011002421142e081c0c103c1c14035114a0f401c07414580a800da12110321500112800e008202d1a1105100311004900c010441d09081c454000d0701c3e4030417040c00ca072054a0b103400c000c00b1640240195051403400400c0740c030624000e460b4000203540140c2d07a1084d058000cc80070b800c41d02d4803409980c140c9401484200c0540d460340d00d01c6010050140050b0b82c240f103100c02c000741d103250030481c00f40c69008500c008200d28a40440e81110b02c0400703041c5510070284032207808080d443c0024504c000d00d412480b040785100b0002c06203c0d5101141c0c002503c0380881c18000e0040c64056088220b0a003c07540c2110000c0b9911070b0541e06500c1c01000b00c2d00144c00030001200800e00c240c0060288100e03500d01c07400c5d0300c0d403002e010071100d51008404130081190b59040000c134558800403800405402e000a62038905003a40d00341c1c032403100420060511402040c2c2c81802c0e1205264803a080b8409840c0010b00d003000503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 534972086 1250 534970836 534970847
    0x1080415021602040b0d11040e011103011e06030606050a080a020c0706050405030706091206050c040e070806030115152106030f0b10181a130e100e0303011211060307 73
    0x6059025170300301600f4650fa03007040f0000e0440305400840c507500d400c10040812019204000540c0102d48d200c0320610404c1c4a4040218001e20f1481d8420741407a89002c0c0718501c4540c1680f0a0702454909041005900c0c1c210080301c04884503441c10703012940d20440f004000340228004038249100b02c41c1c010900c1394001c4c00920680301e040301100c5419a03541c3c42110758600e07501509101c440700858250003d5620b400182d00400c55500700ba05290321090051540c2d81e08442c41800940c0351000e010203410203129440031945102c80700e030755460420054440107e0b1100c0048200001165009020046180030a1400d82c2c1e125050003103a40c0c074100300c02c00d01e2000308103542105018002c107003440d01c5003c1031400c841000c00d8407046503001e400d03000020118400800c0442c1e80d2400c3c03483c0c1039681c0b401c0008406102c55000540c0c0c1c2c0b507401c8254a0035410b100000340c024640007400b140d4090010a03030b4110307a0b48450040300d0403114a0482a405402011a0340150f030200070700030340c0c54014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 534973336 1250 534972086 534972127
    0x15010f0501090816051002010b0d0605150d1e11061b12030702070b071b090c02100504021809160b04050405221b120c05090c12060108041502 62
    0x90307880311a19034403182c0c0c290300c1d0740f400c80900707944d802c0000c0100140d0038080e200c905072104600002811800d104040b4200c0038050000322850741c1e8400820103810040c46034850044400c0d60342040c465095903a810303100c4c80b90524400440000c03078800302049040d1390410f8907000f001e007070191640700c1b21481c88007612a200c0752520b14024002d038941c80410784005e4a114200381c0d40144409854441503c8280d03021902c2a01d0b25515105800c0364101d44441450040c0500200000c204800c024000d0806035210203c41007941001d0600000d80d4483c13420941c0c0e56002404d0500343d4945503500ba1a2017500c549110046c1c645142c0040c80c140950041c00c121101918140001e5a030400400100350800030b2106405880340c03c0c1002103103005035021030410500703045802198513004c0c07892080d07040703000407074400312001014496828407449480d004001d0f02d01d498109108407041e406840760080104d4108080140000e007848071180b007032104d0281100d01156a0002c0c1d019060001484 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 534974586 1250 534973336 534973339
    0x80d230402011b111e190905092a0d05060c040302190323030c1905010605040b100e040b1c14120a080a0f1506080a0203130305030915010f05 62
    0x1800d801103002d1000e1156181e15a401002180c44001400070017050003107582c50f0440d00490407224410b03c4d200e000000709125601d181a02003103150035061020f42d14014502d100c65040f00303192050061003400340b4005103c442e5007401851644001103040a0700015001d01584101c80901031452003010040003500d000340c4038031403e602d18006806c29041148002032441242501120b0604c80600090125140301d00c181d924140740b0048031440c0140040001201402d004e503a8402c000007449540b005101c2650240003401801c2c00290f00b6489540d40d0206000b10b01c1c00710b003142c3d960b640c402c1e50207070300c024505801c415034074001003850701900700115600c0541ca8005021204002491812007003044800c40c608001000100e5059402803c4c09101944401200400700d6250060340d12428000550b01c0c051403600c50010070f00f80b40a442210107520400610400402c0da041042c15103030076040c11903903622103591461500c481c0c03150034440543c114001158413040a0340d1a812140c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 534975836 1250 534974586 534974597
    0x80c0102030301150c020a0e070306090b040902061b10090b160822050a020909012406090302010f120501030501020a020d11281e0c0b0703020604080d23040201 70
    0x50040166038a11080c001d40c0911a0400d41541034584640d820f10881440603000445840d03895060050740c98040e03603a403000c070751200d0061102c20185d00c680104810304403800c3c0f185603540d401040b6544115415000020001c1c400d25495000405c003080c805d0079a07100421001c40581802d5507600000e8554032410622083d12181c99880b804025008219261203181010141c40440c03100401440c1c0407180c9018055405016980358409188a4802e2000120301641850208140300301014105003c156821600340b0076039900043c07180580e6420300f001500115082000d540c030440070640784001c28100b00011003001019000340403000410f408481c170710a80c00001352031404503442c0c03c90039613200b01c2482c050b1010b40d180781c06400c1ca545c00643d681240340c0d01e50095040070a1601c820003013492102008101c03c09400710000c0001000550804002d0b0b9000dc2d2101c9010704090a17541021076800c0c10300388242c1c00f07407030a0900682c038200000700048035000090b80845040c0c5c08100c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 534977086 1250 534975836 534975853
    0x100b12010b090f100e0a14011d1501020109050f011b020d050301030813090f150b0903030702101403151005040e0703050a1e0b04050606091c050a0c180c11030d0222030b0108 76
    0x844010f50070941202403114283c061b4ad4003050054082c00d44d245041c11503485030300100c089007040c041103103c0f880d100001b1501c0005203518090341020355108004540c0125a808440b0f40e1003000e803415a03174004800ca6982c01c0c162a5004040d01c6900034140d01854031031007100800e100e5106040c0d00b0599452100e10907500c44904420f4007980410341c1d0141c02c10480200186001c070f40c060540000c40c281020703a2240282c0c25102c68004a54010001c3c511080c401e8040c030307105a1032440c590300c0d4584203251500709814008521005003028051540781c074045800500240c010b0300004071b0586118040c00030240a00303025000d094072240c025890400403c080d81081001c98940c408054420541c955442d110720a05118200381940e040c041c0a80d40d20005064045402c0104a680c00020407004040300c00300885403019005810f00c02c040700308000000001c0181c54180341042c0d4010b07181c0981e0242d1302035041c0c0043c802d07c070b81a01c0640100800031060b0750181680c03145002c0381d2501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 534978336 1250 534977086 534977099
    0x5060301081506060409050c030a2d050907091104090501120f03120e070902071a06090610030204080d09081e060f06040905100b12010b090f100e0a1401 67
    0x911080c0608051504100581907000008104140c1c1180c1c0203407030702e40340655503070260040f22420f03900059010400020f0016a20090040080850b500030311a41000d4a85004032540d082200d190814180c0f5080001c030b51090600104e0000c265031541404400d280c0c014180c443d5200d40100c0c10b003d4602400480d00030440440884c0300355010342100141d07841514161941d0359094080d0302d1050715203400c0300701e040081c00f0000050030700400c050303140c002500d444286048042c004070311104a40c0c007002041e0f500c3c3c45149412400680700302c08090080e90040300648140c1d004600c03a40309940c402003603d94048d03c0f89041307804060a5a05003003ca1500c844400d200d4840540551700140c041001c4d580d41c0c2c2c84c095004800180001814045075a4540c10700d5040082520761942e956082c06c2d850030652900c8034061101d2002704802000000025181e0700d001c3e10b5251030305820310008040c0b000c148000320117481c81001d0009a80b4158a90b84003030416103884841c008402000020034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 534979586 1250 534978336 534978349
    0x30c0a03020601051908030f0c1903030506150c0a020f0409020d0507061b11010509040204170624060304150b1504030521180102030f04141f201c02150105 68
    0x7900c442031b001d10300e480120107098546070000c80c540c440d28000c8809902c924102c0302000400d007846038402050524004042290030f44104001302012030080050610211000c1004241070740d04685440a00c40c0d80700100d402000e0710f0600941060412000030140180058104200c0702182e5400c0641c021840018a0041d040c000081800103410100c3c540740d8001c0d4040c201180e009000181401e540e0b0401e845407200402118816822a0040c403601c0c0e1000d01200d0b0380c40751a54414086508000007058081c84020f00140204100048454104905400212062340d00501102031403a405640d420340b60700c42e100443d041e100f0f0b40100c07141c000f0040410704121881180c0d490428408200e00e030365082143e03071040d0450004002d290110000000500068008102440080301d40710080c40481a61980c14500200c444070088000d940d00947c03000e21040b201c50005c41c26043c00c1513003071a204418083c0d80902180e512105481980000d082c0120300300a03041505d11b03665501401507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 534980836 1250 534979586 534979589
    0x903160c0f1a0a030e030f1801020115050310050c0714101b090b0705150a0606020c0a05150f0d180b0f070e01031a0901080102070312020a090314030c0a030206010519 73
    0x880782c818810b41d4600350085e800392550320f80c00d200381c03450b011540340c107641e940d884441c400307052858031002d5010f6940e09207d205602c421400000071744904201c002a0703a01c2d0319280c1000d100380c032000050400e4040c1010b65003465400030160045208118030a5112003036180b0140b9107a00c1c0c410119103200b041c03a481c181107801743e100d48041604103503000c0c0440e400390206944a12034804600384510141402030b10030701c01d140000400c14105030b0024102202500d00700c0c031070954110180150355880c003c0d4540000760402c191381d02c0791141c0104005018000304880c4252820a01c1c8540d100c07050036010f00d0a105580c1e28625950b52080074841c8a0281d45910000d0400d04d00f41c00380754044d0340480340f404005000444030050900003e02038580c00d810030942d50350003250701c00400d071700183c6001401003204425805c1492894004000980720710010f0000003080029141814091040300c0b00340311440260b484e540c9640c280a513440901b8030845009105041c800e2844070385c1071311100c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 534982086 1250 534980836 534980879
    0x603020a121503030507030e03060103060e0712050c0f0a18020d110c0705060d021b0d090f18090c03080d05150307030302030f07060b09070f090614120903160c0f 71
    0x2c84850440c1c074121540d0708028170031414060300341c1c1003641994040200302e008521908002c6450118a025182481103d40c0503000d0310b803500751880c000501c00300d44118500c0d016102084038080311400201114003a0784841e0249200407a01000c4010355001400c0600c0c0c0a0814084a14080421181d500c1443c40d0140719402c8000240010300c2c003400244012541c4079009800c0c915101c1040110900c910050090350b40212110b035045a0008500d1004000d505503400e401c920704003050031190610300802c0420f41c0d680c0c2039141004030701710544000e150000d00e419103599415400c43d00070403055800300000e1801c0744000540d440c000401c941601d516501031410030100300840752171070f04002004c9940c10380312815104180c440e003003481d200342d40030b941c0c0080404180d1806448100380742c00034420000c00c0216003410000d50012070340181892007003240555140c03040c45055015041100d12021415032105c82403001200c0040c0c00d603041c141e28446500d65803808542900011030010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 534983336 1250 534982086 534982121
    0x813030807030b06090301020c0f0d08040f0b0c070b0c0304110f0307060513171005070f080402130f1506080a14040215040801090b01090b0a0305120d020906040603020a12 75
    0x50310140310f0781040e0030082c4003624140c1041c68480000b42681c0041d524035481d0350103840c203440450420803054480b04070a044c8258142040d84640302c03081d04015003e00310744146400b02d0700c0c40d043d42c4129040140c01044001540c108100d040406920543d002e4448104002908080f46803c801c1400c0030302c0024010b0190350300d031603415211900040e46203400b40d0049480020b20861406c0886117080c1c0c0310020b00142c2605120038022154007030444020400b000c1c00d03035082c503500410141d820a404513200c0d43c51072080825803002e0010140345000789400e00c8818880c200c03c000d02c020542c3e21310b403286000c1755100140705080f600b411084404002d0108082009030034540d00c0140803200042896240503242c1034443e0175030308140800c071885c00304003004005010b95442241c8000c0c0c400c48800b1030b11440c0d80c5806549404030315041c05e68080c0010100480c2400354115440c1c1000501400c0d01d4558961000d002500314081c4c0e07501185030a038489030842d0b090704c6a80c414100703a40d0013 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 534984586 1250 534983336 534983341
    0x61006030915050702070302120f070b161407081e03030106050903070f0e1006020105190c180f06030c02060907030305030c0d290303070218070e0d03090608130308 72
    0xc40103000e80d0394040ea8000e1408008000a080c0d80c00b9461007040c02d43c00815a252961051044103660901c80c5278540d00010035114011802081c58030803500003090440e21811004040040000c00c420000d1000c180903045400301e2801050000440d01201d041e120580304c11900d904038001603001d4110190010070042c0070042c0210041c0c40c1010b405011900d545894807808d4903644420340208451200c080c0400295200740c0d43c012001d09007510081c40181400e110051007060300e079444020481d00e6030a07405015200d03d03415a1100030000440d062507564911380240c0d10414010000003070f08100600c83d1003400018500c3c09010114000c0c40c400703107181c41c116001d8002821002d842d1400300700c07020010241e8090900c041b003241820702ca0103a15002811032600102031058003e0308140600703405a07450781c0d9044240b003a00d108155041d5202581110001004010142d000b000c0c00711403014554010325400a1321581d4544031810703150014001c9a6114511004000403a100b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 534985836 1250 534984586 534984599
    0x120a02060c0f0c0d030f0f09050a030c02150d050402030708060f0109110405090930040504020f041214011103040f111212090f0a0b0313080f0a0906020f0610 69
    0x4281d907461024089083c1102241ea0900701014810321000103611008090009104c2d403069550019460000300a4905a41c0d02e60352503503444480070b410b0140c262241c005540b14108140803240d00e1030200707035a0b003c0004c1c0f010b00400d4296403c0e8001e200d15040881d42c0b035000101c0c039005d54000ca01e4643c00740e01e0801c050008d4004801240c882d88800d0100242948440c402e00340910f0800c0301401c1444a00d1a082943d44940a1400540703000b041c1e4400408030312031700302c2c2c0c1919001e81d40581c0d5401c14441c02e100d907101c0c81d07115280080143c1c241000b4002c0e0065600b4400c80290000c0c480c05246549102c0e41d8042aa0090321199007000030700c0004640e0b5001d07000e01c9070b014049000c0101d514242c281001c2411981f11245c4000203180c60f994505006400b840303201c1100c100d09800c4c10200c2e04c0c80d10780030013440b10b0090450212020140603001c001e03a0034003006161030a59a01b080746004243e0019403003184054425144900c2c810b60000c11942d00c42c916100039901d03024a0f040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 534987086 1250 534985836 534985861
    0x5090402060f12010b07061b09090b0a031e0510050108030d02093d020a0f020418150b0a05040207030806040c0c050105160801150212030709080d030608120a0206 71
    0x2224500780881003040020030f0200701d035150700801d8440d142c0368481034141800c1040da49605209020350750701c080c01002264000c1c03500015100c0204000400d00c0052010400e1003d0540000d010355030744107000d581903d404600c1c20b5081e4840c0c82600c0c5290213071132420081c1da0085c000c1d00c20b00d4100b48018105078020342c2c090b00440d0001810900d0074200c07401010f03440c01c010361203002000c2094585c00d80c0e0411040b80106134460743d10040080c4030a648030a2000440108004d00c01d40e103070394224005002c000b03080b01c986604283d0140101002d116002c00400d100c0e0f101034001e1031403510009207032070079200344d0b4403864058841c00959a11641000000c0c0b911110803402d2210740a0043c0100d5802d2150720704c1244a07002002038104106030280598505034402c40e0228200d590410320b660303011412400d42d0151010580e12621200029690300f545500088060301c00c030107030f8082050f41030b081401294a800c055404003201d8182541c654840e005604016030300c4035000c50110203100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 534988336 1250 534987086 534987097
    0x1407030506340206090712110d06140a0207060b040b09040204050405071809050c101d011b050109020406051507031b060504121701060e010507050c0405010602010c09050a0509040206 80
    0x14040360b03003180704450488076600e119075110040c0e01c03030342c100601c00c81c040140b031019019100002c140c0220720750756140d82c0d0140381c00c2d00d802980c1c038a004100704401d5401901c4070390154420f03c1c40034901280020001c0d00003810503207100d07040908451085c01e01d441550940b203808ac0074900c41f070b0744075020312000c4c09002d001296a8030a01ca800a0b060140380703400016401c1182002c00e01800e10f0424524081c400440700d481501e4011500c54415008485109212194000b0307100315143d44005850480704420001d031020345202000741001010351040d191180700315020011a42ca0b0001d1180310924804221b6156500f0407065001c24010080010403a5a08640942002184d030744e4005a46041e502200c907180104a041d1402d80c0080e581c002103800da01e510981580b4000d002030512409240d468144207000845109015080c0300450514a02400510141d6075441c4000d00820a00074040001020240c2c0400d070f903e8501034074011540300400300051500e850302080f2540d40079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 534989586 1250 534988336 534988381
    0xa020706080c032404022101090b09041203140c1b070303091e05040f2f0702040506010e0d0b0106120908040b030c1621020102070218070224041407030506 68
    0xca130b201c41080c1d41d940001c00703240f01c1c40c203a0b110f00007841001d6421000c0341a04031018090614040d21520349031261519070058101201e650b020203250400d42c018000c02d0105841c0c1034081c000c11001c6c0e0319080c001c101e030580d0b540502c00305214188000d0f480304400d00005000a018103000c00074400450205080300030444050901c550707403440094201c9070510030422600b0b8850b601d1100c0350645480e58100b1049102402c22102c04142105005100e07070003009100f01e1752200400d1603a4880d03400350304452005003000803421400d00380110780f000f003482814001070300c14040c010741481c1c0c0d0281c8100d180d0312080e003d0038242002c049400980000340b0843c0e10000070b10000041c10110228684140d001d0444c1d843c02e0042003a502c90300b10f024420a0055a004201d4080140c075069440301c002c640d00d0380c0040d45520b5410040382803140c0c3e440900c840300d200c00c00c2c004103109000c100a01440c410061443c500020070f82a0342c456140d440050042d401601c005034030700c2c09001a0b006004403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 534990836 1250 534989586 534989641
    0xa05031b010518060d0905010b01081308030a090f030806030f03090a030627110a0f03050d0f020f100b09070306030506011406091309030311040b070201050c0f070305030a020706080c03 81
    0x1025801301d04145c00c00541242110744914200303051000c00e100e10500c600081c81c142e11980f07058a11103627541407420b402070405400000043c0c100c81c5590042240301e50108018a61441a00700240000c8054450030702c00d000d030207812080d1803000021100c52400c040c0ca00d0010340e10316200c4da401001140c0300542903a2184110000390103540d028034a640d4403d8801100800303083d024001405a03075001552503419500090000c54000100e0001c400894500014080b500c1710003203050510a03011810035224a140c1a81c80041a81003469540b4082c0c96582c0d050303a40c8001103080c1c882a2001401c50340241e00144805000990100d8072280003509103881c045052021a083e001c15803d502075095851031030104040d8503004886035048104c190506140c1015080303030300c0b031007040c80c002e0500a00091035a0440824046001c60680800c2510107085da41d08145440b94004407420006000300c00307000c074456012308980d90081c514021101d003565510340c1d01440c048810b21120301c1126 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 534992086 1250 534990836 534990877
    0x1b0b130c08030703090e1b1305150c0114072f0604030915110c0f040908070311100615050a05071b0614030f060f0613060e0a05031b0105 60
    0x400d4509560010428080256900c1055040c0203200b4640c0350400d202001a04e401c0c0314540032a03100079400c80700c008121941d15041340000441c0c203003065101e16044044a8208004107001802600f03038982c1e404002d000c1c2c0e0b12490a1007018800482c0d4800110740040d400311071542d5861221400b0345012482c8031244000d05290701d113404802c0b03c08500080d0665000d0021214805981c1915035160404200e0300f8a85030050307450341010224140281142417400205665541009000c0e582040b8011350341d0b1200d040092803559180d807541143c3c810740c204011240514810001100c0243c401d0358494045103d04441550044440404004050152401045800f0f02074030450111040c541c0038a450004040d1080c482105900004402401000b42c0280440310040e489001201d00d0385150080e840000c115000300c0c5880244041c2e078120108805801c95480c90300f00b4412600d080070b20b9900d400b0580d4841503501d40541504a0000f0a600c42d40908d006d803200d00040c0e0303070544c09030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 534993336 1250 534992086 534992093
    0xf071b03080c16081501230d200a0b0a030b040f020d0e120703050912150411130506030a060915150f061e14090a030308161b0b13 57
    0x2d070801c1c4405850b50b0000314907010b1280d215440e020051040d54050440e49882c4010890031000503c2195614500d070a218040358845240003c070f80c25000b0041100c0403514100f0a1031220300c1010b0b10482343c440c901400035860b01c60391001c102c901d00c2c00b94502c0c2c070b2400325086010b40040c54000341c1190300c8040080154509001800b0218002c5000090300c800340507881e0701d40010340300d2208944408106690109501c2021a541c1000903210758402c041e0b0151405d281000903844011000102c03000d01007045000300d52142e000c4801c803500078104450342822011100306071040c40d4181d105040307540004180d6000b140304c040c042c0c210b1007030034080e0701100001d88032854000008010305001c240155101c030140d07030000c1c18407880c0c141b104000655001280395031030301c0c00e50b062061400307003400110340d07480803036001ea2405081c0c119070590b41d140142c001441a02c850003424240501c01003518480c06680f43c841c1603111185e003128442e07464044000801400088100c2604014100403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 534994586 1250 534993336 534993353
    0x302030f0f090406140117100801110c011b092105030a051216090308031315020301050f1905060708120f0618060d15020d0e030901020d02030f071b03 66
    0x14845036026160303200ba00208100861326a508281c06510b4000d40d000c4007030368481c1405000c9001d1100b03001c915120012501d12414180d07001c10150341c20711000d81103071001140604402115070000b032108024140030310051501c0394500c0000a10004420011801c1c02042c04030001560300035030140d0700ba217888403421948528403440100b5030014009250b400600c100340c0d03201b103880c4c640004504404070010300b102464403000e0030488012002c5011400148090207201d94040b1003502c04401248070b41c07020750400d100b103901c138510f00d03d140700711030411262110002c3c03012020840c2980c248400c100440c2c101c040103641a003014080801120320b09494140509411030201d0601e10300340007082180030f02c00141e010f4100c2c28906000721512840c60b00724680307034440395031100850b80f804910028003905280540907030415086e4400000b012006001c014800c1c1c1c00c0d40c1444040d00b00c01da0390b83c85a2141d424001508014032008a013001080543c0d0800c0d120050314000c1d602e031504102d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 534995836 1250 534994586 534994597
    0x102030f0a05220f09020408060f1e100509061002071a070b09060f1305030405010c02010e030a0b1f0b0906090a03020316140a050105180103240306050a020c12070302030f 75
    0x14003c0c0701d800140b008042c00706522005000d0b000b010361500d41030820343d0380c4844010b00a01c021901c25800324014100940901071610101c009403c010710300401940080a0350b0b101c3e080c090755154001c2007650400c880c5071080c0010b250018030080e490075807602c03007051901911042c100014060a000540102c0005006846c6440100001c0c103002041114000d07020b025841d01e0040d805400d000207201009035002c907082400c1a816140740e070700040c2d03001d0050f0380e41540d040c003a03502850208807185900320f005d45401074100d90201400c50b40c02e0f042c500c19000780c0d03540c1c42d800d20000e4080d1812030001d00c14010080d00528a10340d40381d010030b1911030320310b4480c595004604400d02451103489100404140112250b0580703a1034600068900d1240103100410810354601400719079000b03400410f44180e2030107403017015040c804848000e00b07407180000c0b20050300305400f0410803a21802542d5041510002418440e84415a1480164044a802c400b0360200340101240da0515201900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 534997086 1250 534995836 534995887
    0x1b1605030d1b08010911041d0412030c021b030a0c06121b0806012d02031b0601030507050d17041401030b0a0f12030c1407050319020102030f0a05 64
    0x5445850400715034041c1c80d0354405041078101c40b11000c00b221070380210500e0444665250018111400085c1290541306580081c1b2010841c3c42c0150360203a001c0144c6c521450003000d410042400d1010b0440585031401e86500059010300141c3c02c0c2e14001001006609200408568080d0026a10800702d05416807045010542c0110881c000d40c8445c094480964440214054a0116144003501c51080500054100f14100e4414080100c411000340c0a41107250311040c00355640c4180259240d000007a1011215035019401100700400a20141a00d07402400b81030005d0a010610008038105841607551040c0c8441a4100b844450000c001600e0039220701485480041c0014054404140402d030040240001c104280100041c0b280e06035036400340100c40e18105820f0803200c0484241e03019106610484921020100001d404003c45000f035083e14400c0d403007100344420941c05050b001e40960130403c00007140341c0044000704403104650074040e0501034402620700e032081a040c0d006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 534998336 1250 534997086 534997093
    0xe01021605070609090e06070c050a0c0b040f05031f050c0d06060203120f06100332040c0506030c031603230708010909080706020702240307261b1605 66
    0x600c81c039030b400034210300030704548482400780001e070740d00103587c40f600249144200400c2500c200b040160030300080001071b13000000000c00e03e445444044e110391283c864002e407903522100000d1141000700c1d4001c0304002c0180700141e015081c056020107448000c2540e181c0c200b0800007000b003200a0f1080b400a00b100b58015901e4440c00c00c0400c01c4031034040c2c9030741206032070780d005c2205c556500303101903242e40118900030a0a0780c0ca2401c410143c02201c031920044226526038400c24140341800c0791040380a07500303254100381c1d514148140c502c030682e0b5855104d9001c100250725481250050f200d0f1180c40c0c0350000e08080c409c1c4804c80c402c0400c001a191417070407401400340301d80c0e00c02c2006001d490007180400a000b096a81c0c8800361054030001405107401041c84410745d030f200d0300504101d10130075022804140e00501450341076402165084007094244142d01103003088880703c01940b60000280c2d40240d1154031412103001e00440c41510144400c100d02007036074001d42030b84203086104a004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 534999586 1250 534998336 534998339
    0x80105031218010f1404181d06040311030403080c0303160e01020a2004060816090203010b030f090a02060c01060305241b13060c151e0e0102160507 65
    0x1003505100c03201400340c40008050040c0103003103151007841c1d14145424204005000c1480c602581c102110050750f280c5e0002c04a00000c2126400d0301414201e1581a010070140e0042580300304032503480001031003250300c0300001800090180c04171035642d007d52000c8030b0405a480e640c07000c03540e0081d904209650000310900120712000e0303180111a00050500d141d00308a100c5c0002e40c0c0307148100010702001005030342041084401ca8060710001c1020f03000748400c68945465568030400e04030130010b62509000000355940051094034181c802c1c446002c0d2654480c00d8450b28140ca02401c4d00074140144030321140141d680c3d00003080c0c6800403a0002c81c803a86103041035410462100315809640c042d941c5141d036400d03001030f10181d0101d00b0184221f945041c80301d20440030300540020340741000a0050100b1115082585000214410a03c48c400840c2105040c800c2d200881c16001052202c00143d580c40003554012041082a0b8400141407200e0b040091034410b29007501540c45030410b80c0c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 535000836 1250 534999586 534999589
    0x606260105040206031308120103050c090a060b040306111306081006091419080a0510060b1602040203062e110d02060f06010c0f060c020610080705090406090b07080105 74
    0x2454a00190040020030991510380c02050341032200410300c1107000b030300c410142c003003288040680781c20078020418040f496071a4640315a9030003100518510842c50280003600b0a8050702400d015141e40f09142820701e4036660b10350f4050584a011b800c140c074020301080d03101e07807100900a001000140c3e5148001d080c5140c801401a50a411070707401c01540c081c00744038130032180003104d48e03504098949034003000310ba4400008608060300310340c0301c60140f00084410300c036001a03009503900054008101156460b01c2d800d8551040750110740c008191502c5000241c601503000d150701490107001d1158486640418210400780425071540070022a0488150194407200c24070362043d50100516810b8081d04000c0c2da281c1d030050082c1c0d030300d0340020700040c0310340d20510302c1040c0d80d540034007506550926490280c002c0e02c1e400030302000510402d80010340c007140107003000c401c8440c3c83d4041c20b803590406051081c441d100500550751140c40d0010140042c00c50185140701c0c406607650900135505000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 535002086 1250 535000836 535000889
    0x3110a09090b01020c06031b090901060e040b04093306030606030c08010203060607080304020406090c030509120306130b2b1b030209011202010e030f0c011103040e010e130606 77
    0x8000a04540c031617040701031161642c408990b003105204603070803c4021000500c131118410381c80380c10b07003141c1210000070700709410110b04023507c80101d42c00d00c00300e803030340d0140822034910800107040300c44040c08840c200c416440c00d24040000e07544003018004450340595040e0b03401c0390710071908076540c1c050800520001c40d44110250203000c009510310f042100000c0c046000d0801d000e07042c0100000400c045503900d0740140024204c9a50512034402800e4002d401130004072060b058501891981d01981640380d811281300b0711005100114440c1880000b00003004110505034100703000c5100c140e0341140d02c08840009009541c0d9a0122860b1440d01e04a064190840d0034803100c00c00000b4070060707640480140c151031254a003406000e00900040381e80030740d01000329400d4001c410500c0704160000c80c503048082030030789602c0002c402c5064010b980f4840e81c4190654182d40c000140f00054096128640080d41e140c40845882d5941d00c07054200e070780d554000103801136501444030000141c02c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 535003336 1250 535002086 535002101
    0xb09011d0a0606090b1308060a06030614060105030a0f09020604030b1e0106020a02010305092401090b010512010317040305070e1b120402090604020408030c01020409053403110a0909 80
    0x40c909000040ca0564041c044c000907020b000c00001022569000c440c011010010050103040120341150510380b1f8140300070551400b00741d07030840c1801c03140c18541621007603640c014031060750382901d10703992001031000410496480030038090310b44081001684d1144c018001950203284214107134200a8600112040310101c0c1c03100428640e001008141c1e004a54119120f0702800e01164982d142004582440000c41c241d8628080e00380031000f0002000c12414180c42c0b920384100513056a520064805009200d0034075200120400148000340c0000710041500c0110230440d800c0035201c0c1d0baa81c3c10f0440303580185c6000d40c0d00d4020000441e1000c035110f03000c0c8411071245442e0800805044d1481080180060b0250014901244641e151581101e0051080005480d12501c030444418080d501501c6a07a1445080202090055142c10101c0062190700680e17444241400071880d0003107260000c41c04181640d071020f080315814010000c0841c07581b11ba81702040a03040c11440401c0f030306030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 535004586 1250 535003336 535003351
    0x31517030903011d07050927101104030b0a11040308031e07050c0a03030e070911030906071e11010b0d0302060f0a0203070207140301020904020c06190903050f030a0b09011d 76
    0x480b13800344021034010417140203035502916112a1595581c144080907102c6101039140e0103101d40c4203c09080000c01c07588071402c4002028400024400305481c07460041d408094000190380e408038540ca5010fa2005c40c00b10803800f0410f041566a0b2900044d6400c11541c1c14281071038107150000418a100c0e02560141c591b0500720b0918150380901030b92555044402010305540b0000f503840b01604002e408020010780006000719401d40d10110003613041035501d0385040c841d8501040041c0d0080880784281c038007191b00d01e940c01000031000c9030094416410325505540c0d0302c0403002c0b2915100e880c0701c03c1178001c0d001040c0f94100200c4030a08000300411620444d441401032000d0598045403940072201c40301030b1020f6015002d00083e0082c4641c00610344c0c450300c0014000c821480104006205035100400c030000e43c407000032028181c4021280080005108115400440c020391003d10b400100c0c0c144006054248000868600e40003078000c418508480100b401c8546940d0440e10b074003209 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 535005836 1250 535004586 535004621
    0x503120a0b0406260c0303030c0703020c240f091c0210080c03060d080412060506010906030204031a0a0e060405031b070302090612100222091b03151703090301 70
    0xc1c004e0740d2100340010007000141e600b45500004215401046248503081000b4150b070f90702d003490401c0100380c1d400f11000701c015000d444004119481e05c40c003910f00c601d06906d241da01e802c0042c00803845d183d21030100c0c0d07004103506000d80c0041e921090000c2030380c000c03540c0c5060740140c01030040000707040550340c2010401500c403081017950804d030811b4a4000109603102e4503581010311303002c40a4090350f04407030412201e032640e030b6061151541000303014850a80780c4a4090b600c1d81d40860a900c51070202801058000300004d0101c03240080a507407091000500088070320780341002504101080d50160b034154004103140b040f50144420607000705401000408140d032a540c08224241002017200b0300c40c0511046600900788103122000200e401d4050856445650090092024061101c07a8071034525414002c00c450803240300d480d82c010402d01d0020306141400c1c50407006010411042502c2c004c0c00040040d0050001e0700e12001c41c6416006107884080900c140b6084541440d082c182455 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 535007086 1250 535005836 535005839
    0x70c0e1905012306030907030f080a0f09320607030207061b170703020a080a0206271c0e0604080714040204061b29040b010803040501050409090f0503120a0b0406 71
    0x103c1458038030301a5a0183d500d151070fa914042c80b03a0601005510191508102c281d0050030440c03008004e02e9006c030345499040c412a2142e004071280321440c0513010200741c55a41035480102800c0f034a4484452510400200300310040104001d80c014043c101c01503031080c501400043c0e00808115076202901c90f94180110b41512400d591256419800e511500c00040400c00d05100307002c6415040c0d01300820385d582d0f030f8007032000940d0b401e42103508500c00d40301188100002c81014002c4054002010020f10010354540807190510007081d00c0300f800d200c600d500c248400c0c0c481e8006400100860300c003810400e850844840d80c1d01105503180391180c0c2c41000148240740e003260f140603070f401003044040407800d610b10b0919407296400c0c5011481546501d80c101c0d28503a0029014031aa11074403061f42d490740c0c2c840780d041d43c0c0d000e0741c01040c1c042402404280300035909a40084d03040c41c083c101d04654004580c45103404d640c4680d0304c40c101e011020040120303444d0a0b0003031103001c5d07000791000c02416 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 535008336 1250 535007086 535007129
    0xa050c0a03050408090d05150901050f0a05070c05010c030b040b0a06020a03050715060f03030e0415060f120509030c070e0903040e1305100e010b090c040605070c0e190501 75
    0x180304415040081c5551400460248440b13101622002c1c4c80140c000090358602e402c2155036032a800114034030000024001950050040c0500da014402101c81c2c0c00c2e06848036036142c806058010400420091600a03003000b15400340210000b0302075a8400080507061300e024001590540400f40340100341140080000c5540000e0308044540c1525046807102807d00d8075000c01d0b2640300741c6807103050801d080441d1105107540ca0f001228826221440748503034030014001030703074000b45e40c0440100228008000c40d8ac0601c2042400c681070303180c508a1701181010135030444000750b515150513800841c00310032101081007600c0103020340e603003450503610304080321650702e118a009800c4027104000101d003d4520038062030b0642584002610305119100307030204014108010829655800e04125050368140042c0e2103000311804154180380900b020310030703145030740700850464120034010000902c250107090014011080c90074111244961030070240182c48041e002440c0b104030011159019 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 535009586 1250 535008336 535008361
    0xb040e041101121506170c0a030c230a080a0902130e01020c0106031b270c031d01051b120a09020a031a01030b10050f12030922060602150403030504020f06040e0f0a05 73
    0xa0244609e404680b5281c040c8003140d035034502d07461410482e096000819060309400c805400b21148503940c0c082c0655503c11984103503000400040c1d000b4110243c2607400d81d01075005502300a490f01c0002d0b15100510009a0840f030081d402135503c0c0381c28162549050060001c900000d10102d040285060b08c000b80d090004c11a158008145a9694a0004946009401030f0401643c1c8200c00d101c880840c00c8014083c0200311444441183c2d1400d4125082d2001010780b003840760b0000b40000540d854040c003900401d410a1b050742e000904820000004519006100d81d020708441030031604e501d585000b0072681406002c1210760841d001c1c0600290715070080c90072090a003120488140c0300003420040c10751083d8400580c0040760904005918503a00340000c01e07609802c48204005a03036a60101d03222055100010640030000c4041400300380310b90045038100d0b000a02e5401d60b2034810340010320503440361f407029210000203030802c200f4400780c3c0a510703402055080c051060b4940300921030751 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 535010836 1250 535009586 535009597
    0x40506010822060c0206070305010f080c2107030305071725020d06060b0406020f01050403090614040902043005120a02030c0f0102040f0b040e041101121506170c 71
    0xe196040040d02d1001e214154400c02a80d50808010441440329400094940000b290b01c480441d040c9000021940000300c03010088a080002411603000720104002c003050b045803c12160b0301e280340384c51981c0ca0341031081000440c482c2e1140c070398544c01d61a051002a00c0d041c3d00307100003003050001900b0030000d00000490008103032100b0762101010320014028070310310380d40502a10710308040441d807030404000030425031324560201c841d600403580320789084e140110f030000c3c001200300c0e0381004000d000d8206480480c004100041c1019161030315801280c0103035115041c0b01d44213000c2c1024030024460700ca203030213001104d848031140e400d0701c0c2c1942d500c42e1030320040c011105c0000c41c00b05040c4203106070343ca174036101c105035802900442c6140d4080d420030300409802400180c4002440e8500c0005c8a08955801c20700c105c09984580303d014105982c059110306211080d041c0d000c544080d8811881020320686880c9001410b0100040801c504140b08052051844052108421503941602c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 535012086 1250 535010836 535010851
    0x402060304020103021c0b0f0901180504020d1a0f0a0903020d050307020a020a030807021206100b180603040303090b06010f021b031204091406011e0e01051b030403020406050405060108 81
    0x940d40e4035a4401200203104009913401c110641d40e241e4203c098058110b80200b1038100c500300c0710740c8525000c101907983c0a2203032030a07250348682203a404c00010b0b00010751003400208524811050364850340c811a031821024080540b410003000807012035100b10523000310030f5003000c028071049d41e035029613907503a090440808e0081c0400003a89a6100b0401111015800f23007400103465a24034010505400c8091308074070501c4080da034200c0600002481c00e104400707940500a00c1e038644001c842e01d90340544044003d2200300c20740084551070307240056000d144241d60010740c1170b0250410400400c0060203080c100041c60040b069070030b82c00030303d204581100c7e0290810f40703910f100020b0f01e03104074684001150340c0b0110700000e0502e120750020401c80310a40118420b80d40342c900441d0b103140044050f00c0c0308d400b045208201c051081000d034610780d1043c100030b40b40000d0141100155401e1314488421640001424000c42c105409044000c010540d0300b840541400c2d00080d1034445d0042021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 535013336 1250 535012086 535012099
    0x902031906020f16050f0c1c02180c0912060114040f0b03010c0f180501120f1e0c09090b18090c15040603050f0601090605130503030d0204050102070b030f0402 70
    0x40140440342c0e044034484070500005a1340d44018243d04080309280e11800d648a0003660300c403d03040e400100c0c0104e9103040c0107181401210080c5c4c0c4007010441c8515040c2d8001b900c4901d007000c512010854107003e1111220416114a0356804100400c014500344680076001240100b18650845619091501007210003144059405041d4401003040a021030b0785036003843c021410054102034000c41154255a6101c00c5845400901c207880c003080c407030980000c8100170202e41d07440c441c0d03116142908046001268200c40c02c4012540c40100218611031181c2c5c0d5245035801ca074014680d80d00901c4002401e10844829030001541c0c0340242010306801c1c0e5140740001d000d90001d0041d04841c02c00100380d00445d0540d0b604100c400d4000d07000c2e01c00824900804500c2001c283c0c1c10345441240c0507580c9100d040c0c100b800c00c039120380000741034900040c42d0242c0030440f95030500c0640782c03ca9103e0b100680312443d01000911b000a56800b02c90202420800c0c03041040170500c00030361140e01038950 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 535014586 1250 535013336 535013383
    0x241104140103090c0f051e090606031906081608010e06011403150a0207061103042f031e481809010606020d080a0c0c050a050d12090203 60
    0x141d02034040c1a0300240700210503013010503107003c460701020070b03140113031400050088820880391001d20310380c1800342e03c210034000141d818500b0034000c40d8041c0317090466408407030304a0902c2040e02d0181d000b41c120341d00300341801400341400c9a011001803c25000a104040907190426100d507010300803008070104008804d140c0d03031400c02003004c01d120543d004c152349103001400c910094200083c100c03a4141420702e14070231000401c06590003281c001e00c802102218418801d01001080600700d0701e8480c2240303561031582d5060251100101a11040260000d0880314081c1410100c0010310702140e54108034090403d100f440309005007094614820407042c80000c0700030403074035410600d5445601d90007a60180520112290702900c070b124000d204940d250f4005036102c0410038501d4000420742000139494420603004a041c80e034450800340d0030010350b911114208804428262030680c0003151a00c005541308001008003549150208820b1005030b00007070b20380c0d0b1100900880c25085612 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 535015836 1250 535014586 535014589
    0x3030a03050603060a061d040c0b0c0106080d1d01120e0f060405060108010c09030308090c101112310305010c1d1f080a0605060a0309110a050303030711150424110414 73
    0x400c040d080302b440c403644400030913a40c14041c00301ca009901c228050649141d280794094a4501d6900d174400c00b040480420030750046035495180324101c4066034403501ea40301c002009010b01a507011140000c1d024030b01d040d040c0203107882d4069024400980c948510086640c0d8442100d00c00e580d071518000c2c8080c6c948279142880d0140302c1c2461580056990a0b035503049070401c03110f1f001e0030a0b0b801603c0072182d0b44088036819018101158115448510b0010418032004520004041c241600200c0c681d899444090031611411100000718040d40c074a02800506149883c0108008840301100140c1415090310383d0740110401328240543c0c600881d049038039030f4200002905015006a440d0f148942000740074000d01841078031000090301c400d6080341400a402410707a480500210f1454440c510308032440341e00581c0c00e03100d0b8015181c0300016000c080719914003890143c0e1181000b2519a071710280e01c2e03620040149000d6180030481002440d00701d0a99007110046400340e80b00d90403500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 535017086 1250 535015836 535015853
    0x50a0803091c030504050418260417030d0203010b0c10050403020c09340f030605031b03100513031101020313030f1404091401050d210e03030a03050603060a061d04 72
    0x104059446030801d00c02c2300d09218804200701d1481d0003885504c02a030880452181c0b02400d85e4128076203051308010502aa890303000c8441c0000035941e003113924081c00c1c0d1003c076003280c1003030300318100b141c00004000703a205a0400501001c0041248200058102a900655107154441e8030701d00501c10307200024960701208803104088100381d1031030390b81c0c0318440e10b00c0101c408420247e900460340d00101740c107109210344100015a48054020000b00c1d403070f45041402c43d01d1300e039400c41d854801c40c1101413041d5400c0c0141801507102218400620519117030290050f101d004854101e0380c810b008000640c0f4114007095195601410050b03080c2070000022140c0030303481010981c070701c1000030f400960103441f41e126104020700c4207604492070f600c81040144004140710003420844401700c601c10004507150f5040780c0031583d07040500d42010b001c00400d05540002c4110f00210f96220100000340c1801d000c040c0d4402004441000240d0030300d01d40d00325420207203007a8080c0c6e241c1c2c94000f4007040301c080d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 535018336 1250 535017086 535017089
    0x316110a08030d0e070f0e0408280306050907032c07080f0c041b020a03050a0e0a06170a050c120c130806161403070503150402040f050a0803091c030504 67
    0xc0050703d0303039100038401c48000b4002100c0e800c44103125a01000680c105039260b0b0b041503401c000c504803000c0d1104c0d21038000980106100c6c82e16092011082850709080d110f020003c014691070209050380b80004101c40814020710003824982005440d1403079103041c81381c21180d0b01d8110200080e841201802d1860310301a500000458424421007010842c4002042003c18104a030280021801000300b10781c03240614950b540983c1c06002d602d00005e0244d0050305010407107142980e4003080c030340c0000f48205050350007a40860506c00124442400c0c0303000c1c495001090030418050713410300740c100e511141710309100c4490004110000c680400304580c103c40400e90080c0c3c031404440e4403842450b46821040c1c3d140b03d98842d07240340b4580c40f18080c00c2c0000c00040020300c0141981c0e10b03584195a180e0004090340e200490003010b00d9103555651014001800155401203903240c184410b0107038030400c507041800c030b0b944140824186581c0b0035080f482e03900659601d42c0c00c407003468030301610301d07020300d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 535019586 1250 535018336 535018349
    0x140420060d0605030f010c05070201080718060903110d030912052103100806131e1a06040c020f06010b0702011709010902040b060a0903020f0a1a0d0b030316110a 71
    0x261070355003072005801810503600300f2026a104250310480c00c90813141340603103000105c2d20511406000d50700500c50356a00124504143c0c500e01c84a40ca01c805400a9402102c04140295003d2090001444207400c01c3e500690300d08011900c151000340004d403c80c820b03035820715109000708042010610264001003030810600d83e04540f04418071042d600100e621000710502c0100015048800042403800b0b51642c1512425000180c0c4524500300042206e88555007041c5200200040514a9411782074600200b00781381c9080c03000410050307600013440f51045600c6529213122110300420f84904550b40800100c0d0354031a284010b860704481007402a41c0904518200b050041045d00f004821034401c44080001a903010200203803400740c42e05401c0082c1d4914070900042c24000d20041c01d0020041078607524a0703980100540c0c6540e00c410f0908444c03000b1800d4480f41e01280950825424114007550071700da0075092091084082d070130058032900485422000a0710780c40002c0018180 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 535020836 1250 535019586 535019599
    0x4021f05120c070209060312030606070f02031c110705031c020109051222030b0417091306030209010803030f0c18040e0d0905040b06071b0509070f12140420 69
    0xc06000d07881607a0030020007a40101c1402e00003c1c6c80389401300e20702044509583d911410751311072030284005500310030022038135021408100350142e5820410305404000c500351510403040e000c82c0003407058031010580303001984008009d000c903079070216061a40149050768421f00ca100751030b0490161034103200151180c003c92a400c03566101c4070f001000e92200e10032086000303036142e803030b805000003051101030b1955800b40007080000c1c032085a081903000307411400c1c1b402e016800703000800c21002c40342402c403944d990704d2080045003080034505005140c014051400d500e0000c51803032031450028200c000c920340000b8170100b0501e4901010002000191042240c41504041c143d9111010741c50440491842d400004140c98140542e0078034850281c14036080201d50355480104150410203038014843c03009010072300d5240d00010130701ca0b10880d603c0b100480703030104000e89901c08080c0b030008060b00b40807403400c204900c04c1c0101d8109502c0000c00c0d0340a446a0b204205104030f10702c5465001c1c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 535022086 1250 535020836 535020841
    0xc0506040b040602010b0d020d031b08191e080414030c01050109020325020304091e020d02030601080901091a3409050a0e0c03061801030b0a0b030604021f0512 70
    0x15903500a0702c2510312540080180030003d80401c5001c5d010040d0095100395070510002c00288644000f400202c60300149100e90141e55130380c0f001e01d80100c001c3d088042c004148811042c1c1d806548196910000902600e00c21140d0030014910000100003800da0540c61140c40d5410308208121070003000c060000f0010341d41c440c14804040c0d07000703440700351140d41200945200c5a0032045c00c278100c41c40079002140350515114030b40307000d025414290364488420300c0e6031000441a0740002e28208541d40d20050f0307645003110025040440c00b07800744229a24200c070301d00c0025081000d000c3c40da056147d0008043e038401e0404d07110306184d4016600c0c00481161581d24514070008003640084d065110b040384192641c05001d01e5400c94030800c40b5828514000c1981030001200954118001030025125400c08646d10f040c200000c0c6d0088a402040c041004400050382c0300324541a00101c025000904168001030704ac00c0218031400c202c0d0140c1c1d0008e18440d8042d408031061400307128251401807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 535023336 1250 535022086 535022099
    0x11120d0c0605090303100e060d020316030c1a0d1a04020a031505100207050436020109050f060304120504090e0307230a060b03070909081c06080c0105070c050604 71
    0x511504030220356560401011880840c03010041d42c1c440e0000142440d602441c000c2d9a0300008406866250010032480d28800540c8050120507810222400d001e400ba900d1440e001c03a03035001030780c480c07120907003948180052605058200d070940d13120180c0200701c407240903841c21001298004220384c81071000903025112130701a0000054902c0b503101904026a0341c00500402c1c282c0f5160040040e00706000c103100c5443d10750700c1074203054040400c0c3c0000c09500074406050486007005500c1e044981d243c040115a4020a03c401910301510011203900e00708000c00e00e6400701410040c450805070311104089031040040e20001c01c1040014818035031aa81d803507840303600980741a5120324074129100800c000004000c400c50040a00030310307141d929178459100802d403403550554035000d200e600040140039402103010150013009040c0d55801e03800a0048103108142d0100707035081c00d04074104042507000c6441f050ba46000c1c2861586c80040d0724101c4401c103516000a98040004980031980 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 535024586 1250 535023336 535023347
    0x20a0b1305060d1d030c030d09140106060519050f0d090314030c091905030a02060d021c05150103051603090623061206010f15110601180f050606040311120d 69
    0x2044980c400104c44441501540c803441101c515100b90380c410400128503921550151569a01410400030b50021208500d401d450640c0c2c05500095800704801c554400058009261200304e402c0c441e03c0d1078140507221803103014030550505100d81c0d82c43e2250a0501a550050f0b101242409040d507030b240085000710b0541100c85428000c6c141030030912603a132448041c400503500700900826060f400d42c1d081011550141c601820b00e242c00384414501d1000100c29007245c0c14240c1c001041904d82600a02406465004039a04243c28082403015000d81d4030b400704a00710b024540456000d074070b07003880000362100e0b5040e41e8841901040c070541640c4c1c2aa182c0f40905000c403024112240c2d00c0b1030550f0b86840078014070900d41010305041044401141c01030b1182409820000c0c41d41c03003103210b5241013020903804228644c07000106200500c130300f40301d1040041c154440409c0130741826004208103001d0b50200a101354000f0003581e83d04c0d51030100184c0c4180c100411194031004800c0002d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 535025836 1250 535024586 535024601
    0x90204180203040b01091e0203040b04030f02011a01080a06030804030b0601080912030610091214160b09060a05121906060c08090d11120a05070909020a0b1305060d 72
    0xa030300c24200d0381110000d0440c021a40030780d03040b010b10801c076400e02c42c0f80402032991100380e1381101c0800c2558100050240051441140070340c110301050700d000e042c090201e01c407003900d00d011645040b4807007002c0b5001e208540c1a1403c20302e4100010340d1070a03140d000400541e040600020404500003081080d80c84641f40b1a1100b07985185031501e46082c4561350345410903a00306a08400d20000d280e07420100100c02c110005481d014170b5591360b030320b99003000d2070819409603940c0c0c042010300c21900e841009185c05540c01c65020346c8155241504040e0903004090300c80d03100e51400110300f080b035880350b030684648031050103074100309041ca205044079070302c15a4061450039003000300c00655103004080c0d2140329070b003140e00145411025020460300740410703c400c449820300d0741c1119045d6207442144c01004080280141407803005400e0040c9064641e512500c0ba03d424540384a0058840b41010412104680600398139440781d42c5500c0d040613443c1e001180c10a801042c10b030000180b940110a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 535027086 1250 535025836 535025849
    0x7200a03081b030405010801140114030a051503061b07050709150f050109051806030f030414030601050a03051c0e04090303021b0109030e10110d0507020127090e16090204 75
    0x9040b44081c0e0001c0d8480c09544505808155401c00411581e880713650481c0003030704140740c40d401d800c02c80115005c0e9a00141e0707146501598410402466000148600451640460003010310345007030648102809001291440344100205a0704200304041007044061300d00c881c02030181190b908140c0317040311400d2050a07116020032400003203950007005045c0030fa038400340050403904c00001d4404000b460203000e16815108800352181440340a101410140c24800740704500102c035181014a44903041e000301d449227002400030030000c1d100045502c0c6c403440328504030300380031a021015500e015081a140703030041c0c188a80c4204041e4540d00610804e20064488902001c006030101d088600340c2c4002000301c2d5101c41411007916004003201040d250074644003020f00c1104000c1820440550340c1ca038045080443c0b40070442da0003140c84204030106404031a0810706600000820030540e1044900d51030b0341d00d0b00d20941e05002d01c03111010343c010100d603440c444c0d514001c0c0c5009502c20310035007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 535028336 1250 535027086 535027117
    0x270e1b0d14060f0703060303080c0f0c06010803090a14130c09030b010609050a0602060628030213020d06120b04020f1f08091204031a07030b180105012307200a0308 72
    0x682d43c3c4e8043d120b00001c2e41d80660750070843d5541c44ca000405a4020300c0540320000c000e10802c030a9520800815001e0960240650303281c00d00c0c0000c1c40f00102c01c90300030274040004034074407181540b103c0411101241c0c8691000c6201821080182c42400213500f0180085040720008190150082c1d00a411124113a4500c0c0080b50f950300100d89585003900d400b0f40c0800c8103014401d00050900d101c0c44891034840c0719109003562a070004480c1a002c00e00c90003060b8002ca0310310407550700e620450008040c01d44a07001c0908050382c03003a0801100400c000d00c00c451001c00003119840e03004290b01c88110061003502c80e0a00d60801502002e0100d800d40000d205503811352040c1c0c9202c1003550200e980c4200300500542904584540e09680102450201a91001900216551101510741440051940c4510740d410003000400c04032500d20004c8100002d03220668a01c022031003112070450b0090005d4600b009000d20307a000d404590547c079580250040710120900c8a500020700354110481d510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 535029586 1250 535028336 535028341
    0x70809090c07031b021906091e06021207060605090a090203060711032a010921020706120b01020114180c10091a13270e1b0d14060f 58
    0x48003000c0c414400010b00048240da20380844603004c00ea445820b510042003141d40d20a0290038082d800140e50044000071356568040044074200011441c040c02d00302c1910900609059020b03540c1d044c2202c600b034280d180014520140f0285500180150400600c08545030078000c0400014180c00c20060f8400d01407000805d07901ca0103084007441c0c0c410200061406c1400e103592242c0c0c0914010125170a40d05d0446070780b07004e020b081c4511512184140200440d00100d01801c5403a08821515503040d5440400103220003600030300d08081990a0f15004100c801c2000c0040f03001d000942c0355268410028000c0c4000003500039034501c0102c001d201280c0120700040100034050701c41c001408003040b100c4106101c0004003040b600160f6003108002407800b501512041da0f403000f0359102d80e1b640030505005141610410250010309441000d05010038100c2c04822a100c8502c120002e04100000c1c04903100341e01c401f210b0920071038200000701800b0041210031a26070034101c420700c2851702c10a00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 535030836 1250 535029586 535029601
    0x180f02040e0c0a0501030e0c04110406020d11062d15030d080615070f05120406030b01110d0e0103060b040e0f09060709060c020d0209041401060819080d0b0607080909 73
    0xc0240d0300b054000c01c42c0c6040e07450100190000c0c154000f0282c9207001c1d4904d45070803030f01e0724015014a40c06802407159501e1400c18024104004546804100104901c0c0c036803540a0000710503400c840c0f001c14120815031241007950181c41403841264190810100f089000c0e40e070484115201c60b0f0035003d41d00404000c003011206030308100c80c0290300180c05995280205111409040074520501c115812883c1544801c0e10700700b240050f05025410010f410f00105a15010345840341d5001c0c20800b043e42408045240c4640601f409042085017803006401c0c6a8400e0708440020000f03007070402c0d9a1a1154841050319808032002050b1581d10000704408090000320984180c5042e610b080c061800c20a088803c10003101c0c050303a102c9082c455080141e23844500003802188140d048480f0500d1000f005400d50748140c3c8480b000f500918072074094510f046405070b0600c2c0d4441a25595008a108558010644460b90035006440424240200155900102a00341003211200e20981c0c07086c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 535032086 1250 535030836 535030843
    0xe13140d1d0d0f020a0b04080f0c010f0e130216060905160614031b03130b010509011508100b07050a03030f020310050111010b040f0c0e030609060105100201180f02040e 74
    0x300840c2d005040035035008045001a1900082d8030b10080002c01e00316a21252061950040d0f00402901d0b00074410043e2488000c20454041d51800c0c00c040800f003907806030207441c00c151040d02074050a07040800c9001c000c1c5075070441d0409440703600b1650300c0703e4a5040882c01020b0800b41150180301c1c482008034840448900501264a9551025010b45451702948481d410241c1080d00d003488013410440005841c80140d80304018800d65019041503904003080300e1507043c0d2040703010780c0e5440014800c210140d031400701c120945081c40d0070291112103103101c100026511070500302501091040801c240447c000451a0083d5024450180e41c1c03082107089210540b038a001e00281c4108c100015401800000f40843c403100000403e40100703804507094542402c48411695078414001c150141c004415140d944d00540081140b0720300b0b0310000d50385100600810340f0689843c07084030300280c402d402030f6403030131307040044c60702d18520302d14240c02442c00702101240b28600b1b04004512903c03000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 535033336 1250 535032086 535032137
    0x40c021509150721020412050c01090605030a090c0e0c03042a0501110102071703070f02031602040e031309020a1215090b040b0904390e13140d 63
    0xb1010a51501c0310280d0300f041042c540400c95006980d903004a0702020310260004010400b460040b03422149005824001e0b6040010306121128500b400082c1d4800c0580354890844d83d40000c2e049502c1c00c05a44004203039000c0401c02000b1070412401e10030540207103010b2440340c0f074071400c0503010014075160032582d81119000104126010070040d88943e50b2000e00042d03c000041c13502031241c540c4140101145070100501c18004148420a5400401075102c1e8a02d0302c05507040000c640059221045440d00c0644125210140c00304100001d000319140c201c0038070311004005684902500103500300d00e8800010071500c40b83c0da25241802c1c080c4040250710300c1081041c15092052a20042407001a9150084c2c2e64400c100c070203440d92a001d6000783c1c0030b200c1d0002c8164990200280c2946105142000c04800340c502030801120f0310031050030790f440b07400c110000d0f80c0c6800240561035034004020f407c09580c00c076540011100401d21401c4894565603140b11840c0100b28070403120201c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 535034586 1250 535033336 535033363
    0x3010603021c0c06170610090902070c0302090105030106050f19050d051b0108010e040303051803070c03021c12110307021f090f06020304050409301704030804060209040b040c021509 80
    0x2d45181f4110044070132903a1076040c24020a1344402c81401240c100c10f00c12105820080d0041c0198034000c1401401094100e0081c040242850b02140f0000c3c8a0340c0c1c46400344140722298200640800040b001901000d041007480407558104941c0d1000c43e07122070f10801d40c0b0300e0380c1d8a01030751041d0b4809041e5400310444034681c3d2038036075085004140041c151041030011031703880340c2c40c44401c0c0000c10205002d80301d951070a50560041080b0000d00d1340e1010400c11b00051242c00003040c5196034038500001e410303d80084207103562810308610540b00025441009100041949504141c210054441e290380d6807a140d80c483c0e614985800a40c001d03900980d1003804100304903d03003031b0092210f20703205001c074010b414a408800c044809400f8040701403101401d4140b2101c5a00040e250241ca0802c0320300040342c203250b10041c2c0742c0ea0002c2c3c80508015000102580d1580311508078030701039403002d801040710b80080d28000303484503884010a160a2040404220200000515071114124 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 535035836 1250 535034586 535034627
    0x61803050f0c01060e0a06180203040c05010c1509240b0604051905040c02060612030702130903050912030309010b0607020315040f08040e041a0708070e03010603021c0c06 75
    0xc80c08110704050b040b141d00003200d503413581c0d80460000910085103000b9582041e02160b103038107141600040c80000410040224410700800002c40c1b45000b6a108440e4203081c4160214000d081c0300211502000514000300c2c18041c001d030401013509215000303804554540c00d403010000c26840280c4601c1501ca41c0d0018080c081444140351980038860801c03548a030310012244c0d05c40c0030405481c2201c10580140c1c0100d403c01003d07040501c1c00700c00f10b000c0080038503d4603226a00107107c90700c80404244a5907551a425070400d0f01030011611540d4005007044584204260099503a030f108849030b00e455401e05c0090750b0341e42441c506542203560300502074240000301082002d00c8840040064400465000390013000c5042e030390091026001d0145d02e00e0f45440c0c10b04190281c441640300e90400092103404000b915a0b005800329009451031800d81e0306544241d00080c0074150507040658080d101200281c81081903000710b940040c4510403028015940e4a4150b034110025840300d0950315 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 535037086 1250 535035836 535035847
    0x30c0714010e010c02090a050901020c060a0506090132010c061d0c06070b0f150925050403081c1d01060905011410080a02070b04050d1101050613020f090303030f010306180305 77
    0x7d03100d130012603000424200050400f4000e9210f035160031020346400c10b4483d600c5003440001c3c1402c1501e94098090314650101d00111102c501100c0d400000c40d074180040c40031507651450b03200e031000c901c0e00d6400c500180a202880c1210410980d101900c4030614401c40c0101b4456040160903503000359002a4015800c0e80d802c00c6441d0480300080c503090a0703115441d11029181e41d5a500c07107008550b646e110245403240801c00e848411300f502401030600005100800010b2545421900c1084010709810501c1c400940e80c50042d1580d201080121503144007291240901580700c1e07421200007400c14080b90341d0300c1c40101d19050440c4551074000c41100c0c5c50401d001e000303040283c0c000c0c2c0500d0b001450001543c03141c0034110360503070702198190449183c40c1400782e03120745d000c084805010001c00140c20b1050001c5e858025400d5000e52160300030178140407041e501c1c425281e60b450b015045c1c90f6a031600402c108840c0809000484880c0d00c2e0010202e10740446004002034207506855142c5030a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 535038336 1250 535037086 535037101
    0x80a03050105090c041a0417030a11032a07051f030510030b04080313061b021510060e0105040819120201090b0c160210050904060e06150c030c0714010e010c0209 71
    0x616031b0103a200f051205c1003000162400d2540302012040401601850319030000e4400109805440c42010005600c2404081c0110301d0840c03144080032150f40044254800070a0781e00c0c14401c05501880d0301440444140c910183c600c03188240401381c030ba600304110382d504840b01c0c3c60341d01680405018a4001000035000a42540055820035582030407030301100400d5aa08060303882110124034000c0c9003105101e10150100805907003d1034107224009140303490350441001131100e1251030304011107846945001e900034030803107002c1d013180310584800c9008210f60200590110b40704139070b250980c0e00d107101c4061040c440d8140340c541c0001c07070f60312944800c52105200c1d0001c490036094429910040e00050340c6e00e5540448044403502d50903154a001c00c10402103070426030083e5040f0000708104191039888030840c0007400e01d0480340b5619410300c4058140b46010b400c1d17866941c2d1041e81000319070455030842d442c4035404241e0311890402454801116946440e00000f508083c45a0210303400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 535039586 1250 535038336 535038359
    0x3280c35010b091302070602130e24010c0203060f0117030309030f0901030e01050403020120130302060a0e0a0b07061d060711010b101805090402030a0f02030712080a03050105090c04 80
    0x11843c0c002d00741c41c140d8190990200480e8003803001214810b500050405120304901e000200a10283e540c00038103192076414002e051525040152140d03801929900701a03000340058403804e074000d0200d074142d00d80700143c5400040c2c01e0103074040c82c1c00350140c40701e8014400011241716500200143d4103101900d40d510b4065000281383c24180364464107417100c0c84900344100340c0708a00a50001c100310030501e4084a088001d030203458500101080541c40390000440c4903400c485d415202295924655035046074024002d03040e00364404004003001501c07603101d5014081c003600503441080549003080d400400b0f0060440c03044699045580021a03071401030407480550071880b0000b040c0c80c1c222500081c029400199654040b4890140b40144115030104800240c08240c40041c02410590006603441c5070f480710003031468040d040340303c045440134011100145047c0c1c0907054603d0862402903840e030071460b07920700000e21700710000900c0d140c500c0c0400d0081c00208412483c29080940c1590b0303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 535040836 1250 535039586 535039597
    0x903020304090207120e011e080c070204020f0a020f07061d0102010f2903010501120b090c030d050307120504080406030e031b0a0c090603030503280c35010b 69
    0xa60005000002c0c1c0d03100540000d181241c41119407010102c01510b014103244c0b4030071a92410803948201c501180d0041d0620202a04141c0c1031500980d52900510b4105200340b105c002c0d0410b001188010150441d03070301030030304e60815800b03607022034800c8003445d5a030b041c0a01c41e4500003542c0c5588001080c07020244800c49440c18800070400015500c803071800e642100041c0c1d075035482d80c2d1148088200e0a030f51400c2418008500070b0049501d01004c110100340251400b40980c0301d07440c00710700410700c2002040500e21024046d00c0746212f060034050495042140e8503408218a000c2d001c030320300d003203104480c41164081d100500b094107150f02207000b01801018101644010410300031020035110000e912000e8003001082c0076021480c00741001c1800f58000309985040c1075081c0000be41180950364014004051034441c5400d004405031504040c076130240c020340c80c0c4181d080e0701c40e5205c8852003002c1941400e407100e507143e0391006510381498255503400070810400501140c3d001c54000c05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 535042086 1250 535040836 535040843
    0x302090d11010309020d0c060f08160516170301090e010b010f030e0c03120405030d1103040b160210120614090a020702030705030708161410031e06030f05060a020306011209 76
    0x140070710b44c0d58003050030034080710000e5400c400d07060300030001c29902480501c2202c1941c51314078880d0810803044044861881c0414041c060040780070124440812444520142c0140d0703412140307200d40c200e0010f0359000780078050b03026040909010400c5014011007540c010f042c2c0d6807140c03450300b5403c05c43c02891035072103c0c409405441d00081285d50b04000c01a0001c6e08940708e25980c43c174243c02c062034107400c1d1220760140400c0600c0d006072224040300381c030219400c10000d00e030707102064003092801c880344034002540030541c6043d00180d164410707202000681079920400120b600e5004400b50204d485406603031205040000420b091001e4000d0b008c40342c4054112028584c50b00002824032100c1d801000883d48171202000075560001c505400a0100400315050004048045100010800c0303012060507141c4038003c4614841c80103506820044d00c00c1000903035104e2605d00003150940740280c1e00c9100e0100498588801482100c0c0030790030507100c2e00103c8408181d800c01420701c0c1c2c0d5003503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 535043336 1250 535042086 535042091
    0x8041e050303221502070e060307080a12050409020a03240b0a030b03030d05010b0309010f0506011e12020f070204110a090e0a0603051b241b07150f08070302090d110103 74
    0x404c80010b0651800031410b54010b08040340c20518030490034000100780501c01c0e44848820802c500300881c05008280d045820000300c1600c0c541c00356041e06c21603020080b0035100003900001c40b50315600040c4646100301d00500c000080310840881d00750307103000f0b5031f5600d0ba00b001030511082c081c1e4400305000d00d002d41078a040c5a4802c00385821548242e0009012000004c100613400f1001e109018084440000420040c1030400000f0700120707c000e00d000803105290000e000c0350303015502c19100b4500007070065544600200032031015800202c0101d00483c241010280903c4000e011b0320421201c0d565500c0d24549010710203140c050015188003042543e0b05404000301304103000d601c5e01004458803541c0c0e00c0506800780441142460304135000c89220040c804182c17203248040310b400d1040048003000c10228070b00c10605042039503200b09a681080030b80d10010a030031200c0d4001030705854661207825614800141c06a01c00d80011651206521010b640007415010500381c0074001071600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 535044586 1250 535043336 535043339
    0xe0708040b24041b08090a0c0e04150507230c1c050c03040b181e010e011116060f020d052b0e0c0f12060f0408070803010308041e05030322 61
    0x440c089840c01c00d81c2c200d0100b10b030f1110110517a0000402a0800901001000104c48a480c2ea10411803a8020912810031440100301441140340c1800f084011041c020003d5041900c2c0241904540441e070040120b4001c0c2c54400a41181058420f80b400350409040000143c2d180c0c503616000811a0f8800d204c418040030203a424100080d101400307410ba111a60380d000c551414400d0341000e1a80784c4919600e1400e0780c81c0c0d502c05005200e0b007403001e08082a410f4861b8005a403201c07122468103001d0b20400380c46205c01c1d949401000f089038003075103500b214041030340e000301d80750b0b28a0440304021038000c10203030328047c1d1214045203804488243d0380500040d041c0303009090380e042c00c5d0103400aa2000a030818580340c2682c40780b800300340442e80b9286011101031241d485000041450a2074821940007905111000701161921030740700894079a00d6840c0e00c2c005916030020300a0600d007141001a44170800032505041043d900010000c2d410406e4000b0b80019481c6820078020308030080010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 535045836 1250 535044586 535044589
    0x5030f03091609090305070f0203030c250512030a050711090c07053d0908070b1f0f0e071e050d050c0f030712020910090e0708040b24 59
    0x3450092540c01e0140420a01000e55980480e01c680c102d8503109152856880c0040e030000110342c11300b54496031841041d8110300000f0f0540c0074900d0300e00301501803100800c203000606840c24603003004c0502e010840e00d865101388500641040ca600e0300c2c5a00030020300b4075185c01070004e005058807400c00320340c0a001d0100802c4030344c0c4081e5a03103034080c0400f080c0320003040b0041c8501c05015007142d81d1a83d01480c641c546040d91715042a0f0740683c11040c4c03961a69402090704400c05182e0000a1a5602c1c11689001030700504216030940c0b960907500804400c601c4104080400c540e40b5841488025092401070303400481c014001000340450190010609114407003903c4100003d601c1d0303251186c2d1204241c03400c1e034100400c03881c0781d540c0404c856000e02c001203007940d40110061070425108640b81c09010020704c00d42d50b5450344403c45003802010340361300074040c000707690401203086030b9501c80d003006480701d81003a240100b00c410954002103a0f02c40398a20115000211408414504c3e240c3c0c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 535047086 1250 535045836 535045867
    0x30f18021302090d2f09010b0a0207030606030c080f0706020318010c050a080309010b0a15050a0203120c280801031202120403080307020c01020a0c0b03060a23041d060f040503 77
    0x144100c40401e511855816404ca881c1007a07940c0085c013101040040d00351741c0020b550201c0501601d0700000c4c01081d5801014400c000c2600556840f20003042983c0c0c0742d00f00380070188403610034882280709014403058481008143c0c48104d480030340041d410481c0940b26507200c070b03801101250400c070f01e52001e040411420071910b600c0c40d008a00e500c0d96403c0c0703000b1a03400d440d00740074241d00584408400308001208428030710b640380400d141c807a27268102410300b00e0951042d90314543c6400d1900d010312040e0609407000b441d10008410307889003400399800e01100810f20541080c404210030400400105080340000349060740c141c8159044052003040e10ba003643c01607042940c00a0000c0104101c1e60f030104120346126000340010400406581e075240b41d180c40b00e010b60309440c94080b02048140c0c446c0049080581100c5010240c034070250b13240c01141d000c0070400c4911890510052340070701d408401b1075000c11103000015110030307650710018200e000000f0707004441e10b1004012028001c9a82c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 535048336 1250 535047086 535047109
    0xc0f0906141908060906030109020310050403030204050a090b090601080c0706090809030f01141e0a0b030102090406080a03080109062114070f030b06010201020a050d0c110616030f1802130209 84
    0xf03442c0c86025003026004c2c0300500d007006129a029a240440c03a0016940005442030a244a800c011170f2039581c03450110064020340d484540c100040e51400720b9a4415504941c0d2030080607502d02d501503841c0700c0115010074090f80c40102502d000c020200101d060354010460386030052106526010151000c03034503025030003844e00001e035564400e841c16450500502a0400d008004d80724495640e808180c00305400602b14040042c1d540f040c01220351800e4050f2200624010000c04c1f5050f07407408003584aa0b81450100c000030244000801c40100c98803402c03064400301d1400340c401308080a03464001b41210306055460066442c02d40303c3c5444108007080250419582d00b80340c040c0b81d8505400032450141405041d0790040c08407a850350b5100d41554207034000391401180e07240c40204103441c84c03010566155810300402080103541f0b0038048441d940c2d03100326034080040d5541254010211003040b07140d074003107002405040015107442046070342d0040341c02000502d0322a0010000340540000d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 535049586 1250 535048336 535048387
    0xf020f271306090e0105220303110f031f180e010b0405040809090c09131a090f18070b030402101106040b040b090a050a141002160203010c0f090614 65
    0x110001405102d03c1030161000c8004000c009012900f0000500d1030302850460054a01800e020440070603d803094204c0310340602d0700b40c11956190411205042c565104859840c0300c250507030003038051010918900401c844805021000e10b0026180316000360002d501e0544a81d03407202c1e0082c40d99543c030310030a400b81e07214801d030359511018242400200714004180000d1403c0a1121140b15241c40d4408144040c0c070401c0002c50030304a60441c200d03401030350402500079a031441080120120512454081d411010454068200d01030319540d542001d40070f40301c035100040c008a00182803050215900c2065810680040c1c803c400d50107140410407075081d28000c2c620800d100900c88103200a0303400900140140603854031a80390a6942c51001800411220403510440f901910a02845080200c9680c0642d90340c1ca0013032070040c60002d012800e92280d4a03044040c104540034440021080c4c884d0b44550b49a5443d2403804d0740c500c24402d288a080010800040840c4a001c2003030014104c0c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 535050836 1250 535049586 535049591
    0x1d060a06061403240a03142a0102030d0209060c0f03071e050a0f06020c01061706060a030312020306010203070f260301050a0b0336010f020f2713 64
    0x80c020300142200000c0c94000010001002401800d504c00703050b0010309051100c03a440c1c000c114102007070140744d290303002500d03404401e0b100440040002c1088030800300702c101744015981c0c0d03580180c40c0000400074040d000d6402040700c0300740e900041d00a048100390040c10142806034a6000ca810070048494030f002c0c035000002c000f810887e4101c4003408507085e044200c07200304c200340d40340342d0f44130310600d0080c0c6442d07040000d050803c401034044036900e9070001c3c000d1126641d2022000b0102038a00c400c480d0702c3c0a10f50005809041c5a20444200c0c0d81694500041100071103c80b8002e51003c0c09241c11030204200c5000810222155000100e200325040c64451810f890b02c0c5812010801d4005040e05080004101550310080d001042d20f0039004a65920f440e00c050821440011640750224074024100000800401550080080010030020300140b2170b0b1203c514202d1048040e414200b25007488003280d8111001c1003000741c074498400c2074140c51003030703030001d10b0200080190682003074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 535052086 1250 535050836 535050839
    0x1b03040c030501050c04120b04061517010522020108070c06090317060d050c0f2803050607050307021e01021b100b0402040f030201050c1c18150e041d060a06 69
    0x8001d2084903030104404025501b0b0508202000f8a1f071903040700090b00d1b992002c40850705001040d4001140007800c032010f216481d0352000c11503c40307080c102040c5015403804c400140e0341c03e0f0b0b0032444c1e03000b81e80254001001019550065400c68809062102040030032658080060000d2140325103207802a26800540482240220304464006282501400ca8203041000050f00004c11860865080b5268652400f034140410b800c0e280400410326254005032420201c0c1e00c0089807182500c1c012019104950350385501900c1c9440156901d10040e488003107428049401032541e6080c911400700058034010507403522011020b52441c9240f115080424a591162201d2040c168003403c15134003503041c5841c2c10894082e003030385440044d040c0040060303610301110061282c00c2041034400b80b40703195901603a8000b40401c448084014804521160100d5405550101c8a5102a16580c1c190146020380c0600002d402c1681c50308119406c2064040485401841000d104d200c16120004c6c466 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 535053336 1250 535052086 535052093
    0x3030504020a060c0203100b01030905010212090106061d06030c0c010c0807091a031501090b070b010609091109152a06011502060103120e10031d0c0d03081b03040c03 73
    0x2101d650060f001d0045020000005071008140d180703e040c1d21001c001411050742006030702174036284400a200b540300085011628011407400d600502c4c00300001c003c02c50300e0750b0b03050711100a50b040007000454151340c8401b0624000006507484403c0810403400c3c240c004134110700f500c01007009080452080000c01456a500141d820300070900602982d14554007091404168400900340f502da114003c045210b446c0d0080c84101c000b402d0314940c56551341540d003803880802200b03000f00700000d17010306400590700000c0d018030305c2c50310251440d0314030740230f1135038104801001102018420030000740440d404c0c40c200e4a501074043c80240750350396a1a41c04001450601d101600102d0202c403405030701c00c041036400222241501d070311070100c1c2c42405541e007042e12803844032000c9940c040e801c088641071441c0d040d0840c0e1034601c1803024940018183c005141d45034002c904820340c000600c0140300000c00d1260b0442a00419461803084204d03590080c9090280d000b1281540c181f40342107802c1040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 535054586 1250 535053336 535053349
    0x31b03040f24050714040306090203031902030a031104061b0c0312050a0806031902090c0403050607030b1002060702210702060307020331060c030e0307061107080316020d15090303050402 82
    0x9210f5103845c1c490701d0300303c901c00001e038044d030302002d0811650351074010115282081119103061190402e10059418004025a80d50121148200007401d10402c5107072446004140c80c01e507002502ea0764468203002c561003070a8941075030140d412640c01a0000049100e20300d592009a10070b560b016510400c1c004082c02e00b590143c10b036402584030881480b100ca0142d409036840759411101d1a00c1502c43c0c5046440c60301840d00050282d000344002d115030709800d9800050810001c0e1242d10110b64110740503a2500000c0300c02801582010600300094124540c9030b20290782d00d50381107400c0c18029004214550001c41e100c8015900014019a591000c0f40120000042c07900c1c100c0c621042003600b0703030ba1494183c8108410700502820b54002c150207026800c41d03405c0040c0840305066580c401c0103115031800000c0e42401d0150800210b900c3c0c40110803180c1c2c9100703104658480360080e03030070b00009012404047c0c440e0941142d070700842056030b00481c2180b80c043d03a000b003100c2c102030040010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 535055836 1250 535054586 535054591
    0x2406130f1a1f05031902030907060f260a02040b0315090f04050304050103020a050c01181b080a0807061b03020c010b0f010e04051b040b1b03031b03040f2405 69
    0x1140c0e050808002d106240320100030342c903042c2490300c6503ea880b0b2030b0741145002c00140f04012410f00100801400c0300e0002044001c9880765030b9524600f07100071002790307411540c12411101c900401401c000544500c00c0f5941d4103c0f0345440014900b545d59518801503820940700005002c25001005001e442c184d400b20790410600380d10500d05007099501e181d81c2e80710720300c5054141500420b00100080c0188140d40c1035224800c000c0c445100044901c0d0313034541100c02c0032206180b44005844101c801540c6141c10b80e55114010b29000b4900d44496400d17400c101c0c0215215034640340310850080700d0110884c000310b550344015071907010002a03542502c0d412214a4020300402c461019203070782c071441c00d031164003082d0b0740001d4984403209a824080c40c45252310306421400900001d1510151000340b21843c51800012007040203180d8103600e0f03120a07540c2c101c00c6018100340c2200050711000540e046481403004045003609a6515011601c5591100000280341c0b9040f180d24002c6000c0c040d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 535057086 1250 535055836 535055839
    0x1103070f0e19081b011b060902090108010b010206070e0109140604080706080411040903050f0d06030803070507140f2109030a0c09050a09020a1214030d060303112406130f1a 76
    0x409240401000030242c0c1c0e000303003071250104246c59403982403000035889001110f8018000d152070b0360311000c0c0d45000e40108141640148100400228154415904c00d251404169201c058243c5410300300c42035441c1c0c00340003640c00801000000b401080070010440107224503102c18620f85400d0420142191501c060b82e4081c60512880c0c6000903030007400c070b0702c503079141900294131042160b9481004240d182c20040c44140000180303c440d58202e0083c0003501d1050750040881c0082c00b04041c3c90340540d1044070b0310f5a000b001085050044480800103a05e100d20449003071a403080b00091501d40d800c00b060307a40804141080c00b40c603803540074144c0c0c88601000300b40b0141115a02280c200b40003031050001c404801040d40c010080c2001100014043c6a821262508400c8074040700178041440304501054807010f2821703a180300400c0c905078544003200c1000302e00711658084000440c00400c01e66004040c03608000480d01d0ba44034401030b640e09800000381d65a4a43c15525140c1ca200c01c50f036 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 535058336 1250 535057086 535057123
    0x60f0f040b010902030a02070f0b1b04030f0308041e0309030b0c0a090618180f1b0206060f01110307030906110a0f060902061308031c1103070f0e1908 66
    0x1002003182281c105044890015005a4039600c01c44d00b0b200a0003000001800316008030031102c00d010000c00707002e001da11070101d0941030142c0d40e00e080c030852140d440f0013040c608101120300046130180c99001d5005000307626500c1c40c000c060841205124041c48200c002c00d03420b640030b0081c8410754503990751000200f42d9840c42d0a0803a00c0107055910741e4481c00c410048503050001202c4803400c610401050402d240880000d440103120015203003080c001c1c0c80c2c0500c2c24500c21210043c0b252280941c0107280c002e00f1003500c0b0101400080d81d00c6a03800341c14081c0c04034100c40d501300100001c2c64030302c0c0607641d0340d5005403c0041c02401e68506040c850307042d900606640c0003249540d81508499980201e0004d44040a4408503000d0f00608624404050340581c00042e41c000200042205064001504a05036517051045048070503c50142100e80c0040c0001001640910302e07002c4282117500340b1201c0000060000b03082c603010a070080241c0001c01c0c0301007003110310800c02402c201d450200036 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 535059586 1250 535058336 535058341
    0x30708070c0f0f05030c0d020a060b03010b0a090b0406030c170606150f070c0f0609080c09040c0504020903010609330b07080315060f0702011d0a1a0d0509060f0f 71
    0x8002c80c01030840d00c050481c00404601a081000070002c550145c0442400e9607900c071b062400107900e5800d2841e040e154030b0300b00748a03c00c040ca010701c5180031406e0000c0c0303202d07885420700c1c600303d0081c40102d0754240c000b591800d0200100e20306106180c028458000e420010b444108100c03401e06002910031030088854014103a203900510080c0c400410039903603625100d82680c1031010304211035910030070034a10f00b10b40c04942c03542d100c0c0b04c0030113541004040700c070540f0040c014800c0201d0215005072840000c0c440520440c074203074009003408a002800890140c0d29103070010202d0f43c034100c45071a80407071000102441da181910180c611190340f0854081c840c509230340e10101e4403c080008041e040300000041c68020800861701400c100a4000c0c0d0b01c0711102e0307111005c56403020b4426070205614102042045281203604d40000a001d080324899a14220302ca048018412800e1009210180045494a0842c2c4a150b1151070749100400444c20843d08182c110a0007a0503000c41d003800b03104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 535060836 1250 535059586 535059593
    0x91a040902011d0402040905040b0105090c04140607060e010507030e0f0a05030d05060d1203020a11061e07020c062205010c05060402010e0a0815010e010603090b0604020a05090a060203030708070c 86
    0x2696441c40782c80038401c0c0c1d5240c043c40004d00034800d036040702884628241c180320500c898202d0043c142c44068505480c103456081d5021071600540c4200918507141d40c0c135950181c103040003e0900988070b13002c0480e130750900074419030070746008440d44d400013a9204501888402c00700708580c1150301e00800341c101c442154545545a104441904040700d4446000c03e50f2500c5a00703040071102d401c5000d100110b800494010040c0d8410442900002c0c800310000c1040b0b500819254080c0c5440890440c9030f203c42d1140c050300c07800042c04001540038a45c2894020786441000344109000c00d4880b070000e20304003464031800202e54010b07074104000c0c0107070304c0000f9500040d02030300540c0900304210140441c40015100e6042c40e00310070740714010100c001d0448414444101e0580f601c01403070351026a2584005c4044500c241c401034840203000d130200d00c1604050380144064407041c541a03107401c141d00c02040c0d0b1000154440401640000200080240c0c0402c1f178a0704000140341650044a0b6500d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 535062086 1250 535060836 535060847
    0x290c1b0a2705091c0f090510080f0405100606090e011d0c07050319020d0f0503130b060a0302060712030c03060b040603020309010e010e1f1b0c1407091a04090201 71
    0x10881c10055a580045004240200403160b00b9030601543d00c003000030324440c014000c14a0f014000007145040d1313004501131a00e480d0450040e40203603100b0100361380d010390710400400041c005541e80d00850311341480f01261401a480a0103c945944140900d00b46103240d000b45d0590154103108800c080c00d60000d041d4a10940e000424044030903103503082d606100d0305511034a503111002240541c00c4030111500490074003401011502c1e41c041240c1040030564151004607101d8800182d440c0c2004005501000d0041c2c0120019002100c901d80320703404070350a0b40c80004169803001220302601c0d4440e605000309507039003040e071400b0b010071460700003203c000d80240c0c015241407540110000b900700e0000d500906403810054000c1c044408003030a141d0310392600c40c80c48980e502c7c030480400c600503454012141d10a0707000302c0441030908014011690070b00308170f8003120300040052903002403090401c11000603056807880007035481d420608005030725084007100fa0190341010844000741c1c2c1c008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 535063336 1250 535062086 535062149
    0x80a021816270603051501020703120c0302120304050304080607091404020304060b09010b130503010209060a08070c1a0114100903060507050d091211030301290c1b0a 73
    0xd041603810b500000d105000c80c801c10401c1c0d507040105600c000501c0c184d060b040a805803071018101e005a50040e0012030301c0308401e01014003801d54241c0d07000c6807a845801c108031854000c1c03040e1031440b40e0601598400e80d1041d2030961300c80d8000b040600c01a0000d011098029a031f504214000c40e241214088403544510f014500c2150301200040c18449250000c8025083c01000b078006980c480e07601c8070860300035280420000102070701c08036090a051003240c11028004000600380400303c001240c0c0d02e00000c281c801086107009549001800317014803250244840b805814856040c401021031002c900d9080500c18a42c031100f0380700440d04521600c054036007100000c1041d54901c41d05503444c0c441c02d650000b0703c51903c0e4855060200c0c0914003120060300d46c0c0d801c051920420041d5640c0d00003030140c1c14040859581b4948000444041c240c55122114111030a0801300b08010303041421001c03000d2500100c9194012092811305502320250820703407c444220389c80707000c00c0312400251 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 535064586 1250 535063336 535063381
    0x1208090c091504020a03090b010609050603060f0f0607082503080f070e0604060206060406091e1e0606110717150a0902040c09090b0a15080a09060501080a0218 70
    0x803040820381c80d1200c2d0031818a81c21000c1d009554940540c00002e0040000840a0703132a404400004607000e44034818110454400070411800c544603031080203000e08c4440c0085500031b840c016541007075110b500141c4482d50250700b803940c070341f00030180f442451032103864800340c4424070803405400070350440c401b9034004500c002142140e54400750150ad68148110000b5804000443c00003211540019024494074043c1e40510910350f039031100900359402c03c000c0c40c10b90381c01e020340040c0c6501160f0064240c15506420031002102c0d4910b05000c03160f00d44c000c980052403888051040ca85c08106410040c420030303000b00040c03680f560f00a9290b12003015011106c40803880070410b440b003550004c269640c0c0090003002035014505002d084a0f52078401c0301c203070600b070800514142c50031410034805c98451b0f501c210704100041e041116203901c001e054040c5150380f0444500460b00e544101070182c0200700052003074100c030740104a01c218401807007091a0055800304803240040030b000e04e400c080d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 535065836 1250 535064586 535064599
    0x3f0a030f030e07053316020d081303121106070909240e0712060b16330b12251d04030e0301020a170c070b0901091208090c 54
    0x1902e2003580d0070f00c4040d40c41568088501980ea80080d4850b01c9408581828565002004d822901a11180c2d004052902500081506001c000340c201a03100140041c0714070301180c0380c2821421104c80d01c000c039401c01d44405260038031075800c0641080c030300300590862500a028070300e4000c2004201c5919801740891850710b40f845000c4c031001c0d01c200c109000707190701c5510034066103030110b0b5101540b0480f8410006541c40c240c07000c9500d620701c030b01c00940310000455440d2252903003540c2401c0103054400c441000c41010003104d0420302c0c0130302641100e42112030f42d049440c03006001055a1b0b400410034800c6024903034440c503800c0e00003480d1001540d2020300c0301180360314a00c045410842a4020614010400301d800c5280301810a514800d500c00e03201d0010400821061500302e008159201e004038005140d00203444e240c410b4042d0380030780041c81d030350320b007401c46d1351880c0c0403040684540c0b0050391101510420030400c66244401d0100c503142405252400e01011651001c081c019a402040d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 535067086 1250 535065836 535065851
    0x50c0913020c0316121404030c092c070303021e0c041d0d030509150c160606170a02130c02060c0307090f270b010c02040b3f0a030f03 59
    0x4400348165100c0702d450003810501c01e9920b0030117003000f6100e0181c1300d0001d6143c00c031001d4240315060940e4240c0c0d400022560700d280c10292204020001c004007141036440d00e42c10080055039010001c440c184081016010242c6589406813406c0100b5034003a07080941d4100c1c9148504000895010030001120045001c09060101c9643e018803004101914090071041c3c016080d0560002401000400102c8244020b00c0c2541d019480c81034448104800040010f03a9140e41111010040a0701590000981c50f80c1c680061000810301c02407900c00e0741100050506502d01000000264640158180282011240e00a48400c4014112300703070104080701250745c50b4890460840941080070b14079804d1501c42c11a50b11900c0c4a59103140d41c1d014501c2055080084e40c01006c414260603190048490900d6003000083c00c2456401504004a1920f0038000c02c480c10100f030003101c0c0780003c001900341680308900c64010f4089420181e80c4841d000e000001e5006401c3c104203201032400145d100f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 535068336 1250 535067086 535067107
    0x302040b0a2105040c0f05030a03120e071502010f0f0e070b130506040906090e0c0f010c15020f03040218010614090d0f060e0c0d051015080a050d03050c091302 70
    0xc600742c07030b804080d0914050810003041580402d8800b91800f80072902012552601007540da1a04124010001042c5004041058519070001218460400e0a903807020340c0f51000c111034010708455180c0140e46030f030101c0012003000e114644264054980030300041c80401e0039940c0d540345038847c1d200d9481c0e001030302e61095180d242c44a409800024841a41d0f16902c01204000c0c01460085481c040d190003000c145001c000074a51140050203841c0300c025070035602c015168113003100000d4503241d560800c2602103408034401080120300d1540c5803601d9052a0051000460310758248049190110006001c529005a051006a903400c20442ea4552000700485c100d030880c4513009000c441e4280c42710082141c0754100c10281c2c40e2290848003900307040001c00c11200d1280c900030f0029041070102c07286108407030f00942c880000681c2603160b9603581d01031852a10110700c0c0c040d1401d4000e1410341c40742c107605026480d0050005601d5a080c5170605e03000034809a4a1081412000e44c0044c0c0300c0e119 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 535069586 1250 535068336 535068377
    0xc060117160902130905040f060b15130303110303090c090604020c100f0e0c06040b03070315060f02060106050307270503012c0105010b0f0306030a0206030108030a09060302040b0a 79
    0x20044070307509880d00190741c1e0314014044e40040194031807440c40e01038041114a800d1081c1445603810002c011580345940e1100c0005054002140b0707001402096111240101a001400c0100c84060090202442d40c20000c00d03010a079880b03007070035820130401e0102010300010040464001190844d159071039180010380281b00f003c9100d80d06028500209a4880035075012122107410078400340f01482c83d584200f9183c403199900039074000005e00c0280400c00074400950341c0301406003000102c0c1078680d00b0b05500e51810394841e80001c0d1b41e00350a100203582c1407015038010b040303504245085042412015210003960144100d0801c080b035202e140c4070109640c0030000381005002006006109401d074540715140c03038078004030b10f15040301520001e80f05100300382c100d5050080480c140f031702800c0000720320750010340542c2d0b0606c107005a00000da91080015030080525200940e40e8201070380000c0c00b140407550212082c948180010400014460b045609280c441e01d00b05005902d00c102d410340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 535070836 1250 535069586 535069603
    0xd14070b070206060f01020c0117040c0905090d0f032c01060902031f1707030f140319030b220f02041a0a020609060c07060c020a020d030818030c060117 67
    0xc14540c0400c0c0240300740c000c52140e000341d50a480054400710a2001a80d90724810b419103400030b200125011500b80c100028113400c1031140342c415080d1561801d100081d40ea05551400d9190001000000840d030000c60b482c40545607420280240700f0103d40446452415403d52480b08038101d0340318814940a501100242903000170864917030408a03460310240541c10500040c9101402c1c0205486241d440c5240003000101d0040c02ca440c15542d174215540c1101804407203480c0801411210b400c2c060001d07190b00a501131244c17000e1400040000c0c2a00c040c07082c1c0c5c60152074040c2900d03404000c001c1400600039421100070903402400010080240708540c0400f01e5191000003003060f01e034003400240844039160742240e140d900d400b40b544c1e49481040d0f61407403082c481002004006010364206052074131007030040d0f5002a02c035402003010703164011401c5001400f41c500b08840302d69682d06202c80030700031a0045050030320032542d6035a5080e06025611004400707100f06030f03080d44104070840c13 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 535071942 1106 535070836 535070843
    0x30601050a0504030501050a02250b06010e01020a020d05031201060513031502120f10090902010c080904060b070308150402090d06050a0f15260d1407 66
    0x15001d522050281090003024440000800d9080c400c007480360108100160b035511880030888149008210307852040300106c8094008a8802410150b1004007800c006000c0520100140c0c0380c00032a100095002d42c010328008100a00030000c4c102c1913940c08044c80069807142000d55150080d0104d8003c2031182990800200b0f221401e41068000b96040c010700c0d00d0b14444227100c048a04488041c0c44800c0d4070140305001c0540f1464074018506050104004100c0380c0c0000e0a05106900c050301180011179084110380e0f4a90091000305903100c8172590f0351070b9500d00074040640072240c83d90040c1180b8440301e031b641001c0c02141c040c2c1a0013003c885a2030741c2ca0359004014040580940d01250f0b840d000410342079810f100c0c0075036110703228401c4e078050703442c025010400380c2071038000f8002c41000441c5c0e101d04040004200c1c0603081641010540004091040c4105014020000c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 534892086 535071942 := by
  have h0 := BRFrame.cov_init 534892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 534892086 ≤ n) (h2 : n < 535071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
