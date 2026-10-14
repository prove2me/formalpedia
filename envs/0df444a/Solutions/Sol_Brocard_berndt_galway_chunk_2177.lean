-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2177
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:53:54.648886+00:00
-- url     : https://prove2.me/submissions/ea93b521-994f-463e-b2e6-25bfea7f2d0e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 391366906 ≤ n < 391546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 391368156 1250 391366906 391366933
    0x30708060408040312030b041a0a1a18041b080a151a07030c02060a0c0b09010908123103080a060302010e0d050f0601060f0f02030315041e0914 63
    0x14030314416a44648068580780c2075990312a5001e680580c880189916103130108032603552801820a0a4507104090408041c0c034020001c8500e0107900c00422950201480b101f0603074a0b104a44407901d07210700d80086000003001240c018440014004440c1c0751a480b0f502015501c0b0b000e42d801205052001d0003401d035a880003140015883c480c0c2c010b00805003404581c21424400603010007400390070300c03111503c0150040f0709140c0c03121081c0310015031546500020070138a00d281c2508203c40c60000c000501c0e003503658881a124841c5d016042a0200300080d04040718011341500300c4a80107140c1070100742d00c01020b0000c0d240f115044010400c020001495014280304d02c00c101c80d016514500500f96240a0081280b8a840b040d074207402400c1d69009100c0e0100051170003805541d1301d04040f07107034028009000f614885610811908100103110411505030002c11580500f01c50004218a5041c8500000740340c40780100f44042c1044402824021442c40d015901c0255070203580e40c9025000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 391369406 1250 391368156 391368163
    0x303020d090e10060f020c04060308030105011412063001020307081f06050d0609020c0c03060c0406020a03050d0207230709060e130f05030d0b13050c1207030617030405030708 77
    0x440140520050100c104441445040280d0740003c5e0740c01030701c1c01c0c1103d4802040c1600d01a41040d116008008010402560300500c8140e4041c07040b0300b01070030036045030399400c142c02019000a100380d80440610b04280324591310620100d0010107050b1a0208141499000c0e420460300039010801080015440c601d007401d50012b030708414460302c0c1e901801c0940c19205034002c80052880e0310399413180401c0a96281c8000c100c80e00000c0000c3c15072988400426140c04401884024440c009000400c040e13070f0000381040c1d480f81c0c50b0400740e071600040a450802805006070141540380000740701100b030000544005140740c4110203648616440301c0d03800003518000d115042c4d9a0811000091314605110120843e03184101e81d20340d561b00031030311202e240d07800c040001c508840d45e48071041c0b46448c28a002800d100b0f1034140c18891840d01e01102126401803c82c0151800b0110001688070b0f803285c4e01005c06404407025050f289000200300542e29041401414000c0c070920f0404a0b4449000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 391370656 1250 391369406 391369411
    0x601060311071203110409020a0504031502070803010909080f0417060a2007050106030b390703030914060c04080f0304080a1b090606030209030c0904030f05160c0303020d090e 77
    0x90200750810683c1c04400030701410500a02801741400041a401c804c0d000411030407141741d40d40c1d030700c6034118180700c0c01007031805120b062454410050a00001c401d80150703411611003280018030000340e1f0030300900d603100b4071098007840d280005c1c0c08200d0742c90316004020950f22034012200ca81c0d0312003a0001c00c40d4030420264480b0314944002180d45100034000305034280c810000411042d58039a58450107650566003500721200f199403040016030900040b225401d0f1070003080c40c005190601c4200c0300e114203100030b000c144d00d5505d50424010004203083c0c41d02100001ca881d14900580302d0015900135001d1103031a40601c00558404100010a840545041034054004003129a0b1001591441350b041a500340c40d400b02c0004084034140304890080110761805641d402c40e05080504013445a40141d101d900901c060001203903220000110842d15801e01c140d450200700300c01107440c01601b0005104221307009c0c0c0401050750100711900300d41d800303440f81c000d41c0d40ca440240c4401c8404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 391371906 1250 391370656 391370663
    0x3060c0c02091b071403041a070317071b03031a03030309070b0a11010c031b0815060d0e0106031209060206040503090d030e03010504060914071412120c060106031107 73
    0x6880206440801c0c800c020000080c45801d9207182c6a0665201c50504040120780c0170280c2002c00c08000b40c0101c2c44c07445240b65000e04032245000202c1d500508810b0b05035a04002c9005404000b0303510038000c21700035201c43c1c11603e007589107403003074034004015000c00781000c003500c414240200b015060000650380a08080000350103000c4c10003c407548181c100c040036408006d401c000c1c00001c41030a00c58a80c2005540e81c0c04600d04044145284501d103880c1c1084081147e682c1c10041c60b14260241b03084000c20454455a840086030805005032400403075030039865180030000820014114000c007069091a00c603000a2544c64078140d8807814200c030301400075007003013190012034a00104000280c3d07109060549403804540042421601c08840c111511075907400e5003020300c1440c0c11070701c4500c40f0f010010080c40341403046502201c0740110206020321031240b105602c409090000c0c65500d01002d5115840d070340702000165844e8002e00c141c8020034034000c0c140080c001c00c1011104032540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 391373156 1250 391371906 391371919
    0x6050f03070e130b090a020f150d0903021204090506190b0a08090313141306050a060c080708030c040f080c0f061e0408010212150a1505070204021303060c0c02 70
    0x20b40480c0740885040200b0030b04210020a080c03100107801e07050210300a003158401800c200100d48107002005810741d00309407094031150785081450f0614070484150411b4080080391842d85449c0607450241c640b46004c04481d00410302107280e803002d510892040f0300c210341501451441080d40c48040c1c03210f00401e110705004108003250580100300654001c1d01d6041168601102002c2d40301051181e6085124107440c518000700ca0307403034002401e0303104603120001000f03220b2802c80001c079013121a21800007400441b00103181071080090650f1344440e040301c0d169030b403031070303e01c091654607409400383d20300385961404041440c6e840050784401c1243c014007040c0b80e580d605030401201c0d4008419281034000c280c1803105610606501030002450f0400025803034007a1455654030f410001001f210036100b4100a00c0b070b0799a10101e42804554504a000c0c5002c031070742c08112a544140203010b0f42190002818403890081c020000d41204e014020411140340c01ca8801c8031710410104001c1c1d805031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 391374406 1250 391373156 391373159
    0x60302010507020d080f040e090c040b0a1a0f0a0c0c09021c0b220b040e1c03021b0610060e030a03080f0601090909060b04180f2303180406050f0307 65
    0x18146507a11103136009080c05170602402e589a40380d154000c1d000a611248140180b1a800d03008102c0c0441c8503074201c4007482002c129001180d203074219442034568040c4000030100c2c0c0780d242c10040f118000104429590344665044010381f120710f07022401c841b0b03803401c400700003681c041a209840501d0000e0a214240107107048981020b0403c18480703d500c00f80b0011455005904409041f0450f040c2da03c001c941c149104c8200011102d501c001564642c12848681242c58200c0c030f0000d60700d00050400507120380c607a022200852040c132940c098907104400c00d000c0c503040e00303030f8080d012280141d90308010044403106058450307202200c024003240c1d249000c51703084c0b4929560160b0011041c0340c0110030640d14000074042d01d40491040c0c500d0780d56026a0140c82c105030080044826045808241c01a0f8540e61080344118070007005d071180311400b5088096005c0c804141500d0a48002260784600e502c4100d9070301c0c28040055288074030f290442c001094109000244c2850074010f007c2c051170b5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 391375656 1250 391374406 391374409
    0x6010f051207050f220b090c0408031b032101050306180a0f11031e06010e010501080c0901031805010e0f06010506040e0907211a040f1202120301080d0e0406030201050702 75
    0x803212080c15032100b1061250038401c1013040d12801e02001568000c143c40d00400e09104103004048c0032515018010402030005480010440708001d0a040c0400d00304038000e01d01b0341c2140503103c1e1301c0e10881d0813584102c1484040c014451b0507103500310252038460b103400111941c005800a820380712500400317514030200d418424281d40320b5018a8111100720b011200180c2004100042142c0e482c520f6020403070780d0082046094054002035008c07044650600c2e00203041107100410040b07030100e0004081396030764401d812503400705170b00004078104003800d80303045406042c00180140c8540f00d040080505d4000c00964181200c030f0140440e45001c0c00c3c103500030f80a0a000305805014441c00700009048a0314000f1040d002219207800702d50300708985005880340f01e00107005a00c81001d03505107c0820b49c0c020251640e640e201c50354020065001000ba400c141b0000c80c9055665000700c000070346104082000f003000340e0181d5503c00002c0030f42c41080201d40c0c2600010f80020820300610006 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 391376906 1250 391375656 391375669
    0x30f0b160c02060307110609240708040b150301022b0c05090d1b03080909010f0b03010510020f0a080c0c06040806010b03060a090f140703091104020a03140906010f05120705 76
    0x1c4025071806d01e52040d0814041840c00009985000710b0754130071030104941d450415034441440303003810076040b49810030b01c1000b048a600a003026108841d0312001c504010768001241814a0001c0e00035929a1030001c20b014080000d206d12100c0620120302d001c030308102e140f00da191000b100391140340c1025042c0c400d20580d00c0c4242d004031200b60350503032a0108110316089590083d80b1840410303a56011a000b1b200103500c041e4046810703e000c4501c01d210191180080d0781c196031050b03600c01c01c0c0945d814401ca01c0d003c1c20060200181c02005d04000c14401d105000f8002e40030103c00b00c540b50903200003840246d02c80d81c4a0010a500400014001240b51800460f04844000d00c9280c1e00c0c0d89501d80c3c0701c01c4524072151100895a0307040f004004a48c0f108501e42d2040e140e0608001d091026101c0c002da040080e815144104ea00080fa09401c601070f90110141c48441c241150091a0003d502a40c9440038012306c5840c0200c0708000509142c13111001207008141005404803600d05418401c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 391378156 1250 391376906 391376911
    0x90f0916110a0605010f0f17071401050d1503110d02011b06140901020301090617031c020f07080c1c051905040b0d0f0605031c0e060408010501030f0b160c020603 71
    0x6240584002e0a01044407401014081d0003240b1640144500e40301c51408000ca05504c000e00030001c100b440c6101100c0418071804540d807100300f5040882c0c072000101c5c3c0d07d100d052000e1030700500d07100d0005007600e82d484018003074078403035040c7c00e84100e03201c3d0421442d14079110300240081c5084c5402c0c82d19107900c49207085580d10421001c241c0d01c810a401080300001110300c26140e0b980440100507076461401a2002403e1020b0500f0503080340c0c0500d16124490310700403481c000c15900440c0b082d030400740d044440f151210b80d0000e032a0701543c680454180c0c00728a002003103210742940d00058280c1d0400036925281e250b1140d43c070b020714091080e9031880c0c100c0e0200c000d010043c000026a005c5007802008484214680007070010304911950048494640001c0e000760312200305404403807400a0010103149807410303c140d08101d10400602640b00350742150815508040001041040c6815011a050710402c2801d90f80d17501c09101e40c80580344010420009410110100003609208001310f4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 391379406 1250 391378156 391378187
    0x307051201091e03020c18040605090c0405071d0a050109031e020306040605180c03031b0a02102c0a1214061006090504090804090e03041505090f0916 66
    0x40114040e154141a07803c0c0c0d0030f100c220055040c018500301036040c08002204401215013107513115400c03da4112000d4010f200030921541c078000304490380360410664502090050040c029850040e0000303004402d21049070340e0001201c0340b4a04246002200141074840c182d48070168245903803a4240e88049641a000c044208440042c0c0980c0b42800001e00c110301402c070100e9107091141c0c06075800c0c03850010700800c0360443c1c070682040e507a003c0300701e419070720042c82801507415000c1d5005061801d8444002d42c404400300d2060006900aa60101030701d03028a010030003081c48640e840c000c4013000301c0d02c581c0114588410700c810080b06a0000120703018401060600091201c42480d21906036030302c1c0840c608aa808015207a4080709000203072600b070710113001d0307014181e0b211a0301d8042d500542050341d4646808080c61001081914001c00c0310218400c901c0e010030750083d11546c03044803a940508200d100c184800d040004901d400f81003521411280d0144c1c081044844404216240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 391380656 1250 391379406 391379411
    0x303070c17180a0503010b18060f0a08010f05060303070f02010f17040c050301180c14011e0503071808060a0b13090809100306080a0f050a06020a0305100b090307051201 74
    0x3804601c0c1ca0038041c0001c96144071001c41c51000c02020040020071a41c0114880da04240c0840040d445031031540003c900741107842c14042e16035070001340f001e000c0c0c050801d402c040e0214000540c420705402140d0040ea2401d01004151904001d054482c41680f0010b0010010b200032840107501c600404586418145860034580e400210b00d21610312050340d05403942c0000820510051a00f80b148102d4074004070a082088800c0755144209800e252280f1929109040c4a82e00c0c01e034020400c0354000110414815102800c4400182841e0000c3d40c0020000f1b0780c603000c60700c2c0394900c116500256250700001345180e03960200620090b018100116400981c0c0e0201c000411440d8050440c612f0311a00220b9141d1145009220402011884401c105400e100301041007aa000c168198440e801102080c0c6140007400d00e2460100003002c0184428400031300042e0895040d030106000380c050035104d0b01d02c80c3e90342ca142d1100d405034a98541e8180c0081e20100060301e03015140d41607010518001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 391381906 1250 391380656 391380683
    0x17040c05040c020a05010f05070c021509040213090513080301140a08010c02010204030b0a180b22060605330d09150b0a08030307050f0a05071b170105090303070c 71
    0x1040640c0c0070b405021000d0f80c800107803401040803e002d582d144a000d60000c107c9458145401000c0d0300300c1780760190003900f04001000140c540041203480d2400080c00a5580300d5604002e92540c562501c00e5003407070741c134000100760300769041000845050780140a00c0e0459007070295500b0300600480b64154071824402c0d0000740c580c420f000d004054191500010f807140d1841c05e0101746108010414103109180c01080c110102880c0050140c045d00016100b02c7d503912140d02d03d5060070100c400f5041c80d282480c410f8200000d6820140039600185c84207030145190300343c40c45a1822410408581c0c02038201d86d0121101d80c000641034810444078042000c0f0010f40718031640410054030b020070f194507030038502041d05100f54024010b042c100001e41c551b1604400c01011409501c0c8100c810b5000040e4400c0110311900c00d50700c03d180c200c1c1c88050240051140c01d00fa01c0050f1041441c05d0811186110203220103108a40c442c0d2a11405180f0b160f94004080b00e0340349541204031054140d80c1c81 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 391383156 1250 391381906 391381909
    0xe04020901263102040e0a140105090c0307120308090313120c0602060609060f150c070e0606040602060a0f06231f021504020a03240612050c1302090607110f04060617040c05 76
    0x8d01c0407840c00c41400003e036402d21203c3c5900303103603492450740e02940c8980d0081145416010b000d42e565034161800d9112920f4000702c05041d881901c650014010802c540840e21407011194150403920a504810505a0f60101a130b1106011100d041c1d004501c40c000170703c54203010391520310141008244c03a100800c034100241d206c1d00071740384941031503011201c2031000e807a8103450942c001c101100d901e414540751240081d07a0b000000e0401c18036035190100c01c050b4222640000029251210048005070082500151a2007551031410310a1601501c8401d402003075403060b00041005901414902107005074041604001800c101e03000303107000d00d00001048603107001c4c400240c00f50102444000f07100b20003406603002504090103001102c800700000400000c1d81214210040e00d543c03a410001750031a1001b8007070041c0c1e46410580000c1d40a040004c0716802c003d00c0d09040b0740700b00d0300b0740c816030a0204441450140e00089452091000c03249181100b20b15880f03407107061101d4400341c8900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 391384406 1250 391383156 391383173
    0x6010e0612010905060102030306030303010312020a020a0311010206010f050a05010c050f010c0f2d1b060e10060b120f0a06120b0609070305070e04020901263102040e0a 74
    0x2101009011181070040c08207503d240180b54002909200950460400300002503d900c01840300410062050312102c81941c028001c00d8180341c0c00620750f00d0b20780e980f03003800034007030354002c0d4024010700440c0004107080095003400c0c0159040a4030a41409080800640e401702d544039080c0c985105022500040401c01d00039024507003c6540e401481440410018103038507414140401d8030315005201910411200901c1407490314a480c0070400140c03001034080080a40c000050800e07400c1013003901200384000350212440030b80301c1c410030021303542e4856000c050040340c0540c20a008100080754582c0c3c245424150041c0744002c00280103542c601d03041515400e000e00854005908104010140c03804050b244d0340a0001e0038103002500c5e0220b40200104000455944102d030b003c50703007008591045110004006e41001e0107107080c82400290025a0022170b4040042811901c04403454442034144144601c001d00e69490120b1550f0300b000050f00c03861401607041d00c243d0420101103803001c17 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 391385656 1250 391384406 391384417
    0x4150e0409080903071436010b0a020708010605060f0f13080a030e010c03090b0a03020409111305270a0b0306130b060a03170318030a050a020105151806010e06 70
    0xc00780d2a41e1a240c9500381828419994400c41400140014108994454881c030704024001401c01000507815011000c1040c83d002c7d0b4241510000c901c00400e81d448028001c0c10349500d603400301d030046a43c544400d42a00c40500650360000d6041c071500050038014009015040c0230780300303550308040c40d04d5420b20075034415901200313043d840042080185604800e0400703224400f841c1401e19100b0b5600c01510840140c130404010520015851811174801c2c1e0640d0013504001c0380c140905004000303034042c1d0b03400401002d0602000202c0014030b500d881200200800a6078401c1e120b200d0b842c0f07000041766040100f803c68001d4030740d40c282c1400c1c1d07402c2c001070784500740c81c1080f14500c00140c14500c03078072000240302c01d001d50842142840401c0504105000c4111507441155480d0745400b01000c04100c82084403a0390720001c10105d4005070018090b100c1c05130b06500030495aa509005c042c03c54124040041c0c0041e402410f01801500c000011580a20306060035030f1020000070100d00c1c90380c000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 391386906 1250 391385656 391385663
    0x1202031909090b0a051e040b060d0b0a050402070507060f050d0203010602031308061003021302071403030f1515070303060503030a18080c06030c2b050405010e0105010b04150e0409 79
    0x16940901c08041e043c0305007040344209503000c240f1642003030085144e22070034020503240348001013035045c0030766241e4101d03c003880009820300d500c0e44507010802c00941090b528442c85030f0784089020074181800c0c0700b0307900e078130790807100400c0d030603181c85003c0d0351f0510741410440c02c01c50708001ca010700680e80d00045000704466801140e84203664041ea00f40000d80d43c001504581101041c03001080405480c4070990307404403107951400b41c900e01820300034030400030024a50144103804280001003c0091031041942c2c005d038007055503485401c48ca81d4951454165803225400745501c485511140140010511074140080c1094036070f40000c3c07035600070130800c0001500202c402c04502c051005050001c11f00c25008108603100b000010b82035000051030310311080400b15081000344000820708801054145904d1a001c0c0c0d0300407080d02818040390700380c2e20340d0308084103035031021030502c1010f040354045c880540c20b0a0920290090051503452074904001c2c5410b51451039658510580e00324520 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 391388156 1250 391386906 391386917
    0x60307050903010b042a0c050f061603050714030406021c0b01020d18060e180108010b09091603060c0302250b060306040b01030609060f0c02160b0a0c12020319 70
    0x103001c420582599058090140910f080120030100c9612900064046c80c10b4007400028205080c1c104035002100000060810f00c10107449000b540c0001c1002c502950b803505408549402c1008180e0644409448644c00240c1480700c080383e04490802441d0001d00c2428090711702042d104100e116440c003452140c803641e07079444e03982602d5a0100a651050541400e000e040c0c240712048111180581e03104010a1000c035951003681e07035035004115580c0e00c0113081101c152b540c580d00d1087c0240b00b2114040d0042a00350b02060100c0c030001510804010300170340030b1202506590350039000c0d03d5220a10310070700d0f400780001c2c175100c50740704203070a03910484804001c1b0842e0036042080d02c0074009000240290400001c0c0004038556100301c2c0d055a80002c070108180c00340b0b180c590024000015034104c214071b4040150364065011481a4101e0f41c1c8040c0411a04d4403405003400e14400c0c03941d0000440d90000e0722400107542d1140c0441c1c040e515006490901e860340204151a8640c22404c40c000341 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 391389406 1250 391388156 391388167
    0xc120f0c02101e030e060619080f0102040303230d1512050f060106030605010c03031a09010902030402090906060f12070b160507080115030b0603120f0d0506090408072006030705 78
    0x700300455844100f02d4a1406001d403070301ca21601900c90001800050103200044a070092098100e1a1100142079a00842e9044035048800e18001d41150108800144601122038580c2e2409140800c2081942403420303d48a512590080203080c5800c20380322445d081c403000980205040f0206058034000c101a0086004081105080000582201d41030601d070803401d12490b680300102500d8198141800110a404400c6c43d500c03c01c089800c85502c80441c00020070050317030a401440c0201c1c402d50300d440b0286c5645c405141c44e4141219a02d4025175030b000340c4441c178a8100326603004142d0304011354a00320f4481c051105140c0c0184a1401d841c50700e84400010440200990310062000350000c018104418548100700141841302400789590701010414641e801e21500028980c100505a034a60742400d40202d250018110500b189184c4000100340382050384030644510b9100c03200303905d4800540c4c0d0b8a00381d45c030302d150032100400840840a050b911102c0046000304481e4680d5910344 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 391390656 1250 391389406 391389437
    0xb070c050301150311040507090608090a050714120d120f02070606140a0603090201140d020c0d0e19030b040b10080a0309140f0a261b100c120f0c0210 66
    0x2017504800180c001e07071800c1c080250170f070751041a90082e030300326140c090b0032a02e4206603203240060521001d001409010400500c01202c01480407100034182c40700d44c208401c41c049c40740c07201904000d140c042405003003002145065644401c141c980c1e11000107043c000c03070b621441c0840f52180c1101011741a00352915116142071905180180424503043c4142c411590000706080d0b4148000a00151b01054040f049420303901601c601480f60340464201c24058400103054500040500340284210580c200c032960a078400705045d641c00640504058032141d0b9484031406c001060000d9220000d5008508820b050010f00075660107036403400a9581040310b62204582c409102d6440360f90500c01c140c141c0d0f00d41c2c089aa00300c50384810400c2d91412040000090500842d04040c210b00a98928191400c6542060700a45009031201c0c0b0980100147c160354030449154050480c240c8042c00041c81c900c12240c1980d40d109d289030440c207101f52540070600401c04102c240c1d01140b241141000341 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 391391906 1250 391390656 391390673
    0x5120106180501030219030809062104031e0923010c0b010315061410080a06080307200a0302010504150201061809030215060d030c080c07060f030e0c0603010b070c0503011503 77
    0x220070003881484411f1450f560307a10b80c1d200e00440140500c03000304800d6458420132a80841d001c04102e0030341305614041c640100301c8026280c08030540c50510900c0d0204900c103508074000d13181000d00c0e003149428402c2031280e142624820703841c1041040300640c2c001403003015215000710300c55661440e03c00250803001c0140d034054cc11030b160002c0050440100d5a07102d002c0041c00448070300b400c84464a03004002800382420703402c502c18031b10000901c5800c02c8042c0c078403080ea1120038480701113010440401c00c05501210303c80640060000e001c20721120148150240c080038141c000007682d50f40c1c42c4c80769a940e8012042d0744071040d60700e013034580505405008107051640050b45503115880d00000040ca40f0307501d140041c0811401c2c4e64445c3c1005803880494030041540d41c100d40006a90711780007010b602c20f070090303603000906003680d0b5000c3c03500028400b11740c860010491030039030782042034030421a0402c1130103499070a040f007400519030720300303101d29400e030700800c40707030400720746c103604007500e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 391393156 1250 391391906 391391929
    0x30406020f031e090a03060c050702120111040e0711010c1e020a0b0c0c03160c1505030c120901181104180213020c150a1e02070c051201061805010302 66
    0xd604100319180704040503c01522203246080203050712030000d24042003035425280c1005014900e046c0e000c00f90280c00c4005480340c64401c07100042034414609a140c02e8801212001d446004c05110038042d617803214040582c803000e1490000780580a550205017901d07401071284000c50154055042c1d18002080342d40d000c0c0d129800108034141c00c0782d440080b010801080103580b010003061669102c3d005008480801c0040f00c2c029039840706078284900800b003148501d02c00d043d1b100b001d0918081c020020b0340d109404000780c0c2c5003043c00160441c2241500140000801e560b5441444a2b034100344501500c0c0c1c0380200c3c21114400103da060100700d41031002014441c2c00140340f040010b0b0703038040d07246600c041c0c0b10741c0168981611106152030315031140d4501e04c84000f0901082030380300d402e07404000035882220084040c19001980a000c81c880e1140c003410380040000c09110504200c0c080380344001117500005180c03075403152841c01d00d40143c01020f8020340c82e00010400d61400d00440f95 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 391394406 1250 391393156 391393183
    0x10e0a0e03090f040c1803060f05130506060f0d050d1706010306050a031e080304050f07050f030607270f0e1509010e060a0b030915160c141e03040602 66
    0x524042c003070400240e00018401c4194855901e4000300600b0f148a441007004d510081d00d0581d01681d16440e2400192440701c10409000345844000b0b8a8107014403403440721240c00c24040c00c450340380c030700501c8070340740c0801041e03600b203201d0b00c502030000b4200708507051a504842d9a14502107011045d9a080e052028024504150074610305010695a4501e1a0200ea522001040100c144203c0c086881d20031228050302d0f100c4080b0401040c0540441e4a103035500180003500c09440d111410081108602c0700b1498150b0300075800034800602a2000c2000103440e0060000030010382d09031841d210103d60050440940503031000c000742e42c3c00804440d000b0000b0140006c0309a00381c1e011925003903052054606c120901c2000c110f040d159079004c24080c201c00c01010303561385450280141c3d559003050420900c0e190140000f801da50310004681c5604507155500c204001c00e41e03c8007400d15141c01e0245c4503a008000004075030040756035a003102c0b1170005001d562190b16040c0040e00307105e00e94074500e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 391395656 1250 391394406 391394413
    0x1508010f1508041a0c1809010b0409050604090203010c0903020915150d0216061b1103030a09080c010609051b030106050405060304060b042f0403020a03110d0b010e0a0e 74
    0x14098004071214105a2a41c10b00c0c02e150280e030750342031409062000da480b000f04440d8140600121143c440003e00c12641d01e1003640014811130800d0100040382403192514449091006114100d4140c11140c0c20090082c0b0100740400381d0303000242195031650410008c911300310810821401c00100003a0310050301222031016410b400c0210f4040c00042a542c07100b80c000082040580900da41170b10a0b10900000100122246180010081c00d0200c502c18088062946403c480c520a28000302c0100c004c0c4090350540d11003101a1020705800e19040b1041581480a0606500c09216140003005150408031f2039007014069240c909002c911401206d0307604000611003590428102c074100c0c0c0c016918681c1d665502c1c28004014664a4035842e8031904249501070302c8644102081c1c2d40c241054440c091900040740118114400d40c84004e4100d1310507003041000c28200030703000000d05c01c050000100c1c1980756840600b0505c098000b54290007564040c015086500e02c0b5110070040190001d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 391396906 1250 391395656 391395659
    0x406060903080a05031f06091820090328020103050c0a0c020d030c05030a120605040e1903050c0f061e040b0f0601020708010213140102060622151508010f 68
    0x1544100d128061983c000c2c803100002103062001004110002e224080e5803801106481f10001000c0381da180c1302e094030515441c401ca0005031078521820810b048622400030a410001d0f402d5032850f0040d030300c245d5040c003a5a8450200096220500c81210030384070040e1280403030740c4005001c540d009088071000c0c003418000b05480c01d4100c902c480d0307825012194100724880c0c61808036a0003180350401403840c0800b055000c4e80c03d40142e81202c8840000109201c0d1a86801c10301c001c89602246004060f0304c25605902940288504a91454041c2c41d11500d8020100c2e49545820030626515200b03921500400078546100e010b44400828004038015142c10f050b110303141102c1010381940524111200420880e0307008201400007000c0110080d500c48007100c0c100038040d02d40744a40103102d40041070050056102107a024403d0000802c000c2144c0640003122812144884240310010740d04d00c502410b0106a2444400420000d44201454650b80a005110a0041e84102c440c1c8078020310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 391398156 1250 391396906 391396913
    0x509120c03071d010b090301022502040b060f040915121506050409150b010216090c021002130e0406060b040e07031514010f0302040e0907050a06110319020f06150406060903 76
    0x8030f036070442d02d95400c001d0f01d45074140300082c0240f190f25079001c25040e0541e20f00151182c50440c950706c45008503410014036841d00e0034420184140c800104428800f00420b200001032a40914101000300300407280c0180c803000742640501003c1c4040d103442281c10b0701040108558001d10024007002d840901c1508120f68668aa180480c200d0074002c64581002201a074400c10001000a20500c592801c259031814860014822102c022005004181c1000c0c4c0c180114000c07105122442c491042480d4038000003040c07042805070040340c0c2e003a15140f0000d400349042002d40007519403031103071161600300010040e08540c1082e801303501c604010041044100d252410000c1c0409080c20250440891103404078024030071508a8038940d02030000b0300c0410900080d102c001d9950644510359000d40702c5c18240e540d40074202d1b04050750b0b4010017418906000325100300e84841c5280c01100c0c1e4611041d601c95090880444030201e540001c5046602c142c038060003075034001c000f1418400000f40c1542c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 391399406 1250 391398156 391398209
    0x13080705150d0b0901240e0f040905031204060515010c050601031203060b040807090b0102030408070303120615120f0e0705040203130f080c06010510020316030509120c0307 76
    0x30361101d8181000b0800d14802d40d990340100c100128002c0034042035603150035190340010003e80404500b0071158541701036142c0918195006000000c000000401001c070810000e4451745508540501050080440b031000008407140103501c83d40c000f02d140e243c401400e1103d80b240e50400b078100300e009402c01020030000704005043d03a4104030b409040390f07511013050b0301502065000300505103001030001100310002c83c031304050340e00d40201804944503d07401203a4034011b9004d581c041c2e411810342040000e018007041c3d07049a801e554041084c41c0c4e41c514100b42211040190703408105213103018080c07109940f140c8071449003e400c00304201e5480741110360b40d41155000304c41c01194004081882d0394200503811000c01d034011030107107880a140c6030207070340d035042020141010311a4400120341450000c1101048105070390040d41464800032103100d4210569109809102c820000d801d542d0300c0e501540c00960607003000601d000a82401418a0b01c40306500840c64a0040d41c28070f5800c0c00d212 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 391400656 1250 391399406 391399429
    0x8120f1e15030a060209040510030c090e100903081807060905130605150a08010503010204050d11040b0306090c011d030309060a03150f030b160206160c02060c0313080705 75
    0x1810340e8405981d41d11418000340c9411030880381d05108602c0c01c40c0c1006078035002850000d5080d01c0c00d10058a4081021544801500009041c060a68414040a03680d80c0c0454610030b50141201c2d6013814554560088804030074059000648088c100f002844151460044102c19113008007070281c90180001c202c00f82500600d4403c04040135004185031003500420013402d00288a480201da540d400d0f1841030b4401007a00c40400e03101000012585818801e40c0d045501c090140d010303c01d465514842100300903049158016501c0300b010302c070707524100320301c1e4814046080100418a10840090104a04020740c10361045210584400548010095440300c03002079030700546900c0d600d00c06501070321101115041300203884400051030200c1440c450110390180d081907000d42c44110143c401c24030209001c00141e40300c3e002042c0044a00769105c03050805d1803a0040310403440360300003400c80c4d100720743c000b074a680f0100b003000da600c2c00340d402c134401818920018100145884007050b01388001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 391401906 1250 391400656 391400701
    0x4170f100b0a1703130f06080601030903050c0d0302090312090a060e130e03030115170708181c02160e0c07060b0405040311010b1801030204020c010e0a08120f 70
    0x2100c4803020141c0750b0701490406030501c41e2401c4041400e00592550742d40004d164a2901190620f00003100d0b0501190303a000d45045a50365041350780c5042c015001b9004c3c0b030300101d0800004001c8100014428450342408021b03565001d642c0d9200c1000f01032400200d000800304480003080b546400d03135204003801003110b095080036046035510350300050320300c810003040c0b4018a08000b529400f03c80040001e6051794000d403085041e440008800b10384031a005c11800d984000701c1400308481b035000300d440d694454a02c1d083e4070200e0078079180d0207082c8a80e40c1c810b039050701402d030781c44460f841e01400304940d028400c1c440000302074942200e001070001c0181000c1c0e254000000e4100c18049540c0041c2c5040001400610040c1000d14000f040403040c08412950f42d440d20303480c82880d140045d607010890038040384c03e1642c2e90079034003044025442090414010740d60703841d550318090001d120030382c4130f1030180503625280c2490012800020070000d212400c600c2c0a0f908001c41c203119001022558843e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 391403156 1250 391401906 391401911
    0x172a06150a21020102030c03070f1209062304081f061a031f091410140f060c070e0408070b06031504080304030e061b100506010c0b07030204030204020301030804170f10 74
    0x2c10300043c0d04500c681c20f0058401e0000045003024418041c1201c24480d1089104050301002810211001c030810f014040005a55811400c8207030803014141030340362040000c5034605030b50b5010307440c50500c2c10f44503030150640503240c4010084881c42680c0040c0010000e0040d040c3e02681407640b6031000504000c84a081164aa5058005440d0b58405004d0f02102003200070701003143c0648500c002c41c0c01d4039440701401c42c045075071940c0c00000b800c80800904081340c1101e00a0030001140c00280c03e200d918407a0503800030780070000c081c1c0795004501501c05a9a140c1682c00c0628040000610385e6019901180d44858030301c6401114550160f008444039440351220314049038501c124811156020601085400316004680564600c600413801202c1d090040000c241040d910104c0d80503002c40c1340d0040a1020402c1500c8080d8045500e1600524042d22030340040e0481c1c000381c00a0341c2c4410042401c4c0800b0840514451040c3e11081c001c04200070300300d041e180d40311200d031101440f8030b4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 391404406 1250 391403156 391403219
    0x150106080c07050106030602070b07020a03020c1003150b0403150b0603010e06060721030c0804020d021018060e011202030f04170403060908070203010b060304172a06150a 75
    0x71001c1058444055200b0000d10003203544c2d04004c0c01940100c0f506840010b0100c0105078020700000c0d03c60161a4140c02508036020560104900203685200050506844414800c0c3d24210203d00201505e07402d40100c0d1120b0031414415050303420f280301c100d0041c0c6071040840595075050103903130440d00400d600c2415940c404000c42c51030301035071a00818503038030b441000c0308041d8071141100b0300806a41d0308200d00a40402c048a0080d1b00b07036400303034111501490440240c2082c08100c0034030042801c02c1d03d0508070651600c8458420340c2d00c503000080c94111a0341c11581d00414100604071202815402c5013000300e4814054200644010301544820422a413500c9468040d41e00a6801c0f82d020001d44803641003030762103a80070000403071195107001c0d084015450b03c202039034052900540b01d000b00700c0c00c214007425594030018001644c0b91071155000300c1007990514403600e29444602905190404075000f41140c400541043d108070880f013804d220f40a801d4a2036103900068051004503031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 391405656 1250 391404406 391404421
    0x30306100302040b1201140402160624030305030a230a0b041107081b0a1703040c0329090106060c0206181801140102060f0727060f09050315010608 65
    0x20300c101c4e4402880e4100100c0d1071030042038200d007a241200c0703000c4e480c1c40180204a081200324400e0f421505200c0c3e09146011003c101958041d00c1c84100750500100c03021801341c04041100c10580c000c400082d800820084640fa06002d900d0030035030003010507107518524842c0c81500075001440c444145039959074007031042d80d80350041400020348101542d40c03a9802d0034060070aa100f10340c030450f0f03129031901c01007881d00c002843c501d00a402500310f003002010040060725950014000f91b0f0100440000400400c001c0f4000f0091001030b03200090403c000748090450b6000020030301c5219034500348041140a8102d000041925812100c2583e1803018843c4845910040143d503134208080009071040740e483d40f4002411f940c0758107522900c1820b1800120b130f8406044880c14003d80c1d000020404080c02101c0c00003644c50880140001984001c001d1600303038189912000005440d11403650300d003a000f49100300504415005400c2c0140d0561402030704000600c110b0f020004030b8000035100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 391406906 1250 391405656 391405661
    0x80c060405010801060c051e07050316060f0804060b061606050f04020901050d06020c010c020313080d0e0904030e04140709050a03021e011803060f051f031101110616091203020303061003 82
    0x8055401d10075000d648c5c60010401d607220300d107008650191042c031005140110f5603429240444085075215542052606070454400c0700142c001c5a143d034450031808844e50b1024040c00c11142c114036800b10149180c01c00606640c0c01034400c00d01041a041408050380f940410a41134403425143c070a0590894904880240b28169030810107500e810900d009941c1d003c00104502d4076a41c2c6400a020f0300d415141b501e51082c40002404186920b16a0450342001c09608d603005000c0c0c20440c1501e1201c2010a0035204004e5807624524400c0042089054004041720b024040a4400c105100d0655000c28035503600c40468992510346038816002c82e03807041005d0504e00d640780103141881d5550389031400140601790a00065941003d000179400351035109180100d04441444589044c40c40d00c4003405050f0a1980d40d040025800d0403000a1404008040c001d46100e040805000b8001c80c00074045010b80e040003000c1c4907407100b0030010950020a50b0307041582114034000084064406500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 391408156 1250 391406906 391406923
    0x1051501080a020c0a030327050a03030e071211041e09050d03090305070830090d030c0e0f0a0b070b060a0902090619120501140907211a030a0507080c060405010801060c05 75
    0x500802d480234040110104215490324440e4800340000d4501440c5103403680528011780644211911043d408aa8101da115041da00c001e480011400403150500007503403417401e40c0c0c1400d1038a4200c004c0c02c02030100014031064080e40740401c02c981c01c90350300030704c51310800d00d025000410210b00c581e01c2c01c5000c043e1004001f0360b8070048a5400034444000a005812540040a401520043c0b2520343c0203010322045000e030b90b600d1a901d00301220402c504103000d800d11580020740d6420200d0303203052200c01020420300440b4603040c01d145c00310401c50700f0304003900003175442401031001981c503840380c03c1070301e50724040030300750b50842e540503c82200c003010f82080b400c1034903080000006410003004a0b00807010420349404d103495880c84810b031034041410030b041c900020042c0044015003400d504c03684420068108007203142400000003072600c030502d00190381540240e9001c100c409803c00022820b034030151652410030f441c1c100064240c90341440b03084113021480300d540b001c10800380180c22 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 391409406 1250 391408156 391408211
    0x61a030604030f0206010e040b160e0303030112060b040218130b0913030e100f120b040204080d2601030f06090213060501090e040b060f030a0501051501080a020c0a0303 74
    0x60292505050040c0110340000d1414054080c1174000701d00c0d147c40701c44140c41103070403200100040e1a040488000d0001c045918010440c0c031240483c1aa035003840118020044e20100b04158030345420600e040703802d80e2480a200380d104000c0392854a220641c0c0215090741225420766190701d04000a0140c540c00c00c1c0c4550141489003044980122400b0f0003001c0e40c000d594044850319030505000384051501e031548040380b0341030401110948102592004024004004101420100045021707a0840d4000c401a80c0003003e14205d4030354844000c4401e034640380104400b1241482004c401d000040c080605420540203404081c010039400c009100395002d04200d15602007803000e20010b01e11809000d00052442d003001402c6c0c100ba004250165070864003040442e11130208000d48da070448914542c041c09060600c0c2e011079400e01c110362140070050208240c0030b141230001400d0400040c1903034212403041c00040004540040c42a54047c0e03d4100050340d11250421107401704611100c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 391410656 1250 391409406 391409413
    0x19030c05150103154508030a050702072108361801120201020c0a0603050703110a021504020a0b0d020408100501360e01090311030a0c061a03 62
    0x214001c0004841c040d04890040895981500d0082800c10a9a0550b801c090a01c41c1c1c0c44243e40d4000c0704e070101700c0c0141c00704080049030703059017600d07004d400e40a50f0003e80c0c0060003c400c10803140d54900525a0108031072000e040114104601802c010904150b00121204001c00c580304025841044a1641e85a1542094024a02904500400b000c0058145c44400388114140325040051072071154100100000305d1980c00c013250400d142c0c101241c02e03070440c0314034003405c0255200c6a4402c1c3c054100f654020074140760004025055403000d8804915541c0300704250400b03942d01040b003010008003010345903280d48031400002c00415a0350016400420002050105a4034641c001c008490340502542c40c0030307421191240c12650240b00761485100614000414800c25416203900103075070f4170a94103d600721400440880c2e440581840c1c1981d50f6101c41000c2c95000380c45080e60000ca1001549001024030780101070b2042c00c50000d04854607200e070300031010310140000c040c081c03025045 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 391411906 1250 391410656 391410673
    0xd03020a09050a08010209031522060902040905030307030e1c1808030d020c07090b0d15090f032f0714040b060a0f0915050a0e010c0f05030309070605090319030c05 72
    0xc4d0b000350b0040000621070701c2400e80108c0d4800c0b0410000e8802c0d1840a407010700a081e684940c4003044a0600445405030340311141c01c01030703459100f00c100c0b55010b540299260710b01544041d0071250030101c00d2509030301080101e00050f61080b07000008811610b041c1e07074080d00a0880700302190580c4c0002c60300707006c04a031803605828194040c002d092200c00c2250a0b9170340d220070381011100d40c100d10541108070b0301600c001240d50724284a01038080795500064080d25178a681d982000550003c600107140c2c00185100d0040d440d201c07156002038120b00d0514091000b820f150b03691118412207200640e00c58122a40313613117580c001c4d0480c0801801403991800e12103001001500640030080209007040d0b400300301c0c00e803496902c0102c00c0319a1502842d0107003601081d560b04c01640061810000882c0c081000500340d541060441d500c110011038507820703d10b60585c01c003982c41c0c1043c0704100040c090907050303603400500700a018135000e00440315011076041c100c2d009680b0600240c03441c42920070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 391413156 1250 391411906 391411919
    0xf091e0904082d043501050a06080303100303030506030c06030103080406020f0d0c030e061603020705150c0a020d05030c0601080604061503080319020c07120605010e0103050d03020a09050a 83
    0x60949128061a50034492101c600310b007400345031032540c2c00f800441480103010240208440210390b8804e003040c8420210344c0d0344144801030340141040070036515003082c44000000e60007030401402150024609514010403030f0310300c0350001c0c400903003050f48560210700e03551024002d4000c1034401a080a0b500d40e141d00344883c0b02d0703101c0c1c86080018410705811040c1d003400454a4040d20300300c0c1d070b1600c003001c00707a07103040b60050781c90303075000d90301c81004c101c1150491036030141c203450b11388a07270040c02c1800d00c0c0c0030810101c41e40c1c03040181d01180080104043d0841d02040203200903904491104041015040c09880c600851003203201d24030491f40023080c90013001800611480c4100421302001c4001a0350303d0000030140700090034040280089104682d100d54080c02000148100508101c1c0c0c407800c5524141c501ea00880c030314403e8141d0402480503e0003030502400030303966060381552465692a40d0b400c0f282003404101680031903d20443c1341704e9407121004100040006510356190780 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 391414406 1250 391413156 391413173
    0x9090f04021e0429180c0d050a110703030e0c04020c1f11030403090f12030f0c02121605040608030a0206060d2604080f0d0e0f2803020907050f091e0904 67
    0x1003020321513191524042c80e250004c441d028411507841b24001c1c1404488203481001d801c010b45007040064032030100003d0b00c00e0310350260005500075073740803406005400c0c180c1d041040010000d8002c9004100c0c0c40e50340e140001380c0d0b24000900c422281c18007401c01000400800000c449040260000010b000515030720161100698442c1c1245a40040d0364240500303401c648550018045420601241c0605004008a0a003103001400c0d43d030032135241700c5426043c1000c04100001100b13102c60103003ea03003054450745001d0403140005528040b90100c020f5640c1d000203007014030660200381f5400812611000c1c907200b03181c2d0401d1900010070b0850a208070b42e00305014520040c0314a1400c603588403400922240c084206494010408004c50140148c1e05606040b80d40c0103410310b5901030525042884c14845401d118035151240d07820351040185205004c0d080030700b080418002c55500030104003c69003140c00486654820103942c00c6904410021800c0191740410104104001c0c8400702 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 391415656 1250 391414406 391414481
    0x5101a09030c0d050d1106040f030c020f1305090d03060b090424180b030c09010e1b0d021305031f0207170a020c03010b012307031106090309090f04021e04 68
    0x2521018100c1b0f0007442030710340d42e910455020b0f21117464a41c0b480046801610741041050008d014000c2041c08500800c07515042d4149072054260740f00d0030800d180d142800000030004884c9030034458035240415052041c002d41e5140c2d0b11071642c4025500c01c00012000544500407035042001e026035a403500104034030003c0091504041c104404200940b4000c10f5034488000b0061601500742d08000c43d1402000740142041c59100c1000c105070100b01e407490103000c039242c50b40d40c05a035520242e0413020003030724a603100b14003c0e4026a10b0407030b400c41d007040b046a040c10a020050b1115914144003940f020f142d0200c500c181340006403102c0c11507000ca25541184001d4009000020781080112034000c409900d14800380a15003040400158001c0205060750103450000700c0039001c584075a08082050f40c0d41d60140d440040c0f2400207040030032006500140d05ea00c141951300e06a0003254000d0024203c0705060b400a403e403511030381d0340342e01004107440940c48421b01c40f0b003e4030160003081c0c800d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 391416906 1250 391415656 391415683
    0x20c06010509060904030c11031e101b0e0607020603070f20030901080405010e0d050d06081c03020c1501090906050f01050d08070314030a05070305101a09030c0d05 72
    0x22400003003401c2c2000d4050714000e440260503a070136a526034a04446030303030b20300c1ca0072101c560580741000c55680c1c040140110020082905569641e040c4544038503142c8440b2a5030040c5c0c0c1001124105d48288108040c0440c07001d05103103441c003d003040000c0c018801c0e4140250300100201c21b02510580c841110b21b0540296100c800d1040e06020800b40700e40360500d40d0f140a07078410015010154415a140c0d90024401d10000c80d8a8094003111402d1084000d40c040c0003030404181d00301102d074039010b000024200803003e00004040030002e110f10328409255402419000075410b065054104a180300104a184116403256104d10030400a000c0783c040c141d41c15814400843c6c511040780507114100d40c0c00030f0080803c2c030116074880c1c03138a07080b1080a40a10416031809883c0101d04002144036101d03800b0001054600f080b0050111180900710414148113104107010700000581d440309403007486003174143c0f101c03010740003c1e1a1030034544e00540c000190f88a00010000001400501c80ac40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 391418156 1250 391416906 391416913
    0x3100c030c091a13030b010b0a081005180c070510050106020c0f0901120c08060108030901110109020d0b0a18061b0f050f07020d050f0601170a020a141f03020c 70
    0x718100100c07403181682c040c99001510340c900c100d280c11600c1c801440c26000089a40343e10664036201c8140c1107200340d0200700c08003000162552000c0e070001980342c1c00fa94502c1c0d4506028140404942c900c0000203510100048542c00710720703032180810a0300d01180d400b4040b0327000b4125404aa602901c401c0c4a000090f1003901410b044901d81500c03c0e00354010080c1c040c12843c1e1904651180324046600706035030301581100081855042402801e02800913040216511a000e600051a815445408409030391400c510040141d5404969451301504122001c241d034a07502c422400411032101c00300caa03c1100030081c03080203503a4121800030030170025144900c480145098403d40c040915440006004010729107102c0c50740009022114000340a5507560407155440c1481e00401b1a500162f55005030010002d0b81075550440b114100c0d480c000e4a100c03041da030b0201344d94151a008007140c440382c0380401d032900d445100468180d09141c01e940007494074a1603000d0020340c45040842030501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 391419406 1250 391418156 391418171
    0x60c0c030f0703080d0c0e0319110909101508010c021c0206071b0c030f0303020d061505090108090a0506040b090606040911060703032405090f0405072303100c03 71
    0x2601203601803c43e03030001d075410b1a004012406000824045106405000f0701321b20000060714100071000f0402201d081300c3c40c6d5071302a810aa000440c8059200c5e101c1c02e01d03030080196044c40480d9180119031241004606101042d0a0b40083d00058101248540c60a078040c0e00c030640c001641c0b40440d2021444404845040d402207840d00c00c116406004101d1304246c2c1c60304100208011604180905500e210107500c0b60703541d0518400d4220140c00080e0080351b80e9003078101c94407400b001840ca00c10948040d608000c0c0242c00b6002c0c8151850600000d000002c94004040c4024010154801c05564042c030f81407500342c060000540d00220079100740000170700b0b682864822191a40d400042e11031211524104004c035a0f44110340031000c158698218008002c0c403e2200302074020250740038252103042c40d0600c1980307980203201086d00c80c031207014000450070208041c800e43d0341c1100050f10704030a0242e400d90180000074419014840c800318802c0c1d0900d681c0c0a06e0042030250381c140041c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 391420656 1250 391419406 391419433
    0x22e080f010509060d080c010203070e100306030209150f0405040501021201090c080c0a0e0a08100b030105150402030c0c1204091b0f231303030212030f040f02010e060c0c03 76
    0xd020074000c194001d82200c0104409182c400e1081403000c0c132691100c1c4c544400300c0045402d981042e06c02e100030400344842c011451902c01041034924a081c6020401c82d403458000444d00a40500740d040001100d8442c590980c0f030305c0901460f5054003806c1401642014582603001703520900e0040b5800400c0000854485441d01881444031803c3e0f94006180e00d0390b140308001742e0711601341d50081c403c4044502c1d4107030302d50346000c40003814800080c1c968420386c0f12892081e50002c840941c03199140504100217a810420003010441d0241d40c016103950350124100043d01c10540d01c407500d403041c21003089071229064001c0c400c1d568003020074003d0011000801c1500203000c10b0650100d028a0140011140300e1503c12441c21130400c040100300494200c501d5071079000484400150420500c2030081c1601000a524041c101080340c5165160164a0b072074040c101a02c000c6c200c180c4a104074082d0783c855001e84280242c014107080c0c0d00c03903150019a5950007840503141c00f03401030f400c0d8050340 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 391421906 1250 391420656 391420681
    0xb03060f0a0b1e070f0b01260a0f110d0b0402130c0c0204090618050307120908030a030938180d1413080607121503060207022e08 57
    0x80300e82c81c1014a0600c4245000260780500100c814416001c0611038840800c0201629145042c02044a540e00354140b0f81030080d02505100e102d800098032000c110f443d900d0015264220940022040f103690610349031250303480f5490b050441d8044080301400e01070002840f04030780154403c84451001e41e02c21100d0702c013030750780002102001c602c41d04000e0025042c00c2c2c000442c501c2c130031680050741d00119030351506c0c020403c4806455a600c0811150200030341d1220b01c0b806c5104034108070801600c2c2143d1150f8034840c040d281c008241d1103001107400c004c0003460500d65940075180d8222211007081e4000815140c0f030303102c210891840c0c80861104081d0300700140c003d07030f8041b015041c0c4d24402a01a11010f1340d10842005102d400c03c42c42c1c41c0766900800c050003a09a00780900f2550800c002c3c000d00c80254050403041c0c40d841c008003140444190543c1104a950040c40940c50b20902d000140b819800a41c8041515042c1c1c4800002604548121102c1020549481e11191500d8008841 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 391423156 1250 391421906 391421909
    0xc06070801060e03191103010f061e0e040b04020d0804080d0f030c08070504270c0509031605090f0c070c030803010f090908071403071b14011d04050903040308040b03060f0a 76
    0x181010007001c404041501b0800b1041034400142c008101741ea00da020301c0080b541c90750703c0385400e845101c0c07040000340140380314203000740102411045181440d48442d482014090002840707041e40b00d02007800c000d000c0055030002c21140095460301c03220110043c000615010038000007074039241d82008181c1c06114100d028400c070303039992800e260511000035030080e50000d003084056500c0d202c880007040380340110399040040d81e85068480a1810502d4030b01440004022030f45652074900b400152034203031b07a081c0c1c031a0440b80040441c1e01c852650207060702c150320300940018200d44000c0103104041000b54100c1c1c555082c2240040d039914007407021180c3d800c1000b0440d030020400440071440240d1403007070300e051140070340f0b2401c0c6250307540f00c0340100090050780c403115060508100e240f0020450340601c0400303080c4040212899030070b0b401811480100f003445103940c1c1004ca40c403040204103980143d0351042c2035598a585a9915003c4c81d0822507034548600c2421800c0c080b2030a14071450390 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 391424406 1250 391423156 391423183
    0x1030606031b0f03020705030310030c061707081e040303090308010906080703081305060408010c030b04050f1305031605100507110d05030a0b0603041103120c0d080603030c06070801060e03 83
    0x101000c2070300c0d00071283e40040f107681e40c041540034480000821010b02c0154040d000e100301c030714040ca00d9880c040bc28501c240d404441070100c03000444d12440ba103d01c04582c03200c1c1c5490121025580e6100706150706850a04542d649540002040200340d0140e1210510500035119040301c1d13a039482d01c0d40d064035407030700420300303540c10441c0f080000591050180c660580d0200740403410a4960011420b2070b08540d00c507051984d150701042c01217a4040c49421144003069034180054030308180416000301000d030100081801c0382644034203200060007526034069498240c0d640000e40c0d4107003240c0d586010040c4030a038614200200d4030260140070844c2074505808054920b200c1c4140342980c0c2d41d0801042c6992154451600030302954408000314401d0344240c085071181039034401858906040700c41001c083d440c042080901000b070002c0c482d0b030013401529007041c00d50707100e1021030705500070b5507840c801520405090207010f50704940010705940042c2c1e2200c00c3c0d172101908040d0307036544102915 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 391425656 1250 391424406 391424441
    0x905060105031f0e01061a040f0905040b1f15030c110a05121e1611010c151820030d0c2f09040506011a031506070c080118020103060603 60
    0x440b151000c1e03000803024544c0c3c14000101107549582e00440c11400d0360b1000031030000018240400e07a14001988050031104004004500d416a20190b101d10302030440f45000f4400940c1890805140004070094900c0c0c40400149000d5000041d0140900c0001400800c1040b038502c1a030707000000c3c031100ea80350800c00501d840541950030080325440910720030441d040b800110002c0c4410507005100c0c05010000c0e660640341c190401c44200c0580703804450402445a4103103003c00c009210350401042c00c801d0000d15141800605002d10f504644000c2900360003802d81d807206010700014520350300064065810300410654115a54000c10070000c0551a04154204c0140044140c00050140c0f40e101a19800c86002c0021020102101e0444042e8807000043c4040c0f804036403100480010001d803642141044101c01111075419021240102800300b9a83d05100d80303e42010010543c2400810030001840f166103d0380c1600041640440e0038804001100340c8a0f00c50800c3c0c004a05022 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 391426906 1250 391425656 391425703
    0x30a02030d03021b0d0c11030606010c08030a1812081e042402130f050303130311011e090801050c0702010e01080a02131412030f070b190609090506010503 68
    0xa400942080394030131001030360080310000a160170440d150b260141610b545903200504c1c9041d04e200140d030048580242c000c0c03005d002c0b041c0d0f00039512111260703103e00e1550b01c2c0d5844245030700050481c0080c1d4070402d6034000010007804030f080c0c1d4030100b001d215645d84071683c0d10042c6c3c40405071381341a05904506e0103c8006404504c0c04c1001c19500b225040c9002501d1542d03a80c00070583c0c00c032140c1810308030804036080007011070000102d80141001d90103141041e61031481800c0507103a0740300151001c045a0f00c58180c50784540c030703005180420003036259080c00c4484401001c0c80141e000e01503041d8a4840440c04030300d0380c141030f00c04640c0d050f03607842405100d0800440d10b1003006007002e40b640e0780a200351502200041c81c0320f806030091f445c401850079070b11010403222243c66903031400c454000f0403205500107242d03c11124601d0b0044080032290b00d13414400700650481101090345249400720102c0e018406410201c0300a00a10031078515903200c07030805848024075040b080300d16151350305 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 391428156 1250 391426906 391426933
    0x30e0f04060e0c03271b01020606060406051b0d020706031419180b131e080a080903040e040303020d050a0c0522030f0f02030d03020a0905012001060609080c030a0203 73
    0x110362200d1407500034130444643c0303880c3c0e45c1012456205421950070841a00c02030540703c08501e941c005091000348010705150001c034080784241c0c024801041030000380c1c091035900da0300c480c0701c15207210781c21a4100d518102c0c0080d28be2189004200000f800c0c43d03418a862121014818001c20740c036069aa05c0c1130241040c90004c0c0340468400c6800c400134200503005c2007507418518442c5615017084144140306143c0011011103402c41d041074080c101030480042400102500e00d0891903086c078068030b440c1c0c140d5161850050f0b51000d6000510309040108156268014151200c25803038240000d4954060b4a400e941800102e44c00003042801001968400c01010400412035120315000b03039078817521001c90700e0840c0e201c01e5810b41003020070310085081c2044034000d11100c900e402c600300303040c07203100402020300c91140c141003203200000c120309007030034502071b01e051518013000704615550f42402420800c0a482018214003d1102d2a0a02d04020074031094142d4000c0c003420f92001d0703500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 391429406 1250 391428156 391428181
    0xc010e01121407090608090604032102070809090a022d040e01031118070e0f011e0f1805090f0a0b12010213090614041d01020403030e0f04060e 63
    0x85258100110004a002080018407603002d8408150420301d5003842c041ca4060401d5006130b0100d000c02c88031b40100220820b0201c0c0c4190429807500c3d21b101152a828a840700d1520884c003200507280c8000781e000d08001e02c03440109050001503442600c82d0340c3d00c1d002d070030482c081c03a41c3c0d04415054441c402184102c1c2070b00050b0140141030b081d6824951118454014514242c01c00c9842c0c00015200301850315203510541451b03550f941d041039103031506100003001c440070000a00e00581c2200386025a07680190f407040181d500d1a40005894002c2110040c004041081e000d00440c0d01e080248680040c13807520032058a4000d8100b00440d01c03040074000480c40005e10f00e404081c6e41f00001c8003130f6a10b507410488010580c90000d610b0b50340c11380302c8482c0c0e40c01580c81180c0c0c20703140010401c4200c0407008031200454040320002003a0302480500c0d41000da6198002641e94030005000c420190031440c2c91683d46010750700040c0c0c1c1d400d010144002c40341e59010b800d11040e10400018074041451 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 391430656 1250 391429406 391429427
    0xa061b060e0f01150806060a0b2b091208060306070207230d03021b0301050411090403031b05041a04060203040b0f090d03091d04080306010c02040605060f0c0d02010e0c01 75
    0x90304070b07880905910340850031102441d8502c03000c0840d8581c02c101c408400c0240030b401800440b0040e0b02c031032400c0300e00c0b00103100e1003c034a400c440b080ca03011150704803a10340d8a441a40c40ca2801e200b01e85052a24908000c617500720780022418640210f00070b8100040d0f1030f8030481c901d8004100003410072540100250080b4080d00710f400700d0307000302c1c5615110300300302e1801288070360001e00701400c4910b0b00c09440799020404d1030080c1c0c5050f0800c004034992048100c1c144009070740c204525122820118042c000104822425030081c103c2c030024540e0081c020002c41740c16000710244542440f240035410b11440c4203000050740144018003070f07140140002d021015a40303500c146403440d0040450200d00e00420240e000c101d0362102040280c6070180400d54002c00b0030054082e600e0569100900da00003e071005041005001400c8115180c80e407102006d000010001502c8141c0310712100e24a50202c484464a070142204681d0702c06e005005180c0f82e010b115001d03141d521500c0c001140c4681d00ca = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 391431906 1250 391430656 391430681
    0x40c0c020328050706051b190602160614060103180c0b131701060312020105090a110d0f06050a0e070b040b0319051f050a060903080702012006060a061b06 68
    0x2c0a4a001c0001c5042040754024030050305c6550316084002115207044240d00440615508910341c801f503003010784025290100e91001005849259070585513429012141005080c10b1800c0007951041e4910350200f48204404d0383c00f8032445420784a500d0605c2081c0700c0040c00d00d41c0304041030100c41c003060301400c7c04881040400c007000e90742e00b8424041803002a4085401d0355070351000d00c14441d196406600781c8100c0d00090200c0d0802d10a9581d031101030843c090003802440300d0070045555030008008000350070550f0a023100e0340c14104030004050540d142d07108149000d10031021502c001c6442c0d03044510000d0312504107031a00000317200641c1b0050042254924102209010785e90358400c3c20f00078880788910501042400030b0a5540c0f550a40140e841205004010004550700c0a030303860a40368805d0601e0740310313441440142c5620401c40304900c80800340d443c14040e801d00002e03615200f8941103c08801960741d03090250781900c00800c18031403511400302844007040b1030f81c00c005804c014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 391433156 1250 391431906 391431973
    0x506070203150a0b130e10150f09050f06040504020109030b060402090d0b0405070e10050f06040e0403050d0f05271c030c081602031207091d06040c0c0203 68
    0x4490990450b4200c110f803140300385030303079002c4008180c1081c4401a5801000d018200550050210403e90301d010000d603185005032a444020903507103603140110018484101ca4050b100d40303902c001800351808a4010746618044030000c1c03018a06409440d001c0d640685170300789114103507100da100b803000040005800030303000c000c0300100e920381083e50b440e064018044032a4074241460710909084065000140c041150350030f0010b43d00c0e41d04a044200c0d1011140028503031100d10101c0c80d24001c3c0d901295600c03488800b00701c1450b82107030007041c038a0044c40c402c00c11812620012001c442081e101c1014000b4280c00c08034071002c01018901c15080f0a03411165410b98400101058020019091000a880d024040345080e005507145400a042031012803000c1224a00295280141100b114001641c8404199041e02900c40074000e8680402ca1481012014040300e84038107050380c003580941c0c03030020f21080d003502c9003d80384d05c410f034000c2c083c000c1204104003035940a40310014941001a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 391434406 1250 391433156 391433173
    0x94a0f130503070b0a0c021513030210020d060f0603061203140c071715011d19050a02070c1d15060c0a050a030306060c051002130909030306091d070506070203 70
    0xa20402c0604182c0d4414600183d8614200301c0500c00d035006103415109540c441001c2c0c072510062003c0195000f504031003c2625035001d400c00303c3c40c01c00c0780c000481101c3c4c030000d80449208901e030050001d4500e131088019495944600446c01c07501d035841610802c952200f00c07000040d00c184100c8400700d007088007403801c24914035841030a01c0c3c2141d020307804414031440c900b030003040240720706d0200c0c003424440c403e45503141c02c841144841030140b1030600d030282800007450807901c191480300f5802003140d04005502e00f180348400290b2007164152000d4440e114001f44d5040403510000040d1039030b00401003a40c45410f0030515910303c04540c668003950030310083c1400c03003040001c130103064040c00040175040c0281c100941181d1807500018208181c500c23904020480003c0c602c52542e5145600580d00e4400131400e11091580c0e400c00e400d12421700c1500b07800c3c9941030304110190b80e1442c500708151040403031040100a030110740e2241a42001104210520f00b41c005000801e00140075140c911 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 391435656 1250 391434406 391434413
    0x9010305151504020a0804060f140609180f0a0c09060b0702150906120103060e07150f0e06030108011406060301050a060305091509030304060b0f060403060b01094a0f13 74
    0x5d17007169030101c0001c3c0d401c80811007440300c3c0d40104070001d40d0003542040703081e50340415507002c00001042c00780101c81e0315011526880302500509006042281aa01413070304016406444240200c410303141038020b80707008501c111403071241e02c0c2203884043c3e0040c60924154240003500c80380c04881c50313956005101ca480380303880c0c0030300a000d100c5405640c031405605502d80882100c1d1303002d80f032400c40c0d80040030030f00803c0460344c60182e0511407070500009072031180f502214025104070f0400c0c0c10180202c00002d50303510540154501c032a1010090426070380c3d00c003d020542c04244103803a40311155101c1005601d0080c0d01c5180c02107040f00544801c6804404005c0b44110306550302d8900f544000100014401c091042d04c82441044030800312400c20f80c0009010381c000ca000242c000c0d40d556400c010968029070400c030040c56000c0292080f01c1e540004400840c030042582103a1402500d407070bc100880f1100c41c000021071010b03205a80b61505452000c204200524403020314545100d400c010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 391436906 1250 391435656 391435661
    0x210b0106051c0908040e0406090c090c110a080a11010f02040f031202060106050712030f090b1e04080409150b18041a09040b0a0f06080c0108010509010305151504 71
    0xa0305041d00d44641d00c202440c48101044940224040b01c50b01d009540382c0003402c503804a600f2291031014200503a00c9508000004091a070700061400c201800700141000b000e8000204804081e10341e02c45c51000f0b500203d896001814000303001d24800c00c401c0c19030a0207011144580803280c00001082c1d140c0440d00012a8450b400c0311903002c003621020070400480c2c07a500b03281c0070b4840c40034200a502d0100e000e0420b008410006108200c204602c04009110b90701c00b030007114143d41c2c01d0162101702e0400e0307110600e050b01c045000a8100300d240100400c0c480403180500e40c03045469103003528010740200100196400c10f0804014000d0000d002c180c0301d8040d013061181940790802124213201044201c40d61104030314a80c060440c000e40c040d54581614581c0103030403080018003603650710ba100c8024031503803200014035480c00501007200040007036581c0302241c00380c03903840141c0d0303c4d4000c100c061902407000405a40c0300310803c100c2005c0c80300042d070b0400c48404d012010b095558001905 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 391438156 1250 391436906 391436909
    0xf041a06090402130b0a24020d120b0d020d0c14150d180213020c060f0c0d1a0a0e010302030c030a020a061d1e0a090234020d0b0103140313210b01 64
    0x582d09808100b261f0f0031220082d0740d10740326940000c004a5010520140c00c1035040d290307200c0d00325030342c20300c290035070329181c1d00d1019a070b13030017030218032620406d140c594140c01c0c007400b80c94640c10f5010011010f500705810068191132042d03482c2c3e070500180c4d0301403c01034140001000001d10790348508000507204e04000c000f40e44a818805a110701984610703914180e03005143d04140441301c01803121096012003150301600030305501040c0ca01500884c600c4c081da19004264019504180025200144809503030590303100728191401c80640ca820940e0b1100c10f44006940701204500411440303008045408c2c0020035079408034460400306000072909492800d00c401c60f42c3c40b143c9014a030b45030101a85001d81240c040840c200b51520f206040c1a50140f02c0b81c50208030410302128007030070350003810444180d005184107142d41070b43c41c1c100c07000b034020b11040303941140340c03401e0f000071510102c15a410200312800e4000200e18041d0130000c4010110858500c03c2c1040900c88081484844030301e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 391439406 1250 391438156 391438169
    0x904061502031b07060e0603070e10020f0f030304320303070908061305100f0902060c0307120503010e04080a0e18011d0f060420030f041a06090402130b0a 68
    0x5494001048003040700c4125500343c3c1c980ca400c802000e011558009074030109107101511000e482c1d42c2c400c401071b16112083c0318001d40c004030140c640e100040d0700151004402158a0960302240c607880007040d641d0200351801003401c40c0e1000050108411640c843e4940d039078014044803440380b4107146505552050301c0032000241c10000902031101c04020058000080301c80e003000b91411601c0f0b650321aa40000b1116203681c82d02e03044003021480340c0000c021960000c0500f07940c2e10200040550b603500056007241c80280720302015050a000d102034034100d400e481c26100139903846030340d0400749a01c048a5107040c408074611703403c0e20b07449050348207010f0041001028444d5051004452450300ba6000c1240d41c0c489040030810b940e940c0d000a80d40005083c1c1d404a4240120091200e00150704000c0701a1b002000c020031001c002c254001e64003960180c4a5150ba800340700340001801c806c00c892440c0c01c0b100d4070000c5801400c01c0c9000c5401d290306440c00140760110700c80080c11445550384010b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 391440656 1250 391439406 391439413
    0x70305030f010b070512090307051f0e090709090b0d1a0a0f0c021c020307050604030e100e1c0201050c030418051608180102070c0b03070909021602060904061502 71
    0xa01e40d44400256024090314010103003000101da80e41d564905000c40c11848940f070109450096440c10000a0041d01c002040e81400d0320400d42516003010894500900003130b88401c02e01b019042142001d4080c00c00d6540b540c10050030035401234086c000c0001c032660080c038000708280205200048c3c2440c005c1146088150301c3c14801c2c418001e0354207174400004014600109500e829400140c151102041904841d0b003450041000303905601030203c0103042c902490b0204420075074040c280c00ca18203022a00403003002e5601c44e040310858170038100260004072203a0340030381c001800b0f290f890b51a03205161261820030500036490440c2c03c0b90303000000701a06c40382c840800b2071041c000c03a6400700f80564419800c8107204401081e034000503000c100003601244090b5084002901101c0b0b403035800c540f00d01c41d01c0741d65014142d42c9520032a080c000151950b60017280000b140d00866028612810382520000305903020403600d6803019001960250355044000740010b495203003500c1c43e440c0c64015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 391441906 1250 391440656 391440661
    0xe24100e040c0e130905070e0403022a09040809220608060a050907050108041b06080103051615030c121b110a0203060c0a0201090b0405030901021b0603130309030807030503 76
    0x18071040e0b03150342c000042409039020f040724041d2a4852003180a0800c06004200d103003450a2850620605401280ea0307a092032042006158001410744800e540c6000c00d0910440d03071a62407850291810b200b0f5500007010008100840c4090000c0e1a0000000f000507113124009949500c0e001c4901c40040d60003070300c0c0d01c070070081c0210501c001a07102000040034801403900010958917800075004271414090001c02140038011240307145007101000b005010302040e1502700290200d04244801ca0b81480f500684610f52907500d080b0204903210108072802c0190300072015400703031140b0003051041210308010a00244500d00510205c2004d021800911207900d600041c496001d07546600a02d40c00003155800603100090010350117078006002d151514a480004c0f809000340d500040c160004030024802400004802003080000907000c907020040780d50348490b030804203d00500d5000e841480010340c0b4000610001034841e1080c6043c5040d55140d6490103415000b2804c20340c00140d01004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 391443156 1250 391441906 391441909
    0x30e0f0d020d110f030901270b03040b010501020a0b0f1306050f070306081203130f0206031602100b01020a02060a0201060f141e03061308040f0914060a0e24100e 71
    0x20f080030110760501800c0c00010303034140d90383d40e4819071001904000301075082c002d0b1180300340480510507a0f45020101282d03940c105929064100f03a03000d440800c00721000250035800000c90b1200942d10611841340c0b6981c900c0d403c1105100245190700c0c04500001010010b00c02d0303c03440b480361800d40500c09060030940b8005049402c40e030400091581708100b41b9641030110f6080c0c0e40e0000e0076001011001d0418a040b0142c00310500c4020b40000c1c0210034040010281e0055004091060342280d1110308540141c0054806d5600d8481c0560404164040581400300c014040c2c1c0d4140d00020828640e00e114142007241550b105035035401c40e0b8040c01c065450300c4000c50080d600b04000c80606003022200007611000090056425002060315080401c002207050b10700410034148000c1701190358883c02070180ca82e195074100c00110000002d90a450300340d580d54191010500c040565035140c0103142d001003105052890f503800046140d0003540e840011720312581055640340b02e071041d001070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 391444406 1250 391443156 391443167
    0x6300b061c0c0e28050c07140309040b1504030209130c17060703090c05010809010618021c0c0806190906062001110a0507020d050304060c1a04030e01030e0f0d020d 72
    0xb800c0082404d0b151035021030b280703a000796508041d42101d01c005400e88400020341a144120f10004100c42d4070642e41880b03101010015110904080d94144032892140d0f04200b0148400848a440d4600620040c800750078030035009603000902101c080241c030b81c152640100c06200e5484507900110502040d04049000d02006400140e1403c0901c040189130b50340b0241503450340101c034100024803001a003004000d422035001400000c0000450078062030102000c4d51080080711514901a00000b1101103035110b44030348100d081e03441300c045489d54420429401d0845000c620381012003000816041140c0c4142c0000b00b449884554001e500300401e42c121038040e6000d81c1d01645403c83c2c2c0c0701d0084800c0201c480000c440d10f001c4c0c7d0b03184da0610008074100c006401c081c1241c070010401040d070341d0b0003000500440b07025911603498915401768521072508110340081c00504c1c0c104c6054099400794010b884081c495009868500c002102c21070301d0300c9400074003080180c0c083c0b0304e003a0809030000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 391445656 1250 391444406 391444411
    0x80a0e06091207030309080d0903241104081e07050103020331200a06180f0e04140307030e06070804030b1f050f1f1b0606300b061c0c0e 60
    0x10015200e02040b006000d070000c941c03407002915001d00c22000850118000b910110421541c0c03808010340040c0c264003508cc0c3d00f2600801d00c00344033360514a405140e0402c0f5100b42c18901c1d20082442ca810320004601a420241c250880540001d01d0421041c1c40e403807042e6951510034001400c940310321f0409491012101842d401d11410b040155286600e4803100d41c01034450608044410b621414082c09a44a030f0341c0c0b050300141d0b0700c443c010030307216a600a900d0090380180101d10180c4a10300120382c4a1084100c000c000c00c2c540c030103a416600741040601030046c000c0c0d8209040641c1ca854a140c5800c0440e070850398400303080501400b00601c0e00151001e44000d0b62985400b84886011452000c11000100b400403220290000e41501c01d451100071130207941f4950f8010381c15850050081d00c040c0c020120911442c0c00c400c82c007102e403981d9190700712407c5400400303550722645440300741c05030107003501d0307003159100d05600a4030f0380601c071748680b05d0b214009200907145800d01052030750002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 391446906 1250 391445656 391445669
    0x3160c0b1206010e1c0b010f0605120f040c0513020319020405010203090409080706090807150209010915020a120e090603030901020a02060a0c1719080103080a0e06091207030309 78
    0x9001064820402150150b03024000f0b0800603078907012800012440412001664484503410041900300301d11040558100c9003584d070660801c41e11040151940d0141101e0403e0b90208080010260082021129041400b62620114868a88000c603002030f03d100c1030151520f40000611034034140784105e83c2e11050741440c0842c00c05041000003034032440390a841600c0340340ca0740002014404a40301303c0e08099030100d8100402c1d441c6142400094000003005e64444c007404800e1104010240215005010142d6800d0300f0181010791420903145400ca0100461140d029900009045440465400e0307101d502c8520480045900b009604080244024044d4200740040c00c201e980004401072883d41c11140c4c50340794004500101c0d44c10504980160800442c45456084100c0600080104005000000c0f8031003d5155059441321002e100040c06400b080000d405410300c6502a1111000000c01d11890035000c040000e0900c0001070340321300301d0780000008008264101c15560000e005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 391448156 1250 391446906 391446929
    0x140909102303060a090311070e0f0a0209100503090102070516051908030702040209030312040605062e120f0e010b0316030809101407060504030206180a1403040803160c 74
    0x3081c402181d22100068810f448942d210040d00341058001c1804044d41481403044640c0c440e59213910605a510668481c001b064549000c281c098085008482c51544d000d8130100242100b0034049030070782c1c402032901c01595400d211001c00140c00340a410101100c43d0300340c100450800c07040103074501100810310419901d01c102001050340c08000d4810842d011100140c070343d011900402d0075880780700e007032082c491800c0c0104420488560310103030107400c090b11000c01c1c0780c1c50350400d142c602d407015500e0004036a030811240c1c6244c0c480c030300c2d040001200c10000b0450918160056081e02c5040d030092003965112903841c1e00c0c0307042c100300c801c61174030801a00092141c6991510300307040c0700c2c1c6503050b8080c060300c0c5100b01607540201030314400c2125441d0034980d204620704101c0028001a07404030b00502515020580c0000105240c2d958080154051f01d890f4000756126108103aa40b140128103010601000807062028005062201c91710000a48143c4180c075103201c18107000d4120041001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 391449406 1250 391448156 391448219
    0x614100207090c20061b0406120c021908030f0c0f0a110c150702090105220504060e0712030e0415060e030a0605010b040810090f020114090910 63
    0x503800104882155964080090b51160054003102d0500d0844070004408070480300b0440601000554584240e1440807142e112407560641900248124071454000515504c00644111007583c0401030b401040e00464510000249c0031114100c00c0c0c003800d80b2021030100c20842d40c0f044051702c0c1c80c1d1201070310f419a464a00288503000e21030140d54060b0040000003d4000c48004040004152243d030041c10984441140034151113070740d1020000328021058a400006c450400c011048841220515111000360340d01f114400101401041601d2054960900c060444400d200c41006000301140410381841030303003000792040b20b1039100140542e00d420070301d0102c90751404d01402616041e240024090806400091600f4002c40340030344203d15003400001c0000000008000f120030340c4058071607500c94048014111500100090703d2102106101740c0190300c920503021265441421140c10301c100b6401099803a44120b60401c0520300507507040c80403c00d801070400c1c141c12100d41e19035044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 391450656 1250 391449406 391449439
    0x11a18040b100905151008040b15181e010602070509190f0e03090a060201020414090417120402210d051803030f1e0c0a030c0212100614 60
    0x5000040010301954000800300d00600c024140b6000101202c074400d200034101624024048820054010b11a181da801c3e42d11400b8003c4404602c550342180d0186115500d114404001e861961103081d401420300c40000c1503501c225011900030b01e003086203024030303010717000c5568481e40701078006405550008808001c7d40e510922503607404240c0c40300820742010540c1c24003000d80b49440322903140714145442d0340720092000001e0800c0c40030850300310241c26581c031340076800c0b0b200354041c0341a60003000640740c081d07040c404005600948a6807110014901c4001d03541101d800542c40782100b246036000380400d6140c0712140d100c08052508181c1e102081c1c0707080d043d40e58009680c0000038420081860000031030402850b107180c91015058a960305000455107415504c42100d0410341010130309005800c03800a0150b51240002200a00c02131a441d1404d544054495200b240d01401d889003005100009101c3c0c481e054070042400701701182410f00200d00c07008000030140c040c124550509000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 391451906 1250 391450656 391450699
    0x70f090b030a08090f061908040b100602100e0a0206041206150b0910030605030a030504030c0e04170c0304180c020d0813140a0c080f0c0109030201050405060a0306030b09011a 77
    0x1004000c5070030038017802900c40410614006d600315408281c3d003840481c000a81c119400d00d04c118421000743c0295039401701112020001401600c006030b0001c42424031509582d4428076580c103030201111800c1038070fa80002c3e4598405e800035607000181c1d41408040117260300890130102035294035020f1090a003c4c000e4030501551900e0392203420742d07540a8800c1400b07680010f000d44005030607155003d48609015141e94044c0c0320458410102e02000502004843d21140c010707503000c241c0301c1503103185110072001134110025000490008200c00903014140e00050707000100e030b0740d9000c2021101010040c4c10203402290341400d0010500400403c0101a0f69600580f6808440c0800142160810032324102c3c010000600d5207018502c0440c00c1600000c160714004641012a070600c84d02000444012005100c02404a0170510061100d0315044010304034045080c0390000d074080e5241c07103081c070050056424a000ba5034814a140080b24038414901000d6401d483c0803030303030081d00c801c40f400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 391453156 1250 391451906 391451917
    0xc2903060906010c15020c0c0f030114011205030904061203081506031308040902030a0501030c06020c030307140a0c090b041d1914030301030c1401210e0708070f090b030a08 76
    0x10013940301c59090802048003034607030042d06540404c54980c43c5070590f0756510992405114803500103c0890041c524050003651781d01c000140d10390403a0391074481c004510312403484044034180414800409641c40c0e900c51a4001c09031a00d10604e4000c490401420307160b40501459000040c00c182181592162800c4a030000880c0b000d2b80c51842c4541449038680c05141c004220b224000018041e8600d141e41011381a00d02a201005016541e10b82c01d1303a480400c400469055081844101c000c6070000311921051000f000030307508881440c1e500c02e411005d1a0b0014455150396486031911030600744288103e20301252800414607111142c81030350741004d44007842107000800e0320b0204000c40c0e2203a030b0310b01c0c1a180b42186c3e1203507141d00d0440518405401a0203009502120088256110718040044c43e545200d400340f460007030300312a07406020300c911040b0003403094840c0010440d404014200c01081014210349e2400d0034030309580207481c0d07105151b40c86580040d01c0c1a000c503441c038045a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 391454406 1250 391453156 391453159
    0x601050d02040e04110f0a080616090b0c01140c0403020d060e0a0209040606180c08041407050d0312050c040e011401090b0c1c03051005010c06090c2903060906 70
    0x6494889240103030020b80300d150000c4440f91240300a10007000b1454001d40c00d036600440352071800c0c0c0d10b00c0041c040e001c030440c07281140350b030300050108000e80b03500721300000114800d14105400716202c5c21b5840c5d803a40610489040344e0756400c15040c03010007110859030088501b14049191614540000700c00d40c2e00c0c00ea000c1c0000360703500e007412102c03103040007000001503001d4400300303040c60103081c0381d0001d00c20b521034074003492428400c2e41460b05c00741c030070011156207945510485840c3c0b91503913102c00910010001c403030b103d0340c0c0000c034a40e6550b0040c1c020641c803030340d101203000b06078034054030a03100c0260011030f07040c00c04c3c8400d0107403130030510342a41500c60f0b10740344038102034a04004960404155205c2182d000c4006001c80e44600042140203403d042402203240d03e9440c941d00324122a0300b220030b65013080034420280940c3d07201e031a8455000e80112008208074659486060f0009100d40c0f240e030010440d1054200314054100c01001d42d1030b80c03016158258541403000c00c0390601c0051016 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 391455656 1250 391454406 391454417
    0x60f060714070f031203062903060f041107060e0a020114030a0213030c090b090408030c0703020c0a08060709060816080711010e07090e0f030f0306180c04050a15080601 74
    0x501e108008008840003008207aa100080a64900307103c8225a400208280024101000498080004a90b41c4160481d00d81c880c1025000001c03a140903803c0503221a80c0085000080c002a54607802424919100c0541c0c00d40e448049181080c02c580400400d5203807a00b100003040c0241c1c0e00002c071006402143d0729426526580c1001c80302c02403003100805216000d2501d404010b01c00b01078032001c16103804541c00c1049043d8001045610310046900600d0101d0800000f4040c81915000e05211032113801116a040d8580300090b82413141e5402c0714032141d200000f000301056008003854024440c07418900a1824500e00c120034004000c901401130010820200b5400d5202e01700d101d0810416800805ca20050b200c84541c5030b42d180e10900e0641424048188801103000c6803a01010306144025407600e4012a0041d56603000188160791103001010311810101404958a104d107407011103480c0c0c0e40303040104020394580c1c203070024a418181030043e42d01c06a00108881e40229090902 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 391456906 1250 391455656 391455683
    0x80316050f060403050a030c021c050901051c020a0e152a030c1b0102010b0a180902090702010c080c03060f0112060803220e060a060302070203070509070c020306060f0607 75
    0x41450158041c00c211494403038001040705166002000c0c20049049a60602140c81c01400c201e0340c0350b44504841d0301e040c040042d42d42d0400d0040c0018042c405042c144207080c1001508580007440e80300310340c0ca6402c0d0700042d203110900d610181740c5600100c211007501259120610700f03506805001e1a0003181c114100d0100524454207080342d5407000c2c200c01301c964684134021000d0300d51940640014a0f42505d0b00c02145544c0103018440d80a02c01400800d1030170310301104940000c1620101c401c405580d409003001589498101d43c2c1701e900290000304007010204c00052021400400d4007030400000c0c403c0c8600c0d0740e80c1080e040315846d000d1902c1c020114103008010f008007001d03800305e201803000185a4281d00413944103904260410910521440d640f884603025080d02203601c10352000b601c0c1c00034402a40640d000e80103ca00142c11103070200d85a0f00405c0c0c3e940700942d8000d020a5140b5188800c41ca0100009503002105980f041d100c21001004501d041c01812030080c021184040c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 391458156 1250 391456906 391456913
    0xa0504090e010b060d0c02012708091c1a0708010518041406072d050a0f0201020f04090b1f0905061606060303050901021002040e0c0706140c090415080316 68
    0x3145203d014010015903588070b201400b8401410341840d07210140d400c01e803601c5102010050043c0b0b0a000d2000d66450040250791015040c2c0d10141140307500000c41e01301048000100141d0646483c8103600d004007030011b032000c0b0003040900038408800c000e007580c010b1019842c2c054800c0100c090200c02c00000d6100c41c50214502018090054924411003080000e59544038a0a40c240c0001a200c01c908107003480200080c1c0a0381c5800c4004501c0401084000d244554050402840e21744001810030030000ba0b089019400356104d0107034103803202e581c00b48502d07202805551404103000c0b26400f10300b816102030001c0b03980d0710455104000114050030b54007204120503150f554000c01c2000031603202d203400f80164000801c094011321450075180c042c01c07098802c0360305640016404c00c1c616610000130340b4a6900c1280211045511640e05000b82c44031f8a113040c2c01071242401d26901c0c0c4810300f00780000c40356011050b0020910810782006884404812100c20307002500310031f60050203509 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 391459406 1250 391458156 391458161
    0x100803070b0a0209220c030933050411090702030703090506090a0806040602190503100302090403050c010c09060e0a0506122a0a02012012090f240703020a0504090e01 73
    0x1150170742020b2410810380c5081c20700c114100200e4102902001004542d280440444086010003403803810000060904500403429808d0251440200c490b450502040c140301503440c20790741180c0350350610024000070325120f1152607020717131b6070b200940c18410540c800900700505071040d14001e41002640d405261186500d400142005c41e040b034481c1e0900b850400700035486245025103100302620384030210392182003164010303030209050141184c00c5808002400302c0207030044003800001c10840c22840001e008421103402c0a845103235905152103005011a0700c84015a441464a038105001d01e586080541b2514041c020030030700ca81c4c1d079600100c07105d00b070641c2c0346c405e02410040103409050b5404000f028020b00c01c1e4001e01a0032070740141940300ca1103540c5030410104c403d01c00c40c5610004400103581c0103c0300c0040f220203544034200541040c40c401c105620b0150040401607005a0300c080098104540e841c00318503003180018010030310700550060414179926659a10040c00c000d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 391460656 1250 391459406 391459417
    0xb04060b011b03050c10110307030f0b0406080a020a1728060e030d0615050d02070320030a090e01080303040201140904020310090c03050c090f18070512100803070b0a02 74
    0x4484607408040039040180003500240220491032007111103030b86c1000c8817030056000c28168040341e03d045883d8079000380c0241c80c4502c41440d0050341e641411100d0350756801280028608c1e04060044030405005200884403a604400b0719201e8401c0440e02c03100300084c2006808158010741d414100e5066a400c0381d8a1140c4400f8010b64200640e40040c0301d000710040c1896103241c0c10401c203103a40c5001c081e00318035000207031501041007030010842080d020380040c4851362017490a0009039001004020120300804040c10141d400841c00468180c1c000018002030035000071207070702a43c50325420340d42d280f07c014030003810400300060003c25a52814180d038591500184155180d14041c440c00f502e1001c0d03407040c0000542480f03c5210362130b0192048070f0152420454a0349400520700901840d140c144031001c0d08000c0d1402500d01140f00c802031640900c40720754845540f1042d0841c0c036800e4a00141001e043d140c08038004001200c000811211950350080d5000c0c095903030381003494000e0080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 391461906 1250 391460656 391460687
    0x5091009150f05240109060305040f0204090308010611030405090c090312040806060a051210050c04090905030c070e01080607180b13060206150a0e060f100c0606120b04060b01 77
    0x74482541048121504180d114035501c40e41410104550140f8403180e139070903140035001c02c14209050003034a2190704915840350203030b01d801c003040d8010390124003216140740082d00042c81c00c00c010f101181d8000e01c801c0c5600e80800c0214101414400010424003018100310780722100000c0059158902f488080d6084081082d555242c41da00d56025440b003808544551042c1c1d000c00000c6024a000c2184120b5010840000d10f01c0600c07190800b801008050492940410103000c001032005140c0a089a106d20130005951034194556402e803800c21a500a02000d030300e6100140960580007507966070010761403428001c4000e103101da20b0b20544054000040c0a00700041c42059009002e17103210031140650708031400c43d0781e603003a400800c20640c019154807002c0c13544108110f55021a650390040d030010400c24186c030034080007030a4401c5900da65800700d40c140c1940c00522074203100307240007031080844118000d01165114514410000c0c00181541d9079418221038992180b0603003030080301c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 391463156 1250 391461906 391461911
    0x120915030702070303020d1e0309080405030d0c0b010e07120c1716020d0306150509130203040b01030b13021323011e080102070c052407060b040c030509100915 70
    0x107001c040203480f504079000982c0580714584407110014801d54501c510588900c00c010005000090202c001d0102c0034020359034500300340320116807940c1c103000f0340c40b024803241c5504032501440d152610031841c2c141d020150500411007049078084d000210b0f85401d50300a440040e6180c0300d00c400780c0d00400340303154400c0c500c0151810410007400e40711941c00703101d50301d0302181d000030340030801103064981071700a9506104c00107014180e118040e80262604040c02800d01042462000c01d010498000b118240c400c000000010401d100001102680040b00325810340c0c624a00f0f80c001c58228031004000e1245107039a205c02e94201c50309144a100c04081c54500c4400f41e5968003403074a41c619801c0100390002203a10380002c0c000105100301c0c0c42c61907001c14240513051910041085104032680c510740d41607a0b00d020001b54403d084000e002c414030076800000d80044e1035061000704ea8594030f252051510306014052007507400900d0780301c52043e20101250780589031500c03207401004814084001030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 391464406 1250 391463156 391463161
    0x7061b050a030b030109020307050f01051b0d090f030b010506070501020c0a0b0a0c020c1302031902030c0406110109111201090204020d060e0601051204110103091b080105010609030512091503 84
    0xda200c0c0052503151941c1d03a040c000c0c1120b8400b0182201c208140096041d032040408001c1820030400030781e0350220505121781014481d00c2d19042034088080c01c0076030380e040406101380d696008a401c0014140440c100c4a250b810b69072203d40c0c051040c042c1e43e205d0301004c07417403d0800500750110f031110701c8406d080c0c400c1c1d501d10740703405607500d1003d0700c41d001c406003044c2c0341640e07152001507880600380004045580c10f1a60700c00041c025480688640c04001c0d82c2c1e03a030500550440e0004600621800c48143c3d5aa4a8250010824800450b0f40402a4100000240420f4608080c9150f1450484a070882e240c8518805401044000b80003500140041110780000303040c1d03071012044500000c0c040d40f441e5110001161144505d1940610030500a004180881d0302d5a0940120020606001030440781035120304203900c07805d032482420000545028402c0300c800380185401043c403814080040d9055035281500d03640c40d42a0324162100108265007190b950b03940c1030400340305110240b552070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 391465656 1250 391464406 391464461
    0xe040b15060d0207030804062921060103050606130b030309040f060515030610020705010503150103060b030408070c150f030203040f0b010b070605010e0f1f03051006050a1502030403080706 83
    0x5800403a000d03102c2d54548a0303d040140818002040d0f04055002442003031280d009c20024010103124413041166505244407120244c204507150183d0300a1700100303e20701c0c1200070044c92240041c0416445414120302e000c4a80b000810fa640d0180f0489010440720601806a0010040c5602540d40490a8442520340614210095004290540d00c0c0f840c00018204140c1c0d40e500c0ca8890940040d004000243e00d0401d606000015481e0524001ca01c0681d00c984007071a507081901c0a46958400198160403c03601c85100701c0140880e0344101c00496019401900003103000310984181500080000c04010000c0b280b40e12141d4441030842095844001e100c070283c000d1001100c506140000100340c5007440e01c02e96100705500da110355400e40e2182002002248850400a001b10f012140440012018448a2155100d8407800120980b0b04020401c51817a43d602040d03023421042c0c08484025401300440342500e80000020350740b20200d14042004100350035803040c1c2e0301004000040341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 391466906 1250 391465656 391465667
    0x904030e01170a0c0318020604031e120e01030b040b010f0c0611030403030b01021011070f050a0506070e04060e040c0b030711030c010f0605060c0604110607050105150a0e040b15060d020703 83
    0xb1300031603642c10011800310070480c04450780c80d6800694445030900c4200b0025500078810184488494280f00c1e4002087c0c2c0ca02d00e40c2d800010041010845401100c0382d19603161050012003201150180002d8000d000043c148042c0c4072010001c0000c0581d4180038800560414801080030a03800b40d075a19080c180140181000b030300482c0103000706000c20a062815018100604038560f420300d140541039034800101c00c1042e0b074111890b0040c6064134010034030034070400e441032100c1e45a1032910300142c403c100450f000741e000342e074088448405210104880c0409102998900e080041c1c2d292030710715041e030f40d440300c840e07411460b4803000036031080542c011b4101c50507200103420140001611141042000d01070441940d03042e510210006000c503101d454894100c070006040c1a19200603501d816003500c40c101d0f001000360720403d04901081c10711100060040800f10304a91450a081d1b4034a40200320250044050211003100884596034590880700110500350085540308203070f02e4003419 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 391468156 1250 391466906 391466921
    0x209030601080d03060b0307090b070317070e090603190f111009060306091a01030f0609020c030310080f0a14241009110f0f07140604050d0e0904030e01170a 69
    0x19060040c0092040306c403e0582e030042c0d00a4aa1101e500d041127501c0701d450304000070503010000500c0f403001d000e105040c2c001c1e020301c106070307200d07a81024001d0620200c1400905030501a0340900410404000300500030b801859000281c1c8a00f1040b5040801100560800041c1c0c07041d000d0701c103a821242c00106410480d140c42d141446a141d807040400116400c418201300d100416920a07000f96109a04c40d10900707a01480004d40b10752281d000301d00301e0b001003000560302c0e032000041c00302c980b0b03008003a880280f85140080c500c01c0034070401e2a468000c800300041004005141c211543c4800b800145112031400c0d454400d0302170416065070342c01405030744200c0840e0381441c0c0850780006502a120018880402c540d103408000d03108844650301c03100c0b59504c6c044c0e05109020004152020081c419484500240110b042504045040c80c1d8420a200244881a00001d466485e03070242e095206800d410800c00c200109030068842640e046550142043d500b401c020000d24164031100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 391469406 1250 391468156 391468183
    0x6080a0b09010b0108060103050403110102130801050c0f041203020f100222050603190906090b09100b0f0906121c020c09010b03061207030b01080129010807030c0201020903060108 79
    0x341680ca807400e0302402c90f460050014006040680091040e5000350022500f2030311900d0043ca10590301c14903a802ca0f005000c0c070398000040b5800810418a003401107a801060b805811490300c40d040511002e28812445078008100441c01d030201414002c0c850091076100040a84042c0f03038244103003c0003036004540e81e010380c0800c031040024121400902900341c1d1409007071b80703155890796080c0c50454100392090540c200c0d260388070000011028000e03107001030700c1011022024100038680f02c1c05d00e01c0c601d60100e051032403c60041c00d540c4c2c585544014014081c1c686c038503030340c890381c0c04a100a00020a10710041c4104446a13a104161100315031864031242d0a075051000e032030040200d448028803824000780070900218460b49170036104461442e21030303000c503004c03142c0d01d0756800c042d040c09a0040c0d0390307659031300300c1d0341a4101c1c1001400700e4401c00c1855107100c100c00c4070018040e5800904038000305617440110400290003581120400c0200504850b15903035111800d9a0ba80800f20060 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 391470656 1250 391469406 391469423
    0x2d03061e2408190b06030c130c0201050c03090d03051e0907050306090d020601091107150506010909090201020a06050a200c010f0510060c0221010504061b020d030e030c0106080a 78
    0x18441c0780800e029060f0f1100620090080c00e00340c581e00051070f0050080c5030b040c051100a0f80c0d00390748090401010700500c0b04c020900b80c1c050000039085030801064480195410010000741c201c2c0401c40002c1c0303804034100020562595491980c00355498204400c00000032000d201011030002805000c075403044080304d810740e9600121a880340700320544400964040001803100301a0703034000341103010310145050300b052910f0b00d80c42c10034515140800340155484060109650303000d040743c0003078500207400b80301d01c4450f41d000075661a44228090400740e550004540712480301c0d040700300a1050418048002207200e64aa8002d9001e912581101d40c6413441e04000072030b25010b6680300350741100103581c005150100a449035441035030204c0c3c0c0440342d05c2d401d950b05550804608442c0780c542c40002042e1a0600d03101080b80d980030415a00070031f402600c00d1600e41d00140c0c000d0003402a18000c215811103910552460080e4001c0311240d50a180001c07e81180002c0c0c8643d400f405040b05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 391471906 1250 391470656 391470659
    0x303030905011116020d020d320a0b04031805040608030c0c0d05070b031503101a04060b1c060e090a1b08030f07020d0606030b012d03061e24 62
    0x19a040e104948a0f03503084031000891348094a002010703c034000340094203c5215030100c0d074400b05544044401c0e0700124900403118408c520420110005181000c0010f110090207034541c007108220080c00102004a00580400102c0552a03448010310000d0414014207458420327080d283c1c1c114110100e85840707609110710a03854205940c241664009019280050500c2121055580020b001d01468454174500828545042141f0380400b0441c650000710040b800c16580c1d00107501d201000d2040c1c1c2080340600c0031040050480b450303491015040760b003804030361400202800780d82e0f00601c1000c2c4040204a0300c07201c0412042e10b102d03c900c0b4091a500f01c0070190781400d801500136a081588280041e60786e6010b100c2c010640d50b40014081c4080c10482e80e101d805482c004d4004039040400c1f80b0041001a1415aa1003603c0e1460100740f4412a042825005400300c240b00103400e5a07240c46041d0011040c01840307840e1903116600520243c010340002c2120071044c044116401d02d001d510 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 391473156 1250 391471906 391471931
    0x1e0a06020d0b09072703020d0308060312040803070c0503030a09060810080a05060f070c0308040206070c1502010603140a170f04180b0a06050703080703050a0219030b1002010c090603090302070e01030303090501 92
    0x9004203487c0d0050081081c2041528201c403e070500600c0c3c40c2e018402c4041103110201c42e4406440202501340c000c40e560366440c038001100c3c22070b6600840c0680d00a114480c1456080442c0005442c4a40b41500c803a6039203143e514403034641d81d4042e140d140501903103c4140103011545034840d44040441000b5522214000c450508a803031000c0c000032030003004500103140580040100c24014a50352080507111003082c0400082c40ea01e20340943c4d0740d00307800c00401074074004c010741035002400945011900d03900c42a130440a80400700080110000f507a121030300318031007030b10040c211148071114400540b50640000b003604004042c0300381d40000c000242e00d8480c00481d024154141e64120f4580c80303040c41500681030180c170b012041a001d10000c41180442c4a6440d14440e403a5804540045414207002201058446107070131079040091411807243c0000701ca80450b0a81d140c005090142d80c01c04906100721900b01c980d40402c00070000042c1581500a0000b00b07004034001c2000001590 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 391474406 1250 391473156 391473227
    0x181e070210110909130c09200f0a0306060e06120a020c0102070b0717100b0306030c0303130302040b0a05060301030f050703021905030f0c090a0902030c040612051e0a06020d0b0907 79
    0x4006200d8411400b0078401c064180c5c0210023a80351012814a208603c40e0840c000c0e50043c40300c0c8c40c04000701040440310507a16000e918020400d500340807801c040010003160141c46040301490315580000701250500525504441480c29880002c40d22100c1c10f160140824400b900d010000501ca040c1d0354890b1302e419840e05008414440e00140002d03c2c01da008101900001c048075414018598030224075142840105040035071140310315400307429072041104548604110a0090544100502c2541c0ba403a040703e05403a0003c007425040b42580c98098178109860700000c0d009090a0072100c040030188180a09a03841142596400000c1c0141c1956030030800d118560700104910100710000c03035a40c4807039021800502650101052040810160b84450380007140d003036401ca80310002e120051001119a03181200344403409800208020349e2006c04040152031075a00141c084a1407406038800764004401408826651600c400054a80100c42c40b101c0d04400c03001854555080108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 391475656 1250 391474406 391474441
    0x5031e0a081603091403030901030e150a02033102011b140321130206130902030f090d0c0809040213080124080a02011e0203041e05181e070210110909 66
    0x91b00035400c2c6015107004601a00d070f070140c842d0359401914010100d03195080d041a10411614001590324102244e44010809600901d80f00c051224071404580005c010011584640c0901e04400c8458007414680341032803800c20000c000e08030030709600c409d401001c0080c1502842003801c40701085004207600030b0f98102203035407000d2000000003100041ca032000142400d80300f840080d440850301d90721180101d9000340c0b0510b0980000c501007115484041001c1c820102991a06080844181d40c410040d030160840c0c103482140c0215011070700484045500005100090083c40940d0f20303c012000120b0001004c1009060391071b4010480400005a260a007541a9122410b9460342c0c02e12401c1e00120311441c00c00c5000801c07000814900ea140d03c000044141c0d540000b601d45020104540c2201215188446d01c0c140307010010a0030301d466180e60f00c2c030301c1303203c01d0f06460342c3e4154104c0c1450101c4030601c0c6201d14106401000c40f2460300034200b200c0007510200c0e095100c80440d9117085444 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 391476906 1250 391475656 391475659
    0x150603160e0114010c23010e010603050c0f0a1a0705030f12061207050a05040e01020417030a030608010c0c020423070504030204110405090402121504150c0905031e0a0816030914 78
    0x10003620705070f404812a0071010446c1c0303000001660031030744903003038255485903106881592290310f05e005245009440744040300011110780031914a440490745403007503491111b0316030080118428050200038001c9400c1c415440494580e501040320054079400070946003240144400b103000d204503213000071a40141d9400800c240140d6103001c082001505892012129554080c040000c40e03980901030020913404d07410282d515905201401401c44030903034070a21a0307a040903818903000d9042414502201e40607a000b24040000390140d070010f0105507075081c4114500704c00c0104d903a5200c0c0140065038400c4074148241c0041207552441d43c002da018030b40c0c0c403c1c1d051010400503c1d00c08414484402c10030255840400316890003d2100c404036070070345500180400440d0b403070035a403041d048410b045040510304c0a0606022070391b18008003a00b182c580050508804000804100640002d0f51065206a8075403241c120620108034009048011651034880400c0c41c030540d1003540f003803100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 391478156 1250 391476906 391476923
    0x303280603150903050d060905070f051312020105130608011401050903030a1b1505040212010e100f021201030807030807050a1403040303060e040605040201021b0102150603160e0114010c 82
    0x480307040b030300000c000480c000c405009040010352000ca5580c02003800812000c003000038035280414018181624503948401001030401038800c40140f410340d240c043e20744c0c103401c20000c1400b178401a039080c4107002c0e40c240030007141c610004081d540501e66030b0603250003080107880b4140001c01501d450040b0443c0d40c0d415003040c840001c1e81481103d651011141180e002c04400499444110f4050b8084c1242c48420b91078100308020760510210040c0380d8a0200300030860143c40b0f868035034a0384803c00591035802d440e14102e14050503c0c0c1c0560306070b6aa00001039286507500e1402150b10f03442408110040fa803214001000380e07024a06591001c0a40d07220050792400e00c0600c000141d00062048003859030311400030408140701c0e50340c644902e1013030100088604141c0006403500c8102c03e500711500390300b4046010f03143d81c00b15160400c1800c40091907010344446001a003840b0700807001d50364901b4142000038075007804a00050403a010b155021a15200c218011120301c805482c01070305481 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 391479406 1250 391478156 391478183
    0x1c05090f03150a060f050a080c0f03030c0706020c100f020a03050a030612080c01050c0306060a230c061f1d040f08030916330c050303280603 62
    0x20411124408840c004003580d09001040001e8020b4001c15545200e4541d0f032010305002424007a0240009000211200c00c08a490300c61001d03594000303400c46500030440c4401d101802d032802c109a40c0c940e08604155820952100300080d03541e00e10300c1c1000e1040f22072044800b441d60180450071480701d40c03903000e01440811a10150792a5009804a8007050303503840001805450441c0082010780c810380388155030340398150202d425a00c01910a01207080c0820500c82642d80d64011034500141c2400e01c8081c0541c0302d0114040480c240c43d22500c1c2100008070041d415002007400340c421954804460841d0102c800c80b44a10743c000e00030440d00c201c80c0c000d1076281031030701c1c890715520900c00c680b420050036940d45c1d20410380e0000c0d90440e02e0365200e6403d508680910a01034800390066180c0b0750986070100250038440300c1c4606c280601c5034698909510b845224118402c0d843d0b4200d000c80399207040c11071500d4204212041d5140d002d4250000b9034002d40303d03c0c05801c08aa40124000102d031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 391480656 1250 391479406 391479409
    0xa030b091513181403040306060f0503100c230d050108151e040609060f060803040f0e0411060313051b042307030e0a051606021908030c03060411030f04051c0509 71
    0x4540501310042d1000384000400075107180a200040c0280031000ca0b138041c68081850704e08100008130044040c140704004032804d82c003031140c0034244030010306035040000da0306240c0300610584c901c114142c0d0604c800420000310000d07520080440b6405448016525080c44410071241d40148000d1040803d020038046803454010361038450140d1400140440d90024000454070a58080c2d0410b802c04a005c003d866000307940b4400508000ba030303240796403800382d1b14149080c021a03c0c00b07101d502c020000c5404210510954000340d6408003c50b07411680100310800b0355003032150745611031801d218072030301c1920350650030607100070a07044401496114003000780d028002c041d070741001c0c6100301301c1e070007010460030407604440d54401c0303014008e480e040003402030a081030200300300400200348e803032440040c0034042165802408000015225202c120000740a07008040e81c6039080c10740801840320f006480e801841c0224899001c6072100008224111640c03408001c4800c00702d4018410300c80c59 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 391481906 1250 391480656 391480673
    0x303090c01031a09070e12030c0a17040308030c030f0a0b01020d0c03111e0c0d021c15140711010b0d03080606090603090d2d050a030b09151318 63
    0x2441d14030700160b03401000c100100d1074000c02110154000b446c00c000d610f03100c1c10449200f00724440d00501440c41c00e200c0d882c909546000340c410040800b98a80c03400e01401c440c15095034041e40d8070800321580c90a14600003909038106881f15401c51961a02103a807500d0b0512802e012504180c000e0070140c200d0040c2074903200b10218085c3c1c20b20480950382200c0300c5051000b00303502014205030121140821b102585414228804140a2568000d5010240c4e50703840188004401240c04000510a80d29042c114900640000c0e2401400c0400751001d0b083d00756a128452038117039940c160360104154441e030076175814089042c1c00c10b13101c1381080c02203403284000a1740302c80094071061902401e00081070a0340d108440902c0c039600211408000958030884061841c4c2c000300c0d000c894002440b850700c0700121001c44502c180301c400207640745a1030080c0c000041d0a00d0040a0083e2494210142c03100a662911040e118601160342c0e01a5144c080c46515001014100c6914440b20555500c4c1c46 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 391483156 1250 391481906 391481921
    0x315010e2803240f0606020715030e06010609170c0906040e03070b07030204081c1d0f03010c0201021c14010608060d0c030f0b09150a020904090501020f13080303090c0103 75
    0xc0d01e40707040102001160404000c903003100340318420101a1061070018100301c8804100711898642000c40801015600003580801c0d100566005400c007100020250700401e81180891a0781c0902400080d28035000b2040d501280e1040340b334400200500701203183c4078041d0319840c5a00035030000c0400c9490619030701c002c02184108007100e240c40d0144e110103000280890b2128000f9400060503c450322040c003003400c41c02c0071410300e81000720001d5001b510300f81c64072900004c1171190740300f007030516078904540c90501c1101074003c00085a03135a0009002c0e6001c0e150f0705500c01d0080c07246001d840c0740d038481d507410700039100c180842c01d9081500c00c8480840c0503143c01ea0220007100c091010a56040380d52000b180705415403074a10382581f40c0b8085941000b0000100d40e0000c2c589082401d0a100e03040340c0c040c6e04514010b1750b0385d200e00000707001080040d070007600f1503101050721400c4020382c1c8003e215440460a1811459684041e42941d80c4400c0342c0b40c0c085608100718001440d40250013010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 391484406 1250 391483156 391483219
    0x1805100311061c0905010b01052106010c080d090308010b0414090c09090a020304060c0c02031915140a060801110d0b010918021206060c07030212100e030315010e 71
    0x626043c1c0794030041c0e64140148245a4030556a6982007041007402d102d40b031044030b800c0c2405c90400c203d040e07014204011511840c8480c007107010001e02d0681c4521a941c04950340f009885807108041c00329030703000b800058021000f0410400000c2801c044110544080300c401210815040c00040180044510081c00901c061501070014041560701e800b031a0b840744422010040c0c0f42e1426090070001d40d40040101024003006145050150320045810f03c1c800d8200f41898074040c3c21451702c003640da1460a540c485841c50b02d2404141950603d0f01c65008012141040c1b0006403600c044030708940d030100185615800810160000026130b41201813030140504103510700c50742d0f40103000301031900c001902c00303079590006541e540d1040460050360403000946403541004600c1c1e04541d518120790001a2041c1c2c03211140d0704074020f040003090748100c40b04000b40441c0c0c5034020180ea50b900182c80c20f040c40034407c038000e202c40d44240701c0381c40400030041c61100d690060344c490150607035005c003009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 391485656 1250 391484406 391484419
    0x140f07080405062715030a1a0603070906031a010822080414090f09060105041d191203090302030409090201031b05090406080111040306110403050105101805100311 72
    0x342981c503400a02000c480402da02c180400d0020000c0000042c11000688251070200e03c0f4902460345c0015203604c5000b1520018580c83c40300c50300090302d4a000d80390b5034011000001c01450039400100101110000e0b101803000380030036201d241500e0640e4a00c6800646020005103142001010811f18050f00c1090000700c0402a12080701682c42500503c8103a0f40580d070303648813400d10700500c07075110480303202c90421424640d03001911a0303c10300c03896100725203a50014484049150071029503041880072115200807550104011000308002554013a1075080d480010900034041c1e28511541a40550306d054103007810440100400b010076810141c0e20550720358644200241420008001e4841a45442680e002c00050f910305411641c44c1c2d03414240302100500034602901c080c1e980c044c80119003180e0070794100556024030751020308250b090200b44040d803080101c041050311a464555009152000080800d0302c00c107030385000c180000e01d001003002c10391004680b0765044005050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 391486906 1250 391485656 391485659
    0x609100b0109080f031b06070f180914061513051c06090c051905030a060b060c030a080103020f010f0e0d03210608102706060e0103060e01050601140f070804 69
    0x59141c00d8203a00c01d18085c2c0e00000741c00c42d440c000700070300b841000b0510000b40340134581600700a20401e180142202804070101241c80000e4909a40d200601001c0504102580600b101c04d070304e0000c19100c19004001c144031030040180c10500f125030305000000412006450001401a1091680000c80e40042030f4107000b40052118019a802e0901a44200300034606003010002c1429052158440e032903c25241000551800720f400201540c00070070025488101c1c01c0450040d10990107002e00a00000460b07626494000c0300c0a41603c0c000e90750078402c111340000649105c000000c80d140420440903000c035082c40c1429603450214070034a4804908600d035983c0310f9a40c11440800f0584940780e80041c000fa50040001d805021400081407003203001240070500c04806014103010440046030400b814806c40760458801450f210b040c0c0c40d00c1c0d69403030900c080100500b802940c40d0794280004210360390b11525102c3d01048000010314079040088548000c9a0f0012100715002d1a05000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 391488156 1250 391486906 391486919
    0xd0f0204090b090c10050a0207060305090705061201090b150f07050a02090703090201022a060c16030c06030b0a0e15011b050307050738090a0609090e0609100b0109 72
    0x2c00038000c207a15001030850148080c100702030288a074100b4130400009000805a203a40050008121a001c1c180010b0316120710740401d080c488150441d40e00b100b00004c11040b0300c072851580790f048900c080402c005034401c4804000e0000b091880780310b054502440020444068a402040b159201e081110340e4042c0560100350f081c0300444050000c01e5450080c0415941c040c005035522465070030581c1c1038510342e140c24ac00d03000059042c0b00e00a01c0c010a0078541541d040109102d151400c1c10025807a65903441c0c40c0034480c0003405502d0001b42441c0498000d070510307540e100152016007007101c5441d0f0b9040200307480c030b80003210014104001c000f401801c5010310074003060017500a801556030703200c1d18100a4582410350b4440a81c2e104904500585501000701d20011040001704120030269440b05580ca00e0181c0c0028540c882411580000e216802488440032114104003c2c44802c80c0007004a0b15a0011030b00c40e040350300100001c0240750000d50203600c0c1400141025004107441c1c02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 391489406 1250 391488156 391488173
    0x1416030e011704051b061606090309030503030a0605040c02030703090504050c040902180102010c0f020c01050702180a09033209060408032709040503070204113106030b0d0f020409 79
    0x101c1c1a03407950005c1a4039100307458410300a04640701c094600ba861304c00507940c2c1c840e1100740a100904200c2d5141644020141f040d20100001e680200031641c40342002c08000c001003e051290a01c128a0298070250843c0003000340c0e074100340c1507150608030511b05410711000d4100140308070807100d010003001c03510203a80e20240c094804030804000401660000180c00c40e911800502c080c0724203074000c044c04550024008500040a1800c0c0352284218030208240300703104054400b00540c1c48080042d00113407031b449040c52038081d030740b041c5030100d90280b045000e242184516080070032910f411000200400f00a14040101402d5245001d9484501d1070a50300304140384944c014440b289001c08666100c0c80015194003211240140c0c109a501d0340e40c0c03803080100c024080c680310034071010605c07141000e46100d01100c11050f12503003000c15842200032540040510707001e2004501040c0184070b8815881d1030000502411000304903a00c5400601c45810422644283c407a440f2100140210 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 391490656 1250 391489406 391489411
    0x2010b06040806010801060b040b030c0703261603060803041a040306020705070603201206010903212a140f0703030503061003090302100e16151416030e0117 69
    0xb103001d06100e50524400b0760a494855002040c02d0106120a00444401c0002c482c0c00100c0403154a030740c1c10292505503820040f20403021400600009015000603100c8601341c0f240301c0d80d140310784d80c0303100180e026021a100b078018090980d000307000512200328141440d103c08940c02640c3c9040035506e03a15001641d1182004440c29003041808100e02d82d01400360b40d40245403265407580d08150320034200140c2c0141040107540c0358580340411081c1e409884444040e542080700c01e03561441081c035a9040d081c41341c401c0c800017550f81e400900f554103014181840101a84806519004142c0f588064902400c1c03503107460703000b07403810404010810006000158880c5c2c65003906d030300d00300c001c000708041d20203100c500341410501e0440c00641e002c100c60700c00081c2c01d64001060010011300c20b252107040a405581851a803d001c2a1110030f00c500070442900e170703620400c0d22003500c1d455128034040e03886090030480505014400081c025a28011001c03c10302d0030506240f40c0140050f07414205 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 391491906 1250 391490656 391490669
    0x50d020106080727050601050705010f0209030c01020f06040f020102030f0a0e0a08010c0f05180301090f020907090308040302040515030105070f140405181305120c0c18040b060102010b0604 83
    0x12054100725800c0e0034840c20000f09007600d422510074209045540d8800104c0280401095407140005c041da030140095850351500030000b041490780760100c2200030b61250120a00c0380c8600744c805004c2c1c1d0710001d13541c0350151086000d020709480c1c5036900400e003111504208e05600051243c0d401c00c003a0386020708080c40b07043d51411981d01251080c85204142501320a011345d0410000884203a005400ea0300d0008042c07400b03e81d518652808895050600d016640d85942003200346003d01050071498601e55000b10f40c0b041d42e039100d0a1094450140030320004200c0f400522082002d071516900040c0d20003000b480307013141c0368231840019003164421100600801c05000810421136849190b004041d121510b04900c0e103424000081c0e10100c204a03546c001c8001ea0700001c510700c0c280c101910805a0003012070740b41040910000c801e03500004140307245071040182c25110751804e14135101d130f070103403e003141401c90300c0c0d54554400344600140381c0c40c1550348952034641507458020041004008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 391493156 1250 391491906 391491911
    0xe060f060304060b010810030b1801150801020304060501050607021f0314070804031d0f060d0b090c0c0d02060c03060402030907051914040c1b060f110d0e01050708160c050d0201 78
    0xd000009080888040c00c030f8205447c6240c3c1c184005500c9005450300001008201e150110f2402002405860038201c0035510ba0490750b400500c0900c15000f45024178421101844030745c0e225001c0c0515402030b0741d4041e41c8481300c010250111500500c0c5104229a14079010481c0500d050303200070010f409407440c40001d1200810401807540c0301c800b0720403403482c181d0190307240c201200010b20780420001c04184104000644044009459032190304c1e030710000740c80d00b203072803403d000c032402180c00c45103810845000d00c084000703030a480840e03441c0c400e01a010300309045403101801e000094000401c404462302c203081c008a0195030304a002030078003a103140c0340361685003440310401542031880c18443c015401c0124181c2c030142c001c0940c610300c6172000301c01039100320103040980241a030100103d10321072901c0075141106050070700900d8000e2000390305002260382090300c00c0c208c0d201290140b001460b14008607801600c408505802001031345028008040d03070703440b281d04080e004602c600151b035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 391494406 1250 391493156 391493171
    0xe240411100509010e091b0c070906080a0311070b03010b070f0609050c0f010305040f02151612030b01051215011709030301060905180103060f0216050a0c050f0a0e060f06030406 78
    0x1a4001d0b580c5d03281a0064800e013140382000000c00412030040c102440301b0090100c0c815201c024100103100082145180901115070348041c083d4461500d9801600000e001e49a1003080240006034801150860203240d4a03580ca071030a54116a001000c0840d00a0102d002e14004a40240143c100f80c60055015000c00c0c1100c00820406000580d061818036051101300004126008041c01ca1181c06556556151080055002d0b161044080040c40001d8459184041c4070007007275518460309090300c02300501d421200040d1264050b4820040300841664002584c50156444120165006050240d11140c48500c01580c8840c200c1ea4610305900202c01001031079031264005c0002d20042c1c1700843c4840ca1035841c00144e440500000d80301303c0d1204030300c0001b076019030b04a528020501c100c1c0e103c1041070b8a020f03501d550328030009649080b200c4c20040b82c075140500c5811030000d4000c100c0c201c210300c2e2100c04a4030345401041540c0c400b59290040000e900d580700118800d41c8201d40005011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 391495656 1250 391494406 391494409
    0x1103030a181d0f0c12070908010f02120612030421060501050f0d06050601090b0304030f1409010e011b060518010e030f040501030506240a02010e240411100509 70
    0x5001d541d201e88640500351a03885980c5902d007000039000440303d0020380181e40d954950300760320b20503441010300310f2580354204200d0704c0c2d003c141c01c0251840705000740b108480703558443d402c1c1e003d40c20729012122211000300d080c601d40300e1706e4401c1480188003540c0c28640e0b60300b00d4090103a0141000c440007910300810b0010009980705031405410100c0e45c0c4110b40003d000414226444510001c1c0065600c0703012a50581c0181626401082da41c91415902c0c541031500410032021421940003040c1003581c10305100c1e52001c20b46481d61410f0707459400d090401c2004540501101c44006004110005000041011400717074900c01d15001340070040200e6a04059402c41d100780c00d1030364458009102d03266081c42c00d0000c07541221000d00e00031a01c1d446000000f1002c56891320740e0a030106070a60f007021114056006030a100660303800030048001042d40080d144c0d0030102c4903d04010040345210124220a01383e0740e0494090200c82060500301400305081c054dc0500780b0000c240c000c00c000046 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 391496906 1250 391495656 391495697
    0x30309080301081006051002030f070c15110d0306062c04020a0e01180b030a0203191d0106120b0f092e0c05180405090a0f0c030c05030303010807060c1103030a 70
    0x10582503902c00d21f4544003c0c130082d200e024101e540c01d440100000c09005100f032040e0364070090103042181458000303c0440141140d1020640c1858030b003d12000301403a14081d02c01e0380c0440e141a259881e548450341c1500250034690595902c08110315804605240c65a201421075640261903070214000140009030600d10340b101158440310842c00180122021641580d4100c0000340300943c40b80c541300110503941038114125000d0f54a4580d4011058450041c606031804100c03000f0040d0719201d0b00c0e03800c0026085400a40f40403134410200d0f8030b8604c9610f1140d80302007140c0640303005250003150001420307480034800124104042d007004c050515440313596500c9404c2d040c490b02d44a040140140c01030f1039000c000d8416a500c4001800824003400074010880d40300f0f100314030040c85e80c60070761100f400300d01058550600c00303000031649040020490b4140c0741844014170001d80307480c2d0704441000301e07440100e50708848400014500d48040014206001244d01d4039200401c1c1c03000b04034517 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 391498156 1250 391496906 391496909
    0x8030706060e01180b01120f06050906030a02092418010f09020301061e0e13022a030d3b0606010203090109060e0406030c0305030703020f0703020109050904030309080301081006 78
    0x10284441e4010019403140d0114200d10340e640003030100740000d070500180c030304c04101c03412014800c0c10071040c03a06400c8c00b580040251b0b1404c940a06d00ba0b1144802c2c159165030150000b500318151101251403548440401c6000c20400142d10076811031080c007041421040380000151880700d1b500600074000c0d5040d08001800c401c490850640d8034100c4014a521022214010b010655010b061410ba1080340c80b40c0f045c2d0350240035107500e8103640c2411300c000c0d4406a00c1d045080c40c83c5408450308615210080a0100c40c400110f00341805c1d0206800100080740181070419030594941104190804501c1e0540001c00040000300f145107801a040c00c0006000c01d0454004006000c51030382c00580e0034056940c18039021170924201008140180b01c627030006003410101407000010824004020302125209034280c81620a0254460b507032402140402800728250f0502400142480464564050300904d40840c410000b625145002e90085e0440041a00038489078969050310b400f4000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 391499406 1250 391498156 391498169
    0x412060c02060c030106050a020726060603060705190905190303030c0206010312121104151d090c0307052206020f031804230c07020a0b1303110a0f0803070606 70
    0xc0180303040800f414461105014100500c84040380c030a40b914400c01038203000e4030018904410003102d004d80750144c81e813041d00da40740c3c034442c49001803500c3c1004a4074a004210b00e0715a107042c180302c0130250003220390350201402040b00c030180000300d81e034840099100c0e5800350070002c11280d0035030a00500341c98600e8142e2041d0340c0580f00402c000713001c1440d80c0d031a41c6100d14111107042c0004006801618803050466025540480c021618182c1380d6020740761207a0340d80714005200b2100415080d081c098100580d031140005000547d1440441c0003540e204103e8908549814070a0072145074250041c0c240038050030040e0024040c142e01049118078401d1020700030b40c113064104100c41c0724202582d001902032601c40151a22030b940d030b03c8401011403442c541440d5185401c1550320701c0c0d03400c440380c240c1c0701c0c119143d00012500e0107031003220051184000d02048142c21510b640c0700685000722880d4000d1160040082c0882c103200c0440c014200480c0690390310101800e100f420f03140700da017004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 391500656 1250 391499406 391499413
    0x306021323011b080d02210112030503040f2103291011070303050307090501030225170703200c090106111e16140303090f040906020412060c02 63
    0x2000c0e090700021250304000742481c0003120344003554084100f01031083d074000c1c240c650120750421141c1c9150050700d0100c10b4854440c69000840309640c4c4d03280000c2c41500c0a0310300c50f62000022910801c0110b50090054419a0f0441555913403d910103a88a030345d4600d03c629096100c05259150052000484402121049040d50600483d40920340d2940c02440f860740f034030145e80518001c0c4181101c41d003941d41507a00b402e6480c203025040d0340c01215441e00003003003500003091a6000307100ba900e0b09442114001380b56072203c02c1b01c0ca8040341c00102951281c000b00e40b00c2e04600301840c001c00b1203a1003503441040e815089812110710304600641428544c210030182e00154461300d000c0c5044900900d4042441c0c2d681c0b050043c203151403a002e240b00c2c40c0b5580820704040800144210200000c4100c0010690f03a945a00010301c0390145a10b030b054008000c0800350340f8120188245250004100288411680d5184000c0307921a1307011b45180e414602030301e414842c461041b051301c8000c0f40040d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 391501906 1250 391500656 391500689
    0x60403110f1e04151d0a0b1c0308150a0605040e06090609040206071416031101080c0301090207020109080a030804020111010b0303030703020705150c0d0e16090b0111060103060213 79
    0x4284000b4841e410280201e40d0340d0051208408505010f01c001c1c001541c4140300c4041080017902ca0030b1040b41c42064590410b030001c0101e080012403454184c0c410603403e60399040c1a9030881e1461070181c0f52401c5d010b640c0e500b00c942d994811aa040041989488a40d5903915005030711411a1008181612525101d020402c29848060b415588076130704960b6140c4c0c4c4c8907585003d18042403c011b411803e48030304c00e0302884034541a448003040e28081e20b11a0b085001c6240111440c11044540c512030200070b200400811442e500a4a011441410f1900700c05449011152078888100020350009032001e0502095580041e101190b4420f0300000b4044501c16802003941ca201c003400060405500040350400d01a050051242c50803040021a445041c91084040c00d0382000b096084a10300e041118250280c0014110107410345101e10850036520340f0080c0d8006110540c2a18180310f440c2100c00200d46043c001b403800381d44030724401070b02c0304a20f41e85070b03141c00c4241d048075040c510107815 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 391503156 1250 391501906 391501939
    0x90b03030f0909070c0602071104050a09020a031b030611130501090602061612021206010f0306080c09070306170a050d0305070819060f03050a02100c080403150b060403110f 76
    0x40b0303010384070140d492400580b14070100b02c826080002010300340510124944040000c00b40c0e403410751980c119018095038507422008000c4914604c40290302c07201003141000001c913030391040360a0032510f21088030f140d43d4030307103c00707007034502100f00d44110794000038541c14040044101c41c1d018041c28a0280300007400d006000e551040c000d07208501102ea4400c12004481c1704401c2086034201011096443e454000d034940b03c00070090300d000b400714620100c005e400511a102d000c2c2140c1c0413400070843c0340c1500050110000307018051030101522035102007203000494034600400841800180180d0403103003084c2d414054540b60a00815003403906100b11168000d10f51908204480e240b4900302104c120312900a001650040c070800003001c0000060010114107044464000c2c1c681c4d4400c45d18080c0c040f124402c610300020100312080c08103001003000600f445031031150f1042c0000340725400000103819904641d00407034103000c010008044a041008180703004a2003941c2d81e5804c21801078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 391504406 1250 391503156 391503187
    0x4031b060906051606020a021c1d0120160f0f0f091d0f030d0501080303010317130504540807080403080927132a090b0303 54
    0x482d00c010802c0201e00c0d04c084250292800420590000045640f0b0079150006500d0307080b0008012a000d031a040b04c5010701e8014104500101e1410180504075407110f001035590800c64000861035441c03001071003032141030802005244402c4a280007a61500d4040f0407404248141c00c035080c0810505010041c081d041e41800c401d0307803131010000c00c5280c8660304415600e0055045100c8510824550040140f00400104844010303040144296130322340d429039581b4807080c88020201404101d0100b2110040000b41444880076003407620b5051f0707244005410389800003c014080c801d00301c00040c0d02d03680c0440c148031841d01100c03010040da40b80c0c02800d0081c4640340c03550340a002c83c1c00764101000003001c00c4403280e0358050382854075a91213041032a070f07a8005208440c01403515140342400e0310044074001c20101030a0b005010141c0d1840e080c0600c0c050041021513510b80300c4003040c0240c42400c140b8104000c0a070482c011180c3ca08000e030030542c0e80c0c154045020790400c0001704140003220 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 391505656 1250 391504406 391504409
    0x2010804140c040f021309060b0a0e060f03040308270a0b0613020c010501080f0303041218051e010909090b130c0819031d06122a04031b0609 62
    0x211400d00c41d160000c030060401e100300003802d601c54500603144280075110f034058880050200c200c000d145880f484a80111001c07400f803503803050014811001030314480d00205210703d10252509060002c14802c082081d04150380c00c40100d03012004011503800c183d48409041d49000c62060002c1c42071070100790315100d0003a0041c2000e403103100007816a80b540794010340c021145000c11541e4a80d050301c007070f009080a0040c080c0c6409070f8200a4490240081964000c136084a42484100c070114000c1c1d4040c00d4102c1a41f0b018030f04040c00245542d50384140022640640614884800714035000500008542d040700800a14003035207070002c14401801c070390b40700010481e0415030998501b4a820319400c5603000030040d2040b01d64803401d0040e4041d03840c800510989600c0074842d0214007400301d4540d1200850b4104800307200206480e809611072503080b00140c001405e0141c80071040602020341066804140200050104200300881505c00c1025078040351030703103086040640c020942d1845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 391506906 1250 391505656 391505663
    0x408010608010b04050c1c0b030304031b0503070602030f09010309020904050109030e0406080a0311070806161e0e040c0c0803100305060a0203060d02130605131a030d0f2313080601060c02010804 85
    0x403020840b0451b010b6840a08c1103000281203940752030703803803820700ca0130b03040c003d4010a0010040d1002070302d4103000400b401550350980145042244001c00d055140d000040c00c1c5040503294400c3c0009030700d42e4841c00d800342d800f600020804102030700340039024042a031b165038001d901e446010450b050020654401465040c945503400d400000c02d038600d000303c650041d07079080c028541401281207420074000902611902da0b0a110003490003900038003c0141d0003c804148940d844288916041c0c1c02141080c08506003400040c10a440c2d00c1c0180d00110ba00c559006803050043c01071200c20050541d00080c0d64105500d58946070703004c03030f27548140c02400a0113900b4401c40640c1314441500014050000500001c3c02c0e10b8140c21220040d101c1550544d90b90401c49080a006040c04204140c601030261103800c40000c04c1c0001301c5103503031105040780c07481300c1e040b41d0120850305480050603900c002020450b4010f050007065805d050040c5e10008c03d0010350589000182d8214141c4d580c0941c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 391508156 1250 391506906 391506937
    0xc02030718090b0703050123030604080d0207050d080907080f0c041e050712050601081b0f040906090c09080a03091202010309050a0302011401060906120203100b0408010608010b04050c 81
    0x800614000e0b09058400500e09851081040025585907010074101c5503c450f44561007980034420140d030305564840d45415400010004000c105060000c1420594480b00140b420780b95894490038003a5801c01a400034440c1001c0c010020000c11210000c0c105c1c11024040310101c2c0310086503504d11014071f260055444411b03050307c0640e01a5940021140c0358400d101724502070000030241601d0100d408503035450030001c5140c5500c18044184248542d0001d10b400408005420100ea08042004000e04104010118140c0202c0c01180014040703403501050120300c802c400742040000e90418102c0350701105c1a40c000c83da01c6115802211600c88110400004a000403009011000c10250040c4920400c00b81015815404100c140390080d02020659803182422a03001d0018400c04c40041da804010103800700403503008603000400000c03250408c0c6c1d82c541084249421a81c81114540d5484108010400d020f005100f1480d40031602000b0302c1c80c0c40100e014040c011300001524402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 391509406 1250 391508156 391508189
    0x60a0b18030115030308100b0c061b22091d07060c031403150301060803180111011b0f0e06040b04180f06151211030708040503070204050a1a010c020307 67
    0x22400c1d0f02c14611007802040b2280d2640d207a040103482440f0594400c01210386082e00041e0400701d00041d140480706003006440f40791500c1e4040c1c513150b1441040503022500402c44500f10480c45405006084c840c01c42100400c0c1c64104801d048840c04c1c402e200458241700c4003019484000b003062411703034a09051207440c3c801142400c850490b01140e010480140000070700c5650540390000c0f48586404030000d1101d1034840750519100d000307030b40c0702d01e80401480c00f0b0700c0b00303070740c02115201d1119600900002d41c00340c00a05484000755803140c00e00c08a114400859520b40c2d205220900404054411a1415140c14000c1c201c600c100c0c450001d00e9045c1180079850300c03082d90010400780c20107480c144511500e40c0c16a440702d4600c4804a004104901c0700b6942d94038250042207801d1005e000d0490841c0d58000d0709540801d40200102d0345800100300c030400594561003528020382460703500203449451044208414034001050b107042c0140502c40400595001580c00180c5041c048202c0088 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 391510656 1250 391509406 391509409
    0x10807270f06080c040e0730030806030d08070f050a03140411041512081c0c020303010f0506131a040302030318010806010908060703180501090614060a0b18 69
    0x249500e444912081c102154007009410320b03080101a1940d010a0b0b40355100d21604000413150294018103498012071010440c540f01000b4003031100d96126420b01280701c00c2d5024048a00b00450210082203111043c8241030504000040c0d42c00d03c5420240e03214149100d0181c20700b600c0800c440100800001c0400f60380e132181d00b2551080f12404804241420b051500d140d842a960080f1801a490f090024290b4010944910100c40e1102100300c0303c02400e841c1c000c0b0742d0b0301200e00421504030f081340040c0715000511941240121030743c051600da50600d224020500c0099100781d100380d10501c500412a55101c010310103c2e803108040b068031442c403c6a2003058080d952000e9850302001c1680a00c40002c2c141c1002040800d0344c4505550b5605170041d55800300b1070041c40390580c01030300043c103001c0c0039a100300102e80000d2600c06100040b941c500d0300703543c4d400c2c5084801c4c580b110000d91031407040c214100c1e0040d0044031032610050600c02c1f01c1185008142180b110318807031740180d0909 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 391511906 1250 391510656 391510709
    0xc05030a03020705040c0e09060f030102040b0a030203040b0a0603031706190f0311030f03070318030f1103010605090601020c190f06080f090312070e01090509090d080f010807 77
    0x40001806603044a091420040c3d21201c01d8807443c0c0c000c07402e10321032400c41440f4498880c07500c84010a056216140d050501249041d104180760b019982040046803243c11b040c0603101d5a0f4040d50096030f2032529240100c401c0901801071840c00d420200180000303504454080380014030030f0b80e0031325140c1c0d0700d60019400e280c2c02440303084048400003000c0b44062070403520310f0aa078050140080025110024103075980c0c031498021049800503c1000d0000744551007522003e03207030b000307141c12254a03915240ca1940c0e8000088510a0180c2c0005415081c03c0c004c50000303140071240e082a61074407100107922000940c070001d100710411b004011a2411009055014199100c00385103403d440d124047e0440d00c0903100c07450f084201b140090720b0401d0001c125003020806402248550311459003e0316019406c0b2a000c0c148080d0103400709550b00d0704505644188091401010110350000d406006450068000c0a9084042005001c120000a540c1081300c00c403002d001030307400207000040c03074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 391513156 1250 391511906 391511909
    0x10503130c0605070b0f09030f0c33060d020603011401020118080a1409010906031a040c020c0f09060f0609130203070c03080a02070309180213030b0a0501080f0c0d0c 73
    0x2581d8004001162590340103000d012100d1080e0842d02e11900d906000c1450442d044511154590003005103408161040380600b120350701801c201c03281e0b918554694615141b00310398061021100513000361119114880c03441c1c00c100162005901c20083d83c000c1482c9100500811100300e05110030b4010b1a4801d42c0300013103443c40710100300101c548500c0c00e00c100e50311a00f0b040f00000d601280c1225042e04100071115000d505844886080d840c1100c00d402030003149001d010148a402083d000a44450107410b032a84565406442800482c06c20400450348100c41e10740900101c808103c0f1a807030385e54090902801c02c6460548038070b203000003d007505d0710b04084041ca0500203c1030000254204420b94417180c0b203600d404006545882c3d61300300324019801c01a0004003040340c104031442c0e030300040c1049480200b02c09803a00700e020070000b003541c14652003214250003c0007041801501440b41d01e0240005001030300342c0800c2519115034412004071202c4c490202e5035001c50400c03488100450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 391514406 1250 391513156 391513163
    0xc111b01020c1c0204150e040605040c172d07050613050a3515090c0301020414090106030b28210302010506040b031e151906080c090601050313 63
    0x4000d40c5162000030f50340c606943c4200e010342d00b420040f5903200400446e4000b0f403494103442d600c442e07940d078507400301800010b442030341e001a00340301c08100b0400c0c03180c15140c500d036180014000465a174400200c07000866887c4140d406110182d442c2c0c035400411840122078045074502e8031981d48003098696600b00b0b03401a540720214100005034400b1003841d18091111004c009410341d000d2104c0070a80741c3c400c1c2601002900301c1300040050280036180b082e04041d41c401120018003525010030708980c080e412098904c4104030800c41a460444131590150840340703000e00203052810081210001c1d0320800103042250391481642003490200c03400004c00070780500d000c0000d2450030310205000c090074240e005500b04000607500e030500740607100140350048d000300248040400c03280031101c00c9585900c1e0741c0c0281514500d002030b1080705180074212840702010b404d4280c0560004450301640507030a140c01031174407030301345645110919511420071f080003983e0796203141c01d00181d035103041d0008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 391515656 1250 391514406 391514419
    0xf061201060b120405010e03160524040b0403021f02070b0603210f1908040209100f060f12020304060501170f0606040207030c05061f050a050d020409080c07180c111b01020c 76
    0x5000d0b0722a420346270741040c1d0040c81a202c46280c242c45503501c517045107000c2000101c0071000b08000550645006500c0b5003e40b06031054141c0441c0c0000c0f5000f4240c0c996121140c01290703c5c424000f24595850704032004034001d0090300c040528070040100000c009440c201c101061290889503003104031045450600c41c440d503008403040340a0450701e000d840581c080d0300e8660004003031142403040c41040da401100030b606c901d440c08070100c405642e0111918100b04140c407480d01d22103110f00145000360b1050001003681e6050051000307084181031140d61195000c5c0317250450011012074010382000b800c1d0703000b5075141d4040c1820b80c0e00b82e0081d9402002c41c4070717010400c071800034600034682e100041130f86027a101c0f590314003c2040a0085000d000e601000d42e052501c014038180e40002d08880c4101200c42c14019036881d03c2e0308255055201c0b4400d04140d11034050700d81c41a100d00d1040c0540350405041071100c0600850f59040c3d6000740010880c0170000e05605a0b00810075500c0c0d100008040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 391516906 1250 391515656 391515667
    0x3020405183706060201020c07091a120f210d090807152f160f0b1003050115060e1210060f05100215040303091a0f061201060b120405010e03 62
    0xc1c225812804001c2c0141030701d01000850036610600840320421900401400103608015507940202021a2108649180c01c4003980107902c0e150340744240022180042e2845542001e400d03402d10f80d00004811080755150a0040b11b000b10380e040e550b6401d440d80d000a284e80a610303000d20385100b05140a04481a851514500300742c0f940c10440f225008081c0061200b6160a540350f043e0320300d4060b003940000c042c440409482c4119440749400c9008817560a404143c584501c01400d50a99100c1800303103c55500780148034007409086001c800e4003407442000ba20708040240175004003e05188540100e01008006507003c101e0541d114181c010200b00b06540c4201c10b09a009061040c6400b0320100da00c01c0d1100360001c06c800130702d000c03020a06442e503521640c08900601c1d20180484442010500400c08510714800c0746200e041c40540144203414040100000b400f080d4640780c0d050b81c10320000780402c18221060301c9070040030608042103512070340740081c050140b0180305402032102240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 391518156 1250 391516906 391516981
    0x30f0304120f050324041503030210050c180f01030b03100c090f03030221040317030f1303050a0c0804080613120302190c0602070209010f080d0302040518 68
    0x160500c1205240d21144162880b01c00b090710940400c0301c11001c09005d91004800202810601d2a01000d009000042c40491f40c0360032501c01c00c1c150400e5005902c1012620740e4000184265a000b00c1e202100d85e0501100f45a918002072041d41c1c2980204020000ca00081c0d01941040340546401410340d0182d1b480020918010003500021a0010311041000900c088868003c4000e482d0103a000e01b80c10806020701c0010366501084050780d0240070480080492103881e09800c05822503850070303983e0f061190508110000207890b24031110400c140c03141c0065080030440b08040b045060a034120006170800081a0160794081c10341390080d9001c000c81000a176070307804401d0b44220103100340c0c45a0010103c0403801001c06100c03086030348031031001039030b4080c03603da10889124040c050302d00201b96003c00c0c1d03030740e0081c0d1000002001c00441805507800070311440c95010084d250450a045c54400007403078000303440750031101c813245031000714035540d0009620403400d6a2078260952078400250 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 391519406 1250 391518156 391518173
    0x14010b09010207351603050102091224070905041805010507020d090501050904020f16030e060906030c0309070b040b07020a05150d0510080124061704110102030f0304 73
    0x141980103000b05080480d02954545600d04507810307403058030030403800300841c0600014200c545903103548551729075000604c548441c0c0c0405548150000740c1c48180c0c8400b81300d0280c60348401e4869a804c80200304544520034007011008000003100c0c40070b1a00d440905868100403908440d07002401e055105402c0300b01d0121034551148240d0003044a41d58075a022600e03107050706c13001130003e0103100b01000300d5846070010740761440008100500e880e80440307100785a40c1c0444000c0050441c104110400c0c5600702a19070000d01c4181d4100349001c0c0d0342000125103200041441e6070b0a034000c00400c000c100700304a600060300c5440c840954440c0c4480b034806058202c0503080348034544204002c01c01d400d00c0c4039100480030710f41701c0c040d0800c4506021880603140040030b0030305030054100c00044002d03090003066541f40c018083c070301480e084521800003c00c019046101440328140840e03100241020b5160390064004041e08000421000100d06520580394000041c00000c01131006002411 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 391520656 1250 391519406 391519417
    0x204150c05060105010806060301030f020301020f030a091401060f090905010f0c0512011409040605041b410d060e030315131e09020a0b040e0405060708090c040c020114010b 76
    0x11401c03034000b0384e40d0718011610240300302d5010380c0120050004000062124080840880c8028005400d110180201614682049a019000d103482b0004503050280c02d000700c4030305421841c028000c403070400390804400c640520682c0314181da00c0c0150001c0c44420f62052031400c203050410300c02111842320052103030b0048400e100e801c2001000005401b024580d4200024201516039a60341d6200d0700c0d00001448000c2080d03884800d200300704002070696007580c40141008180b810b5004213248941c4c2199204501046000441452401c010604101c914101c940c001c50302ca100d07040961824102030000394000b0310044c800131040c4000030031003100040781400c3c20b48040b21092100b911300010750b00c40c2400c2410244d8800c1c54050402c107540c01201d61103001809074202c10b40d441c0005d142300c1d407180d44030b100303202d54140c140400c01c5801e0244070340203141d43c40c010045e4180741d0b500c8c68071011070401c95845035039a0b110040310301d03000790083c1d8441c0c03401c1c0740303807010543e90350f465281070354404c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 391521906 1250 391520656 391520663
    0x302190309050613050a0f0302010806040b04150609090f060f1403160902030a2f090a0b03011502071a032d180706051204020409020d05120a1b081c0204150c 69
    0x4041c010407809091f02190003102d070140c5d01d0301102e481c0c200902000381043d603402074015407030380d0000380c1095406541d540100b0345c903580c009101d840d21201d1002c9400c04614103440e581803440c00c215140900c1400c505907203009080c5014220030000092404110386091500115982c6000071928080d60144d845810298014006240c0001d400325545601d1191341c420072240241400c4000c02c41d10240990810107032003175204c140c50344624140c980007644100ca80540b04d0401060540e41072000344020710410701c100425698254041c4064080106130441a820741c1002c4500400c1030503644024056081c01844039040400100008015040440d9000c0c4a1148005003161284d0101c5030800c401403026030644d1074079400c1001400800000381c0e80002e1035550400440c0040c055044450042c20060f99038506904014002c9001148920303d4074214148070b0001c2074014040742c01c01c0da1090020304200010340d0040009000381c0d00b0031f680d6001c0d10050140416004200c0100b0a0300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 391523156 1250 391521906 391521919
    0x230102091905030613031d03010e1f0f18080706150e090f0303090d1103220311150711151308060c070201090303080a0908130e0f04030219030905061305 67
    0x68503442094200403201700200021421110a40c50a81c00d1002c0d6917410001400881c83c3e0b0640d5182d689010314000c0a01c82c2840344000c5411040c000d42704a95400c100c088091141440c20300c40c40c1800210000d0103404e40760005411801c000c03a0b6400840003212850000302001e840702e002109100c41203c0d0b444146c030030109032a98820f80041543d22485140c4010507817498000c0c000c4412140c0600f840d45544401e0102c119040c2c80220a100a440404101c154261540c1003003a0b8000e6003c07040c07402602030700403195403900c08408841243ea0481000c8034241210808074110030904003401942c030002060b004184000d007100002200e0a2070f00300d400e65211040e011409101d003850081c0800d000040400009000d040440d03030140d00c45d100020401c00d5034494855550200502e41d036080c15070807090040000c0c0c2c02c110ba402901311881650145800e95001c3d54070b00003900342c48072403290908043d08151042c03404030040c0c10042d10554540d0401900d42c5108005402900d20070f00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 391524406 1250 391523156 391523161
    0xe031603170f01061101020c010e01020c100905060109110d0509100b0405090a0b0414030f12010617040b06030f0f060601030501080604030f03050601270618032301020919050306 78
    0x1000000041d01601c0b0181c042100399103441e005a441015859059a980d5020302404022910038490b000000e26031000240c1d890700d18403121740c100207518012000f02c5d850070b01183c0c040b90001448a05441035800002050412900941810b0107420101d03000c003801d020410001100c04281d451000d40302000c18888084410201b1042d01c42c1107440a41c980d02029821010560303040c0d0268000d8007a4039800c00e032040f44840d46d81103520a00c80240310b00070004035050f221802e064981e0041c143c501d0820740c0c0c410740c0c040c4d113545c100d805440070f03203840111000718403e07079410b0150740d480000070012104050001e2251644580d01115403c0c0402d1070800005080340e000f09a540c07050703501d590f6100c2e20041164043c0e00400b0094800b5041101805544c40000c03d20703210b03649001c50308016207540c1890000c00030b206110028100000c404a40410000034124800442c0a400e05419019100c00040480d60090049880155104d181c41c4000319a038440c02102c9801c0c0d40081e400d0315002d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 391525656 1250 391524406 391524437
    0x150d1505030c0105180a03050601060e09100501020a02040c0905191502010c140315060a020f06090d0c060f020708161203020a2705090702030a02010506031203190e031603 75
    0x329070042c50300303001c500c0403c83d4000f1000310708800e100308000100114009922a1074040ca01102600180c01107035044142c81018a026000c065204620b00c004440c000d0515000030346a0340320010090040b6111280c690445004400348000f43c0005042c10501307142401d035001d4030607442d214107007902c018590a0b800c600d10600038808950016103550582034030b412101c040355440104001030040c0c428040341c1040d07a0314001400041280d034010b2006091402a4905000c005047c182d03135640889000e07221207130811501001c558210000290329002050640060301c0703448070080460350002952100600740c40c9090503800d00401103664170741c02d4580164200e214000102011640c644009403203002511750025100c01904440e82c001e590303079004104e5004090354828050780003c1090100b1a509104081d4448800c078000d05911017075003c05036140c400500010215846500e041e11212840d400c600581048402282c0d55410100740398102045030007030850004070848103a4504 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 391526906 1250 391525656 391525663
    0x70903060f110a080a140403200601050a050d1b0b04030c0e06090118200a1407120f0216080d030c05090a05060c011812080108030a0e040506150d150503 67
    0x1c80b81c80307150a0f45003054250341a80d80ca1001080c2000240c0ca460030722020380c6036421850f0046210b511036404071120010007100b00c03070150441c800f09070f001400405c129500d400e2410308541042e282c081e01c998007030401c1d10082c00c84c1c0c6100e40220640110000b40c40003840010000c0324017807035400298a072501080f422480c0b061300c4541d8010b11100050244810442c603000d41d1501c2c000001074400101c0701c5240d541c3c1081580160030380d10105108100c103400040044203485000440c0b1318041641c0d540d030440c070083c08419400c1200c0d4482d5406058002c0000450320a4031008030000c040da00c003040c07951440301d014140c001038104100200424051401d8540e007210081005864500f42424410760b5082680d00b41055904c504040c865884201f602c107050038094180304d000314119800243c14540d041c0e101221a40c0101303c005a4103620826148600000701c40100349500d50000141d40d01e1445120403a00f0307140003900c880001d0050340500810745680b1125225140e4946c101501c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 391528156 1250 391526906 391526921
    0x1170304051e030106080d020a0632010e090c011b03020a021507060c0507020f0f0103020d11120919030e0d120320040b1608070f031d040c0906050903010e0105070903060f 75
    0x560700442750b640000d0001d4025070f010018a00d41e9032403000c0b54600c7d000071048000c04080000c40080010701c11000348080140d88294104010218400450002042c11030a000001410400e600d04803007094402c0c401d003600140c0040083c042040800e030b602a566002c40e03021100b6600d4440900e44641c0a4410f544603503400600c04501c00305110184104200c0c01c2e0300c0c1d20b040580c2082081c05a081c60720030b2600400c0c0154003581c07120343c088000c140000c0302820b244a1f591103020403040c0c83c0d500340c20141c0c1c42945450a0440c03400d40c400827455200106100400d0700341c001c0d280e0500b81d03505600410980840041980707500c005560309690912450003a1241a6010002c590354050365440702480c2c684100d03001f9152038095259401c03012500d0108800003030101074400705030709600b411070b00040c20403181040005412240500303402014841c2005125022603441603640d000c0d4410010000c0400003440280382280c4010400d07042400102e84180c5442c0a05e100031403e88a00035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 391529406 1250 391528156 391528183
    0x807031715090403032301120309140d080f09030109062406020723041109090a150e090a020d0b090d080c09040203040f050f01090c0b0a0801170304051e03010608 71
    0x41e05610f5070744040700501030328031780c0c8043d58003014a14401451901c00f03103402072690650820307030078055150003001c072401c43d84020314003405040c10345800e43d1003070018007451742d00c03207c0300b0345d2004004010003d40c042d00041a0380b6500c0c0c44060f0091140d6a04800b24140030711444218058001e184d0890050b1a03019001c01a8401c42050003051001c1d00c00c01042c0901d80b04e42d1f403412030403030001410b0b141505005118104045920b0845003040c8a800781c004092080600c5210584191840814103e01c03804910320b04100100e4074501c000d100d00c98413140c0141400607a1041824800300c04141960306e4007480c03081c40c00c050721140c4115540c0d40030f0440a11514504008001000060b410141081c0d480340c0070100c41c400060700030001007405440c060000300b298001801c20243c2040c2a500c5200050003c0011014107580b18a07030505441081903024056180ca02455295006d20341015412007518022400c1184140100c6401c10310101c0082c40001d407591100c1e5210142252203d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 391530656 1250 391529406 391529419
    0xa08010e0c031e0601031503210203030c0f070201120207110a0b1602040b150301150206100b0d05040311030403081c0204121e06050a020d0c02030307050d05040206070807031715 78
    0x80828000c1602d019801c104e0524022400d559080040036804040340d000311070101c180c80200c04106030902c08072000715858005142140b4110340c6500f41446140408811000c001501d01c045a00840c0020700030424250119101d8101c2d00c0d000d4520100c101c04580b180501302c0d03002444031091001c80d040140e060783d075000070306141c3e03092001900c1106c441a0b4003452040400e10851000405180242010090801d8401c075914000c2d05100c00580030b402c80310441a001d10020f0110f0044901000c0724178400617031540c1c6e50404031450742c0d0704132249010f408001400020b005c03000d0080c189000541d1050b0b041d5005406690040b44074620941d10514548404640820920780000c001402c402c00d80104030384071a44e80200302e034011624520500d030f0100346000450721920030707008000b40350f00085255043c8042c0180c0603004541044203825110700014085446100a640e0680d82c406480344d15403009181c080d00046219017111f002000e47d000140c07c10118805c46c181010018051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 391531906 1250 391530656 391530691
    0xb0a0f29041a0402131d040c0602070b030408030a110408070501030b120d0c0f060606030e0d030504030912020301060503030f03041505010f0b0309031303030e01031109031e0703080a08010e0c03 85
    0x42c080030f0340240c080300341704081c1c0708030000c0d031011601820305040c01c50350190a5503242c03524200361558010380040086610102c8240440c6070b085080307940058205100315120342d2103140c114094074100c44400300001c80880d0000724403c00040e50700548009890a010440c0084180182050082600c1100340d00001a1032541c1c1d014401d003034486400350324100760122441e1180c4003502d14962100000070b555108172a00300605000001d502e00191034103000d06d05041d10300a000410a01030304000048002d000c00031554258011801030002400740c0f621040d0741401080c0c66041290305541c208400c801c041c14010040c4a001d045e959601c101c0000d0034200300c03124100d600000c19003135051004102000d004000f004104008511035566450300041c80d4000500707540024603d5070030040c05008501d0559004103a01e0005600c0c4605e00c00da040c6401c0030341e440c0140716403000c0c4c0a11000900c0741483c56200c81054142c0d01700c150107e200da00c8841045c0400d1000300d03902d008204081c0d10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 391533156 1250 391531906 391531909
    0x207080708160f050a02040f09020d0201030b060c010614030d0906081506070204050a0e010b010306050a0308130b1902120403050607080901270203070602070f030b0a0f29041a 77
    0x2a001d96482d100c01e203540c212681d5100042e06150f43ca050f50a41e0212030303490110314082c02502e00429607403009108aa04aa010030b060381100740d0020b0600d61200c0b1410520f40720741040e111040c07003001c000d01142d41da44003a400c1003038000e0710031400784c001c0c07001800156000b010320354104e940710765078203e260750386c04075151a03070b030326120300e190312000c20003543e4050b03941c60217185e01030358951500041013155240030a0840d40a104194181810580c0c00c00c13259a500c44000201c80d00b00803016916031101c4082c201040c0241c1014180240101e2084801030096a9a4003408001e408442403900ba4407545400b6000310701c80108503138441e00004090a20425900d504000c1071000400d4050410815000030f001c620660800344454074880010b61034100914401800b2a001800c0e005042c00b1507113814064600000d0b2042c0094000f00e00c0660303eaa112150700140020f00704601060104003024003400c0e9030401c498000d020040038028074191054084050640840e140513051550 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 391534406 1250 391533156 391533173
    0x3090303040603050a1b030510050405090a02040902030a050610060f050f16150c030f05160903080307020a06050414160f1e1503050103051005070f0e032103071202070807 75
    0x6000b0301c5c50365200c1102c4080791100018003000802c241d20301081034501900c016071070042d81e42c005441203081100b0301504080c04160050401d805503804211a607850002c2890300100f90401007092051100f0041c40b03500102d01c400030340b584e59445030020011920111428002c40c1c0014007482e10400c84149170804254584140b184110480031150700e03440b0500713086480c040d4017940401d0b00c1c3c803610103483c510303486060b5211189142014100740080c00040904285000040c1825000408545864000c00c03041010030380c000e03c2408186058a807090007030940b602c000d030349413141d60b03078002c2600e51402c47c0350240c9a11040c08803681d0f150054031640e40b44000a0140340200c1c000d00401c2d4090500156440f41c5040c0e100403805516524090f4a003814145034924054a000c040c012255400f09480075140c80c9807420b25000c1554034000307414980c440311055002e5042800c074502841080002d14031641141d01d45219940001c504113060b031103049001031010100300032000002c1d00c0361 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 391535656 1250 391534406 391534411
    0x3071a070e120304050102010c09031208040305070b160e031c050a05120109051e01080307320105090d0e0307090e0717070806060609060711030c0301110c010e0309030304060305 78
    0x40c07600380744241104000c00c9006504208a110b40c2d00001800d01c0507503024021215104810715103510b44526544420344031817098020704d001c006040780031a09251046050310180c1e070708542020b604d81050080400c10303810107501e0801055042401103403c0c40c010076903003003001e2000f40740009106281c7d0b08550a03440005041c05001d8144000d1510440c2d910703406021b0302c2419800106820700b541000f021905009214014039000350040c01048004026102129031103441d20030340000043c0003d906100c499030345804a4003120511004580c150060383c000c0c0f8092080d40c2d42c403030f4900c8007154241d014811030340d0035601988041012414a0f80b09180c15003900003030f41c25181c3c80f40381d601c0401800c031562120540c01280107000a0005105c0c20390401c030111803030761511880c10b002c0740c15801407003000703880c0342001909540e01d1746052203040d01100340100200229040c0703800130305664000900c800130a610300304140e4101d803000011111404070060080d81800d01d0204120041c0800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 391536906 1250 391535656 391535671
    0x3060609110a140d06170f010c09060c0503250201080a020a0c081612050301060f0801050d060b1f05040e0a0506011e0c0c060f03051003031e0309151d03071a 69
    0x8000302e130341c8000c0304d02c100340140000000c0750202080e4081d101d07103090318190b00c044450745448900d1144603000003810040311001e05182101c48503d050031411402030641d0081512890303944041d1210b000c00c1c200340c4181c403d8a6540403034690760340000481c0030f44200c85020030f0154040d0804100340801608009810748030600d8040410f5503401c2c400d68265008501007440400148119030b0030003541c0b207504c4210324128032250316000c0046e1050700c000f04007814a9a4441e01001d00c0d071903400181c00c8080c03a41d4071001c506110510b00400d198000d200305040940b940010404481d000d000d0340d40a018140d4404032001c0d0110040301a0321102c2e54010107201208005900007070003480e01c00010281c6444543d82d074500107002809076000148010441c5011a406000080d0800d01050b1000180c43c00041c040384103180c20350040685500c0501a40054010f40404850341d0304901c0360980076403a071030011280d151300c2d10380e00c0c00740070700c000e0160b0b1b050102511300b501c501d5941503203e43e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 391538156 1250 391536906 391536947
    0xb13080c070609170102030708150d120906090b120f061207120c0e07140f09030712140303070c0f080909090106081b0612070320030103060609110a 65
    0x36a4082103280c00c250b94414800705800040420401c240074490180111400340294554a400d5074010444a0000c041e118050103884c106642c0c1c5d1076869104140590150700001b4030042010302801440462080c3c0000504065021503e5074400050745c400594040300a030f0982c445800d01380000600500581e082244007444004501041200c18000e0a0214140425103a00e041c00c0308290b0b55600b1145032680c44000303008a582d0300c1590a07000684107022079480341c504d880f04408070b200e4846010703414030841d400403580d1851882d000c1c0149100e500c601601032a840d80740c44d204e001c11145070740412400240c035008600d0314a091a82d0500c00c5a0081c0b50540b21030000d07840001c02c0ea003103056a999000140b00703842d020080c60340801502c42e08044507241c0600020a40d1240480403011032100b5408124400c0c020340209005103011144040d20101c200544040c0350824071040e500b4030704040d00041c900003280310b100c0750116012402840d040325048160f07034009041542030164007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 391539406 1250 391538156 391538167
    0x3160303090f060c030605040203090c090402042004050a090510060f0e04060e1806130201180e0405150c0304120c050c0a080102071a0609160c061e0f06030b1308 71
    0x58903860b9080106125030320008802c1e03008803008044030000d4000c0e60180c0d2040080c00241d1000242500b06030b5070450344010b0582d1540301040181c03c07100c2400e520651019840005510f9040117041620410b40311403003180e80d503102080a6410035240341100c0e45079543d0501c1080d10880007031480c1d1000e0708104204952003808142211102d40c0044050003500702804400c1c0202100d100000d851040100068141181225100049800000c2c10301ca1802c1440c140d02c030244041c08020315805488200c0da1600e0b08296441c0d126407251645082d0207000040e655040c01002c0c0c85c001d03074008411582d00258500152101c1c4000074003520a8800d500000c001503035001e07030103c090500840096100e4000d460412100b203504409004588081010401191294010340d64400d40c0d41c5021401c041500c0c0c8240c40c200b0742c2c0e48018024a007425040402c204c000c20903040d0300f80c0c40c1348080000d04540301d2450111082c6000042801103000040345e401511030540c0040c0a00400c8000d04d0803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 391540656 1250 391539406 391539413
    0x106032a0f1203030c0c0308150d0b0a0509060a06080601030605150a0605130f05130c0c0b07020c0906010c05071a0c0a050f010c090e0703110d0212060a080a03020316030309 76
    0x9041c00d500210341212510007103020198580100340010300f06080000d40c0d03e500c2e40c3d0207022008000c06440c640f5514400f4000b4a550341490620b005070080d240c20868142641c544004d40f2040f10000d80c0b600c244804103004045900c60801110340c010080c0c03c050b400c60359448040c01e40544152030002c25803100354010381d00c808402000b40b0803502c0e815901c0340d201404042041c01540f103110030b6010360f11704000c40d031241d46800d0800d1311540d80004003c0c041b0b09082e0703110402103e024050003181310411440e40c2d0002400320007101c044418901c9507440384011600e1046d42140200311380c004010400403814503154405484040c00485401d02d60700d040040d1901e448000140d030242e000d0700d0310031020042031003080c400c2c0c21186000742d40241015003021180002405036400c15585014052013110000c055034503594030b00a080d542d0380084910303610300001c15038296100f000100000160450002041046254590007540c280030141010f0114050321040560605885440b1031000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 391541906 1250 391540656 391540679
    0xb0403140f07150e041a0a080c090a200301170c0411070b090c0d03020115151b02030102040f0b0306090106050c0c01080c0c0102040308030f0106090509010e040303111b0f0106032a 79
    0x640d96030301960100d1b003a404100400411103a101445540200400422030b4075500b00d0303240d10118000022a1001c0000b1403203d140041d8121000308460110002c143c00b20844050306d0021480400c44080035001c0f01003001301d0f8500403002440d0203040000301c00180f8504417143d0b008030f0203002ea903045075014002c1003505005020450040c0d5542104981c0d030b22030b002c400d070040c200e41c05514188208804000e802002e08503070140c51154941028006c650302501220094919090744c1d6120587d1880c000d80c442d0429104c8611030030044001081c503a00c1441074442c20b080c00c0c0000c1c500ca50b54500155260300000c0c010b460400c0081203c206039010900080004500c01c01e8a00c1e41d82ca40402c0c09007413000c06800020400010800c1001659262036146064030026404e04410340c5680c41c094006101c40b4003164440c010101d401502c20901100f914204108002900c465202c140001c50803100c2e9400014000da4140004d02100c4000402030700d84580301c1c940b0308820700c0d2a003102106 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 391543156 1250 391541906 391541921
    0xe060d0c0312170906090a080c0c0409060905010513020105040510030608030a020616140415050c0d020309040609051312021e1b0108090c0103110f040b0403140f07150e04 75
    0x4203140a00b110b0f80f451a2000b640e03403001c0628003070f04042c01c0008615403211110500038000f10070204000303840600c18880200312400042041080545501d4458050041304100786c03169440c240010303085100d0085200d5166038140d40300f9140908010070040668450305400040696548000c907250404000401010a0a4004151516101c5210701d4904809002501003200c220495510340050b0000d960544096250b60824244100c408807040d02403000717031003144e04c521140740c240e040e001310043c60b801c1429a801c0c0252522540c44c0b0f4281d82042c0c8011a403004140580740124201103c010100341640c0b05070360200003034411514420085503016069500032401104288490714207041d1103100a00b03162509240c1100c130151101c14005095040c19102c21205420815207021076070300301c3e02101020b40b100d40307646c1e028025400502040b0b444c1d0500058007004003000060100440310044000e040301405d03d00068070700c6140c030244a040c040c401170a041e46035130b180540c18 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 391544406 1250 391543156 391543193
    0x90902160b0f06091b1204170a03060306181527060606031d030d052e050306181c1403070201050603281b0905011206060509010e060d0c03 61
    0xa0611000f0042c1d1311130060f00c43c3c0c03070120780c0708100301d8200c04810a0f5003003000600f01c000401d5440381000c126820360040c40e00003054001555148281d0164007010640380104810010351200c02c0502a0001442c9c40281c5403000102c4a404841c901e13800501c80c2e02030103441c0c1201403140141c14101e405d20100c0c22152552591003d12105a241c407403030b18a030040c3d410301170011104006464481c0308125240451a803910001400d8101d101e07111200300550711805240074180301039400d0800480d000d010b02ca0b009800c04210001d0117507143e12251455100074001e000d6500000c0c04201c00003680090500c203002c4000c082403503094014510540c410380020500740340100c1011300b01001e0301c02c203c011000840401a42c1100c0d41856510319600100d000b0a182141c0f0003000341c020306074801304480781084e0004c50005500451220024441d882c00d0280300c0c0c40d8000c0080080f024003c040320039105800049142c9803244040c440c1d5401202c2d074415942c1c880c1c81d01c2e400c0010f6282241d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 391545656 1250 391544406 391544431
    0x102030c180a0e040b040203150901020a1803230c040c05071112030301180e06070903020a06050c0c0f040902042c0703023105040b0402010f020d090902160b 69
    0x200e584080640420341c00440850300c42da00d0500b000307403025040c0340250011380740444040005045403407c100c611507031406509411a6460310f20101070103948128554400110020000b03400c4034a000c0b001800d0725070214003064085158601203001200028010380c3c203200e0700c03400c5600740d00c507031042440300045070303039019174032026802c058200301ea0b1265031314052a101050031180800220940e4151100e1914149140c0700a182403c00342201c921041040c0c01a036042c0171011382c00a01200c02c0b64429101800384980c2e443c0162400e00a05000e800543c000c860300c0402441c04a0a80d900074000410004510f04076070041804c84900715a048001c0007600c0842d6074040c411312842c600d0b0b0004000a21b6010300f150701007590011004a5000700c07003074440307800002c1e02071229054442c041d20360040000e8585410115054101507030168086035007a11000207480c030100384d070f140310f030001e80b1503008441c54804250002d40c012140e04840b806000c800d0800102035410090083d251400e00307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 391546762 1106 391545656 391545667
    0x90b010c061409060702060403170402010c08030f180f0a0803060f13060302041a1c05030c010e03070218010302090c030c090a15030c081902070c080102030c 69
    0x41c01c90341418069020b142c0e040800610070002e09044603c15121460b0a03038845038256400740014012110b03480d100020303c1d102640007407041c505196080910780b12040c1d203410682d80460045154414004d045d6405131260840b0103081e00540509802d2580382d50391601d181a00030700c000c10100004001b0b54890241d4210104094048103518884040340801000a400120b02c524500010881d04810f81138404180c1c0e070018040308010240340c0d544030001d4412850803070305840100300c0100c0d9a1000e0041011445203040210b0300d50100344100100084030b964101c0403000401300400159450000441d007005000302529980d4072803c03070500ca030703204010f02e95130404540c1d0720000c0c00b408403950300c1511812954040006d01d45140c800c885074001514860345044108500010048542d402001e615200f030ba44803540a070f640b00c94900703a0300101c40351008200e01081 = true := by decide +kernel

theorem cover : BRFrame.Cov 391366906 391546762 := by
  have h0 := BRFrame.cov_init 391366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 391366906 ≤ n) (h2 : n < 391546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
