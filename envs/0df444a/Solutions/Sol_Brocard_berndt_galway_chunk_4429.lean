-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4429
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:35:14.864113+00:00
-- url     : https://prove2.me/submissions/ff03b6e4-1f45-4cdc-bf15-f6a3729bc54e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 796402877 ≤ n < 796582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 796404127 1250 796402877 796402889
    0x15041202010e03010f0e1e0606040b01020c0907030b0f0a1401080907120b040b0708090318060706110c0d0203090102030d09020316030c080606062a21040302090109090804 75
    0x510501030005a611401502e00b0603050361800d600700700240e5580d884480b00e550001e0036074600c00c0702c1110350300c11341c20712100d40005600004007088c0e052030503a01250014106006542c81d20031404005001d151044034480b0100c1e807181091380c2c152034006c05a103540c0d8011640c20400300c0c144003008918108204456046c0110780010601006041003448000c0c1212a103444080b60f051601c000e0108013942c0032a40b031402c500c041443c41780107401091081d106c078001913003020b681c40d181620403203c000c24660001010405803010600c20b0007101c2c1d01d050720100c03465035400307108040c600e003542951032070303046410a1044402c113a070302000721440001601d201050030344c02c40c00000d0030310300c04040046280c0c00d084000802c101050041c0004c4034209410b840841e034890341031011074821083c0d0031070310302c000c429036683d0b8440300806c10030052061811141040c116581c19100811103101d00d2440d5440803070100211f1424040320350141078045414810420145e880070302d02c1c02140502c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 796405377 1250 796404127 796404149
    0x1f05101203030b130615110303090616030603150618090206160218090a02010909230a1401141512010317250605070c023703060f0b1504 60
    0x450a01d40c3c54900c4032441c013000b1402085180d81da00301c0c19120410a0000001081280d03003d420f040c1c0300401034030b1041a40c9400740040d942c480800f1a16180403814000070300d03950710004400b00d040242c10082844004100043ca00e080003544184210b02900d090141403c003403203d80180c03140001c0c0c4070714007203010b40d01550b401c0301d1000441703084000092017a541111002c01403c40400201c01c1c407414001c4e01e43d004003940f10f0003141c044d2400425680e2500c1c1103420840b01510408181170340c00b807a4a1400940f0b110103c903035040c03500c000c2c2d10240d451425030441d80c1c403c2c6000400103001202c844480da241c8a883c1002c040903501c148405400b0b610a0100080d10600d200120b0718803920218010b00a050101010380c6504104e41040d80c51518204c0000d502900901000c520309400070440c40c80c46121450404d80c820352b0210443d0102403680104020200b14074042d806540300319804500d200000c00004d007114101000a40718072040007440c0714050700803040303900b03840d146404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 796406627 1250 796405377 796405391
    0x7050705040c20010501052b02060a05070506040c05041523030f120d0f090206030f1005120a060b060a09090b010903020a030f0212010b0a05211f0510120303 69
    0x42560500c08810302510b4290342102c215680d440f040d0700050603034004446c00402d10000860310038100c0035015501c000ca0301458600d20152414a010b0302000801e0b1400a150401a43d034041c00d0a070103079421540140c8000003440549864020781c031400b4104500403000c3c0740781905506a40800c16244000781c01c0d030401180298500340000d440d8265540c0807954550036402c426251b6501003000c03440785a142041c1c41e05075000078002d03a403e8680082646007540c46106a4400503032025003200920010148001013540342c0300b0b154030420b403403240940600c04040c240102581d400032500c610601c801c12040795110382026801060714502031000560102c40001a00c100c02590000b03584001629000820012034510106001d4803c2c0c1e9480c0e02118007498443c02c0e150103c1c1c100d5400303069003d050140e81403001e8541283c0702555084141e54904c0d050142c140304040c144542c84002800c40c800855840e400303525080103e035055803d2701d602c1c081082c210549800343c024101521910 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 796407877 1250 796406627 796406651
    0x4060b1f110a080a05030702070605130605090f040c02100501051c080a03150b07031d06160c03080a091706092805150105100905060403062307020c090c0705070504 72
    0x1103803000840e888015913948012a0030042c019800807500840144120355001c58045c5c441c0c0c054400c005030451280300005d0601100b582c250704a030713040350703003145a402aa8850b540c407401008820207140d00a03058100608055009845058204901940410000050501049180c000ca0719000408113441d40c0a000c0224080e00707103100d03142c11280034014049010f010000c000c1aa5078440c0d20340600b064240701c04c0ea200c82c1004001c8603800320091008010031081f000e04c401010b032080440500c00c641b00c0d92110030542154809800244007904140b025002081c220f200001e2030a0042080e40342c40c0022540d158107204068500ca412818a4260340c010074088840f40c0740e0150603110502120851090240802d120f124441e51410301c0e403022890007100f0300c8040d110003812182c80c040c00c41d2203030000b40c900f6603802d11000024007012131201c0800c084d0790b0301070b81965025148a2801c901004401203025002c0309080d0700801c880000034800280040440d130f0142e90100f0510f00c512 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 796409127 1250 796407877 796407883
    0x311070f05030a0807030509060c180a0e04020a29091f03050718080a0f0c170703060606110d2016050909010b030304030f0206040f080604060b1f11 65
    0x410024803105100810108215011002d80020182a90785882e1030765542005c0341500e5040d50164810303005980031440b0070f4007203c02820021590b00240300b501c5020317004603403c01c1e16684400c03070a5112005000861904408541c001c0100d02180d00315207902c2813201030840242545400e00041c000707004500354898000021011181c40700e407214074200d50401402403d4103c401d1400160494800c200c152941d58455040e2070200005100000903551440d0b1168130211042c0c590400c2d41000080d02c5030f010340010b030381c801104042e050359032840ca003040076945560454818480d030750071340a02401c0000b85c0d480011940b460a0303511508405401560001541c0b03050740c032401400170303041580c1c180c006002c04441081d91180c1c41c40c7e4800d16580d080700c0c211003a542c0d140c0c004000c104040b40780c0c0101e000714240000c1c4028030381655007510702c4203900d0710350052500e600710701d081000340000392180d00524003003580c03500c0d40c1045512a00102100e9144580c050080c2c1b0400c02d820740d40d00b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 796410377 1250 796409127 796409137
    0xd2627090a05060406180b030601080d12050a0f021603020c030705010503060913060c0309020a0f0e0c030907050303040314160b0901050c280c0603140f0411090412090b0304050c010311 81
    0x10703158031b00342d51404048002400c1403c96880c001c0c0703e49000051488030014203141e16039003560300c00c40303205104294032018040241400401d01d494030606080b80d40c00b84010700010b491050346402d0300c05d01d890041d061035450b1400030320039003058008001c0e99800c48110b85c0c1c0100b0442d17803409150b8402002d0b003a4685c45c031902801140c075025002c1e000300c0c0c05038840c2030146d0003294550707200383d61000020f80c107807450300038904500f0454002c80c2c44040c3d1840a1a04070041c10144d070449501c0b2004a40f8540090344240e80c007041e0317007000209662003406080b8620081c500d00103005420f0031000c0c42c55214203087c05041000002d0703041010002880f6038485101224440e06403a00b68075241d010312050aa401e84a800500000090071030080c418500510150100c2da1925624005280358030b00700180b0644948811007180c2003c0c0d90740500061095105d00002c40c505482ca810042c081c0307140d50040e421f295005c10611011840014550403855000d2178080703084c0c0c1050504101030301078 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 796411627 1250 796410377 796410389
    0x50a0c060e0a0e0f3c010503120906071e05030a050a0813030e060309071e0609050303070f1214070b1f060512130215070b1e060d2627090a05060406 65
    0x3561802d052400c0d400645d18100e61044003160700e24401d4001c4400b1501ca81d03090240d000004110300317400502c92100c0b1040000c0c0f000001c908200d20b58071010b06642c40102100000303203002402c07000541c0c00c16500d40d005007414a6088210a1a0750701030140c0c1400c0040c24402c400200000e521000100b000f00c01801550802c0003401c5680720108082c408680124404941400f801085c541000001d6501c5923030002040400508a0380703610142e41200310105041002815840c069428444010040f8501c5441d241d1983d01d0001d80480ca060455082c1c025158140c0340104038035580001620340900c441280c813a900d40312078205107e11094004025044100440420b643c4400900076051040c01120352416a83d5950b240502c0900c0980410500840000214040f0b0401404107004d00740306051107024203030104030151101803195071000d0300c0303400015480d04560240340c40580101196440c0d210504200d070005041c480b0082540b42d4441c0c0d10400541240e407075800410080403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 796412877 1250 796411627 796411711
    0x1050d0b1f0906170a170a020c04020c06040302160605120a150305060406060906050607030e030f060a09210806010c05010207020d0309170a1707050a0c060e0a0e0f 72
    0x903a8040410141c1414401d10400080b448221302031031001080b01c00c4c2c0701d81e101d00180c2c825200214140340c250841d1000a045100310041034440d030315030b0710040800d50304045c020a2245024174000f0b260000c0b1000e502c0418070042c0d0200034181c0c0000030340c0c1e8002207594003d0015070b11640d86800810150741646560440d05a0000038882c000c201ca900550044005102e556140e4074000e05488079840f440350800710802030702000c030344903143e00121003000070309030340da1101d400420601d0030030261080ea1955545203210400c21070340d06a41c0215100c166080203040e80c00c0800542061801056a810700034400409801c03c85d00b0750440e070089900030f140d940c1d0114242070040680500e4040c130251210302c1c90768014128000100000295802510464100c20641c4d1581d0300350400a800ca03002d00c6018521000078001c1e05c0394034041c0071260754070720307246d83d040d0708001d424003165204041034a100c0d4207020f1558010005243d002481980301103078014a003203007403080042c50400c10103400b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 796414127 1250 796412877 796412879
    0x627080910021f1d010b03070b03090a0c03051b040902280f09020306011d0d02040b0a030602031e0f0f0f06120d0e010906030204080a020d06060803070303020307030c0801050d0b1f 79
    0x100940d03002050a0320140d001107442c816102c04c80d800c0340c103520001c0790305500c01c810070013012403c20010346d8443c0c824000d0310542e4400742e545800316003090304100d07001c0c2c200c1c81d5076650350301240444402086003100c09215661003900419000e4003e115042404011140e4038804032902d402c806000b44100c001403001070350f4804a0200940043e41d000b030000c7c0c90031000f554400079107000c0050f03202d0000c2c00707011001190350030040241721180440b6042422260000b01003411171001d181f18482d4075100b080d02c400036590b60090208002e181301c000c84403100a0100014100352000d44c400d0300601c80703030f44948550000441c0304550700b070000d101c0d1040c9110031130502d030701048070070940c0c5084c0c0f030b9203201603100c0310250241c1c0541d000b61482a408020f420001d4a42064213000305402900001131542c0c8a9001d94115442003c060300401d0300001445105c1d81c0c11300c81c1080403d160303e000710703655043c90006806c00c3d2001402038517020700003000c103900c2108411100790001c45500070803a61 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 796415377 1250 796414127 796414183
    0x12030f070804030314210619061110092001031b180504021e07020f030105041a060d0c060c02010e0301051801060b0a0c0305070c03060603062708091002 67
    0x82d81c0315000850008001685002100507500240c500228050990101000031000c50072071900004080c503521a000984d81c4c038a040b0780d02c1d100c0300902010ba8441240d01d82048041d480d021034000000e60007032518407201301091071800f400e010b50f00e080d1504080540b0000040300600741d420f403016007501c0364000d4121035035004045642012031a4880e6000643d8450030001240145090203442c0c0241ea202a1198180c400c01003455030701c01454041411035aa011a0071104d08940c200c070601500c003009002101d030030b00300c10781c000350480d0003d42d0020607503104801c10b61944207490520454010b91021a805010404008400030b4000c020070700d001c0c503c4400a031000c4103080b11039403070500081840c2c40c80038101c0c0c1b0140c0346c1351031300015080d0554040740c46602407007041d6003003e031000340480000c52501540c1c0007580946404240140c07861020588c4d04000443e0484041f4450325920000360702000f0307200c038454222824208e00c3d020800a90801441c0c400342c0041002e41100c80306a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 796416627 1250 796415377 796415393
    0x41e1d130c180f05040305031f0905010806060307090915020d09051b100207050d14100510030c1203090303050c10050c03040515071715041d0d090b0912030f07 70
    0x42e03032207451824040041c01191820031503000b03880140004008200154940b10300c10401d050500280c40078402d1943d4448c0080b0456a00382c101d1100c035040b00c001d100c4a894200540000b810b504c000402030704265940303004068994084402d4210380108120000e0055544043c190300d401900340e03280141410050351900030500d20ba1803040c1c0f04d642d030004081d840010300b00c06594000c1d2090081c84603d484448100482180c088201e20800019480c000c945000c6c00340940f15888400b401c4a00b03601e4141001d6041d504030a110904c004036581c042a40450300342c0440340c150405554032210000840e0070420740e0003008440c1c0d410001485401c404136401144503501500940b0100c04081c1c0240280f000b040c0e89001c00900c1c6200c1c00c281c446404a216600052402c02c01c0b11928903000c08507007921154200c0c3c03040080c40a011426201050100d51044a60303031928581c11403c0500114440c01244800c60090b41e801c000c1000da0a4200100c0e4401a980d15009813240210719103001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 796417877 1250 796416627 796416659
    0xf050109020108100e1519081f0e21040b0a0c06050903092202071a070908010b1c081608030108070b0306060a03230705041e1d130c 58
    0x80043e0140700000c2c060060121a00d0075200760314a40c42045e01c0c0c069900011071b0302001007035840303c42680b9000c2d1400e400e4480b00b0040c10440041c042c00b8040c0d5620b54868154400d0749802641094240c0040b200c01081803030083d44000d41e009080400d03410726041d28011600301c1d0702c0b400800a0030740e00c1560440309111000d881f442c81440307155684001c15449000d0000d41c25008030b5140000e445800030170245550008118400504007076007074540f404200b50bc0102004888480c409110703410303030301ca0709001c040c02462009010000101d070100d0700818050b041c01c0071f90100d88200c442080946d1003242c038a010340f41d141030803028090410000a920038898041140b10709107001a603080001c1c00c0d680706401c014200c90604d03030b0312102540075011440e0400603080403544048400d010840a05001d0040b07503075020388490519110550043e50505003000419a14004114900c19035480c2109583c81002d6500349446005000a020110250090800c0840100800c4044491020315 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 796419127 1250 796417877 796417879
    0x618080c0f0708010212040f080d050a1a0307210c17010507110f0c01050c0102130b09332206030f06060810151716090519090b0a030f05010902 63
    0x2d52a83ea4980030b00e4200d101c2c4480081d40b03440c08100041c041101680e03000300b070304e004042062424036a6a001d40c107c44041700d1000d230f8165540441e040310f08010f0128000a6420350080c030499080000010021110407030548280c12421100020061080f4800c00282505076004d103002d10540980c81c080d1100303c80034800120042c0458030040d01c0014136584484001000d807403415001001140c19034480d02c034911740c80d9000c0000300050340203005040e000b07080490201e921903040d02c01700803072500400342c440c0355910380e00340a0080c81707010181d401e02c2071014415140c0d280c1c14045071001005000c10001da04401c1741100080040d05500041c7c0390398074070355040100716210201038410407015030f21040341d913643c102e083c0001d00512040c0d013001340d82030504d04114171070a801c0345118682101c2c00121100084e842101044e01b20400344082c08007102e1490110100c4900241081124454007102c00e455506441940e15984404009541c02030202200c1030000d00742076019201c04070040f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 796420377 1250 796419127 796419133
    0x207020a08010e151b09180a0506010e06040b0316031b0504150906020309012a0f0c081903030c140f070b0a20070503130f0801050105010512040618080c0f 68
    0x9029a0100b103c0d60b00e100301c2c5d044190100c00e10b002d215600094200b910b0243e0404c510190170100c189090f01d016200f2a401c1001003aa49001e070001002c03440395100303a902400d002d200504c5801030381d1083c5c9501103982890344e440f06591a0088020b48007e05000c0d00c20b02c079154401c11455407000080050341d90300b0a14840b4906142000c84203a25603118820042c2c00078408a840ca43c80f0716101401107001d01001074031403241031086030390340c0005070085a4a502c0f0400d04810000015039900040868202078500ca49041d00c184140600082004040664076031480c44514002c00c260035002c8140384049440342c100c54084509684040810746650742d5840004400500a00400e04010b0703003d413111644800d0110081e0361a00a07100c2222580018082404115401843c000040840aa081da140341c504084142102c2042c0c018a0400100b0402e40495a41002096070010703800500040d0041400703082c42600b08540c0f10040070303910001080803901c000000c803080c880c201d517001d0f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 796421627 1250 796420377 796420393
    0xb1002061503031207051c181e030818030c010920030a02150706061a121e0c030a1b0305151212090307090903020304090605040e070b09040207020a08010e 68
    0x8140c3d80c1e00590440d19040351a402c00112101d00c038201910000310041c1d60400080001c1a40c50240e842d882d03c40c200001415018a090211060500191083d400445130120360b045d1001404003070010b003400e2140d00c0000458103035000c100704131411840500700030004000c142c60466566501890a2520742000c0385009009241c045251001d0550013088100c826811034280c900320b8105d08400e4403c5a40c1d41c00c0000c10034501080032003110700b40491190782d4000c0c16440708640348044c101c0c45e800164120080040e00f07040085030381003112000100d840703a403094030390805042e1000c0c01004142228444000c0300d42c058004502901d4000200301111358100180082884845a840600d600c8031000c1c0000d090302400902501300d020b000d0302d03d50703a1a059980f0a403100071000303c005900021302008144814801c44002e40302c1243c003441100c03584020075550301d48034000c40c02461000034482c0c2c056680c0e0303070403617076200d40c080c101005e83ea81c0c51803814000c191600e801401e600907412 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 796422877 1250 796421627 796421629
    0x13030b0105040b130c020f0118260307031104050613140f0105030c0d06030218070f0f0c03082d160e0102070608060a090518070819030c060b10020615 66
    0x14400c002d0102510044c8014007aa02880c05400420000300c1503029507222003855074000c3c064090010144607201ea40da502070f01e004d500554084100456400c0703c1000c20303031500d20039411640c00c07841c64074021881c0d10b489452054540300e141c1c01a1ba110307400255941282844800c3c9504440c5180005a03190203494144006000c0740380106d40010800c100246000c4180d03070240c00c0d81d0600306130009413103407658042100714404102c1d0b0506190742404008850358445030421800504d85401d1440401240010309846800d200003810f00044c1c1c0c0010710399201c440c850008030a0ba014048185411030b07861070041e114280d40e89515124940c40d82c21400380101082511003030180e008142c0d181c43e050b0300b02c85018000d031000e0380c00b24a40c180050114140c1c003445001c3e00c8212807260300d682d90210200e140c03080130307407180e40d89402c10f075010050102c2080704100c64035018205040042040d20b0700c403009103502e031f103070300e6018801c0c81d814a0701c1c0e40d0002c0c185114860015040081140e104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 796424127 1250 796422877 796422881
    0x2d040510020a09170313180c091a0307020f030f0d110f07021e0d0803070e0a030b07110f0d170c0403260c01060915090608061302011413030b010504 65
    0xc040d075000c1218000104000a824204c0310351240c80701c416a401c1000249440005d201c066120f11540362420b9540c00110400d0b10440c03140003468207200d06e6151809c008001c071090115201c52042d01701000040030f0701e0081c00862a00c039072205c2529500d00150040c0405c54201000040c990f500d40186c40e4440c00d00c5408580410840c6a16036040002d80d034200f00c60010f84081c0305280440c207411050884d00c500d1120b20b03040e8450305803a501d0786411440144003018426010b4442c00c1d01e00c0c002c1020a400310141c0c0d40105413490700384100808400711a245c8082007070340c2e11052003118103003400310350711404107500da8406904106442e102c690282c1c0e03240c09640400740108406c15108224424a094901c10b0241c184c0556030030038015000c1c8a003110280c1d80640d0180da2100d54981c1d071400e041410501030a040d15040042505044146540b040010008980315402000800c296070049010300c01074116804010390b01c2c280700c440114011002c2c4404c40f0701c0e800100010901e0316082c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 796425377 1250 796424127 796424137
    0xb0f100f0306140a030f02150301060801090f140609070309020d05071509080c0904022d12010e101113030606060f110c130e0a0b0402180601090e2d04051002 69
    0x10401821507066854400d85251018800c92303214030708004155030460100f02850081c801074840c2000d80d031402c501401a10302c40b80c07100b82800c0c43c1c000450a124000b60f01950070403010740301c805250703030ba12500390700074521251302950111660002000700840020074609442c0190300ca81c0d0502c400b10000e580d22600390041c6252504040c035428614209000001c1e40f10b03000802e074010306280c45996031a100202e60030381240040300800b506041c14a049480406c0040000811403200041c00840c0c90f10680000c03079032a59211040403140c0d62820054030703183c2e45190b2070802c3d21541c901d4210b0041003144191400b04030802c81a4801e5409003046008501d107160151410303180034810407050304185800d0380c0301c8556aa4000b110f07100d0411880d000c4920882380f18000b4142401003100845071030103050101c41d0300c2010003c071660f1000d028401c40c0d41c104094102d82c2c44481d280c59254002000d02a0a054516800080301c154110103e016034018000e40b040885012040e2003070b0700c00c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 796426627 1250 796425377 796425379
    0xd0f0f0e070b0a0513080f070509100302090a09170415080103020a2106060807180615050a03090b130b060d031d03010213090b130218040b0f100f030614 67
    0x30007141044560640c00c01016603082c0d51400601d44100c000c1404d08006454110502c694010a440788116030104100000703081d040312038400034a0100400c17500c102550100030702809607000883c110418640000701c40942c015410305080c800c0d00440c00707885e0094030544451098491026140780d028a686034107817074000e41038407036a83c10700800301c02c6035a0380506141c1d10509000d00d0004182203208030000f405845000d0204545441008041d5188681108a1042ca40f403010003500030190912880c0d410300c0d091054a5070903100080d801099420006003820070180c00300501c0d00c4441035201c1c0650311821328100142c40d2032050117003074100c18070004d0101e030105003400d0310a6240d0f6a80070b030648000b0000b51030685003102200d55203080e548911741403a12071182c1019440c1a001c40040d0040c03130f181c2141022500c032410803841c0a20004c09000d6079840084c44207903140c03281c10300007402d0054000e81c2010b4142000400212680700000d002919061000c904034200c90700c43d00c0340c03000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 796427877 1250 796426627 796426633
    0x7110303061c02090709090f0e1b031905030d14040308220c0b0d0c110a080304210228020a0e090304030c140a060509010f030504050709020d0f0f0e 65
    0x20307605050158201d0390701e8244a810008140d0a401a560650100e100d050981e440c0d0b1090b900c0c0503503800a40b12020301c403202084c1004d9940b101c020000442c070750040216986041c5c002101400b1a040000c100040c50000441c4845082404400070013006c0e048000c4404004407106444030401e02141540c000300040c41d40d0000c218001c4407605032400801d0140c0c00d940c0300c00c40382d9603110f01c80217180d48954001800070460f0f04a0600d10710514510012170309000054280049495444d40c00751000148012004800b040c00c2c080b070f0300c180d500d8103161506043e6906442240c00b135034030358108018004401002210b07008142c09441140c14a55015041c2030380300e0305103580401c005400411100d020300c0280000004100d8258070f000040100d001c087c0ba4203849a0144220118030360000e40a020082040b0195643d04c500e0300c0718500307920b00d00010952910b180c40c5040c1042e55122001c4a800418001d40c004101d41c001d01c4404450102000b070012106924801d81d0070390b011038000d6070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 796429127 1250 796427877 796427881
    0x80a2315010905090613050405120a030603020906220f09060f0905102007020310020403030804030e09160507020d060609060e0a0507020c011115101e050a150212040e090607110303 79
    0x41c185070000c6130041d204002b911100001103c0700308041c0c009555101c00241c0710b000803c25410710a2400c3d40010080c1c500501490603c6031001075641c0b40304440107401d5403030401407083c5016520141078182d10030000e111403901c0203810b101410002c14195803a000e4486500080031051180d0b2010110050340c03418001c2c0d42d041c0c0c07009aa00720120a9805000d4038081d109101d20520061010b1403180c0c031810040d05180c18024045607440340c45070b0085001c002071000702d082c0c602207032410f00d802c0d19025565803500d10100d05080b07408100281454204580070a0846036030b0824010b40303400e00d000002a58551080c0429108180c2e03051001d1b81201440e44480d520641035540340e82680400c441203480d41c92040c4412520441d952a410400b181050114a01c41000c0c21501003031410107514041c104000a6000806403048245244000d550810f000d40203024140c03046448482507501c40e5035407a40610040e40854916025009240000f03061a000300d8803607000004060041d4116 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 796430377 1250 796429127 796429159
    0xa0b030f0c041505060c030307110c0609150d110a02010c050405090f040c2c0606070b060f03010e030c01020711062b090b09010c0801050103090201080a23150109050906 74
    0x10640000803c0d41000c02800124064aa0400818641e031075000210f54900e410b80c2e0041a00d0221000c140a0750484000b90441c0e03610002660700c030880444895401150382c54201ca8607101d0100e041148a007402c80d0050300c443c4840280080e0070041d0002d006c0042c40d24000c4078203101c0c40c0500340d0b110a42c04007040c0da00100050341940144141d606403100c45d110034480e00303441d80410403410b00f8000b41c14420305104c04d008101e03400002c241c3e04242450310b580d9800c4108280184824054180024031000554094000c41600644402625507941a80300580d010354010300098403980c81144806074203003460401c5580007035580d8880c14515410248080f03160107003442e404051921244a6004076440c0140e06004840400002504030140c0c0342c00342c4245016804141454074106169015076007094a1a0340045030f20720001d407481c800301d085070241d5144043c654541b032440c1c0400c000b10102c0080c4c0c4103d41400d032107544c040760b81e4004000c1c0b800030484855802154003810f48540c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 796431627 1250 796430377 796430381
    0x604140a0608010e1204290d0e10050408193c080705040b0c0a1401020a11010b030a020108090a0c120606091e1a030d0c020a080a050c21030a080a0b030f0c04 69
    0x2034502c003c3d01c047d0f010414264803241a000072110b01d038420f665103c01c92401c041007000c140050a01071060116203419200c000d4203015050700703140c1603ca040400303910b03035215442140f00181040000580c0500e04000740d00034030000e030392240006050a91940e54240520405442410749541d41c6141905100c0703000070301e030410000b10703400f84a0645240d0008411100c5212181440000142c03103500002c0020894890b02c1d00b9402183d15050380c1d103c503614041030801c4150f80a0a1000050725815441c500d41244203001a1900c003040701c020030680480340e400c0c081d17540210b509002c00c507110010042120f0138401c4041c02c070304da0076091a101401d25048203c400204008501c110080745020a05001c01d28800c8400218040e442808524080107010701602d100d1008086407800c99a40a42c0e460280030b00078480c81204108421031080307c200011280310b5802a40e40320701005501911100060710000c0b051410806000e4140c14001044004203410000a15406141a0500c40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 796432877 1250 796431627 796431659
    0xe0603280c05041d010c030b060a0c110a0602060f090706090303080702150a06091404080904050c0f07050a12030c140f0c072405040b120604140a0608010e1204 70
    0x11041c1c0c8807400007078036960320720501140c0c00420f1100e500202c0404562800c49035100e540005052900300964011f03182e030001e40b01070b080e16082c2444d41082a0a240040e503a00148080c0c5c0034900d8100070a1007030b0b0114070240100e0306c1543e2081310b074440302c031201e484070464091080000d1b041401040801d00ca00505504140580140e03031034100340d2000d54107441030461b00c1040240d11031204111964040c4034185a9401880c030b10300240c20955910780c808d00c10038003090f00c12071316200401c48020307849086400c01c0000c510481c0e0b440c48030f482e00300e448504118007654042d0816002c02215070080c01750f00050320b03507607451190400b8a5030380d0f4111500700c1129040c005c2c00c140006003110001300604005885204d01450107000c140503580704d141ca00c441c0760b0003000800c1c8402c110000181c0c050314030060602c1c804c00015900d000100e0018041800001c2c25503451409111041c2041e030b001c031040d07400c80d0000707009a844c0d0100903551111080b035030132803d080800c0200134040113198080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 796434127 1250 796432877 796432883
    0x31218130b0301051503071a090f040b09010e072c010f020c0316030c0b0a0504060e030118110315430504090b1f05030912130e060328 59
    0x40c000241e0408a07003102c0c0116108003584600784c0c449011407a0400031840141248100707038110501900741d4250f94090075108900a4014100110051303460781c001000d2040060301103001980e450600303270000c0c0001d44909d8042044204e0300d09c00c2c901e260303207030011180c01c3c0150a402030307000100443d400c0100718031420450084d5094107200c1d075001c0c800b04030580760f810140f55455040d82001c0342d440c0059840004480003c00c0650360044d00101135408035922400c11004071085540802d01400b44500301c1c046d000c0624030010700300080c89040c82d1480100f075040322120b8441102d004400c034029114182c25040d410540684d03003400d4000301102c411a1600e20f40081610058036820303003c00c640c00f001251012074140001c00300c622415105c1281241d05a801d0913040c2196034030380302d109400340200180000010700f515020804500340303d06000c5100e503104059100c090001e0400e00558000807052008108245000100d00c3e0084280025800b0003d4804071800512100d190b021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 796435377 1250 796434127 796434131
    0x1e080a0f06080a17040311133b0c090105060c030c06010e0624030103061a0a0303110708210901090b0a1e0c17090d0219030203121813 59
    0x103981454040c0d440104000c1000f40350207103241c5007040c806004042010024142444200017007200b12484044182096030076802c0e0b08245003842c0701800c41d80504075070b04c81b201190035100c6000c050410485049140c03400202c00b04c1c2c010b0594403210907000b42580862240c00501c00c0e850f1580040196004c3c000c00c8a140c030210ba48201d041c00d800340e005101300c900e828100704150515002c00002104204440705264004500e010401c0c0410b0201030000c039900c1000380400a6015500d82c440840100002003941d82c07072074000c003000032190340b45025000e0305c103001980700c5001a01c04002c4c1e00319070700ea01c0903403580490102107401a4000f01c0c10450702c40c00010700c11030000001c020484042c0e850b4400041056080e0504952401c4d01d18100400c2c90a650041905003280042d118440021240e9480446001442c202440440030798880d40c4d00034124080030070b04d00c400c02240e10a1b001e03a1035051000540c0780c2e41d40212260540c0304000b00e2910105840d1840d03984003000c0040e240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 796436627 1250 796435377 796435391
    0xc0605090105070b011212030e060c090402270906121b01171015031a060a0306180e0d0525030e030d0203030405010b090412051e070506040c0b16110f030f0607030c1e080a 75
    0x13f100e88003158041d81340b0401d5100c00e071400290400100596100300195010b0110b034080d5006643d85e0699101c0b200c8418004443d0251541e01c5440030a80b00301e502c0c5074000e4030381040a0b0910800303d151040c0e00c031003003006140e46240d9020b40500c1c500b10820b229020110b507204002e0060a900084d100c10402d60344150120704c000841003403280912041400090b09008071425916107a0f200c0c01d2030080c448203110000d010203182000b28510015203050f42144906840c0035140c412100c2e00c800d5060050503206048141d0000c0075510950240e40207012010204050244580040c1c45c0503182400c1c034100c62440318000d000416561440040740196070034010710010032900507042c110f500d90840d405100c248001a40e14001511840342d80911308540d40304840d40103c1f0002005204c0d0648040343c1c0e4140e641c240d540d050760f11000d404c0e6600c010040ca0000d0310340004650820200e80341c0001c58203114880e01944a80c580e03480c87d010f00d45440d03800159840000200300d8040240c132600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 796437877 1250 796436627 796436647
    0x106081506271806010302060f07050a0602032e0302010215090708070b0a08061801090f1d2808070b0c1606020309010b09040c0605090105070b011212030e060c090402 73
    0x80440304008189503082a41c0c18180008607030f0940c0c0107030b0403196501c407800510150380d519045585640803108203d03540d06113440e20508001000c040944400c2c0302201f00300062040f140d0019940c050185c4411911189089148414106000107401030b840351404132682c29040741f0590308802c1c2c6000702e40c01c0c6941d4100207031500700c0340e4000008103103010406c6840300740c005d00c059401135012244516000f80844c04050ba00340144034002403d5261158294400b03800c5e4040c0716559040c19541095040404842d0760300c101c0c0c1e00d0241d5094000c04c1c4408560010b090003200c110707a2040c0440d2509a03035480c2c00303e00764409083c9084000d0100b0400055041d10803482046030321400e4051f880b450221107040c00c59200c64801c0d0f01aa84000c00c0000003071303401c0380000c00c0e40c02c5410700720b0b140c011a500403036450299140003071020089a00200d200c3e41602c1c01ca400051080315012050180301c1801c07030035900400101c1c40d07160702450200c0c01016036800900324051005d8001410604052 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 796439127 1250 796437877 796437919
    0x1120206040314030405090a2f12040605040c061b0602250c030c14010507080f0f0d0b0901060e03100c0e0a090609060f050d0b15060c0303180106081506 67
    0x3d80d0540c140e01c0050300b0000c07400c15009040d440850300b00204004101d00f01d12108200780302190107000303c21440075101d0720401c46c003903c404661003103042d24640b62a1500c1d00080c00d00303850039180c4050325031001071180d110f005554418030040012220960380c50b61900040c0d000100c2d03462031440004240c09012804010074112540200201c803100303444c5080030198600960070448c3d00e000841c40307401c000d9811004403241d05a04c0301c02d660392608440c020345064000c00411400d44000090318000c8001e85420249a988048801f0a03080e40da07030100751440b0594401850305504106407201e50040c590f4051200320f552401d0400f040300911000800700d00f103580140c01072582e9020b0500106041d0b00c00d680240c020726030031600c0e0300d0400340007441c03800c4c89800080449001000280380d10f100e6042c211090f4401401c441d844074092003501e03859420440c1c403000b511100c0b19202d49c144505010710400c4640000190042c130071001e19032030811800034060740e00952030804e00c21001c2110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 796440377 1250 796439127 796439153
    0x30727060302040c0c020a0e161d0306010602070e0703020304030e060a0306260f061b0f0904060603020c0d0914040207022b05100908030a050601360b070506011202060403 75
    0xa170f8545d404070a26204200c0b00310032035082000c00e02c2c0500c041020712030f034010000b11a07000c1c1e8108414104c3c1d2540e6800c851104000790f076500740c01200c000182c81500020340d101520f0303072015202129507500da8210100c0c00f0803100500015040c020f510044e042400060903100345514010880c4e036110450f08000c1e49071640007190282110402c02414401440032080c81f510f140b0190885003001200420700041c41c100c01e40700640000740046401803c00100d94220101030300070300c0610340c1c440f0003800a40040c04c1544060188140c1928524420740301071064603000e294000008032a0800c1c44000d4000880417a0400d105000c050b106c1c0505084100920012181003585c84100b454242d0402c0740503403703004401d08006000380014491411f0f241e1081c0030641c009560755600004070340d80301513010000c003025042030b80078440d02d0562162090980d001e0781045141c80c0e0312489944140305095002e003154100b000103221011007040802245400200700b182001d8894440b40200804 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 796441627 1250 796440377 796440401
    0x320a020a0b04030e0a08062e0305070306060f050405041203050a020f0315010f050708160c05060d0b090114030601090f021b060403020d08010e0601080a061d06040b03072706030204 79
    0x4c1e400298402c0c03402215800191000c107014095a04044949017414481000f445460090b288032180e00108040980c00c011a0403408444034140e690810314010201070040a0050f403085102241c0c2e030a05000d4203000b10f071720400070f01820b0515802100100740c00383c1510301c07030381c3c0810046000e061400e004d07500460510080254441c110800541180100000107081c000b007800381c4408a00c41c2c000f542d250b0389002e020340c0e9940c4050b103403620100342503402c02544900c0114800002040700e500080504000ba80d802048cc1d880c0c0400d006071200400ca07280e030552001c40144030b40c0301a1b401001240e41d00420141c1003480e4954040c00c02108a072206842c1c0c1d10800810051560401c201d81c41c26041d42031046455040508410040c00001e01d628140a450000b05124010f16031007000284035030000e400030908050300d851000c60043d10681e00c240c0c24685000b1152501048000403143c003001200d104540c241c100940d0801d0400544207a41d907030b0000080540c030307107010b08110310b54 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 796442877 1250 796441627 796441637
    0x31806150504092006040509040f0b0f010510030e010b06040611010f021303060b0d1b06021c0e0d0f0516030b1302100c05011b0807320a020a0b0403 65
    0x6030001466040d0426948070502c40c90410840b4000b040c1c001c004030058605105000510700410004904039100310760205801c501544100004d122501e5210141e5130301c140c0400400da11183d51b1503105100030700036154002c4220804480c0c0c50b029a0214050004074400440e511120500160054100f5440325000c175a541c030302c6032600c4c00b00380703e01441d210038104d00f181003c202440e00720a44803e80401800d0356a5480002d0481c0d40d06030200c0c06103540804461317080944200720000404031481002c000d441010082c05546100c0881c1c441c540030140c0e00c00030001840003c0200c065401c2c42c007503c03164142c04184011480a2085602d0296414040050355141d4030f051048104010042c100030180300c050417005940340900890400018078110703612040604203940100075008446141d0900c02c820b08200a0f04524214400c034115115180403880280c0c489900300595440010f030040308024110761401144003800c0150624030444100031030f50b80e41d0700407140f01540c0c141d0101d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 796444127 1250 796442877 796442891
    0x9050d0b1b07080405010305092509140609070e0a082b0e01080609071202071202060c040602190611341106031305030706053403050403031806 63
    0x1400e450078606104110700520391412a0710f4840642c14000c03401800d04050b205c10115110f04c81c02c010b40500354060710402d0307515403084114000307081100d1082c1c0c2259801d09000c0c400d049402031b100303485900043e10b071601c1c9a0381e0030001c4070882c1000707040c154004022840414490401c2200e1000c6080c000710102010500f4212444080c42403040d4100b000180c6500d03801e6664041041504408195030000007606e80400030b40701d40480038848040c140c4041030380d00600c9a6013025945d010b52a0b000e490458031401c0440c20340f4410780c05240e000d40d0000d84002c01700130b040714400d10b00038005d240c00202134007041f100300380310380c08501980603c00040720b4074065090f102000d485103000800a09a907203020b5a50300302e0030700141a201e842100c0210008a1140708010700da01084c0d84081600e41e166a41d103030400c01003400342c4080912001d004940d507825001c00c5c0d00c410301c00310f01244134242190240802c44c00341c032004008504042d2154240da8031000000480030b0554421080802c0c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 796445377 1250 796444127 796444141
    0x30c030c121624020c10050c0c06010308280c020a060201050907090216081909120b060d0501060f0b0a080c030f060d060908040f0801050f0114010f09050d0b 69
    0x8445580c50074844000100949420b80d11610302800e49036500c0303001415144460440300d80c600985a00d0401582c0c00000d000780c10b044041002c0c031000407072040c200a2901c441c3c07a04003150007110603a10b0142c1c0100c0052022840000c0a0604080e03880d141c3c04001c0d800180800d02404004400b801242210703014a04502d02103120740064640391000700060b06e044a80d841d40c07140d41e03108000d00990300090310790701e40326001200361806402140450707031418400300590341403182c1c4c1c4000000441c4004003207200c07020200c88030b0215800004640725034590030100160f009000000300d40566031034800140702902c2c0c190b200020501e4641880d110100c08134041e069441c001d2161406000c1007040080000480c1d000a03042802500c41d0880a03c16240990040482c1070010300b410401050019940c03c42078801c900ba0b41c01d60b8002d00040c4c0356921603d850035001e014200c99000360841540745940f040440039070310145450110651699040801d100201283c000d64030509140108062 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 796446627 1250 796445377 796445383
    0x160203010f0504080a111c02030c0601060521180607020303010815040f0f08040f0902040302040b031501050f130612030206010e040308040201030c120c030b0901050118030f0204020c030c030c 84
    0x4195407503105008a1400795200e013550320405c492903042c0484105401d1411038200a100381960500d01c07154494929940042d58a4002400500051103900d001241d1544104103455200020900c0c000c90869034440000041a00510262109208203c2c4e4080032004014613070040c011070300559903075410041c0e024207186411680e480070060540a0000041c080001801101d810030b00302d00406200d0310348565a44141d03400540410b61407040402d803040b0681c010070031a03200311010004401040141904d032806084030212112504004100a04000d8006501258000c059128104c3c8041190041380c0703183e0000152042c03503800780410150104280c41c05004c01061351300140c501594018030040c4001c000904054407010b403003a065000da1081008811582800d006840e940b020007001000f131020f62500c90008240002829401204d161032822081440070500b607003507072100d07540d206410340e00302c1e08503500b0006900090402d1020b444444100005595100e0742c038008946 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 796447877 1250 796446627 796446641
    0x714060c030d05041718151204030801141203181f02011e060b03040f0302070e07020a02011d0a14060d06030b0108060f012303070b042c01060c080c0c040216020301 72
    0xc440000308608514100b4a000c80d000004040719148590a44147c0110302805140030074200019448240020190840c01240c1030355001d4074440c880409090400409142d06582403869400401140c1141c01034003401c604907c1000c0d01000b01c90345089010340e01c101100101e40c0c0141d541d40c001040d101e20003841e40e01c141c500a0414000542003c207141014030007e0801041c4011034140541010b0082c00828002c010074041508e1602e1b100a010f900c5418444d130890005143e0040035010345503959a01c41c0340c0c00054210111581032500303100c015400403204541c0100c00380300a04084030a0301800d005035214901c00480c40d45421442d6142c0304010304003207544000c0744014002003100002da0f66402500302c0b0b20700305448007035000ca800d0500f150008010b08200103400303e24440d0100e15a0407440c1008a00341c81c080c0340c502584901e00d000e024000010300b80c41a02d602180084001d0a01e44102206840e0800f0310b0340000790490340480c1c11150032031609000c05056150a2007810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 796449127 1250 796447877 796447913
    0x306230c22030b06011206030215030a0507230714010c0c14010903080f13020a0308090a120b06011809020a2019140109060e0a0b0601110714060c030d0504 68
    0x3480e4034110f5407103082c5204004d00003410080c2d811aa181c9031440c03134200341c0007580c000c0c0105440700040b52025107140d004499000c00a810500850101442495411385031a412115a907a44a900c2d0b00000f29600400c000d6a80c0784000030140a0311800b0701c2035102142280d1a503000c18010341c94100ca021100300d00403181649404031070400b103034018400a9000ca24440c030b01d0030650351a0840ea4070001240000303908107199201c04010003800c07200038080c036801101d846038400d80e61034100098000b040c41c0100300c900d109001c1209540a090b241d01004001d5500c4290241c81d280a40102e801580034030740081c4025800b482c3c11005245074000c9003180001802000d407602d60400f01084a02e0002002400c071035685603080002035100b002ea01d07074403640501000d030100d081e455559485101c140c800481c90008240342c2d6010716189050551a00c003c0c00a040c0b90a21250312082000035458001e802082045048841130006003440001010000340c01e06082c1404c0303c03182c40c201049 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 796450377 1250 796449127 796449187
    0xa08181903050c03150604090f0503070f0308090304050a091505030f0705090c0a0509010e191d070813060510031a070807110309060903010f06080708060702060705040306230c 77
    0x202e0b0903201c5c3d0034080c90780604262030104040c0707904e141c5011007103811132003d0018000801e40c0302c10070041c00745d100748041c02591001100c0d254140742ca510ba00c01d503c50035510003201c180410806d8115048060390001545c141c000a0351389801103400c00740343c0104e0844540019900340103515141500a8010b06c1010206040c03a080c0700002d00903220f00d001c414180110215505c0d800c2c0c3c0c50240c8440d01c14401002c41e41419513950320308001c03003131030f644127003035041044002074034148913015403480356252a0481c1c600c2d8440352508030003003034081d1071081005501107011002c2200c924800b000b0241d1201c0c441118a02540700424a1001034081d004001da00103080141800010940e0040d4800b01c90807a5a200f050002034010100810b01c1c50b241810400700044011001c1500000c580300801a61582c3d600d0820480e1103403001c0754498041842032000b440840c1196102a2084034030440d04c0703c4039100c90710024408801140d00b0150301400180c0740500d09070b0000714104c2d1759988218 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 796451627 1250 796450377 796450393
    0x1502030306010e06090a0314011a090f0403110109051b01030b04140c0a030612080a0f0f09170a0f12030606020f030a0f051e0403020103110c0a08181903050c03 70
    0x80000390380f043c00343c0c0b09a0b0042002d14459403860075810003564485231150131044c0e40070340749020f003000c502071001c656980c0c043c402b0726042c9010f4541c4100c06058101c0d00603941c50303900741c0300000e898001e002c2544d41c0e0049c06000803070801c281142803080c072440c0c0e041c0c07241e44000103040d030745419000e9010f103081c01c082400d032600d0803001c00d4101200c02d0000d5114601c0c21011002440254040045000c0d6a01d103503090029100080032000c64590712103142c0c0c440c80405440c6445001c031600002414484204420f5030000394400605040b9400e4500f030400c543c80c0c00300031011007403050ba20f207d200003402c2551038262083c01c0007818240054010700381d03031034010341d140c0c007075104203100f8800d2000036240c0aa2040003200d4402d411007413481c102c00c24214400301305400500003240400c1ca4401c112245003000300039545000c2241c801804e0303800099407074110b181c0000c1000042e1346864201903c00e1794a2040100d5805031202c0c1f1008084d256041280c6090b04181141c0e01036000040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 796452877 1250 796451627 796451629
    0x90e01030f0b1e0a05092806050f010b0f1e1b0d1106060d060608060f0a0b1e100e060c0109381504060305030c060106020304060c391502030306 63
    0x1810360b48220310b050001902c0da6004d506d1801c200c0b00942c04000501185009800c0a030102004040180500000c00160713032091140e41041c0402e00504180c0c3c0010b112070301459210500501515a14802188000011000703400154100002503900725010407840c13004480108581300904a1a00d0484104030040103007a0721070701c01030078460040c40480390302400d01000340c00c4440108950401c0344c1c00e516003002030000108040d0346550025041c03103810310b01e0b450a52071061802e0051a00c50f403440035808108088a460a810390702441392410386034500c0e03500c40c2c01800c0c0c1185981c0010506030b045281c40191100400140c890451607645080701c02c404924a103c9070803200e07104070036540c0310301c0500580030240c1d138001a806403c0c158007008102c0040060041240701e00100e030503076602c4401c10380c1c80c0d001c0e03030107400005095a11118085a50940c000c01404181c0c25958200c1d146480c1070403c5103c00c0d01c640c1040b04034410100190100e2003002d088101c0140301550950900c44 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 796454127 1250 796452877 796452931
    0xa0f090f03030c060e03190206070c030e01031a040f09031803030516050309060a110f0a0503030a110903120901141204020108090102271c0819090e01030f0b 69
    0x1010140c2004203c51081003044655071010380c0c8490800116502e03814000c0c801c1c070706501400700c13440050013410042040c1501612024014950603140d111554040c0700046008103400c85d10302d42841d40c41c030160a0180ca031803050413400f00100030301141698403814050186280000c00d25100085130604001096006040c0c0c0e15000981007040d1410f103050800300d00d503000d5891b0b03c0d0f078080c170001080a102030700910443d0080920005130f801525600d101c898440150b1080a8442c0d0000c00001d040702041b6801014010103c000060a01c08050046440c2c1171100c28120035100000030004a00e68026913404210340c001c0a54925081c08442d070086820400f40000341132003c903401085402c102074064071402001002100d03465108a8030081010a1500c4041c2c040e203000d00191120604950450512a401040d19454000c880d10b0205101d11044c41030400c0103070340d0501085107004030744040d0085000348520903200c401800c040514403009800008070b5042c0c0d21031490041001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 796455377 1250 796454127 796454129
    0xb2214090a0602090a08031804271202070810050f01080712170405090a050a061a1b0705060406020304060e18130201030e0a0b0405010f020306030a0f0303060e07050a0f090f 76
    0x100d440035031550301300b6000c01e13010309003034002111074080815800c802e18100c202e511849041140c050103140f100015556047e00380014411811b1600001d0304003152224030002403c07003140c030403a0746103662090307403d04207882d4003020081c0c41d80707032800d010913048403090380c501500011019041c02450050703414001c01503c01e00070018032a03080b09441014030003007614024007001d04940c1480c9046460b0400600c012228031145526003c1d012405e5140b2a03080d0300c03025400010149000808100030303202c004c3d1100000c0701e13845401b0b8046411380300d220103440100000d03001151500e04090010b00302680d014046402103030503014141070b1a140820031504400c0341040720706c04a2280c00124040e0481c020510390038031503900170004200710240c010b882280900001c2100c4589162040203901c41a19199030660040d0f05510105806001046846100e824001600c40d901c144081c29040304a03140008104042600d0b14031903003008178034800b8005490704181280c24000700400701d84a07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 796456627 1250 796455377 796455383
    0x10306080d0f0306181d0607170a060515180f060415030b04060f0504050f13020603070e0301050703050403020f0d0228150b0a090501060f0f030b2214090a 68
    0x1507252003400780c0d4084c0d0b1000001d04140c1406038600e8800701c42290242a02074220300f4100042e403500507611001044990040c41c00c0d07501d0b02040c012015500040c100c01a10b0304480700e0ba11a40020b26549841200c943c1c80000c007001341d1100303040c84890084090691919000b1b0320b185003605081d50f144411981034499024102e61280c82a07c1c0032001803050b04c0c05150030525050340499800c0190b2001400c4440071074090000d580c0300c4410f44200401500c25220400343c0382c2c260001450b140f00590340c404240d280c1501c00409410019003514415075440b03000c42c1d65102400241907041c0444000081d0003001004031904441009545015000f01209100004107400c06001030400c801c1035095080004101c501340048494401003800c409403d01c2002e10b00b00001d0544201d004240c121441c1c1c3d1034400752012140340c00d803005180034a05208140e6076001465240c0d50b82211100c42c100003c09901034240f86002c82811140b01441207029015008108070f082d80000500d07104940d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 796457877 1250 796456627 796456637
    0x901050a080403020a0210120b01030b0a094d0a1218140c010e031f18020d060c110a0b04080a05070b0f04050c061206090c0405041a03010506010306080d 67
    0x2e203c0c20102d0400d4103020009510a4810038016115580150101c1d50008005400c002e480b03083d100550480c2c4800c00c3c1141c204180d21002c0250a4560703000300f80e0318540e0703001c0138000240d513001c01c0844152603403403005660600e00c151400360b044a00910088500c000343ca0703c0c21201c0d140c00380041180319501102c1640b10807503034211074014010b2040540d8026145031001c40524801902c1d05040402035000404034030207402545000281000902d485180d00d0700b5200500300c24001800000c1ca11041840c01298000c005860342d524015407103002d460300007551200001d0040252002d08005801c070b03030040003401c0124600720201ca8106e944204801c2d5120150b003415101402443c0c00604141d4414081085140c8050905480f840c424015111030040d10410046140104e0008a503c1c51425000445508007201c1d42c4e904240da180c445070a19075200c00040548202030211608403035140058440c9080034040c50b1f030040e0007420305006a5013840c41050381c03101030451036000c200b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 796459127 1250 796457877 796457881
    0xb06120a0204173a05220b0a030b04270203160e181627020307261303140415090303080709050604140114210c0901050a08 54
    0x1129035040303800600040546607010b070304600f040c0d9200c135104030048004150341d0841464060320110200403101c1d5242c61082840c485580c2211540c02201100e00c0c070718001803c1010131040503900b84000d212140040307948410b0040c00805690008060074026400d10200b618440c14040d1040f050030401009495541e00c0c50002a203021f0b205100000e13420090350300400e00c0004180d19030b1080c40001e114502060241148980d06c40703d44460260800003243c0074030160f10654844014200900c10345859045008400e9040341c0c001d0322070074003041c82d080184240d880f000319204d070714000c044003d00ca185032242d900109650300c0c40d002801c0000c81840d6071906442c081c1a036003d050110452411402c3d2900043c10500365404207034086841603002440745c620035040300040e03900150009007420b140200d00410301c643c0e80c1b601414403050f104d02d101c0d10325101003e0282c080318400c02600488a01c07003150703450003000c4c2c5004080c0504005584150740c0010071508500e08500c0c00d120b817030f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 796460377 1250 796459127 796459141
    0x1080d050702040603021c20011e11070609060219050622060207050a060539041a0301090c0212030103020904060e03160510140c070615030c090f0b0612 67
    0xc2c08a900007c0d8000c62100e4103031180c000300247d4661261085181000e11720103620070104801c070424104c1c8c00160500100000c4000c11554010341c0440f070f00302468240c00003006242400003613008000001c0403440100002607041090480349403c201c01c074501039020b0340301c1d5601c40500078928070211842006041c030001c0d1560b504e00505070004403c43d220041d40c501b04ea00c03403003200001e480082c24400410740c422030b08400020174a41021401000f4485030309010250402c50403002c1e200d4800707000000c0c480e00211054041d282640c10099540e60612180354221040141c0c548110750015503103460780c00b466812241542e404a0f0019055585c2d07240038806066100b011040b1384c00f01081c201d50500c01721007a4a4003512035415110440c0303852080704c04650594411991940c1000082407008903c0c100409515000d2a400320720a04c040050030b41c40c102e56032040300d04003080030b000c1260344994495041000c07058041800300008060014246008118503d890005400c0200f000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 796461627 1250 796460377 796460381
    0x50604061d060910080618160e03100911030712120c02061b06150303030907051e03070b04031401021905090103060306180b06030105091221012c01080d05070204 71
    0x3c000350040c0b070100764403c00700b4001c1c40e01600760b603414066600308409404c482a008003540c1f1900d20000414294507017034a085070320214400c0419094090716000505002c3e990081800740c2c1c1c06590004c1890704940c041c1032401d800c1c1d602c1a5014407d6400c01c0c0002010a04c104c180007006140c10400c04803d400010201d01c80c0d4442c5a030700031500e11412a0403400400c84900c01e48180e81700d401c55040940a140e102c1c4000c5401804a4105000620151400310690300381e4080c0300300311540740000700c804685000c003180c001140e2040c1c0400c0420801004d98000c41244041030025410105040796800b491003180e25808103006021a801055921a40c0070000860f0170000c03d0003c41c0808176035002008205006a5007821104001007103030a05000300341c09055050300600404203000c10b029880c0d004020301402050780030080541c004a000d0410b07000e40100060b100c004141c40d9444041c5000c1c2c1e200d64034001151100400071041e0114a00c84040424102540d44000c0ca200240c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 796462877 1250 796461627 796461637
    0x1e050405060f07050f03010e0a0e0724120501030b010519030221030c1515011404030f080c0609030318010c0c06150b030a020703030c02031c020a2a0309050604061d06 73
    0x41704102000004407201c028200700d014484040d02002010101d0140c540c4440c10340c052080c000040f01b070303c0d10240d5910f0354140c0c1c0590003880d00101298003c0403490a840302a0701c00d07144400c21a0060243d480c019512111180c00b402e40c4040203891903010428240c16501806101d4207100301c1c2c3d0100f94000d000b01c82441448a0035a90450008260400d0340c04060321900321580d01d4004401040d40609403070703500040c1e440101420945181e9070401e003201650000c44a0280034404482426010400f0030701411518010b181c891401a03101007440040d2604030041c2da0400d130100808a412600100d070068000c0004540392400014034024501940c0c000e01030107000100300105410141d000c0d218081c440e5400340011883c07080700301c1c6e80b80106801001d11040490004846c2e0595074020041c003035281c1040142018241751850003405d03900060b040f0172202040380c0c01059840716000010300400c40b842c1c0d0810781490380003400c40308d1803407007600c40d002c031000040382d0ba43e195020b40e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 796464127 1250 796462877 796462897
    0x51005060f1009150518090402030309090a0c18120210180311130e07090c0212030f0609010e07350702030c070602031806030a060b0d1e050405060f0705 67
    0x40c2c010124164010142081c51060143c0070752554040401140b09200711038000d04608020b031854401c0c00c042050f248030151049900d4401085405055100c0c014602d10944003210006003440d80000044c0c2008441c1c4011007800050b6002407140c2c890780340413904055015076a0021a4480040541d09802645940302d42c00d1100d030000410490103505815260354207840d0b6002003800c054000341601c80743e1450700c1c00ca410040c8240061400c560100303444110505c100c9a021641b44070384d003180da10944500b118001c54100704445800c0c198078545c01410407101410240ca030164005180710417680b00c04410488c881c1d5000b00007410b108180c1c02d80410342c10f44410700d046c4201c000e075a942c003c2c0414a4070f4058000000b40c0c03140048152038454221401401114410008014856000a210100302a51000c000c1203180801018001c141c210000004203a1509010003000c040729142c0240464248003c100c001900842e02d25000444101e04a0380740d191103400f65102e0182440344 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 796465377 1250 796464127 796464139
    0x320040605041107061a030a1514240108070f1116090506030d0306440c03190f0803040312020a020a140d0801060f0905120709060b0403051005060f 65
    0x20041100f030710703401408014450102085540381e00d10b0300844070408101c4403a031507081480480045503071000c00742d44030051361070300041204191040e242e1801040d282c41c0d03c218a500c1070810101441110207041400c01d00301402c2e180342c043c60091240c000c1080d550100071450f580070040309070405c20014958100c8440a80280c1c44a1520006000885070340c0c4c800c0c880c880031406918080e2143c24186c512611a5011039080101e842094081224000c004c00e54501410120388040302607c240742c12101c00030b015450f400d1002c0620380940e8402c80c0058114401e420380004045410405d400d941c050819501c07a40e550405460400001024002d07207400064290b6103281d0210f400c2e000701d4880c0c100307050555400540c0720b90340da0540c4800c0c0c4c0410103080040c003459004207060340302c400759031070032090250300c50740460885280700537240e500f940300740001c3c440400c1600849000c1c018842496050920b19180e01d5a01d010380804500321660380d60105505442e1010101541d20024100b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 796466627 1250 796465377 796465391
    0x27060c1c020705060f1f0302060f04050301140103021f0219030903050303040305030a060906082505030f070e0604270204140c0705010c02060c0403020f030a0b04050601080d09032004060504 83
    0x119180d0104840c00e8443d43d02da80000380440e02104046d0030248840a1000c00311411642406081c0c0d209000c241d0220390705001c0040c0e0740d80c0034041c1030034480d090164000c3d25491441032004007501610b611109a0400913043e824580c0001c0220180032035403d5508004814241681e0741c103095000036100e4000042004281508900210700a40603d50708008103a0303a00042006c59003203010740340c6150002c01800c3d40103803610b080800c84200e4291a443c5142e0303240c3c0041c5c54001c4100c0e9544164001d9141008206440030500d40e10540640701131185072000070700103414a11220b440d8142041c46054081035441d82d91020320900f02c192116075a608240c01c55214a41005174121500d41c244504521081c3c400305070742e07000b41c122340c813030f80d00381402c1d9030030030007402840034000341c2501c2910411130200e0750719615680154010000b905036541010002030820412000c1802030101d021000c03c0010b90312001f080d860038180c90040007480d5204001809800d580d40160b034000d041084d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 796467877 1250 796466627 796466633
    0xe0f1c11121c0f02060c1b0f0118030e040509070b0309280521030a020a02030f070c05010807180b0315030d02030c10051b2104060527060c1c0207 64
    0x410450103003007611118640c0043d014101c0ea202c10455004800c02403d0004200b40b15030741400c07150b40340080c01560541c0750300f1410b042c00c40e04400586608030f4902d41381c1009140d0095860013100ba420384d42807000d403500103d45035503510588102510540000001760b801d20040c0130880c0981d00c3d52003025140f02009a00e150080c00080040c0c0d003d0080440c0d0840c8118001c00b03481454007070f500c1850965540e4a0028000c1d000003021406500081021500c03c0c88000004c255040c401e01e400140d00e810300380018000c0c3c9000380a0b074180f10303801080e03903580c07445000c10310b0480c1e244c2c0d045169242e4070552450306200310881940d80501c0755490303050f21079401001900c0e00700701c03203011100306561692480b404d403102502d8101050300342d0b0185018841d8044010f211071002010924035500318162980b102c40c404a0741919525501c9080c07004109620310716a0308445880b8118850318a00040075480d244058840f40c0c8908001401d2010780d50000340038040080304000442d1506443c0c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 796469127 1250 796467877 796467913
    0x30807021513030809150402060a0e091e010b120f070e10020604120f0c17130b0a09090e2a040603030801051207032607080403030e0f1c1112 62
    0x80c214045000d5200080340d50b04c0001d1072110f8007628446c20300d42c2da102c5809100f115400741002c5001c10180b0105140103480318a00307580103458100042c03220701c000d02c441030302d05039040e0440445448100070205003860307040d5810790880e621500210f09a201e081d02902c3c85000c61040f540c02075181087d4001e49030300400c2240c401c0740a4800300d44d81c03903568a000c0799840030b02c0e0181008500d0110100300460254aa44031041c00403040252616007051f41109080325036a0105104110004250b440240d004002c40d00400e12000140082c0c01000c03c00c580f1078901d02c90a0720f1000c10040c1400480302000301d5210400c4000d0800c05c04203071a4100101941c1090051500540b8010503100783c2c0600001e0b9402180e401408043c00403500b13078513550406a11224490341090300b40300720b0000c99154001000110b00c81d032540c1807480200414001e1040c0d050504500c01c80003031034082c0202041c2d107103010440342d008451107182e010407030000c0c1d0920380d42e001000403442408076070000c040142d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 796470377 1250 796469127 796469161
    0x21309050a0c09080f070e220f050706080c09130902130905120901090b0f04150507110f1f02100608160f0f1202030a0b09010c090906030f0308070215 66
    0xa595035080f854603050015550b0f4082c5c041a02240d20052040248200000000d904400079894080c3c0342a280c02d034907428180503a0080c1c981c402c071009080700b00641041103000600290030701c005a481e101c200f8201900a0f418884e02501d210341c00701c40d40320030070f5004a80c082c4d8014191100034070200ca40500802005a080300c1501c076601400701501d82d00c0058035611401656905905820301c42c0661140d084803a200b0007500007444049001d070f44940b80e018030406603903215511080302c0e08104440001c035240c1c043c0519140c00c0c58082a490308180c40c901c112148583c882c0780740c0c412000303e1601810801c49401180341040109d26000040740a0101d055908100c465498440500f10b140c01540d2084410204a40c04200300a018124078624441d000406858001880d03442c2c40c80c00c140101c0c0c0c0200c00340d6440020040243d0403c403100003070852040104109411551940395480c40248040d0520a942d0000307400544204000d4405101e8441d10380c40034148440391440d24450 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 796471627 1250 796470377 796470401
    0xe03190306051e0d020d031b060c09150207030b06011b050c010305090d0512040c031a0a060b090f041d0a11090708090a0f02030f030406020a0501150e01030303021309050a 75
    0x40012098052450001c2e41c0058240080143d14802c04581c2040900e010004040b014800400482c42c481848d28803494105405810301240300c981c080401007024006800808042800c85c0b80c071000c85500080b920152540301c00001840e40303d40b40142c0b040300c80d1029014811251400c06410000c02090013428460300ba2014400c907103560f80c04a80f2084501e12403000600280030b030f42c2d401c100356111242c219000740140082c1c1901d07034403000c2004426542031614261104148901d01d282485520024907031800c0f0300303090040c00c0c070026092000841c8410b10580c0c031741160511170b10542c000d8480d5075a004003107070311826003850066024039407410030f180320389451000142668024980548031310b103000040c1428103c03660700c020928004501c107a806101364484204080340800080c8050500740e00104cc2640861409600b9a0f40a840d041ca0408a41741c041008186030100581586d03414180581c07251409808450b5442e01c2d58001d00c0c4150400c001d0001913021503000f0408289 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 796472877 1250 796471627 796471639
    0x7090603050105060103090206160201030b10020c010f230c1903021b04050c030c0313080301091a1905010809030705011404060b030109080a050f13060206160e010804060e0319030605 80
    0x56113500540c101c031a0820044d411000420512a45980345500144004d205040c0020880311040114150350341c4030b02c0000240e07100c2c22003107046d5a0407040035020203489190610701d641d050700341c44d51b40b008066200d41c504030340400c4d1008900c00c107022081c0c4c0d901078407c0c0401c1060443c100290307030f04ca030700c500c42078522030840040c02241028084c26105030b010340d10b03591171034a40c40e000403019440200420842040c45c00d1640000f41140020740c02440445400300e14030910210103c0303080700c100581d0380308175006c040940b43c11040cbe0038000c3c212002400c20b180c4a564100c005401c5124802006000794a043c0d5000c241c4c1360301c12a154003c1d030044000b000051360481c00c0c5822a01c000c0c0c0060f000100902440a000c0e00c110010300c2e0b6a040700d08024104910b206402d000074200707070008405030b04480b04020720401c043c2c0101c0d1440f0050300c2d04948090320346001901684014101a20454039400e00c640402c10800c00c88901004881c00b12800c2c400c400b200800928203400b176684141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 796474127 1250 796472877 796472881
    0x32a080a170c0c03070803060303070605010e0108071707050f01170405030a080a0903120b18010e01210c06140f0c0d0908010603051902040e070b030708070305010819080c07090603050105 82
    0x954800150f0301c504090702e0045107008500d0300c2d14429504002c01d80355040c4801c200b200e0006915000b481c2c0200110750000200754185200315040845a8200080d11620b0140c411100d03280080c4603411039030142e900c100030306011030040b2030310301c40480c011411407442c03000d01c01003040010042c1031920b85551400000c0d11001503210a030346034a0300c040c00042060310507842c550141e0340700120003c002040c56401d01031081e134650807203800740c0c440c0403955030301001080508101d1041c1c02d480324841c0ca0811040800b40d8886400168901641007000310741074a0b001003000f880112160340005c0e406c281d48074000d8803011030395807640d143d00d0340004034800340014024105021b100d040da40c3c07110241c10f240d0500d411044c0e04a080b404107a078456200c0304036100042050210201516411103031541d00d103005500900070600107001c1c28101844d04004001c101e20110f9101c22800720517080038005903a608203c1180c0c0280c00b20000070340502c0c5030025112880f0303409041124441c0c0c000744030075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 796475377 1250 796474127 796474141
    0x40501090b0909191814280b07211a09090d030908090406060807030b060901080103030528051309060501050f0f0f0412140109032a080a17 61
    0x1805181ca10581043c8004081800ca600d1000741c19414900000300103100414001000c0001c0e185144c10b40d000031204c039405031703415414000000030140085445c90429003e0101513a166a403000c00303080e42d004000411652071050a00d00321100c0036808001000a1402000d0000c0030f010032801d041c240341b08085031039401e000048074490200d120203028450001c0000354050004c05808442d17070401000701103030a0b5102e02ca1130000d800790b982d685400d0b02d00740402070100c1d60088a02849014140410b04c0d803a84d1058140e41982d034503181194581c0d0f0031061407800c441194840701441c8500303040c0c000310103034417101a095090420002280581d82c0c2c0210b07170211000d602520b070014008101d811010301d800c0000700440c400c120441c510b4001380c0e016284803a0080d8102144d0480d42050740c00c1800391051400f038002e41554007c0001140c42e035000303060480802c09000405030510b001c080e03070f000401416509240c00c400f4440d920303070840c070005107080584550f06072020704000101c0c0715 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 796476627 1250 796475377 796475399
    0x40e06040509061501030c0203040e07090f06020a050c01140d0f0f1a030703020f0307030b160e03011b1d0303040315050f0903030c0304081c0b0406140d08030402031c020304050109 79
    0x1c2c6644101d481e01001c0b80e84c0044010300b04c00c45904c81580b000f0440043c0744080c030f5034004d104003a50754400301c2e8103003051945090703401103502c154115030100d0002d030302240b00841c102c44094000d090811010340740800700c2c80d0f103003d1514070b10314161614a0710110702c80320b41c000c1c210b00d13a03007400e080000ca040590f0715903225000d141d49603010b50001c40140010705001d078001c49180c0000b000c407021240d490341e07151081041180d4010341141407011107141603800410001030180220024010528120002c0581d0549544800c04014124240303400a004d03043c101c1c5020b80002d019243e07650b4980c1004002c03007181803144086c1901e440c000079070a46e10f0304043d070702407182240035600d19102c00c0380d0901d0a410140060316080340070480085201910305c600d04140c81030308000f050300c280c900100000c443c81a4000b01081942da448135039503595580f83c4041f859405044141c90361110f0020a281c03190180c0035080341000074442c0007205030000301402c01c490007647d0b800d408540f01e05ca00c00c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 796477877 1250 796476627 796476631
    0x1090501141c021201090b030d080403050d0510090204030516080601050102120d1407020a02040c0207080304091a0301110d0b18070318080f0a09080604020315040606030602040e0604050906 83
    0x112007080c0a000c800c1010002076030303007020280c2c60160400c00000c0001c103080c0700030392000c0440c55444100103a9401c00b40548044a180c3c1d05222050f407803c0d88000e400c1d4030854078003001c01035851002840803071281680c000600400c203402c5480b0b9442e441c040d5654400760128038400c041c2d961000801041c0090128180e4074182e02601042d4200050700c11540c00c4010142c0b01036488200c0e89207400d5031210380d140710b003505600400300d4910303c0c010720045a00084041c41107410600052005010000840301103c2041e180065684100c805042c2116a071040321985035082070781d25125121604054440e000850f001080307a51454007c0041800003980d005081200c280c00203100e19010794030481c18500d100400b250360041c56500d20b002c0d40e0080448a1000c8408621210030a82c4944400041d01d0068010034107420700350002950341c0b20010000d00358100401c0040c0402500340c01020007558014405d5441d66120000001c40210841e035941c051403402e0b000482d0a0300008040b8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 796479127 1250 796477877 796477907
    0x901050909100801150e06010c030e01050d0207080a03020703020f07053f0f0709200708040909030c1a190f02041802030603210a030216140c01090501 66
    0x20346840d04000500080c031074010050000d10b0180c020000300103c0a0180f014520b5100b124241c156062000c52954140b0180829040000d024111000690400d01c4030100c50002d007400c546a11000c4203910180c031070304000074400c8001003581c00c0c1d1141c040c3c02a080e000d1180d002d40300000d5030b2014107691034000e4031409610900c2c0d2140c407441440c00050020b51044080c0710708e018084c905400d404400c2c20040c002c03200c1d520180e0400c150f03030b50501c0380703801515815005010110304200d910b007040401444184000000280380c204014020044034010b0100402c2842032aa1070308014101950108040c1e0720540301c0383c401140660784030003203442490414500c0300d4500c104001080140b40844410b00300c80d41c00c03c03000c00c001c0d24024901e0491a41e00b480941e40b444c205040c03504000801d071000349490f5246450f101c070049803409440004519150058586200b4071804810901d10200a4a04090004c8010340e00f00d020030383c07580401080e241c1c2d81c25541d58030011540c00c00e60404038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 796480377 1250 796479127 796479137
    0x60f08060903031e0606210411030118120915090303170609131e0818060306060d23250f020714032e0c0807050304111f0f0905060901 59
    0x4940b0f50f041190640c0154000e006d141c10700c0f52968901e0f00c011181098440341e103080b0000c0108201c45011101d0081d04150000d00000c522400b031002000d044400083c821a0101c88440c4042d10402c0080020600c109100c6e00702144040d004e40700244501080e00042d034602c07050b00c030540700c140c0e84501401e40541095825559021038001c0000c0a200484130001101c40204000b6441640003009500520703003560307220f0814110680700503074844840e000d0071050080110554640054452a5210040c08540800740140110088a0440c40c1004003d450700c1404050740c290303003501c080520103400c201c1c84180209401e503064900207038040d005034003542084c0701355007240346504802000901240d0314000b000913000c0c90340c5122200c80c20000a13100031500d95500301d000b03240920304107050018581c00c3c001d0004002e840f008001030a02c420041c4050500d480344414080000040194100c0d1000300010042c4817083c00c0703101600150028801168a140c81021600746040584903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 796481627 1250 796480377 796480411
    0x1020106120201180803030c0a02160509011e080303011d07080408190e060c0114070903110d0302210306011403010503030d11040305030a020624030c1e04060f0806090303 75
    0x4550f02e0113800031071055500d0304400040c00302410805540109400400b6079102d00f40090000d160103181c000400c2e2510107e0001c00035600c541c211a81922441d651460050b080c18282c90545149584a40340c0341c0300c000000182ca2600308010700f44886240d120320219280d0310f404943c803800030386020b004e0340400c00032500c901104e401c2c0c00c0c1031180703641403070110314052100090290300031540b1100c640c0d441d6822414000340200d80e0562000045c01e1152001d419901c0b000310380c800d070703000460041030407400184c240f60080251420034250540102003c1d0805101e1041641040d110340e804030700a9104806400d0301c507000d0324141c5001900960500013615254806410215402003030003c04220200102e04180010000e44080303800912550926008146003c4081c6d000c0141201c100b0300160b00566003c5000b09500764211036800d0302c03031380001d905807550307100290080d4011329040c800030314142c0304101c0100307c0c0c850a094404a684a038a803640328442103c0d5140c0600800103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 796482877 1250 796481627 796481629
    0xa050915060f300708120409091a0a0b030618060c0a030b0d0318090515130f06030f0c0b0c210d051e06032802060712120b010201061202 60
    0x2201001d0314000800301d4801c0d00d82104030a01102c0c030404180d0301d07243c0046002100c0503081200c0c034018012800145074035290040c0c1c00301c4c2800396000d0801143d0315108400c06101d20118080c0300314880999448550400400308001026505003003030081c0500710000d483c0401d20108491340900810181110382e450009076012036200840400a050ba40c00c1c455010b5140c0101d14407070700d44285c460200101041b1030302c00c101c846561000c180b00d0f06001c100031807541c0c031406507002c5030b2082d09c042403820f40c0c1e4070f4408040d00b8030701500c4440620307140c0008140086940c0c120703c4070780549866075415844404204251003071083e82c1c2c0e295886000d400140e10b0b1118800080c07160a2103089080104c140d10340d105903030041d280c40034060b151111000703981091a48942e0800400c8004040c0b0b806155400b02807030f454080c2016009680000c113a05540f00d8501f01c80e6071f0b951044642041140440b40641400008031000003418940000d000f07265005110b14025500e40890343c01c5540e0981e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 796484127 1250 796482877 796482889
    0x91605180c040b030106081e0115080403091e30020d0302010605130606021b0901090b01091e0608010902030f011a0705072612030f040c0807060201050a05091506 71
    0x5008428a2481000700142909460004c2c40c043e00c0070b5a40d01506042400104034483d42001150402e182280010000381c10307060541241c88030282045003107a40d840c01d003500c1d00c2049502c50341903c0c003603641e401c010840d18260141507415884030399160101aa084c10380000c0d04455201c00542c04114150241c9007600c20302521601c43e05c000300c0c072a40c0b80c001154072141c050800c28a42a1100400e01c021501400012101540c0580b250202070524001503007500e0184192001d4a5940700307020442d0740710b02c103e07102501e689012004026044159441c44556621a590009204100101d068000da00880e03020303c880300c5000c601c0743d0a201c81e059425410b041c1d103800380c0108122a03800a0020f20100c0d00401c0e03c440c070812805c840d00010080001c445000a003d60000324603103902d4403010741035a800c081c0d82002c034041d40da1030f03150038080c40b156504001030611458100246140c1d05420840c1f09804c4c0600a110381d4481c1b403c0503503548025410399540302c4103200080e40303900b484 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 796485377 1250 796484127 796484131
    0xf0617060d0809060d060303050909181b010c171803421009050a0b030a0b04020a270609060b09090712020d020c0f0d090b1c0204060201020309160518 66
    0x10038070751609010071103510031a4400e42c8108c01051010584941c14500500020781c03140240308001407031103203c80d5850325080d0016a20440386201c09421000b6407090068480007640507071810803460b08081d1000140d0010444200c82c1132550590804500340410040203418104645402108030101c0c1c500d06000c00070086105440d815a04000064034071400340e0280c1c48004c90802060300308803008060300c500800c4066280d0070700101c84400d0b1400290215032541002c14400320741c5540c8002203070480359901c20f03003201e4201c91400b5031404407000590312881950b80b0803c1481c1c0d842c546001a5041d9200f06032605100303001e040c405060074480f00780d0080d02440c040703603900c901000500032078015000403110b159010460a1104004001030030714048104001e1845181c2100d000f80b80b03401c5802808500c0001048681c0d007000725856000030940c41c908199111074031118001d00070b41040381e62860741c0c454040c0c2260900c910074010b4090340d401030f100c555402a03e1660341c410040c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 796486627 1250 796485377 796485379
    0x9091109014b261f1509150e1b0d05101a0901021509121605101a1525050a0302010b0909061003020d05030909010f0617060d0809 57
    0x52112545016511030900c40b01604550003004652110208940740415081c1002c02c40d0f6480207441c03102140810001e9034112441c1c443c0401c481281c40000c031a05201544160a200c0c00c01d00760340005051490b89074291461740300414595610640c44128000c41e41d068038007072040030010b030121040c40c0d4000b603600002a81210301250380c0c42024031024030380074460821916000c03940101c2581d040c006800c0403a50143d5a442030300300000e010742c4450002c1e0741d0311644800041e0300100c0340c00c02c40b81c0040d01900305054403d200b01d06d45100d40a414002105d07115003400c50240b05072860f05540c00c6800c10804080306007084100740c800c0f042c0580541c003500951215050740000260100074101c0914425030011841c14403100502c10f1081014011100d5034018004001180c072529410070100d17138040700c51503800e070a1030030250f05511950900b01c0d0058040c0c0b0011500c040401908411680150b860001d68080341418040307400d070a8402c2c03a4406182c0c2480d01c04501c2d100003034108504 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 796487877 1250 796486627 796486739
    0x10b03040605041a040501061406030c090904030c1b32040e07170106050f150a0509150c07060806030102090913051f0b0f18060114040909110901 64
    0x180d1400d405806020417501100c15039101e01c014410742c209058048600740f01654210b055003404030040303d06029006030b180c0149041800203051621401041ea015500014401d1406149504000f016283c82c06400300005200030512006c07071421b00a0b580100b6040c20071914803444a081002400880c80c00c00081c0c42450701c00720705000240c8002034850b103d0000000d0080c03806051007140380102800c0e80c4140d08010f9a03680b20740c030b560b04a41c245036007882c0c01782e619250800029102281180c12254800c0f0104031142880000030750f94060320341a8482c03840c9907a0f004101401d0340306640405401001090100311810708041e034503015240b1480a55174090710b05d0001c00000e80c0e0401908860030380304c0c03814404034189001c40781150282034465011b40c0f166240d6203031304a00e014101604100c40d07060301d28025401d400507503000e000d4581c0107003c000700c0c9080a041d0404091036092280c102240005100210b690240124481450406200e803d14140004484409002c2c150b5054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 796489127 1250 796487877 796487903
    0x70209060123191701061b0f060f150f060302092b120c08030601080a0f05010605040302091312050d0605040c11010c020d210605030303070806090f010b0304060504 72
    0x507500901c0030703030403080c2050585070b070300d038844512401c03918080c280140030800c030059801500d01304016041d10a00c1c14040118030451480382c411491a040140920301c2440600c820440190042c034841e04103003006021701885030660b031503005040d109580f84801c1d09601080194000e8000c4d209006d4002d0036581c0c501c0c07404d500303e074100c00711076511782c034041680c00354108001c0000c00d041744042c504d00e051282040940d44018251201600042c140218500050ba0401c0d040d04400c0601e200c00e0418411540e44075400380240d0081e0008070702c03030021100000c01d02c0d042242c282c840c03103403c283da0688500c40c03484183d4040e8859a0b0252803a0744500c00840d00d51164016460031007030035510580d100d02d0b0480c60701e00711030a0000060441d0010b5000c000101c3e401000800d41001590400642c0081000d010004000540c0f0850300740c0008020020b4070740c7c0000c1e03001d102d0001960480150395815600710300d88a02409012001e1400340081340103d8100d5010395401440b2362a400d00d0b403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 796490377 1250 796489127 796489157
    0x1505060a030f02090d05011401060e03060f0c09120d030f090b070c0804030b0c03010501110a171b120903071d070c060b0303030901330315020f16030201060b07080702090601 76
    0x3900c5445d00944060b911000003011409034a22610300502e03813031801403407900c2c03000e000035200c4a018058900d007035004030105810450340b008544503108010851070500480d140000d403a001c00c080807102180c5001c1803510301c4050782c01824903032a40481064210fa9070f4520070398141040e0b060540700c5400a01c03010002031114103640303014107402c007403070b0341c8942c900000180802400c0101c01c0080d004121a9000909543c010071030416030389c0c4009480702090701d40404000c000030b092046134880d03240345010390134206004080d484000d9003921030007900e41304442404503d01c8062285a100078000410151041c0c202d918118030903480810310111880c00249540c009481c2148141d54482e01141001c01504a40d00300d003c86040c403c1040c000b00300000010020741c440900885149400809241000d40c115102d01c10040b0b0840c0d2038621445100034103002a2100b18095840c00101052002d22102a1140c281e804860540740c10800d5080c0000700e0305c040c18550500170b540384050700c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 796491627 1250 796490377 796490389
    0x803090109051009060c0e0609041e140108070b04080715020a0812060a0515090402070f021f090803030f0606090301090b0c07051b091303090e1303031505060a030f0209 74
    0x280000d00b0f00c0100e5420b00130305140e401c903110305100b1000c0c040e2016118813292030b14820f807008250100c400040b80c50681d60f20f4104060510a0a10801d2905d05408039071803603641c0543c140c0f0301174002ca031b01181d11146042e001d80f10301e005075a80b5521524042003a0211075038015080c0c2c1c85441078401415941e40c451102d0b0b0000107a01140c0d02d07601d41008050709011240c80d00400c1c044696403a00d44c20f040005009219102a403801260001641c1044c4640460801e003005d0707014010400146101c81206050340f02c200368100010300440e80054034070800015a40120314518030a0032903124603040004d254441c00d0015003554a0b0340f00100402c00c11031125105050803500c00d0381d203d0442c5801800e0a0b40800754880301c1800d0700a00103141c5840395041c4d8488580c41080d803543d44141070a84102103c0d5100d8001c0c0c01c80303503080200c20014141c03104c08141c42a1002e03c0640d400000e01e14a1184500416400c0001440b5909145103c0d820080d000003201c02d00500d840e02c43c401041d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 796492877 1250 796491627 796491643
    0x91e11100e0301050901090804091d0607020109050610080c01110a0b010f1a070803060f0d050303010603092112050a0b1309020f0907050d020306010504090219020f0d0804080309010905 81
    0x2241c01c81003080078600302802800e900c4100700c00208160003095480e8000780c0914020818016030761480702080f444420f041440c100c0d01c0d0000c0314500d2070908002401f80c061000e046a00f4061400426640003450518071b064402080240900700c84110044030313003a085402d0b440803480f4404030500400c04169040c0e0207418810080300c819400d01020707101981079240d040301d03041c1d42007101c1400302d61410140e98200b0001c480f43d614141030140050440480725a0150140c000040001410f58066110303ca405201d0a901d0030715605111003003600c40e00032072a000110744000181c900304003a96000b5640409841030000b01c0000440218820b22010b40840003000d80e650302c1c640651819041c10452a8011074040d2b5040c541600000c200d40198509125546e4011000c2119603010b2400d032406401d030010111344959042c619420180512001d8002600030702c6032450f5150400314030840c11181071344807040640ca40d036881841b140d00c010007889140d562200000000744050011107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 796494127 1250 796492877 796492909
    0x110f0603070306050102061305100902040204031b0920030f0606042724091802060a0c020a0e070c080306030c0604030f050c0303030610230415080901091e11 69
    0x3d8041c240030000e443d0038400360031041c01503284411070001520000350042031540242010510303000d28400302c0d029024507040101a944d20001840c00740c01c54040500c11128001001c4c48074110340300d0102c0c00c4003490251403011040810000e4000c20b016415070f50071460280176031345810b44c3d80e9100c0508036410144050480320304400101406003031301070700030000c00d61944117000f0307503101e02d4003210507000d4801c07032002544075200441c2c442074200380a5038945e00a4902951214800c01c001e0100c405104100e1050400c003038007144020f01c0c01085407181c401500d88214088071350f16111207c1d040204038541c54070640310101c900d511101d01800c0150b01c201e46038140411b2074941305050041240350b45002c0e030310606c10841c5680da1a4031000c41e0000a06100030078000d03001e00000701c91403412a180c0d40c1c5000203400900340100c42c02c035203103003000ba9440c040c0503114254954261602500007401ca80c840180c2d103030035613036144000c80d00c180c441d41e04010402d03032010109105082c0c4031052 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 796495377 1250 796494127 796494131
    0x603181006081006120b09010e010c05070302160609090b060c013b070509340e0103020708030a0b0121090201030605060306100e0f03100204032d110f06030703 70
    0x1004086000c00c95001c010083c40018400c2c0b0741050b01112204101600c040d000340000008642860001c2d4464590800703448003c1c054440c4c10400a407040d40f148404500500c902a4001171800c5004203000c1900e41c107544200b1070030714000078580917180d952085640030b01d04112000f005c000920a11180032044000c601c00103110410003200d082d144424a80d10043c400450891100003041800503100d080311041a99290150b18003280c0b90808100e90002d004c24140c1c41061101d512036100b5034060350b07502c1c0340c920385060046003680a00c2c94011300c205070900c04074880b03081d550001c41210106142144100801070403424075548101c03145c41c201e613503d2884109650341402101e0281506503039643c0b440c01c100001c00c0c0030151143c0400100140710103154003d546a0241c200c00349030003030890701c0c600d0301c034560344000b940035100445000980c80d60312840341083c0b0f104c0200106501c407041d011046191281c0d0720960501c002542e0240120603881c0c000c0e6290005035008a00701c1c0c2d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 796496627 1250 796495377 796495379
    0x20c0f0633130204120506010f060203040b091e130504020310090201020c09060a05131a01031b03020904090f050d0801060e03190c360c0e0603181006 66
    0x160740030580d6100458055440000d080c4030046040070460310900c5000d40300003011a182e007405034000d0056422420880d40428071110a201000800034141e42c51165103140c02c507500c0e035040e6a41e20603031181006020080c0703c91101403406040d0031143d202142e074001c90910301e03100000c040e02480c00008109560760804d00c4154281044144040544464208010076041c2c00103566003802a030740ca80302e20400030018090351070350301c40e00c1700801010780460500c94456642801801c2c070b0030f01010745241c800d68988003030343c424002e001a0108c0c45c662095024100c010880280d40715060964100d0307112514100090503200724110000d02a002802c4800c142400080c807419040e800901000b207000f400d8580e5a80210f00b0605a4212000034003d9003c186045400c01c50194807010410075010039501e0803900302d50204c21008100d022081c051a4107140c202c0c21911410b01c0800003d071060113040c0d0720304147c402036400c0000482c502c90801c92a041462410800301c489044064580e00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 796497877 1250 796496627 796496641
    0xd020418060906140d02030a02031222050a050603180307030f0806010315091a0607030306030c21150e0106140f0d020d02040c050c15010302091e0601080a020c0f06 72
    0x420346010b800400c00074402d035807910785428000b41e059800d4034402e07181d510f0002c046660401c20320f400d40340d0140642d41111001c1c92940d941d60131038507182640981e4450716085810b12542d110003503650080c0b891710001e0034400bd11034103800080620300a01d0691140011202c410030107400c502e4030a03550380c00c0300304c0740501c003e118075809001e06052600b0000441c1d0209411102d03079046e10070821000403280b8120000400b116500d11200780c118500040b03060a2540c19041030050b42e016101c05402150380303800030914100281003000211201440900015040f6010f2103403081101101041010491480c00e08585240d409080084200300507022681060302400c00e003c0011101c0d03107170024054012034103000061000910403950b862001c0e40442c000d40594162001403000c60342c4c03480080d227100460207001e0006a03c40d9400000250700c00021011010500c070000413001c1440c0c640c10015240e00b80060103003024540c083c00b04092110003005041c1101d2041c03001010039080c0a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 796499127 1250 796497877 796497881
    0x140111070c1d0414070b12060907110c0d060b032406010e06040918080403080d060911090d08160c0510170f04020402120a050f0a0506010c03140d020418 67
    0x6800b030036001000800701c1222907805040036a1250b0820015031001c80700200050404005d07820014660038041080364844008520440c400c02081c2c1d01d002907030711442d030155038165010100f0521907020800196081c2001903150f4285481400c011460b50240000241003071105110340740301c4502462889100f04147c010079801030003e007030111203503441d400803071001d115030f025255a442d103480c000c512803041030003200140358001d80e01b183c03665140c0c070317107001c00f580040c180d00c04090070044040f441c403445108000f8194030703110340700d0728252460061185401c401007068034039101c10b1107011405004500a144060b12600c170b414010b030304000810640e2300d543c03030b100b00403c54071490818000f0001041680c10000400d041d16071b564032440010080d101e80051107041506d541d041c40418401900080e0007480555200380c45030341c0d000304d414103d40049078202c0c0020544502170011a01452000c0441004149020b103000e1601c01c08070280e9016520010312145c00b034004a4500c1014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 796500377 1250 796499127 796499129
    0x8010b0f09090a0b041103010603140601090203061e150c010f110f0304031404030609060e1902100e04090b091f0c0e12010f0905030a1b120309140111070c 68
    0x7151400001e080c254015940d52030800c01c014201801c00c004030741400860a110030550720010300034414182c61346461180c4044150003074601d44aa5000841c0c10040c2d4000d4a2140d1005040015400f03082c081c40c00d03c07907221035112900800c25100704062004010004c02541c0c2c98200045501d0343c102c1c1000088419500c204c00b01044240306140d4003c41007030441e03030007942514104280301158403e041d0395110320b501c004c100c940f801044a0030040260043c80c0904c5019095034030001c1e48592450b04022004002036003d102005084460f0b401605010144400900000740b0ba59035030b0748282d005002510070201c160700410f11501125048200a004604809810700001e148130001404154a00034018464000c50314100d591420943c031540b601c103108841070103040001d0803d15100e42c40802c802000403009803a0040f0020000d10000703115500c60b00610f0613008266084000700410714080f03502c441000e0344002520300901a034655074040091840e030700e00741450041100c9210f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 796501627 1250 796500377 796500379
    0x12901020c100302131502060f01090c0207030b090a02090901090b130803150f2e0f090909030c1a07031a0d24021b010e01050108030a030f06090608010b0f 68
    0x40420a01d1060701c03405070980714403041c0c0c00c000d43c80324518010381e0904030341a0044240030303d4400d00c09601e00e034000340b201c2c000e031940a42c1c04010703600d80c482442960030380140c030f00140e807144108100041420700c10f01e0b071015161007a14014566a4002a0040b034280c801030b20b40e80d101d44c00003041c000e40c00d003c40d4100c1c401f206101105041a0b4503a407450000a01c18039110341101e810b14065103c80d80c590303030703414402820b454114180703120680460442c100c480c154206184882e40100f8015214440704100c9912880d0b00701e031400f000c017400760007408011010804010740c510000340001041c810b4000346004584024a04000001c040b180d079140d000c10620340c81d082c150400d0b03c64126044000380c2180703156151030a4102119030034084d0580380d0381d81d00d1000803401c134016503079a900c1584184013002130011107034540d07800d03099a00078014000b041e0803c02c98a451140a03600119070f4805036035000c21020b590b1880e001c102c5603a54001d1f007070750351159010240d6250800c0c000c90300c800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 796502877 1250 796501627 796501633
    0xf0403110a060e09010b0f04030f14070b0a0909020f040b1207170417070215031e130305030f07091802040512151311091810020f03161101290102 64
    0x35403400000c0361300c20103100d4207003500c3e0f0000da03000850114034101c0d40515000f525018000031246000142802c00d6030b800015070140840110301d1100b00400c079903142c2020f9841c00140f5040003040002580191400c2079500010080003608170381400c0680301056203051019200c1c50202001341c640101043c1440c0003240d1001080001451035290403440000d8a010035203401081c400300750508103411b003600d4400301c0842000030700d4900c2031040012242c0442082496201c610f00c1382c8041c03000c4840103021490074400201c850000710940c0e070707110072a4500b90520f40e698190040c02001420252014607400140502150510302c82e031780b81c028100d600800300c4501c0c0c0303400300c003034890003510500c40500c001c140303403046c00360310701e00440e045400400007000da09143c0140d0224040011841101e4000d00c0e9204c81c03074480a100f5148d034074903550412444c0d9a07501d40140c2000241d00a00014041250343d9010b900718244240451021405800c4010780d00710310f202d520645040100904540c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 796504127 1250 796502877 796502897
    0x10302010903060509010f0608010b0111060402100807140d0507081e0a1505121b010216061809050a05091b010c08090a030f0503070201081003030c14030f0403110a06 73
    0x80d0303200001c4801c40360415000a065240c801440d409442c1a091204030a420140b0201e2400d4066005d0f841000d0b098881586407003445a281c0d0721548101c40180d88130402042001c14203018200b00751f845005480d1401480250040c14011500034116140c00c01390303186c0030003039495080f2200c01d42010a10039581000c0c0e50442c1c202c01042ca0091105004a844441d522030301000d0282c0c0300d0240500414800d262441c00011a65038100890040f40180030418894965400421009090001400c04066190030190300381e8014401035140c40480700c403c04001200d940354484d490007007049000100d050b0030105d550030714000e11102d000254440c035001201c082d03030300300100809a981c41034206803030b0650040040c60f00c07012036201900080caa00f40c00c00400002000603c80d2a05c04d0301e600265407508888003118110500004011540000d25000402d0085082c2d034014051034044901d010507900006166400aa1007140c40008501d0301039142d1034450105c0c4064280ad01c0d00036449 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 796505377 1250 796504127 796504129
    0x2030c0117041407050324060405010f0317070c060c2a17192d0b010603090516122001080c0f0f120402030105060103110318070f0902031806010302 65
    0x14140c068001460f184901d98810380301c00c0c081c0140c0c0d008101c01400d40c0c0d410710310210140c012110b00070740742200080003000100145400e01c50035050b101514548035084d4219510094141d05181880101410134090240000c4149100c0005440d840da01c065440a151030135400141d00d1004404060700d00212858860400807401001c0b122151081e031440d1055001e8542803002c40300b01410781c0c1520144010501220441180408982c809040c214410103079900088400d43c100c000c210390710040c01040f90912035082020086e001c2c00a5403070190466004004401040c1d001800541c0c0400d035a5003030108041c1c14000c8200d490f0fa11840c1c2004100000700410401465080300400c0810822200085082aa001560040445940da0316244000f02d4900b2080b201280701c0e40c241000200c06512038010109401d0000d104036040d52503035a0001050f040c0e14881070003602c07502000081251980c01d800c0002c1c0170b5010016076078182140c038100041d80030300c4c48280b2984080010001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 796506627 1250 796505377 796505417
    0xa02190e0610120b0a0e0a020a120e0c0103020d02093604211205090c150a0e01120f050f07030b030f031c0209040e0f010c0f05120417120402030c01 65
    0x1001202c0b40005040002c4c10000398010356942c101d00880c015460411008407017a500601da8043c554455026400980910200350b420100c0c01c465107070082030030204154081d4004d080403181251002d2306207149140401c2ca03544117411404400c030110000e001c0085001e9071440c0e2440c0c00390b00d40708403e20b010380381d0041c1e01924020502a62040a8842ca0004d00c0350000000a0704044414405414603942d11640e480d08580841d2041400846200006062008690360754840d61030b11000c0051400054070701c8140456082003043d100c1800c1c02e03000c2d107940700340c61040319800c04001c510b00300850020b04485400740c0542c000c0e40310320044c034072084000042d00c4000c0d035400e410380342d1201c8000408001c1d00442116581103818282030180c22800070481c0540402000000c01c5049040f00e001c03107009144950840108404220344824450f0340c59800d42e01600841544541145540710005194401c40303c1000301d001c100140300c210316090086d0351b1742c050b0074070705400c03418442401100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 796507877 1250 796506627 796506647
    0x8130c051e090703051605042303010f020f0d0617070e040303140c0307080f06010f0507050a051f05070305010b0f0a0207080f0708010b0907140c0a02190e0610 70
    0x4864450304100000da9062420702000c146400b41a031249418401d1014015000a0301d800c00c082410800780c52050b403050040e1011120404460f00c0004000c2559400145400b40b110790503540702d901c80308060919000801c184042131401c641d448064481034421a000303508010f11461a0441d1401d20401c00a008010786111203040d280603203d51138240c000b0000b4001603590030309844100070640750b0310b1016621074406916250b90343da40382d040192000104450190104001480640010344120040c1c940703544908211018507150384c40e0985000d11403141800c6030f104500840c440d000250080d40c0d007100c06400e003440340d0b50410000f901540100421000b0b040400b09101107598420400c441c01070800d14161203220b0720600c4101d4a41e03206001d00e180b10f600b00f11107410581050000070780b154100756581d110350350840d480454a9845610344440e5071040040c0d00001da9a8212402e8010960035401d20309603180004a008980d00100200d02ca241c00003590717154640c211603c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 796509127 1250 796507877 796507879
    0x20106080304141c02091014010306051f020312010803070c060315050111150117160b1902100c050d0c180509070903080f0c07050303031605030a061d060108130c05 72
    0x10300c00c0380c079010138664208560201940c01083c0c00c050082d01c0710450192400c0c1c9801c0c030416000554000010340640e50a4480d21f50000c9403c01c40348035800018500c040342c0c1c0316910540c0c1c5002d12a40708500c4914080c3c0048503650000900e01c01002400384580004000b030342014840c41548441321035262809101e0281070101c0c840c90300310200018003040003529880c40c0d2808413941c645081d19010f4004084603035840c4031303284800c08110881c90001c2c0441308904102450080310055156401070b807a160a015441440c0d021040b8500c03030301801c400340445680745078403419072402d09000e507a00303e4100d0092080f184000300c0400d008880a4007911019a9404c1041e1601c000448030840103501c09042c0350008500490000c1d03490b002070103854000b40403502030940700c1c070400d5164403040d1000c103507a0244007001160a802003011715400030500300300103021031352041032030038007802c05044001c0328622004210617980c00c035140a03088000340e55020001da0450791611a00042c50040ea = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 796510377 1250 796509127 796509139
    0x390806060a06020c012a0302070303140705100b040213030503130914070c02150d0f0f0c0206150f0a06120e030a0905060c070306060e09060604090f1e05061602010608030414 76
    0x10302100c1b100c044c012407280c1040b420164038a1820025100c5202d80400c400241441406040380814041507914032078100000d440e1040d804828580141741607410290019004d003c52100606000c50000c002c43c05103001e156294880200b103040c03c8815041120194a4000049006540745070b049520051908055101d06010f00010f110080542080441144001141074802259800c0140282c1c01d10308107122030020040c41a095601e140b080000603405000000d88805030b0712003c29102201911010541c00c17201c020a0004032242c010b0000300760758103802e003608040362240507400140346c000740d0700705000300f00d0060040c1464840c0c60b1080c1c0e0042001021103c062042000a650002041100d25502c01d1619000c09045503900003034001c4000088180c14207000d51111a41d103e901c0010300c2c051a61459800003440d035498144481d005050000244108185405102d0501d0001c0007801503500c0242581c0300b83d041207507150000e0000700a031520300442000718140896070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 796511627 1250 796510377 796510397
    0x50f1c050d14090c0102070902120f130501090803090d030911061c0606020f1c0e090408090415050312040f03032010020702090c070c03390806060a06020c01 69
    0x18040c00507001d50442c0844464180828804002075086100b0303800c1c2c0071348402aa480d08082c00302d01070b05e80800c03001d80040b0001190481c19500700782d071010400c103d4080c3c0c00c0c19600c6543c2155102c440840381c014000007801303124042000920400310035071034144a440e2140d95030400303000078050311a000b140d0101d2152440095070b045020100d540c420100700d441e503140c0b0025902d101100540031a030040341c9003009496006013141200c0a01511034610724500d4405212041000900030b5408120030310003800d1070707a16030144207030703044c00c0c0c45000c02aa820a801c040c1403004c09017001200c40410001003211040b01c81441d02241e4060a240414281648001880520202c508021070154104c4503801e05442c2d405001600d0080d035580403641e90341c42ca200c80501c1900000303016144c001c401080018540b000c0184442c00c21040307a407036204600d5100b205d54400201d603c0301501c1031007080c481030303030700b00710f039a40c404c2c0c0440d00a0317103032844c0c0200a0b4480c03110b8a0424100081021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 796512877 1250 796511627 796511647
    0xe060a231516260301080d18050415080106060905010c0204091e0c0f0f0602031912020f030a0c050a052d0c2a031203040f020307030c03050f1c05 64
    0x42038039810b00e00040042c040400c1480c1c05604034079450210086202c1100340e20441c0307107203001605d068804c981c00500c807100035204151140c0c00c00560b12001154900030108003034540e4001c258044490302c60a403219428207c41c070782501c509800a008110080300300300950382e1b20145402c03540c2d80658000403007804a0400e180045c40350f10501584490031801c02007000961a00c14044800c1e0700c01803200681ca80f944448841c11620480c00164014070242e08032040000e6062200c044909082131b420b0f0107008140301366004800400c0c0212400320402281518901505094202c035141c064540249108041c0c21070041c82c0300800031180002c0946d224088501c00612500341c10709600341c4803828000c4255071620741c0421074402002da01c102032001842051050b034810030040142111202d03010112040f900020000c0da07400010500c0341c80542c60a1103907401450042c1000350704c1c1c5065044c82407810301c145540b84080e9010070f507502c00e8001c04c0d503100d81005400307140041c0d40300a160 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 796514127 1250 796512877 796512919
    0x210081b031005120d02062802030a140901020c070518010e07020a050a1211070608070f020703020604090203040507060504050306060405190f0e0706030e0d0e1302040e060a23 77
    0x107048140c0041900901800d191130009076420000360382da080780e48560301e5412821100b01221840b094090b0344039204040744d1515005154070503842080090070000d0360760031070b10015095481102c0c03a540080d2456042d0030130701c4924081c1c2001d40300318003402c94076011780301c220005200340000e076030b40040400c0031580b003481584c43e52034010007291001ea8050034223064020940c0075a102155001003802210803001c90441c04441068a60340029070316281c05440303004811401c4001c6000707815000c40143c2c0e50784e0240002d0714004c44010307103900c0d091802614004464007c0c0080c464140401c100560300050980d0f0700140664001c10301da01c5003564069684001d00051030a1428203030b03a6000d808490703121031100d0042c03208030703050030780d450300185e044031410108080f40b5044051516803050144800a1b502000a02000c0406120040e40022a0001c0e003122540b240480c003844003518054452802401882c242880b18906403000c4101140015400600814100088001c901e401e8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 796515377 1250 796514127 796514129
    0x1030e0f06010b0a110604030e0f010f021b0a030f0f0b010b1305041a180a1a03150705120403030b15090d200a0b0c0111030f0711011b020a0210081b0310 67
    0x200c912034101072234054008424000d41c240141c43c0882098100e40c811540240900306540282c800d610b4030340c04a5450f46400c0d0310f0182c2000d4103040010004c0d0400064445540c0501610702d041d00051078000010352041e4403261011100f03010422400c20a0082c80007120710485002a40d9110301d04440d04a275459a4032a50000214036140c40000742458820f100344802d21041003440139810100790121000c1c1e00c00c1d50194009500d400709035801024090b0000140c3c03d0003414001203241c00d1814440c21101203002a84440940c071480c00d241c0d403824030070030307945010354100f684103400300340450004070010740846a000d1000c0c960755a5100c120464420141182903800d488039280e05640e0b03c1f030b02d072081303041d031928884000c00c0c40700e0415680580102400026640c40745c1d04100c0e031601c030faa845200136550790180030301c2e0b54180280380c5000f10420f801074608200c0b940100710501c01600c000c40e003448454000c01000851080019140c80700d0700410644039254000241820354103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 796516627 1250 796515377 796515407
    0x100e041a01061701270b0a05100f0f0903080f1e0f0702091b121e0a1a04051902130308030129040e131a041101030e0f06010b0a 56
    0x600c00007184580d4800300751121108443e1140ea50341c1d1380c55000740c10050166000c00226030b10000480042e500c950400c1c1c030405401015046840d482c1d10000c0c201c0c840d2140d04001080508444000715070300505014440517903420b102944924507151000e041c86070000500c404c003000240b1440c0341c070741c510000642582e512a0349403070b442c0d014143c09160380b140009a2042d4402d10010301c2061a4888460007035062007113203418103204403c44104070030094503000c1c0703d40c080b081840319581c00480c0035124041940c40403d105070038060f2241442c068521042c01503080000b00400341440c410440c020500860005035034030380c40c0d83c613200d040140381c000501c10b01d00040002401104070040001500840d100c804014015080705080e601c82c520a0604024a42000507082d050103201c01c00c0e018010181c1030b80c4003040012142e05d40c40308407800c803041d40c8d50000c000080d5034540701b2909c0e025040c5000305145448c4544aaa80703400511440551716000a20041601c4c4219030764200209 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 796517877 1250 796516627 796516673
    0x1090f140f0a060c12021801141b01091502070f020913060204031208090d0f0810151d100903120201090c08030403060b0405070509090903040f03032006100e04 70
    0x94602e010f0020f040b2501100000500100c45010303025114070840f0b004e146003441c9040c06000e11001585c08000d6020394402120003403050340d06030568241c106003030408550000804192078a8609200b40c80605001042803040c03140c0ca00045d00003040f400c001d50110307526642a510b161005088882140008094500104000080001469030022140d0340d80c2c90300e455035030390080c10542d90228002030303c000460300c3e5800300d0100e0103024415084002c8152034140262181080390741b0301025a084000958080101c202c1d4000310101400342010845141c0d00d4003408000c0104003440d103000140c1400c01e49410011030034001d5102c42c2d0401c1d17004004480403980c07503014130f0320703900144070a9480a0801c016856145000c0c42241c0c480c09842d00e0b25401c0906007010320001d05001052440c1d540300810020401a24110f9000011f61085d80c5030007800140f07a514940e07444100105142d40c1c0c0c40b0f441800a10141d20b00c205003503031402c0c08400302030340d100d05100b00142c0501403802900c032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 796519127 1250 796517877 796517893
    0x1215030f030a0c020307050904170901120911010f03061203030506120706090e0109110f090f03100f0f021911010b0d0c081b0907030209040209030d2001090f140f 71
    0x1e800412908055008506440d10342c1e90392018419006001c9a00a2080c00c02c80030050440b0b040c00d00be051500c1c3c043c17610b03214201c4001812070860345000c4c0305440000a4403040000c560b400580d03420a1142842c0c2408801d2400d9580848044118001028180c840300040c40c030f0f0f01c42a4018443c600080d04030b0b04041d503145400303881d114942c0214895a0003e000104e03002c0614041c041468406200040c6060300d83c400003d4960001c07a040313503010ba001c4c1c2d070600c4a6982017001c12100003230b0440005002e0075910340d41c400c075800e60f0a100a2140140200d0b03041f801304114807850300103035003008845003858036059401801814600c03988480c52459130414090fa00640c40181c0c0c00400454001d8103604043c03001c0183c019030116070140030b84001480c0c1c0f40c4030741c01410840f50f001d080582441940400030b41004075148003840040c009003030402c510241150b40101e0100311000800003a0f40d41c0c0c54a00c000030f41c03400042e14200102c1a4500c840b403040000c13078030f0000c0c40c80c1079407040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 796520377 1250 796519127 796519147
    0x50a0903390809031908032220040f18081b0a030c02040c050316050a02070305120304060c09060c0305180d1104061a0301090c0e12070f06051215030f03 67
    0x1507000030348001c3c0680f02e1114240d1405006550345d08001d5004800c1e641542e982800105020b1880610b00d01044040ea85030000501440c0074135143e1880c00c034200c941101d031881800f08a41407843c45a60203410f020301a030341c0894003100c0e105003e40044410f980d940600640c0110180e0f210a404201d02c151034048003890392143c041d4240034807c0b54203003c004c4080b48115898082030300d4441c5088512110711034854001d10050441d01c0300f81c010b503425507a9039140d01e801c003101c075081c01da22264000104410000d9610841d0b03420384041c10304800003424484000c02d4040d122200400340080050903482c0030260541da00b4210b807009004001c078801e00e25042282c07003141d102d000d019508120002c1084a25806540c0142c11480c604904503031070045800d010b002d0401c4218203001e07802000e040390b5181c40001050b001070302c00040101624118a80120394050b90003c0e04100050115400c0040c00c68009504040c4401c140d0b0a400e1035040000c0c202520030f026142140300002da07142d05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 796521627 1250 796520377 796520393
    0x1d010e03190203190206160212070608010807060504030b0c16060911040b0604080c010305151801030308090c0d230601061d031b01050703030b06160501050a090339 72
    0x10620035419035550b8140030041c4c40111140010007540f1240c00c1c80525565032650100c2c8215500081c525500c200340c3e9901241814641d070010310009082c1e00040c0424102080108010001d619189141ca85191250a036203000030300445d2001c000002c0c3c180d94404d036105100e15407600301004110f03043e04c500e0a662511000351103a07019070300301103e1441510303041c1e05440c04c036049180903101d070007c47d10044000f4200100303030806440480084040d41d0b21442e99280e00c1100c0c401c443e4100e9411418080c0852200811078000f0b980302c0420700728640c507000200300c24598401e00509846808000c01c0000b003a010202182522580b400051001c2c1d100b0b0041c1d19642251001c0716030100050145a01d6032410300040500049180c41c8103111b510601c01442000d019240020b040b202a00000d04181c0c440c05401c0c1d10904001e40020601800788107194005a00550801618055680241c42d0a02c034480d61551511600c507000c0c00e183d48042c0a4088101e0210005102583d0f807501940d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 796522877 1250 796521627 796521673
    0x31305030d0f05010905090f0705040b04060812070b090106080d110a150605040b0a0f260303010909020a050f090105040c090503060a090b10030f0b0406110304060905010b010f1d010e03 81
    0x41780798281000300d0031020000c130700420780c207100e0800344c003002e07042c078007407102401d140380101d41c1085e0b031b0395000130b21207100b4011542090708081c100d0381e039030100d41043c40c2042c0016110140380d0349444000c000303041000481103641081030602103440c0092000d46400c002c0b010401504290041002024008150f80710070141c0b0402c41e820095803003180103000c480e82c0c00b40508106000c040806005c03090088091121407040889451401c039820110305085410a078401d00c0480d4a940280c0308500d0403200c4100502400c0e40e00d40c0540c01d03204001100030303006100b442e00690b5100c81e020300941c402c6000e407020b0711001d400c0300e01134204410403a00030f1074100c5050390182c080d036000c41e01200c104803c45080741d402c00c0c50f004411845465514110102420442e4041c0d030300d11814521900000286105501900300060308080d5420322a081d1980c000355a4104854240300d121280c0e003101d182014101c008003100d40d17072304541e0010790b444002001070651600c2141c00a4915aa10764813082e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 796524127 1250 796522877 796522889
    0x3180d0f060b0a120818060405060705060601031406010203120406060f08061803040b04031e0c181109060f031b070b0718050d0206030402030a060515090f0c031305030d0f0501 77
    0x807502d955122071003e03513000740e03a0082c034180007003181507800029501514441040106507070b00c0c2c03540c0c40d00000c0140d8000303601103400e03030805e01c10401d91b980c051145101c2c0b030542c0610b5880c2c62412800003502c80c403c0c4200443c04803040404902802103560102010341220b1511040954a850005594541c22203001000d081d9041c010044801c0210645086410000701a8186429540c490390b0840b122903025190850310030109010485001080000740f510f440b1a03200c0d03174048050035003a20182c0003d00c0410908110302c10a0340c41c6ca4080b6800b80c06142400343c2c80e41c880301a90f078049200124404003088001ca403071000c0c07011000c2c080740151003507181c00075503c4401ca0740c080d84890600c1138607072200003080701c00d01504240c001150702c41d10082c1680d03500c00c80b580c1c07203108a610903a940b0a008034100d803460040d0404400568010b85500e801d02021b251110000301e42d0f00c0000d0440100410140c100001c22030100207441c4070f80c0503400103004040404001400607c000d110304 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 796525377 1250 796524127 796524139
    0x70f030f0915200a0302071701150b1b070608011403030c01060b1306090e04330605191a090a090509010207110d030c0b0903070f0b010e010e010803180d0f060b 70
    0x10f5100080d00060901c005030f0305401420803646840550321859907000d0712402155256018181000010a02c8002410a14900301c0e1145500307480d03000c0c510040c0c44005a02d030f001070000d228164120b68001c0c1182d00000d51030324140c03200004642903000300090040c0a41c03c040e80403600809070805009501d256171043d600ca15911501181e00ca0042c0c071441101921010204001c21000400c00001091500042c18048400d02c50f2510b07483c41d00e9050702c4065510030050150385441700f10045082034541c40414400c0c10304920004601c814294400384440005065000352584903141d00200341c41d02c0e0402c194581005598081d603c165000c482080c00d5407042c0b810fa1404015000115030160380d10030550a0f0f80da10011300c2c90001d007500c299840140000300014821081c1024011f104590301c2c450f0707526042200d00d000c0410f800ca01308203801d002c010f00510800000382c80f040042881003007440000b5601184140444a6000e42402c000072618014050660040c1207482e10075184 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 796526627 1250 796525377 796525427
    0x11803081209120a030c0c051e100204051c05070810020903120f1207090b0c10060b04050d080304020a0f0e040b070509010f1d0a0e070e06070f030f0915 67
    0x110303a80350085031080460100c4244850b9240c00e221b50f000c80c0030341c04982001c0596103c00c3c3c0310540382000f01c1c841741070032a050f54080d45149609004001e1034070049441035003032a0425002032000c85005c6d2464000c0b41789a1441010301c881003021000418510f07040c4c51510030b10001402c0030354404036030f450003442010100300c02002da010480c0c0e281c480301c81c006802c100540c2140c4042c0ea8000d00740c54100b203202c0901050818140c4001d00e08007000b0030090203078804a1400005542080d400013900c42c40512041150b601c41a00100940d64007210326035890f6520704c0051026444c80c2c20580c01d681c038400010a01e00140b0304070900403406152241e03011780d1000421074492007007404150000c0d2215020901c0680188900c11540002820b40c8001c010301c1b40205180c00714a50241044000490501404641240b60140c07203003810754000c1d04d4000c2c240c6400c0c91440d8200001000c02800c8001550041d104e4440b0101510801da40060410042400101000c100401c03e019104070401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 796527877 1250 796526627 796526641
    0x1203060f0b030c120f070f0c0b07030e070306021b0712020319151109031b0f060d06030204180308011d01260f102d02030c0706020a021e0321060118030812 68
    0x2040080140d1081d10340209a8603440102d020333182110f440384051044400100004109001400c0548a4541050040c612080c09a03103400c54560210248006240302d80015850200d91607180300d89544c480031031060b10703180c020952841b00f4141350072507251090202c3c0c4a00c0314802880e411501320226090018070b00c1e5001140715501c1c001d254400d681c0710000015042c024083e1100d2004110000340315540c81d000300c1d080c2c0c1c01e0790401604114031020341c1c0c41007640120071a8050710035180c82c01c0d82c900704040034180c4062b042c00340e0701e0342c00c103161107116110055504640641e0842c0040c3d40c006e049040341985d54510203100800040d0030420f85102403c440c10380100d03008800d00c000d80200e4040d4419200a5002500d41044200c04000705404112240000d0900c460154000d002c00c6000005644401052419041d200e410070840c1501c040c456607401d50b17101c840c2d551074000d96250000141c42030500d002402030803082e0741d200003040c04400e1001e40311554803000c01c000e0035500c0f11 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 796529127 1250 796527877 796527887
    0x1b0611070b0705270f041104090510030f02041d100c14181c020a0b040305010f0e0a03030b0609040c050c0c0a03031d0a050d050a1203060f0b030c120f070f 68
    0x1101d401c441d10600c05a40c40d080d004c0c400c1520f880e00040c000014804600d800710b41500c200d9182c05450000c00102049504214801e9683c8281d03608180c075000380c11030351403601c0e0000449001e40300b141c40e414901c100400b121255402140041c0849a200c0d01415582c409000b0341581d100c00324040744c80c0b8100c0307040c8000841d14800c1d011403030103000b86148001c02064403404032804070821003c442440050329080305c10006070000301034054446203189451420b41d00d0b8407031090400f50900a0101080c40c001450220f042d40c1401c0102d050450180800c1c05406009402035100c2c1c2014903c41c0940c2d0400010492038010000ba1800c05d20b0943c1441810410341c44002c00003030301c100707a410818904103840610418000d2018055540d2000040c1000e696480d05407040e0b000500c5400801100d1080181c0e14443c1d41002e20500e441c1c0820185020110710407000b078440c00000007902d01e03441c0720440313444600c090b00030002424410f0305103180348001c991650101c1c1d481c4044030b50b60f601913 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 796530377 1250 796529127 796529137
    0x109080c03032b090c090b2b022e090e07050403030f030902060d0b041d030313050c03070602010c0809010203190207020d02030d020c0a1d01061b0611070b0705 70
    0x50025440c0400c4030311820f240d4407216805100003950310014466014140c000c4031110742c010110420010305214841c0125802d0f2405d0921820350203503140401c00343d12101581c4040b00360710400c1c4010160000c0754102c1c12507090354029000d2075002115030b60088003100b030307100386030342c0e50824441d20b03140d4009000f0030aa60301404110144420000248103800b40c040c0c4260510b40418100d00303a43c0030641540102d140526031a03201d040210a80c01d00344640014401c5505c030b03071854004400c42545e103e10001d45900f0700240c0c0942e0b508140407040014589641016080365840340c1c2c0c4410003070080140d0810000003c100e9004125818014000e890003a02d8140041110a080041000003944010707030072030300403e41f0413491000d030780c084c4406044000950040c00d4402110b01c03c00c120545144c000e808400ca00b19128151082445e01ca00c3c15104181404680c0480b000a10711144007041c01c01801b050404000c034480503040f40150002c05d10440e02e441c80350300c4400090341d15000d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 796531627 1250 796530377 796530379
    0x30615020a08251502190315030b0a270506010515030601080601111b03010f020c0604020d03110d0e1801061718010f0b1905091315090506060109080c 66
    0x40c09411900050f4410100800840c4140b42c0120049036503511201d48401c0c1380c2d510325681c04142c0c03504010803d0f1081c0b03036000c5246010089903003440070110a9103124000640038401110000741612819800070802c42d20b03685815406644441e203013911000310010032501801000000991130070200c071000c0344883d00c08426401c55480d04011100d070f81c0020305040c100074904803080341c0044c05201030b0002034129181400c010303500d8002d1500751082aa1100b505501c1008540801e00c400301c0c010380c20a41c1120a10310403441070408481c0c2811a520b80960341c0903440028105540000802c081d415080d100b180482020712071503076441000f40b01c0e03400842c1e814650703078038030701905042c42ea8401801d00f4108003100000c0c0e02c0500311034031007495010030341d5100c00100ca2841d10495154201c07802075034820007a4140800300c0c1e4400005800c1ea0200604824032301c04200c0000e1900400c41d042c01002c003c03c26250034450b6451340151422800303e040c3c50f5012807002c10101c2e4134580700384 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 796532877 1250 796531627 796531643
    0xc1008060112091a0c07052107150609020406020706020610031502210a0605030f1605010f031118130e03040614071e0506150108010311180106030615020a 68
    0x42c041c4000014004680b81128081003a10305400e1954032681d0f0140240e051540c880d443d1503841c0381081c0342055500040303030500740d428505030104850104407180c1175406490744076064130302245100034040d103400400e206030000c140800c800341d00041c100304555143d4200d03a180c1d04c48a0009400d400a808041c1040c41c94607071440d40301c07446400900c04100314810041030244142d0f00c0d018ac0d9141610101d2a642e140d82c0e040000303240030040c180c614501c0c02c028001000c0d42da0030508a400305842030905009940300c160340b040c2d0190380b2000e00d845090b0555981d42c603d01803035928041005d0a280d1082c0900081501d03840b00510505c1445041d002c000c51915040640554080704400d003c491001020454540084d82c2094107480c0722079442d01c00800949a494120700b0003900900e03408501030001d80342d02880c0e90101029044a03000146948402c05800c040303100b080c00b0712019540c5090000c000241143d050340030f0411038071081030002c448444208200d8680c50604000340c1614 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 796534127 1250 796532877 796532897
    0x30e03160c1e27061401020d02060f060909071706061509010905130605030f0f0f1911010507060c020a15020403080f09031504050a110109060206040b0c0c0304080c10080601 76
    0x102c1c00403500040b11146841d0f220352050303600c1c81072040d981c494010140c418001d901d08001940c040101c6e50180b100d0307001030720240c54500062070116a00030440341c41203000d00b010440c2c26005101e0700b00507008903400481604207070586141d88080030340d0114014600c92404e01008010241170300e420701816500c41c04018a04000c0140300d100d003018943c40e040d43c0d80310000b0269002c0003140804032501014081000c803855246003082c2c4900ca17650840c0c0c00c040c02444542504880c04644250f01052095099a52100403100c9000e1400001d10317903442c0c14400804541c000680b05140e07032260260382d08104410002c41c06901641c4001041c821050003111400400030001c1c000402d406002c94a000b80ca010002020880944094500350007980c1000180304880301003100c240c0e000e082180a0703e180442c029a40c1e14000d00c0949040c40e100301181e50841c0220885602c40181c00c203c98582d501d40500644400094074401d2192080c21006c5914a01603110984520b605840c0c0000715 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 796535377 1250 796534127 796534139
    0x50a05030414010f02070c05130204080703060513080301060c0b090708100914160911041208070f05010c0509090f060328021503040b06030609061501030e03160c1e 72
    0x1100042445200c2d554131291600074010380f61014200307007809941c1c0c464020340303440c081c040c0b89141c04141c81501030040005000c0c03c800040c0c2882102d40c04100041c85076180341000903a0040910001e2200b24000000228680d0002c0301015503405a940703c605601c030311091581c0c5003203a00c5811026089a0014100035101c1d6000c04c0c5103e01400100b001c10042540b080d09040140902044050030007006015103c1c541c4198425143d0b19000c2500c0d140c28000c480f04118a1080010080f1600042075003c116100441e1041254050000d100190034406e0150054005014080c011780c4882d000034660400d00c1e141c940169009405000311004c02902c02c000c0c0917480b0700b079064038040b02045070010f0b1a817002c2e01c0c500d4044c104215490742018580300d048908094000f51081c1c2c04031301030000e0721401199940d0840341e1b0340d0b5091002c681c41801a006403103411006442400040384150f04080b100110055035407040e858007414580342c0b055507420074182243c5022808042d4824411 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 796536627 1250 796535377 796535393
    0x80c040b100e01021c030c09060e010203030c03062409010f080423030f0a031b0815011d0901030b06030606090f010e0c04180c030c021207021005070b25050a050304 72
    0x1c40b01061064030b001130140d044490f0794003108828400041c0d070721901380c280d01d80d011001d40301426903850411002010180002e43da800050084001514000301283d0283c0e0b072000c03010011564800354081040c2c9800c1c8119194014036410f40c0440c851003030400d07a0b0b52040c12894070860b80142403494800302c400c944140c1082c0008440c00601c03080000d0070a145541c0b02500724200c03d0399010480c200c08000307100d0b840c281d4404110500400f801400480222a81c801404860a29001c0001100c0c13901d6032225130b0f01c3c0f0180c5a008480d03140048180650385c40352520035103040d000c59030191122024000000002c070303140642c0300b510301c0051150400381e90926800c0400881c4071403c1c50349868160072201c803100c40743c10116175140c200040041d014014500350003020f0000c2e1880f8017080380f96240707502c0b54000082c842c00e80741142040d114080d4003501c00e0305400c05141c0f107940c5018074450700d80c11004542e01e149440d02a2413800c0700d03441841219203103c4960b0703602e03040d92200c2d515a07070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 796537877 1250 796536627 796536647
    0x302190503180f28170d030f0f0908090f15030a150306050903070b09011a0103090f240b0d11010e011710090e01090807151103010f080c040b10 63
    0x39002d030b07101c0110b0310700d40d03220032000c1c10b100b41428075013214102028464029808a40c4400001034031031451000408000c02e5031b00a81c845410007040324540c110a00c4001c104450020718032910f420910010700003480f0240060b01402c3e5440300c02a011041000b0b400000d014030001d1104042001401e0f03480c0700d8209038060fa8074208010301c1c02d9145ea41f0101507070b00c101c0300900d540c0e00119650040c001040d903aa1780100c001c8000b0440404554100300000310600415818162100040d02c100200000510034264101c42c000007403851000603482c82c45a10342c00600c0080c20480034083d64a4480b600c03151040e13001103002150555a40156a450014140c10303043c4440040f10189400480014620500052114120b03050500e08040c086a05004400141d030f0f15003000b07240000e00c4481150740d102c0d08044038440d440300c91040c0b03402a054149000103092000f10002625007820f071400c5080d03e01400035a020484100d0030701c022141d5241c0201d40c4200b005160f40051400303506005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 796539127 1250 796537877 796537879
    0xd0512010b0c2503061e1d061b0706020417100b0306042a030605060a0e1909081608070c0902030709030206090621100e0709140a05100804030219050318 67
    0x2c143c3d40d40c3ca03191601114042040751801400c0f180c000d44011100e4803a8046451f242c40c9990076a4280c00d21055654030000c01c14242220b0400000049001340e80643e580a40d022006665564458008140b035103c03501c484103043c81044102042d44145020b060780d6a4005402040c65a0795619040504598075407404600c2c0c040c0505c1803403240c5801f000501860040c070780800c8605281e4240001c2c1b4401e40d01c9552201309903c1845469802c41d030900b002c03107603224008038181459080c82c00e8a0b02c83d0440800c21403010043d00c07020442000050600640682040000583e0f2450500207a100c01c80d14800002c1c8014002d2006140c4400030307151a880c09013120703082541c012099040005844c2e56180b00355105800c000160070038030318540c0a00f403001c800340414140424051b102c1c1d2180e0140c0100300b0610000e0f0003458131400c0041b0020300c00107003a0b0824103006a4080e003000d0080c1c40903401800749080c00e00f1a54050010a69410fa00100545c0340c02c004d1950040c100f01404955 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 796540377 1250 796539127 796539193
    0x7081209011403150108010f0e01030b040503090a0f08060114060d110d02040f080f010b011407050c0d060f0605030c032a120303073c0903050d0512010b0c 68
    0x25141d400c010b6000d14415650443d0300015a0640c0c0000341407020b050348969015003025205105003401c0307040c101e04480d40040d489490b61110302e859811405070b000c850707401503240400003441e061008111400c54a6203816142c19980f2200080c0c003400710b40d0800354020740104000c210f28401c0741d00800e8058012480744c0d003003452350704540c0140ea05c65440100d06200464082c021070409002c7c890308684020001c015007228080042c0841d40c98041e030490302000424084188501848003886515000704510407012007031401400400d212405502c03018034000001c56039080015441e0a416001030003000c0d0100c440310a00d50369002d405094566920300518407243d619204203111251804a001d951a480e05481c001e000c0c08403940781c210074680c03458540c000c020401c0c43c2101c101d81603580030b5414000c0e911b001e840081c140c6c1d000074440e1060074106c08415074080301800c1d002068410f80d5920380d030b0310810004c0e00e000b0030a10760055003021909218035070301c104002c45030541015034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 796541627 1250 796540377 796540397
    0x207050a0b07020109180f0f02090d1e02030d030905160501050906130e04111009030213050703020c0604120306080313170a170712050705070509070302070b25020708120901 76
    0x943c0c00307101a1b0155004040d074841507042d00c1910745008100806620310340850521010b000000c05911440700c01521845262081c0042e5440450b00b25950640180407503206809030040240240400c1e002603ca601a515488002803a00c099000898005940d19410704802c50100016a070003801c85548001420f000020008207101031300303120700d0042074100b001c10448000c0c0218031305007221103030030049040f01c01c0c8010794030941c5ca116180124500020f0f241d981c15401c0c0d0092240c041c01900c2840340384200001c000d82010300622480d00e558003481040c1d074400d0b1055590242012a0045c0d940981051211491030242c14251601c0d8004640ca02d900d1925440454020000c5404080344000b4000c0d0603c940701040b0308090865150080c602090b644032662500d1050044510854124000c02c1d4001c1c071a070192003035103402c1114031803e818840c01100c2414006140b5102a80316078030f501c0e030344900104a610840d444100906110581c6c40a900348035800040018180003034000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 796542877 1250 796541627 796541639
    0xd0204091b080c04061d1c0b16030e06040f0c0308070311160b1902010618140a0902060a0c0c030f050f210703050d0209030303040c06030c0207050a0b07020109 70
    0x362046840c207900300410010040d4200401008006041101009081008100035075001c5c4d00008030810041c0007582c5402c1180005502030b03a00700c41181d200013000300b41c80c140309020500134091f164010380c0c0c280756960440180c0503075040301041e071b0581c1c0016001501045480900b040c1551040102c003500540701d9449040e950010403080d80000e51110542c40c00c00e40030005d0b0b00000c6003104201480b01d00e000103405003403141c5c50300862103460554010300c03a41d0003508603001402c0301c0d000e241d00303180c3d0411044008007000e0900b142004d28290105500709024442c43e0340c0b0fa50040d01c0540303000408502924200d60042040f0381440d5281c01c0040424030003040b012560303210340090920078410070805d502d01810415905200c0c4180c1e401a680390140b80c0403240000d0f8142880740d20b0303020b098020402801400b001c10340601000081004112080c611801580c0c03242d18100708420201408a03078500d11805001d410052a40013403084404203006000f003988149840c21049860b40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 796544127 1250 796542877 796542881
    0x10608120a0c0c03050d023d0c030e01020a03090204050f0112121103030703060e090f030d0f09080415020706080606040306050a0e1614010507120c14070b04031103010209010c080d020409 82
    0x1c40c0000143c08c410803110300d4414000403201d180c590200e9081107180c5248040d8000e001c07081c0b01e00d55455442400b0408580260001004000400c0c001c54a0708041480038024207003030703c1c080703100b203203803800013550485100c1c40b1318141c4008400b1341018207806d5441d1803140280101041c1030003402c051024100904000a42c420855503a010404c00e00d0408002c1406001906011842c0c11201e4038000c008000000d0700c480c505a0040425441c403030f84000fa0040280c240301415070040000c021034480e18608501c4041407481c2e0843d01034a503103090849000409556043d07101c00c04120420100e29a500650703086404074400203400d00d203071050a40b030028100798083e40140703500c000300007913042400041c040c01004e0030320b149025446c1d43c500c6d944804d03444c010814400d092020206114140a440d40c518210f00103e841c0d4588a11144c002c64100c0e10003241d8100d11003c1e0303c00c40c0d04040c02580e55130383c03040c0c64002002040d84d4035003000e6000000c9403125583d0031310000616568074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 796545377 1250 796544127 796544143
    0xe0c0306121501030309180504121209080f0c0708120711220b0a0b0c060105040504050c0307030b0105150f12190f05010e070306030b070f050f0408030309010608120a0c0c0305 77
    0x103506c1d010315a510b044015000381c4c40e082e0280481c545414104404507029010500100c01e0610348443c00300143d0b0744050042100000260805a0104043c1440400d0708000c14444001e94101d40420380d0b00c1c1d0615956039100c0000000035203084c02030368005035554000398410308008061460318040c507040305a948625005451040703450f02c0c14243d45040c1488242d01034004d60340d805144c40710049007942e440d04188140d44c05541d46100050038405c0603c400d03940000024141d40c07003180e0303d09044440020038011a80320f00c0d400b019801703000c01494204d40c1018443c1a501e410501e50791540302c2c0f4200002c00c402c01007041a20341d040d070400f25200d20840c0b458486030000c0d255051050305120b8060003031035041458a004814008a1381e600c40f03039540540c1c0780c90700305200c101d208000c441c0c500820102031451000409c0100b030421010001d1440b500048008101c0300b90750b00c04581e59240800c90b4003151030402c004003800a171080300c0b06122680241a4541596070f2903850703510700015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 796546627 1250 796545377 796545383
    0x90315060310051918110901060c1b321c060b1f02100f05040503040506031509041101120c050a050f13090b0118140103050a0b040519060e0c030612150103 68
    0x185445c204111030a40f43d440300000580d2544410340c105403003d408150f289002500000c0820301003100e10b184400200c0c064541581e507041d40c0c1010310385a03007544a100a590007201d4050690103418103003801000c8441a81c0c4d0500c1c071031400c0c0c0d5101e0b81e00230080001c4003a00714041180d850000d205501030a007202d48107500800f114410100d0900071200b4014517040241c1c00d250601011410010549080da1003c0fa0841c0d582c1e00c4030110200d500b4540e1803140c0e0010700c00000c02c000d00c01d45c27894202d80201d00382c031083c280d01c0c3d11034030381c0d400c84210b04411030101c1c0d001e004541d400c44c4264044c2a403a07500561241c5400960b2070410701080c820f074000c0204544070036510501d547c0c05078803204017000c0446240d40b1079052002c942d0180180520391810036a89800040161041d0b4000342c6402101030810406400d000c41307240c40e0150070220301d80c42982400c2340050360208800e000c503c00c40403078082d981943c4615041010100e18501e92400c10f01c5154a0091700c1c450700040c507402588 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 796547877 1250 796546627 796546661
    0x120609070c15022a1b040603021008090a1a0f01050118090506011404090606140c060c130509040c03030e010c0507170129040b0406080c1306090e030903150603100519 73
    0x9186900c0c5c19141c070003c00740303602071401d00d002000103843c0c82d981d4002c0d00d48141050003540e654102d03107a2405a03c0b800250461801d5104081a4030110503411f0180580c0c450302c41c035680c0c8860054034290a41151800a078500d01c4007017004104503880540c0042c030525241040c1065041c524143c0e4100b50008005940d940d4001c020380c42e000321802007004070104040c0c1c200620812281c0c1c80300c10040c502c0c90106000695800300420f84044e4201a2400821101d064200b90034080c00d25121400101d0205000d0301d100f01d11503010f0a4124025640030000300400780c1480140c006442c0c2e26014080b107903403036510800a88004413950900c21000c045800c0c51003c0d05030400c01034a58030104140568076004090210401c003086031690780c08107686200740c40d007004002c4c80007000315030300030810035141c648420b1340f0000100007808001001c404803030903402115203420740b5110130340b44c4507819840942c191000c505603170040c3d0751007940d0310150800d1074401342001041c0e5200d0080c00b5404c01c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 796549127 1250 796547877 796547893
    0x1e0e0709050106090b042106020a230c0307031d060721080c0405040b0a050909030d3e13030b01030b1b09010e04060b120609070c15022a 60
    0x1200c6441603500410480ca001303820240340c482a25264441c0740904c1070484610b848452580441e03d0248000030740c009011561000f40540c002c00b00301c0e8080c1d02059080301c00086980518400064588006400001c0c501c0c001940c1d500740d031070441c4012420001c0f8418501e0300700380e03541c600c00341a010340682103410354840c02007150701d100b8210308400b90a103c4904140031a4003518000c1e0f6040d1031003078400003040413900001410f03a4480740d200c5940314054001f00610301d20003101500c8082c14a0005018072090011b40c0e030016090031030041c08450050b1074040d80d408040511410700c1c8841200645400754503118480c2a80c90781e00266403920b039031001001004180e1500c0703076010002c0e0b01149040344018071004401e20404d40501d0401040c07801a00c00c0b5500d503440380300200100810300b90758030400100031901400031070700e0b03610454070000010030071400f0741804d50103d64000d40000d6914200c815480080d000350000d0310312180c00d0200040368603040103c80c00d2044407607008021032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 796550377 1250 796549127 796549139
    0x305270c0405040c17151302120a23010209090f06010c061128021b0a270b060403050c0402210a0b09090106030209010905071107120b07030c121e0e07 66
    0x2240042107045d043d4018142c0a4040b0403144080e60401d4000005c4112422035000160412150000f50540c43c01181d0140c800c001107044100441d40c04000e0602c100314076850258200d0180001158021016a0009900103c00e500003a400a01410242041b50b12616080201c4020400101e00d154000454180300703068040d07002c0314650f070a0160a248507003e4002900c2c0d08140d0155460b00240c51041c201300e40c0c3e111040313406403141200000701400000c8203072005401d6081800070aa140c40e00a100341d091210858007a0b80d040401841002d0b217550038030000b54810700c5141280720048170395038420401780c1c3c40315014122001000c0760000200041111600000e0007541d4542c2c9030000820050f116540818111041c00000103115030712490180e407181840000300806004400c2c020400c01c41d000240303100180a401d03200140e07070710070b4010b50468144c03846c0c410114800440d030061040050308043e81207405441c84421071043c1c00d5800083d01c2c8200c001e00c10344d8105040034041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 796551627 1250 796550377 796550399
    0x60a121112030c06010303140c190203030912061b0a0203030f0a061805060108010b180103021b010e100c050906160606082a0418030516020306010b0a0206070305270c0405040c 77
    0x144c400c3c2d8810323182c50081d041a643e507940460310050710f90f40100100040079950b06200341c644c9414007a0002d400c031110031400c0e64442104803400e8110f5020380c442044c2588051302a5104000190000d51a42d1900321011a50140003072074601c40755250039001c2800040003101c894211034040001c191800c0c084005020400c0503040084c80c0001882500301c03903650560031140210b0f0a09006940d04903241c070202741030540b41560b803042c1d820503100c0b0610900029100c8409030f52020100034040c181c0b0000c40d094854050243d43c000018071050a140c20903280c4a40083e1040800003160340e0b035505890b0506402ca000070040384204a41c1003080c15000d40104220801160b04000411031034201201801070710b071018040020100344800a40b92045480d030542d60014103c9881d9030303488408240315888001400c0045c090320700070600c3c180c020700070240600c0036503003128400c03134010321600007c07010349801c0350f05ea11507007000c1041910b0307910401c0d00075809440ba9004203401d054401c08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 796552877 1250 796551627 796551647
    0x3010608070e0f040c110a0804050316152d0f1107150c0c030c080606010e04051005060f0d020f0d060b0a120f1407020a0308060a121112030c06010303 66
    0xe02c0716000007107110350744800d48900030300c40880d40081c0e6600802c20881c0c07110f004c00a0785965206d8280407505124815000c2e00460b4011000c03200e0040c0150400c525920b680d210300742e1850a042c400c019150301454002000c240c0348241181d030801c42d007580084403907030740800300007140d0902180007445030b1010341c2c0c0711280b15031002410180e1901608648400d001d400c032600300400c41300c1ca41c08100201801034025900202d202c02100d4449070700d01d13240c0105441c25400319240c1e19440d100e600702400340c07900c81c2518185000c52185004188211540524810043c15004000c2c3c0c000e800014405020071a80500e2595164042400154125145900140e00d006000e0203112a801d038015510506680949030104290032104034200180a610009620600c000010851500e80c00642d144400e070003542c400945840d050188140342010f8000c000e00d592005421002041500b0019490304c0c1002d13000c0705202ca900c580d030b00c0c00d6803c9a590144181c00110041080c550b009500c21 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 796554127 1250 796552877 796552891
    0x60310050f01050f0f03100e01060504061808100b31050c12340503091c17041407031212180209040f08160201090b160b0c070c03060203010608 63
    0x80c3c81d040613a450901c0c00e008071710040307071000c400000040380700020100940c010a40301c1c40015072561174900181c403540040c05003100150540c085c02042d4141c6a0410045071614805880d0024440c1030150240c01d13641c1985404c01c0c007061502002c0c2e40d00400d81a40c0e0000000600707044c07010721810b103040e41d201400c60b1250b50420711201c000b0703c0380000c6054004807194100310a050051203207030700c01144005140004484070000f9941c040d0488021841030b49500152076240c2c089424145040707010b0f684410018010704458600d881001c0041a000340c01402c0d01d0b82015940000d82d403501000e138008941e500000c1c0d11850009412400c4419507070803103541403202c0700394a0b5a0b03512600c01e1401c0a0310807211100454240120300d1207001e0020b800c00314071030f40d8505801040c100b0f16800002240011604403000501d140904241d40c507080a200c154507a80960f41c80e000d045000c060b040c1d10f2410320030440b10b0300041000f40000011071040c40d0140c1c030303507152000c05000711030300405030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 796555377 1250 796554127 796554137
    0xb270a090b10033804240203010311090c0412020a090c0f0801120503031b0d0e030a020d0e090411060c160302010e01050a0801030b180304030609020406120b15040209060310050f01 79
    0x70540300740c00c0c2c2c40e558035505040310413802c540d501c1e402c04040b40000360b882a40d03d444005201b10345181c483c0c000318141d82c00358126100d081417240501610032130403101c00c40e101000780001d00c02586400e0a50034400d000504080102c2e440711396540c12520060110300214100d182d40406490b04040385600504005184c0c561240260305c070304c0e890b480010b15203940c0040b110240040820039009540078404814001c2000c44030406441c0c1c1c4e282d1001c071000b40075209510300b41500710301c18002200040d40107840d00d84151160b80d0b5448003158110a2540e203d00207110409118000b04400e40c900e090004100e0019807550002401600b4426261410400c0400c902e45565400c0440d10341144d81c014018000e0342d440000044800ca2821030340f40352400000790000911401350804d01415000721010060395039075140c43c00440700c010800900303180151000a01407410315250b003c00b079501510151a11b01baa50024115600481d02821b99800140e004c0c0b0035824100310303281c0910300030308013 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 796556627 1250 796555377 796555433
    0x615030a0308220b0f04260f0a1e02060106090f05010e0f01050f07030504030c06080103030e010807110d030609142701060906030f050f0d02070e040f080408060a0b270a090b1003 78
    0x81c00f4058030450f001008008c400141100c402031045005404c81521110b40a2804801c1140251070b03000c07e118082c001403800c4008034801c072000d41214100e8030140c6032401c0540055040c880c2d000b022038040c5042c0716082c00b40a8102c840c0d04c009054591003a908c81da9510304615006102c0030040c0c00590030010004018000a030300035115403000c440034282010300ba540d9902c11214040408004c503440d01440002101558142e0400e20513541e10700c82c00c0c02542040144058000300c100c0e180c01d8440c03d80e0341100450104011105d10952580001090392030b00d54440806841e405d0f401110310210400820b4188074081c0710486403503004101512114100c1b000c0250340755024012500b410400001282c100b00c0d0b800c48480c400c1e6440000320307807220f503200040c9e0707203481c0c04650803116542003000c0916145002501c0f5401c50301801002c61148207075048110005200800000b80300f652045800e02007040005a2485000c0742c46100d0105400c51400c5020304441c2c60b000e443d07000451413 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 796557877 1250 796556627 796556693
    0xc060e0d0804150207242a031d0309060706060f121e0224070219031a0705070803060d02040e0c011215060c1509050615030a0308220b0f04 61
    0x14440043c0c40100240d42d407502c400c0a000014545886241807400d0b004140f0380700c1100080d02880f451f2200c2c1c07402c1102c0c400f284203034400450380c890741e100708e90000c0090f84038614000f0702a0424034050500040d0f4251100c104040c0e045164010070003103400c0c01029410000800c221034408114050706040842c0700b41e022400c840403400d200400b6000c4000c0400c180c000840a0302e54664000f8608800240410141c2d00c0c59042030005807070b5445907090640e0a0458000407074064010342d55006c2c680006074a072122260005404507600071001d81036400940d45030700a19150a40c4080540500301600d000544040d075100303107140310709060140b61940c50748218100000c45195084c5440204c4945c500070011080b01202c1428041c41c1001c404140140011440c0c456500304050310030000c0400b04159641242081c0100010541c100140751456188840740c00c2c0c1c10503a85810840d0311030355030043c0040007152840c444c645181c00b0082401800c0e40000c41d104a242c0980c80c200111071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 796559127 1250 796557877 796557893
    0x2040f0c02060c0c03160807110109030503090402030a110c07060e0301200a0504030b0a02030f18030d150518060a05043813020d0b03030c0703030c060e0d0804150207 73
    0x14055030f1010030110311221005018021100b00d85424035a41da0481000c0c036101260380c10100095425680550710300d062940906001c106480c0c1040085040c102000104400303540010100d03148241ca440600c000d03011840094a1510140310107000039605000e0014a0b03e005402c541d1b120f070303060401d0030054000c0542000004425503400715038440b0440000e0b5401d01c5903034002401c1c1e14248082010700c0c040d0340d016500402c00c801410042d03803500c044010030a4011100310465400402c80540248000c0d8001c8207464158441307100265075602c0080c00b40000034040701c14101101c010000c5510f40400f4003000341904076802c01880d8007070a411301a1002c00c60440c0036a8070b51492500d000f0840703500030010f085005158100f40c10615819001a400665070b17180010301b403000d2003280d460084255401c05148a0003032400728950345007142d00444221060b55100d50f0340070002c084080901c0544c040f5907440e00c540416050074540b00c5000d450b40c0710301855042c070621503500003503000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 796560377 1250 796559127 796559131
    0xa030e0901051005071a071d01090f050603180d020a0b010509090a08031305012d1406010c02041401060f09060206070503070e030f0d271409100812030402040f0c0206 73
    0x82e01d8040d031112103510b8005002c11a2603021031010140504103c3c01f19800301264202d5100e610301c0000c6290000010342d0110441e024880007686c040d402070003141060300245502244c84102c21108007400340d00707942880580041d010060700115140e0b13040c8a281d0710101d0042c2416070b61031f030746442c00c0444682ca9183d50328004002000000104107400d596410310a1041d40140c000c00280041c8901c0100c804440c041179001440070000e500c0820919100f0100130603031a24501d20f195075014011500800441c2080740d110781d41e560903408038542410954040e100039252481d10895090000d403980403140e10030b008541c40039003042415070b408410750781c0200320380c20403026024030000080d040100307075102899180304100c43c1412607503018140c4800d50004100020810b030303040c1c0d505440307a95240500c0007540e42200c0c4c1c0000341d05003c04c0f42c5500485140540c182c0a2302c601d882410b0400c0c0580c8690581030220a0109620b014420004420000f0804100110440030003a440d8080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 796561627 1250 796560377 796560409
    0x3f0e03060a05060d050d0f0f020d141c06030b04020108090303040f060b0609060a032a0207031101030207080301080d2618030408100615020a05100203040f0b090a030e090105 76
    0x456000c02d201303440c1c0580c0d042e911a4402d054403c80064000001c199805042c071040c0001d81400c545507941d40081260210408982e41c0c0c074090703c0b401140b0700d1407988441201224103920030742c01d820030f0b1100c1c410f01c40591320800b800780240c00e0a000052600e031024040c148280c004205000c001104048042c2d21154080c0f07011032003441d6040024501e0043d0f01995400080c0001c1d6680c0159060740b011174403004080b00c2d941d045054140c14a20f060410081c1d0025a2100d4014004112a08c5000042203014034016103802c0d0305607940041030300280d01c8040c03241d01030001500f9107600300c08120b0181d4a2192201d510501c1c450380c54103030304000b41000080c21315403800c0d03217055001401110043d020840c21036004290384803804005000310300c0750450b0700e0015001c440c0340d940302140e14641030380c0100c01418840c51002c0b10800a40c0040e204071915a02140c1000005440e21f18882c401e0f000140501130b03030b99103410702510f000080c800035440360340d100006004075030b5510f240c82c0071914 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 796562877 1250 796561627 796561631
    0x3060d0b040c030f081905030115110f01020a050a1409060a4409010911060d1b0507060b090402010203030a1a1c0219140d3f0e03060a 59
    0x1a1400c0105030782c141d81e04081c00d050820a901001c0c401613400400c007144201401020380c101c030101c101c0c0d01c1c1c0400e0140207030070341c4164000703007030075215102400b5080c0d000404e0340c4030708040015103422070b0700c040c1c0403101041c004140720142d0740e00a010000c5036a840c0c401b841c034080c0c1190010b5694801c40d0056410700c220036981c401182600c4050000d0500b01d00780800120fa08200105e04602d5440804140c4001500024a49140601406405030b80c0005420b022503000420440544c01c00c00700d06d003200740d5036840d03182440c10a1078000d030104015202c041d070303a00b0507003058803d9524034801c0c180901300740801e000060b40d0000469a2000c00128005849901c45007a62803182c0c80c820030a5200748100d400b90443c80d01103800703042c06032007107540401c5440a40850424040e080c426a0440b001d202c980c00036a003420003e070203410340309400c0504810b0885c1d54800d0020101c2200003201001021001b81103800c10302d0241143c0114148141c085000400280c0c2c0d0301c0d0010152960301d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 796564127 1250 796562877 796562881
    0x15080705091e090901050910180b13060204180f0b03060109020d090f061b1706010806060409050f01092304150905030a020313060306150f0908010e030c07060503060d0b 74
    0x40b059280b00506507800914440050138404101800307414240c8400c030003409001c0341c5090482c080e10510045601d1021983d0344500c4640720407071300d08401495410202d03048192a000a01540300a00140030322451107270703852541002510444005031410786486151000100c900e950004d45141180e131880390250b514000c0071a060043c000c105d82c003c0c410804000d81e03004000c2c50350800e03004000d4902a50414200b8401c08a9240035540640727a03c0c0d1050802142065205043c12540b019010b8583c0780b0741a681c00d20b60040790300441c0c00e05510441100188100c04c883d00802031102000900301c8504010392080c040300d42000342c0000c10410440300781c0361500400fa04085070307030b079000000d580c0ca9000ca5080030351a6802840e45e52000d0003407040214409000e44a03510030380d001440e030b01c603050940b04011ba400f440c0e4100300205101c00e8410003e002082401808811004e40001d162680000c070012840c24035a504410103001c000d1040100913100d2820706484241c104c60465025 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 796565377 1250 796564127 796564159
    0x61219201c020412050f2b0302070615091e27050c0a0f0f0503121204110909100e03090904081804050a0515040902010f0c02030111040f1508070509 65
    0xf44655030000d4140c0a043e8070f00000d00002080018000318010160b031174004e022a00100c4d5603000d0b0340c4801030410030980048005e072299018094081c841d00d0006043d20603803400251b2050305511111034107440d450b00314844c5000e850660a2064a800140250b4503d440f18601e004d4079030802d0310710810809205014400204a42c40c0a0103015020036420390b1201c01d018800c045500980d407140070000740c00203c5041c00500203a112901d084c1035400d0089600b11740380304610203003041e501101d02201d81d40301c5550710b05440d80980445401081c01d0120502100196001c000e203a0034030340c00600000c01c46840345d65040354010341c00506155200700c0422030b045441200c14210350424030307200030010a0b410a50000e8002c50003010408020043d000070802a00c2c020303140203001481030140c1044441c000c0c40b15988840c401030002c20003d0b804601201c00d0740203503200c0405001500020005485050074505420032a860b02a1440ca0001030203171140c843c180f040d900401e00c0344018119 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 796566627 1250 796565377 796565381
    0x1e0f020d0b06011b05070626041a100326070c090f0b041512031101110a0318021e0d0204090501050f130308011a0408030c010e0607020109020109050f061219201c 71
    0x1e0b41203000038201480c2454140742b81d841c01000490900820420041100c02c005c1c0d96030391045980c44828800044004031000810039007a18204040d800140150400034642903491406083c4100700010507a541d01c606506459100710300c1409103241c1800920010b21014080e426580c0c2c0d006502220840c500c2d08681c60120500554482e51902d0740e4502800c1001004107020b1100b90760601038005000c00410702c1d0301a12100030b601c43c6007203102001400910a00020240d402480d4604000441e00824140c1d001c1c1c00307040380c0d2030350b542c410001c4944090211a801000e01324800d44860855503000d40071340018002c070403034100c403039001003000c0360740c00201c3e0080c00c1048141d98444081101e2103019000c40090503e83d406a400003810a0303105100b100ca013140c0580da0021010301d0301c024000d84640e8041107032781001c020070055450721510205c150240c40d40140303d1011401e180c3e01c04086030f000705006602c0f0006064120800d880407000e5503108040103040b200b0700c010060345240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 796567877 1250 796566627 796566677
    0x120501050a0f051c050f0607080f151011100204210519081b03070606060f0e01050d06030b040c03211710170f0c0d1e0f020d0b06011b050706 62
    0x3215201d06c00010034042c801243c03c130b004003010780313a958603515607082da10b0044400311040c0080d5000d0440c0580c4924140d158500d40e1034503824a060002d02c0709010b20700b011075950100345840c0d0002020041c00c401c02d01c804050140c1e000840140d06415903900362200129001c2c0110019040d40304018840480d0482e0018107201c0c40300418100d204180c90303201e800a090943d491031074030400107600ca010b02e490a815007004c6d50b410b00c010300d1010040d55580c100f44681544507036140170200c0090400f40744640074070302440c00c08e9502883d520308026144003410388094080b41041c400c400080d0000820442c103d0340404264150390b40a400360304845541c1c3c81271402410308803a0300002c84010801c15a0700080a00b66180880c005047c004840030b9460002d16140c0309014003520f005200710300c203250610400c13204c0039415158001452441d07075031a0694048100d2000c0c001c0c11340e00a1401030001944113203031016640b541c2c8403181c80789058403805061224041044100c0086d0240e41d070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 796569127 1250 796567877 796567883
    0x2090303040e150402192606210303252303090f0604061a090c03061011010c0f0305070c020f100905041b0206060108040b07140712120501050a0f051c 66
    0x151514043e413500780d07021b5004030404005c2010071070b0f0541203c501c600c6c3e10642d2000e8420301c1b90349465600a01406004141c0080b00111070400c0b4042101402c2c0001c50080156851984818044c51940711001ca000201102030007101d0702c07002142840b03100200300b2280d440400315100d50b11804201d05042c80c00074020010b0050344100300c1040300540c0041d8585802007114812030541405000c0c007000e0544041c00c0522042c000102c2514204170300c02007164442c9401e010080c1584c44031401d41d80700d4030304034001c111407891081042d98140b00310742e4012072a140824a00030140c0220f82c540b045000c42c94010b0b108000c40341c4405014500d5070740282005002040012440440318141694403181e49005000e4600070803070540c0f0401040317000d03d4000021500a48480e50150307101c0640c03015034140c4035030601820000c2240c07290f86082d5419983c8401007604412507012040380d1058000500c20548c20b0f4080c843d40a540303070403905513641074410342c1c40004171394940d801d1280303100402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 796570377 1250 796569127 796569131
    0xc03050f010f060902090102030f0703020f06071e0806010e0f0406051005090a090504030f0302030a060b07050303090609010c020d03050604020d09080a0f17070e0a090c050a021002090303040e1504 86
    0x41408540c055000c22a0552220700c104001515001942c05900c100c810050051b071040c010b850701046100000c00c0064460300490710054002c001c9a03041c088200c500d80003140d503242581c56000c0c504184100000002e02e0641e160340342641c0080c1203421503003007541c014510a088001981c86a52248018040007085c0e240b041500b503030000c00030380c00050340d540128600702c000507a5025902815002d00c3d45925000036603450144128000c0d04000c00000f5401e4a5070000140224501d0090a03651b014101440d9a4076003044058600200a420503140340c0c0f50143c00f452059010560b14400307080f80c60007052980300e036000074029000c2c5280410745e41c0e103025111400c20840000600c894522030312803401d09110b0034002d8071404500b2000e1041e1403083e1000412407841054203040d0401b0040400c042513031034031b03c50303401c5942c020142d4010036000181150919010011104095010941503140c04050404a900e80c055480341c2d14082e175040c0086907468030300c1c00712500340e87d00207001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 796571627 1250 796570377 796570393
    0x3110a09170f070b0a02150402090c0c010f060620070b03012c0a0b1806011d06070b10050418050304090b030f030d02040513090b1503010207020a230105030709120c0305 74
    0x14800241d0300921080f1702500c1050b401485403d0750440d0244656002420303500310703958401c50b0f0041076001c000054030039544d03151605521803040c42a8405800c01d55119054242110b00e240c5040140c2d410f804035035401030100f0000b62002108907415219146a030716403e059221030b0102c00b0302c0301e40c0180d03c1581c104003007001e40e042e294844643e80d003045880c1089200c200700aa40c440c88182c54160000381003001f080d9801c4a00000700c030303400d00c002e070a070f910345501602c403901e0701841642c80c1082040f071104100824a8140604540450741c03004036011381005503266960303881180b0038009000c2d224030f0707a00520342d0b007485082a8103006409480e95007001108800081d8014045c5c280b040c81460b080c4c89200340244250314400da4020440c0255840311485045504400c00c180c613030541d000c0100300010713104e01490b40c0040c4201440c102c4180d021030300c64a0101144101c60b1304100e010b01c1004441e9034826000b900710f03804100c0000d1b208665051440114140381c1011300181f21f00d0388 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 796572877 1250 796571627 796571639
    0x1050903071703010e0402010311040305100501050906030c03060f040c1503060603060603050c162315070c0b070f0c0606060806030c010306050333011503110a09170f07 74
    0x2050481e2180000300142080b80d25216420b01080c0540158480003000280065010358041c5480700b9842c2841e0f4205a642d41d2024544820030700701448650301c0f413004004a00300307505401c0e04808201c0107011445003500209607030311002070504125424003c04a03040c0302c46001c1c2a030141079014150302d40b104c0742000c0034003c1c3c04144102e00c006450503100141d0701d4840d2284900501c201d8952500e01a50031519032245400d5107000c1d240d504080e441e08540111903881c0e0750601c0c0801014000c108049925503843c2200100600305010b40b000742c000c00528814095a071000180c10311700d0065000e228202c42001c00008010001d626050740414100d8003d0005031103140e041b021200c61094100045003905c0151040702d0f0950b001220050600749000b601469091001a05c480203103050305c482e100400003270f4456000f031901c5101c00b0100790750600a49100a20705a0043c0c0b501c5810a0000c210101c684aa14403018142c0f00310f03200a0000d12810076650b6881048900f4691198 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 796574127 1250 796572877 796572883
    0x9040b0918100c08010b0a0e0604060201060806241311072307080601091a15031603020418090303021603091d040b07030b0a1208040f090209030607031d010509 70
    0x101d1500150700c02d2410900c140c001c42d015400380007009a450410b1a403900700c3c90343c0540c210280c0c110510000e8001c0850503125178015000924040d400810f2451400d803031141030041c0649140c1c445808544c03e40d41414800e002943d0314441503440807240c981070b042000041004400030200b1381030016204050040300c0e24000d010a6018541c140c803804007001c8140e40f030f580e41c0b25420964004800401c40c481c403c0c0d00400d9240e4020039400702004501c00011605107000303188046100020080c0142e0303111013090400d086010342011450181001005100307072510549240440d07444550b0b01c1c0415200c1d8041e25641c0c055a52150141030036443c02500b82000340c090200300421704034201c0c07015601828020700954000349407640d982c03100c40c8118050655040020b8000542c201d0000e20a280d0030300856840b4000e601850f150307810803550b011208210f5001040e45401403000f40b12544d004501c1c103030000d0749400d00040b81001c0c1d4618940d8101c01c41285c942d035518100800060322004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 796575377 1250 796574127 796574161
    0xa0504090204030f0c270e010902060d050106081012060504030507240e0102180d05031908060103180317041704060306090e0f060f132a15050901030209040b09 70
    0x2417002420b0f031600c0c1d07003064141030140601030070141842da42c400c2d070021840c0d1041810540c0013001241480c80c940125011754050580000d034590b0300e80040188592007140300e50040220101110901d14054078280c2800080c1c101a2800742c0d00e038003080404d4000c1086403100c1e036110072005110f9142404404c0207051505c40c1074500c905110601a030701406108039080309120110450045004409101001c02e54920849003440f040040801c03080b85004202c010300031590b03078000355161010004003a141c68111002c0e41d048a4036244d80081d804c440c04050b2160b810190020695843c1440b01d405030301c012a1700c4804d000010040740035035042d00900300303442071131409002c104c104880440d40d8010802c07040044d5000301c404501780b1804500040e4000f100111000302101c0700d605c60b604880c0d480e00a19840c0a074040e15140c3e0b00c029505528002c01e554201071003980500403024003284175070000e19042540c00200103070203555507400310901600241c80f101881c03070144c0b001e00f204105 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 796576627 1250 796575377 796575383
    0x90903030e0c060f0f070203120d06080624041d03300c072109030213050907090b0d0f05010920030a15230a2f0a0504090204030f 57
    0x202607040d00c0c00720001445403440d44010304607030f16107081d201030a1010740042c1c4078034a80042c03c2000c040036a800b0842c0700e240d808012800c540e100351000c03020040f10300e10384c0480d08a0704400d0800405000c0507408403200d0b452001480121551000001d000f407410308190300c801074220101ca01030000001c060030b041c10181c5802c480f5086000c40c00e282c0742044020500b5018081c00c0011420380c80c07031001d014280c0c07203141c00c3c000c4910f0250003002c001faa0811100c00203000c0903030800c00d5103084680c1a01070480e50314200007506040d42416201c0f007840c01110f514603114a00705200707854408504003225006007400d91040700c40e16080e8081c0c0002c44c000d03150511100007240c0303115801450440e000c00b000f0000c0503400103623038460012809440046040e182d45000c411326003000c0e100d4282c46808091007150091030105019811500012035181915840345106498052112000ba540260008415482d80160349040b0303240d1040380c200b502094004900042007000c0980060f140b184 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 796577877 1250 796576627 796576631
    0x19110f250803100905240d0602070b060a0518011703040e040503032a0405131b0806011b03090b031f060203070c060807020c092a030406052503020d0b0a09090303 71
    0x244e42d203c1e240a59209440101d452524801d13003640100548812101d0801d000e00302800340403042c2c85500880c0c200e4034041c1da042040d02c04001c014640860850041c14084400403480d054804040e4000a014000c1c555818a840071350091035604200381c4000b4820380a01d04124901850460303140d40003550300001c5600d1000001d929040505954407000c1100209141030601d05403c005584c01070704419020076654607819036800b8a540a0b00c01c0006240d11350303ca49041035000100100c08811404400e004d0f00c50204000a510883c0781c803c4580043d04240c603a11a0720300d02240390000011040707400c024484c000750f001d40220140c149036000d206d4944020743d9954007580c050404454010060f0000300d08500c03103261803415150400342400030f081003107401c04001042070460040107500308101108000c100507650146a5005004501c800c41c0f0001080d01002d8402c400c60302d050071b068002c0b490419101d00d0b58440d900b42040207200c402c4103035403049010018140300901b900068 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 796579127 1250 796577877 796577879
    0x506030c03011505150a0518061e03090c2209020f03030703021615090b07050705100504180212161106010e07081806011205030409060b0319110f25080310 68
    0x50417082914075400c41501c485280003e4181403620503032034082915030004050284444501c09000040c61442c02039401a580c3c2c02c103800c500d0710f80340700000001d1080001e580b1140d844904508451881500e2420104140c2401e00c009880d066221502507010b21011603001f040c1940001d40c0418102690074200346c041d25820b150186460007044440801c0200c03004119a1403550000e00409005900381d54002d51540005494007a02c510124000380c000314090014111680d0303010501254013408500e02100c43d0b84851041c04001e200d1000c400d502c806841c1e0180c00b6001900030410910309503002580c4418040710076003020390701e2000007000e07100010a034060b0286083d90b24040c0f007004080b43d03803070100b805103107046107001156580014440000d00201c0c0d401a0405401c952000c1ca4482c034011b85203003078800261000f031108070300b01129030315215405001c0780c0d482c0031055140d541d900000102180040054804e00a52a40c1999950280f10640b405580a00389264000c8e0002d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 796580377 1250 796579127 796579159
    0x30f0213030c080c061605160905060a0f0806060d1b080703061d0a0209090a0501021305040b090c1c020903060405100e1219090b0d0e0106090c120506030c03011505 72
    0x142c44c84c0c0103a5900a801008100d2043c03003100719942680c1d101d04110380c04d00c3e0f00404481044821a844840b00382e031904144a140d242124115018211314180890080e141005590b41c4201c043c00c0b0134003807851106442c0520a1030034980205103282000e072421180e41c1c0320003695a41880c4010790b0f40600d000f00c0c0454124190142060200d41c00c001072500380c1c40f40d004c0005409010b03100707451030711030000c41c1c0000540c20b00213415010f4842140c400307070a00d01000c0c00b003035565043c0c42c02c2c42030849008200e00c02a6030700a451003a20b45850010000d007040380d0080081c490000201da01d4405e00003044200280085c003120a03504000c018404803940401c140e559484000b100e2860300818409280000c1c1440c1548254201d50f00e41000700c0d43c1d480084100683c00b054002d802a600c9001044181e0000d00136007008208411042000008a1200801140c10103040d00f695544400c00305025036401c1210080110005008004014a0f0b20004c4140300701d5200e054085d4504100c40850 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 796581627 1250 796580377 796580383
    0xa15051203040f0909050303070305091f0506030601082a010216081b040213090b0d020d050312090c1c0303112106030708190606080d03020309100e070501030c030f0213030c08 77
    0x81c45c0e500000850458946500c140d001c0c210090074401c161080d0b0100303810b1b0703807100c240308140b0941c482c400040d60705019042c9420444140c03c01312070f0303600c58428080603900a4a07060701c0114001450035040e60f0b01c40c0100d00f080c0088115035032900202c5000f00304401d011072010070700e003415810f030310507201010180002d901440e100306118400129040055004030380000c03041c48001041d1001c0081c15600280d254513280b20251020751000c40d410700e4105c4207811480d007044202c0014044800b0000c0021086121207c1c00103200c45000b03588ca04142c040c0c2c0040800d800d903032a040752205d40c0c01c0201402640c0c0e8241c1703010000381c09001716086080204041003034611030005007110307411034920020a503d20322000c803403841e99400c0000d0b40c50380a11140900401955001d07969043c2840c99600c1c182c0c9000408c0000c61130600c1380940d6490000301601120420300300460310f0002040260014807030350100012440c000609a40004c0d6251841c1064034440c4010900480c0ca0b4074409036 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 796582733 1106 796581627 796581641
    0x9060306020c10020403021005070201050d06060e101b030c0503070c03060b040b0913061a060c070f061b06110702031524090a15051203040f09 63
    0x228600306000f0315900700d030a0302e41542014219000554180c0494201c10240b05001900c2002c41e4099810740d400c5034540c420411030b1a82c1c5a4015041da1300b141ca06a101d0112803240d180410b00454030b41405011032400710b08120a03e69060301c80118003c0181c80511080c072100380003c0035181003401851042c0e4000c144d0300000303410720047e1007400780a00c0c860820f0038108241350143e214040a41d9400c48408242c503680004100b101280410700103400c2000050001c60405001030010101c903291003440c4162551520125640c0d00e2500b24840c0d1003a034060013402290740c54020780944102881542d1405003e503001a203401090790b04a0100c003060010401c1480d2840494082000c150031003082c0e44940d0702c00101e10500041054180654030785a81202000c610070701d13000303400c003c3c0c207006440401100c00d0350b417504144580340088604c490b01013415003090103242 = true := by decide +kernel

theorem cover : BRFrame.Cov 796402877 796582733 := by
  have h0 := BRFrame.cov_init 796402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 796402877 ≤ n) (h2 : n < 796582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
