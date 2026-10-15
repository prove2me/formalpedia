-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5337
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:32:20.328063+00:00
-- url     : https://prove2.me/submissions/45940d47-79cd-4564-98b9-29dbc19f8ee6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 959712230 ≤ n < 959892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 959713480 1250 959712230 959712241
    0x120414120705010203040201120b010c0201121d0f0601080d1e0e190306050c130608090309060f0301060e01090305100b04090f03030e0d0f0f1b020d03210e06130218 72
    0x54010718006c5100740c0300d10b2400e401c464201c500310760340c00000390b0000c1c040150384000343d4010170f030041020b0601000420740020011814480000090801015900c01d40010501c03040a000341400341944001900c40c00c0f0707800c440201550f06c031000b032a9201081880c800c132614054030b003162601074081c1c030141c0d02d005000700c203520854541c4019140a4203000c0010071006103801280d082400d80181e4a03001400e20740c0c11504440014840c50350340c07104001c0121b031996183d02400110240d00d046503501d6044c401c1c003c0020b03103445400350500003402c00070302c0041c0c0003191143c80009040c900240400480001901806e11b022002e40b410840d262072006050b850b401501c400c41e681d4007142c10300d0031a40d00440d9200c0d111142c0200107a0386122230360800b0701c04c1c03000c0c0c05400d100e440b00c0da81c466800c2e0002401d220406c48200d004c540c1000811105c820031803001e001302440700c00c040083d8010101c1050719100010705000102091140b08070840d61904a60400c94103141c00c07c003e245045c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 959714730 1250 959713480 959713483
    0x40e10050a06050f18100b07080a0f0e0f0907020109021309050c1504060806181006020d0311030402060904020708040308091e031b0402310605120414120705 69
    0x64400c000200d0501d680860b403130408070888950464041d004000800301c00608040c280b002a2589603198829030700068000072000c040c207071050051401d17660b40d078500341010700144414010b81d410300c0400403004500f5500d07000c3c020004441503803c40d000b0360b03405408031b00405410380300951203130550840c4024425690701c004000b512903802c4031803032442402040090b078005815030120003000c100c00c0c0902e51080348c0054000754050220b10160300746020450708108100c5213145004a1500108120b0b44d04000001090b80b060604100c000203105500b0307540c3c0700041004e4001c500c00615840b6a407030780e604441596420210340c0c0d403203640303070701d00a080c991085040920412080100c44070300c004001841008000003401041703c030904c0c0080c2d00e00899025000c5501070f0742800300c2254000000c051108003c0e104000028807011a01d1048041c000f81e0002d1041100038070175034144031204503032507800a030091740c07101c0306001288500c1c0c640388400700c10706450903003c9941000c2240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 959715980 1250 959714730 959714741
    0xd110c0106090f05010608010e130611030f0a050106050f040e0612241b18150a0327050601121407260604030210020a03060f0f0e0c040e070e040e10 65
    0xf03420801c0c40581d0341c0d40d42c00c41d0600c3c002c9c0500309140300246c0203e0495100000f01924140c1710341d81c0800c249e80b5030305103000c0d1600f0445400c07400841c11010483c0365240d074811031380034100504009040c40b25500c100c0ba0140114098884041001408100c056491480070001c0b0002041260360a070800c0041e5041b501202e0145411700141c0c0b030201c2c1c0f0f4607404868040502c0703d074104e4641801d4543c120851140c106003a03040d003000102c2c03909014521650010400351800d5100400d0030f203500b0440000d03c105600c00b006002075100010350000d2804904507045034049200900e068059040041e60102a0070503c0da552044003400203000a600d100c880441d111812052901d51910804903241d8408840060050b0400401b104848aa6a01030f20029103e1b280001e15680c840d814000d07071403016080322404074030040b000c01030060610701195003c02260601c500b040d207080c030f40996040000c0c040b801070102600503000c194603158482c1c5160200354081352044900c2c890403100900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 959717230 1250 959715980 959716001
    0x1f030e12030106030c0f050a02100c0c0611250f0212120403150f09030212030c04030b010e06030105060109030f0f021f110c0f0d020625052a060d110c010609 69
    0x254010400071a43e4050008e880040d602d5402a101c0740100d07600c41c000400b40d1314128010f101b0740c1d1601e40040341151184a004030040001036640324060001002d03004040e909462982c131140500100042c03504a89a070640c1d415176025884001c0c1e11605410680c1c1d0101e01c500c542008600082800a68165074942e0f1581d03400c01c100301e40d480c3e01c80c00141c0744180070180c05640610ba9561012405a00039039201c80144581e034103044d1241d4942400810070b910840c03100c05000207210302442c00f8440d40707401c00d0013424880403c501d10360b80d54002b103503501000340900b0381d8200103034255112014035180d87d4115041c51100042450400f41c44a140c10654514a01c1000005011030070410011014010024001d24502505908004459000400c880c1001248219424004011450f0700f030b07407184500098120701d0034000b141005403812110090004c513a003150040d06807584012030b0519641910701081850f42103c014000d44140c240c4408075610308040080c080320180d00200c41e02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 959718480 1250 959717230 959717237
    0x6010302011404080604032001360b0a0e0a0b0403020f0d080c0d051008030f04060e04051b03060f030d0c03091428030b0403031a1f030e12030106030c 66
    0xb580341e140d1104041c040c50150650583c03003400810086406000c180b4885200b400e2039601c1a80c4600790039007503c1140e20a040401d4082c00081c40410100c0c400ba008007941c40c03e06140c00c4a140c0394010150b2000d401d1081c41503850b10f40704802030080c4106100190050396100082c205464025a0703841c0b840e8900f1000d00510414040441c411301402c3c1c068948100b2140c1050300c40084d00f801050301411109148140c01000110517000303002400036410783d010284d0b100c1d1302e004c5001d0102d070340c2203900c41e04c201d10b010104540b40056000580f0001500e0b102181c50360360380380114080a1503a0481903261042041d03400c4c4403603006640701166446662525400d56650a202100d00c114548030b070351081d090b081207407040140c25803c410100382860074104507a62a22490a2030340182c0341900042d4480002d18880da45900c030a1482d80403d60f0f9070141c0c1c410000c0200498260000d4203020581c40743d0f144140c2440030072150118082c841055035a80d6503841c2c024005000480460010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 959719730 1250 959718480 959718497
    0x1812031106040507170a1b0e0a180f11090109050a0e1b0f18090a0c120510020906090a141002060c0904021c0509250b0f090307170601030201 62
    0x1500010076614001c0768081d000f0242d580c2400b2170012120602c50840259104508411000c0307401a4155a5500c1c050707090408601c0c01c0c001d1090900f0001000c49040d142015946d030465103205502200180e08140f410808680c03600d0041d044109000b4442d0b031103400c1000200703298629501030342c06001c0c54103040003480181d0200d291070300d403980c2003003000304100040501ca070300b440c0040d40004000140401451680c0d024807c0d08041c06840013841030744418450010002c2c8600c052020f0200301340d40004054072039480315a90000140e0f1010a1a0082665210744c0c60b4141612040f803001810703125036a49554000801c95001c81c1090712401042c00510034050020800500030031032050700700d00e04100c0c2c000f4000a54800d0030070415003c1855290160440b881c0701c5c05005079242400f900f40c0707150304e001811400f8104089003e01c04031100c4200b181c4100c01007165000d180140c02c8030b4179518107a000034103100103030341310400742d40310070140c86070034480810414141e078400d0301e41c07806 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 959720980 1250 959719730 959719757
    0xb0609030a0c0503060a290301230f01050a180f0e0a0312140105130c0c0f080a080c03010b0403030309050f061015035f090a0507030b07181203 63
    0x6a40c1072200c4e002001160000d0111031001f01d034121901440b006e0004036610745104050004d480c0111041c810480022080c00301c11800d00070700c6c5004000844580041606250400d86410700d00030000c1c4000f50307921342440f600c403442c0e04100020402d140c180d42d80076000e1f090142010955140c00300415107415103500224040c3c1403014141c0350060510782d020f10000c4030040060050720009414030000d241c80030f0025520301d00c1c0c5043c1e144110740640d01c03102803440250600c04007414002c8058018030050225034130400a480481e078252401086c00d44460620717074180491070100c503245014840c100102c88910745c80802c200e4400d003650400c000280c0d10200c003140c0824120003c0b05501c55150166241c82070400392050a840f161940c03d42c6080c00c0e481407449240b107039980c040e84160f004031511130b0601280b075804154140985000c5120395100303512000726000044c01000c0b501c004c122824400e000e01804860003400c488500d6407100420b0712020841c000460016641000003075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 959722230 1250 959720980 959721001
    0xc0e130908071205042103081003031b02060415031e020a0807110f06040308150103140f0415020c0115050402090108010b090402160c05030d0816030b0609030a0c050306 74
    0x102100c0c1c001c26440e00303280c035503901e00e05124007060200c01084401e01001c030342c0050144c145031480640d00d001803410261460301600e08440144484080041480100040b07500111000e03028009151100101003442c0b002407200e0083d47c1114030b4080c030200000c1001e41e0198460800718a048005c1c0c01c506445500b04011391081c502d4000024410700b0105d685a40a19003810600640364190303107003282450499407800e00200c4081d0005003e000c1482005009074203a0070a83d0740038a4103001d00b032940d551000302e2035006400964408402c60005003800000034855085c5c04c1811400c0d9500d040f4a43c07410f0217443d4801d02d044156240d07080c0080c0f035141c28802c075034200b581a11000010384c68010314050b941c000e00043c0da00f164003044040c000050b0780142d05105440381495100382d6040200b803600e001c0d00143e014041c40342401c00d1215110030300c05152907001030b40c40d02040c2c1c01d01050204400e40030f00840c443d050f1040007800c01c00c100d50310080d030003550403c2d82160a0703555050841d6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 959723480 1250 959722230 959722241
    0xe0d09050a0305121303081206120d0503010b07060e0d0c050105180c040f1b091508090a110d02100512060102160911120108060103060c080708011203120c0e13 70
    0x2442640020b03c41d58480c06010007810480003124005c1040c1c50340c9485281203a4000c008403042d03441a0020010546001e007114503596104030018900c2c0001030b60080c04902c4180103046036001d01003078100401c80356801003c440b41c5040280c0b008144c0c156000b4084142c0340c0000c031440e500f0400000e40d641c04540303605600d44c0b10034004001d040490401d200080034802c5034145802d0300c0e040b40f082d8424001c884881042c14943e07850001d14904450b0300050b001c510300c05d0007045140703011f015010000040141d4107541101c07016900d00c441800146030581c414400a402403511043c001426070002c5c01703481c8104182058007030660300c441c0120303141c110300c2600b0092580d1008080c01000c10704c0d070201141842c2090340b28075140254a8940c0035141c242c0c48615141d00c41401401048a140a07101c486410b60038501014186a11f01418170b8505006d03140319a01e951704902c041c18450b035a600401c0000c00c408002030401004000c1440f0249404180101c00315031541e440f140f8188100d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 959724730 1250 959723480 959723483
    0xf0d080915010519030501110a030e01091212060e04060903080907030b01260f0705130c05120705190203130e04050a060e0a1b050405060f0307030b090a060e0d09050a03 74
    0x1d22026801c142c2081304112410000d542c0f500128000030000030024841c640c140c0a9030640b450b191400c0c0c0e0740040580350000a10301441e41890741030303030008110502c500207000c0ba5060010942c4c2110300030800400d011351010301d9075a040d80a0000380b1049911044078903000395075898907a62105450340d92070103a484002c180030b000c900108001d80611900b58800d140c0e040704080c02c241180303011032914804c00d100203190340142000300241d1910100b400c0c00782c801c0e02e50510502104030800703400d81c011121038220f51020040020440d610410440d81c1c403514580c80ea00d40204c0b10301c0029502c1c0c002420211103031300b009070003107644c1c0036064a2074400c0d45d00c01d0003807403400403959803000035005c2d94006001a104e158038480014282100ea91420750100414950702807501c010401591009009180140d2110704400402c2c0c078007141040599130040c080f81025103c1250191070103092010140001b031400c280d07502082c5000c070307038140203e415a0320310041c140c13240300300510f60038140700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 959725980 1250 959724730 959724763
    0x82502010806151605060a1d120a0905040212150301110d0e0f100c02010b0603090a030f02120f0301030c0503031606150f0602030909010602010b0607060b040902030f0d0809 76
    0xc00074036044040c20703e01090f07125041d040c0850383e908146409420b810072103507030308800200000300d081031085540300c43c00a000420040401c480440c1c44091719100c3d030b10340040000f43c3c081c0302030048500304010b10001d0000c55445a01e030320401c2c2146000d03151103002d400320350702804003442c0501aa40b122031070001c07024900103580350a040289901c110000c000d001d03500c00d247c00c4a80500160000d1000d03040e0100d0401c60114009084404c030000c0f0074812041841481540c001c00290140202d6244c1400803a1010744a4141e01c2c0000100040054500015503249258400d4026504982c0b00c3c000c0540816141e00806449000391400d0b441503c0000242002049458110f105801512207079200b08586904860728454241d4018401582c400640701e8400c0c240224950700406580c0b00800c8080032400c0000c0d618440e601e000780c41a500c490b141d4050395140d600006000c0c0d401006c840c9103810320380100e40c5030084041034801041461000400e22a800704010051b500480c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 959727230 1250 959725980 959725997
    0x18010201053c090604050c1c080309151303081006170a09050a060212370f020d1b05090d0b04030c0b3d09090206070503030408250201 59
    0x1040c00040381000340c120002002e60190140340308402c0ba40301e40921910b0010b02a03525103070500501c0e000090321114041c1c019040720580078000a010413480c0da6001c034010342d03241ca50000b858035110071000308a0010031900d05101d071848140282c1000180300f52181c2e1060796610141001211443c4100004103100c0007401c0020340740345250590100300b840001549000544a60707181071107808049a0701a40000c041c3c055005129030240e10120000c4140c41ca661000d8001407c2e1110481501049424a4022541e00d605030010b1880100eaa44115240d14084410b840a0080074000e03011060002280314417092103041240e40d4004d000e0051a07445580d5620380c080b04400900c190308000301c0d82d00d0040024080e1310440c0c0215514200b0b07040c280710640c41c810150742007215416800b044416001e0590010a00c0d4400305d40182800261030081400401c2451150b4980184180800000c100400c04184094035000481100704185099402a0741e041004802c0c0068003161780407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 959728480 1250 959727230 959727271
    0x100c050f03011208040b0723010207380a020d0b011d1003021b0c0f01020a050c151204030503070336060f020f0403050c0d120507031e051801020105 65
    0xf4100c400c4440d1082043c545050381d00c10f8140c1c420303004414100d691000c81c06802c2c0d0300c10314401f0070b20384440c001e0000b1841c1107510350301e0405803103900541070200c0540b040843e044c0224422001da001c014038400c46118505202850000d6001400a0101614040300817006510400d04100f840d0b0b44c0b40420701c240061042000002d0303405031005010150200203003514400083c6206001c803908a00170480500c404040120328103a0000c094110341c005298900400e90000f105074029170280c2d9990207480ca010003102c100d101d034403c01c0700300d80111403c0c00109907100c0001d61050550780c3d420044d540303031036810700c0b46125503007420000751078884441d80d101c1c40b2028003180d006104110020304d514001d8085420317600418080c007041c503000308040060103028041703001034100807242c07030800c180c3c0d40e501c01d205001d041ca10b6000304013010402000701400341e204058415880c2103c0d03540c0e03d00c0440010a146e202c07540e41d000150010301942580d50050003424050542c41d00394203641c20300b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 959729730 1250 959728480 959728499
    0x7020c09040b10050d08070201030c14041703040503011820010c03050a030e100903030b19031e08040f081c0e100c02090a02030708091f020a031409100c050f0301 71
    0x2412007181c1c070158031030009040e17541e03101042e80075101c0c1c4040c944036203042c0000341c02c944000a58009000f5500c07550740000100400300c4094034900d4100540c1c00f40c10035990742c614080c40c0c00541e019840c000b006103280c42d400e1402000c0500c110300943d2000c043c4580c82d401c42940c004814041040c2d1455440024024000f820a19565140c00182e814038000800c0c9010320303403000308000c240d4900c01c40b810b0581c5402041e159460503107103090711072001410307004030480b40d110242c03010818800e84a006600090554407180c1c1000007a41c8403510748840c0c07100c50415100710032041c441c07401d00c42e01540d81c2c4000c203007000c902c40d2103101d4101010800c2c020000e06a07c100000c1000c0c4105540042e92204041c90042c1080342c00182c0703d182c5548064042200030342411104d81c04500d581d000d6200a4016981948003483c01680712078803003900740d0181030340300311920007020f22004000800d8030004602a850301d14a9042c01107078206042038807148125100003020410800c01888103111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 959730980 1250 959729730 959729753
    0x306031504030f020d08040503090d05160803040e130b0708070c05070f06090503120d02070c17100f2309030f13060f032c120711030607020c0904 64
    0x405015500e544a0a04980022050840341100420042c00c1d00c0562079034100f0000b0011000b508201d8101c0c24191692940c0340101c62100b40309058146250080190511802403607003240003461100c00d8a4000d0301303460b034006006800586a090000981d25201d200c040e403907094020701070400d20703155000102c1d01d07442c3c000c0000c0180501c805102c000a2820000807006100303c0c9041c80005003004402000080c075580107900c43e60110000d0000818003804540c03401c880c103080143e40703240a140200050a4035481f90003030901d003030b03040280100c005c9116a100341c51407404101c0803c01d01b60180480b200c0c9070000000012240d4010040700c18aa04290003114180840b420140c520301c04000980c0301280036028800d0180c000c10440740c00110304050056141000c3c000b00c4440c214181c43e19a40096810030541224034071b0f41d4003041030109120310580d16400750b40c2c1c3c00c66410070144542103001c843d070282c4102c00c0000e807039030300c0401c2c11070140314014440003441e280ca45035007907282d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 959732230 1250 959730980 959730991
    0x504060b03030d090507060e01022a060d050a0b01230304140a262503120509010204050f0f01020a0821010303120e150712020c0d1107060f0507060203 66
    0xd6980c0c50000c15980d040002d8281e41c800128082040d50700d40c0380460400700703540c1c0301005200e881c14000040f40c2e004645034082118401b1081c4190b0041c0b4105004040945c600980058001804861048603500410700c10314450342d042c4400c00c2d01038011185044002c0281e108805002c0242090940e49030081d500035004001c803c00f48260380c1c582c2824040c4024003114180406492100d040741401000c80c3c011500383c17006410807140c10300443e5145003545030f080582c00f000203070200b05401107589440c08820301104001516141000c00d000b5881406250310603564807003010302d2843c003d82c20700306007407040e8050a807505599488200b0750700001004500580c42c040700d120b1500e0b800c5807070380c001d40c001d40c1d950034030039450401803049810f002c81d0700040ba0010241e28103848a42500d05410080501c4e000300c02c41c1030842044c000f8002d1607003141550155101c0650504e921003494201102248152080700d40d55500c00e5882d130841c6c0c00428042034003840000049940c9501855014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 959733480 1250 959732230 959732243
    0xa0c0303051213021e01170a020705060c13050d1a07110709090206090607030903060c1218050618010f020313020a0506040602100f0b090a0905100603020603040b090c03191e0b0a0504 80
    0x1210f5507c02c07103000c0d001c884846d030096012610105200c1e00300010b5820002080010781742818100c0c41c10b850071241d0180e140a20701e650201d001b0402201000f4002d4001d041e40c2005074201a14000c1844d104150303000c10310b108405011510510034454804801e900030540e500e020301c090144812074100e21010342c1400101c00001001c6807a600560100340d440e0381c1d803060148180881001103546280b240050702458000300d0300007038400203030241c101c103c16901c94030b082c240702c0050b405000341c25240d0319403900100034440120f04440010799058400c40320150f010307440e141823008901803403180100507030000c012210456405d5205810301f0500c0e2101068200050001c01c002950950f02c5c0c0702819039800d944014000305115aa44400300204180001d91030340c0c00055250001800c054811015080810030240d010000808266005010749603800c0044003400921000c0070350603620000a40000081518810f180c6268542d0001c0c2d0714500b03440e254407060080000030310403180d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 959734730 1250 959733480 959733497
    0x3110c1801181d01020408010c1704230f010911060a0f180e0c1c0b0d06051807030c0f0801060b0324041505030115051008090a0c0303051213021e01 65
    0x1001040c3e5511000501d40002580d01d074a0708040c01d0840700601000801c2280c0000305158465401c0c9070250400e4100d403c5c404988404000d0407003a54031200040028450040c40417140501034200380804d82c0076400c00036140745084140440c51280400040016124aa900e140580500000740c03007001d111020030049522030900a00f48081a118070104030300c0850b403c46040c0a0205900100004c02000d20001d1040f1010610a2001c0ba80c01802d590311030000500d143c0203c0007408102d0340e4241192004c540e6070400c42041c003090f00940d020b8503010200420b6a5505010f840c0441c1d00c003002040c034503515a00c8030086850250030341030340c10308007450030380d110754035402201456980d1181f840c0301c1c41c1c40c110400d801c4860b540702c2d060800a020108200031390714680d0201d00c10f0154241001c95941d2094040c1c185041610000d000008030880030061562040c0500361158035041e01003219200d040002e61004030b841402076210b6080f000a100501e40c03114002175500c018100443d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 959735980 1250 959734730 959734751
    0x60b0612160e0907031d0703020a121b060e011404050306010608130b0f010620100e030d09060c08090a050705010f050d0e0c0306070503010326090d03110c180118 71
    0x180078090700c000000a4660b8141c2c41952001b003081c0000350700c00e200610910f4907650100d0808401c13481500141e054480030b100620444c920b04000c0d0302c6851048403000c6c0d86440c0c002d0701404442125500080600b10036500d4501340c501180e0a48800a009000c5a0304e00724003100c0000e4020108200000108004000507102d501c11601505000d0001c108a44c14190000d01d5900442100a401824202800410308010460b0340c000c501c8a2008903d0b9205401c229156100d01d600c010100c17481c001045041c00046e90150a80d01c0702507540c0505a1a1a40e180e03a0300e1542440242c40c1c1c0c1c000c2c0c54100720750741c000c40090191202509000d030401651515450894002040200940e00400c0d0380307076501e00c0c05200d60356020007141002030965040d03841c3d03034201c66803551000b031211098024842002420310203071800304100800800c401e00141c500100041820503001c02584205c00386d248051800003142d40c144000b4919014031a8680000c2c0540081401005400305da0307110000ca1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 959737230 1250 959735980 959735989
    0x80f0706111209060703020a1d011403090a03170f06100e0d08091315060f0504030b2d0115200a05151b07081c0e0703060b0612160e 58
    0x4154900c10a0380c01c2c19103800351070181003035802400e150400d031040102289aa40001d01002d9105549821111400c00c400050f920311111400002170134501104204840c1c500007070b400703207052081d5104000222059007900041d107042e9104050200048001030f91802c2c01c0003401503800407850004566107241000c00c005403203040050b501034500240d04012400c110311464164424a0000c0200303250740c0e5030813913820445003d00b0003000701d203140700c0945134803804c2a10081c5800c040354280c5424a6070505502c11440881000040c401f01031500c8030340c03214500e15049506095442c90070100e901d03021071350340c01901a40784c4541c50001e07400844050400c000f4150501c80c400400281c40000308441c1c00031002010102d1455031800c41c60880b03a031100584001c154014041c40e00c0f4208650402050781c0119038450002e442c0c54100d010705140090b0501c02c032402a0003c01c4180f20800c00e214540c4200300ea02070030100c0290125811403e181c080d440c40000a14101032591103040006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 959738480 1250 959737230 959737237
    0x110f09070207080c10170901111801020115080d0e0613031a0a050c07080c0118061e02070c170703060f060501080702160311210a06060b07080f070611 66
    0xa005074486681800300c50740402100e105450700300d8076a403040c04901c000608000300ba107569140407401b040840c1d0044025008127104c88043d5810607226020130251408520040e003516005609011a1040069507a5000410780d07001601900d001c2400110984042c40906600303600100204043d0041c4d0640d5001c00c00a5031144e134a19030a114050740800c00840060050003c062600040c804036407000030071568074682c42643c454440c860300007468010058042002542110307d07107458100401588806440c3c072100c008102041d042181c502e089009000c0018801401450305024a034480080480403090081c2100c900e42c0e10780d42d41c041607815020190003100c1e12080c0911641d80c00a00d0300380d0117520391004060540424030151034524a80c40060042d07500c0003044050380d11001c0c012501c1b040a40c4100000700000c0450b143d641e284a003007500c509181a60200300118200111018140c01c24400c500b44111551013081960180e84101c039a15900c1e0380041e052908800030307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 959739730 1250 959738480 959738491
    0x40c0e0a080307061d07061209060e0604050115230d1b03120305070519030b030a0c03170304020d03050310030c17060901050601200f07030c06140403020d110f09 71
    0x70b1921070505152160594000760400c03189130405183c00310402d0740000e031400850304545810312010902100000c018905410060405428846a2001c400001075010f00403807051000f0402c0070740c2e10301901d80210190260384400c2c881200c001003010565140050121002421100113141d950341e2441d542d101c00b51269903202c4068030400902410b214400a50411828188a02d03d000c0307500515602c20050340004207000e031600d150880c0c0c401d80c008541c007240030f402c1340c100446a081c466201149444110741402c81c0c0000d85028500c00c3d82078034052503000c0e00020448049030f5003541e19030002002c0c03140c101c202c180008040742031010281c00074600700419890303100c1d52070079050070841e0060440c1e20300d0781020180000b80c2d91040c0340b501241e446170340c0b50b0051f40603503551074101a2a511640700304c3c41801c8001c000d1008030084402120710b16260100c1c074441111560f5a00d014070302c0040e40c80f81e1034061250105070300a003c00031289008000b50300d100506c070001502200103841 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 959740980 1250 959739730 959739733
    0xe0c0f16050106060309020f09040606080f01150801540212161806030602030702030919150302031f0b0d0b010804050a030e060706180c170c040c0e0a08 67
    0x5036402804802c0c80707000042c0c0712524007441403585a03000f14441d0100854103070301458407140054140a5582d0108004d0b22091058519251249090a0103403003c6285e004031a44100d00000394218144611980d4042c082c0344000c0540d0a000ca03503c0d050819405040d4140f011445505a0030030100380c04281200f480d140a500b4910f40180012803c603041340c0c404584c410010702141d003542911481c111140c180071002010100140c2c0c4014209641c070042485001000b40010f4a03004000380c11a61400c0d07640c1000000b041c48020301440c141c1c4207103410500030b811104403007482600110703445403400a000894030b0000805403c0c0d008103502400700348101144501080c0c0c1c07240a01c42d0281400d28100b6501d060603161691030b03c07a030890050921200028180381c0303071220702c161140143c0001041100c05c240076400314500d130f2910021a8031001e100c10105107990351020302d4108690709001060342d5154841800300600b911031203a824055184031950311a900d120000c409090f42c0c20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 959742230 1250 959740980 959741017
    0xa1e05070614090a0204020a0c0b0103290f0c03040606050d1505010b07150c020a0b0411030127141606030e0c06040b0307180902030c0306011e090e0c0f 67
    0x40810884040d00ca82c61009440d92081c402e07030307041c005019032000e0f03012640140d4419040c0130a0307501411460000341780040045c00001408034020001210084e0418040c000c50100ba0b0101100d00c0c04503210201d541910001c61882c848001c09194401d10410700060310544540008a943c50002401c8408404210b100803290540f0b0058030b0060030340095050034400d05650300030003440402030480641d6900c03070448035040e01c00c00c281602e0507007050b046d15060502e0f050180200703c40c4a801800b0350b00708a1400c0300c01c0690714002c0809000309545a01110072907841e21004080c5040100c00e921800d00000c4141c0c1d9400b080900030038403510b0000e080d04c50b11754040d08105c00c201c1c0c00783c0b007810240b10400081c1c1c0300c1341c21603a12012520707000030a81384402d082e80144c181c0f50000c4007001c0c03002c01004404401200158000c1031309894101540c1055506483c074010000358030800240c020808025068010400d141c103e42c1003803049080c40321400000c0c0c3c06030464542d8044030030000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 959743480 1250 959742230 959742233
    0x110c03070c151407050c0a060203070b0c0708040e07031b05040e060f210a051e01150f060f03110c0703140d1e05071a01140a0503120a1e0507 62
    0x582045008116100b003141a40c5401c0c60050200c1c00c80050100641d81d0000d094002c00c5000d00202004060091029000e40d4071014001d50325007080000300c0b52011004040343c1103100007000d5404080d884410185450300f030121801072ba81001c0c100d681850745031201b011103055040091a451441130303075500c0d252890020f2040d101880034000300e002d450103c4c001d981d591201c01030343c04410307103000751400c60360203481d03070140340411516011b000c0703001d8401a961001c0e4a01c400441c1500224000d0048118a400c3d0711104041440b801150002c80d15040100ea402200c2454031000c5d00d080001d43c205080b092040c9030340c0182155141500284010710400c8200c500480f4031500400c0204078000700002d010b003405c503400c2030a182c00762981c031503030000b00d2041c6d040740c5106501c84007881040340143da500400355000c1c002c41300f0b0901c02c0700b09000c06003003200050040b81c800a0041c40c1c240851103904501f544074003013203400c12804000d4200303001d500705c0140c0d900008c00d40d103407075940d03050307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 959744730 1250 959743480 959743493
    0x904021e09031b0913021906030516180302010810050d0602041d0405030921030711040e010c0c0209180307030f0f081501121d16060503060d03080901110c0307 70
    0xb0f50b40d5440d0342900701d983c4040a52928400c035540f08082011002d0050814000100021803030722451192a046400200c1c0e000c0d816000140124441c8c01d0f10201c142840320292921006034002103c50b17900c041d800c05c0950302c2542076641002118814406003038492000c90f6010200c0700080c2da440703400081c00c01c00c449244100b000c0091074040302e00d4903800c281e80c44540724801c045c0c10900c290140c0100401b440140e0b1000c40304001c040c422690ba4108038a0010840482c1640c5544280d240040001b00c4c210180036030410f958030780d03986080f4140146e00b003001c2ca00018048805060290448001d01d1100f0001000301074040d4031001c4407040709403801420404c0020108041100d02018811026036000c8000726204c400d090203a190328031007100703400800444202e400d843c2c0b403044000c43c4d04980480c0d0000071a80d8071030001019074941e03605072500d00c0281c03841500407007000443c602003445060025081003271040045181c08000380200d403c1e0b0058602005690000641942000348 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 959745980 1250 959744730 959744743
    0x305070b070201020406050f0304060b1206070306050f0a0b0f07050307030503010f0506040e041e080412020f15030106140904060b030a0f0507080a0b0628121e020904021e0903 77
    0x41c0c1c4020b516060074058001c22502a4141c00c64030210080302042c00c00c4219000880341d03034006415031401c40c1c84688500d0b503038281030392130303002080c60541c0118090402c228070714212400508200705e0f061074481d10020f02d602c003085400c1541d800344551000110240018610203000c3d5607615200d50400714042c2a000c03042d8400f03889028104001c10400380c1840126a00c503411180102001c0d10104440041001e00320004141303204c00076001c91904800d131a054000d5000303071400101c04442c8030038420f50b04500501c4501c0c20b5020300040181030f100d5100303008007440e20700460741841d45040225095034151780080010302004402c0041003505446241d8544001c1d07201413042d03080102e4042c0c08101c1c0a0b00780c4405039218000740a007929007500b1642d003003003008982081004a505100d0400003ea8403c800003500c9080d600280076847c02440601e181302c940c2e040e428885070110b10020f501c0200c0342c5400640070f01112202503040d40c1070041d4424002460359491314120304140c1804c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 959747230 1250 959745980 959745991
    0xa0f0f0c0807030512071a190605010e130b18071e0518010f090317070b06012a06060819120212030103060e0c091311090903090d0c090204030305070b 66
    0x500014040001c5880000c1c8040080c025003017403655466113043ca134403004542090720301d61f25010303000d01442c0218418086c81c030150110b0100802034541c0300441d082124081d1842d030006400c00416040d5041f42c0c8103030501364005011059001040410010520080f100ca00100310080300780c1c0862180d590f00c51003914090b10b001172400302c41c00d0140b140481000c07140f50401204068081500303015058a01c0615045861160000141c013540002c0380c1c400700381222100c070000d002c51819405485450400b1242190f04d09075400400c0c441502c2040740b4100f5202d4540740c410014514800b8840d8910200d2540c1c106014040182880c07800ca5035451104811580041002c0d62040150001d90781900d0f442400401c282402181c850301d080e41030242942d01181c01d10a0154007864560b42100c244c0c4500c504155061040d02044507a040444025189400810207024540340203403070318000d24031070300d41c01c89240e40b200b0300c05041f170300260400c034007044c0001007503401e0180180c00f0b0359108 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 959748480 1250 959747230 959747233
    0xc01080709030f0b09190c1401030902060403300c0b07080915090a020414010e0f0f0403080a1d03120108010b221e050a0c030b01140a020a0f0f0c08 65
    0x214910f554010380b25035048005886114500040b078100742080c800440107802c1d00744c444580d403009050000171041644950f80121407200e0480300a94003900588003c0c94000307202d142481e02c0e5465198520488410711400c1050381050300310490019116018001090345c0c60000c400940c0c82c00344c540c00301c00f40400041c003003944100001080300203980212080ca00006081c1da444030282180341c141030b200000c0d4010708040c4042e689286020b0302c941206c881181110017600e030703600b42044032041034480e4801030101c0c01c00900800d010b5808250801d880b014006444803800d407034000e5265030420300200c2504001094111104030381e49060152034404000c0004001800004011004001030341e01c640031020103403102c030051a8082c0c402c840c00003001604011800802000404045a041c00c0d05454100b03040000340c441e209510300a001a100e030074003030041582002d100d4020700040000c51250200c4100012030100c2c10014061050f4080703000c0c400145000b046500e003a40000c441e6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 959749730 1250 959748480 959748497
    0x510020a110d050a020405010311030601170d08041b0602010e0f0c030601061413080a061b0c031b210f02121207052b0f02070804090f14090c010807 65
    0x1c694160700c94205141c0c1103401030041d001c0c0e460440c1c18a90440b0010354414034150000050041010036174044400c201c0940300c2c10384c0c036003012810780c6c0c201e0341d00043d440d4070100320400c046000320162604107002c4c400303820b89002c5d0540314081340e00d219080140143d440300315140b0b0000c0208102ca84201c00b060242c805101040c010a03540d1205116842c1000b122141112800404c01c00b240c0d49a460005048611a103401c41640c0c0c4001d03030002114041c0c40d00a2041040d00c030400401c0d50030318560b5030380345811010f03181212150700c1500c00100f2040840c0181d00014104200865000303030402b60103c008200d44005091081d00c03000800540d004101021f945038245421680a600100d01034061504c62080c1241c0d40d00496588000101c59841d000030381d0642d510400140c160b4a44050080f001b0100760f0800307900540d800200442c800b448280661501074001004c03a82d640b0800103030b81c04000b0840320041c14161507054440d0020080100300d0350f84250700740c2e03000c1041e0509000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 959750980 1250 959749730 959749733
    0x2108181c02180a09020303040e0105031501080c010f12020d05041704030b0a02070c050a080a170c030901030f0b100908010b04110306120a0c2303060c160c0b040f0510020a 75
    0x241114025030401c402d098440002e0340c0205a80c482400a60050b04072a1581d844000da0144a0300038001c03e03100388030b030503103885950400d01c50b0315058030031382400790545950140064139003c500c03801010501c9882c8402188074800ca1001c0e200c0453b20b040080b82500380340c1082034881c2c681d01c0011900840420003440410703c1200c040e508030f88101401070b542c04490624011505040c0c1000f0341c40003481c50002998607000807910b103018015850030507a0010b100c2c0c0070f20325210b08810545a40c109006641d00c81d8069440546e03015884800400c2e0040c074400003800304003030f124030341020510400003400400e03000d01ca5040c9002d0283e4040024140c0800140d43c9400009c1c0440d124042280c0070085044043c01065813007644902c4d0610a183c50f07040000c4000c0f4181213000700b418040642ca15245800600d290140c3c4040c928140307070644101d2200c03600c02042000b030b60741c04203412000507288400340c0200000d095880a00050a0400c0c041001c25882c02030b40b0f00442d40240421070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 959752230 1250 959750980 959750989
    0x120f1b19061704060204030204090c03300f0210020408161403030301051c0b0408030a2702090403020f06070906080106170609130b090d0206060306010608012108181c02 74
    0x260400ca4881c0841060b543c3d42c64010060710851704025001800d1103640010045000b02140a4910800d1560421742c403259a03c0502d20b415180e180b100c500501100c017010b07001c0c601360101c0690500c15600d5102c020f01c040c3c01681d1041d40f01c01816800392003200700024800d004880500f503002e0200496003100700000340d0f2400b06001d107603c1001c0c030418404401201c221000b40181d40400450030038030741410a11465081114404211410001c80c088900c44c0b52040c20f008489041d0180c15400081c0c0a100c99190010300403010762003041ca903503204803010800c1a01c200401d640e405666410a01c2c001c2101d041a030102d01402108405c80d42c1d28507000d0040c5a1100742910b44140554406218aa0102c0c1d8448040c0150201030184005606c021034441072100c4650210b170382503194072060664941c024802c80340000c1a510050048215810300c2c1c0c00e00000301041840c0680306e584403c02c041e4080350302e07404542984080300c2124140500300000003c00d80d0740c480b4441c0081c0e00442c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 959753480 1250 959752230 959752247
    0x706140a0f0c0b0f07140f0f0f04050910080d03020c1f1e0504051204060c03050c0a0212060a0b0a060f0c050316050312090105100302120f1b1906 64
    0x1441480780000d40480c009100303a54606946070868001d0319241880c2c60503045802050300c507040003c61144e02160358400714030480700074900340d04540c1d10381084c28a10145a17003280d8018450b039071007080009100d43d42c5604d098041c0000d440d500084510b019022850041d00c1d0f03207140203043c01400b00c401d111201050924001c1c04102a800401101c111890000d00e812004400940c6601d10504102c507030350351007244a54403420071070b5585072150f25000035a00481c810403002a40921040300081e204402404080c0803100846561060550001d0b030000d100d600108d100d50b00c840300708085245c0e40d0150310280603095451403e40b9041400003026508055034003418051020302e0981000010400c0f15101e4107103403080c0340300800074582140c1700d034046024614480c0d00c0c200482c0140e07506200c1d1074004d40302c051040705041d10355400c1c483d0b06581d1203003041040c06240155103001c1000d004107460340107030400700d48502c89200204201c16040900e200b1741500503550612550b0b401c003001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 959754730 1250 959753480 959753497
    0x14070e0907081501090902031801061a0915040506070807030e0103050c0901210f060f09050c04380d11040f0314120a05090109120528020a120302070614 67
    0x14041521540180e517a44d1080d0320810941d44000100581c0b40c120244245240e0b007004024416560b803500004070501000210101c145010450b40c2c1d41850410301104001501ca09014105036a400019a00e900408425928030303100090300d00402d40d00003001c100c03175402400c0401c003e0070710789030b80a510b00602d14a2414450407a0340c0c42c5080300300c11100d11343d410308410240031102c0040010030240c00d081c03065800310a000341000c100000d00c0d0044510802941e1402410241740c1048090444208039503907a815860009200c128090f501841c110f51524480d100d82d0780c1680b4507034404031020b000d100b80000340103100a00284040080380c500b243d41003141c1d2851000a0000309003046200840900c003180d0000b00170360041c0c0c10001400504d2400d0721a0800240d40d1015400030381303203410b0000e040c1d8200700609440700145140c004802c0300480100a83c00c05150b002c0340e60a100e54101c81401c0f400381001008041d81040500042c00e194544105441034410081000340941c540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 959755980 1250 959754730 959754751
    0x906090f06040c300509060906062b0b0103171602091b0409050702150403020d0f18120203060a020a05250b0c03060301050a06120209150414070e090708 67
    0x7400c0c409441485010484404114080d02581d140c1c0c0544416000440e1504c10460600c000540d5284020903100d100e00c0c0d1a8000c0d0240d48c0d20102008040880824907015909050784180c4030110381c024402d40440c803c65104e1000d50460a140c904480c07480740300c01400c10304101594440014503a0940324940c107445c02c0c1d05c1521103850007240a800342440110105000c6800281c00403a0b070407550103562141c0031381d10b00c405c0200c0b03140c0281204840c09005030b0300011240000d648038a12f0000303034003080d1501d140d0000b4200c40041910766103920140b10880881c503054154a8144010798101310314400840c94981c5d00d40c0003402c14060300c2c4010304041c0c1c10b0f040c13440c14400050519900c1a901060b013100c1842c01d411754907115001920f0003400307586030400298802105118403070a0300c3e4070319002d0800c0012b580c00c11009400050000c0c0302541e8040c9281031a4855000759244151305288161540c42d00d000010104490203007510320480d2900b040c0301d042500114100d070800800403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 959757230 1250 959755980 959755991
    0x604060e03120304080711011412250306030203060108031206090907080a0c1e240e0a080a031d0a030201050a1e180504092a080304090603020906090f0604 68
    0x200082c20801122002d1151070000800c1208100f20304c0000c0040c0d0384107400c15262440748100440e5103800d506100d41c1c1d4040100a01e041c00002c8030b00d21540440c1140000360041682c445110b20140c0b004000404242c031481b00b0302c1103140c22700281340506a00d1000b541003240340d4060a050380e9001d00041c0c050100000880e80300081849004060820300040346c0b90300c03d0501d40048905250300c540030f220080c10358180b449c207003003080703100c1120920000d1980d01c1102d078031204180040b110076101800f0314540703540d801e9100c04d8903150080c800e503c09444c00c40d0312818040c0040c0c225580c12040050325114100e06a81d803e21510b094075020300c1d1042e101c00c0018420b954252008039101d601200110f86900350075400042c00100390000320b4440b42e119511800c1c00207031303901060010b01d16440120441a00080341c2c3d40c1004100c408001651070668603100030b41141d00c40d40004804949440051041d07051180b011904628141d40c0b80c0c0c0c40d4606800b4284100c0400b40c001d83c131864840c1d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 959758480 1250 959757230 959757257
    0x4031407080a0809040f140606090a03050f0715081605030c160b180f19031407110906100e0d08190c051c021b030a06050906180606060406 61
    0x1004080c010340100d00842c0c444080c6030510b104280c01001d2410f216034101a080b1b80c0d10512802038014011000001c0c1d25103840d8a020080a50041c4a255400c02079494000010901c1040412400000c003c098001130f41030a8940c0c0700d501d60703c3c220100380a041ca044c003c045103800b01c0c0d11000905458440d4803a1203c45003261584a00500300d00304134000300304c240502482071107640c0104103045001030395458858480e9290340490041b100b40f50850f8581d40501c0c504107400303030985c030b1003807034400300d200d018005040c0c141d04070300c001740e8003940d12900d8560030342049020703140c01c01c50440c1c2e80b400072810a41c00402c882c001d0101140250380c0c005107003041068240540d80441500c94070460340b4114110b00038145c44146009a805100306c6096540b8038465800041d0100300f55409044122581c0000302c000c030050500b1303541c051003412403c00c04205c0900c01e050040610501510007801d080d00410710700810448002e240717400410902c0026034800040360221041420101e105161703c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 959759730 1250 959758480 959758483
    0x1801030c06050d060b1b060108190206031008120c0d08040f080c072c1014220f0b10020706051902120414090f011a070602070212060109140c040314 65
    0x50780300103400d0b8000300c0c501c40d006946400b606c021050700d00c1281c025a0703803081c030265207840c000412241f03642c0c441380100240c20250001c69000d111140600c00c00b03a5548071a610740782c0070b22000d4226480c040f0304000d801100303000101145499250501300f50405480d00000305103111001400d01e800042d0700c40c04ea4005114280040c40500440003102c99003140400c1c1c00304803601f5034200c0000b2040061642114808400142c60902d03412502c40e020190a07c421a003030040b0524200c1c200444a46108803e8001c1c4080c82561101c0840c01c0d601c100140300300c1d6803850800c2c00c20364000b508140004c0da0f100b402e94500014100e00e48441881040c420707403e14040e130740714481600001a011883c40200417001a801d28243e070780301034660b03d161a40503508401c1c0603242c0d02426040f412111983c0e03460140c014039004410051400c07109034006007186e49689442d0030302d40c000c02c0040101c00202e100e401403842c0340b40300f001480e103002c0071441441d100b640002095002400c4c108000200c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 959760980 1250 959759730 959759741
    0xd0804110d050d020115080a0f02030a0c140906030f06271b100c0b04020d06020423010e030106080a171c02091009030f0b0c090303181801030c06050d 66
    0x502410711035050a640c201640c032042200c6098000d0340c02c01c401d1004d200030f180710900c00c98140d2809003582801aa50b18400000c1411050707a0500c1012821000b0503561409400280151703200c40140991001c04d001d0600030040c0384510941140814640d111400311b1a40c3d03008081500c0d01c10b10300d4000d440c070311502103050030300c1d4071622030f20070802030054060501d01c0308180111610391042240f1030301117600e0b819850000b000d40c004180801c00600b0081d01401400c3c0c0300f0f00c0058102034860390300c81e940c0d02c0c4a0b03149100c25901084400c0507540c00c242001c14401c0700750b000f4013a250030b100703c0340e54a100d00c00e00142070000a4054020b50310800040d0340341d07000b2400800c441c054016902202a42040c038005100e40c030380c49180c0c90703150301030071181046a0b40101980c1010105444400b000e500003022500204403c1004291580c0d00f1b00007001c440c1d050000310000e81c0c4052083c0326450928101c000c8031011964018000b041448180178116081840d006503162000f0207010003a20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 959762230 1250 959760980 959761013
    0x51008040f032c0a12120e0301110c1b090108031614010603050f0f06040308010b0307030f0615080c040602030f07050a0c1203030509072702041e030c090504050d0804 73
    0x814070262400b6005103840d043e0300907000b20b800d40719898540380f80c400b4004030400c2c02025204010a809140c5005008040d1003410040c000140c01d481c1e0510308600b6444006000d9161f0000600b210039441540b80b001e0301a030301075a84020741c1d070402c180355075248108010b40c81c0d80c05500c0f05110402020254044040328020000c1c070807103607640750540e518003240d01800f00d14021103031030345c200c9000080e4091150b80c059944040f281d00c0d192410040383d20103045002050307124055403901c80c03014050940244002108010000b42c04031000b4051071002d4141580e05404000c100062a400020b490700042e40ca1141035070380e000d43c64440d05d4211f980c04010102e002c40d1100040300b00c2204501c2d00340340d00a44090201e40d03a401075041c0c55040c0c600803512290014400b0007050501c0d03600d454900005078ac001890582c45801100d00700740c0ea055600d01c8840000000e108105400840100038402210b0500c6a4203003555091784840001c0010720410800303d0006041c420036030002100741 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 959763480 1250 959762230 959762267
    0x150603100f02131509080d0807030b2110110c15070c0c0914130c03030e0612090d0f0c0312020d060306050406050403080106111c1701080a0c051008040f03 68
    0x1d0342c0c80b09054085a9014140b0002c01c000300c000050300c4801140c0c15242170361f030f650303103a0040e40c84c00c83c03e4004019501205030800d80c410540c12080301406001903071203c181004044c0f8070070040c081b40a45400011110348102c040c003c2e054822400641ca8000581c9070429207031b1940c411900300c41e21400e11901503c13100c1a107000107aa18980d501500e1411261803044030300365100c043c0c00300004c0603803600515480c405d00c01000424403440d1151a138500c010314407031400d00e00380820914000291400e5000d5000284820307907003900700042500480b142d05208120401e1a02d01070500d014142c401000140c000070071400484150344000044c2d0392007001001942050704000300205005c8038100d000c6a0b2810011603842e02900440da00c020400c002040260400d2907001d134039103061a043c84c02d00005078800305402c0711902c0003501803c00d810050442200c2d038102080b00b0034007584443e000e1880e0010328000d040c1c0c4800010f40c09900b0581c005511300c018034045507403408506000d0b048 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 959764730 1250 959763480 959763517
    0xa06020c28061503021e0303090d0b0f0601021507030b03030904050103030c0b01050402030126070510020a030215060109030f020f0405070e04060801020412030c0c1d09150603100f02 80
    0x1d00d00360108092015014003010080f1802c0c8254a41c0c96074503e020196200d010080c06c0090820000040c80001e0380103400c0d681400940d2021501c408050001140c09501c50400c01889417020f02d40315901c480d003480205400d10510302c7c2c120910401909240070941c640e410115586c908004036258800c0c0607200f0401c1e50ba590030300504414629008130782860700230000140d9071402e4001d681c142c1b51444c0440b85a440c00d1010b401d41e6a0b403d00202041c1c1c09061070006665440501d04130761031145402404440c14149002400c00d031007581c9003101003d54109102450b64042da050f030540380e1080c04019403241600005021804410b00d00307501608203020420755036800840f1a00401d0b056600388441902d81044600b42c3c001d034014280b5044000b000080403a204000c0e10382914041c3c0c00c0c0180e00d80c3c032100765403074008040e00314210801641c2e003484403071042004510603000c214059030071141001070000b0380390717520701600c00922510b4a001c0700c64502d103a41181c643d03610b0210303421308 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 959765980 1250 959764730 959764783
    0xf0d080108010b0f030c040216020406062f0705280b090a0503070302030a0b330a120506011e0b130f06050a17070507050a060f0e0c01020a06020c 64
    0x6500003406000c1d519400d01c128500c003070031302c40441c0f03480c0b00303008000d0300020010702c0a200080d0408440121000600044400540c65610030107000d001d00b999880c4292100918a10465803600503160b04c0c02103005040382c1050000c034014042c0d90088585005034690110301808455071103840c6085c0328520400025412403010040034488019203000c07080780d44e903104250f2903408900c00650103400c62414840042e0141c18a5a40280100004090039a092b024841504898501c08152000400c440d03e0346140c00414400103003914419000500c4c2079030307150341e00c604040c4124400c41a1b01c9000406141e9a10100c902a09900c0045503d40201051440450780305118240344003030f54201c0400d409114100b100c004249986942c5143c00085d4041100d0b0100184000c0411000340050000100c0c14003615104500035035000c40d0011036591503004603501e008030402190b220480482071030760082408481e0940091380183c440000d00200c505110300e80681a900103480b0440c0070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 959767230 1250 959765980 959765987
    0xa1d060108090a0f081c05160c030801121707200609010518040b1801150306060219080409050f180309011403060d0f0c090609330b0c030a1d060304020904050f0d 71
    0x23441a4000a100b0b00c207804056801d0b208800c581d080035001860b40401402042c00045405480034070482c4150400342c0c0003655a28281c015a60898885070030380841840c5442c05008201d907604200c230414038000c003040001e40036125980ea06100d00341811011002580d40f68400f6581681c0500074804208000c40250f003401d00c240604110984559500c10060303102e44114400c0c1e80c40e42d00200ba5550b41071040c40e100d07004201040380c0c190410000130a4104c400e02903d409164580e03004590303424081865141500c1e80380380c80410340d00034858540307607070307840000c45c03550042c0030340b0036a500d8456001040c011004440082c00100084944101704900180c420088130f4401c4020802c0b1034842460000381c0b00c1884800c0c1d03004c80c441401d00300f0f01c0030000070500c41901ea4107044940b1641c521504c8440d410982c80000180c00106414240e20b8210f180341c0e003804005081c80c883c10b01401e001030340c04c0c04003900103070142e100000050700b0400300300810490302140b0400c540c1003070301d4140000e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 959768480 1250 959767230 959767241
    0x6220501080a0201080a0603030f0c14011d0c120c12010b0306130c080f0606091e01060518090f0112030903080c060604141003060b06090a1d060108090a0f081c 70
    0x104c0c0062945000034000250500c50b84040c1c95240d40c8603000d0600100080b03901a959040036592410035070982040000b0034426003459441c0242d01180000f50804200d00300b101248480d030103526104541d0528038030105440442490485a00c0e5008080491203401850441d0141d07402d0712806041c810402c25003102d01d0705891140c1d00f001d0400b901c840300c0b2511010007008400c0745030b0004020680d203140815810354055108000c0700c2041c404400c0183ca202020792000c0003180c0e00213207410112030422228203010409079003c0c0041d00780307000d0700c04102c8414400d01072540c1100d0101c904062040325030f070004540005107242c860b006100241d45824080d1070082c4031fa860841c044172142a14039150788110140b2000341d4515103181c5a04003c2d00c0144403465101c041005980d260341d540d1090a405030a0200760b08040031200c0784454420b41c2c2c081c00f0700b8140404203080021a80d00003940898156000c05e00b180f240106152000e00340c02604200c081111110340c0d20f90b20b0550980c4503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 959769730 1250 959768480 959768483
    0x30f040f0518040312141807060504080a1b0f0b0d050f072c0a030501020d050a0b030a290c09030709020a0e04090c1d070305010f06050306220501080a 66
    0x10444040c0e64100304a001042d00c002c100190398201e00180209000d42c43e2030860b00e8003020080361542403a02d000c864003804030b03400105c50201210340c06048504100c5040a0401d42c00c051345000d040c15101696003018090080c1552030b40a03400009000d1a0581001814200031036450907441d20b0f64150306800c080c001c0c400740ca240c140000c00c8a0b4044038010700a01161700d5110048540b410f03184460704500024101152086541c2411078a9900c0400011805a0001038a409582c04000c06a46000d041000c40b141488140d6202d0354005c81c07491602e0350700007181025680c0180000000886040c04184202090000c0090316003040e00200002c020480994000035200c002c80c80803402150751490004050786883d01c02d50a0940c80844018015000815866510484148a181c10014450420b1545418041e03543d405010f1207000d842c2d80c40408503201d09010b401002408010002d0344208034a134407001080386c54408500a0740444903041c0165a140e1210a40e1401060b00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 959770980 1250 959769730 959769749
    0x15120b030d1205090106170f0613020a05010f0201110d240b04121511130602030a0203030c1602030a0303020915030402030304030201030b060f043309170f030f04 71
    0x4010440c900400d501c10310080d1038445003020101210b00324014000102002040d6580b1140824401c004c9540340409014a0004111400f0781c09051403c181c40580610300058000742a10010303035500041c403050b230b00f0a06c0c02c8081080c1440c8201d014210040b000102c4080000e28a484940c3d035030048481040c0c0540061141540700d40b003801c10140701d114220412201344428030a40400d840027445850003407000789040e80c0003c605d6801c46000907128506404005122000c4951141c03143c3c0003400315002444c101000740030041d40307034480181800d000d03507400a1700441200c840c50303070744200d00c2c0c0243c1215252862440d01070000d512241d282d074869078807070010419070038035882101d2240d9030180107141080c2c9941d0041d0050568100c3c00d5a000708140107841c940007849010b0401013002c5500064001040030800605039180c449215111080310050303540c1c9078110f0031600854001c00c5100601c0801c0802c002c0c146481910082c1c1c01c2d0000081407210211020050400e482c010718 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 959772230 1250 959770980 959770991
    0xf070c060e010f320f180906090112021311030a09060b04020c10090f020603130b01060311030f041401060906090f0e1f090804080d0e100e09060a1512 66
    0x9410341c3c4002060062014801d0136042903104000c4070540c8488001040c0502030801d0a40c01000e4083d40001d02c0016111841ca000d4a02510306a1030181c0c0040382030720684446e50504042c070b1103102d80488081c0c007504c40e80a1076040820a50b10030b00e24203e034414100d44a0525402d5140513050b602c0d0b054408a09200b1184202d15092003250200500d280081055010f0b11a0300e0000e406400307000c4d140706541c00144000750311854011880740407090040c2032442d125103040900500181c001c0d104140ca0001550401c2d1850340449401400c019025001070f9101d01d060700041c0e0324201320841550074070000050350a91030308903006a032542802800b080c501c0159480132200380100050003580b141008104d41c00074ac00500c81038130003001010820300e4094980461030351196015110395800340850006040d4081c0005081045c119800c00c00c1051441d80249100c40c40443c0341c0c80707030b0034540214109545a2100c0d6008100b01120340300140391212002c2d01c0080b401d030b02c0c02c90103410003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 959773480 1250 959772230 959772257
    0x10f050f0705030921091f02030a08091606180909200406050301020a020a021c0b0c03150604140126071d090a0e160b0d0f1806050604061211060f070c060e01 69
    0x1f48900c031140c500d9a0065042030354441c01128521005010400380740512811489010b0110b84c001000e040f454aa0520100842c0440c40d0035030b51552010845d035103405d0342d00001404c0252300c49038032419002d54891038003075800000c0040142c2d40c0166810361000804c1c07000e03d900440c900c02014000c90312032a2030030211500b100c0310507851900074681b000301000146071200c1c803006107800c0404461809018544000880c0b401d6200e81c02401100c0b05410004210b907a0061003001c4030a035034030100c1c1440500c8801185089405001c0c4e100740800c10300c00b03e03880d400b40a1445100e1b040100740c00c01905124034000c0050028840000d03c43c05440c2c0d0603e04d13a8003000b02c1d44121640c0d0482d8501d060400c2d60100000c2c0b0700411140c0515445082d4447c0f02d0401c071b804030b03204500882e0002424141035080004803822544410711240e00004501c4c04500c5a40598003c41c2c0191802c1c0c1c1e645602c4000b1100912510000504d5004040c0380800c0e0b0319805541c810b6141c4081e210800e500703e92 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 959774730 1250 959773480 959773519
    0x70f080f0a02061918033002100b0613030c0512030309060103031b050d02070504180809090a0e0a030c12030227061911010f050f070503092109 63
    0x208000690450740400444c0c0d0b80a031180c001c1c220746180e41c9409100c000d1845180e0139001002d034402d480d81410070340b14000c00d0300e10300c10300300c440d60340e6040f0321500c0c460003507001e52180005009204400d6441ca82ca4855885500848000f00e110049416215843c0c0c9030030341c3c50148030b000b194000d10b85c1c104144410000002101d00400c80c080c0148000ea10f1071f60201d42c1c0e8000354403142411021000d84400060080008040260f00ea8020b041d0361402c060a0001710386402c1034840020340d82e0442040410350a00485240ca001910b0307110072566040040700c003a1850703c845504501c5410ba00105142d440f02d8105c000d14442c009885026400c0344044003603000389000303140040c1c031003080c90907440150546006203c1c0043d0520382403400c0d144402d0066000d02a413400402c96503010564205421320404010180034a810009401c10364054541040c006141509201c000008a8041501000440c02c2c211132903082c520860651505210076801c0901810301031595220301c0c030300d519038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 959775980 1250 959774730 959774743
    0x71202030306180c09040207111021200c0a0309060e091801091407030c0f03050319050403080324030105040b070c0606050306090a0c060e01050706020a030b03070f080f 74
    0x2051030b801c9a210650f520030300403001c2c011072511841040990210f4076103002520b0741500640307040d0840581401800007490034105208100803640188408040390480c0b003900800362680005444600c0030340450909031031a01d0400b22840208024860f07820001d11402214440e46da0001e000703030780d21400e4401d1541c4d2040740c2e0b802600600099070300482d00032440b140e4013200c00081015601c1e070b2240d84141c40341c09400041904100c0f818001d01807544110002004076100d47d0600c0303891920340e140c4038040c0003044030b1403030411028041598440c1066802640e0000307100c0b544d0b81072017618081c1c0403114031840d16250f01380322401032042c41c041c46903520843c3c1107416601984c1c6c8000b82201c02d404590b400312901550381c40702003002e03141040360b240304030504401403d011505080081403040070b81c2c0aa010400f14400030720040c6d92150503602c0103580864050f86132070090700264054184050300c1070b01482400d000081d00203040f0505011142d1150946145e041c0740c046042e200c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 959777230 1250 959775980 959775991
    0x4080f19030c15060b2502100305190c051207020a0c140607050f010504230c01181706061906050921100c0206060d0b061302160302030712020303 64
    0x1036084508010a0090301690700c95445038807102002c80c2414515012540960070901d800400400d5240c1105a4200c0600c5003007a80c000b101070a05080d0300040360005126440d03001c058840000c41d1914030381d056031014070211100e051100d484401c1c0000c1050700120300300e01da54240380d0085a071650001ca240c1d07110f1904000e200001d2410103071001c074100340741240e00da0084010003108012650a209900103205458004140c1d070038203050151800b07100074443e0800032704d09643c90400d143c0016508041000c2030810700007900c0303200100309540180b0391282348040070f402284040100d0100f000ba204541c2103440364042c04c28040062642c40e03160241c8004500104000c085910b8030500c0c4880705611000399525030034072007a61303e00b005807107405003d14a03200c01c050321000340c0601070b0035031161041e00d00346008001900d6120f200f41c001b500e458018101410100350313800382901101d19290580c44d404506100515009640340d214000a131016110f040b00b90b801280301001310b03070065 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 959778480 1250 959777230 959777263
    0xa11240f0c03181e010902030c010806060a0c110d0b0708010603150b0c10060b030708161e230406030f1a011b050d051218030313030207080703060204080f 68
    0x5543e0f03030510a0704000300001c612030f20310401a120b41d070062600300e0b41c410700d030041c00042058003c9106261030020390306140d03818403050508108050319a402a03940144961402c0300a01c2d50340e04040829007101050b40b5080348119008500b8407000e0b80b035481c001c402c5559070703240c1603030b0b00d0508800302d070308502c43e102c28044032100401514405201800000641d0400d0b2111100300714041c104440581d4045c10383c03078502000b0004440c2e00950b00a1f07110400b24404680d0441000000f0701910040001c452030740c040441c1d64451f0307440340c059036a0100304584580352051500903030702c185800511810000030301380071540c00c0c000326074010480664800c2c0180a0007a05030001504c4000c0078424032405170840c6d042031404034000b04a81c130020403841d1a5240d07500007010004e41c2c0104020400803422120b02100c00c03c0703903000011203038041100d0000441c030070f103180740883c2018520f52010f0041c1c81f940c28007105100030395004000310356a910441d140005501480740d194ac036045060300c0b14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 959779730 1250 959778480 959778487
    0xc080d0c120b240c0a031806090e0c0a030b12100b03010e0c150d0f0c030605060309060121020402030f09010e06010602030a12060e070c021302070b0604020a11240f0c 73
    0x1c0406400040d40081412040f2500b845200020185461171141040d00080c500d081c0c4a6034a50305405d0800c043e18840c94000441d0f4100301c1403a105070006810b00400c01c0700018001c010500c41e0348104500c000081038030210507241070791070b9a00c81c00d000b41901b4140c1b0344600211103103014801e030143c01243c80c006c0c081034403956080042070508010164810041080b01c1c10031103200380316030000ca4201d48000100e14003100c100804a0361a40c000601a074420410300003505000580030741144c040511810a111001040e4500008841c5000f0741045c000700501400c0d18404503003030f00c901c002030300070803080404c101d07030554610080c442c1c480507803c2042a4070b000c0e4481c49485110684441003c5802035907088807040e5820101c40350000540401800320840c40e2010b0303450300b5406414001d43c02d091083c0ca40e88110413001d0b000c148119400600311114601614115410070803500940e54007082e001c6041c03e84400c80e15203810305601e52030001e07030140f440742c52aa0265480d541450700303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 959780980 1250 959779730 959779759
    0x9060d1506230a050702030a210305010803030f100902070f0b0907050a1701090f0506070f090f05190b03040c0f0f120602070c081020031302010c030c080d0c120b 71
    0xb80d82d40981c0b08001000300070408000541c500f00290000c45100c6c801070202c28148080c008100310480d41c40c2d408240c100001080031800c000242e0ba00900812500c404c90b8841d2842007180302c40c55800082c10500100d03090044c084283c901544050050b030750041565104002581c03956440d001c0c040d400203000030f00b0b2061030038004ca02418288420000141c0e80e1550700d070620706440c0080210781c80d43c045c104000c002036104041c00e10514a5080400400741011840080c52086015190150703e100861800880ea4400ca100003441c18506103907403030400781482c54180c6198003a80d00340c1c0c0032600c40010b01c49240303043c1d2000c0ba4458014048030758100d80e030300300c041c3d0320001080d1400d000c88000840d0141042c01005092603070010005100800c0b82c004802e84c2c0e1182c00d440e09010307014400c0204001d4040074000c481503091070804203aa03014681a0f03592140307948060b150301d8011030400350003826135001d00e0044005444060f862900c91102406490b25400030301c1c0c00058035150200b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 959782230 1250 959780980 959781047
    0x1d100b0303220909080901030f151203140a2d020309090c070210050315011d120f1f0506030d172d010e01080307030903110609060d1506 60
    0x82c2481c000300320316980c0c5903542e0103281070f5294400c0569100200003421880d542e003511400c0001d003241802403105030303482d04102c1c5070324071035200c0e4004a1860403481d0003050b01ca5020018642c0301f209403103445100000005105002103015550120098082c04161415960300158205180e0f4011450031000c00140980282d001d410151103100510034000142e03104801c50584211540d510768891030714010303d040c283d0543c034065050101d080c0107041c0359000c0080110a070b89081e0740c07000645100c441c11514050039003440560600442c00392908200001e421240817843c1c004041c400740c0c580d501055143d41140b80f2103070104880041900c10315402a10203a4001007180e203202807081640055038600b600c000400c801094a600140280610b00c0802400360076420001c0d424040580d6000d4010703004c42c00b0180c0050305840c1d501800e992020107c60340042c01614140d1915034000600000d03140c0111f20302c4411074403090105429106002080b416090f40b01030f880340a6a640b240c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 959783480 1250 959782230 959782267
    0x30f070c08060708040209060f091f05120c030d030204290d1a0901091b030f110c0a21090b090a05090115030e0a080d0b0a08011d100b0303 61
    0x21101a20510400030301c00340d00340815841849151075801d41841d1510400207210300003400305208000901d6950816268002004d84c06242140824694440207404034449445503004952112002c8400e114140c404035401000c0c1800750125407804540d241c0c298240c0c011401140c07000380a10110703a4108407031103e440501c448401c0d50310700e40750901c00480203031001d059402d4484115008241160b04001810f54014051003501704606d00d40c49440c1c1203400074821644080586940345000c0e06c1a40d41e110345000002ca000d82552911808040c64a84518080540e904d805000016450720664031401742402c0040c0d40b40518207041958412480e080340d0f078080d8000300b07801004a219159036680c580070340a080e11040c2541c032001c0005081c2e980b848085085034200c4851040050301303400036150040da0b544400325881d9034000205000d2070090b03000c08844d600f4414810740d04480d00712000300c00020302c820740304103004220808041d1107900b805160960701c200680d05c0d011440380c0d0034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 959784730 1250 959783480 959783483
    0x1209072c070c0f061805070803190507052b1701180906060906062a0314090409050604060c020705120a030f05070f0503091305100b0f0f12070206010f08030f07 70
    0x401d0300a000c181c861000301c806000c20500c005117110700c490240003080100c0c50040400310025403520301c416442104076486010900c0501c0000324414080203c1404901601c0441e1302e104500d8850380c50106c07408510340aa41c402103400260100c0400002e042c480d410b1302d640000310005d80d140001034900603c0084415100e15585220204100ea02801024010070b1540e45400d0ba242c4100282e07008200c00c0c4601a613888041898400006d4020b1861745070008d520b004036843c1c0e59191302080240c800c1c3c220041a600441c1c007000b04016017030b07111018a00c10b81c0d08455082d5261000e100e040c0d43c3e40080380000c0e50000c030100700001e1141a800540304002e00e08030342080159921038014000c88042194290000701d0441e80c10300780000041c400340e080740401d0126041c901404200410305000320341c2040800941b40d800070311550200c8458000103051a03981e04141c1544200180c81516520010301910000260031158080c0c15410f41e20f260b4082c504c1c0402030000d0840b2544404070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 959785980 1250 959784730 959784743
    0x191d0d080a02070b0c0702030f150a090602070203100e0606270402010c150f051b0703080601180b0405040608030304020604090c02150403120506100f050706021209072c070c 76
    0x180c400101301c00c4545001c0c01404000715100d2880f44101402c24411424810890388514566641c0c403001d414140d801520380140010124560705150020384295040650544205401880034540c290700003118014810296021500d851040141030200050328000030624008005240f84040f580e96800502c14148400f18140c217649144c1c0c4000c1d50300b03010b1807882c0d0700d03046030074a41803034003541d03501800700c050300d00c0e443d041d0100c420054010707103002070100640b8400042c0140d00640c0e51000800c0313144c125140742da41d24a018178440d84a8060705015504001002902e80e400205036401150b00400c1141403030300b04410f00e4020544c940c1410304503c280c030b0b440008107003020f504902540c081d54030b12902e20842c401c0f0b00252800503040034024080e080c10300a80031f070301c4102d06d00303803113818580315640b44600d081280107401a40c070491504007202c0103014113210b001a140c0c1c101d9030b00c42e41000300c5010081b41c004007540000760b8001d084010b4000070b058a4452850840b0940c030810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 959787230 1250 959785980 959785987
    0x91005060402070605010e0723120406060b0c0307060f111c06050612011706041205160206120912041a0304020103090c14150309071203020a0b191d0d080a02 69
    0x4880d036055400aa1101c05010847d20600800c194000781140c0900480d45455404646180e1400c10700e100b1059800341000480011404215442e04a400141558203074251601d64015642d51698040407046500c0c3d4035240c0000075002a0707000300f0f0580b112540741c80d8209000c0302d400c0a140c02d810780305820015555800865a55134a0001c3c10328030110320100c500c03a60410800b41c3d80d88400c04014085680044204030004100003400f0f0400c09052400791b860b032001c0514903100b40102c44009520034000304818002001c40d42e10248505601021689455004d00d10821140704034020b850050401d616040341c100c0c400001590000c0c41890001070406058581c46600410b51300401d080903030441c42d1181c039142441c4150350744502d10038042d00d9401c00b9000c02c1c1c2d0700c00c03440c881d089000f2070084c05401454000d100340c000c2e050300f18658807014030b00f00d000329070030341c14051014095500d40704020003589402800c035150400c0e0345006042d00b4060700d2081c0d0f0502c8009040122540d001c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 959788480 1250 959787230 959787233
    0x81c050c01180b2a220e07180f05040b060702040510140f010e280f0e01060e0d060f020c030703050306090a05130f0303021306020a1a09100506040207 66
    0x74815218100000c5450b40c1506400349041200c807000940001c8008003090360490804844025003045100004011a580c105220480300400701084490110540000d80020042c66040b5414807036040d9540b0110780a14107188040c214000380108040e01d1038100044c00701d03041c158405502014020031250038a0f035181d0028003030f100c0407541e1000c002403e500412900b074066901030502a41100c3c01a40d8001800c002000308000d01c0c0b00501c51a10140380302050100c1d240041402c0c00400e50b1041c0140e101c0b40510500203441c807844400c81c20340000040c02030b1044d105894100001000604c8001054580c2c03805080550a5100540e90801a2180c1c01808200400401e0300c00c0c0c9170039442c0e192900400c4400000286140f00a40c1043d0400503185a0006020b0381d083d0b211203003810348050350404400a0150540c1c0c42e02d44840b00501152017070f00000c1c0d00c22502d100c2e4849518590003003032810950b10003621100ea00c2c0d48858060a00340c41a0f801c0035601a401400050900b85903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 959789730 1250 959788480 959788483
    0x405061c0506061804150812070b100e0106030b0a0803190e041b1d0303070b161403011514180109090504020d03030b0f0a0e0106090f081c050c 63
    0x4041960440006025424410055402415030100d403c90b0711038102440b00c551405007400f8082070301d124580d1340b5000d40380d28080720100d00181840104880c6460441d201d4443c4070741c4203072016540f0201d1440055440d0038000d0f010000d941050303242000591801905802400315481a81d0f404070b84400040f58014040000d0100400303007403985004070031466406890702d105801d4031802103040c407050364500035642c170441c1030b190ba0074500108880c5042c4a55036028080c0e20307005070706010014110091140c00040c25014100d008400d0303240302c801c0c100981c0c0c070b148895201180d01c80140010440405180c4110b41c0d01d00442c01c0400c00e441c000c058003400c5500102c460303001e124002c51160780c25684804900050000241e0801050500340c00140d4a140080c50003410903860304881d80c01510341b0440005c0c00800a4041c1511686034140103900e000d00340214400907148850014410a050300d60300d00b2662080c0c040c1008001c042d2103075242960a414010078080200000410501d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 959790980 1250 959789730 959789737
    0x80306180906010f1a04051504170105061005180108090c09010803030703060501022b0c0203030d1e060f0b0c1c020307021c020612100f0308220e010b0708040506 71
    0x5254040c0182d5810801c0c060910031a58001c5c4820340d000e4568001111030310411101901d10484d085001d14880b00c01110051140e504200141c00c3c0d903058480c42c1c0e08054000c14080c41088500d080c40034448101203c0f68001c440d0701c070b11006806090007025500810401c2d400c08030740781c00c0d107505c03030b00007000705101440aa011050642c400800c01c241c1503030620408001d000248041d001000b60742e0300328000c010f0051201003c1c1000207211140b1355020b8502414140d074040c081c5c988442c0c8041941c0000d00c091074480c407039641110105410300350144115426039050234004a00d090410840300c0b415040700303801d2031036445514114003643e038090b550221303512015401540d9400080c4181b01d20035046094140d10020114900c1e80166114410368860508509141c070351603551000841d0500031643c40000c4500144e2004024001e28500408008110f840382d103103c12003150900ad4070300e00c1c0307205001500d102c2c0c000512001490000610103a4010742c407850409840e4070001d40b842d070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 959792230 1250 959790980 959790991
    0x1020a020f0c01080f0a1e060b07170f070605040206090d0c031a070905060a0c170a03180506040308100914060910051e0406030b15130c0c08030618 65
    0xd10011507000426020801059284001c1c6010001402e00342c0d0010000d03a009820046126142d6408038540310000c9502c52415100c60010300000d079407548240d001e68410b400c15110220070303140d001c0300d4031b001e00221442c1c4419180038600e040d4071515080001c010260040341d00400c00c01626605907075800000740040d00410040d4141c81c40c51030724012000f009402e140365070708000c0401404541104400c0e04441054a0190307584d0f5241c03404a55a04a038580240066015802c0107841c4aa00c400b44c00380b040d207030b02c04100001c0280c1007403581e4120310a0041c800c3e840240050000782c0b0688102c1c5d00300e0303e441d1084110b0342d116014141910380044064480d00a04001c001c468074281d10502d400c43c8500b01c03490f01071800d0801140b414203024180c0e0811848080030810b0603201d03603100000440d0407158503491820820340b049640184030400920502a4031451600c140321441909403000d5103482e800701030402070341c400700b6a8200800d000e03030058052070000c2101910004c101e2003817 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 959793480 1250 959792230 959792233
    0x6030b070f08060306180c041b0210140406091a04060b01140c1531050f070f030308060f0303070b09060112020604090509070f150e010503042a0801020a02 68
    0x246081038000349424880c41414081003514414030409850108400350814909205001224400c46005250640c0d040d2400d0300700e40b070081c48010f035400518008101c1c206540c281d403415920585e8140542d40342c01c10000542c01c4010214001890725848511118800c4001c0e4a04003914a5810121201241d00343c1c3c40946510440a6035030f8411a40d880c000c0e01c0440d42404c01e0030b00300e4801d42c0c0f402809146030a4000f04070214841112601844140c00e40780d141c224138083d920340c0402060410750504480c3d900c25612480200c910102d401c100b9102c6860841110903d1520100d40c1000302406a50f0044002d00c0015441d44003480205120340c000d455162007410724500807132600005078020740740c0401e40b0034024016601c0304106c1d401c9a03584100070409490b400801420304110354880c0c18264405c41c0300003074803a25000f50610000f2151201c1007078042000043d9031b6880f0803600108a4040c150003408001c081c1c0300344c51001858032071100f0362a40c45075091030890b8400310355940076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 959794730 1250 959793480 959793503
    0x915030816230303060d0201120c1d1f050d0906060308131502121b060f040b101413090c0f0306060b090f102d030506091b0d06090603 59
    0x103025000441d50b0b2894444a5120810030744540110b40341e020282030684912608148201035a10842c020821b501050400304184103c860f0f01034292a0b5100580c110010407042c6c1142d103141900491520b021091072084607045c0901084619034032031000081216954290700c40400c500e03200b8500a10f105401903a601d445d4040c1c4010b1105041d8000c241c80c4c0401c5030580d5081c2d6005c01d00d80d0101420305e00c001c1d1141d5090300f0700ca213455900441c0e15994424102004642d0781d1a4619901890042c1070002c1c0c00c0d103e095090014110754022015055140e213002050742c20403410020710ba04480c0d90001d10700400f90390f80d10054a1a40c0015140482034005005001c060700c951030051001840c460f19000018000c54807500c07548030054460900300105908a6000f6800e411044814040c104081d4003211120094190381a4045000903e0302d400560343d800d2441c540c1c0d006420748600d403481c61054031801082944060302c03030b510b5581c44000c00500c2c7e00d0306005480c0030314032951381800c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 959795980 1250 959794730 959794733
    0x131401020c0409052a04020a0c1205030103030903020d050a0b070504060909051006030e160603020a120e151f1202040b0a06090b16080d0f0b06090105040915030816 72
    0x940611074081034801c51900300b04100042c0d00181041c200c1c400082c05c6042d1000c0e6400a601a040115081340c00c54000100603026603030003038091410a1107001007038204c041d803450454660000740070080110300b44200030300c0503241c11200342406521134001c9409550a41c5ea078640044c40c1038581ca030210700d010905110271604508494040c24070071324100400d1030000518000030710244640c1c000d26039101c8158010110078031091845494032480c640240d41c0e6418018020742c001940a40019014001d41c11421818060000a140003d0003000188130150002118000261a4100d141072074441440405000d0b040d1100604080d00c125500150900502040c0c50b101c07040d4910525020406002c244c2d0448081c60641d0b0070740d40920784410420403080c92505442001910402c004201110001c0403034001941c00c004203d4140302151401090024a01401281a02045050000303001c0c41503140d0001e0029402d40702588011581c036143c0c00c1d47c0c3d501c00c6c209418034082c2c01c441d000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 959797230 1250 959795980 959795983
    0x15040f1208070915140a0201140f10050f030a061a030706080a0608030406081303090e040f0c0603020c1e011503210513140103090b150112020a09050904050313140102 73
    0x14010103c981e08008418a0f410700204000d50f00c0803170712026180840d144011910035070040080f00c0912045500e00d00f028101581094011900180200011040030565081090886c42075140150042c03084d0012580e400000d0008a00700d241d083c0c0c1c01d2492140c550381c040003a00000e0640f6121000b13642090308045066a40b41e40060380c0ca03900030001000706903484003c0300d0340800003070680000c01605140898840700d15601614114401001b444240711106480d1038102d841000c411542c141d40e00c005409a015040c840c0364130350042d030040400002071020900060400800000717500c0d00c0388640a10401e440d130400e4482059039601c0c0b001c109038a02003841c2075101c90802c1810300391010100030401c2c1550003805d00180c5030b0800c81d190369000e504841a25907000b150340340f2900d092848040c007000c0c1c40e42c50030f0018203c65201946100030303200701c0346410b0f4031380c0d075070841c090606041c01042c5001a000f02c0c1d50f40b2081040144040c414903001014100701060740c03501c0c030100d10009 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 959798480 1250 959797230 959797247
    0x2a0207050a0603091a1303270b03070c060542011b02030303070203091c11010f020f1b03070b13030b091e01140916031b030f112115040f120807 63
    0x72200180403000044070111000d48d031080b56906080d02e0340c0e95403564022141d840c203c031b1008045605003020300c00e40d149101d144050203034554071000442e40b1030306501100303a0310003ca00c1410340c00c40c400b0300c10700e54441c1645402400e2182034140750001030f9804031703155034000c98901c80103803c0411051240d1501c00e50245c140c022412802440c000305032a503c0c0d85610810003641408078044540030802d0080c42200c03001061070043c0c2d1004108004140190f03051654014424098404046004204441990111100341c10703400d200c94150f44d01c00d00141c3c4064080c1000b031003006206000c160320030f10446682c0c00428004180510310325025481440094141611a08801c02000a50f01c40f000488100d0fa0032010031903110118818241c0350384480e4001419461506501000703210440f0b2090110f030605803503800c00e488500302250b54108096048881581010344460f0b1590242940c040d0070502580c2111a40f1913142d03101e0000089980031700c8003145010042090700d54000c03110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 959799730 1250 959798480 959798507
    0x7080d030509030c100f3207090807050f0f0a060e0306070c0b0a0f0b2808030a051806040512011505030f03090415092a0207050a0603091a1303 63
    0x440c03d1000c0c018031951100442141004540c4d62584506d415482582052074450001150328018200745664080d0351295890140c48100d0500042a041446082c1800844042c8009802001d041100300704070180d0303911a16501001170205042665109520603004040544035008503203c03a20905090000050904060043d080d0b54203020070415000203a100e01900c0c8000350405200706071000410300e5004103900329146041134031040d030313180300c030301c0790b50240305042000c04e55031342c00503030358074410080d014000400900161806107103c4540c2c0050b40c034020102d5007070a80701d0002ca45d08050800c45411160345485a000c00328003894108006000c09034058014101c580a401d60749204042c2e103180550350b6040300034000c040520b080c0e40600009002440315400706509101405803500307100c10035a011045d030303411450000440d8403c80354050030a4902a28145080e0000e1540c8113007500d030b4a130410070140c2c0a0350071100302d41c4200010075440404c00e54a0174014021a004003a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 959800980 1250 959799730 959799733
    0x212f190311030f0d0203040f0503210a06031101180e0a0204060807020a081b03040e0717091c120902040e2503020306060d0503070609030903170a080f06030f07080d030509 75
    0x1900390700c0fa6080d82181c0101c1c056550160740c3e1b0325203252100c94140c109801030200d00011034901032400001c08104101d49a100d50b9a0b40c036101c0b0014007040380c80703034400140343c00c140720381b00f48080d405076103001c548204a150f10f81c0d84903614004130040700c404803142c9040070350004084c4005e50304503d80c0c40d04021548010018a0b1165441c007e10744500c82d040454200910034100205004004850241203201440b45042c14400d17400f5101c0c5081031100c03c0c0401c0d000d0700240020800003102d124003585a05e01080101d01c10800340c803480e00d1071900c030000300d0b1154038007005a1a81d00845038101c1c5510010626000d24421440070403448644600350500c40c3c245c03c1015031343c002411a000002180c208016041500d4040d14500c10164001e2000f414250390005254012070040c0c00c990141251200094203144055018411501800e001c501000082140400d106450301c1d070084001d01150000c02c051000d80f480d1400e21b078007124485e400200c011032940d504d4012582c00544400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 959802230 1250 959800980 959800987
    0x80105042609010c150609021c1b020c010305060d0f030917010902010e0f01091805060f041b3e010c020102070305040b09150412212f19031103 63
    0xb80901003030300c00a046108a0011740c000718505520030303001010928001c554640c120040740084605600c81010f980740303003006540000b6a941d240c0800643d0750741c00351866880c1c02006500509014003219080142d0000c250005130190f460b1020b0030b8065110505500c0c070300310707450b40d4511190380350700450703410446104010303600040242c40c80b05040313640b0b403110f52410004841c2e1200603440b00300788070f0114002c041700c026030380d101500650342070300c5100400044405100640303211038040a03a4030402203c03119124807489032031044944a080242c0040b4491030340b4191020602410035402001c2c041105401800748500c19000b40345000070360030098036440251440c0907500c03a400030894000b4142034242e07a820240d41c29000b034240080d80722a11074200d00d04034051440100d403610180402d401105080c1d800c000003c0745540e4400c500d1103414050141074868184104004140383c5079407d40c0f0002c00d1008020010444031250142000d90070000d08018001c140340b10aa003041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 959803480 1250 959802230 959802247
    0x1e12030f050117150915190513020904080703030902091815010b0a0809240f06010903021509010e06031527010608040302030c010e070f0f120605100801050426 70
    0x89804c0c40c800c3c010846954040e030f1442d90303580c107003001031079405241000e050400080d070010901003007805004110400c401d96880ca1180e0000a0382100690b014041a00050004070048000d046443c402d2501060503111580400c04d10101514040c1d00507180ea50280e50300741c410405030140540c06048141d0552500051400c40d00c12000d464080024407000118202d50400041340b01040c00202c502d0780b8040784a040310750b0003060320315800118401c1d011403a01d61091000c0030036a40c00401100704224422401c4005500070340c00c0e18180012198a0010f03543c620010310311072010740c000200c0c280e03074400030090b4540c1d105072043c0601a64540030410382d29800384842c190307590303400c2c20031140c2c840313090507803450040042d201c0203076081500303556250350007040c0b11086a4140c0f00001c003282d110a035840c0b080210f1301800084180200c101c2000c00c241d5041190808009808d00b503e9540700ea65003400d540049400751100110880303a5800f020480c0303190149081e14403204d03401c1a014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 959804730 1250 959803480 959803483
    0xc06010b07031e120c09380f07030f0c02130216062c1c0c1106030a0b0a080d120207111201061d22023c0405040503071e12030f050117 59
    0x505110180100070a07c0d030301c0d84944603402d941c0109040720b5030f40e210081d91100000d19400040c0440000d4505140031f810940260405029107a0040c54040d0320044c05100740001d4104040c01440110300c1071181003c0b44030351044185050b01985121a070780741c603d00b8811581c104035011225907020807003201815060034030580800d40a4078100176002c84505143c04c4000c8000c1305654016000024881280c4070b9900080702034a0035182d91110980d2002625120292140b04501040029012451700049503004010b65882080e50048030030b43c100220740180c0300d68a90051507950390b8828031900081c804543c50034119502c60030260315045403d04071424015020350f82028080d0355580840d5181e00785681c40b0411600300745d00010080c9980400c41084429200100e034008410700000c0c100b50107224440c5400000641c94000603589110340410011044502460403881c0080001c4011a68039100300c41d640d004200300b46080281011588181e11100040c22403d0308100120340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 959805980 1250 959804730 959804759
    0x4060c0b0618091b030d020a080d15030812010b090f040b0d210e09040c06050307021609091b03120c02040608060403080702120c06010b07031e120c09 66
    0x2800200c100c099210074020400492809441000416900c02040032000300042d000204132101804a10510314403018981c40d40284500e070401a003184900d24003040c21100104138589a03400c0020b1060a161101d25242c00c2c2d5810072680180d00080b4140c2c0901c11002c9903000d001c00040c61460030000c240011411a900d03032280d40103903181e074040303151980d620200800490700311030481034204c40300001d51130401e404107080f40440c0ca202000f191904141e0800c92140b6840356034500041c0c20014155450f0300001c101030111703c910414411820380c0b9066030402002e03603d40100d0b1100080c94070402d25220031514078031102155400b040071484420359007104101074140040d58031002c1c004103010300816004907189228910a01c010540d101d0641403003000b16030300b5500300b0900030038040306501c2035002545141d84803800511400070380d0401800c8d41031080c00c000d0445103242035502e1290800542050100d444500910b2102a0f0390060000e211941c0c5840c1003810708090401c0507001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 959807230 1250 959805980 959805983
    0x3030f0a0f08240102010b0d080a030c050c150408160b0f01080a110103020904020405031902012d0e0406081504112d0f090108100f050c030a0e010f0f0f0b0604060c 72
    0x3e5401000e45850b4002e5018240c0098003400002065080f401c1072180c1e45e11420491002034600340401102503c9a0150b0701c440302007001901d225260a812403468110241060f0383d003901c20888001644d124480480780580b1a0469480a1515810360faa4404059111800c1c940043c1e0040b40042c0c0c418507400500031090800584401e030000c0460001c0c010b40e04516058861507450250000a6085d0941d556100340c0c2c0d002c00003d03061210701010a00140e40140b01045840485801c0f4080c041c0003d041c1805440014201d03501d0041c0d40c5450101880da513081c00c900400d01041c018468800180702c082035070b11801001052482d0010710b022004500210030303150658252658960382c100503441802810b5200e60350311401d10f1034a07040d048880420300791906ca48071382650701c0780c01010300c00d00c0d054032014115a1000b42d140b01412001c0e4066689559490a0b001d84920b18030501c009249212000102c0700c180001d000100c82942400521400060004020003030380950402c446a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 959808480 1250 959807230 959807281
    0x905060a080702191406010501170408030402040209090f0402010906020105220f05011518090f0f020d0b100315050f070f020c03030a0c0b070309052a03030f0a0f08 72
    0x503511100c040342006600b18900004022a01e0920140600b11000821038174014003601c2c01640c0e1080107541c0e070400d1040c205c8140300340400082c00310340c007100510350090028001500d44006e0900160803804211413132107000c031080050100307659002018002130161030000300000c0c1008103c51031401603841100028140c540c484c0070801a04010380448164404000e00402c0c00c1081c0400101c40c0d10301543e4002c003014503c00800600c40e0282c6101c460300021341150502d0300e619a16a540035801c4140e0b041f0f21154020000190901074042c82035064040d5245950700b1403424403400c0c8514060511514184000e001e649448050f140b50017400ca410000c4108401110076030404044e104810f40c03500011859541c2150810791038402c051284a0100e1140d0318100c2c2641150780d412341c09882d47e031006462203000105101c2030141940070141f022106c00807003000034a580e101d000100041c41c0c0200e83c0803c2d890304034100c1d80803074160742070500280c607141e8980100901c44100f094000e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 959809730 1250 959808480 959808497
    0x327142a010507080d0e0f0102071220161409010302100c0c1701060513090b06010e03070905010801091a0c0a050d1e091214030c0a170405010b040501060905060a 71
    0x80d6030182007100c0e10142c0c0621500c1e10360401e060410014a800c0b43c460903103010b00c0d00b10203080309040c8200c4c1c408503030000001c61585190542200c0403440c100422034050418403800d85605010031000e084148d501b034011480341d040465143c0c480125499550050840c1c0005000581e41c0481e040403000e01494102c1c1d44000a040c2030244032140d50003c2c850002004003032000700c0c010342210f41643d0007660700840000008409a0443d01409800381c6000585404252030b90b01c590700c01c7c2d2a007440102120301d031507241c4a08008441081e80200c0c8140c2d03481c0224000c10501050386060019211140c1600f850580004079252113621050030410000160503482c02d9111760003002c00348082400c050b002d0501001e400000d103140101540d628003800071000000388101c1c00e00ca007400c004504181103441d1000c1003090364002c0c04009051011900c100401d183d2500d0055100394010302c00819141004e4061004a80040c0c21290030801c0c030207014841606c03408120360048520f450001c04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 959810980 1250 959809730 959809813
    0x2d05100906271b080108061008030a080910180b061005040306050606070b01030b04050105180a1b09020a0c0c0b0a05070206070201020c060c0d090b09010c080703032714 74
    0x40c8101c260961000c4003d003100503203035030f000070014142c44d03c2030308039086600d50806905400c0010700c10b4040c0b40c0c3c400c000680d42188552101500031290307900701d550410380e142c070038400d4440f221032031052429903403008418815121101138000300d0a543c00c01c5405d0406800400500c21800f001d004141c55030045185130312813408640015402c2880300e6421358403440e06003070804080c0c50903100fa40c01c0c00c003c80d41400030504480020501c035001881508655a10f034020342034407605503c0c2009981c1400102030026000904000f0143d41e0384880c0d01125290805000c0650740110340496010b112004031940c01404448034039404641d400d44680c51840102d29081000200c00d8001c11b01054849004000040b181030a2107a501c9150b221074a03181a00300034062201000d00082e400300301c0e68042010500100b0b082402031030041444140301c0103000f0300b01160446110712002015030780090003044d0035112000c0140b100030349402000d0442d14050303608040501120415110300551 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 959812230 1250 959810980 959811059
    0x60703140f0c2b020715180e07020a150204080312180706050d0c020f030406030e031608040f05010c1505070905090a0228080a2d05100906 61
    0x750500b100340125603128000c03c810200310540901d45500c007400c0141c40c200750f00d001040c0d580941c1c5003003800d4550f1a642500c00c50b41c400421402e07084200e02d440d800304807018a045981e21a9540341c0080c80c101e0785510707010100501c1c138490810024818070003400364800c007004071940724001c600d0041c504c0d124100c1510074040c52445942052180040000d0750b55002006814070360200d04003040a6450400180d840f02100308800a151304100f0007485030038001d52003041a002c8640c200c2c0d0802820800802d90b040c004001079400d5000898200500d50108904902a06081c0b80201030102250355034240803000c440d03402c404a0300d400000b1044e034407071f05003d001000c00030f0549440d404c2810102c0025480903400c0b0000451500b0405080b444000e2481c0c50b084585d511007450760381e00e295220082120030065080700704094131a1404a054148074885400141d400050383d0070620b03503008082e400ba03403000212509090041029844030403503070101c80500f003a41c02c9030301040310204 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 959813480 1250 959812230 959812237
    0x8070914090601120f150503160b071b06020a17040803030601270e15090f130c0513021b010b01020309011101091a10230d020f030d1d060703140f 64
    0x141c0c0c0b214649020a2145d01c3c1d560401400082e04011440c8029101c505042c3c0390a8007000503641074810101c01c020141106000340303003540c01000e01061603141211000302c481c00d90750152005a0040c4091000c1c000b51110040503440c01200d01c0340b40a00c0c00382542e482e800010145818004826050004200c0340040b50110810049005a42c0358840c0200c085100082e03c5d414121000400707584250300b0480191809240f83d04e03c0031145548000c2d503080740ca513a0741001c070b4005944180000d084d481d664409820012040005600c0e040d6640345004500200340c204030423030303040c840c180340a40d07004030407500214002c0c40c1c10168451000e014030302500140a005010140d00d14080714642020684240141f040440340c4050076503924030305034040700c80c008118103403460814950b00e91070030711517040c00148058001d01c1e03d00f05071800282002c50642600021078914103180d109034900901e0300621034803c079038603400c01d0031b183c500826194030300401c0300164000140390350000c200b00e03003078 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 959814730 1250 959813480 959813507
    0xd080a03060b030a0c0e060403021c08040b030a020729060607031e0c120504180e0f0604150c050c07170f1b0405010905190c11010609050708070914090601 68
    0x1140da4a04041c0354136401401450b02100004142242c004800d04e014030845085a40040562a011612407000e000c0308501010445178650108000200d008001000e188241d01e10038005071114818101508041440d07017184460a840f43c5600c800e103c00056500c3d0842c5045e1810740e2991014a801d45649401ba202410280202006040441e5200100f600131a210340c1060b40c103500049415106d9000d54010401c0050310302c4500354540741d0315480701300810110000c443c00c1c13079202c40402c0d0070003000b501c080e160802600c003080e40722425405a01c2d4080000c0c5401803a02c0d80250030030380c030307620240075200ca92000d000c41a0b18035581000345403204101c1c0700941d44203001041403c02c5100010030585c3c00789050500009000712184141d0b44034800320000c43c6040415800a44020072118080380306101d2001103040500400b4070504025040c003600011b2a410815400340001c00c008201c0000c2014000045c89504c0e803c22440017400310030758158074151501c5c00103844200c600303c1d6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 959815980 1250 959814730 959814749
    0x100f0308040801060e1614090d03090f0b07080304080c01200d0b09041a0604060b0d05150409050d08042916030c021902040b060c1b0409020d080a0306 66
    0x1004000e100424005200b1989084003c1108680e60300c44100b85800442e02c240c000c080d40c0d8201d602260050f0040c402141d180090700b0b15207a20700e400a070703c0b2040c030001980080da108100303000c0e01c3d0300100800058134603000942d007808203595690700b544c07100501c0100907041c04101103618007070075000030400342c0d040c00011020900744107440040e0780062070940d603c14200032150429044c000001809240c03c000c00c17003141d80c0d07100552120340030007134190341c3c00640c0c607000051000c1d104800791000760054900440c007424002003100c040d41800c0115803040e85448030790b0340001e10019601c9028006410041c80741c1e40e6038144020081e81c84003000300b020f10740168220b09503202c0c49505100f00f202018210300342c406400200d049528054507031015034002c6080762401741c00d007064888a54801007021a40b03162040201c2c103160481c030581c4c000343e401044520492024002c05102a030000c5e10704002410396600010954030038940e001d0540300700007560803407030345c0300782c2007400a08012030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 959817230 1250 959815980 959816009
    0x3070f1701060e0106090303050a021011090102060603060c122203080103120908030a031d0a0803040210110709020705010b09070e030c0307030c6903080310 69
    0x804000342114084180d84165180050115002c40185501d0741620525910500c02505545c1d00b0ba480b0390051060f103065220f05090315401010a0180c0b0007a4508030b1219901e43e440e540003e0315001d006000203200e900034601300080c6031300c0380c01504c02007503100d43c070382a00b0b4039101e160712411440c00e080d10000401155030002031540002520341241d106d440846014128660308454003e014000c080a540040000351201c5201f03811031048108030302032020302280c1000c40300e4582403030005c0444403040c001c01084154a0f1002d4a145d682d01e017424105c4602d000d5015894491038503004981d840c0b50b0100340e180500c002544101c0380428040c00340201c5062100e0003900d071250a01388544644111031610bc6030342000304844003201e41c4410703100912400c0c00c0440c0c2c00c05012425440b118034000741e00403c9019450298001c3c10307070014116160b88442da800200b0046224403000c000d82c41c880c00200301f5120301c01c0030400c4940028510b6201c0e1070b0b030000225420320a51043e5511030500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 959818480 1250 959817230 959817239
    0xa1202070b0f0106050a0f180f0e0106090f0b1926040501050606090f0409141e0606180a0b0418030305150102060f16210e0706080603071403070f 64
    0xc00c1500c1c002c40c058102c05420740e9858500320b540c1e100e010121000501c001c2c80300703424a40154420b50300001c506881000d1356403101c8014040d00170030351105032669085001041420340003a0411302400d50082c103105054100082c450891045090780076487c404440802c407880d2140c0110544255079400c5140303030580c2c0401c0000140016541510f0355484d01001c1052450003004498008202400c3c0e00c00b140007010400c001020107620076908200005401c1c0d000740703000c0c00030200b6080d00d80c4a41c44922401d05545240c890014482030007000c00c0c0f0390001032803144004669100090700300209040e0000c50224001c0d00c1c0907440c0e410790502c40001402016019001503115003e01c00d5404001046040126980d040c207450111445800801090129006640d4654204064281a43c0102078440d03180010340304411a40c9081e56202c00904550006114513401407586141c24602401c148002a80300c604600c2035002040d000d4014110039101070055800800c0305560682d400d0743d86 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 959819730 1250 959818480 959818493
    0x31e011b03091b141201020c030c03040e0f060607061a030d090e13020d0201050309151501080f0709050f0f0310150806041115160c170304080a0201050a120207 70
    0x614000b194a104848080382e040003483c09110119041d286500a00e4000300e4140000740d038290039400c041d95003c00100d500d12104000405840180400466036145041943c00348004083c02e401c0c1104420b5060151a9075142c050303d5900f030b00054002000039441003894407200e20380b40b03019010b010381c11000801541012400301154500c1c100c3c1c1c070040d031b20801420784004402c0340081d4480c0c0c104200901652017140a940d00c1130500c0d08440040341c04080700402d0110484440c0258111004c0c18601547c0c03203401e16801015144194655081003807011301280050702400e401044104440705d00e540c1c800c00c0b14184844d015050b00e160360b010125503006003030708204001c0a440403440000e110b00b00003070424425074124071107010b04013003401001001e4902c3c2000c503000b02070600c111046005415140200380e48203001c0480d8542c903002c030844003142c03455414000c0342c00c284010040007a021602c00f8009030b0928000780e0340c80280005032616054004505141d500c04903240042242 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 959820980 1250 959819730 959819741
    0x903150103060204090e0c180718140a1203020a17070602070809010305090a080a030504060b03010c03050601140a09031202161202013f060b180405090705031e011b03 73
    0x2502d035406d008601c07000420030b0341d41900c40b2000b90451100400c0e680450b08120708550401810310304072101c015248807000c1c4030300445c0c0060844001e10003c5510700d00d00100c0c140010584880c800b003800310b030380d113000c0d452300074809000d80391690940300301008061840466040582c042803c5442e0b01d010b003400150b41c4c010703140d0755010910340004160000313130004220b5441a48021810329010104404a020b401c001c2c200720741e010340f00d0641c103245507000c0c012407507202d415550005040ca00b05000400d00c1218403181c400f980f90170070003076080950100150042e81d400c403080000c40c41c80c1a008915003031500c0155144804036900114407038508000020005000341e0b1140540d100ca4581c040117800d000116018000b00035018000519240400d0f1000e80604403002074010f42c0c41d0541000c035808201c0d030740d254100c4100803920340c6c5400c2c802c0707a40024090b001400740c20706240110760f81c2d4403045401000b01c0300300040300428241c00d403c28000302040320b44001881c004900003401804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 959822230 1250 959820980 959820989
    0x60e0d0203040504200703030b040617010b0112050c090105071505100e010b0322060e10140f09070b070c081b040c2f0307050a0b0108060c07170903150103060204 71
    0xe00b4042c0c0170031108400d4030303d076641c40c5000f84250300d040400d41d002c4d00240004890150007586900001132911001c00d80021301030801800810480c5001c40014000035080038010003890ad440305200c441251441507901409081c01d00b0740e0303143c240341801040c00000400c0d030b0703206505040800c0304502d01d0300f01c40011200c035060407501caa600e42568241d18081114055800b80300e54a4024809040d940c1c0da44e51280a10b4002480c0c00d0103248583c20720161044120750f2039200c1029030841c500e800c3c12294000c203001c88840860078a03004450702ca0b001e40c4103981c040040031660806100350b814690008040c0d0380704445051010218465041e1a00314075140325502c1c11031510602030291101907a045400700314a42c03101a052000308580071580c103c2100d030300c07052261100042c0100080d51780540203d000c40c000d903240081d00c41c503008000b08149140d941c14440a0005255944100343c440d0096691b20744880c0310748042440c01c03690005058103601400000414400c140d030061059030b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 959823480 1250 959822230 959822239
    0x605030f0f0a0209061201060603063305030c040f080106150518120f03030a0b210714040f0f050f060406030b04080717040b0d0b011d0d060e0d02030405 67
    0x80d5500c0c52074486a01a003000c0311900081107107030062906003401c5900200080407403445e5042c2e081050308407001c030f8101d0310110707548076030500a0a18075074118031482c0c5c203055011540310052080ca42c03590210210401801004000b0840b5550140c0a8038007402d210f920420700e80350f0b1900501d019003414420100d031291889001840144513a04548540210141c02158640600c090048000c0344031a0700c0424022070725070440103c4240011801040200c0020811490140412503502915a003400005900800001940401180ca0f03000c80d000c141d01305800a881c0c40208001e401d41c0e1100d0f080c0b01c2d1074080e0816030012181d000074041c001055030000b442e40c0d11400c0c841140c805002c050300d181441c200240014241c5401002c1c018810195001e04040544101020390050303001040304040c08241080e040443d031141401c0c0020901c2c0c108140c0d581c2e5a50440c0c00e188038148240202000503074041802100d800c060040302400c802c4070041c0c2602c00c0025143c0d0002d02403103204 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 959824730 1250 959823480 959823493
    0x7090c0305040f0f02040f150f05010903032c090a050f0906060a0506030a020903010e0d021011070201112d0609010207031b0311060c070b07021b01030213031401060503 74
    0xa2482403055921443d44003000034100b400a803030398111110461001c0341e0040c3c41e200315044840080c001e8000121090120f20300d040e052034500c02080c286074120604000c04040100080f0b680120074000400c0000b003851001c00d0000e070070b9140700c20b050142c10740040700b030b00a1044007a116070029100f0101c00034003094684800c00705588411040e204140d01c0002c190303081c051442c0c00c000a54004410721030040c038041216010034203403040c042c81e410131604039455110345903805000610742104122401c0000c0303442e5541c15010ba00481e04080c0c10000010240b9030b460310200420311b0164150341c0d400315516102d0340051074080c094080c003a0280a101c020803407041d014025902c1095141d1941c2c0001d8000c400451400440c28605804000c0340e8a5003c42c0b02c40c05108007070061031a4010180e13203101c2070421000d0b0f00d40141c00c500c00c55001c13500401896601c6a0200e01c0201c003441d0142c1d0361101051a2080c481c070507000500424541d003032001c10120150b0100e0b04076402a81a18074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 959825980 1250 959824730 959824751
    0x411250f08220b19091d06030f01050105180403051e0d0608070305060402040209061e030a05060f090414030922060b0f0301290a020c0f0609150d02070f050709 70
    0x3158202d44515800b04905000c1c0c0381c0e410413412000c1d0700e071410b145462a0859035480a03400c1483c1111800d900031413011042c071403c1e081c1403082d001c0d01410369000f0301c03c95141c4000f01d8031028200c00c000040340c50b4100410304143c45501110108241c2e4811517446902140d0b0410a17a4080c0d40381211b040e00e82400001c24160110300f4408803900000908890345e116000e110196000c0e0f24402d60200042280143c1c01c440c0c40c09103410f15415143c0c1d25100c3c5081c085007422103102500c41c900c65611009000100da4810000c55486030744502010420710202c00711030b103140141c203812540300441d1768016030a045030200c1c0c407040c86051702040c050141c0d40c80c881ea4051082c8203040742009010001409408005143c00240a1004100c400311408103a11500c91740c014a1540300142c0022803030500700d14142480c4900c10310103c4000e03281c0740d281c4c0002901000b94a03001846e5810109888000b4405541658070f03e075080544504482624640692101c40d140101c01800f40703001031141 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 959827230 1250 959825980 959826037
    0xf160512090d1e02061504020f070506010f050a1235030f070e031e0a020a06030b13060b091e090403050a0801080307080a0c020d020406230411250f08 66
    0x910f460080d0003405d180e844a00c550018580c044801c560410b4080103020b248501e503400030050940034a028094039410000d1002607031140d588460301c0707804003240500006000d415034600840d88030722070b030441c02406081c031101800784440822220356152180f5504410440003584142c0380408280a03558079000c00303556041e6890000d5405901c140e080d0308400d04001304a80422011100300d0b11400c10507800a5040101504000006900d0718180001f81c1000c110301d0350707588a17140c011300810341484c040c10a6402903400fa9445800b4504000c42001c0f140c0ca6034a00c000d0014000400301d02d0681800b80c015800012032800092040c000000d10300e00200079500c01c580c2c804181450080e40d07101c111103501103070344140c0c0c0c003030100d906c848010b0751184940001000340703a0070401000c0c0c0d0010610460603444502d2402542814080d00400194000301c403401c0e07548001d0b5416068007a540b00c1004001420300808003285a441001480b0716034000d4410b0003440209078801609411144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 959828480 1250 959827230 959827277
    0x717040609060c1419050d0e100c0f0f030c05060106020c03191a101403030306090432060f06030d080a05071b0b040501140f160512090d 60
    0x30001800020003801a240b00d0361031032586034010581c030511400140a80740c148150445a02d0b8420610035148080000500010a00403118104010695065404105c898020445d58010000110b0f1604104010710f0102c0481603000032540c0040764071490054903041999000303860307134801c041c000070344c0d00d10000b03001049180180140000341d001c912000e0641d4010f00089400313000c0242c036a450301c2a200c0e801e5100703110584150048900d48041d0440080c000f00802d80070313070000c0081080f01d484814070180c01c10791108800f4207000440c024a14200e0300124242d2401c2c814050b24a1100c0002441034013071917188407008031a0304c8203000c0594814000c586800401d178403000242049003582e203c1d561045240c10704030304c10038801001e52072040b0f1503603045a03010494018041400002d00c82d0303285407500ea9801102c2800c0c201114011201d004040340c901701404a0842401841101900c02c1c4100b4011040018103180a101c3e80311081c005520b0002200d50448008021200461 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 959829730 1250 959828480 959828489
    0x10080601031110030b031507141e070305090603010b040503010b04090203102c071815090c03140a0207120503070903021e06030907090f0204030c12140f03071704 71
    0x20800031403588280507000050f8a0160181a40e0b03149254480d101400420580081c4051980c22481c040034043c0480184400d221b04094081c044215843d01210b0301d00c1103280752540142d16010107180c01c4400d40f190448142d00040044000a00c01c1034a202500c19617000320b009000e050468003d0208440c1658400782d0b03d81d010341034084c54080d56a016401c11014040d0040100c450360188200030306100c1d0010034158401141003101030401d10244d1661060614213024180008400d03070302c0b4041f0340c0500303010556150507000409000364000041c0340c00c0c0c0d000400007850160070540080d00404025107101d440c52510141c014407550481b8030500d030648030000d5290840d000c6c04140da002d07811800107081750480d10b55056803100c000c0d501c500d02040c000d280980c100781d00c1030706440b20034503190100780c0180000d2000549204041e0b09035850700c888000d00703600508100600d002011040005070107440142907240d04044010400103009642c072109010040030fa60000744103a104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 959830980 1250 959829730 959829743
    0x501111602120c0a061709071202060d020904061202030c01030c0816050d0f0204150f020d0806061b010f0b1f110a050f0c0a09140718030602070b1008060103 69
    0x800610381500d85416601020040b54803401043e0302080c1c1c400000c0d080300c40410700007500c004907101c5541080f0b6004040d1001781000758900007070300d108a9081040248680c1012914903940170240c1d0555444040003001400020340d20b5030340029030380300000d00340e000340202c00c030185140d4000d004c0c41442d4070150b640c2c0c4071203685180c0500c0100d001703c800081002000c0042c80302c440c11900405460902c854001a9a1840e00780c2540c80c003906440704070144404101c5221455401090603207548980341803140081d074490002407030382d100d04890300c0c1701101c005101e54500c05c1d0551000f0303050f89810104201f0001204104112052a07008007005038a100c0d60318004188107144001d411343d0504e080f10302550f41d0b03690f5142440b10346840c000301540b2826015005160102c600303001044c0c0303000100700300e00140c0d10080e4412002064007081c000008500d49042a240d0394040c0155002001191078404502d0240c103205810b44850560f081644004114124003040d501c0c1200c1c0d0222 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 959832230 1250 959830980 959831017
    0x9030f080c03190e070909140d110a08070f080712020615031b010c0f060504030e0d110910050d05010501050901050a051c0204090c09050405010e0c150d06030c06050304050111 77
    0x41001c001c0e02c41c02d0f1340385440e4081c1c10f80c0002c1501d0b603801554000d52250901c501ca001025000070b02c1d01502010160400820040e00e80006001245021010382c010b2242039175960340b4184146035a0031500000c0c4613070400514070041c05807804040c200b076031550b0b09440540e00c0b4520035000500c4151102c0e5807641200c00209aa402c0c0301d581c0b500305201c181400036100070b458864034100001c100f426140075031150100010182e01c5a66030b00140c1e812104030204590710780b55146521441241c1ca4010041000868000105000c81d24020400200100b40103a05031a00c036002e46400e07c00c890160b980c2100105451500514000540c1d0016080d1074210903002504005102035400580e04540d44512840c04110745860400203001d6060020415090515109086038010084440c05401110308415560b9545011a11141d00300c189251280d1084109400500c9641d00040120b040844000b42064001016502c200d0080c80200f10281c000f1055131101c1c0b041040b00101c0b1150348 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 959833480 1250 959832230 959832271
    0x806040c030b01020726010603030f020715050301030b15040e1e060402031c030204052e080420060d05150a0603021801030e030c101d031c0902030f0109030f080c03 72
    0x40041d8500c28940c680c0740c1184040000c485c1d403c48445800c00d034004bd00ea17010007501ea40d01009520000c240307080e80b00105014995005000d4001130000402c0c6031381c0071000c1030481507903010340c0090a070001c0c81006100c03950001159108e1014019400d24030051130b5440714444081502c034440d076005005001002004100c1c50b03c40c07100d410b481002c2c107900784000b0403036464076400d000c64031040c40c000a800420352401c0240003400742560800b08800c00c010400011144421507031450b1800140d0b0903c4480030000901d80c0c0500c8860241031450b000030007a8000e000b100d00c4c2001401565801e1000380c480808a00381c2c0300310b00d814900c940041000c0d901740c1d4072981c0529490415181540d050080e040803940c20950710401055a494452200d403004207070300b00b848110b04000d20000c40c0f50401c480c803c401d600644405100d69295a03407803075015900c003800940b280c440d844d002007020075900d00e005003460008034400d0b03000a0b06040040d5135403040000700ca001d098030011040686808 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 959834730 1250 959833480 959833499
    0xa06140411181504060c030e040515060306010c0f120e0118030b0c09090f0a0b0102011505100c15060e0a0c020a0b06241c020702010516210806040c030b010207 70
    0x20b000e8690342100c07280f41c2150204034a81c0c050700191000ea541c2c00000e0303806041c000c02c62014440201d114034a40024401c00e64581403015107801010b54404d5260390700c103401610003141c210000b50001400c0030417541000300c600460b200e000d0b050703210b0040f2450000011215254810190701180e03031301510a0010030080050a03500c000c01c20515444c2a00c1c0101180da46403040d1003c4104100344824000003800781d0242da4036102d400e1008111011100300002c0201d40c03c3d10900e1f0081002010240400b48a49800450f86402850140c002c42e44500c1d002d00428040c42205028240c803008074444101d2802503540c0510254020702038540b16448901d6480d074058001a07004406078040b40036400007244413103d5034105000a40c0791581079400c541020b50443c0c2c80101184100460b80040c2e1308042640c12140320340f4403070669400240f8100404800d000040070001c0984d02507401205d1307100414920900301554144842503030b442055003130b6101c1c20040d50145e0060841809200030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 959835980 1250 959834730 959834767
    0x1d070b09130506030106050607050109031d130e0307062d05010b03010e07020c090a0605091806070f020705150304020f0f010e220603030203040e0f010e0712020702090a06140411 78
    0x10081c00005e403207647c2c0780092030341d50085008481c544d4403240680141608000c0060340d580652007415280b440780b8000405482450317408000303190340c82c000e905082c07100b003040c1c8a0083e48854100490202c440e140040307050995028140c26071600d50a210707441c040d02810f03049440f00075803d41141d080645880d81c124000304010114401c000b80c80030715990b401042d0340500c0f030310701c000500281800d0a0000e640b40081c40c9030f620795003440d020200040c00095944d481003041c45d0000409441160403410304c0690740c0000d81c0490282000707207041030044000c0d80a83d10032103100000d298144103200400f504404000d0114458482015450a0040281c60b5940c1d4018425400301140071030301d021225103400580c010381c40410203001800010b000340307410040c115409a03556141c100707800b0301d0000c0101b100c0c04010030020031250318105501a83d0007140e0003400d50b110752805200201c018221071081c900b0080b091620540c440c07e180c4140a8a00840c040c0a8604240c400710740200c40c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 959837230 1250 959835980 959835991
    0x6010b0405180705120c0307090803090603061212030708060907020f15060406050405101d0411241902010b04060302010503060f030307020a0b070c050405010b09010f02030d1d070b091305 82
    0x200408024001003650f246d20540b0a50300e15901e03404c107090300400311300c3c980d0004030762940304100710f600c16591001a25405070044035442c2a0f08168610641411203a000d49010700d0408401d0004d82500300d00f100e40b194100342d540b46415542c2120490f600c42e040407241c400703074024294103141050380300b8106501c11000360000c6001aa40c802185c00c5034003c0301c03920380002200c10b003800070000ca805941680c5c051b890b018181400e060300c50303040b04012018280d12410303a0a20b100c540301034281c0d4551b02e400d443d4072419100c000b010800c080140190b43d54000551034002c0640b2103251034440d01040d250113a40301802c658410741849280071024800544c5440b0900c030074801a500c584040d000f800f110308500f515071500c0d01c0c0c1400c0500d100d41015104a04100061000001c070b00c080da030805900b4a0240d298440030003080e8250f2198038078060200f403c120041d40c1c99407075400e0701e61000d411041165107031591034440b05600d01074800b8241d030042e65074030640840115904901c0e00322 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 959838480 1250 959837230 959837237
    0x201020d2c120307031115040c0e07030f020a110c03070f0611070e0702030a0815010e191e08060907050d1203063201080906070302070f0203100501030506010b04051807 74
    0x307102c1c0607440c5400071071040b00020505d51001008880511090301c201c136000c1074501c12420242d46006000000740a8824036000c07013000240140d1194000042a0010310800c568400c15450014070080750440754100b0b034400d061011504e424001286021180740e00003041300745041042c1101c07a0105190410f0b928441c5440100e943e0b185020340e240960b06d560001d540d1030044140c042d111500c020400d41c11034a0741c092003602c2d640c1002e000c120514049811400085656036035220300c06041d000300091a8440443c1c4c00c501c0e800e0b0741c02106036000d0100321b4002c0d55038401c91680c4e4081e18029580c1041080310302e600000d814130410200f100076400d02140a43c0c03038075400346251101c43c50024801290004400b03045c0d181040001c00c1e41c5d420310301b5183d0303494001c035125030324040680039104042d800240c0c80306101000210291003903006007500c800d00300009624019107428001526240542170001500c01c201e082150101e450143c581a10414880850000d160009000d401413 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 959839730 1250 959838480 959838499
    0x170708070f0c02032e020906030a1d0f0106140607050c0f010207030602030a0c030e0c03120f040f090504050d0c0302121b060403230f0403021302040b030a06030201020d2c 75
    0x51358140200748121071041e521041c08032101041000710181c84551016452040182000c582c40351002c80b03071b101c0354001000c150000103007007010501080541218407801020094080204190010782c12207035040b0200c0c164400b0031007000186e126920703004080303a0282e0816007940c2443e49181c1c41d4500b0500580700e10070390300e45424042e0390084507401201c81da14400003c40c00e80500c604c003040900f0400034001a554000800da85148504030406c1c01c400115580c40c418038100c040320050511070440ca0340007603696161002034281660100d5607405a481010401c1d4483d00403446010b4142c6d00800c800101c40a910f40164020003015560b079140c40c004244e410030811801c0d020324801d0f50758400c1c280031b0701c8550500c40c01c003490305400c0700400c2140399440110501910152a01282e80b06400000c0340c0302c28009205503404021180307000f20400041d541d45e07900c0318040364000c4e025200b1a43c0e00000486803000c012515911031082e050219001210420344a040e010703025099111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 959840980 1250 959839730 959839733
    0x1239081605011407030c0215100b0f040f120308040f031818200d020f07020301060e091908192a0309050906010f08090a060207060b01170708070f0c 65
    0x600e0452050a448503034480d40000c0e08000842d01c0198480c4882c6010810520500f000075141c20804410b00801200b0030041003400c20741e4040701000309a0750590a0380c0300900b0b5000c0e00b00790028881d840316207a90000005000030b1240b5400c040c0781d41680c03100b03031903586d540da000250700d01c21009a0400c1401c400c804040700051a84101801c50000724801030300181d100b80c4203541640b10410b05148410f580341203003420402c1680c61700102150b000d41c40780d92440200b41c543c058058007941c590300b40000001c05042c3c90003c2400303444824140d62509140030040040100c00079401001d042c000c11214148540f02c00f140601018640790004041607031061a11459440403000034500000300d025000300740e00f0a0a2f00c0050006486c000a240307032410010340103a21007807072102400441300008140e000d0521031400c01542c48031085440341c40f1410490010100d124259002c1405d006200c03410380b040c0802c0c9803141c1101e81d41d618441d65481411141e60505100c0e040034403022850510 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 959842230 1250 959840980 959841007
    0x170301030c0302030c1807121b0801030201021002030114060d091a060a06140d020a2102040611010510050f030c041107050105011e062a123908 63
    0x60086004800780880309040d4010107003800140210644103140c500700d0114080c0a0701c4241380e1203d101d0420707900544507180003031b010b000b2410400907120014194502c800d03412035007040c182c900072380c2101c0c5540c4038503035904100e01c028000d40940021580c5030402a2800c200101440b6106060106441c2d0045e6241000c0c0700925080345042403c107410040030341403581d00318000301040d01e0005592418117070414032030b21400b0721300e00c201600002c0c8485010701030303902601e0740c01440130700c017003010560410700c802504039010390000036840c0c1d0a21040b030300e014042c1c1da000c3d10108065010340e07071800d0208141d0008407108136806006030810008a907032244906e030707010f000031110143d41345900c5c500a401c40344d058200e00324074030340c0285000d4940b804047c1c49003502e003142490011540d40c0c0700ca00300d441400c0911810182e061f801940700308103208024150031410390b1140688400090080182d43e8220451111180e0316507007819060104046928061401003101034039090a0480b4030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 959843480 1250 959842230 959842237
    0x11090c1e04180f0e010b090a0e01060e010b0d0524041509020d06080c01231e04080f0706030507021f14014505060f060310170f0a02090417 61
    0xa1540d2555001141c0340580140104c2d007401812400800101d84000c00140d00000c000e803100741195600c00c02d003819541c2c00d505c220041c04e410000b00703100e0760350350304078458590105014070004d038108004250961a05002442550880c2036800758103204c071001e01004141c9460042c101c0b080f4420300142e410300c070740300402c0301c0f5800c05000b280b102d09000302e280c58442c11211141c104402e81506027140b1301007089400741d0300540300001c0c0d41d402c455100801d0910001400c0160140c001500003544003000035480d2800040300d003550b507040d55441c07080d0125441100d0180144c0c0000240340b54040407100306882e1400c54910014000802903418003068009030016580c00170020800ca401408031444000901c0b0300c00d80309000042c1d040742440c140b0240321103014009440d03901081440d42c9150900c0305404020b072140c1e444c0e240880200c041c0241d50f1042d0612043c040080305100c42001c10700030900d45892000b8030b0191000d41c02c0c840c8050300180180c513201e19243e8072800c41403e58008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 959844730 1250 959843480 959843519
    0x3a0606020c120a020102060f04050c030118020316030213020703050409061d09010605150a0e0315061212040b0f0d0c050702011209051c0e0603011211090c1e04 70
    0x41c508003068070144801d2050060400e9010703403081c2031860050b82c1c00180d1540c082c3c84082d9515203030300e6528046103482c071104001a850b50a10018440f4010a040042c0d2220b0084007258a1248000e035045441469404003039000850720302019000a1950010020903110b8030303019140640c0c52096100b00c2c1c50340e4100003400c1d000d9109203003c484800380718540055080000308101442c10b000030300411800024010012408201c100c80140a00c2200c602a37201900703030303808101c02031003100c0b01e01030495115210301c22800000e142004006001264501008491468035044c6005081c2a80241d1400300d610030003040b0400c000003260186000240b0310391034680e1500f03034602c005440b02e00304007000f0b6041480c2121000100d00c001403600380ca40da004428107259014164115104c081c114007141c0c0000b0000300010703420400c3c41e00084098000c05c100c0701680441010012050800d0f00c0201c5464030070f00000c0700465111089c0003d1051a801091410355501e0b00c00300807020f02440c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 959845980 1250 959844730 959844733
    0xe0306041a070f0e010c020414070816050a0e060306120d02210306281e080d110d1103040f0905060108160c061a06040b0d0b063a060602 60
    0x110500e6000c20106102c1e0002c0d202d00b042110010b001c1c000511050059462904001c6212044425034403581c0c090a00307182c0380c20714164286800c4802500020f0141d0341d200f010200824440c14403031180094030a40405541d9099410040c401000300c1a00090102d03940540d918181004545d4200302c09102000b440e00a49015030030600d41942288910249104450b02002007000a0340c0f042242100395441c425a02850070b01c07507105580069540d04000903150100190b8601d580d00541d0030710072035440000f1184900c103594021100e00107280c2801c1030b55408805140195806442e01c2075000c4a0f0a00702d80c1456905c940c1c01d26206a9a8040d0340d10036519000e110a5580c4640d842d94020303030f0209544d0900234114401001c2d0f940d444800f50403a5501c407000300180d1250300d0181013400c0002c10b400e40703d68403082c0780b904640c4600e81f0718054610f0300d030000e8428203120080d1107405003d0046541700040c0400082507107451000c204902c0c0071420030407045003d05109000c00390000c2c0d070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 959847230 1250 959845980 959846003
    0x8010203160305010e040221070e010b0d0608010603030509060a110d09030b1003020a1503020f0a030e0d031806050a0e01050106030e07170303011406190e040609050f0a05070e030604 80
    0x14002c1c08541e8181c00080141c0c51510030440541c0740c41d416940600000c6000c4105201e22404248c01d0801582001e2000c0700d0b00000040d21011240141485001c801c000308001c9070b41d141c0203800c9944a01c001000f041c07082c00a04001c0c900240945258030b007a06080c41e0340f0b8844604142001c2c40540c0d5503010580d44a401d106011741c00006640c4101520300103100241180c00107003081d1040d00c182641c0c802c4050008815078401d4043c0c0d94400650803d0948131074407040090b003c0c0c000c054a4000a2140700107055999101c3c0c011781e1441112034410068039125615404c1c003501c40101550000d0307480d5110784680320070900c541d50080103655000152440d00d02c403481d04050040e485507020201c28032107c8040312010003181d046907904000d0711040d92242c000f0030700380d01400412211030250b08511410060708040d0809440c181110304200c055159140c03001203a0f07003a035108500c07215510001e220b010650b4052900032215060400142c03122000080c030b0008200da0842c1c0030154107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 959848480 1250 959847230 959847271
    0x260606300f01051e100c0b0c0304141b010c111809060c1c090c08060a0606030507050403030f0f1218060e0c01080c0706110c1b090603070611010608010203 68
    0x41c60344501606085034562500040f10f030700c0038040c0d1030140c00c1034451000040740c040ca00340241d880d00030303182d03002c0359803107040c9404050301350b85820845043d218401007584260310340c40c02184401907800c10011500c180300240d001150204d002e0071084820f01140e10a598090340c60100640703003010b095084012038501110518100507016103500e5280100f44204600c10648030a411518020302000095003200760030060440341850340703d206540108006d01032905002d8109505a603030a032014092512180320403641817203030b8440507002406130750102507281d02c03c1224515610403482c0c50144501d10712021030403900c03400040f030000c81070743c1d0400c42080038034012000e210300100d010300b030310401d0007001030702400300100f40d05410100003880d0070822886a102e2408030513006000b40c0c840c05d0b031b01c24a0342c2e01c028284811580a40c000c4180180c0d19009000a10400014000e045000d00d01901a14242c03403001c007602d0103540350440414010424400b840c491034078101420254400e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 959849730 1250 959848480 959848501
    0x60703050a1b050a151116170a09080715120c020f031804180b18150106031d161a0c0a0302030a12021206011407060e030a26060630 58
    0x406600c01744103040071580751040805030180e50351005030560001d1204040e18026402000d610340b0782c407400002140000c01303187d00852100698102204485025880d07908032485036100708005070000b0a03c3e072681f03032007207503682042605207400e004035081d00003003100313940c1190040d50340c5542d0b020341414004620f1501d40118240300c610b00d41c03200850300b405c0e01c624460400040c5100d2a0003042d18550500590411046000d201301138580c49141d40c440740c004001d401c282030703000c102c42c00341144001400e8009c17481e01200d01c4814066000145026802410b480c1030000130540c100c4240024a0b040a080c40f21641482c4650f019655942c407480020380070180f034688480403544107003e0829512680510a0b41203a0309007001c0302c41e81000c01440407644688880103194030b0400800c03002c060030020103421946002d449244d140084c2240100246c1c0820080111400103c4082030341800c0440c01480c03981e000410302042102c501503d0640500c03030449020303206c03c7c80020003a0800340b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 959850980 1250 959849730 959849753
    0x108060a060614090d1a040b04061103090c040b03030706020403122a1b150804061a011706060408030f09040f06230a090c120501060e060703050a1b050a 67
    0x41403d03c8004078084645004482c01843c2109016500d581d00800030300581c441004608046000740002d80d10b000d140c0081690415201260258149041060300c08218401e0b24880c901d008010149002c0740707010000940848105590180130402403900899002e00040c405580600c46800d150407000070020302c4299424075816901c05007103030300341c486000003603401c40f801d401190b4400c0c0020b0540038154805a503a20080c40d807200f04082e1411650400710861040d40621000c100303803500902484000740000b00343c103000a02c102c0e00e104140340d2100f071031600600301030300541c01c1644480c012071440c0d22a05c405d801c6003002051092051403d4003401075020030030300092229501d82604a40c509210742c480114845103041c0340b01503900c1d5129500c0082c40c02d04001d2103031007003905e0003404503240128440710481c01c010000c550701e80510641c00e14100040d2a951800c0400d4038110b4558000c03402003403c2060002e60000100d08001400322010300400140ca0301c40311501d8207885949 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 959852230 1250 959850980 959850989
    0xf03030301030209040b0c13080615060c0c01110102071209140406060e1c0b150a091802060a0e0a030b070201050915070f0201390207050d0f0f02090108060a06 70
    0x2401040107200503260500001d42182d44081134070b505e0f407074881c00300f0241d02840e2040c01101c000d40c90000790703c403000513407a40102e01c409400b030301500c440401c0c001c0e2881440d051410030b40c03118640344c40039413060241d0a06410280001401e2038155541d40304203a104825400004e10010800e000203c11500c90010380f0108803001c0007c0381c03a081015188103c079040304da1007201e00505d0b4500c1d02c60b5a0013074000742984420384010b68074141a00001815400198500032140314038041a0103507503205a40c5140500c8030091145011a42041000d030300c240200000c201c1902c1e03444800780c0b03480e403e8401a5220b241000580c0c509400024211040104140501ea000c002903140c81815991076030b4020a441c5400c0003180a080c000380d01500401882030141c1c3d0808a4800303200210301d400a03040b506c2c0e040c0d01d810b15031809204a0351101c00b030207465444051002c2880c000b03107034500014802c0b4410b00d0280d0303000ca80343c0c000540743c00c1c0907070103010240c001508110440a09204150141 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 959853480 1250 959852230 959852233
    0x605090c130909211d0303090d1106040b030c0d0b0613140402130e150303390105070c0203070f030c0312021e0d140406080f07050412110f03 62
    0x401c0081d03020a11a085116101d031a90355452a0010700c904100382d800041d000c1010501c40f548090b000402c507012040f118003c12136400444801c0340390200c03c40b444121300030032442c24000540c903402e0004200f046013607030260b03040000281000a007400356100f210905902515060a41442000c1e139004902c03451040504201e4225640d802014010507a40d03000b8640201080d004c0200b40240f0503085020100d10001e0340c0001c0d00480406034511890b01d1001c02900c404000041c16500c0c0240a1581c802c004519004221a41c091210409441009031501143c001420b41c440c211402a141c07500061901030205056082c208a14401008407040f18640c191464aa4031402402400020041103a040607000c4d50341c420080c444c007480c610005106800c1034844000c1d5221002d000038404501c3c0c52124804080d0440103440445603607032a001c0542d640d5048000710800c0003804070003449000e10010038000c510340c0403491001d1284141c0b03086540104200300d0341034100ba1046209 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 959854730 1250 959853480 959853487
    0x111030c0d0506011823010201020712050c0705061c0b0f0d020d020301090c0b0318010b13020c1011070b0c0304030512090f06070f03050a06030c14130207060605090c 73
    0x100380d011012a501840316600c00502038480a0040750460344429005030b4004c10701c2004501c5115440001d5a002c14030300034089112130441c01a803d030f02650700d0103000c580b00b0b80c09099401e030068000341115030105040c2e54081e92150000340c01c03034202031a010b07250808424003407076081540c03085c0c0303110800403110329491008110000315040540309000b4000e000588419046407025041070403540d51002c0140001a10b404404620745c0080310007103d00d481226401a2152040c842e85903860070140c2148900c00180041002030341c003400134040684a039000000c0e40d22036a1090305803c0000d96015130351812282044070b07020401402519201c442041440300094104003164074103501060f01c8615981c0721145075080074640000f544240c080c6004000d0300030f40c0001d00d152245841d4408205a45400c200f0303008441c101d000040c02ea0400300b00602407880c1a542030074540c60020310340c244100030114410240d80003050111005e035140d201c01d1015140030160990b015602480e90f504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 959855980 1250 959854730 959854741
    0x1020a081f1815050d4b081207050301150207080c04110c10051e0624040b0c0106030507050d0b040206070611071401060b0c0303010308090f030a06050405011103 71
    0x9a80402ea58800340c020f540300010000841c040c2000001450700500d06040e5001a0518060850446a50200c4c10002840d40d2001000d00412141d07001803d4488100d01e5030003000060a07041c22040a0ba8042000d100c803000209043c3d0125100740419074400ea02c951618202c00f000c902440303141d50564101d01401d120400000581800c44101103c004c501914500d03200041485242c042032845c0c0601000d0030350101103904418040c1003850030000340c0d0300c0080040881414151a00b0b13030b11900244d0342e002130715580020200a201d45440b107900e055650a01c3c01d0003503002412002c0c103039464580800c01d004080c01307698010901038407020315010240d0350b000100c8a006000030306c18000400d0350f030144a010b80c800b450030404100507682d91406400e01c685031100e0421500d11030741c240703031000c144400f07681d0550349e00124540040d070440e400c1d66039400c026003007841e046e038000c8001942c0341d40a541c00c0182e114044d008080c001660f041c1400c109096400d2043c041100c0c00d4100144030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 959857230 1250 959855980 959855999
    0xb060402210c0408060106030c1d011d030102090a08160603050c030c0a05040b2a0102090d29010e040302010c020c011d030a06050a0b1206060109030f08040801020a081f 74
    0xa0203001c2080078000ca64544060461502854101d441c1a200310300000c114150175902c4404081626102c800b40000b11241e10408941c1c0410b4603400501000c0c10900b42c40c42e001d0040c5090314000740090f003010700171000b1800b00f82040d40180540c0e4017241005d010030f060f00d20301c0703009050545420b11180c505244800c0081c4406400c8895044002542050103441071059074054182e501101c3da88007100500103000d50000350b00c515100729005d45002e11001d05100716900e20308082d11010800c002c5071a1f40d400070700d01e00030110300a115204498030303140307080c28844c1c0030340161441c0200504150034024211200841c86006550154a0b41d54141c0c1c1c101008049109000800b103c1800317400d030202c0e040180b01c20b001004241403c0610004140301d80152076010001d64000c0c3d901145403ca05a4907081512000d0110b40301c000b05001068108590b15a200c1c040c0e03811030302e000c0e503510f101802c81e80100032180000d4050790078040051514902c03103907401c1c007003503801d03100c2405e002480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 959858480 1250 959857230 959857267
    0x120c0e12060f01031b0b0d051e0727081002190206010b1c140c0915120c090303040305060f070801142d04060806160c150c03270b060402 60
    0x94140389001440d85d40840954081c00e01401410b0340711611618401010b601801c01500c0c2c58a0720011244c884246040d658801403040580e80da40518500200820910130f9018001c00200f0114906009c501c4003410040302d4800004044016500d02c220b500000f00c21001403020030864201200401890704100150703a001c41c10824801e50198180e0040e0005001c5a01540c1d400020a4100459200e141c0d0242020500a90701401a0506002c1498081c42000d4008004000706400b0032560a190809008030f5000601100c1c0707010388a44a1030f1401204030b91f2010300d00324400810800d00c0e80203030340e140142141000c4d49a42807010740040d500070300030300003030180c1110304400b000049050889424010b07400703003080003100d440324085902d0700000c039051401c0d038034511001401ea0388140b48041c800c5402c0750407540050040c40b0a4000341110181c0c50041684404000d0203501c00d01c06090500030307411421601c810882d10701202c00940041000f4407403071046c0a400074024504050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 959859730 1250 959858480 959858483
    0x13020f090f0a03030c12030b040c0c020a0911040b0a0c0c09050618060f040b041d060f10060c060509150c030411031b09040f0b01030302370210120c0e12060f0103 71
    0x1000c0ca00b1b501c10030100c000307140961495900c24240b8800442d010740041c90040b5032802980c1010034982c450752003600f664100c150313241091804000420444690034003030300d01c0c2d00383c503e0a401041d40035101c401c04c0389815004031000c01c0d9100140034242c5050403210f00b101818400502e020700d46a0300095014007a04099800380b5100c0a04d4200c035a150303030201449042203402002c0201a24110729078039102265292038800f80e140100d001c1c8a41040c42c02c0859045a5800801120f03683d601005040c01030140e90340c501ca0898010880c80008245600c03515801025079224036050030803034520503102840502079044040b600c891000c01d05005520610305441000f81501c492510b540f0a00c0c10802c06004c1c0b000312000401003660220310140e001000c0c07014501040309810740c000001800d00c1041100c3d0350385840d02001070914403401742c204596410290744903950600e0001c2501c000c00200400500d901c0c501003075a1500380c0142505040480081850f07181090801c109172506000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 959860980 1250 959859730 959859743
    0xe010e04110a0503030c0a03091a03061003270b07030b01052203140d0206071103040e06030c04141009020301050604050d080c0a051501080d0206011413020f090f0a03030c 75
    0x400d107507a62608980c0740010b150180490382d5418810042c1925209203180840000f103c801001070491708921750082c1a001d2101c11038950f0f111a010405018002e201000c24903888120200340350011303001c5006031441d14100303c8004101441d24140f1284014184002d141c60400400141c0c0d80c4042510710700040034821440c00e02c0079610b1044a05100e500c01081c0706080000d00305000c2c0c2c0420743c2d241288060b02211016102c40005480c20140c110303c24442e075209120400492032640052500114044c080d188820024000300b8246d030403c00300003400943d1401444920740c4211160401040c0c130b507008500795410500080d00501c107510545d8801c2d1a2100e82030180004801111250301c0c0b804212503000c82c462600b280c070340c28a03404840c4203011005c000102c48001107032800c048152640501030b41e17030034a64540b00b51080400c6440d040304401802c0c10310603902e4401401304100ba00381650300c4135045e400704241461103000b171303502440d440d07003080000a802007510003000742d0242 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 959862230 1250 959860980 959861003
    0x1e171611030a020402070804050a0f0b07080a1407060504031d15030a180b01030c0501050c0c040504110d080903070801020702010206040f1115091807022d0609030a03060e010e04 78
    0x3a2414920a0b400f9500510000c1c1c11410001560024006c0350026107078840e005554420f55101030904e4402c03400d4041c01044030710b000512030341c0103001204080c28404d2502c46d1a01c2110060781201804940050392074060105154104000981000744015001d07030030700d036840c0450081e003158101c41030199008801324500304c180b5001901401c14007510000120040c2c205001181001c2c4401c0c1c54074035400c1004141d9510620454126a02d2039004021122000003844001d0500030015103100790322400840040c3d0700c8081241e1000e005070034503a1070741c890b002050b007480a03e034410300c4280c0c070401c042d40050b41c000c10059801904a1106603031154281404568201900c1c0304960104041400c42100003114024124a01041d1100e4043c20003480d03008101480540b0341c0790141c0e00030b59003036018041c11900854110b9005601050f00c103c2841000e1500205a0300345a00d41c0001c01c2c440d992071740c98401d000041401100131030095150030fa05a0b04444090030242c100b44070314 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 959863480 1250 959862230 959862263
    0x5091302011202091005131e150c061d01050105180403050a020705040f0e0c0414180a0f03030501032f04050603030c0703230c030d030203070c1e1716 66
    0x20f606881d100740c0701030b1007198042c0b02840700801e554420f100e8a070a0b007081e10b0001c500d41130070881124003424003480c0d44078464248201c02481c1514950481c040005e6a41800c00242850007182a03460103000c0b03101c40441903042a0742560380582026000d0800d03000d160346106980000184c210782c00d41031555031780c200158101e00700440c6d40c01c85030b0000d090004084a4004c15400729001840000644040c03080007002c0100340c0d01481290b0b000714105001241d50341c000c0c00c0c0c3d40406403c8900440b070083c140e0741da8a000c120b5001d0b0003900401d554000410074401d9040d00490100c08014450b219000300251001425002000c181c0c0203070381d00c200042058604000300d8103400240301c121045290b0741d140c40100e1480801040241108550100c4500000003d0903545203000401a00c00c81c1c02d2401d04500035000140210200f02100820002054115005250740e048911242100b0516418046032031107151801d01c2d041d0604203e020b00c00300c000000100141d900200301c0701c812466 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 959864730 1250 959863480 959863517
    0x1518040915320106030c030b24160803040209090a12030b01050c0a20030115330207081209241317070b040b2b05010e0f010509130201 59
    0x303600325003004410b4080e0350b9051900701e452950484040b980d05001e10781102034120191031035480f0031900300000c20054659561004480400040031060945c00c04440580159590740c14090070340b50348500209100940c03d041b0341155000101c4002444460444c3e030b108810408004d414008240e518040e6000aa20650803141d9081035142101d0080c1d0060600341641e8011150382e0483c005100c0c5044414201802151404810322592400351032900002d0142c031103c4c1c466001010408064020300001ca4102131003130001c2d44ea0040542c03c0c1400d190500c0d245000188501a1b8414050812966140c21001c0380c010200c04013420b024100303407014400c03406040040361954400140c08604900c090007501c07200c1c0c00b6141161050342c0e030b9040030314841c840c0713006119030848100311400e2000e0408540740c140000d88004116400c01207003440088801c00c0c3c11400c240391100081c0300f0460400c0102e01d0150400b26140c000030304000010440e40702c0310346002414072041481c5c007041c5010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 959865980 1250 959864730 959864771
    0x1b0f040b07261206041b020321011206020f0c1c080c131202010e03030c010b0108100f210f0606031b15030c0c060c050306010818060714091518040915 66
    0x7402c4c146c07220380c100b40380194580e0824000443c02007140003032002d14000b900c1303015040360503210b00d10084002c2174070f407240a58002c902d80c1100c1481009240c0c075504080141642c40b00360002c40094a00c0b4590004080c1040580200f0311030106001c40480804056401c400711041c0b142810780003042880141d600c07449440c01181e00d03010114594601c0e03c0c1c10342080e00f40301c100340da0300d0116503503894401e000845180250396484240840500c041c42c440b411500b0300e4195007400000144440c0d0751446155510041160451b4450800b00300700502d5076090786c4020782030f61a1150950601b403003480788415543e02c80341059200c8104202031805540310408990300100700b4412680f00803400350503944203880b0740707001030a03080014002c0b860020061010070024000780144d91683c40040701e80e040801c960300c112000812441042ea95400e0f02c03855080d4042e54903548038083c2480340301242e0a01101c171401107040c02c02110020701c81d110708100001002c28001100d00c0908030300300e071044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 959867230 1250 959865980 959866001
    0x20a0f1d0402101116080f0114040b0a0e100e1b10080601120204050d050a0b0c041211060c0d1d0a080c0d06110a2c0105031b0f040b0726120604 63
    0x30050813020030b5148007c200140100c81f840000d02441c90518000c1044140454016000ca60080d020840c258480d821400d250b940201c00c40d609031070400018001c50b82401c02850b0346a00500361425075410b2030f1100312100804840403108001d80d50005000d802004180d03d042059a81c2c400210306504d60540d0b000d404054072049108210b80790080d51088113041c1641c021014000043c0801d4281c0100c4003602c0c021082d20800d4000c6507610104100d9000f01317960320003030500c12000c5a41e8100076161a01200760303504680301001010f02c0ea9003212400300e007402800c40340014028510009a0354800c01070503108451002a1410318a00a1181c3e0980c900c0c1c0a5001611100300c81e4483d4425201d401c03e20300e040a003c00721075502400e6a11a002e541c041407041c80003d44030744c080c0b000151900c40300c0d5100d41c58400803014840c000c0d4440c0d0460480c840e00850716409100c203140c02041c1c2078606d604500c030108201c0c2d0101030035000744204a003203a2000d0001504c0380e00d65401034803000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 959868480 1250 959867230 959867263
    0xd1104080106290408120f1903090b25080a0902060f130b040e010909020f0411040602100209240906070b04060b011d011b020a0f1d04021011 62
    0x80c1d00d40310214000c03c1c0e80383e60803000c0540d150a00790300c4610441110111030b0b0081c0240103525044540407450b0300050340d00807c0030001e000c581010691001d031250503404a0380d0005148256250942602e40c0203803481c280b100e400d003110303540100900500c0100d4416810001d2940e2358400181015040e9250700940118012481e0603904180380007a102c10070540d8603260105e91501c40a4140c1d01a912840c1c002e1000e44004001c00a500d17840412141e00241c80d40d5111400000400c040e280c0320003028034103540008003000314542c1448481800700b1400419882d2401c0f84e0300207120074601014810740c005040f5144c03429101180101c4159031000b505240d25144141400204010100c0301030b1607807800c0440e2060300d9882580207103203280ea40c0c403900d2030707507100e44004507440c440c04135050290a10581088015984803207010000b000801500042541007a440c0d45000210510024039840c50005008c0107a44550810904122614041035901c0200b4401480c0488402c54190300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 959869730 1250 959868480 959868491
    0x40b04030516081b0616050706050c0d05041a1b01060e160203090a0311030f0a12110d02120a1707120605031b060f040305030a0906090e07050d11040801 67
    0x200300303002c110401c1c0c004040c0d100c001402c3d82c0d00040750b11004080074513220306610311a88840c2c1e1900c41c014010030084484104007800a59070360f9403801c20b0580102020a130007094078899041c081000c2c07101481d0515015080a1400d002d02048101d04070b11612220b0f00030800c0c6404441e5611410910020034000303101c01070340c451100d080f80806451600070700700034441a030100e500020031240d256101400600c0e5082ca15107611151644c4500001d034540240c058039450400100081c910b0319000318100b000740c0304045000707401d20480b9a00c41280d40c21008882c800103401041541c000c50404e00002d1f40c0e032a0351001110b034480e4003040c0c4500f641d0160140207140743e01040402008101410402403c3d488104140e0740740f100315910381c3c40380103144c07129259007401805040c0260000c5289801c00b602c07941c405080d130704410003250014507613800800403643c2c44a4001c008107a5000c669a16040c4441d00400c80c1c0316003c1c2d181166070301c400000180070041030841c3c0041c21040001c100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 959870980 1250 959869730 959869733
    0xf0307030b13021801080903090a0305030909090f0a030e040f180501050a0209220b03030417010b01080c0d0e0705130606031b05040612060321020d0e1014040b0403 72
    0x100040810140079242c0c4154050103165284210fa070071540115450f82c00ca035095004441c640c0f001170a69000d0300051205a0300ca40700e0164107000f03944039902440d103841c034000a0101d4801c005013014480c1d441201500301c0280c000c920341c40d4864240c038040c1d04440081011038054038035032103c81c00c09803422060024603103c0d28121491144140c00034011034503a0740d0408117038010070880551084480741102035525000111070702611200e100400c5003000700e80002e0650304558400c83da41003080c40400b8602d002803180712000c40090034004d10905200590342c0a40c0100c81000080c0303959070049001d400c130200891002070000900b031a903003124646540d00603014500c03078500030a04210100581d9680c1592071000c0c1c1c0b49950301d603070501d46007403011100d007103c01c0c040030a026a43c520101c040b8808107444d9198031808a900d51903001116002440c241e20503085070104034a805c1040200d41d90f000001a0f820490b16210248000da6405410f03076100d1548410303502400040e0010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 959872230 1250 959870980 959870987
    0x11d0f280b031e070e0f13051612050405030a05160c06110c0f030604030c210c0b070c0c090509151008060c13030602180618040506180a020a050f0307 66
    0x18440d00382400f03c0c1c200707600e0307855071410002d07002d450344000305802c0042503200d8108002d1401480070300610b0f4200c0c103001c017460b50080303800586a42000c041040840c440007a00100b134919010100700301004a03240c181c881c16282d0291410400030840300041480c83c40342c1c90607242901c95041801400150b6540d000a0240b8111840000c003d0142c0c021002c81e603c2e10210101d20000c01078082d0031543e60326a022500040030750402c860800d0407900d41d203100600600316180900c40c5031076200c1d0540d03060401c10743d9900c00400b00c504102100b06540e000501c0840c002044480008010a240e03d41031131f01c80c101700080007540c20002d015401c000090013980b022000310344030303607042d0f402031f0700e400800d0304070751007000340c241a25008c6000800005009900400704070004200241c400c085101c002403941d070201c46004072044018452201038030701441641d421035402c507507464242c04048918040044010000d1104581c08628845000d01079000c50b8100242402099500e20b841003028 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 959873480 1250 959872230 959872237
    0x18130609060801021c0518150709091b0c02120a0807060621110a1a030a0c020105070f08060f04020408060a0e060402060d09020f0301051005011d0f280b 67
    0xc8600341c0c00c15400145482040c42240c80740d10ba15180c001d0040f1a0f822140064240940241d01c0b2946c80c008014883c0414052042c04281d076890346c002c80d040c03803c5c00811525554000d02d038507910f0b000720006504160000180d448a450a11108001150002031040034100303007070741d01ca03015a01040c0200301182c0f0040807020320894081040503112030b10301e40301c0e226882d00c0c15030100e00500e02002007450440d901c4c5582c68010142c030520b07034440f106080f1144041c0031040003003801006010101a40780940d0b580c0100700d100030401417030007045c01040c00015108a0003030004640c041a41ea80701c1000c410240c0001501c29540c036035843c08200d9649004444c880300c0d45140880f549103140700494650300454004003080e00340320038005d41800074503601c3d40c2203030300c43e02c1c10018407441d0b1000e0050300e204107161a40c03610064505070014190048402c00480e10151000052981c2d07030700c0b948444201d42c3e0a1b00d14030446010000c0120100c82d071a5035020000f10705010000e0340104a0005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 959874730 1250 959873480 959873489
    0xf07021609090c0e130213110a0c060f090503040603020d0f0e0d080f01180b03010b030609010507090e190e07030f082505070e0717040b06030c12070b181306 69
    0x2200302c0f40d61010068071542e0141d5440403004010714150b0003600e4041030f11038201540b140c00180c0384050301400045603206110300d03030100761440510410301925101c1c002000f2089a0140194003903551419140d11541c000e40042c10350220300411242c0342d9911007017403090b03a010100040c8491201595442e00d643c1035003030004c0d1498002070070480e502e402d014101c44c050030004019100105c401005007a07660f11090b059965440d40b400b10380c2d0b041121070702501c007103000069a0708080000400606480d049500358041e0b0b8000d1251070b000401c40030380d078081401000514500e072144610b0405040c0e03030010b0aa4100c040c250414004d55000805004841c1c1c220051100c0500aa1000d0111291000740080c0c200c1c00c0f040000d21b07038a00a15034041d0709803420701d08001c10700b0a20400b100702900c0c140c4401010008001c02400d0030007a42001c110111180211100f9001e420745c1c0c0c03400140030343d8200060118940300031140c0703502c680c5080000100000c80d408003002c140002445644035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 959875980 1250 959874730 959874743
    0x1305150918160207080721300309020924090c0a08070804050c0d060b0a08030304050c03030903030a0e01090b0c0c0102011a030307110f0a060504080105060301060e0f0702160909 78
    0x11002c070341c9000041580032120f103407010b0804240380c402c0c1344a18418180315555801408010320f800070300a1104610100100610342c1c0038030154440000c2c8c200c00b0302060340203251402d440c400141c1c0d00e107941c0c01da21016146000e040c2004403016422140b07070f401c0d460b5801407080018420080000000f03003803125040e95a800482e6280c2c002180c041e01d007602c01a10300d0f001070070300d00e05900704003240f40320300341c090b250201e11501c00d03802280e00c1884a52120780c0303642001c81448104070082c080410703980011001582410a900c0c006500c0b40300d510940814040b01d020380c4a4039034042e4001500a011405100780c03100c09114101c0d03282c00c1c51402c8a0300551a0024120080c1d0480b2010215986c1c0a40114241401541c50340c50250b9091070880c0e00c801171047e195007a17941d40ba051000f0340007650300c45803a01d02d49100e490a450002d031481d031290341445e5043c8951150b403510076903c6801a02194104d407100001607003000f1041c070900317446c05100580406c0c030b0211a000040c0c10f038415507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 959877230 1250 959875980 959876011
    0x603090a0b0c07110d120518130e0c060a142104030306030b1b0a030b12030412260d0513050a12020706020313050f0a080f0a020f03031305150918 64
    0x100b082040b404c817900080281d04001504c00d40300344141d01816841c041c8104101e62500500005803510600c042d11560791900c401e07803207010032014002e001041e00d0a44040341045101c4802030484c0f1040002d0401c03450012644100800d1100300304102503074120003c07072031070030729060040c05040903000543e4802032140110b401d58013003011040b0203200f44003019040c5040510200c1c044c01c02e440030180d1000040380d01280000382400144010020560304036181d204d00c3c645007200c40e00f0a0010902e060901510304104806d110480e82b01c4540c0c0031000480e9134514400d49c071000c0c00004050002e200d110030481c200032034445a4212540301c1e800b25548a80d1303543c2e04907038038810720744040c055031020b1008000e40d040a07060710f91111001080c4c032602d5519a512146003d143e070a0040e255402203403c0700550404600c40c001400c4194003640c64440104c201c5920000c207441110b0040303903000700c2640c0010325941580e20300000105a84618580d56640114600007074500300e80340c2c001032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 959878480 1250 959877230 959877263
    0x6090b070e180601020a0228061b1b1e05030c031f05180a0602030a060f3606030c09050c03070c1704030c0e0a060510020a020603090a0b0c07 62
    0x400000060380070003000c2c2440098015101c103403540c40603001e6815442180045001a9a070b440421409102c0d00648960400311040c9987d0141080d800902448204c02c00d061080034000e10005d141a0440c00315030408004035000d414a015035071102c24000c41038000c0c88442c1324240f42410403a00100d048940c000d440404041c1c5070840300340900c586003000d110001d04001039802c4658024425050b81c0a0b81040b910064182019900e0440c0c03459400010481da007070f0710b442002c01910303c89010501140c242702e4240c6c1001e00601c0c041c2040c0300214044041c0e254481d408112103858013505110140d500d140000da00d00030341c010903d10508000000303000042030340c103913440b0380d00755a40c007408400383d038462091001e80d03030511000c0c0f10010400031020030700040d01800100a860001d140303614180488000b2255150455407080ca01d00100c0c000c15507001455a03000c0307030100c40e425a0b07a111082114036100207400c005000b50f4626041103003050a2402070400540030712140480031900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 959879730 1250 959878480 959878487
    0xf0c09050609010c06110d0504030c12020304050a0e0a15060903021c020f09040602070506010e15031218010302090411071e0803150d1b180506030a0611041206090b07 73
    0xb0b88002c1400684d007407034120086210380c0c000801c803d4103081c1c8070745000b0f41c94603c60166001194240c01083c00000d0441c00c00c4294421021034030707403502c003075420700e82840002201004c19109280e13610003241c01240b4820b00c283d00c10141c2006014040350442c0d55160003a1038400f00c1e1100b42e125104128ac2c24490319141c00c2a00a210350086c516400f10004004010200e10041c10580b0002c2d800e102e208006001000b20038003800e0404c0b5401d4480c58425880c03100107a40107110303806034002c0010005034583e11010b4401e010300c480d014041855076900124028052480030795030003818100d0703c00c1141c0d2702c2d00c020100c550091203c00034050b050500e01b8103d841c007003070003400030608200140068680340500002104020b250300291416502e4540308445a220f44d040d000b00e014400b00607158404c1300c0d21190152040d0240160310380343c0006910b171400c0c0200034040d02c0d280c00e41450400800c3c000c950107002a02c9030803441c400142440c0008000016085407010b810314082100c4a00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 959880980 1250 959879730 959879737
    0x8010906050607170c1f02040311040c1d060f03040b061c03020d03050a0e011b0e010e0306010512031b0102030412050f161106070825050607081005040f0c090506 71
    0x8000142c82c11462011007240140e0340300e000c54000c140030f8244013101b65051171021007044c03a0a542d002d0389503811802c0a0300d250020403030903842241717810015040580c10a04642c02001c96482c41b81d805a1410b000c0b4101c2e1181c0c1d10b41d880b5143c800000c1100b0010805003403800740100f502c1080d004d092514403c003441c010100e019026a0144600d14103007446030f040300761b003d04140d4020a501100103645400e649460042d0300240448018402c4295800141101d8420003464081031402c1c003100440e45504060044a01902d6014004005102c00b002190505070f120520840b000d0b0365651294000e400644080755054198018601d00f10b1064003a282007108034424186800e201c60345080030b01407040f1003110743d420248415030a5a4803480035046603070254022981c1d404261110b585e98171650410b60302ca420b94588260702191002805540c040c0c2a420820700c0390720790882c0c8503031030903031940016445030030105d202c0c04c51744117500001006141034031203c45a035200c2e4100072040c007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 959882230 1250 959880980 959880983
    0x60e0606070b0603030412050c010e04060b25022d01080c030610030609020f07060608010608120a0306090603030e01030515010e040b0f04020a050405090901090b151f08010906050607 80
    0x103828014540400c0003848000e0708040b004003140d2600d43c0d104035905419200034016a080d03001902c902483c0d5801030300c2c0e242207140844003000b0840c1441c88d07000d540d0090b60200030707114a55542d0f4600102c000444180c1c950380013440480d180d100c0c211844410200050041d00015110703200003059409650308034000d000060741d0905658880f010f120452808048200401d0348841001811000c075100410100360007001c2260f0303440c05070505400b5a15258889022a031519500b04440000030500c15065960302000a41d9000e2401e02280070b86001d03008800000d10b403c44c00001c0540040d800301501000380c80c1030061340d0b107164080408050080204e404a0031000001d40740749015440600d01c610020100e06e40f500c00a0003240c00c903041580d00c8408651f00003014042c500d00601c0c80c607030260000c002803121441c55a00d02e040d100000c0c0c51510a1340d0001c0d1042580d541d1542c030000c1541c03000e8076429040b02c445e000180019020302c21100c8483c0752400100e82810b2220403a40460f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 959883480 1250 959882230 959882239
    0x40902040f1b021c0c03020a0c0e1501090812030606070c06030603030f0c05120307020a14060402181302060306060c0f16082e0615120b1c15020d02070302030c01060e06 74
    0x1504070005d071144110345d0000ca00310f000d4070480b00d0003d901c011122000e0803a0721002c007664906158145a80514505600d061059081c0100a809000202460482860030301c80e5101e0322031001040244c003c40e0b0b0000c060345800f072000303d03200e46c0c5a4030250441e030203035172040f0100307101c0b500580f50717551440805800307600104680c540c42d14180e0000c640291442c41191403c1d18207444041c0d04040180c00b000d46900050144000c0d85490f245560412995050040f250f0610100020320a01d6001c002802a0300100001d035055840300f00782c03805ca41d10007060720360041120f40c5580d210800d10888043d00e070188040829201000078041c102051100014003041500d62013005504441007070103001e264588002046140c0d850100100d0322669032160180c0700da00440c0c60003540c8078520700354080e1003034070070b810f209c1030540c80c0c8034aa540d0402c0d21075610800e0343c0c44040180c41010405804a4000a5400109030b8000000c1024041b040020080a0b85039090509882400e944042c2d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 959884730 1250 959883480 959883523
    0x51c06090201050c0d0206090f060f011703040e0405030a0305090102090f04021c1407030e01020906030a0c0c170c15090a080309010915141b18040902040f1b02 70
    0x60440d40484042401410f200e41411030340d0103468070f40b090741040c0f800141c03c81ca080c441302100800600300702280f15000f81119103410604007658040511401240c20107440140c18104030610449000d812001e03802c0e007442c07a142c10013a640c0d5002d003000f200081c0c50200024400007042c404d231f515141d070043c1428080703003040d0200030103500315582444900340c0762003580107003109501c03a060312a074660950b00c0151a2203440501100d4200d00c444401d6401046107036503956520301260b0f4881d42c1c001c0c0004582118800882d500038044c50000c00040700341400c1100401010040c2c003040040c10704071403c1d04040c4041000d110010745d81d18403a94400c6070454000750606001d160f00405c441c000189a01e8280c41e50070b040c1001a450f030110a6030340001c01900801015450b902c8164840c040c0707000d0007400a07141142c4144118002038000e0300f81400e050340d80340d401c020b03500d5030024030500c050500c000310b69004164945000c8180b0281d4010f0a420500219034141c0300c40e00350059205 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 959885980 1250 959884730 959884733
    0xe030307030b040b03031917090d0c051501081e0c1507050a0503270405060109030201031a04113a1127040510180e0c0604080604020901051c 62
    0x941100c00d0b0460703005840340341401c800e441c1007010f0300f0500303403000c2e2410203c0c04d10360001c2d200075890781040c00c0350b40c4030004000850400056001036003200d454446d0b4601d12500f810f6007008214203a803080c4021030000010a41030005035054400441802450300710483c1d0080c640d43c0c4490700415410114203c0b40344508039a5402601145000e07400751240c8401d20b943e03050842d840054030070749120713400c0340c0ea0001c0544040702c041200e5060b58100802d04218002800751910391000904040d01d400c030000e4008441540f490f41c000c0040c10034850000d0075004061a5005625030182a4085c10b0420b1050300c40b100401450303001081e001c10b800f10804c5520030260400311454070700860200419010848081c1c00740201080390030940b0104038400701000103440000c0d001709802102c6010074054105051049005000101d900040e0340402005150600b0003100c5850342c03101006c540003645150100301e851080c0e108032801e00e41aa00c0c0c504000c0c0044000c00c000d6a10300781032110740c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 959887230 1250 959885980 959885987
    0x150d05100c0908070e0f100b1219060303020a021003150b09010c120309050c01020f25080a0f1e03050f03100b0f130e0f070c080717180102010e030307 66
    0x441e03589240c9403040d111910307403003000e10b030a00540c051005a02560100201425541c10b003507005090402007465a40c540b040c2c1e0420790207484403440b64600e00070701254001d0b032504940000010464814041c940e602d09020b915844601420b9001d415105142080756110b840b540c20821800e810030304440d4227014281c1c50710341000b038105060080802000740402e81c00d11840e191400d0075900454842240c2c98402c3c00c0200c6a038000303040d507010b842003032848200810820700712426074503060100c0c0c08028003003010010950040b90980141d179503400c2403110702c440400c0a6030140d11480c450318280c0340d5850444180c110040c0c0020800d22080e02d1403000c4200454018032105000b1400030340f6081c14030003550161f40c810414a1000070502c0c0c00d5a01c10021000a10701c805000103603150602540941003c010003800420200800e480308100d082d400f40d44106401840c0e182c0005403000904189510038286024130036000044400e01d50b105004585d10600550051803c0d40ca80e00d5054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 959888480 1250 959887230 959887241
    0xe07120b0703022101051905011b0602072009010f14010807050d1a0f0406030b0f040c0b07030207061b020d060b13090602030621070623030a05150d0510 67
    0xc00801d0303020007211a50418819509410030000004c04c850380d4501070402130103400c3e0f0710f041c00c005c58440b501001070781c0c1c010440e0345041c0d00c4102c01c1c040c0b207074040c0b41c080001e105140004161224032541c95120804d140035520070304809595410050741c8030580401070039039521843c82c0d000342c03003c08045c05500c14081580c001003203003001d50622241c030340300d00181d0300d2078683c480e0042440b02e0316000c5880c000101d20b4580d00c0030b031000c00095003140c455040320440149100d2000c2c2494000c14100710f2854007000092042003203441c4c9818480c1f40080d1102054450340c0002003140c04221110001e8828103c00755070700034940d0107034106030794401c0c0203850f2207039045074000720f00d44021075001c1845c0603101440d48074030300040e40c034905031041000c004103400d0040422025070310f8910341c506000030f90707109983c45420543d100b000303420a0618800301e00000d82164260200c01d01440145079003080d4000e100c1d088900c03d058501d0818483c00745071000024001c2d621401c10f02c0f0384101c456010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 959889730 1250 959888480 959888491
    0xf011503150e07081f0602030304110123040807170a0311121b01050108060105030d08310c090203060a09110f120109270308250e03010e07120b 63
    0x500c0803582d9160012005001c0840b8a42c002c80e48032401c0180f500e41030f15500000d04922803130b10400d5820709a00942c2e901004000070b00c03811700441c100ca0542c1c040d0130304201014a11140e1415969110403080d920b42081c45881414441c0c0240460755a0402c00e07601540500d00700102a407a078681c17421600600c81007000000c2d8002c404401e610500040010702207040240700900800074102c07070480c01c443c4140d202c2030a81d041400180003c5e134010074008080e40e01ea1034005e0340f5407200110005544250800c04070b000c1c11420500d1504008a5441c92525000e032414080c400d550b0030b42242a407004481c030a81c01804602c0611485141d903024a8604019803d964180007182d409082c003070340200d070500c0355900e51b00010800c1c0440e41c041c840101d034501c0751070040c4010290301c61149030745001004003440302e0003000402d00e440c60510300b000f41d205000c100084040c0c816001d0038405405c00400e0180d42000300c04184142c0c00a400000c9030620420300b07440318242d4544003c0008090b25 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 959890980 1250 959889730 959889761
    0xd1518111c060b0f090916050415050906310302061b1911100c020315150d0b0a1a0603010902030c0705010c02060610030507120c03060509040606030b0f011503 70
    0x890302c10460f00c090701250803403040c00741d42c8000b010204200000000c202000c40851121310003072280d0b01205850843e040404a460480b0b070103e000d552901503100b0072030704100003003001604004100a01c421010100c08a00b03c00700704000e010071441d0007400b01035048041000b1060043c00c0c0304075440c0801c80311000b95440c07082d0070305036194008501c0c101a10290040c05295400340352900745000d43c284107040c5508803100c0b40e40820340b01d02106250750a6281c0d080000b0700c0c001507507580800306040081032020390016524189500000070788009514030310381113000303803144401602207900d2000200880e0650b8030303040f03840b0040c0d0300042001554810034010007001400901800000500c0c580140c45145090814000385202079119001007500f041d040c040001d82009000c5100900c030407010031341c900d66020550180585600a9401140080c02c120a015442e403014081e03e200701000301d5162112070780005140028003641c208500100045001c16029501c1026481603540303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 959892086 1106 959890980 959890991
    0x21020a1101030216020d0c0807081204090b03010b1201020a14070f0627150506040b150d060302061b0d1b1103030d1518111c 55
    0x140c01410b02d0381c00501880c46281000c003444030329401404400000200385021070b20709406104e1051030b4015a98082440c0d00c0100e60a1202103280703d0050806050402d824020117065003080c2c1e0540d0380d80c5d01c041080c0c0303600711504038034484180016114138a8000c042e0500ca0050ba150740d401c00104003040c001110440d9480c007a54110f070340002d03901684081d00200302c003400d4066030584ca80420500410034500210000d103500e00a0a104a4130740c00301340310640d82c6055080c0d501c81403a0090610240103440648015000c1c01c00c0840c0081c3c0d02c0d00400c116070b220305142d50071151900191001031000f0003030254400c80c030340380451000c0ca050191403001008000020082110140e01e100c94dd0307402c005503113040801c198100304c00d007070010209481a041d4490b19003001c01d081000010a03071140301310f1041c0b1014440d02803078203030700c01d4080b0102c44010310502030b107968a5 = true := by decide +kernel

theorem cover : BRFrame.Cov 959712230 959892086 := by
  have h0 := BRFrame.cov_init 959712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 959712230 ≤ n) (h2 : n < 959892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
