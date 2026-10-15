-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5275
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:19:43.928584+00:00
-- url     : https://prove2.me/submissions/8d76f3a2-5d4f-4de0-8f2d-14d4b052642f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 948561151 ≤ n < 948741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 948562401 1250 948561151 948561167
    0x7051b0c030309060d0f05250c03050a3501090f270807080d0c0e120a15150909050c030613060b060c0307060504060513080714070503060703140106 65
    0x100e0741551060040b6402890b10b40090207074411540000981c9200b1481203106951781542c014144135101e491851050300354890384910540141070442c48100d003135400038500e100b5511260104500410751280c01c0c645c0210a1000c020003c0d000a05105e81d0300804e08401000c0c441c962603d45844490301201e440790107801042405d440b03051115032942200d0110700703214281d088800b01c404000c0900080d0564000c0d0118083c0c0c0300b00018101c0107428060300c418500c008040c40395000100469482d0341c005955290641c0c00740b071603401d00c990100d03201c0191156402048000e1613400e008107180900c0e510038000b1354002c1c400c49861414403428103440701015940041010044004100030840c0c51700145860310000e08458681100343c1c043c2e50035a08824421900b0b0794446042c001030004500410390480c900b00c000340c072000349035564005144108030009100801e001800c0c2049501440503800404c1c003c4c09541291400380b07030080082c407840000c020703424407003000455083d2080c01c1c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 948563651 1250 948562401 948562423
    0x6070908061f0803121f0513200c0109021005031b070c0e0109020d0f020306031f0f09030f080c041809020d240b0904050c1003090b07051b 61
    0x26003402d0b110080c64044002c082e0034210303000b01d55501e000801401c00c00041144c00e8000090100500b410555140000020f048040010003965028002940c0f00a01004c420043c141d0000f40040113003c4004204080d20303640308101408207402e250725030190003901581e803003210035004a4040d00705c141c8036400f066400d16481e59860304080d428101840040c00707030f140600d100c1807601c0d940b0300350543d10000c00d030440340e41c4580104809109006a02a0740da10110b0380c0c1055056142c144013007607481c804031380e0031201c034400c4181d4015034414644c000003052a1072001840200842d050143c20101c1407c00900041e50b110700240707242c003041c0700307442c01e85000300706c4100100c182c00c400001031b201100003071780e2024200c00301400040b8182c10406004501c1c1c40141e20917403c00603103004031184c104031280a45941c604001c00158040754a840b101011200e80941e1440d01a040340200812a00103101132800740c14880c4860f040000303400300c2000d490301403426024264030b45895800d1820 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 948564901 1250 948563651 948563653
    0x30b01080607080708040c0b030406060e0a0e0309010522080c090f060f0f01021f051b120133050d0501090e0705041a030a06090b07050a080105041a0d050d0206070908 73
    0x205007514405c0080c540c119006030766084466403140185045907105480c201e4810742e507104100220384180508560050b02000e0801c80f400d46c0403180d54a9104d41840c4038100100024000b0304045c2e1130145c1407402000141c480c904980302c108056454080704003030346c4954810030001e1440d0400d1a003c0c1d01c920b40c054803d461440004c010b0007800c0541c1c109090560060a400d06031080540494000300300300300c2408203490403c1000815103005c011180806d400b4108103100554409520444c112034100501500450403400803e0500c2c10a1401704a03080180c10201d4402d82c0c042c0c003620a520b041803007000342c0c0e40c1e20540c2c5400c607030382c0600102035a0082d0300204850718142e80300c2904205140b00780c001803a109000241030000c00c0000302c07107050340d4001d220140401c8032901a0712581d1070501c00d1400070815009006020144034451003982c0b80c004043c4c03403a02c14030580700310103000342a8004a4489280c0305d40c480281d500044014490b020000c3c040c035126014180131981084 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 948566151 1250 948564901 948564917
    0x203062d0103050c21010e060406031713050a0f0905060a0305060402040c02480306040f0c260f03030112021324181b0305040c0519030b01080607 64
    0x40c0041d4080c0c14010000c05869105114180f08503010301d0075400e40c404804c00700b074030640c10071507107500e1071001401030f43c0150726003201400010580c1031940e040601103408951078440c0c0301c20343c40c0740a070203401075074105001000014080303e00345498001d0340c4403820b051000740d640c24213000f1030800c90b02c401345c8a03a12080c041005810179512480c02c00303410784160f5034040368400d1950240030707014814590784500829071140c48024101e02a079840c0e2400a00894a215100001e03600d50f0040d102420b4001052010700402c80c2c000380030801400020401a030b10755060900c0c0d4600742c10315000e03981501541c5d0110707010301c40200c02ca0b81602c14550500300314100c1d80d000e00c680d0341d0780344030803c101035510b590034070070028900b0004030155801c02010400324100310000000c0000c441c080b40780d50b4103241c010300616001d1005189206030781d203000a1950b6850404042078401036028540004440340c03501c43c020300c808031a000f513034041d05a4000700e903a00d044407591a4800c4848000103030441c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 948567401 1250 948566151 948566239
    0x209070c0c0b0a0f030b0613031202010e0610050f150d0b06070606080c0316080309130f06063902060a1202280503060d0803060a08010906020306 64
    0x50121264494051007684095988916202c085a8400c01160001c565000701d561103156145c02000c1030420192016400e1401d030761143d50a504280c00000c081051a00c28a000d90b8400d41c0601019020902212241d0805004610002040d8080c081c00b0300b005034031000c041d090940c40c042d9000e540d101e01502d840d0380046550010011041a1640000d080084e0004a8568020540600968005003c1e691009010141340052080c0801001162050100030204012041e1061000140c950142c00103814003400001c2c80c404c3d9038551030341c4c6800d6010401640c096040d810b0000d038412564282801404085016031441280c04180c1d03008200140040c2089006000141414100b000503007012070b010f101a0703040829204e44040d0800c61070b8908d2401d00140700d0300380f025424000c0c03440c182040802d804502000c0040d210010010100b211911101c401c04001c100c04c000800c0300000d5481d21402941c402d03113015106071211103100b820307440c2da12403447c0f24800d9200400d03412080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 948568651 1250 948567401 948567407
    0x212040f0321020715110a051024090c050c061e10080307080903011413110a0608070f1116090501080d1707180306090312050c090904020604090e030c0118020907 71
    0x700140485c20042802c0702d5012044003048a603c1032442040504440c80503040004102c03051913807032140c01d2004209110600410000000c16070708920004140003800c0e0b142626640302d2010421591310880c0204201e0f140c035503003400020204070b42c4070341b0b06813900c8005000c02c00041c00707203031055081003065100064050b4014400c01c2000b40000c0340302242e003002a20120310441d404030f8441154104030003001001820814085011100550580c3c00c040d0300818a50f4004c2c41c0314184103c120207204400d0003000b0700c05203080910700321200e586800740c003208410440d100d002007841c100710002c210b4032808110b80d01200e03069034420481d2814400c14580904000d4441414080260902450107a6040450010710b01940010400784002d00d001030618400c140b03090442071500b001e000c0030744a1101142c44040d02203600c00665140c03400007400d1072050794403e100140c580188200c07609000b0001d4210f5141002c020404410725402845034484031440c020362101a0303000048420380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 948569901 1250 948568651 948568679
    0xc0604080c210f0708010e0102030118020c0f1209011e020d1d060301140f10080105040b06210708070804031e05090301090b01090c090b030c0a0212040f03210207 71
    0x10301e0314001500e482c291502034104500b8400740c0b882500200f20500880b0340c00d0007580d803c035030307020f00071460b40d071400704c80c203042c00201c402002a072600001c000e1719a0908018200c2c241180303100703590b00e00410442400300c03076010040944c08100404075044981c80c040980204002a5401614001101110484407880c490304048903a001300c03034040704181c480c4000f031406018000022100010b00404010007a012542900e210380c06810085000e0b981c000c0c4840d0455005590208403082050001980390140e890001c40300700900107071050910040312424000c05035501d0340f1700c490700c0e03a1200301c90045045401601040010710500200f14440706c540711f140c01c01d0b00e80141804c9145c4002030139100100c1064803095446401480310403118401c0e4804507079a418070080452800e0000c3d01e5a0200070010784030031501042450741c5a00038482c12881e0340164414a6581b41c84100164520b80b46010986001c0c0c07400400d4816545591156010b031001500244881e52504007080c1c2421 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 948571151 1250 948569901 948569929
    0x90905070b090d120818030313061a040519110a0816090e0906010e060d021f0c0212010501090f0b0904020405061f08090d0f0815010314010602030307020c0604080c 72
    0xd2030721040c80400c15410040c004030519544a00c29810481c07030f00c005540001000c184280c00c00c0040c0201d00101450100d045d0303910200100cbc601074020180f070705102c92546101e42250900301088511010000341070046080c0300c200300024003a0f102403900038002c40440402181031107003c00c0845d81303034100410444443d0701d480680151200c5e06101500015901f9007015408400117100000500c018140c0c801c0060324519000041c85e0000355281f110f42165880300c6031440500401907114034120908182c014158070491040c140c96a402803009100b03540c1914a131401c11500040540112002554010405059600c0725006c00c80181006800c0b2503011a8400b00c0c090090788919010025002e140c071107147c0e038075007001241d04158811030b01d02d0400c030031071f08900340054019141c6c641025a075169100922075450050300109030002c080201401a200002441640000254811400c55081c7d411400d540402c0c001c45000e503000740702036070300404003000c600e08001c0c01144a903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 948572401 1250 948571151 948571159
    0x15030b011a0d18030905011416051219080105030318120f060c0405150307090315061802031f0e01050d0303020d021201050117160309060b12030a09090905070b09 71
    0x2c2400c0b4110007048600c600319003504052507002d00c030103054000a42c00018403003820554040554011011700a05c1580c044a646204005060003801420004105204a201c8006a5448800c2c030032414428505941400050001c000820203050101c02e50704204820b064481f41160500b0801c1038212030b0303035900442403080401c40308240600304500ca02a00d480600590b0766030800041c49108188620744e40140030741081030014555210034500c08580d00b00407990007000382081c03400050a8554004000d103819100c0c1c00003081510380c0214040c00600e80480c0509014071800c407642d4103e482024064200400108141c1c01c200820b0010f4038401d190040c904100307030071060100d07080114620700b01714601c0014031040d60041c0240320595240603450040385000395410011504111440c010907440f400d240c1c04104441d041018000c10082a0f8405c5000e4012416626040000742e90006803c140000034103010070f102d02c4220a40000142c4405410b0004d050740c1584010502a00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 948573651 1250 948572401 948572407
    0xa0804020d0f020901061107050625020109030f03091d06030c130b041806110f090f0609040f0f0f090302120a0e13020c01110c0d0c06020c15060415030b011a 69
    0x140d84108610340604000c1d00c45106d0f07c92540c001c01d103001065007095001741e104000d4000084034400341c1149a083e00146049256000c2c401203407044103036400140300700010042d03142090f402c49026003e440d404440c224038000340401380505202d05840c1c841c2c05400841416044e41054244d0b004001c03034841000c5040841c6001103002c03621001400da03070703880010386a0010440c3c14007503100c2104106240e00d041001e03505811801c0e202d000403661141c00c10701030101181c1c031401c040e103040040041040201038070000410003c1c0441c40c440c44070703c5180018040c07070721000b8403a6800c01d42e0903074010449036204050005c0c0b0f5a00c13070445e076814001008a44d00f00f542c0c5584030381e140703109500c0c1d002d170f214002a08414251041019040c0e41d0010034801c80703a07210400280d000150750030f13283c4980890f600b81814002485170420780c1456021f080401454880c0c0c81c10400e011f04015070b000c00940842c425041141c50a038040204242d13038404c01040001c0a40654032080700f81e84201c245 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 948574901 1250 948573651 948573653
    0xc05091201090501050702030a0512040c090e0d030b010810030b0a02070f150f2009011403090a1110050406050304060e030703120f1a040c0507140c03060c0a0804020d0f 74
    0x4018003114101200aa4603452803000b000f42c00e0140d41d0300410309000443c10041302c20b0003e0300900410ba048940c100c0c810300004c0510607841c40c0700c1e00501180108000d4019400b515645580e520003440e404682441e4100d1529445400d009108002860440c0003040c03c43d0707242c82101d100a40b01c000119001c0c062440482c009110b41382c00c81e8402c0e940706d0a12084150f2580036104440c640303000881ca0080507818100480d14641e00200c101c4a405a4a40346000140c5040070310303810032551450b012041041c0c1d2140001c0d8a0900ca00660301901152603140400040090314030520000900500c0100880c50081e409160424445d03200440c6241d40b041407030380345030820503064001030a00c07058651040b1356407140050741c0021003014040182c07004a050207980c0e401511901681d5180840c4008a2140f03003544d10782c41c0d01c2143c0301c4c02c4000b0314044581c0c4070807408405119024820110f0484145030040701d14084480e19000d00e6640c0716002c00c814510b03040800c0e980c0c6400001180 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 948576151 1250 948574901 948574909
    0xf0702030a110106170d0f030501031112030d06030c050112022107050f0304060507090503150f070302090603130302060f0424060e0f09161d06120703060905010b090610030c0509 78
    0x100c0e1045e1541c024030b4519000800240101c3c1e224172614141480c080060010407502c1050300615101940d50228500c18000c2251130f521440580c08129440c1c4a004070801c500a00094112442640d443c0000780461030100c08900c94405001841440a801102040f619007034655000c0041d00700315041065400d07480040e40d100701e600700d802e03e9640003004101500412640042c110640081800c00d03940a1002d004450142c050035401d4441070004a101c1e11a40403100d00d050050241512428038440070b0380070196907a021000341c010480015140b07900041d19610482d0000041e440e10580c0b18184501c1c40d1010035220070380c54649c81c021482e44000f00c406802803090984030802032401e01c0049050ada018455005421010b810800800e40703094910184007464450341c04181d04e034000003c9041844e51450f141a01071400c002042c4a00c0303901a40031240a64005c5c400541c0d62800c1184c1400100c869941c80381f1803e21280483d4403d6110390210308250600600c1c0c0f801180020b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 948577401 1250 948576151 948576179
    0x6010e060c160e04030230160b0c090d200405090a15020c030a08090f0109080a0e0f130b0406030606180e010203072003070c0e0f0f0702030a110106 65
    0xa2486a8442c51103007040e28009031500c001005403440b403000f20308103990000d40300c5841c44001480f0700300311000c200d00c0c070642c407130740003040743c042401035694561264084a5500d000e4a00b42c41c511217140c009601e0001c0c0e40c0403500c09001c010b15102c01084030ba610070040708031008904c0f01111119502c190140c40c3c9104a1340507040b110010501c0c1c0c0340301e14040c5c800091002c1c0443c1006e0040c051a1056040003085d1a00e030030780e9080c40c02541e40c0381103000e4609048400038840341d40c20960b411061118040040c000d005007940c548a00e08414000c0c8080341c2c40b0b0311031264100d02d00082d50300c500a00b030380c001010300000520204038950340341c607020700384e1f60203411891281142c042400c2c1c203034120713110300c032a402d108200940c02e602c0c0c4064094030303c418110030804041c002d94146a114913040c402c03126003540c000d040c001c1a40d02c822102c40c0d03c0350111500ca03000d50301e460200c0c1d803c5205210191007540643d0080d481c12003254401c807140170020042501540d216440442d00362904801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 948578651 1250 948577401 948577417
    0x60207021c0b060d110d0807050a0b09070801020f0a03050403170906240d0219031e11010513092c0606091819170a2106050d0b06010e06 60
    0x8407501110581480040302c9030203000340b03200301c1a1340101ca000401090249000c50402c440c01024000141028215403203490707801040e9000d03000c4103030f08001861901a00480381c0c43c00300e981194440380900d00f01e00c51520390204410091100300f90551203604441e0f48644280f500e001500c14204030585400001d84801000c1d82240e0104060036051051035440760b9410745001044400c00c03004191441c82e8080082d00981c5036443c2d9039843d80d400e015040041d58000c1407e5048107001c0700c400c041d0104440101c0f24a1161044401d15611407019503441141c0b030381c8000442da00d02003240009051403451400311510709a444004100040c01000c10225030201a002134a070080c1040a0f15070f0041c605032180705030b011610b4469000044130030005482103200e041c482403c0c14048107004c80055003066511001031000c03c49903001d58003168428881c0340340707e00140039881c242c090340c071036008203a00482c08854401c081080000403580011040c1030802c1503090340d2011402c03940c400b41c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 948579901 1250 948578651 948578689
    0x301081b130f090312020708090d061d0604020a0f0b16050c1003020d0b0a0e07031512050a1703150f0604050904032316261614030306031906020702 65
    0x2400c01415048100700c12a0038150a0440c0f80401654501888d4014000918052415a4034003420801954400b201c1402c0c84102c801101880e1070311603030b8a41d41150128002c003281580003c0f50410b0906160a8404502210782440d50043d03800c1d074075260b4500305031100d2040e40c009440329103030381602401404041e40c000d61341d5010113042005980c04104180c1c05101c0f4484100040d600800406400c110b040ca00410300c00100604d09041112503003203030b4207882c0f8000013901042400104c2054151240342c01c05d01c03106207040060f50900003100c3c070032405c0f015160380049904c6c0c55015000e03410001402982410385500118124150444085021400070091801c1110800c84040c4003c0e00000c501d51608103007407186080240300c0300004240340181c1500f01c5010002c01c0d041c916080440803a2900d40f540d0106000841c00e0714a4140c4003904680f90015071008040216442204e020380241100c5208810f11030303140e42903540036074240d94240880030059881c0d2000c51600b1018034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 948581151 1250 948579901 948579911
    0x190605040e010b0c030406050a0903051608060f01030b060d1403030f0709080d0e04022503080a0b030109080306010f02150c040501090603050f0f0a0e01020705030711060301081b130f 80
    0x1c90001200c9040c0c00286000e0340a00c00811090400012203064520501e440303901c0340d500000658040c034007600001d00318060f82081003082d0100010001c101c440d060101d41c10358407650407401941c0400c0c0006803000b44039200189450a05900d0544144d10070782002c0a545808504c9500b550029a11404208110401e000e2101d5100c1c030108050040d5401500b4110401c1030017a15000802c20700502958011940800e242e4000310401c0f080405002c0d05062000240750003801041c04880317848195280080c01c0345141014451842c4541d84810140e24503101c8000540740e40d0180402d07a8110300c02c0c0d8095031005d586202c0040d000310800c0512945403400c120001d48401c070180c000e60105442c0c50208100000c044010301e8203d00d5440d0900b0300760b20b43c200c004005e481000e078400f80c20360000420104120001000f011414000c0340c0070100c8460b420f040146520007072213120819802001c03800a1001c055071341103c049401050158110602c01c08042600c168012100c1402c6d0f82d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 948582401 1250 948581151 948581159
    0x2031e1c262a0d021902071e1202120a12120b010801090b030f0a08121b2b0603030915090627031713080c010f050903030f0c0a0c0e04150b19060504 65
    0x400881c000740283c83c0030b5016210b003840c600d0010348c1a0380300d101c8003110813404a805544036082102d4a110b130007010340768681000d0803e10f12015081509500007032901c003a62880b01514440c004c68040165075200099190140340c50140102111056150150300c0d242d4030b140d50100b0446400c0f5114205442d10b54001414090954a00a0003c0f23801000540550050031000d0200d4803116000ea0480820301001c0d01602c40300a440c91000c03158501e00340c008800c1c10703049141e100072644401821455100c90b03da003107824244c68411803001c0340c010072030058104540140c040040800f03910b00403401e80d8030b86030010004001a000e08102400103041005078010380b07000409072800c00001e01070b03506100002081c1002d042050340400c000480c03075150950f030034004c590b81800c00445458851003100300b400e84842c031442d4201c4030a00700301c40005503100c9583c1c405100d541c2101c04601d400256141c0b03000030b04480750020341d0064042000740d003840706021030007016100301d0b5201500c803810 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 948583651 1250 948582401 948582403
    0xa08181207031103061003080c0f2505030712020d05030717030712050c040b0f040b0a0207081507090b0a020109050604120e010c02031e1c262a0d021902 67
    0x2610b400c2d54001d030032417005c00c4100c10b0b115403003c0850b54403000560f0f4a0f20b0f4a0b03242c9e814042c07410072140710350148a5001540803241c0d1904806080c2004059403a02d980c0c01c10165541c1041c800c100846007250000d601624011008180150081040e2840e218660755000400c013096147c44d00d4001c0c0c044248100c0f1a404900a24202944a42000b450602d255460702e540110710404410040000b481c030b01c560424070903503004117103030f00030340d80c4595180d1030103504c60045c0c1c0114130b52841400c00300c90800400b400307014050b04241d101c2102d0582040c0c9602400d034400281c0784c05540d00e504800d00000e400300140e030b22a41c041c0e01c0b041c840d260f200d40000d000c2210341c10150b04101818004402590b40440c600000e44045541061048800080c2c0c41c10125078507460140a8040b43d03400d142d554112800c0c800380429011682c079100c0240c60300d140ea08005907030071003150058030b058110113611920030f010aa8064195103041c90f5801c0030000036a802807501611810004060200c1190 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 948584901 1250 948583651 948583673
    0x1141303060606080a05130b07031d0a02092a07060612030e15071a071b0303150510050d1e0f0e0f060603030d0c171e0a0c020a0818120703 61
    0x4400e07401885942081c00c1301030035894441e10050300d411500008107144600903481020012442024030380d8602c050bc0c141074461180c140107901071040d0f080000c80302a07100f001c0d0014a48080c0192803404050700c4040d074160000b0008450440e40e41c0b101149520420045079003480c4a5550644050b52400034007140f050603004902c7c4050b004e2100b81d00103055102c012000b07500780c2107034411558840300211001010181e0069584a041642e0300c181940b40d000010f42002101c4498500d135510010f03c1103440c0007a030910000340e0705001da203580843c9604042d2021a8409651070b0301c541d20050f41c0221030103490a0804aa81d07207181c1011180240200b03844492010090451480c2c0380303010035101d01c0380c203400c03002495550103c2c0c4030480c01094204120115080301e0109032601340070240301d820074190800185040c55000507400d91407802401e014250380c0d805040c90481e607a1b1480c2240d0818035240301c41502c111040101526000031802413810300e00000c0032094a035040c400c40c00c036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 948586151 1250 948584901 948584911
    0x60902030108030f070204060e1801050105010f090b0a1101020a02010213090203040f0807050106090c0801050f090c191b03020106031a010806010501050c1e0c010e04090c050114130306060608 84
    0xa0040c4010842d4020100688864829070400b643d982c1a95100080052546811103442a2a41d40501061250030300ea17921155043c10001c001030b90301c40005444124015262a001070400c100611444280c030018005a07501c0b41041e032501c2040701190b90998000c00c104a0040c0c3d404240640311400203107148008084c0d0100c11403031410030b5250302e8200e40007410b01400d46400055a08100402580034400401d4260000c0202480c0b00d01c000f41100c1c0e003840741a00c980c800001084051030440700b034074010308244146614207021068041c0d1114480316082043c881d90450020030458104e82d42440c41d842540006031007811132805030700c40c420842c2c03441250300321f0000500c0b07000b0b000119141500c4c02400c04544400d95981c0b05450140c40055100d94001800e1244084090019504036001c01c26268009410140024402100d2280c0c4001d0540b402d80c5004000c10b5004802d03c400c00190054041e00d00304a00003183d644031a03a920807900c25a659008100d2175034003007140d136000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 948587401 1250 948586151 948586169
    0x702041b030f05013c0e0402040b030d020d0e21030c01110703050706050a2406081e0a090f02030604081e1215190f0302130213120501270606 62
    0x25410000740005005041c1c078507070b480e07000f4a085c0c0f4030300311444039a0b4045800c0b918032142466031500c4091140c3c2c00107075012401507040003e0401e0600d40442d51655900003940117003101c1800d0903048030f003901901c42054114003140345403031034680354940d00d940c100c1c01d0b80000c0d0b035680e03103540900342100d040001000c804002070106100107035008084070075160b081030002c035185d180e44204c0401400320341804940c09100305811002c07000c0030140c007000c41d162500e90740d5440d55a1004c802001d204007018021170321b2101d00054141205a0000344a58020b0402c10107900c2c0590120f490001c0540f003c3c0c2e043d01000c0780040d00c00c4c5045180c8580c2c5210185490300341a8000e0302804105005041d0121002d80c02e1001f0b0700300d40701c0c01d0380a402840342c5c07008084599500c03958002c4004150106902907403548041014600d05402201e1040440c100b0600c81180707460038215400003204030454465480701e03400600014140c00300301b110403200a070010004403600e42042210503a611164807 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 948588651 1250 948587401 948587411
    0xb0f01020705282c0604060b07020603180a0b22080a08090c040c1101060e0c09090403030f02032508091c050405090f01050a09060f18020702041b030f 66
    0x51078840c00200c42d00401c48005880f00e2041000b80c1541404007034000b00112980d25160a07905242002080424802e60600d01042e03143d00d804d0000b90b900f039001d00c15007040c0c00c000382401410450000d5502415001c51002403800c489147c0381080040e04040d110b00348824103001f0054180d480f0003482d82002d980031040078009584070b003480d0046c1101442172246000000e11405024440c01e0000c403002881006202006c55016004001e42a0407011139031030054049400311520461500039180f8000c0141410f106c00208907900700010011000c040e15851880b45031101800518003428007880d10459003c580101117403500f20070900c4d2402c120a0406128a071400030448040da0084140e82c01803031101400107807034034400e682c4801e8000841c1401c01c891010390440c2039050321411202800c00c40d55415840c01520894040c100d28054541c90030807861a24000c001186402441e02609040e105c0d0000b80444d4003c0040048203209105d14034820341d03161140c000d102009000800c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 948589901 1250 948588651 948588659
    0x120507060807021002072603150402040317090102031204080d05091603030305092a0f030d05040501121b02010606080610080c0a111c030c1d04091e060b0f010207 71
    0x140e6000042030500c4600c0d8000381b20b1060160b040385a41403042d82140500301d0403510760b104002c60380115513a001c0c2c04010707400080c40d07103818000c4800302c941001c1d401c80d1035481c0072540d16040c3d001030f250310306611007004419140005041d25600c04c0b801803400944402e5002c03023002c01e40e20014201200c0e60040c0d2803090164003205800402d9942625001600b0f07036030310503010b10b40003030030300355065012040175031b54a03880c440398803481d20280640342507103000b110b0424140d441103903840b4140401c0c0c2c24003090155506c90003040364040d00700900410521402e54101c00101c646500020050f51503100600081e07400181d4550800c0003a940480c070b544c00c244005084103030203040c02c03071000700c0090b03040102c911881059203210b51420035122151a00c440b0000c0190f1030f10a500046401c0c9264000d00034010701c5026410868215090501d49100d001c2100074103d004048605540c1fa910403460701c4016a088070245104000000c3e141c0518030030000400b0700c44a819045510283c0140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 948591151 1250 948589901 948589903
    0x201200301030317041118090f030301080d08070e060d050708061504061b050102030f0f0106020304060e010806150f070c09020c0a0b1015090302040c090623040e0112050706080702 79
    0x5134075483d61603480c00c1144c0305e81c907000c0309074000e04405691090308070003501803203038880c05018003816866044039030b10380c04203c500f5140d010034412020950000e111401506014001d0304e13070311070650316060701d0140208000615540180f030300d100039030740d6500400001c00c3c0c001808a811070401c88040828040020004850344030310300400042001088140407140300703410b00f40f843c0b2035116000395101e252284403609c4140c1e040700e00302c28840c49000000750a5001000b02c03000c0c1c0360700342e41e0f076a41c41010000640f03ea000240a517a00101e1040234100111200406404403500040060342d445000c0d00704007050000a03042202c0c52403040010711072600002034448501a40514404100d42d14038030040300007103803640810598608446041b8400d13511a9108003903902c210b1b410000514000c508445007111402680c001c42d02c0710030113011000d1220f04c611305003500c8251042c0f5041d00c03403081c1000c243d402ea1104004095401500c0d0030042e0500c01038000e040300745002400e502d800d038002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 948592401 1250 948591151 948591167
    0x60506040b0c120301090207020913030c02040e0f06010b04050a06090e01050d0807120503252109140309030d0206090303010506090409051e190503030604020a1e02012003010303 78
    0x480d2010700003410010000c0240048051031480102c041e44039a920040c00c406507011507001c0b03200341c008900040311018092800842150191340780c4c032407028250700748001451011a000c0700d91041101c0000010000c10060b40685495480f1540750303450501880700c0548190821010b01c070080d9014401c2c0d03a854600c981c1110300403107201e081401c06061080c2d0900c0342c10780103802114014680324400b074000004500480e0403444d00c1e114000a42071542075103200c20780c1c40c0c00160059a01d1643c0c03004400e0041800000300c00001604070856803140344108903020260800d0704040340c00007040c07400b80045901c850403030001e4281c51602c40080c030744911050140713511030716000c00c40c007015031116480490256404000c03242003079034052110516010f01c1591000c00d116058180803070f100020940c401096020000f1821900d0319020000a90000c028200401c01000003001c8003100340405515403171519000060f40f400301601c203110310740c160310440700e980400b040108002503116500d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 948593651 1250 948592401 948592409
    0x8010e010519150f081501141602060417070b090904030c020f30070b0d0c200a200d0f021306120308011406030a0903022a0a080106060e100903021f020d020106050604 73
    0xb0f050ba145080c2c09d00c030301e41c003070503110180d0054008540895488504502d00030750001c50022103d00569030350900d489441084501a00030044401180001f03000c1c01305510300a20040411120300041004128901c0c1c804510b1464110224821414184507407140701c41c64205102400800303082105800d0588124150380705c60503568a511401c2c0d0340700761800b20a44021000d820f00612036181010b40d90b80c941c440940c1c0c28551800c1c03000c14186007103c0010038a5010b0480080d080c22612001c1d1414142030f4280d07000300c050403100409800c83d200e150007412055030b1200906059040c020300701c0d00160015110b10b2a903420342004e665807182540d0b8814078000010030280001d181c00c03410903118000d4841c50101d601c1d0111400c000a16004010400c00c2d2803039a0b410750b42d5908242a03d03502d200788008618401d031b0b220700303605210035015100c45950815054039540ea901103074a88507440140000300e44126007102106a060246c0420007542c1c0c0300a02000c2c0c1000006140380c0305a02c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 948594901 1250 948593651 948593687
    0x909050c100908010207060e0c01021b011d150a140301050f0927010c0e03071a1b151005041b030e010e0f030903060708010e010519150f081501 63
    0x1c0e940c5000e1040000c42e028002040080d902c03805540b500b80301402070060449a28000c0c0c45900a003035100042c0d1194455a407000003110703140c11801550844641c1d808a0100d03a00e40603640e0881c5c482042411400711b503800703a030799602098503005100213070341415001d150b04100010003050340e40d00700015030008101c480ca962502d500804070900e2004505550300130104501c2c864040d0019802000c01034010f03141d9800c04001035040503216031440c06072400c002c0c076003192202d11015040141407000c401c00c013008050441c00085510704807020900703d4500103020f0400c642840c0340c1d0381e904020407040e02c082c050a407124032401800c41c1c03803840580805503940050300c417494094002c540010002c5080d80c07107004024400f075840e030b401030702014020702c0380c04c010422603032040d02d42e80c1c1260404a603c0113036900b042e0401001d540d40054070f9404c00384240012407280035a5449034101003054898038101d41c0c050b04040c141c0b0380c00900128070b00c40c042d11945601d9030860110580302078015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 948596151 1250 948594901 948594919
    0xe04060b0d150c11070803041815080a170f0a2a08030f011e170109020612191806051f0e070207090204210f08030910060909050c 57
    0x3008903001c0140260054110444500540090490b0340d000d40080c0b8503c1c0c1c0e40000c0922030341c440c1c0750748641510900c0303c250702c1000304001c60410440c8012900550a0000c5aa00c4600b5041411880c0030380101003182c101ca8414003c01c41300d040d00c03503092803c650255003030204040f5509000c1c05108241018002c00d0383c4542a5088211408044032030b00e0742d40008482818105417010b42c00440f00c4c1558841c4e46400030596440c80c0780d0b41c80c504407561501312002030611078160010345407810140700c02d640f20f1142d80010394901e006080244103001c080851450a107a0014000c02404044401d0916104200314403141114507600025084a008a41a00e842113660b041003020360070000030301110709012400070b00c2203520700c2c084e051b9a422034003641e46401e5200204e00c62072061401085e0340301400d5148100c0240e003401d0b514052180303103041c0b4440751500c1086d070b0300840d0207142e5034214881111800403607100d10805040340744d10400508d0706030f03580d03a9520310a103c0200e10541c805 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 948597401 1250 948596151 948596171
    0x1020109120305070903410d0c1b0e2205071e0b03010312090806060310090302100f0b10170a0203180f0a0201080c431415010e0406 58
    0x1500407800443e40080c412070200b81c482d031007001900c800c08108603401f980201c0c054000003100038004180c1000009850040c2030b25500b61004084190111900300c4224807403400100075880c036400030320b1300e144240201d15220700c0c041c070381102d01e4803001c0300a44800041404a540040c01f04151840396818161222801040000003403c0d0351001424800000010041040308080f114204c1815114000c40035264840345031516421504150194028490510000c0701d9400005d200d60090050380c80e851450080d1200352000341c01344c42e0004da146d003110f5801d8185400d016484940b036141c41840d049207842d11601154001c1c020303c081580200210345680499402c038040d4400c00c5044403509904441016160300c0880c006071b01088054001a1001c2c100070204c4444621440340030001c0e045d5072480140f1864041900400003000c05060240c440140100c040706500a848010700f070354504214516010001046428644046004121104614404503001688a08041040350794 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 948598651 1250 948597401 948597407
    0x6052d090a0605030102030a150e04050a0803180f0c01090603020f03061908061003020301051b0a12060b0c06150a0302011d0402130e09070e1003030e0a0909031d0102010912030507 79
    0x8942c00c051340c594400001e1100001065100592110100c007260b12403a81d1a0034041c80c6a400b1180548030741c0003180f0781e500160302c1100959101054480543c10b840365105140d1406400341e807820010b40c441c00c040321444d0307000310710780780106000c1c54194602680e81080135558000070b04140e00441d4030941d064806040050030744054007233034048900328503204003543c802e000b80e848264080d520b02001b203030851001c08040107004c0e1000c100e580c60000c1c0b1b03420880303860400c4640d50082039924207000c245064031200601803081c402e4010003007402c1440080380440d18006405100c0d00d048401000180d070899000340d05181c2251142001024010106001e8490540c5000d4855401400840e6045101c03403410700482c00f9a084580c01622001e04088500050b198240b403114514001c000291207081c01d201881405030400100c240c1d1131030854141d55921783d045010030425900072929207203800500040308001d2000f0301c102482503d44043c2c01c02020070050030151074070300061090740 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 948599901 1250 948598651 948598661
    0x181b170414010c08011a04141c050f0a020108180c0909011e0606020609010915020903070308070303060512150c090f0d05072310080612010606020106052d090a 70
    0x10481e0001d0100f00603005004015400134010207080007192100001028100720994007a6400d000500d06407006803404c02141504e050008280a4410440c0000107101409008a10564000201000c10710741c40003424554008210030013135200324858100100d400142c00c0044203050b5601c0d03a1a4440740030b01400b500c4580c940801885d00c28880790a00021544a40c04480c1070f40c1c01d07074a0b00c4c1c076003040b00c0d82681c03030501d0007900c00d0300c00c05c10b031400380b440c1070b401401c00070002003c0b6522195207903500c03580c507003000c5025001700340d46050412442c101b0402444400800340c001d404004903045210a42c0344002d48403021440d80032515800c0d0741c50b2401d44541060008180e004000f03014941180d884010740640b203889842c5200c1c2c1d00c1c103000c08640c4a41c900300010701407010050000b10440d091800242801c5d80114100e0a01806004c288217030400307001d1a50010401e203081100340000142c00c8180b914601440d130840e0240d03c0013852840049160403075280724561a0240d038840682 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 948601151 1250 948599901 948599933
    0x106200d030e1e0a021002010e061623090301060b1204030810050603250e030312070c020a030b09060f06061206030304051003060e07230702041104181b1704 69
    0x910b00001c018006100113101a0303581d1007110b041d0b18a0443c0742c001ca007690101414010154440d4010480340c00d8650140341515a1a143c40c0c02a0b1070010008900801c0e600782c001d00000001603003084504080c058003018010004c81c0300d26046154803a11286080104050100400403001c42e03100d20000c01c0030001000020a1152a4140300c6090a60081c10981d04180210610425a00980200c4205080300c0d00100514207240d40c4605440c00c80f54000c003620100070b8090184c10069840c3d04082018500600000f1200e2500c00403030382c130b4204041c02c0e000b41741403030a04020380c03a906d0704d04a03003081c00d6040030404035031074180201f231450140760002948210342d0100c21200e690306134420b0040340c510f007412860680721302e082a1241e075144a03a0b40000110341c812103000c015214002d003070851000e40009400380f0310081c40a00c42e0010f030044140310030662081c9407014058040c52014185c1081403e80c41c113081e000103401ca40d038142403494120003520005041c00700011020442d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 948602401 1250 948601151 948601183
    0x80423040e060705041e0806130b060603010509012c090f160303020304150513030b0f060a210303230f130b15060c010c080106200d030e 60
    0x1409460524562000540094502507441c02964800358200022000c0c0558030766110300b490705061801855100f43c4444a8204a00700c1800004001508111803032064800d281c0d0b02e91018070900d0040e02014020b0f01c01c0780302d860244018011755a905030301c2c0d03044400010408030070320315420315641c0703041c9031908444195000000b003025004002c548260000c00031301c169100000d00c0c08020b03511000602006e401640148024420b040c1c1040e20100d16251710300b0f00a080940780c00380000343d05e5941d0000c035503403001642401500344500400c1500070034110f40b42c04020b418125844140c00e4540400300c110040ca070080c000b89406584102d1562508008031a0132401303081091501d868155405550300f0483c3d40001d5807075008840424034142e20401c0201c168503200642d00e041400440c150b44d0008041140d144c404001340705a100c01500364032480180e42c940700024101a008030010000000010304d520030114020a040082181e5403e000800385400e4460500e03002c21440c441c610 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 948603651 1250 948602401 948602429
    0x3020714060a05010810060e070e030f0f1c03051b0a05120a0207021518190504050405070806010b0408030702150f0d0b1309030816050d11040918030206040f0804 71
    0xd00b0b48140c2085060f070b182c840448244c46881754185d000c4a49520800140400b400003040b65240300d0003403d000c58000070220389003c0413010480342031903081607142810f82e0011200004020500e0b1412158500d241003c00c13a43c64200001c02e060f0441000403400b01000180c6d005544e4010000c0e41e5070030300108094201c0c1d00c0c045882c2c01c020b50100b003040e403142c0004a416055840454100c40f40c04e25020b140c04000344d08441444050115440c43d60504400d41c000803803a9140d912031507100354014801842038138500301100d400c04c01c042e0003910200c40101b0051100e61400422105030940c1600c41100740035902c02e42c110580200140c0c42000d90f000600c0c40c402e508140c01c0f40c4803c410403280040300d040c00c00030707031021107034030042c0200481d00450000e240041c9201e008030350a01c0505106180c501c1408a6508541c00c0f01c0c011005e074400407906100503251071144440d651503e06081d40c9010064801a5440400900080c000b8440b807a0f00c00401550300301783d9000300040810582 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 948604901 1250 948603651 948603661
    0x31605042705010b0a0c0f0510050a0b0405010602211b0d121a0a03060b1f02280c05150708030408071a0606041208130e07090b031005010302071406 65
    0x484111040400307000c041c1084000b05045036510111003410445071614481140940e0700d4400324803181c101900c5500034030701060304076030017801140d1145046170303000500068110200030880300180c100c10f0442d844403410002010440c030303441e0850041c0a003401d4072a4414a4a140c044407054071400c0340b40290260f03000c40b0394210354148501c8001400900c0b0103900c040f0b0002c41440d003610107030b9002d50705041c00c01c0400d64503486100f0040000c1c01e500c882040510740001790041c4e2401002c01a44014418600441d0a12440841025120207038014020f192500443d040c05800741070320a4048101d042c045081d198211b44c0d40b250700c4134801d6140e16050070701031540e800040f0107a03080750700002d4160446440c0c00c9a20b2150800030859418941030031642d440b00d00c100041180e07104002c114a00e2054500b4102800a14021000c5000380c44c01010003009824203521000100d0802d105000d02410000034050a0b11000e2030016101c56060614600781150403080c03c5032402441c00340030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 948606151 1250 948604901 948604949
    0x1e03180213022505032b060e1009050606040509060a090905060a23160e061b0d0215010605030403200604021f08060f030111030a020d0c1403160504 65
    0x40700e100c0d8100b02548110307542d01031a0049402000418070703001000901b00758000c1140c05152a010b0a00c1290383c00d0b12000340c101150000c2d00601a50703000703281041209080700180c0743c00707000494414031890402201040c418000c601520384200d42c001c00244007621800c16180007040b101105000d08120340c20000c1d00d401055811100490034600a800d00c0c10402c03c40f8601c0c0300c1d0107100d83c40a40d6483c00348006481c0180a00d40c10059404030322000d550305c41c4003612a040d061a4032203500703840d6400c414a0601c2c140d038800d0640d00803144446041c01c0c41c10003941110075a04003d42e603a41c41d450110750503600c20f000c84041101304114000c62190000751507116510a4882440c1d01c000d20100001d88400e4002c40c0000038224400500b89003420414101c803c140540045051008200c11402ca900300300c48090080d030740854103c2202c2c1241c01040500c028905000301200250994200b03184401003112641003205940340e80344511810844005081e03d03402261407500d1003080c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 948607401 1250 948606151 948606157
    0x406241d040623220b2e0f050306011a030c1e04060c0212070f050105090a0302030f25060801050103091a070210060f0b0910031103070507050d1e0318021302 69
    0x113000310035030440b14124030807040200e80d0f80083d00520818219a20030040c540301070903050300c1e03101101d0080d010a46510391110b440c0040d0046000c40e01c111410f04042c140381402c140d000348003000391041e140c1451100941140d410103500f06950341c0e034045001c034003820418454404540d02c440018001031035039000d165401f08a10803100c480f9240d1071403003802d555442c01d025040e10303004112401c002070344c061401071900786005410310315a00e541c1c0c0c0010382041040007a03c3c0c41d6403c5510035201107140010100f030703074071903619079680c4031402c01100402a20701402294141a0f0740d0520b0810710007100ca10321003a651404c00d42840e0300d4644802521542c15101178680b65040082c0400c0c207402080a8a0a8919481260341010207030030810481d40c6030281c240341490b94512842d140c1e4842507005507c61a46519900d0b03407001c9070310b0401e01d00040509050204a0340c07074090941101405d01c0340412414600c0c0206031000b0680140000206c4560020b41c081c180052a016000042d005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 948608651 1250 948607401 948607411
    0x90804030c0311030a1509051507030e0706260414060447100305010501060309030e040516110f0307110f0d03020a020904030905090406241d040623 65
    0x80074081c0c3e219203041c95924126143c0040140d1600b024515080e02c990340301440042c0107104030780400a80b14100c03a1f0509050314480300103511a03c071119881d00800c1041c0c014402450001e03040f812210749040d2403c040c8516004411b911404a4107114801c078103030000c4c04129041c0c401a0609203030210340c08503142d00910350710b01c40032803c0a00081071815070002480089203554a80f000714050200110000c20302070548446407400300114109100d128040d0801d6140020080613504001e0540c41d101480c0310306c2581010208145120780040080c9110f449080852491080c4c00f85e1a04015040302c40b58182d100114131078050240d040d1402049600c141c1d1940d01e141280d6050140b0745003958000b4025a00c21f5003032400506152120f103512a0003480c0006005446800190503944166402e950654440c030403000e4003150001d03592821590f803107081000d44d2910313006c1014540380c054072640040400c07000405100f83c136048002c0c010255814a101e5069107010b00d01041c01c1551 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 948609901 1250 948608651 948608663
    0x80c1501140d080703050c030c0105190603120f030b0301020a031e060f14031e0c011808191403040605130812030606030403030902060f1e09180a090804030c03 70
    0x80400c5400550801c403040989081e103412010f40b110001035102040c105e081060070422900e140070b043c4060105000300c00d001080ca414444980c40040c0f000707008082005113804800c00000ea9043c00641c0c80d0007480c1000f03100011096400c0e0018804007628a8055000083d010700c40c2c1d80c558000c0e40001d500006071000001e04040c031000300d07002c9005100c8a120321031420302800f100d002c0c24034800d1100404039200181d030711614100046040001d1074140d442002c1c201100e40e040000040c910300d82204014050f803a141c2c2203a40d0b0000c610300e0405402c9400805001e00100c0e01c2c944d005d405031801100d50307480d5104070051480c1d014400e00c05010300c1c99171001c00d0b440c01c082000c2c00803c1c0d0441055085848130410030049a10141c411030603d50766110240c010384030003014068054600f4885600c641d100d014126141c2254051000001c600b0031501c0480d655190000e10101264a2a20b016503195480307040242a250300241840704007050000810402059000950b48208 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 948611151 1250 948609901 948609943
    0x11b080d0b030712081204080f130806091c051e0a0c05100203010b09040216050d052116080c0412050714040b0f040515060d02030601090510020604060b010507080c 72
    0xa600a41c0301850b0520090044101b0000c2212481c64407403200d030003034022140c840c42e1002c0024031602c00da00c948650400c0c444042c40400100f04c05000d0745900c4404e4034094240036606102e84a8040064039035401800004509601c810700e8058192060441200f900c6035200040e4102a181400c05c1b2130854240c41421400c00503a03007103000741c0b4129241c40d0318140c1080c07110700401020303410000011000c1c011783d10800380403e404000c00900d40059480b0b8950303442c2900c4454500b081a03a81ca851002c0c0c40009106481c080d114003c910b1030464903200a454403071000700071483c400c0750700484003520b083c540ca00a1120200350320044032425200007031100060414402a10000c0fa071050348140001d8500207141003030b40256a014040c141c4402d400c0e01003800151507500038104240c1c000c0c2d0301108110495800565240c09001c048821880321040350700020760384c603802000101070b0350311203804050b664000c43c1039500103070b4030600f40c6444258121a01d66038241c0910b40a060b11160 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 948612401 1250 948611151 948611159
    0x140a05010c030806100e060d140109020906180d1b06090911031918080304060e0609030a0c1b091a24030c040f0e100e070e011b080d0b0307 61
    0x7400707030030801545034960401c59504d00b01041003040582038440709222080e4050350743d55455100a0206114801c0001444011910100c5005030140c0122002920402c18217159036205015210b40c0303446214942d11490b95140422650001d10700010030300c0e0401c0140c0000001d0001455090f98086d60b5844480f6603038810000c141e48030105660307825078042001c50182100b4501b0b400d4164414070b008641c00c03000b080300a4030300100580c169000039010082c8001c00c4003900070608681010300080800d41402c0781e1550f2a8801c0f640444144902214100100031465030406561004a94403504560f5103c8001018182c5800c15542d034a0b44a20400000d20700062113611561100c80e45640c10381c248881c00761a9071028160100c2e69006000001e0113607600e080780c1c0083e018805003440e85080c05c00084049840075004085040740c40e400b0002416070000301d000c0d00341001d10381a03400e207103158440f009a070f41e1402d010707144000c00a00c1c660382c82500d82160b4030310001501180e001d640e171 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 948613651 1250 948612401 948612407
    0x5030a11040509180109170c070509060109120c08030d020304020906040e0304090908040b07030302130e060d0f03260702070b0c070e07090f0905011a1206060f13140a0501 75
    0x32800b41c1c9902101d41c002140c0c910b4810b8114903440d04200000190745411030704e034003060007144010600101d038001031f0406402d206003c80b500525041d20065658144080082c0c031281440c05000741004040850300701b404400900c6600402a4070142d0b603440180381d0021001c1c0d03100301d030b082c0e010700c40c1c0a0205850b41064070910b0170040421002d503003090b081035a21400b90044e11010303240c6030703020b0001040c40c01c112030042c0f584a100c0e80700142d40c0c1d4400e00020318401700316030010300a6944041000300300d840f000390000d4101d900ca2044840046d00e0715007170720740c0c16151400c900c1c1004064503665001520401d0a07001d15000e40845207003d54982140b03072035108604200405030812002013100f24524440c143e003112040c00c089400b0390303d9021030600740d05542e20410006846400400490214006018104030300780d0f140c40c90f2180100d040408054040c2034203000c2d00300000c1b440058843d04041e107541d600804080303e074456440708080c100c481020421f901c5041003110000352580 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 948614901 1250 948613651 948613657
    0x31205131a0702070f0f0312020d0e040b15070c031e0f15140a02041d071d040b13060e0a020307021c02030d0608060f070e0d0b04020d1205030a11 64
    0x5440042420388544154407986400009818001544142040803c0003451038003100d01805000507061760451550500307209118051080100759000401350340300700307075018010981080c0140e81c045080705042c0040f0710365800140d4103400032840440ca160411000700a13002c2241d000d8900098002d00c0501980c074910703510750008150f036000d8401400041e00c058451001d03111000c0340022401c19000c50450400720031101d40d60829400502072168070034400c200841c000c0c04d1044480d50b85000e4001405407442e1440c0140751000c25840c200050790f450b0401620184090103074070795203031040f582030050103d50080da000010b5001c00a481c84c0028800d4910699441e40141035440105540d00d1052040660040841c0002c2010880d011003c0c0580d00003448400002e18061421441c07100710031034050004c070108102d004c8004000d541c0c511860001c0c50308005c583c00320f52954800a800c0b03006400004100200701c009034032046400002461140300d808005225005426015000b00c0c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 948616151 1250 948614901 948614903
    0x8030c1e031b040522060e04050d022404021e040f06030314090105071b03020613060f08010524041706090d0c08031603090209040606080d0503241c03120513 69
    0x71020021700380745030001d40008142d20302100d070300003001d6883d149903824401f002c0300c0075900b5070700001c11001c1160f810024009550407030108560f06180010798041c0c0040301800280c883c5075122400a001e000c43d011080c0c0302a0002c00802800700d2441021001d072600c2e201c15400b15081440020b000c0c94a9000c42e03180c10416912a46002e25940d1013032050346040da06410100707a540d40110060300c9070001003c00c400d00354501c00e8074501e0310b00c00906040074107041404004680d00100640d4030362030300e404809000f500e00c002401048002d40c0000c0d00595100107003c0d459049040310b804000325505d8056580f07803081e2403072400780e06000d40d0060711004004000890420000342d0046001c2a116045500c03450041007454150b000a0507889050303030180c5005580346802c000702c1030308005424102c070890030314038254904449540c090f410704940d2a0b601900d503460010140e5914903c070721001c104400d80303d60351b0300541001850f103244410343c403ca82e4600b0001c140140c10030300c1c1c546070003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 948617401 1250 948616151 948616159
    0xf0105061c0c09390f0f030e031b15040c060e040f0203250f02190302120c07060807032d15121a07090308030c1e031b0405 54
    0x19200780c031807000400500040a4950784040b90010400b034407640241500c11800100003519060008041d940c3c21520061140d450040303070030100103550b04007043d01441d21160929400003c0b006c0c1042c0e01501941c21081802e000008a15030852240080542981d4443c012602200401c1d00003601d0f00341d084da80585211003180080040741e115128007142d254000e440030135038404a40a06080e41c0040e140511001503070000c10908a80c800082e4494091915109068003030050002c0d440380000b084404504040e21080d006041c000c01006c68031070715001c030309a5182d200340b80b040e4a9090a0060b00c000424070008110300922074001e00d40003190400702490404807101e001070109168401111030035495144412144030114000d00080c000e24200e810b10301080d160200c4162118080141e00e074a03120140518203038410b603000706903584142a5035407a11101c3c8a60340d54000c042e0101c1c40c800100680340c8101000390059401760110306880840c1003d140c0c0d0100d21030050740940b42d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 948618651 1250 948617401 948617419
    0x6080106170c040c050f1821010c050f0909090321010306060501090f0e0a0609020c03180a031a070203070c03110108100608160905040e0c120604030e010e131b020f010506 75
    0x4155000300c0141f01003240749440c0040c0028074004650708082000c65010248240125074000754000e005980d0741a28500d410b5180011030404400d590190200c2c15009044000004445c48000c204540c0c0b2488040081b8203404e82010b050003000000f4042103a9041c00e100380050071303501038104202030713600480e091080d190500400e4150310358010702aa8840d6158440004e1121441c40180400701c0c4003405199540c0301c005c41c1400035244000d103e40521400d041c1003001c28603011640d01c00d2115201c0141442d120340c0d004926500400d00003a0108520110000800000c81c185240c07aa5003a211607009603103050550000305124440d13503001c40c10510000311040f8101d0316880309002070382401c556040c0c540020504580d003d0740c800d520390307010801c510303000e141c074011140381808200024580f924040d0f500400030070071901d025041c0450805504a02d03036036030410300c60000354034508001e41d41c03450b140c0d8a0141d169090201c0580508001c04c00021018000c1900c501c1003d00b244135 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 948619901 1250 948618651 948618667
    0x2b020402042624060f090408041d1905090703210306050102010218040c1403010e0609090f0c060f09040e0d0e0612041202031b06011e03050a140106080106170c040c05 73
    0x3007490f600034050b03a80908a201166400c0d6684201c00340558082d103141915036007050144149030010780000e020500303250b0708100c401140f100d081108655560340200d01c9442c1c802600d8078003085500018000d00c0c070400b00c81d00d00c000710000a8103000c010350303003402455583c0006900f02c1c400d425880b10a01c800e80950501f40c00c02e2341081006414900e003100641c00e1031380448540350000e820604560700c100c0300b44011864485040ca41000e800d00c05403d60344070702007400e5035074200216401d000e80d002040e03180482d034002c004d0711000100900b00b0700040d030250f001961901c1d004040c2d9004148031040341603150500c582a58200104035800c131940e62103d482d0381c1d40148103540c1e0b01c01184010405145852415050246400300e00c0c03001348902e5041c0f07611042c0310004d0b541414150346024000b040400d4002039a0f240654101c20705004810900d92803e01402c1a900541219800c00b500010260101e150006900144400340c8065043c43d02c2004240c90358150103c0000d541800140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 948621151 1250 948619901 948619963
    0x100204140f060415030923060703050a020906040e0604110f04030303020912150405060915190f0501080c0f0f01090e1305070b030609070e2b0204020426 67
    0x40c04000c0102c1d00302961003d04000d09258459400300007600c540c03c410401c80810002d0703c48070040990700c058803000310045944c918000b04040d00709601c03603022640c22080703941103a0050a010f03214aa403076480740018504101c003a030707000740102d2910b99504044460300741907400103400d002015152902c0c6803800c0f00a074101c4015141c3c00b88002c9113080c00180100f01c4c007030100484120052480c505400c010317044c10301c0200510801d812091000c150311040c0b001e4554805540380d1a106844090084a4001c0400000818010303107000004600c1d20400100228051400ca41e12010b99081c0d006201810600c24107075400700760f0400e07007400055a00a40903500c01c11600c070004041c1019114035240001c44d60103a458003400006008050420946050317000c1a0760604040e01e02214011942d004c030501c2c0301e400310314180700b9a111107040b009020101160000d0003551200d0701d940810340809221550b00031140414690f0345080c407000b08041090b0200d01507011f0030b804800001e2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 948622401 1250 948621151 948621169
    0x1050609010c021c121101051003030c031b0506061003020c1c0c0f11011409030a122001230106090608061503070804030912080d0e0313061110020414 66
    0xf01c2e442075120286090004440000c110300c0780c014441d0340529a0800d5001c0d1904075984008695039042000b00a4501d95108401080341c1d454a0f0011031540303203080840300003c080345801540e058080100c0184000007401d0741c054142203600841c3e030400f1440c280c0c200c0c410289100b0603500030300b00403a040c802e070320030602000320103081c1001611403a0781c4036080302d004041d04407003100303d00d0f4101c4480e5034498411000c400d420320f41e40e0318001c00b001c0003e58403480ca400040c9400c40c008000382c0414490b1084005840f04e9111300b0031210f46017141c143c06040c2e651344400c0101200b810300b10303002d01d19440d014120381c083c0e100d4070a40b80c00c00e903040b9603400008180b507401003180c40c1041c1080300b0610042d48a80b0156076800180e081c40c2c03030018419201035020200707840326900c02c84007007040c000403500d4443c08e143d0001119040031054509500034446999162062018001006074210b41c400584030227200640d01d81801c6051a00101e0180f4007541c004007a402000c1031942c144180d407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 948623651 1250 948622401 948622403
    0x6100605040f150903050d020604050d11030d0c140409060311030d051b031306050912030a05180307270c08073501091e050c0a123206010801050609010c 67
    0x244d507405883c5e4a45901e000c40324140748005a200c0c4c400c01080c494207100e1009120521f10b452810440d15490140da00d0044402c0c1c4580c1a41d00c000e241d1314280905111103480001c89a8242c841c2c0d23560340800020059840b05840fa0b0343c0ba0000d2500c94580400d807042c0b4200140c03245801c0600c12000e4050700403000503c8861343c801000300d550000c1d1002c0d810030051880b652802e5079040003405200c3c05812007180340700c40394014425540441c1d000001d4078025050a070312006640c4029000078904115071b8403185140c0c0039842c8130301c65050403603c00b40b4000944c100c28402070300020303801c544004003110030a0000c1c0c03c03078001c02507000a01305007004990310340031480400c03840825642903100c401e070700080c042c2d07503103407440004552083c41000100607070080410072842c0090003090700c4c0c4a19484c0b0303410040e20a880d0303540305210340d125400c07129240c080c044080182d0806c1c6010b103001460325a4505060400158080d8441e96202d81aa94060300542c18a410440103440100305248 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 948624901 1250 948623651 948623657
    0xc0c04152303010228030c0e010315030605090c030d0e100509060706110a020c01030902130b1201060b07140d0905040e01020408010213091103010b090d020105190206100605040f15 79
    0xd401e11160303030900240008a5003425840c004a00c44a03800807040010380380c0c50181030405443d0300d10190451007401591030f0a080100b0660350104a40403c4189174200600f03681c0781005106080e800092032803940384068085800141500109544211140c42610b83c022101d041e07a0241a201d07034003403c50444c006c1e0115040c101c55a40c0e11082c2c604c0c1c040108906080840c078091405d0b410407204200b2882800e08020440c260b4012038a41c5200080700643e594640c41d60f280e240e00e0354070b0480c00384c40d03c3c03100810a580d140c170321340d0784c1c1540030b1b100594028048204000320030101107040207510240d92200d450301f62502d01400050b141303400c0300c400303295820700000919940a000501c1c0c1d0700d084407510440507080c0041a03003240c5640a00a140b0602480180010a0090203c6248480032111503110807201d1004a410703200714041400c001c055045415080364000446a01843c03c0101c00743e03500d40c862a003142c0700e004521422820821151041002240e83c07101c02c9409a2546 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 948626151 1250 948624901 948624959
    0xc011508250501030902010c06090f0507050109081b1801030317060604050d0605040507120c050a140a0b16061d0d0509061b0705030703050a0b0c0327210c0c0415 71
    0x2271110380c11682c541d5001e0f40c100800b442c489040081c28440308001c0c05003401c042c0e003420300305006603640384840074113031200d40d0300c500d090f591559902101e14240d0101444c0c91100d9a1a460028503184000d05801403c07003142020861fa03191400548040c0c80c1c028004020700000d40d11394401a0202500076105409000c00100710f080d120740402100d580580d102110f114a080113004c8107003d90745c00700102c042c4040708203c1c1d40d5224044030003120008000207880704203c884c4036001d243c110074000c1c4028540320482c02a8012010b00d5103151503100240c4818481011050746c40d07104e0642425404102007140702546620f02e240303070805154407004c9802c0b0b642caa0010a01d0020340b03030070603291030740101c407105e04101000e80100d41c401540c03030382d01d82541002c000900f0f10414241c02c00d40404c1c17034901d02e29900741e4208161110551950031194a0b020106079000850f4803501240001c4d00a00e000300340a420a070255418aa801e030800c0b02c241e0f840e00c40851040109100840c034001210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 948627401 1250 948626151 948626153
    0x100b0a050d0e0607092102030c0909100c0804060c02370b0c07021f2f06070e03010b011716050403060e01060905090d0903080f0c011508250501030902010c 68
    0x8100382e5204944da40c03550030480341032060901d0901c0185000c50700a1511042c0c520050b03c1c086101c2600d041c040d13605458985981000c03600f0109601e080150701894001c0d40f0b5403681d1f00c000810300590180c08204070199411008980b195170040e0403800b2a00490881c91605440c0c0d0b82e0010b4240310300d480344141f400c1c0c035076070100c41c0b0b4000d0f92100f081c03000205950095143c041c0d604500c00080300440007680d00a40d0024007801048410946649450480860310080360380340021144108402e5500620f4102c0c4090011030044200601075881c14555084c5035000701d8080d0403405050f65000051744c0ca18219550016007034003d4010801c09010010020303800d405141d9501d2814000403034100c0c00c0480360303001c071900108112000e45c085072855004a4011440c2026a90810010b0f039950080c0d200800c1140710780d0908074215840c05c24050060340c2d0b03110207041600c08880568969820840e043c90840715070310502015070355024030402042d8001e41c0311640581c0f0604201c0c0000c041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 948628651 1250 948627401 948627403
    0x90301090b040602030f1e0708040309030609140601090c0801170f07032a030f02010c110d03180f030305040608092a0f030d09060810030c080304080105100b0a050d0e 73
    0x3518210f0f040c907000f009004281401e00203c503841101c14102d0070301181003807000c580c40c10000e0180070500900c0d102080606200b441c80d54050b68000c1000d002042840c44e004100c280717000119500b5010795000402d90f05c0d2240240c00c0d60f90352130b070f4850036941d09015407082106010814610f16100c3da1003000c03000361007400f00000950088983e00000701440782d25454450000000b03049940703542405000003015030b240305c4074540e02031810b4000900e66140009001004001e9280e006a68030786820802da80041e020b2400d1100d8072540040742c0d42c82402581100140c0801800304006020070b0102078410a41164001d0441d82100d06180080406407a45900000400480320060301d204040b8103115403407002c2c003d0143d00600c07840c0d80440d401040581d00c4e0044104101042e400320b1104000013140300051500404040030316941d480c50076a0300d42c0144206e001d6942048001442c452100c8143c4c02100c2d020214203240c1079925204980650003c0041a502a614031601d0040d81d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 948629901 1250 948628651 948628673
    0x1a070c150f05090a111507060504060e0f01020a0e0409020904121404060507060c0206070504120c0302030303131707051e160f06020106050607020d0b072a0b070c0b01050609030109 79
    0x19003d02910303d00c1c1160424005031006829028000d05144402c6541ea000e008202c48116810600010701070300c413490450b010345181c0301103030f506104200c0c41c040204010f60081010300c0c03107620350511003030500040c08140d5100ba40c0284d400794500c03000801140b076100702410034034124034110000b81e25103141c824081e0069003060000960202e004401c100e224420003da01e041400200380c1e500e03004200500f20701c5075010380703600c028111230f243c0304100f094400b0300c0c05542d00070140e0f510b07442c10182140350501d6a40c0282e414600d40c00840c0c400c03070001400c03126a5034000001c0d03c2581c980000110410405205520346445003040902d100c14a103000f903800380071401d42101d20280750a40c000d0a4480760381001d03104201c2001810010b03a520380c4c2c0084a40e1b40031041144fe540c0d60042a10450302c000030100c84a0209503884559140840600681c0c91040c1500c802d10f85031070400f11400e0310240c070014100c1d2000c10040c400b034035040018280e41c4100900102d101038440c2d0340d810b0104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 948631151 1250 948629901 948629911
    0x50606011407061112010e0f04030e01030603020d1514090307021e032e0c17060f0a03050f01060645230102010c0c060915090803041a070c150f05 64
    0x105e04c410b1081c1030003a00c24014007200d41c844c1c3d260b081201c07803c42603042c0540001e0034007203400015141c590181d0000c1c8010750300101000210341b1603043ca8880d07150752900001041c0c1c42e1610200103001d10440343c6000e101840c00941c02d141e55542404a08a16103504907980440302ca103098040e50f0400462500c09070000c2d41001d0341600c070030500304403200e44844450803810300014105080e8010419450311410075030230052511504007044c2200300c500314041e0000340015010040c00000521b480800c4081d000030054240d0700d4404039910f1048201c02c20f0319883d5169620702100d19085094104070001110a021200e0703540d8444190005900400c020750402d401c0c25090107080301c001d0b0344180d00380020312408030701ca00028506030b03203000001c20300396a441403c4288071114000c0c20f40c050040104002d00105400d0680c1c0540084608a41980d81d400040c0f1840070a00c0c80c0d24001c10381d94484142e0302125986039214490850700e14080c2658540e40d5a4a50718a03003e464028 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 948632401 1250 948631151 948631181
    0x605040908070b06031906020304060f06080703051c090905060a17010b090c132304060f05130615030f0b130507090603020c0d03111309020a1b05060601140706 70
    0x58040d40f510201e20300d0014100b0b40f080c0c004c04001d1510a914401c55110315500c12001070342c0e0f50700c03840c2040040003010000c070280340c5001408103031356600203210019030313000e0000c0740d42141e07424480c02d001100c4041030f04001070150f10304000e40103d82c0c1020750000002401c0180c002d072940b104055808207a04522500e81d1564286685424413481440d0412140702000345440ca8900d9024042401c5200309c101d1580f442d003131b04451560701454240f000c2e42c018000e20106036154002500c50515005043c401c0c20781e0a800380c0814298803503070382100c0301d20140280072030b84440c0c00d60041c28020710a0050646038055505981e40703a4202d03a0003280f950800090a00b4214401841d04009030840700a141c030400c0104e012480006508000711260310f004204a111510f29410078061081000e100d604942c4010410842c503401804c0d0340c0000b0365401c02d10010101102640d11100400a040340d000000400c186502c601055032615080c80e555500d00070300c1d40c4d5458101c0700c007080303441c4403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 948633651 1250 948632401 948632407
    0x1b0501021c050a06060503152110020307080a23060604030b09010203220507270207060e10110301120f050d08061c0209060d0501200418110f09040605040908 69
    0x183d4886116120291405203001411444c2c186c8592000300f01100d40c462044a0b1208820000382401d074070040040d8100050340d040c01d1074914000080d40096844201150780d61000a198148920440440b001c4066148020000c00103200005c2203010300683c1c0c04c0002040040045903140d51058016900c2000060780c0e46010542c0580c250709120405000c04514851071000c2140028010141d079550781c01e050fa0780350200800c4011580c000c800c180f5103400812124248100365106d00e500da2014010780e10005c0d00c10b861075080f2900a20f0070b8421700c801340014403044d096034042c040c00c1d9102d40341e011401c111b140c4403140750132040d44006002800c0c02003042140d043c1041c0600c0d11130484458290304001681c0055441c5c0d0008207028050301c04205103174103012094100e140d0182c0390549480c0000c10200b802030583c0d00501440e0002000f03800c17099491403043c85494014030310344081a01f07008502030303903141b503a000706e600c96406515200040303106e540b00c0c8038a4000900c07030502d50366 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 948634901 1250 948633651 948633661
    0xd0b040201081f0f030c0909080f030601051603030912050a0903080306040b06040312090b12040803040201030f29030d0905061305090a0606031815020c0712030801030b161b0501021c05 81
    0x3842000ba400500c1481d040000c2307280001d8440003910803400c500c0200c42d440c2da5807070300102d0700d03405440c1c5030300082590260000145600b5a102044090051500c1d95142c611110185d80310301c1a003152a00240100008202190340000a150440d00c000e002080c01c5414400081481c6c00981058400e042a03d0300f1030b28647d00100390314001d062140c0054140345c65204000b040150040010381110383c0080000d0442e88640d0100f032074848040c408006908640981200c000da201c4050111100200304a00143c640022104411140d42e40da142140f4144424002c2c176400000e078680c0c03042c850420116403a920f8680b42807080c046404001049442c2000050664902a160501d1006842030311000b09108a10190302030441d050050f035101c1d0b40a400901e0201c9551040030780d1070072903001d0810140d0010046048a003e035181898a8131444040041030301d11064110108141d001c89034099180c038400d507101c081c06a800103041c900301d02d00c40c1d8805800850308407103950741c3d001080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 948636151 1250 948634901 948634913
    0xa050702060f090705060319050406020c0706050c0601090917070506060109150e21100603030806011d010e121905161d06030a1a0f060d0b040201081f0f03 68
    0x203610a100c0c01c2c2c20441da041201e481da449118070b00456000d082c000002a04600c5081c00d03040f55010207500412072032905061400c020f400c510040c4000d40118074000405510840c240c03603444009030301909203a440e091100b0004d180c80e403801c079010168a43d07041c001701c1001d401b07420f07440c0c09507001d84014070744400010000656a0040f46400301035104c011801903101e854881c1d02c040a45200e01c00c400400b520440580303031460072108034444c051140b208400300740c01c071030102c0e846520350000300d4803458015241c0b1b2110700e07511821003007d01c00e01142584140151000510b0240041100004104002d130034410841032452090030481d914500300b040801c00d882c99032101025400d605801d1000582c07040c410003003075503101c070081e5020035220395085c05200340f03050340704581070007401d4400030a61403980700722500050203010303500194103130a00303002000aa0754481d6080102c4d0703440c0d50064030072903006000140d0fa1041c10400c480303482e6103d000c07030001d452019807500701149546882 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 948637401 1250 948636151 948636163
    0x305030f121608070f050c01060f0509060d02030a15020f03090d080105090702030d2309060a0f06050f010507142401090e1905011503110f040908090d02011103030a050702 75
    0x342c0e4841c0701000124a0180d8003418240e08081c992401c4d04030108031182c2161036006d0f10361054125440c056000500406d1181100c0c00c80300d0540d1035171001d40c1d800e01080300c160387d0998040d405411990388070000031400d21035210445525480182003100c1c11500882c9a04110341900440e44000100c00e40c0c150880780b000c2c010a0110b88181042c5055070009459009a048580c415929000401203034105000f07505803039941c1c484c0c004000e00d03000301740d0356072510180c81e802011481d001d1560300c1d004070340c0a280c0550320701804984070606004011102a03000704415100e080025644406902c81400020210030811540440e603005210080401d40b1040e0b1080380000c0c0b8081c1503290422010031a2415840600d00c0c2e802110041d082403805400140e240e448148880f55001c001c00600c40480c1420180c240c034420410f60580c030030301084480c5010080c00905003030058058615155803101c40c06441813600007040725904114a03d50341040d620303208995160300400211582c10001c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 948638651 1250 948637401 948637411
    0xf040b0d1e0c0e1c060207082a0a080313020d050c0f0103061212090e0c041d060114130b0301080606030d180b0304080c030703030e0d0302091f090305030f12 69
    0x10008003100480c0a4075000baa040d20300c2c0201049095582ca000104c0044d840c510b0704450190340d11029458000529480710495403c0080386c030841c143e030306038030300401e0140c00303058002822032403150340b1803110710b80006200120003081a04c03602c0058543e0381c40d5500760b0344564014600700782c90b00e0420580480c0c214400c1d04040c0380a03400c1001100e01d9001000242c0c0040d0002030285100404a610741d005c2e03000850101080014000c02401c03040c024030846840041c0303998000da40700c28078140c102d400d89401740016112520f1811102c0c41d00014012409840c00748032031706903140010303e81c582003603200100c9600003404004580c1000e1241748070400091810600300c02c0541a40301d0700040758003541c10201c00200c00201000ba9942c110b980441003181143c6e100d020324038004001c1d050804060000340501c1c0007140c0164024001c0c1c40c1c0d400c6005151b008040b031103080c081d034240c1c41055944104510244000003040040c001421580320703000e10a6990005000032010302200506 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 948639901 1250 948638651 948638711
    0x20301050a1112070203130f03031803121416030201051e041e0809040645110f04120c06081b0a0e090c1e0a020a02060f040b0d 56
    0x903480905010b10307411145800030b009040b2005458014089285018010340503256041d103000200394a20114141d0046911035038079514464a4040109800452480000c01072480c0e0f45800703a03214000c02d800b0003001217494445080c44607075407102c848000c0c1250180e0140c0d544109214194011102c1845200f54440b505091030425076903c0070f2044100308000d403000e01d20a0a0b40801011500312a14848010400d019583c0c0b5030120165180d030860202081209016001011805030300b2030403a103031264807072510310b41a41450a8050100780175028000001040b08074260f404807405070000d003c00c890401e00440c41032504406000280d0450b070b050008001c00c010000f4900c40c204040c00300908000d130746842030510142da1584c01403c0d8250300c05900020009241055030250104221040c0d0201f024400b4541007000f0307205031060100180c01c03580124000d400c20304000c0a0311004140124030b019500c0c40a440303181c0128100540fa03035220350108110b04241c8402c800c281c401c0003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 948641151 1250 948639901 948639911
    0x100f11010c0915111e0d020c03120901030204090509010506010f020a0503030c18030723040608071511010f0b040e0610090f090525060207080a1104020405060c0a020301050a 76
    0x41d03400341a05100707100746071030358240c040c070484441c0c400c0e10b000c20f0912040088a05c080c900d40500305903005062030721010752003405814418180b000030300300e4620a000d005054040b6140d80e5400040d4040c481d0f041c181034080000080c80381e01d52240c5842684100c0c00021a801c22100062480000206440c210f41c0000c4651000c1440407044903000001d083c4613030354032201c20b200707049000408079110f40c0c0350103012000030f0010155600c200e90601c6540c90389102d00040780410044440310300410820354018101072281a00d80018000312411794103000c0001c0404d40d82c070300c1c2034907075140c1c01c3c810154035480b12028600345030142c0c8540740232450103002580b030070048a515620a62180804494a8024403074440000c0e501035501c40d90048142c50304080030742c0a0a05080c00304041d294500e1102c580014518800f140c1a0241c0d20a80d000c0c1803c1e00c001c0d25071500c65450381d11081e6201e1f40c01c020010311a83d03030303100070401c164408003c2c058a20b0030340100740c21180000c0940d03810754281 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 948642401 1250 948641151 948641171
    0x30c0604051c08280f0f0f060f08120901110a0302160f05010203090114041e14151803010b120d030c0513061d210f010212160c02100f1101 61
    0x1a15844c0001480300d6035040c01e4080d508101000740030071215013020513207002001c217200603180e000700741100c0700101c09021142d5a0141d018011007103126520907500411700d00d003030100c401401000c1e483c00514203811b00c820380490190030010312000450269100741d954640b01045074031110020031f07801c512224103901e400d001071340b07901c140c00740c0d9030400030900c050603401540c8000b920040d041d00d1401154820780d0490480c00044540200181e0741c41405c0c55118528004a2400c440121809042c0c01c10401c01880030300c0020954025034155203070b51460883d1b441c4e00d0a0b401c040007941e4002c00a00580d400d000d41240c0c6900d5131803007008400c100c0700c10320000c207450b40e400311005458a884c0c0303035608941144405003135082150307109030a4001d0200080c801d00492000c00140310640303050040a010f0311f0300301d100700000130a2404184001031081131190450604104050034000c8140c0441e900103400c02e034070070030a040400c2d140c2d140c1403441c55000019000191204000300a40050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 948643651 1250 948642401 948642421
    0xe0a030f170415060f080c01111b010c0503070605070c11090702194106011412030c010c050d061413020a11070905040312051005040c02030c0604051c08 67
    0x40204042c1083c00c02407416210807034558054002002c0e0b4060040070a07031038000c103984440039080308500140c510418103d06c540f0109209082c0204482c82e42274045c5004010f480c407102005042d82e00c1c3c0418080f8002080880c0110341c0710303030345071b68941e90b03002c50074070700042c044028100c1540544d00d0081040300c0683c000800c2080e140440c02e02084081301c0d0b16054841c440c200d0044008000982c50641115421140044140a0b2218004d907161104200c3c680d8803a805d10425000310008010141a8100700c01900609130160040d280f401400d50203042c25903041c00d624a002450000e01844092010f01c00c0728042d0040e00692481d0f12440780025080034542c100c0c11455690008030b00b01c01c0e0b402040d10109010005007901c06969441c0102d41c000c040440701540410700000403c9006d5010b8442c0b039215085c2003402c8040304c2c3c144418000103148156a407020b51108101d1560026410014540300301e102d5002040a10740401d0300b020340c048505410380a00c1040810300061141c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 948644901 1250 948643651 948643697
    0x90c020a06050a0914030a17100b13031e0b0705041a0306011106010b0d05070306121104240f0515030103110307090e010b03070803180d060902040e0a030f 68
    0x181240700410b164807202c0310708000700020900200b8841011003030140311030000c80a030000104d19101c10140020303220080154000c00c9502c000600044101401649180c002070285080e502c004464100e460356030305070400400150350400081c4081800342080400e1b10f405030312030344529042e41824940420300300d00e80140c1c01c0030601d9110100c0007034801d0f40308004500b6240b88040465005594407400010207900844903841c4141c104000110b0701070081c0030b11022200f02c3c5003a402403480c140c60f00310369807080200da564000d4444000201032008019580b2100d44c104584d103041740e10300b50102441801951009000c0e03101040d490403501c02d6042a03038112a08000e4082004440b80c00003820242a81c0201c0626864a126882d240505500030b0004c5d1f01c0c245c040300e4020fa29100090369030b0141e882e41d40034840c48941c00840a040007150380c01032511800d07002c21176484550010302942c2100c040d41545a004800c1c00c414103611a005008400c803608101c000e01801d6031484000d19 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 948646151 1250 948644901 948644903
    0x7061e06170a0305280c050c040501060f271503060f030206030c0a0207150f0e181501050706020d02090a060302040f0b1818010f0e0c03070c1e030c020901090c020a 72
    0x6010460020031022542032158012103441e80d91080e14002102070f00403040381b481030b02c0c1842204084a9079007003a21495068a1903604c07448000300c110345003202d009c0b010081040c40300c56039032140000d8107040b404880152603d881030600000c1482d80040c112442d80c1e00100505602400c01c00c0540c5620003140e40000741010074607a80e039403482c01686004070550104e00000b0090300c0a0b2046035112241ca900b506541d0b85d100d90f0107103481c040022500306540764583d4103042c00042860310580040c41c41d5203c8040c18490f0600700d0a0700c0f1001240c001124841c02d080d0005020007080c504100210098281c6003021403e19082036441a0300e824a4003070203507201c070001b45401454020190b2040800b03001401000c15100403440804600800c1c41803d40d03c01d07900708007064440d603d0100c18460907440080787d00b560740c0c11a0807220401048025510b41030311104560151072003580ca0849540680c48900c2120744074414006000c005034001000b961914140036881940490300301d040f5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 948647401 1250 948646151 948646157
    0x50c1e040f06121b08030a1706090601141e03131a090703030807050702130b03011a1806060423090c0c0d1d0d2f09010b07030507061e06170a03 63
    0x1618070b105180c4440b40c43e00051071910002c0360307d682c0a1f90051140b03008120091030300000f51180814072080a42c2641c00c039000c12000c4100c00a410541c00180440c1041d6103482c1b07452018182080c0341c144e1059a1b26000000d564244000b40512518800d40c0d00d21145aa05103610300030566079140d03c8540401401c0011010100b4452031042c425100800d40007041e0341da00803400b00340c80004182c40c11805000e94200348100d030300042040400718030904050b0401010510403000044031400050005600c214103000108070103d000f11000e01406040d00e60140250702d820030400000c20040003442c1e0031401b00200c0c0074841022a1282c41801c0906003151020130418490003a11a41c41a0b107405c001d0900001090100701e100c1800d45034a1403951501040c074600c5980400004900c0458002c040c0000420110b951400101085402031400300c1c101210395903040b00b1791358001501d20388400e04d0540d03991001402d11030380c401004211070a1681000c610080794032040c5040f806000c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 948648651 1250 948647401 948647423
    0x207120303060509130201090602074a07140a050f0a020c040c0509210604330606112d010b09360613050c1e040f0612 52
    0x30940250001c00151800500342051858420f1000300d07148100b1800381d00040310244000340040c0049982420744110f07190791210b8200d0b040305001a0010142c14004190041c000030300442c00440406180c100c0820407201c0c9828a03641c02011000031795000501c040e0200540300030280c02c9001c590010206942d05615040040c000ba400c010400d1515904282020034030280d040d80100240b2205400b2903a4031a2906124641d904149900142c00800e17408040460040b90b5804001080c4e031b60140c0c0408910544520f000c40d20780c080049000181e521882d040c0241c070340150071000815620002003000c0c500007181002c9071115400302000c1c1c7c1090181208200000f90001c10320504003802501c05400c202c0441c040b45980d0070382c4801c00c02c800d40c41100d501014030324906104607241c0000c12040e100c3c000038070604030740c2041c01c81d000d03c90042011038944039070501c0c040072140140994401c041c3c2c0340501003542d03501c0c0c50300441c06142190522851a0390b541203104d56420003c03043d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 948649901 1250 948648651 948648653
    0xa0b090a09030c0f030908120705211605030a08090303040302070920040314011b0c030503280905060a0605150f04180509010606142706120a0509070303020712 70
    0x6008108160080c00301380c41c0b0b10009061603000000c006c2112805411a00100440a02c03c480d9001d40000288242c005803030741a10740800040b42200c41440c1e50146103000c841c0b10406002c11010321080340c1c25040418040c0d58150801d44085c3d00c10f48200246d481e515056400035143e80350f41c0544025203649154501814900c0304105a08003141d0128a81e955100c0c10b02000081c1e006d10000704945c2051080302c2450800c1046400701400c81e120060703e600c6941e4140c407681c000a100110300316000b00038503100d076102c000c1040c2c0710300c000c7c40000e80b54910341402c905048001f03010142050602c88104a5031b01e50000d0314500901c1c0342c202541310190001c0301500d07842554000b243c030032044030705100e2194841c2d1145005290700c10081000d0b40e61b69809440c3d84022407800700040e001170044583c110305051030a111255440c41c0c000300c26640c1c0000881c25004440c08a032619084010468005800c2c81440c0e00419100000d2250318a0350780c0080d079540c02c5004402c16001e10001c100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 948651151 1250 948649901 948649907
    0x1202092802070303050f0c0c1c120f020d0501050a080307060203060619020601241d040b040609060906050d12180e070e040c0806010e011b0203010f050f0a0b090a0903 73
    0x15040090121041d559050b8905005000c2c080c20b840103646243c43e28007040505000c9000c441108840358040c21a0124900324106da00c11403020400070702619240b0b0480c504043d2003100c1c40c40c0604a40107895807440321802045400c141c0066001c0c6460200502140a000054a9a0981c40315015030360386da65a01003002c90250001401174008100480d840407500810114140d8510000c8022a62880845003084d9100e1020780e5000c5001d82110510a07140c0360b1041d080e941000c1c101160704400356000c02c08840443d84203820040d5216400c3c40241058050b950040c481154448031503c190b442d010640200071260005104041003450a98207851810360020100052001100c0c0340c800005007040145503101d51284d80b0b0301a4140c50140517152940c06494103070b5929500591060064540c81480c0010b5500c01c040f240c03103000185d80074019a0480c0c8182803002c1004d0500101c034080e90840940180140c42c10030021b10b0300781c1c5500e00056441480741c02c000c0784005940c141a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 948652401 1250 948651151 948651211
    0x914010504050d21080c04050904030c02090108010c09050d112206030302031804051018110315040605030706050307050315090405010c1107050a0302040e150a060f120209 75
    0x550440c454240501c248440c4481584d00082c45070168040c0060240045580034412244000150002d100034051400d01c4010144e0045c46428a400c200324260001444000300741c0c0206802d0b9121504840d0344c6920146000080c22b0940d4204034810140c2d03610a83d40110341301c0c0c64052503101c604c08102c11303420344030310341ca24614500800c4200d8507400d00940701c1d030054101c11913410741c41c2605a001d0600c2d1284d54452001070a003618003d040070302c0303000201480d1050740d0b800e03600c411070910380a4560b00114041c0c0106c0750000c03209030014041c0025130b071040c1d0243e4030035084030404020303054000085a03800f09052070305654a580c1c00c0c20900802d60214082c41d0081110800c100403c601548801000c1e225511030310307210300400490a548014500810b43c20a040c11000c000605294001d41140a501806c2d43c400c410040c241100301c2c10300f00c2e41e003009aa100c0d041041300d0520000980302500fa45101409142d0b02900440d40a0358081c04034010460804044807188690000c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 948653651 1250 948652401 948652409
    0x106080c1806041b030203010911070b040f03050d1d06010b030709151701120b060405010b1b100e0a15110f1605030a0905131b0809011104091a0d02010914010504 71
    0x720700c1001301c0c0b5200400941090080090341450300c0340140300000c2c98400c0e12511a80a0403900c05961070ba580c594040c1131402080301071160600800c451001240101107424181d80403100c441c800c2180c161340327005010f901c02d2101d0441042840700d0554400e4021098072062031501c03141e1004c03120111001f460300d1040342040c0342200004280c0b8000510300c40d0205004040c00d10380d64403094200021500213100340c43d4598000c00500070282c11f850541c00c62061424143c0c0c81710003034058170b4815600807010510f119044410201c0c10004482d000c4900c5003000d03641044000d541c403401040d14400d0001d0000c400b0000b140c0007080c409650b4202d914194014140c9880b040042c0e0003918401c914000c07148544544228690f0240040c464100000102c1c6e164807419608044d0581d240308002d0700b40841035480c1c4c50b8030320741c00741c42000a000800400e5400600201078800201110440d10380172442012000d9041025030b170b003d00c0e84416945c09100c80d8003601160001a07800c0c2c415644 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 948654901 1250 948653651 948653681
    0x60d14030a03050f060f030705150c0109030917010501052b14030d060b0306030a06110c060f040c060f02070312020c1905010206070c150b0406081b01020106080c180604 74
    0x50210410740d40b581045003e0014203282400c2030301c5e180c0801104440107180030380c05a0100d5000c0040b03203000d903900460019801145881c0c02d110450641c00c0d02d0000301d05a0109040c0d85d410411400c904058001c5c0c800084020000d65052400040303005840f101911012422813404100020400495130030440d445221342c141c6214007007920703481e030b0028480030942516040001606040da42c00b00c0344141c8000700501401401b81d0b40751802483c0100080c8040441170100d00514202041101d002e88600d1000640c80e1070a85008154201a50810000c20001e400504035090300003c0040c1a00e6006d8200301e00b440750190100d10304a210a285540711008580b040213440d110394003c030030348100b0380c2607072060740d11035605941d90b00c1c0f1100003c1008035004c1040702510295885a046034500a02c0441e6291390340f00900d00d0007111012003103800c604011025100d40e024442c5400600020002c0c02d041d01041002a40703038014800c4842449905000080e031a1340c0d0341d0b10901d40d14124403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 948656151 1250 948654901 948654907
    0x207110603090a05060109060b03060409050c0a091e0c020c010c050c030706080417030108100218090c0309100626071a0d0b0f130e0a080d32060d1403 66
    0x702c2e82603482c181000283e65a0041d500003080b031020600034102507883c0503405616503212102070000801c203800c0192554002c0c03d8058280ba80c440c20810010000745030045003004031042d001e41c2500456a503e060245000c403000d4009801090741042ca51017401c08a4171910242005030800441c51078081d0715018102000c1000c0750010300b054010784c0140ca143c5440b044202e50701e11180b0003070107000507683c02401e0f00f140d0318000da002017080070f0014102603000ba4002010489803407055070000040103010007000241d6204200c03018ae0b0020300d00c028414035250002e50305005102c2c1080c080b40442c2c00414030f40d420803c000444c0200440f004075070408440000071012a0080e00c44070b12218100300c41048a4a000d868000f451400108644000103c5078094030042800e60002c0b94030340942c46201e40130408460213030210740b1008401062184d000e0000401c00c0071030b4008208203081903000a00f81c03844841c4070030703807181d42030318032903d8010b0070b00340089608405020240c240c4000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 948657401 1250 948656151 948656161
    0xc0504020f0a0212120c07050a0c0909051009241506030b1f0503010506250303020a17150405090a080705070945050f01090b0105220207110603 63
    0x460041000c401141d003130b2000030001c014a0715142c8500c0d1504110500c404010542d22165400200030035480f510440380e00000d0369031605240a01d030340c401500c695039040300d2f8041c0841170001521100c203404d802c00008216549a045914070740c21001e190b4410441c036031601d0100385d8001c1007481030801c0442c06031a9109402009404200c030924016080d160403850182e00c0d40803001601032045e16000d05581c00c103028480103800101ea01c8403000c0d0950740007184031498070282880c0324043e0364003681e10014010090000d80448000c1210000341804100000f9120000d40c0114136040714080b81c540c0300c0126803407410b50280d001814100d400070319801000400503682c0110b8090400601c603142c043c1a1612050321820f10280c0152004400b582c0280580e9202d505616104031841000c030301d850b1034840c0b80149081002405a6450010b80f00380899419540c0c0104000c42d00c44013600c0314500400c05500c480307900000700300d07004030303081c1d041250100d08141c5c8601d020300129240c2c600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 948658651 1250 948657401 948657427
    0x100209011106040623150103020703030204030212061f0f030236041a0c160302070b070309081506180405240a0501090b0a1e090c051206030106031104090c050402 71
    0x304038540217859420f01010f59920f1440c24a0601c9442001c1d603036034100c0440b0005602940c00024104d04269082001100583c0c486001d04d10a000350b00040440d8034050141d43e031403c0640d08050640c402c03508007000429501d40030071007900d078152060b0b400d0014450029944008900415101e111100c003c25030744011240c2152256005090350a450214000c90490b22101602c44030f98440007044203003003c0d0780140c0c1c1a81c00c00d110384120341031142e603081480040e8101900071800108101002c000000e400c22260118020341c460420950901a0014018007201c2d14072413580113241c800a0b051110a0103103415001800302890410100515800340c0300344111400072180d461314001141a000c2842a01840e0401a0501040908080c481d469040d10480f0048100c901104085001903031400fa00c03d541c45240c4a040d1a140094000707007400800400b03242c004e81c5000b03410000300390540b18800100b002603800066641d41c908012a071291160000c9801900006203541c944c19 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 948659901 1250 948658651 948658661
    0x603050601240e090a05190c030207110a120b04080c120a080a0501051c020d231b060720120c010906140901050f070b01060c140f1002090111060406 65
    0x10710034241604140c0c40000340d40c0c80b90f0160200750000f10600000310242c00a600c10398015113060114100ca503500070480d800e480c184c1e064600000d401041080401c056600d040c0040541210325600050500c03a4001006584c1d140240103204601c1c085010300c00800101c1e80c94854190076110a03101c001a00300b0140c0c05110f01c0310003d880000000c0408186110307007410303214003c0c40f820050302c40068000382c40071061002da0b40320540d10818400070b81d840b4403a248440307650003020001e10581c070780e1900308400f0580d0b62482480000b009262955048200c5044951283c0c4076206000350744200092a940300400701d40110204130140d58840c0700003090003990b9026a00c101c0c0c0c242e03c4a030201c1e020f02012150044a000c18401c43c0c0e22903000b20003500346a99001c0d80076040c0060340d160f1305040704082e406180410301c0340c0c03c2041070110905007035030300850341001000304c00c80c2c05213801d990300003402e50309441d81e5021441c950940c1c854010403203065590011203010f030505e800c016000306 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 948661151 1250 948659901 948659939
    0x507091706280b0a12020307120f060c03091a0f0121060203060103110711040c0302120609070203040906090e0c01021203012d15020d020705030d050d0603050601 71
    0x46080c031600c0100c0000150191003075040a580301104940002041e000e4402088400a078a44800b0240c51980742c1514820040c903050b2664030a0300000d0052505001558001c00d4042c815102503101040164a10300c00450f44803000003003002403510200c0c01041c00c0b110040101c106200340300300642e80020b03440c1c003910115480b00c1041e680c1e01c80b03c0428075208007003c0d4034907500c14808004100d1075400b0b503a1005041c1408108904070301e000d2400c950290320200c8190035404040104e500b018800c10018020034141180f03010102c2e0100c4407000b0006003002c0c40b442d1000c0c00a00e545100b401510010002460700f44004d589a840b6034018000e038281c010850b00c14494501182e601c001903214020540c950300528590808162000340c00e015564140d1a00c206e005172519450200030590003441d583c00b80d140455a5400028200300f01d00c00d06800f1984851070502c51603502040d0090f080082d400e0091340d810300e0744140c0d80030340210b5001a020740504400021400d00a43c0b6454000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 948662401 1250 948661151 948661169
    0xa0c030c09060c050c1f0806030c030d120b03191203050f15040f0e2404260f0a0915170c07110301020a1817150a09050706090611030c03180a09050709 66
    0x1f03565000300f07150fa03070b03c500c40b011a8180d20100100755218002c02c1c1c40c03880e10341c0360320740812008202e5012a240c41680c2c02c00445a0354003440302c01c00e21142030850786814070302d4035040c032030b608000035400c030820b50151141b142c1e40c3d14100742800319030b6260f001c850b040a041805100c0e510040c09542c1e02d40400c00520865400b0000b80c2d9030500f4032489589120700c0d48908818000801c40030301e00b1240e038000030200001d0f1420481ca800b850012001340035600079980d900180c260804801d007009070b004d40048402d116940701c3e8050040c054443c00c90b0300980044031300b5140c40340c50602c0407400325203440c0d55815510005150705030542c4002c070100300e80d91240e0b881078140d65850360101c048450b2040d006c0d454101d04002442000845140c1d41c0100010001280701021621020b0505046501c1708012400c07004042001d00e0700500b051907500d40340c101030350500b141c040340d0a40f64403440503a840c17400038080b070289441d40c40c0c03000c000140c280c0080c20407a41c9030801001d1f0007050540104405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 948663651 1250 948662401 948662417
    0xd0c18060906030506040803100f081b0306061e030307060f0b030d080c0d0b060714060f10060516020a0b0a0c051c0c170417060a0c030c09060c050c1f 66
    0x78002030b4011241200e5203c0001c285a584030748840d460742e0030281c0030007011a1110f8002460101c183c0d401c02c003604007400580341e00030203d50702c4c40410700500300307550203074000c08104880b0b80d80300c101c3e030300c114035010258244003544100000c1c02c1d44a40c00b0024480b1745042000042003106034003030300c9070341400d0701114141006a0720989240004aa1104007204100400c007901c0b0b20070303084661092000b40c451400e0125a030707500742c440e5404840403585580a40100320700400c441c0328182d044201200c040ca10b09050803002070903403260361003507070188803518070f00c004549400e681140240203941101e5114800c2d168000c0003650100f60945461190002c1d1038900a280c903811407070b40c4842d4580201d01c1451390395101c543ca0f02c00e810340580d40c04c14000064002250703240b580d001e400000140100d0b04c1c05071480700480da2140000c80030140b41c00440c042d4580c010702e4540035500e1f1030030b090807074040e00d1408910780018000010781149101c0c100c0c207040102c1c00f03c00e082d00d115035210044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 948664901 1250 948663651 948663659
    0x903030b0a080c150913020d0f020d022703030703030e07050612070e06090f04050a14090d02101b050c0102070f0f0311010912050f090307062003030c04030201030b0d0c1806 76
    0x21580c06175840440c0d012003136040200120400361300034641d44e00e60000c00b00e010461230714018100e13048030242c040c0613600001ca507455880b91000445101c42128421480e003480140400c0d641d01031781e00f0050078503980d62840110101c0c02c110500c000c1070f006101035540e2079504401c00c01c15206460580220b001125131102528058003511000c0d4005440c600c44c5020480c10003001c0d03c0301520b503d03c002e43e50641c1603d4890311b6500c0ca441031102d4001041d400d030039008001d01e80540c82d0141ca4070f151a0245515a10a00a0008051302c0a0703241068881c00980716141c028403a1a40050582e000130800c4420085400070000c212070007505d60401c004224400103081c0e40c0040b000404044030000e125182c107000700050045030041591041c03c141405000c6858108660003440100d0800000000c190021aa84c030346500760400c0a5800d41c200543c3c6c0c09454010703400020305050f04e50b0000c0c4100d4540d02011103900350011034200040d651162044005ca00211484820900740300b4086 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 948666151 1250 948664901 948664939
    0x130903120c050d3801021905150402061210090507052d07080d06090506010c0b060f1503070903030f020a02060301120c080d02030c07091107060903030b0a080c 70
    0x303075440d440341d40c030b062582c1001c100103203001c42154410640300f094030002c40248640c818200c1e4100f03184401e04031950f6001904c1c20301c0130607a40464464801c03481e000603102043e81c4206240b1840f01c0001c60716148006601c074011107408100106082c030801203407003040c2d1000401c0303034031a00301002140c658030404c641070b1003009028803800388090040506d00140301900b40aa2000b4404c441c01c143c82c90340c940b4660b47c08001d00101482d114001880351000314070529802c29000d003018030011226607560005103c0040505118160100081c00d42e80c80e80b0003180aa1101c4480c0b40f943d07032403c920702900081741c501003940051140074000e08803500020f40200c0407a0010036007401e580ca40300d00705412242072942116292402e24001a1200003002194469082038018580ba5001414032070303e403101e990300034001b50b82801c4e45103c0300800032045906d15900264007084502490906a01408a5240090f002a400c1000042902010030311241118084030681c600c4c4003406044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 948667401 1250 948666151 948666161
    0x7030f0609170705030703121d060103020f180403030e01090f0302060f0a0e1b06040803210c030c040506030702070e10080f01110f0d0612080c0609060906060409020d0213090312 78
    0x1013030769101b048210302181c003c100301e00714000c42c01c0c00418000c40c0303807201c1c0e401c040d034041000c403059220354010f104500e00b8203144008640c00356407040e401d4076503001140800720050000360525a072002482c420079003e4100d0141c080e000304204408154070303e0001d50fa150102c3d1000f81603c0c0000105103150228014942211642c20060600d5032a01c0c0111000d085503074503255114100308000140c0031024009005408200781c200c09101c000d501c0041c008410003094480d8480080081003170040d409010380781030340c000360b503404e44030344d14007405900d4201603800042d05400180e080090030202d000418050741c40300c0d020f6507481545001000d0a81d40303802d1001491600c103000c1401d41c0f111060191104013003900703021507040c0d0b035034a0100030103c070310906560000f40005d488080110030881c464000d00500c000300030390b141609000b5101c160142c2200e2145444608031029544d850312400340302e94000304004181d580c40d265804c02081107100032008562a000201148a42c51182c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 948668651 1250 948667401 948667403
    0x50d0f050a0e01020a0c0e010f08010c02120d020c1b010e01020604020a14060d060806070f1e1202070203011b02190f06271a1003030e04020c07030f06091707 69
    0x150609100c6045410380781c0460682c029070440c821300301000041000040208000c2241e880d44070300c1541066081070b16020240c00200c003580c14040324000160380012401c50042c0030414040d21403203d010314001920425504000511400e8002c04024090dc8900c420035031003600d481403032149140069854080c210350203540200054002c02a608406106000b13224000f000c052400303d99101400407500b580d00f05424560101040100554205c020680e02d0110f5043c000304140c078030740384a51311403603c040b0b80003003000c401004101041d43750160f4800c940d006000303001c020200700011500e0070b0244800001480b0b0b0340c1c10980100f5620200f002d142c2d4114600f1109203c15445140241044400200c4001c1d0034101200c12a05441035401d0014414500003840d22808100e4004105d8083c3c4076031392070a034903201000044e801201c00c0390485801e64003d602c0c0c003c1400a241498400d5002400300d40250201c0b8041003081e034400d038041845400041e400304a50440303010399000e1414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 948669901 1250 948668651 948668657
    0x51012050a1103060f060c0703050a1707050309040f0204090c02060f130b040609050a0c0e04021f02030d0b281a0405010e010315170109150b24090901030807050d0f 72
    0x491340300d08000950b9106500007910451829030b507104414603040d401e07402a2401e4100f4101740c010481c1081ca2004208188020f1500306051900d83d182c0740d00c0b4040d0240c2c4034607581c8402c0590a04d04d501520001c00c0703800740400903032907600c03c003944411044400b229921070600c0040c211043c42703000c9103c80c641140e902c4105582e01e070354500042c01a2442911544543c50702c01000455070340c5548c014245078a9a60020304051061140000d06031407440601c0382101119902c0307542c00001d503041d00c0000313000403520403004400300702d075401000d0301f0625a8074969200352a02130104490b108442d20007154680400c4c01e01d920900501590007050b00184040d1034400843d8881c3c1c200841d01c801340c4004101c1140d035000c104041c00e024044103031041e51a150440144403060a8450010b80c204400b840403c400000103444c07075040c0003800044404003942d0803c44070040094540c8541e015100a0b800c3d6101d00709000c0c3ca40201404440c98070038454164503403481000f50702a0300e5460b071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 948671151 1250 948669901 948669907
    0x20c0d030507020108040807060903031a040c08070c060f1104051504030201050405060c0f2e0e03040308031e01030638130906020d020406090b03010b03040b10051012050a11 76
    0x82d00448174820042c20a90301c0780d105002510218007188519041a8480c0d00c000841d94021112401112621483c1900c0b480c070741078460550582000078254000b0881c42c00d900c074030301e2601c0c003900107000070384901070440d282c8200c2041d1030318020001d200f6140210ba4a41309076402480181c40c0d4461400000d00003181840104105d040003006003075410758641c01d5a4003185101c92180c6000000015035014010801c1c030075684801d44030b50761007455032201d001d000000e41000d00310f5a9201314400104074420000003c0c1c13490b031050f50441d44800c110a412812541d5908045018004070368281e840d5040f145036542611140300c3c01c4440c00280e014094454004030f008004401031241000c6c1061034079010741c01d00013a0103100078000408929001070300d950808400400d51403c44d00201d80030102040148203802d500d505880d803003030b0b10100c00c1815130365aa00850b40d1540341e501050300656100c0c0521000d41e001001e0264904408508000070f03918015000d0582c0c08075500520402d03810 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 948672401 1250 948671151 948671153
    0x5031f02070305091201240b12070c02090403020f1203160e15040308070506070201090f0b07180626060f12190c0905010515310603060501020c0d030507 67
    0x280d0090145180070b802c00034203002e0908082080d00202803190301981e590340404504400304880d0340c42d403c58101c2400b030342c800c0c20000561402d10a42640c410b10000c4d0034000b03510103106400912406038050200b4034a42042d00c0d0182d40c580c8641c409000c140100c14450517248141300c00e50303100e108000906c00f0384614500046d51041c1c3d07002d0040744c02000e04081c0820903d0600000c20003107120f400800d954043d1400c1c050f08000c0b01400c00811a4181810500440c20001e0100040d0781c104950800315102c5c03040a44449070540b281e910b803503c0045c400141903030000302d880c42c181222002100d03131501d2114148160501125816480034032a081c4e00c01c81d0400c05851007500da507800c02c41da0084540c440a00d080c0c0c008520449500780d40500911022a05005103030040c03009035500c1c02802c18005001129000303200300035490030381c1c2c1c607a03446401c51b0395000240201801400744040503100d850041c043d004502500f8054840c0a6124a803400c0c031041c10070740c903a051758a003803c14040b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 948673651 1250 948672401 948672463
    0x12010e040201120c0f030b04060f0e0c190527010212070809060304081e070f02043305180c03070302161505040b010b09030d03110c060f0f010503 64
    0x201400036410486030f5040126180150322079214120400d44407400d207150110380060940341000d09081c000c500b0641c080004400c0d98100c08152801030200b1031681da2200c0c00e00070346020703d694241c8030050245000e10302581080003060032076040d8600c03a04100c00302100000c1d00102d40d0100d030040c3e001c0c680030013544c03000401418500d4855100c4070f1400600c000000c449410544059604000009600f0040144140e030350a40d9040781c0c624908048890700c03034003012152400040d01482c0c540c14003a00d0414812040e0106007513811080c180410503080c0301e00c56880313900640303000701214031020f00104000c6814602c07884201c1043c51030b503035440f80100c3c040d401240e542c1001020100040c400074040c44210700702e00350130b070b200042c56142070305040031038a4041e40708050b88001000070080c00e44010924440710181800c004c91340c0c3c1101900c070145803080030b01d941810300402c01440b4500f04403000c03e40c09200030054000700c0e640c0340c004060311400480403034076030503014880b0400d543c88 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 948674901 1250 948673651 948673679
    0x6181f051f0303030c170420030a0c0e0609101505280801032616050705103c030506370905060a03260705150c2104020d0c0b0c121201 59
    0x90141d84ac0760f01191b4a24501030301503006014240c181c6420024107040c00c03008691b01c89110b00c0c01746031041c83e0900320740e0b04044070803508081200c0000e2094110b00c040c140e43d80c062581d00c02d5091340d0984090001c000c1c41082c0030448a00740720072680014058075100c00941c04845100d00d51401d07090a6170390f0104500b10f8411101030050142c0061180d482202c44841107581d62149503941d8070190900307203507083e0610030b0b03081845407082840442a108070004922200e6045c0000c66845000010f401d000075041d0740d44010039507a00350072900c868116401101d0f0b480004d030260054559201200f62401120704903005803c1e0201000443c9031a0040700d20920100e04040d900c01380340750740514035400498151410752100a2601e00341c0e8140e6403940d4098040301c000b600345071610010001c00306034001861700450030000850b09659828801111a0f988412040a810781e0380d10710854070780141d44030948a0251b111106140500d40382144c01840d0030294202c4207a00301803800c06080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 948676151 1250 948674901 948674963
    0x1b0f2f16080309061c110712090933080601080a020306010801180b1503031908060d050601091505031c0215040c0312020f0d0206181f051f0303030c1704 67
    0x5a161b4400c15800c0c4180d000403c881c90281040d55200541c0074030203810101264001e090182c81c0c6003141c0c3c0a194048140c446110807203c4661a40b8120007048001c0b12554200d481c0a0103039100008040f840000c0d0010414426400d4032150f80c0d03a40d02d624201d400d4103000f00c50602c2585a0200080c0342c07202000d138081300b0a9034151091085c1e90210f81f550304112800c200220528504130000358201107407e030302000c1220440514540c41e5200b42d2102c1041c0b113900c0c0c15680312400e1f520340e004007500c40c0c0003404005e0112580038058485900b0490ac0758003072040940600307034141c3c450b841902c0b6900d100e05c1e045034403051200c5c40c41c0d071400720b0328544104000c00c42c045c034280b51008580521465040c1160f580c01019107081001a40b103840c1c1480400075a164031100c10764090702038071805c0d240058003900001070b070395503025050010310080c00007103915400074960100c100358055000702190b40081e41d602a5003200241c94064140c0c0a45d0301409503131244590381e03401a100710703140e0101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 948677401 1250 948676151 948676207
    0x30712020a09050703021b031e1608030a0504060608161505211605072d02060c060a0f3c090f02041b0f2f1608030906 52
    0x950b5103841207030440e181652508000307900026010001500e00750901404400640034500d415869103101d1b600b05000d10f103207810303201b02150070442ca0740c10744aa201d03082e402860319507030384c584400740302d006040c03c0b207007155103500e4440045080000010103010038001801050b140174203190107034040d0009400c8120400c00200002c8082600000c1c00ca82000070044070540541418080c0303044030404510950100203003484800c000c510030801742d0040355000c00d4641818030081480369521911064040c1d0003a000091145145000082513841030610250402622245042c41e80a540300380311b900d00114001e0000a04025843d20078001d61140388412160381315600c1203000030384607040c2c3d00b030b12640da0603001c80003507040c107000f80c070080407000c00b19810150880b03001804d40010201c2003410405401d80064420013050344040004d80143d41c48021400b106a41980e10201030807151910005040c001504040c00070139150710b2403005049508150b03007403000c2100703104800300c4441c0e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 948678651 1250 948677401 948677419
    0x40e06181f0f0219020d020f12040b0f04050d0b01030c060206010e010905070e0a08012c030f0d0b04050a0e0c12030301140a170604141506120a061d070902040503071202 74
    0x200f4003104c0f81c0b813200c0d0b0801d402500d800d24950101034240095184070600c5504043c04100b00c005d2446d00b29402d032010640d0240d12a072802584d800c13140180d82146402800c103200e40c0d410b0096105030581240d00c00e203c44a82140c4544003244c4509080c459408510316040040c410301d64150003c0798091914940000240741e44000984050390b69845102d15964070308500d0381800c8050083c5c80000300c00c40700040510341209040745e591068031601c07400b140020074451402c0c00c85030400c040f410402030040c0141d04000800c0b9004001802910920380724009905a2604040d0800071400941202a6046a20380f9010301d544070b148402e400d41c071031203081011485e07240003085000426200001040140b42c10701c0c0c060301012079800b14400d00c1d840804101400d54a41c0c4441d90300440c03c1d81c1142844075003101071840d01516980c0141210705113000b403640140103009071107072204084101d5005541d0303505860200d104a0041a806d03801000c011301c109202c60401c69201480078040c884 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 948679901 1250 948678651 948678667
    0x303020613060b0928050402030d0e180903031e040b041b0b031e0903160f0f0506070f0e0f030a0f0f200a05060a170a0b040e06181f0f02 60
    0x10032000100c0750443c005101410600e441c06282400302041401c0c410301b00078a080580000383d807290528032000c10000002c080074030648915071400b078080c90701c001c0d0700403a08144811540302d40080f5204185240100450442c80300d41010890003207401072a500344030b03100c40c0c84011411407200c1201c050131604500025000c560903000358401c042e43c8008241c0c90543c034070080c8403641c1c05050074280761b209001081481c00c0d0080c4902401d68010400c07403c1108030f24041c0500704100c0006012400380c0420056016000301000d61160707016655101815840c1c4108110385020550098060b4891601d480000d805440d50640407400b48d2030741c2c0800e242e0303940d81c032100700e114858440d01c20340764036110724150500740410b0010741001c450460500002c840024001c1c589210100780000c0f0800c04034000300d446601c90030400c0005001032245450088856a5980d025184d45640708522140e04500c0900810310300403494841d01035000c60010039244502524640b1418804035070300b081004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 948681151 1250 948679901 948679909
    0x60c0a0510050f04050d0e0a090e0c1311070803040f2a080a0308060918010e0102180406080606130e1c030515090601051318020304020a0f0303020613060b 68
    0xa4a0148140014880001e01c900100c00362400030b8043c0786a4040300741030000050700820441c11228242c9011201c42c01d0b07110000f002c2040c6540300d261001c4c540110002c880b02c01082d00107003044180d0350144103001d1782c03105900300e401f21510b24401110170700440e00024040002160042c3c0941400307500140151200d2000300c00e4501d21404007200050004101048416070b00000d04120f005802c840185480141c140c02d0000c042510821060b00003c64019051207800c080030211030003001280650880306000b540004080808100d01d9501c1c601c00740b4190080105882030300f00a0001c82c2c85540501000c181e41a208031a465260616022654002c04c0010015802410040351f030308100e0303c0241c01c9580c0500115221100c1c9805503246803101d10002e03804c40c0003071900a9a0b04003048603d2800521900038548004440b40050703c03401b6503401441c002c41c0202c0d07203055200d80e01c0c08460708104441c80014003503044000050456003482100f10300d414019140841c6080d007200000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 948682401 1250 948681151 948681163
    0x109050d0c09060b0301031a090a0308071715011103182b05030d05130c0b09240a030c020a0b0408090a18050a1a01020c040c032027091302060c 63
    0x808904c00400108244111081621560b40c12042c01c919241015200240c4800d1032040c040d081c40455808034041d1071190500068200c19010200b8050804050107090352084040043c0050140001d04c010781d400401110b4680d8404126510b402540c0c2050081080141400c0c040d004c00741e03600606030780c948640c0904001d200d1005969a1180321501e2000c803440034200d00d00310b0103c0121034001489050750841075a40b11400c0c0d41d00c80c804c1d1000501070803c0603218500e00740178051101001d01c02c480141a028245071014032401c0300c0d52000300d959030303051900681803004200100300490703980700003840301001c040c140445194644101c219072032440d11030480000d03612020400c6030005803151400211865000e05144841040000c0da1000100400c07441a50340d15880c00745240640d000789206186804001c01a90700203031000515005022030410740041350142840036440c0c1d610003036022400600d410305a440b4016400d90728162000100c4e0046c1c41045082c0d202c880821003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 948683651 1250 948682401 948682409
    0x9090a0b0d0813031e050607030e03210f0604090b01120c090e060601080f01150e0a050a08030d0c140a0e0103110313020a0902090d1e1a07110601050109050d0c0906 72
    0x1641144504e945041d180110364901d054003140c0d0841444400103001107000e5811240714640441c44140040045066100c2e0010030101d03001581101da00881031124030030321401103207072a035441d60790b00e40070b20058410403a001055080140014010740c41c0080c10000d281d8041c03400603001641b1040a0401c0361800700390a08543d00180800140b0340e400301c0f29a41c405514021a08107501d4010070480c00b0401d8180c58081c0800410490b01c1d0707031611440100113000c01080f10141e01d84d151092500e0343c0c000400780500c6420b02103441c0c3c9890003a01115403440200c842246006c281c0034040b03446030400403041c2e04054941c49a08408001c00c4003460242c904e110101044d8042803040100800a0340d0103440c950340148200d036425a0b410b1000f00d00a504075103d43d1510440650b0046200d824950042c8a030035801051030a0a5920070b07402d00c500c41c19150f008880710f843c40490380d074002c01d02c1120b0005250072001d21a60134030b1110008060b114150390009551544590400d81d0110b400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 948684901 1250 948683651 948683677
    0x140a080a030519170a05090f0c06030105060a052215080f13080d060801050612070509060d020316120605091f020d02040504050405160e04030926160302120309090a0b0d08 75
    0x20a107e07108a0500c200c056080c5075000902020a203e00031418130b0205101c5c2520520000c2411680700303004c1e01c201d807044500013000041043e00c66a1003e102801c0d8014010066000300104186500076104140107480c1d1400c04c251580d1003201307e81e103072504100200d503841c0090100740c1c50f000c0c0f1750040c48040e081e450004515481d0180038010307010003400c1500c046910841040001d500d40404a540000091722002c00708242070002c640781c05022120340305105e540140000b41d403d8030004512543c0c1c4070350381c14002901c6034075801d565680001c0c050500c800240600010110040d40100303052005940d025050a68413400182160001c803000c0d0703919004040490306c010700c031340c01c41009040403105220803401c094400604203a2140111800501e81c96940b000390281c102c2c110300e82d01c05040131100d883d8903060345110a607040c0d01c42207000304851003038900c03090320100079102940e0010707141c1d5110390344060480000c0c10102c903441c1c0d003003041140c0110108407039034000c15842003889 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 948686151 1250 948684901 948684911
    0x4021b03070605070e04200304020f18060a171c02010e010e03070c080304180b190603021305060309100911091314030310120c0f140a080a030519170a 66
    0x44c0060804c5126150191155145c198005041081e070880303040c41017003690310719440c1c0e52a072010441c03069800c40da00f90720196540012a1031103e150103540724407030581d140e00c0d095645040c0d0508000d1802140340594006d00855901104125100e95005030b41d480003145c8030701c100c1c50090866100c044500010340000138010140096440404000c0000c0742c000e5240c07900d8010410120007085000d08881a00c03041c0314a281d40c0c400250b2000900b80304074990388595102c4d07014009500c1001d03600c000c0da0351200d00180303602d051020340303102e80240e40107450000d00c3d040c00103008104542d001c84241d00796805189903074540000b80c80c440c180414507094280c0702f5040c0f011003803803144240c6a09034010010022502c44100c0e80c3c1040710b018114540454800d0f00d01788241070401d4010000c103002c05280013481600080306c0d24051903068441810040d102e04140c1c0c1c807401d107150302401184040100520650642c00c07000e81d501e6003171400d802400c01d0b00c510700c80d01440642d0030400840e00c407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 948687401 1250 948686151 948686161
    0x6040b33040c4109150a0201090b0c0417070305030f0c0a1401020c0616021e010e10021b06010f0b0f040308071505150901061416050f1e070504021b03070605 69
    0x2200449a00601d40303a0600300704e442000a403c041030902c50495510021072140010b034003d401004150740e000d5010549443c00d24003910309a0481c0c420100301000302c0b4041c815003031020400d07805880d001400f55181c009001c075104c540d80d00408140c1854800c0505030000b10b032000714007400b0460701ca40090399501000c01e005141142c09810082851300c02140711110170380026034090300900d03421024800328a0202c240b4010841d6a088a405000b50300d10003004d18226401002c1c04512404102c4465004101503a6a05424000c0c1103903e4103484051003400440c00c042c0c500e18002ea400399141a8880d980c0e01c0c030581000c08111401148131201c4030040000f40a01c592080a14800c0748141005a00143d4103407418840c03641404020013010710150a103908503401001039030f19000100c078040c03400641d00c050500c20018240034006c40080300090b44000340c54605007100040000b02d00f800700f0440290300c49d500c0035102406810041101c08024005020458050b0200003518508 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 948688651 1250 948687401 948687497
    0x10801081203041104020409090b06010f142517030603011803080403080a0e030a02031b0c0604140d0c0b090907030e0a2306040b33040c 60
    0x681082103580c00492940881540c0803041d2944a600000303c1303400d00b419034010030b009106031303003040f18a00d041004080038050002d0000703008080c06e0f030b1001400d86402801b118102c91813141d64884070401c2010065821030381d0380103055403c0286050300c50140a90700d000364070400c0800030072a002d0101c100b0a10303250a01c03031454940c265000e00c0c244140745a8000380110300040005040c000001701041180506900407507640102c4c4007103968521003404080d607a6004a021a225109a0302e04400704003004506192513080107842c031800d0509000d0341100781001c1950b001d8215040079255408038041283d240002e00584101ca80d8030751a010038491b60344802030441c4145400d001c190030038000e00051030213840707801c0311101c80d48a4105092148410211207416101e2281d4014081400901c221250140c2e010300f1402c070181c2c840380c0031600921410310390840740d440580d0786a14070703050036000310855000f07500d402289081e4201c10401c662039940d00301006101c0e5400c2010560782 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 948689901 1250 948688651 948688667
    0x108090a14011b082509050103020705010e06070509190503031603020c0411040e060901052b06051f241b0f08030105031203090c100210181101030213090203060a05040905060601 78
    0x4005892514640e1000d0009021b04075180b05003410540d0000d02801882030a50280c4498100d8074265906400c0181008100e40c2000801034440c0c0010034004d4560441c221040b0101c820180c0a1820702029548160b4a483d04c660280d0a5000b0b034403541c4625a100d102d201012100c200200c0d4840307050104c020040c03c0000c0142e8040c01085005200c00e07a070f030b0315102183e40b0f00c00c0c075210b030886114042179102411501000f031440b400e00041c08400ca0400c4810540741241d51045480613985114481d022007400c2203809104804c482c4101d400d51280b45000010040c1740d0214204c4045035851940011008205583e50303c00071005100764981401044004214000c01a043d428003450146d11840088141882000c9010750740300050300070702490220002c1800108209034050003450101915003408450400c000c400c03021080d03010384255907440040b1641140365a00380b0308483c000358406401c2c3c0b58440c922600c0092590744a020300c0c1801c0c0e1240004c1c0516081900c00589111 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 948691151 1250 948689901 948689941
    0x60513050f1f0b1f0504050a170d080c070809040b0315010e0a15050f01020a080c0d0e0103090305070b15040905070e150904081602060708090f0108090a14011b08 71
    0xa08002c88038030540e9a84c082c000360340030041000d9921002c107650a84252095030b00c1250010b840d40800034503020015942c0c444403003080181d41441240d101e040310511800c50389824403000c18030909021400080290407901805400024240000000286400c030300c200c1d625a0800440e00500c000c103603650011340c02c464182c505100110314101c044d8200b020a00a19000342c04280001c0b88a80c401c029a80495800c2000e440e0342d8401c003e01e660303c1c1c0031600b0300c01d030103d2800709200100d540f191080044058042e51201d0a1020b19541e90103008006002c1d0451811500110145650f41d481224446440b4100500b0f080b80790030001c2420743d200408021200c141d041d074030031154844000ea96885035000d6a100d5640c003500030b800c0343c01580d10301d01039042000841c16900b001346c60002032003e000115000d0240c480324500446030a0411035005a085c1c00400c1258006240520b401c03a54142c59800800d4501201c44506032410140448000007007441090000208070101c41e01059 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 948692401 1250 948691151 948691213
    0x6020306030d0e0a0603021810020d0201060803120a021b030c0d0206060d020a031509051204030506180d2a06141303080609180f0c0a0807030b0103060513050f 70
    0x100b03d9000005091143d140300305014150002130000c0340c1e89500a9004069400520080408007a00d0000b562041c2c02030b2400090f6207002c1d80031074811000005d44410352a40403d4030525901c1d521503c01079004081480644280c0311a010a03500080c80030f80740d00c0c0c82c110000c3c2000092010700900c0e06602914582c0140321031000e800240e200e034900c8400b6603411113440f0300684800c90141c0c004140c421406050744c0074505050b6540f034585d4000384101c038007942c110354080c0c0f980c05035022680108411003200e980821a91100e5500405c211005105284501408503040101001c4010a440000c07034089603106068182e4041c00104e054112020146100d01280559806412503101a04551065090b400003949a00000e90103a0b500203a6500762040404502c640390b64400c0c008089610413886070304040740105000400e001103e40001d42410242d20315140c500c0140302c007400c00c5200c40c072402800d42c04103800304040b1110f1100d10004107a81403020503e4507401a9184811204c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 948693651 1250 948692401 948692417
    0x1b05010503190203090f1015050306070c201917030a0c0314040b0a08250210020a05120702060106030f0504030e090c0d18060608060c0406181206020306030d 69
    0x201c00244040071142e000c020100503625100c8600251901d03c2401c80d9012901c00e040b0f03004101281508034010307040c00700c5540456140c9647c101511010b04492080008507038007511310128052800b04001540604c546400c04284840400c0d00200c2e003003400c42c010b1409120400841c52076506100700074244d07001450418030040d8005007482303101e040180c104014001d1440c281082c40e001c940003003030300c1030050b0340d039456500026068000071502c00c0c1c800c055420b14001240d4124281403149a959400707041c040041e800f103400203402100f2008100074007844200c841410581c083d5008000640040840c0c1d0300d00507008050710042d004046001c1d00705802c1c880029040082600611412210340505036503821194085005e030245a550450030032604044050500007041503181c01000e05010440c2c0703e50340d80742d0f2080e09507000300c0401e43c100700400090344030301400d416040d003490b40c03100c083d03039104c1000808030602c4805a804643c00403e100c0c82d8a010040400d07a03441505100c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 948694901 1250 948693651 948693661
    0x3190f0f23130b0717150a0509101a0409020403051f06030f0b0403170a1d03040609052e082e06030c0207030204140106020d090f060f05070507031b05010503 69
    0x38a505684000f011201408046226140140203d84140d692003a4440b0380b480d11980304901d100c07102d075900e4062800050086168248102c9151103110b04500106080740381a40e508016401c0c40c0c41150110000e00000c01c4052180c0001c00045001c0c00040542c0c455040000348a80ea540d034001c80c2c250301d4038104100042070850080320741c1c0c5d085100f12210303507103074181920850b6000200034001c08035001042034505050b0710070051543e441d045501c000700310120a5990303100703a014400110704103410030082813400036000200c84507510341591001c6007010403c40c100b65411404400b00315841d00304404105032825000c3c1c1e650003604020241c00010001022500150040008040d15020810f0807113000300020402103602900400091029a9000328004002c0c065800140200c40020344010f10908051b001d4400002030030070110b1900c081034030101c00e00e481a00c01d2100506c80c003004640d05100c0780d002140613072510b0381e40308800e070104522041640c029505002e814420b0103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 948696151 1250 948694901 948694921
    0x2040b0d06150b071106090f040e030a020f0c03061b1309020a1d0d02012006100311100207050112060e1003060b0a0b0d110f1b010c08010b03190f0f23 66
    0x17000c160290380b00c80c2d441c1c1203400418003c580340c0d1100d9402909200030110107a00c004010459a0f0581d400d071601c007418541055107610540441c10750560000c1e000c11580400c030b0b18070002c4040c0000001e0318240d1071007810b076107250b4141d22444840390301040394480190400e05880d40300640e80058940004154002640d034400810041d04000e030841481c0f8250391003000d110b2844800404580b500d14183c040e155603011140401c4401607107070080300046083c4a04121040c8400f030300540000c0d07003803000440780004040e0340a0521610f13004002504d0030780f201d56600a8103c080e5904560381181001015201c1c9140ca15000f80301c1400c0801946403032000b6a1028072041002003a042164800c40c81180900c8549614004000401d201c1a07810040260781d1019102c00038040032041d03e40c10b542030743c02442002c0c801d20302040001c6450f480c1000c2008481c0083e0b600081d248036616000e82290082e10114890541d24500080402c181c03940b00745c005070311500300d000c15140c1942d000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 948697401 1250 948696151 948696173
    0xa03050711100c0e0d0c031109010b040614070803090c030f21070c080303070804060513170721050703140a0c1202101e0b0a061b02040b0d06150b07 65
    0x210081c960300c40d550303003925104403940d80100c4e000030101c0004a44074200190070300b00740e100031211042d03040c2c0002100d00701007407601d04850480850b181401d15012040c0c80460b0002e200c4c01904100f0890040001c1151010703500844004008101011340c0ca0185898440c1c4a250326845074024150001c02d10201140e69031000603803040941c890000d46050410103006802c114a076000100030031a0a541c00201c59104a010b40810302241c0c840f0340f8000000d13140701002912081024013107401c601c02e120014a0454410408100125500d07280c6ca185130141855420010b040090740742e06255026121030002140034851034a002c4c0c2815001d01400400708000b028130300c00003a100040d60003802450704070380c01030005009d00028841c801c070744510300300c240511152818903011010308084003803c054a103191107454082042e05101d00324485810340c02c0341d101d40c8941d8a2481070701c45c01c40c0039241c0d922030000480c0703841c051004820010820341000308482c07400e02201c00854940102 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 948698651 1250 948697401 948697423
    0x7031109190902040303030b030d030b0109030f0305220816050a17070305060c0406090b16020130090c1703031906080d0c0311010c050324030d050a03050711 69
    0xe403100d441d40540d51803078907841d0300003140b81d480414000306064044d08800184001241562011340c0075203020350403541d030440d005001856544060000032009409981ea1600034105941802c001d020316104a81c09554440c1c1070100d8618100072400c1c0800c03000c014803442003030340703800c0710706101c04070303c1c855100e02c240440d510f0ba00820450b80502400010301554010058550300c3c5001d1162400c10703071107803145100046010800107650010041515002494003011202e00c488640045844480d220401e0401101003421082d0300541c12203001c2c1d0030b24000c5000320b1011130609014640e50182e5101d0104c00849545900e1003086c048102d030350010300070000e1083d0204004000d0014540c5402c00c42c1c051045149101e4001e0b0003800d5039110911a41c0c2c2c076900c0b00b50031942d140c240c0c0c0c4852900d40104805102045058401c02840d040210503000e070449494500e40000b460011141505c60100304009880782c0317000d0b81406070301d03032140c036505080c95104d110405483e5075243d0610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 948699901 1250 948698651 948698659
    0xc08061c080711030304232205180a0c181509020304060204030c0602030715021c180803070519080606070209041109011806170a0b04150906020d0507031109 69
    0x1110020001d500004400e01d00c03020b021170b03071100d49807180700c4200d400024604251074803850303c080b820f07d80320441028845080440344d104480080c0c1c04405881301401c00c83c130708000400d40c02d071140c07010000b6401042c000c81d0725400c114980544605500802880c1e91003090074659881c0d02d41043c41d4481d800c89540075001692a5141d0400c440207010ba900002c00d190920300340001c5440c2c1c008007500c0e92a015076070020796801c071070b0100c40803840b407240c2e40c0026810440c0018407007015035109148811100c8180c50850f58a9959801d035540300321030840101d400481d010440c0000402d40c40d950401700d041c0f082c0c660a007074000401a00611000034030641c00c20b0001020031100341006010100091f00740109561907084124407030385002034030b4145614015000a031920a445c01c40b8000801d03001038070110010752107503454480000c1040e00d410000080880b1301e44514440c040c2c80c0d900820740140c440403414410401c0d120090456001c06040064200c482080503040790b1400104803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 948701151 1250 948699901 948699907
    0xe0a020603011a04050904064a0f030a1808030306030712020402070f051f0b061204140a0c0905071d090601030b130f150e07080c09060d0c08061c08 65
    0xb403c5101548200e81045801460b11028403080040a8010815200012410390303410580c07a00d03141d18403078000003112040c180c0390214041403140c0440c01040002494262442c1d10080c03a0005e00d55030100ba402030001c0d000000098000c0c00c4240c0c5400075100c80720182d491030074083d00003540c2d50f4042c0501d004074070080008070b0466540ea41150001ca5006000845c40c514904165407a00840035110003d00841500710105421520419081071030003019141010301001d820841510010001c680041f81a550020070b204200001138010f40705203603e82003942410001000e03104040d1584090001e40516400f007074180e07480040f2030034070565842c6465a07030600104c003e802d002c481d04e500501c500c46885940380880e0441440106455814000b840702d020341c21b07034684054403132550b04c0700031480814030301361080d09401e4101c01000c480a0410100c100065125440310124040040c2c0d01d400d403c0d80d10360011499a442682140c0b03510f20865181d160300c2616855186c003c3c0942400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 948702401 1250 948701151 948701189
    0xc0a080709111209150c07030215100f1716060509040f1107030c05160503060a0f14090a030e030705031b0d0804030b010e4203011104090e0a02060301 66
    0x1402c165000c07050310300012615420308480c02602c40700160f00ca4009001d070750000900c0e42042d0001c0f6402c507035155008011011070030031b0042e88950041c00100312181c42e0344000420810007140f4001500444000002c003007000c40c4898034142c1f09420f054000c0c00400e00800625421800380c1d1508081a075012660382c540800c3d480043c0011400e20030080400f0409005141d1301c03010703010266200384111258846072004200b07107601036200304c40d45a8007490000c0c2da404040d40110b030444282c004046002d030040115003441c10811540d1014991000003040d0516a100310a1900c00030154090074641d030038000401d8480300b17886000301c1400740d0455482600c0e02c0c0d4001100b82d241e0095842d03902c554484c079080d00c102d0020320502480c51821030201c3c01e0340711480c40d85000301881140541580d040009040701d410041d40c1d6403118010300408240142d01d0a02815920100c05020f0030b0756981005680c2c000c59480d010350f800254424005c02e40141c94000032039054952100c0c4449074072141c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 948703651 1250 948702401 948702431
    0x9062606070f0806040f06080c1c0b0730052a040915051507050f011107061e05100f12080f031902070812011e0b0d0b090f090c0a080709 60
    0x515046c1c1c1c044039180c40c4000a005101041d00141c4a00842d8074146c0c526402008405c18103e900010b40700c081503901164803e40680f1200407843c60404041251010201000b00e04044a15040700c01503120010400c00004240e410721361450070f0f90303181030205100542025140a980561090300b03580f04801c2c0710f004000702001004000060111000400980500001d5000000212200d01c51003490034030551041c060b0b00c0e11110300c002c503e07003883c00ca501c03100d014081280c1e031002c0712080140d0b00c0d88040c156004680c0302d42c04203070381c100a03149001e50300003441d5016402405020002d520440014541b801180d01c010020651719480b41c80300d140380300c2c0c21f421207400a1400d5200040311803c00850002400442a41d10320044541c2e0303990f4001c81c03095501e0b074031041032800345000504c03214641d80c01030002034480d8240080c000400502160804005690410602c8911810412601c0040002200e1510240d800c1800140f410601e15510103090290385840c03070f1282d1142c0500700c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 948704901 1250 948703651 948703661
    0x60106110c0301180c061106070c060b0301050a0b0a06031119020f03041805070306060f030c0318050a051207080d091e060c0216060c021909062606070f080604 70
    0x15008008001103841c81900b0411005130104c2214009843e91000175080c0c0130380030280140844402404455440003000c50b18014804012103415a48280b00d0816032800d02c00c480c402d4148003000580c0600c0e540410122103565031240040500380340c403081c0342c0509041951a0310103a040301c414621450201a41440807050350658544804038000801218030420f40e10715420403d000c000c0d548903180d0440503602c2d1409044003260b0318544400b82c6511940c00312a10450030f00e00041d8418821001030342089001100750348603406a042c07001401130511070048140c0e44052058a00702d8160358506840c0284450440748954543c41003007130005000c41204414100340b81000544011b1410100500e090743c0390f00018401e00350700c03041482c8000140403c1e1840c035242c00c030340b8444a0303003009000142a8000c840300c03c002e400001e80a540c500481015113200c400c440c9007070b005075914100090400500e5030181e0b20181c24001c000b500030001c0c1d120200f951810441d0b83c0c0c2c0d40d10106010308 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 948706151 1250 948704901 948704923
    0xa0204150c1b140114041203081501141b0c030607180f0f120303060e0f09060708010812090d020a0902090315100608070e091602070e010e0a090512030103060510150206010611 77
    0x31a016521004060b40300030327114481c05013806080080060b000045483d6110303400300c03500f5001c040180842e140101900c00e5244442102150b40c041e00100c0480c0c200710301a645500407802803403200442440010a5001a0182d018015160362a110b410765200300b040c400c02c841c02030501c4805003410300caa08024050300d4100090009400e0034500000341880440b00503945000c0e450110719064426008203048666000083c5018800f001c170189442c1e10052125034424046a400c1c401a207427070340200014020035000503200d00c014014141030016212206c211a210030041019900720230001c02c003910340a25092405d80e403440301c01d40300b010045010a60040341041005840c44501c1d10b85440106580d0a035003a01c2d95500f83c0410b007407801e008401c211a0b880300041c0f4001d400c4d60101e41c00394080c504403000e04030320030711040b4150700a800564840d9104d004101060ba68007401c500105030703070566407031328110400d0001c0d00c031401801240304100c01007614950380752081002103004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 948707401 1250 948706151 948706169
    0xc1c05040b0f0d05060f0312300a1b0c0f03030204030206280311070f02010e120c0306130f060f0609021605010509010608150a0204150c1b14011404 65
    0x40c140040b01d0603094200101507001a42018001462418050a607030034581015008003902c8000c421b1540960b00100c110b40030441c0c0d51034242c110180b210001a00000302c04118000034201040c0d80b80c00c0ea5041100030b4811301e00c0c1c0c03031076036103d40e4850301030354209410039088031380110f1525084005c0e22503540040d6000c500480c055080a0907114105d0440c035000c01d0803011800500d0040d0244d80041c1d41d0b01c401e40d401445404007080014a80d030201520524207035440c105503000044186501401d82103445c1e0200c50903040300c0c2810001190444805131390b0090070a0729aa540300180040d40c03004201d5500d425420420035815046070028209461055440c2c020000071014120400c3c501581c1560818001c01c1c0502010b03c50102924204c0300904228a51602c107510358881c00f90a00360641d40c20000000c41c1400951180d01d103101d19900e400d102201c90a01042405880051220301c00040d20100300703980d600031082c003034000c0c2800d006040740300700b40481045003c0c6501c98400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 948708651 1250 948707401 948707407
    0x30b04020403050c1801060e0d081b100509070f060e011112070203151608130606060c120305010b0d0e0a0507091d150a1d120d0f020c1c05040b 63
    0x8116004c9580640b10707205a403c0c00700c00c01400c002501c200400e1041801003030240c070040c0d0300e50604102200b0924040c1e0105454038174201c8007544c81c0703800541c40486a800080042032138001e980503150b04200c20034010402d480c1808070000303207541e4600c60703401400104020703440107034003804007540140048401d41d40d0310821141d0b00001d0fa4403611040748a4091040140c070b0006426503824059094030510360040d011076403065525400c044d0000107600c1d0400010310025140d1b00580014102d43d47c0d54424641a900d001e0340e11812101c2e80301c09250500d001441122506415581d40c03000d91200400c0d0400498401414608102d070301030424080c0d1940410340201c10381003250041c03680e82d403641e150a848241c26031038071001051444625482c0c004142d810206400810304550684100070301105c801e0a602c0c81d100003448032a10702040071a203640811040d05c5491420780b0356000c25841c001003620300513141c004496107800c0c50785400400c00081441503040e030340030340080400565 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 948709901 1250 948708651 948708653
    0x80919030305070f0c080901030c020a06022209050f040209100b120906090d0905060304060b030331050d0f14030a0302040906050604062001020f04031506080a21030b04020403 77
    0x4042d0004580c444041107240034101c1e040c510812442e000285c104603864100703040f4800440c040c040d0b4440c103a0452148046c1c40000c141c4c2071008148111803c1003111021030807524a07441010b40b5840300b0320072031504c070410440b00c1c00b8444172a80b0035412190354230280c3c0c0c0c503d4070100300a1180c004a03005600030030b95010f0340703071411181409900070004031180360b92042c14665580f48951290310006800903010400c5040c00e00285410902c10000488c0001021010900d10781080c8401ca8805040d443c008903d1100000da4940d0721100d024610710a90400000c1000c540c0ca052000340f00c00b0714030f0070702000e0107101c4e01600203a04040e401e80c0c1d550320301040d0040103074000d4011504101d1410400285074941301d42100c08440e91912a0703080046032400c01004d0070150a08500310755003c00c0328880083e400750040000d94450b05602d6046400b09400b40700711512500200d100380d10520341000401c03010340b442d42d81114401c07100b62140c0b02c5a0400c4001d04003030050181c2050000c50040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 948711151 1250 948709901 948709907
    0x224040f2604032d060203150607080306010810150c0809120f07080105070e0415050307090606180e040b070e15030915011a0706090c0b030117011a0108091903 70
    0x11240140620403240700c880840a04a0715200c0807203215071281c004138400502c0d03940180d50300c4115183c2c0301c01c039501c4040100e01c25500640040380c12030800003c108541d071f000001c850f04007042000b80ca50150914070780001049880c80c0ca103007404003201c111010060850110be840300300c05072410207200450b02d40f2541d580b2400610a9590040c00c001240c0310105200b081d12035590380d959410b6180341102484000c0ca00ca0b03603922265a240500810661401c01011004000300d4400150341464440010850f18844c081e08811100f00202001607284420b0156046038102803041001e46805d070741503400360280011f094108481c6000c400c036021415015610640c041001c3d107041104003940f14030301304401d004805c0709120081c000703000810000003800c03405210b500e0024045203152642d036600d001305d07404405c208100200502600c00070448002c800c0c4c046100034000d17180b4580341c0d0110390204a80a80c108a0108001030307199908211500c0c2d510044103141d0440400c0f41802 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 948712401 1250 948711151 948711157
    0x305030903060702010209031c05070b01080d090b1305011808070906030b06010c0c0e0604020408060901090501060815010e0a0209040e011b0e13020c070b0301060905010224040f26 79
    0x240c1d100c0e00034000001c1c10540180200d41034690014050031200d1600302034200724a003642107120801901380401000a200703c15614080c154030001404681ca004038001d085142c2500009000034060007510090448103003024161202404c00720413003090071394070780d50040b01644080ba10780302c0d150b0001042152a03000100b41c0c0c0c0a000700c004151740b01e07801550312003056400100300d0310b07030340d0010000c03401c2c0e0000c41030300705c04020f201620b05580c400c20035280200641d0303142101d0755034046910402100340b080000509450014005280d00e01022182c01e150501c145100842c00900003000f40905604482c00c440d0003c0c4204540e007808156a8002e181d8502d5840440c00c02e0800b200c46c0c280608040c0a8000e001880031b07013407408a045c00e00c065040f00403940e0321407048510101d020200304024502a01199072082c0b038951070030000903e0001c00c40204082c00c0c2c0300340e1880b84200510350400e0343c050380111072800c0c141550324181911000c80031000084840504c45440380361882c00017 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 948713651 1250 948712401 948712417
    0xe01060201061409310b090d090f2c070305311403072103052a090a0b04060302070b0c031e220c15020706270f030503 52
    0x82004945414920721003d42e40c00360298080c4299000410f081050940356900c01c16150070b52418a01011407001c070444540e504848030000035041000980c0c0400910940d42c3d8240b03050040c2500d401080b0446015902404080c0d400f52007039411909000000702c08800c01841d1251264602a003009004000540e158400d102060b841a4524072000013040b0000490881000d00d40300f1aa0300c001c2945102c00e4422070f41c3c0001e012800c0441ca43d202002c160340801c01c3c81c003e00104040c00101100d00080050002140c3d16a25000c8c841c0322003141c1d02c20240e20301210343e80d04190350004651400c10340c4842c89030100004d011842036859000303440711901c0740c1140341c1c0c1034036030351500c1f501800202c8201c0c1c503803401440c2400c445040c1910356500070601080c1081440803140c81903008010711481580d00c0104098200401400449100921021031010f8440941800783c014050000f506001d050075900c072085120003400e448a1000400d9082c804025040e600e1030219225003107030390 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 948714901 1250 948713651 948713653
    0x3180f031505061509010c0303060b0f1e070309060806030f16090e0703050d0c0206070507080607170402010e060d0b06040f05121506040504032105010504110705030d240e010602 78
    0x201042c03d90815600d030741e820b000740c028071608008060004440a800d9218107404058541314001402c580090040200043c134042055840010503803010074104543c0e0b143c03032952010060030300401d030310210306001e079115442c00c145207032182c4001034642540c03082a900c040c083c00c8084020201c031390a041e0103c1d0400e09091280c000e0314070503079031070301a14407014055410908908205512525680c600c1c144020145414440c16403200c902d0070f05150072501440e4070520a0146041c2c0110030001d50b0703429810280010310b016030008104e01d810035485ca002d441c001c06c800b494154160040854404041c0c942510303140d031446604000d1445218850040882c506007080b40d240c04038800e014984c1046601d00d40e502c9540900008140c001c0c0150b0800c101c200c101850f04100d0090700b003000031484400f0440b035040c5400c0204841d40c1000308010303001f04118450010700f000c0181e50591240c0840000d55140d003403041005540c003195032107409440074801003a0848008505816120154 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 948716151 1250 948714901 948714911
    0x605090f070602030a0503010506030711190b062205060a121b0b0405090123060a05070b09071202042c0709060b091f020c060f040e2203180f0315 64
    0x10400d0f44c030ba101d501e1031000010070820041c40389041c800d004540040c01450055810f00c40713200f403541011a0b00e40105820300d100859442402400307004140c0100c42212441d0400000700d4414440004410794080b80c240c0b60000110f07140c0c0d035007524000038030101f41629011061031400092082c2410740c41001180355050118601d114501618240c0d84c002d04108076503424808041140315408a0b594410340e0380b45c01d034091944030f80c0041c2103071320711940b030301078564a403481d1083c0101c4000700042c1e450352108804000d9400f007070240441c0713260144d0f80041c0d000e0750501c0c03c0d00e2000c605a401c0305200901c0000409051f400203600084035649401001910780740c41c000c100314030420322801ea00001c03210140c140820b814038543c1e80340c865401202e41d076070119408510a60403900a50810030000309080100c42d07601d1034600c5c1d00010b6480b0100c1c804034005852489102c3c2c151000c3e00300010780706481130480b800d00b070b072401074150b103088869100da0324503058820208086518983d6030402d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 948717401 1250 948716151 948716159
    0x1b05090906010305070302060c011506050403060c0f2003040803030103030c020111060c0316020f010f32010306090f0609060b12241306060b070516080c0d020d0605090f07 75
    0x407446905070782d030100c00f800706549141c003080510340041c001104155a104071100f4240003d07540f081c000d1032181c0f41c1603201c03491404c4c000c084610101510040c411520304100d84290b00400414482c0c400000343c0008001c10200c2a24500554000c0c40d0140700020001c8181a009080c004c1c00a100340c2e1aa081d80c1801c000d0161070342e100b9036252407075450520100e0414404d0018559034414144100e64245540144081c00d6402c43c0007840c4900f40e994000c0690000d10081c0355075030008040b80382d800725468104010000320140720103040c1a54502c0214100081198000d1005402000170301030007031107003080c83c018000d04250510400101d811310140890114030140d109280c0c001019404010781200ca5241c50020074400c180001c0ca0600400500c1e1481118003601c140940079444000e186407180c07805880d68041e00014a03006802c11404030006042410b15100341c070561401070480c030215240f950201c1004140508050420040c84c000007035202c000344191707045034092540d07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 948718651 1250 948717401 948717403
    0xf06130b0c04080a060f02090916030c051602100504180509150402011e0e0310020c011a211e010203090615060714070b070309181e0506010c1b050909 66
    0xa148140f120a0b004a2078440108100c3d0b0b010740c000e003804581c05882d0050410020340100c108a4451905100510500e000507a2520489003038040e035060041c50310014444e42014039a08090013841003c0030341e050204640703e00282ca00a09a80c0c0312030001c550712090490240608503a0003106119400024007692076003649a40502c0d01a1914000040055041050821900c2c1114107104003e190307119551010800e85034224554100107884404201c0c1301c038250b490b4020781d0b12031000c10144001c241d0381c034445502481d0219801c0d52402070662070b001070401502d0b0180c04284c100e80e5051048001064004600c51384131001554070683c1e445211400800c0c0040c6180d4020b40284030042c00244410b400d9408040748008a0308103660740c40c44e1031810780c030a41d0200e00250a4210800003000142169041d12000002c02e110701d058400342c9032500e9039141409143c09484034003060302031b4007648180000e59001242da0203c000000d0310006c00303000603c2603a01904a4400048814034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 948719901 1250 948718651 948718657
    0xc020904140d0809161d06040b0907050d18020303030112140a0c0e0f1b0c03040512070f06020a0213110903010c020d0f110316081606060e0a02070b0c0c0f06130b0c 72
    0x100619030340802c2046d880c0c84882c4000101101c0d0040da4442d140e840959481544600c10203c3d0355820355214800720401d41501e5140e4001c0c000d02c07216540b690016a800b000350b0341521003808000011941506004107a000340340085000c900620300c480c0107101048004c40261030081c4000e00c4030707848203030000c40c2c000360031a024072034001904c0007200101452002044a0b074121000c032070420361a0000203645d1a180c018100035503100c400100a80f1603103496034001001c540c0040d00c80d42c009600403e01d000750900380c40c018940d481c24203010054a01c41501c0c4140005002081078400d4020301075540c0407280c0207007011646c00c806240317004c2e2140d0519540707107810002030360810300a103140c07064041104604440c02141405450100d500c001800000180500c0300070030b0b82c0d490121000308444000d08116540d80c01005507902241488801e182c000c038a080c1801e0765030a020325160308115903274550f600180612010700050010f003500d8000c0d01800780c044803200352030760300071848184 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 948721151 1250 948719901 948719909
    0x40f060503010303030509031227010f051509070e060702150a020d030e1f050a020f0c0616030903020c1504050a0b3c16060912120b010c020904140d080916 68
    0xc9c40400180010301e010a180f50403107002060f92400b15064000c0c82c00d583c00c0002d405c4015589604111071071500080c0d070508110190b42100003424031120080c41c1c03500004116000d0b8000003045400c40d103501c074a0100b007a01d2800d00c035480f0012114000d407035880041c04440040d091402807030314074001141e1821240d1007020140da401c2920103c1c00301820004051005041d07082c0315041031400e0100c010008946010050041450140810810241c0e11381d80d08003054507029600c0000f0303400081100415100701d46803407500300740486134580e41c4284e8110a805c020091000540c02c241a030160107444142c0320a4902002c6170040107400b400c0411144402917541644908010341603002090b174802a0f00301c3e02e2070307180e0326100c03001625140d1000315200714041500005150740201703409100c140342c00e0b06020310300303080300006e01160345c0c4100030b13106028440101c0d0420404925818030b0000c4e60702030301d085440c00900580158012036100d401805051210001034a44c402010701f50303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 948722401 1250 948721151 948721177
    0x4051c05010b1c030c05160810051e0c03100b0a0e03150937080d054b0124170f041b0305060604060803160209060105040f06050301030303050903 64
    0x25503507644080300d000c0c003045d10580305801800051030510100300810b10140072440010b01600780c62200400481d100207001d41d1001c5003040501507043ca02090340341e0049881081d03981c0300d486000c88440f88c0b0065034448000000006690404d840c4c1000c11402c5c072206c01c80a590305542e001e405807000408c104da0940248d00f150602d64000d2982a581c4060400c0b82c040300003100071401201032041c0c0030200141e501540100c0e180700c44203400e015003070f0300c6540c0d449030020b002c118604150311400000c0b081640001e000e220080b807400444604140e5401c880862425940d40d0082d51036016041c0803040410020354402c5a070150061103242c4210008001c0342c481680c8083d041601144050012201180c44c404902e507560f45180c6000065400742028106c0c0e0705052082204869055015110b290000c0c841200041d0200503c0512184c058510354010b50701c280040324030b0b10a0350407502c0c103c3ca0f18900400e8096100001c2c43c141e0740310352130400c0b0319200c02000e02d98074040c1003015694 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 948723651 1250 948722401 948722449
    0x1d0106080a12110604080d0b01110a02041808040b0711090f0a110702063c0f071a01030803011401030227060d0e01020304061a030a140304051c05010b 66
    0x1990703040e018034035180b50300e09201d44100314280a0b0130008241c40075078004601080980d041c0032103103d950750705042401c09028210f100c03030f074503504ea0410b0400a4801c80e613039552038004903038065081108684c400b8840e95207584903810281c84c3c1d0030204c03040d40d00b488240304000050800041141c0034003008420f4a44554030b01030b224024000d030034440d5440381018044c900040c0c035110040c001e00b030349060941e031400202084200b462104064041c1041061042c90308511494808039000305031a416040d0395641c2504004520b441c0f810f90b005e40c5801080f000100388154840a18182d80e0400d68002c1104600d00045041e40181030800174040880119440d010808050b106015140a0107480c102002c1d06054021659081e60604951b5000400c000800a0360f116554409040d042c00700c502050480100b5a035014014000700082020342154034000b40801c1035400410300140480709a0f51850303048280340758044400c4400c0e41c00d0454621907803400740504204004400040b10b5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 948724901 1250 948723651 948723653
    0x9010b041205100906050405060c1608280c030224010b1c18020109080f1203090312010902091f2a12180609080a080d0b03101d0106080a 60
    0x703111502804221568400c600c24030b00404a84e0160401c1c0602034100045d562401d401c3c010704200f001044481c0c151030410080b4050b04001c0c00b0501440e40051203503490714480b48401072102941c00b07540d01c0d0190b000700b51002ca13070751007aa5003060038441e030b0a5601d600c0c10f880307100c0c980041d0080503084101802c4d006100c0b805102d400f400a150000101d0001c25001900c6482250641c183d03001e01c1e80c000c48241025075070080e441200400d41c0310000d000e16844484c1d100e4541034441140d8480e14000004039030014420400d98003000c110001d005080e50751400a44025841541201c1c000d00268840000400c0c40ba64113210140341c648402407500e2a520300e4900420001a00c0100401041d00310700c04109020101020301e00a605e400119200f03400d01c15000600f40d43c000c50400000b03a200340304001c00407a007003405d544e0104180e0f80301c50141d01814040c003185000d5541501c036000c24000440c15580046d01b03028910031549900712038503a09035090380c81d41d00451f41c2962000032194 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 948726151 1250 948724901 948724919
    0xf0201080c07020d05210910030b150307050a120c0804030f050c0a0c0501080c16110a092d150e0a0b06070f030215041a1504020d0905060609010b04 65
    0x181d4000c0965956901d0000340740c1c00507902001c50103068409902400d0001c5503621184015900040440360b13680c10010f0303000004610380d12900508c4105900c130007580040d9110800c0c507610300d002c401400c2e9280d00e80081e00070b21070380010034004005071000640042402251003850a040256900c141443d603e94074180e4851341d00e00703141800c2000400c139003069800f003441882032680c880e01c4000384551526000412185018080407090401040744800d503030314082a0441e816485280441d001c0050300c0019071510503540b01e803007204e041c0035402c4c20541030701c005800d01c54490303598444060f1001d0301c00c2045400e03500c04401c038021038103814040110521103190b44212200408a0900d100e8000300c1c04a8000d42c2c4111442114008042c0415070180b240e510b651030a0028086149000d4450010780440c5202110030002c16030041203048034240c02c4680c3e69a80504259038440c0382021841c02028002d109940a001d543d000c80c0040ca40801014101d5480c02c01c01802d090400c8041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 948727401 1250 948726151 948726167
    0x2100c0302100e0f0a03020c091b04170c04020c010b09010f080c221b030e060f07110f1b130606020309060a0504181a09010302010f2f030c07060504030f0201 69
    0xd0511072040b86100000c03458100b09031445e0511940c09090280744d00810322404443c0904000c62111001d481c032803892204034103131b4088501c0b240c100c083c0a0040d00171641042490220203400c1800025803007003003201500f284030781800903140c0c09401e03039880c4880c01942003c0d0247c104190007004440031245003404c000d81c022800500d110146450601c81c0390700311014000750885000d4103030030088540e901881210396290f0044054443d83ca00f80030b1341c40000f03c0050445c801d100c4405001031a092040248080341381e02a0100c800c1100c0280018084680d81402c1d0361080d0045400c2e02d40d41546405484100e90707a0340c00846c10100c1d00700801115801410781d280800005102c000b41d10134007003c1c407442602a40d080080d2114280c00c0190304902180c82e418000c44103500100010b0764407841100b0f619a032403400e140d448000d10403144d88410780e8901d83d1410940746c2504c000344034000c40100074907802c0c4c1007101c43465580c1d0b40f02a2094061403201402100c0b481d00c00d58055400b038825 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 948728651 1250 948727401 948727421
    0xb0931210e0a03030e33160501063506010506090d12080a0b010806130e0a06050c130602070308041806090203040c030506060109030b01051309050f03030402100c030210 74
    0x4540c004001010a0307400140f944181c00240b0140140310b014280121081015070180c1000c003100c1184c5511007034a0f00c00c05500310048a40041e0009400d007010340c00c1107103941d101000f409100d5036406015183c07544a000e0310f41c0c851024612001446010210311070480000c40039101a0f03180c8010041d0980215010710b030021108501040090302e440348845281c0640e80740c8800302d0070000000012907000800c1c1c50b06002005062101c02e940f403403151001d05902c0c0f100070a0300100990308600b41201010002c1150b403c3c40240114008008040e007c030310034481c8811412550f03013500320ba8032085840003400b040400c02c800d000c4a41c0c505100b41022103580000b04141d80e07500a01802c03a8012241920740d00c1040d5070500401c2000e0214a03004502441c0042d03540d401c41d12050300340d10040c0b15171881501d5001c540000308080c1e4128000c030f99000380680d850301c02041e8040c0d031241d0048904034070420083c1c00c02c50f01c01e401580d6150865805034002c094407000d81041000a00394066 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 948729901 1250 948728651 948728657
    0x103020f1203391504030201060b07050703110306041e05070f03081b0d0210020c010612030924050a030e0f03040902041a180d060b093121 61
    0xa400c1414040420080000c4106404803140b8600d840710280d490440c92040c0943c000802c51846140302c3c00021540c004042c1038044040755112840c090f4010300e45036200040c0008041000000e0003408a122070460f80210300c0030240c0160201055240c4030200c40091880660291070041130005406c0c0c11015849070003242c10300350b11060140c4044040d541308546a44000900e0071240d034503c5581c001d21082100208141c0545002c003940f00c1c03600c4070301400002d6010928208090003500020010a00a990501206c20504008009402c5400384040c14105103140c96a0008007503c1080d190035280d80f41401c00c1d0200c1c400301c024103003800400381d0710720030300190800c8020b040c4014002450301a40040c1d4940ca002c54030a20b09540c000c05100100c2d0901102e0300b0190140880340c64058111040c1d400078441d4a026401410b41c0c609a61b0403001a0041141084203907811411464101b4032203011442c4000300c225200c007450000414a080880080d1490741e403a10340244525103c1c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 948731151 1250 948729901 948729919
    0x503040c030803190c081501140f0d060815092802030d1e1b06020f0d09030c111009090515041103070906170c0313050102071b0b0405090103020f 64
    0x10b00ca62807650030a40700b4207030451002c1140319280c0c2e00c81c0b280781c0c000c0364503040111092426140000c861440c1d07060041c1448200155000080000340480b1054006080341d1519402c8503811107004000c1806030300118450352060821030701c448042588618404402070103510b46d40e4283c00c01050083e42d03050741c00c0b400b80902400580d03082c000803900420569514882d000c51150481801900e81c0011061240d0700c0b0000e400e0741c007000d010300c41c80c0d40c010a000d6a03a84c496841145588685203500d641c145c60045da0800301a4440c0940582500442040345211a180304012105482c42c20040214000810400c040019074115580c09641c01c090f68024910760004181559502c2c031502008900002c10002041d41011602c409800c041c9041c150308406581e8040101e1809080301e520510044006440c407011b0010480629602c80002e54544400380307080c0c0365182003d02070200c40350303034108049201c0d072008003600c00702c0b0b4006010f16416441c5030240403004280101c400e802a10301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 948732401 1250 948731151 948731153
    0xc0201140c010c1e0207052e0e01080a020a0c020d0222020403020a080609030d27051c14070201030e030d050f15030a03170907180605121204060503040c03 68
    0x840260101c00d01000c0003050781000c0c440000c1c420144003902903620840480211203056001900805440b025520901c141041c00317010920142e0a101580404107124480701607254410341034450f00e14203882d58211915100d101c4010b03401032682d03080000d0320307a00d01040035261941811401c1c50018150a240042c1c00d00c82d5010107903503800d5000725980010703003003045041400880005008060281c451802d11880d16900d0344a0144000c00043d01c0340e444418101508070005c3c0e211030790007001156490285041d03900c45555490440240d4034511f00e035200350b4010340c1b651002d40c0482c0030203898403460354015002440d00e031100d0346a512041c40131480481240c42540e010704a6115401804d15000c0d04003607020305130a0406010790429490070000a41140105692183c1d580c0103002e141c1d0785030106464174041c3c1d0b2160300354540c48000d098a04005a2244050f81c400b500d0b01245881800540d580c0d40052411000070850100403c000c03151040d00516001486142100829642e17 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 948733651 1250 948732401 948732437
    0x10030e0609030a1404060203030414070b12180606090a0e0111070f020915130504032d020f16090c110f0c1003050907030204020d0906140f0711030a0c0201 68
    0x10445000701d25500020f0341c1151103800082508002a01c5440381e8079141c10604001c3d22404058070091032080150400a9104020301030310001d8040d001020340ca5001c0c210000d45001004e9541c1d90070350301a6070704040c0c1d0b400080344651180001900c4002d03207071200303440c1c800180702e003201d05404c1c2e560f1199440e442c030362800c00403c81785010358a640a086194010042c0e5480d01402c03034120340c258401440f01a443c0c031100700131000100031001445a4039410203845059007881c80140f0850248101d00c0040001c1d0458501e0800d1907007100c00300c19090804980d104c2040c44026140100e081c001c00c01c402c4d450300030200c004454a4542d103c110494000fa242c003e881114855030340214071480510304210084030710034101850280001c0c1002c0c1c01c080d880750502c0c08064000c0380c00089000300780406400c40440d0030341c0441c1c2048251804c0c45541c00c40300054400c0c50188440401042c112031003034510184d072150300030285103064800002501c0d071003050b4904905000c110101c50801b92a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 948734901 1250 948733651 948733663
    0xd06030605091e0f070308250f2001050f0309070b04030302061603180b06150c0a140604050318010c0605040503031602011e050a09140a050c010302031510030e 70
    0x401c10000f006440caa0480342140740e41d01d4800485030741d0090b500440c100f000041c2503000c0300e8114407501d9480d201c1c0d20740340d0002600e81c01c3c404208212001e040c2d0411124450341c1e0071060007908101e605050440c0f9403c1c1c1d086100105600240701409a00200e0103604c0080d0740200f10a41102d10a42c1e560f400c0664940040c5c2c020340142c0c0080c0d042069001407031307143d450020640c1c501002039909202d40d036138000700c002e40003418500168001546a0b1078910800400c010780c0d8110301c1c5c40c0da0010301019601e0488030310440394a034001c04110040303000040c44900036070380000a1800c4c14184a001d0006106640210307040084286090300400c4203881803a0141e80150059607691400c101d0550291130211514005c5a00d00705a480061035806200340c004014028013058640300d922490300030308030450700503140d03802c0100030100311880041c2c2084414420b10a580352410902c005400700e01003140c030700460105125581c003241c6003400080c0b50362880313410300040c0aa4940320f609d00e009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 948736151 1250 948734901 948734911
    0x9110912190b0910050601050f0a03111605120a0e12010209090a06031b06051804020c0706170f04050604021c0b24060705030a08040c090c0203090906040c0c03050d06030605 76
    0x182d05109000d120f590500211590420b5060103112601744500028854460944040240d40001c0f5590307040d00c0c402c0d00000c01002d0b000740350035110f0800c90b90700c00d86015100c40456040c49012581c5010080702004d0b580c0c0081e140e250580c800080c2028044403807000c4240442a541c01c0119002c1561600601c80c05050a0f080020302d0600710320f802d4070024002a0140030001c80b01c0020088503511108a176070a000d0607204030a01074411010134041d00405c00c0300940d03070003201d20200ea00d950100b0001154009400110b00f592218402860910020341c0c000d000c1c0c0c6c100c400003402600b4001c810702c2e15013212035100c0044e1461521a514059015107080e00c0f04400c646040204094441741c8040c2420122441c0d8507080030756a800e83d03644940031601003400000e5000405000200403008004c000b540001e00c240038100c0da0080d103c4d804070325881d1244104401180700c600707142c4280d00c6008010348031911001002c2d10259029080f4200c2d5110058079014080005441402598020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 948737401 1250 948736151 948736163
    0xc04120c0b120a0b01030b09041506031509120c080d2310030c05150403062f09031212070e041e1d0309010c030f14031f0911091219 58
    0x10f05080540d0425212128000c504060610001d0002da940b4024a5070f005640000c203100078001c0007107900b000c0d10050740094415a11401d145000c2c54080c0c008112140c42039552443c98000c0f41c40c00e465021002e88041c120b040148484009410b00c0d6000009802c040114400c98000800204000f803500701d0300d8062083d02000c0400c204061140781802a11049450702c40c2c0d654482c0303420945000d14800030b0325280c6c5074407044c9505c1c4542c00800c00440700b1580708450211114a201d0040c1c0d1240300380314000d1040ca0000b401d0306800b8004c0c1c1d44083c01c014041c000e140c84e0b8900440700050b40624255010f07994010800d04028012a100c615815040000c10500303248160045010034514134140b29400410130240681c0e489043c0c1e00f90303c1d40c5030505c2d11140c5211041110314a441e08040c044207580001840b10034201003810001c4c00c0000300c1c400d003040c0e0704c50741004240e8080c0304180300400c00511502a05151680d881001240e044c8210303001d0391007a0820108000e4800030071385070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 948738651 1250 948737401 948737437
    0x31632090703090209060105091e06070605100305150c030109020a091503091109041a1b0409052a1605150f24010503060603040816140106060201050c04120c0b 70
    0x441c00c5c60400f0640c040c50909100d810000206c001c106048407a5661810300003280c1d010b203030a070340d81c0300c15240740f01c0e08010b04010f185496800c040c001c00d1140000d880c2440303280c0601c1c050350507a60750f8501c41c042e022401030031a403a1003d110069005035100e44c0500100c4034010544500100407249070030110342d0080360003001c2d4284030b00c0000b4064001801000800c003000301241700702050040d8500e1a2a48200c10303a01c01c5101801b006d15a02e0364002401c00250026100c81e4640115000e1a20b00fa40703440e40524000009201800154601c005940207125a40c02c140c44600080300c0740c0d0254040c0c481500b8100700100d0140741c21515030001c610898140b15056012006003003140307404446880e80700f8006000600503000050407070344544000000941085112400d451441c0484003030560414203514100c800b5805030100c1007107641c0f03004000039040d03105004480c0190305c0301d41c00c10710b824204424048100c2c010321080e150038110640c001031074000640108200c1180e050640c031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 948739901 1250 948738651 948738653
    0xb22090209070f11010b0d08030405030f0301181404052d0f010204090e0f07120f020303070b01060305090142090b03070f06020c0f0f0a0b070203163209070309 70
    0x191680004c0c0464940e80342c07000d40d08054071840b01c5140c0e400c4d0016003182e16070780c96103820b9103144182c00e5044214003003c000040d1484c07038101c041034500f010309400d2102c000c1d03880500c4a640c408440c0a003160784044190044000700320341e071150001c1400190801c5403a90505a4a04032401144603013580d030006080290303100303a10038080d00e80c400318090000b088100141580e1403400d4011b4654190a110f5100304109502c10b1440382a80c1c041c055a84540c000e045c141c10781402403040001090a240c0020007908043c811a0b6110b0940510440e2002c50001d500303501d60300854400c07803a81c0d00c8003000c000d0101c00ca16090024910b400d000314400400000b81800d100e5568041134010707070040b20610960343c02003104480071006444a0201e40c500d04002160549098069500441c15000202d0340c016040003d084990094041b1a41550808103444000880e489000240d00100c450851072401c85811521007111400d96040c58040c2d0100180c0301c400b06407130f4000842c3d03441035240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 948741007 1106 948739901 948739907
    0x301060311070c06050903010b04050115050706270c05041515030605060a0302040e0f01030c150e210609010e0309040b0d0605011d0108010b22090209070f 68
    0xb0403c41d910400070304654415400140694280305600382542014090f0b14120707102c81045003100b0031064022184c0d50040c0c44200d80c840d4540040e9003041082140000e17590b40b1500507001200b0385072800550741442a805a40107500b0304031141c001b0141200c0007030890340c0e550b080340d42c0525440400c4000b41b10310341160380d00038404152103800d81d50550140c000d07295580b1515503941c07150950038030b40711000d100c000c00ca000e811200f80100907aa0031071403108060341c20143d40c25811100010320140b000c200240f9400301c0342d201072100c2c0504011313240c1c104a01030003c02126582010071a26889065982d500075510750510145640340e680c083c2924a411102c104000d507103a9142401d1180c400d4062440440c2d82400400d604606106d12804000c0061110311981e001100b90b10071001d0790500c3c2c248240d51041c4072009601d038151568031991031507449405855a030f08000e = true := by decide +kernel

theorem cover : BRFrame.Cov 948561151 948741007 := by
  have h0 := BRFrame.cov_init 948561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 948561151 ≤ n) (h2 : n < 948741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
