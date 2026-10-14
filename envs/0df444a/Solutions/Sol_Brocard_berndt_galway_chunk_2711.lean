-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2711
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:31:09.941616+00:00
-- url     : https://prove2.me/submissions/8328c9af-a6f4-4082-bf2b-e39e5a04808e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 487410071 ≤ n < 487589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 487411321 1250 487410071 487410107
    0xb150f1b0703230d030501050f0f151c0f05072c060c16060207080d2a050604030e0d0803060f130e0f0f03041d04140a0f050c0f150a 58
    0x40345100c1420f05001110b648503885000301d501d112071040c041d0140da0b05864004000c40c2010344481c081c8010f03200c070400840d07072140540e005003001003c003100409804400c12039188814101071425420340e0800c0c086003000d58641000c0010255010b060f46400d466591207d2000303c0c1c44012540c4182d0464402c00d5000c0c10009011140500010b400302d1042c0006940811541d601c0005070b89038142441018025080081c40c0103445108250030400d2036a256440c840c0341d81450300351040c54100d03490032503103a40110140720a154111550100b403403c105d500b40621a0703203640d1282103000c0503103040d0241e40c00ca0800c900580d00c00601d5903c0039000360003001061168060786650303002c9001d14242c0c2c0c3c0180c40410002c02000300440e801e960031840f480a025102c10500c01c3c07600310003481601c40315071248840d804490144080030070140543c1450282c80c0e59828814100a04220b04511541c00c40070f6030300d9244c13100846401200c044042e510f8650010001c00c0e940170358400d142c42c1031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 487412571 1250 487411321 487411343
    0x901080138120a0b130e10050a021c0504240b031b2407080309030c0d0201060906090b0a05010e04090b01090c09051002060c1806030405010b150f1b0703 67
    0x20794401d1000b40410702c0003040000420340700c01c00d2580c2180d0f01c0e203481c81c0c0c000d0010000f66903507031100d8024800d001185000c0303da5511540c000c51003180c80a82c0c40e0304001d500040c8814110070441d40c480b07044082054104400c1c1400e42d04c44e01c08200401c00355400c105001c0c0303204548425680a110f00030409415610700d641d0345518001e01201903150036105030103001c1e181d040d001d000d408100250706103083c81460040f40d9155070400b900300410807502803000300038850220701c003070150341120071440d00085940b9092800000070b544a139080244003514041c0101aa0765600c0880400c0714820f08103180c0400c4c03068041405801c41c01e40c084c3c041d0b014500000380303458542c6d2080c0000c2e40a82d41e00c082140d10b50080104100c0300e590003400691101d00841c1003180002c0c0100304110341c0c02c0e81312907008807020108440e41c02c21a0251200c0c0d65441c075200080c20003100600b0001240c41003a4606840a11003140174098401c1d0350501103030340d0004414100007000f440e800b868020f803105038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 487413821 1250 487412571 487412669
    0x30204080d0c02040f0e061801090c18050604050402030a120e041109030c030c010c110310050901020901020705031612020a0503120c0c0303033c0c1e09010801 70
    0x202c1203140504038000c1c2e01c1c01e40d04215a0503140b013103480c10035540010742101d0300e40440b904815605030030448a195691024900098588202d51009210041080907450424291017013244e03401403005008600f030904110040c0c0e0080b840841d1a0fa000501002c62a5826804c9030350007508441250803d02d00071105298441c1c450250840f240700302c048070498000138003032585800701018a1703804500b80160354000180a0314540340c0342100502219030000d1a180342030203550056604458a950010b00e0704415641480a24040c28054000341032000c1c00d16120b500401c0c152240020001c01c0041c0d040c00c42d074034910020010000241200c90304481a65031a06c541c0c0481220034641c414074103000014180841035a00c60b8400c5070b5800c2c80d400034804400704540744880502e6018980780108610f0080d4081118003038030940303502d6a102c542503020b191105c4800b40c10100c4110b0244050882c5a81c001981810740c2c139641c801c1e02d0242110080030704000940e5101308100b040e51900c1030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 487415071 1250 487413821 487413827
    0xc090907030b04051f09090c290a090801050907080d030b120106081c18180b090f091207120e01020712051f021603110f16080d090b0d0903030204080d 66
    0x1783c02d0490244800d4805640b07401c0b21088070016100100800a8410708005030702030782c5100400f4000300c08194103401d910301002401548006401008608100344c05d00c9990000d120313071039100d10f000b0014005103007481141031f45c6404030391b0031504043d00d0341051045a284c00b24201d210b0002d120090000c103481d0050f0580390722141400080c0c80c010b800c0078842c0240b040100c40b030039030b013541040400c06040030703008403035205144183e00e41d0715140d00ca0001d65072034201000d07200c0c1c2860b0f101141c15050000070b41d800c0c0036510316404111503042c0010f4000c00c0c900405080359406508016010410000050741000b039181e000701c41c44585103011009000c408500140503004c50b00e4044407091854944104a00440044c00c1c1c0601d1001491800a40a4207110161b41000307000c5602e1f1a280c49101860100d10301c803210323912040d10341d0800101d8010000241c4040341c03410301180311070034801d1070b40c1e00e40158460f88a0550300c401d0080103150180d030445000c0d04c40001aa0302c00c0c80200006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 487416321 1250 487415071 487415101
    0xc0c17030f100b0403030509060f160302120c060604150e070509090a060b070b0a020d2d0207023304090506030d090803040e1b0301060c0b0f0c090907030b0405 70
    0x400000c081900060340d1a5070030038500b09844107030700030a0406003583c80c11038150704581e204903003081c0d0070000c3d4000825000b02820044280c00b800810304081450000d0400703982e4102901040014054414009004914030703510050036107002914191040145125a400c0d600c4014004021020b0022aa9109008040301d82c0240e032007094586a18845400b15091403090aa848000740a0300b000950090051504050702c05c00142c00c0c81080e600040840311340c8201c1000c0e10042c4d80000c020760300c40c41c0340c103400418400d9045007450081c0d004910030f1855404101c03080c0034060034034041c0382c82c00c41c604050140070042e841d4456031034a41c1c05004020aa420b10300c40d1142c04000380d06071b84101d0f01c1d03000755040c540246090502e403002d4074074009805811300e07460b201c0302074003400343c80c1c18000694000c02840e46d500031000214202014411005000182c408012500b004a100700c402d00f2110100c501360740300c40303480c0d64081086000740070590b4495440f03030801007030040300c446034140303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 487417571 1250 487416321 487416331
    0x7060c11010501140a0303030b01031b09030203010b0612041e0c12020f0a030c051002010b03010e030301030c080d0c03050a051e0433051b10090605090d080a0c0c1703 73
    0x801483e40c03615036030314813002c4c92402107621903032155003400000c0c400e82245419440c10304022400703201c0141008581c0d85180e505000040e1a0704041055240034020303a0071305142031314070904e80404030b8090103500c88010005081400000380145510500d07445c0041d0440d0400762148145842c0c882d000440480500168800c1842550400d0315180c10743c4240c0440f03601940b940c041520345001d1107026644c00103800c040d95a40c0f811814980c400380100134101a010f005580d407581980380814884409030007820496102205946803107400401b01210300e601400d00d40e44038140658115200e125400e0424031120003a07444201802084001d0000d4441181c4050031100e48084061128000302c0300468140c0d83c0c0e200d941141c01e0046009240301d556800408401e1942c40c070030180b51501100742c2c05207940d640c003891018054241b00710354221002c400982011140910b00412055000d4080d000f110b9680301e00516440c05280142402684044d507594200d81c1f000f490103841d041151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 487418821 1250 487417571 487417573
    0x10050c030402040b01031503020f1c1110050a021009150c020601030b150f060703170f0430030e07210b0601110d030e0709021b0d080126010207060c11 66
    0x11311500903600a0040c03c8025410f880c01001407403443d02007040904000c054242c12040e1240402e094080a03500000780302d00400c41c0d00101c85141040c070070305440b40c071500307000c0107801d12001822940c04a40406074600071040800c942c174141c2000c2405280190401c12110301e0306820b44003450700803450504a0740213040040c4241d6a0102c40c910802c00840388660150f102491845107217410360160030860301034a04650342d03401c55103503291102400d480048008110030100010031103070003c00d034081016044110754110002512480c10442e100182c02410346800b041c09040030100b040000a003c1d0400f10300303c3e810314049404c0c01010a0a06440c5603d14a000600550040c07512903542403002008104034458000c04130b00400150200c0b01c20360003a0301e80040c1d4584240003429590780c40b0f0011581c144580d0754038901d04640302109005104400780100308401c0054124180645809098010140305090290091040d00002000d05140c04242c45090341c0c404075500e54207003010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 487420071 1250 487418821 487418831
    0x50d090506040f0e090c041805061b09091e0a0614030703020d0209090304030f03052119150806070c050709140a020919090f1811010804030210050c03040204 69
    0x1414494030344128010300e00883c0f0340100401ca030004010006902c80a60300c19291114040c200050548106070204000204094010014403000780022504403078040303c4d22a801082200a4801d40284102c0c0351207120301e0800a2000030400c00d0908440d184001c0000d1980b50504080004001d00c1c080c0103200b05107015000010704001490009a0fa001455400c62001a03030800015800042544a07140804d100005c00a8154070859003010722075200d0545031007910b40300d841c0c440c1c01e62100e003801d18641d106000c1d012000c0c1a4a021002110a01041f04115000501e201021035404101a4800d050030403260300c0e40560180c42c52840781d42501d60031641e40780c41da030540316a0b103100144041c0303140120307164007119801440400301c050010380b070326800c0b03451880e45850b1651180e444e1580703c4690104c117a19a20402c2c0c10356074039809228000e10241c41d182d0070503c003001481d06200a00005c00d0515000b04111142c901506606004600e00b00107800b1840d041a6401c9005900700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 487421321 1250 487420071 487420079
    0xd330204140a03082506060807051f08190e03130801060605030f0f10052106070c030c0206030403200102090102160302130c030b150306030c0904020901090c0912050d09 74
    0x18003a640440f508107506900302050144141056249044807070201707000d0080110010f003460044900400b0100c024000c014a000180414144c8039107103206800d40100102c0c1400f030b00441a03d400103d09440d01c1d81000070860342c44010607441408501e00e10001c00c0c0e0400090308481000c00381c2d88440000d200040d0354001c1510140000e03140440c070303901c10900095810031803001490f48440300d03c8011200c580e49070007045491a56400c00d0704021104803e0055802d400c00406e41c12690610f041485038486480080ca09000001c00902c103142c0040450141880381012881080404031900080906110224001e5110400c0c403400750161011010600c8618207003101105d401800200003e20442643d0008280300d04414091580c4c804480c84182c9030b603207011401001040c106952405e00c1c4040610b40001e88440350700c11030502040100513161000c1c0b05046136506000820100303228041a5210700840c0c10404038402d00406080c180040083c0307003560000c2035100d6130340301c50329 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 487422571 1250 487421321 487421329
    0x291b0c12010e07060e0301060504050703020a0e1014072907110105152e0905030601140612040c03080f04031101020109020f130603140f060c03060d33020414 69
    0x941c0c00c2d10a2140c00c811010040140220000742e8145e6005000088180d1141c0000b003c4400c1510303401c00281d03002c901440d103d03411800c003102c451411241d00801c0d034442c00c4020b2884c4034a54200090003c00b0410f0340420200b000e423690725a191040b210b0b03010b466003000e501c601d00304640d03080018581e015210120304042c403e9034000c01910204241c601d901c1810300191801d118499680c000354400d155580380007013035500f00c000c1030390f80d18440000d1514040516000040c0c00040000d07220700301060080e5a01000c582c141001103980011950b601c0c14441700e403584a80c409001c0c0c2000048010803201c11600510541e0702c01c5800303498510800d4012400c0b03a02e5444001d400c400100c002543c1da123082000809003810b050808542070b5203d68411078084581103a2504035030080155012504080c490250b0185410305800c0c01d5281040010300000072080c3e000d0807043c00d00015000a82c101d00c0e00c100551850b905c0702e0714080401c03404400071340c41446403034014035040540070303d240f82c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 487423821 1250 487422571 487422581
    0xf0a171207110904050319050406030b19170304080a030302070b15090613150b0408010506010f0503060420070f0308011d010b0d090f0b10090501291b0c1201 69
    0xb82107200c1001d00545402442611000a00181d40511050094407802008201c414091003142d5136280e40b16071800c40045c3c10f451040c2c49107407103804d20421680582c0f45030600c850450724000d1f07804c2001c4004000301402e52107213802141c02400303540035490034150150002c0880c40e02c00c200346900c0f0f54600d0708403082001161240e1341e215140d0310100d442c62800442c03181c10410519800128402000524480c03200d0715409241e903071038046002c000c448000c0c400c8039401002820588449416080300900c13501c002404a4406c5942e0103d5101c10b0000c1c54103030310000b8941100e00e0780c2d42c40504114034084402d000c00c40c000740e0079800105980c10360040c5145444c214058164031a400c0c01181a23503a041102600364183d82ca822070b001242c911305500746c4250281d000743c1c03064141402c1405198085401c100001402c2800420001061001c032028090383c0210400000100c004217a840303100b10162204441e01c465019950010049070b0360131990740c100c980e0b02103e41b08001113401c0e10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 487425071 1250 487423821 487423823
    0x122d13090b0139030e1201050907030f03030f090311060903090102030d020c0111130312020307080a120921030f0507230c1002121806070e0f0a171207 66
    0x2400c00000702e0703451009060040440181103518500030150b03140248055141e510b01a00003034084501c5038960701b0000140038a22007000024082c03450b001754582c0c0d8038004e91000074114101450b55000707051007580308005007024030405200141c0a03040080400b030074004440c1d01b034040c2201040001c140042213500810040e00131b54244940380c1071400094020700e45402ea02e5413209070040e02500800002d203200e1142d0710010f4a8a421401d040326005181c0303840f030007503604c02c000c0e0304085640ea078141ca04c164076601d8426080301916107400c0180c10040c00080400e9840762520200c3e00310404402c1c0050080c1e60700b00300514555064070b0550380103031103010101c1d01c00b52069075210703c00c0c08015151030050340480c1c0341c0780501c20b00b2454450401580d440c0103501080102640200850554002e447c01603000141c2c07030725043c0b040c6c4904012f081c4070280600240c104880713856491605102c81e00013880e008802e40e07620340a48290101030071540090041c14150984d40c00d000d010350b5501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 487426321 1250 487425071 487425077
    0xc080a140405250e0c031008060f0103200907021b0603040f0206090607170301031421030702010908070b01050108010b04030b040605151e010f090602122d13090b01 72
    0x101603003000542080c00006000e4026483c060007280440c0d03c031018030701800b041d4600035540e01d4414010f012585040e0010700e0303540c1000081c000c0c0728440b1140706042d80d8110b064031400c0104824501000603840190b55006400b10041004850300801e071640e040441c0e1041580c0c3c011082c042000e64881210028543d000840c0070101604000e4090869800040d0050b450f01089848030030a049080403903102e0f282c0004014010401d00c90003400c00362145000501c80400340218078114110714442c4103005850110000340c21620035000406c1050300400b40c181c0d1103800d4140740741c81507800d0194030f0100e080c1000029503504c00008035004c0341d0300013404054648541d51003001400000e0450155092004a01c150329541c8240c400b840b226000c12000e00b8490100c009410798500c402c0c400e080c05003402c020001a50045030030300f00c403110b42380c6082c1d58980410306403005034811003500011120070700580c0002640e01d0014505c1c488070300e00c040c15041c0c2d5004041c043d1802c0218085c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 487427571 1250 487426321 487426333
    0x9150e030618031c020702030c04180b06040b060a0207030b0709030f0b07020a06180203011b0e09090a0b010612150b04090209010c08133008030c04090c080a140405 72
    0x91003202c1c00c0b001000d07a034098914150360020144510280021801c682d40da0020302d12046141c10860800e104c44d0a07107040c440e40720f110f20603880201010710003600c2045980002040c5a460394041a1900303001009151600d1803090000e44d01e290900044a4800074203000c116818001c841000c1104c0d44011000039000e019681ca070341445029082109512540c801c00001800b140502c0199102c2c0342111184503400c1d00415007594141909014460140e0042c4028180d00a14060441a0039240d00c0025102c10300100e01e040303206030780904015031600c00814031551110811100a24128082c001c540c00100b83e080c1810301032040040d607000c1000100700780fa03a03540180020041c1410107070302000b49600c80320b00c0359000c440104002946c44000307111406045041301c1e0303040b030400680780c00744160b10241ea06880c031011001d4060f080100000d00d00c0d224210440d0082c040c036920511003407900400141203842d0584e004980d01e0308180411070020b507200d03501e80c801c0e60000000c1503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 487428821 1250 487427571 487427581
    0x30f0a02060a030b040501060323040b0a0e0304080f0601060906050f1213170a0f14070305030414030a0306030c0b0a08070809010e01090804090b0a180b0f03010c09150e0306 76
    0x40541c03041080d8014140c42d070000c0c0e11360385c0c5c0b80d00c5014000c0655840200d20001001400300c210b8904400c0c80324031040500a06c008104000d030400d0748101c2c001c5c00083c43c040a02c00d52451400f90360300812992250f152202066400071651a04954160f1100e00c0e2164641200b17680d180103a00b0810031080080c024039015030140c104040d0803a9003401a04c01d508880c2d165801d0b00e504001c13451541900001d202412603034007504100c07100c0c2c52032404101318840303003812882c01d2269102c054200000480824107000791036a01800c501c0125048980d036504440001d4090f109034403040da8104000100080d192103043d0440f10b41c4040c5542c0c6600c9a916402d00fa980c0d498041d08a146966a030120082543c00900c56030101b240580c419940b6140340c10185816249880c407814058500344800708020505e03800c3d844035025800002084c041500c0c008140c044a022040f00e42c15030910110411039604280d0a0f0162644140c00c080c0014071502d00f518a00712012410340c0561040700096 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 487430071 1250 487428821 487428829
    0x902180106020c01080a320c0414040c0201060b03041109071b020d1e03020102090f100206040b190207080d0b040203102105030c030307030b04050f0402190f080c01030605030f0a02 79
    0x141e8001b140c0c120018100da540e1401c42d101c0503400a6044001d451017012185030070170503500d40e51180e40030004500d0541000050b6503c00c1c44049010700031a291680800494001e40104002d02100c0c00056240c0c5071500704440312903401040c81c0d01590422020441c10b42c8502c012003840450b40c030b030600c900c0907070798284005211a030406a99405668141f48070020304080706c2044a8040c0e0300150305e9148000410410380c078803140d11072003501b88444c0140055000305810784d1094001000e002240e840d54400c5003004107201e449040c0610005909041203c200c020341120300d02c01c40c0400c1a1088103080c401280706c180d07072510007510940c404000c40c0b000e102404041a0840c2e900030704001c060380d40c0d80e16542084900030300503040801001040b5515104022605104403000d11160801082600072200c011b000a03001321050480210641c0e03541114500500300c10b01c588021903a0b90025a8a8450a621080c0040d0810800042c58a00020503c0c3c0c90000301c1c02800320684560300304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 487431321 1250 487430071 487430087
    0x3090609061803061009055509050c0414011401020a1a040b07081005011d030a06061d04050312100e010312030501080f0a03230403060902180106020c01 67
    0x240902103030b1400c21284a45080c49103d000341004601d00c4042420403160a09035103004040300e100e0480401840b000441502038400c03001d01c5040c02c25268240c1c95801c603400d40c2020701492002c0522480a1013241a90788040001400740301524001000d503000c000665100d10000c100c03060f00640144a03000302e5030384001d81284140129140fa0803555940321b4003071074401d0303540c0724900540c040005004d01170407503951200e0540b9007041186030260062810700d90340e004150400c5144511403064003060000b1b50b0b0b258400408070341c0d645a0b14070f040c80c0030f448140500e03d00c401c6120914500b901a401c14940546e910070040d40c240b0f103000d24002008080100000d4445c2110203000400c2800e10030441c2c0a14052260038040032807640010781a0b4406070701c0100d03a03a01910086801e521701180c0785452940c103103001801d0340c0b01400e0f1004c400c0c03600c038074081c0d4001000a0010400280340d01280f0040d100f07032906022039510301d0320300c00003503001d10039200542c0018440c424290320a81c1b032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 487432571 1250 487431321 487431337
    0x1c02070510020f0904050a0f110a0207060c020d21030605030102040e01092a020a05060705030103020915130e0106081e0a0611190305040606080607020d0c210f08090309060906 77
    0x3c10b401c18521134005400d03100c050703481554143d600c11040941625a004202c0340e00300f03c03070700c16190800844009649145d14444d1104002c502c420385070441d038854104104080c2c00c00e0b01c2c4214004000c0d196000d0b40941c82600c004070f40360030750001e103508040c000e0706c044501924403030007541e203080c1c0000c014003024218560a01003899000070708024055094451550642c0240b4071080140b03002483c20390b0140c002c4060000c1400100700503960f0858107507009410340c030750f101d95090400c049903110010164aa0440b82050380020207541c05510403070072140c040c0111141c1042840c04040100064581c00c58140c20842c03450000c00c20343d4101c92100203203040032a241410401c500300d852190308003100700083d100c1c0180001d0010074000c4174050b1040740d000e000706080c044406580c4101f0780000c5d10505c1500041c0c0000d00c0b14042c0c00030302c00c10980303803030b00c40019a4000040660100b41482c601043c1041c02041c0c505000100b0f5980011f00600007034036041a4400b004060781210308 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 487433821 1250 487432571 487432597
    0x191b0602160503070b0916050a211202011e02040627030503040906090516021903180803070302060912030112150c05030105030705090903160c030c0303051c0207051002 74
    0x50300c00025608000a02005002d800042c0007402c1c000503050810b1002540c40154408400043c49540c0c0c0c0d0319003275403c9811444840c0407504100000780001c40d07919201804103140d4106a01e0301035019040301000e629602d0f44d0005034010315031010205d0040b03001391380014003030b1320005000c072004150049d03030150815449000141d50b0707030340c003840c551040c0c115882c225129101080507185900616401000f4021f61046805041c2c02c000d40d596501d4002c11261041c0f0b00c0300109050041c906421b00c01e000030741d070000c0303a82c42e80c003460ba80c0c0c5e0004038120300510618000603080310010901e404007170912010140b450340380a079a04ca5451704e5010585915002400a0301d02c0070f0540b00b41a80e0703c031240c1f00d6035225071601c01054140b6005070b1056000303d100c0c0d03041045070781000c0b0440b4800e180c0f20b42c0b04801c0c456103040c203800c5010150001890500000700200030b143d08400503008840000d80d15281a002d64040b00c03050340982d000003040d550000080b0040703c40706402414505409507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 487435071 1250 487433821 487433857
    0x40201030b1c060b011b17030a0605091311101d12010507020f100207080306040207060204080a05030309011503030804031119111e0105030a0911040908191b0602 71
    0x221035482c107500c0c2180300300c400903a0350b04000c0303407035802c1080305070880c1807100004084806030310b407490040040041d02c048083e00200050710110203600003801350001601c45c840b24982007080c551031000c2814150341e40700c2e007204502c00300d24000d00c0b10b207090b00d0340d039403218041c444001d0b6540d01d817200c441c4900d9101500b60700c2d07e00c0c1024244241445903840364010701c0d946445000f031038180b400c612030a0b141c2c07074010490100403414003812a42c200310140c400503a00c4c4079a00b0420001e0041d504103c406001e200c080c01d06010002001d90701421114008104c0c503156440903074001c117414400103010402000005000ca03004503600488004200c0950f4610203040411f51400b0910b03440c122002c1c101c945054240381003e0f80b184d44c864010400e208202600c03600064460300009104030901d503111900700c0100003510900b00070b189001341091100d8009442c220503507030000c800340000b43c5403018005202900c51301254507040800064400d100ca056107a0300f019500202d01c00381400e40350 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 487436321 1250 487435071 487435099
    0x8100603080d09061404030e0906091e0603070e130b061801050d0f051f3603050d0203100e070c020906120703020a0f0303021b0604060807020c1315120506040201030b 73
    0x501755a0304c5584240d80d080e00c00940202000b5120a01611140c099a03162040003071824a2052036030740304600030003a108a50303a903000246058050b4125007520361541e4107110607140c485031615407107441040311031a90764814040c4441e9900c00d440c01c0484000307500041059007045a0301c140194003511400b01198035070f8440c907140510007401b6070030108030048030a00084080c07103a590412100000c500c411082c1c0600011241002009503502c405c21440c0c5108040c000c10403181480c240b03507029910b9151416030b10317620300303501d00c9014004080040000c408520030071441500d59801407202d0740781e456403000d01181040350701c80540103106185020000d0b80d542d151402c0209002904000c40700d0451030020b0425080c1d00c40c440403010140107452807559001d0a03503055503503900e02500181c0e0b888800700c0c0740522107112550016078541d0609251903980e0081c1504c40544c6803c00125640c588550b090754807200c078003071720070f410050200b00150702c030350010b080c000c00043c40e5944031082 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 487437571 1250 487436321 487436351
    0xa1d0109032d0803090d030b0306040209130c090c110105070206010902130909140c091003060f1805010b010207060f0e1306050310090203120304021f030e010e0708100603080d0906 79
    0x10b2a4000d8543d040003104016010104002000303407107989240920010280c1c1c0d01007561044007400c020322480b10b0000081202d030429585000050300801d164000c103035a80200d1004160b000d4000740061080c162503e200c0070140a902e000d01d6444e0300922240c0e103410303808002034000c054040056004541c00207500c06030f500031109280c1c01244000c2c011a0301d400c03a02c1c50f10324891500c1c0d02540c1c2c40b4007000314208030100d201d8120ba41141001c07400800d562100b5000b0820365520060301958910070200b0304c2815400404030300021780071a07142545880c8183c5404040a120341c3c0059441c505400c1d40b41003942040b070941c15104c030b01144d00c68031807000a0034221047c3d001295150b40341c0200702503107002c0103450f0810524034042c52442c10280c01044040c803c088003540b800d0b8201e014803d0441c40b0b0340c8019800403c503002000010f03020509207480302c1840c41000404d00c1030f001040000800c80c450401103e0340030311800d140104200c07540c0042d0184400544e042d03580c0700152101e04d20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 487438821 1250 487437571 487437653
    0x20a170c0c0304180f05040201051b010204050a1401032906090a0b0a0518010c0f03030203131e14010b060702091308120601200304091805120a1d010903 67
    0x414a88100e400441d00d0035040c120b41074041745444141c102018800542d810104413010414102c10540122001d1000640a0b01c620390002d5001100c0d00c00028070540f0b0940c114105140036a824480d140c0d40e00d0141c5010701d0840c2070394800100403110701415251010040809850282c20205503a44c0c0300405681e0f038200a1418000c01c13070000b10340319804d8061460031000d4009081201e08500e031510b60a1551807000d000806241d8008085004442a916101c10f15640003243d014005600d00303c441000025003011140e20030401d10804200c04180105001140701034281410401ea41c0c003000f0f03c448002c0d0800b64503010540010005c50380d40f00050110100140c0071440c5420103d0005160141402c0c4e01240801c50241d101891a00441120115040a00046480c071407820b2944540202c00350010078603ca90401d1005e5085540040e1107512403503116100030a0f90000d001110b890078595240c004fc02d00032080c0700289458140aa0481c1c4015003141c1e890704a0b400d10060380 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 487440071 1250 487438821 487438829
    0x30c0801020a09060207080303011211032a1e0904080d051f050d0b0109020f0c03031303030c080c0706050a0e010c09030b13020d080903032a0d03020a170c0c0304 71
    0x40d40001e04030b241c841c1c124600f480140302602c01041c50368601011036840b80030602440300f81c11382d0b000b042c80500548070110405444d004090790b081007012007000a6804c1402d140551581c000c0104052518111813001c03148001c40101c818840b016034200246030900a00441e44e028052000c02d100e5600b0b403068500c034000c0c402c4507800f011070711607065032000110351082d0b105108501c14000051011b00a050440381584009038840755032800d41e103170302c0c001c58035580810f20010080010480c200d0310040341d554000d460400c00325000310402c403178a41046641c0000e10004001c6400001c1c0d4692116a000480180002d03044051040d1182951006002c2e90b0000b80860b800b4414480c1c0442440d1300002013104903440b070b552540c040782a04d44080e01c094118200802c01032807644040c0111110080141ca0310801c00450030328100c40d0120000725061103101d072044052007540a48210303420f56004d600e64000c12000455000d0300a80020000c02c2032a03014403e880c200e03002080a04060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 487441321 1250 487440071 487440073
    0xc030305040e0a02030118110d1a1201090201020337030c0809010b1003110d02031e130b16090b0408030d0e070308030601080a0612060203040212061012020a030c08 72
    0x70380d1800404961092014112035016841080100008560b44101201501810744040341002c8031502c140301e00c1c02000c1d83c4202c410300340b20603000070b204554040c1200c1c0b03104540e2810401c00150005080310b4610400038007582c000c2000805943c22248482c3e001c40320101c0040061400764001820500c80711040404a621144480801c1da0021181c5500942c0e1400811a10315048000b5049620b4291500c013410b50b6070710301d209460308100c21a19125960501035549041608004489002080228900c4000304022506107405020450041904407a1401e03440e12140c4818501070203000c0c00740140413a00c440000c0c1c001c10310780548005c4c01d10344040c43d1501c0c41c08840c00c080e641c51140c1d1041700c5e000003105000141c008410350360040c0080c40d021200f075642046a4004110340d4110103100100842c030fa004200c0f06030000d41c440d03442a41d1200c00d00542d10800b507501d450554110b04201c0018109002c00b9600d03203688402640000c1042c0d0f901d07507803620b0720320f180d041a400021a07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 487442571 1250 487441321 487441327
    0xb04030f0311010b0a150203120709150c02010504270c0906020c09090d200a0507300305160c15080f040c05060d020d020a02060106080a06061e0c0c030305 68
    0x1030503041054200091800c00091051801510002d90350074268002c0359a4002a186c0c810b102c54820020743d0700b03003a0444c0d90840c0500f0110310160072042c07a4460200300080000c50b0f04500c0d441420158403240e8103841305402c1070b003000110907141704000040101c1c0c50102070900e80b840d00c81e010f03080301c50031300f61200c440c280c0c00d040e0700030704182e85100e516000c0c041c00e40500440100004510140902c540b0300114003e048550000350901c00b1782400500b842100000410f00c50040b0f034110884144482d40c20350741b1245a44907074001006c2c0c450403d5100f05818a101003409000103049134200840ca0f2500901c85580c1c400c1005002e40000d403c03900441060354105400510164200d01c2c00040503403503113400e03550a102c2510500506004030030101e4582800306164064a0720348014440035501c60005d100700950741d8609101c8c110006200d44045412800c0921070171082e81d203559586c0c4074500752102d0b0f60448a90200039001040a08404e05000c6030210311640c020b94466611650303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 487443821 1250 487442571 487442573
    0x270b130e011107020112090323033709110604030f06060605070506180a150b0108071d220509030703020c0306010609050d020d05010c0c020414040f1b0b04030f 70
    0x708450390108240c800010822107500580c0e0000b0303500140008900d40460401d20700c3c5401c441001684480032658010848010099020300000d54400c8100300e103820b03d0000e4185c0b181c40710012255440d42004188401c0b000c200c40950000c43c1090700035412400761000180100c1d1042e40181e000392902da40748138200042000a020b0b1074000c1440d45002810400e640d1500e03502c0e03142c05440c130824107280c0000540000003d0113104c0d440c60b0041301000d030b92009142200042c040c085412800520310000184e081401100c800160004c200401900403004000b40103001064011010725141c04000044240c40f03507000d014820800034001c0c584507061480d003c1d10308210000128400d400650040c04001c0e0711a0100040340c1044644291035556400400c0c0c1c0c14841c03420203042c5500f4110703990040c03030f00031072620f24442c0300341c0b0704100081c510b4040f445c132501c095070700030000e03104403100e1004561506902036001304050b40380700155a541c1c00f01c814560140c0c1c021030304a00109030b0b540c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 487445071 1250 487443821 487443823
    0x807030309050c0a06020304030c09060f1e05090c041d0f1b07140304061d1305070309060f0e0c01021f1e060602150c0a09030206161406100b04270b130e 67
    0x40000e040d00bc0c4d00b8400c00d4100301c0621800e08035806048050449981d446600400507103482000b0400642403599034141210281c06c41d62103406074012441c170000450900c403d04014952240002400b00444c40e15400c03030300d0160205022140034514014030291020405250030300750205802c20085581d54070f841e07400340908280c1c04420101c0e0041004940881d00ca40011014400041c400011180d03590b503003e030003c1c000c03804051b11080c0f4008500c4043c03500c0340d1000201c118450105c60301144600e004903520900019400c080003c1961200c3c1d15001c1c9402c5601a101400181005035180207810800c440302e6501001c0168400350f400341810754003440c0b1365008504c00109600d0a0850000546070080e40e100080c0a41e4000504000c00f00d05c4030114082c090b8440e203000d10645070039a20a030b4440c8250fa081898040740c0a000480030001000c441c229820b28145050115140050482488003007080c0c105c00c9403100942da03031a58621403d6080c144502d1800038403591041121 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 487446321 1250 487445071 487445093
    0x8100507090b04030503040608060a03060e07080106090b06221503050a06230f04150b0702030d05030702071406040b0a031a01020d020a020405040512031e0f040807030309050c0a0602030403 83
    0x42c0340c41c44400c10050010813808000c0300d0607103480b82420117440d10345801041507201d0300d90000c0c0080b407508800550001002c50082c0803115014004d00043e519095030208480e90b820a4640c0000100801c840d402c0305c0001180b0095221248a11060754507504552001d013a002082d002075a102c00b04042d0075401d2242c6005800400c0318912808211803d2419140d030b40e100b080d100c0d407503040c041a030a80d2143c018102d40898042d0107074996a4030885200a84c0080307a00328442c0c016480070040301807013081a64483d030360550051500ba45406d1041101c0c1d0000795101303822450812001c121500c042c0010814000d1954000400a40b4416030440324216040d0a5046404c0720100346400e60740040c05110158040b9000116902c0e2483c14500e400c01c0d4450903d0038210200c10441940511040c1c2840344d400500780800c00e54486803610404081250000d000440034020940441c5c420317030000081500c1207044a02444150b00001e00b0100142c2c890300044e400000c0502c1000011408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 487447571 1250 487446321 487446329
    0x5061605030105060a39170304050a0b0c09030105150f0301050403140a051608090108090105042f0d051e0303061e0102070b03010e0103330b04060810050709 69
    0x10035421035042c84009102803081c505090200050911484203050300e07100515400700440304005050f240150030100c02c1c3c0390601e0203649004500c852212008182d5013102d11071070b07000000c0e02991619996020102602400c40d1035000414030840c03015803401d108e22030203003541c0703020403401240f4641081038500b5a058141c0c002d9040805200c002600200c40c0905010b45022564484040d420215101d0050400342a0003000318000042030020f844010b0140180c00e9807002180c0d41e50100207402c1e140c0070340f0010000f0000d2620b81042980c07400424010308035420320310590101d60344c0095020010201c1c00d0305c00b50007442601446042420320300a85139001c0c0c025508614000e80001c8032104a0610213008030f0600b080d04140341e10034080701c8082c001910406031256101d000845074910300b400121842580380603c1c0200c01583c0c4407a000c0e600c0c500c1d040d81c017455100401200581081b1201640264030703001c000c9100c00d41800b800e03000002c00e80c2c0008035442c1c0010700401c1d001407544 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 487448821 1250 487447571 487447577
    0x2090a0b0109091e06170d140a081806041101110703170f120106080402040605041109040f02040f03051f2f0f031e011509091d0a050616 60
    0x1058080a9070480498800c46007035200020728118881e1680c074aa8071004c044405551410384045111410030b4510481000603104a0f0311040e00c10205540a886000071441c0c03002040c08100081c5203d080c4140d407100075001c1c501203060310803a070603140c080165000c80b0304118081c4c0030012960b1200445c4002c03003121004050080c519202c2461111414548554001002480300d840c220200c0031513100c51040c4d0f03c809001e40c0c0d2180000d1480e5030030b980880c41113040000004051900f0b00a030040722000c1c0017450b10300000ca504000c0103001410100d08455003d020002d9004400c4040760025801800a0101080319080e4988e00440f81002e00303c045c0e20307160b500c0c168052a590582e600880592418103803c030f8070401031119014a55001442040010400c040c600240d407210381100c0b800000f90810340d0f202c800c5042864208010034001501107001045030020503000768000ca200e0001c000300700c0108801890a0000d6100140e489074080d00a0005180c5848048a04405685 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 487450071 1250 487448821 487448831
    0xc0804120305100909061407110606150421061a190b0f22060f02100b010807030902060f04030606150e01020a12110604060c030b03030412081c020f0702090a 69
    0xca400300d04040c54021501107aaa42170980100b003801c0c1e0160ba025a4130034056025031400d8400144207009082070310388140600e4021401a040c0f8800c1c4070400c44192036640e0809041c0f00358004a0100c400c44820740040c0d01113a00c020800602c03540d50012003561003252400803100503c06130011220000e4642031a550b41001440301c01001c0d941000084184280c2d500c1540349140054405e51340d0307100b00d4000100000030069004103002030709050317036001d840f082440c4035800350071620101e1100740840c00e007400044200340702e40d014000769880200903e0a143c4034410b02036142d00940c104981c4a9584c2000340414400041000e50030805480c2401c030304034207180000d4803070007100c070b0081c21070064007185109070340a92103031600d0304a8181240c140b89814101000030b407080300c03042c501003850112031030140e04000c4101c4069510b483c240015544076a41d945a02d60711a142d030b81c45203256001c60b031404071600e000034031030800b116034525102c20150042090481001c0e048000c0c0701d07d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 487451321 1250 487450071 487450081
    0x51c06081605030a03180e0106021e1b0609010903230114070203070809060403050109060f0b04111902010227012a0f05010b121606050a0503160306090c0804120305 72
    0x4c0c2c00b900155042c90001e40460055800084442180d041040032000c0180040b90700c507800500d00301040d01c0300111a00c0c00106550170350720344517000182e10041d200f18101c0627090070700780018a04c411042c90f0004030159280c50356002800c13442944025090004142001c20009004980087c0c2c018403000d8503038100207030086c0d40c900c50ba4800070404900410146486c1d9184800e440080d90008000e000e20700c0c852504900030007941d0040c1d40c42c00c3c9842690403850805c2d10902e00381c2c801d0740309118640380c1d071f010308900f01c0407000e00c01c00300b15034081009803c1036a600a104491000105c0c1d0b009410810400241c50124075225284001c500080100e411011647e10b003042160001840341100b9144c0c107109001d0180b40c2d44068000d4100411030200762800182403071548440f10310900300030740782d80d8125030510074130300d0f01000076905102060900c80302094400c4950b525050008060b030341c480f080e406482502c0000400b045040c0308100c1400034007070201d0310b481564038041000380f800c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 487452571 1250 487451321 487451323
    0x6160507060908060a09031202071a0c13050108090f1c02010608010c0906030902030f06181908073903050d0201090507061112030108071805071707051c0608160503 72
    0x1022445d410380c4820b0701d5001c1c10b003e8040304c171030038a0f03080056544d00e456062500110344603041c4212041120b030001014540010300b503404100011a610380d050b450b28004403405103018005000c01c1c00384101480341400c0c1041b0391140703c2d02280140300d00410040020b401c4907080e80c000d00b42a410a803c0b130100544c001c3c80c550903245503050015443e901c90002c2403401003404002560342c4a29414840c4410050904412048004044507140b06c8001c0301711381b00260281c80200311340820302c007800006d084160026001c084408002c20394590100035100201c00742003e065035500315544c10710910409114580c001709a900080c0700e241d8550f99034690700c141d03d1154404001c40014003440a1000740b15441c41e280500348030948a50315281e403191034a50512a8400010180502c0d03041c464043c02254801c013015100c0103030020b01100c00751a0700000501c1081040700c1003024013800180e4104108503000304034800a40c450501640510788002c0c40703105079240420050400050b60 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 487453821 1250 487452571 487452583
    0x5030601051003090b0106050d0f110706271203050f09070e0901020f0409020d0b092e1d0a0b220b01090b04060f02060c09060a08041106160507060908 66
    0x441940e005071000e102e4007080340240034401c4002c100125a1000003078050303012000d0700851807440d90802a091030207540b6400c4540e1066001c0a078042808900081412644001d070400b40610380261110000c071001c099070140b0450858040140780540d468059040c49143d42c4000301c019042100d040514040d5650402031241e046141100f000054001c002901034602c4d50300f580d0400c07501e6a894080810103908007101003666149055240780031403a1003181c0a01600c0003492207400d66400501c640000001803205906016150000048010f403224440d8074074982c0002e511401c2c144882040259030444103418426900c0403c002c2806080e203c0000c01c0440419000504513030640040c1c40d92001c9a001d4400d0001c04200018040c1e0450303d1100ca10105900307403012a03030760300c44c0c9281d907005940c074080d0842002c1c000134505074000e1518641140c00703240300ba114404506c2c001400c582c0300080c0e1403103a00d04000100108007042001314003900781ca080041d1a181010320060b640d070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 487455071 1250 487453821 487453829
    0x506090322210204150b0903010c0302030c0f090616060e01050901051b09210619050c0412020d0816170703080f1003050304060e031b010806010e120a0b06180105030601 74
    0x101000070380b00215622540700032504080d4040b10035401d992008840d50301d1300300404060080d420a06042c100c544a442140e119100000c801824103c009980c42e401c0d41100e403981d42c1101c0c0810100c51243e04885c80259603a11900c0c0100b0001e2000d02c415086d501d01504042c1d80c0da05101c140200715040b0a41c1521074189e0202154480c01010001201c92600724005a0601d900e54040d88c0d00e030314046600d41c800d00b01c41d038000b06155100c0070b5490403190100d8100c260b0130414001401050650710407074541e54001403a480300c288007a12910440e80c081140d8a00e801c2d03001a4140c04c0280c0380391106003403074444125904000031500d0140840b00000d00e40d110251040c03000031789149502c0c4515000e1070304001125160b984540e4003801d110400c135410344c42849030784110448003c0040a0701d009050603512808181c07140b200640354016640d080d02d500100b03154101401d0442040315000c06401200d00c01c400f41440300034040200b00500c40c221002142100500c101c1d140004c0c028112 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 487456321 1250 487455071 487455119
    0x501141002030a0c0206090d03020d1b0209010b07061b0f090504051b090d050f16120309090e030c0f28110108040f0f0c080c041a0415030506090322 65
    0xc00031174400202144140521150701003540460305003410760000356000940e02503150306480d2030145616400c40c0c020880c0c02540f280a0a0040c031101026201800d809442858007240a510540203103004031440c0c854003000448042034480e041e81e100d07600000501c01680c0c10840350400540780c42a0b0385451000c0182030300002441c01a0380c807814214416581c0000682d000002c0c0c6602c0561100501c117103c450503030302100d02080e41d241c1081c4007910382d54180ca0f0b20107907038a8400094041c040e07585100b02c0e5030200748041c0031030700c409004100da22402c0700050003a2030010181c81445601544901d01c05140242e80b010001c0e081010410b030200e001d00305200310341d50b00d10f410814450440030042400c542c001841d405c0000c00c450440a40b00f800060391a2524074105000407103070241005002401c4440390300b07040303041030ba01041284969a40d0320325002d489440f000c0c03402200340c0c0e0840083c0c4c0001480c40c059480c00500c1e00349840c00c9258a000140b404a51700d013002004404c40303030a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 487457571 1250 487456321 487456337
    0x507120c05070315060504021206040b0f0a09150e01030804060309020609130c11030903071211090403051905090a03031b0b1614030736090501141002030a 68
    0x406805880e80100d01984002207490941d180c1c600300410780c4000a22502079824204c01089034a014000d50381d000c02007a1b551400da50307071281044050722040189a804c442001051180342e00c40d06840c401800c800c1030049101100c10012501d071a2069000c002007000790801400020360a90803101141c00b18580801d5240050000402501c20008003991001c4516045810310358142c0203018448207940b115508041c041162540701d104603074130958503070400c00c030038003a0890100329017000c03d0180d012003500d021544003294000500b914240e0100340003182c40c080c40c1d0b508603020f2000f030819103803290070404480d0100c0c4040143e03020003014451425400320340c404034003d02821241d0401500d6a2900344022a28055602da0f0240400186500242403141c400307a030440303024900544e00c0c0d8031880c08540070642c26014844490601080c1080c2980305052080400381c0500010940082c10354900302c020b4010861000046004184000907010401e070040261111107005040c2025 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 487458821 1250 487457571 487457603
    0x304030807020115030f02030610051f020f01050a0b15120406020c010e070b250f0809120f0d0915090b0a0c05010e07050414040c060f09030b090a1b060507 68
    0x805132241d41111459060107802c000203000c2010520382d03401d8026401d6400daa140e4241c8483d80304094007440780c0014080707051011214031916072030003603d0b16105680c503805200c0c0e0418217403070003511030840d5180c54040c1000145802e04002c00285110340e0300a1600c1a0140c51841c0c4010040c00500301c1a40803c040720044d800b034102c440410f0f45102070b101c540b510f0307040d05102500005a41040349105030501070307554041b00001e11981d0b4010b40915000d1342280d1742c104080c0d2007a6007060304100c19801000d81507000308008044804200068606600e0b2444010244c046980c44107007401c00d514102102d00d60000170071402d0322007080c9540d990b041a5501036401240d1000001c00030f41c80c01007620100300740801e1041c00d0b100115428860146003504010900c40d007a90007600412074200100302d0b03e40a001c1e03020f0500d1860500c00c02050766a02d859080e460122594860f9801c1a0650740c01c10240901145480c0c4010382c031843d07142c0c2031130720013091402102d4005144645405940c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 487460071 1250 487458821 487458823
    0xe01050a09030f0c030c090605130b0325060813020d0609020126010e06030109021516020607050d020c03061537060e03060114190b0406030c090812030403080702 71
    0x400074607005484100e0890a9243c44c504000c2503100c1a21720303010500b008a20032500d40500c00c01c0f210300600f5401741b1200c244034400100003011245038140b003041940d4940031110702ca251a910382e4071500c1c0041c1071030b10300f01806e403440c0100102c401140c0c0c2000c210061b0b9601402501d019004500040d098407e0b10059505031582d041040440c10480841c0a1001a5100490603128031600e07a524640b2100141803d030b841040000b03522003e40289205582008030103402d0340484854401449425900881c0e5590f1000c0c10650310b68001d1084c410f0456010001012860700c284c0c024001c0c0c0ca00703c16544001c54099900038840c0180e0f83d03024a40700752240f183c01c529820200d0358006040454281c40a02c1a41e22900011a250750510001454081442030495a0300d911403010021031000300840300e01c0346a020305032490702031404219840540080c101404003030724005501d11603080b003c0c0400e081030f07001054581c002520303503610b044440b00b03072608181d150521441035112b0384420703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 487461321 1250 487460071 487460087
    0x15032d05010213030302070506041203112103040614060f0402090f03030d1b1d010c02120d030c090b0418021605241807060f050903100e0706020604030e01050a 70
    0x3600542c00401d114a2101c3d545142e032045910036001c485001da03840040c402540614441c1c449201080b00280380400d024160512990340300c03106a9000721a0b000c22107545552010b038140017040c0200c100b0041140910450000ca4110042c1c0d081524005c0c0000341c228480c842514011a0007180c3e00a20f502e8030900b410004d42c0050a590307e6140811100d001000e020030b03917100b030301e99185050210754045c0c030341002020b5100740750a6110140c07000541d1055001f401c01c80c5c0080801080d1030512405114081400299940110701d0840d046002080c00140383c0201c0c60050040101b00070300030901c0c0ba0030410200085016840300444c107600e0240005540c0d0103040c0d030140308400a004007000320320301c448170b20028a084480d22281803269400802d801035032402d500408c2c0510519005008240011800e440c280c2d10f454519004a0704044820340c0c1c10030340e0742d100d20200d041102c050001601410040c8010304851519450040080812a081606001d0b00041c4447e0707462081000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 487462571 1250 487461321 487461323
    0x114091611030f030411040c0c0c050f06070f03350609040309050a030303050103120e010813020307080f061006052b06030f0302030703031d0a1b05030a1515032d 71
    0x156500c070714140c00c000c0704030040380c6c0700207204a20309040c0910041c010a00e42201c2c0c0d030000c15030003243d800d010610000c5c401440a103075001e1000d01000700080d81c1c03500c0f9408164802e59039124206070400030881040c0f90039062403c020003c00d140c502c18102c0a241c40d41c000c50484240003607444d00d040640713041e05203400454101c0d01b100004070174036415810240c101e070f1007149000034085241c0422101c070890f80046900040c502c0002c105a4140b01003003106940c001000e880d5843e80e00c20b4002d15044c2c12800e400207a070010000c0219001103802c2d08801410305081403450500d1440710350f41c111b41f4100c901c840f0035500040d1501c2001c007643c01072002d958084201c010250031400c0c003a66070380100d001200060304200c6030b8417061088200d002403401c1c001004011141e5596100d50f2582c07111012410040480240002c0a80d0100315038803d16002d541780c110101403d00600c0d0903a4800900494101e907442010000901200e40e501170100c2d0040301c4281200a50807004508070300184 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 487463821 1250 487462571 487462597
    0xc071713080a05101503060e010f020315090907060e0d03170c030609060d020916030f110702130b0105030c07020102010b0d0c050f090f0c03040f0b040b011409161103 73
    0x101d0804000103078582400c2c01107080b5100310511a00082c26078400b80e4800601c104030090420025010703820031072000c1d00e544000b15420b5284040c61040380c0044400183c2d0400807000c0700014203100e03480030740002c00c0b21701800c0298140070001d008460300f20b10503806410840000b900b41481901c0b2446d420162b010f007264182027440990000c0d810a0325181e01c900da0300d00c080381851411001d0a07124076400f0b49042d100e50307190725180c00c0f8030040c0c00da481c040c107031a080756601e0048640300791303085d194500312540c0d191303042d42c01032007001300002c1400124076242c444802c2c151780e00302d0152980880074200032136840b0460b10040f4050f0030143c0200c0c0e0092503a44e0703041c0c2007241075070704070301955001d03500d04c4000314242080000a600950704d24065140120124129907001001198040c0c054842a0b820070791035911541c101c00100d0381078852606080051000a107001e013a160742c00401c0320650100e08002c00304410f402c903401c00000c00d0012049003088814003d1090b02c0068039485 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 487465071 1250 487463821 487463857
    0x1206010305031b0a0b01090c0e030715082d0402010504170a12050a0813020d0c0b03151012050a0608120d06050303030c031902040306020c0c03060f0c0717 68
    0xc03074029030702d0b0071a00401c900c8528440907a02a090000380f07440c40c144e00514400d5881c0d01e4440428010481c02d2603000801c84d4104080c039094508001c03c40081c0800d89440c0c0241503402002440b040d00070745419400340b41c1010301d0040c03450b509003481d0102e092083d0108139841d5440140c6040c400c51307101200d4540003c0d140c071f01d580004a82034000c03900800017010300701a034510480d610b1103040c0e80395001c60070349004113028000d14482281a54800b80c0b0140b040592912010b00300310040d800b4082d150030000400545a4011b0007a87c0740d42d0f0140c410940340c050000740038000c450825560b0304800e0390740300010030f5a8150303040030740244804405d6130910a000c8060030303215806500b0150340c1c3c5042040001e024140002180e1060805410725370464991480c108003d0b8121700d100040b064080c8070100c0803d41c09d10003090030140f044010302810f43c00100303040c10000000e04026000c050041000300310000c501c21910400d6019861051918142d0351660a074003607a80c410a4500c44a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 487466321 1250 487465071 487465073
    0x60302030c09120109030f020609070605070c0504020408030d0f0c080c0904090b0c070219081e070e0118050f0103021f1e052104030215092e0c050906030f0612060103 73
    0x40d409a42c1c110f0187d0750b001161600084242d03a0b5150079a4140050740c03150031f040050700c1c450b00240000521880100f07040d966148005416a0400c1d0802c5c3c501c1c0e00001100308103035030503200d0041000000705007802018048580a056401c000705511890040020724081583c0d03107a2107002c4581c0c1c807181107402c60800f908070325407540108000f28000e0100300880609000340708200001c9170800d0004140702a100c44200c544100628812005841001408035811141110141c040c000d4020620000070060000e1402c0d10f0f07000e80b00950102c0040c005001588610216101050342c043c400001580c0d0703004100e4071651480e501c022190100e0129500d09644040104158214030000c840c50150081403210056025038004004d68420b00940100301030035050b071588082c0440c00d50740300d00164164084141c1e004c2d0004004121a85600b443d1008a071090001c1c1507981d1405604220702c0802044282c030010300322072644808107001686036615843c10303450b41542c2c00141d40c00ed59503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 487467571 1250 487466321 487466323
    0x1302030a03090501031d0a08130305030307030504030e0f090705180406170f07060f03050c0d020a0e030610060c080904090210080f01050d080d0509070b120906180601060302030c0912 80
    0x1c0e400f03000d0001c3d08111503040e042040346170b404840c48041003e080034030311950381e0120303982c841d120300c0a0b920514240000400c0050024501c260820340740842c2500c1c1a1030020042600c000050344100c1c944120f480303450b1104240307150f0001c102e041c003d1f41c4440060f030901003410300d241d07038a44c007604000c0086400b04006c40050442000d02c0f0485a0302100c1407420303500c8040600810b0005101c110008400500c250804c0f40c0103445003840c41d140155000d0094182c0c1c1c4030031000d03c0400c0e581c45001005041c200601a4082c1801c0e1903248a00d080490042c5010081d00010b0000038000c11000120f594a40c0000025540103181401c0c101080e00081c1c000c10341101c0b80c4a40d09200302c00000c07142807500c400c103041a44040e00c149030010504501d40200005407490405206150001c12050300305002003841ca03248081d0b132034052620808031458408000c100d00401d104400a00065410001c1d41c0c505480080c1800760b2030b41d0724920802c1c1da274010009426401020407001d00d040d208 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 487468821 1250 487467571 487467587
    0x102011e020d1107020d1101051306020d020706030e0d0c3f03020711060d0605220506030c0109030f0501091505180f03091c02060a09050a0f0513051302030a03 70
    0xd21840d00340452540f40340c0320940c2c0e010718039019402590740f40c030940010b000819403042a030f40505080d401e048140e04a4005040307541c02c0800541e00402e4002030f03250701008540d005083c84c0c0340c00d002c400001d4500c540c4681445403607c043c40355281c174020404c1607640559032084540c104103422003080f504070070300c18907029030020301c425105886500e003e80b2034001c450b00c154222075060302005c4400d080c044c244e48003000d403000140d600c860215069071410458655201113019042203440210403010071940058060f80c8a513115280601c603d0741c105802c0d404076a0090a05040c0d00203d0800c0c50252064500041048a0100d1880e41500c00ca9008030b01400544a080ca21181d604000076036400040d49400b4046c1d0040c0915802c0d49010816010a0402010403e090351001c0e8003152440d0800070380e8801090110b802481141445540b107001003800071542c11145160501061600c217009082c07507a01c0341c0b80c000086d103034800500010701c035070350180c103c0c1c0703100d02507060040ca242 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 487470071 1250 487468821 487468837
    0x90c020a1403040b070f050c030f010c0e04060f121e03050703080a1416020708011a28030b0a0b0310091509020603130f050a030305010f090e0606010e0102011e02 71
    0x80c5481c07040c0103032500006071802c0d0f5041c010000c0c03801c0501e444104180708031020854051140c02d0104100713480a0001c2003404650600100e0200090354000e4250800301c081180128074020080040e014078000120440c0c0c04481011080d0446041c10500c03245000c07070b02c4210441404e590f1013090742c007000611240d0302039603804000e5160305600c03109403408616541c10084620f03010541e0410800d10500c0a60046d004564855507100921800d580f0300040820001c086a070380c200190070f000070a18000c405240720350341006003180c001e100590a80c040540810031b2000040d682d071f50a43d04c00458140000c04903030140c2403401c034080252408401c200d42d000043e030783c07060f90300c00140103e040082d40100001e0442e43d44490340000801010001ea51000740c624207040030640502c40301059502941e4003154640c1040300ea240303440015401107a00920708054446c1b00710700481c0b0290403040c02d1074840144a69807004034054000c0c000848200300083d1141c11142c4034642c01043c0035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 487471321 1250 487470071 487470083
    0x212060f0109050603060415062d08070b0a08040203070f03050d0306151d04060b0f030a0b01050a0c0201030e0c0301061805090c030c01050732060f1506070c090c020a 73
    0x90381c07102100000e0f14015030700d003601980080d020400150608580e103500810000001030010340d5400d404003520060742c2c54142800600c9104015442883c43c450003500f6030400520ba003914080c220081d62066401c0742c801c002094012804541d0240301a5008115112011401d5516400c0842c0c03030f6040402104040b900e051400151000400601400030129849405182001048406098100c4281a9071103030b40c40d0004120940440701030650005a800280d8403460722940d07400071241c1190400341408810b0020707000080e031050401e00030b0303a820300c1c0100e0f0002e090000e051609030381c0d10f10710f1790550a1079400315080e01030805108040580c85801c1c0f0154840c100c002c0c2c1c90300c01200c6515015040300d4a41c0546501401c01011514410400c00c0780c007082100043c01c0007003610310f600001d07104140c400c860302d00c410412541c10a5861301002c0c0b49003854000030100c6030301401098011200424044140b00c6442c0181000382144142070114020700d03d0000d4968100510481311 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 487472571 1250 487471321 487471351
    0x204020f0c0118030e01120b06031312050708041202120616090506030105130c02070306020406050315011b03120e0f070f0e01030b06041a060a080a1a0f0d06020403021206 75
    0xf40f403629664640e02e903a0075880c0e41403203610502c01142e070b4880280c808540c1075142c0a001ca01d5458100056202d412166010f001d00c809500d4403c07142d8030b0000708141040401d100d00d0002c5481e0008039822918a0018200c80baa51803001c1640d849500d210703442e00d8064242002244040c000036251360521980e104804140c48108001d81800207020751500070981081c40307405041c0d6544000d00a0002d4011500c07069a00d40c1d03604140c1c0e002c1d070401d400044001c024091420100178507041c030b0802c00d003000c601b01860b200710300460510840010b0b0801038205041c08000181d5800300705640d003060207079200381d000c8a0b0526910040d0344601d294030002c0400008d1050403032054070741620b5104116940350348800c8108000b401c01c03120000c1c1104101002c00790242c3e1030740d00400c049150390312181d03031600e00041340348101e0700f002c42c4881c031501e45c81c601c180c0c0c0e9559170781050400c804102c82e800c1c1800c045041c444028055a00000d400c01441d040010b2030181c00a140c500c504103541410003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 487473821 1250 487472571 487472591
    0x3041a0109020a050d15030807030c0515040503121f0b120f060102061302220b01020d031b05031f0b04081606090302280902180904020a05060d090204020f0c01 70
    0xc0f440752029120000d60140300746802e40074150031070090f8007074080c06d1602c05a2030b034540b0a521381c048481140800c0f070700c2d0b90000c100202805420702d0143c00b030041c1d070300d1460142c951030786a00c500102401c45034840400170390102c14010140680341000170700840c13040c1d2141c03001e000d1b46d4410001b10800b049100c0c00a0840f2007a500d00b2171113580180d014040d9601d9540c070840c1042e0704d55070201d0340205218143d41000484c5e003000454006500004a401c0070140c0000e41041010540b6600705804d1016071001d108522218818415003807400707942e02c0e6035100294424002c4031441407010010b00000080c809407134809001914140b1040c1c881005200b0b15809070310742d05206420200c4e117407038010800352030a00441a40e07207040c5908109d01e0701c80d0f4162104482d505400c540d03011580455030391450b4000545d0b00002c1322064403441110700340f54001501d440c034280304403840b0300000034442014044030382240202039805002036413208400030710301d5010741203444084041e40c80e04c66905 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 487475071 1250 487473821 487473839
    0xe121b0c04091e0606120303020301090c090e01150e0402071b09061d070219030801170604050709051e040609031d0d140304080703110a1d0c09011403041a01 69
    0x5010b41e074406168503142002c0942980380c50701c807440c1902c040e5903c01000480b20440b944102405109030390050782c1c3c2d8107140e00841240d1410640004200c0004001e001c0305604100060546108104410171900c02c110304503490410820101e400600101b00102000803080140701709203107052015860948401422003200c40c1803140c18014030240444444040e210b440b052340200301481510034000701586a00f01e0303140c2032202180082d0344070b80108aa0381c1d004401100c280c0d55000138041c40c0c24107845c0d8565441d010f001798050a643c81300846d03041c1d5442c2d45603d00305108540c10b000140f0301420081d0007802c8003401a0701055001122011442800000510300c0700010a03108400f500350301e03401c030350f0303454402800d141d03100030440070a07640d608101c00c000540c840e1181d00044c245641c08d10442e00300aa005c0c8055400e0a0501d03460b5421610b180c903803210070209c10303503218008100100c40c00d4605400e642c46012001007444180080d4400d02c61862401150360071050366035502034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 487476321 1250 487475071 487475081
    0x60f011505090118121b0602030a050301030b0601091d0f06150d0f110d09051624020312010b031005010809030706020d090c080d0318020907030e121b0c04 68
    0xc100090740400c80101e030341d03000e1105261030001201401500315103882c4240595180c0f1202520316900c1c2c00700540392a0001101000070303040c140302031410a086250064001d02040c08014010740600700001c0281c1d220b4079100d0010304006040e180d060070a0561100f042c882136482404207001b4200145c039505146140c07400380300404604502c2c2405092048000340419550300e010180c840300c080d680210828080d0900c5d00040714001070300c01051400307510b421400040a5102118108108401824070000c1100d00440d0a03840011068601d0201c0c01c51140c1042c3d203041c0c207550000821610b100d000038521568440103800304440e03e900c015907001d081200c500040e80d204022660004010790080c21002ca03085201140b4010070365200f448410254011207082c0d8051002216a00d6243c0104018044681600d010f50011600421681c00c0c00822080605071544048a502081000480002059a0322658440c14070101389007403502140d4a46903180b240800341220703407601d8822 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 487477571 1250 487476321 487476359
    0x160308090c0303210603160b04080c09010e01060c1b030f0201020c01080c1e070c0b09011808070302040e030d0c020607091a0306011b0606030303060e0f15040506150705060f01 77
    0x8520013404010441c0c492240c00500040d05070003900384450300350b2910308aa10203040714610190310b9500700409103142075003058441d842031800100400840001101150550741a40340a040703090740350501c2c2c820b00e4002c004000c06601c80f554004140b20f52840818181d500c00d900b5500300140802c011100540140c1d51455030400420596010486c40c1c15414042c1c9441c1c403120342441c04e29107840802c84481c2e40910000700d0f001035600710660788000d1000d1120100326200c40b9903070500e48416501c400501000380035640e17a80c442015548100265104498800c400f44491134240100035121503065034401d010a2084102080308036520080100c00382915440740e003180d5a00c401101d11600007a40503103200e0b42d020b41900415028015031020710b000e514042076043ca0184030108071000101800600c40075203080c170200780c0501c0c1c0d8046103250200d8004c14261101000140744100314010344490500c002640e0041043c0032580754407405d171240310550103170ba032506800d05210403103103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 487478821 1250 487477571 487477597
    0x5010302070c1e0306050108011b110705090606090405071706030a170904090b0a061d06031f020408030403050a05010c08060a06080a0b1c1203021c0e03160308090c0303 74
    0xc4188070200b10295018400740c0f10401da85092952a101d9604541080c0c1020341d40340d4551005000f450b1400c01d032000d540c0e0031890107404170501400c081d600c40c0e0716070003a54803030026000030542c29520f5005076004080700600c100070506049001070503009490714545404500c0000103040d41c0b80200308149050307041942c0446281c68002e0a956030391000540d81d038000e503502044c00214215541c120b10400d000070303000604c030342400d101c0d2244020f04480c2c0c002868070402080b070261004504441e0403a1380c043d00c07109a4511451641c0680140c1c0c01c0b1480920003c200002442000078a40707600d24080c9008101750405524111508002100c1864100d03210390410001248500d0341180c1c400c5038080c0c0010a00c1c01e8000003420500300158886281500300080018041c40c803003211880510f50078214a84100114644164610142d0300100c450362000111003c0c08207104440401480b615280c880800034030303001d442a203043d41d4008203403040140c503020606000007221110340100c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 487480071 1250 487478821 487478843
    0x70c2f0a120308040206070f05071a040303052205060a03021b0a02010806120f0106150809070f09090c180e0d08010311040c020a0b010f090e010b060d02070203070308040305060109060501030207 85
    0x1403801d59203201e0180003286c020070200081c00120720201100500c50307100e41c024100140ca0107072301d8528050515a0400366a00030270080000980040482d49100546d1846d81c00c1d0017180c10000281e0785440c0d12a58000000080c000400f035499401002800200303517441d0a80e800303020407943c0c1c4181c43c00c00240495082008281d0a00d8045001060440707030004442a01540305201c509645582d40900f00460800088800f41c0b030b0402c60095125000c01c0003850303054544018020303021100d110714220340790360391038400034000d0020107076018011400010f00091280108040188940b59401400380180340c052100c052242d04440c0c102e0b80c00420051012001c04100300042441e81e4000f001e6115940e03440700000c90006900d0f0091109042d00e0520301d1030701c1e4402c000e503040010641416450107010441c2e80d500d2809982414aa800c001a12038407144042454002d030ba40002d4442000424004100b140010b0342c0c1d4140d80000300d003800a075075540019000c1e401100001080e5131044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 487481321 1250 487480071 487480073
    0xc070929060c0d080f090c09181002031006110d050403060b04020d09050f0f0a08041a040e040f02010f05090609091b1815040312030203070c2f0a12 65
    0x144005000d004021619140320800030340d00d04805010742001068040c3c0030000e603280407000407540321a40c800a4581c141c00c0380009101c2d000014014a8005803000074420301c088104088014032204090131540c030b04200d40c2e400c7c403604091280344001011484450b200401c040303200c81d440c540c6502c03801d0070a42950b072480081e0500591094005509103c0b0f001070401c240595011075003d0b001500142c105941d40c1400c040c60491011010b60040120034005650541100d040740c412011400c00e45001a06085103840703a94814a140d5168000303200501c482c240d10924640c0c800d0301c6509407503c2103442900c80c1d01411201560003407045c40a0070842c1030103c0c00d20351101006a50008900c0810551030b480d811881140010f03440310060300c420340c14082101d14964840c407401d50305151540e82e95070781610310440d51004040d004004a1002802240380c442c1a60703001c40b540b0300039200102010140a03460030481c0c62108011108a2641080c40f100c0d003d8030b442881041d000245 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 487482571 1250 487481321 487481381
    0x6080d050a1b06050604050603030309031b03040e01172116020f100c11040506030d120e0607030c02010f200906040e1005090703050717190606050c0709 67
    0x301902005106180038040d214100720600380301c070244103c0000400c5e040c083d003400b0495078000c084038065401042400071101002042e1520039141c02c40301d126025202050b98258007640d40031000c5800081e00118500c140a0103040c1200343c16411105a401c41c141c40100e1211900703410a0541410485a00c1955001c0d04101505001605900c60003420307101040318044050025400039800388100b00c01c21010422941c1050401ca0381484282800350000ea02c1c0c0844100480600070903850301207100c4802d0700305d000122417031320a6802c0c0c0c0c58800380140c0a42811200b2800652a05101d03a001e0282403103000424110721035000d20f901140c0b02c07d00c0e81c0f54420303803001e035110200340000100203805a540c544103000c00b200103c61140351000348540003a000e4418000d140c1024208001180d000898074903010024040a4013074035844441589079045113692440d060a1200100c1c41982203002040f246440c0400c540340180d882c101007045400000e80c908051040341d41c403200c4503035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 487483821 1250 487482571 487482577
    0xd091d09010207150b0f010201270f0512070b06010807080103060507020c0d080909010f0311271501021b01084002010f0503094315020106080d05 64
    0x18112000514207983d5443e040300d0001e035a00d402c801c054a405240f5401c3c10250011000164280000c0c05021001f40105640c40f0060b0341d140c01846002c5000340030b01860038072480d10550444103891100480500003070096221071010b031800320726107011030195449049c15a120f41001e0382d91107020390840d507031440642800341c10340045118014615075603540e6809520080c0344079034030300b40d903c5480303005200100384140c0c08040100b107610410004942189801c80b508075040b19105809410360104035074010070070201110001c1841c04200c0c0a5040b98036121849101f6000c840404000a112040d01540712071841c0c005440400444d0072141aa40002c410940310300d00b0200001a0320400844256034294006005100000c1c041c15540c20841c0059111aa464054607500e40401c0f0a0341d070700506042c07034040d5622000c5281d4008540003c0700560451900489040e2848100c1184224068010410306e00148540341801138014800c1008072540d1030090200d0030112007043d9602d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 487485071 1250 487483821 487483831
    0x13120c0503040f06080604200d0209041b0c021509100503060d050a030f0305010905220203011e060305010641030624010309032307080c0604050d091d 66
    0x2200c20312020500b85603d558080c0034060a6030340b07020510b0f00000b003005940e00540414064408080d840e50a09003404c2160030309030b203c08015035181d04910204008010025606800c0d00100708002481ea510030100c8000354006c40f100210080344911402142c0704a141c425400581c5500ca203040c3c500440c007459022a0042c03c41040402c44d0b141ca50401c1d800010840019100c0c240e440111a018400d05003d031448002c00c00140c170780341181c502922400d5007900c0d06030100540740c008560702500010028041440740540c1d040309450020054007003400200d41650130b003400400c050114485034019103900760681040301c080e000002c10543c0c20300c0140312404910004da07966907103040000a0217001540703132201164204480c9850942d0110008604141c20840c068000c65801482400c000c40c0442c1c40e109000e00e20580c041d01449086802840e051011480c8120342c40080360580c0b2a0380100150740d502840b070282102c4120150184548500c20b40352042c00c464244a84140d101d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 487486321 1250 487485071 487485073
    0x1d0c0d1104090305190908030703030914011a040e0c0a1203090e1006030b0904050a1202031615050606040b030a0b060c0f0c010f410406080f13120c05 66
    0x100c890398020505849203518150040360001034800c1003020b0310145555135122524140510702e0809030701c16168450040003408040d2564518814800e000804181c0600c410008000c13400005503801100211541e0f0300d031080e8980300d009070800704003040ea1410850002c01c200b09807400c02003001d401e050b0081e030603010801520b1001c43c0e8a21110882070184151010b9060003d181100c018259190040c0003400340341c1607400d120010750000354a036030207030384004c413446407081c40c040882c95070254501002c000042942d00e0010300107a070100b01c0380d04006c14001e00080e5604000d00841c0d110794401c0d08001da10070000200c41c03c245a000b2114480014a5640782817085e02c05503184c084000d500240a030481021402903681064906810031f2250400c2c001221a004d042c03490300d05401b4502a0061003409600090f0440e400b80914110500101d103480b2a04c451000b8500b2600303e40100c1240d050202168000ca040b031000d07000c00d0307800000c89012804002c07003114401c03400c80c2c048681d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 487487571 1250 487486321 487486343
    0xc140c0901051c0215030118020a1e112d01060b122a0c21120415052a16110411030112020915030a0828080a1d0c0d 51
    0x50340c07480c4175424521084409682c89504061580d0307019104c10207090308071441040000080398004031f25648048802c10712503a03003489100184e44c000c0390340f500203405000703203e076154110a032400207002d0490b94410300300c0c4455201900c0340c01c0b01c01c54040d0074207945090103a041441443c3e03402c80d520070440841d800380c40307024030100428041d0035101c8206060000c500313140d80c5401085010491110600b0003016000e181c83d01003030340d114104a01040f1050040000d00748081c40e11400390b103403040d0104000c0d602d0032008051044006107107040400744140072412650f42ca0909075180c010442805407081c80e1207954201c000054900300c0c0d40c204d521800d082070f8131100e140c00b450003000f2900030140d420241d07204000b07505000074001040c24149041c9842d003503c1c005204100c0035030040300c03103a035424200e20b04003031950000301c00b03440207508401c0c642c505ca9008503139a0285070303442824081410071031074800ca444500c070708a0041c0d5211a805039030b20301d01000003500d458082e90b141d1b44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 487488821 1250 487487571 487487573
    0x3030509010c08011e2402100911130b090f07020d020c030304060807020f070b0928411507030e0f01120609060e060306071d0a0909030c140c0901051c 66
    0x45403400905520300c1d44020104103891454060140c058511289123040101c1104c503514015076032510000c41e0300403c2c1610a034a40001541c0c0000c24103407004202c040280b80c4240c01c00610744044880d100180074032403000b4005030002a049200c40001000703581481c0c208101128400f000901810851050403420300720f850b0144040d00150030984c0340c1d203940708030080a000c0f48140529034000d5902c0c41c0440c0310000aa08003040059540004c084003440c3c2c030340d0f81d04066140006058082c50035085e485038030f91664941640c0400d030f1003030781d0034800d0000004040040f80581000030b0b0208506802c00c0205240101c0c1c4000103e41c1410311890407103440c1c03030000844030f25802c10011583c1e500428042107280d0a203a503840842100240010b00c0c2040008041c4c40e2070074070520280c0c007401000e03652551007110780b4016113041801085400700034100104406d00c0c414050320f10800d0004660701c5000e02284d40021054041c1c280303400b603444d040074070446504c91a0002c41d10014010140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 487490071 1250 487488821 487488839
    0x6040f110313060606050f040513090b090d03060e1302040c120603050c0a082a0409060c02150a0612030e040f05130c06050313080714010606050703030509010c08011e 73
    0x40c010359107a03180b00e04610700c514200003280d40d1504040103201080c825944814001c00480341035410549041042080810120380074103540b150007000d04440404000a02350005850304d5803500c0f0703540620195540380082401e085060b00c002456038683c2017042e01504241e00f00e00c24800d07951800400e00644103240c4002c840303094000725150780101c4016940e5240116200020b04018405031196032120340300218201008814443c100204000200d40c59460350f00660800d60440014003020b228407000035124000e00c01e0400d0712003060f81c08940c4002c0184100c406803402a512030140b11071360f440c07d580030307e42420a1030740300c3d0700c442ca9948003144a0003218041c41e02000340e070000742c205241400d02041c142c1c000108008043c400c000c08603074089500d0302101d4000d140c07643d0300c08141c04c1c03200502c45071507510240c5600704080003c545502070000c02009000c5d907000c0086842d101c0107182030b1030498a8510015040343c005001880d95026a43e1104044140704441c041e55000381c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 487491321 1250 487490071 487490077
    0xf17030c0444010b0f0306180106030206120a05070903050d050903011e060e18031206030a021002060613020304020607120c060c0f0f030c0f0e01090f0b0c0c060c030306040f11 77
    0x3900050b100a01a145004030901032213807007500480f14105035802c0c11001c21b680368001001c801010035269040c4481e0711080d0b000303401558002d07100e1582d0701c07203150076503500080554030f84641c14a081e001802e154801c8896000360303035002016010b035903410402100c079508003085d110f50555860000920f651403248205414092031740c404202c0525010554082c210b000303140341c0d90307022044041c07403014001104032041d20320517142e001001e44555011170f1400d0708414000b500402013280703000e1103e40008407030b0706c03481003103c0d404403044011100500342d000603200250445000e00c011000200c01c0140500300d0105458440e041482c0d0782c803004e0075506250506400318000c00e102d140c980354000003e5200c07500506040c403146560460007058513404501003c2000304c01041c40c0d01720781c0310361a0710005015507022040b140d0340320342180150303030301111007110340e403061001f403026909140040d1200e1820000c050340c1141d0740d000a100103811061210101150f030350180c5929601100d0107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 487492571 1250 487491321 487491419
    0xf04080109140d17100302030a0b160f120b010507050a030512070e1804080c0d05040f050a0305060118020f0403050a03110c0d03030e01020d02070f17030c04 69
    0x1241821840c1822405207000e0307018100d440d0008180f119003160080d1a440c5a80016661000303943d55100b0800c100d9941c681009605024041e0403c003840100d0864601445000b0204400820000c005035907400c0a00326210104005110540703126a00d54810700103c0300c1810000c1c80c00a403a40d805040c144560030031000b054004c5810000041e880440c254000e8a0741001c4411544010018411001c0c8038051803603054540002403c0040410a4800010000046a041c90720394000a0300c240c005000f800c035a00002e050001c0d41c3c2c40c240c2c140c0c0c01240e800001030115a401d001c100d070200c0986800b00c0060940800a0010b030801c4100180021030003000a8030300402d46180003400b1055040c0390308160350108050840940c6c1c1c0c4022000b506505040001d05a110700968a001e80078074801c0c00285440441d5260500807503030030400701544a1403000c41107102009440032140810740714154144028802409210240907000700348039168040c01c00e41680c00312482c0c514070a6804 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 487493821 1250 487492571 487492573
    0x140a0203120c071a07120309060213030213020717030a02130e150f01021002090102070905040c1503020a08160203132709020303032a1201060f0804020f01030507050f0408 75
    0x80d8030b0031001d80a011050140101580820600400d0600300641c0d001e02003000d0000c5c060f40144a8405000e68404068180d0000095440b10444410011070072000c3c44141d01540c030789045000030039442c0c03081784c1a00e5445288608400c65202c2e6121460304000d00705031a03240c2c00c0160044008180075110010102c00032621900c1c03400040b1801b2102500f518280580c1e000c0c82805000ea1b00820031314026424900016120031420707004070b141070b140d5440300e0040382c50301050209010308040d00c80c05442d282e039464505201e10300e5080342248540c41d8444001002140400c0c42c00d0300c060070b0182034880510403603042070004040100380d6905640301c2411881e0032462070000313903070800d103581400914081c01c100040040c1c01294981c40010700d05104003031b000d607103159141c3c0701038401c0341c00c202203000311034450040c800012403510080c002c03031003c9403c400080008620034030b1140d02c0b540d03000e0466030000d0325186c015000303040041c00e21360078440c0500c060342e00c0300703189006000202034901c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 487495071 1250 487493821 487493827
    0xc03030105040c030e0d051606061d061f0e0a0b03090105010302040605010905150c030412050c09060d082215020a0614040f0b0406020904020307180819140a020312 72
    0x15003000211803c0c02c9403081850306001d00541c2c0e135100490400700010b0710342000c035560030900c0c400050f500d80055009020601e40700010440c07480d401802c50180701c00d00d80b00013041d00c1d4a020058480712000d4200300703200441088403050f0b4030410b000042e02c80c025121011040d1210300e1005503420846250f41b40d80c1d5100e00410035807030140907440082c042801d01d5001c1c0c5042c01c011807100d60074084440e000000000d07090600090400c01c450003004014130381c11003000a450800d45814008142510034001341c2c002c1001c49c50700f0310704c414401344d10005580c81e02c0c03801d404520341e903110240107400d0182c0d914800039280860003074441b102c12303003540a04150101031030004c0484403016800ca11504446003000000f8008411040450390090043d0046603aa4908040648030700301c2015046030000c018080c65a4100ba2626003000188111880030707a2617400d0b240c0e40f040804034094070101003441c60400725440d41c018051000b100c00070f8035802035260300400c2c070301402962500d01c420303000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 487496321 1250 487495071 487495079
    0x3040b0402092a0f0403060608031806090603160309050729030c071403070204112106010f11010b030f0601062a0201080c090a080303070212120112031101020c030301 73
    0x30b0b001855000e032001c45100d1542c980100800c00500302800c0200341010009038101200400300144e4008503880101848019202c1c00e80391380f69013000420300314848002c1154001ca29116003038803511600580300900b150b0f110399a500e22221448509000c1c156982d090070f0100b0800c1c801d82000c1d0900344900d00241814503209850703564510081205041c042c4140700030021403400f190201d9410031803c0038541e03900c0c80000d055104462000358098a003e40043e0741ca080c03400030b0243d00c102c03050150544101c00e0005014400d0840d005070000d030000504010060061480c81e06540c0b071800005140502c14010a2408141c003d503410703a507200c1d600400c040b42d070000d2107161891041c94199081e198480484070a41c144c00002814003180000080304e186e0040241c620340d03c8c000300f0000c66282c0d10400c00d42c6030741c07082c1c0d82d241c018001c001d8501303400c02c0c00c14100c541e04449140f1302411a1707c0c100d00c9118100c40d1080c11000c00c80900880c4141d08424009009900501c1c400f455981d450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 487497571 1250 487496321 487496329
    0xb06130504050d0f080105210f070e060a080c03150a060b030f0402040c0f080705031e070f020f01060b1602150f0301090c0c030507030e01050d020c030c1b03100b04020d0203040b0402 80
    0xc1300c40d0030f200b040410b1005222a8440c807070781c04541915100070031019500e00901e03a080c003654454442c003d01c25500e0004040d04000542d80c05100103464a110154840c1c0340151a080369070409500b640c00524129511071b440e005c003592114503514009512521004500030769030080d12450302c40c202d070384140015403605124a0348a030703145043c15101c3c07442890019240d85c20042c0740d807007401f4001c000501100d644110250b1a45086d40700078000317103046040900301d201008108401481544e40103248214148901001da0343d441076590b060201e1141504150700391000708076045449941c402691000200150140c130840c0c0502c2d81d1258102441d0004540d04448141d0070440380d144400040b030f4001c0115108560589004082000c4010040e1114459500300200807840001c0419800102101420022031000c0c280c0d0401540304a602e4022852040c650781e240e0000b21100032002e4680e0300c035a1025101400250902c0502014001283c208036019600e03010000e04000451078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 487498821 1250 487497571 487497587
    0x1030606092a020c22050a02040f23030d170c040302060306040e1507021e161e0b0f0c150c0313021206070207050a1706040b06130504050d 61
    0x41c95100402a20840c64a00010503400030200441e21056165090110b8424400e038544640050500f50003010840500c0356000c0b0106005851940742c031000c540c502c5450300031102240e01c034020885620b130508a0302d035000098a2428010719032042c822032040d88003409200c0e015605504d821081ca60981034107890500300501c54502c4240400040c00143d8a100582e0f42010b000c0c3c070005140c0c201d44a54514004040790031070f00354403035401042083d40d80015481d20384440080ca60300350502e07060480f5610440740700c2580100c0e000440c1401a021072030b91040f040f0000d8260000402c0d40c450140301150b1021a60300c0020400294443c0788200c10402c00400100802e0000c90500d0402040c0b00300f80030103040c111007050184480c205543e14084460440c0308a0025107050f800c008401031742c0c1c1e00c02c602c111030054640c0d0000241d403500d00f034961280851880050081c60750750391b5032045445002082035600161140b02c2c1d40c40c9030003620030584510302c01d0707004102090b0412000f0385120 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 487500071 1250 487498821 487498829
    0x170d0e010f091a040b011a12091b2202030424060501030b221802060c061503061303030f090510050601030b04020c07090908090603090106050a050a03030e0904030519020601030606 79
    0x3c0c2d8003805010008031945036460450b06021810b00980303003460030700c13241d80c41113141c1400c00780d2010007480407810001c200300c3d5a4200c02d41c440a091081402440300020358035401746202c844803101c10103a0307400c640013182e000380700707054919038900005030140ca500b00708103040003d55516001401903503010310914a040310100c03500d03800030358159608401d0115408a00000c0380d140c0e25600c3c041415002c000c6000d030303801000320fa2108014088a0b80c2c5020403036180030054601e000c80300c10340c20049001402143d08a1506c1214907041d10240c020380390352070098a205a9850510f00481c4050207089214200546c020030030b4184040010140d540e11814103104620400103400024030010300d203421900b440901080284507810f01c01028001c2e903040b075070441c50000401600c0101076001c0c0c406d4980485070b40c6005a2a1014088541090301004012400d4503240000c14941850b040703a00ca032280c42c1031440d0100e004241d824068500781d041c800740e030000700180301308050790042801070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 487501321 1250 487500071 487500113
    0x405040203010b1203120a2c01060b0417010501090605030a110d0807030815120304090b040b0904050a0c06020a1e0c09020a02100f020f07080a0e06041202040c0903170d0e010f09 78
    0x40b158100c89060708001d42010210690048d20702d11401102034100d1001480c00c608846e031100c3d41c1c2d24000701004c000c01c908081e41c1d4a0880085015903e0344503400c15580042c0007400d0718080c40e6140c005a91101c120658804007504400700055a82801400700b03a1290b0345548450424080c28129110b00d82281d901c1001c0001910910900001c207440c116010b4010200d044170a860119008260a0f03841d55000003084013088244040001d91222041c8a00c40741011140d4400b412a150002014000e000c179802070001c812104103110034042040c0030700035902c492903468002400300d912052440c00582c0101c2801e4a60030700301d2240d941d20554845d4150b1a02c0030000005240e4806c50400034010306022448211481c881e010300c0000d500054200c5030750b6503c0b043c42d00e0440c2c141d04000c038462810040350580d0a0302c600721510072668404440401c2c250719000203201500031500b6a4921075449420228611090280c841c1810801d040010903802500740400c00d0030b042440e00c460 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 487502571 1250 487501321 487501331
    0x6020906030c0c0c120c01050d0e0714130501050109030f06020d0c0909230a05091c0302030105040c1d040e151807060c0c14060c011401061e0e0405040203010b1203120a 74
    0x86010041016012440240307042d5a844109d200110300070000d82580700100d1140c1180403035212505180c00f604001c2c100c0c6c034120556420501030055034400d005845c0010010102040051611403000c41c0030b9104000c058140002e100e0b00504440c1107818400c00150000802c0045450a10404202500c894a000c0b9500004501800b500c038026050004140d42e13000012880c00d41400541c04000c0f41d4241c18603031500c0854010080d400a014042c421480c041f084003031540a200307500814148140b08a01d65407608041000910100a01d0446805410303e01848059003401061044400c0450068050081c09815150041d550002014030110100020204800f100d810f000c6030f01c004550b020400d010000b14041e401010340c1d40c400c1350b0a05c031403191410a0b8901c114107841c0b0560364075200382d200c2c0c8101d6142494000c040c2003c03c641e070210341100d08141d000307564000c2c005400460407400c41c1012a070303208000d501400b0950070204503400b000009510700c81d007050b611242400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 487503821 1250 487502571 487502599
    0xe1302120c01081504110f0d05070503010302010f031a06130e0a050c12041703010612150b12130b070903060b030606010e0607030903080307050702040b030109030f050706020906030c0c0c 82
    0x2050101c043c2002018407110540020585d896800c0802151340904000d13803103c0d0b2810b03194200d9041003107000706c01420301d400075400c1031044042e60f0483c2c0c0c050b5500c501207248000103030020220403101600b4280d0320b01820201d038540b00f00800b0040392a01c0101c4c1342900d44000b040744440050480362603a4101003e0003c529032a0058521890302290141e10507210362500712a54043c0d00e989100000000c0000165140c008001207000000f2000034001d14888240340d41004800780121041842d040c41410410b11104215543c08610119044007401d45603d5a202e1401c2c00c03240c2d8000206499418001c200c0207008030900413809400070492820b208001810034103840d4001030007828049900010b2610030381d0b0600c029034200b4103059603401c1c00300c0c00500c4c40d40440c400340d0282d42821000344241c00c05100b1030804075055035030b00900940c0c20000300c400768040f080071b0702c406409009940d907550300c1c0c0000754040c041103564a556109107024403424008030041003840341c151401204c0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 487505071 1250 487503821 487503827
    0x301090201080f07050706050a09110f28080304030602191706062101091d07080312060a08100204060e040e120c0f011a0102060c0301121b0e1302120c01 67
    0x643c000c1509181d44409a4841c40212140c1c021160701406a40c2003000780988034104c0d6103c0d4400500403600c02c0007450710340003842540f4031808282d54001c1c074110b481c031100e48080c242d20041200551082d01c0120380c1d0720106c40c40c5030000d42041e00c0c25035000484021745180b100c1803030320040c1e5034103000f18200709815044014280081040e8000c6c42c0001c5c1411240c01403400480d80511004030a444550b11003400c280140350068050ba00c440e0008401d0600f0300d80010048115600400290f14052050401c4003410340003810b5907400c288422808107040800703111000d2200d074092401611103142640050160b5110a9240d01031858101440e00821001c5085009508001c02c0c4aaa4a412074003191525003244046402c03546040c0c500c224800b521000304038a29001d908562160702c03800c0e40000786110a1007181300c40c0d140400b940b4001004c040001c5c52100d20761902c820ba080d038900f4072043d40c000c11100200b0340c1025052900c114a01618212a01869003004201150782e400020b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 487506321 1250 487505071 487505087
    0x904050705060a1205090f06073b0d06050601030b06040509072a080409230708090a0c180c020105010501050d0b0402090622080d092c010f050306060301090201 70
    0x8600842002a0901041d070107040c0710200c0a11001d800c224515001e506c072038903040002802d05c0710f40550008a05840e10070700350b504074164250008601ca07a5a80e0716900c0540913050104403da40c3c0c1c4407a101d0f03c0c0c0c0c8802c04028034601a040110b070310301d840310006003124031200d072043c800d68040c00b0511031901c5100080f131303200780a82420503e001081c01000307026040e007620212038a0740801164104202040038000300d440201c0244420700c101c049003040f440d00700308880c0c2161040000140c0081c8240c03040c5402c00341d0789083d5900d4000355120712903407000540048240c902c180090b1041843d151090640d8411244001c101a5061500003802d45c07080c4e1400c0307000c42e40c54800190280e5660f40c1195030130000204202e036190304460060118a403581e10480620140c680d000558a8000c0740d600d0100f089680c6141c0c1c00380c1401d034184540e81c280880d01d0ba800d000b42120f540c0720030b00d900c0894040d00300000003207021480c020406240c03071030013403960b402a4101103100b401030743c0021007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 487507571 1250 487506321 487506329
    0x30309051012360b0c1204080d02091009060f0c08040603090203010b1c14010605100f021e07090c0908120f07290a0e12030a06050306190b09040507 65
    0x1090440160407070340c200041e641020290300b01c0e0103031140410820f0f8842c1c40d03038152180041039016900e400003c0c0150086000080144410000140009000c0c400405a00f0202d090050070718031034030040781190340c010000c600829845d040610000c0d8000c494242c0000c1f44d450212007050043e40ca498241c000c61240c1c40078591a02001421980c00b0b400c1071300c5520000d01000c0000700c8039046a00000d0760880140c881031180301503000b0031703c8180613503815607501618040201034011012629500c40341c41020441c00f8201c5d0520001d141b003110040e8828a900090040605001110003141d07084034203217090000c1c0d0721080140703080210b005401103400712003541d2600b044110035859807241e2030004103008441c03200c42d0305681e0080c00c2142030451804001c03110740d50315550501240d0342c3d40034122540e03002c040300380c00a42002000303540c0850040c00c081403070b0b81d54101080c5000d41c20742f090707442d0015203804c583c0f010469208400382180c0446095155041c00e8581c50303102d41075801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 487508821 1250 487507571 487507607
    0x3210090207020a1e080a0501140105010c0b010506090f041d1009170c0f060a06060f0e031e0c03010c050c0d030605013204090e070602060c0904090611070c0303090510 73
    0x8a0340038404c20070480c840040c0320403000c0d81c0f0210250314001d070080810000c81c200e031100b054000305040d445040c040c90b019621150711005a4204070821030a9000542c01c42c4e80300500d07007201c540c113031540d00a1401450700940d940c0e400074116040d403030030000461402c1402518211455004ca5640840c02010403484a00603644140d0080b0072410701040d011040310700d2252400744841c120041e1710003022100c059413030b440300e0340c0f039800d044580e040190b40555169103e0175050f03080b074080d11072540d5402d1000084030740c80340c01d07440804e00b95084020001c01107900802c04c0d10005109001081d1401003510707040041c0e078205000a060007213002c130f42c2130142c0c2103828034903115141c610b005820740881d50161511255100400f0018082824a00c0300305d006144001641c01c3c0009201d5005110f4401642e0074082e465082c4001091070307120546510391109000c104080300c910050000324014881c0300c00e210704600380606080d240368451806001c03240b11040c581d43e0301802c01e1410681c251 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 487510071 1250 487508821 487508849
    0x317161506350a0f0c0f08010c0f120e120901030b0619080403030f050c04092d020a0c02131416020c09090a020a060f170405103210090207020a 63
    0x8400c40d14001003c4001804840054069003d214400120004884816001900c025101d1a02c07138240c503003104005003ca1901880f070081d550242510a03050403000300001090f070300490145142c143d4030f12480c0214040041e00d58400c0d40e0500070f8450041c4159082c901c0c2c000740302c024090401004026074100701c03150002c60f00b018483d40140c00d911007805014080c2e418605c42d1001c55a00c28070900545515150018000c4821000c00207195551030106507820209190810081d42c081d040304020412200d1803240140d40d0f8141880d900700340c0300000200c50100e800c2084200d82e020b0108401000140041c40b8440e0380015480032148081e61125602e8071640b48075854002d042c04000e50100c2003003c0810311071f5002c1159214030f921030341e40c002240400200540b9111301a200682290400012030b20300700c3d2203800440000c1801450700034003040e61500350240c21211004541030300265800d1020300740c54000c548014025001045141440550000301340140b03505c12598044a48 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 487511321 1250 487510071 487510169
    0x609010f09030b0f070806030a0506181203161106010b161a191808030621030c0c0f010e1e01050c030a020a0b100501090317161506 58
    0xc0d421040055074031541883d202e044c6018140000c440071240500060640c200103803030780c80c00103459080c0c80d030080003429060300e4405001e824000a0000e03100e00307214440d000c030204894000118400c8003844400707074003c05441001000404041004031141c1d2181005120305824401107483c501c50000410703046115520344001180401024911145201010085910302c0d0301000c0d041da519600e4104440d1440d20440c1743e401c0340030000503128001c180005032050810b25250001d0900201c814131051800900240c60b640c0f024450f80c00e10340106c019421103080040010098410900340b000c1d400701000007048000103080b41030524104850044206a40107804036111041d0308401e0303c0c3c1d5007005d858043d6030380f00707105000c42d40641b101c000245000c0c209505003082d12416501c0715405860340d03d541c02c0702d403400c1080d03010300b48081140e081d20b400d10060705050b07107218403007420404501d034200c5c100301c0d5807a9200007030b1101c0c2c10f802d20030017508030204100550700e043c0103032902941c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 487512571 1250 487511321 487511327
    0x1501080f0708060d08040e06040f06080a141501080f060106030c2705090a271106032214060a0501050114070c0306051f060c0206040e07121e0c0c020609010f 69
    0x4102c07014018170b0000034085081d084099a20b40b14000a66060004a04040ca4201242e01a2003070762081cae00700d0501500080c1491171350005801c2c0d141d0445030f03822285048ca0702004003c0e80030b215158030100141d544180240146801005c51f0f0800b04541340e01c004000c3d01000040d40c00d42410821042d01800c1005068003501c00342001505484043c03034072101c120004e24000c105002020041e81003225105055840000002c1d0b00094103620b0b909003e0030b000ca2900083d10300540d811415580e505004406202c9011840c001c18102c8540e030301c405200e0381480c00c044c040c07525a5050030014842030342c000170703801503468032154aa41d6540072410803041c0031500b071300300a107010f04040038030502c40c06500950000c00b021120706c2140a039228001d40e05c2404640700203400100910003000080c0024407034950149841c100003480703d8113040c02c0011101c03c4040751101940003003c2c600301c501c42d4403504928008900b419400d49078260002411401081e0445041018074106038513551300c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 487513821 1250 487512571 487512589
    0x8031903051311014404080403020906030a082208011a090a0b0303041e060207180c050910181401170702070b040608041106040311010e190305061501080f070806 71
    0x8030380b41264140380442141c0807101a4083e006544000c858111505c1c110303285090580151f0b4018083c9241a1943d42400074418008200c2d0340d0601480290344041030900000b0314003950862100010089944c1c5509950350098000c4040c683c50702c1207400f1050700811745518100340460751040756585000c40c1c013001c4d000803200303541c060102090000e004003941802c500c00c00307444000010100e450300000c81c1c1c0c601c15846001c40551701a1320540880c6080d83c40540a1151071410500d03140c10000421055a45030383c085000402084601c2c8001420140717044c084c1c8103100c019460001d031000000c0c4112080c004441c9481346100101d86558000c002d440b0041c04030085a98a9a0703031400e01a0000c142110165103000d00040e140089240180032034098a600080c42c980c801440001110300042c000d05954110441c1940e0341d140154440c542d400451040000b0410340c9040300711148069080500e45051048010a020307113040042c00080d0300080c41c0c94042500d0780c0d080f0000d00115 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 487515071 1250 487513821 487513847
    0x90a06080d020708070e071b05100203070825020d05090301091a0a0c050403031413030c0f0314060c040e220605161110090206040f0803190305131101 66
    0xc490790240c1d02881c0e40204860084401c0c82e4103941049540e0031500340c010300225640e40029500d00600880074a4000011003542d0251040390303200195525440220b074410b442440c0400d0303d5004004510050000d901012107072025049416406600041e585503c640441c0003400400305009045841c2540724440581d0008441a0048050400c0891680094a03800725181c10400e01207909801003040340c088960568425019240d0310003104081e820000103501d45801450740000401c410414a03009031044003000b00300d0900e90325112a2007a184803100b6460341166040182a00e4000152030494015200c80c1b90715544a10a8904902d070340108a0703c404260003010301800707002da110030700c20344034410408000350501905841d825000c14110f1280c3d44a541d22148022458000084040c4050705903400d09880b00d034a00071031001500b000030300303500c0496100c203ca210725810800b50355440c14200240d0800c501d0340c09440fa50070034041c0042e070401034036074010b034480c0040c00942 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 487516321 1250 487515071 487515073
    0x2d0303120207110a0905160e0102120309150108010c0306230f060d0c031d0c0d08090a0308070f1e08070605040212030c07050901091427030a0f1b02030c090a0608 71
    0xc1c0d0b105e00c0345600400040e1440c02000c031001c9915110a80a000c1c03448848205800030840e4410745411110745900040055115004540c6038079004031101c01da00e40a00500350010800d080ca1842c02400c88000d40d03c0400c1d03001c4241e0502e4030022201241002003c42071710710740840f02d03454012980030700c1080144e40350146002e000c0e043c0260705601180c00d000f40103a4805031582d54151450b5a81c0e28125456808901000100009803109005101040c8041e1a0507401680e035164070120b0382040006603251088846c4910811000001814403030300800c01607140f540b030985560842d40503043d4002e044a568902007402e40d80e030b0403084660780d4038803001ca0745c0e6089403048641c1c81c4c10092240501840641740049401ca419000708840120f16280444a0350b847d2400c0b42090074500c0030441e80e102c090481702c22140030a10041000d140e5076200c4a40700c550103400100544038450059070b003a4288424000182d402054141043c0d10440700490b403901c54154000080c90f0562000e042c1e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 487517571 1250 487516321 487516339
    0xf150302060a020a170c3711032505030f0703030e01030b060415030c02060c07060504080904050c0c07080319030b0111010606030e060a02070b010e0403090305072d030312020711 78
    0x126500c0d0400400360042220262100c080d400b03140587c2e05103452010641500c0ca901c101c440084080e10000c0c492405248031800040400020a042118954000e5600203451701041d0701140705140200040ca01940100340c520403a44c803180d01d61081d804020300700400c1403503100c580c2e80700350010000008003d011580c0c9035039400444200d041e40c00d100002081c144100c15081e1070020440c280325443d0078000900d0302100f0340c0c41d0401014000c03c11507003500d06010b002001d8135140300f4503114800c07041c0c0540d5a407400c46d41140c5404000d621a581950040025200c10109181c2c40382c00170801e8100803604200c100c0044c4c5107030729008140561503188c1500015a9981074103d400765034800c0d819201141c540410080a0380f05180c0050504901600100020030741e0182151f032082c000e10b00482803d45a0b030307560341490821303400b407544e020454500d60320130080685d88680401d0401120903c0c1807440d41c0140c2003100080301c2072183c83c1c0c041090b105003d4404400802c4040007001401c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 487518821 1250 487517571 487517603
    0x20c06040b0d0507030903081b0d0f021e0f0a050f07140c040b0402120c09060c0709142401030b060f04080303011e081c09080609060702010f150302060a020a 69
    0x446500079001d42d407881400c00c0c02190f40309001e8822051895003580da548801c0e940da0060a81c1405001c0d804081c60301d003000060340c00405842206007040b05a9030240c0c0d148481c00700804400c26030321008030001020007100d6000c0704064103c55060706181012521407501c00f414000380d004028002d0440c400e1880a5221108003146a4900c0328041741c0030072030b42c000b440600080b8062146500c8000e8040004a14080300b07142c00390130300c890010441032400d0004e020b0b06082c511940d1140d28801c0c0c40b8803040d0401841c00000322b51091901000c022810701020080c6400d46016025a061603516859200503031100c004031440502d503404103030307621a510700e03c2e5540c0760f00910030a080001500e000d40c2c04011410032107070898070740400400125109543c24840074460400420078031000e903200041281c000d0003914070801418000e070019240100003e4207440851050841d06485c02e50f40306000b10450081105498054904581f03582040000764a400600030000d4802c5030601da08072 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 487520071 1250 487518821 487518839
    0x4211e1a0703090816050a0f05010b011b0201080402012f1005280b0112060801020702010e030c210a08120901060509060f04020304050a0c06030212130803040b07020c0604 75
    0x10800601042002401e994112044040b50101c000081806004001188000d100c80c00c5a521050207034041e42d413001d902c1d0351400c1d01512000802c4030665142c8031038110640c0c002c1d040c050b1900703100c904510406001c1c3c0c0001c0907550002e00003070601c40303d520381c0001440c10000c05400307045920000703072280c1c040d6012207a481040c0c94244000d90b042000040c108103051404124941c9281c180201d290303001d0300240c018103003620343d643c1040885d48083c107420549014400080c550903000580da5071450000600400031415405d01075400a007210006466107070440c141d144100314804070341c210000d145401d12900280c0500740000200700d0400301e10141902500034052040200714441e0758406110790b07107100b1503086c0da0000c0c0c40003010b0b409080a0700116403043c440d009a580d80c0c205642d0ba220191415002000060340c0030840486010103074948527040100260030540c410250f9980c4007107488002d20080080c80c00c6400325003107074001c100c800c40c051002807001d41c8480c0c03640016 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 487521321 1250 487520071 487520093
    0x30605190f060509180706110a02060406030b030615101d09070e03061602070b09010e1e04110702101404090507080f010b0901020d0e06070b010b180604211e 69
    0x215101d4200e140c041041d41c005d00c1170340d581e0702c03500c1d07405005290328000c0140d8421603e1641c0d4001401414400c0006030340d002c004001130302c25a100014082c40e81001c0c0b41c40d00600038844400d101c000b01c1750030307003d9071030a41d50b000c44a000c0c03820b984000c0503000c111072101c5024651641010070703e014018080c3d001b1711014041e40c019411680c0558a882012044140c072103c604d000d13030050142403090300481002800d0784c0780103040c07800c803008030103012581c5010000c5421149182c0140790b040d076850240160310303640076400d000f0760a15002b500090780000100c0c00b00c9090100040112000c3c941c034905480c0100b510b06420172a07450440b0300548100c4c81221443c5a8203c8031002107025400d40040d5080d01c98182d00500c2d0b5060910000d540207084122103503070250044c840b51000401081c4258081c00d05a150035407541040d5402c0d4035041e85880c0c00383c1c8640400d100a0059020941030300b045507189044401400c05141404001d003c00c503e00380d80d81c1603800000e0828452202d0607 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 487522571 1250 487521321 487521329
    0x302070f11031509010516050a090510140304230304030809040f090803010b042c130c170318030d020a060213030b040803040201080f07020a08070813150f020604080301030605190f06 80
    0x700c02c7d800410004c03500c610030ba10300f6402091405a080c07081d414a58103a4140c41c0349410b02014006610111a8a0b5081118111a260009028500040310a2000d843c00300380d440e009500346801c1d070783c0f0707074029014240c80180104d42e1003c41c14000711540e08008285c0c2e42068007117a42e540c60b40040c1829501c10301940b64010580d51100340040c00303001028000c0e01c10090900d01a032152892a031240b81407140958105a1030303c1c000c90080390140328440c481040c24002c540d500c3c04030303039103212500a40300c11504c26085000e070079000341d401242c07000c00c19600280069580c550751003030a68403010b0b40c0024081420745810031081040c0500154012070007600c1384001c503030700e035264590011001c13a00580107802041908000661141c09801d20b1880384007450305040c0301101000242801c0c0e0711107640030070000c8a01c43e416030081a030004211b03641c40503201a103080c5d00c2e82d2030300c1d10040c40010b2003e6074a5000400314200c900341c280c50b001090708184018034000e0b001c10060301d00c40c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 487523821 1250 487522571 487522591
    0xa03030f02060f01030c0501030203092a030705030a03020c0d0f0c0f0e16050a1404150c1202010b0a030201211118010804020d0308071e03050a06060302070f110315090105 75
    0x400f0424507009601850b049a51006024542071700380401140a9000501070ba54188904000c5243d1681424aa202c501200e803144a511214210425251807841d50080d4080c2e00021082004254045201d442c00c490035034004252001525080400b03045804015000651a4102140101103202c061003101d0000340050600e843d5282064050182d0110395808110200720605419008a95451840b0710030b6002500b090758404562200000455220001510410042007089982c8501182c0300100384004c12400b00800e0100c1c000450718000a8180700446540c5c018a01e10702860035208418241d00344104200640d006600d9007007081c40602c2c03011096000e08841d44105041c0c0d11880c0c00030003e1503050040d80303069031440e90107000e8000300103a0b00e4480424500c5119000741c0195207aa0004043c509002c42c94201d8915030005010980100100070101e40c0b4041300f04512500201403014803000440081d2410b1100440504034054900c200001c03480198009489544058 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 487525071 1250 487523821 487523833
    0x140a05030418060b09031c051606020705012315220603050f0102161118041a01090905030306011110060306020d05100f15030f1404021503130803060f0a03030f02 71
    0x4001c0d4090140d1103500b501544181d216407c0129000842c0d0403000d4507040c000e01e80101005c520580788a000c1b000c0d01c815800141130400c01000b44100b41c000504d61008040340a44134585480405014000c090600a041100141035580610710381e080c001c80d20382010480c010846c0c9030064030341c51000b0744140c001c0030b41081000106008031414074041c1502c0390500b2005550301c0b56603c442d81805904212000b00d96090040c030040c0d214000c80c010703103848015545280304e554029005800c4007014504281150700068800000c1d6504074800f4204202000380f010b905a00e0143c04509102c10f440c01c0480000c107100c1d41340d009250b0802258024000c0e0f03a190030300000d140038648074144110600d51000c1040d44a05014103014581c28a0045000765200d81d8040075211000480000d800c0044240400c5107000105d0f043c000c00703181c44682c158908140f44003510a0743c1d40e03025011110010004419541d112503001012078018540200356849082c0101001500640080944504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 487526321 1250 487525071 487525079
    0x1e1c0e0f040c0e01080c040504020406080a060b0403030e09040f12200c060306060d0b09040b060310140601050a031d0322180c02031b01020901090b0304020d140a0503041806 76
    0x18002c803a0007200076151400d5000300341d001102c82d010300030000030f21010180004105a90749000410041100f540c0d20138840c140507160004445041c0d2005d00c0c610380c2044200002500064411101881114000360350359840c200030408c0b4140300001465440040d05960042c0c0d040302c05440d400300120b02c541c1e83c10310201c141d17070f0b40c03103d0b001c4501e58081c400344005065490048010150803242c00d0001c52000b1f03848004c1008d03003030161412140303c1004410040385040801c1080306448404a0900c9550543c1e40110700304180a801c040c104000001c1d1014118005c1d08805051200300c0c810303620710342c42c620f001610b940249640c1104500b45045040c001c0c08512154001d0300c982c0c95803c06442284e00c515030051090b1a198019400280071101038064145070120380e00a0410002d65a84003200006101a0240d00300500095040c018880540c07160990700c0200c540c408a4050b11251244a407840c1030420784004045100016000c80c0151051030714000c04041c5410501c074807a15 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 487527571 1250 487526321 487526329
    0x207030b06041b09060f0c02240c0615040f0c0e01050f0f041401030c080c03270d020f0f012003040812040507030605010605041d0711100e0c010804051e1c0e0f 70
    0x10308180070350301c0391807110000c0a5640c2d85127010f42d6049650903061402c50382e140410b003030000c125281641d51a180700c1c1900c280c180750203004075400c00c441080201e26980c00000c0d00506c1022407241c1000004501c000c0e48804200850b15044506c845003600c032940d40310a40d0303154004030b2a0600203400c28003c9441c060061141c980140b0300c040c2c905084d40c2e51014800050704c008041c1811300441e18856480108080c8629404100142e0140090001890406e80380c4464040f40f190240e140410400c1f00010360300e9440e101c240d440240956035102c50411740c2c1203008040e01000041c04200503c02040000940d07401282e109110a1106030b83e10701d015603103070265102e00c111441034400081c024a07040003101d6030158030b5040c2203c4040c28486c04a10780240c4d07180c401c011980e142401c01041c8000c02100b00410000d00c0c08440b14a425540c41c0d84580860116082420004064105c035103418009002c55018100100298000b10ba500401c0c500244030b2290080340c44408844079420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 487528821 1250 487527571 487527587
    0x506040b030109080412020303130e180d0504120f06110403060e06041104020714030d060e060402040510050d02091815030a2307050306040804061d010207030b06041b09060f 76
    0x1400480c04d40c10f16240030303628030710300b0917100040b80c1c180000c2040c590340c2c0300c0501041018001d8641150403078602505d1000780f015039071000c01201c2d4001e91a511106a00500311410350b00441100b004110440c6400e05003400b20001c024060b609100318400521003450180045038043e04007801180301c440300c8161100d07010360780604a01c0c104004160300c0c2c10036400a020092003204c403c0c06100300307004010f0854000000350030140b82c0f50b600c01c000c82c030209914250801e600300c5045161520f0040024640c490503120300061201c04101202c02107100c0c2d059486c8100c001d0400e08a41b040f0450802200d40112012512840160f40d404058200007c491440651003044c4034a0054840300316500403031010001405031141d1a000b1640b61800d00c01c0724040c500c9000c0640d1100e09001e03000d0400392484041e00720700310f4440e8008401e0faa00048090499030090001c1e6169121500890050a00842c10b080565107804403000420b6120720035400300c1e64540e84048040c4d4881c3d4045800e07203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 487530071 1250 487528821 487528823
    0x60102010e2d01061e1703120c19180906380a050904060605030618090709140f18030430030f030c090317030919120806060307020618031b010506040b030109 69
    0x147c402d206000c1404085020240c02541001c03403e41003110341804036200300248052100003846408000150030946a640700140c02c241805000181c00d00d400d11404503500e80904807151403c4101e1a24107403541c094285444044021070380c0c030b100d04803000d845a0b00050389140503070301c4c022000070701c3c1d8401c006a0b4015600285100c0c07903035090145030110f0000c058a00d111074090f1000c0000c2040051141e52204070204660303414030300d0060400e96103940001c02c07881c032040d21944c8000756150080300301c0742512246031096041086941456900000100651003221305240500f018550030050440c0c5c03002c032550f000d103d8010014412200c4410f81e11004080144541c3c058501c06098806590321046035801c41d0506060b0000d004102c204060003910403900e55403200e000d43c1d170b01160882e4042ca0640fa21869810000c0001356a07001c01400c50200280f0f5a50340314001c1002d0003201c001c2c01c40a540040715006000c03ca034002d0800781c0780e56200342c0c43e01604540d81e04060040321301031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 487531321 1250 487530071 487530073
    0x201120b030d030f0b03030703030504020405012103030903022d1c0f110c0a0b0a08011d0402010f020c091e130503070209190f0b09060102010e2d01061e17 68
    0xc0d0b80c1c5400180e028010f6407102055090b2203100c0703024203403000c00c09401e103180a0f64001ca03450a09006000450b04103802c2500c03104040c801c109044810000d000d9601c03545440d00140304062810200e040075039806030810401451450382089042c1100a42a1100410107417002030f240c8289a1006220351480080400e1209403c0402e0a000b005504a550b040c40b0070b50380840b5401000400c0d4144a0700407c000d13030000300700b81c207040e42c1c000503132405480101c001400320400542180b4031910010402410040c40d00c4c003041015109008015070300c0d40181c20b00c0c0d9641401402c50300072101a65510741c81426503c0001d6004130790043d0a500d694001300518900189902884150303039006000c1044c901e0f00c048081c106001600c00c02100030420310780007450807130260030002120030240c01c80d411681071240d03074581d41c0004203d403030400b45060340e03170500c8115103402c0d803d6006412600111a51801c0fa0006003900101d24101c46000030038042e00c0140e4a030084082d0140d08600c61200c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 487532571 1250 487531321 487531333
    0x10203010b07140a151a0901030503040e0c0f0306060703111608010b01050f0301090c021c0203030601081315050a0908070501200301060f14090d06060906050d05060f061215040201120b03 82
    0x121200c031b03500401e414140c0440c0d446146104502003802c0010a031b0040b00d032a8400501044110308059105810810103080d0601d0403140290104d4603020291031f0510501000403020700b0140152a8044030441d04415135010300305841e40c80602c0c1c490362069907855420803610155541c480c00884041d05541c0c7c511504690030440c4800007040f5052610042d440f90365003604000051280c1c195038000c00384d0080daa20720b0000001804503402402400300301c41c1c0c4031026000244400800f070b108184404000640f03642e02c000034009440d101201400705500050031500740001034000c900c00c9204010700498501c8030304103912252009106010000e5645070340080c4d105d01c0307020f0680040450808845c1041070a00028080d14041c10045034415510002001000b00138000d00d801071104540406011005880c1c154580c01c00074176800c04e1030b6900c00040c0040c2d40f4180c0360031980440a080700c070340d50142d5071a0031540d0000d43d0700740d011815041d460b503190101402800c03140040a006040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 487533821 1250 487532571 487532603
    0x31b0904060c09081903090609051e1302040b040e0601140d05040f0c0b0309100c1d0a09181703011d07200d170105060a12060503010203010b07140a 65
    0xc000c140b000706080801403142000a55107204012943c500704101c43c41118044e814070f005042214554443e8051002c04a810040d945d580c8080a040a6080030720b0000100403e002076182882c07c009010030a20228000c1880d11009014200b1385200801050392a103441c0010342d1610250b1b4030b202d5006508120103221101550005034106125030500715030000301e81e0f41d0070a4242c1e190030024031440003008200d2460030030414030441c0400b00e042041a0200841c0040030030f207141086100303201c0c2d07498440d080f41d154500b0000051000500400c04880c1c1920f43c281c1214030401c0540320b4002180000c1031181d085000c84c0e048842c000300003c0707000300d500c403c0c1000c0ca00081c102800d021482b1144c60f200e1221409048108408a01078031920300c408001820004280844441c0381c0004c0c0c00602003a11580c080340d070300600904191a070b1008250036000a070600c3e0700807a40550011000150039007200e809800c0841c031030000d01d4945030010065590b80e100b541c201601288000c58028 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 487535071 1250 487533821 487533833
    0x10f0512061b0a0c020402030c0304030e0f061e091201150b03160f050d06031407090221090f010f0b0f09150907020c0312071703090c011b020d0c05031b0904 69
    0x304440c0d190600ea0791044d85600001e0403600b086602c40740c002da0000c00c000070190b21080400c200c02d0200c038030544d5001c0810200d0024007543e1180c88030070720a403003046404003041b8251001410010540311b654984200c06a0290200c01c4c2201d0704a0700c0c00034082401136484007560f1055081c000d410035050789500e011070300250800c1d5403c05009041001040c40ca156000f00800b440c083d00d410703105010741040e40c62a0188070f81c8000b4500b4418403800d240305080054182030241d43c03146010340340d183c134280141040e9440580c4581036182c181d81c3c001400c10f580041c0c3c1c042d4401c84d01d00c3d4061038030006105500e4000c80e0012503010f03003402c00405a00e40300d42c039242c00c40c0320f502c1298891030701000800d00c0d09810b0a0040440c4102283c00c1c002c01c660b0060b107010f0f03032305940707602421810810415a554400c030780e0250306200e800e000e500c240084003503070030101680003002ca0000720214200b0b00c0e003051440c02624000d004801100d50b054012aa404e0700c0b08001820424055480d502c9030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 487536321 1250 487535071 487535077
    0x307092117030702030f1e1305010206060f0112150503060f40080c030a030218030c030613170313030207060516150f02040305100e01061212090e010f0512061b 70
    0x850310101000c01c101c600c4900800944460304082d2307454081c0b5814440060301d40040248400d10074140f40d4500840c43e40c0c0711070f040c504458551004220000e20040424004029802050b0075105981c02c008114444041c540e01074400c403040c0e615640d070922040b44000460111010b024140072400f4408600d611204498041c0036102503801d001e00c107401241180c1c0462500c0300001e4000c20001000c000c01c40849103450750480040244100d0800465110880100450443c0c041c06154500780b2480c0348424481d81c07141c90701c480e90380ca881050307290711180d2903009038014031540901003505405603040720a12114980620215451650f4158814000390005017019455000854030082e9500142c40518440c034042c1c00e000110641590466400842c403207400da042040411181c800c0980c037030030094011012181050000d4001d561400703d6074082c61105490100004410040710100c0040e035800320744610f52080400b4005680f8503069842d6861005c40c598841c203154009001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 487537571 1250 487536321 487536337
    0x40305090409210e06070b22060204060815012a050102070b070e0910031e050f071502100b0604260102071505010801020313080307092117030702030f 66
    0x80400c0a420320760383d0802040c2420640d08110f00003101200f50307140c20440c0403203200070545803542411402e44070502805406009a0036100403110a800c0c1d42d4104d18031410382d150001410340d41c903540c81d1002092001d08aa201e200b1010460b07400031158070901c00e001035021b142c001d44800740b0550059140031000801c044480b90f600300500720000707103080b00e0a072183d000b540301c075281400c45206000e03044900a06549182d2107841060002039000c95034000d192200e5546600500e00390700e0554900440b402441860b0701c5210320016800503000c8204005103601e07403d03120b40d00c1185c1e01c41c0046d6510404100c2c0c3c05181400705011803840640c851001750a501c4034204584000310241d400c9070300c124416940340d811242400881c2c8464000c242c01015200021440c5150010601c00440c05100008111100c008042010188101148400b13050b0941950401d07142000110001004142c8100e40820340e800100010a181e41c2c00c0d00c4c86044a07401861410380d00b00200345082d409000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 487538821 1250 487537571 487537579
    0x1707140403020918010e160b03070306080115090c0c031421010e06041505011205040503091503090606030601050a0b0a140d15091505120708010e0604060b010f0804030509 75
    0x4400000b503550f4002031800b80c2e400d41c403126940d003a4548a01d007514914580308040c0c0d8003030442800c032032003100401021030340f90120103520390322013020440140240b540920700c158240a800d540341c41058890004071000304404100a84200b0421345404285080c0580481c8e00070b111090040e2741c8500903c412850701440403051415040b035104851000c0c0c00150501d8010010400d00b42041d10406040c11491450b042c901071a0100080c182d910b044c04855407261180c0104081200c104159250b01c5070090107802200300184000791540c20071141e000080c800c55002c100f03241808a03466050301d001400f0b03840e2603130409450000d47c0d40f250040d5000c0107013442d0113014982c24240540706200c030150700482d04071040d0180302c88001654100101035840e1040c3c01d414089003035424000c89800381d41c2444c0d03940000c0c22480c2450415441070030300d5401e201c8030101c14040031075050700c101e00c00c01c020415100c6031001101c0f1440c20508a0700400c6020010501007030148020b0050500010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 487540071 1250 487538821 487538827
    0x5060f07021f02161a04090207060603050303011202010801050402040b090118030203070308041706010503072105191203020307020604150b030f1006210605040c0f0f06030c170714 79
    0x2801071401c40b6010b840e07200140c2020408424580d43c0740b000000401d070240c102070341170451042c00c0e291880b992082d0380c04245d000034140c080003003c0d0030100085410a058a07220741c1e5940100010311000302c1c00b280003d40280002c10203142c588203030342c02d4400801f020b908100c0f03400f0041d58000420300085c0c13070f00c0400d06030010069400f004443c0c007861182d06815203440c80d00707180b8080360000f007984956030f410032070061000e610300160700d10403580303903501011180722542e89040c0f55a040c10005400f44c0601d44041040188080c490340000c1d2040c180650075503400d560032400c071301013541c1031300060b0041c0003c98049100d80301040410708400000007040814034001034544440074000004980003c0049446078000340f281c00001e010000d6000b1884983e80c5464419050a2100402d0703290f0310004130b001d0202c1201104040c107400800201d50f80d490300d981d181071450074861040020300f041c040349a100d01c5865412418031000e80b4941c40ca0b254920180c442e89080307000203003210014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 487541321 1250 487540071 487540099
    0x150b19050409231608061302040e0c030402030c060c060103230607080601090519030f032c0901060f0516020103110721050f030705130302130b03061005060f0702 71
    0x3511440a0031030143c01018610703104a0890300490000424035640b021900c581121001c0d08094101e91040085400d0001d802122941c01e00078083e0341c00141d00e11031100d0800001111000095001fa8001c038110f4018040d03031070400080c5d1080340c0030b554058008100400000710030035016801115810b03911030200451203a502d00d031000c02c40f08000060050418841d103541c0080850020b07150a848404000780300841c028a62903080c80010510020f035541030061600c605c0c80c0c0403c2204c500720071300b01510051030b1255004459003c041c4202c02240c00044d14034016140504110000c0c0c4a0904180d220749200243c8416034009034145525803407100641d0803558014282d042c4500c001503d1000d484000341c0511030345451100911000304114510b04130181c0c15240d0207581c03483c1096840d0741d91400c0d80b403a407065506c002d40290580480f0098401a60882d8108083c1a400c96400359651102da00c044402d42c400d05801c0032081140f00c8020400700f005011040c009880e4010500e04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 487542571 1250 487541321 487541339
    0x13020f12090a0f2003010b060403080904090f050f151902070c08061008061006020a0f060e0607030603060e0d0e0103020928030203100b0f10121b03150b190504 70
    0xc0e11004a40410f400d03c480d0701c0850724543c4c0106400c0b019002003140754260703004103d07244254000500900400310360140c09030b544e6003080741d0381d035405114035580c3c804c2803404984d030b04811607001029024803000384141d01c82ea4104140b242d080c40c0e00d200c0200140c0482c0c5c070000d500070142643e6a5072034040115044900700b01c554007603005951800078403454020454104100a4007220190700196801c0100c640d00160f582030440c1c02803003810310042d41d440d00300010034200b015129180600070800150f290550310032000c5034083c08042c00280041d10313405413a000c1c010b502c500030461154004015511039800341451203c094061382d9a403000e084000d0b40142d5181402d83d0040030341c82c0c14411424207100288248408042c2441955140030006110700c0180000034003425035900c9060101d0700c5034095a03041d185248040043d400001041900c0d4108184500b000c642481e01082003e00c0c0d5034803000480704a21045810101010712940941070b844e00b40d44204141440b01154640b5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 487543821 1250 487542571 487542593
    0xa0219080a0e0708160509040f230703060f060602060f16020c15090a0602070e061e0913060606140316020f0d08010f0f08100509120d06030213020f12090a 68
    0x140c600280030701d1744162108000505103070041d50241e41c6041c14040001c0c0c000e014020031551000b194616403116012a9540c0c501d140d220800f6881070400c0001408104c1e0310100d107807030101e070052140c16128042680d540c0b10540303141e0f4035100c1d0140003c4180700c486009491400b114810b0b00d0811000d90002001c480016018500741c2100052203e12490541c044000074407003400a030403801c0c5440c21030364180310b0007810140030300c0200b003111014900d454152410644020050b01d0242040b1142d191b4200680d042195010b00d008801300b001400340325000d40150525403918515903444040180a0320240610001d62040c1081504032031028080c0d41907075140b5588040d40c941c0340c0403c2c1d16445200758007444036040941404d01c0200b60105441c8000d86410344082460388a000c1ca1925100304000e801891000119107120007041d50380240007128021280302052100c40841c00040780300e206c8100c2c002030303010043e04030410035001c000c2c5d511603144001d03203420f041a91034950b4400703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 487545071 1250 487543821 487543829
    0x4060303050c100c080103060e03210a0f02160627080705070504020a050f0307180f0503060108061005090903040b040f05190f09020f0d0608010e060a0219080a0e07 72
    0x504003182c51101c20030104459410351004280510200500340400350103c2e00601001d0495034036410300840710b8400304111080c0d01c0702940010003200401c142c440c40480d0548544014505080810440350120b00a1301c01d524040d034090300007143c165031034070000c10110040c030203400d45c402540f10810400c1c140d01c02907a402000c19941c0c13502d81c1d14141c5d06280094201611452042c0141144164444180c1b00e2846207080015501c0c1c80b1800140c0d402d68180e00c2d0f60300403c0301c000d00810340324120000001201c81c1901107450503602c5201035a20780000301d5800001034456482041a403800c241540d4202001c002640d01e40340e103071207101505600c140c210344014050380c2805c12141c24280000408c845410000041c213904016100d07012108611519031a55004a031081d82c840ca030307400311900001c1c884420007071184d9a07041540039002d01310396a0341758068200045c1c041711450085404415940300a40002842d030001503c07103c0c005840b0006561740c48030b610142c0c610400c00d00b4060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 487546321 1250 487545071 487545077
    0xf061421032a0105010f121b090c020f0c1c1e03020c0f01080f0403231206090f04050c0d150203040507050a05010f1e03150608010614030402011d03030904060303 71
    0x39007407900c0e81110700298942e02c980c09070303d043c0041128500070800300050703c50024400d0b5150300d00b8286030321645001c240010070724940c40b400040c154001e03440b094000c441502980c0250f0810459a41c0f6030403000c080a4001d0500e60341d08806602110750400d5507481a50311a201401c030101156503010071460071809a441980c212100385460342d02c04070349a4003460500b44c03500d000c030310700c580030b51020b0b000605001444001046204142243d41c5e00a40e4040840392903904803c0b00040d06a416505a40980203990200d11070040500b401485590070800038005440314070203210000c22504070030780307643c0c020404a005d80c10b1140001c43c0a82d0040d40184003040c144410041400c0d49944a1414851190504004a60801440d9415101c060f100401c0310040d100154080c01e84000c0004d0a140701c1d05001c00c059800c5140b60341a100b0070369840d00b0707840d021001050507200030780d0040e0100e42c950000c22400d001d00707800c40c0000e0902400781c074100070394003000c10140d581c3c2d60012004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 487547571 1250 487546321 487546357
    0x8040e071701090203150904261207030c021f0603020a151d0a06080c0d020406120501080c1e0d1709040e010204030f02130204030b07120f06142103 65
    0x508040e11071854054a00c0c003d0071803650822885d5044a1442c4002840c001c1620500190501022030061490403082014041c0d440d1000c0030032078034540c440952482c0812201000c50101c91180c800e42d049288203400400d810707807c82d03030000010000751041005580d122040880180c036003c4101c401041180800001c0c007030040c0015000d0481980100c200c108611090009036540c42d01c4982102c2d140d00b45141c031900d800882000d03034031405401e020002d00010300003a07229484100b5910f80007a0005c100b0103a42c80300040f40d202e1a0164440354000c03070301c0d000c0341041c0103040c40703090512400614130002a070301503498054a0340d0600201e0807041307000c44c010226080a00a00301e2840041008526050555603000c00c4c42100503000b070300840300c08410740c003101c0300e44c0c0c116009150414904091440c21410041449110201e00d074400c60804d050303007081c1702c2c980c0a08010745034030280c111a080c4080302404068401107211611140241700080c252071010b1004113140d210341040c1d030007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 487548821 1250 487547571 487547597
    0x2070c03030320030604020a05090d0b0402010807020f030a030203060d02040e0d03110301050d170f0d1d011506030c0c0b150f1801031509062409060803031308040e07 73
    0x202c0d2070882820480840c80c0c681c3e200444080c10489611240481c2c00503100c04c02c0510448150003094801e81c1c000c405410843d043c0702c00300301202d200d07034400da036510401d507034102c0d0403615a009015020f04580c000d00a8054043c0a500656030212002e013980004030700302e400150a4841001c1101e80a42004810b49091a40350142840703038540e19924910b15450100404e560441050700540412007890503520000500b07421078038201301d0b26041503120004000303010b00820307418503070b18a403520203c03180c0c02c0f10f2418065054000303031306640382d101140303413000650140c06a00c43d1841001005425200010b800c54070791805000b412400784000002c01c03040c401100b003004201885076030000030040780d61501c440b61905581e0f011302c0790f26641404007151405400d103c00020042410b205032031200764507010460086c6003566040d100da9640d039806800460b04540a030121641080000070b000350625040784101512860b01ca6107056501c00e65003070030400685807500021210b030380c40301e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 487550071 1250 487548821 487548827
    0xc02070602030f16030201022205010e120316030e13140a2901031401081c08070c0f021302040b0d14100e04020f15090a0e060a03032102070c0303 64
    0x11000e04500e000070740c9442e45010143c2010f000d12040c0c100400e00c0c00e01800308240c401c1d01580d0480520000910310b011188420302c00e00d42041c02082d0000c1c00c6500d4103017480c50704a90b8031100c1c000007401b441c42c102d0b41c0c1860001402414000f0b40c203108006020f80e003181c0301d03400d81e80650541c0312000204103464698141d00490050070040f481402c01c498880c031559081d046070886501c205004c04002c50800058000c3c0440f440c0d08001042c0c45000060340c1500400c60a00e034010680c8580040c0c01c1030348040c2c2d407032801698503400284070b0080201c00190b030040c0c4401001d0001301150a11064115100181c0c0d20a8205d01000f0b007011441c49281d100038050020780c40c854181c4020075103400c03c021500b84985124400c06030810102150540d120740441a01600001c1c1201c1d01920100480b00090ba00c07120125018030407052002803440d80503100719004a4004100c0b403011403a42c0c904582c5d01c5d10340010100c01030300101406801c10740e544020095284119200c800551a5007009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 487551321 1250 487550071 487550083
    0x20d060f09141b06040627050a030b0702160b0f0d2c0709060305060609190f05060a0f08030a211404020a06020c221410030b0601021902010507020103140a0c02 70
    0x70f540150018031061000581003042652843ca86079a4001525481d41080c5084070b1075a00c180d0700208070700f5010050244144e8140d12a001c41d80031514601ea10240d10034120442e407241c070284010900808000700c00c070300010031080c0a108808641841c1502c4460716001031702a030b9940401140f890300d01070300020301c00280140196401009054996107604e0345801e00108540d2260000500003240341c4615421a4a0b500030344000304428140031150700b004000c10365070709102d00113070311001511140003c0c00e58180d0384040041c508003141c40382c06849205010680e00d007090100440c140c00c4550b58031034400f8030010700e000b40d0a0780c140360050000d4102c980e004542107400110940452f42c0b9038a85990755603d0407241e42040c107420200502c020070040c00b80b800350880c1c00d014412110481e10081090340d0048460340020380301d00005a80e00c030b401000f1030500140d00300d0300074055802080540240ca00606020405120402c01d807544080226480d4505503500d00101012560400031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 487552571 1250 487551321 487551373
    0xe0c0414150d1e0501050f0c0405011418130207030f030e1504020307230f0613090504050102090904210201060503070b0c01020c030f1c09020d060f0914 67
    0xaa00014200301e0984001a244031040a000e41d4214455a08002c915031110950001d4030300c5400103100d503071519501034803090310b4010712034052501003060103211400701d40441320161034426401c1141800c0b00942e400135408248811038221000525860f22400d100180c0400080165a2042841c002d0300304880c0ca1168030400d45810f045000810740002c01c9044242000d18030000c5a50341d10019140c202d60343c0120110700000c044007030354007900c100040390803842101c0c601c0d031080802003441000d005d014001c08100c280c05104000f00c0750540d0099070020702840000d468410400003040c4090000d5170215281044901d14210048006900b0b0744401c1003403000384221482d120003c0e5490302d40e4002e000c0318031400980d1100090095040b02d5001d0b211038203603502d440700e210444804e40c1001115814214070680044d064044038403c8101e165402071010401c120355807170380c40007403030b0f05031403904c0c031a035505c9406000c10a01500681041c2d000e8000345100b00110226440008105607 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 487553821 1250 487552571 487552601
    0x1706010f090515131b020706170c160515040809010305150a0b0d0e0a030e1009080a0609060e060406050603010b040902100507020a0b0f070c120201020c040b03100e0c04 74
    0x30500c1200070f0b0549280544030421652643c0d06207000540d10000d00c281c00e20001100e10000212440ea03030041401021644182ca1300caa03605101458001e540100b1541d29103803260400c51036420303c1381c80703c205d42580d0144040361650440c0144400c00090151020380d90b5071000700310b0074419a414003031503502000b10f0302440782142c55000031912450b40d078028009503000102d401d40082d50150303c5081d150a144007114001c1c0110309014040c7c00820400034020b1114009142c08140a040c2c410308656a41e0001d1174400e1280d203801004003540d29084401c0c07a1540718000016000b0040c642c01030740144400075250400707900309801c449072000e009003d10700300500e403005a50380440c2c120032102242070903923581040d48000340350040c0b6034103d000b80350008580e810080e50000c3c080c05000748604a00d98000381c550046c81e0343c1c03034030307110000340140d111540004841c106604102d0808401600b01c1c0c449080510991041d10928a5050031a602c0541204010329160040304202e4030080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 487555071 1250 487553821 487553831
    0xc1c050f360d020907110102031509061002060403050304031e0207081e0a080d2d050105221a0618040b0901030b010902070c0b1b15090d0e0a1706010f09 67
    0x41c08645052455800070f40704455640c0028180e0b40243c1e200c40e80c1d0304100000719681c0c03401410280384440e1380c5400c94000d843d020b00003901818562420310f400a000c1e00204025992a81c04a4095200810031010400340c1401c0302c20350141050200401e07503050f00948000341c01c1100f07491600795040d60001400c05805070340751103208045620031100d0341000c0300558a451940c5540c025107003030701d1103030000c00400004199440b01410924609160844188940d0760781d042001280380c0c0c8150380e92113454411a600304500f049911a00c103c40d0f034040f40c078000f0001000001c500d5009101c9406002204488249007131601e4810429559012505100c0d65411a104d81c5130002c0305000d00800c0a90004040081c0080702e454040103051501e55079995141380e5410161000d20310f000382c0c41911402d02546004c81e44c450300c0901c540c850500070103103550811000c079000c49254a8558010b100440f001c02c0400c1c814034025004030051000b44440e52501c1208148c8401c0b44d031080b0100d510304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 487556321 1250 487555071 487555177
    0x403030504120323101205060417120105091522050108030a0906140903010c050909060108010e0a090c030b01091b091d04020301022101050a05060c1c050f 68
    0x11303402110120010401c0d0940326940c4000d4041024001d41001e2042044800c08604000000543c903200da84034059000010030240018900d60056440c4c0ca003210144400502050500f000c2c1c00d64044403000c0e2150b584d2415001068880c0d400030300d0142c0f044c0b24440f018400a010340250381c0104126002549090609180200081020b004010821028481e203400308050003050310036000008008001038222110042c046030f12080b080c902910f10000080c1241d8056415141200d4040303800c66419958901802d000380030450046034800b20300b981c0400840d070910001e0f4042c0091b502c00103070034182c4503901d00d071414000d0700380b0f0204000c0c60f00500c40092103401c40d00101c880c10048246545071440082d0180c060061045500b0714182c1500283c0c448252109040710000d884140d4103030f844906000151088604c100c02c1548000c84446c40b0444480c800301802040e440c0c154145102c1807042d5003a680182d0040c5a80c4100e174001e62100780c3c011100000002001100d040e164902d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 487557571 1250 487556321 487556351
    0x1a07030b0f0d020f03070806010806060a080606090a1107080c030a020118150f1b120c0e3d091a032503060f030303090c170304030b070c0b04030305041203 68
    0x40b080c0003401680700c121250041e840411400010344088010703a60303036685030613609580ba04103c40485c4034a941c500002030707203100451910701805002c2d00c0d00c05190b6407640014003a068881080002820400c01c5401051304440500184007040d0099a03403a102d05a000307080d101c42d4019881e84015000956000842c0001564100c03c642c0c0c0021480c0180726481d0001842040c4100401c5510380a9000c000b50380915592442c00c02c9610400c1520f0708000d040740d0141d102007103c0c1c2c00400e400409004a40041e204c01309403c89204900d01c0c080c4000300700781010529812032004101c60260600c01142003288010b0000c2004ca6082d00314500081c2400001ca10f508004000e50036040c0fa28209078465041107000c0c26841800522099580c80c008000300b140c00d50030b6030075029005010854a0180481e0202c54503c48010360401d801d54a0b1200080c0000d040103081c000e00c1291003002480409041d881240030383c4000500e45000c0c209090301b044403150400405240030701500d52094 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 487558821 1250 487557571 487557589
    0x1c06030b160c0b0a20070212060c09060d0b04110d050a0c1e2f0105091b01080703180f0308132f0a1e090204051503070c1a07030b0f 58
    0x5007107140340b642910b64140c9040140b44102c04030214015a05c0701303514410b0010b00a002d854801c1c2d4440c40c0000ca0a0941d03521060261401102210100b082c0c3d0303050302d0050b0240c04400a1000e0014020441360700003411110043c40318500d400c0049195070001e8814429581c4c080b40c035030b005228681c0e2951004006d1308204400c000c008456400e8000d540d8425110800081d01c0740c00070791700c84022010051070600520408418a40c01d000004815220100e1403405405450008104442e481001521400c1c801001241019035880f000c0101e4005800200c00060040c0032950344081d050400801c01a8001d02c00d80d0010290b110090008628400b80780b0707900217050107032440443d040341c0041c3d0010000c4026a115904010102d4011140c05042d075000c0004601074030305a03035810700c40c01a0f015904c1425407222000f0300311444008030100947d4082c0451400c4c0303581d8590350b551006800e444d00d82e00c049260307a240030400800e0b0148203041a604044800d030700b403d80d04100054281d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 487560071 1250 487558821 487558823
    0x1020a02070603050c09090a0e100908120702100606030603020a0b130b1c050c0d0b0d080d050a020f0a0e0907031a100c20030d0518040e031c06030b160c 67
    0xd84d03a8800200c40711101c5059a150000041940b6424205050000c0140080010555460290b0240c030440a540d034810402c5a6602018940c00c142da10503c001034000000c1c43c010550041301110383c5166043e100e0728010b480b4a88002483e113085005000d00301c1c41540082e15121403c0060491614800858404840910204641d14014000540030645031500216486401e2600b03100c043c11220b809007402982c0f0b0102003100b500d02e00e0130419080000701028041c88020019015540c02640005900400e001e10144c038002601c0c84104866000e03004100003c3c0c0e094014441d58900403840c240c0000c1c641ca0207100100d81020741542c0841e1041c1681e210380790680003844094007441301591032507048014500b150841900000001a00a410520a0003241b5420911600a01c1038440404909180f81c01d40c44000c41403000802c4014660501d03803009200176480c107e911108940450065074003c50003a15600d4a248000e901600c08051082c84483d01691203610101c90892a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 487561321 1250 487560071 487560077
    0x3171e0a051b030f041d0703020702090c03071403011d010501020705060d090c0504110c010506220b0a0b181c1e0614010906150e01020615030f031201080f01020a020706 74
    0xc84903219024074600c84c0340400303101000c0c00310300000c000b400c1c04081017000140c80c1c060750096a4182d81102280b007078a000035880012600400c181071700410103180d0150301030820580c0c3c2e1203903808400558000340e01c641203424804030018590341c0300c103540d02d006090070b000a00c24a8200f0700003500e640102400c0343c481c0c1e40c2e220961000c1c0050500303224001c0c180a0410000700c00316120a01603a484a41842c070a5820800801d60b181020b0000c5025404100402c10010701100c5003a00500702c621102d561010820341d02080d0802e2500042c00b4480d10010003000c00d0a9034400d0110107214981560200c442080720207010860190b0000311525011031000748130600c030719012009042103156104140080300c008280c00a031a81f241080d64042d04044101c4044140304803000d4807083c0300280181c2141010581c07858032a14041d02040c4018280c0d070900901c2c9000c2451600101d440b80c01641c1c5910041000c024140011004800c8120096180660000340699520710301c3c40380800b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 487562571 1250 487561321 487561357
    0x60310110a0c05071a130b040b1c0212090606030d080f0115020f01020c0307060b1905040f0209030a0c0f0b040b031504091a0f100501020a0b060a03171e0a05 69
    0x10040180304681c041d017514030740020381000e071134421601c54114250510344018079a41c04200c1c5242d0409503000c50b807145003ea403419164101c500c1444030180102c0420030340902044d1002d4407001d01c0d20384a901c808000308114540304040501e403000d00d56011003402846014807440340c205042d40c9054407070108015422000701d00301285410080d1501c2e481d1548089141320080402100502c580c900882041c01864400810000c04c2c2d548110440300c040f20400d41003090742030503001540ca5400400d070050071b104000300403038108169144110f6241410300d030700740450076208074580050319480341d4060405003480150341140c8070180112894010b02d1010102551715504011000ca902c002c03141400c802c0303450303101c0c04010300352000340000e07000400103810400480840404c681e01640140b0108031142c581100f0310030080c104a402c40803008022000c01d500d0b001c5a10304544900a0030b0383c03018003072104204038036807200809500f1420002c00d02085d91100980e1075002180c0d210b01d003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 487563821 1250 487562571 487562573
    0x1050a18020a0c0506040605040b0601030209031b150f0c010608030c1e1009080a031d0c010c06020c190b090c0f090601031b0903030306050306010b1204050c0d0605060310110a0c 78
    0x42c03c4109240003c04174825035080004004084d04801d005500c5840c608040740c0b10b80c00150160300800c0e0401b5015072101c110b030b24030800140c40c0d214940001420519000092070240710a981c0300040d45140088000742e41c1948000034403420b4001c1443d000954140701e0769503d503a442d0060040b00191403642c4440c03110781c1500910416201010140d01004800d00380c1c581014190007101244010a14007208107110249401690b96001e0700e040180444410110054408440e0140f043d905690700b4003642a070454100031038001d0f00f450760505003020b002c0d80340203001c01000510400c800d4100316040e8034103458400754242d9041d0f040722404010780c1d41c0c9004070001d148505815070184032041c800b044150300910004244c0307000e60790a00282c1c4d00c4901741a0307228000c0c455a04182c0e0100048005400340582041c3c006106201784c03100011800700044005501c014140d0f0310382d0313071081804010b10302044003a0052000030010701c41d0440e40c01c08020140074070a483d4091000c4201000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 487565071 1250 487563821 487563827
    0x5060703090e070f0e0d081912090b0906150907030b0112151415040510260a052d130203060c071b081b040204150e040501050a18020a 59
    0x3001601d103100180c2c2d181e00d06104000c2010b820303040d480c40418000850b503046801c09a003601c0034241c0050b65a40380c0300c03a0749000c000c10300c2011641001c0002c106090349501145001d80d0301544c0c0114450b000d54145003500b64186038001c0d10115566508400e40000307a21462107041e8010500c0c100000d1710307862070340147ca04091402c21445800c1c0340c40e0800d0307601080c049241081c1c6075807154420a002180382448040103011040a0b40c201041c44204450314000021a0320000700345010000d0307900180111191138000c4201d9841d8089000421a900d045442155480404c01c003a075801010425001ca84105040c6036682000382e406001480c668042c1d186006601d9024040341d8a51800d03c04551190700142802c8030101e00400c0c0074540500c0c070102e14020749240c0400307801ca59008001611810821103a0103401c00e0f0280300c00501c40d020884035410b000301507291001e1055187c42048121130050f004a031040c100510705005041492400e01d140800c1000c00581e6041c0b01703c015 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 487566321 1250 487565071 487565087
    0xb09190c0c1505180309060d09020d080304031116030f120522030210020708150a110a050d060b03070c0b13050105041a07021b130b0621090102040f05060703 69
    0x6030404900304840849042c03507901152003259102043c07070034032a1142166403030380301d00c00740c0c590301c4182803112440b0043d05500003001c040c401081e421007100340c0d0f0354007003158108590035004240298401005404e00340440040c404000c26052181d9007075550700441c8118180c000f0704641c4034442540856070091045a41c9060124413000440012180300c40780381a0b580000c0740242010110010590300004148040d1075a44000c0d2a00c40d2008846014031a4000e044200a80e203818484032080b035550b00030048920160784540d41d45c890341c248481a91025408904200c1041041189003030f1b2091a180340d8a40c01583c00e0301917181d03009803000e01d007046ca60140140d481e00013030000b00043c0701082c90108401c40000501c0340d4401743c0503030712144914811103802450708070355000b502e0035428031107a450030700c4000a02c4000070f00200700a60030031010b0066600b00ca07082039a003c40b05d50140c5034000d07040c1c0003d5190509040d140340000781140302d8180103280120700e00781054012844 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 487567571 1250 487566321 487566323
    0x702090a1404030c030927150b1b0705060c03030103030f030219080708070c0c061103090a0f050a0b0309100b190806010602151302060f070b0f0103021206070804030e0a0f17010b09190c0c 82
    0x607441d800815032b240505c5544201201c1244a0b0140c0040e043c1011400c6c0d80c920034070710015500f96860b6850980c0c03400068005002010790801400d500100002c2c41c0942d160f01076035440040707142000015106000c0680704005024a0080c0340d40010802d01a540989044d444c00c1091382403a54a01e40c03460180c0110300780d0001c0842c40224028803e0780e01c140844400300c500d020344d150741e0320022840d84030540301026150043d00e26216000c0107034028442280c2d000d00214802c8007405c036912101010f40e00b20642c0340c2c2000c0010812658100030800980c400c03655200c42a040500e0407030805407030030380d000b4000c4601207941c1000b4102c210075240082d4100700074003928900201d101c00e2400d0240400ca2181c0e410700c5640c0159034002132450300c921015143c0489039100c80d01d066030602c0c502c440b06544030010b40340c042116001704030758200414401850100006051030100e003594841210940070b2100302c0b08110041d283c0f03050306c2c501c4a4081400007070606015030308a4004000c1c0d40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 487568821 1250 487567571 487567589
    0x412020c03030414010212040b040521030c0106081b0f0d06021e040f14010210090204110f0d05060f01080703020a1e020f011505060702090a1404030c03092715 70
    0x2400144801804e02c14a42c912000d03401c0c0d8510303c02e4010140038500a0340150b50741c280c8148410311683c1003016041240040c2c0030300088803201444000341c0783d5444003030b911803165128401040741c0001040740f03840d2401d0400b2540490390a020208100d9000c2042c100d101e1010748810a041c8000c540c110b40914034000c00303030366480300f883c2c2101d41c2d03075440351040c13010801c1000c00004480b05042d8904021040503070203040403500d00c0d1581805410f2414050b640181e9550404482c00d4810700140501c070441c00d80283c48000d00700380c040864600074202401403001c4100d18640e60791041807140c0c84941802c0050316001c16082c2100c03802d01340d051802102e2000660b03480360503000100140b0201c0b001b80240850f01c5d9aa00036884850580300700754102c002400712500620b84951a03d030b00200994000a060b01c0902003c041e4240c103440c107401044805042d60140f69108001801034034007030102080d2204030111401d90604400c402400749591001c90102540c03418400070000d00c0746103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 487570071 1250 487568821 487568827
    0x904110c0d0905010c0b0f091005090a1401051003020d151505041a012115030b040b070f0203030a0f180302010e0115080a02100210022811060412020c0303 68
    0x12150340e5454035024006800328840e040000340540c4681000c3c044580e01803070a2055844e0703081049100309019002e1030943c0203000380305c83c910b00f00f40700c0c0c14032448510000300711701c2401d07040c0907020009c0b4500180c0942d041c40e007041504c00c0008003000271039a054504410382045418640144400e143d80a05880d003081040002030400c82040002d6403000c0300e0411041e5810369a26001c0c4107a070708181c0c0411100081c0c00c1e5000e000c8003e0680103140880d0200d141c2d50942c0b12000240703443e030421610b444004044c401440104680d0690008450400445601d140000a952400000c1884074a2034440c84000c1c0c0075010350300846074080b80318402c26010f4a980c074011340a841401d1444200b90701e0001004000c0420b030b0000f400300d40010020344100245074003806007900000c100d00c0154401d10b007980c09441007610007403c0202104410001d074071401038100a151140c5030303800c010452000110180c20f5004036005d80c000350300807040718407010100030580c10328100283c0c0303e500d40808 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 487571321 1250 487570071 487570087
    0x12050a06090b01180302090705040315020403050c06040b03041104020f030a0f0f0b01140307020114011502060c180d020307051003020309010c1e050307020a02060705010c03050604061505090411 85
    0x1500440140c03200030900b40004448400110748a42c0319400c411051103d08000300050f0410709000d5030056000c1c50513610f060340301e45514480960100188034203590008040092150604c4440e03690301c0d003200e50900d40761605040c40d1190001500260099840308a41c1c800c558440c2d0449a000001c15450740d1130b868882e000d20014041403110300303d6641041e200c4c1000c03900d180b058003500c9074140c50350708001e03c040910300c89a810080120041d50360394201b08a54190101c045402000b000f89442d800c04070410009050480181807445224828011507020004032440030640e07035815a1080c0d144411400043d1030100e00341c2c002504094081c080340c05a036499002144603131211030090019450701d0300e0488400d0324100c00c0c03014001c0b0f003082c45c0080c0362050300150340001035441250401a0180c0008a15504c050001c0b03a5580d55070924800180e090b0003003039485071048038104000d6240001c80d03214000754500039400c1000c00110801103075925440440d19861008082d52190f400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 487572571 1250 487571321 487571341
    0x3051b04181a01080102030601090308070c050312030a0c09361d12090105160303140f0a0509060105130f090606030b01030b090c030a0f050307050d03021c0b0a060804031205 76
    0x14041c180355002d000800801c00110500072240a07074010394a8101040c0b4549071740f40c55411280044030416031204001426035010040101000e548600702c1c1d0b84c90501c1041d08084403e0032441c9000c0c8030190400308603107080840b004402103a45004155003002844040d690310302c01c04111403400e441d00414042e10780500d0304030f41600f00007030b007140c02c80b8164900c01d64450040c0c3c0d4074103001480412201c04000326202d032080d0010711030306001c61000024040c00000740350484080041000351010007102d4481c5000b0b103038028100d8000381200703504202c0429081111040700000c01503c0b0aa00000701015901a08100d60803100410001c1e0702e030319120445580a201c02c0e41c84212035004108044400304441105150040c001d2403094202d6079408110039440c50b085e5028001800010b0228500340002c08900c4030b1030341c1c0140d4460b55081c400e040201c0700c1c0c500031019490140002001c0d02e510383c0e020300365615802c108200d56541d26033110480000410124200c3c10a010b22940481c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 487573821 1250 487572571 487572593
    0x120a1202070914010f0303031d030d090c091802040e030c190506100e013615120317091c2604120309020105190c0c0e0103051b0418 58
    0x410100c1800f60b280d0b000c0c080b804809084c0185e0503003c0500d442040004c1c025400000083c000402845064807180031160954102045400510761503a80c407004006028112101400b1402410880c050041c103c412115803580e40003030055a64058490b0481d8040080d590b042041008854550a81e4a400740d415450b902003254248182c8000c16020700c02c5a000005543c8840c50b0007802d68030700301026894211000701856650011001024260100c500700d202180c2400804241020030811444031180182d000780b4140c200e10f00340d46e00180d401007480c2c000c00c0d082404140c0c0c0703403280500c01d03040030480f4415048001101008800700c5d0f0f04494100b10540d1106820309052040c0e4240c180100d100b2900102420101c42c0d0804e0154060360041201c2070040c0340550a0200a414840c500340b40449040c010a40e0260b80704e0411100122500c05824481c0030142c41e545190345d615620100000000a12040c03921007032034984917640003545c0c00011080d4254040c42d10309007025050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 487575071 1250 487573821 487573829
    0x2071a0409050a050c0d11040302040c0c020a081c0e0a0b0703110c03031608031315060503071401022a0a030303050108100b0f01030c140706020a180303020705120a120207 75
    0x2d003010000340308000e8512030b552051415800092a1803000342400008190102521070141018800440541c40b2841452001c001c240c5401000510030b0042040400f1150f10240e02a48031102403541c0c00c00309801c0004048890812220450788500000c43c2c034105c0350030070541c50078040f860505156001c5a100f81c000040d100750b5a680d24110241912481910840301446e02c5c070040140c00103064000469215035404c1e90703019482a96603c2100303400c465401c04000390380b80c04050007249018460f07000140700c2400140312440254001035181c902d4540c528030789007103082890203120480200d40c000b9090043c481c0b100c141c0c0340e180207002000280a4a4014413581038a480050708501c60302d800700c84000c05145081170000c0044001d001964500c80030030840b4a000a010f0400703801425655202d58809a1556908907004005070859411074203403038010842000440d80124901c0141c410650f44040b80c240700a01103440d000d006a00102964015508141d0843e40801c008040d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 487576321 1250 487575071 487575089
    0xd02180f10030c03032106090608071d012106050c071e0b1b0c03041715010e0703200c0a03021e0312070e060c0706080f0f1602071a04 59
    0x503440740c07a4203180701940d40c0401042c003641c225003800420301a507107104400c00d03a5000201c51300c44010203402519500e80c010a552602c030302040c810b104040c440ca0010704110104c0787c2800707100001c079036051132061040c52444c4c1442d007164214540818440030005800041c240040c2c1465035030240c81d40d00c806001c0d9450317084440448440221031120220700c5070043c07003d4680b91110180138445030100c941c040c1c0c140b031341045455040002880580b005196007410301e01407001562070350341001040c2c5624206801f0790801806111050403545400c540c9078a000600b01c1e000c0b01800b0400c24414064070f0650034007080c0c000303c8020008580c04618802e500b9074a01c0c505213035006207800b09100d40384919820074403004001e440d0800030240e005644d41b51030040701118a02041c0583e0080d0a1184140c01079070307060154503000700080d0b400507507018141c285882d203080307608460039019007844000d6641c5e002000303100e0310070413010b005028441400705c020440d0720035071411580b00d407144403070b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 487577571 1250 487576321 487576351
    0x50d0b060f010c0201023703080a0e030a05040b03130c03150b030115050d08041509080d1b0807020a03020405090a02150a020a080d0e0304060c0201110604050c0402090d0218 76
    0x1442d4418001c20b0b1041da03043c4c000f004103441c42c410101420030065190b6000e076440030307000c0d07540010740b94580340300d40d0194075000c070f1504080800310155440040c1000c1e50340d00c100501007000d0740c007004960896500c400155241d0310380714401c1da6402640b60010b00528140c40b008014004842c0008051a10359401002a5450203081c5403d80390cc00321150005c450160040207142480b0030b04e481c8141c49148580e24150320341d0208002c00802100340e80026055540500c4544001c0060303150080c1c00782003020745602101160980c40c03c0c101001059980049203500c00c54032400035020180d51300800500051828402e500e41c0c039414014142d1150015180300000c103440341c01242c0300f00029a01030014920f035a00c400300d241d80a040400041c0d0790380c0d00d01b0361008900740040e01c00303842c0d0340d42e40c0c2005058500004200040c48032410809030007090030b01c00003601c0051a40301c0103a00f501c0c09030300c413103044001600100c03070000060f4005000e0340a4a080c0c5201d54003061054007031170590302c0703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 487578821 1250 487577571 487577599
    0x90607030e1f11062403030702130509070614271008090114060303040e070210020415080705210702031c0501090e0316020112022116031104031b050d0b06 68
    0x561100141c680010070f01180e90b44240d85c032003142c4540c161150140c1280e14002d403560201c4c404000084441c2210303580c030810303c412500c090245400078000313890700d8446568800705e084501d104d01003e03141080c4038a02c1c2c3d2401040d06c4d1040e01c885200c018030106400801030030281c20a102116003004c0c551a02400c0702c620400c10745824021500030b401141480d0420101c0c1c1229800544200c0561003407102406889400d4001000640307050101c0c4c0c0e000c2070700910082d00f441c0b0094418010310500b88840d0243d2107841301d10501d1110800310340c1c103007a03c40c1c0304d0682c03c503c1ba103013a4001054006002c00000c0c1b00302d8000390704807040c0d07171420010440409040394032401044409000c049200307040a0141d0303ca031903ea140711030b10281c018039041e4401e04c1d510000005c4500001c5010a080030000711032000302084c0070303144103410103014541e400858001c0798895400014004c034243e1040c06907000d100d0f820140030b40340207080c0d00c1d0300c603900e030800156800c806c44c2c20318481c010b481c504038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 487580071 1250 487578821 487578823
    0x62f0a120e1e07060c0c1707030b01170c06190c0206041203030b03060a020f040605030402130c022d0a0f0609050601061e140301050127061101051308090607030e1f11 73
    0x1c0d07171094110f59088201d609007081c10345035405103004001e6500c20714a010000c110900300541c020184003008004840c404188182001c04c0e618100380310f14002e120300c1e0059070aa1003100c1103404030345800d410001c4244000307042405903801a60701c920442e06080101030709607020003001a002c80441d0016503d000300c02c401ea2041241d03113190200148020081a4000c00c003039a0010b10080170080b040b09500b209030300f01c9520300e00c070740016400355600d681307503000b4640154a0300e030060302c50740078400480c1352143d45c4903440039000b403882da40d80b111041884010f0703104002282c0d020055582c0c0e543e60b640001c0c000d03414075009008803008080140d080364051624481110000b6a201d42140c4c68030006581741c07105100a481c1d840c140103c501d86103440f00200d00301400ba19200e100725100c0000c4d0481c02c46600174010340b440b500c011803450102e0b6000d003c0d1600c090044540070350710f210a1a04441c0381c00d11000e425004111180c49902240507682d0310036000100e9a6005002d0348484512 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 487581321 1250 487580071 487580087
    0x90509010303020a1719030501051e1c030302070203011a0102060a05041505060f151e0f0f070201021005090303061e010c0204021e0304062f0a120e1e0706 68
    0xb000f40c0d000418200000c0c4942480e1040140294021800c2c0741c0d8000d0203060740c050010800001a60b5400107002901d4010801400f0071040003506040c08410b001041c4500704c0e00074540448010904420b04140c402d03011900c416901074028411460b1a980550344043d01c10400e50250041c107000824810072485401e103d5904144a603038401c0e1540481001080080c00e03040d0042c0d010b54003101207031105101c4412152450240a94079045410000598201c902d5042d61400c0b040103d00304120b400d0b0241c48440351600140c0d9654981480181e01d45440c43e2101c0c25031505090410450400120203188184010340b01e0310225000f0f58403003200305408603001c41c0031400c607440120141c1025030241441e51000c603070b402000b0014411506850b00304450071160a5100c0351107841603400b03032640b01404038540d840d0181d98403020030341180b14004e032030b84a8100641c00010b9151005070380c0050000c501c903003061710010108208000031018130b19a0050503489040c1c0001107507072081800d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 487582571 1250 487581321 487581323
    0x110a0506040f020a1d2e03060f0b030601090e0d03020405011b0213020f030108010b010e0603010902090607060c020307060b030c0a090911100f02071a03010e06010215070f0905090103 80
    0x2520141d540c542c2d840c030000140e040181d030040e01040010840211400c0d105030032407441c6252444503d0b0450304010608050042640390181445040a84014980150080c0c0b5400a00401d414038070a02140060a01c00e100c00c4d8184146000040c0c42c50042d03104004003550300c0103a03801e8991f4044160160702c00c5104160000307090110014400c0304480900f04114030050004e04220901c040300030076a000072003d25041c000000040216080902c0360392032900080c20030000542204001a600d408140f045c900c2868002030505880d80c1c54030101e0301003030340c028030410680702d1080000f0741d29084000100d031168503004101d80700d81350000c0e82741340c12640108140500c0e424072501703401824031760000300c0d0341d038442d80709200e1240e94100c606c07043c100441e40d0f502540051900000d150030380550109140300c00c03c804c16000401e1820440f03054640d1a941902c003a01e035400104e107814a000c0e0f0042d88078541c90180035000e5445161000d51005a41e1050ba83c980c0303e40401466001c01e201c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 487583821 1250 487582571 487582573
    0xc020901050103050717090c0306060a06050405010c080405030d0314060a050a140607050a08030709061103041203020f0607081e0105030c040c1e0302033705090703061a01110a05 78
    0x401c81c1c0d612a41001d580010a8035141c03003000c0c8500e80c001c05011050341d010200341c010280c82c1496085c2001926481041100c69941503031405201510700d1185000b02410422a00c5580c018031014200f1a00100400703000c940045d10b80b16001401440e091000801c51102c10000c02c42c28071f0f1040066069400c002c007842881ca2411204010a140c40c0301c0c0103400c03480900558010034810700003500380901070312b0103039a41d2400d0103004000c1d180640000c3c080c00521302c21258001c00001c01e6406603440b0b03014804400c0040d007802e0345050400c03205903407144140d400f0402c0c001d0344214014020900300f041403c0d1707441407444114403600c0c01d00a6580540c0806041c10142c540781e0000c0d08400f0340740c10003864142c600100010340c04940c001040100750000240100c5600081801321050390108119070303840c00700302c2d00101300300c080c1e007148000b0b94407071011502e0540244103800003554040420000c0c1604950381c080c90703440c1d0b8a1014081041c0036126030052601240311400789034807038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 487585071 1250 487583821 487583839
    0x50601030b041a04050624090108090303011a09120f0f07080d0e151204200d24020c0d0909060e07091520010b040b030f030a080a0f060312020d0c02 65
    0x200a100003401c000b040240d00441075284101007c40410301401c0660355101026561810540050328098025005c66071903402007004100600100d0031468100d451401c1d4240d0340e48503507002032080d0600350140c842e00d020300246040a507600040744c0048030003250960340d205968031009a158980b0500b5003000c81c6401c28042d4007884c2189138028410f0306103101e503013000700300b841200d10500202ca0407602c0410920501000041905c04003c42040484249807038141941d10040754005051404444041c2102d80c030310300e28811703019a540750800c04200c5c1c8840e07140b21802481c55803144140504c0e1407a1502c0862000c000b1022648074811035254002081d103440031701100149a0800c0703000b080300e6100e04981c0742c0d42031072242c031517000038500101d0300da95100304000440c0d920341c601074803d500c0215044058030000c42030780d0000c1064248854259618071048010b028629140e0780d05515004000c0100104200b1130002c2c0d02d070375802c031070180c00111000c0e500b480c0201c030082e5101d0900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 487586321 1250 487585071 487585121
    0x10e150402030108071e1e030b060306060d0206070501060e09030a1e05040302120f10091b080613142b11100b1c120e0105090901090903090f030501050601030b04 71
    0x400001403080a041003a403400300e0f070b00d500d8810031042182c41e044c45074811f201c041081c072072000c0840d03412000480203000c040c1404400540c8100c1e0a2400070700480000c2445418400207600160040000c5c05810b2000e1030408a9152254044900344001c203502c150003d00e903003241114081a801c1c6d94817001d20341819902082110540038018185522038500004104081030000c8800b241c1c40f54000f18105405241003002d07078009082005640c0740ea14010000303410000307a0503401070100701d5082c1c5454450b003050980058104020103180c89481c0070300610304e01c07142c421000303c45002c286041c2808658000c0300c001004a0103881a90301110709680d00ca101540312900c08900102006000500145a91201c8071a80c600b80e499000c136140c071060315a0000010490079009180051130421034000003050b24006000d0040560346d20210f040030580104005405032000c440b128000c140c1d00c3c68805c0c00fa00003102e03802d00103030400354107101d035003450300400891401001c8048405400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 487587571 1250 487586321 487586339
    0x70f0503100302091312030915020a0206010524041203081b030601030c1b1103011a091801110f13210b07210203040c06080f010b030c0d0203010e15040203010807 71
    0x160807911700306481003001d03001403200106050513a50300d40f80810010300790304188242d40f0552104d240b01034010407001c1c445607402305965065400440784104600208842040b8440d402c0c00c04148140b000980801c0c5064101d0031951028469510002142d88607080041ca518009520608011303081c008100298002e42048204041c00d01d00803501c00300ba00107003407261403000001e8a802d1a040d0016095080c2801102c07800d1400c10508000d085401000ca070801400904080b0a0307044103016800d07120382034220b045c4c0960640750254403140391020380c0ba45a4405410005281c40c0a0b00002d42d014080311171814070309400e8800910b81450f5124007298100050403041007100c00c203441055109009107403002800b403880b0044e140c1c5024500410315589a0300712900b0310411200b04038114605580c210305581c0c03d02c402c82c2d102d4443c045410010300840c018644802e00100000c0b500e00c038081150b0348610310344410711012954143c103010803803000f80100e21140e00010380038084050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 487588821 1250 487587571 487587589
    0x6050412050c1c06061509090905030408060c04090b030d050f0306040e030a0c0b0907030c0510050906040e04020319030909090503040909080309071d04020d02011701030b070f0503100302 82
    0x4091019200c0d4000e2420002e91800308081c030f142c014038030032a152818041c0138403a0304050142c900b40c0f403801315003803907028141644a1003201891600d6040b1070003041420700c140c50042c0014401c5615a080c98020310302035401078003420740d110b0701c1d2442942d001e1030002445000c080440e100d40d494040100312151807540014422508151034901003002c83d40200010000111030786d9810321140140d2801c1c03000c1c0200540302801c10b5000400038008125017010020880750101c03460548070b0340040c015180b500450800d0381c4c1c8201c0c0407800141c02c0d00c2002d142c5100707038402c07000e440b8904010124100e01d405042e1003e800910300d40c4080c00000d91643c0000580c6000e14112400c0c1660781840c401075411400e07003215400300c04414409115001c02911b00900402100e0350030048800d02e02c020074041c02000a4442c5840c2403596040d64003424807005541030407614160b603580c403801c142d98001001e981d0f000010306c0d183c2c00200301700c1c071420640c0e01910b075a1021140c1d0a1440d0200801c1e01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 487589928 1107 487588821 487588823
    0x60703020d140609181005280c120c030e06091501051228080a0c0309050d02090f0a11070605071403150103050c04080106090b150406050412 62
    0xda4903d4041a40603445c8100011890500c4144500d88013404040b085244e01c0c000601050a4107040d140c0c2042c1038100d40252000c007000048001c980400380681c0000704000c0641d0300400d4a500100000714640c500810008800c448881c20100d003602c0500c00b940c400f140c05800e00c0c1c114851140140303c03c0742c02d241600ca4100c0c520703403528000d400b004c080003401040481c100a02e88100074115400030002ea8440303100c9103000e4094003414205901051468000081070318103650070b4503035140d0103040502d90380c90720751240107210000f80035883d2080e1103492482889038940c0240c4080d030302440010510381441003015007400241840d45805200030020000c605008200000c546102882e00242c1c5a8a07165156030034010b0790016610b55091000c0014400544d4110b46112841107411117800c200c403581980e4079114a1040300c020400610080010010a441500c403007 = true := by decide +kernel

theorem cover : BRFrame.Cov 487410071 487589928 := by
  have h0 := BRFrame.cov_init 487410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 487410071 ≤ n) (h2 : n < 487589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
