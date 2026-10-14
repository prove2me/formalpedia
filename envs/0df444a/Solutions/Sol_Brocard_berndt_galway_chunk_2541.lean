-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2541
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:01:15.613338+00:00
-- url     : https://prove2.me/submissions/c8cfc75a-106a-438c-9b7e-70c8026ed2e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 456834532 ≤ n < 457014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 456835782 1250 456834532 456834559
    0x108150c07141f0903020c030102130605071109040305030a0f02090a0e09070306060611061602030a1101180f05061510110c0315090d020c0105040b21041203060b090d02 74
    0x40c0341803044a1003102d1503240401220203402181d1009913903520035403c0d038001e071158404142c241c2c094803003010694441c581c000c1090358050001004402d1040d113820078511082c10004540d41d60886090700840c20000c01c01451403c01e02c5552006129030f0790450500388008003050840811307011b810516240300c03001c035481d40c401700102c00c001c0da030204007440403071780703514000304620820948200c0600c2607402084110300e41c00c3d01044040c0700c90f4001c5040845500c801c0b640c0131210184550302c2c0d580c41c294015564880007420fa0320500904180d5a103010304d2806a141060041c40460314003940f4058071300a1360391085042103803185240c20101009160715203410101c801103415414421407404c00c0341c001d000030540d403294900c041582c02c92600040140d881748522a011030000d00c041005101d01c126080240c188900d14610a512161210300c081e510003070240c0d8165030000980305170b130442c1c99060103402d000d400b40c0132040341048481c4020a00784250000b000344220242c40c0c502 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 456837032 1250 456835782 456835823
    0x1d040f090c09021801170c1612030b10021f02091c060c0324030609030e09070e040e0d08010e07050705031303061a06120c04050301140108150c07 64
    0x891007608038000751291a03440400790025802041d0044a96500e240e5003419580500524440f58003100808400c0f551142814481e65000fa4802c0108080c10500d40e00411406d20240c6001c45440d10300085040c0003d04202e03201c5607126001c0210350000d843d1102c2d04642c0b07d00b0350080802c02c3c1300541c45944d00e50010720002c0b0f0303403440000210b484400e040284440d0f900b0000c29080c0302d4600f005503c0e84145001401c04142c00c403010030f100030031410030005015511a0345400e0191401c60a41c0304980000b4610b15010350303806000440104100700103103090300c1001080601c80c0002d00b85000014805000a01d05210b5500810048400103000d140601b049802c00340d44002581e9560717014821109000b249400143d0310070786080641401042d41c01041c49601100904c40c5007069001111907010660051508021040c14400050b06841c00d016984110201488440e0a90b06002e84e040c50031410304111759008080d0030510a0003041002141da91980100b10900c460106080b03c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 456838282 1250 456837032 456837041
    0x5120412090b0301062f010e031b060108250e0708042130060f170102030103030c06151806030b06150702011d150408100c0203030115020a061401050306071d040f 71
    0x11030115401d2441123001400003000600818030290b1146511030606511980e0315070007406514083cad07000c41e040b981207141d0034580000c1003a8085010b41080e440750071202c206041a0340d00c2e00898400400d100400603840c11048500c040d092400c2905910010020100c1346450751004010000f1092044501c080c2c8640102e400c0041c081400030a64030741b26000b0106244c4141c000d1400003203103003800c03250b06008880c100c1c0e4269072036140000c0075440e0b1000034120100c6580d01403449802c00034007051b210041071250081d405000ae5498070b1070601d141c1d4410300401161007980e903041403408142c00c00043c0c440b810780a01e0312104240030710034a031802c05040d0b031106605c04d0300495440b50350760002c4001e1042d01d10681c00c2c0d0b2a440152072103441601c54040110025070010f20050200d06039490580c84918100d10456070548081c2c3c032540221403900e04201c01c10100c180050280e070404014041c0c00c40900e00d40941110704c21755a103a9011040302c00244569102c2141e4003449406410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 456839532 1250 456838282 456838367
    0xa0b4b0d080c070b09030f0a171b06070e030c0103090c06050c03041701021801050703080105101b060218010206010608160306031e020405070c050606090705120412090b030106 77
    0x4551003d600c6a034602029000580d44078401e01c580c480b0420021404510803a05a62103242c403c03000002510302c41031504824000036843c050000402a5450104031045c002c2d0f000f84c50b4420303a2000b920034141400f00c4840c07020305060034010010001410a0709881c11a10326282c10341d11101c20401150440c440c681c041d1800511140b862842684c066006088071060419003200c441c40751001900c2d54001c0e0400940405c11500040001d428101c1107007010300400d25050030500c919090f24a03480c91000400c2c1c074425030106642042c10080455040342d0102400184420743c0751a400030b180030380c000e00300d01010040381d40701074602d40030f03410420180d82c0c0117085035100c0c440c1c001e406c01c921085402c1640f18504040101d4803041c02400b100c0081c6400c02c010b1f040658030807080c041e40d400080c00031020400708002d4922490350b802c024a028922880415002c43c0300184010030300b01c0641c10186030010200300410406400c0300d005203451410500310380c0510300400914111008510 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 456840782 1250 456839532 456839557
    0x405090106080f06101409043306080609030415030f0b060703020d080a1104060c0c0519030605060f10031a060406030606091d06090a0b4b0d08 63
    0x74086007030f110010402da0702c2884035801600c003c1e07a5495014200d103101c2804150001500000300b1b000c519800508941d101c030300c0c00b4400d10b0480003901d00404c6941201184e4426940700b805010104080c026160401100c1e001107041905080d415410f4500c9001f015041c180d48a88000000c5816080016800710013061a5200c0d60207080c007949461446c4104070018a480001401c401c1040c802c4641803541c002e4101e04042c1005004d0300d958002c50401e4490064214000030140e450820541031584034030340a02200345180b40403025500f000d00841e21402a0301002c032447d40790300207441800384039841d0103d9200d40038800c0342145419400610b4100f2800680411520707010741011084503050381c0c1d4248083c0d43d49840704850900800211801e40c3d6103c046111880d2440c42c0070781225a00c030300000c1d2522150b0000e084243e001046183d84a115084556141f00003000e49450a03851020f080007401180d100c055040780e90003401d446204281ca02ca018015407500f520089950034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 456842032 1250 456840782 456840793
    0x108090c031f14040b0117100c0509011202031306021b120c070506030c0a080c0c15160c1203020a0e090a0603140a0302030906090f10120608010605090105040509010608 74
    0x38a805020107041c000070342c14082c14030407200d06203408201d415116a400c060303081200e074200240b0746085243c4c3c250107205d500c2540c0100c0c0e99103100e446000c500800b90740301c1507034500c0540005040c0000741c5412103060703813040c4100640a4000c04801940e240c5c0400010b0343c86071880000f002c0000c450603981c03240e1103065204000e1065004c003c002480c109170459101a680e00308220980c8011140e07490040414811f403c0e105014030304003174019100040030f5041c04424028203207010301c00c0b640c200403500084180168049140040a1025010324245040c1d000d80c0d03c6648584000003175010406900048400c04a84034440d08070708600010b040405e18280303041401d0107006035000035168059400099241241d0002d290340c1170613890340140d410100308408000340340d040301440b185c0282961030f41e2150750b40c440506040071030300340d1149003181c414150b08a0032182e0075000144580e250400c2800707181c0d07650300210304482c0c04403808600d0f17560b02800d0354050b1005611504180c42032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 456843282 1250 456842032 456842053
    0x60a031e0b041811040504050f16030b13080a0804030905040f05010311010509130510030204051f0902040b0d1508030307050c0f21090d051f0b0a030309050108090c03 73
    0x100c1d08002103081c400c480a12030380309080355080026403500d000030440c2944042c40c04460403d9048241d000c1c5c09081039900842d98542c4003410140d50b180e07092100d40710502c040c002c210042c00d145800c03c3c40406400b81d62500c69584103010b10400801e00305100d01000003c04140c41081d8000141c103016000348101302d103012441018010a02040b85d011651220094895101c0c070142c4000c0c6c10010000000050304050120040001518014030003080200c0440580c0f580e01629004401c0d06c00c82038004116500d00005c1440daa4110071522401004100070341c12505066544580a101c40051009030042d10384401140503400380d20580808402c10040c0b5070010040c1080805110542d1040b0300c1968030035445401410941c0401c07144002c0044d001e00e800c8015041c00f280c0904801305c040c1c0f443c0c9480346030040c400c501d8069602d4410304403080e15442d00450705a0303038050324025112800d43d60041d0100c2610f0007103904001c107080c0010440c000030003200300c2222014043c1e8070898903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 456844532 1250 456843282 456843341
    0x1110f010f061a12060d1103120706180b0c0a1b0303150e010506070b090a0507080c13110a030e1006060e040608030307140307050d110705070602030a0905060a03 71
    0x50340309000c07020008420340029014100e04990401805000d04c03025075807800104030340b81495550030b40b40802404c1c62100182c0b4108100044540385400c80c52702c9405c0e03454440c058880850045c030b5904815070000d00001c0c3c900b881c094000c01450000ba445800c1810121011b03083c0b0080d210307074256203250000525401d40d102d103403040c4820121841d410b84401c0e900e603000c8000c1c030070150814010001c60000c601d00c1130b072031504400305c030b0b0641780c00c540b02d40c440600d048656041090980c1005034001201e240044940d00c80400c86041071286c0d1403c00d000e14490701903401c00005168580388600340701e40050002111a4012400404c09a51034080081c40c0100400c0d0076405036140030303804180210004140c82c03007682c40346c0e00d0175601404010295110340025016009106c401d20a00840d95094020701c03168040d1031103460349070b08440c180546480640d920801c01d64004201a40d07182d0340c000d405200340c42d4140c030510b980305a400ba08400808d900303001d42d2000d02004446417684070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 456845782 1250 456844532 456844541
    0x170a0c020d060e061b0418020f0d050105030f0d08012108040e091204050310090804050a180c0c03170c070b18010f06120f0602370801050108040201110f010f 69
    0x4046088450551751885114824403405880015044060000700165090500c410440089074200035007003400398a40c02179183c2003981c1d200c0f2400d445000501982c1010000010385060541c02400391080d007440140070b07030074103000f4141d501c43c1401007010400c0c40709901c0ca00702d079442003000d543c0760341d01c0e0661007030542c0940e500001d070300038442005100e01c0306d1000c1d907080c1d900003400f502d0255600c040b01801001004000c80b50071100340800692542d44038060001400c02104040d07a44130641c1c0050300b01e860300e020700b80c01e1007503040490740460360101619000140b140013000240d19007030042c0b41c150060758002030200c0e5084c01082800c180d07941340202d00408000003400408c84100686040d64854011008a480b410380c421000c14040000c041ca240e004000051604000480081191855403240050103440038000d070203010012038078884a48141c03400000c20750520000820304100540064104078045480d405228070510060342c5142101c4020800f40410010354000b40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 456847032 1250 456845782 456845801
    0x315180606061c0506010c081602030114010b0901051c0c0e090703090302030d091e050c09090d02070306020c0c0a080610090b0a031b0803030109051501020109170a0c020d06 76
    0x500856001c21620300300b040584801d8500c1c1c006181400c20701026920003800c00404a40c10444a40e40072808220158020185817103444034481100c1090b0041c54252403106907038000701e40c906070040007040301e03130010341e20080c07000d1910680d21418403180906810038240c0319009035103481074900f01603800c074414900315141a160b001155540e0380c820f40855607005000b070b0150308108481e034040d136140c0e0f02c510603843c032545104421500280f25140e0b4000c0307008044509902c03050416405140c242c07000d0f03910a0403540106507080c80c0c10b00094641c00d082c48004c24560b004220328201200a003c01101e0090140040809079a13030107801d03a442c841542c0d16907103011380550108011a4502803016070b14409055090009d141d5990801420148030b00ea24062180004c0171848903001d04c0118002c01c2032582c0413500781025240c05031718641003281503055a1414490f840040c0c0c41684404c0424858601c1c25212a85c0301003e5840d81c09100d0001e41c42801340000c03108004a5520003400c0d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 456848282 1250 456847032 456847081
    0x30030301050411070203070603150308040e1005060f0702100e06030f04031209170705031308010b030705010504290405060a0309050d030c050f0a050904050711010b04061d060315 78
    0x943c8500340040691203103040181d01038000c01c100f8000680039402c84d40c291000b070816200081e03901d4840c258140c220303412003640a440c45c0180441c026002c1c01d140080c00d42281c4003868100303000311400c40742c81045402401640e000c040d509085002d007000700710000e00600480c0c0d580c0340c815420030400000300c808402080f01c10002c0c54480c410392189100a6510030411502042c0206a01800c3c1e00030380003c0f40d081c03004101c41030070130811401d01d1000b01004800424403420080805061040c2c3c1e400072410080700740b01c1001029038840e0f42c49600c0041c42c0250211019950b9069030600c0380b41c1000f40c205034001070b183c0c003040d41a03121541c000d0003003054484440f8603141c1102039074058586140002c4050044505110400c0002e0110101c0e904240c3d240005100102d0150380c41100c010001ca190703803171700c404030420a00400402c0c0408550030064075080a989030f0401410b0084960900c100e01c2c005041501e04010082112800d80b0f1400950f1811074809512040144102c00300b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 456849532 1250 456848282 456848291
    0x601090e011d1623010806130606021c1418010c1407090509070308040e070201180f02040c020d05030c0a120501121e05030a080919050f0706050306030309300303010504 74
    0x2040c40050a6481030468050b041350380ba80c0000c001100c003008083e2000d40d000c1400603540034041502e1084100034a0a40c002d86101054070a03039449000809222500740022104182d5107840b00030301f2900b4082c6a5511450a814000c0040f83c49440c540401001c03050380c540c441808600008101e4210f4800300f100b0b0004c0d0796a4180c0945400340d80c8030040c02c00790b041c4001e011000740031582e1580130300c5034800010041618060980450307183e0000303031002d10306c10303500009600b07140c011028069410b0006043d02010a940145940710041017000c0e40722001c5020040c80d0b00c0b4096030501a003104005100558441e03540001c0c8042c201e84c201c3e20710306040204500c20a0b06074640f0036841e00300020f181468000d007410b442140d0000c000012501034205010f00d0740c01d50042c125020340c0900e0042c90012413202ea81403a01c0e00c1c64204506001c414410820582d900000302c44402d44280d504140c024400411404810302c0c0f4050280341c00360314881412440130010245048680c1200d0601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 456850782 1250 456849532 456849539
    0x40609030807020c1c03021005040c170f0a030c1410090314090f0f01020a051b041b090b0f04081e010f1515210b0108060109050d0f02030c060f040906050a080601090e011d16 76
    0xc0e91110371050242e83c03038001510190200780141405030f40203020340038101081149140680c10041d2258400e203004c0d035030700e41260515a002c3c1d140d82c420b5541c800320b6880d05040000094100345031242180c851103d440303642c003039a4400e00c440500242c0c03003c100c81001d0004100020003003c1c0342c1d1501e00a034582030486154605001c03800c40b5160a544520101c3e41c249031a0100aa000c0302d42c1d012804d4081000040307421040080c1c00304000780094848002000325035150950f01d81d180c0c1c1118288c10103481d1903d030f4043c12281b80c112441c48541182c09801600d082d9006c4550490100d1410301c003203100780c0309031582c1c0c10108001c6001d0f0384804a9035117020040d282d00141d1b0050030b4010211036652000141501410789429000400710303940070290a001803455400546030b43c0840c0c80100d01041945014013988004c0e0004403081c0031000d00780801282d0700c040510412003450344070f20110f550840c013940000b213020080b2200d65450034a00d1035284e41d034040000c0c00c00c41c00d8000300c07001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 456852032 1250 456850782 456850829
    0x1b091903050f12030a0207060227090a05091b0409020a06050a080f1005010f0215070e03060a0203010803250807030306180c1e030b09040609030807020c1c03021005040c 74
    0x1d400c3c11004464a0a40d01d45103d600002e40180c281215419405c0040c00081c03164104040912051800140711070034010060100600c4042d03d41031401d070520041c00059030010038074900305515400010300d1804041c0000c0e0180680503030103900b0024035035000c07803c02d03848402007405814a4607203192030388520700d10801c2ca0b44216031200415000a9040c8515071143c4030070103e5052910441c0c0704103004414a03140400140d4408010500d48030240c0319a040500c001a031144501400714207540c544028540c4030311540341100c1841010f6100c4c030000702515140c0301c411079000810561641c05500c1c0240c020500d41c068012030889280040000c01da4502403004003049035501c5021149011210041200c11890314009141c0c451600c1c8042d40c80e00c240b4644514003520000c60300798454100500304000140c0f2010454100a2014415494502c1e112a449061400d80b2040e00440d050407800c1220158050100da030400e0244424480d00d01484404e40b071110500103a18485618035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 456853282 1250 456852032 456852043
    0x301080610050306010302011b05011401081605090a0b1801080c09061f03051008100c17070905190e0a0f060f0501021c03020f0a02011b03141b091903050f 68
    0x905a140d408413005100551058080d00300410110307207100800d80095a600d820743d1040704401c01080d074032000411982c24200070501d00303c030800109003880e41c11318010880b801d000800b0881070f983c44e100800f4468445103243c020454041d03c5103038095850f000c4140e20b07030f40c020280134481c5980e43c000c10382c1da250200030001e40240151640b040500d4416055024013401001c4441c0c4030602940060600c009110b000e10018520f4000074018150003000340ca52000b619840c0508040182003014a640010010045e40c1c411545081402e200207034144000d000e980101c0e0850040005004050241d07400c04d21483c07100b400c00303005031615944001e4030300e800c900c28140180d2040c0214400c40009419011006078a407801526105d80d030f81c07440c1c00a40c425885000180c1d50b4080c054040400c10a408001d003d1601d1b040c001040f020f240e44860010181c469400301c1c000350450440c0104800454858140140c4050180480c5200072410340c00b0a21040c1c80314000d122450841c4e40d8081f40c3c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 456854532 1250 456853282 456853289
    0x90209060d050903041508061305010f03060e1f050a060b0903300f0c1203060a0603020a120f0b0405010911030106181a09100c050303010909060f020409020301080610 73
    0x200c541456a03044445024100c043c10099550004000216083c02d400c41080c4810340d09071101c613882d041c40e03400e05c00c02d179040c1182980c1e41e038986401489036404190a0004403a00204041808405024500d0511128800800c19045800300300748a4140782c1c4c215921403000c42d03d04100c1a551409202c01c60301c515261564160001c2d82c064419a600d00c00b0202c03d60401001c541000301e88080c0081d60398032002e4a8000710300d001c50054080031040101241d0000c04d40c94050840c00c00718049103854009004840605401103010000e02e407040707456540202d48080284403681590042c900100840390089010700c0c100000800d00c24890b0081c1c1c0d800c80c080320110b07461a8a00f0070100c2e040c0c185120324014406042d10001100b4500d19012401c81c00d0040559540d4005501008800c12503218441b0a108141c1c0c02e4001088001c0140c0c2d0440d03501c10000711300d2068a15141000b00003040059415520104010850320b405034065070580e001c58084560079240c031000144404210720 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 456855782 1250 456854532 456854539
    0xf0f05010315060f050d0b062101060306030506131407470c1e07060e0139051203092b03020703030209100c2603010e04020a03050d0e0a090209 63
    0x14611342e4034405c100412a110b24420300140c10b80c81d11700002c001740e10164616000409502c041c140007039040900c5170040085003801c00100d860340c1d03240b07034035181e000f400d07031031407164540c03050081c40500340900e100980c1c0d800c00d40e110b450b03c40314900004400c1c607501141214940d40e130141008201a418405482e1001b500c00201d03840010030035055000744a680003c0c054000303000713414000780500c0c2d511080e031040500a101d04006008200e25038501510f41081900310480407200f980c55002c803d103405000c4840300c082c01c801012400c80d07903100401030640c841d0100d021907141d804006107008107404825140000c00c04005480c1c1c0c414400d40300c0d509119a11100f800303003070013507000b08659442400c01605010b018030018280311100042c19002c2840c1c8201c080c1000310204000980003040414060002012210400c49000c140107125901d1803590104082d9540d0f212154015030303210301150400c40c51400e0041082102880d41d41c002c01d40c122010030200d030701d0b0090707950141c40138 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 456857032 1250 456855782 456855797
    0x7030b030c040207260903010b1e0f0102010e070b0408072403150506030432100b0f03030309030a08010602011802010f1404090c020f01140c0d060f0f0501031506 71
    0x80400000303500070001120080c201c40640b07003207071700002c09050744410444251502d500c02c6d1002d06081d2150a0b54082c440c1800c2c081c511300303a00507040e15039000041502c880c3c01c0c030280800144c0c010b0074850320030b010318402c3c000000303400c800c14801001a03942410580309401d9844210b200b2035541e0820142c0c4613100100340030b1043d8465488080f440503480d210b0303440907581388040b806542c0705840c140c0315010300c5c1a0b80c85000d0031860b11661007501d03005840340000c03040044140c480d108005104e0304180c842500341d006d507640c0c9100d01c41c1a08001c0641c1c0c4e403800e00080c8283c2c0d0303501c400844004070300030703000000700030340103204451036541800c190303c180c08460707401111010148815581400310410340350442250250207400581000704001507503494103c0081d150060962204c041c9a040420603010004503030021034012000c0240d032619082d4000030200a4841c6820000e1603480c038120020b1041c40030b0320048221002a241008480c040703640c102c1e041d108501880d40801d519 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 456858282 1250 456857032 456857053
    0x3040f05120919050321040b28020a03120b040603050d18060203070302030d1d0a050303060418020a0302240a0c2a050906060f0705010f060f081c05070203010e0609010507030b03 78
    0x3d0344295011266641700507d06519021002a5a04451901501c0c40c0f0b10b96206090380304121401c00c04d980c041e00082054843c2aa0002c00d40b0320f024512074a007079203440c03a0506a8960b600008091944002903615403140b400000340309550103602c100401281d010005030b014008400c50b600c1c9a00340d4040c5180001e281e08207800740601140501601c07401e2041310f0002a42030101141451288024560b01d0504804100c142c0e424107060789840c40d81d03a14503178016691210312100b244c0c2d050f100081c0803065001d080550654850340400c20040000e01c00c458980e10401100300280f0405140001002407400d460307280703081d08001034072403090f40341c240b007540760000d01c059001d0310080c0003524003a0824072030407d54110040444090391142c1c1c66503c0900e041c001c01000c2c0000200900300c0c50700d4142e90954910000c0c1000f401e00300c40610484000307224000300c40c40c1a0700035000b4050a100d9220484e80c90404840344000c5500c5d000c0490180d500c24094400484801001400c801c0d16 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 456859532 1250 456858282 456858313
    0x6020a0206031005030604050609010c020706090e090a0b040c080105181e07080708010203010e0106051c020d14090a03020c040b010c02092a0a020c0409020a0b03040f051209190503 79
    0x101030700c86155920283c0300001d2580c2d0421000c0d10a47c0315901804450a0048415003580c2c104203501080d50400d138001d00c110380d44240b645d01114040000c0c42a42e4646c1d0341c4184c1031804840000d00900702c110304020501150600301c1040b20070201c000c00240d56820081180c40703070a41c50007840e80d08a010703001082c3c280070603d11a9070800905a9a0460751502c84902d05100e03944039400741d0b5000300c0100309030080d0280207401421507040042c80c19101201001c0c2d035112095a586d1b1041d4007107031101e43c151a82d0f20011707244840052034011800d24010242c0c0d222411002140103104800e0204074504042c000c82c043c2d4201a1a03030046c20f0f60351740c200100030f9802025580180f04003890940640041250100e04003071443d03509640321551fa030000d080003c4102041d003c0c0e030519100d4001620f0324440c0d01704032040200619141c1c0c03103e180203c400003140d0b0703000d0300f903105090402c0b500038603420040018000485034210a00040107990b007404406210b4a981504820710032360040a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 456860782 1250 456859532 456859537
    0x8090411130906030320101b02150105101101060b130302030c040e210706060e180106140105030411100525022b0506010e060a090b030a12030603020d151506020a0206 73
    0x34041e0554240203c0741c02e02804588d5503c0410a000702c2990a0700e400e40c2c0c0600c60307840c03007003480d03408058103604120119050040340d400341c0c0204401400028402d250a62191000d420034050345030b0703904460025140b00704002e0000364031034040c4451070190b524083c032901403c5a06403000c3c0c10415801018401d8140d14040c8611032044100050070000b8200c1c86a00d02410031921400502d06046c141c40f051610341c0c11040ca005d0785050414840c54484541c0003605200c02d1034150359941d200d10301109020844111181c101e084140950012a0040003920303000750903500340700090449610f10701000f0314908001e500030b40a6003281c04501c502d222031030200303000340580d85160707842a136403146400030983c0422010011a0240882854003941c1d401c0241502d40040c0a104004000281c03107458440b802008081a0107071070200d640250482002103400074050009803100e0305202005a4048441250f8a46011141061040080c55100554101d0703070062207140300c81c1e0309004039035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 456862032 1250 456860782 456860837
    0x110f01090f0b130b0a1b14060403080a0e0313050d301409010f080403120c0c12051306080405011503120305280504080904111309060303 60
    0x84100010601601a0040c0c0009141d01500d0b6559041507081a5407000c04a400180441c0c0c401c00003141e00507401302145180901020032900d00c1182450545080c440307103850b80019000f00401c00061580241d0104c2c443c88041c00300f8400014124445a1213110342c2c1c0100d805501d1000c1d007071005081652003a9040c0d0710509039070000018004c0c0c0b0000c14080051903001041080e02c4180d201c6a018404180842d15107540c40d081c050300c2e03400a0603154421010714100010700d400241810302c10580c0905000e103898042243d140240802020b0a10600d810344400c0c1d6003040703198405100c2c0040300c800d04ca802d5245802c1c541070482c02c480b075040141054036550740b85d08150358100706100710310000350300c50140c0342c0e032080c90254003130250b507070003891015180c600030030b8901c10030f01032042c011919080c5032001443c0e85d00d41ca04143e542c0103611030b0540003031030312004c10000001c4000520716444070080e0300d05a80c0d500c2e040364042c0c800b6800014005075011030b04000b00048041200b198 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 456863282 1250 456862032 456862037
    0x30212030d271b240f0504030b060405151906020f0304080d11010b030d0e01110106061b02010306170619060609120311150a06050301050103021f0c14010501090513110f01 75
    0xc0b991a01900340300c02c0c2400d80da104c00000c030b101c0c200549821095010b80e404035410720f181824555103841000702401054540101c0c0c68100240c103003419946459030b0460014010220302c0082d1181c1c1d803080446019035009413151403401030030358000000343d40032500c50000506402c3c01c44003045031526032040c9840042d6482d0084d40c0c2455a00344040158070803d1350710260541031060006011785110002d0800d2070345880b50a120041d4401403070705400d01c45000c0c080c0d0b105002d200403402041254130554100e241185000709030f80c000700341d1902848900e40401c3c83c40800c5120392084814078800c0402203030303404e0002c100304003014003101307500780c02424203c1114008040e035034100034080f5860982e65500714100701c0d000b00c00c3c0c8148409080280c008001540c110b50200d000801c503132841034a24410041500c0d8010f100e907c00010a56020348941404054001c169006e0b090a000d50100315040c800000e0242490803001240a9081410074460000d00024403074950094482c1504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 456864532 1250 456863282 456863333
    0xe0c03150604030c1404050612100518061003060b060408060f0c040b0a02100f020903030f1303120810050d0b070c050c040e100b04150b090604030212030d27 69
    0x8940740500d600f001780164800424803816907420042115001814284036070010401030208800c00261707209001e000b01030019042e181c021444460b0840350562084520800e400c001e01320030210074882c1100d2050f00180010010002007104500403030103041015813009000401900002c41202e0f08001c00d4070081c0e18040c3c4941c04548181d11800f04070300503038802113100d480d5111034818550342d0f044030a001c41c10704405100103601c074820b080c3d01685d02503011513400202586440300b0002168808203644448413040d80103405540c01300c0c0c01d80e224001100000409040460031a4141a8040e4000c8010303500ca06055803844d25030a07080e640ba200d603ca5034806611144a00701d058034035800145101158003080800350350006401900413800c06001e400100f0707041c04400d0a1300c00104e592a1107820407000b06c0d605009030b41c4040e6206a490071a1030300ca80f80480200714030303180150140000c000509440b040003844140028007000500c8544e00499040406da00144500c0204ea05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 456865782 1250 456864532 456864539
    0xd050f0c16080712022d030405010c0602090603040f030e0306131e02090112140c03030910030f1401080f0f10090c080f01050f09060105010c02091f0803030106090e0c03150604 77
    0x141010264007050005d0303800688240c00e03400340c00c80380d01900c00000711101008a100403545071a40520300c503480c10f10042255100802c6819010740c3c032200ca0180525447c0c0c80c15091410020500d12810303030115418003a0300d0200d082c00300700f5900c00c080b04507208580f07000554561505015403580520f00c100820021801039641060043c000c1c0054901c080f2034500314101111403401842840c0b4440e8000711120060742c4001c815a40c00e0141190114020071008000b0380c042c01145081825503458048416000420780070302c00e0580301c044044a806001152038190343d1514411202d10f181d01900160b81c68500030380008041d07074171404524202d15503810a9038544001520202416515282046401c100241d030350b6038020036210040805524200002e4250420329601902440c4a040015a80c42201c01405484c450b124042c0c41c1c81c0740c3d61455152290420702a01d400285145d80006201d2082d5000c0d0303001d04c1c4032441a81c03854407401c0241d00342c0888074905c1500000c0c00d21000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 456867032 1250 456865782 456865793
    0x4020c01060e0108162402100f051b1305040b040b04020c010504020f0d0c050409031e090e0c0403031e0306120b07170f04061515050d050f0c160807 65
    0x10006081100c0c000480f5418003020500340000a2501e01c048010643c08006a040420544071410b400401003c9005560001241001c1400e24843d2006040c40803030404a00180d201034031075180d00303000103d08466070a0607400d904c9558809400c0211a21080c81549416403144041440043c0300048500321107000c03c0603a0455100c2c281d2595584081000b541020355461980c100c04944c8858680150303078508041e0805401024040c99440156908040c0070308035035a007100c4400c90600708107240d1040180103090a029914881001d1000b00d0b00020818040d101903941c03544503032840d815040a41c3d207441d03400381590801c154551100180c04004030300c119a05074001e0043c4a03091800c0070029042409422a040030800e84408000405d1000c03480d01e80c0180e4416070121319035548188943e25090150001035558154840c00c50900f034010340100f11000000c10203005903503801d01d0614030007200710b6810f01e00300820890844600302e0407046c031050500c036203011403c1041e07907180c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 456868282 1250 456867032 456867041
    0xc1109090c01140d1e060806010605042120030d1e0e0607062c120d09020a050a0f0f0b1602060307021005010b0403020306090109080406030b0303070203011a13110a050904020c01 78
    0x10900c07402d1025018041c5c030a0f0041130043c164680042a45514210000740703a40320394418043c200c1e16004d0b83c20803242c0d0340f0781c081d0740b115001078030414030750751540e0303105500450a1401032180c030411019200460040000e07002c000310a000304511000601801e40c0c04000e48150190f104004220300800a000740c0310b105411000c041280c990284141d80c4080076450001c0c41015641c440b0444030140041001110000301c3e9840d00030566201d00d00c0803400004482e00401c0d0700c17040c82000807600710f078001248411180051301d0f4900e801d507039600d80c1980c0d00c582c00d91b00d03d2403081d01800c58091700740640150380040e1644116242c80d5812080d810032aa400c8e00481890301c2c0014003082540b0f004c0241d40d80122860000b0012404655203d126521652003140240341d2108000d1480d0303541030081c2d410300c513000340003445520a0942601c05010480d08950300c5644098609207800e806032248940039014503200303c0c0750003208141501c10f5000591429071243c2c0811070000c9680c000e000c2c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 456869532 1250 456868282 456868301
    0xa0306180213080105241f0206070909051302010c050f0a0c050a05190e100518180d09061b051e0622020d050c0901060c1109090c01140d 60
    0x100103855540342800030080006503800b590f10380e070400061003541c036945245aa04114034400c0700c82c0c078480850101d01000072a81050002000040c00c03024525004641984103034460340c0c0705503180d529951044116581039403800148811164100011b5000d01c0e0303030039440fa0082d02110400c80102010903d070848100e422181541100700401550401070314140c00b9150071905c080302c0310f90070710144400304032910404020345542c102040048402c1c95001000d0b0101800a04550005240800c46210191070010262640c000400c54428010030001048881965166080341c075200b800c84280d40790040060403010907404480004804121449000035002040e0082c04030400d00b141c2170041c028014003004060040111a00d622000c0c0400401c0c2c0c1140d11280003540742c00c14525110035100044e0700b0001c1c00b4008144d02d5000606484294483d610b01c80c0340e081d882c020301036190410780d140c03100fa92280340c0c03090940d8050040c11b020661881002d030f00304042c505401058950184 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 456870782 1250 456869532 456869579
    0xe061614031911030a0e0a08161505030708041511161a0106020304050402031012050601140102010b090105010c170f0c100c0f05070c050603010b04260606060a0306 72
    0x700c0002658030410424488034a0b070070400f07501240a110141c82e4421100904204450140c2805039590b4000c0d90101038001042250341e003107606103d011560f11a030013080c1010740d44007101c454891060045a00c43d0f0410350303034010380b41c580303540301000c41008039840070003140c64280780c1513152001c401070508400c00c03681c0e0518040980c207104441c2011010b041300001da404005010342030700007040707504546050b100180d5a41e01c06258401102c4c06801501c1e01c20341040201041c0400020068140c1e103c03880d8100000640d4001a400ca070100250250403180c20801001607601400c1d0b400c5c0064041e14104034944c841c0ba9030010356030b014205050b0700b4a404a48820380b01410000c6040143c050001004030400c00352010701404c02a0f80303d071040040009040c410010345080f603000504014207030342d8581d40c44038001942c54006001e1841102e03d08007107544008401c0d47d010f40380414003405400d1a864440c140a15a405002c402040c5074460300009004400e0b0112614080240c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 456872032 1250 456870782 456870787
    0x30703020a0f0c0209010501050a140f0703121a0906040b0d0c0f1d010b0f04031502030a050a090224070f0b010302150406020304140a080d09060806100e06161403 71
    0x88070251004040031001c0701080145076003000182c07514040300c3e040d01e009080460329a20720b22011a00720586180741d852521011603151020304900002e010058841d8a8407421040d1581401080316101d60404000c41250a04a0003c0c1031255006400c02000b0304041034910f81c82c004540901d40c040700885481008503010000360759603044010241c10f0208440b80d1070402c8004900c007018040c020391121a0300000c0c51034000e1165000c8400a652006103a0505003c10120704001d400c1200c0503401e881c103100000d10710384041d00c264140554000c0411501380700e030340d24402200e80b4405140503132180030025003020500c90091462040d100e082c10b9840c542c118810300106140541d5100b402c91400c1c0800c2c0b1041b40c0110544c0c09032410206120a840621000255036800076400440c2c00d015084030a900554484d41a50948180d0780392004c05444400610aa41a000e20000000b958288040300d2031300d0484c00804071107140c2502a80d83c071820351645d007000d030f06124012080381d100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 456873282 1250 456872032 456872047
    0x8070c0809091e0c04030b150415171b01021507121e0b030115140d0b0405010b0f0102071a03060f0901120b0609040f030e030111030106050a091208041701060b03070302 74
    0x20703180f0081e4480f420b10481e40c1404d01d140e440110b203007005072810641920010032003e151300d590340003007001d5040b040c1824085503504222449055041500d260a02440f0000501c15020f11140070400c00184c0c02042d804107204810442404083d01c4402009418001c0c030000c880c0c070340903009004660950180c02c103003400c0d071100211141134950b00d0099050981c04001c00101d03030580c90440350140e0110900342610f00008620036115030000300041c1c2000103000c03c1c81030552002025103003d8911441503607108005903650b0615201d404404690104112912280d21000d5608210003425981030040007100140110000341c00502000c2c030390740720403800c0c0301204001d9078001c0c03003d4410000714100350b10780e408040c802d0300c400f60038410005041c10991710250301020090001c802055281d58640d07800804944c081c511070000112142c00c0410701c035007029540459140e0020b00d40d0310305480d00e00300d00c402d03c41e10707912103225558039800041e107010b420008510801c240e6600603501c156 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 456874532 1250 456873282 456873331
    0x7020c0102240408070f05011802040c1815140708031b090a1202030a0203062403011e1107050114070909050f2e080c1f08070c080909 59
    0x5420044245101c48a401202a03003041102c40d500705403c00d50107640d5524900302208030702c00b50300004081b50700c0d042c09a108540b85810380f03810795100301c6007480030038010b001c03ca95118081400d1140116118070410110421000340c078000916414101e4401212048140d8503400183d42601c04800001c10000c0d10345028051080050461002608000001021402c4c0c0c41145c020480300041c0c00109806541c0d040100c071002980c01400c403156850035600d064200095900700c0714007150001c5c1422494078042c0151181994074582d0300d03501341d03200d01c0c0346c03000342c81d81144041780580208840c402146081c090010198034070300c0001c0c4c0c84c1c242510014183c9100307601620380e079032501c400d2006003000440d00e40c0d00610891040002440d04003160407171140265911f40c080c03a020310001600003408540c032461640c0c00c803901d4201a01c0c0c0020341c040f0b200000007041c00510401d000802440c05103150192283c007a03100c0504104d1140045001c60206544900c0065a1000b0b0083c6225 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 456875782 1250 456874532 456874543
    0x100320030f01030302010c091805040201030f090507030b07020f06040b070509100201050108070f03031e050c0313030b0c190f0504031502032a070311011808030703060f06090b03100b0307020c0102 86
    0x108185064900359241427458132605046003049060300da2184049401e40e0f200342c0201c400402014000c10154000d40b42131940e0300c54622044819900d40030000301d00310300106113000410421005440155120750305c0c8140c50310f005200006005051028900540713813501481c05092050700001015414000d00909d060b0b4141c0c403040030103400c0882400000e03400403061005030014150440341c0300c40800240c0d518083c1c501d16140318403000c030711494013400440a5004981c003520b455130941d11100941c02c1d0303138400d014650303d02c40f540078001c40d180717841011030b003103d0781181c6050350400b40c403a40c030309241081d603001007110340e500417003401140340800361100d20214840007038010514030340b108500b09004001c0060240311059000d11070721507081d00052140840c602802684c0325803481d080300c0c150815130b8010002850508086840401d643d5034800362501600d03514000f07840d102c00100726600c02014050795800348040041c410a4075006140a9202c1e80c01070804036241000081c030740b1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 456877032 1250 456875782 456875801
    0x606180a090602072a2312100b13090b06010c0f020a0f1508010f12050f010c1718060105040f021303050c12030f0d090503221503020306100320030f0103030201 70
    0x1201c001d001049410f55070380c00061640c1500589141a00b000d20001d45c7c01041d5034a4000140100c500b0f00302c8100f080d41c03007030080e6482103503c00807406850b90b403031088035207294004000c020004049030203507006010144000e4840c1c0c07001000c94007079070301241040c0b600382c2c411021785da9402c006002641d202c1d890040071510701d24020140390300d41040449143c00a101e0303508040100c40500c0140041413080014460343c1e400244501c010104000341000a0700342a9030803221314001003600014000c0c602e081a030103041c0186420303401c01040000608460458181540d803c010700000b0011100301c02008500407806031112604d07420a001c9503408559106c035040c0c008010705201c0c500306205880000c007044100203428085440d2482c6103200b01c2ca0b052030b60903110032a0b84210b26080c0011410384402002c0c0703640e5842002000e42c00e80c081500c075580d000031325220b4140d0f5184264008046409207000d1310744900300d034802c1c03070403030398020b481d91400061140c00500a1680900561660 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 456878282 1250 456877032 456877103
    0x602070f120c020a03020909030d090b1f0f0306020a030207050a03110c0607210c1406071d0607031107050411030405061803310915080606180a09060207 67
    0x65000c2c0e0340041c04144182c08024494800e110104610a0040007500d5091104003070400200125003840f90340d00350700b02c4044551000b4400e8240100c160b0031010030131104400c840b04009402c40c0d94650103074011500c0701d000c040d400d1001401086040021101d440c1c003d40303612800360103420000e410a5400c420107405104100034030400545402074119240c5241e0207202130700908031204031411046120080c040d2520b5400280110710003046846c082c441e81c0c0c85060b0030124410208070003204540c502030780301e84248032000200303015400030045011480e0030380d40c0094a80d0001001c841000401c030710090000700c100302c1001003c1000c0d40c0c1120000e040e60008020b042c429035560704c5040803041ca03250040400705d244040000030100748592203900c0d142101e440341e6816004200c045a035001e9010b02001c0094010008152603005140241c0b10b2202d105041c0303019506104d01404007104950f4805840003c243c0328030103820190310640700315441c0c1681003e008010703912186000320 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 456879532 1250 456878282 456878297
    0x311060c03221104062301090303050d0b041e06050114130303110f011112160503130203070504090308041b060c021e360108030a14070602070f12 64
    0x6855200162034440181a04600c0c03002007094034140d03104150540c0c150343c010703080c40d602084c4546d45048030111904005042400d4100c1c180c0119042d035100e2101038045402042502008a19a040996400300c05080800c81c0074541c0c40c01c1014054207501b0000541c2c2e80c00d405e00c00d5680c0280d07101402100c808241d41400d0b00811140c003071001c684401014840a2000416052818040780707a00c0160540204140f515031641122183d11a010402d41580020009030403c02140d9460b811000680d4919095070364200f5804442058982c0c1644c2c5803164550001d032550780d034050180d03604d00c282c0c1ca2780980d0510f4a80101c4004200c011407103401c103a42024800c00d640300c8204808540c0407100400300681900748001e2080841c0549500310351a040c040d1100321110014810150301154001da1491005115000c1d0003401c0c081c2d07250072340081015441c1f65205a0101c0a51041500000d1a080250341c1c1c00c1c0899110300d5003110401b20116118051001151900c0307407001890601c040b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 456880782 1250 456879532 456879541
    0x10050a110418050403180806060f27090a061e0606110d0c0f151a0f010c1b0e070c05012d0c1e02010902190803030a0c030207020604030311060c03 64
    0x2c1c8070301519802401c880e0355440029040c54402c04420282100c0d11507480c00240d26a00c40700e03101c03041220010301402c0042700846207401c00c0c0300b4101411107880d40003168080c6c01c4420941d00000502075101a01c9150102008541c5074410488240d03140c0e00000c1d405a42000400c0c15a19581d01040c20b02c484520940e4481201298a109401903890025082a01c51400301c10142600d200581644956a42c1140501c420f03030141c00c40c60f034410720200205940c074040214800030004030350300150301c0f0721a6030001041c0b01d804c041e00101421075a07075425195030001c02d8800c0c1c03c990400014001000e650207016003881a6258482d8110380c4801c54081503e5407070350741c0c02503030100001c16034036122004024410030206010080c0e848500d0701c4465217440081c0a45840c2009a1042c40f01511030f01201c00c1c0001c48008aa14908c0694216039500064500a00c0001000d206140c2c00700301d400700581c0c51710000c002861180d10758088000710714001c2460084024860500301c5070800922 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 456882032 1250 456880782 456880799
    0x703090e04020a12080706110906180d0f0803071d0a1502120f041d0601020606011d15040806150a05130603060908030601140a1b080c10050a1104 64
    0x9058455104400400c0d448a1000c24144225a880501074101c1c40080d030040005117001400d00f030380654402c1c000b030500c04c803403144144070b070f501004da10002c20040341d000e101200245140501c801403503098088040e890b0070b03550010700103013117495503400004c0040c0250064548454803280381849141014040c0104000540901a002c14002013281c5403c1e41482040201601050450141e49680174007948141a1b00240110303802e080040029201c1c00c41c89002e510311070b500590041c03440362200001982c0e843c944200038540c20078040302c200110340300c181118090b04403003c0030b29a80c40ca41607a00341441e001400b242c4121011151050480d40c807004072000340c0e403085620785004d2002c4440003006044c2c541c4002d222a041c0a14903040c060580c029511032078007a00c80ca400b406141041121921840403050301281c0c0b00e080041c0320152141e800e03034050740324072165032400b4030301c80c841490034013410605482d080c0caa404000180c1301a02880300c1c00c0c601c0b01811400e140c24100392 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 456883282 1250 456882032 456882047
    0x4052a1806041509050106030e01050c07060506060408032115030c060a0315090204171501032003150603120f040e062b0c0b030f04060e160806061002030703 69
    0x109103a508400300422074981c0d5592011070088048000280115134420252014190910542d40443d05d415000e0f001d0304c0e018040c0c9849075240c014920301d0300c0450741d5180700070b003005000f054016000740408507864a080006007241c90140f441900280c5001d041c18403584001402507196074081c129104054070300090301c1c0d14050b4121000e907254500e0000450003040c84400c0020500c003050300000f0600610350040007a28560182c560407140b5001e5030507640c083c16032102c111004400c00400128503200c241900e103044400c0001e0602c00c81d140001d1500d04000300c20310b800701d440c0c001d00002c0d250410600204082c51003000d8102000440058114000d070321440301d244000800044090f13440d040300040c81d0b4800c0100c48101910013188040c880100001103aa100e21008046424550340f001d59208040c5414507081d2940da0b42c1c1d4090180001710003c1810703228500031201e00480d52803419015102000003003c0300d10744141049203514a02095400b9034208010381d00119030300130302 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 456884532 1250 456883282 456883309
    0x3080402091324020d0c0c120201050603030412150614040f050c0901080417160b070912031116080114010905090c0907050d09062c06060d030504080604052a 69
    0x5920703d4055000c681c10064420394030039031500c0745400c003841c00c40d6400c170020300b9045014031a102d2001040880a07800c03a801510150340c5640184000c000c8907c141c2c01ea40c9906200303001820610282c060040d042d603029401c012a0040f01e29070380e41d84c82c1014030961014074082c4506101608061010084510400e0341c614100203209000405000c15802c8007013044103842e52040d0703240c0c00800f050184035221134080358002c0e82c40b00407401282c0f281c1500e070160f4284070103094914000c0d075815603000800501c404444d01400a5240c5100b9114005c1001400080b00109620300038540141103680160840c052151408081c86207542d80041c1048060405440c0d81000d5120240c00b40c2d183c3c0280100280301c1d03401d0604003020021190450001405000c09203c414404800c00b4441900c1c081f000f92010703407020000031524500030030200f100d503000b4186280340a440d00a42420700d14211025906035202c01848540752088039200e000300c49480c0640700e9850065000203403001000030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 456885782 1250 456884532 456884573
    0xb0307030c120f052d0703081605010f090c0501030c03090f060b12030c16171203070311070b09210409020d0f0c02010b030f010908040b1b030403030804020913 70
    0x2c591a00b0409a241d0030b40d1010307004021242e034100c1c074100f00400c00700550800b01c10480c0c2802c040e00204800101d980070389510114290034500d0303100308400030703400c0b024007074440c0c1d0f48034280f82003480c1c0f091190402c210b01680c104800d0605180000d030a0744d0204888030701701881c0c800e000d004a03407203122002c54241e11400105241c0c0d0903000040c040d00b80140700b00b40a010000345110f00400c0001e80c0340d18481d8005140c02015541c660260540290319424001e07a08032000c2d101800c01440019a4001524200056006c541400b0903441b80c2003a0340483c1d282c00d0003c01e0015002c1c04001051014800c1d41d00c00c10326441e200100f400a000d103120f1401079640100700e8001da2049a00714070315200f200c040c100705001c007800380203004c1c2c1900c4251074041d01484204034031500d018040c0d02d0010f900300070340e41c1c5814541001e14003950b010000c004048003034400100000c0c1c000348010002980643ea608405043c00e004000c49950702800700307100500c00a10110003e400340089201c042540e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 456887032 1250 456885782 456885809
    0x120b0108250909031103030a02040e16020303040f1b0611070e190902010c02130c030605060a0906180803070b011715220c08070e060d03091206060b1201050102010b0307030c 76
    0x500d001e41c0c0030362881011902a000100800c051552303642c0c0640f08840d030040c00c204840d201e40c40416042d0543c41e11500c0140c00070000034011a5458030b0841c4854800c00c60150703c0031003c5501d648000c9241c0190b00000c40340490303a281e00c1001c02110380500690b405004160500400c1c100d8199889105500030646488055007503a010720000d440c4143c01800d1a603251504500c10b0006055544c0c40602017481c201001c030720340c1031820a803201c08445803116001d06040c00b2003916400d84843d00081600300b2540e021401860900240c100940309070001d05995051425000900110a030614074543c0301000030a0780d11074032a01103802c29910701e80070640c03454400c400a00035402d658003074848280400001291003000071044129614512420429220f003c10000031a490314000307000140216800c0c4410144107030032440c654803840d0300290143d50340f010300c0c1c4e945c0c01014080b055045000d004001d5960207008080110408030040c1c4011401d695440f0b18009540c0074003054451103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 456888282 1250 456887032 456887051
    0x20c151512011b0309031130190e100e0a060f02010b210c120607050c031b011407230a0306090f0f1d0a0b0c04120b01082509 55
    0x2c1d07120f52a01c550041c1c2690010841040240143c02c40840480c0000e0081038070340052400440d42c08446011212003081035002294955110b0028a600381c1e0000402c2007400382850b43c100340e02e401c0c00095210703180c0c40c030201c2d410004800c810050460901001c40c4001580343d031307458280d03401d83d0302d03c6c14100010300c0384040c12030041c01480e80711a0026030081c40c2c9596504910701d1000d500c55a4004c035049007920308144140b0411500c64440c455100001050b00640110040c0980d0880b02c000c8034180604070161003a00202d00034441c49903550f8640c25804002c039000b009501c800141802144000d11a00300c0c0d041ca80101d0010503081008161100028400d80190000741040c0d1420300c0030003c5103500780010441d2074041e01001e40340c031031040c00280e05d00d041e0002132101080a00b5021400b510740d0080140c00502900450a0401020419088158494070402c1c000c440d8080c035981800c60042c03502010004440c004004d00c1500c5d400d0b0744100000c90b0030354128110110301e0084 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 456889532 1250 456888282 456888319
    0x8030a0c09080a0609231507170c091305090c010c1b030803010503010617060a0203060619020c010e010305100605071a091c030b0108010506071a010603020c1515 71
    0x103403074118030460300410154500340044d0703070042e0039580e00a14855a00030050031180700e109180103070003141d0b5000740b182c800803613141d00035203644405a414031040b28541e950134415403100032540784c000481d0108015200d810641260746611201000402c0b6509000602c51350340d078140d00701c0c83c2c10070440c458424200402040c01c42ca20f0b40c07010341d1400c4650384a10b444c0c6180d4009026031070007580b8080c80041c01d15900b0361000703604418030000d40065194455024003a500c010301242d04610100621401da044034500070104040c1c6601600082603080001440232100c04259410541010207000b841e00c024808181101e0b014102650381d0a81031805200b41444946000320300b151500800c007882230b011821460161505070728004412560000360f045405110711107000a05440050000b410543c0003024090b010310820700c00303404001a00c0280c8103090308013034001b03030300072640440b000d00400403a0380300d1084c046103041d42d1804550300a0550441e40b4414810141080611600300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 456890782 1250 456889532 456889547
    0x604120212030a0e190506030115030603080a0f080f01081e01090b040f030206010603020c1005181b01110304241e051e09130e030c0106030b040b060a0308030a0c 71
    0x38040c9060343d4681d0035104015000c1e044e014a03c500400142c4040f0548100c0860000203543c0000d00c0c050450b401c0400356952041c0c81c01c03844090541c2d800000c40400d8660300588145042036451601d000c9003280d00400340f00c0c1c05820740030305031581d80062280100103e40d4501c1c42c0c04040400d82c080c1802d207200303805040401e2021788402d2455042c00148404200081c0b00640650211001a40c2e0741c00b080703080b1301c40d100d030801040c0c0100d030075010b94403419000b0a4012004040c0220301c01b60300f00300b035800d1102c9400759141558503809600c00a50300488000107001c4c0c00300145007030130b1500000103000c21444c240310502d510407586942045004410b1f0300a900d02400c0f10913581e415443c80030304940d11800d488041e4071a0030b090051200e040004588400c0805400400703c0b19624210501038500c5816540d0b081c001070110030324004007480f407030f4011805120074181c00e0915081c140000350024264074000c014401050012443c2201160742011120000007039442c0d90010840f01b07079 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 456892032 1250 456890782 456890809
    0x20907050921010e0312040b190f0e06060a05010c02280608010311040c0f180b0c0705040e010903020d050c070302090a0b010305060906030a1502040902031008190206041202 76
    0x880060340b1142d2409060441181e1160100803c04540d2010019680c0d010b4000400b6843e142403000400140c0c1050030181c100f010115032200c1022800c5e40d001c2070303d21080381c070580d2540e43c060540b5503605c20000c01e500800d0942d44202014100700000b420100041f40203801555503880b01d546080b1000f80c00784090342840e40600042c1d465540042080400303100590345410a80408503c07440e141c400c0e403107858041c0d2078000c480b003903004068514001840d0744518183c80e00f4000501d80d90000c4c0240051084800502091400c05003003104951769181d480c01c850b803401841c8400203800140b2440744072264249039866030500302c40036182880c0c68000a4100d081c1d141400b92200054115107503c84090300d040c8895610001400f8001c601121026410ba021000b0280844c0d0b142501e00d0401810640161601d52500d10304c078181e03070066481181505c1c100c40c0c00c0100000c00e00c1654240d203121a45410a4081d0f600068a54020741c0140c07459817050958000441d900c0b91028000c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 456893282 1250 456892032 456892039
    0x5060d0501092916030e0c04151a0a05090105030c16030807030b030604030f0507020a051e01081602030301090e0f070303030b03150103050d111f05041109130209070509 74
    0xb08549454048503400203000da11955008405000f02c601e0310012086201c0c00b401c1854540d05012480b0413800b600b10320169001c0f600690961611589850144904600401d07542920302442c0201c003650020281b0a034040111041c001102d283d6803000844104003824684161a034480c42045145486044084030701d046400813440101a00300a020384201c11548080009400d408141611004102d07070090010b4407507400d40b03105078010409820040d0028111a20098607940400e140c0c81c2c001010122a821061504174250727030008040e94840c0b582e02c26648000a0b04501954900040c062101300e20f88480305141c211008121154200b602c0d201164125681c03810090010400088210301034000c4c03594000b120280701801904880d0b0101c01407206031365200342103885088a0b0500348440c01007103440d4044440c040d1100c4030805031440d0000c0c5e14103103850907032656002400018010743c618410060364400580d44c00d40942c2e01600c520205035140c035011116841500183c950 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 456894532 1250 456893282 456893291
    0x50f030619150801090506010e0d02040c0c0609050709050601020f0a0b34021e0a080c010605030d030e1513061508010f021c050c0d0209010509060705100515010f0305060d0501 77
    0x8586074403003c00fa04031180c07405c007002180c032070000444203404540c00d910380041b095600500142403a5001c0d10300041c0c245000e1502903441d686d01016035600110075036151b07102941c10302c482c68152040701e8210809000600c524128142d9060719200d429101900c0c6524000004600303968034540481860308804407a04000c0001e40144403100c1503075280c00043c0300740340012011200c48000c1081b8a15a0340041c0105151070356035550320742c4240e221061a5480c0c28001803e42c03002c0002c02c200e0708413600c4c046003100304003030705138036000c8600380d0141d0801c20b000a012900300300e00c0b040382c42c2c1e0303030410004034401c40d92008002c3c481c00e4a41c020354040d0318248410b805c0c0b05c541d40c06401900502d02c4004c00c44550000c00000f52542500c8403450540c0c104250034561810f6401402c0501040c102181003190f088001400c07034001d08030540340340e00503444000043c440ca00c40d099009500a03d01e03000c1128080008150f0800c018810301407613523a101048103507541c101e101611540c044c00a00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 456895782 1250 456894532 456894569
    0x402040e0f01050109061416170a032009060a02010b10110609010203010515131d150307060e12120307050a0f0e06090d0f0b010906060906050f030619 66
    0x92003020403140741842500990022a00358070038108803048031810303500e9109004540407030400c0d0f6440740c928005459560001d80000030010301e002c5a10f4136001d81c10329161800c030a8054203076014280c510b204003003008910f85448034946c069400100c1c082c1d49080d100c0c0011481a80140001c21302d45601410165a4075002d0b580022a81c01d80300c0704c0c0080d1400343e191011458240e0200b03000b00c541c8250000c1c01d440306c201920002e040a00d411000c000c0541e0381e500c60150700074101ca092141010171000030420b407554110064590618240c00400e00c580c41c00300c0c01003200c14003c044034815400c0303854221f40790404018140c941400c07811819628104201c0141150348040310000100d1070320400d180340140580c1c1412040c0e41b003c4d00d0f5a20b0582c48008000106103c0c0c40e040b5115030300c410122021502074900306005c0c0c0382449001a00b00d0a01a01a00d480329aa000c401005402c010a1011226030005d40c2d410940588000020014150100302c0022194010441484180c0d105a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 456897032 1250 456895782 456895799
    0x206120a0204170304050a060804150e0606270f06060403080d050619140409140a030c11040204060507022407030804020f060406051c021909050f0409150b0f040204 72
    0xc200b11050340d00d0f440f40782080011055200c1c0141e205595028112600c00c00199003e0704000c2e900511034800201c40c60404852081114502500e07200da59020604109441c01d014005e01250f00c10010740e0000400d0328294003032000b00c01400c81080c680040c001c901181c440c0340c07e6901641d400002c4c603480f1000c40c0007030350041c0382c215641ca100703030f642424049400c0456040c800c10741c3d100d0f01441811300c0c030312001c3c80080c3c0448a4100d034000031000c56803c944a06001e00f40403a8400d56820204060a00304000c89100429040f4441e510401081140070b402c14204c5050960542d80046038503e48400d41c640c04103080c0261001c101c000504034101075010342040d1040d8401c81d0100714003240310041c01903a0081d4050100410401c10007022000b178642e00162141c03920fa4405442c0042da0f4032600c600104c0001d06402044503d94284a60f1801543c41000450195010002d1405940380d8000e03690200351030615503907a90306d840c582c40d1141c3d11404001c8130068019035460780c2d180c440b03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 456898282 1250 456897032 456897037
    0xf0405100b121902090a050c1e070212030a0207090c090302010c0203030c06040f120e090403030e0a1209060e04052e0f030c0302090a0c08070e0a0906030b06030f070602070306090206120a02 83
    0x4901c14510751700041c006400307510400380240c682c07007401da06100300f007124207407120700c00c0c212103031003400c14030080700140d0360040d980000600c11005140c03281062540a49828105d4002c502c2281c203010a820340180c1c040e0400e4200c80e0240303000c5000c404da0317001203801c610603540c0180807401500704100c2440540d1000050503445515082c01d058035802e42100c028a50725405640300b00d12401080c0842e00c2a081640311038440c00c107440141d10380d0382c2c80c20590281c0c015003501040e225a001c014079074015200c40440b4000380c0781800680303003042500b02c1c104c080d048081c210801030742d072045515041c001c0741030140c072030041c0044400303440e0704207441c5402042c07004902c01d00c3c1800000e03500a00318018800e4448060300e9040b465242d13407005640200d070740001c054100d2105800021402c005015a20007540100301ca03260606003c4d05050501c0e03002203050900d6070180c0700402a03964001040c03422280c00050005013041c1070301c0007500500c6a5403038485800040740a0041c6899961700 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 456899532 1250 456898282 456898333
    0x1e060f04080a14010c02060403081e010602010b03100614060a1206260c0906090910110703030b010206070c060f0204050d03030c260c0c0123040b0f0405100b12 70
    0x619031101c0c060f54807114282d035240c045400041e041140450002406900032036005044503058101d07424001402414004d000d034010700060391108141021400c050141c0305503840e00c00000c1c000c941c00c1c000800c9101d541c071040c50f40984000102c131840c180c8104020910161140710600140d40e440781074641c040030510311868804041c0a00c0074010f94001081200c822000c0c00c0c241c400d136184002c209030104014014400d44c022550740c10104103a510580c03000381d500710802d0b515a205814020100c98050940c00d055600074070070f01c00526000001c1c00911917000e0808129108040000070190140764009600705000030022405c05415411040c0360900756603d1070602d580e411980d10044d042d01481501c0006840040f40300003907558010a902c500704000450544541d004d00b00811041e01d56811203902c0c024188001c001d40000403035041800714015030a1800c203516842d89550003510171980d5203541e1503000c809a02c1c1e1407020ba54045403102a56070065407052030007440700c540c41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 456900782 1250 456899532 456899543
    0x60f0b0705060f06010e010c140307060213060507051002070204140c1c05061e15070b040b0a02180d0302160f061b0506041b0f0906170c1e060f04080a 66
    0x3800a82d05007500c3c2c880610401c41650f80c43c200009080056803100c02e000313001d4807000c1d014061840c030070f0810001000303800d00c20325006a407482c2e220041410304085030403000410404020380d10118000042030700c454440d41c000141d03582034903c00540201148005001c040f0414800c2007481811240030b001a442d100903a007502010b101c01120032180c00300c039403e40c071000304117412401643d0f943c0041d400100180c10740300c0f0075109110f0b0444903005040c0071608449000100000c00c0440d554035034108804007001d60410228820490155030a0340c403060060007002e07007000a00d0307c00c00c03010841e014044408452541c40340412000000c0c1070162601017103030030001c6000b090890031641e248580180140400e600d03507a5170000c0e4052181b800c095180700c50080400e020101002c10390080c85280d0380090003625080d01500b00508900b000569500180004842501e8510408110f0b020200c015612100e401c0c0c0003a181f07000e02c580141c5030708004540414540000202080d900c2c5c050f0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 456902032 1250 456900782 456900793
    0x402120121210f030902010f0c051204030804031b0e0a0c170c0c0115080a03210f050f06090912030a2c2e0507030605030307150b0609060f0d060f0b0705 67
    0x542d42581170380c40c0904024000f81850049018071403064820748252031244058824501114050444540042d003013983c61190025040003000701450061414204417050f1720181442c0c1400081c0d104801000c5d0041c039a00c0329101006ca520950078a04808a4019606030606141c1d910381c8031a0070201c402507003507203422050014a0556030340700040710254401015801203da8044170180e410003505034003820038800c651503400807409400c4440c1c51000740005c003464490350382070a50300003509040c0904012414000b5114021418042e8403000a01140c3c3d03030780b5281c1401d0010403201e80040244000304510412811041c0f541e4a5034844410480d42d8a0244920000600da03544214400e2003070140200003401280340c1020f540100c103810005075035540d030700110b0b056620a0344102d440e070350411501e0410302e180c0d105100c04110b050714103d04006074030010460074859142c41211310a40411010b0301c1da00c05412240c094001d60001400181d40d030a038040591700300100032030701401903 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 456903282 1250 456902032 456902057
    0x1060503010902031e01060b03070c03180308070b0c040f08011506180e040305041205010518070506040608041e050303090c010c020109030206070606260705040212012121 75
    0x1409076844031500207001d01072000600940c005601004001e44011b95220350b070009140d10210b020318440c0702a03403a100c84040340e9140050100080303100001e1104000c107802d1000c514100709407452258413448882841d1140c69030461280034aa11a40850100f00404210010103400091554005900030060261203900a032500908105a01c0322800130300c200b08003500b2031506aa80050007410a0f502c2c0070b4032122814400744611200395801e0b9110400d20003a9000312580709041c1e04090060702c1c2e840e04110010f0014825807051008100c0c1000200d403e000c03909070051143c600154502c80d44144501d0159200e800c2100c40b100b0501418280c9401540a03980300c80241d9416519040124155401c010554000c0142918500e81c0c5200200b00e07001000a0510484541d07040c00403254607480304245800155001315005500510280d03600c2440d031041c881c10b40d42d0315004801092145020100000031203031000c1e02d0007012440390305003040041d00c04036290000350b0301c036018240e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 456904532 1250 456903282 456903289
    0xf070602070f080a111507060c030e06090f1c02030904020d050f0117070308160507060e0307050d0b01060f1112030103061b0c03030c1b08030105042a050d091a09010605 74
    0x1d034032000e0b001542c1002c60040c01c6c503010009650040b082001c035400c02c0c2d52a1120022160505440b0020a940e81c3c0500081007080000c140c2c022000c20090030103d419103031054880e03246002414807058444020003c0034000e006480c0802d501038402c5403501a0340d8458009004280c404600c4220144004101c1200e01603400c0f1207010020000c01c00240f40d9981c10358290305c2500134610041980d114080011828405803008140c03039990558140101e00402d4180b45440d84814410614003048100040000e082503044942c5400c10300c90440304da84c01a00c0115186030180c1490094071401e03041d001d2290302841c181d034000c52041250708200ba024590700840c940342c80e030104042e426003100091094001542000b00c0f45406005c084481c0c004100600400c00100da003140084014081402c1070301c2000d1500c80e9642d04d81103031501e211110004160003070260f0003000390000f40c2d0302801d28250000d401d169071104080c220b010940784262161101074441c0311095081c041d0001c0c0078074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 456905782 1250 456904532 456904543
    0xc061b060f0121051c0504050916020f0c09060f010e0d0b070f0c030e0d020103020d0212040506090c1012060b0c0a020f0111100b0409021c0605010e0f040803090f070602070f08 77
    0x207600c60f00400445213031290580f03100399190400301c1005010031000c1742c41c0c3c850200d09ca02032a1101400c128003400c1e180d02070f042510501d07030340709d1a0b030107907091600550780c5802c200e40146c0c5c141c40c003074880c0d603c030001290034003182034002c3d40040c0d10107c001c040041426031603116640da0341c2d4070040c01d4040e480403a4070200c0745101400007218242180c06520340724003641c030b10310700c1410010700d1f0680025008080e80c11110131007030300e80d8984080000740071092045139400039a90015100381103a060004e04a250204000d50400200c081da5401d45207190f800300014055545403140c4456044100a94032400000101d004810a22000e1110b50040060088e0040c0354409000d2000000f002900104080b140e102c2e841900e0b002c102001d07807924100c04c0228218505074107048211801c0c160103540041e40f21050000d200c1c1c04105040d40b003424010340043d80521040e94940b207140c1441e203070a0300310003500d129000e4564009406500016103404480040c1220b400c0107a40349406500e44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 456907032 1250 456905782 456905849
    0xc210a0c140d020d1d070807051503220803013803160905060c0a1e0506010506090d05010e0c190803190c330506030c061b060f01 57
    0x40240460120107880d43c0240102401810300041d1286a0b440c101500c0c0743d1542d03016086401c00303081401022014018040500350a4980248155881034007580300d203c0184680da081c01800b040129180c41380941d45d18268002e94810340300d5854002801005120904e9640c1e407403141c1c04451111900d03284101c50702c004540700c4030b04664520100301ca40e03119240c00e000401041e2500820075075500130152050104120040c0001c1c801894040540d04d82c078064091155100232103080043c8000410300d0550710107440032900e405565021840310350910800502e41c0d428134600e0001d82d03400048210041c2d40c00c4079000300c101c40b200603205080c4102e001e41403a64100b0044000d04d055050581814800c0600e01649030b40050780b5040c0e018800342c2d40307040c40140445840d011030150b91140c001ca03120340072020492803d0280c0081d07580c01107012420301400020511070035002c01201d0002c0c41c40c00c5a801d4a4440c5880600554005400d005021507284000300c2101010101c032001e1103031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 456908282 1250 456907032 456907067
    0x1605040b030a06051503060103050c010801120807030c080702060d05040201080604060518060105040b040605210105090a0f0209210f06040c0b0309010b0d05030705010501091e050c210a0c 82
    0x45202d50303102c55001e480d00070410010340c0d0704c6141c00c0700e02c0e4804102079402980207038042c211002d554800105220010391101c0b12220884888402040301141107504890b40360901004071007051070000018000d035500607500030000300d246030701c0e0b55442d00036511440c030036039a400703c3d551103208000840351a80211a007111510001030b5403d158486420b030041c405040050404d503450706000c2c15588260030450000c2e03801b0844104034036441c0604004030000c0e90240b03000b5030400000c11815a0024580d20701f054650b8080a81c2c5070385503046498050010384007140d034407040e040703960303003440e54050032070682c4510801d260040d24041000b80c01030703a000009181c0c061401280750420b400c00f03041204295600d400b808065560501da5000d59481800a90b4a400c0c49051150840748160700c061a010f00302485e0380783d6140d0540d04810203220100d000100343c1ca407852503800900803114002c200800030304d8a42c10700084084810302c2010741500500004503141c1c011258401e00c0745c00c2800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 456909532 1250 456908282 456908293
    0x6060f080a0f060e01020a2d120207060609050702070501110c09160516120f1106061e10081b040e06010f02010b090a0515010503011503050c070c081605040b03 70
    0x41e40b1448422100c500038100030500c690004c2d021401c81c1c0c040034148000c04c0c002e58004c2c2d8140081301000c82203044080345011960500800604206d4080d40300c41c1c0026130024014042040319401107002c0d060300d8000308894500104042d5a9071151300507140414001c40421300c02d0307040050a030100010180a01100d5101e0310f50303610700400300f10015014804280020700e1120203040030030900c2801103082151140b91141c1c00f51500c504141c41ea01040000440c070a800d00700040d40310342100040d1160100c000d50b05181c8400d0060b1208503070341c404a10513520721015844072101d4080d444074102c2c60000400741e40402145d01c940d10500748a28404000280070398054002c88200e680640008600740e02c00c0c100140010f903003110314510361540e031002d114080e00905001c2d103c1da5001c0c00c1c020714550601c1b0b00e251800058420034020103881c1c41c000307420040960250381070140d024201c14245074542c00000d89510060918007403641c4882c200290915281c021440401c82c050043d06 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 456910782 1250 456909532 456909553
    0x90c031d15100e04030503041101021501050f0d080f0304020a0b0408060c0f210405100903021515100e040507091404050a1b110613022805060c060406060f08 69
    0x71200540208016450068000d0010300740d0f8954071400d200c0d0780310790b4400350360b45401d2500c200b020b5482840c0f241154807415004601c0b500020086040d208216581c42400d1051000101c80340007801c0d00625407032010500c0040c11400001540c0254400c41304594403e460702100307000c0e0701941c46890603c1e401440881c0d8100d00ca03600912412080f0503415107040c055415250441841d5504000001208420081440b40500210070320424564090200b22520f46000b50384c4d6512415a5640c0d00f0301201241c54205088401440110007502a100f5041c000001900303640103400e503580903034205000610014810052503065403410036891080c4032180082c480184002881c17811115507031561422000f03500807214607408104d956007184140da1058041c1400300c0642200351000d180090340c0016074840b007841d900b5040010301c200d8441c0fa001c0d100200356000d40c0c4440d4100a000800d080c40c02400701c1d0701440f6034080e540500604c0ea6800d810920400076215085003a041103507800c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 456912032 1250 456910782 456910813
    0xa050312220503070b15300f060702060106031107060f061802091206070c03122003160c030207061214011d0c0a09060804020118090c031d 61
    0x40303801800e80e18004030100002024154800180030341075030b880d44085203100801503141c9200750f1001c00c2e642c0d052048403511003c40c00700003081803408840c880c101108490424150110400b51003e0412514054000d442190710380e1816944200107004004c00480e100e4000c6c0141010b05600740011450504543c44a50041c030182c3c2c3e03546802900d81c400001ca0704170120074024000e03001e441c01a602e51020b81005640503182d050f610107500001d041000c0346400880348400c4c680c060404910030b07041081048000c00b04524010480358401e00302d801d121b5005005981309034407032551108881100d510940c0c5100303217501e0040060740b010030103100c528418030891400c0043c914002c01d072602d4460607200351440907040341916084071207221582c42c5402152a8000000d060450700d8155203200041400701c140c000e0b1014400c95001080442e485030205031000b05800440c418650b8450b01041c02902c840a41d880000e8102001107107181c07074407807203180f115080b140280725884610070b41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 456913282 1250 456912032 456912067
    0x7030624140d1506050306040c0306050d0b06060c100c0905040b0a180b09011707061d040b0112050f06100e010804230f07030611070f110f0607051e0a0503 68
    0x40741a80d841e081d01c488500f0719a400070001d0076a94580c01e86a1400d0420301007180c80714000b4404150030810308101544a500300c0042d0950072403030205895403624042585031017019603401c11803003544100c41201c02c4580c81707910602c00c240d8032010101c1e03588003007000380c0c0c06404a02d80c0c051401d1100700640d0980c400c00c0440c01c0c080110120b035854800740001d200c100f00768001241035400445100b041c1e030061003004085d0016050002000a080040d2805104804aa240501c0d59101611071580c003444110f0030500350300764280040d151072680900808070070380342203021340c600c0c1c903a661082c2e019945c041101c2c03a042c0d41c0e000712580c031921907141e20320314006200711035a0001c4442c080b641e424444c100d8203111190003040d0082c950310b8120201d0720415002043da113400c1c03002c1c000086084401e0424140c000460f410544030030340008105803071070309141380e00c802c00040810400c4000300c0c03031982d05e0745100c3c060001541d005803070a840790701c42c00c8020301a0300100940171440460048 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 456914532 1250 456913282 456913297
    0xb03060112020901050d0e0c040c0e100504061b03090335160602180d030f090605090a14012c011205090703120504150e040515030705040903170703062414 68
    0x11900344d50301d41c50105d4103c600248501c000920000c1c0a1041800c7c04040d0b181361020394170300184ec281c03615030020f12400040100b480510743c2c0070f4841081c188241c0e007800185400c1071425180c008207500f0f08008010216003500c251030401c1104600604c01d5050704d030f11820400e1800b040381683d41d0303040025400004a070b1008216083d202c2040d80352085444900c901c61b807900703400e0343c07140800030b800588076503c0300042180c01c000500d565201d2020a00c01c540d512600e107001040303210300590313103141c00c00d407504458003000c260030381c040065183d01d551080c02038a03403d5450540003461800d131401114901e5003988140000c000044402a40600041c1070b0301d806801c140c1ca800b42d0146900d2540c414900185d140001d50009281c81d00c90260824440604200744080c14000f00703803940c40754801e0921070f980d200380c0c46080c075010f02200f8001010b0300c41003100c1450a1a8090001c00060241071202c48106040c0c46061041d034a0a80104540c2c2c0c540441160050401d410301368030490 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 456915782 1250 456914532 456914561
    0x4080a030f0603060203070c02010909091502071e050705011403010b0f030424050a0b030c0d12090902070b1b0c0304050d2901030311070f050d1106040b03060112020901050d 76
    0x400c0040404c035a0b1010b1400342c44269652141c802a50000500200d40d40d0058041c0624014030a00000c42e000c404110443d0050b41c0982ca421a6040c40315103421001640907000c60090340900030408040b07450000d4600907203a00011081005980c6441d0100b40924010040c0401c0010039134240303c0d01440d44548285403246411106084551203109010503008150740ca8400340f00143d809405209003482056000b0100001c155000030507491000c54094409600303c12510002445031a4800c05002c4111040d5901c0c1b205252101e90100116581c0a64401680140c1d110b100300400b01e8184d00c2400c4015800c1c18200b00810161029001e021130b0040b8101c40225000c00950b1150481d00c485011840310381d40c07542c00d0141c244142c1401e0032000d604801c9041c80b07030341c1049070003000b038400c266001e1031803600030325082500390101826251b00c8540850b0001d40d615807030000310300c070380c0c4281da50031000714062801c8000d85c011040d00780d020a0b010301540da5807041d00d82c0034022400742e40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 456917032 1250 456915782 456915791
    0x801051201151d0106050c1b040b030a0305031005060a05040e0703061206150806160318020306010b0c010f0c0503070305070c060e0309091806010302100c051c030c0804080a030f 78
    0x60b40064489407035440948038819002c552001c482e69400003d004000d207051031480d2a040303046d41034540b400c4140080c060b4485801c907100301d444952100c0070002010f400c49002c201c060030701030310755001103c0c0030000c001c0403200411142090070584007011207d4544a040ca81810001d26880000400c4e51081640c0c400000032841c40c40d03044144000d00400001415910740c92209994494540048009912210600181b01d1881262030110402842c0028038002044100d10b0b15032510800030307504d4030400c0004108401e00f48018400046da0200820910105010032415140c04c855100d01040c01400040c044c0ea01035002654030548500d881c41d1409031039607c1000326043c2c00c0c1d090241358004295080c0609200c3d43c001c3d007100340440684080f9402104142e035504050100900800741e1072640d00b80742d406a5800074121340d126082d6441b50b2148000001409480500140000c0c20a030600c000180500001030140c1e0700445041d10b02030740e5000540242c9140b00080e65581e681e0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 456918282 1250 456917032 456917051
    0x1020c0115090e0105040b0604020a0201020c120a180305060c03150406030606050414221a090c1302070c0603020906040b07050d11060f0403080a1b020c0a0906060801051201 76
    0x203110310745503041071207a9034030920300b0008550101d07012000403143c01ea00d00310600000c1503030700106a500110454001d030b903442c0c0008040b03005e030140351101d1903507115091b04000c5510212010704190301e0642da036401d0410703001c006180000360620000c0e2594000c5004a8494a040700080d6844040300c6012415000c1d50008201201e0580d4019248030399110014802c52a26001d03e0001c003100c2c0c0041c5205062420000401441000a040f101c0200c14421000c00c2502d801035162041342403260342c49454414103080e120030b0001d454510818940c040940702442c06e00c255400d07907400a00b0445014200074041d002135009003d2554041d800f40800186482c180e0000c1c80e1281c45400500040c1c03029001c050055640c03140d0001c07082d0800410801c0070441410100d901503014607209076030341c85018483c0010040101d2100044c503201e61001038070b076000200d0041c0400140c07010a246036540f40e801c0c084440724000e00c000208000010840c5140c000c800301402480b281c00003442e00c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 456919532 1250 456918282 456918307
    0x206070f0b0906011701060f0e0703090b0406090c091814070902042603120a020f040308070f1a0907050d0215160c050a26010609050718051002120c0102 67
    0x82200d15407620351101c00140220305c2c07100306a5208090060007032098a041c8400c490401e101d6005001e6081e8003140048c0c0c5031b42c4284c110001440d00030380d0304011400c2c24200074018181c03507041130303070014005d940020703c4018038030848103800d040c002d400c1080c080d00c0e5a000551100f9018450300703841074050108018101b80700034001031001d49080d042282c60090011040d441c49480c814807a04144400090301e42c05c0403501e82e000c003440d20010703a1101201c03000304040c011500b000e4402d40c0d01043e07107810001c100c441c1c0100c0500402d4409214003425079401088201118000c00d10340100c141006107041c14030607004014402840382c1140e0054010203011600221030194070603440080c0c1c0340034040207001c107401900307003500c04091039403d1200c0703140e402c06641d006c4d40c001402d212049120203429408540a4006820144414244008001c280b940b00c13100000c2c0d101004d00c400121482c241d0b01030221200f4035005400500c4003503084c0b008542001c02c0c0c0110300d54080180303002846e03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 456920782 1250 456919532 456919553
    0x106030501110c0c0904080304030f03020c0a2a03120c061407020d080901140f061201060308130506040f151e05070b09010e1c02010e06010b04090b030601030f0206070f 74
    0x10b510440b41c0d459090703280c02c8518101d9100c00660242d00c046080c4808291000b0440380e00c04e4050904818607480781900724001e01c51403152903580e0150207100c01c104055080200402100241600c004410701050080c0300304040c4002000301080f0806501e219000d0f5004a486074000c4000041a0364540c101344901c5404441381d10043e0041c0b102842c44c15009a003e0b5008018000200a03240103500408510440a0042c2d980003a907031001031203903a2200c49003070890f4510300081c44003d6503031030016855040203441c100e038050480004038140c02e103c0d058a02302c0300100344e100c2101e4a40784002c2030402900000c0c0d001c100d480e100705002d1030042c03071411029445c1560b4140d51001a400c2c085100000548480407603410708074403180344500001c410304429002000050202a4084213038010800895180340e80d000d084c0001400300c64144c080c20441e0761400d02808810708074001c040d113074070003404001c1101d58200c85c0072000d800c02ca000b4013056071182214480aa80b20740341d500750344 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 456922032 1250 456920782 456920801
    0x9170309280f090c021507020613080708070605091209010801030b04080f040b040e060901080a02010f09150309021003090317060d06051929090a0f1d0c0a180c020106030501 76
    0x40d1a410312401c2c05a04101b1910310883d080c0c0c00d4403586c00c003c1c030002e40319040984007801d80346008495500307111204040318265940509101e42e10202c62403c04080c10088030350700c00c540210081010750f420210125001140169242c5441c0e80c03e50b03550f107044110281c400d68001c1010702484084d8041a0004c201914002e400c01d03881d58a030104003268031034001c2000f030242200c840100021700002402c011031660900300030806048409085400e0845a03002c2110100250350400700d075501a03211940d82c6000f80d88491a80c207985c8400c5e01070b21342c0f0b0301005000584000c51810019502810703540c0020300100381e0030300b108007a141c210684005548103e5414090306a11800071950f125a000355085056546034003264001000541051550014010030030400080c950900e03a901418500e049603004220740b01203140c05406800d102c0030303502e03014801c0007142001480d005020804503481d52020650495a20444001500c1c00141e09800c3d5074031340d200800014004c1c000c0b91400c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 456923282 1250 456922032 456922049
    0x60f0b07060b040615030b0f03030a170907030c05090a090f1a0907030206030c0c030403050106080a02190b0d1a10031b0e10030b0114070309170309280f 67
    0x15082942000740484030b00c0c8042d2482580340110800c1850180d010140340a00700d41800502d0044c0c8201240c1c014178440c40d8150315010000c0c50704d5031207410055415511500c504001c8841d034070801d14541e155046c1c04040c00311691000100b02070324102d540356a00c0403a040e0007040c4001d60341e40d4040e00021881c0101c0d10814012800c1c0502e40001c0012580021030f40000d05803a842d68010888920014182c00402a000144540d0b2604200212001981d124008000055461055a80390a21613004a02c11110b9003000300d601d04480203071005803800c0d070810300c0c94082101041001003809102d100c58070b0b2030825a11a6980d03d1981c0c007014141c071a140822040040803101c18820340d0a1320300e009001c041c1c0398003075040d1900c941c080314841c814140040c0b440301c5000181c481d10012040b0444503d80007841204245c1e009000b5002c031fa4080c4698885140b414220a03224090047c449070021030158429820104041c6559284407400d680042481e48401942c08a1192a00003040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 456924532 1250 456923282 456923287
    0x30403090612150603050c0c0a0f06110a0801060e01110616090f140607060b0909030a0912081911070f051e010519031107110312041512060f0b 63
    0xc0307070308034031000b079005111001040381e400024035112150710207015400400d5920800900d0302c942c45070860350003070b000d6002c0325070440703440c80c1c084204404c1d0380080300c40c68180304480384071504c64002e40b4441200c54a428116a090610449002e603850506904005070400000481c060504c900d90042413241c0e0880d280103d4075802900320381c00c42d800b4112842400801b003008040340e000c6001c1c103010803a4003d40c0d5040d142415405480c2546860354400506401c0c420300880000082c611001c050b00c03000b102070364441c5c04648044480c20007a21940d0704001303448a010f40400040034400d018288810020f00c9c1604da90f15103100d60b00404180b5803c103c06000c1403600c1c600030541c04c00351250580d0403150500009190b402050540b08642c03c4100a0307002c01402904039002200c00d05607001c1c0c40d000c032070805184086210301e01a000c0d00401c18040c0074103582d80121000c0c2e074007c071140300f88541c0d030040031514001e0501d213030390700030350340354404100f45e480c0900420041003907a12054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 456925782 1250 456924532 456924539
    0x7060f0216030e010206072c0306010b03070314100506090102011b090501110d051e0403080a080402090a094205011502012007020301021b030a120b1806031203040309 73
    0x101280c216015460540d413006c03013041180c550101a01c2401400007030344010940074a9002e040340e10419030101d41c1800342c2c2c1c0010405454210103103208002d9a44d0910150f25040141400e500007600c120000c0050390350140220b09100d801803451030818400010759441500d030304c6200d1000c179004a00040c8100300100650741c1e202c078242101204640282c501c12544100140951080e8038420b0a0108200300b0a01c06003c6482518029608400d4051f920903544070300416a01049804900c40c507241408207084003214420810400d030301041c006003521010101043c0100f29447d0b0b4075102c00d5500f4103401d50010f98081c40040c4450301b0700072420f541404403003010640c0c840c14100442e03140a1a568024419103805100c210a21a440d5625800b60020902a100342002004515000c40e03844000420010082041d40311070703540d00414200c48254a01520658010320740c2c82040040c103515840408000c1d1a0440c10040c1102c0491510070210041c642040b50280d01140402c0f0040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 456927032 1250 456925782 456925787
    0x14130e06100504080606010807020709060e0412020309030c040b03030408010f0c090819060c03110c0708060703060b1b071505180105030112060c050f07050105060a1d0a0207060f021603 81
    0x80002080d00b0114185414807100d541d50b903030018076150401842c0c2d004100ea6500901001010f80f0340c0b410280880d03600c582d002c449440c4c0691741140c2c124442107910170703582d1000c000d4940d060801005003802500c8042000054040041c040f07906000421000a03012001d01c901280228044c0022840540d10040900b00004a50244140390414800c00006038001484030b4459070b403000002a1005c41c0a81c1100100b074101c0415822420020b0049450310b03000030340000302e41e0a4001c541096072504401c0b01036404601c20343d2808102806100214804d48258a11071131030801240c07022035955804010100c0b00c122100c0c0407460001e11461001c4109145000006080c01c1c40703403440d45805d0000d2066a89514040e00e05960b800c00303540d54038403440c11a10032004994419807112203a0615a0003800c0c00d070f403c24401c4010000000d0240d030400800c00c4035030005681301da110303a50b04c00018081d600010301280c038281c0c0c813032110385003e4880c0b000e01030750306410610801c8040d031882e02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 456928282 1250 456927032 456927049
    0x103050d030b061c0b0a12020d0311030d06080303060909070503030d020d09020a0611100902100305060111030a03021b01060303020d05030406140a0912030e0c0d0f05010501090e0d05041514130e06 86
    0x10100c0e040030000303100b0240e101c1142d10094a98075141544281c0340406050341140a0903037080f154078200303000003420400020103540112402c03141103990391203901341107503128010f11806825400c144810720046030180d02a0400c21001d26002ca40c04002d540007500c1601c0079004540810119a440140d15000304040c1c5a81612018100700c40c882d1500052610900b400c000010035032104000f0300640d124003d65500017401508681d00c1d074180050143c041e4019020b440d071145003091600c800032505004031030480c0d8058002e8040320030030304030450713040d03200400564489c1d80711a107010000e003685000f2841201c0c0c0d4070002030f808815107400b0365000e40d003840d4001018140b01401400307210116000103100003c441c008040c4401d4a041c410503080080c02a196501c0d11000003884461500300500f2691074006494610900c070300e06841600803401409149480b00f44a4660b203801559a8925104840201030800000614244040f43c0315040400c40e54425000e002290915150 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 456929532 1250 456928282 456928289
    0x115090c05040515090904060c030c080c1e0408030a0c0201141e03060d02130207020a0b1314011e0c0c0603060b07120507151a090103050d030b061c0b0a 67
    0xd12a858504800030554040e0380501440b40c500340d42103110884c1d061040f540a6240500f01e20130034545803d00c00000c0c00c070188100c001c2800d10102d8000715100314a00c80c0701d00714440410f801d244010122400d14241d0301d19049800d0360821010400020030030250414040c140c1c0c03040c40b40d20b030620005081034060010800c84610034820603003c140c2482000052800c01c5019640701d595880000384000c040c014060f40010304c040552519175016001821014001d49487c055903070345450b5031184e441181c0884404007540c81040c00501c1e00790303c4042440c0380514113140201c50148039522403043e0240c02c0c0d408140320310308400030400c0454210008100c10705040010915001c60752070b0074403c04100030714402c05003809040e01e40c0a00165440c10b80c20080360720700c016250511200425170003681e00d14014280c1501e28441c80c04507e685d042e60780c0800988501c1c400564154050b12184186d141c0c030120500184000240c55030038004030412490010903c50006020302c02015000e80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 456930782 1250 456929532 456929549
    0x215070512090f010c050304090c080105100509060f0703090e1603110a120e070306020f0a080c0a0e040519020d0f050a0e28170703020d080709120309030b090115 71
    0xc8900150356428003e2000f4420a00342003142a01c0c42c60107d0641c440d54102c9949a494403090001d02613000800a05a4034152141000c034030600c0c4082c2c0b128001e00d255541d10103001c10070505060103000190081c907100341020822203481360201c40603454100d62403010203d0501400d801c0ea9407501420905407a000b8403149000d20341c007002001982d488034a01c00302c684508001e502c2504c1081114005c5070046811921061100d5540b0751543c40200342c8400202c80c080407501c0c400b0324200700c50030b089442e201c1e611118000010b10018000040050070020085003c000074012103000400340c040c4039050000ea9524003080000c1107810207072181060514000c000b4805000014a00c035600c50f09012140300001c101c2c0d440d0808a036900030040c103c040c8030103400c0c0a504c0c03020160182921030307000c0c3c901004007010100d80c0244100c0c3c10b0030018812017070400460500dc645041024042c0c034081c00301e15182e403203040704c00b07000303441d0b400b82c0c0e81d501c904401443c40c4041d041c1015000c182c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 456932032 1250 456930782 456930787
    0x5070b071103031b040b0403121d180901090b09010209010f091208090d08040602060a05010b0304050c121504050f060108071a09010905300115030f0f0215070512 71
    0x8207030320380d03a01000304403001120b01202822800303940e40f000d03034000381400742d041540c490f16460302c0b03400c00c8c1e1522841c401050000c505042158041d170485501e010000e4030061991408800c94601c44030042c148050075542c030080741d000310705601d590300e01c150190400540d442018400040c9000c03801c0ca103000c10044502814021403494000d180411500100240d440d0108200041e59400d03040c031008200307060005001a2064011981e03600c140960b100030000703aa40c030b84440801d031104550040c0303650044101046540740142404c84001c2909044544054803000c41407000312054400365455808280300c000c41a0040004601402c14903024151903441c0c200c0e2180350322a070b07540c80d805039400401e18240c036034480e0301104010000104981ca401e032070004000c804209650407100300c014644040030100d00c05020300b404117051440c190300154030f592a4004540c082104c02c8595014100380d0b4800b41ea42c5101c45000302c0c407060314141cdd403400580b400901d020486c2c80c04c1c0825502c103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 456933282 1250 456932032 456932057
    0x1f0914100507080a0e060a0c051902030a02010c170d150504151208091f0810060e090c13060207170d08060d240902030f0307080313140d05070b07 64
    0x1d054400707090344001c4a50312003544a4060301c000c800c0c502c8141e0800000b195100c9000d52181420701c404e03020760240c840601c5001070b80e504000f8440c0700650540d0080d920b0700019481240030081c8940201c0300c0040496106036202c140390312100300401010345992800102e1038101100600a09044404000d5140b546280344200c841510405515642a59030b0809210340801282d100c1c4a0003000c1d030300c00300490302e070840114855212101c006034082e40000d120101c0c0380500070969000392205458206e04c0000c00251040090806c226803009000f59804803080311002000307400d441d00038140a9041c05140042170f030042c120f5030801c2d0700410031680901e80256003a030704840b05442c08c4039042c0c035605156024020307410303454030340c0c28192040c49003000d00b9521203100c46100302c0640d106460348002035943d0780241c40005c0c051500400210b0609a944181513196500c1111750034401d100900301581400c42d43d841d107a000c00c500050f41410081c4003160f55070720086600b04409500c42 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 456934532 1250 456933282 456933287
    0xe0106050f010e090a0b0d2009040320010608010908041e03150209010c0507031b050301050f0721110406030e0105040b071404030204090c030302240c091f091410 71
    0x2803140c6544c010215080424144409900b0602440c2005403030740c102c251040c900204008140304c003540d0a0541c00c1c130900c0c01e83c40c0c90071501e0700607609691102550b1038124144120b0480c4009080d09540d80e900d8001081003081c001e5068150068007220346861600035100e2000c0c610b0f050a15182d0f20180b003e20000d1180c04d00d02e00c07150a0401d00585070140718006840725513201d2800361039442400400403c0003642c114002494220440b004000c41da250141400c0c0c0703d040c0c03200b02510480000250340b1a12540f42e400c040c04030425840800d4100500c124221150101c12200d006000101804442c1d01406208404d12080c2d00800c80c0b403400d912850146c44000e80f0090401001008800711540440c040c0d801568001f041017189079001c0c50122030b0b02000d40f200301d000d0702512001c05044050103c03c61881000201e040341380307076120a04141075920041c074855011001c01c0c420300002c08240e1002808607015100c0300406824a0000401000c00048087c802c02c41e0f844826290395 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 456935782 1250 456934532 456934547
    0xb01050603010f150e18040203242d0906060405010b04060e0112020408010204082503020a0b0c07030c090e0114010503100f02120405060f22080d0f050a0e0106050f01 73
    0x4501401304d81c1031010800007101c065425040a0394040030414940c0a04408844003a0149100702c04a8080740910021201d2000400021302d0014440a0001d8520b81c02e40040440d5050340558103803417140b10404103812601d0075100820603910440070024070742014480c60b8003528540304420b0a00e4580b11b00101460209aa414100142680d001c08070007040d170145c8020b441e000000355182c40d254688260b03900d0386542c2c0300a1040103060b51040c00f0350202120400e4036000307080c0118907070a21098140c1c2d944401c40700d80582c824000000f0201d601100c046001d0041401c0c040b5401510740100e500b0b42d184850702c10303000d107000d000400003694006130900d4451840b100221f040040344040c01c009000340c40541145040210401c13041000214032203110304170020705034280303403202d02c1d41e101100f80d404403280800050040c158003061079000a040711100820003c02c040241d400000151a0140e170242c410702e48800300c0c039004c0602030180401410701500c91921b0b115451f40000e0251 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 456937032 1250 456935782 456935789
    0x209071d040f0b01030609150e041a130203371703010605040317070809040506040f060305030c0d1b030c0201050c01090b040c09180209150307120b01050603010f 71
    0x44020414020036140360400884606402001000316010604044018040555126001074940f40c0086946d10092040500c204009058a010242046241580c24201610550b000c0c1c080003910341c80245482c107090302c168800144590f411025205040c600700c0c113086402c403821101e03a007642e405000c0340480c0000c5001140c04aa080c2c2e00c0703085c03065150300340c185403980052001001050154000300148101c92259a26800c107140740c0798004014015817000410a4904004450003071900c0c0c0c108a801c0350700100001400c422401c011002c0300d2540d031044810350004145241504010300c07800f2a55207445c108461140356289020407070500c07443c0010148440443e040307081d644030700199856104d0941c0208102d0005007401c501c3d501040300c3c100c13201c41c00200007140010250245a458100c21005500784004c1d680c02c0020110703004107500729890544030611420390b010004138000344060481c0d0358440702d807810001d0300814141c002ca07000781410001040000384046c0007608a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 456938282 1250 456937032 456937037
    0x2010816140c0f070501020d0903150e010207050c01110a0507170f0607080613090302061816030609020406150804060e010b13020d1a0f0f0a1a030103030807020a020907 74
    0xc0a0004019100030000711400d8106040c0829440360350900060200b0a20b542c007821200c0b290707691401241c0e1141c030480500001011501c042000404400038004199a0303004042010319041c1d0302c0c6402c90f0441901907403260710180c01e0f2000c03540c03c02d440c401d54202c55405009204120340b0b0300c03645d55005114100c0c0c201180b440c10f40d5440018450010510450000d0381d40b941000c020013029a00265142c3e803048205c1000182054100e01c59140110741c983c0246c02036903105d00305580d0340c072010340300042c0c0390040310446101103854120b0000517504c104400a8405d40d10f005103c200c903010382004401c3e1746032800043e4080d4116034019400f96100f007010840201486200d0f0241121004040d000354080000841101c200e030081c120070010b0300010421401207010054200980a2a66820100c81c0c0c42030040781c2414848200c068002402c064001c03941d03400c000ad00300c400c50404041499000c0018010035600014082d0031032803030300c02010300c0310751900020358441010703218006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 456939532 1250 456938282 456938311
    0x50624070f080706060609030b061912050a0233040515030907050406031202060a0b060d0c1707030e1605060a0305071b033b12100f1e0207020108 64
    0x70002c0341000c4800c0341d5400034061125030740e5410068030001e001d00044038800d450000151301c80c18a0715104400b09400b0105144051500c4c24201c2c010104200c2998603000307100c00200540c840c89402011203100c100c0102c1600c20a010b05410712928103240d03491400c08010810403640e9280e01c001441c9000180240d40307466007143d5502c0c20700140e204603042420440008184080c41c00100004000341d000e80d0324a40e0307200f4459084444900304607a200f00240908104140180d001c200400c40d1818102900203464048034081c40080340c07400300003610342141d0090460107101e0124900b906000c81c2c000142400c0000d0101e008010580c2c04159a41e00051016803184030401c200e0341b14209a040343c070320a410010406d00005160f00d001e20480d0013009a0400c2182d03020820f1010b800410a1030240041040030601c2104207000382441030782c4281c0c040c40d040788504000e100f00c03c180010144518041924078815001034030071040d10501c03625000d030b41c10004842d80a81103820145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 456940782 1250 456939532 456939563
    0x30a15051306050c1e071a0705071506060e030f0601090207020f10020a03020106272f0d0501120819020124050901080a0c03080d110c0105062407 64
    0x54180420000240801d8201002e0222525046005025016075a01c2200351185039a401c5c1203107109a80005045541c0c607105200030240218020b9000552890402d01d4501c0e16180c1041a07aa41000002c00c0b40d507a84d400c002160f045040711141400690240070301c005c00607400341c0c60701c40c1445554038180d0002482c20442d0b44410b80d881c9900d500804200a92980103030082d81c0b100b0303181048025601e0280085003c001000d090580d00b40300121410303040151101400140003417800580f10b64841140d10101c4107080e0420a41101d0400d419580b50200722510106445042c0d1044407103514203074440f800716446c01c01f01c1d6010300f81c140159020160804003280100700748003c05000a0591188800c07400c1444480000c40d40203c62904013039807100c900350346030203880100401010a188040000554141c0a410050a08040040c1a980060a503415a40440300502e0680d545504110941c546950a0b41020001c07410841c00e000064802c030400d4800d101b4003400d9600340701c0521 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 456942032 1250 456940782 456940801
    0x6082503090606030303020a140910050c010603050a120201050a05010b070602091306090204090b0f0f010f021903091d0c0f0d0908070c0f060813021c170c0c030a1505 73
    0xa4141c5500441c20803050f907403410300800039080003d4610002d92600e10030306101c040c0006070f0313800c4240245001e15a0009900275900d55100030000d000303a540311580000490800e011068a05020710103000740504846002421144000d25044010b4030303080040c01700c01e0014003901c0480354020801a507983c00c880c00540c1c104041c8500015290130810045103010582c1c024104542d86000c0c14441307400010104200c0d5810880bc803600320000c040341044540c03059040204001541c0156403810f194614840c80b4414004416800304541c07039000c0103c006002e20840d101041408403405605041c80c01c5070b840c1c0f2a4508040051402080c0e103080031000340c3c00b20803210f500610041d594840d52405483c1c0da56035104842001244120006031580904030700ca1103142120700c07a18441c08983c2c2001400c3c070f2a4030746a10482c080814a4001542aa900015a080d1030f80d99640b0b078505030a100d45408082e0320494006d4000307a41c101d00040144000d00c112076070301d140100e01c55481c00d000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 456943282 1250 456942032 456942041
    0x307020d0c031205150a0e1b091923090702060a110c01051008060c040e040f080d240b0c0318030a150203040c0501092729090106082503 60
    0x15103aa071622042c003000d50002c0361a006082800d4a06e0a06203548214041d0401c03000c44007503a80122501181885091407002003400840040404204000da00d5080c84141815000390559082c040b040d0b0200e410f4121404a400c041210301000078940000000c3d15594054400c07a40b00e5245d12031015040440310a42e840e0090b804000c203c0e40c0350480c3c40c0043e00803039100d4030240307018031000308000074101c01c1241c082c0d510101002910b52155507501c8415142c814040d41c01c540c041c44625007000860241041d00c071800c900f400e070100400c00d040e11461541d81d004400302c41d4204a14410070001200703840705400c0c0e4030780e00c5046500c00c101084c108101080000c250020024034410190300c1c95000d90f020754091200782d9001740d180d400545084000740070f10700d48a1181e0000001508594144840680380154089600900315410105440c060b8280e0781e845080c0c8001d0b5031140c189910000c2c010a05480c1c0721085040032000d462a548001d40c28481e90107040e06610f0b6841d009400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 456944532 1250 456943282 456943307
    0x910060e120f150f0a020f03040f080717090906031b010e240403060f0216082a010903081b07020d0302070302150301090506100e130f0e0708120307020d0c03 69
    0x261503803a25418161800c40358202c9404401485136000b00da00184d5510070b540c81c0841448829145403a5a02c07a9084103840301c4080340d040303408210f01c00c0000c48109441102000c03103611962640414802c024600c040100054025070204002e03850b010f00c4020302e2410b0b04000c1c2400b540d6200341001141444002d030100c840c2c500c042d00640c102d0440d0410060040347d000c1c28007003040051144c0300005a1042c0604902460320f8890741c000070410038001452a00161034201032145a0b001ca1004075205500d10500141d659444c0001072542091103240d000c0391490b126480c05c4614244c16403580202c40000e401000c5000c1c20750100b5008203c2880035580091031007520355003101c0c002106520034061844954204030102d0070341c0c140041021410035040d103480c26600051803c1c0010219a215000c0a0350b40701c00c03510304661050300c180507001d11081302800f4043e0810f10240d14003800519548220142001042259a404580c030b40280c601c500d48040090340d82d050440e0b41802040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 456945782 1250 456944532 456944563
    0xb1314010603110d0218030706090302010903030305090309030d030b04140421170c07031b0203060a02030a090c03120212030c030c030711030c0d080603010903020c0415120f020910060e12 82
    0x41000c042d1b042102c10041c600001c40c21201280c6c3c80c2d220448241406203c000c0c01b0845c0118148002400394101c540e000c2d0002080342d0920103031a00080ca0300e10104408000b007581c402d899012420540105890b9080c3e001240100381032a80c0c030260281c40c00c095080100201c55540d1031420312640340300c1800040320031541c019003841c1001010f65480030500b03c02040040c440c0341c4031b003501ca0389402d1559070020040d022903131351405540040d50000f0f1400782c0103956030003600001191180c1000296000709100f401903042804082d113080c420b144550010070051040180d0142e094080302e510071150121071b52a031311030b0181600c02c00e154000844140c000840d01c0818040001a6440c44521590b40c0b010551510307024142210110320380940103800ca2603e61823281419044036189510a0500d41880c950740d032403100b0450a200c0d41150356190040040e01945005065241c00040c1c05c00c603101d00503d0010041c050b580400310080c005d0403810380e4250460b0051060350044c03042c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 456947032 1250 456945782 456945787
    0xb030601030b06040c080403020c12010b060d1d070f030609050313090b01140c10410a110403020f13020f070501050a060806040816080a030b1314010603110d02 70
    0xd02d00740500c20822103105006078641200302014a100b082c3c51401250103802809000b0b81c40310605c031705440d000c155442c142d034a41114846540b40d40c0010a1015064100041d5484200400c0a040b0b0000c1400f02480e41c84240c0503c07848244450920440351301c460000740c08840c40c40d00e18214000c24050507107100800b140000e1641d41904000c0308880240c0c2c60f151101c01c01c0d42504032a02030a01c280c071681e4000355600080003400d40c07015a401d50481c0750304545240035140d000c0d40c413400052607019100017000d114074490329a12001d400500700002070103152608079041e0303001c1c016480044d00c182403e1981000a0304c5104580d00b80d1440514159aa0342c0d0003000b0900c0750340191000c584561801c000100c036110207104007000c0d511914058000c5407103607110f03400242c1003280344140207804030941200003010b200003024000300e582c80c0402c180d1100341c10040c3c440fa18001800042c0d00700306100f4030f284001e4035510b055030350a08000400308148517200a0398040c035440600b843e03100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 456948282 1250 456947032 456947039
    0x61403100b030a0f0e01050f190b191a09010c03080c0c16060210091505190e07050f01030c020d140f0c0601090e030703090e2d06030706090b07080d0b030601 69
    0x55410501e03010b0f620440502400002150007402c1f00c5085514014503009240407800282440303114152a1203030003408944100071400050060307560911003c85d1102c01c80302080301e841621840400320661000e500d040c8110b00c00080c1100040c00001410809000006090807c612081d900d11078898408c68a03801c44800107071416130b442e8003c40e00580309214070020100030b103000d640c5c0400d0740404680b50120032840d0407400742001900b42cbc5409002841c1000c1709810170b104140405410400030888140b900b0305204e001180d50a0386810942012000070314280c000070b841c48480c0f96460094002c4089031403007042c40c001c481031180201c0300040c59044d10707031000440340d05075400404200400540e600b401607072481900e030010040740000300c081185003200b80349142d014681000c624a047c400a2a60401c4840c2003031504075a0750310300038405982420010540030b8500c0781401094103003028080340c083d004030407000340140d1000031034400b01011500405040d107405022138019584 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 456949532 1250 456948282 456948301
    0x122502061005030c01091206110f040906150203090f01110a050303100605041a03040213020c0a050606040204080735030a02011a060405060310240e030601061403100b03 74
    0x58440400c00710020802180030715010030a4241604143c40e031a58075490300b03207001801e2040d074030203540c3d40f55075040d80206c16074020003c190b0401e0704041c4540e220300f04100c1000b101d0050704240c45421042c0d00040d061f035000021551a582c1c100c68130351025400c200101e0301000c00010540d56800340b0303070304007003004000400b40d8080c1d08000314080707086803581d60807a40c50040d0721401d0090314500140712003808046005580050002d49800085181d5151000503644035002c8040980c0c01000c00700203011040c0009900700d0340440e410351620303140c2503c69a644509000f100041d041190f00044503603510045829410f21590000207134825448800e44c803a041b4946842c055400c024001540718100c0c0303410000311900400d0141014200824407030a60001481c50000c081020800304440d15001c514100102c0040c00d0302030b203042ca040000f84a2a080c0e22003078040d40c0034100501500ea00b1140500000c942000c1051b243d9852100e0703035669161603404001080130010510182d9103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 456950782 1250 456949532 456949543
    0x130305030f07140d14030c190915080f01051c06091101080a02120c090301150b0307170103050304050904021c030e10110615220912090308122502 64
    0x500690301d898600680d070f200b20b51240001c0c01d00c44001003402c00e0320440d850301c42000c3c5821188040280381844400000200d8040056052801161505400b00a26840252240302221b03c9207803803640c0d414920380d241030400040c017805110f600d801d50944550700010800700440350308140103000d502c40c00e003003500012001a401c41e0002e50320500140c50205c10340202c94030b03150210854401c9130340310914203405070040e45407103a15548602c41219805507121200c00500b14103e20f055072030505040113890394012319100c048198200b80100007003030011007500c1c1220416510348009a807070b840041d100031b141a00c00b410b07034054a00048140745c0e2000380c01011210685500c10b01c24280c8500783d941c40707240d403e4618161301450015410105840c404018030340054400341840c000310078030000c40c25050784014100ca503604a9074091001e6048030081c650443d00308803580c1d42c00c68440e941d540c0714079524441c07a8584c03080854800e81022490802880900f114810380c000c00c0d190094454 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 456952032 1250 456950782 456950797
    0x60f050405070212091e03030c01060612200901050405030f100b090609060f040204170a0515040803011a2a071401091806050a03030c03020d050a050708130305030f 72
    0x303a280500007440680000b452000130b02c07882c60303590f081c02841c40801600640d03c0a10b5010040002a503580c5038408101a24002d00d40c1c0c00042041400d24400510800c4030f0b00c0c0003032031503061150540c0881590440c085412318260000e9980e4032043d401642c240c85164800f0b0303014490840c140c00408000b14440c4c03055041c0343c90500c158204681040782c0000143c80e4030360b11070302d0b01c4007003a141c7c44c103006a540e600c0406070000d804e05656101002c3c3d00700e1281840f1031146c1040011904000c000d1000c809150004d41c4150032904082d101c01500e4001405010800e200700911841030091076000d403a00b940400032600c1104d1960401d502030110810b0055107135100304100890520601408032020140695a500c00540b80a48000c22088030070361070391003d95609004105a21600c0204000d103009031101d912880c04c514009203005041d40825040020501502c1701165121045410f042d402861184d211880860084c03030301d2405510081141c84000b032208014286140a003421 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 456953282 1250 456952032 456952039
    0x70f270e0709051807030203071e11190309050d05160f05040513081c0e060405031201060801060509060c0c100315050a050d230303010f1701021327060f05 68
    0xb426a90350901c00320001d07001d80340c20312409803400102800e00ca0390103980c3c003502e640382c44081035144116404849402c0420a0001100e8810013440d40d00200030605200e501105e642c104046151801414004680501c9101c0c00c45400c0301d40502508204100094101c60309a440440e500d60303498680328801c1c40307113600503424400068140c080c00610615440d4014401500c1c2040b14402c4002c140f0f644038550b0100380d0740f07401200170001d042000500c0350f80301e03000940e500c20341c1042c07000b1241c3e41684410308006c811001800f20590040540701003000503941e0507103071448002c0030780c140882d08461a80280584018140c065410b0f0040624941342c60050700c0e0071a200c03000c0c01020030075030190a4001803d00c0c0b1640000d0344442294840c014440d0b0400240700005c00d00d80d0541e8801e81c0091000c100183d014000c040d004404072100c1c548c00402140341111015803440d45034010310400e0030341c2e01060164000072044c4045c1c2340c80c403803000310208001c0d501c520311805503503040e0140a00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 456954532 1250 456953282 456953297
    0xb0c010515010f020a0605060d08070b0108010b310e25050303130315020f0711040f0911131503060608240109090807140a030206060306070f270e07 65
    0x8a0394081c000f00c2c800b490240e409000e090301141c42d19070141c500901a15013000300c078001e500105540d84081c2101c184202c0c00050301e075242c414824207541400c100b15100e00040000406031070305020034002c1008441c102042e0841ea1202d5400003070212080d418154000c448502c80c4026454000f4050b00395521007219440d5110310515550b80206401d01c1d2000c007030804103001040b0320032910402020548805413600c071080a50003030700e410124048a44440071320302c0380541d142900803525807822918040000030000d448000c481a88070310858054000c200512500c0202500700001e9020540390f202141d62343c9241c594000d02413441003443c50b00490745481d8292400094606048403100045240769081644820040c086000110346501d01005080001360005041030700202100c07000d044810320a08003e41403d10051410b071190f045034040142c6250450310f44200e40340d6a00d801110b141c00c07c03140c24485034207800000c0030144460000680e2581e9a5011485128550346440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 456955782 1250 456954532 456954571
    0x6020a150213120f02060f0a0905090402011202031e100306050c030c042c0109020304060509010b130f090b040b0718080304060c0f0209010320010e09040611040b0c0105 74
    0x2203004050200c5407030680b8800400c118002100100c3c0d42d00d004080302c3c041d0200030f500203000341d401110032001c003800c00718003003103410b401003042401041d058809108500e442d40c0001e1607011444500100c0c5c4e5400300c04501c0c409100c000140f6159085011380e84242880104514119618402203c209043c94001005044e00a003981d00a11107519080c1c2090f007030944501c0c403809051f1800d00c03c50403101d8664000c1c0140d030b00140c001d08100100681d2401c0a0501c202a100c2c000c001a401e41e04003543c2400540315041050038212a001001611404032102e11029100000c0080c100045840511060140208200b4010341c90754490250402a5122a00c0780da126881503800a03042840100b090303a000d8560103040c58800c003800c2510404541c0003c420b0202030304240d032480c4007103100005082c02d8185500002070f09003040469810700340002081c801c0700a20042a00b601e88640c595070b10400006d5030007500020340328548030660822414000c0000b03c5000903454010315040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 456957032 1250 456955782 456955823
    0x20a0512180d03090c050d150f0b011d01091a21150a1a072d150b0904020d21031b05070807110112020406020312010504060e130303021306020a 63
    0x196002d0b034840f131808401c5d45003804003c124007484409030f414044280c50302107200c4440c802e800555450380800243c5d4030284000500f0b441c1da81d90a9006101c440041013440da801414610407038a20b2040c0d4280f80485407501503030b41c050700610604c0e441d5168178130014040385000da5403048a215058048804040c03040103d0078006224507030040b8070024850780c2d0706409200521140740100403402d810501c8c3c0f151444040b034020f103080c41e244c0c40000c211040201c41e890f801310781c400b40c00301444a8079000c000527100d03042c041d2000703200d01c204031b0364901007007010240d00030914140900e05280c2000820050098800c103007408042c42d110090030680d480c02a0305071480f8a40048000703060015650303618165904113002541408201040d9100101181c0014005820142d01950701d6428562054800c5041038100d54461401d00c64240090910042e0960f4400b942460459a005203070800794003e01c1414501c00c00d10310035600c00b02d503441c0c000540700c1d111485120b0018040d40b017813a21 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 456958282 1250 456957032 456957041
    0x63106290a0302030c1b0f07060203030705040519030501020f130f2601060527090604172104140f010b0603180f0a03030c110d0e04020a0512180d03 65
    0x180c981120500031180391500c83d0b0f025640c8a03c45007401454807501d06034681e10040786500c5d00700c50b039101403001c0c04d0b5801d0600c9141c1c000d103040e00003541141856400034049010714000e682c000c90401c200c0d0700c0d1062030f43c00b250005540102c000c55071041c000b04010304c581d0281c0754019003010184030006010352019408011030348040007410140508050840b0030750304200743da503c81d40d00c03104040b8603907940b11480d40440702c0c40ea0200104c202256240000c8200042900c101c40e042002007001241211481400c141090030049903251040540c1072406600c3c03101201c140040502048200007550381e0030815089000d00310b03400103070b01c104814245c444640005410040500201d030084c441194241511007508094600441d1880b1100303242c03c0030007805900194692262005d000c0e00b12a00c8041108402c1c05032800400400d400751561840000d142d000e2940003401000c02846082615108012440c0c041964100807501c1c240100e98000b201480d8058510607040d1140a40b15 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 456959532 1250 456958282 456958349
    0x3180705010219060b0405090609010b031216080c0d02150a0218240c0a11180411060702130e0d09351e0c010801080303063106 56
    0x80000c043c10320022181d0110b03402c0c003110b0b403e0300c1c0c140404043e0303900d006051146811400404692910f542070710f09461122003c14085d4101407104648201003104480c45024980c0c001c1c4459400e61030190420300c01c2c166a03035118040e01c000001825030219941024a5111010794000d0310342101101c22442200c0c402070256841e5812203415040529090b900d501000071201c00c440c01c00c0d03039201100e5001a201810640000e665641040040042808000000d8900d000440d1409035082200800540b01500030725440c0d8180010b6a255000c40d40d8095006c1c2041003c820079041d130328007601540740c2715440e41c09841c0c00d070000f952140950004544500e003075000110b2601446c08810745c42d003405440e451060340c40d1100403030302c204206040d0041c505400700c40e55130390121050520311b45103031307160401080400401034a1000010760b03030407820445000590031320fa207541d40800c20040341c444031503100079018584407000e1a804001162403200b80680d4050401c1c00200c800d070041013 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 456960782 1250 456959532 456959537
    0xc06140c06061009050d06051605040e1305010b2706011803152013050103090c050f01020c030609010605090c0403020604180b03030301091e0501081c03090c06050318070501 76
    0x10010b0700750302c2c02c01c1c5411110521403d000c450b00740c82d00089100c1045a030001d031031042c0c0b40c4003444280c01c00180307240f0310284940342113402c2504000500c01c086002070509101441da2011200078040d00b94040c42c41c40c0b00c01040021b0600c00c18200540c6038690001c0b0541c41c503a4580000d560307501400d007849560f0b02d001480000301c0d0075036403054a03920800d07034003115081c3c1c0c482c1c1d100c1d2031030b1180b110120540396400440d512502c02160b021203020751600407134100b500344800480060b1117940703401c05561b8100d030785007005c0d481c1c040103d150001c10a01c82d039041c40790b02d0500014100643c4643c00f0390b00d05480c2d12045c0c0d6580b20440c842413189200003074114104110070012002601071800310354000034404141110400d00092442e002a0481d07441c80ea41c4040464a181c0c1c5003250000038000e91005008030340c904114181c42e044d03030038080e0680c02036181070b20400324482e90194078440e030320501008402c0e4803000b00402e41cbe0000ca824010ba4145d82903140040320000662500300c40b03050703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 456962032 1250 456960782 456960793
    0x21c0c08040c290406031401080d09090b0315040c0f0b03060303040b0a02030c030415030f0e100e12030f06120313050f0103020c03070b040b1501050f030c07020d0c06140c 75
    0xd2030419020803c440622000000c0561129030100b02c2e002400185a10780d00803442024954100c0c03c5000180d206205a5110303011012440c0e400c10070382411102c10500004404100344046420240c844034200d80c204d03212001c010410041395040c006a4030342c21410400961543c0d4240344c0752000b034030361961560080c081000103649420003046031003c28416a0308119908043c240341d45c109800c540c003600307403003018094102e90500c90880074540b200c00620042080009550b11440c0c04108a8070391a200e511110110b1400c0080040d0806a44100d540d00d1030400425013001d10140c84c55440b40b000000105040d0200205030380310700340790000c180052842c010800c0000b061081080b41031503003e10400c01c0202c0c040c030161145034042e03d003004140c68140344c00c030455200244010000c110b08404030110340d9010042d1000f81c038103660115940d448002d03040040c7d0245000c000c0d88041000c00a17010080c5803c411003c40780c0390345904000000300c5011139031b030b4001e0a00183e03299009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 456963282 1250 456962032 456962039
    0x1090204120b0a0b0919110414100e06070f020f03010c0801090507020a0804030b0a050c0a0c020d0c0e0c04090f0506150d140907140d05070513020d021c0c08040c 71
    0x6401049800a04071070300080c00940d1400445c8079030034200c501a101701c40500761140841d11502907030345548516040b9600d800d080010f0074500542280d48c0e10b0007500b1007540303556528000c500d030b00200c2100400701603d86116161000c40540010780803400307122201c0418a0301c0c2014000c50038004a540c4132440d00341c2c00d00e00107200422001b001131007113104019080010901900091010b0341c012a40b00c41c444c5010308000082d00e45c0038280150b80802007001d0504907a100800480d201d07411106044001c0c03840c100081c0384401a08070308440e162400901105d045070f80c0013481220b03185c40081c00340120b038594010864400301c1e801608051690740e00000c06100030010208902c400308000780700341c44a009105010001c030707044003003031740018810b0100d80349080000c815024100c61007414583d10f80c2c1e0350307504c2d0115803245500a0f806041042c0e04020a90145c960315140c400c070454943d8600c50f4214109400c40208420306481e2500002c0c505106803100d030320498200e22200210340c078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 456964532 1250 456963282 456963293
    0x4140f070323150a030b01060509031e0d020618100509010f051501090f080d110a0b0a060e061f120b090c132412020906030703050901050109020412 65
    0x10020800010103996003500c424641d1020b0790303400c19001000c6003980c50b1400031000001242d444110500c00d403003c44040001a111000f901d064456620b0300684030100a00820710b0600e0070f44698809a07030100c100b140800000a0950626051f40e00300c40b903545800050300e49030130206002c0d000b40c1d00410317540030060896400540d0402800e4000203240804100d9510850b1415181c840c0071429040d8400c0346980d20002003405025083c020300441031800f88141e5594200501d40424403007032000403850348909000c05141140c000e031060296191100d0b040d0010081b50081170070070a04003001c50600d0900400002c0c42e10300071220983c40900904003510300c1d144100c00940c1030340d15000b56000d44d842d12900c1d20700899800c0c02154903440425801c5010091682001d01482031404468200381003419182c0c15158042c01d10f001e0803581040f0900c080e11560740d0490f0005800024000b580f23500d644198820000380c4000c000e00d9883e4002007040e8461071181905002e40d02920001042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 456965782 1250 456964532 456964561
    0x503070e0108060604030f0609050105220b040c030c06030b091b1602060408030703110c0102011416050403170703090602060c0417030c0105090f0c0a05010807030234050106050414 79
    0x50000c00c0c0a080a590b547c403001200c0c15000d04a4640d03413030f4400c6c201002024020b041d04101d8603418100e00b080b911200481c00c000c50a00549104001c80120b400e000120078600080c5410660701d00c5003503200c40b00030340075010b1404124040d1502030000398030f0210041d040c03d0f41c00e1241e81d01e01d05d0309000c401c000c2985000360070242d138401410800044d2a69080000341b020038401c0d1612005038010306042c6081c88102450b10381035905040c19001000c014680c1079900a003004003011004001c1242201d0b0750003280c0008020000c0402124840245080681003952081d51143d102c591528000c070b07280c80003a070f15000007240c10b000c1407044c1c0301c4080c1203520b1501100102c0f800d054016903001d003554010340d00c42400360481040c0844114007805a20000e4a0594018854900d0400020041030008024104240e4080351007a42c10400c0c54440e5002d0a10b03d051500222081d140c2640700a4070240481700c0d0745c43c00d00c0019103130170140103c4402c0d1010810315440d95850844d1140d000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 456967032 1250 456965782 456965791
    0x80603010b0303130e0a0e1507110106240212091309020406090903092309041103120408101109150708041e140f10020106051201020a0206070503070e0108 68
    0x55407075003404011520100080d0800c000f54a40e6074200b903103441e07002e070300220b0060600401c0b542445105152a00002303901400c540134a4001c0341c4598070407104940c240442d800c465915424240b0000710b9000c11f01d00c00070b007920100811803060300d03502c00603641d80e51404a410f4030028144504a21844c0c000ca031f001040015201c00318172003086c0d60004080340c0ca95080003030b10303a41d980c4503c401c1c1507100c00104050070151003081c1400d58a00c0984966041c6501c180307101e25804030009040140140d1031000128003e0115050484804c4404a80360024000c05803548202d8800014480d07650081189003a0400400c0745070a00c080203202c2058131003840242100c100b001900b001079400c0009000600c203852161200d100e01c940050707954801035014001c0344c01d5030181c6110940c0c0d6031400c2e031002502162902404d0704200c2082e800343ca560380c4000d03440381c2040800711001c001074008158012455007a501a80c0d2079041c01c2da96400160380b8040002c03c44401a00254003032216103821 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 456968282 1250 456967032 456967039
    0x3140303040f031d06030a02040905010f06081902072f010203072a03120906261513020c010218010309050d140d05070509420d051807050a150806 64
    0x100880c0030201700d4941c0195030030100a40d00107000c02c03500b40e99101c3c5d940984284070b074500369146440c0000b400001c01403d40141d0281d0040e0380308032000c156040320642603000e0808941c91030030005005039800307a20401c00c102070b0014030b0307101a58404821115520ba01425810407005100349070110030201c149041101d005c0741d0004404540c2c121000440030b20103540b080509410b00000070316514052540c000d200c51400c0580180007120261154450b02800700154003148100c0058454460036003604bc40c40c1c0300081c480f01404064004100900504400c01c203481e00d0000110110348200202400d80e8014003001140c0070721465420807800c400f00341a90514400a07010000c0b07030010740320880031580000b4800111700384030719040460349031200b002606030b00c40950308000603c0c0384241c160601a01c0c1c0b5240c44c805903102540d0365010a90400c01651034180c848403510301c01c42c00c0d03000491044400000d06464083c8592058448c62103074000b020b44480019110300d5000703000c1c2e690 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 456969532 1250 456968282 456968327
    0x51203040b07050f0f07060210020a050919051c14030f0f03070c05190209150a1a0c06010f180227030109170d0b031207240608010603140303040f03 65
    0x40f42c1001c0001c810319074801c1c0003410300540340103006803414000303801403549a4018007000845079001019a41c0810301594006401c00040c007005810032034ee03401595003c08041503010303180c00984113001100c0c1c4640c044180480d0050360195980c003a928400102e06000c00165403a005032801558204500341040e0510180039921241843c08070001600304100d07e9080740151f01c0c1130940c1e150040da14450188040003404081745401c000c0d805207040c10450600b016aa00070a070080f03e201d58604000d9a00300e503100c18200c040c151040c8518004440c10781c0c030394038200545108654504c250180f07030480318915a69180310400d44007004950655913002180c020410703100407000c4d001c04021915641d0301040441008868801d41058029800b4000d00300c0c0b01c0003c44200d6030060f40110078840031003100c808126140405800c0c01d5101400c00400082001054001c01e0035a446112042c01301c5288044403039030ba000440300503000fa121100c10401181c000d102805190340021000103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 456970782 1250 456969532 456969553
    0x6040b0604030b0a1a0d020d020918070b0c0f030408060103150902030a050609070f0608011a042102010e010302120a0e190302070509060a06020a110402070609110901051203040b0705 80
    0x1d01d070001c03035800088035103403541e44200030309070011711019420449520b040c203846034000c00ea080d07640f043d000f409402d880b0007141030280c0c0360b090704408800c4030080340c1c0101c0c0c64501c44000c0f600140c15400c45445000d40c600d00244000c4181e4050f502c04400520080e031071511303902c00f408002c1548009143c0d9444194000d44c405211483d44580540c0080c04c0e10708180f2002498402c080d0b01136107504104060a211540d48440100d04660f180101d0354005000c00d001c9000c2ca11032684108079600102c0d4641e0800400c009a04400b41d000b41c031002820034130301c40154140d2055282c0c511072150013400144c40c44416a000944070f02c00f402c1207914031840f1a8800c00c4082481030160301590080c4000c2083c0c0c500cd0f81c2c40f170340c014010344800008a18190010b950b40601e0030380107100003ca5654003841c4e803100d40c15070309850b070040790a002e103503040c2c24510701400007001c00e140641d050400204441c10070301c0b561403029211400071441d052030403001c0a078503002420102c955000e6801d040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 456972032 1250 456970782 456970793
    0x31415090d2312040308010f1809050c180406050f010f030311120a030e2b0507030e090403030516020f0d1215170616050901080711010c02010605011803080306040b060403 75
    0x100081d0380c102c032040f04181000c3c20080c0103e1416032207041d82c002a4030040c822489142c1044840026542011900034101c0c03500608160204c00b1254011081c001c0c0c0102292001001e18041c1d070141508209940346e0b4400800e240c0c5090007102c503400351440302000040d1284948980b410000010348401d00707054002e0380030315400844118002901c4c0c0e40d041e0000c00302405011550001901900740c100943d803424026203001c414030390f05016012030040305142c000e500b06424484003c0c07106245140c00c1c940a001040c0640e490110340c940344a0740c80d401800000c0ca02c01e0300c1d61034801081e071b0300c010f031070200d9030382c2c80c1030003c1030500303860f07003400d40340d00400c6038184000c1e02c100c9000315404202c0c01d01d003e251020040c001c0c5c09808000d95113601080d0003000f00c406522081c40c1100256603120400e0311301c0450300c03444114030f600e40850b06508a9040d030041c4150380c3e00b40e981e407008040091810048070b032140030250020303008101080203171915504c410010318002d802581001c0c5e807038445 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 456973282 1250 456972032 456972037
    0x5030909090a0b0612030c0616092913080106091b0309020a0504051e0405031b150f070302070b130b01151d120a14070b1927031415090d23 61
    0x141f41030310001800d042782241c0141200c8040c00c203802c80102c41054100c0d000702c41c100b040502807805074000036008088a81e03024208050801030340240502561003902800400480c4500c46401034803041d1711104511034007e495032545c0042c984840c850602003000300030007010340741200c010422042e82c8008644030501611490041000e1a10380b0703d1500c80c041090300380781c1d0364842d6030010f0b4201108014030802e12500a15104501c5d101a95003c0083e002842924400340c040041c10b802c000700c07031660f0409140503520625065859903660b280404160048103040400300d20840c0910440e6010201c9910544e50000d051000303807500d954056040919071101a90b00303842ea9a08407445a008000000041c40c07070421642ca40b05c0200001003001c000e83d01800c040089100c5d000ea8280c038400d007040a480c0074001c40c402c0e02c070780da807426826060460304000e60b507010b080d801c1110344d00d203507540c9489462003901030718840c2c455503c1110f5514065200e2021040001c100707a40301c00e2800c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 456974532 1250 456973282 456973291
    0xa02040f060f0608010312080702070b1c05040b160305060d0f0f0c0602070e10030c1806091a010201050f2208070b0109020a02010b030c031c090302060705030909090a0b0612030c06 79
    0x540302c2c02d95066041c51f0030b940a0300c0b020441406107030000d03c0b000640c00505403048a03030071080c1945481c60ba84020704258402d000d1020300600302001c1c00180004c4417020f9000b40720400b200d180000044c00240d00f96601100c6207a07000b014244250085242c01e14482103042c480d9001d0410ba4906076203241c0314a07016007100005a011000c02c0c030140303c00b625429003125030303412038259003841d560303614031340c18407070301681c2c1030140d1f040c2c40181c7c0300702e20390007100c0a000c0000041c440ca0141d82c3c114950801c8a100301801036003400c010a8052050b84907440c042e10307901e02d940d03201150511a641120019a2044544000c10041400440e520390651800713170451036030160f0f0b40c0004000003400d4810400d0ba130b921a0b00006140c01d41c43d50b0001e00d2500784540c0d031307060600d40503200c1300595407142150320107504000c3c0000c40a04100001c802030982400440d144d819a85814582503682c405441e001055800c0500c0481d02615003401c0d100f651010079012645000305040c0d005091000a45 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 456975782 1250 456974532 456974537
    0x1e090c23060313020310060803161a1914010e0c0a0c14030304020a0b13061101060503010608010203060306070908030f161a07120207200d0c0803070b0115020a02040f060f06 76
    0x10020011480c040c4462106c20202d40c409000a40c01d219407079403240704100b07182d00c10a072402c1c0301c00100040311190110140301c40700411154a4410742400d144100c13500d42107006490902e030340b80840c0c4800d405505881c040060901e0130b5542c00704009245c2e024a03006428888a138001c000012482190541c0e201c20413806140c8a05192040c0607005c015500f0851100406000c00070082000c807a10300d00b200e40c0d03450036151600c00c842101e40145501c0e00b02d00d4140d401c058000c5000081500154000e440039011620141d4903550100d0302846a40039121080c1c008001c4ca194015005001d031090040381e241e941d550888550320018241118010380c05043d81d41e10030070121903000070418484514001e42945002c05035569245c4507507800d42200700e00301c04d501554459840340c80120354a1640300d070a5940e0b030b80d2102540d030b07501d4101810484000c052900082004c140c81c00340c034145611640c00518910710154200b01c003402421440715030382030380c8a4000a0102c0c440103400300810158 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 456977032 1250 456975782 456975811
    0x20613060b03060114090f01051c02040e15010f060f02100207020121090b0105061918080114100902070b01030b06040b1f110106060c1509050304091e090c230603 71
    0x50181b00e0191001029410240e840300c00400c0241c803032520080b0b07010407000c1014502d401505c00100181050f0003040f2640c800d0854100701094400f010f00d060741c0c140002d0782d100c80e94803441100c41c0c4200c0c580b80350050700310108408107031034650042e18009205050042108580e0800100b88032056040341d5443c0f070b06c40c0070b01c0d0188103170312000501600b81a00d070b00d443c1450038601850340303032060000e000802089841482484200d0b20a540c0a00003520007400082d180c0b540001c203c08050350301d0280a04c190b0b0000412091500c00c603603030140d109440010f00d07840d640302d100306000000d03c010341194885800052031f0b5601d441400000c132511500103002c088094000b002c0041896201c0c80503854920706000c01604115031601c80307644000e4000350102e4950090000d0700401000400b14030000c100860041004d812680e590780351030100c0003a800303015102a066030900d02002d48280c4040e14103001c4038a03840304028111002c4140c01110b89042400300c1c00980c4200e40100e05075603074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 456978282 1250 456977032 456977069
    0x20d020703081e011e1e05030f0c09040602090d0c0303020105100b0c0a0609290105280b0c190b06041524091e0501120c020613060b030601 61
    0x1007403125800620590a4000c03200901c4210b440c110810f0082441c80105080e4171107428540d92000350291810034190390750420350200e41d459122460050034402d00030380700c250910310720004000b11103540003031803080c082e196519201c00961104039516000b212900c440707030104429803803c40080d80700760300005803442e100075102c0e6080c2540e0021010032608106860554500040071b00086070007110005001c00a4070b802413100c0750051500c828012041a902c18100c03400014504803881500c0d02e5071026102c0d000714122081311015501e440c894540d017030001d021450060f2a0042211044556800400403030301880d0300f00345011a511988801004004e0030503025640f80d140c0c0c0008502c42e01c41c10500c0d0115414100d48c0d160103e010323010000c0f214188102c9548000304040d03507190301c0054840f00307051900344040c000d05010a801c01d0b94060b050409118198003190244d010b041c1545507942441c151030000c400c2900d0a42e2204c101e0002641c091180074000c01300e918809206241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 456979532 1250 456978282 456978287
    0x34120f03050a09112b0b010602010b2704021302071b050102030406020a03050a0525061a0d020f06210406060617010501030b1912050c0306010f060c050709020d020703 73
    0x1c0c0184601003180c20500d1103800940700800c80c2c2c40c20242205c9010059661481c0c1c0d40e02014003010003075280003000804000d218403550706d54113803245680240494016a01400102510303200865010310b0144002c00101900d01d100741e800030320041422a18111481c01c2c00d04ac1e800c140002d032111180d000d01e403006201300c0e96022000301401e0000d14241868020040e4455120b80000703400d02c10300003845e4000600c01c800301ea240388420400500e405000d111000302a05000e03000f10340c003601d001c03078101c0524984d505032540c1c554000c0080091000715424044481c10f00310400307030048020700c0416449050704009000e815060b00b0f111031645403904166080e244244d0258050044c009641c151400002458505441003801c010680300e18400c0030a041141c84041e0501541e003802c07001c07a01341c00144203660254050402c54a806681c1010180c0320a400c0c45840c120012a030020441a40114401800c29005200b56808283d0700c40b00a0180da0041c01c0406115a000030114101034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 456980782 1250 456979532 456979541
    0xb030a0b0109140901060f020c150309010b0405060f010518040905011506090305101805120d0b0307050901030b040503120f070923060f0c0304030c05030606030334120f03 75
    0x14161003101e20074030302070f000c5140040c06011340d2040000070700d05100f1442c020002118800d401510340d444031100001c2c0c004c0d490f00103444c15002c2d0b5007090004082032401e8010f00d07000c1c02e801090524040c6100300192507581c00f100d840c0180c0804036100240780d0340d884c840c0301e8645020b0000803c400381d81c090b181d074909040c3d030400d20520840d05070920210b44002003043c040381501c540022014440e8001c014440100700c0c0080042c4102c2e000130a10440040280078841c400b101d051010b0101c0d0020107850325082c0c0182500900b280004001103802c1081098002d03000e48140d038500200d03a043d000c0c10b028121085101452914184150a9031144860300201240c03069502400d9400840f01d00d540d8034402150710406004ca0081200704000d4100d03291400e0010440e039407140c0d40c0c5030080c1e84a041c0c4c4610352183c0148000144103040c04000c481500310111544140802c035180303e11201d403481c0c0c00200c041025144000c001034a2001c03991076164913500c400ea1610391811009040e036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 456982032 1250 456980782 456980789
    0x501080f0d11060103020906060f0a0207080705011110050a090503030f090d080103031707110d030f06050402040303090306020f040504020a0e10020c0307030206071b0b071e0206030f0403090b030a0b0109 89
    0x45003001c0c0710340030007101140490640384d04450587c2a03444980020b403c40c00350032180c1d002500002480da01080d0001030601c1102c01d40c500b59024143c0ea0b4005645608056604c540035810001140369910b400d5409581d0010304a40c002444120b2030312000c0c6150130485012018800351020b01c0200c042c01c000d0624141018542188250304595004000d1894100d419022450541c0840c8290340074480502901008804896003100e003540014080d169445021a541d450603c0208003400d00b80211410b40745c060b10303040030140c6140d8800c4000c0d804180340c8581c0300c3c0c0601c004038075036844e80010300316080f00b80e86200007040e0304804c0100444000d081001590311803864942c441d180880c080e02140d404030340003500c5120074104103100d8000741d000340c28010212400441c202080c0b001804445028410000803e2811090b4039601224090b000c1d6000100b400000c084003851031050754887e100e0700d001c6108546e500c90111154106070ba448800544500c0003003c907581c82907800008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 456983282 1250 456982032 456982037
    0xa020c090c0a0f031e06030b010803030903040612020405030a030801140d0c23090403020304061103030108060115020c0a0f1403010b060f090109031b0f060c0528060501080f0d 77
    0x60406140c03568070392040812050034003002d016101c003101e000c1c3e404129403010349031380a10b00008402c048001028540403c0f07422055050004c151608000292031045020364000d5140608191080d0750030802c40c010204c2d050303020440030889440a00c0450400f0f4420386030001d2550411a41c0c11b10508110754650003498603ca0703050128641c03014940403500c01d400444803280c00e09190015042940220603000784854080c0700416900000820071101d07240d039900400c050681c0003d0302c1c0c0c8000e1040442650080c0b00510122020322194143d0f648107004603a101c6c000a000b1075071403007050303000e080484d600f01d2041007030b15010312480402c0c1c0003c6000b0442203010a0006240d802101d42d240f0241c400031030001042c3c0d0003203040c500510f2300f02d85400752201003054409107500107402240701c032142e4810005065406610007549051748000036015120052003044c8400c02c04100c400749440340b1016100104034680f0039070307010701110320290141507600d0304118601039424030041c04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 456984532 1250 456983282 456983299
    0x60e01090909030c17070f050304170f060f0c04080105090d020d030606050715020f0705010504061a090415060513090506130b340512010611030d1509110a020c 70
    0x1035813080000f8001c942c4000201c107203400c0030740066090b004142c00204002d4840c10020240500003016104817000c0304100b2418600c02400652030b64541107150309140e10040c0171442c000715030a41c6603071040050101c103050503914002c0c40d00f500e40c1551040502d030010a03d6101c0c40e9030500842001280714113040c0030051074000002c00e00e11038000042e00020030890803150b4007c06404984250400002142d19681e0034100140204010341d4200c07101d92604e5140c00900c2286244022405030040055400c0c0d601e030703103e40d040003201303800c0d802483e5030311000401d00e940d881803c1400407000010020781c544c1e10340b40030303447c11101408000e48010500c40d542d0000c2c0c200b4244a1b44106031196200c00242e0761024042019200010740e0070103808042100a41503014000c0e1011242130b6000c44480d07680c0386001c0d6149015219a0700164000b0420080c225070560443c12a6200400031041c040390359040c0c200843d40c151000070364194000820b03041080c0c0c100481c00030301604841010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 456985782 1250 456984532 456984551
    0x60509070806090d0c02061306081806010e0705130e01060c020114040e0c131a03041e050c04021605060f0103150605030d1103090405040c0503101104061b0c060e010909 74
    0x550340c2c00184102001c01c03104190240c00c5440f0001036400300d0340e5110003001307034030384411002d880148100c41c1915010bd109000701d00102000036901d0403158246220609611140e034115003070b80c807a44192811000c516000609054400000c0d4002c0c040d82e520800203007098400182190400f0384955000441480148a5010120321182d00150041c0c20b4654036102e040d1041b0403298191300800d03005155552514200145100a612440c414200302c0300600c0c0c145ca143ca80252142400380103640540b0406c01c6504083d4000c0c50039517100180101c40f80c006545180c035180d400c4601e0100d48006d100108100034016425004e0302051740b600340615820500403c1d61a201308000750100025200ea05280300003c1c01100e0703480718084d01c1440385183c541030021419070703907100700b1b8000e218904c40301100c410a4400c903102c445a003080d81c1e01d002c0c035090084400010710355909260038484400c52002074a03500c17000e00181500d0310361411103420b090002d080909240e03c0160311604060010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 456987032 1250 456985782 456985801
    0x30f042f150c1b13050a0605010e3007050901180c110c041a100e190f030204020901091d0106031a03060a1e02040810060f05061902011503060509070806 67
    0x920b041c001a110f14203076408040c001441c401c2440e92030b045071803030401030010481940e04441d050314070a07258151000500d006124203101a000100c0040c901e04000380001101c049200880701c200303000b2600303804c0d150400540034030f400fa400725040302d0ae9210b900880100500555104c48041c1c00c03c51a00c4911549894560414815491295a4414013040d00c81031100c07230245501c45c054500064808004000b40585a141c000c143c81441e400444801c01015592050240c502e050a100e411514542c00c0c040a50801c481590520100c6940410300041c0d4a42800f40d8a16000c12a50903500d0020b0150031903c621607100c01c1d0440c250120302c041e4400240454001ca400d030301c00502c1d00d2210045111700c07104006142c1500e400010001248a000680d0200f14000080700304221940c3d42090010041e0703e100380d9130002d42c21310241c220305840c4c0d00b10b0302140b6294000840c0000607400c032601e243c500d07900f007124802e40e14028003030340400401580c4043d004c4040213041506000555 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 456988282 1250 456987032 456987043
    0x90711030f031009022b090b04050f100608030924161407030b071209170c070f050f130f021c0c030b240702040203070908060a020a05030f042f150c 65
    0x1030b03410600681c0e2515640944da1fa0203503440a800c100300550508191500d20b890f07034206060818a8440c03030700040c111100318030420007214030380e000451608a10780c041c00799840008001c680c00b034505081660b0251220401005261448100180820076518101c598840402803428940e440800c00784001981003900542081507414405803006a4002030001751a041740700a002040202c107400c58031440c407001e0301d1038039000002d945503181c88400310303070380150b951007001d5104000781411006814000d02641d048142c83c00c010a8800782c2c041540240d80c4038140440c1501c00e204550301d2881c02d584641c20380f000b1249002e01c80301d00c00e00300242490780c820300b1240809244541c40c0c1c41c05d1500b40210f40034154050401c0d0340301c1c5004480070745404440d208081d00c034024072001a40c41200c07442118080c0c0c0c3c1030f031030303550443d00c40a44030064841c0090049920804829442c4070b1980c1e41c580c001c60701080b4003615602801441c091103401c0d40300c034059031f00c2c03c042440880300b540d201050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 456989532 1250 456988282 456988327
    0xf080109080f03091606050d0605120a02060705030c0a03050a030b03010c0c081305090c0a110f0a06020306063a0e19030c0f050c090105090411090711030f03100902 72
    0x10300d0301c0c1d0300c1e04e107590b0341490030b1040f40d54100c0818a04c0015042e80145c05003184021262081107102c0e92030b030074041080303464004207080d80c101c1d1000a0061030641c014100c41405801124100f40301c00c01700314070f008100032080c0c000c24004261505d005a05005a10014005600070f212079140810702404500b68000c00801c0b240f00402c02c582c1007002d1600c13600c0140300051032507000c0d00b003001d6442c1c01a4000300e40300e00000d1003440b0341c040d100c5002907002a00e03003d400003408504500d449281c02500050840d941c4160f080148003030b06e82c1e207401040041894078140b2000000071407148444070381d0081e600758881c0e0400d60411882e0340046555985244501c041c18240c0050f40b800700c030034080c01c802c002c02c0380c542110003070140903001426100c0000145d582034030070f07600e0b0380c1003120340c1c40c0071200180600c2070324540c1c080b58200800c1483d003002c03450410501c551418654581950444410b1111409001c0104500c000b44412a54010711248404600d408108440c0d20425041d840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 456990782 1250 456989532 456989557
    0xa0c17100606050711060f0d020c0c010503010b16030c0206030a150e060109090509280512070b01150924080109060305250803190206070e0307060c0311160f08010908 73
    0x3144020346d16040200e0340001d264288481d44c8414400556009400400300c40105204041c80300d44c055000b101120705030758600b0151428040020740e114544a11400c086041200110300031005840d50405140134070400304010446502501c60f030003002c8406d45c408100801101c00f4015240d030000f101c0d00a03108125004601c507680d00424520300030491a00f541070b20080b80c6030641d4220500105240c0e80e100d10242c4181d030303000ca05918054012910301a01111100004005540142c40404003050850400c1407405aa40c00c10a1001c0b02c2d41458031520501c00189031041d5501c2000300f401361070b154008121041c11511429960100350600c640d128000300c041c030362611b90005201d0010032130441243d07a1180c10001c01c210034040349400d58054031811000c01c5070075000b599070100da0031015000742545c80c86c140040701d0408051805405000c2070f0030400d11103030420310102e580304414a010b10040703441e1800480464049600600301030f49407004e0403000a1042003103502070744115 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 456992032 1250 456990782 456990803
    0x60d080a2f030a09081b0607052e060f03050a08030c042304140610030218060301030507080606090103030e010f0509040e07050a091119020a0c171006060507 69
    0x600c606440141c02010500d07561900c1d0a0503584441c0010041284070403507980e00212680d5070880ba66103081e03008072440d5841d440c4044040f1400c1c004094001c0707078002d0045540c00e84000e100c0f410512a0684648075803c0c40c44a03103034583d00302d800b5802c01021000c41c2c80c00618a181c6070652070b00100c18000301000b200102040c030803100d0409a6002d80426400d402c14203d581410501d407100e540326070b502503810844035680c00c000022055105a07409803181c01030008007902140203500003507041c1d05003900f503000d6404c2a2566006135000c2c510810080100c3c07410b02e24000d103000310013004c06d4401c0b03c8410040c40000e600001001d80c485081c203080313180c0300000c1c0c0141c034076000300c1c030500d9041803510042e013180044c001482001c9900c240c40e0403180c251038109050030395903081d00b0020300d64410441200b800000c134801032101021b82c03040c3c46920340107a4840b0070405503a0f100b204104184589020452818001c0450403c032480c0d04000300c03450100081c210b8020300d40b0190103010070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 456993282 1250 456992032 456992057
    0x50406061a07050c121501090204030302210702093102040609020c07062a05210901090b030c0403060903020607030b100806060c010608060a060314060603030405060304170a0e09060d080a 82
    0xf00911b440340c0454855188840d80c440c0201c1e8020b401501c01600140720f04240c803440400440100081c0040b000c40d82c03032400d8116000d00002d28406400603090084000c0414822100015a0580d0f004441080d030702100040c01000f0940740e80b41c000010a0f441000b00e84446180081c2c0c1d0800c54401c2d090194600880f030329903102c00b03100208201c4003518102400c01c100031001c110416484504420b1100c0018801083e41d0a402520601030100720f0a0f00180800900c04000e9030740100503c094902e415140c1c0d84003010341e800988100d01603801030090180254150084511012042e2015110310321446c0c8002c04029003d0540b80c0070b80e000040140c0b444034207400420140c03412000310b5501e81442800c600041c1014407082d50320409841040040000106429000701c6009005604190501c410801c40b13910151080311095800301c0785a0512411a0141075031040f030303480301c0489520b03074018070683c1c00008061030311411001400e8000140711038296203042266250030300c102c016 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 456994532 1250 456993282 456993319
    0x30720030702061911071818050d020706080106080903250606032009010b040b0a20060a050f040f0b100503071503110a02071a0d050406061a07050c 65
    0x500401070341040000984d89008210404200318555040d920300003020354202e98541c40c1c00d000e002d503402c1d045480500c030b4202d91454203c003c864603415040410000a640c905144c03d403001014005230b001200c04000042d003041080d401000d0300e0500122501d08008205e8803841040007003000300400c0408110100d01210f41d58019945c004c0b41004215100e0030a03821060142c2000c0c41024a4140b00c10c04604004031201d049603250b41489040c01e04060880070b035030300045040ba0030420021342d03900e41180e41c00c0300c0c03081460605000e4100c0e810b0000c40601624001031120811850308004d120009010712007045080b9000507420505032200c054a5400d0038095000540c144107802000c103130000b0485600701da100300c5840030015248600340c0c0c11418081c0d150f1840140e009400100640d0801e41c04d0074100562051810b0314281e000c11454080702d00540703003038171103d40e524018031500c40310101000403c000b001c40e5a05214036a03880b01c1e03454034141f08440c000c1e40702502001c1c5405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 456995782 1250 456994532 456994537
    0xe070504030f0f29150f030d030c0207210308151005091011060c031e0c0c0d03110a051c050f040b0f04210e0301020408010c03060b03072003 62
    0x141d0081c4004142d00050818151103110344005558076821281c0710140302e0305480304c070040101c42c860081d0440d52103041400007202c500b07410580080212a546066503020b00001c1c51100c2c4640b400a402c20284030000d150110035000344805524030740702d0030310035442c880109000940c9407425009658428031074040b401080303040c0035004a0b4a14544100315008406420841c03425a441801c021400d0f400726020281820f000c680398100d40c0100c0d402d54000d20055a100001411750f6403009031a00d02401c1c3c034801210054540d40c4013140d1203805800520000b44080c0c401d2605101c0141e41c520354555521038100d1759410700400180401034042d20b800ca0700c8070702151160030482d519100c1c40030f8104060444086401001d048000780f601a03607011900e00954224a081440d442181007401100d001902407009000c28040f2140c01603501740001e0001c0c0861310300100700200c0c07096000d0103661081d040307072504060a10410101d01d0744596120340150040d032240c0c041181d250041810b62 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 456997032 1250 456995782 456995789
    0x21060503010606030f050c03040b1801020f040e06010e100815030a1e1e0f0609050c030a111003020306030c0607021906090e0603030a0c03080604110c0a12090605040e070504 76
    0x15402c0400c00a8480e4040d4000140c0040740d210034403840d544c02807040c02a11040b100101013442c840c2c0407900d08070803e426079500300780080c00140381c102040801a200d030825401440c00b41d0b00102004041c0d6480200c20200e40d80c161940401880c00210203040341ea002402c6064003952800300e800c0c00e0b0703420410f05010741d4026201181d814000780010249111021081d80e182c2c642e48440360103500000c1101000f81d42026941d02100400d076903c1c000352902000075125440742c4c116528203503505200c03161b4414843d041d0b81101600c003800f4480b8107004c60515409252040c010070440f0344020800c0c841042c1c04843c55503542129100180d1386100320544900496551348003c184150801640d2055a403003d40c0f104081e9294004c15030703030780305800300030307002405128200000070701581c90160020310040022070814402c07424140e4640000040c010568440044503041c0190342c000b9407051101c601d008101241400c0029006110341c2c46550240c0c18a0000580d4083c45282610b01a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 456998282 1250 456997032 456997039
    0x6020312041e06090503190c12030b040f020a080a0c0201020909160201020f0c030c0705040203040f0f330c0f050406080408040e2d13080903030c01050c030f0601050a210605 76
    0x303d84da500700303165250800c050440c42d8000340310f0021401030040100e07014041e801401d08030103001c9c501c2300302d010b0007061f84420340098443d00c2841030740325540050701d6540d0f4180d030fa0301c03941e1a0402c0c01c14103651856103142c1c29a44108003c141c2c0d9102c20503150750111003c040074403411031901d4224020310a014507800035000129aa05880f0408401842d084550404980741640c0b9403040204a00c03003030310003c05540d1075050180025554800090301c0e00d0003400c00e516070b99a03010440742c4201e4100d4060481070f6298000081081a81c4940b20b20040c1d2441d0550001c000030b02e01038079620407030040d41d00348044d030000981000700c40401c690260009481c0d00981e402c21880d514811310440e081942c0e48400b0600075066000c40403041f40c401c0403103c00740e00c29401d843c0c54626a5a20a181554050100b042f03907002c1c42c9024044c0b9030040252040b41c613a2484c02c1305641192410240809041100400c0942c6507180d1200b1940d131403520b90b12000380c00605480395540204000c4d40680d82 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 456999532 1250 456998282 456998291
    0x41d030310060206101409060a03020901122303040e0c040306090c091b0f180906030b0405061513180f0303020a0f0806030d0c08071b0f06020312041e06 67
    0x11400ca8041d01c80100c074840d40844038961202402c201030340c2028003e00c54581081400c40000345002c01e407042e0420f5005c0c2000d10f140d5200d401050000400360090b046614503900a04100b224054080c0f144000c008619021801790000d0a03469110b40d200e91049030510303c000c07030f103081501422200103640c810f030300300311002007890f09005a03080d074400d4072101c500d0400c00905003403840c038115460b0102c95513500410280c000007901c4409040d1600500b0020548020841011a102d5580514010402c00e49140303400d00c2e06601c1c144008202c04d83e2020801c403d074200d603d41c039008007050003054034041800d030310003422016490105c2d40007501d5001510b010344180b6426900412280d42e0650b01c20f42e06840000c1c0c00d83d0300131025142580c0590180b0042000d042c450303803011413002d00c00c02030b10f41741010710344401a21589225901100b146a03040800c0003a030103000c0355000301102d00140d030404910b00d0340b61640000040c00644580e10f008060698030071100e4400f10781541c408030801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 457000782 1250 456999532 456999541
    0x1f09082b03021c09111203130b031e0a020306040b0a14210303040b060102060108010c14030901020910030c02010c0c080d05041e03020312100510030f150801020a030b1905041d0303 79
    0xb480904840171801500d0605640b402c0070b00c04801c855903500d400308001205071a25809018590009040c4624080044814a91100421a110b0064041180258490500340704120071501644e052911440e200c080402522092044491034102c040710505504074074600046e11111402d0702d90300280c080003080000b0081e0030000e042c06101c0a81c203c60750740e88c0714101070b4201c58000410317402250070254014016150b590046038000800c400250403c00502d020a29400c14907001101007a02c580c80368000d141c0c240318081d400956441d00c00303800c8040c0d8842200f035100700a6200d01c456120000035003070240c840005440e011494450f020000c009060007501c903080520f800b0103031564900480c0d4083c4801c402d40c1c06440001300b09084c08203000d00c2c148c00414015055940d12034403040e81d54030816001d80450014031520001596450f44800000c08445100d82414801c2e0f089064440c551030400901206440080d1000500b8500f815a170b1a18400d10300c1840311188000001c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 457002032 1250 457000782 457000793
    0x90221041b0510050711040603050a0c09150e011715130b0c0f03070c0f050303070504092412021315060f02030a020307111f09082b03021c09 62
    0x405003084020300850050780c0710350400107003c41507100782c0700183c000d12550020a100842d11081104000e000144281e50382e960581010040b117400d881c508900e040800c4008007900814010345200f1044810307070303400c00c01e1022401c0d0042c06010210300e0183c1281c20450802c00c80700004001c80803540b0040d04d4010134007401410074031003c85918100c84d0220368441000401c0d00d5082c0c01032a58a1f0031a41c480204503030302043d48200b56502c0c006150b01c1d5010503428802103014003c60b036503c980e106c1c200400402621141d403c50909001c00101c074071640403151040d101500d1881074009010f2000e8000541800e100b1280911018609a102c040e10f1300050b80c40c0c0704845140d04d0351010b0482054041ea1240900c030100800350304200031040000741100c4042c241194005d1000203241c010034071403420190b00468900104003555030038070400c0c008101050f000c0b2104c4e2031114103091201150903030001c03511594400c0c1500422011000d82045003481a114800e0000f081144c0c11410b00c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 457003282 1250 457002032 457002053
    0x50f0c09040b0603012019110a260d0203150d020109170c0603180c0108040b310c080613051203150d030c030306060e0904110121051b070c09022104 65
    0x4900581868450403507006001c1007909900c035101509d81c1030842d0316861821445d9560b031041c140481c41e103200c034105011025060f4203043d0703140107031a890f00740e004200c0740070551590b6201f20a640d03203040042c4e900440e40d0341503644d4000c000e0070b5501c0494000f4a44510908000d46c007880c04420811801d400e01e10107200a40400110303809982014015940d822060707401074040720304071000981c41c00d41e051100035451080c040c0c1c1400306200180c083e481688559045500d51184201000174007801c00c00325820118903c40300003980c54903600c583d41c036030014004140e0f84c84c001c00090301c030a14481988070302c101e01900300c400e500c6a80c80c00501482c6030040440110341f0700440441e44034030401000710141d0300034083c05421f0700c0e141c42d80c8240c0814610344d281003201109a01d0205100c04407500c486880a080100e02410500400c03141c0307220341c1c2401e10f5010000d102c5500410290200042111107004006a0301d890380c0e0f9075880340c0d030030794441c801c1041090400d010800000c40031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 457004532 1250 457003282 457003297
    0x7050a0e040c1505030109020903030405060f09130209062a0616171909060b120102040614071a070e0a030c1e0807091802031504050f0c09040b06030120 67
    0x445409594072a40d00055040f039048540000810500050103c020168000c00320100001c2c100c90516644000140c480e03441950024070040e80030078440c1d1141400142d601e541500c0300c00940c240b15201001c10300c5806a54034012078030022408002d0864000d0003031113503030604030b0f042d154149040d5800c281c00440325200c038ad001486035101d400f00b102000044c98010705400310301e080f00100f4058600040c00740c02e03a0540d162681c4002007415980d07000800e05582000e80300142e1224548280a890f0500c003140542c9140c1e4208141c100040c0031002d1901070a0b445109180c5507180e0000884000c2201c51105d40c010f040c5801c040107105041820004443d02c0002d0203802088002501889582a02c0341c04060351141c4810f004506003600075816000d0002090034082d2016000a03142c4051084003650001c090014441808000d0000c000791119040040c8068050b800220301406001000134000d0f10245000c203129039420341162042ca44e02c01c0040e9290b040c21031030070115620092 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 457005782 1250 457004532 457004543
    0xc02060907060306030317090f0105070e03071d2205010207151107020306190e030f03010e0105190303030f020c0a06050105131a04050604090b0a021305121b0307050a0e04 75
    0x401c0000c81030302c41e0246030103aa50503603414265000a0152241e07a41000e412000c3e64040c4c0c80c4140041003091284a200d01c480b43e541c01101b000070024541890815046010020640d4000300d801c00380b0b500c585500b04603c14212200d40d43c1500144440b81d00c503000080c4194000200f01d01845410028000711510b16078040181d0300550810050f9403044070030003900b40c2c11003000581103801c030400151354003d62410126104195400003400c0d9400039940708a0044040014007010446829035070240c03034180c80c2ca14865401c5050400c0c448800d101c01006c064075601d2a03800c480c02c0743c05403030794240e5900482d504c0f1303159882d08401600c003d00800b4011140b8501030611307000c0a0055940d643c0c00e020340401c1c03060f8841c003840041c200003441c01d504540c45014010000f154040309910500d4805c80068440786034a07005000e182403a44400d100da84802e142c040642d00114100c400076800c1d2115041100c08000440e042021304d0340f02c1603002e280c40800044801010a00c1d500c118840c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 457007032 1250 457005782 457005793
    0x150907210201050408070b070b100501120b04060f0602010e060702011503060506210a03020d02060c04140f0603090609070f150f0306030b090c04110301030b182109030d030605010206150609040c020609 88
    0xc2c3c8ac02d03846491500c0f4403800286101500000b02240e0307070024982000281000c182c00da11130300c1c000c4001c071040c5d01003c0140e40d00c04040c107803100244545a0807018600c020700c0480744110100d0b4250302c10340009040165900081902e50f81c0d100c0000c07211041e411501700842203454a00ca80722114a0750680c00340c0100c140080300785102103035040c030a01c4450200c60420b4200b0120200228444032079a400c411a0304880005548900207544281038200061081d450505521401c1ca4400d600c003214002010205124400070444640c08242e801c0c03070281e20060841e2402c601520156001810410b1740308181b0054840200e0318844000b41070301c050004c01546210400540720900c8081e0007500500c010400e030b444010802d41030b690b10a001c035140ca51618070490810701035503040305101c2c81c00284034102d03030400307101c580114003160600300041454140040c0d1580b500900950b01e22009502d100341582d1080300b5100f6001024100f0000d40640c0703a40603607166003e48401d00700d8440c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 457008282 1250 457007032 457007041
    0x7050c01030605060d0902040e0604061514060712180e0a0b0d0c12030519080f13050c04020d090501151d07050f031005040e150907210201050408070b070b 68
    0xb800344030211607025104c0c92603d0444d668410062141d220201da0143d2580707480c40a80d0800c02c01240500c3c003e60f0300042150f8510140700d40c122841d48480301a81c0031b803c0314501c9507501004e982c41250000942100c01014240c1140e4254441d140102c43e00182c010109904100d50361180c414103104000b0481040030a007004865408060000c0007036a8000d4140080e080c1c100c2d10744203492003410030a082100340a100428082e20480c200000340d4240308000e5038800d0058035603009002800714024002d003a88403940c031200d4101c9a1800b41d90001401c0f4040300513940a03544007038001d0001c100c3d0b01c8500e8500b0560030b0081c0b061107918089080602c2620740c10002031400f810f065110742d031a06102000036401d50300000c1001036980d03120000013416850f540100c8106c01001e0f00078020813607240880c2403c1a0b400340c024525580824818844061020a42d81d2103174940c3c034540d0321884040c401240c0512441d0000c481601501c030000880d81ca005001d032903058401c1400c000c0640c0c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 457009532 1250 457008282 457008287
    0x70321050f011a0f130321020714030c240403030801050918030a180302060d0203040b0c03070c03120f110d0f02090f0f0a080d0f03051312081503011107050c01 70
    0x341d00e003c0030311101d010000300c0e40800302e9400030102c0140b0f010130321004595948820041650481c200d5000e90b00241c04e08104990505c090006802c411828441c801c1c0729402180ea02c201c040541d6002d030b0f81510312136480c29002e0010b22809070b00c803c2c0032680c6070b441b4a0700070010340707003071141c1400341d40540f0102e0303c000c2d1000c50419401011200550a103803030004100d03140c1805155a000241075643c0200c05600c50000400d5052005100940d49042c5440c0c41e08611400521640b1820014010700070f142d07500a102c40e0300c55415207003807207282c0c0030104014000c007d140400541c0034604008241c004529401905a80148510070080071a6480c00c400c03d03031003100788280d4080c100e41c581307048603c0d0424100740e42c001c01034100000c1c240c0b540010351400303c0003052030300429160b402241006a06000c0d1070f034071654400e90365484403002d035641c8048420a40e81c000c103202201002031031460800d0100209510014001c0c841a1001c3c4e44402c126408150152014007554154558550 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 457010782 1250 457009532 457009559
    0x21c110a060507200a030f2a0902220303021c02010c0e01050c0f0f0304050a170601060e1807050409060b0903060a0c02010902061201050a0e070e0105070321050f01 72
    0x940d56182d0303034606416a0368960440791080e4024031404019a0000980e48801890101031413003554000800301c03440c1800082c003000840e0f41c010141c1c00b0380b01e03040c000f15071810300c20450b41c4e2100050703110142c103100720320304101d41c42880c41d500c038004130300105040c0e001491000460641d16800d1105241d54012826502c0100c500008200703009000308813544100d001300380f0040440241c80400c400003000c6810901d4040f00071425a201290502c85450f10800d1113000b488140482c0c5080441070701c2282d11680c051003180c060082c0e00201d102540c9400c0b0300040c006480c840540c4107460010409405a0024000c2da40341910b40b400c003003402e80a1000703d500c4070000900a00b480d98420254601400a840c140b100b15502c9105450068a03103034040d00007280340c410019460340c1000240300c4030711050b51020240310303c0c0005020b6a5600292490344001d001c0c170340300350717164490304003990035580c8410843e41403030b00903810342d100b0303451940320314000d0040142c0b03c07100f030f40d031010006600c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 457012032 1250 457010782 457010789
    0x15090203100f240e011b20120601090504030903051603030212030609060d1b0b030103151e02030a111207020c031b060d0f0509070812040b0f09040603021c110a 70
    0x50281e00d401074000c0d070003010103244d600c505140c841800300e18a03400d01001c0d420780d801211010004c003c070400000c0301052003407040b002601d0b11180300b005240741c169a030006101d00b0250590b0341c0007003400c0c144104207103005940c202040b10b801c2d00710034884c1e171403084040c801900103005024038020407000c1c007008c5034003501d0b000701404043d4480e001040380f400310780f04085403809915604064403083d6110080300034010042e5441c3c407985503090406036003007000318030200f4514001c60040000702c3c0c1c0b130301038090360a030200041c1c5903641d010090005205410854110003c0418000d1a000d5200307040c500c102c6495003504e40285128090507551111850044601040500d0368011414032601800200c0e000160104008801c07240c05011510140c40100c029000304a050104880805c4081c103803001505010f854a454592000c1f410f003e03215003e01c03541000130300b01c4200d540e076070004000f031a0000d110544030101034800f07000814480301c08613840003c00c40d0101c82c9142c5281507a045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 457013282 1250 457012032 457012079
    0x160822060f021018030518031c02100c02060f04080c010f050a29040903020312040507060f0e0105090111010b130b101b020d0c0e07020601061d0a0915090203100f 71
    0xe803503041c0d4046d03c03183c00550070340c50030b0005160365070019901001245403105602114000c1401c51042c02828204130800824820b4100700c104e0303851960004409a100507403507a001c0c0b0503103030b0745000c0e00140b0444019550f03641c00c010702c00201c00196071296004001c00ba604105a40501015900050725403900101900790400352440e0707400e098001ca83c05070b110380b05a0b4600035a0213860104a00280e4064a07543d0180106010068005105a100f0115824104112000000001c05506c90b842d0a01c0c1003160614007000240c00940058401d200e0081080c488858070351605002030486c0a404c500c83d480d4401660a0380b03004140c5016212460001d070600c0f17448903001d20100080b03400c8200e03004110b007100054003104400d4002e0181e29907034041d10340d03540740c81c900070045068112941c681e010307000d014410a41e86c0022841c01c4a14000c030228180f02080d065451141c030343e500010180f03000104103e0104c102050b2803060b54600030650300401d44030481448603000f0b0550280a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 457014388 1106 457013282 457013321
    0xb0a030218010503150121030c0515072a06020733050703060b03040b0901020d060b220501080103060902040b062706160822060f0210 59
    0x28142051000110317a5410b04040c680c5036078200294004010020150404060290510301840f680040a80d5010102c0c0000040e00003400c8541c41d000458040034080452240390f40d02402c1c441c1803021507007004103640c446d40254003404040d60344c4030501020101100400104001e8840c0c13220040b408c91400c0c80403001954400b410702c40501d810601c040c00240c2e01101502e038810780101566942c0d4551132982d500922070041e02c03c000d541011004100e00280300001d02c00301640c100364168481c00030340301010300e40c2a4020280014440e50042010074480c1e081546464002040061000040c3c8001202a4482c00030301000d000c034460311442c40e44004044801921040d901e4520340380722003840b40c4110f03403c110002c1c120034000c10807102c103622401d540f01c0e0115080500c0130a80b07498060290403040c581143c20b00520890720300b000145075501a0386807260038040c80702d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 456834532 457014388 := by
  have h0 := BRFrame.cov_init 456834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 456834532 ≤ n) (h2 : n < 457014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
