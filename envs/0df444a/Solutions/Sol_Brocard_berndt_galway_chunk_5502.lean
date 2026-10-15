-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5502
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:04:58.764981+00:00
-- url     : https://prove2.me/submissions/4ba06aa0-dea4-4bab-af25-2612fedc8fe8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 989388489 ≤ n < 989568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 989389739 1250 989388489 989388497
    0x909060506071a271f06030309051201110f090405060d05100903111219110c012a05030d0b01030207050c01080403120e0601090b030105270a14060901050f0106 70
    0xa00703075200c41c2c8405441e00b000b83d0700e613034601c2d0500603520904030395011100404541c2c003d01ca588185e030b0012910740c1000400e6401000700034195100144686464040c10b80104940084400071580035800f101440f1140da6041d9180c60f0760404070391031070f070000710355a210f141490046003040c6440110f80110f207601200410003c04000000c0000d4100c4c01801d0301440110000d105070a41e0a0146085c007100c20990741c1e0b51000210b1000e900d018400c25408100300514400d120300017000100350310341000c01d00380441c980140e908150440f0181220b000046084104040b04000e00000035001941580009119480d0040011002c03070140203006009540709020100081d4055004190024001d18060110f21001c070000d0040d81e02c5c1103c0e030025503100340010800260b4a129490401d00b00324001d104600304500c40401400d030501214881102200300d024106d10104548890540d2110780e6400b001803200c521030325805d04552088541d400d0100088031100c1812504d8143e4900703460f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 989390989 1250 989389739 989389763
    0x20a140f040e092b031e05040203060f0c040603110403050f0a0302060c2a0309031b0306181b061902060a060906061403070306030611091819090c0308040303090906050607 75
    0x83c0c610018040b03080c004082c143c0e110362000c03408500017002c6c0c100c803030315490104007400c00b481414646100102000c494520040902840140c000c04860031a020b601d00410b03078030b806001002c582d204a5000801910440034401c0d50800301045084a0300c0c025000e03101c441d40c4d9010389000750711441c3d942d600c48020000b007402d9101c030309a001c8011144100102c9080401d0000402c0c50040c40d400c2c0c1c80d03945e090115502119107070030803500d0790041d2800c500c1c110003008e0140540c0d0f40e44c524203030f0b5135155169802854083d104c04c030a03a0304101c0104c5d0028004d048250029448800958481a081e03003490030100b12225130307000e034408031082a07a0f140d1038030b5100d05040356250000b60040b02056107681c4000007152884c05044c1500d1a0001c07050f07580d9035503038104948000c2000f90080120015404c0016029a44101c1241440315000c0400c50401900d8440f000541d143c10040c0a02000b040200030b141d40100080103032521504d00b0001c058030f8a040003403d00800b613008000a000e40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 989392239 1250 989390989 989391043
    0x20c220c081009151e030c0602010209011704020d080319051b0306060d0e01060f06030c022803180e010503151009020702041506050a020c0901030804030303020a140f040e09 76
    0x3900103050340320441c0300102e2850700c442d541845078558172544204007035090414000d104142e00080000c1100c0c1c0004c520340009000041d090050031415261041a000300213415920368880c100c40c0c881c0c5c0311000554920340081712400340c8254625000143d40340800103850b111291002c01005c4800030f000908583d06ca504100c0103500130184e142640341c43c0d101c203207992002401000003a0010b909041f2040d4249a0018200c81680e40c0300030441d440f0440c101034080b02c0d00358418100b114150390719041152401d0035241428104018440c020217090000b5021441076041ea040c2c603022000c4e00c010320040240c0f03803080d080964501c40718050700d550410804172541d00410a80e440a44040342e00c00d0007842c108a80f0f02c0585c004c1022800c0000ea11407020343c10302c07100300641c03411503641c0031039411500c58940d02d0049000003810715900150008100d0301070008596500c0c102d8080d256560100040e9404680040c0310300e0340c0f1360000070040741d10110082280041000d0300300300508481031071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 989393489 1250 989392239 989392241
    0x20604030b0702031306090509060906090604050c090a0905010e010e0c03190f0507080703060b1e0f040305060117011a032e0603030e180705030406020901020c220c081009 75
    0x54000c42c10f52008003d13810010710000c880100030410782d21074141d04c91804081c0a980d50005049600c85c4041004029032703036903003500054100c2c0c01a5000622035903880c20104c030512520384c80b03561045c03503510b0014000c0d000350401740c1030f00c08414160410343d036039207a1200341d050240c0e0b04107103100c4140000340700041d018240c00c1d8142c000c2e01001c941001304070f0b110f2048600a030360203070004040c1c1e42000362250b054015400100b17060708000f407901d140304022024060440405004034003000400001150442052702d0145030800180c0b14035595a0400c02d828040301c1400c0c0740c040d400c09081403c0703500480c008013160400900a00441000c0c1c50899480d52a00000580030071601180640718134140c2c451503019510a8a41c01c80780e5445804011420035001c08044078113105a040000c020750040c00e598000317900c0710000d0f03107443d43e180c0181d003070500d0602c000b600a01400e070a1951301c42d141e04c0c1a500340714038000410241310102811104048121500c00700c40c070041408106603215 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 989394739 1250 989393489 989393491
    0x3070306090c270606020f07050d0204020f0c03030919030801060c03030617011d070605040b0c10090605060f241806070c050102070807050a032405042a03020604030b 73
    0x89402102c01254481c3c00302d011100c1e4002003003d01c941d01070ba1014039803480e4407501028203040d0000701000d0701c900300844d03907402090090700d010300c020755868070031511140c05440e400c03180b49401544407960801031644c2c039041102c02c85076074426103043c3e04001082c045024021501650b8015040e800c240d0182ca07040f55424003101055500e402c00502c50b140500e004215160395400400c0b4440100b8905080a0800403994025040404200f001c241c00000f1202200c030180b01141d00c50a130010102d04007040505c13008121402e1a1924042048940c0421b02c2100c0856040390f400e1280740c18480742e2800d40c4080c90500807101e0f6a4a41c514200c806405680c841c1103c0514920300e0401048440e00f2a400464404100c20000d002c15a0188181030140051074001c1000c0c0d403405000401c15001c5120140c07403e5500c10f0311902c89050010700090f01c01c0c1c80c960078001e606140c0341c0105102c1000f5140f108804400ae010780b5480c0f40c4121080c101c940080c42d43c0e0800341103031508401a90 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 989395989 1250 989394739 989394743
    0x12060e040f0212062406030c160201050c0102040b030a0e150f3301020f160501030914030a0c02191a0a09050d05240c0712140412060e030304020307030609 68
    0x4440d40c2c0e00b82448008100c2584200d07000d820b0510070705640070040905d462040c41c9903108180900420004400380803d0b40c0b01107420b03050340600000c00c0d00060307c00d0b10949000000d01c1d40001004518142d0f0480218001c0309900003c0201c03480d000002501c07243c1000f80810404c070750201085840c412049145d07003000030386400c0c242c52850702d9010030517103003a0b442c2c0814a0032000100c60144d81c0502c1240c40d03c1d0501c0000e44100320006040d5103520210380552414141c0d036405100c02e001c00c03401504030302280d000c2169a101215640a003813495070780070481c07103801c055021039083e0419000810840d000c24031851551842a58441010340000c02e003101001187c0f44001a0b50f540d03ca442d01030700340a000075005c1503140c220a20322070b04005003a0315940280c5020700a0750710707210b8219220a0f82000c4036881558513510202d070041c9500009901003400441e002c90b55128070b5000e101083e104210402000070540703c02c3c1e840380800c480c06940758100850410106503a07800030081d9078 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 989397239 1250 989395989 989395999
    0x2a0f030403181706060f03060108150406140a02070c0603021303151b110d0804120f030e010203090d030f05060109120c08030304060207050c0910090216140a020112060e040f02 77
    0x1e880d4030a1100d203074021103030124681d04c0481402150704158101100140054010309010f6061100346030352828034410200102140900003414005260305c07901e452509a540c0020030b040c030780610340107500100b0040e01c4c940001a00018042d00030310840d081242521299001d051031500e03060b4080a0b842c442410135625400107403107268002d0034000100500d41c0700c1d00d00007500401c803603140c00f00604c440c609201c003510500c40800d010800002010b08a031030715400407250400c08030301800901402000039800071080c05001036010a40484000213035808101210040b0018001e40c0e8081d209940072500021040c4420703080119071420b100c0c0103409004030b80e6600c03607285146a0040b503041e10480e50100b00b40040040510400312210002c44110810b402c2404001075204484d1141021040c2d00044840a00e504404203138041070b041001c00c10000006011640c541d0490102240050440d46801c0c4500d895441000b09440c0540c10001e11a59603580c0d5203495010705c6411f903440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 989398489 1250 989397239 989397287
    0xc030207050604091410060e040e101109040c05032a070804030305090a0b0306210c030a0501200403050703061107200f04090506061c02092a0f030403 66
    0x1540b2078034010702c01040c004c4000100b40004000390206003c004d06241c0302114001c20800095901442a40d0381c42000c40c0c0004004507600e005903d40000c003000c44000074180f4440a001350104c402070a021141a01e00344880c22070140c013100c00340300480d8807079160204074a0708020045031f04600000003078010a000d1a00006803107207000740c1c105030f10843c001500014440c18030300f45450400020701c814270002e17040d414458005842200310b00803480d8610070142240c5800c03441001041003404002d000d503a8085a64204207020304071220394030f1003200c8000701007031648000c40f003284d0407650090701a00300b960942c2d481102402200341d081c0c025240600c40000070032001049601080c50700341503c000b1842410a020050700ea510b2420f21407071514503c800440c50115200358000c6048400d200c01c0c80818507860384030300103000c0194120f00f001c0100510417105501030300000e80c22522807006220100d4020038240300da26140458500203002040c002800341e090394440b044820211010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 989399739 1250 989398489 989398499
    0x20115032a0f0e10090e1b06041814010f030201080414030910050a0f02031303060908121303090b040f14040f020a120b0603132d0308010302131b0c030207 68
    0x9000990704185148804902413207044501158400b00030608840300b40280e4061181840d187c0001466040c4000b0200910000665944049802500600f5910398080c840404140c000b0502100455036107103542c400070498440c0c0b003c03901d08817a4165198103665407266102030302d41194800004843c1b10600450030140da805e40ea0062042c41991460b03151041c2c401c000b09101d4003030b03001109641042008aa0301c443c1160441d05880d0010030110b02c05005250080c0c56118120b4440084145c100910601440516940300340900030b684412956459070315070001e03807040340708150a41110704010407400b0503402100d044404010400a0b820415404000581c2e00034000f01c00096440811503112034000d20481e000120161681403d500d0000c04081d011041c0784405002c00e078081407290903c4502e9203c01a928001e2445503107201224500604000070030701040748540c00801034240f60700700307502c5006c40520411104411540415805a90782c0e0142c50054045004020002c52 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 989400989 1250 989399739 989399759
    0x6240a0e04030221030c0c070b04091b020106080a03111531020d020607020312130e010b0702030606010810031709040e3702031507020115032a 63
    0x408424400324040d16180c54000d00308421101d40b503420140f16110040000b14400c10303070303a002181300c074125038404240d442685002c5540d0322014441c0b00004010840180710b0300040424107582c5180d0b81d02c030b50032050aa090728100e0095201687c400e29001012903c500460103180c1c4000e4241c130700510302e5890340011050300b218140103003980c07141d007e94054000740b44610003542c007074451140a0180c0e070000320320702c0340c00c00085c2c85445c010825070305554051101311041c084458503142e0f100420141c000d08a8039600c2404c1400181c40000100c040100080f1080c0990040140c085652418010368029101610049019840e1071008c80010004081c0080492100c8001520b4043c0601080700b510350b1903030104002e03007016075402070b14442110062200410010406410302c000b0030100682c03401c1a00180d4144144054000b01c4d0a020f0006030059506500a01c1440801500c0c982039840b248070045c400303900d02400741080d5841403c411b680ca01c3e0704614038812550349052507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 989402239 1250 989400989 989401009
    0x6031b08120f2107020601060c1a22140d080103030c06050a110a03060509090f060a05060d12170a020f040b2206170a0515120a120914030f0624 63
    0x66401e030b084404e000a8a804000c00b0740100f58901d807a150010044d1744003241488503030342c07400b0b040c01980045601c040301c1ea080c0c511450b082c9106080d01c01003d003806045044102c524000e14014002d603030580c10f219681c9181030325010740341c011101d055903951000801b0300614400446035280a000118852040108039000b03083c0d07804520035042400b008000c03500541940340c03552000e4007412000030080b84041e40042c00c0f140c005065a203030400310f0424401c04a00420484400844d40101e80d00702d00071044801e030000800500380e80380742c48a0304a215408100d6076a2105000410040588100402c0c01070070b885c004003c488a1004124038407002a00810041203400c011014559050801c0d03c0e032010340e80b0401c0c030541c144500950524584451810b02406204203078a414100800900c0d03007440e48858944162448568000c001e54214016080b0700f007844c840600880c50002000c2c2810300040015050b03503268014843c820240c2c00303e500030b140c0c1c075010080d1015555541c8030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 989403489 1250 989402239 989402287
    0x80702040f1d1c022d0610060e04060605180f060708040501110d0e0d0809030f0d090b130509040215030f04060f090b04080c0f010f06031b08120f 64
    0x200c0c0d40203481a02c400c1c01c1024144040b03d100d00c905a0220105030b00041e15484201c02c12840c062072134160008200e00c503001c41050455118010a02c40c5418020300d4410450300b00d541d4154604480c0803c0000350b40c0c081c800d00c1c0001d1010300030351400c002c1120145490380b42c000c0250f02880038880104e00250800d15041d41c0c0c200000c00c0800c0996006800d0307006c40c8481401a1450a00e4080094820100c00c4030442c000c504e4143d00720108004101110750700000103045820a2086080035555800000b400c203001602e91100002d1103205141910166142d6003030000e09542000107002010348014400c2e03900250034074005414500d8100154001c01c00000305040741d28040c280f84050380c100600c5900700b585882c1010000c00c0861841c0f640140c3e000031540e40c0d582015011524010411114003429440c01e82c0c5414440130341c1d401103044a2085250305843e40c104800c4910480c0180b24042640d041489003040540110b8002c10080c400468a1824004903c20606da0701198541c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 989404739 1250 989403489 989403521
    0x71b0804030231022511100e0603010e06040207080a0807080f0c0306100210060806041203020a08010603090609080c100f0204050109050d02030703051212010e070c080702040f 77
    0x500640c00c0c01035011003c994003089400c8010300326100702012801903000c1030006136000c00c400005080c4040916003400034681c000080800c80e0a080c007003645001783c014440d50045043d00c4585018551441a0940041196045a00e4811441104403004100e258015400c0140e103000500d0500a409078520650340d003115841c01d980040c4c0b000300064170b500f0100b0b0040c4100140060802c044940c003a1060b5541008030f0a0a501a40751440c0b4000c0c20803828180207011408003400100144180c2c0200104040c1c1101b002007a8202c0c403814403002c00040d001c1005100150094111501f071920840000681c2011500d810015402041c841e4016402107216404103a41c07034010103100c00d14020085180a140800180c060740d020b108640c01407480400501c1555000e0005c007000350b80200c01d0721100c15450380700c0002603000d411a0703496651032800100d069214119114030030034075915568050b282c2c50300d07085405d401c03898080381d119032940d411004c1c08041d40201d0000d007440c108 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 989405989 1250 989404739 989404747
    0x605180a200303090d030c06060e0a0f050a2711040c031e15060c0819080402090907081b0d050111130509060f0603091204080c01080f040507060503071b08 68
    0x2407078404164045410700d00c00d91052082d0040341d0303114060000341d01c0d414102030342c4502461800201510455204020080c0b0100070000c00c900c5036085070800108a9074104a5643d4000c080b10032110b17480003a8102c04e00b40c00c9241d804a44400151181502442003440481d00754400030b0305545404490b403000985a4000710305c400144013410300800c1c1000ca050208941003480303000700d00090301c509010001100c0ea40001c2c0455507003250252418603180804155460300c0242101c40291000c82c02004690000340318104045900000e0b1081d8001034a8052a000500d034030900c0034490a9134091707000303031078007000030001d100384500d6036885001c442d10340d0481094400e0302611648600c0c01890010200500c07940c910004280c0d018045a50f0b50700c0e0303210000c2d120701d0306a4201400c4410400014003051100c800a0001c0b04260240d8a005d1207030759010310200d003031074140c1d402082a40b0044081c13000360302a03c00303158010f03031720316100721495a01001141c4e211200c0a0139a02d01c54005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 989407239 1250 989405989 989406023
    0xf120a020d090f1e1802210402030a06020f091503040c0e19020d0e060403020606011431050303071b1401120e0c03150103060c111e072c0906010506070605180a 70
    0x35203000761b105896034600120301d440c2c0c010070b4950030bc06030010710381d540c001040200040050103581e8a0303134014000c0d02c20007600705200c2080354001d03101940c1869191030000f5141e01c00e805c0207445400060f030344411071460715a5402c06500105010071174076450b500088500c4074100840c0303100c1e50191b4005c01440c141140054801203070030340c1541d9055400c00c4115100c014184802074100c1c032504407081109454200011155480c0d0041507050000007601418002e9081645102c41c0c828210701d50500e0380d41c41016a1101182c6d801404141c40205000000e034481d40040100c85180d82641c1206046400003404c191408a40c00d0400907182d006006100f1203210b0004810b00c1810030303041801c99800d9032a40c0b10b8034082d01d260a502c0000d00c21992800c280261030082c5508504000f400c1c1c00701030303400002901406a41c00c0701b0501800103401e6500024854126100078040d1403600c13655846507000f4240c02001a0300300c800701c1115400d4800100310511029011f80d5110706000303084 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 989408489 1250 989407239 989407267
    0x130b04060b160b0c0a1704140a080a080c042d0306062d0515030921090f01080c030105040b03030c0706170f060906060c0f120a020d090f1e1802 63
    0x3404c641ea0101040c003c030741a594000704041c890310b008074171010396583c6034540ba00e50040b00d01d5610405006203401c0d0b03800c1040b058040c03c2080c0c5561a180500d50707035520704540b14003030f42c410505c15050f0651442004140c11a128690303044140203610031507101c2c2c41380d8050380c6090780803820448401b0014440704006001d2440b404203105ca00c15074452400300010794056404400024848000003c2a20420100000c00b1501c10003074008030f103051100040c0b01e250b00248042d601174a546c6080300401d42c81802424407800013100924156403d060910008048140c4459058030003006100c0f002d06042007181c00600882e550b6003100c40956840d0b00e211130700501884080102d100a0140d04c1d5140c5440c40d510000a95034136480d01400d0035a6072424200c00b20400803801103400380c1c020400008011300740307070807160211424003241d030400b10741d050b01602c9010000f02138018240005108214044000802c4145c0e441c051a10b5810b00003102c01c0e01c09450075040d5000848071001060 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 989409739 1250 989408489 989408491
    0x30a090b0f04050f0d0f050d1101140a0c0309080403230f031e0409050f271f1b0302030f01120b060d140717010f0605130b04060b160b 59
    0x91a8015801d203007140e52019028065409002e10500b42d04008040c0d588a503d08401110740245c0726410303050044c1071003901c540d6045230080004410841147c4980414002c1c4c00f9003100701ca407c1000f642d0384215800003800031140c0c0780b00b0152147c0c0f07184040b80b40b480182c0061800f80d141c00303c01714190000307081083d034240701202081c2c1041c0e0141001c400003205490800000700c4407901c212882070070003000d031f20171038100580481c5000d090010403481c0100162041706001800e5081c42d609451902c40b0542d0003203440995401241809890f0490701d0340d506c2c1001410002241c80309414401d007510f803c842c0902000a6404000c0190042c1146021801020700c02614500404c1c40e0700c44401c1154002c0c482d602800c5141482020005400d03084103900b40300b50180c50a0584400019407526449074801740300390308004800100c20054801d41045450007010120f0911000000b0b9000d41100d00d030b03035a0700c180d480c0300004041038010020640e02c810407100800844103460482180c03c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 989410989 1250 989409739 989409749
    0x1b031204090b0405180712061503050a0b1833010b0304120302120112111f020f010b0108190b0904060903030e010b01090b390607050333040905030a09 66
    0x2085d2a4002d5181400b00d448415118175907040c4031001240c1c00d0143c0034104854000700c500c140348500205210004c240400e80700c0c481c01031171445442c0c000a401101d20014074007551a0002940401c401840010a8101d02440c3c41458654012020340b800c41c12401d80c4815003821000082104025003d182c0e124070981c541170441c105096a100402c07507003414020510403911000c02d041c24412823080050a007200105940701c1901001503044110100f00d00030009481040e081d2a10880180240006540180d480c0f8141d0790700c40c94000d910f9100c480e940011650b50740402c0e01175407103c0090500c00c80c060030001c241d011092400604898200c01092440c1c0d140082015803682e010182c1c100300c84030b1a05480e210b03130038180918001c130074000b03454403805440e046600354030001e10f540381c44bc584c200007603945585e01c4c01805d0341e40e80b104541c1000172111450400c0400c646180c04012149201c1000300d0b19a041d00d000b103030840c1d40e901e4099a6550001c280f0aa4880e480034010000d45 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 989412239 1250 989410989 989411011
    0x18030215010b040b0a030c020c0d03031d0f0316150e0a120e030d030e1510030219030314030709080d03060e070f090306020903030f040b0702040f020c1b031204090b0405 74
    0x245001300d003010600940311403004160312200b90580d5607108114890742d041005281810340d01e076900d070184c02401d088240e99064002d032092028100750100d404921401900080c40c9001c3d0011094414648d205200b140c5080c035907200742c4001c000c01d1040c1a4132190450040c5540035441c00c0c84958800400700c91070030402d807400254200d072000310ba0010070488908002c205004440c15141c1002641c5070b0a1111035041010000030145140c1c0140c100c2e40283e800020350700b40b507007451040c990780e8000600851075168500c28800c41c010001d652041291504ae80404e07228002e171810075050f11958000291140c0c014004810001116504641d20b400d1403456248402005800d4089501c0040d0506d6404a00500340e61000d0044440d09000308110665858803010b084505800844090b40224600360041c80e4416052003151102d001090040ca0300282c5d081003a0b40e40d00782c0b4280c242d0103010751010884030303110a00c0900302800380003002180d101064000e2004071000104a20008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 989413489 1250 989412239 989412247
    0xf0703030b04091a0421090f1410050906040e070c110301063b01170d0201020a05030606030403211a030309060703051e280c0507050f0418030215010b 66
    0x240b580c4411400790810128060300b1030744c460070b00420040060700c41030000f40107806c09072001a0b04c440d102e025540074181e00f50501e522040c40700600303044801d415404c10505603c62403003500410151102900c010680361909488612030b12840c041502d801000c9803c90002d0f030100301c01e44100d2001d101c81500204910752900f4804480840145410f242c81e8a02d5120340044141a040c0b80c41c09005050000c680c40d43d43e009078881e0b80b41c0700e041c131100c00d014140e0396036203452040c001c43c0c3d42c4244a6a4071070858407004100480c59001030030442c1803005074101e2605988038400000c0f076001c9802000030740d00b00e18000358030a10f0165014a03209410030403940c41c2e85c1c1d842d001500c03481c40d01842c0441c2c5810481a130a069001b80248100e964030011440036030151184103101c0ca00903940c10f044a000c08211415036464156042c000c00b5074021080a108034103040103100f03142c1c100204045105400300e0003000001040450680c016000540c1c40c2d820226980c0c1d00c41c2c01010300b48802450 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 989414739 1250 989413489 989413493
    0x40504141009020d150608011802090f210718060503070b0d09030c0506090d09151707120e0f1e0a0b04080403060e07060f14070213110f0703030b0409 66
    0x1500000b401519000c69000c40c0d0340362195034982c00b560f04581084200e405460700c4610141500c9001d11403102d28086840340c1c16200d250034001d507400c0031000342c9544079444144040282181c1400c9090000c050800c00001740a042048110014250041d81910368000c10140307006490154003c4c07401303940a4801004105500c00454224401103880000e0340c01440c80d003210b4003009408045c1c0f05100348014050031490108403448a0160303901c80000c5207580b000030a00100c4c0c0000c01c0e0300414801c2c1c050403410a40c008035280e202601e4549070305441610445c1000700c50701240b09000b40d50000c4080c51480c4010002107242d407441c05004014040d007660302955a60680a009018070f828030045001c2110442c199006141c0c400010700c0040c040001040ea45e906612449000458414a14026034000d480070030340078840b4500300345003004903000c0c09504002c0600b040d01c159540c519000c1398447c500f020301000d4040d00d82c819598001410003c056400190070b180c0f180b840e004000300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 989415989 1250 989414739 989414761
    0x3030e070501120513021f0815061918120525091119030f0c05041224020712030515130b13020d09033e12040b04050414 53
    0xf045207501c3c5012038103590310241c40c2c103d102d90480c000d410454150382442e800c1c514801c80d286503174031030340c4041d441d9480072009074090800710090742e0041c0b0100001c41d90029240c507d00c003008182c0c180f2200520140740d640303203900903960221280304100d0f1100001c0240c02e0100c03400d4280000310740d090800b5003607440b14034002e5610131125460394501c4c81d002c1000031034094491118000840e030700020041040500907115140940031103a103083c05002c401c0c0e0191054406540408840101c2141c050382e81410907100341c040681c071400004001c801c0941d00c0c1c0000c000051094601d0380200d028808040c042d9000501140c450450700520143c01751103030904030300440c1c000303100490451070780382c00704046940708280317484481d00003e80c401c1e80034015000384825601c82c1d07440081440284c900354400000d200c215412452001440820720b2200c043c4040c2e54140c0c0d20282c1e50b04110b0001428065445035001030107d841c041410031840c82c0030312440210000c450700000304c6203050305c5069 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 989417239 1250 989415989 989416007
    0x904110910050d1103010603020c0d020604050c1009050d05030408150112080921070f0806130605060612010f1503020a0f0305130b040b0108010c1b020f04110d060303030e070501 78
    0x71040203808140c1900c03040c550380040c105164805125666941c440000402a40c04070103240300d684604800450204d10028000c9c0c81290480d000d046c07040c4e00341040101180a4101500c100440c4010101705580e0b00c1c070038440380ca407260f0000e541d110b140070142810001c948803040703021000c10004000082d00c5042d003000c02c40d4041000350f46c510320300300020110241015012401901201c80f441c90160010700d00c02070b075207510480d4078210341e103441880d510308080f204410580c07400d00d0400c0014403260000d03508201e00500850400034144070311030450400364001c0c0340d08100c000d4100b0005002c1480c0003481c6544c0d1a05607c1d014004002401620740d01002d60105591240061501c0c004a0304844042e43e2200c102889410a400c0402c10083e003800303400c502c1e5190040101c1c403e4014280c0384103c501c42d2600d940b4000da01d408220001c0d60078060940c0242d15140c13103861180e6844c0041000700c40c070400008050b425414020f00b02c65005002011641c811031040c0b100341e811a41103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 989418489 1250 989417239 989417269
    0x9030810030c060f0909020c010f0609061d13020306040813060507031707020f0a0803090d0306050307120206070206070609150e1e0a0615090515060316020a1709041109 74
    0x1204c24049100c0c1120486219481030813510302c00b11750000443d0781074026040c0300a803004188440794403100c450b01201d030184226900c032992100e54141c00900d101c070b0300d039010035156803000c00207a003500820b0506808680c00c4400c45400588401d4084040d10400c01409491800e5414107a003690083c0c0b1580c40c0c000000c1c6682c000d0303400502c8180c0308006030701e44241c051050710000c41280c80c0c00440c07a003040d141c0110b6070107020301d510001c0c0e01c203104c0c140844000400400311245001c2d14080c1d504444007040e40c0181d0b0402c0329030090307100c1c0700007406018403c0d180002c590401d410141d4501c0710702c1c1042c02d401401c05503440200e00300010101c42d0300d030000311481503480b400031400c0c0c40c00258220040110741001d809465610700c001c41c0c031040395a004014401031750707102c6021500d82e102042c001e52000b01400421400140c070400d4908808441c01110314021041d26242c0f410045140d0340c0b401c051001030320b030880c2d0820b0701412000d1200c41c10003d0610980e00009804000c025243c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 989419739 1250 989418489 989418497
    0x3130f0905070c020607022808013608070204060e0f060f1e010c02030709021201120c06140c010f0501060315030b06150d0c0203030402040c0c050c01030b040e010f09030810030c06 79
    0xc08419944d80010003031a9404c80454005024840100c88c04200640d200343c071403035403030b01440b84800c400d090a11a9070801019454100140c0c056243d80404080d50003641c4050082c40b11a006071100d10130700d406001007030300d682c842d17180044484224000041c8418041c1c0c52280c8610704a407180c03101581440140e180d004040002500101d031803901076034002c0e526201d00903001503000360707580c010001345a005a0f0703a101680c81d60207042c40800c2c0a40c00402c001000a02000036612030031365035000d6408100c62a1500d03030314044040c01d44094504070b40d1810369a40c010005c960f01071180c100b4900110300741b0f031001891900c070aa8140e50080401d03005da011120f0100c1122000400c070b0325041e05100c0100590000300400954030382080f00e04a004c0e500c0c042c1c244092600814a0100480e1f02c00010010500c0d40001180600450b00b590794000741ca8207100d10340c041c028000c0f2444902803031000254a0710605008002a4000e011204c140e525120306002141800d11540159001818 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 989420989 1250 989419739 989419747
    0x60a050c040b0f282001021e030610020601080303010308090a091509150f03061a0612060102211b07050402040315060b0a050307050310120f06060e0c0a030e0c0303130f0905070c0206 80
    0x54450280c4a10000004507560800f1070420365640c00c0046c9d8010a0306031a5000c00c0d8424010581e5202ea080c0108041c5a2088c801000007811443c010504250041c114144d0103030b40c2c4024406440b4020303030713504014802e8503042c400640c03e44159101d00b01d000703030312701c081d02d15141c002c005480a5000150580da100c50348c0040035610484d0b824055140074194a5482c406400020406a03054410314014003d4144500302c042d0b040f007940303c3d4211203a40980c60030714000703503003007400c1e2828008482901074000002120742c0c807880500011801002900940c056405001044482c19084110011004d00c483e101c2688e000c400c2c0c990100b030a040c61a9030f0346a541c08030700b1940c1c159110303103200503c00490408100000d8070070340c0c40074030030340d010b1107100e4039000321140800c0b04a4048103e20000d014408041e40320360080000b6005210540c2d26148418020034216444500240d440454003102000b81d442d112440e4401031010307100810050812100041a07500c1460001c0d00c6010046 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 989422239 1250 989420989 989421047
    0x2f121f141903080711030c0109060e031c1809020c06010501210516030e0705011d12030a081e07020309040f0e0a030f030b010e03060a050c040b0f28 65
    0x1408406410a9400d20141c1499881c07824116503400040121814030705044a14141c0c1000188061010320585410141d542003107812505c9280440415a240c8540d510b00c04100030300051302695050740303944182c40220140440e0715684515031000e010700e881004004841d000200710705041d507209207400231052003c4100200e030b1403520044e04014030303e8030060106019030840208441451614144002d80d01c50b000551100e5051280034041a5142c524010001c00342d110b10321007810007080354100c640068015480d6420008110f8041020b5074240403d144d803541408805022800d01d03160740e441e107440025228050240518000d54846800c115000000d82001e840c444020003180e00744030b170741c0c100105038030760902d13404d00030030724200c5004800d5124a418a000d001c02030020065501c6010b000c9000741001440014518802c0c0408502d038403081e4000c102c081c4240100310b48920b81204568494601000b06c0302c41400341250355844c5603000011380c10540000c10000ca00f40945e2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 989423489 1250 989422239 989422249
    0x30050c12090a08030d020a090501030b03070b0901030f0207061d06041208070e030a0501050609160509131b020a03080a05090a020f0a050d03051b06192f121f14 70
    0x1500003c2c118080803070707031180c0c1c80415405404d01456aa661840407982ca00c015021106210740c402d8158000d402e090018080d40d81c01000c0b0200103141c0007a0031000c501c905400c0f45c01802003200c055841e291840c0714041030040d00324141c00110082c00c4582000d544844881c4942d082807801e000c0e0080004202900904955030201c03009810b540742d041d01031070a20300078502101c005118142c80c0c1c001c90551055035001251208580d05c50398a0003440c10f040050034170940f04006c0180b0303120100c1e102c189154001103c3c4508081d002480e20301c0b41b40c1f4010f800c1210003000c2c40c40b450300e80300400c036038407a000454a600030740603554400d40345058804541303a03111507000140c126001d040704604040c0e11400402d8604050040d007820f050101c014151102000e440c0c80400d00f46424500175227442c00d40c05502d958800081103032118200c02840c100c4004420840e140c0000c0102c0d500400d504c00807001d81d407010869206440300d4070500303818100001240030304200c09200d071018030825120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 989424739 1250 989423489 989423509
    0x1091401052203020c06070b0a05070e1e0d140703060b0405060d0f14061008010b060307050a080c160605070e0a180c0905031b1315090b01050730050c1209 68
    0xc0500050350701c0229040040030040d05449e01030006203400001031505d4410703a00d0103200300004100180030584204a186190440c4514036405510f01d00309000081003115808243e42500015010b01403a5081043c101d4020b1f5440c0ca000381c0c03c200c1000216070f580d0382203000955010312030841d03041c604e00342840c055442a500c0201c030702c19007050201c2851840c1020302102e801400920509444000340b02c6203004c1075a40c500031807000e00c02d0031070603402103690a80c81040d07401044d0408080c030580c40b1115100760000e65040350b541041c84003595002c804000040410b0318243d07002e40c9414240303010301203807078403030344903107035503144840d8000d00c41c1c0104001807900404451b0b00d1092180c2404001c0c0d101d064071842940ca103551914140068000d0307100b078014805e150004180b0340b030110b0002e88041074000d810004e017045440000341c0084250003aa902d4000c0e4030758801809411a8241d0301d06501b08800e0110500084000c00303030014800300030914408045494103071040200700b0100c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 989425989 1250 989424739 989424763
    0x29060d051e010b0f0315060405090a06020a0302070b0a050f04020111010e061f0e09121b0d03140a2013031a09010b040501120f0804170109140105220302 67
    0x1001180070078102105400122001808990300c8001140708004c03d9502c0e010599010400142e14000800a14141e40001c1e84a201e450540f0038160807640c03510200da100c1c80507400441c0e40468900240000f42904943c04903403d6000c0206061643c0110b011503002400241009441c9400040100c000c0d0403500f80e100c0c4000c01c407280f42c02c00103011200c4005113503000000c5200c0d204002802d0b141900c0c11402030b00060080c1500002d0b401c55008640e1101700c02480300e40e1f181d0b4460480c41c00801c61212541415170300020406200c45140e140c101001e40794042480c10a040b03003000340b2180c03e01c240c03c0300c0c2c5504200d949070310036001624007014030b0740003400c45c0300304410001005140109c654403d4140c0d40007041103954407020841111000c0c050f0f85203c1051184400003d420003650f441060301070b10343c050400381c2e0744402140c1040b1000340001031f651944200801c214161030081009200a4024041840c04200040382003502d003d40c4540b0045803008801418000e010f5254186 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 989427239 1250 989425989 989426023
    0x12030d0605060406080a05072a050c06070f0b09030708040e1e07050d0e0c0405040515010617070804060e011505040e061e1b0d0209030f0a030917070807060c29060d05 73
    0x7507040310003d04009d0400e50103a81c0d03400f6282c41f0038020301c0d1202c1210b0040d075008007105030030b0301c0540b00c4d0609500010201412403100b08150350100c0c003070700007138801000510ba45031120b103040306944013290501c18424018010b1300c410310001d540c02c80c003620110288010001000d030f0314068900e10700070591160b150400c2c940020b0105000c40407640b80b40b10040c01c041d03441c807a40d03100b00c21903061200605080d0300240803400302d106580300d01c005da50070034090700c0c020641070411800142100d038401080440941c50480c00c0226003010300036020506078034409003070305281c401c0b502516070b40045140104030f80e90400007071511589860348400d0a200403406602e80d100410f0043c020346c00074840714480c2c40344020300c0c2000c2000007290301d001c0764155101c03130085250100e4110b00f41001d072003000c010f000c0c00303401092105080014100030101540c1b65015100c89042090031107a400005402c40035850140c040b0b443c181c0b580e103a030000c40c141c034030315055009410700c24101011744040f54200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 989428489 1250 989427239 989427287
    0x90501030506180c1003090f0b090304090c110c0d0201050409020301120c0b1e18120d0306050d0804060f0302040b0c0a0c0617040b090c12030d0605060406080a0507 72
    0x8008006202c0d4410215002d08400b041d08000e030305590f80c0407801c1510741c03008003015800c010601c60b80042c1001441846e510030010740390b603900c00c41c052080b201c41810ba40089401c02c03101e4001d000d403203804081420b100071107807121141c80b6152540d04040754000d5402403024011640301e007045600400c4c20384821134032940c40382000240341450240135103007a0808000450074012070000c0380c1d42c02c5c41c0301e803448031005071031303440140c03503402c90014025481c08801d00c0c008540c45064950503680e41e050f01074502040320003800f8007226000e403c210302520441e02004005807682003290191503940c10490080040490220040d20550b0064030310018046803007283d04000007619485544111b1210140c56101c0304200d0303030528604070102c04075144202142c045203040c0507264001c0c2904056600000608001c60342602505c562030946c0c2e8000140d0152a0300d6030b100720300142500325800761801d458010002d2001c0300103040c40032080d0742c2d01c0204540500481c00024007a800c05908180 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 989429739 1250 989428489 989428493
    0x70c0315020408010b010f020c131104090b040e0d051e130803070203151005090a020c06090f010c3b1002030d110309060c070f0b0f0411100e040f0609050103 69
    0x180d08103118400780d5600301864217400b0b41c0503145c000c40c034880303c0d03000b821811020401c0291a0440314070307100c0d0844c0e85600400d0b00032401d4000384003410924401142044c1c491040c08100c074a580c148486940010b4184180a80d00c8400c0f17820000541010352001d0641200d035800d40c0c03040c00150407201040c100d0015900e44048090706043c2c6c004c400340c45455040407000c1c0c0c402042161503850400202109019616241c10b205401c109006001800d010359510a285002030a4031054271304e03841882800c01c40c80b024000c6801850240c076200700008200c01c0411040980c501e52040071190741d0040d4540030321204090000d140006010088407000c0700000b070b4980d8888544843e005040a074030390072a1012008603401040e100c0000e14495039802c2c003580140d0850901141c0003a0150100c0010681303100d460b0b40240c18044961503581400d15104020820080303d0a000c1c500502c220300549401c203c1040c1000004e0750003080f00d01150305120001d1559412240c03455182ca0000b00c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 989430989 1250 989429739 989429741
    0x80f0d0c12150b19021510171504120c020d0b012912040c0902040312091e0923040602090a05060403120e040e011a01080601050a020a08070c0315 64
    0x1580005010301080008058442c0d00c0d6582c4840c001c03000e80581c20800300c055a1400450003054286903c1914841c6101c0d810142d10742d02c0036150000041c98421007800306180300c00e07002142d0014040100000c407800b80c00c203102444000c1004d070009414018124065000c0c81e0038441007503004000400c9828140b6084842900030f001d040000d104e01c0203c6480c1d11a0300c001c00341a1088244040c0c00c101110310440c000000080c011a0880c012007400948000b40e4005000a10321514809480803400200100850f070b0551004140703203542c41c62980c25503840b119030010b5072070350103000c81c00c01c82e80c0b01c8451282490110600c5081c4104081005105140d8050044844111141d07054107a45008202c0305015038000640001003c40d00c440c40280505980320943c5c00240c8041907c50305081040d086941d581c2c250f4a15003910115841950303485000180d0100003400c0140c1032210200d0003d40d6005060001001c00000080b03043c18045210211402103502c040302040180007030360400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 989432239 1250 989430989 989431007
    0x612050604050106050a080309061e0d0606020d090e0610020f0f160e1b0a121a0a1a091e0303130e0a0606081515030a0618050112080f0d0c 61
    0x140c2e15510742080812140b034181c00303880803181c9000085080803181410000c0e6171b446440c4400c0e5035120100d0744500c005100300507103100140c0c0a000107061789000400380c1070208000f039003801c01146880c24001e0000071811960402c03001d0380caa25404030180c0c0142e01d0700c002e124011a941c07051103212074101380c0002c1c030001a042a05580c26107075549591542c2044010b65507025040d80711000c401140300010003070301249406103811035280d00740d03840d00030455011000350a44011145004a031505020780858000d14050f0328046500340b130381d810130405025494400e44140d5058a958907101900110b03202c461301c000341074923650020001c40b80c0b4643d03c18818005100d070340740d001812100c803d126110883d001622180b5099458400d4007040003203003075045902068485040302803d100320045d51050101d260f00148441c1011001c1044030032111072a517499060000500851305040089906154480c000707548612603030150f05864000c000a600c4590718111502c0a0a54803020003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 989433489 1250 989432239 989432243
    0x311130302040e0601151b020a0b0c0d14091203040906080f1c0503060103271b09060807060807210522050a0803060a0b0c010e0d091a030a0612050604 66
    0x410608544443c0b25848034400d100d040c20034104c81c541403142034025441100f0100d02d20955907448280c4da80006d1150b00c10303400ae210254004921106101001c002c014100201814a01c0640100d4030b07216041c3d00c200380140303002c2c60524001d010201001c1050300c000e0a8451020300c4041e403038001495a9100110802c49107118469140d10a01e1861940c040d1911a9549562465481d0310054001c0c04006d0301c100011400040e5244100c0b5800400c4900300e8070414030542c40c88180700c04031041c1513940c0c200305d0700a468484c0070000d42c00005170b0382003100c84e1400c0ca6181c95548000650303429010040f028050701c500d414421618500754401c0c0d1040003010140d28914500800d40120354410000041c0590300041d440004541511f0207146e122200a142140154540c454994290000104404141c0d19030010482c000000d10500100d04180e03c0d00d504000e14002c101c80d40c101a1a0015a1003103000000c200d14028076000000a007ca01c40d0a1074101c0390340c03270035547d248400c41d81 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 989434739 1250 989433489 989433491
    0x1e051f09050108040c0e06010e030d02010c0327230a0507050306010b120601200a0f021503040317060f04060617010f0501140c0c1909140c03040f03031113030204 71
    0xc0820036600541800c0d0059400500202e44c0600341662858048000303400c0300c0c148503c03c0c40fa0022542d007007100700c07020110f40e80003088082c084200982507030701c1144001090a154983c10449244110650080c990400380f07030700c143d00850060440040b41c018142d6078a0040e00c0d402028014000342d05012210b0a400f01d601c2c07607903207540c10203c5005030a5420075036400c0f0f00104006601c07030f8800a4161107030008030f1842c0000720291a14224004e0030458840b42c0c001d02d10001c0d071415040d5000300789160424145103113860382c1e0080c03503040c880c030151800301000302c08110702c1c0c2c4030301d075242c1c600039005081002010f486850150040e203800c2d0101c1541d001f000c0000c20100a0810108221103041c0c56603101407070001c00091031034200c13400503980344c4241e50242c8410750752240a1004010080f0342e000160f400d2000c01403c0d10800e007c03111a42c2c010400340000310080e0404c0300e61058006000e00c81c00201460101c014081d001d0003103544d028046513419100007107100c2d840840b4400c0310 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 989435989 1250 989434739 989434757
    0x81b0618070f0b040618180902040f021201260102043b0a090303020f07030f110303071d06210703060501030e030f130e0a14150306011e051f 62
    0x20081c0c070b07841d4900034095050b40a1100b0400d060080001c0b040d045955201c0600e881d44442c402d40c280c0c0e291840e41c02c403503078884817070300d00b541840d200d181c0c06409495419854000b91684100310480107120f0240c1c440b00d00c2e20254048200300d44071113030b4014580c000b03541d0b070360b51151076806102c07440000e40e11065407800c1c0c00400808075110025030803500119400240e5580f2114001042400403d8051507005c00a20040c0b00c000c40007009968426100c6085503140c4400c01071048012440401c03445e4010014072552507040128004918110000d81ca4200000c0004c0742c0c80340a568145035100700c0340410080310f650440d5525204e210b4554040200c640c0d110011000c1d5a1101124600345e0410049801e0242c0c50400038408011280b1840403455aa1030400060780710031581c044841e580c0f100404030034070a100d1059040515045400080529040040d46588041c071650104485c40800e90010300c88101d80540102030003050221410300c50b900c040d038014803985202000400200c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 989437239 1250 989435989 989435999
    0x1c020a2c0f0a1121180f0d090611060a020304020f040e06091c0801120203070e01030507050a050f060d05100f06090e090105010b03010b0f0706050403030f0606050c0a081b061807 78
    0x1000b0380b80e22006013500c8410312007124180d0f80003020050401854054091030260303000303204102150b0042001c00051601a04002000700201d242e40c106604100040004140600001034219002603940d403006135640c0752132000400340001118425001410a00d8403002001c020440d284264024002d0352124828854503c1e201042c13605002c000c900381c2070060000c100a140c0100580c0d20250803520790707980360a8500358000c0241e000f00c1d002d0b48214002c2c0268240f0242c0a80200000e13107115080c1c40c440000100280641940562010303940c01c00105a12003e0300c41400404c0300080c54101e060300c840c40240440c41c5401858a041101b501148a102051060314101c6103148110f50031a400d0405810840e8003440340085441014041c0740301003259440392031301403442610009540d00c502e8805405507880c80d0311100038400305100303921071110081004920254401807503651a510740c28034441d401c00043c43c041e0300741b240404104201c1070400b075400300000b483c000c861540b0351f14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 989438489 1250 989437239 989437271
    0x6090c02011b120e07050909030408123f070c02030c09061f02150a0e0d08060a061404031515080105040305071205160c051c020a2c0f0a 60
    0x41024100040d0400f52100b000c0c02d6036807049010311100c0c01034440d6039a41718000b5440c084207403600c041d10341000500300500c0004010820024844a124605005450504881a079884c86d85070440484070519400d284100110301d164404458041414500b042c640c0104400d009160803070191003a1070141c00c240c0342043e407440c4580c07802802c81c6400c421542034420901b84422000c070030b42c1300d6682d0000074000c0b0400c4092080300c0035000021304680b201381861038038003140f400078140311041c030038408135480d1844040e060300d5003400d04a15002803180810180d216560016001340828000a6500117954002032025140004c010500503100c200f00e500320741d425240100811000c0040c6000540508090303201c1d045141041801c10003841050b4800b80380c1750340708880030020350800b03001c45d1409004000344100720001074408581c07144c0c0403a80100c80c500640c0c030030000d5214030020b035000e001d180707050309400c0f000c0400765400c098030000b1008205840c0a07845504101d299a80f079068 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 989439739 1250 989438489 989438531
    0xc100e060304020d030c051c082d10032f31022205010306060228080c070b090f0d0506061905220c030e0a110d0606090c0201 55
    0x801010645552150340c200a01c0b03c0028504a050041d09044500420000d01c04500c0d03110844c1301c03030108001e0440d8000c00710702000745a0780b540114401c0b9281c0a038101d00595020030000c01c0381186030b4603685506440402c090303100518241d252448808008190340100e4000a030014130500c145406500308000840114440315200b041e4400000303111002c0c828075540101c50ba170005241c0350581815202ca04801082c172000038001030020852941e1601c03610000f4600c03840074201f8504654014070301804240c003c038481103a0700307070000240580d00d801c40d1040016002103c2c0d1a95840402c60074a822111095110b400108194500c03400c0c1100b00c03003240340e404400750104e603855104001c2440d8424240c94014501408081a0744d10340c110454101041c0c88451541050207600c00820740340140040410541000c0c110000e0700f00008030740401ea0f074021505090b0015640c0400d5001401035009040b040c03d1402c001110205540305c0b0300444440d6000303102c0d02015103003030004080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 989440989 1250 989439739 989439767
    0xb0f12070903050d031808030c0702030616141b03120115020109080714070302031b13060f0303142203060c14090613080a06020a1107080d050a1e020c10 67
    0xc091309101e0058401e901007420303c014a202007440c080c054440c1e5003c3c0d0401c42d1076800c1a00009000000c1d49000c0210540c841304040a100c095002d254000386071106907201a0149403001c03440500e1000d001da4640082032a000444c8d84842d180c0d15032101611084c401d10322010799641001c0180e51042c000d2070081038004500c6071801d20349958004403032280c0c135004280b45c021994040b005179014072203040d407500354184044000c07149404118080200e40c0102034060f140200421a03080e015440300d049a4060a29110352b015030020450301d0f1140801c0a01c44020040f10b540e42c4d00130b104080e409881c040c5c1403c00c20304051074170070303500c04954640e8040c420308140710045a0f403030030b407008051700011001078921032580c41002d81d180507060b00d02151829000f25411109590144004a034010319000500b031861802e464942c40f81803407442001004000900d401c0142d000c1c024400d000d07501955182075a10903010000e458111140c0780512403007190302c0715208184070b17401e002e107005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 989442239 1250 989440989 989440993
    0x80c0d0f140a11010e060c1806040f051c330506030705061e0f0d140705030a0504170304060504170a020705060304171309050106030e0c01180b0f1207090305 69
    0x42404001c0d5070114290b1950710f980e40d29070444450040c03042c07103413138001c0711035603641a191814006440c0100d00c19103952402000248400c1140065421010040741c6080e94a800465044070704003024070b90104001d019210301d03015440c0000e0020644020030701c0c01101010380c81000581c0082030320825550035a00da07002550a0002e464000010481c42c1c5444240c000310000d5080c0c894015002407803000d41d0b420b804502910306403201e00840c00d0942100c01401c121b40f0341001d0142c15404050040110303141e845000070304100c11600c80c0402c400c05001d2240d220300c0c25181040c06040220740465508400b141041030608441050b02c0300c907405078001d00441410482440b2103a000180203680701100c075000002440c2d96403004000324040714460588041c208251031084d54010b0340482c1c100741c40c203a4801982ca502051030300114000f40382001915510800c0300c8401f039103941041a803c003001500f412001e540320001c120402c8100324191281c1c0d102d620580d00001c2e103100141142e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 989443489 1250 989442239 989442247
    0x90703060807232e120c031e06050a0b03040503090d080c0f07061704050705091f08070b090f0f13020901090e103011031005270a080c0d0f14 62
    0x41c03030300c60410300c030004a03030f180c2418100d850804a4091b01d00c020001404203035252002080414071102880004a2401c01071100c581b9010201c8c3d4412881c0c80ac00d001e42c0750110103e010018203100300c42070307044008e160b0700c445c00f2241804d01056104845c4a0780320310403076072400e8844078080b444208858450700e0310841311040800c0000b2441c001001241e0324080e0346000714003641d0303420a55004881c00c0154a035402240e60b109003030764001d600040c095900c0341074200b011404600842b5034444051358180e0b0b4a4a504011401e6402c40c0100c041e03000b0000358490010621560241c8210f500c240d80fa07460305a42c4907101180c1360313025903000307000030b440003c00d02143c0c40070f001041d040e41444400c0140000703960502020b00c080424119545032480c40d40319407038a0704100b1204203540b903490410140c20b040450030340a1458080d01240f11074280241001c003101400000805038020868540d522500d107541611150b44860f50300c046140c1071010341407148142c070300d0690545200300700c0d0b1030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 989444739 1250 989443489 989443549
    0x100503062e050711030601080604051204180c050c1b030c06031603020307020a08120403080c03270a0c0b04092a03052203020708071508040209070306080723 69
    0x410340c840c0e00e040d40c6014082140c0b004e103880c10000540240b02440c0540300d40c1c1400e15100741095170140e504800141c09210502c0301e8400360101804510701407400003654810380d441640c0301c0c0611055140d49000d0804058840801da4168070103003601282610384111f4010f0400c91607020a071b540c480580325400440e00c0240c020350040da00120a401103861000c2d060340c5801f001d511420001082400f0281444205600200c0d07003070b00402007407503190951415074030303980314510003010025043e5144003001c404420305000408440340c1004d030b042445d6840300d801d51400c0d0711a1050040180c80c111558000f907901c102c140c50649004001c030004401c010b08100d001e080043e1038881c081c11200c0c6001c4840c004240940c400f18401c0e0040d01c10289043c83c076906290090f13100070b00d00441c80059521840d0300440c066030099040b55100e42540718110200c0040520f904403650340d1065407004140c900c0c0b000c00c034003c1d4121009400045c0d144041c1802203514024180310492911602d04441e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 989445989 1250 989444739 989444747
    0x8090402031b030112020f0f0112110f0408012403020105040314031c090c08030405060f031003021513090605130e1203070c02090603060f0601050f09100503062e 71
    0x5044150385038101e40000d460003080c40030f0350081c1e0014058660144007001141040560028056000c484101d501c29441002910071030085074020b40c3c03140d440e1141e062035040c2d00151900c1020320940c03207071a02d40ba0400c1500800d000043c150680c0c1e038850994600040c0c0c10382100580c0d034107960301410149035940713000881502d4140d803444ad00052208007500d03411140e0307914140c06030a0010a0900b03090600248501040c1c11210701074008200501a81d10f601c0d00f202c2c0a041c1c1c10b2501c1c2d98990302c180c0f07800d030441c681d900000d40c030001c0b401640c24040c8030350018003c4401003104a0192542d0b619660040b900c045c0300c1c0c540c112944c480c030f0070400c0e10326a109101150b068020f41b6942c586440460b65298011904080803808018410096090155009a100381c00b64001e20341420211a411142e49008003907504101000444100140f01282901c484c86400b510101212882c0100a0680c1d082100c50302e0280e200c902c0c0d2080c1d04003403141104c5d42620b01040c60300d02903601c104125 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 989447239 1250 989445989 989445991
    0x2060a03020705030f03011e59251d120708070e0603061611100c1413030b0c040506122205070501080a090b0f04030306050d0809040203 60
    0x220038107030300340100c10100c2d0090006140e290030209215540c2d43c1490143d000b50310100d0700c1d071034040d041c0c401c041c840380f40405661200003000300f4041c81040c140340c0b500908070320510a01040b086071404d80c031000314a16a40c580b13003074640345103114143d540c1071008402c95840340e035030160100d803a960755014103024000c064402454070307190280d104a08004201601d402990004c0950303c101002c20503902d007440404050216240c1104141c2072180c0000e41c0d548001e0701504d54041a407200451160085d10100200021201039641d16002820382a000f0b201904c080404514030413142c03807528440008442c00c0340e0200c1002040c46095450f501203880e4020f101c1c0912040c2040041001d51f207100c00b0b040389180003081070706140f41404440002c400c220b0040e40300040c080c100039000640100d440d405440080c44c1c0514155a5070503807070040d06181c1801f80c0a2120001408440184030540610481c080c0d2818821903580388240a20954414005440701c642440039044901e03003a0011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 989448489 1250 989447239 989447257
    0x10f020c0105130806150108090a030509060c0f0a050105090d0c0201020d0806010516110f090c04090506211b15090d02061b0a030e03010501060e0f280807090b0307030206 75
    0x1200c0c0c64803840420329205040c6c69036000f512480746605150341c3d00a0704e807a8403007001e1000c1c1030900030554010304107001c0d01420794401c0c98040307000840040100b0000c000c820a16040b0381c2c80f0450f504006000346419140b400040c0540c2c0300c490b441c54040c0c01c1840c141070b4181e00503d41036036500300884005070003810041c10041d0800c4809043c40c040c0d50042c84c080d00940380310001c91588010030000950b00a03119002d010300404216850348200103079822950308980c007192a6491000152211074610301002d01c0f8000b007841c80a00c0350f400203407060243c0e441004009100038031000c0288070b90382d0400201c0d5a000400005406007041802100700610151443e81441c0c400600e980c1100c0b41c240f201011170f0b10204001c010b0503807002d4105580d41c0141c00802c8103504203040104240c0c034005146005140401c0041c88940322102c0c1000401283d0400381140c05141102513100802d0b842140b406114501010034019004d11603401a1000100103060310f1b49541d082c80034030782007042c030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 989449739 1250 989448489 989448517
    0xb030f0f0406093f0f080a2d05090a0c090c0c02030303090105190207050a0204090201050d0e0c01030f0e0c0f06121303091d010e130c12060506010f020c0105 69
    0xe4007000410f41400c0204c0003400e0010200c00c10802031038100c042d400f0790040e0807024140010100c01d56082540070741c6a040c903150404440d550115000054200070300c80c60b51700040c1d901e2102400d5480d01c94000207064101081c1701640700e0281c56035844d540480003800060700702c01d040205c0d42165001d1041c0c650705040442440469400017821a001210000f042d65141c20030041d252404000d401411042e900c0118105007241d02d50f1695a031506400070300545d070700c11020f819a80101c0030341d8500f031642d48040c065008081d880039201c0b031705008050b01090501210300d00d0800c09015640b10f0381c003848020300d203020080080011250080100319004130b8100303d88029203104502480c0b10300e0304c0850420701d0821038a002088208036501c810104564901d100340411400503c080c1100c29020050525486003030702c603000a200024014146150404006841f90701d2502182c1514000d010030405552810b0045d948004c05040d10700058001800005143d80100040e05114055440c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 989450989 1250 989449739 989449751
    0x90c090307090e0a060b10080114011103072f0f06090f06040e01080d0306031109040204111305240f070318120c08070b040306021b0106060809070b030f0f0406 70
    0x8150007114015004901ea40e00840f044c1c0060100500505000d94000c0d51005511141d5410051510300c042c0986219135411070342004c56680705100341070b08503801c18140c03661206503140c200940c600d1380a4040c4505400d200f041740d00b00b00c0300d04021142c20081d218490450300300c1d041107a540e20080b5107580c09480841d00700d80f030b0340700d80001d00068100b000340504103504010f1564a4644c005060004043c2042d00074800903280e446200451401034480400d0340c0ca0314030001e80078000b6541c1452420f800800c0c012806440220018201c0b42d0030b035403400c3c80d4185e014020300716a80c40180b48002d1030341000a4910311034a080205174240c068900300c28103c0001006524038291076002c000c9080c81024944180400f08025600410140b00200b020600d440c0343d01c6001d0095100161245902160021131280364101d1024040900380c020484641c4070040035200100940c1c60801c5031080e1040030990324020720489014985100e04d0a100f540d490417809c0c501c410080040f524162195 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 989452239 1250 989450989 989450999
    0x16050906130e01030506090c060d051003061506030f2711041b02010c0801140f04020c01060f060212070803130609020a0b03070f1b0209180703030c02011706090c090307 74
    0x400a04080c1c941c2169003041540341d800c103c0c0c46d0034405080c0e642284c00c01c1c0d8544601c4c0c0e5030a41155000141040041120303500c101c42e202400c046640040c01d4281007030340c1011301c01ca900d4100410b4a0590700c0c02c000c0e0024440401c01250000b01e016440351460381034840c1c001803a40690040c00d48500c0501c81c1c07801806001c00d007134440074400c07015500e102c0c10700c1c150a5502030144000b40d2040349802c004640c90140501010b00f4841200c500513844030102080c2900d0300c4d0121000d540e10003009003e1556160100c1100c4816407044000600951400060703107020441168040c13a08001c400c0c0c2152a080f03c18250040300c04000c5a078a503417850703d01c0040c0c4035140000300400d40040c0546e243c1c50403000141c205603141120904003e11581c8a04940d9108680e41250701c0e01a1084900e50743c50020446001040504200403403058103400010182c0c89485c03021030328030130b90304c0070b618240407004290307584801d40d807071584001d9650000320741c05010806001618002401c030b0701d41c20b80d28 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 989453489 1250 989452239 989452267
    0x1e0607120201060f05010804050d261302270c0d060801150303080a060602100b0303130b03010f061706010c03050405060f0301030516120b1b21060916050906 69
    0x300c10480c0250351141010403003810f60310b2000300100020f007403a68051900b03070303140b5880300884c5143c00144a000303241d5500d0100c075540405091a0550940941400c0044c41c0d1440714100e000d041b44030384240c80c00c0602c442101584201c2840c90003a00c1912616290030f4621f264212102918640342e0303a09001848040c00d002d152411a0a0705c8000f14450075420020400b541c000d00f81018a403c0900820507190300040e0184640510180014101c5074580024194450510b50581c005014940419019001d0740250304a911385c0c101e0b10303555990b83d642910101c1d90010320008100f125400100d0035402210400c030403034400e10b0a170b45481d4645002610311341080784410600c0d1400301c010700170450100108255400d0008082d15114230f805810562881445002400c60700483c0120b4070b03801104121880700c102400340c072a204c44c0c00d60305181d0000843c42d01c88507440c0c40354001c603c1c4ca08011181d103005200e112420003803132134a00760a58060b0301004410303801c41410040324480f0303007031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 989454739 1250 989453489 989453513
    0x1092d200d1511090d08030a020d092a0509040b2703090102162907020d0602180904032015070201020c0708030306010c0b1306111e04051e0607 63
    0x2080c48803180c24403040b00040201c5600840c0a50750120401109441d640d5039141c2c0c0740d0b5158005040c0d550388c0d80700381110029028071020050f0107414550f99a0130001c0e443c0500d2801c2003d003122100f4860003210000f0004118400c094000754450082000b044814070080c0d40070601c01c03071103051842d1001d00303d100c42c020350146041e0b50b003001c07551000541e410f0161001c4903a00b0010800c00c0c60401504800f031005e1640b2000c40d0030302107042411084120015140459001403560403040110300744000030b540405060b12040f515138601c00b05619200d5074450007103415036144503040c2000240c80103401c0c0c0245801e25980310f80328015043c43e801d882401d11408041d8005030311050b4202d0b07290702d041404e400c0344106c3d0700b00380100119a68020200c050980d0049255802c0d03481c3d5544104000c0e69208015195a0600c0130b0700c150216058010409666140201042c2e603c20490a403001e0207107024541d4060f962104a8505000c52102510402002440301c5d2421000755107401042c04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 989455989 1250 989454739 989454743
    0x608070813030f11100606020705120304120326060f0603090a030e0303040f0b0d061725050301090b06030d0f02060609151011060606030c0703210e01092d200d 70
    0x70b1211b1051280c40d80c1848001c000707003c25a0080d0030f20642c0f4090300d489004038050034030480e0200c940c840600d4801d405140c07619545580d8046030724001a0030440c800e0044074580d000c0c1d4030a607050741890401d0022a80728004410141041620740d941c2260312011030b00d5450351500c410320000c00c90a120311440c50041c0040c101a03039a0340c4c0074070020f400380c1d02280d104c04811608010b1200c846030300410185550b04c0c0d02200c541007211128650104440913801550301503203400000000c103d074800034140180003c80440c4d80c41c0030303258011610804090303015001078006c04003281080c10041c000907003014286001d004160510300105501c1c0005107609400940010300300c0a003810244602908400d0a071141455441c00c40307087e26842c810500002d00300821012500f05003c400c0e01044041866020140504030040407524007030800c6240a8480429507902c400c040d080300084036200c01004405101c10038019210030000610106090240c60411400145aa0b0b103101c81021914 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 989457239 1250 989455989 989455991
    0x60c0b1807090f050708041a0c0421060f1a041a0607080d0c1b0f030201060503010218090c13051203040503010516021606020318030109080c070608070813030f1110 72
    0x11104900101c240d8130054411024031811300144030205a65407078840c0464808071103200c5d20380b18244640f0780f510460340b100801009095000c0440302d42042c14020460103200309002c1b01d2407010042c0d0894084080c2c1d0741160104411595a6080a0300400d9805d000c403c1c80f40746510035400429110791003c80704442c2030100051101c842e011a124456002c0300d28a007034020244100d40400d070808108001030440d03001d1440c9102014401d42050014280c064000d43d201c1381c0111241c00c8506010150741d03c02e1942c000021640c01d6a130080ea80f42c601c90141944009103400c3c140a40483c20350b0b00502c3c20700003000082059102409100d000e44162041c3d0107a1503420140241010400800740c11011001c0c01c040014642c00000c3e82d0f196042d0320080c01c0340140030030020303004028003040100f038117201140b10381400c0380c08500c1c1c0085405a8481144982e10f10204a1308050121190403001210001c0040401d1240700007040c50310701c5061075508203c51941040c6420607001e0759038846 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 989458489 1250 989457239 989457251
    0x1060803070318031106031546060e1906051213020d0615030c0803030115020f0307060f0b06071b090207030503060f06130806060103050c04060c0b180709 68
    0x550b00c2210f00344400199002d112406085949000c0d03400d62011140e4800c90010012440e80d10036840310400c0000000c1404144031052101b20103a10706010714070345841c01a64814040180c0c2e845800a00042c4a40a4485a041c014150341050300d101100350801c2814480038140e01c00c903075540015109945a081e00c420320110700d040700c40d400a20035010706940c00400c900507110300c2070701e000466005c0008900c1406019121014204c1680094481844c55500141403070b4044015410b80b05107c40c031203203c080c03c00050f070b61035916081c110311a50081080c8000f02d041a4044411b00e12004d00c08614485040700203182900b140105039001d13a40c8640c1c03180c0f8000301003071802c014244003406505101554a0103041c5003c0188043e00403600c05d21202d0a42e5908811210729003c4040030a0243d0340f00e00507039039510801c580443c0800c3c6000007085035841d09038142c9003281c04943d50500f01c04159556041c00e1040501195a030054096094508420500c0403401403ca190030000c0c0c0c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 989459739 1250 989458489 989458493
    0x50408071517070e0f010504150e030313060c0b0a0c021f0612030e04052413060302090f04030e090c1920010b04060b030f04140c04053c0105040c090302030106080307 73
    0x441764519142c1c5040c82400c000070407500f1381c0c041e03004100c0b10440c02c00c1401b04107000c01081c154400c01e5005007566074907a902280258000405001503030042c08000829035810f04100104e409885255015038096006903008420807089080310541101022039000c0d036820840781c0482a8030000c41c0410a01c081d1341000c0d06151180036440345011417914a8030082c15032168a0400318116240034194144a03507040500300d4020783e006503805481803a491038040740c09610304600b074608138000750124100d00443d1a018080720700801907440000c0c41d20315220501c0d030201083c5141c1105000124200030040c94200c0b140781c6c0301135240c00000c00c079140c10780304110460740103402555042d4000c0c070910407201d15005510741d04c83c0d40441135013011105004c1b03131881c149071940c2080e80b00b4184010809016009400116010a00b881c0181406143c0c644d40d0200318030314401c1c0c0d02405410004001515084d00b1148608400e410441444d5171650003007030a445c11a00301c00a242c1c000524001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 989460989 1250 989459739 989459749
    0xc0605030a0e28061401030b0f07110303061c0510050a0e0307050312070212040f03020103050612060406111606020a08090d02060c0702150a020106090c050408071517070e 75
    0x203204040a8054043d54243c0703142d40d0714441c4083c030000e103c059208003c0c8100484e5600c100510b0100e61350b100e6542d030f900e16050007520005c40b28124013001c231001080405024203003c0f812188400095800d55650005012a4074880303441001010002c92800010801c00d000005200074060b00119003850181910f10030360300581900c039043d0340100504c4012030404402c1c0c400c034500c102d181d820140c6910100f04e140008078200030009507070021b000560000350b00090b80440e4400e1700c0500c060b98480c420030500342e00a800e00c03589a0054000100007030140e0340720210210f0700907441800d20040303201000442048120856030203a0003c4e05096054000300d003540c1c0048148001c19845104007802911030b40c02800c01c02c1181380206584007156900c60390070102107102c00295450341c400e040c000740039060500c0f031801c566240688400500b4481c40454065652400040c0001072070180300d10348801c41503040300200071216082c5403100251107075041c0100b25954a040000d01c225003008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 989462239 1250 989460989 989461001
    0x30a0b190506030c070309080f030d110403080702040926182416080f09131503170f0a021c030903080105040e0109080a02070e1311090c070c0605030a 66
    0x28001581501080190355031000c4962084c41e10301901d445406510f819129419503801405140c043c02c0e004c19155640040a4803c0e008080001e00005007060b140c80660721070303400b020f4001901000621301608040e08440d54a9110b44441d00c409445801244040700d882e20b420041c007580000e5446c0c070f01541e4030203a45a400b044414500e2060340100260400e1001a0303283c0c2c242d600824140c03000360850400d420815084035940b550340d0380820084000381c1c841c2d141c052140040d07000203134005e25240704161341042e0b00c0c003030a003841e803c6483c0c110308080c0c1d070300c1a50040c07a003c1101c0464540c5060241101250747e400410801d49041064000085056001005c061506000401180e80090300b10f0440750181c0c1c00156050411034514054000014040c080602c000354141c20b031580024034100b01c0d4800e504c220fa65441d100c103480301d100e00c420030280c10440759890f11035a42c5404494190020014101185030551580c3e5440c6242842d81c0405c011a1021041105500c1c55004103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 989463489 1250 989462239 989462269
    0x20a0615091401120210020c0d0b0a0e0601080d03090204021c0e0d02060708070c031b030809071410030209180c040510020f12030601090902030c0702100504081f02070206030a0b 78
    0x40b20640c106944402581901d00000c0d1203850440b0032483d40ca8024441002c040f04040c02002c19044503050160202100b80c480d80c00b00c502d010020f002107500441d626041c1e411000141a2001884e4400c03805462010b1040e40d225600b0091030311294041854144441500e0070082041000c040c6003600740a198a02d840540d0030150801604541c40010a54450a00d04014010380480c0c10304171980c0351040c0d0b00d0440d501044180310b003030540011890b480368081a00f20380e40140c4808034030098a211001407a0410b0b01020480d2000b40241c01800c0801c9014210b8a40403611f40d0070002d490b01c01b9140c00b441c0000000d000e0101b030a260101c03131071032013290000b0003090701d800403c0c1d82e44682190320000c0711800800802e40c582e2107000764000500080c2015134403400c0c4000312540c66402100100c0c803801e0366001e2518043e011b642901c082325101c030040e000d0314114200c4882500d140218400015908009003801a5602c0014601071448541c0005007079407501e06021206440c1005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 989464739 1250 989463489 989463521
    0x70f0b0601082a0f031807060c0201050f090103090c170d050405030307200406080f07050a0b03070f120c12150503030703031a04050f10060e0a050d03020a061509 71
    0x700701c1c6852000200c442c408020140c004040103918000c640079004c0e498400046050010034441c84101c030402003500c00d00c2110680b01c03000e80d244401d445040c0e0381403000b8081501480503040c0540444080e001448060401080701d60280d5107501d003940c0207810903e19105c80b0070121941502c03c00c80c1a150880d14180f05113054103003030001e541c90065200044c8400178240e1030706030a0f411004800c444186c050300074803e00b0788541f403041e210f4403008003c4c90070f44140b1500141134944200d500c000c613012000b0381840c2d0707280e5940c2101c9030f00c0d0b841110f07014450358110b54149420144140b4a140041c2c0d940c52400c2c1c048da4000300d09950030502d0380030340007000e40d609100a65012089480c81d5606060000e80e40c0b201c0030304035204030f80e00d4610581c814a080c0401c43c0301504042124801c0820440d0004003035103030b00c01600c04500c041902074001085a10a001d90f090201328400d0700c50090040304c0c0e40140e6680d882c030640c0c001d5001e0170000031240e80c0401808c4020b028a900b24152412 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 989465989 1250 989464739 989464741
    0x1f032003060112080a0e150901082202121f0c02010e120301050d140a0b011805070c14160b0408190510020f0c03030109051005030a0201081911070f0b060108 69
    0x1d07500f20448402d54003c0c3c0014070004a044900d4003540e540d10b4111000b510580041c21210f401c3c44079504400019408201180005049840100b01c0c890540313840c1d5414990408041d001d0001c55150f00ca00d8840500c43c025200440303089000c000d00ca41480d0381d0001c15041780c800c000a0030b44401620302003882c0e201900740f07a0141c1c00321007507030b05498090315100300042c95410488811102003281c0074040c0100c0400302d0501c20100122810b0340c0d0b0300621510000d2446d5051400c4800840d50342000501d2015601c0c00250600c0016801050030412140040601480c5210403035040d40310380c41d1038130006001c024464082c07100000000340d101c4000045d0203652201e80e20360006600e102d0302c4560025180a00c0c94101c3d040d64030a01c070180c1200e8407580c586401ca402003a00707a902ea00c00310040b40000405103800100054100da0694810001d07880309030141c0c0301000c440000310509502d40303514190404600001d089140d001c3c1d8014900c044140c2001d02c0b1021000d4155410484600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 989467239 1250 989465989 989465999
    0x60d0f0b070f0507031e09050a09020a08010509160f0c06140f010503030c060a2f270319021c0b01090e030909040807020612040f021201060503151f0320030601 70
    0x400c0304c141c4100340c1c003800100380c911b00080b100c5007200c1e000345e90b006042c2c00d4049041082c030750241001001c0317600c865080b41d8072030703007007110600045039188003110601d00d000000c1403180000208881040c2060300c1c1030201341e070700d402c151103004086510804001d42005454410411200d004240680c055454000c030b040c4000e88658004204e80320f07207a2210310900400c802451030001c019201d2000320011b0b012480d03440300f1a8450039038003902c07450011040c02001450001e007505c2d10030080042c4441e0032b021600f100c4242402c1c4003a030344111814040d00b40c08aa407145125060321500500c90998100010a000c8840b810f0160034258000e0050709000d840789074115800c40d4001c0b0b4101d0f01c0d0381982c03000805520420240c200e00740c80302000d002c200810420484181442200c010061200c5010740508031000c0e80b0407103038594801890a00802d101c1c000142c1c001401003030005015079003641d01c505800c42c2d0b610449503242200c0c000c6400d551140030f44041c9400032806448907500d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 989468489 1250 989467239 989467247
    0x70e070504060e060903010510090f06060801030f0201090305070b0c061f030b1306020f07060e06060105160c0305030307080603071e05220510080705010201091703060d0f0b070f050703 81
    0xc1c0201014040c0c3c42d10201c0a0b40e40d0b2405881c10010000c0013400b0526140c8071001110400d84101e030718040c203240c19404208024082c0206841e12569148140da280d6102e140d070f1040c2200e8141d06218000001101180003845407078040d1403035026440e551000c0340d40052400c03200600c0341e00214104000c084101d6503690200d401c5075002210340d4604c0c0c90f6040d24056184000c04010403035840001c81e0030f418002c0c0d0000d0443c8a008440c00c010100c80e483c1c0858413440201e8003180000c074100401240f00720614240c141d400c1c00f43c80c0c0010083e45907a1501d00d180d10580300e41c800b1840381c808005040c917040000001406001400608900d258410b50341204460f0268a1141c0c0481959449040b5841c42d80e9100b924800414090f600700001042d00c10301041c05181074034041d001003c44c10b54014002d40c5240da911200748480001000c40140050300094600365000c1260510400464820f104000d1014021136203810b25003408080600494100c82c4650148981809040046071304 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 989469739 1250 989468489 989468497
    0x130203011503020304140109060c0906081e09031303051b0613060f360803040b090f010c0c140f0a050102100b0a05131a04020f0a050918010801020c070e0705 69
    0x542000f503225200d906c0d040f401c0203c00f040c05643c0e9841c006c801824007400c2c2c3c105d440000d4140d1968070302e80da144c0c002140d8807002211964008148611420030480504001c654024102ca060303038100301c40b003c014840301d01c843c1d2007031701d295100c18412180e190450840c40c11045048a51034030341080c0201601c1d20440600c260b00c2804511420200b10601070394804d80114080b809160803e00402c042c0c0340e107208000c8010000e0b508440c404544e0400c0001203405494a030700500341401352550401c003030301c04844005410800522182000100a106000c0151901c07040d03019a810356002400349129003010010322036051524100300598000c203440702814014500410164a03500100e01d011000d41e004540005030074409042948055002052215889810411604914042000382c0c01503000314801c4510030070040c0800c0e03000d080100301201000d0700aa2612611081200d0361242c240d2040b01281d40025a41c41c031907a0501401015041000440c2c80300c1c02c2000d802403480c00317 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 989470989 1250 989469739 989469779
    0xd360201080408070309030c030b3907020406080f0d030f0b010509040f09050d03020a020114040b18010b0d08040303080709061b052b0f0c0305180d05010903050913020301 75
    0x43e0015150f002e251040c5210805580c0040d4900c1c0703596600c0c64004c0b80321600300d039540d041c8102041010106010b6016110400d584a81030729143c039100c40e4002d241d84c0c4201c2049034400e694603000284583c003800000341780002e0b44090140d200c1e640c030020b000d40c3c2c10507a416038a5880c000a800c21a038210041e500c0b444c0040d140000c00b4100c00c0013000c0100070b03064000e0000d201c1c90158603e071725455001001840d80070b500a00c80c0c44404181040c40807010f4600030b100c00702d40d0000403a41e11255426800f05e03003150002003401c0f402c007070201d09680048002a01e042c2c100003400d000741608210300d07507002401071801c05900b501d040707030050905504000150b14a5074408040d02488410419044000344914240d0810180205a8101c110401400d038002c40c039a8a030b4502d4450140c2843c0c8081501520b40034900545c00104840395420030304d00341da11a00d1340b0160700c08501e09228a4111034802e0b101d06d5a00c1042c001084081c0b000803845044050041006008601062412814401d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 989472239 1250 989470989 989471003
    0xf11150a021023090d200c0103180b01141f0f1b02061305090106170408130e04030c1e1e0206040b1903180221030d3602010804 56
    0x8028000743c200d00e0000030410b0740141c050401401403000002c036001014200b251100445004031100500d208581401c46040c550040f1400c1071842d40a41c2002084d50951001444039103406d40d94412110070a030000440f424894a201e881418000b005104450b41c8a06a40c00603c1380100286001c03000200d1508200c000d000c140c030340c5241010100d40c22a801800180ca40c08103000854000031140f080c10700c40c00880c8000900c0c180100d5a001161003544101151682d40361100a0031364082c083e4122041601000050714040b9450100c0c002c44c4640e4440c4154852820034501070500d00000b0701d80c00c099410ba04d400501014051a82244bc040c4da00d049440c01d4000902280030343e502400320307410005404600c2c0c0400314010910ad180ca80c50400500d003410001140740d0507610b0000b50409070001d01c070301224541102010035030268200f20391410600301840001d840e480000941c45c0301c42c80114110040800c4440400e5103103070891801404030640000b00340000161000e0008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 989473489 1250 989472239 989472251
    0x304110d0204110a0c060c090f0b0f0405090a020310170a0f060e010203010803070605010801050609060d150f0b0f100504150527031603050c0f0d0f11150a0210 70
    0x6449070f4119074841403401030f5694980140f041c2c0a4203074500b4110840e65549400140040c0c2030103404c140c01946d00003400290510f0400c0c0d00321185900071032401c16807c10900c00002c00750b68600205100c0c11f01c80c0e2001d0f883e8103040c4203803254400030b1b4108d100d00319076411710004440301c000384c0010320726002021240b44070001e08124000b40501950f112a5500010021030b00010010041080c46e10407582000b2580c0e0303840145089903019500203910200d4000481e8240c40c01c10280d01080e07001d40d40c91903041207a08011000c42d05450601c444040d100c0c032003164a4601080003e800200c156204007008201c140000e0140c441e0380100780c0302e10440060030b205d540c8120300b581c41e1a61014005190035000d00148803080c540c0d40c440510a1181228004a410000207c181200e40c400014801041c8640030042c8484c182104c103a0040c089000c4c2401103001585151009401f4000304071051503c0403d1022103409008401c002c54030400c0b0500c28a0b1303000603512250345440c5000a10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 989474739 1250 989473489 989473493
    0xb03042f182a090901060e0a0b0906070303020a0e0a03110a09020c03030402010f17090303103f06090b0a0b031c03051b030907050a05030c010518120f0a030e060304110d 74
    0x30f0b0141c0c0e02c000c0c0d00200c0c180000300312244c10241d0803050b83c000b103c0990460b540c441d405205031190250b0039030440018408100001d01076009001807040a0500c50110070079140031514581c0382d540b003a00d0340f6158004d2480681030200011000e410780e16005c0d0714080300781c20320369aa0321010700020f0410020b00c00b080c202500c112401c80b00d000400004015908101306415640d4000b6104d1464005959100061313404500060600140310303d49032050010054600f40381c180b40132600c4540c100d0080c207500c00020460300c2101001c3d44954081c8070b550800035030301004c07107088182171030282c0d0000c03032032002d11107902252000252051401144036a9500c10001c41840030000c04440d02401105128840c2d50100b43c0740c0a444080e6182030003203135200c04043e07035500429a07050124904000003000301420a9000b085420090004c1e008003e500080c9403504689a0360f460440c1c204110100402d58440300f40c0c1c14003442103170301c1030560030682c5030865000544a04280310700140149001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 989475989 1250 989474739 989474821
    0x30f0c14090f0d3f0806010305070909090503071b0f090c120905100506220b030712031205010909121d2d0a0308040b03042f18 56
    0x2400740d1380304500100724079000101c50241c10360031115010300c010141940d0040340c0038401c86400300c2603a81d180000b03622400010740c0281000740a040420806e0100444d000310f19004560816116000440e0f54803d0f03030070305443c0648106004203100d0748481081100d00054a03840055841b041d00015603226099410340d0b034000106040800c40781030420200c1400320208060303041c100411006c0c0040ea4840d001c014900c42c01c481103035013042c0342450b062080046944102c402c42c4001d021110119201c0920a5901c415450300318005942c2c0303902803603410700600640f40107026441040c8441e020303503512451750f17158000421040158012010007111184000c541403c0c00203000c10200d03280a0074002c0d40f500d5849070311400008100880b20480c2030000c03000c000c498000c8052400e080c1130070305000607a032000d041507400b050851b081003d19071403da59003c0e9409848103d140703400e036071800c9c001101c0300807060706142e034100000c011903003100c001c419003031240c802c0381c03d0903062140038a88 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 989477239 1250 989475989 989476009
    0x5220603120309050d0c021302090f09010f0f0f06170702010b09040803070e2d03030d020a0203030a050a0b010c080d0207060e0d0215150f011e030f0c14090f 69
    0x5000700450201038001250503520441100740a2020f0742d41e100c03851102600c12084854000303400000201c41c100e080c000390740c0604a030320030052906683c50080800a040c0306e000382c002490451041400700301034a6610400713801814148440075040340360000c00b42042d2140f000c68022140e10100284040b8401e42c00380f200c20800503d075002900f01414007c1003500210360740008102c18a4410800746452051611040c2000616909901e8003c484400c105010b074036040e01844103100e0304402114500160180e10410b900440c1c4030b1400034018405e58901609040d1040c0c0390082c0e403c1e00380d0740320201d60380d00b5030841401c66580840d1b0268a000788290040903140e140b074240042a50b40c0c02042110414035079030300312030202c1c0d10003503e00301e0040283c0e906448407406410340c1e00181400c0c40d0206c02c8202c1410480d826a2441080303541d5142c0d0400e507040026547c0c8031003030a481a510544080d12074500c2c008054400188200e60785200302802648550b14410306020760b80da1f030340041307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 989478489 1250 989477239 989477243
    0xc010206131b241814060a05040308030c090103051006120507020f1209101e0c150c0f0215010b09040f11130303141c0504051e0307020a0801050105220603 68
    0x19419410851100281c0500d04400c0c450001e02c0840044c16504501e00d0f694040d00d42040f072084208424004002c00c0d984038488070702c1404001c2c0710000120b5a004081c41c86201c50441981e5210346000004081b188010b0070103d048201c00c50600c0030944c802c203204130b034610b02a000202d17a11080302c16071030280e44060040b100d2041d1484007000e58042d6002c1e03c24910103035008015410743e030b04140d43c0b18060344120040c24a2098480315440d1061446541c1d0b0390245128038bc500c40d980301405c06845021103840c01080200701c03030030b90840d13040044088002450207055842d5040007482016841001041d42c4595100d10514540710031981c4146025502a540d1590302c0000311458004982d2a200641c089441911210b900c90f02e03c40c04c64001550702c0d2801180700c04540184d01c000d20020f40b06507001c1c4500082d0303190015030004c040a081580750000c0d41c50702400d1041000301100e0fa0424001d0741d0400b8010001503c40c60380c6600200da14196440f0001e028042100003001561301c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 989479739 1250 989478489 989478509
    0x5040c0c0308270a051204080a0b0a060b030114090a09020105030115050d06090605031006030b040b040618060f0b011803121103180109090b01210b03010f0e0c010206131b 75
    0x100340c14a60b0001085814540b20340103446d204940040051002d02031441030412640000c0c2c00000001c0b0303882c05555101443c2030300040e0387da441e603a2a0a2541003600001c01c002c0c3e490085440070310380030040720b40c0301d4981c1d0010301007000b241d0b0008005000600c16404400f5001c2070442103103015205882d100501e012007080010780d01c03110100501301740d114a6000780a085103840481010740240c030240c90300180708042d1501e6030390300c000d170450340284151841d40d40d610400d02c01195002c50000343e103028030b0005c558004002c0303040e011103032845052414400c00d0340f8418440d80c08800c2d640c084a401281000c042102c040701518108400c40082040e40400078003180441c40e014941c01d01e126081c1d03079900c0e400d40c40d48090000c8402c80d03c495808038801902c0c030041c0c410440c800060942d100403001ca6528800c2011034296066501440d01c520b80791100b40c880e14004010302a07000509100030801814086614801502c0015014224404103010302140c3c0081c078483c60300a040d4012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 989480989 1250 989479739 989479801
    0x130305010e011b021207150204150c03030f0e060408031b030a0911120c040b1c2901030b01090f2d0e0c01050a120b06070b1005040c0c0308 61
    0x140706030082a03000000c0711000044444000c10600c0004c1d50034009070b421440900e8103145844901c0e410700f413100f880b2a01502080b0104100100448040b0143c060b0f4840d600400110b2502505880704030342c003d841a4036200ca011203043c0f00040310764000b9006078120359a07032900142c219100c2e40402803181c2002c40041400ba6143c01c640c048040d2078042d0f034400503644c45800400c00c0c50300ca128040c520b958844845070712645415400003080120040c040382850364a80880000d01d245240295071b00751041b280d10301126486802002d500c420030f00780c0c2d025581940d4414880c40b20600582c1d01d61790341c3c0c10121390003070307800d44c420145072000c80000c3c508803996006c034000211f4a001440c1d0500c0c00e10920f0501e008002582810000307050b110a8240800c075201210503004603100301c80c01940302c104c8d00d8080d4a88500070b1a403035018507141100c40c03905500c0421070175880e40c04540a18a8641088060381e4443c00956190341d25107401d8840d500c440c295a200c590070845c42c20b0079500202 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 989482239 1250 989480989 989481011
    0xb1b030421050f03060405060a09110c07090603080a0c0309030204050f1602210702210a1e050705010e030109060f0c030b120606270a0f05012913030501 67
    0x300203a2840508025040c1e01d04001400c0300d0b00e0140150b4204540c0041c0089021440e294001c25400f00c40941041805940c84100f00d00707580d203c20108451030800148040050f80c1030203010050010984180441072856880c1406407186545841c20040041034100826100d81000c0b002590001d1043c000c50030306984194003414191101e1441d141e81511040d0403600100d0000000100c44103050039600c1001d41d0b40140d60322242c4103e074021920003c40110f124088011499003034003000500194140b442e001101042561302030f44120790840454001803000200001076550a00c0c100d03114406c8000444d01404070724000800050904504000e081010340c071039058200c2c543d8050100e0b610400501c00d40d14180007207800150440400100c160800c0303080c0c060790000d240301014042003400c20181d811b00044c0d8400c0740c00764031420540c03842e81450003103601421484880349640303203884081240c2c41c21100c1d440700c012000862010206103107060b40c01e0007160480b000340183e40d100b03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 989483489 1250 989482239 989482253
    0x803030f0a05041a060f1809300913020307180504060302010c0b0709080f07030515010b071103010b041508011b0c080904060b04060f02010609180b1b0304 68
    0xc4403094981900440010301010142c01154000c41c1c000119040d8800038071807005459400404558020ba8a040d9030103158035184020f20fa407032441c0e100095282170448030a420325401d42007950b482d03030780506059903400c0064180032040402e485490b990300b400c80c003c80d20f4440e903140b00c108070034400f008101c15180c00c4440356010f0044d20a0095400703445c1c404001c1119880d02010380060101075106000984c4408075942000c10307820b141d10496075441c02c1740d24240300e6001c005001d42080c40d0410401c0310401014411a0080408001c550b0420780815404c1c020000050803105809000d1102601d0070340c400d00741550040c1090007600032078410307404038850510078024550b10708941c21550b9003900d15605440c0c0c020f5929051502c00c03e80341e4501d0f540150707004c00d6206a50b110001a0340c030140d00140000c20b41c5403540c0781c20103015a4040e0841d07403070b988154412410400d810700c05000702000035109561000e24003840d901d81020200400e424a000c401d1503003030000900051080b5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 989484739 1250 989483489 989483491
    0x2806020304080d0c020102040b040e04020607060603030504080105101d060a0308030106230306060f03090c060316030b100e0409030905030f0106081606120902030f060f06011409130b060c0106080303 87
    0xd00f200502055071304100403400c0f0b01c43c82c450341c0183c5606000038010044210545500f0600052203181003900686803a421150103a10440200c3c0e00011304000c000428001c03281d00c1f24a00c0002c00b8034520301600081c41040411052901c100b2000c00a140c070f60720720340e400c0080c40d00856815242e43c6c40c1c510140003035944074070211010481c4142d040d0444146011203210350000b030040e500b8125030bc40d14014540000d01031084034003540380034030125121032003e035201d40c080c183e0f2a400303440e18002c090211145c6912187c0a46280401c0b5503640e90843c90901d07900310180d40c001184040e41c2002c640381c8480da00560f80c14007840c000c240e80600150465002c1d00c0300e4105940c0700001d003900701030304940d0358440c9001082059000484002203584035081850010701641d85100007910150306222082300c1c002c03078130003c40341800240d580c080445003401e91803c12103450544804001100380041119000e417040e11903240b031244d91614401c0c2da41540e8104000e0040645a01c1e62544a400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 989485989 1250 989484739 989484757
    0x4150227120607360b0714060f071101021204021302040503070f090e0304140d0809184c0b0304080a030b46080f0c01020f280602030408 60
    0x7286216240c040711144240825030004804c41c1002646489068202030b08400000c0d91064242c0989004a40080c40030030300c80d0000c04146401442c109202a003180004c0702c8181c02d50388144007034035038100d51202c0150410380448541008108003d89040a0710490304150f8142c0030307541c000589907036204004001c0e101c50180c184503805020540940d207000f81d01c5802c0c45400301d90301446d80c41c01c0c402881e5185a000b04c4006240100320360204032407185104000740f1252840007003261982007000005005482002100000e541c8086640405803c01d011003100302e041110016844250780c40c03800080c840044602d40782c4c986801e20624a8009070106d1003c0380c100a016540d600d0403004d0030181842030000d42c45882c03001c412a080c03214401c0c140307038041361501e540000c0c0c080020790404014003071360008291002c1603980342c0e81015084101c1c607041d0360040621400d040d00200d81d00c200d020700403a2019140131240c2d001080303008900740140109100005100610800b5401848640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 989487239 1250 989485989 989486027
    0x11040e0108011103060108180102480307031805040c111605010504171024050d080702100c0b0f06090907050901061206030203100504150227120607 65
    0x160860380c5843d075074072080314920b00098414001a1500340510040140c13045084001410488005803001c0303d000310031711040300c0302c248064004000f0080e9915203181410303c44401d8000b4a00110745a803805148002011312665000a04520203803628000041c2402801400344251120b000303055000d10900d81d1050b4042d04840c1c0c258060f540381600201c3d01c0c180e465904c3d052030860b07014460820143e00b48014001d904c20520800e85078003c0002001c032210401c0c084191a4884808080041d0b000b00c1c080c6114080c410042002401074400058040e101d4107240e1400120840c0ca24014500051862024200303002840c00f0003520f0a1240038165121a42910340502159a46030284600341d44010120014024a48180761032000103a1050001c1421034607980000e003407160306501404541e5840c800c10003031040b0310085600c440c010380390440c5040c01d0780016034494000309514218004a41301025065120b0080d1001302d42201c0099440a041501005100340d11450b6915165 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 989488489 1250 989487239 989487251
    0x30e070b040f090203160f0516051c030e0604060b0102030408060709030b070516150905060a0c02120c030a0507110d0f020310150512030f0a0e0411070f021311040e010801 75
    0x5100c920172a03018034a420142c0c410020260811138548008099281c10407900784000c0e910143c1e004020b0740018454800703844407641840840c121a50a12100000c26080c048007618102022030760399081034012001040500c034050040c0d14610582c1e00190082c071881e420000341687c00f00b400001d40c1e1003015041001c0d140c1410031243e60048810302da00b031408070840b10b00050844035114403000051880850b105896881e40360405204982402800740c8850421450503030510014641c5140e00b141d242c200f42481700c1c8190f8a01900e03c9042c18448001801ca05105100c0c1c10b00d120b941e80240400441001894400420080107030704902a20401c07a0640605003140a18018904014510010140703042c01300807084070f18018100719030000300110a4010764490051100400544408150381c00703030350a01040700e982901d0714880c40030900112000130103c0c009114980d404440d03404444c48181d00001c0145041042007091743d0001500144648440407c0c9040301c8040c2e00070411 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 989489739 1250 989488489 989488499
    0x30b010b0712031a0906120a03020c3604030e040504031808061b181f0e0109050907031a121f231f260109170a030e070b040f 55
    0xa482c41004c28140c041901d0700100c0785800e008080b29402040103040e50034114030000140e0400003040c50035001a04840c50340e0070141422004900046181c1804102e42603041008180111818207500490400c90010409140c4601d8103403000f940300800400c0300781450b14019080d1454070340f070081c0c2c8003040500050785070743c0800c010b03110306450022807003503031603000000103980d10198100c10303030901c241b840c0f0300c440e200c0c41440c008c1c4403000c18000c0390005406401400c0009034180f0f0354108080440c00307002da0740b150142d02e0341011050030f02180e0802003818113003016070241122600031120012041041000103061400301d0f076200182600940b0f641109800d9901e498184c50034000d020030300d0380d030610703a1141c0d2550250311100080007044009418030712454480d071110750078900324114040803003201c0100c1014100170300020030040251b9a540103020b00d452808914901c000f16034103d2540c02a00008030b00700700c54068420702d9413210301d208801e40260145802c0c040e5010408a1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 989490989 1250 989489739 989489741
    0xf090e18011505210a050102030c1b01110a111f0507320901050706060b030f0c0a0815063006010c051005060a03050d17060409020901031b030b010b071203 68
    0x41a2540540200001c4450302c8961034130400103072201042e84074140c01d0101040007840554020503001c03440d41e5858840b040708642d4000d9504282c1d001d0707454113001489180c0c500088a04281650800114031005130001c20300717006807441c40c06410a80d00010050001d4940d011034442e07000303a151110513042e0300d84204111120894201c2034580003c0c2038030984442640a0160100140741007850071849641c0d02c019510f0980c0208000f001c0401481241d4080040081d401080c00d01c0907410140d0000c0c0040c8607503000f4100e607070800c00c46641105980c607840201c0340d131080240040250160900d69045070030149480700b020210547c80850610342c45000411180c0360450000c0c4028264900310400500010380070365804001030034008001802030240450012003521004214a210380c000d034944000108218401da2512880c840103071b40301d00c051415250040c0301142461801090b07100e203a502130300050300030a10039000088051060005203c40313417044030048000300040100360 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 989492239 1250 989490989 989491031
    0x706050a0f06080a080705010209061308120a05070b0402012007080d02030306031c0201062705070302030c04030b0901140412270506030a09080d0c030605030313060f090e1801 77
    0x360706034104502e13180115050002820220f0700400006141686e04400508160b209440c0401c90086008042088a00602000380e9003881c0c0103e2500d8030403d450000c00510450318000c10103c201c1d4003113010f591061030002d003000c4850740c01c014000d00180d440350351603d02e4400d0308414440c205aa0701003d10110550b80507440141c01041c08008a00300481207040100d85441151f42e03894001642002d4021041705100301c58550980c04026880b40c2d0041d15802003036042414010801e1181c0e403034101d01158204c940202e2901b095445d007100c1180905440110040d094001406010a0080112118080c0c080d5501c03080c0c0c0106640f620f003801c14040b00325500362100b110f1810486810a24011036000c01a5000090b1072566030b6190350785d6400c540a5040d130507998072030030064150184a40307000340100720010740c18065005131181c8030324018001d4808000115061200090152040c08040c5c54845640c01e032a1038890086030710079102c0b2417440b0303541d13083c04003403540c0244450030b603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 989493489 1250 989492239 989492249
    0x912120711010e121213051f09051504060c080c0930071502120a08060310060b0d0c0c050604170d09030c0639121401032f150f0706050a0f06 62
    0x80c1c56a680c4030b09040a8090041c40d40343c68103502e881035000010b1090106002c04080cbe100081c2413400c00303080080c11110f00000300003e0141040602c5000000b6805446050500b290a400080c1043d213054000400c1d80700684543c00280c440048444404181c00003071301d800303100491341300d0744500040b03a0b500303000351400000800030402e40345051b120b0000540d10000107000c481003800c0f200c840504558099006d030070110404201c0074048034190007800c1110740d0303d180108090416840f03da071a0500600001d0000e103510000f4480491428195640b142c0c0001303082084803500d00f030250291207050412909549494040c100c14182e0380c0c071184080860041c05c2580001a03522020300c0004019081e061008913900209007040340d020340e8409450755081e0415075451482e02e000c158010711280c00181340109100d10040f00e10400103030442000321000345507404184400c074818030410445020041000450070244000d030340045e4081c01c512981000540b410103052012a406409a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 989494739 1250 989493489 989493493
    0x709180512070c0915051e151e09190621060311010c032c030601052d060d09050109140c01050702010c050106090509060912120711010e12121305 64
    0x205014620305584991203596007000e44041761a1a140000d203a00070080341029080d51650300e2401c54117050b00a03110880c1000012800e101e4503a01003000e03022690245456080e01241c20302c03c035078a11600e1310709510207d94691070300703031140f200503c0290302c4214103809520158100c26040d807030348905070869804c10250102004510011a40191820700c2641001101510180b03005810604403101207802c440c000c4c0448440c3c0140f6040c8401680300700e210300303100303005400f081c8215401404410300c0c0715480c0399a40b040100103816405440b1000c1107643c03615589004000e015030040300b02d18002c405416050311600ea406560b060300e210788a002034414021703100194003c1c0000b0340228440c9002244440e103881c403100448100b110b01400d903902542c28049003c1042c4800c00303201307860030001c51515502034541d400008001d4080000c0199088602003090030a41c040000988090207455017039000310070340480b030703004945070740c0741002c0e20342c0440d82841403001d00e0704400d540000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 989495989 1250 989494739 989494763
    0x2402010e0c06070f0201020705060301090b150903061f0305120406030b2e0c061503021201050402031207051006140a0902120103060b03070807060f0e2e02070918051207 74
    0x182d00812203130420402c03415482060070201d12035880402845c0a4559000002800c664030020420b01400c40c220915281c601040260b45a440c0802c249502c6089110725201401001100c18020602a07201038854002c41103060b03501080d041c01442220801c0e43e0510100b0601c40c1005890f05035a1600b59030000c03420011600001720007038854034036981c0c0c100f000c0384041030345581e41503c500052110941180c80d0041c411860840d030b2040c0c144be00d06008201c40c2ca481d03404240e8600d480c02c800c644401c4041450410014200300c42005c83c10343c8402440301580e120600c58400540400c0244148461903001c0743d016018403d81d8203654039a04110216461a2110401440c60070003441e09030184003030200e80d07040104001001012150743d15862150100d100911800391136207418070988044c0b03240601e0300031500780910304203505142000c01014100042e40f8140041c0d1000b004070741042e2910401030360355084185050300400c2954081088002c0200a52040207002014002e40b09 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 989497239 1250 989495989 989495993
    0x603110f031c020f070e04022404121103100911121509030f070305030f010902161523040b010b03070c080a0909141e1902132402010e0c0607 62
    0x119034041e50515900580d000001d4400740c0500740307005c03900801036030b6005600340021820108030402c41d0020341c00d02861001500d66946000344035600c1100420700554140e1402d01030a50011010b200005046880380c02020000d01c024092140007500c21544d800c055032014107000e40300022441a49000c0c0c8040188996007030311030030002d03020660a220600a041044013500001d1078034138042d4440548a250640058555460581121505074010700441c0d0710036400c655907402e02a44100300164004540d58807800412485030fa4220b0340540160041c1000c21480c01380c1c0c001d50180d0302082090380c82d41ea05d1002440155101000119004003200104d04090f000d0700810402e0714040f02c42c10b64881c00c40050b1420501c1c0c561510f0030600912075601c6514102042901281a002502d448c02034500519090041d42c454420b079000124803062186031000712014203030302110400d0110281100b841c0c0300070004200c10266103080c44034421420005801c60001c6c50080103036140c1303540e80e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 989498489 1250 989497239 989497273
    0x30f0c18040804030b0c030f010b0708070308041506090f1d0c0d060e0607051c0c12021e0408010e0706090317180a090f0b06040f1a1b010603110f03 65
    0x70820340d5803074401c3c0400310005100098690003806000641d40c2c6a0170b0100050081d10b00680c09075a8001c1c0c20402e40c40054188000e8400c1c1e1b80c0c00d4103001503da075036400d094000d480c0c01c0390b10b000c1282c94080c0121742e000f06039011014020404108020382c03000150041d8000c0c041d02a04002988038510340380c454a050b900340480c0600c14200030400042d100b580c103280440c02c0d2052404558045503030b200c0c008121405420941c001036041c080c01c18120005064404151565542c40380c002a02004c510029080181199403480b206503845540b00302c030b2802800c0324181545240910003000a003184076001403015650001095080d044800001c0e10550344501d442c40c3c0404841200d8414641c5c9021458004091a40c00031032040d14221079481110b0240302c40c1f6100740c0c0144001e03c000b0907844c00074000c0e01d00001e1041e03014860b0301003800503402010a040b2030f010308040c41003034142041d080700080300e1103940c4455040d005042003000f01e00e0754008254160b4004502c1003048151 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 989499739 1250 989498489 989498491
    0x410d030918021c20070b01061407152c0d030b150d0c121d010501080d020a022416020406050f0306070c140d0201060e01080106081b03012702030f0c18 66
    0x301e00c4001920b40c4c280c0d0480719243c1203000c099038400c1c245001040269040b8441900008150312001c0c600902e41c1e403402d515490b62070700e0300d6555640e0101c9010071503098800300768040e02d41c0404856040d104c0c0c5a66a101a0781c1003604c0060306001e4101200d00f41090700941146644030300b1410319a2564200b0003d05002955008000090355030000c560207a02c900b100b0b5a101200c141121100d12844a09403001a0300c05c13506a40303d0548019031a50110724103d20a50444140103401c2c824083c082d00c0e86001c0c0880c0240c200c0018619242c0012a441081304900c203440501c0115652420005903000d00070450f6015089600010111403040180085062049103072541500c6942a014500b4055450742c002503950382c0014001c20010809032401042e52800a011541c00c0a1a80f5100e00b0082c0032580b403003d8a1158902c00d540c00e42080c000114000120401182c06c0a00b40300e00744140c2005038000c6c000c02102c1d1101e28030110720481081c002826404002642c940301d41c402c413038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 989500989 1250 989499739 989499761
    0x3090c010c05280b0a0f1a10050d061a0a0e010206040803040803100305060a09061406031c09050409120809070f120212010203040f0c410d030918021c 66
    0x100000400001903400f0030098000c1120000c0014980c142c2401c00c000c03140001030f950340012241d91f600080340d81d965000d0515134800d14120780c582103524200e10183c0f10076040909000d080603034030307442514610064120841160340e0500c4003400d040069854980a03600130748202c0f410400200419041c400560704800b600132841c400c01e13079230b80340d250070303d0007e64004213102d485002403010b01c0010b0064001d540c10340a4002018182240081c1d95034603000c08207030043d0a46a0513402c07840c01400c1c010010f020103031040c4114086840c010003032042481c4003401145005010a0010100040b203e0aa03040b46500fa920755051501c0d120082101400403070b0310401d54080e90710380b034000b030026501980c071071404c0d445282c0041c900055000c0c11500310210051540d03840f110f580001e0038028841461400700d080300929010142e56040254806198101035582800b004240e403040c500d1007140d8401160144140c00b8070602d0301a88504180d980c0c0040c0c4038520702c20072240d16841401000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 989502239 1250 989500989 989501053
    0x1c09030216151d12100e012a0513030b06011d2103090d0614010509071209391203120c02030702130b040c030207050a0b070e031203090c010c05 63
    0x30800c800140e1007140c00c00aa11302d64001191161075a02c00d80a4246400c1c0e10100900c885507003000001002c0d000344820f40302041000301d103601490701032822241d485d0200165010395a8580c1030010035100207942d43c0740004e603056009d6042000c0400366200e010002440c550780c7d029180020f80d0310540e0000c00d440540010443c140003030b56119490413411f8824035010640b000180d00da9a00e0110590009000d0194a020464100d074410407038045440d102e2000540c0b0b0721981889004a40c000d18103e407426480007041140740e40100d8151440e01e9815103404480e51140744100000c070700e100e002004107917040303d80d03140c2c00c65075000240e0b07803020b070f1046a04200407500002d0021000340e1944003444c0c1c2d100c0d0400340074149401400021000c0b0b04007545090384076a10340703503528040700001d40bc11031540003090805201e0380a804c20124000c04540814100c0290740e02c01d07510a84403250740c0e114405624040d0350007204550403e903045805000424010b181503021144421182d140c10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 989503489 1250 989502239 989502287
    0x10e0f04032708070e041707050a0f0503030a0e07050d060f0e06131406040c09091a071107120803011a0c030d05161d0d0204021c0903021615 62
    0x14050120600c003002e140d020141c0c10380f4501003005040130b466400460103e03500c00204008589007104000c1e5502082c00310750341d40e40c21810310300d0070965600e80050640e000c5d60214018041c000002d103005815168040180c0c4010220312030352080d1501c503094001c1202e5018901041e00c5a200c002250040301d00424a030228000305400c042045507001130080004030358a0074810908018047c2543c16802014103080c1900c07108140c900902c0703590002c980b100d90745030410001440990300311003e101c014005040000014282d100f038041a0010791051110014410601e0121075003410780003a05940796909101c101386496017481820300c000582001404c0292104000800301c0421800d4006098108000c3ca486560f803d0244c0384200242e642c04050700e05c00211100c074100d881140c498901c2260b500c085800b03030060304a0942416400440c00d2240541500403c0b2402c0c8a40d00342e076403100f202c07a4500c02041d2180541c103980c000703054101c1c1c0d00d49e02403000800341d070740503410445e20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 989504739 1250 989503489 989503517
    0x1401050c0312090706080f01060c08071a0f06030c0607021020060907060e010c0507140a0902130305121908041103010207060e0d030b060f16020907030e15010e0f0403 73
    0x190482541c100c00d00d1352000008008850b0f00c5100c07a80c014407044005c1c1a0f65142490045c0001003815001d0540d0900103280c0702000a4071040380c015003983c0e4164a520b18007004101d2002408a5186010f8055084100142c2c64514221070322640d0050400400702500c42c407c030303294583d0f004d00d40c84c04451002c070704000d0442000124860304141004145080c00e0100040910b00c94034600340c180300d02ca428040000d280480c1180584208000e1004182d841500190011640c0d07402500d6103480050541c01c0400e00684a00651340202e0846130082d8141e2280c003494460401010005201050b21100c450700c240a03040e00135028124581030301c0c69500c0000c0c00ca901a040440300703155194454a142c450030f2100901141060a0410201c040140414824031481040d03040701c0b100000c2c24030842170000c1c0385042454000c2c0021001e89071542d4054000c040040c001c0210b0320a003c0242006010000c80c0f5040e20110320100260341c585c181c1190002c60f0141c422800c4c0800c500c0da01d01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 989505989 1250 989504739 989504767
    0x204050a3006020a032717090a140306090604020901120204060504051302010906090807030b0c0c01091505060a03150f0912030902090603031e0c011e060e0a061401050c03 75
    0x109942c0580c50050740d581d400f400c0030b01181d0801c0c2d08404400c03101c07150300d076081040d2802d9044454008541100b113014200024a203032060100e444c0d40001606404106209040205480002c00364120780d50354807910b840d1940ca120442c4c0c029480680e1900600ca13110301691024045440540041a0180c031030340020709a0741c080703e4180362070106140490542d0fa0102002c1d0081c030060401a03451070070300d500a92180d04d24000074000c2c8040c071000c24241140d00c0115a14040321034020002041180750860068400ba207100d20740d41e00749408507040d85001c15984048030343c04007010721188445107002010b0034510102117800740d51041e00e040400c402007000079544005175000210360382c81d4410001d010102402c041d020364420700201118010010f101c4021900c4646410748a851281459000d08029408100c05007042c1d200c80d81d0390039845e0042c03426100503036040071855482410b040111051880750710070040002044149650088000740380c1e1013040400e603450605d011781c40c01c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 989507239 1250 989505989 989506079
    0xc0301020a0509030c040c020616182445030b1b03040b181002070804050f06090a030215070614070f08010e06010e121c11010204050a 59
    0x5010a90010383d603d090324050140c2d409001d0200c500308040d025070480290b4400c00204100203014815120310201d030300420404017031021410038440100d40391800d0100710050302c06120a00450008000b06807400340d400c0d1b030700f0300164850080042c44c0c1d9917104146004440500300d906203181d8003015201e102c0d00c00a102850040000000500b02000b849101600180800a80020a10074000080d89070300d40150014041100d1049941d41101c2303076424541e030702c005a81c1c694400264030b8204036881c0040c0084400441d007020040c0c8427a400d00070780b4413910306213640c014a4900d090006113005040c0360004190500f486081c543c0903668141151009441040c0f80d240c4d0908000c5441d511500076180b10710f9a1800c0300465260010520641c68050300071170501c4141d02c1c4100481d1280e000106982c80c0e5070341141c0c00c6011030030100f0b40301c108209464000402c101041d01501505000316000c90340007405400365a86031010301003011800101080d042480030031542081c3d5401d0303041c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 989508489 1250 989507239 989507257
    0x8060d080408012c070b071205120f01060e0d080a081506040303120506150f0c030f1204020f0a14060304061113141009060516050d0f0306090209030c120c030102 71
    0x701034414034012020681300000140311456600000080c44541c81d954140c400d129031103019440b0b10700c08184140d0340b5008140040d11140d44040c1000b146410b8114000d04803002500c07040356101d008418003401c04801e0602070200001004544080c7e4804c1940310341c0f00d070601f60205c0c44c1020315800a0302c1030b440799000b40c2c002201d40c5d442d1441509030340f0500da04000111002c409820024141c0f8809000f410300c62002118007203000c0c2000030040c02103804403103900840c00d589540101d10f00800d00e00596040e80074183d0880318007070501745140914259080301640c210b000e00780108002043c0c1c401082112101e4460b0300804001411707001401c94800c03010a0844460f06004000c030300c10f050307280d00030b1150014000140c11142c111900200f650200c0c0342150351161703c2070003070100b02c64204005205105a400e90400e071a403100c0807031014400c6e542e040c032600d40c1d224100e5082c0e0284a00c02036140d000140c40f82403070b2a101401c00c04403440c000944450001410002c2c0c00c81e0400e80c03030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 989509739 1250 989508489 989508521
    0x1d0603060117040c03150905101a060c010204030b16030515090115020a050601060201270b060d0812010e0106030c02010506100e03070b220e0f06040209040f05040f05160608060d08040801 82
    0x451010010203000d030031009c0003482c00c2000100103002c8001442c4412581c1c0ca400744070b0025410307280c84e00a404807400b03140c00007101c1500303003030114051182c4419010500002450b1a002c1200c2d55509080343c08003480c000d010b640540d00307220f50802c1d242c000801800a5200c0c941d910304c0018400c2c041d007402000709800002c1c1e550700b0215111603120b0301101c01440c9800713840400e0009017030b0038900c0741c000ea0165117000c02c402d80ea1524104920880710104c03040300c008400014a40c0711074801074103803052940e0910181c2e040183c103a084e02e00a480f507551125040d0a0690f40502c2400170640707001e4000c0c00c6402c42a581e8040520642c407074528407050304800440702c9841d00007440740f5401000a149213074201c0c50001340401030342c940900707064821500001c044819039500e4001112000607e0810002824103281103100c490482d04100d406014032004021020f40b8481c0300012625940c4800020740e40b1340b03003005401d610b400401c41c6c649205000215583e802441a155008000d450b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 989510989 1250 989509739 989509751
    0xc06040c090c0807020a1b080114040201020c060405031009021513081e061b19180801091502030402060d1806110c030f07080c0d1d0603060117040c0315 67
    0x202803000e8070b445401c08414081070300c0034040b645a0005603e013007190000010b4001c0f04520903c0906800d0940c00742600f90b080c161100b402a804440c0d00340258400d0702141c100f02c003d04140140c0f40268440c2e00d5043d0000300d00207031183d446401c801c1d00c451009024520f00703052000c808070349411000801545503480542400900c104006240203801c45507481c5000d8500c0c00ca03180d44c0c079032006101c030120388a0f0a10018001c81108103440e213a00f0301c03586076440100201802485110000c1152004004111000034860010303c580b840e0700303030890780350b0b10f180694903100400b0b580003802c00c90300007031308004141140806200e15040c0c40d8401c02c44860f1039134141000c0703040c1c1d4a4120281320350182040035908c0c03488000100d079030403070201e00000c0d2110b0082c10b0840180c003402109241b140a44030744501c503290b006582c0110320000301e409088240e000b006010107808111081c502051a901c540c0d00c001c01203542d03040d40148500642d90011743c5980d58800000c03601c29826080e240c50b28 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 989512239 1250 989510989 989510999
    0xe040e010906021908131104090c080f010f1107080a20011514040b0306060f1518030d14030a0e031e1c090c050613270b041406040b01050c06040c 64
    0x45c1d4031a800c209002c994107001c10306a00c80d031308004030501c401845907a481503000104030301480028020050001500c2030f0030745201034076010b0058007035656080341c40c058a2444103c0413009684140313400461417810036814240035030342200120600002820301a8421003c040d09024400c1000344a0b112000e0702460040a007103510389103030700709120350b041c003503660403a450000d180b0ba40403000315450341082000202290f02715a051b0b00d4141008000a00c01444a22480035100d402c43c06904a424140410b001107a103030040d9010120300c600204080780d01d18a00703030086c6015080c00800d8900d00f0800611a8850351800b0f034030b20441c1000130910840310000c0055000d2034000c821010f01c41c51a05550303006002203107018a500c503000218120341d000c075110800308040d11040c611741880c0e03502410025030b161344040d00243c0031800c0c2a030520f03039814503004a20b070400381d0304880401c5407181010000949070000c803080c10400300380301950307642c041000498061802504101021400c00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 989513489 1250 989512239 989512247
    0xa172d010c180909020306071b0203062a1216110f0a06050c120a0c17182413020402190503061306150c032003280e040e0109060219 58
    0x26a00000d0351070310708904c00000d40c81c0401d0b01a0711103880e141001c98008003010b00c040c046d100c69000b0b5058071480d01008400100420125000302c9503034918120306401010140251282c0075a4001030a040f41c085120300344841d1920340980a60300b4485a0204546402490075550703070070350a01d641c000010201400038a120b880d4110321000c04180c80c182034041e1100c000305010b8804201d240e80c90700d42100440c0300e62150880c89082c4903140e515400c2c400185415081c51154400c85401084a444100410070751010781c800001d11603c03e0913a41c06440218903022184180c0c0c125408124112100703000106171a440143c9403100c039141d041c8001030142042c20346081074442031500c41d06000428038100c3c01084000740c2d00d0440e003051042d01e402c4603042040c078082001d5500c103040d60702c9189008005802005900048042400301d8a04500303403c40120a8040105102c01225009420680c001c084a42d9010001181c80e924550303401c812688004484002e26102308291250140c1c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 989514739 1250 989513489 989513537
    0x702120a02160f0b04060c1a190c02030703090506070f0803090a1a0105010212030406020418090311120d0f06051c0c06300906050c04050a172d010c 65
    0xa840108110f55043c100c0760362013441140108428003414a070f01e0010040403a0b01d01400301d04c1c809200b0000d04040401c900000155030000300700b9403c040001076070320b10020581c2c00d13042c0c00da5170391501e0b14903000070702a4a071300854003560980c42403c00040420602001035002d00420303c000d01c81c402e4242409440001c00000200750a070000004112a0303078001000420003048a442e10350f292180c2c6091002445282d10402d45c0e910610301d0404640400c0c0c0c04103c41900a8032241401c061000140b512800c601700c18122102d07040c01503405501c0280c0c0544401118038500180154455001584030320541206140c5420b07507079140402c0100030705800005195a05040700c85114210a001c4000c030000324100001c48a14942d80c0303003207c503800c0b140301d40d90045810041d43c20540b0348002d09038802c1c0541170051a50b103c00040c000e0329001500b14981145003c1e15a440c00503011001c85941411402c9541c200c411030b9501d200b4084c4a20311b2540d00c01d4039a0205c10040c0c2c0408030603106c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 989515989 1250 989514739 989514749
    0x1706030a06050a02120f18030423012304030c1d040825080c070614040308090a0306093503040f0c0b0f040f050105160605060102070915050a08011509050702120a0216 73
    0x8c240010410f410454588a9040a0003151140d0f050340307040c0101c40031301d243e41c070b16681d10f039011103601c0000c030090b0000e2054900820380780e041c10b600e0b40c0b54203a0b1540b094000c07404200041f4002008540d50b040a42807000c03610030207948001c0c5510300c006004000307840c207682a81c00000c22149601c4104548402000b941c2003503044c05250846400c518021440064034080e400244511140d5408030440c2c040c6030300910170880840541020340310340c071440c0304034015060b21541e03015054a0218a9543c1c8015404010f480c698071aa2210300104007001c04880700815400041601e848043c094030300c1141071a42c0d00e44861900c3c43c0c600080300c841d400179050010030807240340043c4c0041d4403010101d42040000c695510f9950040717240004551028122500d40364078050000c044003480004c50b101100d501503031540f600000da00700c42c0300160340a600130b450401000601d2a5401541d030080090041d1a5000304038050103003164840c0d110000186c01a090754403140c02c03088040b0028003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 989517239 1250 989515989 989515993
    0x11a030708070b1e1b070e160e04060905090a0303150b0904051902030109150f120b040303090f03030501050306070c0203101a030d0309031706030a06050a02120f18 72
    0xd2034016195210402801040c1c41054005084134001c43c0d40614403103c0408141c00e1170b540d608241c0040e1548076194400302d258003422200007a1039a80c00d8520340030301031104001004580203102582d19003031541d0b019400c1038464000051300c1da103a2151500c10240c5501404015265241c020200c0b800c0e074008155400201c00b0034000803402100b56100810141d50000340394441001e0828044002c081401d00140008004030322000280c1018084812010070240c2084d240c030528061001140074003040300d969158404041552010010b811902034200060344022644408030a419252010750200ea00c40004001c907003010040c0c160300114614103408112800c2d40040e844582604142071040d4070b410509a5041802102505007400241201d503904001704001d0040e00818001341c000c601d4002442d03549001303804c3d03680c0c410b80000b0040c00d0071407216038814000f0f220140021001950134000300c0340c880304c0030031064054484210350401c2d130300d032000383c2c40c011140c510310007182d035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 989518489 1250 989517239 989517253
    0x20030a0506013902041503050c030111031b0a11010609141e1504061710050603030a0905100903060f09110d08090d11030d050d05011203020a060f0b04020c011a03 71
    0x2044580b4007081d00071016a5400103c00e03001d00000340502040c2c20f44004a90402400104026000810900c410400d0380203022502d141604600c46010444142440203281014000c85420b180002c2c10401710500703000c000d40052070201821079030b603031700445501a955090300c1c012001c2d51110b03d0303000710300486a80b0724840410040c0d0341e580015000c69440440c4c01c043c030405549540bc002d01801031403d00011903942516600d6a400c01107900c0d001552030314000c5100c41c1804030880e240401e05807102009145010b05008401c500002e20904005c410580800080c255016448406001c41c00100341e095013030806100710403441850b1841040101c102000080384c000680e203c4500440d4080300e25605800c1c1004107800b5091482d5050080c0b19081d0210f54100d4050b080c40c0e14041c00410a603038854509a048c3c42e1140c6010700513a00c001d19000c0090180e8124503504124044085541418040440c09a80004003c85446d03511200140c030340186107600740c09101000c90040c288 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 989519739 1250 989518489 989518547
    0x21c0c0c140d0c0e010927020d060f091a07080f01270207050a021e0a1205030c0d02030408070803070c090203190c1205100b030c0c0a020901120302190308060420030a050601 76
    0x7d2031181c210001d0040c0c404004070010301040c0c2d80300382603056095500388456011494600e100ca100c4904000c15446000d0101d003400b071003100001d1154034101440031850f400c21074200c1100207100b0044603841c2188442c08030401050000d040c000340b0070401040c0603845403041244103000c40800c81c85580080c0e0000145a0318a070440b812a41c41c195038a10780c075090b062040c10351081c0a003402981c49456410404141c1c004000c1003261045c0c015690f91545892441c2c0e1280300300c603005032981038162030600400b42180d0003140c0010403205541a490351910b6a182900c407064440808107800e90032090201e070782809141d07801782040c1a0b80c44c03c00d0509082e500d0900000d001c100f050040440c1903000e12108101180410383c005003100229a03640c0141c90100140c40c0c0200c00500034140d0706641007210302568840c1e030f80c0c1602d034403806584580034000202540d08001c6140582c41c643d040d000900c4100542c05a807101101088514240001500e25004803020f540d002d0313070f081d171744403a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 989520989 1250 989519739 989519801
    0x8250908060f06090610140310030b0f0108060604020a021609050a0b0102070308040611100f0504060605010e21070b04151806050304061812021c0c0c140d0c0e0109 72
    0x51700070000c0b120b0b404c919420034800c460307000e01c3c0c40c2c1321908031200005100d2050580e401000803280700d940c842c6100d5030781d5407001203403074020320964140383e20110200320b481c50143c015040c85121481100c100c501c108503007509002007540081030701c665600034403403061124058080d12203407c0c00103040d500d2841c0e9460b0703030714401c5100701410030000c5c0d0709150aa0200340800e4010b00315049082c04403010403599030004210903102161824a41100007a0ad54041e602da071698410080022410300d4040907012040d0160b000308280f40d0140310f0300812810b0710030000d0405040181c2c105e480200d02110041c0ca9121221780d82590a006443d0400829a11078212948203a00101c040745d14401401900442d200c1601c1c003c05074200320408405a07913000a900f0780e003c80701c2c00d01508100c3c400d10152110188508090414910700c00140702d195401c0030503110860001d403001c40c1c00c007110780302e4901f00701c1c1c9600f104009071040320042203a805039005105d04884c0800b0002182061889000d0f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 989522239 1250 989520989 989520991
    0x100e030f0a1109071803110f0f011e030216111507022407020d050303070206072a170a021e030a0509090a0b060406030b011103070b0708250908060f0609 67
    0x1074402d4040c0000262036610a070705044070403850b5036840301d845d502c030302d09406404152212640141016050030b85185428480d007500c41106031111222072409c90b019400c1904200811418950200901c1c403000340050300c401e2032140a98510103861070f0000070040d1003a030741000c8502c1c00c4000d10803c4096507401101a4912107000983c042001c1540542402406101c01c080d5014003c06511b805020000c40110700c1644a58262001c1c1d03500d44009903444035400710100d901014400d0210301540d04604105981401400d5459220880c0084002241e00c07800d00100140c10803207400315140300c0103c50081c801411070145d410f2040f2104d004040e4000c0da1031041c4100207103004507420100c0341d40034040c0050050092980d5a8070789101901a2002e80400c41c00194111078000ca0741501006451480303500281d107942540703c643c0100c407200b001074925100250b01c00201e41240d954140604e4560724917840c1e400390185031446d0f442c00d0010041100700d5000c109401c00c2500d6940303422503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 989523489 1250 989522239 989522273
    0x2032d01060504092409120809010b030601030507090e01020d0908040f0b09010f031a0405010306150902070b1b0c0304060f0e030604050d0513080f030405031903050d090f02100e030f0a 81
    0x841017503944d40981d400a0401c2c41c001a140d2201004440280d03980100300c1c03441186074200a12041c04054141a80d5410911024015401c104000d11204625410240042d85d261b000503080c51402d002010880f44007030021161000006010050b4040c40c0a0041c014a0410703506030a01e400300002070084010016600100f51703440d50f00280c4907070a0000c03490103030300241c01042550f07180e203080d100810040307156071110058407500007010300150003100d91040e400200d4949548402c81001003203450078a0070411b2075414422580d412a0810142c802040d0f07640d240c0c14103003009a405840d14980040d2070b8040d030080c0c0208000320b0307000141c2c0b240b50f8005190590717071009120002142c80700f00b90058100b9006460030184500b1000010f04242c8100b2002d503014100d141940210841d011074000300450011701c001d814500d900d1340601c010302d02402c044000c65180e80c0c001840c0710030709420500030030082c01c900145810100004a0100d400c80c1c0100081403c81d203844945a0980000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 989524739 1250 989523489 989523533
    0x140904090602160302060f09210f09120303100605091f02030f0c01200c06180a0f12110601050312160b010f0911040e0a0902032d0106050409 62
    0x10000704240c5604481c0d40410019004000f20020b16000f51180703c10788054000510b800081681c04e0b0b00420004455a040135081040320086a41800980c00c02e8039050401c12082c010002c4a0703e030789031030071780c01c1c00c418001e5a90307441c20b0020144070240c0360300a50100310080c0301e817160320784400c1d05240144035102d01b014071400394032740124a14411030164010114021400a06d400815003040c1d402d001140c1440400d905920b481e022140112400d1034065070010b004520004170f448084560a864002500c0303100381c941d1140040b44041117021640c100d695000c040b1465403211008480c544d01c800584a15490040003d03512402680c0d0329088420005001c1250740c9000c08801400c1e03403118480302e0544c0e60380d42d019888820340c4903142542d81400b038402d00854413241100c064030141c003450300241d201c0200c17010003001101412a01442028400f140d0581050001c00400b6074038009a26104501c201071800d41340035902440c044c074100080c40001030071703d81129190000c0c0d402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 989525989 1250 989524739 989524751
    0x1e060a050a090c0e06040f1a0a1202090117030f04030c06022505012001092405092806140a06060206040507170a0b01030b0403080601110a06050c040503030409091101140904 76
    0x1001030440719243c05047d803900040e0403040d80d00400059102100320356000c0f4181d039038101c5103400a84608000d41c006645001030100c00c5603a2500c1c1ca95800c50b804072401c04100195011256026030400c2d40c03441540e420030844540c0c100845600b03054803590242c103140c29861001d50b456040d000744c0d0b0521080c1014805411001000302003c260000000e0090180300d041506107000e05002c13208214a06983c00000f0900c28061240229a0704004119411304040000810785070207814441e103029003024400426464016005d0064804007000f4507402e200b4000300403110150303c1a000d540058080101040e008030b2110200d43c4082110a6029000b0748000c0c104600c00d403004052005080010042c04a00e03140c05114601c2511801c0d03680d1111001940d101070200012036080e8402540c000005019401180d0080c02c0f00640c5d0703007040d4403140000c0c10350f00250820b00c030306a81d5040540500041d54441210902d080c00c000004042c08114022507100e03283c82180110745441c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 989527239 1250 989525989 989526001
    0x20916140a1b12020622080d022205030d1404120309050904060b0108280902031e0a020307090c08070c030504050d06021201210605091e060a050a090c0e 67
    0x1a4642c0480d410076a0b8010916040d180464940251140c0c40c40140f203900000b49054040702002880481d0b544105e051208150352001701d541d2140c40e0400d040c075000c0c442d1034061420481d071605c5441070380c0c0c0c40313001076410181450b140c184901703180d40802c9580c4202c2e1105084120480d8144d0b00c0d035200c10f040c203010a050075206010268400c40d0450481d03020401030180940c400c0c0c176088400d980316640e588038461103000842c03810b150301803d200908410511400c42d81d12190a03e0720280c244e600c400d44031902031810a40302001c109080e0000042441186403e004403000b81070145000c1003040b041110050008030010718420070b2106030b16810060501a605480091000808403401e8001c24a45074001c1c0d045442d15480000c0408004100d030030250074034010015500d1a044102145500c5103000f8000191a201407800717801102501d9000d2140418441e1803038400070500c5060503d1901c00311807005101607403040c9860038601c0061601b15901049414404111415403161 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 989528489 1250 989527239 989527247
    0x31810050c180a08031201080d050f09040c030608061017010507080f0714040923011a070807060507030207050f011103010909050f010507030f061d0103080f04080f0307020916140a 79
    0xb134018040a22000c42d0540c200601c40d681c040c140c548550a96000c0400510295a02e003d001410103101409201c601020b0070141d110a811040d10305d808202c3d690f55101d00c90408105440650307045410b81c2c001d0041010b5a0a4030302802c099000030011482c214000514940c0f010703149626020100340440c19652040d215400f0800e00c030045507540da9a5a07100000500e421350070018041c2525802190a02c540c1c28903d049039100300b1003400d071402894003030040d580b050208481141c403e1014001180840c440d00f4070607081c9480040e610620780c100341c1c0c50400300000000382a1f0408c400070341c1d40403105050300c1c1103420018011442034640d00c0e00b6401c050440c0c0c0500300942c48e017000c014103943d042e044017001200c905410001240c481c002005c0030341c81111800c2e4201c07515801040000c03999001859000e03c085500e80c20070b9280c0c10307a2030a10724030041c040c0f4546c0c000315070001940b500c810300d281c000c01e4100c424125101c3d03060002d4440c90015102d05c000040104030a0403032401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 989529739 1250 989528489 989528509
    0x803010b070f15050412050c151e0c0901090f060504060e1c120810050306061504030209190f052203200115090513080307021002031810050c18 63
    0x12040c0a40c030b40783e520400c0480200f40c112425611860002040358090340548211015400040050100480e51540e040d001080c05881c8050743c12441d602103200b180b180d51490b0003480031011b403e54070000e28000411428154205400360f00c0e80038010816941c00c1070450f0222000d505046450312178040002d05c003041d41c1c429444150010103139020421441070407114a110707458039164196114411540c86c4400c030f500900e41c040d444000400c81030b1410084001c0e500941d130a48928007601c96000c5606070000b980d1143d28241040d81144065800e40165850759816080420036441c03c0031f40c4c000c181880d01d0480042d00001c000c031100f818880e410180c0d0700841c80902e204040b243c0c100f80ea0013868008903004d040070301035a0205104101c2e000d8103004401551881820b0121901c2c2c100c190350000e4803500c2544500400c0d0014080140051803150700140040209101c0b010105400c124003205543c503030510b440d0411100d10000029944028494843c00319075081b42d034081070440302d0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 989530989 1250 989529739 989529743
    0x30d03060522020909160f09060f0c05031326010203060d150608060115021009050d08070e040519051003170a03290118150809011503051b0603040803010b070f 70
    0x11780c141000403c070048005e10005005036580c6c43c01100000c9011508a0024050900041c1050b50400d0846100340e41c001e0680c0d00030400d491504060700a2000d801130300c1e912080c500c00c24202000346074030343c0c0c2c0b40210b500040500250710f14900280058071007400c50030014840603181b91000ea40d00150703801240034181820441e041c9507100c0700c4940c1b10042003c81c0d81c00500c90710ac909540701e0101d020300c2001a034800000c00e80010600c0065681d41401801d98081000d222940342484e079031805108d001b0401d24800281003501c03102c40c0e030103565000f06078a0901f03005110401c002a01000c0059043c0300c0d82c0d03aa43d8807400e480008a0180440040f14900c010480f0078504a00700c02c0700780f8a107a51426250a0b0520811403183c1c06042d40720721800c076129407085c00f5034180344e008046459000c216900006540850080b8003103081c5078075041900c0d01d602030005078407604003c010b1080c02000c116038050071458542d840130f440e84014020105e52a801081120802c00c141d80c00d101040e03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 989532239 1250 989530989 989530999
    0x301030302032b05042415121e0b011d0603071e090510051801080a0219030506040c030b070302040b1605120c0607091a0706050c16060605030d030605220209 69
    0x20400e414006e010b130150713540c0c490b44448042c10070a19141c1d54410b08840403880e030803094015103408400f815074100701009464101c90440e02e0041c0390300c1e40300805940f61244030054195414284030441d1151005100c1daa0130007948207000c1c80740d5000400360b00f01d42400d955440c500d283c41b420707040c50704074a9000c00c00b49070521052150040d01441d485050f0741043d18074850100d50307144040303550b480c284503000d41a000098020050709210380000003843c01c840600b5045a507030740c0d0300361410000700e90640719100701c0d18091040000c40d20348a90030150754507003907040c0ba00341007a50303419118203182c902100540c43c88140411009001c041d1540b29640032140e201d180c5501e11903103a010890f100740002d000c8840202e50589440420401818100c0205080590b2544c03510024003000c2c143c804010001c0c044291444041c000c8020fa15120314404900d051504080c1361500ca4601c0e410000c0c1424030805108030f880e00411503c00e80d41210040310780421051513100280b11341550242c000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 989533489 1250 989532239 989532241
    0x62202040603240f060e032407080a05060102070b0705070e1e0121060506031507030902091b120703021312110904080405061b0a0308060a0b0301030302032b05 70
    0x18a8141d880341410b50004140c1c00026000f0501c4480079208901402c0b60194510b90300b4030070306110380780900140d64050111146011190114024100c01203a0704d2940c055840c01c012055900c0000d560704019810424441c0d4146100040c0d200e0381640520b0103a0480031035280c0a005081007050018500c49004005904158150314403e1114415410a408041000190001d01c413819800d2507050403040d04010202035941102402d03000e0f00030f50b030510418003204000018800c000c0c0c090040c03500d00090513803403403042c0710141d2801046039200f560845524040c4407582c400301c5607a008440038401c05641d41d460150020701904600c072204c04594200810b40104049800b40c3c0280540c0300500720060210030480140301c00c41c0c005210200600c41046941070070400780c5161000a9070210303405416009207450052050b40540c0000c9411081c043d2500b0310070f14080140000c0302200d4555030454a006e5034920440c000a01300201d032624003034901840c820040c030f107000202c00500031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 989534739 1250 989533489 989533499
    0x123160308010509100806040201031d060703020d1409030a0e010c080301090c080901050403020a03050a09030f0b0f13050c011805130e0705010903020a0308031e0c0a18060806220204 80
    0x4031090003582c1c0910070040119603200005c032116021119070900030103407075407154011005003c000c00c8002003111000011030404109221182c0301304120340c0c006071202c09900c01401a6021100141c1c0520360304010300002a2000c030499000311030509203003444c1111200100c070000d050081c040d01d41d000100c0003185000c2650025512020242c0e1498a281c6405040c64200c8805480c000d0240c1d1100e035010000901800c06806209041d00708203c88554a850313030400c8403903440b800c4a0700c113224000c026400303503180c0009820051035844c01c106103810b5070300e29544088070012107050110900d14020000300d144508005000c1c040c0c400b0070056480301940c4003401d6041040180342c0559440483c6951180744c5410441c0d40081a8054040ca140c07102c40140d440079062000d2040c3c07501e031042c2003d01c1e001c5050302401c90100055507030742c1c000c5002000c5002070015050460300d00001004107a50110f049034210308201c4030701a00101f41101140100c2011003514041d9002041c00a8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 989535989 1250 989534739 989534747
    0x10305030d0c09050906090901111804060b0a1418120604031d01050f0d020d091b050a0e0c03090c0406140f03070f1509080102040b0301090b0301060501231603 70
    0x1001d88000602440b0b030450180040e20040c00b58061103800c01c030b10303c000030f0080c0f80031488aa00890a1070001900207400c0410360b400390b02c6441464506008400c440025040c0307485044001c2400c203103030a09207011007800070700c1c1e00000781001801001c04030382c041114020900d5154210340050041c200280350328981501c6940444041c0e0120300400725110355040102e005e03103205401651142e00e04400c40c030005190b900690b21041d4450781c00d00200204108a101e600b071050b0017803505102000305601d045101c51410b810050040311400020064840042802a003240382c00402e25201c0e40c81c0752403a447c05411001255002d401c8c42c10002c0e404030704a480d1811450241c48072004980001c0c14195149100c1c0725001c12240f070884104000c3e840303450f4003411043e803480c160301600e50300c43c0b6107401c1e40c100d178100d5143ca600001c010800401c0c60b10801d0032100040c0c0003031100e2032030f100001e480180384500030100c42580001180f0071100f20400c40e1003102030703105c10300c800c1419414010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 989537239 1250 989535989 989535997
    0x7060f0215040609060506090402100f0903080a110f03040f05090603030909010b0a020c042f0d02071a1f0e0604150305030c0f0703170a1416050d050408071707080601030503 76
    0x140385c6500e8440072a00310b060001041d481070340c01508035040c4103203900007249e0f080074640780c003000c02c00000001b00c0001c2c0b00c000141034a141da556030404414407045c03d28185800c03030081c0d520030352003080104032410300c000584007244d004540060f415510f00740842d041d8840d1884c0356500118140000c1808140781000d00417440c1d01d9821249002114020301044071090081c1d00d10b800341e40100098500d14400314503c018840307401e170700d04018602c00e0720400d90700701c0542201c08611803603400c82600a5200115130001103501c0104a10780c0300078a90649821500846441800f814002141d0342c44a4000048001503c064440d0140c0e42e030034081d840c2d0b0042089007416004030070039034145c0500080d0b0b0314180c0350070801c1e040445410341282030b1540d01034400c080510101c221a842002e4500d0083e0203840d0070004048065045882d00b80d062000d01d01d58041407000511007404140c500250305c8094030b00c2e50320465103c039078241310b8a1a041195010484c03a10501c030000c403c002c4048013030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 989538489 1250 989537239 989537243
    0x31c0305010515030433020408060f0402060d0507020705150423090c0d1b02011d0105150402030603030f0a0c1704030f0b1008120a0809030c07060f0215040609 70
    0x2002682d890307800b0469020b450001c403080b4114180082000300b903107201c0c1c4151800303459140d011303603c032041c0c84114440700d44410070150031740c0480c0070003804030b05000082c0c0c0b2a2903250804120301d8035a000079113a00502e1000c8544c19510400104118020048140604802011003c4440740020390201310f030300601886803d28007001190b0040d4450240d0f00d080c80a0003881fa2180d540c0d001c0100040e9006008040103654481000c0d103002c19124482c2c910440e442c1e07001040c1c086a03c1c1d0038a07106901302208240603071400f02000311a80034192510544941264007503034a840d18000030f407941c002c0910f41c0200c00030001c1c61080e0a41c0028140303458900c0381c01ca5081608a407003a517080342c01107100250031482a085c42000041c00c01c5402c2d5400024425000c130080d448190b124506403290034140c0b0710010000d100c0d4106508181e80700e0780030011100441c5049c00f10341c0020b407200401e10441c070a00c922034907440c1c0c8840c020f02c04012021190720034407046240604014010f04440081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 989539739 1250 989538489 989538491
    0x110306090a051b01050f03070306030209101d0903220e0c090907050a02060c0912010c09081219050307050f0f03010611010221090c0307031208010f0f0312030209031c03 74
    0x4078031200c20040300c030745901c1c5405845c3d103400c1441c441d0074a100707984000c1400081558820003c0700580c0c42001003805040411112503045081c62452404c01110b2110440d0003604130702080340170400042141d0303150040035650400105100c5044040d41c01641100e5804103040c01001139070307440e800291885807000c4401c208540c982e040c06880d01d20030b08000d1001600305000190000d41010014040c0507406049500d41080c905295400c54284400b04400904002d07070070000040100b081690140391003e04a140418040d015024881154411000d1160100004031024029400d8944c10f40c0d203407006603543c0e0400f800040196109020b80000324003504140c5c0c20001051023510517001c2150303105c0c087c041c062213980041c1c01c0e00810383c00240c481c0e4086007110761020b100c401d0007140b207810301a81071150244064004001600500c0001c0c10880c810008000c882e500d110440e900901861800101aa03040f8041c0c410342141c29094882e000c454190710f282c401a0090190165070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 989540989 1250 989539739 989539753
    0x209090c03160302031323100612060506030a0206070c0807060801140f0a0510021f050705041427040221120f0705060106090311010c0816110306090a05 67
    0x154164082a0345540000c80c2e103030190100d40380641e0086170000f124242600040e4030540d15503600c814640100c424560502d000342c65880810007482e03081c2d202800f4203002003030400310101d0b5281c070ba051000d0801c6843e140400e20300d071001d0084841c180e4000d0201581e454440c148102c0e0380380309106400192107a8000065400d1280c0c8090341a150980c0e4940003401c00c9a0811030f10952400c14554081030140340054990b030f52000d100036082c00b9802400c4e0045500981d0400fa8440c0d941d415040c9041204108a141c0d216040b10309890741c298025121030044400301b0302d41c1101c42c020140d803040010800001c11134100803107114501c225880c40480f0542c3d010303241d454440106980785580301d06580454140c901002c0d101002d03103c160242080e0310780d11043d113400820f9102c6400b142d0120005d0007400841c03540042820000c4c01d100241c080c89542d1541507206d071150700040741c40c1038130301340081021003100d0401c0b04038001d0031100e07242040d403a5181c8480440358116440d1007222 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 989542239 1250 989540989 989541001
    0xc030304120804020f100e0634020109181b0302070b0603070f062601060905100201060501020307060b0d0b0403030e0705040908030a0507051c0902040507020328140d020909 76
    0x110110b1043c0e60160003610744040540c28801c1003040a040c0e54280840039813080720584448020b0043d40c56000c014042d00c1d44e20070f018250790301384410340d803805072817138008000540d030041052402c40340701c1ca01e001c80d00445400c07144d001380504d200701c203440d0340e0301d00c2074a45256154011f401d00c54001c905001060b107800003050741e45c0043c1d200e0814a122044401c01809000c2c06001c0344003a41161000d805081e210f00706070360713010b0036008500441c28580d020b000311705080b4000100b69a0900080100a0503d00080c0d568054280010030040d01c1d003101c02840d444603403907007104550150b40c1714800d04080c40d000c0c1c081e002c3d5a000c622203205a20f40002e40345424011070008035017250409180d502c800f04001d010708401081e0b1f00500004010b4840b01d40c0e8103040d02c40e4070010f800d5000425140c4c510401003500c00160052045600a01c0030410051441c11210b5034000c16604041c001c40303805070191684214800c0030081414007140c8000b0240d195002040d100c6001c0301c890215075150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 989543489 1250 989542239 989542247
    0x7080106080f01050405090a062f04030314070f05160504050a0603031d010309050601150206070306180c0909060f240203030a0f1821050309030d050406020d020c03030412 75
    0x8035502c441200b030301001000f550401b80c3c082d80e003240c3c03120281c400103042516900140c4084c0620210603048020090000d020b02c030211b10445045580158a880d18545005081d448072455030090310100107260010007402400212005900c0b0007030316a504d00c1e15a1891000d402845031a00070380c01c1c10b000591a045034032411742a03135070640310700c4c45261031000c1900040103010780c0d1605240c0e0301c02d40d481c003089013000b40314020680e07107c40d5244410440002410440701406031414141011030900149948004121000410060004000c400400110390741c40641e8443c1d0b0318540740c0540400c010080340c81040c161900240300381c011423004440034481102400c00140181c00510128400e404190002c18503a10b030b038540441d0f522059410160000310750340c07040301c410f07040d104c81050140e108a001403405180d801c00d50f06500e00b0444040c0c880c440c0e032044958080e0340f08001010040103034156600400d107201c08648070b1485001007641d991068a00342d49100d104030b001038045204d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 989544739 1250 989543489 989543491
    0xd05070c21111f09060b0a0b0d140708060d020d06021c06050d1124040e090606040c020712051c1106130c050418060e0705190b19020715080708010608 66
    0x2c81100c40860700f140d540c071030040c820030f4011114240c4860b1100081e603504806a400b0340341301441155583c0701c10000d601100e20341605100303025440020080f4103500110141d522400030b48200b40025607520000d40d1916050000900c100e102040742c1003202c03000704040c000040f503503404020710b9850f0001c0008402c1c3d001402030003a071078400e0000050404a40b0b00c00c4d080c0750f1000301d4a000c50007202c2e10a1a41140d0041502c0640100c00c00003111410072460b60420b8040d02d04001c5240b40c07160003901c445241c0100d0a03a54038100d50f40003040b45c2004441038080302e040c0284200c0c0c4403544018520540a000503009200d0500460b400b011000d01a9491a52103408a6446c5180c60240800340621500c038419019078003070070b18041482e030f004407054500d554028040c0141003074204856072455406403070002c820301805100031070244084540c41051401c1034800c020b417105040b882c107280d40d004207083d4030781e4040b107125180e00200713810b024220640f100126603894200403100440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 989545989 1250 989544739 989544763
    0x1e1119200c15190e210a0606050607020109030303020a0c05150f160e1e0316292d0c0312070807121a1804110103020f0d05070c2111 58
    0x100080c0d90b40d07070241c0100c4420035600c00151112840c260f21100c52065004172034605201d80d0841c541030000c10696114207030240104442c0d06040885a8000820313000d41400000e0505034009805d0200b41d00405480484940c010104c8071904449000d0105806007500e111143c2c90000010444480c007a01141c01c1d250b000f5504d540d201d8040104026075003507030308110482c03c0c40601140702d040e1070034461006403c40524160742000c0c9424200c4410300c940840d00758202400044500d814201c28007102c1c15400c0d0711040511034200442c43d1088400342401000e188200080c10a807040000f00c09490b4a102c4002181880c2d0394169059400c507504030344820003d600d5584104000c1300e55840701844070b140950504a2051f884040751401c1640c4d03a03080d01c200d80a00401c4200035040100900d410020b10742942444048618442c6038003d0020500c0e0080c0c44100203900c0702d2041c044c0380d5205c0c1c0c0240e41109a00b402031001c0f13004415040d42c00000600b075959188105c0340000e00000100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 989547239 1250 989545989 989546017
    0x3090c0f0f050f010329040603080a08070e09191a0d15230406020304030e040e030904061a0f1b0316060b010e2404050d03031e1119200c15 61
    0x51b84070080800e4080100c01144d40280c0e1072101202050516021b86804041d40e00c588140c1d044c0400302811403840720a03424030031050401000700b200d203298100200c00b0081c50380800c0411481c41c4c0607a0700c981140d40d5941102c0070705080d4090044a00d1161030a040d0302000304410282002c4040d1000c02c081c0320200302240c4d9001290002d40180e0085501c1400307032070f08008103054078000409541c03503140c2500c401e6101144406451501d88509001407100c00c03080041c411082c0d264484500922880c030714403c10104c2c5500050010b00320b00c1800c41460310a585c1d40d200c1061407505202082c03507051707030b46e10300d088490f903603550040c0d44107681d106005102e1045c02156250700200c440341c0000100041c8002e0100081c942c94502c00d40103d03910035240810401c0c0091801000900600900c02c4840d003044500040100c00c00c040340c0a900c0d1500c0148911944010156654078103c0c40c1e44114180d0141e05070004540801d030085d402008880c1c2c8156484203810124141c001c6542c1c083d541e03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 989548489 1250 989547239 989547281
    0x1b070314030402010203161407091a22050a05040b0f040b04080309010e1504140303070e0907030209060d06030c05030313050d020d0506041101030f0c020d03090c0f0f050f0103 77
    0x1000300c11000e168440e1051040302d1410031182000741044445103070403180c11140c1c0c0101c8040080c1481800d000c0c10908000300550210b9100d0000c00000c00070740d09006030900740c40800d660315140039030742a2448ad12002c5c0020306002100b00020002244c0030f07500041601c011401043c01a105107000b50740100c03114000751a1911003200c0c81d0300241c8064407a660f1210000c80c14401880741c498194041240c040e09442e150501c8011460101e9115000341c00c20020000b2464024114105c1c15005403000c081d00d564091055009200d00c102c5103a00c80c402142480180300c040d0010303c2500e00c2042800d14090b9100207241c0ea90164203249801c00f05140070900550403c0d030300346d0405074001825800e80d0585030b101c1608103402580c01703858222150b03000a5840d6003500902a40000c6a181000f5280c40c1190094803a01c0d111803010400d52100284010700c80c41d612841b01502d010204c00700c1d680d0742e60004407100a41481900d008514011b441c05203907000c0e108140745141c44a80b070005c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 989549739 1250 989548489 989548517
    0x10b0d0317090c0301090803090d090503030f031902071b0b0313110301020d0513110a05090403030e0c100e011407120c030513090b1915050708211b0703 67
    0x40a5001400c40c8a588a11039040743c40d82c2d0240141d0a40ca80a500965aa42441c503d803034245440e0361920401d01c07c08210800482c3c80020445441d140d842202c40e403292105d00b804105000700d8030789040b501d4004240c0d442031005070a00c810000b40300c515100d8503150b0b184070b92203840c042180c181d0000c408660300d110200f0010b00504924140c0200010700c1e1100d40301341c80c8106c81c0300740c4141103603a029803008002c00503c20006140204120307401d42e40c00d40b404002400c003840081000381055210551240c0151042102c040c1c0000000c10f40765140030810700c000d00008200301500c1c00510104007140d24604080112004140c12495003900480b44507000c1d242666145011002c000d02000f02951152444401d14054140d8040101d020391882c07003004281c015660030a035041524240c200400410900100c81d0764505040040d103407495814090785900404050303550854101200c00c11402014a400348075850351040740c0c2d0b500270342c0800980c8070302544c900100070505110380e840e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 989550989 1250 989549739 989549777
    0x30507020727091b0302090709080604110324071b02030d0e03030d020d14070816030c090f0801021b0a030e0d06180b06030c0402090f0f0607140f010b0d03 68
    0x1101009581010500c07072800c0c0c4c3c03110741301281d2602004c040d84011400b80114a00881e000c0d40007001842c041c0c40d050b0808540c5c40d03c41c01c001d07100a02804c001990564103460500014801d2410547c0c6042007280e00d400c01800072000f100c4040000710700c00e034850a00380481c0e070382040c0c46801900030251401c9440003503890401e030b0b507802541072000303000c00d42d28007040c1c0c002424825086000440c00c0e07824491030024401c8040c142405009021003008100d03010400d028003c000d03540b4000c1401020a4000d4076000310940186146080780765000c540d8a0701500100030520f14418a000f4401d04801c519445070304940008001410440d20520f9520f4a015203401b1140100c00014901c1c041c20b41000e1000c01c1c9038000c4a500c01400204822440c0c180558024403a043d03405503d0311644500040340ea1002d03501151041c1c4071800c41e10303002e0300e23800142c850059003c1c6100d40c801083e10119580c8481081130304c2255800d01402403401d0902840c6200840d40c9925030307003c603a80c03580402d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 989552239 1250 989550989 989551049
    0x60e0d020f030f0a050c0303070309050c01080411090703020c1219020705101d041407031a0a0504020705100c081b0a0e0f0d0c1e090606020601120f0501060f060305070207 75
    0xa0070800e040c00001b007981401d00c01140100101d032070000d99a4811300c3c0403410810990f5600e81800b01180400c00410030aa1019214040483d9003000701d503a001c0080d4024020720720641c650317114140c0409055282c810040082c0c4080300d81c0c040350380c155032208a03680c0d01e86000e0180c20508601c003415203903014100c0c104188862902c5200380b89480801b0a0440304070303801c4c1c214614220024000c0c499010b2082c501220305c0c0c040d03512900480310020403100c10b818491240120390000d806810b0100074031465080c4410030f4028002c202c150003000309120070a54075807082d0751404800001c40001d2108440f414000c030745035030060001f1481001300312040211216040300c10070011900290013000441c01a0031900c0508091103031504105c1d121030407607041060900e19001090081d9a0001a03041c1103d0010f600000002102d14042a00c1c14ae0504003c0c074a40c05c0c102c0100d0b507210750328002c00603946241d40400c074070760b40c4800c00c0340e841c51584941c02c82d00e0105881580c801210700000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 989553489 1250 989552239 989552257
    0x60f062205090403030f0e06010b19140328051303030e030c06010b03070e060705190206070501050a09210c02310e19050c090a0f09060e0d020f030f 65
    0x240c80103a0307407000450700451007118118002541d820030b08040e068203106502090b040382e0300070192903041840f40f040910400d02c80040c02904100d01c08001445603c2500d40841207a0140d41c0342d052540381c0003484080d20600940130000c2ca000c20300214007074880c9500c034454a03095000b0500c1c0c80d4505400401c00c0d0800d59149000c100846580e202040102d14000c064000445d0340e24a40f51500812522070749010600c40e0380700300b2150300032800000d80007040b20403445841c01080f1062000881d2480348800080c11942060704100c0980740e81c0e8000d030300c2140035480c0810120341d800c00000420031032100c01030100c0c00c042d00c45009406c100032000b00d0711910548a02c41c2c24054031084100b01c0c2da03800c1c0c042c619901c030000c1310368000040c001752000904002d1031030102aa59a101a200c40d41d41c9111070107a119a400282c003014035410100180481243c1000401d0b298184140940f40d0030030320005130f1082e140b84041142c07000904100c100c00d0840554180100440b41d9001c96101c8803a07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 989554739 1250 989553489 989553547
    0x602160e0601111b04051302150c01151401032a0e01120e1c09060206070e0303040302040504080d0b0604061b050106030b1e010f0b030105060d090c0b12060f06 70
    0x4400d912140412400003203404c252400044505890304110640b28004e00c0b0b0450041d403140d4040068071a20041a2040d080b140629101d601100c402401018031840c1c11494454052001600034640c40460300d40b0f500a82c0d0520025031000b0300e41e12050940c2c41c83c1d06c444450741d415101c81e07510a01d81c1c5080340c0c83c14500a00d8081d4101c1d10401616071860540300d86030029000102780c0d00344581100004c140500380050002d29001d4044d40303c8800602c0c400501001117850f0209541c01d10440300616030081003080305c5d0419003024651504001c0005081d549011135804142c80c0c110143c804864807a6110b90410071403d40607280c100801c6400c03115507403034001c0480028107000c036440c07003994800000803001c004000d0f484040071042c7e20521001114000610207003458004590540d18242d17506a6603070f2101400070000d128400010b4840001501c0214204481c01300030311010480515200840e207400c401c104020f4101620544d1248040045010f03c1d000c070142c2011828000709 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 989555989 1250 989554739 989554757
    0xa051002010902040219091d010e1003080a030c20061501030b030d110d050315060c3408150f0402060f0406080f01091404081b07031109010602160e0601 67
    0x401304040e60400d20720049803220304101c2003080380d0302c504418000c02c1d1034814203100002072125492180e00600402d070781c1051590010710411102c404880041d0f502c40c0c0c0b62641c07480000030040c020204004098001035982e0040e4227105041c030301902140e0345201c09420f80e078807040c1da0030409000071039005041c140c036040c016075103507428812005000f5990711034030304041d40c1c2c203031082c281041d1210030814040701f40f0920243c194403400c0c2605940d41550301d03a6035041e0004100e85041c0d002c0001901401a42c1086840d900118101018032401e8903030380104585c6484415480d40c200c88040100c202442d0009038100344a41d0415070030078000f0301001d143c01400302840616a100f600008041402e2005101140038810042c90042640110030004815000c402e06103010003e4000f610b00380c0081f80c00101fa40d105041c2d01c4160803c982190040c40c0d40b85410401c6441007840d00744a0440c1500006041c0d002052009403642100c1c502c0c64100d061041200f103001d006007070300d4100614a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 989557239 1250 989555989 989555993
    0xf0f0309020312120f01032414040c06022a061e040f0608100b0a0e0402040f030c050a090c0f120605040f0f051510030f0e0d090303030c02010b0a0510020109 69
    0x40441e00384440f082a00680e20300b0404210f00070a0b5002d80625819031180c030040010030b0450700e0030304890b0070068600803103080821810000e0080506110104104901400100210b403555541201c0080d02902c462300c02062040343c0c0d4503c541c447c204031a04041050a15161a00042c03060001d803090841403100341040c40d81d00380d08a038022002044400030140304030380e04062525030200380c910200c40c00606003001c00200e801030360041d0061000080045800d1750f20782d0155406040d8080d5240c905d43d1342c0c0e04019214013a02c0c46410b000701283d0401040c412400d000d854440c040a0b00c403044c80710ba030520308a07a0002c80c00044000107a4510001c50140e8880c003410f0b152502c2c440000c9904d48001e2112412500050942c4601c1c00c0c00f0000010b4584601c1c02444103103841d03090018020680c500102c0152250190082c007602071808100290ba0b0404249400e880c000e640801015068020036800c0325000750203540d102c541d024040055203080a440045003400b40700100f0380381902d0f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 989558489 1250 989557239 989557243
    0x1504030f1e03081005061908250e1806031e0307081b0f010903090501050904090524090703020a0312050c100605130203150d0f05102003070f0f03090203 67
    0x2070001100081c40e10070a01000342640c1003e003001d0710f0300316000c92038a4502c554104d61140003260342014801001e00080004000c8270820f120710244800140e068840b500000b404184222650b9100302010018000ca404402d40c00c9481008d016000706560104403404003144541014045c145220130003685002800e86030191030f20f0f0960b182c10001ca01c016a503c1410300714801b80030b141980c50045128040b07640503a44008940c02800e00c140c1d40d070104808640604100030002e0000d101d445609112507a0106c80031048410410054040303403140080319480c1d60fa18413019500803a103076800c1c004a10340315032654402c502803e02e6440c3c60000e0258034281199101264500c95903007030308104c54200b120503104102091030007140b40d4035182411481d010400123800c2d01900042c00b0481c10807000c070f619803e0b45030300441151610080400081c0141005611402550000d948007402442c400400c0e6030141c221603d9154503d2603254048030541c0c101c187e0748080648502500c0d0140e201 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 989559739 1250 989558489 989558543
    0xe070b070b01030b0612030c0a0c170c04150909050307060b10050a050a09031b0501030e0c15070201030b03120903010c031802010c0512120a0b0105160f022b020f1504030f 75
    0x928002707801700300300f10b040000518040390f1000c409040050000196180d0206d40110030440c100e03400241c0749464440d03d5124400c42c0c1010140c00d26211006040c40380000240c0107240c855034041c4002840b103400d2203050b484103011080450020700140c003000e0700400240030322403000d1034030304201583c0380c0310f240702c02552554016140300c25140c28402c0d940d040c0a003505c0c99104e07800904000a4000218805da402c03044207940380000443c00008580c440c1e040b4807041d0400604a030901500e42d4a0340366140e0024000714030941c0b0b0240c450324114000e000c1c4046510350015418007010482d001951710300752044044803070740984000b0012590b000b10281c071151151a4281403e450844140c504032081420118140300051003608108440e0008685055a1101c041100c2c4600ca10205880036600c40000c0340c00807054100300244842174100d5a41c9a000f110101100d400c410300748010102c240d100146148410031090020a21442c0007143e610b1140c0c0c4400d5010034401d940d40c548402d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 989560989 1250 989559739 989559757
    0x30f011424070b0f160525050f0102030106020d02070e010501050304020402090409020a06031e060b09010c0512180f01081b180301150518101401120e010e070b070b01030b061203 78
    0x6550144114026502d080002d1703078070b40381020707850541d800c0b80415040c0d8507038001d5100c00380050343c42400c00034240440042e11900000a54803545c5900010f51900080004c450051040741c2000036080725065a1604a940c180c5620745140c89580070b2001030340c4007440054120361036050500040c0c498104810041005660007d100c040f40365664403091103030703508882094240034060005a0804048540030082400d042d0f012003110301d001030a180d46603042e5141c181000c156094030700c00b400c000c0210088126015000c140c6008010b44200006076560b050341a5242c02c00e00101e80e0110040c2144810280e0701480d06983d0030000c0c0c04d582e1007854800300d60302011010485400c0120207021410400c0c440c0b02c84918091425641c01403103803094908103503070900c1d01503840c0d004002c0c404800c0540790041c440c16200c08a080d003c0c0c8420329980010340b28440b00062140845c0b410b0724002980308084e0f040076440d43e15840c00e44d60b0301400c41036120301d003030510070280c820810003441104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 989562239 1250 989560989 989561011
    0xa03060501091404020a0b030709090e0303190c02100213030506010b070b061f0e041b030e070602190b09011401080706080f161d030a030302030f011424070b 69
    0x9030401a122080c1c0c0c0c1c00c10301d40700f0501480424440103940d0404c0720f200341c4140c4040b440d00e0b9034540c1000c90758030103141e110384100c501d001140176450070080300842c400e90f4040300d4411100500200321086a500e0801c4100503008400d02c1080f01d001c0750000c054240101d240d03501d41540b60307100c0c0b5061510030b81c00701d8080ca100003005000c01500d280e440d03a0240f01180c000d0510780e040386500c9401205445100300308a590300303404201d552140d02c070100038501c21401803405209540050300400c0e10603e401c89074400d20750300048540c0300080c40c1c0d101c0c00c0c07461040e8080325680d84d1200020080944048041d5480f101403078844175001014a00800c0170800a140c3d90303282030405400044003604466003803030305400700321500c05400707000c0c0c0e040c1016141c940503020385212000c1035041c080c04059403601075543c141081c1913040d0007441c050701c1c0300c0ba00c2d504d16036611219601301100180d0b81c2c079001888024203444080902c4520600504198055440c14600780e0358126002c4044600800c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 989563489 1250 989562239 989562241
    0x2b210e21010f0f0c08011532031f050a0504020d1823060f010311030715090504180c06180503030f03040303290f061201030308090f0604111507020a030605 68
    0x141c1d20b01400050704a1390408045030350421280c1c85800e01c0983c110400e1011b0354001c0d0040c002d160081c2c10003014040c01c08014800d00d00810400c0748d000340e403401c01d00341010ba1580703d000724000c20101180e40040201051525102c20302c4040e411802684246503a44c07000b643c141d00b088903550201c2e034400c044540404581003e01005000e07082c0711411264046010002e2034803c1e801c0007415070790001302c0f0060f0500c1060029145c60500d0300840c243c1d0b415500a0f900440d040121141030740d00c101c9040c030909400306c2d200000c41c00742a5000e414032024040070003c1c68090303085201d04442020100620716141c40c0801d20f1580010340820b1100f900104000500d0750500c0f0f0500700030b80e6506d11090043c1c1e00e000c3e1215441c01d81040380c0c401d04a101ca10402a5a03c000f140d55000034028560b00e07544e0349040c05407540408540c83e454034000c5809100e40203401140d542d00ca19840b0200042c1d0000396018049a40c0345401107441c0940c0810404000da9030314043d20000754072072103000c602 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 989564739 1250 989563489 989563511
    0x11040e011e090e0309010e030a06471903120503040b0a020a0c080a180e0a1b02072102061201080f15060904022b210e21010f 55
    0x981d80e890ba0000d440d452802d922007050141c04001c54441c05001d02c0c01694030440d02c00001c2c18510080c0004009518040c409103114040c0c0b44507081c52240c40c140082040100c2c1141c800180000110001004032007a010b00c081c5407441122a00b58079034000d500102e501d0b5a10405050021210880429004800c010410400c004007a81c4054541c1081d42442d80d0600040e01402100e1001020224007085100030380344107990881c0246440180c1ca49000d54501e658412000305444000280c3d0502036907030080f080884081c2161704040c0e00800300145050305131400d0880391010201c070310030072030184005651468090210203001504020b402e51400d400540b030045120701d05c0080350000b901038103c00310084082c0da4440c50135510321a142e40d42d840010842c082e03104100400100d0072103865100c0ca411421950250b01c10105c0499840516031400000e1000d401441c0c0040d51404606030075040405044c035010444001046583c82c18040d400d0071744110000f00c0c0c0c4003907910000510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 989565989 1250 989564739 989564789
    0x40e03211f081006060c11090403022802030f0c090103080a0c020d03030e0d0f050a051b0111070b0c1213232b05250f030f0e090c0a0311040e01 63
    0x8121604021403004c0c46c0da51928042d24540340707114807520300400002c05050003400742105030340700c45031140350b80d040320201031500c1600c0c1e520a038040d00c58407211180041d40051365142c800b03070061031400c00760f180d60b441040700e41c05100e60004018070303001c1c1c00006844031441c03001038074401d0f10702185e940d00c94002249000c0d40307081848100043c0c2106100d034503810001b200e070048558906503a0350081603090b0020420826040c00c0e9a42c41e01c041603112140d20b40103025800d11400c1c055025071254842d491030303802070b085008400c1800a01088125041002441e40c00744120384401d640075018134000040d0221500d2103030356030403900501c104e801c11613604c03422035113008944412406c98071000500314000c901000f85014102c070144c1d11102c544945829488d9442001030280243c80d1400400560074440d02902013507030455030140a160582c0f0003440f45040d01e21031410000300303040032006402c04070074004030144100070210701340d000340b00d03620701070300107003221680e4600c110500c65 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 989567239 1250 989565989 989566001
    0x304090213180b060306060a02070302030304080f070807030c12150906020306030705010c1a0702160303120b030d020a062c0604020f010f0f0c0201090e0a060302040e03211f0810 78
    0x41c10403403a0602c0301c0055501c02e01540c2c1c211b901510030319140d40301e40b01d0a80c1361000540001e54075120101d030000b0803007400124003050915440170b855000741d0714008107039142c8840c000144800110081441520810809007002034000c100708264140a11002000c48080071000d880c002e40001c00c02a650604100710b43c010002842c1014801c06551100400d40046010360310f030000d0030b03d02041e89640b0800908000e03c103121030b5010140d40da0b01c0e02070701c100d0500410319400b03070901c0d02c4071a03c1c0c5008901c45020541640140c100000c075951a400103000b4014900b030904903000d07030309080c020640c811006005100c801452107081c54010003100c1498040000c1c1004284101c02d0004c80e0b101c4006a800449420459481105880141c800e0b1842d0341103102c800c000c003010843c114000750440c40c116030081d02c00700007180d10f00c45801d4503842152011403209441550f040c3d4603548040e0710039480392405808000032840b203983c4035000316841d4000351140c2d02551074803000040511460f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 989568345 1106 989567239 989567279
    0xe070203120709031211010617210702030307150f0c080411010f141c05040807140715030c120509070305071703030412020304090213 59
    0x25a6a0001086045081c00590200b401e0074051240a02900c2d0010251105c1c030030f01950503617490300c0200c080d0783d040d0340e540030024815000c66100d4860045000140c071072102100e4406900200e004225110340008000d1100143c1d0004112006241d000002c0101011840c1c240340013818254910140903051400209c02580c0c0094013900c10b0b40702c0d00d10000b6100c1d04d40d00444022024001d0364000c035020034944111038071400003034a212035412302c4070344410000803d41e4060320390640302210000c1c0c007c0f600718100a140d802c0c10703031a0072071040140241403824005d075152001420541041c0360380d5a50781908a88210038103403296603110b40502c124280101c1c202d550b81000c0c40140c4003401003541c0403404400b80100c4801070503100c401035081da1126290303c00041c2480d1312078004c4d8441003000142e000700030300103096030a04c0040400d00852400c0c109030030704003a00200d = true := by decide +kernel

theorem cover : BRFrame.Cov 989388489 989568345 := by
  have h0 := BRFrame.cov_init 989388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 989388489 ≤ n) (h2 : n < 989568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
