-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3261
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:08:32.712992+00:00
-- url     : https://prove2.me/submissions/f0ec05e5-de45-4553-a968-e01ec88c167d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 586330935 ≤ n < 586510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 586332185 1250 586330935 586330939
    0x42303031909022803021011010506030d0c02010c020d080f0d0f150501050d0e0f01020406171b161e12020c03030d02070512030103030c0b240603060105120f06 70
    0xc58040000d600510581e8001c2d40d004000440c0034108005030134148a14410310707140380c0700441d800001a56005406d01c1400c109841d90082c40700c04a41484c00c40b0802022a4029084480c2800c45d4550140a01103071070341c2401c00b520100014004607c3c403880015004028a00004000d000015000064503004a8540080c424500c1444d0084183d0b900c00401c0100101c0c2200203100c6580100040c0c908519407046c0028845401d61002d8503084510078101c2e8241d50015040c08102d6100074a10002a40000c16000b07604289221a250b20400b8143c0c446a801c0401c030080c84000d01d0304841c45140d0002c0c40c5500419802d00382090000ca0007904441e480303009100070700c02a002140e862950705005028600b461172030b56203980694000403007220789000d0402d0110130448a4005517020794000e40e201e1102500501e4920b01011b4094444401c400c5252480ca40ca402101c010900c0884180d580c503491380c48800050701c0c00e020310074084a030b6614603c01c000c48190034480e82d910485003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 586333435 1250 586332185 586332211
    0x304090f0623060706091407030308091002030903161e03170133030b150901020706050f220315051506090114031f06080901060b18010804230303 64
    0x890b0340034101e490b00d00507400f0740020040c440e41001c2011035000c00c071828003c1c1f801e040d002d00080390301801c252854108402090b941d100340031810f0020000303450144201e0708210725502b01107030744036964001c0e25902040c8014a0302c85004005004074100d144003000b9101000c0340105182c0a040c8181501a050050001c0d900010356084003a106403142d090054400540d030f41103528100215004021040170305444882c0800151200080004108120005e80d5101e6000e1310009081c01c4641d80250f003000b40500403904581c82c00d02c01c840c0c00c3d0801c0b80c6031100d0591000c481d0031065256030310141c0601c0c81d1603940c0d030356507046070442c510502031501d544c3c4d42c0b03001a100704110750044030131140c0011000e1a038070802c6040300c0002c58000010304110310200c6051990b004054810f50040800140e0810038446010024040c0790044e008a002450900860034041e00003011540d012504010300a004501800035120346405001c01d03070301405a103030400000c1c1503622740c07003a24200c42802d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 586334685 1250 586333435 586333469
    0x70f11010e010504031a0c130602060f0907030b281b020c031c080405010b03030c0f1006060507030c0327051e090408131509170d140a020304090f06 65
    0x2101d0703c11202605d600844101c110b0881900c0c02e40590002000d51a00c040b04000400040d458000150020034290b0700518136840d04c1a00c2a660420181c005c0c3e801381c2c0000c0007400080c075003904443d17119010514240c1810700490080044145009512028901d4148041840c54000050541d41c184a800311104031003072005140c0d0340c20b4066040165007001418004209104a00060700f00780a0000883c5928569001a0070341e4054424000700351b1180c40000c242803403e00107180d9002e0301d00010000c1d10314000d0701034010710882c0401401c1160b004143d008140c0684012030b002d101d02500074070700410f1005040946229800f40754841c000c10006014850b00d0307000780f95000c110103007030151aa103d03513481420903000030f1600d0360480e030070402c0401c0b07080c2080c2c1450809c0b211a03646c40b5841e071070f010b85581c2c3e0318002d03200c100c03540e00015070ba591501c0c0c00680c560b080c1c600c4904406e64400413040201d041d030081e500104480c60400400201c2a100c2c0d400200a50394800d0900d0480c41e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 586335935 1250 586334685 586334687
    0x513030f0206090d030b060f041412070305030a0309030309141f0203130201180b160605061f2a060e06060306090a08031b0c060412141b03070f11010e01 67
    0x2c0c012205194203922200e282040c0c07500caa0407062420030302a00701d40c00c200000c0304076100750b0025008098401d5040313640d03501b14608040500300454551014000c11400c60307c03a10303100c1c40307200403a00525484001c00010184203038807000b403d5070003c4158180040720340081d5111030038a20000b940042c440c0d024044840b084c400c407805400280b00001c1c48201581c0151980544500704a418071462240003034a284014001c20304030300e000145190b04402ca00e0000d0803200c000d407080f40168560208031510410b485144030100001d401c1400d001031042d05028144070b9610300814011000506030340400030150801c00204900000340c2c1c00c1c0e07030744803024940c1c3c441e4210b450090ba40d01c14414140858490700040d6044130007600807c650944800240e900d079408004094541d61243e02080103008100700010401c0301d4074a40036203d02c440c131542c1e0b44140a05400c48104a4401d002162500810000c4410459008070b109641c1e0f64a0700f4450210b50500a071a400300307004c044000c07203079 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 586337185 1250 586335935 586335943
    0x8090d060911040e0c0a03150212070216061e080c1c091a0c220909150606230c0703060509030c0606060301030317100306020f090a0b07020603061309060513030f02 72
    0x285e80103001c03160028690f4407440055000c0200254450f0390030000144800081803900780b0404240d0001e100c81c0020202e000c211459940c0b0010801241003202483c400001d03c80d5101030100f442d0166003606c4203100e4800e140300c1d20000754604000041074014141194100614140c0604904d642da4400000c9001203c54202c0310040400800c02c10032103600c9040d1300705110030030f580302040c51694a92180740110b441e000360983d4802c0340c140b0a003200e0b89980c0903840203007030203140c0700c0311002400910340340701d007503030f182141104d000414198450386040100c2802160043c81c144038504010700700e642c403544220300403141c500070840021200d00700517046034101c96048d030300c40d8080c84005c10b03c0c8007171200140c03142074007034234401001001c58220b0020303001070b03104003420303d41d00c1d042c010800c46c45070110342c0806440c010500502c1c02599076041502d078441c07800d4680301540071900216800521030a80c00030942442d1005110b006000d0000c3c8042d03071486030700c03642040241d89030103a0391 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 586338435 1250 586337185 586337203
    0xf0e01150503010605160507060e3307141504051903020c0f0117010e010603060509012102130e060709050409050d180302130b090c0f040308090d060911040e 69
    0x11480400040008071711460041c46148002c04d0079400d040c0651341c5030f5080485e1540f0900000388400d44844182c0b506084075401988000c1281126000c5590481041c0104403008000011b01044140c02d0180d5025021100e039159001c0d1409080e0703184814030945d500392800d03969072180c04901441d540900a92a0136a82c05400078102c0b940c019040110218a00140e05d0401c0709454440f0a6244941c01c3c09028103000004042e6640c14040010211249a40818401c0081000403c02c0c41000f40c40458014074800500c9144013641c004149c0044618040c680c1d403900d0031018410f40f000101d01d05008031065642d01e25265650130400040e500d4290001e42190081d0044800c10307800740e0f91819502d06183c80740701b0341582d25000143d0b143c0840344405916515413060b24800c2c5020340859a0094606820354100b0041c00d080364114055408001c00003c1e001407418440d5441c0309903110308503400941800420061306c2e01a40201040350141c0c011810030480411000c004141058 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 586339685 1250 586338435 586338437
    0x1509051b040e0c030c040e090a03020606011d04020a0207050a090b040b0a03030519200a14070803030117030d0f140109051b0f12180c030d17060a0f0f0e0115 69
    0x141945079140f00c1606a07201500000300160104800900c54456101c1d140c0300f41d1001019000c000b126050280c1080307070003010076040188030102c3c00c241d42552004210402002e40e00107803180300720700d0141d207822642e07005070307034002e580e5040020140d0240c0c00c100a01407082d5018041403941505101004595010003070100314140100b00710703005035080301c2c090210309180c50070040c00551000009055449417501c001c0d0003841c26042441045410550146180d200914a42d0302c3c02da0040e49a0006006005080b41c100d0400314241e0030400076281e14041c0000d0821035902c4800781c1200130542c1600756030b800030040b800011100c00364030541d4843c13040490794104404214880c0b08007580300410710703041c2450512a13010000140e4525071301c2a40d0b03011154403528490495a881c14640390401da100f540308081200b803066101e1842d510401607020f540c0d0303807512214005080f21a483d00f1002e00e140c1c6140001421404441c1c4001c21607000412600c0300e40d032201e981c0240c4103101e2600b08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 586340935 1250 586339685 586339709
    0x309040e0706030e0102130504021804020d0209031c020606010f260115140f0703030f14040b0f04030f0804050307050f010b0a080114130f050105040f0201140705060114041509051b04 80
    0x11049c141500100b0b943e10131802d6081c03201c50401c00041c100c0e080450030004036903000c1102c882508041101e86071454400051148042e02a0740081d518a802410315040002400660001d98055040d41c8241d5542c142c0a2288088002c0102c0200000340304010070700441070070a01c00540102d0100c07400666409070340d40b800702c0004d2054110b81c00880e04408140d40c0d448840805035040c4101c6005a00ea140c0c10030701c80c2081c0c24211b046080140081c2010b0035090300340b1000940003003a0140300d000c1401c00309040c0d070b1282082421805204800380060285044103020400107500c00c0240d41c2d02160081c03000d0341c036080410708880351610480007447c011030110f00003002610103240c480e80f1404070300454903516920682581c80a41d400c892155840001500315071b040305c00c1e000040241040d46042140136142c569841c0300c1885035421001e0b41000e03088003516540c1107031282d040c513201e045c0315150391120203000400080303480c141000d007a0030007115240000011101294000321b504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 586342185 1250 586340935 586340939
    0x1b03050708042303070f0b0c0a2709180506130521090d030905042306040f0e0a0f020a0e0106050d0b01050d0e01020d060e130807050309040e0706030e010213 69
    0x140034040d100705541945020108102c0f0180c0f00104020701c0458420090030240d2406860322003140311001e0905400b44400b880006141903020a1000c20581d00c1c00e1752001c1440540006410008150400c00d001420300351071603010103540d110080f030184140200d80745981e82101c20700380c032617420400800c25000791500100c10f55800c030766142c4180034101c4031442d06404d600012041e65001f8401c81c0407540700142001503250600c00e0049000ca45254581e07050004a004074820100805140c441c44c0c1d24134554036010303081c0d405031018410300c8040b19550000c6080c2803140007032080049110b0f044007240030404e5500042e0581c102d9000340c4500d42003041c03129810002c0c103080c0188504000007402000b6a00900e80220700680300b4820006946080003107441041c0c60136500284a00d4207040b007408060025889090714487d0013407501d6840e4101403400508510501204660260800400000034400810200d080341c0345a2001c22105502c00e003121300380d009042480c462401003400c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 586343435 1250 586342185 586342193
    0x1806090f030720120a060606210e120c0a111f08070c05030301180b010212040b1c0203181506030a1205280201180803070c02120f011b0305070804 64
    0xd00c1030a0452000d8401c4682d03c14030209950045600b1400700c00e602c110605401d102d410f1141c900a0003242c40c0c01040300c000407900d001c01c0102c1c00440802c25a03141e6154000e00001d005009544034071440043ea42c03c00e41180c103694139850002507910701d000174295a01131030310302c0e07010380403102102051110311038022054038014002091003041c0300d1662488400158188003d6001e08a203400e1141c60100540b03075001156130961207241903600c0300600e00e10401d2014282d800710b4404403c100c0d50f8114401064092003101001000320b240040103012107a0030004107402c02122030011210708a101d40c0c0b038072141c640295900703901a00100d96100108941c4401a600f03e00103040103480c2c0007414817004801d01088011040d81100000400d082590a00840a00101050544002600a032288401840094240d900780101800f01030115103071f0780c0750016080400c01c141e69a540c001800c080c040c04010101e20f4920f27a8001c43c00b10901d001344907c0740030b90b140b981e542c6810390303565035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 586344685 1250 586343435 586343453
    0xe0a0b010e0c12040b0a0e0309090c090a031505070206060a12080a0c0b040c050108161b02040b0604060203090a1203120f0e0d120509032b141806090f0307 68
    0x1c0358800c0c00708680c007606503d031486140914420a8065941d10300300f013006003280d030001802c103030302d820400990074195940b00100b80c1102034509402e6441d040c842c00203203800c81c10f51009041528448002100001e180d210510400e445d4003a1249550f841080140d004481e01544040744803481028020030103007400b0300b20107501414850040101501c802c44080c00031135046501c0e6960310ba042c401c5590003045a90091172505d001648034280310005460480b000b08000a40c411950280e41595100c1c0c10072100303868064071681d6940c1d01e07050000e4417580000e0708a405a203040b140050072180b0000104525500f43d9200c815410710380d8002d0002e41141088824059115640040c88220502005a070300445480d0619020308161007003060b100002d14409030703034009001400f000c0050354508200d040d18210000231503640d80d94113500820750480380f08000361101040126000305815854505086407045680d9680c0707181f0515540d9000e040c408003075030010711281c0002041c0071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 586345935 1250 586344685 586344691
    0x6072004022506060509070215040525060f05070b0a05040606030506070c02010e090103020109030b09031c0c031a0a090902030f0a1a09011107020d03051c020a030e0a0b010e 76
    0x2000980b034040c0d504104600c14034441c90550000e0014101c800c01c0100b648600e00041c202616641d02c64a000400a500c94040710900710440000c0c80018040100500c1451420310341c1c0d103080080520b40351201110105240180030206072220b1000041c5070066041d15140c540c0300b0142d008954410304003401422018104450140d00d800000c00002d8007801a24400da2183d540c1400002081c00014040451030070034074000c2d6800c500600141c0d81c40000d00095a422104080b11a1100c00302ea82c554030072180d04121036403170300803080801c513901e4000000700300140d942840142c4109000140110307088030a50f621003c5003808100c1150300340c00000740c1034001070a581e03030003401700181e508080744104100e86404c8581700a14101a100310003030b400600000081025801480105102e03100340e44010f4852140c128101003054800e078111a1250312508400341d020f1901c0d5a100040c0d004800c50704046414041442145080056407140550b003141340748000c2c0e440e120255402150103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 586347185 1250 586345935 586345939
    0xc0d0c080318210a1205010b030c07080706020408071401050a020c19050a140909030301060c02040f021605070608011a1801020307080a0513140906010305060a120302030414060720 79
    0x10f0744550300420a4040c0d40701030a0900404142c2d1400c0e00c08000b8410041812200c14251070b250051158820020560b030340194200a501d59030002c03410140001e006001c0c0041044e400050301182000000c1420012600035150324940c5140b00380055450340103009490f801684418244030b094600504042d108100d13100d031484100e919000410058992a042208200070b070220000c0c00e0f061220613140d010907035502070b40c11541401c000414160701000302034031594442c41a01e5107441164101d07998400903a2500c00003020919050351a07140031b00c110300100c0c401c00d0000484100200a00284080803e62240b820250300400320b249800030084c0c0d411880103000e850000340754407000300810030f100c0e26043c0c1c8400021103050b00030140ba420070407408000300700302080e640b00d01c0345007500050242130100d04d030354540003c0b5881100f168404412101c0ca11280c0c0305068000c4001d0040d01c074403031100c42021074400e0a01c0142d21580c50001e00b0f40118101c1e941c500c86803441382090071200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 586348435 1250 586347185 586347193
    0x40504030e10201908030c1b0c0112020a0e01080c3a020f0714010905030f0909060909030301120c0b0a03060e0709050a140307090c050c0d0c080318 65
    0x81c0d001c621400109110200800e601c06121941c042c0000503540c8144818002889034402d10b4040c0750403007040c80700c01000c1c1c5201001145d501702d000030642d102035401034031000100700152600d503901c0c403100002c00d010603500802d9600404050080368000c401d1a220714100307031a000b004490030b1500030080c80d0020400e2002c02041c0e085a8460041c00385e21442042000c00e03100c101e01304501c074425201085502c108000e842d000c40d2401a150308940100c1c030702c01501c106107a501c2c00b41043d250018050301001601c2c8844204410191903c80c4080d1641c1a659031004280300d000f0209440c101c5032070b4800c0c00100941c41c02e100360b500341c02e0f204907120114a035682c01c1c160350326048501c114000c2a102d03032040c04242c80030b09240340d0204581c604021071078506000314070384ac00c840c02419008400342004240a44082084200034104100108841500031500400c1504141003003025805442031410005210309415041c490700840a14a5a01c8445a00c44c159162103010142c50107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 586349685 1250 586348435 586348457
    0x21c0c030e0c1e030d09080706051e070204020702150d151a0c0a0b04030f030f0c090501050903010b18041110020c042c0a05010510080a0b041e0c050103050c09010e04050403 76
    0x141484502c5d120961902c845404030f050074505810b00c4940d80102d020098248004004061180000c00a4811b400c02c16507888c19540082006403103080c4010b504103900d4220030980728201002848003084410081021280d15122120682c01612460740880003055903200c529108000070316901302240c08a407013844059941c44038071300c1c088805402192041c0b42c600d180b2a014011034110000060f010402c1000e0344202518604040c05a10b0401c200452078107030988095019900e0048010039202014041c1c440300110610b049070220340440c4000104100c0d402e00119001c01045c96401500c801a4581c05000060001c551102030718103500d40000c07002d944294003280100c401402904985400381812825618090501e510003d0f40c1c141c00c1003441d40c041146a0300a900112040d995103480c106440d001c001c464000711185800d08401e01008081c042140c112142a00c080c420750752006903203000b501841030401d020450244001e031441c074080d8007090b403241c800d04000420352 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 586350935 1250 586349685 586349689
    0x110109030f08041d060117180f0a1703100e1005150304110a050609041e050709090b01021218030703140706030612171b01021c0c030e0c1e 61
    0x15000d070416105003400080900c09660710300d480241e024083d080e068160704001d80001c00001242c0d54000d80491070b0b1011419503c981c81d440b484a00d00041102e4a4041c881e500645894944104842c81e401030003100c150040600c056070b01c1085c51030600024607182c0022a001480c1c018642c0c050040c080304045515682c02030103008000801c00d8507501c0303107014507064035801c0301c84003201d100340b074001802c000c2661058100c81c281242941c0110307000405100c20400303032051406145240e410442040101503210305a041101e0100c807007445191122801039803100340c00030700d6414448040116040c03c800c508282e2a56036406801c0311055540c03503c403c12000d0a11004020f02d03000404100065036240c0146400f0784031031184502000c2d01503a80030b074504ca145136a480030000100350480410a00c0d280e1162115900000350b507624008040c000c840419080410f00c103610300762806240600c60300c10441880c280c000108a0341c55082c04104080d501c1c2e2116140c443c0c481c079002c0f0700316 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 586352185 1250 586350935 586350953
    0xe09010510080f31020123030a09080c010c0f02070f21020f09010f05040e0f15091f140a0216081c0f02191b020405070c0209040c0f050a06080411010903 67
    0x1044c050f07290038010480910005101c0321910b004100c2481550031030a13001142c0c0c0c41181d8201c034407481d000500c61950301d0151072501808404600a520b41a014003005800c000b682022aaaa038207450030141c039401580c0e0f0003c494002c4480c1b064814074540c01481171894000105800241856000181e0b40e00061031003000b60020407580145080070000b6007414080c0c08980030100000d00040e07108405001e50301d0700d8002804403032900070350101e0350448050140c25070441003481501070130003003100c08201411042d00303050998101a4001008001e941c401e403500304085031029403000006440d40321045e0130042404114011088800e00190501d00c510240b14050b80400b5072207486030a02440c4002e407001c00c40c800c1c440c551030350b0140000352034078004480b541103e00007665100d840d021590502d05500c000e4212464006000c1800030f85c01078807040b01e403198070790500143c0310010b206034540c06100c1c51000c41c91036404500020762014a241b21000103140401c1d071140d0341e460306040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 586353435 1250 586352185 586352251
    0x4020d02030f2520102406121d0d030c0912020f040f020d0c0306090501050103020a2c0d0510051b0418020903151b040302150a030b03010c0e09010510080f 68
    0x80d26a5451960070301082c03046c61040c01e071501c601c01401052038001d02401c9503110700706a115065895503500c1c40e941e080c200f1203480c0d800312000c441c60404000e00c00f400516018015030040b030300782d030301c0040c0f0440d001035054481c03580649420703c82c1c04900188070103000c0100e2400ca0b550780030301800310040e400e4030400c0600d01641d540807030308a20304010101101c1040c0c10890405004000e44034009d80c04c64174030750320158020008403824041040c0c107001000c1c1c40c1c0c0e140394807038103070b0314038005100e4002580c200142c0c50320800c008a840361403002000c4003001c500d113881c0c0c00040c80100040045000b90607081646144054500090a030000b4181030840d100b20502404540900001d58981c001d110078a141d65480c1e079261605580000d141040c4841940c608214005102400c142c4213411140c14040c01800900110010103c0640150320512642d80510002000050304d03103041400030120002c0d0f5250401c03552200c03c940c0c031602070020030703889464808045802e00c440d40e483d00e80d40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 586354685 1250 586353435 586353463
    0x313050d0207091b02031903020c03030c031e01050f21250609140405060f04151404111605030c0a030815010e01121a04020d02030f2520 60
    0x48841d04003009601110454013070112901841e18807220000d80001c111001c8044041c042d410402290701c3c03c40c0079200d45151354515000100501a01e82c1c40a03028500584044103000300b03030746c03d5040d01680c2080034842c45911000445e01c090306800e00d503945403403d00b00a003000d514450000540341c038105444c0e02412103401c802041c00c0740c800040b00d00c90003030b021628100304903a1614080211030170002c0303090703071090341e6500110340c5a40d213a8440324862000900706014100702002d03486103513407040c070802c0c282c8100c0c001440300d0391a003407080c5452944040007450900382c45600c00c0181c2e21081c0011102031200b00b0560000303400801c00c03500b035984659100f50951414603c4900c1044000404906202c078140301010b040c2c0c0c01840c07400030302c4440b0318000f07451100081d110302c16200200849412510000301d24070441002c0c0c00561185100719400184c1d42c0740e991030511403030303442046c0c0020b1804080004502903c10305141e0000300c28424007400b0700070700c0e03403030242080f898400c840 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 586355935 1250 586354685 586354693
    0x50103050f060f15010f0e03010e1f090b010317090303120115111005102102090609090a06180605130308181e010608070b040e010e011a0313050d02 65
    0x100d15001c0040b03e61100007202580e0403030078024a0b464024160014030b90510084154040645100e0325425820010050003400b2039140040c52075120300a8841007402c01285d03019146450030305000310088103920012840e0f01d81e10b140c8494000b81200c91244140640811035035480795001c00107440c01842e41980681c0039490001824140d0100145000030300440e00308440314080003081d40c2c110b8104000d0041034031b035a522803c5820020f580c20164100003030a601c8400c1c03048000401c1071083c82904c460f00c1c280c03104070400100c80d030300b11403010450f4400e01420300064519009188071101c0c1e110b041001224507526001910f1044400c3d401941c0d9003a6024140342d40f01c42815044010504c114525602c40c980b0345d0f41ba0243c0d681c248a003010800350050141000f5802a0000c200038010748076460745031515441c01e54050f04c40c203180170320118008207010100c064014126520300c04000c6089000380c82d009180e0b00010b03c0030903841909900100070600600200506185903070180c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 586357185 1250 586355935 586355953
    0x804050f121818270105011a0a140316080901020328140a02070203060f060a05011b0f08040e0705040803040e0a150e070f0219030806030a080a0905010e010c0c18060905010305 77
    0x15a21000302200c8941c04c2c1d0381020010000095010300740d10051101d240002d0383e901c804030040c2c0300c070b03101040c04e1019007000004114440d043c07080b400860050a6580000c035480702c440b003d00b40d0005490342078456404501c90b07400c1c01a40c03450042825005500070440e02c0a0000910b45d41c042140c0ca400c401d0703000a281401c505d014420b4990200314200045080c1c2000c00200341c0c0f036000c0303028007414044080343e10b06d40d00c42428480000242d000003050f03925444c13440c0ca0308142d0014440c4d258211449000300310014011400d903801e1b155807400450826150440c0c640d0104005003032075000030f6445520240300303520b6510f4980a02044000512a4102203100910050620f1004021900503140041d500d20860346003800380c036094500382d4445e0302c910b8006402c00002d03000003003043c0c00014080111503080300240b0100d0b40c007600c3d4150070707030641320040d55007201202000701030040c1c10b04c1c14812100c0700300b1164520040044002280c645401e503013411030701d080e0000c1d1b03001d500000c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 586358435 1250 586357185 586357231
    0xd0509150703230f0f0703020c030c0724020322080f0c03060109110306060702151809071716030f02040305031b1f0203090c0a060804050f121818 64
    0x1425500312a01c468103d61a0a2807860045580074220b11400c80c1588080f40d000380c4aa010f469042040c4000e5035a501481d843d455500ca20724400c0489144404010400411b499402c440b084809500a145400006203800078045192080e2111640e0310004c0031510704410041e42c00b506008600508400c003e000816280c034505a200400c0c8608040440e0303000140b000c1501c0d080102503895503124011440010001b6010001130080501c020402002400d0104506100201e003902c0c201200d8840d491f081b200500749880c82040741a43e203002c18101c800c1c60000110701501c40c80d00042d00f0308038035030010690380b0a5009407800c2c3d00101d4001e01c503403e040c0300c0301c401c2100800203203074117403d0540c250200d40c090f649503200700b81c0c0840083d1101500340031941c0c850200510302440d0507141c8101410394801640c0649003885a00f0b16420320000010360b12104900387c109003030a0030300b40701da441d18400c200084590820f1020054003020260450610b024115618480e032001c996014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 586359685 1250 586358435 586358471
    0x4060f050c03010501020703020405311103031201150c02040234021503040809130c0e030615060a110601091b0509010c06180209070e1c05030d0509150703 68
    0x201450581c201000100020b07a000190070040360b5040d18041200d55070341d801031703d40d5002030391240f906000100240161400441004030b001d03104a900b01c0300e4a08107014107641e4009d00e980e00e0b001e10840c00041c0700403101e25200c18041d9003546401480030426a01041c16030700140344079581030100004003010007400340c0104c1c90035100d10301340301c2140c0c1d000c2e00000c003084d041d414100c0f104100000800d003400795401c100c80c003898003d01440201c07112102a080100120708654001600d0590900550302e40491801e000320340c0c28a604042c0340c150410050283d1204201c0d01c18881e02032041e103040d4106010042c000d1030075100000d4103100a0f0301c00e005400060002c1010040108000c0400b42e820040d190352864101c04002440159101d140d009001c0b001d5002c1e60226141c410801143c2d844100c0010500b8151542c800fa041c1740b414501d500300c4030b11002010380d00140071081c10045554803466002507040111100031440780d849000003c0155200c40005e17884507500504280109 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 586360935 1250 586359685 586359691
    0xa06080613181e1208060a05010f030e060915070903080409110702120604021e0609060a051b0c031204152003220611031204051504060f05 61
    0x814011154500800010200841011104200c1c1d03603680720b090712100c0c2d51401d00300351030740092840c800c583c00381000300c0401c000c41000c0318207024000614030302d10701c1400034a0241c4809800c4108242c00c041c019103a091155050b1401c00d0780d50010300f80b51940c1000f8880c020003100000d4400245a8403140b01c84520090902c0c051018a880c00c0000503600e42c05c0f6011074080080c0040c041c0c0000b800b0b0000340c4603040e40039600442c00027114050f000c1c085003241c00b0314030031260098020fa100891203c1c2401d201c50b2103500c048144000c041600340000142508403040c50064501600d1118151064400fa02c1108090703010000108141c1001c0140d003134401c0700c4408c6039040c540f03000100c42807808955a0f800400c605c0550034209014185512000300c80000c0c00e0701d8407080b5913148034056080340301c40804032100717003803000a416024030504440e0700c00210103545454146039210b2050302c0b0181c4211801d1142c48174260001000f02c02c51030289102d1203012030309612400e640c0d01620070203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 586362185 1250 586360935 586360937
    0x8090604031b15020d03150909030201050907090e0705010e180c03040b070c0f02190305070b0d06090c0c140a020901030308061f0504120317181c12020d0f1401050a06 73
    0x403a8100f100c0c50380005070941026054580400c074008903842540c1548186d0780b1124099040802d98401c154042d0081445012042d003101d080c1c1e580c441c00c1700140d0750080206485030b0031450080c0280d510034440084004030183c5012054045d9a05189030030004550302c01081ca00401807000308845256000d070054010324000e20480b1b1192507120340d1491101e4000c0c4642000000d501e049003d4681d5640119000016601c26956800703105081e47e004000c4005114500b074808a02d0f0411841481041c1c81da5903148544003100740ea0b5a010550040090f00342c511a403d90580160b40c2c504016029600c02d90340c200c12030074490180501401040c0c5516a400d074592000d4a48a600c0306c15101110081d5501e000c444103181003d45181020700810105104d135081001541d002c14040070145170024400c60b88200750b001030841c1108000c241d041c000902c00090041c44288940203020791a00d021000101d01406c200746a0031203000703445068602403001e0042180780340c0603901000038511 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 586363435 1250 586362185 586362209
    0x40b0f09212407080a090209010905060f0909030901050c030409180201110f120a120501032a0b04032616150c020c092502030d0b010c0201051608090604031b 69
    0xb51000d5450124401041d00c001c0114003000a503645401d07410040341c01c0d4020301000c40550b11019500043d00c0100d50380780c083c22520f0307045511070408a404501c141c1803400550f00f400060f0004444641c003640e1125028402484082145c5c000e6100c2c03103e8005003081643c0031814144005441c04900d00015134468020060300c8903171a001041a80c1510306c03031001e241e901c240341e500c256210b200344006140c40b2443d04001104003c281100280268400142d0700301b05102c02e00c0c0402d0708821406040b08140c5d043c442080001e00ca1000940a482e41d02c4580601034030841d80d41d29150000410302c01c050f40e08110800612815a50f504120900090140301c0f4009070f0034042c0d55025466030240c018040917000403448041e052140c4094294a24464009030007034000961300d81002280765190f07032800510f196650b000d803080b42d0300298103850345400c10390307449202c41d1032080c0b0020aa903410340402410728195240001000074500c42c0c0e60b40c1441c094030202442001d12907401c1000c003120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 586364685 1250 586363435 586363483
    0x150601020712151d03070b09010b041b0809070e0a15090c0f0509130e0609191101080405070b0d14240d030203070209070302071a0c040b0f0921 63
    0x8030740c14510410074003c24080384600302c05504820908070350b64840502c0c080403e0300b4042100000055001e40b03480402409074503281005c21049607140030701c0e4808004003e40302c18907640205146980011b05000780c4083c1c40e40c40750840d000000459442d0034240d039883e002c61521003280e501002030080000100600c1500180107402c8030312040e100405d020000c00c0420300d40d03a8081000002c1c44800c41c0a102c86122a000700350b0700c0d0010f6811401d01d0040710900c90140c5081008140d800350440180748540314000010f44140d000504155211f008540e000b107080d051003030080c03000c03034200d2000050807021103038040017640c4040c1402c04180d80c10004008418007840d40d0304c2c141c1600b21070801050f0a5403909074614030030564025001580c3c6010802c07103036016400b0740307070b040d00540f41000f4202c0c2c1441c0300c050b1180c048507184002d2509100901c91049890007400c2003641d2145031500d8a484030b400100016100b40d50015860580300c0400e4108800b842548141c01c01150742d914404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 586365935 1250 586364685 586364693
    0x30302070603090203010f0603050303071d150313050a0507181b0509030a051204050f010807120209010216090606030e0601060207030210031d33040b060a08150601020712 75
    0x105a44600d004041d100c003d0b034001d41d43c003940403000c6140d01c5c40c0b04000060752031410075142d070421a5640d0114940c1600d0003400c000c000118009100020318030000c081cac9101035103420b908058225000c5500c1c882d01d04000585c02c014040899000300d0040c102e0300e10702a8040c8002c80042c1c61601c065003010750080c02c80c00100c11a00c01a400c90034155110240c0001103458021800d501415034071501300000004010312000340181c402c26100003807407000880054034412411ba5291000500ba03421200b20212250f01500d000c000c144103941c00012411200b0002d0b2080d83c101d882400d603982020000980c01d40325101d580c80c503c1018002035032509401944079025440b000e03004242c40540c0c800c801d44a54068074909070010b94202990f00d02d00000c03940d49000401020710207083c0503407101004000c00c9000c203440d00e817620742c003029540c5076144501000050304090b04005900f2020070803607400d01030b00c07945281e40c001090052816400091600350b081d400611100c44c01c0716100081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 586367185 1250 586365935 586365943
    0x106230114030705070c06030603050d05031e0414070b090f19031410021b12090f21030304050a0302062d090c030d231206100c0515070810030302 64
    0x503080500c0c1a07160303903400000341c80c144100a030041c48051b010740f0108100b13403d540644150f902035030482d06905164002510107100c26180000700c03000c00070214240925542c802a405882101444280010207805910f02041508640c1840c0d00228030130f605818440d82ca03210b0414103c90040408495121076801d5810f103000281401004450090701070000704079400c2c2c2c00c4c10080c000c40d41e51810b649030784a81401102d1006643c0618480b001c901c40107081075816802c4014460b4920001e40010001010b1f0ba21a10307814a1586400c0b240c414241407010758411401034003d0b20000d1400c2c03400904101c0c0082c21404500c2044801482101c1100d1808103d4440035078031144d03070744a01302080e28044c1003084042c0d0620610500d031040952080d070140c00b1110040328001c011920700f06490a60040c0c038060910094140b000460b1458018092400e0765001c1c20120242c20310360300c8945c102000307540003403a0103481c0b1041c003852590151a0603030013801100180d042c0350035554000c0d25 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 586368435 1250 586367185 586367207
    0x10030e341406030c070b040b0402040e0c060f1b03041202120102210402040e2505030109081905070605090304060801060804050a061104080f070f0b0705030301090c030605100201062301 81
    0xb0b40340110004140c0c1c844d0300c0481e0f2245411000102d81440c1618040d07051010848040307000d2402c001c0d8102e2980000030f80d64030880001000176052403503880c481062500700060214005070f650100349048134090006001409a130340b070042c62200140107000c0c013502c80e0140549103070310401590000c00303903031201c5110360041c0341810000e40c0c071180005800f41c0b1005800680e640504040c400003091a4101030078003040e9031a168151079980d90400d400c8601415000e0901c0800700004540e10500d02d0600040f1101e0707044c520300740840340d2110802c8440072900d55001c5ea1000a050210340e030041400ca00400c41440c040700585042c1c0e850540324003000f85d00400054441c03800d61a49900001a00e01804524084035225203041c1103040c1e85074020b21400003042c00c1210080748094000e402c881c000c4c1d030448000c510f544d180034074007001809096903580415a40b50700115040e076901100c0ca00301d560b0390380045021410041002400394040205c0400340c0b0001d60701c46440d9802c0140840 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 586369685 1250 586368435 586368439
    0x80301050f060403060f0b0301050711070b2d040303080627090f030d2702030a1203060b0c0307050c09091504060e0a030215090303100510030e3414 65
    0x5401d500004941d40e4041d40c0c00045c1418100142c0305200d0006900140400600310024021511106020b40390318004164a44080d0000c04042c403114015000801503d00441c14840e0011000c0414544106100b0002c20309460009400c0040c15030106800e900050129504001c4500c0f8400c4101c0700060750b540c8020001d00f00d000640009001c1c007401440000c0d00e02540c1d9a04991001d8500409410442c450000000c004440d203800501000d110200d5004e0f000304980c030140e0f140c602402031840034080406031500b2011a050180c003015040b808070900003143c6038a298a001401c00509140003400340c4881da04005029200054021100301c02540d1201d40c0c0e01c46050002c09082c022a02da0014411010b4a50405900060f520450700c0c10030400403040d03c800c1149504c900c4182c8407403881cac0207072030b00502a40c544141301184135462030170001400c0c1c0004000c2c41c102084164014842d80900b40009d54410074144030341c0f22560514159910390707040807210000c41a105185074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 586370935 1250 586369685 586369699
    0x6010605040b07030c020d060204060c020a0f27060f0f1d06031009030309060203040f1a07020c040b12061006030e070f030803190207050105190209090115020a061b020d090308030105 80
    0x203544851f1011820303a034018205554845c2c659001400c036200c043d008900802119500040c04103a60403030350f080d0f45c560021520394850340540e811010b6581c00500d04a15680e400005032141283d046a00400f004594203d00915110202c04507210030a4400da082144604000c0340740e034007040c00461a01001c800080928403801e04030014801218001c112510010500051150407040780c0d180305c2c4a14102140c11025005c40740000710f01b03540701009030f840500381c618145820b402013010454081c10032208440750740c44c49440c1480c280c03404440118015024000700741d060040404c00a8618010301c034061030308000c1c188202c8a484050940c2d50007002050380c00d48101e03940000800841425901e818590a009000f050143e1340343d0542160f0711944d480e030011900990702621401011b4554a03032034035001c1d402003800b040c210011801941c040c90000740441c4202240480d121807480d5210721032180280c907104500303000d4001d00c40801c40070000075120008407419140c00b55102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 586372185 1250 586370935 586370957
    0x1101120608030d151a070803060f03030d06170c0306010e071e080105090105040603150e120408241b0705120a0f0801090e0312040203070512060906010605040b0703 72
    0x4200420301500406502c0c000007414212038030751134004a0502d0320003142c01da015039880052942181d40440e220007010800c2c08600d0105620101440e4007060203454040c0d105507020000f4150791145000c1114140d5658040c8069059000c4140391070145100030002044804000fa079600303c144200100c5001d81c4c0005070f2031500c5103407102c8614030f01008590240f494280041d007a405c01340500c0340141e0f40c8000018042c98203000351411070b0313040585880c2d203000049110018040c1ca940c200b8052040c1e680802d074900e003400040c4014501c03080034101c4040103054003000c00d9441c1c0c0110010101d0f520502511034020b11a20b00c4222a6018240e0b071080145005402d01e2a1800540b44a00c004141d54840340c1d002044901d4030074465036611402e030b0700d4813851811a00041490245a1700501c174011041001e01c2030150094001011195119500c0e0000343c21181601001041c3e508000140606c102c010001c80340034162904160781020b081c0069141e841c040e015018003009000050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 586373435 1250 586372185 586372217
    0x412080c011107140609061312020c0901080f01050a0203070e0111100501230301140a0c050c070b091e090c07020105070b0f100b07020906060c070806011401030609091101 75
    0x442182c60482c5500980c69611a06000d40c0860341c6207100d607024028400040c10aa42c00324249200d100303209400e00d616841c60711801d0607031500c00e4401e001e52251454500796960b07900308090003403903400c006100f005242080c3c2030950300301400103100d1900620620140a8100342100541c00e000c0c40d080300354500740100302c0d1511104038801034500345081f001103107504060b140f40c00419880c01000c0c013680781501c18142240c40c280302901c0401d13240004030310500e1568200074801e002d0740c6440c0d41000414a60a4244851540108910740300040c10317124a04103100d103003d8400300200740362032008213071000c030300031020007800070710480c3d80001c01104580c000c200f80c0354a03d420684015040c036180300038480c4480f06a90746220900400000580500c000049450181d4080c000160a40712101070107616088103440e012035000c0c01c40d0100e03042c0300401c201d9008111a443c0c03505288035840014044840c00d40200b1011801c0c5210403022038100c05207030500360802e10b8810880350540b20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 586374685 1250 586373435 586373441
    0x1a031510140703020a302019121e0c1e030c02010221090f0a030203061302011b0807021003021303030801030204110301050901031401020d1e0605060412080c01 70
    0x1200710820480801c0341c070306150340003410490051080701e05d8041d0148004c900030501c503c0d004c01c04011742c102070a000b51141705c2d13202c841008451248031707100e1011080006080c5207001002c4002000190075503400c1c00420783e94031681e00e440d42401c44202e503032148000394012000009609000300d800c0c0e95810071290030000c503125185640000340c209000c5c60300a10703080070380205a0040c811041c031101c100003103001c00042212261402440d1039031103418401250f8048410550081c0340181c00009624140f01c0d00f441001d600014540040c810307c000743c10101c8850039504c0c6140d0404541000644d80327030840d01d0258046449186180505504401921481a0403081b91101c00c00010400d03810600c141c0c142c1c0d01c00c07a000d22650400c0920070b0300038082407080f1648811a00010804180c00b907000c80301d0001d01ca0009460100a11041c20550b900d43c0022a507148080600c8550303903405100740c1000d0f0408440c99842c040c41c10a11840c1000040ca010701100000220307013410b0a030940c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 586375935 1250 586374685 586374707
    0x5221a06071103120307020c010c05160303170a020a0c0b13050d0f11010905061f030b10090f0c020309130f0501030f0c080d020703080706150902041a031510 69
    0x300199618206842c020b05044510700341c25001e03124400c072080b1464002c0003500d215038060f0740248811031115004569106000c035040d2494014912211282d020085005001e18001d44440f07441a0030014a618040f0000300902102c82c410f21220280990204000c0412504005040d030603480d5a24030b080c03980101e000041a07481941002c030030564201c02200f00c1c105050300c45d50580e1184248080c01e903032545500800942081d0001035414503103440d41807003803900c40554008980c5a0307542040801d0f041c2e400c494034440101080040d00b0303a901414903c220408000e100340c002d01d90380a0358078052900c0c01c2d0b02c1425003804011120820758008001035000000c00c1c441944d603400c00c1c2070100c80d81d44080c1c50503905a00e000c150850005400003d500441c0d006001a518549500c10782e41c01ca02c0007180c0305a2a041c081800185104100000d00024080107070703a240350030f0094450041c0c00c81d6100b10704074180200302d0380c4410805c203203600c05801e959502c54222000c800301d40c80010300c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 586377185 1250 586375935 586375939
    0x13030906210c08010501030609020414040915021614010e1b0f04060905062e0c0812090f1b060315011107140910150f031803170105221a 60
    0x18102440560344250f4881c12a042a00d04101d855241d241c41800d920450190380d180c81075001025071603040941c8645105030203500c1401c101c402e207840040c2687e008142110f4440c00b960407600600200c181c2d82c00c100841310008001d111103518120303403a0700303000032060302120207920111800d0302e514001c9180c440780100200b16150b1a049a40018141545c200b401000303002c0003504403010a984000e0245002e0039154101840d20504903406d07010300300100c4143d035041c420070007080520041d080c02488003e004d0190301400300d8006203450500003801070103080350b1800d45000c0d1101412a500410001da2402d40c15203901c0060720860180c0a07071018510445100045004281d0340708106440211101b21954070381c903c000c020000d06002d5102c00d0304c065060384d003080d4028081c0303400d0541281408166009102c0010381401240c44003900400caa104d5003c5d51151001ca00b5409800211000580320b03000c2020400181c200c10b4034072103e035642c0c450007070b80c840f401040300706007000c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 586378435 1250 586377185 586377191
    0x1a0d020d0804050312030f090a0213052a09040b0319110d0b090313050a0b160f120c060f050c0316120c0e01030c02010614040c0e030109110102061303090621 69
    0x25400c005c1c1040e90080b21106001010040400c20009001c07400a8030302da0014120031400e01c400d1281c100a0001910341111850703c1104660b0380c03045000314001c0001c44d04412030f113441104040c0810307100c410064a10a03040851481e0900b800c041e00d400100d82c10078a04018051002c0c0400d212010401c40600800d000d48104050382c1c0000005101c0301010101e40c1e09a030b81d03680c0a02c2003400070380c02005200700040c0306900e41e00500313030301a0a201c3e010f4201d40100c0036481e120001d1b4080c80c2280b590000c0c00c0b00940f41c0600c80503000d0300c0307080c040d407200030444d0745411506600c0502010700001d480040200c44007074901e0ac08d810380c50521500c0701e400c000c1850300c040081d017814102614a40070030304040800d0700403401880340e0740c11104030503d0042c1140300c8500f000f00802e2441100c030184031701c00108180c07a440c248600c0c14103038418200341c0311071000d00e000646031100040c080b40001c1900400c0d00e00181c1d22001c8201203d40b6804c0c510300d030314008070003a40d035029184107110281e89 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 586379685 1250 586378435 586378453
    0x4020a170a0f0b160809030412050a0c030c170a05060114180c09010f0f0806060a05040f03080301050a0506040305032709130c08010209180603030702090f07031a0d020d08040503 78
    0x10b140100b0f00e014184851070ba01e40c00b0350710030094802c20760455041d952a00140020004104610000c203041886002500c005e10225521a80c40d9010b80d002520320f02040541800340c2840803503030110009452004180a0b042c0b82d0303400b0f6850005000300080b00711007011a01c01c40d10759503071038041c04109544042c864502881080c04580161080600003060801c9055055015030036103081c0b0100c41e9954400c5540c0d12007846210750100041c1c004002040000044600c04604204042c52040c035849540e03504d01000c0140d05c2c441070300624450030040000300009000002102c221100d00d0700580601c501d503404c40d0342c0d843c0d05400002c0d004285c0130308002e80c100d840e03248040054410315040c82380170344821341d1038200c0c0110300125410844004612500422a1b42d44c541d000c1801022240342030030321f0780400d01c50801907915416070201e1005001040340c06001380e0703030304170303508a0465008030401c00090000010640080d0040e0304010106081c00030304c2c0b04642c05000050111000d90f0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 586380935 1250 586379685 586379693
    0x120602040f1502010b120c0f01050f0a080109060801290a030c03050105040b0106032013120818060a212a09120302060403120e100209130504020a170a0f 67
    0x310720403620b400194a0882c660f8418a02000301c0d01c0541e5036040100b00340c0030f0040910015001007070700203046c85414024240e0885a402c000d003000c005c50303542c0034400e5151a00e90b070243c40c1c55400060f00350f410301c041902c01c00320550346c000e004010044032101d42c600b0b003004100d00802e1900058011404000c2c00302c01d01605402180c0101d1007041101ea07140e0707803141c0807000c8418110004100b0341d409a90f03a066403001c2d0020b0002980c4070124042c800b60f55054a40d54101140402c90700400049164050a0f5030a42c903030380d0550003550600d02e080001d0078001c1c101d80c0c1135101c02c50000604000d141c0c024641d6400800484602104001810100d283c000104d03400c0f0b000035000586404400b02c1c4074804d032003842c088558142c00500315034036955415500c4800903c43c03101400d540d01014400341c841044980d00403000500c005a41c3c8030031800b80240e19100e83d003115036050800c810702c00180c55a40e500c070200d5140140c3c05020520082042d4207200540d1070241010403828820000c4c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 586382185 1250 586380935 586380959
    0xc03080d091b05150c01060504140108100e03031810050403110f03070209040807020d151b080601020a11010219110901171b060c01050f060102010b0316120602040f 72
    0x7036800b82c040078001031049940200020300780c0c0a902d400c4403520f041904141e402c0c00c00340281d080d0040000c101540c80f01c01040403104003e2205041114041c0100407400d418030610006141c07519082c411524204155903030b901c0090542004008580a465100e010600001c03109010040c1c0500240c101420018032034039138042180070902039030003a00552800082100c00c074650160002030280d6803900c4110701e070740000300c007a6086a0007a0741030740010600e6084003007030511000c2c0064100b0036500004146e01003c0007070307418000680e042c4440c580e000100c044041381e210444165403185040101d08000e1103140c0c051220303880344100c0042000b5000034003da548190f0703504d200c3d60390710101105813402e201034403c40c6400001428540140d03402090600800c05003100b480c201480038180d086a0b02111742d000f1040c400c02c2406415a420b00698100c0c101c11070042031103c45d0308490010304a054412520386440b504074603003c00c4002d070140c80003003032038206000301269600e400541c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 586383435 1250 586382185 586382201
    0x80a0e030d091103011a06030405031308011e050403020a0b0a0204090606030e060f01030305030c07030e120606040c0f021b0d121e0305040c061d040606020a050f030f160c03080d 78
    0x11283c0340c24202c0c90a403e0511400c5241180c400640c0c071403c4131881404100e5101401c15180c42c0810449400021100f00145000340314a100015914540f0417900c41c1c0a41f400300300c2009682460b090001003940014500c41c0550002c16860b05619016040c0c8002d2080340e210f181a281000700005040b40c05500c503c2c02510f150341500d034190744007a0803000042c000d010080200302d007400807800a550420103085030601c40c1c10003106c030740f92101c00115019001c01125105600060412502e03041600841c0d182c200c4606000004889540020303448001c101c0f608509000c48a2248400f5520204403101058100c40d0400100150401c024026a009901000101510141c6541e502d1087c461548a5034024407582c0d0b03040d0410804031800700d558118070b608d400c079813030715148244d42d54030503c0c1c001c1c001900102010031540c541130382040e444404194041d0002e000402c120404101151382c018a0065040c41120300c03807501501e4400c02c0c3e080504406408030391200301620a501840c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 586384685 1250 586383435 586383443
    0x61802091005010c080c0304092a090e0a0b010e1302031e010f03060f09061103090d05030411011803050610090e01092004140f0412170403080a0e030d09 67
    0x20340d07142800321011491611400307000a00c0c2072807410202d4608000380c4500c9001d0030641c0d1a2598a451480c181e50302c4442344114074080d03441d450112084001080a000d05074100b50710b6440c030307100c1c5540204c0401013034034482c83d4540c02d901840d03a00c00e030031030f001c039000c01056644074940c0000480000c0d00116008040340780558143d1400451816016048415641d101c0c4402070655846001410440312140041c9071a00c958000280c2103000b103410012445883c2610703894281202e03072030302e280d40c802e131010301c0030400502000c5a40115500e507012800c1c00c001103a008840f1074000c00e03040301e44c00500540181c000f4004242c0e103e40d90407007182c141d00000d02416255001d01c9088800c107440041040e103c0c9420408030056004039099001e600400c00264800c0d035988516031001c003166000c04401542040108100b028242c01c0c29150707140c6861140c0f01c04510444240c0c0c07030044c10240038440404001103a18540b904074400c0e10810809490303c07680080442005403510013000c80e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 586385935 1250 586384685 586384699
    0x5060709060804110402070804080f0a030f050a12090503040302134107090b0a03050603070603060e0c03091603030f0908011104060e190e10050904020d02060a0c061802 74
    0xe0301a21480c0d455000320341060001844c80340030010000207600012040360b070040e09000c001903110061081011400a03100a000c8004191400070080b0b014250f00c841400018480400300d507034040502041c211b00d10307900040d918404c0c10020329501817a840290f01032442c0310044022007490300f0010301c104090101e44094103400b510091883c4000841d841035100740500c9450100e0000c492a810901504201322059294010441164095604480032035200c40c1841403a041c10003128004140519007041428200080840c0000000c0d1081c440d5481c0400451480306085c08201a909044401600c0ea255a4600a05400d100440080102d249100005044c0c90306001d4500d50304112400300d4130349810b020055680709150744803580c100800c034203110800241c0344d400300042d10311820507100a00d0424038054410405030400350207460000107000040e114a04000d020940c1241c10588492a00d00101c404110b1140e005d0400f50a01035140c80040e8a60603021082c3e00a942c09 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 586387185 1250 586385935 586385939
    0x705040e1005130c0602070501080601081b030a140a0e031b1f3c11130e18070501050406080a0e0a21020313050d030c060606050409060503010b150c0c030a05060709 72
    0x2c6e41c460304c8034880c442c0811000000152690300c602105544142041100140c1440c2d00580399942e402c2100d8030f8001079540c61507010740381740380208180d005c126440140051030103030084a07203c0c010400d148002803865110030b05480c030706228079020000045400700c1204084038400010300060303116030303503040c8034162a05a02074685009080e819001c6a40244040d5030711400d1000341409080500380c0803061229081165070190800024161041b201c52113042860200303010191006c07000c14103502051041105903080b074241c600321026401c001709540d40d030005110140c10b2004105840d8040d501c007407800c000401c02c5500010803640700d403955483c10300c00d00760380e248190282620000380d0203001f0483b501d4110080c0141c18464079045040e115255240c4064400f16040107000c80d0010800340030707005040c440d010080c42d0403402400b410000601040c0003040480c2001010131000583c01c405d444104403040054034094226444445141401c5460311000e0f204000046d501c140c0c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 586388435 1250 586387185 586387187
    0x90201080a1406190302150a0201050c131a0f2d040828080438030f07031107080d0b0604060233011403060907080705040e1005130c06 59
    0x880e4801681d580c501090b68070f0700800c10a0000064850300402c030503420000c40113032142105950301031000102c068441181ca60701a00f5100000d0402210f10301c140301c070102d04400c230180d503011604410314001c12604071415480d182d100d40306c8600c0d0302040000314800c000f40950200780b110b0300c401c176849000a0034500004514400d03131042c0b0456a1084c9206498000c09000c0e030401038401e807a81800380c2c400760707072240260f40081e48000f44c1c0b242e88420308203d010f2000d40205100b03d0300c412600e448401c80000d503140e40009400d000a135030540000942e028042c0c0c2c84076440200d440182500c87c09c8901d07124410364400e11510540c01d003890b4603c101c80c01c0200503181a41c4090f005048070f100024054004500e1921a9501000da007600f005e503090407034807100d80a0302e00819090030741c800031800c1c1450100d011301340c0400d643c0251400c01c503005020807110203542c002c440203d8072281e141e6a503450b100320446503042d06442c0200f40001c1d880b44807503201c5041d00c0f072070f60401001c1e99030b20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 586389685 1250 586388435 586388441
    0x20301050a0905130f050304060e030303040f0f0309030203060c04050109050604120f21030f051008250b0f190503040807061d010e010c172a0c060406090201080a 71
    0x4109500700418035000d02180b06076030011507105507500e680000407881611242e040049805007902c01e40c2000906000c0181d012021034224070065004602d1030030725503561b0f22001c042c11409000d001b090305441081500c00c090382e40040d83c0050031194107050081c99200030b54001d02c107440c04500c41d0400050301d0b0904101b40e6003207404114859240000340e489002d804089420100d400b40303403268990903039511402158504010701d41d00003609100701c803006400c89101414142c900b107036010342008600c10005518403a4114a402540d010000b151600c1c42c10780320790400f00d009080880c0b03a000c40460a400780000c03c142064209503a640d1a0058410381f000740c1d4094034204042001c0000300340c036900107210440708804401528036040003d0f41c00c5904a48482c0c880e0b945601c45414141e6010550940b000312103140c1c0342036820080c059418110080e04001c419040750600740c2c4c125070120050759540307080745040d144549440e2600000030012414128041010100070505103102d81c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 586390935 1250 586389685 586389689
    0x1b01052a07030e0307031703010f060302091302090118080f19030e04020a0e041509051602070e060d050706050a0201141314070513140a11030a0f11040b030415020301 73
    0x200c0d0301e400301944049481945a0ba1202c1e014465511700000151800200000b4002d2040c1c41c95102e504040380d030a4180350300d9200c0410180140408081a601c81714030b43c4042050640050f0340303404090050791403810424030b01100078041500000c00310404030b8400e035540052810b40d0341044010040b0040110804000713400118550001881400c00c2d0340184003140e0745040c5401c02025004c0010107503034040b44016442c0a0f00a0108514141c5008464004004a03a1501c080691100c001d40d9502d903407058900400469002c5000f075240c0090761040150041c041c0c406036a00c3c0d0402a00981c42515041c0c015880c005600c1c2480180c0b04846018034032140300c2c5424010305881d1580101400f4149070b1450007244000210f0b641c80040d116034002102102050015540c0d16a01d003c5a0082c2a0340c10141441240000c4030005070889074050038543c00001c0020311840702b200140800002101c498400043c0031404403500405544258803d80703400035460000449082640800c8c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 586392185 1250 586390935 586391011
    0x30a0906110705060406020d02060105030f1510050a0b040303020c0108070e0d050f0105091e060412050f09090109090203061e0610020c0a0605070c0801061202151b0105 74
    0x19800900440d481040d19034040402207080b9514240c5500c00540941c0c0b16074824070240c1d2080c0d40100303a168060100034018481200030b09100e402030075140c1c4d02c0e442c4103076941401203a4580020540ca140403d414082c00000d0a500d00c1c0640342c8040041682c090700041d00580314404101040d07610911043c2d1262102d80d50b100080300035030003445206100701408130b039075000d03074a02c21401c1c4009206151284901000802d11022200640d0030400300c004c00340070040c0c12100030000402c031403060302c0030410302e645000c60740ca5a41502c804150302032844015030041e515000010340c042e05810030040700d4000c5041c0d60142d141c12047d0152020360b4098183c064000c0400103500b0b1801c1a01810849518010b49802107102000103c02c1c8565410441c04143d0100301e510500008405400240c41020020480c0e941002606440598804402486000d5001085006980d007101361581011000c0507100c444c0c803c00004c602800040b070f25180800c1044031a85031410030158641d01e44071030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 586393435 1250 586392185 586392197
    0x12050402031506010c0b04030906140c060115050d020c0714090403120209030c0307031203142e1d0f070f121d0303040f0507060c11010806040b0a0909020f0102030a 72
    0x418030012010b01005199a050042c08000380010a00000c4414401c0b4400e03510711700c0c0d5604029000d400e030700300c400c1d01c40c0c007240050000240c41040005d2640c1514000e41c0e9402c1e40800a4000f16564810304660045103030020400b9403424000158800544402c1c0c404592071012010a01242003011200540020740703035841d240b40000241d00070080c2c030a0150940300e01244100100389070580540c411036400c84400501050710341d25101e50701c02c0d0014110705000ca418035404180e1154401c4880c02090b0070a07054080350b58484100300070040020b16020b203440c148980300640d544408440920b04030201d40300040f5040e106504c202d1064100c1d858003607045040f101c1d41c000a0000061041004074400d401e000080c0c0304001540c45540700e0011211417504919109040486690100381485000b240c0000083c1000041c548030b80e400f03280c41d0031940e44002c0014060035442e428550403518014011680c0629600020030072030003600d00c034404d600082d004a9032403084005620009107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 586394685 1250 586393435 586393453
    0x1101110a051812160806090606010207060809150a050a0b030705060703031d06010e091605090402040c030609020c461401020f030f090c090c0a0c0614071205040203 72
    0x31816010b1505101d0107040340f00c03d05101400246888020748002065440b41d090400541d04108480d580c460004c002400a5082010010f55a40d045001d4201800310b0100086e8a281082002403810103c2502c007030214280405402c00514054840e1141079080008801c480d080004944040b20b50291006103002020b4400b01e00600b000d0008130740100358603445049105080181c24040d2a05c00328030200303410710300c51603490704000e01c54850100c100e000c1c0402c00f80c1ea80c0a007603a80b00d80c040e6008510400300740000c0b0010284ca03080300c00b40b41e1000c1400003429000084008440340900c0503d010300c0d01d69004d0907054048102807044541a00781c00030004031046c0480030031248100c0c640150315508560386030030780c1c20913622140060004020000b440c1c4c01103804541114450019080b0b210a0070040360005500130400f02d40c100000810382d098034801e100d039145060300300804200500e00380303054070034404007507410b00f0008143d031044406a404501c2110b000e81d600500400c003d42e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 586395935 1250 586394685 586394707
    0x711060c160203010c0203120109050f04030c11120c2106060d0311150a05010b07200f060d050703060e070f1b0206030406050709090207030c0b0c0405101101110a05 72
    0x192103031405841001c00e1a12040068809015120300d020703094001d503850384140e42005000c044e050703104003041070130038080c03081201041401d550441d40500d409030510750281805545441005000e5801407101000b440c001c0d0b202056040d006041225104c0d50340c1c1d500026885100050944c6010a0700070802040a610700711500030701c180e229051004001d0712202c1c203141490500c0d42403601c5404040100001082c052040c00d01400b030144850b41049034a0f142c504d081414501c001c410a0980400001542d40b04e000c24550789800a0560360744414000030440681020364822000c2401c22402159403180c003410603200750070f1590303200e828007900d00b811960240c2000e00a040d0b10342c00582007016884250007544540c4c020440810a81000302e03008000c018541c5c05040000c3c418840040003c0e4003645640119030002c1e0120f03107588907800391741c245204560010342c0c0105280c40d1080c90542080c414218601940020400011080700600d0b0f40d1283d000183c0001d203003080401402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 586397185 1250 586395935 586395937
    0x815040201020a0b090a1b03110f0a05060414040c031e050408253503090102090402070c03172a071a070618080909041e0f02090711060c 60
    0x824014412260100420f07101d0b20f12055068602034220303000f080c00d1704288584d00189014030000301288000092031902c1c1c41c140141008207241c8101c09402100300207030348200440c000b43c04c005021564803503451800d170040500101d0060301032404e1510300000c00d8000c5c8a5030750180302c50f444a1320845040d4a02d41e00401c6d0040c0b084984030b030107001c503458a078107a2100160010200c204800000918100680c0c006082030301c10700041c0380c000d280d420a0117821881084a454030329055200e4907400c0d0321501a024001c1810342281c404100300c4103000ca0a150300c01100c1c09602103d015411070840f00301c1900c20001e40010b1410302d952000c02134021180d0440390071810744151881c068070303015440720500c3c1c0368084808010700402d5030024404640f00b04641e2810100e075400e900e400583d81e20900b8083c0612030b5109407540300002d824803400701031460100075071600074003000390030340f40c1803015401c0f41d04140d00a042c1c0e40f0001d01c10354024541c2c1542d408100000b4a81966008440529 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 586398435 1250 586397185 586397191
    0x6030b01050613271b0e01050f04030f0b180c0d03050705150412090b1602090717010803030f1e04170c0f010f05160806040b0f1f0f05040815 62
    0x108034a9401c0010f081e9501502ca0529a0001c82d40700750008610013011341a158100201640c02d1144007a0b0034001d904002443c1038444282882030f02e9800f10602e40d20140a250b0014055960036040d9908104244051038440e510380400c039884030700381039103140c2e59109001c4d20580240b6100e8040000c0380c02040a082403501c52011a080c1e160741d140741c00d401d0300c010f540465064142e15220000550003410b80800f500710000c0181c185283c110404401b07007985c3c01d01a014400c1c90010030303a411b01c01d00c4d200d02c540d0141042c0025035659410026aa1350088031580c0e050360014020500c1152001c0840d550300b01c81030460400c80e122074850310b110855040c1208500750041080701c04019041c03040d50b03032462021000207801c25128580e0001d07501c0040001c01d0b402c0103441300e0b980030303500000318940042043d00c00103640d0560078081080360b60b02c0112a61f000d83d0131010640c07100105910030b0b58460035991058a0051a880c080e42c041c01035004003001c03904402400300100520a070910381c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 586399685 1250 586398435 586398457
    0xc0803010e0c07021806010f0314010e07030e1603030201050c040b07060b01030b1e100804050a06020d02160b04060606090b040308030402061603081602060103170d140115080a06030b010506 83
    0x460704083d43d001641d44440d60003105034140c2180e040050b15038020f49094402d2043d0304041c0242d480145051414220500400191841500c00705844500c82c0d80012181d800500c111102054a0080b1190940007440210b0056003402c000449240100c0309a41c21141e4420a60741070580c5030742c0790005002510001410541da440e9106c00c40d540d2544445980e003442803440d00001040c000707120107441c3c6101c000b000d005a100c240000290001860f41041d0f400c01c00050710340210000d0100640b140f000f80c0700002d50018080024000f400c02070b1801140b247c8010090346642e81c0c4180d4288005c2e12400413542420303c010404100c3c0f131001140d03c0392000300307000d10341889030f50a00003003900341c4400da00060030841005480b000f1f101e001d482c0300446000601d4658910307034401d03042e8450200f000c04c03c114086501994855a9048242005c0b0846075038005d079030311201100c81440032001c6010022b0440f03004503da0100d84d11404c2c0c03c1e42d8108091304c003180c0c00c21050121690124030581 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 586400935 1250 586399685 586399687
    0x21040801230621030d06081c020607120b0d030f1b0309050d0c12060203040201120218010c050a02041103060a12210504030816020111010e06011e0806090d0f0c0803010e0c 75
    0x2c043c0441400207001108101d600011000e06094105191001da041c0090890702001c001ea18101e0700001d0300350b4042602e10b050f4901c0010719050304040c1030340c1400650040c403815000010140c120090007690740f075036610b00d0422805182c440c1d80b5503035030640250104610002c10311030390400070b00200c95540204200f070740c41c07aa545c1e0300c82132000444c0b01c2a56280d03404400e000c05c56a01941c0c540e0400008001541000c00402080ca40e03201c0116100d81441400d06882041040c103000c0c107000d003a00144200070864450400260341d41c42160341c0c51194209805c089142c0602484001141d9003145244210246c1d103003501d41101e48a0b0603010a00c0814400000090b021000030070342102c0c81403100c10141c600e4030004d0040f1400c098203030030f182d04088180c2014440052031604403a07210f1090100c1c02500039a008003003407903422800180c001d00c000c0020b0a00d00044a06500d642a03451403072085011604550100328004000c048003c10001041a43c540c8484039802490f003030031403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 586402185 1250 586400935 586400989
    0xb010b0f0f070503040f050901060e06031005041409060117060103080f1306021005060402070506060f0402092e020a12030b01090906030f030e1c14210408012306 71
    0x96000c542002c2011181c691000800744050900012808020802130b0f5004143c2c0d410944007429202d07038164481c0c0070f044088005100543c810174a24010030b0060070400c020100380c3c00074448924101c50900040c841c1800003d403000300d4644005801482c20043d0480340d00390b5135081c441780d10046003100c5000052140036030862110603e140280201c0d002000044002a422015510001c1946108910500c00400807410100385507900c44000c0340c2000c0c0082c18400003400070b02843c8002500310440302a2403440e043d10690a0104449109280c03c030350000c0c1004a030f076200c0802d40101038402144561034924000e411210040300141803c0c80020348400312041281c40951042e00d2031051068480e00740360300500040030baa0410790707080c4c03889520191807079234425036620002c0403501c403403500e1f0003501c02c1440481d840811070928080d0288043c80700a409401a0107520f2a5518008010a400d4030200d04101c5403030303403440310401a0391035400700815030191016401c00d00340f41c4598 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 586403435 1250 586402185 586402207
    0x2060c0a0c0c0b190e0301060b0712090b0d060609050306060d020d0309120c060f110303010b22080604050609011503080a18091a040207051e0f010912030e0a0b010b0f 73
    0x54000d1301d075407510f641440340c1d841200510070420040c50034004c0c0d250881c280003000525088171100ca4000c05840001b1412010440324042241c0c0086000840880c00503482811500040d00f280d54682d0360700002d81e100c1d4201900ca0b801503d0b05940304403d40c0400c2d005082c504500103c00d400b0703083c440102ca40d14142100803841e218001c4030305030003105d814041380d900032003000726201380c1e032504c101d03485d45540500b40d0320b120601030340701c03030f410080355030a00c0018072103440c0d1100d00c1e041e07030340070005a86100440e40c850058500b00e0b45402128005100540144101ea40050802e01c00b8403961340782d600c1b902410f5004020a508001c0c00d80710106403200b00c0d0403c03600401c05400005803100900840552845000c4c0459206038010081e000c0810000140c403500004600241c0c00e07020340343d05195213819582c111544407542031008400602c081584041d01d00c02841c2c40601080f86400140ba0b166544040c0c024201d0001c40010320904906002400d1500700c00700c015031520b058041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 586404685 1250 586403435 586403437
    0xb060409020a080412050910030515040f02040603061d1603090b090f0601060c2a230f09010509180c0a08030d110316030c0e04180c050102060c0a0c0c0b 67
    0x105004240c03000c00784800c2085004046114886a11b0b005040407010703000a108682c00d01036038420503840b03c2c0892451540069040707000c4000510801c4400b4003111410301940183c8200b00109281c0000001c003c1c2c007401c01d80100500c20310318898256140346100070300da85501200c1d400c05940e540c03148001141441c060b405000800d0050003101c8007107014510b0041d05030407403030400407820300590014503008002540009244038039038000c2580185861001d00e261b00c02022041c2c203145028100c0d02d0b21004444103402518143d91500c0c0c2da00610000030700a20401c2d40014184000640c0c0d113032070859881c000d1060b201518400880c110001d201510140c110685603000018503d0203445140b26001c3e81c3c41c07609003500d00703524004074051064002c0c000300c00e042c1034462000c0408248150440500800e00500420120f80c0000c0740b4420a80c5850003140c241400aa01050b0756000180262082c81402032851418440110440e06c803810b00380102d400c0320000502007140d102d00c00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 586405935 1250 586404685 586404697
    0xb071203061a07060b060901020a060e1002072019030624080d030b0330120f09010e0a0507090207020d0204050405031c0c02072d0f14090f06040b06040902 68
    0x2d040c151906140e080030412151890142c3d0302c540801c00c60000c850342c01050303030003140f50485d4000580c004a00041d42c20301d09007240003603106100045071410001d81c0340100981c402c58409a0401c00d038078100348a6601c81e81843c407402aa4140c004000180194008102503003160b000c0100350410312040040b508980d401c401103075004404070412150b13051160180b03c0c4403c90050010f1045802344003c4010500e1540c450441d01c4290058600584002c462140301a9280400c992815198512200d14107a5a4070b8055007000414036000b50300044645000d50040d02801085150000e100c001b54001c142c100d8004100464480160361184079052140c0d0080c4040e560b40c8402000302e150b0121044004810f041c501f521021101d9800615a0705039541022240b02c02c00d100c0b0103400d1161410742010701d4020031558042014210350400c4002c444801640103020441c60b0b081168584d81116440c074118410303070000d4424585500040052800074015500d00350326040418242d900407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 586407185 1250 586405935 586405979
    0x30604150e0613050c071205072a05060307171b030406090605011e0302060d02120403020c1212160303060815011a07030c0f0303152d0b07120306 64
    0x1a02080b40e07905000b1038542040c007140034200400e240003030409510f8003496601031310109480301c0c42c0b6000c0f80101c00710f03440550040d4401040189103095040b501c48041058252400028000280b500301001a2801420243c5480d4010700002c1804443c0c0c100080060700020452517048110798010ae00540c0141d00034040070030085a50300384107043d100180d00401c9240e80c100125000c002ca5442c40e9819241d04480680c3c0e110016030002c1d01900516400b12045c0340c0d403500340010540c000071004221941590224502d4600d5042c4a8a40200c8000049508401c001021040c403c2c04101c9a940348241000500c40762108181072034040307100307a101c500c02c030180010b0015022000d040690740c48400340003450301c0485d40c0d0050071124006001000141c4c1e582e5488209400303074220030741d59034030000005029036076000d02d400710f00c006e018400892003860f850401a01400480281070340c0c20400d002e441e09000340c1e1428042ca80018580c0c0c01c0565034240070442d40f0300040491031110312 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 586408435 1250 586407185 586407209
    0x42403050615030a1716021e152127070f080705010c290c0a03140f01180b0a03030e01030b040c0e190e0705130e041703060415 56
    0x850300356214940e039a010383c403d5100c26401400a0300507141800800d80d206041619101c0f40c081d0502c907801c0c88100258051500e0740e0a181840d42caa0000003055402c8500040d0300004001455440c0b0800074058080600b20030b40812002c00c0065003500541c0e9000c9444030801e0404240c0580c2000380484000c40d001114104480500c0c888a00058080c0d0800f0f8003000d842c090001c0d290482000c1e00500000014094150442c0c400081042d20050401503031650f2409185000480e07000543c5080070a183c60741d00010b1440382180240300d05440c81c4000d05c2c45c2d0070011190406628402450040c1e0348842e281c500b240c07641035444000390310940350301c4040003403e0005020340741030480140c000c904d0541001304030b90340600300341c2c0084c409544140d41c003010030030b5010200c0211340068801442000a02846903403010050100700c1800c07411421950b02e0780e602c081141400c1e44c015244210305506841c99803000c89c011030300720341700801c0083c1c4902140d1001d107042c2d0460b40300d107844a42c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 586409685 1250 586408435 586408441
    0x70515010f23090702010b0d050105061206090705012d0906090e071d0303130e0126060a1512150e0c03030409110912010e1009020303090424030506 65
    0x285034200ca8050540c0d0b03108880703010521481e4140207400031055900c00d44a20380421011030003948440e0a8960150141c1d41020351400d00398081c1200340c420ba40900c40c4201400c40ba01c0340419031902a03001c00b009090034920b00801180e0105240409021600d24181b540300c00c98850054603c020301183c4500145030f240c0f2801030194807565200070403610115040108095001d81c40c0c880c04c000e0031803881600f10300ea10100385940101c1c4608494542d5400000c501b5065500445049170300405941001c2600d6102c0f60898210380e41c031414240d44050049100840d141d00404e240c69802c402282500365145000415000c002c3c4c0c0640d01100c0014001041034114042c202142a8280c000d240040c1c4400100c1e940784928415107001960b21301c54242c000100c0811203185120080810308086036a803810350003040c0000b009c1500d0311034030507039858010060007807402d41ca400034042c0d420a06c00030f05100c064100300d1205000c3d450020080c50034074456030076581c0994000c5004141c146 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 586410935 1250 586409685 586409699
    0x303191e08011a04030b0f190e03041503020a02102307030c0815010f1d0603070518010e1c020d0210021b180106110c0d0f0b0f04050309010e0607051501 67
    0x14420048200c03180d01080141701080350541c1003078115130500780e040e0070380e5280b803001120101d502008524071402d00400c10084034000000e44180c03019001490216400e1050980c22481582c1c0c4003405600010b000c002801105e03809580c850360f800120345000040e180c1c4142001400301c03840001b19a48a070202680c40d404441c01c0ea1140700c100b00c04001120410000e0000240c0c04501800c1100103901d04860011003119800741500c0602115124107040c40301500c0c0e50070407000190062480d07610541e06600c1020b8950440c13501909103403e040680c2400c0101d9410044180c0e0040202041070005031604506480b01081e1765010780340c000c0745100c1400c100007030354808602c12205a004001c2e01204c41081e14110f54050520b400c410450b291802d05000b801803c003540000c0700c5549200740441d01280b00c10480c400c2150f02c0071551640c21070036407000c01b642d01901030345c800d20180c1200e50040c1001030386494000e00a0782040704581c1c0b000d180400040740c443c00e01040d680100140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 586412185 1250 586410935 586410959
    0x220614060a06080a0e031e071202011a010e060c0607030b0f0d02030627030403060615020f0c01080723071412180609030609010c020c0a03020303191e0801 68
    0xc044480d4410a441c0c041c0003420044003400d8801a1070341c500903440ca00204004552240d201070b02d040000228042c0480c0064001d04015148507001c001e0702e40c502441803051078844070b00d8080b40f4032503134045801141c001c0c2e1140e1a268001404202c04221a90200020f80c42222541c1d0041aa00c140c00c051043d1040042c3c2004d00900c0b109001c040140d0340070500da5448400c020030b212000800034174800422404545414182c04000b40200a10226410000581d040d89280e01507510391441c0c1281d440845143e881d1551301b120b03091030300a6210325000381d0042140d14080c4103003940222018080484650740781091440003640c0c1040000483c03070340c1c0c1840080c2000d062684580c500c00b4485d840340064020160559480c0c0503616511001030790015080030341105c00b5860140300ca0740c020a41c0581d034001603c90782c400b58a491a25528004c1660381c06000ba6082800c1814090801104602c4120502402402d0030454100d0b000500780600d2403a9551405545010822428 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 586413435 1250 586412185 586412191
    0x5160503010b0f0d1520030a0501150203190e03031803121c0b0301021902010b040b060a09030b0604091a040b07030207231f0c080603030a020c0108220614 68
    0x142c1c4043c28402159075024980d11110390415803405086440c450450020000c060740d0390b000c1c03401c11802c0100c94042001462140301101c2c03007046aa40c8440180e50450040311210005a10420081d400054042010350518000c2d0804040c0c0c041c007070000034107542100b41c14400009020050200500d410024030440e5191010141d181010f03142c46001e290344554285170620b502c1d80f60461040e02d0940c1201c0000c1a041c0d0000d400d0411264002e000e800c0d9401c660f07220707900b040441e02c0035191a5089602e4241180c03682c0e50458910b5503500720303600c00180b07100c0d0302a944402c21400300d290061161160126141440319525181c5080c01d02c1100140486041502c144540300c0041c64120019582d00701c000c031002d0060340808001450070561403210011001c2e0228000401041074009880c82941621001030030741d540000d040d501d0182c07d000c040180e20442040100354080c10b41d0079004115840c9602c3c101607840078103000099400002c40701d05a45007084510980c40d40d00080e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 586414685 1250 586413435 586413439
    0xf1407060c1704050a05060c0a050d2606030d2a051c0807050d0b1314090c0105030c07061806020c070e15030705090709090504080d0b09280905160503010b 68
    0x106284c20f02d000306810030510301906014003400a1002c403042c0e410840720707058960100032605c0c900c210103c0200811196100f103203000b007110045003a450800100039116410240007051003110025003122003495141c249050f5040501c8000b000311605500f0090786800b420040188051141f06040140300d416220802c2002c1c03002840f81c039580c0710f01142d03039114a204002c591b462542000551140c10140f140081c203141803180a0f81d2188010017510411100e410327601d0341c0c0e0701e440056070345210880c1d61043d42c02d42002002c0000700d0903406503d80010707031030804030b01c010695a40002c903404200309690383d501059080041c2c404d002462a440800c00340b0103040c078a40341d004641d4600c10750003441c1c0701d0441440051341c4c0e10311440c0302c08014a4803030014401e60801c0c1c101126254809090002881d040008400313903030600081641c003d201b444c440001c0207039002c1c010401d001000c400f00c2c5586d5110804000400c80130090011720740d4100e0075480b2a6480e060400d821250030b0f0a81034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 586415935 1250 586414685 586414687
    0x31311061b0d08070927020d02030406090314090117090a080d1416020d030f0e03040b0705070504020405091305100e011b032702030c0907021e010212040f1407060c17 73
    0xc45940c42e80c0316035400046e80c0b00403504c403d041c064242400380c003805c2c5408104900c040108000e1044907007005400a00030703103d070a444110f1003003070103080c415505840d000c201660342200f0624840070349554884880800d035080d00311199075510950340f0038641c0143c91390b00c0c2e40000c481086400111074210543d150241520b9048010103501d40400c20058024103a5850b803580003402c140c0c0015454501d81020340703a0f101d41700c0c020341100b40c000d45815030b55807048010100301030929100700e0f001d48000616035442030b13072030210010300d988004500320b80310f01600c90224100100f500130107000440c0b07000041424120500d00903981510f098244080504200d10071389003080100c0140380350440420b036408952003d0010a10b41040300100030f401107501e900b00072855a01241c09e50b022802408101c0c0d6015201051500b41d0240c5100d41500c2c0c0030200c04500000c0d0440c10524045101d2503945400401d0400000d041c40865446030000c18480e40d42d5a00700503042c80301901040c1d01003911 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 586417185 1250 586415935 586415939
    0x11401120305030711030c01090b010e07050f0d020d180303140402131a1003020a020601060f082205060103080414190509100305011a040b0105031311061b0d080709 72
    0x415040c0d400c080014082c850000701040c070b4503210b6041c00992407401e000b10b980d281e1030300c034030345008251009042d50030b00c440400116040e0f82201b0101d000e49110b907103090a0070a001c48098481c2d00c800e0200d1152942041000280d107010f029055a0148039000082c09246034200030707080d213161a510301a560500300c10000166203000d048940129415000120724800d032100c860146c0368180310640c021001d0703104508455042e00182814801c55082c0c3c0c005036650390f010358400810740003100110f80003600040c2600000009040300d90304000d41410781d100340c2d840c0c05081c96405c1c0c20071346824400150034400415502c029032400a41640e502807820a0f90786d04e4000d00072507000d218031410486000c601000f9020214030003660b00440204405040d01d40b00d16280c034030850a640c01942031400c0003903190b0107882645e1241e141c06100f400781f14441c0d07849040c80780111084542c4140700b401031190750350141890600c1480030a00400110b40c80103005007034000010400c20401c02e983c402 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 586418435 1250 586417185 586417199
    0x30a112b0e0301091a07030608030f07030f090812031b16031d18070c150b0a0b0f19030f060f0f05030303010503210702040c1e020318060c0c15040305011401 69
    0x5d06846920312440d240b629212598220301514155120f40c41510000c203084600c0d841400050000900c03036281d40c1c080c030300d0001d420b032080282403141d48143c0d082900c3c08040d44c40d441e0010b55206082d212005400c02004000c01c485800c0040d80384014618030f4122001c00d5003108a9101e9014040c680d1340107024000001b440c40210308103041002460100422816030088800400f907070b40c4040100c0994090040e4180281900f00c1c505100d940300d0740c000254061201d0440d01a038613414003091401410720361030030003101c2d020a5030003003655858503104810103e20842d0302501d03510300c515101d14500b40625000380c0503034006604c00d030020001004940e50000c0d600050400a0043c0e040d0082074009205550003074803000313500907082210b00345107142c0c0440b1101c1c140c20106e001c11201481e41070101d0342c82c0151510501300d42d0664030b600780340d49401d4010346640c01c20803003100d0310800c03c140401d80c240c2007a01e0750400450080760500801c00e003030182003112900200700c2c0d00550b141001d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 586419685 1250 586418435 586418453
    0x120318011803031d270a050708040605250201020409200a0807050d0c0f17070e1207091503050d050a0e01210c050306040c020f030a112b0e030109 64
    0xc40102400140d0003c114080741100c0c541c0841c0c68004c020008005000b01170300d00320400b419081d04601031120004030b070000c01d0b1143c2c501075000b96a038225640d449079510700041c00050150700139400c010040b5280d030040380424a010000a46c00036071070303601d0400040309079013581201c0c12112203074008410460400b203094032184260740c81c218044d501c07180c0f0152514450b0400896070356040040e2001510b4100d0b04003101c1d081150744034113a0204c1200e0503010890203680403400120444640001e618000708030240c03401e130900607901c148c0c1c2d0b034081c4041200d00326111803900b000068020000d00c070061003418000c58540c24514504010b01d800244082e0600c0007039810b010000a803d94104000c42142c0520180410100a8070b50b0a10300274015400486030a072049091104810300144007185901107044180700460500d01c408030286d07035a00010710080c0300c61045a42640702c00e20740d81000481065011a0f590046400c144010100301c44140d241d0301036030424038000000790080c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 586420935 1250 586419685 586419689
    0x151a0c0d030c0912050109020f580c0602060405032203060504060603020a15090905061206160f0504050f040b030f070306140105100f08060f1203180118 67
    0x1c6400100d501c00c1e4071094a800c400e030341007610301e03610044190702045015400060302c1380c001c8403120102c420380d400708640f80744600341c00f0085035504030400b000c190342d07510001c4480c20355440d40c24a5042d420b140c81c06442c0050710980314a5244814141800340800641c00500703998805021103190544580b60359107d9292001c045070810210040101c8050700a10091944110144018201030502c0c4000e0103203400107903c80c18403044001000440400c400134000103a45844400b245040c0700c080081134020030301d98112003c58a40a8160310900c0100d1099110301c2c0030948508148000a11540e0b48103154414008100014041c9640b42c0f800341010070b00484010542c0c46404012038209400401d43d1046407203449004001c00409400c445070840c11481003803175680c0e075102085214400c9018000210309101c83c044000ca1040400f0b5a20010141032034026a4076040810044010086444610780000c12810302c03840c1440301081d001e410901e04010511424011050901098 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 586422185 1250 586420935 586420937
    0x20304060c05150403030507021606120513021503091504031407030309140a0302012306190b0f18032e0b0402040f0806100308030127151a0c0d 63
    0x2201e0410200101001200c07041c0003485249080c0f42080e1a0240180c001550f046004d801460401107031480100c07040c1c8101d800350380d90b403504403483d02555002442c01501101200c07040018242c0035880e1000012000b10308040b0282c3d591510030384603800c14621580458070f60700c1405c103010100c1d51022016129031810b010703a60b5039900500d000c2c3c0040041d0080203180c810081140c0d001d02102140310075040e070081e0000e1140c01c0048600c81c2002600d400b00c42420716100011840b1070401070a5104418580080c81c0c5800b84c98101066141e000145441c00320400010044c05900c90794144200c4c000c0c0c00d07402032004116000b10321003008000000c0c0607403402e0104a10100c02d04075000b050309030001401c07c540c0d854445d40c0c90036441c3c550307003c1c035100341c4540400b01d000070340302c4c0552030112a00051802e0959081c030302605943c4500c826055003028003d0710108000c41c007885800d1032410340d00f0300507103910300d0080e0143c40d550440c103040b50780c80d1080c4180080048017150041000000d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 586423435 1250 586422185 586422197
    0x3080f0105100f02011b1119051e07031a010513050f040204150e0f09011d210708030f06031c021002160b090a0b060406230402090d0b0f0112020102030406 68
    0x2c0b10404900401151400e03498807503071b18001145e06a0400a0303500c03e4070b042e8081c0c0e1202550700e08030b40714503600e005005002d944407010b121500030319a40701e005044c1c510415520520f44d030f5195064080d20454030000c00505400c010401e130704e003080340c1914012000700c06214074036109580500c515402000079004036101c1c0c490704a86c0704c00c640740700301910448040c288a0b0912031103030001c41c10221407440540d031814090b200389107800590b4030201000310000307240108941000c0815005200400703141c1c100c050001c040007803a41303c00345224200c00c6182c000907103012400c041c0740440c8100d4080c1543d0700c0034007204c1c282e40d0100c0c5140009204d168090f03540c88280c3ca0341181e9111941d0050310304103910040c8144580082064a2070038003039000b02c940e940700e40041104981c2d0300d10507400c42d00c204101000d10342000c9840c0b06001c1c0001000182003292400206003061058507003220210b191500700b1008840481405001d420806510f04d800b00c441d50010b035403442a40290818041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 586424685 1250 586423435 586423457
    0xe0a0902030a020d080f0703030f0c020c03071401020a06020c030d0c0e011d030f06010303170105030c131e020d090203070e041713090903030c1d100e04021303080703080f010510 78
    0x1030340c0040303403543e81c0041b1055995410a04004000345001c007119160310b414404004020340c030000f64842075071001230282180a14008441404039242c5240b1810350180b403160301d000c141544050110040d452014556942600c7c03a503034120b5400d03030818030a0000600381c02d009a61701c000999081411104c500100d5240c8000091619040500c003030302901c26400084200342e8482401d0506420941c0d8402690341c03500101074441d500310045c0b680000842c50450800020f075040030300c0c414403000c070051741c0300150440c90313050b64000c112040300d05444044000860900f04011070081405890601007428250b0302e5414100c891014000c0080d004501c0c0c14000c03541e001030305c00404000c1001c10516400b0300e00500a488180c0719000400c2407100d1b40c282c02540b0009c0a0b8107840700070701c9100c032800d0910040d21b80c5541c00413061b40080d801c1c80f4845500920341d90203000b4500640890741c50b02020301d801400c8410003450b40c1e01805240300104995295400c0d003448021450800c161000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 586425935 1250 586424685 586424693
    0xc0e040b030a0f03050405090f04030804030c02040e0703050618060c0409020a09090c09150302190f02010e160801060623070812040b01060801081204031b0506130e0a0902030a020d 79
    0x5410700c00103040d0f010038500d52010980c00c10010022990306881d5101c1c556100008150b11450032100540821100400100000c0c80780d08038541044c8028400600003040c001c110745448960f400807149a4891818445454522000111518980b500420440c0790942d15840c40e40254450311003025004100608001d000e00b00080261244050401c040040d007500104440d446204808414012460101c01903220703000310340701400204491030003000080d03812110181c9462413403045540e14a030320640c1c64024040c60318a909501d410728205801c084010b400c48115500c201c007070100100c0700309040e6540f04000083d074011480d21380c4d204c3c04c0a05000c0b505210b00300c502e0300e03401d00710803c000c1000b000c1c0000b94169101d41da285000c5a899443c80c9584543c040500408401c0a00017000000c41d268036480940f10080044146595a14086039458002c0141c4510110700d4600034450150004081580413000340f00a115091017078002c02e4980c111018007034040c04000340b07500700340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 586427185 1250 586425935 586425943
    0x703350a03110a090617010608060108100b0a020604050712030f05070c0905090f060f0705070b09010b0405040309090e07030c0e0604240f050d024b130c0e040b03 71
    0xb50b074000da40e6a60f24010050001e061403c035004030804120300741140b4500880441003141600d20545417a021038880c0c000543e40084014015400e90014850214001c01c010300074000c01c0d001ea400030b11450905181a038146200ca07000110020003c81030240442e03805000880c50408130304001c0d0341c402c005d040c00400c1c11107a40001ca60103080c501405408040040c204101045600a442d4640c4441480324421017094030719400160044c041c42c7e02050742c840c12f0b950045001c00000800a031408040741c255a400c4401f50007154188070204014480c03405000700326119507015198181c2980d413001d4001c40f540c003a11014201180010700b084c0c03a40d600a00c0c0c2130660144100c1d0141d0600c8580d214441140105009262803620004903402c1821114070308960041005903e441e04121352071500c054655580700001c0c590648102640050071400f801c82e00d000a6245641044020701543d054180f01c4800617a19001c0301e45481544241e4030f00c1c61440480700030074140c1c04000020700d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 586428435 1250 586427185 586427201
    0x1203090b18180f34090e0c13290306180103051c0908100207020307230a1203020604020f030c04050a020a09080706120203040816050703350a03 63
    0x40141e48480c400b00b0403003940c8034458009200404081c2d40d0341040761044511416844120141803440c50801c4034000c1c10710403415005180c2804483e82c0d9881014115a080d9003201c1b80b01400030704660418842c400603006860840d224006008010081a080360304032000202c00c00b0021020078019a90b84a4924840350500c4084a507541c50b8144580c8400701da0203600310351050003850107c040e00a042500403505101c010301403808180701d1400180d030000c02d0899250080080100b081559860016240c030f040141c1562071032100000d0150701c0c1095000700401b41c1c01041c00c900040e1780041e40b0341d409541aa042d0008020308000703e440c0031401241258420304007000c001d407448250f8040c080715405680e8021005923159083c1c0d8480c4000e000307c1c03001079421418903410178000e40046410520500401c1d1509465240f210a503091885044075144c005110400c140211f4800f10300170800002801c0c1e42444140804040501502450100c0c0d84000f02d80503080c41c1c001c0c3d10600c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 586429685 1250 586428435 586428439
    0x906090918050a050c040c0c0f0206130f060203090301050f042001090b0d0911060702061219060305010c090905060f0d110303030f0108070e070e0618041104050a1203090b18 76
    0xa85a03c95280080c0ca45040710701c0d40b40a2441c0580301d03943c0520406090481e55007110b20840c2c035564580078000e503940001090f01c0c690307040060014020240301c3c1003000800407503000d16141c510140815082d20307000350801814140303076402d1001080b0101f4640e41c0c81000f0088003203100c2608001038440c0d002c070b6880361420081c0402c044101440941021041c00e03c40d403e400f508002e1502080081d009010000c0e400c600c0500002907949824000140c0108440744009103861051001c002a03d4282d002252280d440d00c0360600d607250408440006032580c401e050005141c0100817843c01c0103101c09080c81052008801c800b400504c85800081c410080c041e680e86e0b1821006035400c000080c8a02c0d0201e100c0e11400066594a1461040c0200c001d543c0c0c00902c40300c800300300040307038000221107941c0c0328840904400a0b036480c0310702c44190765803511040c0c44510380401c214507001d20b036018110704043c400b42440040d601888490560f40c2c003110321501d0340044610b9010495581000c99 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 586430935 1250 586429685 586429693
    0xf040b1510050a1e0504030215032503110307030e0c03011b14042606070513060c0317160e150d15030c0909200915120102030c030402030c01090609091805 68
    0x54507250303105c030003007043d02e0007507401c0342103103141e5500641c0500c8129450a0031040125407620481c0703c1c0c620003c0d0122051a011604424454a1034955030003603460b2404039640300404880c500b0144141c090202c0c003207008000d1a645030441c0c407001d480b02c00d514010810498505040005160f081e100a0329040b1010307401c3d81c250402005024507061200340c8607100750000688510b20960072510414407901810b08054078101040c0d81102d4214411030034000001d01c0d500c001c1d034400d0205882101e1006d10185901560000036081001c3c42201728064180482030b8070070326031000100d0700e5030b8138101741c006a0f8443d103505a0882e602d450300001c1c010110081c00152a10564101c80801405101a41110041d001001c1d400100c40500c05030440305580c0020680f09444603c0100d0980c0984001c0441c01c0030500242243e000b11403803a5010300120601056003400c110139400c035071080c00c1c03640c01d560070003201030103480f503521844040d42d80780d408004003000484c00000c1403c0d80b0504071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 586432185 1250 586430935 586430987
    0xa050a0e06092116021e040c020703140d02060f06060c100f0f0506330d140f10090e010207080a020d1116050d02040b090f040b1510050a 60
    0xa41c1c8070070240c030101c004035110a0301d1051086090040b2103032424031400810600a40398240800325031314801d000280c06d03c003140d501140d01ca81c010003802c200d035540030f482c40c5400d500d04100011801e098240080d4404000405040c2c2c0000d0120303001104100001d40c6544c80700001026840ba002102c0460700621904164100c817030703000184000301ca03c4007404220f84142e4440c0884404440e090350041c00501501d0b40120b043d40c06420424a030b40b50030f01d000e8228034510744250300a1600500465840c04000440081685500d40141e068038100046007000d0580d055141b856005031002c81c1d40e11032607825407010950407203103c1c0e41e01500711616481d01e40e8003e92102618651800854400800481c00d060041100b40300142e200068101c060b0602c01804000c418550049800c00e0391800704400759507864070b101d44600c505408181d410b141500e000d404403840500728184582800004414954a02524140b80030141c584181c40e81d140700003c4482140d8059130741c04850f800c10075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 586433435 1250 586432185 586432201
    0xa17100f03081201080109111009090213090b040203060a1e0f031104050a1127040501120515060d170d0c0323010b030c07150e0d0905010c0b0a050a0e06 67
    0x14040039800f110542849a030f0350886503099a1410500400c0101c0f0702210042919011407446011282813405032142516000c0100480e130181d89a0300500780005010407904450f4010b008519105441c02d500314146075001c20b85000c0b8a02401d2409800c0e801c0000035100301d0320395600104022050f04000769640e0425804550703061044500450408000500c00602d501400100c2504544c03203a140031182c200030612040d003d540c50680c141d40120380f00c1e09650350300540c2d010b0000041c8030b07554074209142c41854098003403050310002c08210b04003c0c1554074004041e0f09039030081441c03528048482c0d819920b030700c40c8a9150500c03d14040f0000480f03503169003d0003040303030105c001d0031100405480c080b03d292024031a4824a800820003d0034840441c8042c040091181204001480c8481010f1055414a4140314803540c0009a066006680700c022940104000e00380711301103102c103468454485000510041c1c02c162540e01040028215a007e082c502c8801c205940c1c070750610000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 586434685 1250 586433435 586433437
    0x61b030f03040b060f0a06050d15030b33010309060905030a18050d0809060a020a02030715030f05010e1513090305120c0f04091e05040b06030607050a17100f0308 71
    0x103403e440d901900301c002041d50a01d00d80e071002030300b001040b000800349010000c44059201001720122152aa450078011030031005001c07010f103114205003859450015580c4600d90450018281481c94074281c04002441101801700e240c070013840c0102d908a02410000c010341000400100389110025080d000c1aa20201c9041203200032089081d807036907100e0800c20a01c640c0360010380b10160811002c0010310b007010003080b5100b03460050b90341420154001909080303035584a00c800444200480f40b83c0c40d494802c140388002d8001e020455541094608131030008002c01381c0040490a0041075a665030f02ea1440c00100c000c11010f21002c68545001846604981c00b01c0389228a02e601007001403032541305039400c2c0f40300602030314245480c100310880900004424003070407202390680e50043c20b806000d068070a5000d0705800c243c504080060600d2b2160007070070f0008100c0c01344080d141240c0c0c8032980d0025020103982d460075a8032910b80c0e0011001d941e07805003000d920380820000812400c40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 586435935 1250 586434685 586434691
    0xb010806060906091603180804150e03190f02040f020309030d050603060906071b1a0712051005040e070e070c0308100e0a1a19050310021206061b030f03 67
    0x1441c0b800c040d0301d480e07051203040001616003803d40641e000c107510425109a1080d54100170985401d10b60034400d45401d5070542c4583c04c4140c40c0283d103078a004805410208491200000340c006103980b88800a1040400c03410310360040c06004590007240565a50740c20031040c0f4103450408659a017004401d04e5502d40c08004000030060a00b000205103140100d036562080590038040d285541d01c5000840d141d240d00c00038820000d2600790350031b0100306414881500386440c002101d4450900c1c00300034103084281641d07a00c00744c0c10442085110f07250090350000300d40d030944000c202c0000d4050340b141000707070541000107441000c004000009038080002040103000e40c41b10031103603c4110345d0381e141c2c6441c4d00884420030706090126024031070582c000d0080d4510070b0000f10004101030300043ca18020040400004210418103200501d42801441c43e8801006011860300480601c954030f200f4005040c640315100103e100480c3c0e6120014400c01c2402e03c500b40c2c2e07510340c00e074103090145030816 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 586437185 1250 586435935 586435939
    0xc09050901062408071404120b1f18060e090709050117030304030c030e21070f05010e0d0302011e09050c04020901052a19050d030606140708070b01080606 68
    0x2081c4000b030f041c45040c15508480c140c1d80c44450a5040802c4140c481c800064103020070070244412101162130400003078030140040c8c411032800480c090030044180e0b0030207822900c1c400d981000c081140c0c81c5039903241007150f17404140d81481d8550640080d00400413a40b00002100018042040c0d004000c01d1440503580b241c481048541d0f200e10b850318064000003941003a070307030041002c80d011a001d00e00c3c076207030b0130b10928002c0f08a0905002040c0601c9507032140600303103403030301e450144038210170702c41c5001800d2042e081d241d0403461303c80002c004c0b40204078910700500541c50110305051003034000c0407070082400300301c241c60440c4424090040400744010f482a00414a511700340d403810b8002c444400405949a50410111412542d020441c030350341000392810341c0c154481d50b80c0061250140b200c20303a0b040e208804030142400d50409a80a1240c0209407800d4000c2c40302c0398100361a9a0300d80f0112190360f880d04030500d03000c030082c4039580c006001c1ca000d10000082410001960070f00c034500c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 586438435 1250 586437185 586437191
    0x318030d0c030206070503061507081209031e0310170604030215060a0605160210030b09010504090c0e191b11010911060708041503021b0a120e06070c09050901 70
    0x2040c115803144500c900103005810910124403820721031005590424001462042080000000002603a10180d07084540345d0010a440041c0f14048140e60b50041c500d201440c074102c0402c91aa00e00c072941144d0004619012000c00c1284020f4505000502140090b0020b04d1541c03106056582c081210b0840041c0b007205111260100c51100160084002411000e000c60806070305980e590018240c0340c0a2031100c01e00c01700941d8a07141d003c030021495450000780000c1890904c281e404050f084a40198101030742e02000460011400e011600c0342c1d640742d0000c1d100d03c41e1030901200d40e84185030f441e908245050000340360303140410740400760036120301da602c505a009003400e0300d8241501a000d881340010b603013280d041541c010300c0340350301c03039030b0301520b03064544035102c20700c61130441c040000a0f07003c105c0c8000c0c0b40701c00080d401540200f01c02081c0402e00340c0c0d5800d940a4801101408105909100414030340301e50050302d1b24280c3c8200d042c4010343e1511002e100400341154800450340c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 586439685 1250 586438435 586438453
    0x150e1608010c0e01120e06011e080c150a02150c030709060810033c0615081903030902090901050f18120702010e060409090b18030a20031803 62
    0x581446260481d1103292140c003e446000710054034120641d4090441a60301c8001416010313030306101c8540078210052024400d801c0c00c005070324031461213402c005082d6000159900080c1c0d1260034808841d0110081245d4510510000f00d0030901039055034030040c0110420301c010142c1090156104540c82c1d940c1d580034a030b072854102d80901058075042e03840d440c0c031101403002c41c1950988803130f84003030090590745008400c00e144215502096240c0c0e24040046611801c100c40d5014100d6a281e0103180d00e14082d081120840d00e410700400c0e07000c00402031101d4542003500a030004a8065001040d88200e40340c1450b005020700b50403a00c8490000700b040005410070f880c00085e201a120000080082201010310021030b83d01c1003000b82c0c14803080420a40840d50b0f490f0080010341395100010800725021710703004c0c000007005040402070010401c40d080c032070a80041611442251450310003000034505010b04040401c07007001404900000800102c1c1502c41c1074000020701d015000c60740549 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 586440935 1250 586439685 586439699
    0x3020306240d0203120c0616030e06011413090305090307090501060f0c050c091e010b0901050d0b011112090a0e0705072310050f150319150e16 63
    0x304600401c4010a01e44000012508104198619039480501101c1826103000300101264100c80211106075000380100600104485185807448044d82000e000340314000311400e466034014040c002028062000e010029507071124620762015a081c000c00800400c1c0c2802089540051140d074000c0c0700e2050001003240380740c801e49040360712603601c0150329058040212000313240c1c28410f440d20301c0382c241074030800d0303494203e0380d400381181c6c120fa0060380050341744149100300142e00546c00c4002c04c2c0301203020780e40c114041b1041e00d01a0100012104403800050352884003c0c100c011052151030008841204440010107185008440c594520380d40c0c0d81d00060300980442d003800001c0c1040c05540006801508005581c042c2000401645007000608a10b00761589940480c1283c0b03c2003400b810600d582d41d440d42102010131096040200c80300440d0303a81680200701e4052a9224021a0500170790405980104903c0d117401e015000150b00c03030035a00c0d0701e010709421180981a80016101c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 586442185 1250 586440935 586440961
    0x50115030b030706080a0e010e19020111030307090b0c19030503011d06060708090307120803010e0114010905060c0a020d2003030307122d0c0806031f0b0109080a05060103020306 78
    0x313801036581e0b00b01c0369952040c42405404c1d504080c11940d9201c501407161344c0e0051103400d400100ea580346840512490000404080307070102c2840c41600104144201594002201416580400d82441d581c130b03610141c00746407400810032b032411180614464002c0650007401075040b10188218421325968120fa041004001610350079803003001007120500045840026020002c002405d8850380c603542d01a4100c400031404045411240010040c000c2c000c2c411641070152841c1c02e0004403441c4c0b8100060103607203513030080500c18080800c1004501204111004a0715800b42444030004c1141c40c04240c039001d11035a85400b42d0f103606005105040001c00c0d40d01c910340325500c0e4098440d664006100030703d011015a280705003107160403840f002e04407821400c07080b040c3ca800070b485c800496000f0080c2c0d5014004503c40e4200842d01d07101c540151440101c0f50000113000228602c0e0100141c5440c0520b91115074180160070540050160105185041301d00035400d551040e0b4034501401e140c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 586443435 1250 586442185 586442189
    0x20d05070905150702190f0305010504050d0c0b0f1b0a02030712021f050a060b030c07022814031606020303150a0b0d0b0120070611070806010b07080706050115030b0307 74
    0x80a0f400d01035400580f505414445002d01707a50064900181c41c0c4a0311050341c007460f04140c1c0e043c0c3d16241440b0400000b04075805041d0702c00e16019143c24066952807041e03a801414000d110980c00001c2056900c000084400d80380c601010659a035001e40700c042c0d00d94110210035a011010300c0b1200c100300380080346080c403070f40640400d010824600d44082009280242c840556107558030070110341c0c0014580214015142003030040d440b02014410494001c03080e4540c0741900201c01c030381c1005080c84410395410b4540c6040d803440c402c40a1000302e0306d0074101e140040a5401c517100300003035413500400198048c1c840d4503110724182d0809070600034040e00e10302c40c840706890b04000c807414030f401d80d600c840080d100c14900311b02c00070079050b2400c03082e100d07004c011009500140c404001c1c0b06d800c03018289901320108054441d45150400700c07611080d0510501c901c1860016007481000124000c81e1a001d9005808000340e50f1502c8110b10300c8240c007012000421314094070394a03a80380009000301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 586444685 1250 586443435 586443469
    0xa1d090609070b0f070203060c04050306070e060f070224070b010f0812030901021b030a1b0c06030902011101060303020304180e1b1801030501020c0d0801080601062001020d05070905 80
    0x35403481e110089080da8000e441000c40102c085c0314800c0103035828404c0a0080801ca10070076140c83c10601050f00300760020304030405110041d030541d1500e450f22380544501002d50303229070752500e4450020460f8202034080c2605441c61404c0940040c600b480094041a402240c0c41c000c00ea03258021800c02c00d159000e82007180c1d2002001c001c5482c901401194400a0f000015040407008034100340d4244030742840150700c2c1c1010a69000c0c1541c0f00c10803002800300e06840042015a588845081850754002c001c101500c4240990540e4010071020350304031440c8008000701966800e0003901c1741c00c9030082c03184450750002d005040c5450f0b4000c0c402440b0010f40540811a01004203501030f0307051840b81174105083c0030307105240d00c1c07800b6150340c000d6001c3c40000d43c3e034a400c4441c10781800501d03130781102481070000051000450000e4034a06441c2c0030b00f42109401d850540380b01c004840c072003c40d1415030000421194454050304420b003d43c4098a5001400d900e43d000c000c84840d54001c520 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 586445935 1250 586444685 586444693
    0xe030318070b04050d11030105130308060103060e040b0901067101020406081005014b0309140d022a0d050d140a090b090a050a1d090609 60
    0x1009600d40035810714440c5d0b2188400c8194140a1000b00782500c0080b0344450500710080084824142c00400c400d50058003482c0411003903082c4500e4402d00b01010340b010705080240400611201c909500c060701401c054a0380525110032000c02d007103003040c800d61200360400310700102c440d9514016000051007240d580d1503a0f642c0300c81241c1c62621400a44008000b410117543d1642c844801c0c030041001c2c1195540715a4145454000541000c10307980c070031410414003000c00c415650642038104024101c0f13a0112a08000c000700800803403502e40c540c00b400b0b03844280009010b9805074007402c980c500c124120082640c2c540e000e80d4903401407506200c0540c01840c0007881001d403c0c09102082c03a07111501c5001c15103064045204810440d030115900d510800e01d4403116500b1a9120303a013800700031012890300d0707021700008052034017902c0340111080e80416219515502c0889a4018000103003003001540d5503801703c04c0b8442ca0014510900414090100d444001c010604a1003200c00740010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 586447185 1250 586445935 586445939
    0x5061906140f090717090a0b0609041e080d0213080c030a050c120a060e0606210d081e04061a0108160e27041101020607020c1908010e030318070b04 65
    0x70000c03a00f0010180b808212080901c140f05d100c4425145001d54150b50080c09100d0440c5440035110710702070082403040d1049010000000ea1170302e608100c0032100f03450344111500516018203c2d004a80310681e009002107500d60320b407042d1000300000c03246194201d0703034503980a2083c1600d6241681d030140842d00101c50003490341c2003010302ca28211020004072440c0e01e0700c2ea10340385c00b1a842c050300101103070008000d00c021840c04000100e40070f2890201b424140380098092540c0704e00e080e02c02003e028000d000541c0e95100705541d160040400f4a400086103003e10340070f80108948501131004100d13140403010f155100b0710390544280030303000e000c0c0c0d47c2c02c51f01d20050b5503505a5507210344c0d111540001c4003000700c214501c0c0c000d40d051058081a0241401d18101000313108480c02203046511070b00420881036400282c01c0c203140300c142c800240f190840d00c1d45003808403098110781e141398200b00482c0f1240d100000217500c0b807561001e00086101401c40c400303480c1c4910703119001c40200c05001c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 586448435 1250 586447185 586447189
    0xb1e0d0602090d05100f05010f0608011509120f0b0a02040e1801090c060201061401590a0905010608010303031a090708040c09050702030703030e01020705061906140f 73
    0x10810608010f1885540d40e04950344d640ca00103041c8961000b00381c4501525080048034002d4502505020804120860405000800b11801481410706051840a082490303600404086000d013a212121000040003070800403547d84440c03004980d2214840d0000c1c91502281c4265010340720151010001741d1620000030060f54241120350089559030054440054070300390341640201815000032404078540343c2e0301e94140d00030500103414008800c245861261094000c1c86100000b07961700c901c5442000c042203514034030000c030400010241d000300c1032003522a41d0303a0410741c881120041e41c2e00c1e8854403004161a000e1143c440410006401400000e010350040402042c204882c41895415000080c0e0824010744031000418030210500084c4040e00808001400ca010382c00d10460a00407802507484c230580c5c1d00030f01019502c000c0068101800e4044a44841d0814100c600500b80000900c0c0c03ca06600c0d02a00d204d4500080041c1500001c49500c0d000075000380162500040b1344c0c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 586449685 1250 586448435 586448437
    0xa0608070c0303142508151201232a030a09030c050706030b030601090b0306010b0304030c1e03020114061f0504090c0e190305030d0902060c0d030c0905011713150203010303030b1e0d0602 82
    0xc0032300c1440d5280d0a922420a00c56402140f100341c018100c0c54490400c2080844001090030b15598000c044464500805000c8802c80c2d400070f0b421500040c0024507030904841c0c1c1c0e061400c004110b802a0a00010880e600d40c20184800c2801c800f501c6240e40d0b01c1c49800220340900d1805600364002400402c03000100038041c5034481e0003401c0c440040c54131a590352482403014001c000e00c00440000b0101810b509100d01a004508841c0303403103e9050080002c0d000b40400ca0441491408580407028450b00c20015600244140c0c0000e0200715803d12005e1700e981800302410b80512031104242c0040c0080ca0505012282c106002d540b40280c2c01108a001c0c010301d440598001800b08841d07600c2903c01c1001c89001d55440d0f42c0002d01900c0060000c01449041d4041410048136004d04060101e80f901d0658204040910f200c6a10740d40d4681100700c00c540340c070800000c0d0300c040000003c2c0743d05a003101e41029012681d00d0940d03150705e005948203c078090882c0c1d8005013044040c1c0c0c00074455038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 586450935 1250 586449685 586449709
    0xb04150e0705030138150a020627120d14090f0606010513150e030303102402150921031f1212050d020f07060b0a0608070c030314250815 60
    0x1400b15180d150000003e1800c0d941f01c0b025000043c5d11400812030091035502900501c001501c0132500d24001c4400561f80d564504460034110150020b0b420003e1289507011a0030f458110140b2603241c42d125540c6501c84044802014543c00344030000750301588100e08030b40c1c00c10840d42c1c03007076034039410201261103841c0c0c00300305c00c1d041c09000b00b0b420b008c0d513074200302540c45100c46808560401e824507100c41d101c0d42c500b400b400c100d41752040ca502d45054002c28422100252010b81301c01603030360019410300e003141401c0c5214a804904040c080703600700940056114140b446c1c203d44802e00d03400800da0314035115200b02d0180342c1a00c3c42c0f81e000900030f80d450a490015038503003141413000c1c040c084422039020600c0810050000150401003100e40e008011aa002c1107449642092a2071004ac3c144680105041e04000f45848813104141c06640820407183e040003403141146072648249489400951b00782a0780602a000f0044961150026030302c2607a241840c4112508940240010542c0361 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 586452185 1250 586450935 586450939
    0x705072003100e0d1103040b04120f020d0b010e0606040f050603093f0a05040533070209060406030809210d02070e0a06030c030b04150e0705030138 65
    0x61544800400201d0090a01881d2014041e210b100d1052a0103006002c0b1224503d07103542042c0008c005200d604820388084030207081d00b4020310612031030180e0440a05910003035104280b00114000c5c09040102207050720400d29484450751170740d00401180e40103510800310380c10810b11080c4030780d0814030701464008010001b00d9000c1c8228002108003080c4d40da0800d6621800c001001d042d07094465000c004140308440b2642c6804111240100b0511840c0a440d000e0487d04014034021540850104000242c100204101c000044602101c036409020706900c2059038001161261801c3c1c841d00d0b04507030740414180d1401c4151000d02241c99a800f0a0000003149a00300b000c130041c06120b01c011200e215070260a95600300101540f8084000d08402541da02d841802e00c0044c2e003101d40d40c0203517600240c00d640740d80e6480c5080181e43c0d1203a4a80d0100c0c2c1d06245d010100c0c010002000d6098400880080c44451440c00d5040443c48841d503c01341c000e4004820548031038503174030810a08000c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 586453435 1250 586452185 586452193
    0x60105040e0307020a23060c06060d0804030b0c030a0501090213090b03101e0608030c0601060518180f15010206131106070311010f020306010f032f0d050705072003 72
    0x1600080c0b05c542d00d030350000950907040c08005080601c3e0b0310010010080448215041845144c000369076118002c00042c000d107250404201131080e600b090b2402903500004000341d52802d041c02001d103030010356205940354280300c008140b018450003500c94140b42e40851741d921320724020000014026880c0c07415054082c07514941c184910310302075030015400c65a104a100318400b82c600c07084501c03a50121070580c1007808442d514100c04102181100c0840c40c000b074031049031011096902c4c51001c6800e903c1400a001e080304909030000f941d01c100c404284503045662605000c0d14030b68a032050040c0103800000000d03240720110007908640e14054001c02d1020011240407d581d41d00151003600452400d00c0340002c548000d0041c8002003044203820343c154200000040d1151024100f0441415103d418944480821400121a610100e4501100c04044501c0d0904030381c400692640b00c68184000140754900807000c0716692a40101040040b0f6501101d444100d80101d0244c1d070f140c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 586454685 1250 586453435 586453447
    0x1211060913020702130c0f0819020d050603010e06010501021f0f05070215090d0801091a06040f0305010e240406061d010e0708010e1909200a0b040305060105040e03 72
    0x90368800030003841c0140d140140d60700c07903600402c140046000b44011407181002032040c0c0300743d4841105010402c40e410441500d4503110b0341740c400592829030004486102040b1704410415030f1300321600410080d0020404058011246503c4882c00d02466001d0f0b4042c2c2070034940880140040103405802c03003400500080c0d40011749055400c00e6680380c006130300c40e1510210442036501c0043d00446500c005202807000d146010308418014415039130000c2c0d4541441c4160700f1076808c030180c0c1c00002813020f81e99036154582038605d18858001030710950301c0c00c11407502c0d03040006007a806d009501c0200c180e803203500b101140004180200111041501c40700000b64500d41020b44548400c08121601c00d5503040c02c1100305000f0000b0120b4042015283c0108811a0850030b020b4000c45c0008050140400210f1183c001c4d1421540c01000e8040c410115055004d405103240d10030302d41185d956400c1c50f80c420302c4c00024011070001500d0794020300c00410032858141d110400b440d0512054070f041c15 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 586455935 1250 586454685 586454689
    0x406140405090a15080c030a0605040f050f070f0b0f04050d0312020403030e1002060f04020625080d1811041505060c01050403021c020a060c021207050c0f040612110609 74
    0x4000c3d07840d8218241c0328a11040384414002d2550007909041d0002c000c51000b00f40021f640314042e5801905060780c62000c03a080c02320980c800807240e0b820030111080c0d0041c05525070f90700c00700380c401c0519100348103101056055903982100c4d5840070f5400d089040604110410038031055540e003c805011802d003a015002070f443c005400194043c0c0c6403001d040c0c16410902c507960100720092011500b1000801c0300800429044581154040d94500e40310165581e4640400d41481603c0031900740c6603a0074010031038a140203000060340202c00340414120840c0c14a400d000c24003000b030140440031044102800c3c941c0c002c1c403d8820440c400c104890b650740c0030448a5001c1041071096946440808c024190100070040d1040e00f0008002d800d0140020000c1d120100408000c09981c0c4035001d00011740d00c00c10203181e2080748100f0450343c600540c60069520441c8012040c01180b0326200300000d403a062145104071050000050f40c0e030591681d69001103088940c000e5807120b000c1c42415159 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 586457185 1250 586455935 586455949
    0x103290906191e0f150c020a0f0b0c0c04060e070c05030f0a020f06090303130204020906193915150906030201030515030c06281d04110406140405 64
    0x1400ca580e441e9450344110b940341c0f42e206850303070409034080148640400000401c0010881500e08500c3d11784544a4584001030540718150302203400035a02800104072550b800c40209260080c10007150b00d00144041440b00b520a144680405201003100060003035000d8088401030901c11815245081101c2240c1035050f004a40210016440300c120300780081020413215802c998240c000310308628044210321248024524000d000c1d40d0081aa4004e5407681000e80311070900c0c3c0f0740820301da20700c00d0740000c02001800c03441c0784407001c1c1d5061103174020030f1440764107400f5041400003504c01c00a68844058503c400d00064000d165904940701040600071603050141401a03404500380e491800014103807a0082d08028070000304100c910120b640018441d00c00042c00c0e10040d1711000211000d21180013150149001c810880180c0011103501c900c50310030207900395028141c060a480305110407914000d10100c00c48034100018003440c2e0240d440c51696005504d119450540c80b0000f20f506 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 586458435 1250 586457185 586457189
    0xc030206030901060f24030b0303091002030f030a05090d0c0818012001061a0f070201180b0f030f010e04020f1908032a0a05060604090c23010329090619 67
    0x1043c00c6561380200041c0501e600800706d15900e1600707100f024007040000380c80c0d00c0b491018074810050441e105c410103000b482510800ca4107042d419440c1c0c600403221340d01415040340e480100340221245600c07424069550352469940002c04641840aa140c81e0031542c034094007024144450100b00340002d05115803420710f141c8488001284031481d100d0b40581c80d0480701000001c0c05001c1c02440c0d80c003600c2000f0364900580900e0403c02c605002d101c1c0520410712600006443d01c40041c6064422070444020740c0910f0003030320305441d5070781e0307600d0340c107402c843c3c00e88000350300030158000f102c001d140104001e200b5030380c250522515507a4032050f01d495640220309106070b0405440b611000c040c030740070341400d101d604800502b020007500d548507a1919001003e0314400c641d40c1420030b050110081c0030401422003c4101c00010541c076205c03d9118511200150005c3d062841c0c0201c00024003206122100034059402d5010350020204400c0c0c40e0001c01c0c0d00d410203981580441450a8000c103080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 586459685 1250 586458435 586458449
    0xf060607050a0317060109051309060e0f0102070c060921140f060603210a0f0c0206040915051f050708090409290103080315040b06041805010906030c030206030901060f 74
    0x20040a4044010340c1104c020192410300c0305c015801c1103182c440c481c40070740c1441c0c034100c0001c0c101d11900e024401070032030010b216001c0c0b28050002c400500158014281180540c6011002e25610745044481c03607014040c071341800b22200c0008c4004600c12103039030b0b80d00340700d14003c078103080b400114285820b000000280c6107a0141060000c0c80c1418072a14412201e5400c402c840701080d10b4020115228588003507003000074841038241e40c0da20504080035400e900610b12640c49540d00b410740c029012110080148004168002509141400801042c51a40425010007402101081c2c1c0c0c15001a03e054079806c1080201211903610351144070265403185d046c40d403914000001b582d000b004440f41801024142c04014030202c1d84900507a607100302413003040c181c60a00c040c08100602400310302c4c141c0041c00807a0214a500c0300c070781306244a04178a4410400e60b0380e90f24680f03060703c00a1001a119481003a000e0016050040045a01c6903910001050b880da80300301d51609914540c0c0251 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 586460935 1250 586459685 586459697
    0x31e050909010b0403030f1d0d08030403080a09260d02030f0106020706050c070504090206160b19020f16080c0a0302010b10180b03071403010f14010f080f060607050a03 74
    0x241601d02090010301603c02c000c151410242199800703000340005c0a005424041040300582c2a07500e0381c0c00030310070300001030042100744000e440e00070301c10341060b24200d003c900c15000007518011184521003000b90065460070b2100340341c15210520003c00304400e207941d030040040042e00c130344a00085001c1c85521410100035031401c54001e06140458015008210003007000b04407403a8001052004d4134002c88001070b0501d41480040e20750b00c2800c40070485900c221881074140080300c4249072007501801800884482203c403600220700c98000e46a1854105011240c1078000c01c8210748403082c4602006807604035031900c00f91810040400890050b910f8091844150030720b80d00900c402107080c10030310880c407503541641d0160801d6009086416801100190055101e00500000003860f00381da45c0c0e4039612006000c03030555a9004140032050110900c0c0d500794801c1e1780d081c0c20802c1d030784c1d1080c40503207600c400b0f190000000341c40d96902c10420b00008011410500c455003810744a07841d41 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 586462185 1250 586460935 586460947
    0x1d090115031503080304060506010504172a2b1a06040b0105190305070201110406080f1806150d08040806310b0a09060c18080c1309031e05 61
    0x18140d490700d0002c0004040680c0003040081c20000a81341c01c5035200030085403a640e03000040b6000c3c02154003440011030701903444050400c000c241c65082202d019101401c000c3e0b0700128030014090f8010880d0003c82c0c94040310303284654044040001e00250491601288542d140c44121104101007203103c594000203104092a0612591031011030a0130000e0504551150b4003d65902400201c42072586400004810a100394004c1505049849899445549515000784034180c02c03a20040e5440c01900800c00038440500e200e0300b066040c900418480d901d90041e200490341e644642c0d60020342440b4540001034041015102900c0c56200070b058070b20709a62420840c10724a030344401c103e060480031400c20b02c00a80c940d0403264000122480d05c1d107036070541d68004c0c4404100076125900d4110140c10090f4031080b1541d0804104440303d1140c1d1725004900e440e5900c090b14240c1c482d0920341500c004280c0b682028144074040d042080710f021001020000300807900c0c9010001980000302 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 586463435 1250 586462185 586462187
    0x307140a0c080601090c030903120507020c0a180e061003030c0c08010203010b0c0c0d2609040e0717011803140712020c03070b040f03080f070c0909030e09090d1d090115 74
    0x100c10802400d4941880503003241d840c054078107100c882b00d601542c0c1e114030002d0a82c3d030080002ea41c1d0440054031000c0c91580e24035982c0d0340f0007054030f030109541d0304100c202d00305d202000503064003c9000d1401054907600d1079409942d22448010101c40d00101d9910002c0c1c010030a1020b0340c002c2c0400e40382e05540c0c028041c80c8600700301090a03c2d40c0305a0b00c406d801c1c1d01250741205900703a80e200114001946040b58071114140740180c032030b09984141002d201011040300881c2990482ea4071140100c4007201c40b500300c9003a200b0004078081140a00002100400e100d075120418801704050407614001241d12540c5240104403d0440581e0010854080900b003c1001c40300400c250582036007481d0600400c00112030441c480a4207411021810020505050302100d11403a4003004880b00260b54409032800f0340a11103007038010645005035803100c0d0602d550210301c0b901e81c410291040d00b200c1803041e40c2407503c590071002c0c690302c10802d00c4042e448080301680a000d00d06000b80709900d4902c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 586464685 1250 586463435 586463441
    0xb210702100e030c0706033303032a0b151806090105030307030203041a1201150801140607201806030709020c072c0403120608030a020307140a0c08060109 68
    0x260b0080e40e4010084c000c0c5109011411406980680c036002c0b90302e0303000c845401c21490b102e0448240700c241028481d0070104481440e0f2041301d02c2900c40c8031745c1a00300e006002d24a204034180340c00b0300b07548411150000c1e159500c000d5200c00c00748025006909448041a051540d080c074035074481880c00c0034401e80b4a4100291801400200c0056241255542d0005c0d1203000390300c00c0310684011030b091680c40350480c4080d502c5c01141b0024035901c40d80d68000032000700c4119016440440c2d40c00c400455802c201c0404502c0182c4003904181c07800c0c42c16035411400c1a210983c100f42c070072464400301d6840c1d40d001c0c21907071039000414084405042c25010503062507040d0740503103500e0f8410041e04000c5d19000c5142000c460310030000722061744120100108030881d445003074450340401001c220405400185c1d4400c021101542084a030ba219030102d0b41d68030a014213400580d10034405e2100143e51420076410030890881503a60300d540c59a15240d8541031794201c0e81c0260002c40041c002102c441c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 586465935 1250 586464685 586464701
    0x20309010f0507050a0323040b010f060903020f0118030602030907050306091b090a24080114060f270703021b06040c0b031f061d0f09010b21070210 65
    0x20724200310303500700140d018003184105c445801c103040d15508030072080b28541c45188420388459072440d4040c50549000c1507080801d0084408010400c000816100c2c403650785501a01d41c041e181010a5103041c0041d9985900107441c055490080903022000134000d002850103a8000001040070300d082c04200340c20000c00500e0343c001c1d40d11140320b241c3d5000a50b010f00c2906242900d07101e10313680303030400a40e01400e1442c510240d83c1410030002a54000c850154000b1202c41500801202d414204070b0b03e90030030b0507608282c0c0b02d050300503490458070307041c50700303034440300c9094241d0700102e0000021039030700101250040b022a901040c5040005200410442e075003181c00c01401203442c003039440009168071402000110000840080d102100710f405000b100080091030a441650750800184442030086103035404541c41318110081c1e0400c10500b403001c0310003c0c55040b6503800d00300200200c0c1c001d40d90740104541421041a690200c90320103d01428140d409040360300c0d043c15010055070454 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 586467185 1250 586465935 586465961
    0xb03010614100806120d0c03081e07050928030b060619051804050411151602151309140c16060c090803040b04140604120b040302071802030901 63
    0xc095001c0590b4414605014500c03203424a0380d0161552400720310049100003403502c19208501c0800340710340d04403d80810003032103655190000c2da140450304e188458001800e40ac513018030400316044078000c5003e005000c0c8050100c140703800d032840300c100780000520650184140410814814028800703640d650010b401d490072480e1030402240900076030340d40041a010840c000c509000c080300f280d0301c07144405c04000c2040c00301d41031030304000340000d03502a605442694400007002680c0d4005041c2c8104c561000900c41c00c2c02c2c4aa020320107580c804031096061520200003000004580c049680c0150201c10000207e41d402500c03008103a24024003401001041032000e4601c000b0000308805107070354002d03004240100346090a5880d13034059000800580000326010811185130710140007221081c3e0b0340d0f00c151501400600045100301d014036500c1c10900802e020104d18014002500070b8071a00c1214801c658840e5030b4960f4800c1ca10303000b42c0180d00001030041d0a002402242d41c042d01e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 586468435 1250 586467185 586467209
    0x50901090302060415110f090f0a060f0c05070f0b0d0b0301020906030604090507230112050103020a03031103040504020a031b09050109050d050a0204020a0314070e060307030f0b130b030106 83
    0x661400ba64480d00200b004014811721054440310a40300e401030252140b201c0300544e02c98180c0e91000c11540c102800c654015140784d00c0801c400d1a09644400881e041070711000c804d0b0312410002c442040c3d83c184240c565100e1240d0001e490001240307094001c001c1903101980f1000c411a034401a00e5460400318070980c0180b001550342e0f550340d41200d820020407540001c01038504d1403d1030414040358801d40403012810002249001c6a00207000300d800d090703070303414040c103030a840c1c81c01103034000e002c0a90069034800302071000a00070035880d507070105214226030030180c0e210700113800e83c0d0000500310300203512001101418002c00b1042e11106e1201d0814141080c1041c000030000003143c894148a40c4100d42480305000c0103100058110750003401c10355413503c1407a000f5010b0b0400c41c1e446040c90750343c100015441e510030416041592002032241d803950b260700c0800c0340070700400e201e040b000350341d00c0b01c030451a0754445074445884401450041150000c0c60100b50840d00c4d1503000f41001c900e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 586469685 1250 586468435 586468451
    0xa09060f080f010603050402010c050706081506030405030f0c0a1205130b090906040f0e010908070b0105010903150902010905090a090b0a1517031210051507080a0c1113050604050901 80
    0x460b801c1090305550040c9030000b0340b681c3d00c0c00102d807500070000001d000350180c02c202180701603022000c1d501c2110300c03541584802800354240b000070b100488000d4210780051002c1039198410100901d21803c0031ba080310500206504c072145c0e920070741400640841c000040c540024032030010010000d14014038940d00b400c0d6400b000c9100345c070b401052240b19543e941310300080b0030040c0c2d0000d8041d4030701030002c11600105151400c016030000e10305030f0710741220f14000501d940c4078a5004040d664040366034100350f0b0360b06551801400c1403420807814800d10f10300110300d544610b00080d10034013024002141c0a00340c3d04200e1807826001d0007843c1d5513070034822041520200c203a01802103c4c5d8285405a0000c1004001e03070441c0145845000e502c6081d80034803541c00354894040c000e41d00100c41c8000c0c5009038000e618290b108016000b04422801c0c0201030a50b8011101d0101035406445c079110320301032010004121820144000080e036070340b44144009424244101580300c2103030780007008020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 586470935 1250 586469685 586469701
    0x1080a09020d1502040f09021804060f0b0309010209060d140106110a1403160f030f02011505090405150903130503030a0c08030a09020307030c3f0501110a09060f08 72
    0x16038007040207000e1980f20803400c003104445904a9004201104489020a03110f800340c80281d0f12400554501c41441c0b1103100e01d500d841d2042504803015005501009403505a2410f02500000c0207c03d540d54280140041501d90700c004100f01c00800034000741c0c01c40c00544e10782c0d000310b0607040142002600c07100b541e03054400064050741c50307800010114942070600d0510b46144504400701132001000700c8140b04104094104407103062184d101c003010004040c80890072a200003901c003034513103681e01c020413607410684200c54116008005607400c19084951800403400151080031141c1d00001e145294002c0e000c1c0584080c0c40c045000d035181c00c90110f070041c803a1490035009050808004046206182070754032401146902409a46429a036424072514500e01c602c0ba0b000444150404128800100220340301203400c0d0703816601664080099203c240301c0d00f48412202596208201e02000c10b5600107004554843c0da43c1a4401d4240380008182c64139005004060182c032070207020b144 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 586472185 1250 586470935 586470949
    0x106030e0c100c020a0305071401080f13060b0402090901060e0a06030608060621060c070c2c07030f0203100311011103030403140702060a030e12091e060705030a050901080a0902 78
    0xc5541460f140c140b060503400001c00d046280d606c0181903205a40d0001001c0307452401c0091a0142600c504200d40d80f011070710000d0500489004026102c49500440002e8055005010b041c00140c001400c0400c00000704219050a07003201700442e03400c8189c0161840c1401d04403000e0030417442c0501901d4500400c80340d94180c003030140d900c907140da28501d0840d0306040d4042e5882c0c2c889041142c00e0340c1440c2c07a50008c0e6501440c0c0c2600c42d1318240340c01241c04210749041d4025041a0f0140020910300201c108503c05000781c4548101503c2c3c0718030003404072081c000745008007465144d114000c1d00d98078184000c10003500549061143c070003185800071202006a90744990181011030545d5100d00d020040e510070503400035444580800c1624440c3da1540c0040c030209102310403104600e40d410080300046c0518150319a00c1800064101051b22860034107040c00078021f841e00c0d04054aa5441c64115000311500324009100491002c0b02580d0150046800000f660f0b8200800d0f041500860344d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 586473435 1250 586472185 586472209
    0xa0c0c08070b1b0a052e0905060412020f07091406030a0314090f120c12030f0403031107150507050c0d020d06051308030a0605090a05090c0d060b0a0e0106030e0c 71
    0x282040c0d00703074074550025043c011908000d500c032042e580070680d056110003a82d40701c02d1004051031b1005130045000142071203950b0403d03422100811181c0d81e20f68821080e840700d00f102c00c0460258400c2030104410401c08403001c0c040102c000324803c0d000160903010b0103001000e240c40b0341e210501407408a50840f040d2110307940c00e46c025541d600340090210f41313070300d95081c80c45800c8100042a2016500c02149181c41540d080350040e002c0d07041080080d6490080c2d0b036020441c24410002040024060f1800c2c104024001c01990051603492044034004bd008000110128000103050400c0003001c0c02850984e0782c04895a400c084101c0d0085001e0600142c40140701942d600d0104201050f030310310303c80059a01c607292031781c0d902e85101c0000113094503101d0305001c0c81e5514041110964070b4091140700340c04000080140d1458902000032102e10110250750032980c45018032426103440d07626802903c05a6402e0b50194076241000742244d1040c0c00c03c1881c1d4220401010755940c80c0249810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 586474685 1250 586473435 586473457
    0x71d070509131425092d050603090717010507020d1103161202070806041208061201020a0e100302130501031d030d0605031207030c02010507170a0c0c08070b 69
    0x44002101c09080000c10304400700c0c1c901e0f500003404000c503042054840340e1800740103c10800c14000340700c00540d02c0d41240d0150303900c42c5041c4045140f00030400810580c2103031012005005c3d0b0303a076400c0070950036841603d5440c4290041c840501c946189502c2400404074150020049844e00020094880c00420034041c1081207400b001039450004100391001d10207440300700c00566a4500e0807103c25520710031082c0140c0a400000a6008008a0a01e00c02d0350030000784040320244042c110340045000740041c1d0721040700240303803090741001d2016010f2a4540d455660034080800c0401c0344541c4901411300801d4010003007210700100b0042c0030021a0401c0c04d010403044910460309594440140b81220284004a0500c640c11078542050381143d1042d03040c0e42140c0c900d10100c0070144115900035011070700710f900b4040154814001860b00c14081c40900c40542e01e00640030840c1c1d0311480c038100000c0e006120f1901030000c500c1c00b4100070500c0c40004c5c0005450301120100e10300070582499 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 586475935 1250 586474685 586474699
    0x80f0403050703030f1b0909140c03060409140c010e0a0542041406131206020f03010815010503061e0c041d04060b0a05090606090301140108071d070509 67
    0x15007058005e400031400303503840703002c1440081500400d0550241c0b4036043c030700016010920005103171040b446112038031100b070007081c43c440e60340ca091b080559001814454003da9550100d201252491440e1091503048030080c04143c0040000100002034850a4601c10041c1c00c000300310790346c2c3d4100810f900da001d00102040d01041c00509003511302944040801d6401001e120140700016030b0002d2060b202070001a18031740074100148601c03405500368009510240600900030360b01c5440310290120711030040949414661081c9103000c3c0c0003a03200542c00e5108000c0c80b0a00d1503101c685034003420080d001030009150400505030900c00601c0c452000c4e071150000304050070008030407a001b80074035070b040b124001210394101001e00b0b01110b0a66003507107420912203091402201c0c0b9021550f004008040c5a1101d0041240d035610045400d035040d0750b25648078400c03030f00c5000118000c204030b602070210603140030501d5681210700442d0042489c1d8030070030042002d0300801900d9048800351150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 586477185 1250 586475935 586475947
    0x240108040f050a0b0c0715060605040e0c09060f0307030b040e0c150405090f06031207170f070b04051e0106030203150c120a0515012102090301090c0308070204050106080f040305 78
    0x2803403c210ba611400361089680d40100100c0c10450001000104d10130026203a00d52a04002c035800c4441c64003424000a07010001003004608135070600b81c0007020700c0d4856242006440c0020f03029840311703410180c40c05001c0300b04103010b038141c800c210700340c03009480a200460050450301d446d82500101e05209800d501c042e44849001a819038003d4070005c6c2040e0b034203041141d5007202a00b0100e4859220f4400c80c13006000c82c8030f0b10070684503c00d612924018008498001c030b03103156005a405e141d0b000f2400c0c04505c5c0854440d003000c900490003840078103000c940958100700c1903104411003030800ea040a00420051b140040c40d6070325080001d4520440d43c4640256821334801c000d07200032070387d4038001840303046485a8000c2d8080ca14200905802d09000740c01555801080d45501c00700c003c9040010f070584100d90010007100100030000222280150b4031054483c02a03042a45e0038840410504118101803040a01410f00c90034000102d192082c1e156a45540007000242045004151 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 586478435 1250 586477185 586477193
    0xc1b31020d020d0f05060d05030409051803070c0305190c09090f05160510111b030f0a05060a050c0f040603181a06010206070f0c021e040212240108040f 67
    0x1500d07944454401e05541e00d42c8040c8405000d401c80700d880140a40c5010046100c5181403c103801d4100e6012010b1401c181c0740603807420051034000c5c40881c1c4501221502d600510f070030300003410054880c0f118024254294148189000900c0e007807808a0120842400041100b4908581c200ea460480210f90a480303850000350b468002800240309220382e00403003004030110300710f580035564196030302c180001408100302d40791181c001c80000c0301e8111700244e80703004032100d58141c0003d00c050f08413003190350800e001d20b2030441c0c106016600d40c0c100805100c107508036409115008140c403903c071810a1300b140001800b9100da4030070a001c0c1035031501d09405a0341d50001d02107a40b60004048070742240d000d0310074015010100ca2881c0140036400008030103600403646c2003100401544d56810200d09a403e1105041c6944100d200d14620103500c049a07503624001010840800315040080342480610042e01c1020741e10055111450070043e980c00381d80c0f0442c3e00c0d6001e9044413101d6116001420 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 586479685 1250 586478435 586478437
    0x40c030b180c091608151201140c0903030a1b020607060b01110a05060c0a18090b1309110d110d08030702190503071212020c1b3102 58
    0x40020a040030310020841001040510401c0911280081da941c14424904002d8541000c0302c0000141302022008032100c5d1060810b203134000c0d0401910400b41810000042c29400c0c0c403d8410007503034644c000100c5040c420360803d074101800b854214105882c4000090304d0f0700541e01010200844609111440ba52000d41035070103d030040c2c00301e55a0403043c2042c002401d01018001d000c180b4880c0004400b8000240b6241340c640c010740500b8503501e504058041c2680000d084d6000c0080b41d0040c85100903500a5100013001c10070400205140d4032020300c1011302d1361103082554240342c4800a0046044c100040742c24090840d40084d805040b454100140410700e860540c000700360880d0001080400c0000b9803b66405400300d800042c0100b440710413520b200c141c02800c68105101050015170f480703601304080080c5003071640f0000c8100f50716404036017107020104180c2c0d00c40c4170441d44803d41103000c440e540c3c4098542d6407025064690300000e00c1c0326880f103010401d0000c50324004601850f8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 586480935 1250 586479685 586479689
    0x1091505100f021204120605011d01090c0e12011d0303150108180312062103072018010e07030c020c190909030315050307030b040b060307030b01080a11010e01090509040c 75
    0x58801c5e121902c4d440044204804003004840244c074020010800c40140c03844020503003030f00c0c3c07503406003a07081c691407001070b101d04684402805543c100c0103440f83e5540071880c1d1407402040c0001140300046900c1c01203540115040c1507281c00400c00d00032900b00319600d07506c14841c00c0c2001c242c2511036140404218007083e14041181c0001701d0b40445480240305558000d0100302e0302c1207061104500d028000204c0070303283c149568010000880095462031403083d60310259014107000204000200d2000b10300500c045c44000302d1000140031001281c0901c80d0411050300e4108101c0c10a40e102a603201e0340c410025210350711036442c003842044440070b998082d280c00e500c10b1085008514018000e80a254a900c0140c041003102181e6402c0001d82c4c0800caa0300f141401d03004d5113460b11012006103001e050140c141c01145c0c40400032940400c4070500801c00c1c0d000401c001000b5061900702004a29042c504000c0c1e46107504803a60b0740078071410180c4004503141000390315641303860f8036640041d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 586482185 1250 586480935 586480963
    0xc040902030109020a031113090906110309030c16060c030c230c040f020f03071b0b070e04050702060129091009171f0903050705120301091505100f02 66
    0x1040404241c0c000d400c0c00449500e00f8004014080c4040360b07207000e41c8e407540988000f841d00400c07280f1000d80015010030b0084400003560001460070103407a41c0219840c1c05035500000c0c8944103188100200004031a140c11519041c42c01c14100401401e2080c5001d410080c0202040062148255070240030b43c070704c0c450032020b0380007026010b902c0e1641c02d40d0a51080c4e107800700d95000103445008480d11300000190245c03446c0da48039016603031400da0b81d1240d07840140c1e03c440d0000184000c000300d4010300b502e48654482d03000078010081030340c0005000c0b000315002100100b000242101b900402c011162019002440d1950315105c00e6014500e80c0a41c09410b4401c50003440ba080700340c01d8107403001c074a52a6880012100ea040c2c0c6c0f01c2902007040c030401c4180170340c504152680d0313110f041c40700e1003490300360b1804181d9141c00b450030700c06804c403a240c560000010010f201c0305100701c03034070046905034210605241000042e082a04602100d0603c40f1440700300e4a2181b0900200342d0249403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 586483435 1250 586482185 586482187
    0x206040611030c16060e0a15230f13051c0b070509090c030108010c0801060f0e040f0c0810050d05120a0c020306190b01050c1c0201020d091421030f0c040902 69
    0x5444204800c029403085c400801e14000f44806141000c101c2802501c0c0c42e800540e1140800303010454143d404c540c50200760190100c7e80d00a4407000f5001440c28030584208203888801200f0460b001002540c00107120b6140b00d5600130030708245080b10a0440c0e045840419503039280301c015119803260b28006070b03000310302a0810095118480256059a10034802013200a00806068404900a00807400880c0e194044191128131800c501c400d6004d0207000407841603000020b04042ea043c1c1d4203e8070105680604001030554a440244010101210100e50710b0708103484e150b03280c410202c610f520310040003c1c058040341c025004e405400e640541114058904409080c000407040039138484401c2c2000041000d542c81801942d405e494002c000d050304120028078504200d194404400c02e654082c00085407021842c8140c48500e8043c0b0469070100c02240c05403130529140048100c0b94250220403036030180f80060940f54404504070031034805071540091404280a668050746410740 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 586484685 1250 586483435 586483453
    0x132041e050a1b020a15060b04080c19120312090506190513020901060c050c030d020c13150e0907050d030e09060108011a2d090a060c0206040611030c 66
    0xc0250302051003500140b1041003869815003689210041044804006a200654107408202450100103010114150000d00e03243e0360b8032608819041980201c00d903410201405045042074200c10441500c0c9140d0940503a0810700c0e0020540f03010100070b8100300c010314280700c0b84400d80c2d0080e003116070803104543c454a41190b4001421070104440c01c0860708100100341030746554554490302950086c16070003160300b82003044030200240d440c196070070700c520b41a000044e1030501101c4004000380e40036000c40d02c2400107019206806d40b40301c14600d450509001074950504104405855540081203c59110b00d08220720301081508019849000c1080001c00c054101120030407803041664480c00c2541c03410700641c0d84074424400d071a0804010610461088102e000804030527404c0701c20f2040100101c84560b10300c0c500b0030404209100005580062490040b00d01c000400080c03818030304c0701d003850340802c10034000d030320566050040c15a00c0d40c5c1c01040901c241c8862240c00b404881e0700702 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 586485935 1250 586484685 586484741
    0x207050c04052a1204020105090f090f061e060d0c090312050d060504181e081209010501080a2103020d0f0609050106020f031602030a0209100608013204 67
    0x1c0ca00100d00f2990351810300c002072400306680140c481101c2a03050610159895070010b58469200001d00344c0c0c095101c4502d0001a6100078031140075203180e032a90803052400070180841c01000644000180c0d042e40d4644203c1d5550800f01d4843c111080d10100701102206015a0020300c2608002c15500320182c6c2c20b604280e00c1005060300d01c407000720500c141c81d039820a2004680b50040400180f1144500c0d84010520701d01c0c11110801418140c5c0c8031200054480400c15085030411815000e002c2042c07011540d0240503160142481c03801800c41c4006a80c0d0311406500385401e080400c2000c15840c03400b2900a80c1a1091400076400c01e101e080383d9440c801700100410302410500f81d142500105540b480003540035010b850704070066280c4850440c8075400380e00410002c9030715100f151038200041e01d56030321380c500581d142034454203428200f9601130304c11041600b011103a58200c0419154140d01961003403414403405100400000350500414040d110901820f8070451081250b910780c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 586487185 1250 586485935 586485961
    0x80703021207150e01020c01032c10020a0302090906010807020a0f110409030e03120406090b030402060c160819030c140a0c080c03060a180b0a0212070305091e0706030207050c0405 79
    0xd403038246d00342c4551158001c015012501d20841180d104c030f030b09110348101081e00c240c4440c1459030b030508880c000c509000341c080c1642e004034008070000b50040f40000060a290a1454100d2400d0030040c2a0380340c4604020354694480c0006412104035003021001d10400700c9402c3c41100c80030f0014044500f1a00b0041c00d100f8007010007901920854445000901b01031040d0782c04d940300c2c1c0ea185080c0750b2078041e0f048215000170340241c0e4015400c2006d040c0954080098807a5040128145a00c10303140012103410300f12082c0000141002a000700b0b40000d41c0400e40f55801c5034490003001c0800c1000b15210b141c194440310040c0304040b402c902003180303040008e9100b4215821011601c1e41d0791001040c1c4143c03107124080c440c80b20856440a000500c1e0088440d0f4808250140181441014169005100011713102c1902081e44c039401d02010a1090140c06010482000401e40d000404d900d031304da8844841c859003040650204940003080700c18007c12040b180e0040040c096810411406200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 586488435 1250 586487185 586487207
    0x61508010e16080106030c03060504020310030b07030b060d2a03020d0c0903020a1710020d09021e01171506040f05040b01020f03032805040302060114040608070302120715 75
    0x12040c8840000e26011150300e0703814030b1104141e903580b07041e903c0c05d0020b4000d0508000d10b10b0034941c03591800724103920341e172000d10f104d40c91080700b030440c8510390b04100c07203500f5014103070000705810441c14000503180c84044500d1382600c000005160b40200c4694042c100381c2e010204071151560744000081fa5040d000f504803e038038010200302c85035105200b0341d0000b41c01d10000790046140305041042c071415504103103403100c944013601c450380c14045654080303030b1004842d8460a41e85100800075401c207000015000f01c0b031072a44204500e8407400207400310001000e080e14038000c120020b42544020b110722240ba08024045030780316611500b5056038010725010391340c019440c100117000507610004081c01e03410074440143d85141c407113800901d40c0b00f01c240c04244800031200c010340c480c4401032042c10301c5079000c5e90240c6415418410f003c640064510ba4082c803484c00c0440c2440001d00114030441285c0d811201e4141c07107501409070754180305031940000518043d422600c40c00030303000148909 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 586489685 1250 586488435 586488449
    0x603010c0309020306060d08120103080a0906050414190503031314010509090117120d090614090d031a270a020f030703020a140316081806040f0606150801 68
    0x4041200308034101d982d4664040c0d415803200c8081203090074500101a602d90080807a54581513061152514481d401c3e4001c50f1114070025150843c00c0e1300c00c042c503000d4000780c42d01c04d203810710304003806100703030b1203864413921840c11000c1c18400b07000013120315002040060203594440005032840501b440d200d2240c140f40b42244100303e82d031503104000710f800c00c0e007000b010341d0201d03420820742407100316401202e405144a8840001101718081c006040011001c06010a0111143c9010400d540141d00d4200301d4407042420304c240d0000101b010160209203183c00510140c84c041c0f0720704850b2801d02c01c035400c90b080b988091280e54191200c49011450905584e059440d0154940100e10514824113200d5a050011410040c42600204408103480c605548480319025210280c0c0d8000c2d242d641540c0010100c840c1b010b900404280d5000307020003118a150310f00e6445860301d42000520041c40249081905070412506a0168002d1300c040818407a450746407800140c03030b400e02806184 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 586490935 1250 586489685 586489691
    0x90f02071104050f0f040c180614121b010c0f0b04120e010509091509070306180b0603070311071514091c081017060610020714090a0608030d05060301 66
    0x307051420706014080c025a0880101e90a560310069071141d40a0080d208490f0001d65850009034040a01581c131048a200b000010380c072460800c50400760880141b02c580994000c1c45681e01c20741c000324050010ac0c3ea204110318044071078000481700b1084c0014001c0440030070012070800d00041c03644032407140b84180586415a044254190360400b401e025140c0000d20403c01c5035582d003003047c0c0d8580c2003045500d240b0720b41210b440014113004421140d03440040c0c3d407000204108200c0055142102100ca0f600700b10220881011502e18440141100b082c140c58800070301d40f1039003100403a42c025400414640f40d0070300310036215026140301500084820201e40c08030709010740100340e180780c2004c0c00310710044800074000247d6027054020401e101445c141d0f100006c50160b2288001940000030b000b03017035103181c208100920744000491301030440d401400306000004d0300c0b0714142c050030812105c0700c44556a408400014009a400c901c00c1c50001103211418111940c119a016141c00c6000b8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 586492185 1250 586490935 586490963
    0xc07050105040e0a0b060c0f1b0d0c1a1608030f0a05130308190f06050901060804200d1709040b03120706020c010b0a03080d140f0619090f0207 63
    0x44035a40542d0181942e0795208401044c0c86038901ea22507100208044d182c0350a081c1c0592405050044140c041c0703206400c8216590601c00c1c1c06564800141000c4032088191782864858030b400708100c0c000c040c14984c010300303ca0310402c19181541d0160303401820002071b60401e842e01e25030f19003040d0f40f000310380b001c00b401180c0502040d000d071a11a500c02c0310149210200c0340c5007160805809000c600c0090340c510038050780d960710f501031940c0d0307510300003800b044043c40d0000780304119105a014000f044010000d010001c3c2e22180c400c0024400c22a0001c0000000c0b000904c4c0f0110000b8000c0100540030b10f08051100c051010303100205080303c08001c460384060505450340352100421b100d2900401003580001c0d030039405411411094000009c41c2d200400205511240f6900250f4000c180030940d402c0c9205140244c84d40f81005100381c2c0c07114203018002d00348242d00901a83d1080c180040d0030310040c1d07081c00d910402080c9002c418011000e07d000214000d5003c1c1d0740c1503424280107120707 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 586493435 1250 586492185 586492187
    0xa050d0c0206240a1703090a0e1e0711010c0f080610020d270e060910030209011503150e071706060301031b0905070f1106090d0f0203090d05030c070501 67
    0x3018402c02d03002c0c0000400c02d600702505500850f420903c0c0307a01a0700f00d0000b059292038182200c000124000c000e6559442110402015001c1d40d03000201c004014402c000b0417454882481c00782a079014410b000301e440d2808280c80303500440315819029031900c00101d1603e9440940024072080301d486100041e00e4071418802041d40d4a403110002d071b1700401620011a10680c10241404503603146500c3c40c2d01d130045c80460003000b40c0c0c0004100c03884102404002e18044503080e40000c4c100700e07225142e500d1070b8045044003405200d0290030030a40500500c915020f5085001d0150f0a0103458415948602e0305990341b481c02d03120000068002c9035600e4110b041240654002e0308020b02c15800d503880c5941d040054112040d42c0c202201e04844001150070680c045d1900852050f200e8003220280381c800201315480c1c07011541000d82c0a03000b88200900c0210b0003048500d60382c58515120001000140e1840c4900d1481c5900000348034199000d102c008406403001c1d018400550341680d0355400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 586494685 1250 586493435 586493443
    0x1f09060c1b03080c0c01060b191d09060f04090b16020a05210c153111010201020c0a050327090a020c0709051e0705160803040f05030a050d0c02 63
    0x30318071a500d1554090000700c2e0080c1c0881e40d1011440d80f03610b107401c0c42c0b0b426903829607a4540c402d603901d0102050720018028002000050840c0c6461b118410250010012901040c00800f07103010700440404120345840310044044048009801881030004034985000c40300d03400c8452000c3c4038182401125060310100340c08074010f03045801802034401c90407092045010003039403444002c200304065070358010240310300d81c00c504143c0348403c81440c1920610300c82030000c00a001c800480d41482d481100c0112247c0110300703400290340c50203000c00340c0050340207100d02c6c44250728a1003107001240401100100500381d080e00d40c1c4900a240501c0c00c07256040c0c11b0981da950750701881e074ce030016040c802554050021007522008a8000a540e40310300c208491003561002c440c44107110540c0341d00400d2600c01034010f001d43ca007091820004242c003407074040d00408014a0344900001250034040e419810041b00c0380c00c8401e8a5482490b1200688540c1c494454201d00a060ee805048400d0001c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 586495935 1250 586494685 586494707
    0x105010315050411040e011d0717190605131a03150105100c0b07081608090d050d111204030f021f020c011b030c02010e0601210201021f09060c 63
    0x405001c810038103100070000a48184c1c8031200381e14000b0301c00007642851459100d1f0003401d5888403014001c00d0b0a000b683c00e003000400c0c01040c40540950f00e01c02030160980d1380d520200c0c01003a40c034600754000004c009000c890b0700044d4010100b0090201803d05e95100800a920b0500390140c003904c0c0d85e05141e21484204802d0072201420030040005040504ca071030744030106440c044840c0621035803100721908041d01e540001035240001c20640c100d030194252141e111904200800c0d1401850b42e80c0d40700084403101080200114102c1d407460050f03004900d40100c0058184d071101104600c1c1440c04104450540c0050801c07520050380b5400416520010784017410800c941c4090101d080000c0e610000704030302159a00c0d2081240324488000071914120a9600421007521183d8002d007510302d0342918050a4102c0c8004000703050080c0000e031982c01a0b915842600c003c03070b00040c0e0a082118803007041382490024540d031140750950281c14034510404007003005d12415203088500503201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 586497185 1250 586495935 586495961
    0x30b19020c0a0302062433070605041416152c041d0316151419021804110403150605100809061807050303041e0503012c0106050411070b01050103 64
    0x198490f59141c501ea5020740d060341f6204604100f0000400107001c81d240d00240059800c2a5540240010010183e0030000e408841300014000054401444034240a040c402d910300307500c010200c0c80c0e006000310b04048442c0b45641c84d0741480170b2403480801c00202c1111051740305614184076103165081c01e00b604a0511020f800070340c01d040112400c07070202103d040701980d01c111440d901080140d01070144284180d10203036801e4060603c4007200c3c0040d881c1703c8425102e00c0c014462601c48140a503807210703080004681c04620391800748001c213258401c0e81c00c0079202c680c40700302c42d8060701d85c0768128000b11030042d107600c00c1c2c1405944c1c00711180d40f8180c810300d034103800940105160805600c12401c00a014405454a17035a0f14000070745075a0050f03116600c010035107801450034101013017070f0600420f000c1d4000c0c0424101c031a0f4070b03001c60f100e4212111080000d03c058440500007540500c028000191080102d00c0f480d04002085400c4050308442c000403001c00800c055100380105414400b00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 586498435 1250 586497185 586497199
    0xe0109061a1c060306020a0e01030c020316020108040812090d0e06030105010c020f042c0115050d080c0709020304030504052719090f0b1f030b19020c0a03020624 71
    0x2244888120710420500c400003842e03110343d00400820b400d44010b224003400741e207560409410407000074003510032090850055410a00c0703882030007060349500010f40c80d42481d10031040c0e0342d28038003036240c1d016904da4104c42c480c4a5040001806000401c1c0740c01c001c8980310803283c00708102c208003052109000b0300340001c9000fa403074001414041d00744141c010b8001c002044900b090050080c1c080c1402920b14042015074140880400082c0700d600e40150f00c407078059403114100070114090a1500c00000c0c9202e80003e40e000c001300062007080c002c1c0140d2103065590b1305182c00e00602d190002e0148a00c204c00016080c02c414a030402070820718046003080c2c481955500103070490000301c01d01400c2043e9245c482e00c00c0001d205e805000a00351040305410b44604010f41401440012081030031808460300b4401c1c0080303850408040d41c420754040050401c15070301c2c401007010b03020703955039854144a00c2811034105500418403d20034068000c0540402c86c3c0c00d40c04194140f0b09003202c3d501711076 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 586499685 1250 586498435 586498447
    0x9141c0e03011b120e0303040f17070c0609030308070806010903080c0312010f1d04050318010c0b070f030b01020a020f040510170601030501060506120f1b040e0109061a 74
    0x1004690340380c0100401800003c1d000d08031507142c10303e00c0e008030783d04000a40180d90802d0180c441d20516400c520880001c604500e0150746520710200104005094080703c5009042c0b524007040c200e03403c150b403002e002a03006699a501500039441400101c021800c0d120014a140b441740d03d00c9841040140d640c04242d92941d20f441216a00c203004c140c204e070004000b41030841d4000c44490b4003d100c4d401c7d00e2208070b890140c03003c1e01d8903003444d580d1070b04c0c0c0c03d80d505101c007085000003907804000c11a10114072008405005803a80b08008800a01646052080005450300086030410369a03503914140841c5221400480e01c81d105510020f5200c0c1e20701ca112040c908299002640c00021046c030801c0c4c075611a0141d1300700c1d46e42188251034a85c802c0c0010b0007005021b0007140300500003524294203094040b060b42920020040c10a8146005100011500901ea0403260b80210900c1426035445071a60302c0c0a00c8183d003400f43c040c0040c05c04000103a201d0f60550100c1201c2954103c641c1468 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 586500935 1250 586499685 586499687
    0x4020f0418030f0207090204180f09030503150a23010905091b0f160c09150e010504020703031409030a02061302011e11011103060f0405220512030a09141c 68
    0xa583c54502c800c601c10b9020114280700607100400107020b8841c1c0d40c2401c1d404004e982c00c103580e900c0c40d0144c1c601e401e0180520000341c100c411349410924585602860341c1940c2c003c0340380d00d460b0ba440250784c3c01c03241c14101c0071806c00c1e605802868070281d079500106600d0b0b10501140c1481900c0021206981c04000042410400054540d00003c1c00040c0e10b00640d413020760b400e040030480103452545101004100c0c028452050a2200e94a4500c2e1041301e0b203021001e140c1b0071014807800f4020707074000035038404051013540422040306d10400048650b082c42070b021507480d00121141005071044174040b4204c1040d100030852201c2d0305a40303004227440b1500c4903005088102000809000c03c12203000744040c001e005007000100076011030350300d80c901842007058803540e040606d4000ca10300300a2001440350a9000c40c1d0026211421058140700e0b03150542c035019007001441f08101020060001005142e0003500080c3e0092403080c0000d0b030791404040e00c401030030800ca100301c820461459006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 586502185 1250 586500935 586500947
    0x30c03120705031204080417060105010e0d0305130e16170402190317030a050c0a090b0906040314070f05011404151b0501060f08160302040513020a09020304020f041803 74
    0x16110303200307507828000c1300c5200f01680c04096500301d45003c0003040500c14480110015030f005403003800107000a52402e000608a40302c40c5490902806100c08844241406103045800048070341c0e0000304544d5950700d1004040c07405a620402c296400e004801c020b5214810004244072804001302041c0c80b0759081200a550895178403040802c5598004007094942030101d480e10750326144d255403481c1140d0352404454005002c00e071040c1c018010052600d50191400080d2494944a1541da4030640001440c40c02190b00080c04141040c1200f03d03103040101d03d2004562004411180085c1c60b40019030788800320385442012101c0910007009000088004c40340800028185510720794550204005c010800207c1524240e44407101085020083c2800310010002000603020b650410843c41401811a1201a1280307440d5808502e1a00c543d03101192080c1c2d0081540101507551507149000c3d42040768140e1242580c0c40ca0007103241400c2c020300940a64819040c049021965425100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 586503435 1250 586502185 586502197
    0xe041e091110021911030d0203030a05010e01030305090103090c052214061e010507080c0a03020606010807021e0c06040303020708060604020f07030c03020c040c031a04060303020309060318030301090501060e030c0312 95
    0x1c5501c44d0305e2045040d142481498030b462655170203582e4915089800b0307015250182d000c000380103070301c1c401080404c0d400000d1f502401024078000c9402031040c1807082c4200f00343c1e0815a44000d6101d0b000300750943c01c15081744007036208501409101c00d192103012614204031031454104080b08003540984e18036299081215105060040c100801500c2e0941c0310b0700300803080700f0290301040030001815010858143d100b0405d00e08042c40d403408a400030340b54a04080404a080700211804100300d070140000081c5001c09806c0680340d9a60f8140250350303030100d12036801e041c06540d0100e05241441d000300c0d403200c1c8021012a15080d0650307011035020421034800c1d030460180b10000c0540b503440307010300140481142c2d0045030011417416809890b03c4039080f144e02c01c41ca401c00400010740c0110075034403506012540591259110f480c200d000e880038040e92130b40c5000000010406604c10791143d41650000d03600d148202d54403901381070340d90890b98041c0e50b255111b0401034000030303266070003010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 586504685 1250 586503435 586503443
    0x60f04060e0d0519031d31050c040806130312230c1909050102150703140412020d02010e1c2006070f260703060b130503060601050a08070e041e0911100219 68
    0x8200400d6000c0d9821614113a03200307100600c000400300090201008071540180103370503043d12400403550007030113408031a041c07840026140e160110111802d41d038a8440401083c0300c020380e130703d8040b800f000c0d2a8400f8070424580d100d22454046070380d12804040d402c0e00c1e03043e00203001e140d5981c9510100c001c00240001c0425894104905225100d014510b000382e00c5901c3d0300301128941c0750085d0a25010030300f02421685404196104444006284026040c07819a041c0a007801800f04543d0a41c03102a40100c03440b00c5825032001000001e444c42c42010300ea6100030380d08548040482e103201d50b49480803030b6084000c5c2803005600c04d4526503038020306281400240c8656511a400d815000120f10515506000c2420485410300380300e410b030702c0103092805510304900c01d400504601405898803041221000c140060358640d03910494001f8500031410401003084a443e0700544420a402c88040300d000469030403905000110100d40c003902c3e0068450700086e0225082a5008003074151 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 586505935 1250 586504685 586504759
    0x18051f0e01020d150b2502040b0607080301050f0a030b0a0f06210c060c050a060b010c0c080c1518010503090304120c03060506060f04060e0d0519031d 66
    0xc400c0200348010140000b03e2040855400400c099a40c5080300a83c031102500c0c20170001131000c00d11001c150901d40812020a540c01c5a4a00104005000c0040e845d900a20006040c40500003c580614120b0303030103c410305c3c8282007600c14000400d00c1440000c0604080c00b0228070540102d41210141905021380040c1301d541d0381c042598481a1880a5089080312032640c00c00c0c80862400d4101a09c0d0a0801e80d00362480c40c0d980d940d5076080c07500f010f030885a86600440b0668440c05001185c56009001940c019407034102003030b210a4040307041c600c0b90420341110301c4034400102c2514505034044040010300b000701401036520383d0004180c0d1815020422011466a00700045e64070468066103405440790706601e04901110000341025105480c148002c480b00004a4112410f550301c1c0c1c5010410840010040350403000400001002801070034124540341610f04036010307100f8026541c100350790340d000074803100629034500e0807600724220350040c2b40752503034900c2580381c0944003c482c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 586507185 1250 586505935 586505951
    0x916030b15180609101b020916020c030105060105032202060c010e06090a08030103021e0a170114060a0317040b0307030606110102121504110409090618051f 69
    0x1d440e032080d50508080742840420301000c201507a885400500c0c1c429104145440001c500140400005404000030800e40d00c0c01380002c20709080200d2030a030342c043e00300000c6040c415400c0082621809046005124840c240ca202d0f140500a00c1d000301c606840c0c90f13145483e403002803681004c00c55075083d4034445051501005884003401041080c0811000150080c00300760707000e081c400d005c0c00010040d4410038500b0b01065040301100c0c1142d50440c5e0b202141e40a003012283d120700d011301c034241d108407035000c0051106012010304154290400080120080580030000c40c0d01c8281e42154201c8103103581800003070401d89481c001c100512049070b08056480101c159249d000f01c406800080d202c0d0002c001b11908070607048003183e030b000025810481c0048901d03254500c0149043c030354003845101d00055031519071085050310080041c47c1e90f116103a402c1000a0181084202c0f2100d1804022a21a21144001c2182a5800b0002d005100060546410709421408030105200daa41e03001d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 586508435 1250 586507185 586507189
    0x10906030b13030c17070b0a020306011704080d180f0f02040b040e0619020702131b03050403050324060403060207150606090e0402130501060f020706030e0c01030e0f15010f0906050916030b 83
    0x1f42ea8442c2001e181c004da503d03c0c000c1c0004008041001015001d14556005d02000450348010b84101520b40700300010313840d2407480c0349440c0c400746140c084c108079442000d10b818040811810103501d802035601b44215102003042c0000c0b41e001003040d500c40d0300a100414202020240a11060001900054280b03003072a000100812014507203070421583d038005042c100d4458206180003401682010400ba26007903c014005110040c4004d140384154a00c0903ca07a101d480e03046040003025243c0d40d1100e850346009002540011410f43c5e50040d90100800c0342d00b4540912000e4841e540c3c0c1c1e003900a440c02c8c000c500c01d0400940100d9103c00c1003104104c4034420f034420b0718000c04844d41c404199084681c0084d0504030070342c21540402d82029464500f0303000c00541c2d00c4995400f0310703000401c000d04400036400c00b44180c1400b849805900c0120b08500550b108442c1a1400c01142009955071034113910f040321402d207e8250407194403000118004180501c4803c203101b00d050104400c541c40c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 586509685 1250 586508435 586508453
    0xc0b070206101413150e130501050a09030c02013b12030c070e190c0302310b0f1905070201090801060812070f061b02010b040e070b1c05010906030b13030c1707 70
    0x147c1e003c0069079110f450f000e11a00740500e640140f030f4010104400082c1d600d000b0158203000e18081c0c10b01104a10310b1450703030a00803074031510902d28415004281c9607203640440024102a10703034403d00011144084150000c8100c0d00000d12801c02040a00c1c5041200720650700c00400100079216811080c00911410f4080c092b99040a6940140e94071501c1140c8102c0c082c0c8510020141c1002588503d0201d00602c60042520a15500940c0318010200841158840e4080c0603010098000c90040f2007900540038000b2a4401d032229107000f038072180303200d00301c1c0c005100300802e039804109c0c041030b135011120041c80e4050054003d0f80d00e80305c49417150700603100d00d0380090340700d0031504080c885115070a108100a00000302c4d81801140003070b181c00d9542d44124001e080240c00d00066941201d8045030403040b03d103540c0c002c01e100d0340d070b903030600c0038014030040c442138130480c04480024121100f9032070f0b0f40b03940715495200c2c5040200740361210030690104100350902d0703643c204404000b0540b201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 586510791 1106 586509685 586509691
    0x4020d0303020c0c280e090c1c08161b0311040507021c0c02010f0305010e0415060b04030804090c080613020a0c0b070206101413150e 59
    0x491103800c013040d00c00202c0d848940e170350044440510320a0600408100205010049503480c00e0290811100f103d0b404005d8200f90141c4066103811a8231164110008400d6100f910b25503036124000c0d44517079003444000795500d15890410122500c0c0ea000424144031801d0742515540d0340c0d004825007a91058400c51702c038400141c14520802031440c21940080300341d052820126806030240326110800da0001d00800d040450045c064020281210182d210f030b4046a17540b52140c1c61150000d951511845488400010b0880c413410060700145000302c450a86c0d0f03074909010710013183c00c1d00c1c10300801e00040d40101b000f141e0324100c0e0f041d0414907001e0050703034804941004480c100e801c12002000440a2018445c410341d002403240d10503480110610040e6880d2403070540f0004040503001c1c1d000c020035a91062a4000c0d420035008811496403407c41c2c261074400d0105101011 = true := by decide +kernel

theorem cover : BRFrame.Cov 586330935 586510791 := by
  have h0 := BRFrame.cov_init 586330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 586330935 ≤ n) (h2 : n < 586510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
