-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4426
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:34:51.26358+00:00
-- url     : https://prove2.me/submissions/9f858107-8daf-4776-8c0a-9fa48064da74

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 795863309 ≤ n < 796043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 795864559 1250 795863309 795863339
    0xa020718050703150f0b090a0509040827090a113a09170a02030f190801080613030f0e0307090b0907210f020c1608060c040f0509040309 60
    0x1000c5140c6500400c29150707014001e4000481c903d80b4244285440d00719018041942400f0750f030040e0f5030001d00d9690780c1e50344c80d84c80c00c098130b4000c00d407000504140c908072005900918130002d00302401d072200084603410000c41c3e4103c01c00a010f1509a545246500380180b860445414441c1020300c5544a24071094600c0e1101d5018401e03110003030404100b924010584a4504180d801c1c24a0520f0001510651180740c01000d052081340e02e81004600030303401e5006080301e4485034130001c1401500c614082661101c1880d4030744554205980320f1034503640300c003000c0390750701200d004080e50500040d20554902010389543e01e04002c0d101c100c1c400003420301d03000780d01c501c2400c0d0711a40b101800d481e04403222a042205401c0078011b000c201c801c0f001c144100c58071000c60965482c45030309000561501112a482507a1050303070801400740c031219840310914007034448a4070a52000402c00100c0100300c5091301c400c1909501c1c0c4919103000c01001100060003102000003ca00c00031350035180540c41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 795865809 1250 795864559 795864599
    0x309120903060f0b03030403080c01020c060403031b030216150e030403030206010305010e03030915040201020a150c030b0103020307020a0b090709050708090c1903020402070609200102010e0102030105150a0207 92
    0x1a044851035820402c0a684480c490a05107503d0b01c503100c44103907400411078085175480381d84c13981c80c1c001100c07225009006048442d455400756004000c105541544112941205100141a003030302d6900201c049029207031510b1801003c14002d24007180c100140780c11603844501010401341c400050b66815500140c5c01140075034031050040c0304011082c043c07443c4a200d0b070b0340250308520b001d01120382d1301d8007800a214007840000c400b14055901c288210444030780c004080781803407071007841100018802c3c0084000040d15141001e021580329000b01c03030060500354001c4c9281140e94445940f5004040d01010080c07088020004420f003280c02021300c18100341d29401c1007071810490a50500241c4c804203807003040c0703100d1034101510070303a212081644e40650f00162120341d90300d0b0100080c5505034000d890303c1982d0310101031ba8002841c4200c1ca004080c0e00a000c40c10340c0003241c5003070380020700444d0751190400c2c00e00d44042a80da0040d1001d100705104440880e540e6800b0980855088180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 795867059 1250 795865809 795865817
    0x106180f0b1c05071425120e0d021e0d060509030301050a0b0309060f130f0b010812070503180d201804050d0e030a15061d0906070f030912 61
    0x150b041046002e10315064100d04508144030f28030740b800c4020310100c074605010710f2280e8042840500c00340e0304d809000f692004a42c10b2026500c0074100070700070304500703804000095690b4010108a051046165014680c00303003c5c901d90b5a03185e074101e01a040801410758001e803c0007041c50105030240030740303800703981003001455a03541040705100f000c400303a40100c40c0d400800c10038032483c2030380000c8c0903034001c0220160103d6038442020b44140718002c4540a40381701c01071007400c024003641c884154102d42680044410340d07240d075000c00b00c07940112031024109030428882242c1c0d072b403281800518081d00003003203013415545664802106c0c4441c0c160542481001e41e100300c0f55810002c1d032a01410f6228450081546270990311950380e0b0703c40c0500e0000300b10340c000c0b5003043d030b07142000014500383e030002c6501700c03020100c046007004181c5482018802607401224543c107071144402140541008009440d0135a42c50390252410140c1e001148109070340c811160300459000251040ba4880c0c0e40d071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 795868309 1250 795867059 795867067
    0x30209041410031e08032a07030305010e100f031b0e040503030114010c050a0f08090612160306121106040b03010e06010f030c0e0d06020d0e0f160501080106180f0b 72
    0x500d42c4d8010880f0121501607200401d103040031a42c400c058951243c0d03102c503020a82c0d889403000c420140010b480c10070701c0710340100d604800c060f019002141601c07964411211a5500d00c000010301c030149208003038031402c420005001103400814144000003c2ca078a00c20415680c220441002c50101c400391941c4d04040300511802e261040348555014091a00d242d0700190780d1030705620340d048040028401d0710206a08000c105449003505d401000041000fa26005141d43c0041c81840480b50b10230450300c140085000340d4003c0c45140c050b0303000e5064001c20031009596482c078602c1d2107401681d111009010001d056012440154003805a801c9405039504008002405c00751510380c01030305050500891403440356200c141307014002011610300c00c0280d19403c0041c02071241000c2c20b10918280060480c0d079810000340c20010713a1f00310080b2003400f0500300a417194040035000349400600d120004102046c461204000454103030440c8010196a9003881c1c5988031982d03000f9642090042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 795869559 1250 795868309 795868313
    0x302042319050f1e040201030609051305010b0306040b040b10030203010c0306031a0108031812030a020606210303070e120a0c051203090a0324150e150306010603020904141003 77
    0xb00909030401200008040c290501141c4c142040c05075180c11090402ca4134009402c2d603100b50445001440100c0e07003003059040c0024018200b0101c1401551079600f40844a407041c240012141c1c400ca0300f04004503941d845507540c45040c1c2c1b00c082c103422a02c146112020026a50a1203a50b015240d10b0f1000104c071451440c100544400100181003050340181c010050f03000d004c03049403510307509c482620800c81c099500282100c80c03e10340c1c2403064440032072100030403034001500b240540d404960b040443d04520000d10400c0f641244074211640041c8041082c1500941c11600400002000c218034401d41c089a64a0140254402d9555040310481088076040943c1c86107224603007000914607080400d000302d106140d6074400100b04241c1c07056170036031000c011039650001b103e0843c02030025046050250080071014000c0c20362205a03100403480c0c40c071003051680e00454024002d00842d078a019000d0b402500f15100c4550071030b07164084240d44207021100b003403080078003d582044640c214 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 795870809 1250 795869559 795869561
    0x10b04090b010e01021b0103020d06080c0414101211030d031a0301181b0312052701020c010c0303020d0e0709110a020a0f060b060c03031e07090302042319 68
    0x81074203281805108100100340d641d010442441030740341090903142c00460000101d00074410740101c04551485c013400880d40c080d000c60483d2018104590901c507400304200000220303182914840d01e0110322920401c183c00d079000031421100d001c0d101141124590030042402e11003182150000030303684c0c01410118904258100b00c4002e4150000c004400b1031582d94100c2040080300070f0070310050f104442c01c02d034020700700500295900c942030078100281400003501e00d0f0050000d800401300514a211b81900b40e103503000c182802c0503401004490a0a00155222442414240c00b05030b0204902000c92180303000f00000f82d8001001442c101e460301d48604210303612010290901b00c0b003000700070b90035a800510084002d41107250003010081d1483c02900030544100b0040d0002c1020880700d180100c048055441000c003400a03182c9072003d85c1042e403400800f1141c40b004144c0e034000501c0507040580c80002910b5400900b28600d1907040c40308400c0d01c004583c8011840401e580200200103d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 795872059 1250 795870809 795870821
    0x408090405010806270f0715090506120a020702011419080a0c0e15090436080406110c0405040b040210030c05040510021606110d080105030d03050405070b03010b0409 73
    0x203043c0140080d420f1880d900070300b814040e00d10030805e41400741c40c2c0682c030300c0500c40c190038240c50b4000c48034481c0c1d903501d003414004041c410100c0482d400d0000040e050802901b01d5900c40b951214010040d03842c3d601c4a030094204045c00d034100300e444c2100e44c046815110040c1050044c99151100040000383d0041c501140140800c4802d400c001c5400101c43e0800c0c8003041c040811100b400c0042518140490035018203031801d68800c1c14408158040310709a0040144442d108203001c0c0312092400700140c034041d07a19802050240200800c00c0114030550300e42c441d100d01441614201c400000008050307650580f401c1e50381140c0281804114581090038440945071814240802802907101605038052440703091b0180031807990300480d2a109111140001e0003031412050000d840da08000d044010032464107401e0b00c01c808440581c0c902442c2c91030b040b200000d00408102c410341030118007070400500308454070b21420074042100f07804400690302074100c885501c1d80340c0c0d1816a60f481a594 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 795873309 1250 795872059 795872069
    0x1081006050105190f02100c051b0c0d060f0f0e0606011b120804020429100228060b0d03020609010c030b131a131b03180b060a0e040809040501 63
    0x19003001310074242c0c4031180818209481c2800c001c1001024450240d04203607101d40041003075032820040041c0c1c1600003001d420622002c9101205a00c140044265610a10b454503239110440300a220000344441e00300c1c840c03c02e201d40f4049070201c003060010013035841e0b26031414250b400c100e04020032942e21028580100c07140c0038040f101c4c4042c50702d0301189000d8010052081040060024003551103540107008403000303e1403505941416110140f4009240d403440c1c5100d814003140d90007100d880010014901c2003000c2882e41c02401409590b180442c015200321617950300e800c030710482640c60444104070a07000f44c000e0401403030200074403821203103044641c0007418500402c2c0384013912420b159400e50303001d0101c0021045850048090710300001d405080d885100c0050300c3d0105400f030f801410002d000308049030105d000e50700d02a070541309080010382c803880c281c1d102c84d004a510381d100e09802c000003800101f202611280410300c040000c41c1c003a24002d000190485c141e00f000c0c0700c0e00340104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 795874559 1250 795873309 795873317
    0x31b0f33091b0b040303110c130b0a050105040f050d050c1203041d01030305030403050310030b15090f0f1603020c10020403051516030c0e10020d020f1c080a0b09010810060501 77
    0x40d08244003d0564050f80c00054104216580e600b4041035081001e5001460014000c403000c0010081c1c24001d031084000586c09800c40010001e02540078506840a440c4092021007915003040c0600400c403400c90800d03503991164008141090f00c80900c141074110a12016541d201d007444280ca05d4040c0d0307c0e28203c081c00c005001003010a40c018140c903040780d890f03c1c4c4280d5a45962406044140d10b541016000c000c190b0280490045d0900d00f44e070f2400300564031211240d480d1588540c00f60002c54a44160600120010314072040802d410034051800b1b0500600700010090070a243c116811030110700c1076030000d405c2c401d000e010041100100a1031791a81d44505e0010b108101d00d2a00986950038181c4840103013907214085d17120b0218504010301054808200140000d680e400c1406840b00540609a1501c2c200c40c408034100b0300801ea4959142100c0115131412a64580000c2020351803070303610b00070f400c2c0b07a07618655034600802000b4001c08060b4004183e19046641c03c1d0310950600c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 795875809 1250 795874559 795874613
    0x1030606061b030905092502060604270807051e060103210e04050603030c0f03070308061c030f1b030e01140403021c06060b0d09031b0f3309 62
    0x380d006200b10306130340d42640e00340300603180c0c41c6080c04524120f014080040e21003003078410b001c623030018241703200340001c603014401d0140b141002c022418001c04200c52405132000c803800411030080c010b2201c5403203982107841c2c06514a500b802c00d5442c480120466411110041051020002550b01c603180c420505880e03c204400010704145550088030f03000d50344902c0058803654092040e60569403580c03050b50942c0240d5004a612580008800c60114140b0004141d4a00780308805421144460640300450080c50f10145c9844118081080420805403c40c001c00440ba80210300e00501c603488000c038a100010014224180d00120440140781c00d03c420409030381d4109010f60080003035281d843c100350881c04e004000d031801740c104480d80200000c0c070846d801c0156206030380740c6002e0b544113560040c1404841e040c0400020002e0b0041080341c096402103070720f0a0003804403014100038203128048607200da80c1e039050304c0301421080c6543e8503001c2d02480f11320f8042d1100b0010440358029a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 795877059 1250 795875809 795875813
    0xc07030f0c050a080303150a0519030624030305160c0605032e090b0307120305030109050105010203040302150c01090203120a02120a090611160e2502060106031509020301030606061b 80
    0xda1b010081c280302d060510341d201c0c00c1e1b41c0c0c0c030b850414001400002e02041102940d81c1c003007a00102c603610045980600c1d154850f69007450459a050707020212412f028026891520200c45a0300011181980c4800090240c000912244060305c000c08954940c640c4900e0700b541c6485644040c140510300070050740043c0c4c540459100d0100040e240d074100001002c54840000c41e16141d11904038105540b50b010961040c15000b9010354102d91542c103003440281c2e02c80c801240c40307015603c40203402050002000750880f5140c2d01034004030402400021307641030301390000780c03620900e400e1508106c14005100613800354107120b900340300d1103c0e0b0315840c035040302e503440141000c00da80310300410812240b0f10380b00c0005041c0005000800543c070300d42009a00c0e03400780fa011080c113556801082070007e80259948418804083c1c8021f0f00342c0140c02140e29020055002c1d00356034490303079101480ca0b0004034541c295840514080c60080780001400f030306065014100b80642c4c110355014480301400d00e00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 795878309 1250 795877059 795877063
    0x1202100b0a051903170306030f01090809010507051009291b0a1101050a0b120a020117091203090c010e0102150109110f121b120117030c07030f0c050a08 67
    0x100c2c0c00a071020518000240000d0040c04055000102000030710820121100c81c0c50010314004c0400328185e0388561001c0c40013500b01d514040c40284619418000c8481c2580034102900f00c841c0203005841407160501c0c41d0404950088000319407900400c058010001c009442c28001d1511034000c42c1c6850800c1800e0760740140000a0b5484d07200000200001c80900c0341c4401e80901940c60003c0c01241003402500c40030b4484a09814002d070f1301c1c4c0044181004000680300b10071a01a102c0100e0a54000e42140116500800c400034a115400c4401c1e00b10719280015403065520401500300c43e070502000412105042d2011070441d44008031201d642100e1089050444004510015440903812000007160060b82490f603c01d46020404044110303601c0492482190304030211101030704400c0c0821040d000303200072201c1600d500c000600c0031074046000556070400105c112401d01d04410741c030503d08850b075001144d03400c0c0107140d040c041020b203c8600c009418211040f61215003070254042e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 795879559 1250 795878309 795878329
    0x90127030816030212040804050103050a1a010e0a0f0905040605091c050901141204050c060301120312020409060b0d050a02030f040204090f050f0d12090b0712060b071202100b 77
    0x410050401088030b03400d41d010358110303459070765000050802403909041c000382030b0f00a07100d000d010038103100000f2640411445901c943c0b40d02c04440e0000501148011208051646102c40c3c00280a40d00400c41c0718100224800070090a5000728040c0360502d8801c050310000791a852030796001d580200e206416400411170130304001c2c5015610751104400481e00d41400810b071250145000a00e8401000900302d46441180208120344181c0c48180902c22144402d01c9040c20580f43d144018000038410004c010000b540008054142900c3c0c049403011200b0a03402906c02113800101051085094001d01c0d502043c549000c50540c541204c5200c042034000300003e1041d5503582002d0100721118001d80125a005002c541204103440c95440d600c005a904040100384610303c020528003450060100c0700350b126880300361680316104155103031015644048c909603141d03400411044002e50142034602d00803440c00345043e4191401a05050a103802d0980030703814006c50b1b0000b6118002c0c81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 795880809 1250 795879559 795879571
    0x90b10140a0302063411010f020d0210020f0f13060f0c020a030f0203100c0503010f0807050307090e07122009060a0302010f14071b0617070e010504030b0901270308 72
    0x105010f0000705c00c10340f40b071243c600b2000c901c10845e880482c003480b8800000c1c00c1d6005c0300b030725054140c2e00922801c0e41d64000400d5110016805003013095404021754000c0c00c2c08143c0030454900b030000314161441243c02014108042d40191881044481e9000341c01c2400d0344190305006009640f03a4000c100420305600001d840c0e444614040c01c11034400300180d2281603c0c46a0410a000d03104074010074641c13007072042d42350110300800041440c03000401c00f50200d440c000e00a00b503007450070710450090540512540264060120700140c071010110110449a01c03505850743c03800d4040040181440036000014000c6a035541040701380c0d1140000a02640d0b0242002d9510340f843e1b5038212904000031a041c00c250402156030810410941141e110b8109007070a4240b03803603110103044802040d044902e002040020020030226401403d0481c000760061406070325090300c1e034640c0f1b112a10705035108030250b0340d2176501045624049069070400a083c2c01003c1000485880040c400e940141007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 795882059 1250 795880809 795880837
    0x3070e0924071b020616210e090a1b05040e160e040e0309041e1406011e05040302060301030803090d020c030a03260103050a1a101404090b10140a030206 67
    0x51000002d036903803e00c4920071350042ca96681e51003840e001c210b500105d000116030f90142c40e400314003102c1e40c40c4901c1100090a569020464102c4420400c00b140b02600c9a1502d580c1c1c0e446220903903034007d40c40135050b0ba032070310b45aa64504d841121041808004c14840d0034060307940141600030762000d0f51080108003201c5c00710f050000504003070305611810b940340341e000b45450652030a101c0d131181c0303198594040c1401041059a90740e8540501c01044841d50b000031100c60803c000c5e48140c00122200340b410f0300d000ca041c680c0325400306038658005c1c0c1041e218a5408000c0140c0030208225144600e201d6201814002e607a42021940c0d0f5016820010140014071030181804043c1c4210100c842c103640c0c4051089503924102141c83c0d40101c1d6043d40c290122074449850681c14902080c01031002c0c146d11408103180201078074041000802c02a40980c68043c031401217100c20b1500c038003507842c90030022202450242c1102c4005c00000115005412814003040507981e802d00345c402d07000400d02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 795883309 1250 795882059 795882077
    0xe03071d042d0c0803120402100c1719090602030a030b060d090f0b01170a02040b03010902030f07060e241317070609081605010f020c03070e092407 65
    0x3410940d940e901c511480c603044002540d01100304a42800701c1c120b14010407142c1d41c0962190716007070712032080c00d80b43c42c008461600400e0060400b44030050b445001890516480081e640d01d03400e510340f0609032800c903010003080614410035207001c42070b01000241403810385141341410181d1030340502c10b80902495a1003610004540301c95040741c05596419000b00803c580901c0c002003010352a0b030098805904030000881d10003406908200c507546c1ca5001042d20303850039400c11020345503040702c0c0c54065480b801d00d4001610100402c450301d000b20350103000607030704000c0000c02600002010500c52200020f43d1074a036480d1240703159820300e4041000396108503c101d40c0308158001d82c4138080303c06003c01148012032002c03405c0400c0c0c40255650503140b0344d58100c0240c0ea500402000c1c080380c407000303104000560143c24022052000b6005862550050800080c100f0002d0f50240201200781300c10005141824004501000c41000c9005002400c825421920300302c020092402c1c0242d1403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 795884559 1250 795883309 795883313
    0x100c06050601030e030c16060503090c0d1a0f01030213090206120426030105010306090903022a0a0b0c0d050703021b060d0f0c02070e19021602030a120e03071d04 71
    0x6080903000c0303036400003265610f2240010055440c542d47c00742070380030080c00f60b020070070074480c1c1d04990060041c40004c02d020041c9208212440d403107080c0840b140c1401c560300c80703001c070803850f03900d88108480082052a903145d801030001d10b080c1000b0702c0412502c1e02c1c9030200160f0320001070342c01070200150b0704281076446242031b000d40c0080c1c1c1103079119490300310792030070000c04150000c2d4180c6a00707a0b024001c4070754881c40c40f009c3c1c0700518802009038001c4140350018100e86012140d1509034400030f881c550000c8008529550b9850f08044913000300001e56101c004000c12028205038000e1400c9464034485846c001d4807075014005180101b5140501194141e4400041c1d8400d54014441008007540e1000008010220b2840da280035000f2088005040441c15204511864840410f504203542d02d0a80e0b9000f5070100a000c04071521103803206015840c20000d049000e44a01c1052164840c00304018203544058a809482540a202c0034417405a0280b4800b03000c170b00c3d446007181251030364 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 795885809 1250 795884559 795884561
    0x60201020412391d07090b03062214060d0203030712020115091d1203220807060203011a03060a0b16061a0a0902030112080a0c060227100c0605060103 66
    0x200354034000c841d00100490310700148840c0c25000321388410654450b80c140103291032011080485a810100d40c50140c02c001144082c001103510040040c618858460505151000c40c0b40c80d00b0903d800d83d58801c1e82c621415040359000c1c0d013040c0e00300c403942c0034450b0650001ea42c80c400c0110041540008810700c100c0f1500135000180045091500b0030071813034542d15400000e101c202c1d440d0f03806652083e1070001d10320700402d071807a81604000a080c5540d4407049401c0d80310307a40b62044030b0070341d000035001000300c0c4502c0050b1614038800c480c05a90f9500d8868416200e1030344c2141203e1440c130401c148003155640c0b070a110101c8a2124a40b40c590802540041c0d000410b80c40c0a00114205110110100c0d02c4201c1c642d542001102c82d49080742d100e00032401240024010081107030018131220300407485c80e4001d814aa61940ba20305100042035a40030b0507a04000c3d000c0c610400e00c001d0300c201d4802c15540b1000c1c18142582c4410610b030403448010580d0003182c101403d0560b81d940443c1650340301b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 795887059 1250 795885809 795885863
    0x5370201030b13090602070210030c08040b09070308030103060b040507050a09090c050c24090d021e010e0708030d180f020f041b11300a0513170106060201020412 71
    0x1980c3c030208168001402c042c000f0b03500c140381c224401c001c103541c405003840c00b900c0390784440203040c2e4803242d013540c441d502d4111505025068400750f01c41c120001000460006c000d41c041c5102d00408101c6980c42c030180819114060045024468240305800090303a000134540101e4404480101d40c42111044c02c2c1c4092003540308010150280b0903444007810310324103960401038105180200f80d40c0c0c1e9018951303102da003c0c0e81d01f0001600500ac4400501d0814a840036188446000008101040d00ca031140340030303155407040880703400110300c0c9011003801b1310cc0e61a03920f0440100c800062515500e000341d142900c1c400071700c01c3c4242d11060b9a1911030703070b01001d100f0414410216012076200b40282160030342000b140b001e44a00010f0a01c00c0511500e42124849910b89840508aa0041c0a5003c0c0c12070400c031410090b0500c0071380003110322003045800500041c01f001003061020b0340d0550a444460b0003060030b680c0108010417030022030041e00b80400f40c12641074007940e401c1c40035004103012 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 795888309 1250 795887059 795887089
    0xc0d060b0f0703090902090319082503020f0615010c03030f020310030c12080f0a0c0204050c120702070e15180a06080601080c010e091e0405370201030b 67
    0x40114103548914541c600500e5454081d4441e4051203503900d26617000da04c1001e07401070b0140c0203802079142c1500568081203000d403080d01041d041021840542c02d03118a03600c047d0070903061800c0c0310818181c050000140a802d040060017551600b44404000114038940283c10420981d00310420f251196000c07013044d01d1942000d40d500d08014800c40000b00d1140010754810f82e00501c0000c1c1810306005d94160781c0e502c100d41909010600b903443c4020f03017046450009000d4041c5040c00181e4942c4946c51161480c00d4015840b400d44880c03214000c5002000c1006550100906100b960307500100664001c0c8030300d0441c04164032582c04510700c4490b450310300c109072800f0380034040d9291441e080380003500e18440443d05a81e076114400b40d030303c80141d80540d010810041d01c07008282046665958485c1c5194207030565050500240c0e244c1c000200d5003583c0a07000a03004001c06074401c0c040e0003d1100e2020040e44d45500329001d92001254684000d0515503070b18651003881d158a102504060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 795889559 1250 795888309 795888329
    0x909100f0c020d05040f0509040c0f121403030708040809060d0f0b01020f030f041827030f090605030105270403050d140705120c0409022214090c0d06 66
    0x2214600c0884064480742a8660140c0140304a5800441c42a001d0701c084500e0701c3c521682c090b1801c801c1c440c0320b40d00038000362441000f50030f000c509201844507c000501c440311201d80d10503060b0a1020702c014040004c0700042d0400c100388141c140e4017680e66600940c01840082c5e40f24625800602c031482440c0507042507038200740305441203403090f038003040c00e501c03080c0c0a41c1c403100c1c0d0000000b500c0b031103108007003841c0350740030722080c4644140d52000c0c0080e403080c0080002c014103c1c92283d60010100700040900f215a059800300309640321109a54a8031142040d07841d5900f8440080d100c0d01050040e14010a05148105621564140c00c43c1054900340b0710306115041600380104164482074800220300c2c105564050043d0002020500c1900c46a48650902c81001c1c01001100e0307028051130712000091002050900c5284010f04038030a070070365058135000302d0f90070107614071072035a1081500c0851054240d0003621142130180d4442c0c0400b032542c0d643c240c2015804001c103015001001d003a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 795890809 1250 795889559 795889571
    0x1014150c0f0a020315091009030c150903090f0614130f080d08150603040311070b040603140a0606021509160e18070f060e0f04111b1605090910 63
    0x1a03000482c42c161214020303000d40d40e10030011200e4011016003a513030141e066202a003881400e140300e40c05119454403914025608448030340310301071a03880360380100001c1355840042104145d0041844801003414006d14103540303262402c09001c0605d9903548541d101e40004424420000301c4400d81d003e01901d1500e51242919440c0c010341d100c04e4260305002207191000880c11071307500703c4180b062500000744428a90340c1c4a940403105211028041c01c250300c00c2d813201180d41c91000e00079001400d0300b65000101007600d01401c440da280c0140c490746055103441ca00344002c0d640800c00021814078050403c4d515164070014526181541303030071050b10000c1c03c0c400310300814040340311401105e00c3c2d103c41d4540c482c3c481403207403225a544500c2c8007403500c210301003007817500990101e0300c1c58100800d14441da402d030b0703008070b41950307a501e481c031006c80310000b450707407480310420f03030350004408003100600b40c0d10484107190080d2407403030044074410700c51140066a00c0703004009440c01800e0400c0d043c808 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 795892059 1250 795890809 795890833
    0x3180c030b18030403050a030e19080c031509060402091e040302031315090e1e01031104051308090d06060302040e0c12030a0917070b0c030307081014150c 68
    0x1581e00503540940e02e0503280b40c845201c0c000000a075030070349421501800e003180040d94291484281c4541407a04804040c0d02d83e11030031801680080100003580241510700d140e442007506002250f0040c1d4288503402050245200d400a40c16071702036130503281c0061079100e04201e100d00c010700d24004540310304000104402c260780070020300950550203441d1041c66450306200c48150700608641030005284003820000c00c03641d68019038101c403422040c0035680754031010001030769030240c1069034112600040c200035410300c0d101d010390081c82e20407984444911555491110f200350a582c61091301c030119060103100b01c1703500c85002107500510070007156a0700aa519220ba07280c880642c400c0282d601c40340510140030040322807011041d520060400c2c101400c50040043c9103180480314403a4010100f00210440020720340441500011503e0340b50407480101840001041189036a02c43d600801403507030001450b88402104460504540651400c41c0507d4050b0468079540341c0f240d100d030126 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 795893309 1250 795892059 795892073
    0xf03150702070f1208071101051603020a050d0f1202092b05120913021e0c0307060609020702060904020d0f021902070909230705030313080610060f03180c03 69
    0x204544601d0b0000f0300099440d1800c001044808001501c09403041001318005140031400600e50072050400e18200344210040b5800035410a00440140c1e0014400005200e400c020f0005040401e103024000c0b40d600510040171111611451000d02d600400c1e400c40b540c0d01c0c4407000d22090350000d650030150881900344140140f0019095640d8014207019a003504800ca089409010001c1c080c45c3c0c0b60302108400000a610595944032104641360f015462003a4040c0200040310390309004544a03071386401c0c050212941d603400303580400c4c810030204005072170b00e10a031401c04100300c40050300c80401d0308145014207120314000908610014031011841602d4508041c0015558202d689090300c4801c441c1c02c4504c00300000c0c000340e4203448a502031404501498581c80351110680c0c56456840e801b00340f4580000c006c03407060b0200da00e0306010041041141d41c4d40603c3d03007080404805d14048014003840242c42d000c03070406451340725592101c180e4003100f41c009030b0b0140e6183e0f0003031b0342c904007a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 795894559 1250 795893309 795893323
    0xa051207110307050109180908030a0b0a090513060e0c04110406030b0307180c09122907090e0703230f010501051309020d1b0305010e1e060f03150702 66
    0x1e9100702100d2045075035040005a44080d144183c4449803a01d04005080c0d135003a55040c2240e5400d41c441040ca4000f0f4212000782d802008070700c0021802a8103c810420011007541104401c10302c0c010170003a641d00001141c5202d60f8011400203080c1c03007540203d5041c5000f9112094006042c01c04822445a882c0c4c003c00031143c0d665810051005100201a250702603407107030310199446141102c0c0c48005a921005c070000c0c0030b040002c615955907454007440b4114100076110941c07580908074541c0c0440c176496003020030b00c03807040c80c1c1441c001501610841705030007800c4005d1524400039002c60b00030360080f000c0703816030b41e1004882c0c510b0035040c801100742181c05080300c2e4130341b00000541c3c1d405401901e451310070040e420b0804509046074000290000c000340c007245900d98000f0302001c0201c1c50a242400070980c0c0c049150b40c109500f06018401c05018000b07403082c0000b20182c200313103920b40250810f60460b04240c0d0401007400288c5040c44241c0811109074000052056007a0006014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 795895809 1250 795894559 795894563
    0x10120c0512091005150108010b090a0315020d050a060b1803160323070b040e060d0605010b0309010b0916080c0c0115140109030206090d020a0e09010b130203070f0c050a051207 77
    0x1031104c0d81e80c214103020f895100256850104043c24014030415445801030403131807502400d0340380003c0d9a5100d410040340301600351a880b07a400520301c1038120306405541e521882c400014002c451410b0b10b00700311440744e07050031113800e5a010788001d82554144070300c020000003000205a865100d00708908100b081d111a9031303500808002100e030320a00800e11004444000206a0900c7c3c40d01032080d0030f060300140a40c0c0e10102c128104000280107100e154041e000f0b1000c800d4403031800400304c41c21522080c5010b48a035000100704564014000c00300c04400b5143e1a00c280c40d51258062460a809070782e03100d243c15424089034807440d459082c80c280407035a0201c2138003804106c034001035440702084c2c08040e4022030104051340d0380341007401c501c159061014045150302a0380c2c18002080310030035180640a65100d0096103003601c0c1042440403100c0401c4004c43c07450034024009000001440c0c405414840c8024005042c0329060141480c0c550f008010782c3c60343c48107129200a968040312007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 795897059 1250 795895809 795895811
    0x1020a030b0a12020105031504050a0207020f041406060702041b0224091e0c15041409090a030c0807060204030c0302090705070b0f10080a0b04030e10120c05120910 72
    0x201004514040b03041d0070071200d80071034040c5481c415400444141d80010410090b0340c13151710000d21a03403103034442e20703208010800380140c45140a104000c01c01001c181c1c11417156040542d08148402400c0003a500700c0c40448100d99250000d00c0441c002d0036500000c500300001c420799008401d074000c03d08600c3d90301d4018003a0140702d004042100944000d031a02c010340d44c420702c0302580d0010000c0c11406043c020b08200da01d00350880c0001100c252030300f1450140c124000c1400c0100c1c2ca4802c0d0420700314401107415203884d20348204141c2d9503240120000c3c0c00c001e4402605414048480200d80c2540d40128040d95540d4690070300103401c0c411844200e0007181d550b400074450510910a861116600400030042e98580ca03003248180b00c8041d21088044483c00c2e000074040b602008490301031440741070564814600307414081c1c4107004148405000e564401041c1041079400310301046040380710b00001a2034070402404075180c1c003403180f5040c0c1c20309000c020f20414000000f140f416424036040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 795898309 1250 795897059 795897071
    0x5040c06140f0a0e03030c011a0d2a1e0513050c070f020111010f0e06060307061715130506030c01050a0c0201080c070b0f1f0302011d030f0f01020a03 66
    0x3008450040a9204000480c0c4080c4469496450300c000100302c807000c50b18250060309440b6001a04507841512201075aa544200c902c1c030340f12004061211501382140c1025411409490b4a0700710003220414001c48400c0710240485221903001c000d01414401041f415842d560b01842c041072481c82c080c903441010300001c134009181d0306000d204c2c844d800060741181800050390f103014822800620403414000c40b4001500c005400b4410760b5100c003a050301c081804446088024140135019244c03034041d420450b41030000c42e070049020140c84004900e050303030564030740f85107485864844081c0b5034481c4009002c5450703840180c00040c0158000c90a8403021800034005440780d00c0380801382c4021584040b8114003540c000d100b421742c40051078001515054160356070b003504920884040740204600380502401e103807100d006119611804181850150440d00040d107401e02352650501000910440e8001d6620107200c945040300000d02222490781641da48107010750070400d101000285001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 795899559 1250 795898309 795898319
    0x150507030219080d0c0e04180c050d02030601060810031721042f0d0b1012030e2b080405040e030f09010c081306021501091b0302180303030a05040c 65
    0xb2414040311503110400740c1c9400003074010403015011041c020028044082e9500c2010b8685000d11842d15080101700e142e06006841c0601d1a1646504038034017900c1052105c1c00162400600541515424102405996070301043c0350380c2c0403042d1304010311052070b06c501106034a80c950040c2c00131000c1d40c0d00c0202d980c1ca1008041800d940e0440b40900035123101c080042d2038551104010582688500c2d201121070041c201283d104d80001c1005c40d0780644030010010281807a200341e101520f101e0700461844001514010440038099001d540704001c104ea07402d1088078200c0c03101a0007035503403d16003014000b9003040302240e00079114060259080010003828090040120344484070710008076820401c8000044418031030b800c3c401ca500c000100591401205250100b0004143e03a5006040b00b0b40c80001507441c80c0d0040e0b0204580b0303428005146d0505160820040c12007486240c01a00d13a42c41c0900d42e42648130100c5080c0d0180000424016103c40982160b48139900600322400a03580e50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 795900809 1250 795899559 795899593
    0x3100902032424030709020310211a04320f01060f080133050619020c0405091902030304090606020a1e050601140f150c060601020f03120a061505070302 67
    0x2ea00f801e54950016803081c0b041820540c091504000e54a410314000342e1100c59244c1043d41c501e50103190b820024001204004480010b10007440c2d110502c8803150511382c4c1e414004103c1100d005403e01d400501641c052000c404180d050500c070801111008100c0c4181c5900a01383c40c010490070035030801e004541d01d8414000c000ea80101050b12a030000c0d4100000c121001d1304005c0100500c900f03000009941d9a61005000c401030000c0c5000c3c104141840017920b00035000c0380c1540100e0130308040101a4402045281014a405004080c0303d84a4400a429445a40c20151155141100200c1d9480c0d0001d0110380342d03881200340d0002005200c00d4904207640c1d000009001d90301080041c00158a500001c03104488094141200100400c1c0081c2490461428a20800601103020014900108070107034101c01c0138000703003854500868403140c40307200d00040307015140c04640204280030b54990142004060000006a0507041040c009016903c4007109400500c03611110350404984 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 795902059 1250 795900809 795900871
    0x709060f0507080f040306150f050901150e18011e0e01082d0607030b190e060f01050c0f030403050d090b0a0c050c0d0b190506031009020324 62
    0x35500c0d09410081c083c0c0c2da801082d8040f401442c00040d040c04004001504d900039005442c0006017401d105504120a0040c9944960711091080d080c1d8001085038030303081c08069070851f1152070003035040940070010400e1074424a8084200c03888bc1c10000038529140440c0c8480010402c0410400964460411721840820f005641c0c264100ba4040c01c807800310028052545840038020300c0c80541c3e00c004040c10507c0031100e1601207600c419a40e41607252800002d242e42c0c20700e00c0d81000b8141005040d1004281c0203140074001d05214021040f6030307000d1710503035082110b98801c98504030180400940c032500184011101c9110b0890752107441230041c5c5140f81a181ca81030318a05201c0201c00c1218180e2505d50709a502d0f014050808006403524000b01041c2c900406400c0f24500300402d05900d102080300c91940c429281c0014040d10799800306002a20091411010405d040359000085c1071466501c41c124100340c061028501010310455a203100303001c0d070898058441d0341c252640e042d25107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 795903309 1250 795902059 795902087
    0x10f1d03040e090a15020306011e090515071523011215020708131707030f1401180303090c050901050d12050c030a1e051201090c0224070906 62
    0x100780014880180d507480281d40c400c10795012214031040baa1981c8110602c00e00e03041d940c103a000001c11180d540c001c0056089070800c04d480b507003c1c0045280c0140101d020b40107451040c003105440c0611048007000f0b981c2d0040c0c011450002265642d110300c4010560300c1070912100648550707280d0700840716003203a41280d0f544040c03c40025070544d81c22104c6400042d003803100030380c01c1c0f040e1300c0456206800350412007092400190410308043d84042d00c0150700380301e0259940400344c2880007d02031070904080a81c860340c4581c940740103080080c00b4000204246180030011503000083c1503168008000ba45c0c0140e400c0c1a90340e40b80c005006c510042406001c3e04032240010850000b0048400d84448413490314109080c108815001410b590002d8001d0380002e000042c468103240c245e03800c0504410320f50030200d1401d03840c000c0c00e140500051180311449076460a01c00d64440c0207202e0b00020748450144544200d10042a02d01d84a9003600c03d6400541c01c0c4001041040c0170b110300c280e803c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 795904559 1250 795903309 795903313
    0x1912030b0604030807021504030b060108160207061d060a171e040803091507020c01170114010c030e04020f07060b040c140a09080a030302030f0a02130612021209010f1d 74
    0x1030642c4c5a4503400d82c03000204070380042511914291402001c800792018505c10803400d415401c104000500b0360324086d0020a100c488500b00c01486500011140d003200d186041c810f010700e00300042c4403020a540002d9980216001a00f0000702d0342c451200302c51100880b4960901e6200d401c1c1101861b9401c0c0200310900040402140200d05400042c660004414045a2501040d8000e450580105595010142e40030002d001d58a60308840c01f02031511014101c61642e616100704c80300c1404a00804c513040c0702c2c504880d90107040c031921840c00c001101130800c5d9a509003408200e42070f0390290105845413407401d0494600c0d8030b4140a04242d84419980b002d0800c903d410518103030f50302c805442000c4c003260386000a1004403e10140c020a8021f44005840785450410007541d0341008240046182c0b0401c521005001183c0d82d56007900c0417850b003800c41003450106080240301e0900f000c034090520318200600c0c0f110540041021010703400d0b0a100c2c103a018550744151f1002c50f1f103844003603 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 795905809 1250 795904559 795904567
    0x3181c02061b07140714010509031b19180b090402010e01030b1201110a09060906052b09050708010f06180506011b03020a0c1d0f06010207081912030b06 67
    0x140c452840d58004254841441d03a00d0035034141e441101381c107080d00c0443c2c4960000d1390100000c4002d501401e00044080c24810f140128020009481c2d0300c0c1140c00c2918000c2c00650711103251524188a02d83c911100c1c0c855401035200c1003926250413044415030115401c00103060f9403410b10b43c00710760080ba81038545c0b140c0d00d1441d400543c00303400e945680c0340d00a0707040000090f40c843c0034080c03218034280c1d080360300383c1d00c2c010164010101d500c00d420540030f01c44020410065030f50301c101240d852414286024200b6150180b140000c0681c880300040120f0a0940444c144440441d2880c1120040380007041030f01009415582179079000e220b002501900c11a0740c01c03201159800c0180d1003141403402692800c0102c00e9040328200b00c503415130050740800501c40400800903e02c4001c0c20542501a0110742107141180c5100e80082115942083c0c07400460401e034000c008042c09000c180b02a1148004810386000d4194035000d001e60b0404040750854060601030f11070454180d01c040c2083d860 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 795907059 1250 795905809 795905821
    0xc0a1202011b031a0f1c060501030b0615030714120126070807050d06020f0310030b010504200a113c071203020705041a180f060d020f040203181c0206 66
    0x7031841c3d17465403a41c001008400315071648191901c5400800d02c81ea10010300ea5045007401c0d00003141c0140200c0c000c00d0140c03041d0781519160420740f58800090315041c998895100f100003101d0080c64044565170751480000300f410f001e05518500080d142013003040f079442d060f40349143e886103188214006078100c508144480c1c00c1c0300320346051560283c0c40c0075150002c17411102030f20b036004850f6900d83c0112043c091007044030354000c050041c14101e4080c4130929103560000d6800001e036803103003880c0350000350303540c40d4601a170040d82c0611800410740c0e02c03c0301d10340850580c02c1c2242c000030080504200e00c1444440c01020000e179205000d500514645080502d589c402540c003400907810b610440200007841c3c1d5441c0108068004541c840b0811401054240000c0e00d07070b401911104610a08200160b01002480140d4850011505c00d1301c4480280003280c000c454070480d01d50098000010444c0b007a82980c40b40060340c1d001d00444c1c42c0040716a0741c0e001801d9a03445004011f801500100781 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 795908309 1250 795907059 795907069
    0x1b0b0408010b4606031b0c0203030322020a17010e0105090a12020f100912020312221b050111030313030e040f02120106020618030405060c0a1202011b031a 68
    0x468402d002c0ea500c0e841008040c104118807140e4054030004c1d86442046c406a101140c01d440c440700c0c01c3c140000480f01170750000b900c03800000c00306a480c400f9051050851007800b424850317140c3d00030308040c51082c3c548664410403824605960341030340c205179011a08140501c80e00d0304c03c29540000e0805844584e8407494a00d000604c15421449810940d40c03034400c041c4090b07036001d0070309200003070700f06224940300d9140b4004404200a40d00144401d81050301c0150354990320240c1001103080c40b8140c404456200407440601070000403141000f502442c01c1040310b003066450980700d207088051503102c0d0a42e6440304490b40703004102190070f4400001d0080705a1810458020408502d04042a4a07a812a045044048179070000319004010564060182e143c200d840c00000d494110320940344e50740e0f40d208502c1040e0003035000103150642c20209028444e00f00b90302c901d44171224213007000001d01904404a000100750700c03c4181400017030007440741707800c040c2004813410302100103801040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 795909559 1250 795908309 795908389
    0x4b060a150e1903170f0910210b061e040f030b01080105010803040503030f0a0318080304060b040e0304140307030209160813030c02090405120a0f0207050609030303010b071b0b0408010b 81
    0x21021280906ca80407507030303554400d40308050805640302000c80103051400d210f01c0d507030610610009440d01884007030580300d003011120210748a521106280722051500061032050398841003140c40503a802008004002c1050360403102908000c0c0501c1c0d0301c80c4c0c0003135201c2c45a0310810340d140d441080161401000e4078054116a10741d4100020410035042c03c00c0c40b02e1424540441e81c00c04000104020041113109440c401282038034200042042040c4036a80c92245014184102400e04c42c003040da6503040002c00003441d40507102a0650410a03078010a182011a4000109268000041e0340c610f060307001443c0d1a80643e51510851210303028852950701c060420740e6a8041c00300203050a110100062540c1241035894a424140c5940c000f41040000d0f0001741c0704000030090828160341c00401c0d01d0646800e040041d40e160303440d1405900c0280d80c141c1c1c0301510b41c00d030600012030042c440e003d8000c8504d120002d000344142c10b410806110281041c00041401084180c0c614a0300301c079080d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 795910809 1250 795909559 795909577
    0x307150f1407051b0414071209110d060b011b03090515070f0b060a060207080307350405101e0e03154b060a150e190317 53
    0x1c5151005035280c0074241241041c10045800c0c2e81e032030a98071800c0c24440c902c440f07000d039000b5a11a0400ca0402406000c590110544003a2550250414415520810709108000801d0000c0f4010a0703d0050094002c04d4005400306818441c0b0002d400344000064485c0b03903040c0d0300c071544181048204032802c1c056508240c01d40d0001d011002c00900303540f030f038400c2144c052f0b023201169107040400c10a5004958000c1c10441d000043d0803c5880300000940301c0940c0e02083c124601d130200d048a19846a400e001c42101401c0c04c116440c12a0410008005503035040d1000604003003000401d80c0c8802c2c402e01c12203401802c10701061103a80c49440210500c610050680340c0d004451113054240380b0f0240d400940c05490503038000c1d80800041c00e40720590b0b200400cca051a01584030240701203002c100c180110021100c00108203070fa44c3c0d121000509045202000d5016400a000b89880003803400343d401030310a2551889040043c5400108403984220741c0c0074141c0c07407207070480d2035500300c2060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 795912059 1250 795910809 795910847
    0xc040b0f160c03060608010c080a0f0e10051e04021c080904060e090f01050408071202030909011d01060e300f03030a14011202010807110d0e0307150f 66
    0xd641d10052580200c032181ca8001c1c10103161050550600100702ca402d44c0c04102168034008050000c2a0005021980486140c0000a00341c7c010715403600504600f601c2803900b402601c1044880601c01c1d409940100003588800c100880c036560b1118201c502941c01a501a0034031201181c03030140c810b8a02d16003482900c4240c14010800c000c10180e4400d40c0202d58808054410801c0510702000b107008441c800d0342c000d100300c1c141903c0f01c0da9140301d40003014281c88144001d20303485900800c104c40c0c0c03443c809048103005607554450145c00120702e0041d0310442c09660000035440d8400e07810640d407210010100400b62030207881c000ca0507080d03841041d070501e0101d1030100c0440400e0000c1004114250050340c1e4910307241e0102d130300321030f030f0540300d0034401d01000f006100c0c5502c1040604c01083d8207090104441d11410b000340c592034800c1105014911508081510b125484141503291040540c11250a00c1c0c4070b80351070034070003100408080021808085c01800602c01c2070410880c4c400070b10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 795913309 1250 795912059 795912067
    0x4060605030d030c11060f0606030c04030506070801030218070801062d050c101406060d0e0a110f0d080906280201020a08090102070312150801180b010b030c040b0f 72
    0x30100e410320040c81144030200c1e41c0c90300c1014101c1e41020400724a8450180a070801d031500250100c014100a0b0020740540000b2002440160070307107003102c000c4d603000400c48102d843c009100030442c1c4002d02003207010b442d1501d6940e015482261441d4051421038130307504007503800c10030121500c4c0c822600380c1d0f802d82050001c00043d522010540d900b0400c050380c55a586100c0082004e01e000901800c19481510f0600c88052808282483d55007291044582e281d5078103030ba1484c0e001410b45505142c0301c502400684074100422903151038031040060b60000c010940160400194840024024000030010042050140381030b0f0018000980319140e614031280d010086800e900c1022420320025039070004610031180d0700604002d500030201c0f07000354030b00280c0340e0303008010245d20910315240301d44951054180b0381c112610140585100b0300204029450714a14100b40c0d03464280c01d80d0710f09441e500204010704100101c07882881d014459500d81440e08a500d544c40e842001c1c0302e05481d00500c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 795914559 1250 795913309 795913319
    0x1302060409020d1508250512010c02010c030e030304060506210303070e0d120819090c0312020a050a080c0114011e060302040503280204020a08160207050d0b040606 72
    0x14000d4000703462030000050f110410001c03e0403c41e01c0c0040c100f85048600d0300708200256001503590a07000c04d41c410000070b00061498442c55110360b13048640d2000c005498007160080551000c001c101241d4020310426104202c02d1f01101c03c900030a1900c0d800800c005000715119801094002c1e8000d017840c0103042100c0c2103400c0010071030342d0038846500000306101c48140c0c41000f080354a0030480f2034210301c50039039a031412034211015003241807001c001e00045d2010403900c40e441d11443c901100b8480182940707001142e81c800ca001c1254282ca4114040c060320307200141d041e050652000081441581c0c0d901c82d0300c0750f40c100f440c00002941d25000d048105180d5201c42c0390090100807206414000107000840d0b4160803508a03804051062104000981d000a05600444401a003d5505c2d4187d204250405a0300c000081d4001e4000182c00407111350142c0c1207403149101c075402140c41c3e0100d03d0700300d8941446200d071039070009043d002d11000c50b85100030160414070494002941c10790b21 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 795915809 1250 795914559 795914569
    0x17010f021c1a1c05010e061009050a06030210030c0212091c1106040914130b220204111e0a0512060f120f25030f05100203010909110916081302 63
    0x182690b4151800c60f01c0540304002d0309000b0055009501c03c06040b0303902d890320700c0da40f0983c0d0320711401d10348071b44640100b20703c2d100741da0028015503005800c9000e007801c541c2000e8042c00404500400611500000c400f200802400b030303a5585074002d004250825440760312801201e0941030940c3d9201101c0140066695954000c00080c180c4c007d0101d4070604206282c07440680051a408640084600707900000d25140440307a403052450300e166032a080003600d1040590712080c1c009401038038002c0840082440c8002600d41d0306035131010030b40c1c450310f003d40341e0ba05030003005124001304409100c00860312800402e282e501410103801d082040c5010000240c8200400960b18581d4111034801c41d40c1840510100000c040b0703d0b524400e24001e045c8000a0124070345c48090035030062081a80100030090113601030480c1480302c2551a56102c912640080c42c02e03000c11184000d01c9411074810b0f04101c030701e03503114441d038021055078003222a60541d1045802040211146120381800340103039a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 795917059 1250 795915809 795915829
    0x5070c0f240f0e10140705100c09060909020333010e030a0515100f06050306041d060a0b03010e0114040606060305060a0605210117010f021c1a 63
    0x303001c9185840108865541242034000700c0c958104020b0302d02c4005a40d810500c0400d04880c00e68000d203141040d401c04540f21110503c81c2c21340c0042c0010904e090010000300441801024503007000588800c81040c3d442000610410010074107102042103c03d02950107035500201417103400840c108200c0a043d0820301c580d00101c02c20318000d89040c0e2650b441850451550000d400528030024036480f0359658080e020703042d038000c1c3c02910000303100c0c000e13903155807005214060740c04c11507680303410001d050368000325aaa80a180341c1444010200400c02e4462542000300001d4603007901c0d00e41218010301580b1b10030701d40564a403409045030b00720034070440494940004100101d801e180c5440780c107507049913000c02c04060910080c418240d4500801804440040c140141ea400009072560903d4080361015507035035845030000a02074242405000850660700000c008901400c4d00c4082240640d20308007400c0002c0011800300c80792070790b05c145080340c0e035000781500b030344c00c220f0004031081c079 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 795918309 1250 795917059 795917069
    0x8100905091219090e060d0605040f050d110d031416230a080c030705031801150605072604060f090f120b090705010f0302030403200105160c05030a05070c0f 69
    0xd001e403d59000d40383d0001c0c00c003002d00307025440160a41000400142e1044003004041c0c085541c80012408221100341d0703010000d07610006480320740c00e00c40300142c2038a4210118001d5805590b00c540b00311842031281d4060181110364101068030340c4400400840da41011280a00844008241761003180000b418001e01030540b0311591007038860001402004047d045610495040c003e0001054100c07042d6a03005488503090111003c0308003445024040408281403010044140800c0055011000f814540d000da0788101181400005d00482100250401c1410a01c2031006000b283e00c1502c0d0600780780300515107001c00c01e032503c4149805001a0740404c07000410504c81c1400c200a000c044c1d0342c04444074000d88161460140040c0448400c400b00e2020140d000000404040c0511401c0c0c51241880151401c4c4681100361389008000c25503683c142694a002c004e80d4040c0300d4014030010f0b55100f0055800c00910320825201500700030022100070f601c200001c5200b02a994484000f01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 795919559 1250 795918309 795918337
    0x109020301150c02030307031b0f05030415020a0b010b030a150816080619051003140109022d060f16030e0f04091e0206090303070b0a0b01081009050912 67
    0x1501d03140180e02c401da101000c0b0300511102810400142c0c0d804800d940006801d810061300c9500b00c0e204200c0c0c0704031400d00050203845101c04141c180304001000c0c00990b40e19100d03c0d20030352075142c401c0c0d03510030114400400714140d041c014410414800c0185070805280b00d000b1903030001c4800c9185408025811a505640c17000728000740700d0514114040050010001804c080d040c407900d0440c0f840d01812b050607030b090311840031407005009120540000c5801c204100700c50000001c4c001d004e4002c0d098280d00c901d01d581242211f800c14568090065543d801d50000c00386940c80030b22a064200a408a480c00e00c14802200285a42040030f45411b1080c0d4030f0100c0c901180f000c0008003911017944038015843d214172840080c1c0d51100400305d601c00c3c1c80c4407230740c111424800211144140d42059815000112314034003084182c090380c6008889902060000c80480070045a81000894191500c1c05940c001009080c110703610058000685100340ca003903040c0c180500340030364442c020940b045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 795920809 1250 795919559 795919561
    0x21e060a02150a110307030207170301030320060618040606030f080310080313121419050c04090b221b06020c0406080319050d050c0403020a0e071d130501090203 71
    0xc0b9111410303640200d01040400c40101d40081c0c14210340030040120301490744c001040c100b80b100701c00b0015000140b052a41f5601c0d0707104d00d4000c0074a03500182c103040950039040c071019807c0b130201761640310345000b42202c41017450b080c511251001d0050800c1e1031686d6110008008980c0007114210454015103090340d0700c0c141900a852100429448024150000d1200c06440c2404030081d208031500302c004880350001900380420f92186d09a2451600c1c17041c144c40618026072114900040c038043e000740d80d0007040c070b0018070040d0b88120f20018070700c01c2207d000079000d00310380d00000700d0492500000742481c1c1c01c0e5942d0842904e54180381c4040540103036420049a0b0381003005009022080d207041c0142450180c0140d43c900840d000f11120a486055200388244260f003030f01d008440841c03043c0000d042280d400040303076200740001c0c0d00402a07445c020130050300082c2503600428a80e0b5031a00c0c40010b002000001100030910260301409101c1c0c5680c040120b4001c0313501914140100586d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 795922059 1250 795920809 795920833
    0xf04110a02061302030a111908061b070c06050f0c030f07140a03020a1227050108090d0e220e0708071401020304090e0115080105060f0a050d021e060a02 67
    0x60b2120041000300a03465a0030000c0050310045000d480f9980d000c3e03c180c1090101e48005960304500c2e94101020080014000031065000100c803402003006d403071075110302c4015101000091007500c0c0040c11594031b51404000071882000209012150400c0c00350819854020090031540319569032030b401000810000705202e0003882e6030210340c14050041200910aa50181d254008000d000c2c04d0418030303005841d81e00703000d007104103420341032298030003040751000d450b07103031400314902603580041c4038140001d6994400042c1144851001c2d101e481210080608000402c00c04a40c00040d40145600103c04e03460280544064440d42c003010380f590750705201459240220f164420031000950141e51080d40c1d030040110b406660805001040054903c800300e4098040e0100c0391260b50320707414001608607819404140500300c1110300c0110803005a04000030724580303000d40c66012004201420051800e110301c500302c020040c1a0181521120340010705503002420004096004000000d070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 795923309 1250 795922059 795922063
    0x120304060801090c020607030b0303041d091006060815012c09060a0b07060506040b0312192105150a0810050604020f03060d0804030210030204060216180207020f04110a02 75
    0x4050f0800e907400304510041144000e649200180144042c9661f8200200b01e40e00c06000321400b8184004280000c511803c00004c00108201d409a030507004d08114840a80700ca405490200c0d01a03a42d201c3c42e130789900b06016071102c580ca0a00d41400358450900c1d0401a1481c500360386615552108403600c5420f0b000c2c0074080300000c006034400d010313145080c40340b02c80060903140107580080c07000071039030303640808100145035041285130302d1300c9400083d01210700040000d11400c10441080700ad00c1c955910155149198200d01070a042c10300254600603030070550040740d225a20001d58041c01210402140c01c0c0d039039a0f000110190010250390300a02c0581c01007680209054034214640541c2e0f104100d840e01010701014450403699000c0d9040c441c44006940c06184c004200c0d40c0c3d8101910005002507100348642c0015000720140c8960f40c2e0601c4881200f19500566006c0e8001e4001d002840294007400d41242d07c5030510741e50441c03a4030365100e2120542c0d10680855038072a150840a4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 795924559 1250 795923309 795923311
    0x70e030a0c0b0f1e130603150315020d050408130b0f12060a081b010e09131b17010608010b121005071412190204030b061207051203040608 61
    0x2802a401000090005050004400102e90141d800151101c2450400416a12a0031585400900e904001c0030503c0e03e120004c04180100d14900c0514a03036405080d01034480b041c004450000e10000e040000c00c0b48461113a0481a01c040700600e01468419108221002030300c05480c0c10310b010622101e08449400b050004c0c0c046032562130304000351040e001c1c0e100d20032402000c1d0306001c40340104140703445040c40c4502400307054042d21102c0180580c448070070b40c2030408083c000b42c540e0b50b2024080c2004003081d0702864401421009140c6c481e1952058501d4407600c41400540c2e2000004440400350051801d180c000c80010400d60310b030189a40c2034482c460000e511405451501d40d011010026942001038600c45000c40c11f03907100e90041c0c91081d1030840f04c9100032000035807030716210a1044810b02c2003080240001c00e040c0c0d01c40b160307003c038052808014411803014010a1540c6400306440a1a4082d5011500c070a42c848000c95a95a01403180030f00f140d201240900400d900001c1103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 795925809 1250 795924559 795924587
    0x306031e0b0a2703030204080a140c01050304150e0f160810051338040c150207090b0d02031e0c0613050d06060911070203060606090f0112020d060b0307 67
    0xd02880b00c00380c100d0601d4220a9180843d511401c104101c00c050003901039400500080f01039541c44203d90900440e0011047c81c0703581203000d80b511100c0300d0f40c005c0b4103403401550040700240c03001603440d8000d8014424000503800d640308038a001500c01104210300c55020000b52100c1c6c140a02e04007220b454842580c0d02091883d04040c204655004020055040e40d17070408443d503d4180d083c1b20b5621600600700e2000300c5401c44420b840342d42c821103100305000303074410703801c9502c901d80c1ca80001d01c6207a90a1150401078009810800103265036401c0341c4003000004003c292109000c1d80042c0c80c02901d085c2c2d191450301120700584c0407802c1484202000f100542e8020310306a400d9000c0070b013072012070003918821702d100131541c0700340403050340110050809100100300c030740203083c0d40c180181c00c01c06040b40300340b10b642c000810324203000040d81ca0b8940c010f0030414070040c9030340c0151480c00440700750009a03942486001c40d560242d001303100061003035040841c0c0c1c03070814000c02010b1110f81002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 795927059 1250 795925809 795925811
    0xe1302041521082710080105150d0b0301021612090b041a090d0302061005120c1018030606050108010501170c03060607211e021b010306031e0b0a 64
    0x1048010a5a802c08154484000205202c4080c1d8034241c0c6a5004104281140c0e02131403484040900310480044a03422044a00160ba8001c0081c00c82d0420024060306800001102c00500000001c0d805806119030b90100401c141c0c9403040802d003242c00000088400751056212a824800c2d54206801c820200c2d241000c8800d050800307103462031156210365100108810a6084441100d1003514040c0c2e02c0101141000d90742814001e548034006d40b04443d004080c8000040d4514040c00140b84d07011521001e491048651b408000610601139044001d0050381004101c030b00085444800155108040005034542400c00045c41108140c0056060002070a680404c200440c101036a2101d00301080541c0c03965082c0c0071030040d0190120013040654000c55140f0070f2008050407010100342030380d64031201c480d00154100c22421091020b0007580146d4018802c2503c024243c0c130150030b045c1030100381c1640c0d964034105503402404000e0740007000c65008004110301e06400c66000b03045108 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 795928309 1250 795927059 795927101
    0x1e0f021c0209040c0c0314090d081303050601080c0a15090f030506091c0c060b011817010e1c05090d12030c120c0e0d061d0303100b1206190e130204 65
    0x640034200c0020207c49000ca24400716503204507544440380c01180d6948400b046441e20340c0e401104e1505d0325103000468490086500200d0f034042c3c009070b0b1a045910007481e03902c00c21324103491048180300c03240700b6000b000034451010a0640002d4035007002144951b000700214501103440701d0800541c05190009402c03000c80c880d003015800a0004032141c0c002138006804e01c0000c0047c1c62243c50421045010b80c82540002000582000c01984a0b40500000c5c8911060b008195031525049030358003030314a40002811000b2032084020709903504010341000004105520360134080d10b0106d444900003a25040755001d01342c0c0c40b440c0390101c0045a44180010600c100000c0c042c1740207908802d000303a011564090a1040c25004001c41031514507100b50300c1c824002e0b806071254811221802103801034400041c10100b5441200c1d0703c00d282491068560b100e180420100f00341096011000540d403550205070030140c0c100c46401180d52240b07043c01028540705210a0b203035a1032005480d40c40d45a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 795929559 1250 795928309 795928313
    0xc05010b06130f140d0204050604320c040305070303050a03020c1e19170a0c0c06031d070e01150e03010c05030105010e090103050d051303060e06060909011e0f021c0209040c0c 77
    0x42201705c0d5190b81250041901d0b6540c01c08134005110070344d1000c50b520713005841c9101c0303007582c55580b10210700300d80b040c141c040d514058450520303c40c074400201660b100101c10008030340f0a001810720b0030070130710380545005c0f5030071240b61a00000da094050420042c0c080b0381d003600310411000c0300000809501501c4c414040d2030360741c200291f01940c81c440140005000039072512230400255402d0703121800e00e003403e0320f0310300040081490540d10146840402c000a00e0100000303040d90403991801c90004c6180c1c24040007070000300e0b00309040000d0002c9804864203a40d07003805003628080c495603506440e985000c000410280c00000514081c0960900506c00702d80c02103209a81050281400b9940c2c404080020004191540c005800d043c41c00240000003800812168022030382164810403584030420320508840c06204150412030044000c00049031058104d074600b00307101107005040c1701821111038143c5400040903140740307900244a402918181c401d1420859052070130000b94075582d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 795930809 1250 795929559 795929569
    0x20105070f081b0d020f0403050a121b12051204110f0d0804090929160318030e060c1002040906060903050a0807060b120f010507020607020d0c05010b06130f14 70
    0x202d40c00c00d0043c1c100013440088408150112202e0805d185079080e03072650344e0b042c00c0351211640d0200701c40c0b1511200b00520038901c02d40c0007a100c90400e442d03021400f02c43d0f5940d075821a150343c100005000003402100345a0920b0b0b82a1881b46010300500c103402e01900040158601501b8851481210010300d403401080d05c11040d101500c1102900180b003007024117125250904400103610944848542001403800c0343d00c2d214002d180d0f40c210701c01004801364040d804d44480c018003180c4040c003140702c240401e00c01d00c0c445a0203100030304094907000b032120203075040101e130a03164516241c0000d420400059144168401801a46400c0300114207507604c01d510341c0c814000103401200007003002802c1c8480c590041082d104010f2580004004504400d0740301c010b0b100d4800800e5180c5000a2201800400c150b80303c1ca11640c050700315070001c010207443c60354482c00c00391500d44da0360100700000e4032400010310403240740840301c400c91841c060710003030307441059004014008401d040e540e0f903544076 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 795932059 1250 795930809 795930841
    0x1e03090b070809210403120504030309051503070302091f030608060a092a0b030103032106051c030207030c03081308010b032a09010303030e010f06030209061903050706020105070f08 80
    0x40941c954044d0b5040c92a0709614011034101505c011302c9200500200f82c0c1180050048032b2090b11030403401030381c0d001008181c3c0120b1000303901925003040003c0740b50b80f0a170b0050000240040242c03111026501000c0d040e509a000ca140109039144401d000e121340401610b03600400c0c0c4c800c14031903000b20b5500c2640c15407070815034640184410040f5804212003031110400ba0000c1e080030b94a0b90795a0038002c01e4010036840c00a20444940e141a049003110b00507c0d064400152004c0c1c045540c1141002003081c010500b41c6c1140a01d20340840080c4c6440307000b030007c3d405082020780381c2408150009007404590301440641e0b00d068640481070300d0120314269a034031203214500f81024081050301c613072020783c40b07915803105c030b854008000c040d01607002000c1181854001c0040c104840a00c0084402a01000e035006220000044080c603000f071159402082505089032031940d00d50340e2501d403503201e030047c0780035075190010804115070000400c06000204e14003031003c0d00300a820003c071100703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 795933309 1250 795932059 795932083
    0xe03010506100804141f0b03031204171e030610020316080a120c020109050111040e010306020c0a0b010803091306030b040b091606020304241e1e03090b070809 70
    0x1907010000341800000c10405200600980a8900b00e2072030041041c041ba90155124010300d1400c46c407100c1c582800416982c890038030b01c3d0303181c0c4107860320b888103e00348c400d41c0e18040c038801040000700c81c6030080c500d03003014030225020b03001e4903424520104040c3e4450203004804560061102e0194100d800781d00d140020f412419103070341c401000a0480d01e0000c040700c0050328070300380030320000015415840691654014402000f038a00c1c504c901c41c1107071183e44541c1c048095840c006002081681d802446c007400360300c04480c150041c90341e420038a04000d03030080015800204814216050a1005803e00710324014200801400c0d5a2580354440000d00041c04150361800094100300d410411041d2625140c400302c041c130380c0e07103c81c025603e80c014025011b000d420726102001e484800300f0905441a010380311200924601d4926018110355810070380c0402031b0200d40004004942c41d48c40350010003543e0301003800300550a0001400310054403000400012404010151a0120707031740c04400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 795934559 1250 795933309 795933317
    0xb0a050f0a0c17090604120914060c0a0c0b071a0c0d05100503070b0a11060601050a1407150212090f1b01090e100e0a1e0b03010207060e010b010e0301050610 69
    0x49030210044a2400703d5109099501e5604020b22540c1503001407103511132480b0f83c20120510710740d07000803510090302d40b0a180f46803024850703140d036515104010b030924001550841e180100b05441c0c520315810641d00031007840c6000900c0c2428410a4103808005850102080c0e106041c820505561031241c0c0e4400000c03242d4844c00314000e1031041d2000001860000d0445100c1503c41448100030b07405494a00c01103203041e2801400718001081039889904140c507050b080c101030007010303222131350140f1034100c0b80c40d020001c0c40c1c0010451102e07106419113941d40103071500b8000c9121641079501501406490b40907071030300114480300046640000400d40e00060556032090300589201c0074640200c06040401c3c1d003005200d00700f4418a1707003100d9a5074182ca015884075104134085900c1030a004510076000240c641691b00250030011880c80090001440c215858803849c04503030161000000781d0351584000800d940e4003460355629804100c000b003005043c64000141c0c0c880103105640180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 795935809 1250 795934559 795934571
    0x19080403021e0a03080c1b09010b070215030a09120201021207110304080118020f0d030206060409080412060f0f060b0d0c090510030b010212030105031b03010b0a0801090b0a050f0a 79
    0x2030300c03014548410860000c0c1881c07040f1503d070724080e00d641d0000c400c0601da5115031880780b4214140305146050028001d880c600050b400c001c0c1000d000c0c1c0c03000000fa6003011601d00300b0034111986600071446019026800250410709260035a102c0112413031241c05c5a0044c880c000c00c2078041c207240c0307030020001d003001e0800c050040144d0f403e5020b1540440119440d0074031303c0704078600781da5002d60076510031665403603a10580000c02c280302c5031a000c0a00140d2120700080d200b070a080d804410014040c0f4212404d003951444034010804c42000c04540858071601080901e2000d8040c4006880805006000ca1401d2003047c2059010392140c000c0665241c0400c00030b21409401c002002d002e01400501d048440c984001e000703003003003c5079140103104030b60401c1c06400c5a0030076641a620018050425000b0300511141141000350000340d040d5684d160781d040f9135032510400d10080924800204401080f41070440d040700c8000d14004940b414101040f0203189410340700c0b0b030311802c2c4000c00075030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 795937059 1250 795935809 795935839
    0xb040e060d061d010605040b0603090a080c010b0d03020c100f1b0c0308040f0e07080c0d05040c180c0207050d0c0e0703020f0313050c030c1f26091908040302 69
    0x38107003c56400180d1200350790050603c50064100c00252042034400784005c402c10750034401684403c440316203054104484450006002c40001c0c180c442c070880020590741c0d070080018041c1c04513540c003140581e201c034622405034182540c1d084080c03106810b060242c1000506c025108040c0514401e00d1004a01190800c001400d080d50014541003441c1d5519030742c4032981c09180072450300480e2621403c2d1000103038010b12981d107040c89001a5020141041103580b00308001d0701c2e01920441e4040381c1c0c101c010452010030300042c020050100c0c0d000c60046060000a420055241c2100e802148080058008a901c00c01c3c02d804854422606802c0b60b0703120207040703000740541a02807040c81030020620601e5000c03400c190400038003c400b134650b03944000b0201a40c5c0c000d0600d040784c002d1405695860007007000c1070300200e80c070b0090078500e0415800c40120900642400516010702c0d10400034170044000c100014040e050381c46032a12400c44144d140c52034140150f10000780709c0c902800350019 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 795938309 1250 795937059 795937061
    0x30902011b05150f040c090204050a1a19180f08060708100902030408120a020304240b0301050a02130f08030f16051c1404030c2105031908010b040e060d06 68
    0x390301039a1680e111207418a103854290130882560169521031040501080c0001070f8800c07a81241c00007406404620b140065a200b4000303c410784080391715043c850204180302e400082c1d042c41d480d43d80c500800490042252549080540001c1420861540709100302800020b01e02c1d0081d6103404e16070b14550300c440d0f00011116054002c82603040c008001e101c1003120110141c66481401d11503020640d4501c24805d00701d004c11203020301041c14107032902046443c5800b16101c41e18a60340081250101a00800d00752082582c42e0310301598001200e1244010a03134150000c0c00c01051556003940c03410042994901610103692044c00000a041270f0300c07454441944101c0b07600c8800d680f5088400301c8144a000007c510850104420715003015640f5440c108640039030f82d03c0442030001c80e04090003801f11230f4aa100c0409505001c00050b808560300b0070240512604090810503140c4590a005100d0a8180d020b1000c010301408140b207442050008982e1004082d201c1d40710460781824044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 795939559 1250 795938309 795938323
    0x911090d02130e120a030f0e03031501121d0d0519050d060e040b040c050f061e0d0216140c010807031802101d0f01050a140c010606080610030902011b05 67
    0x181031489001000703031104080c1c40250107804a01c1e2000c0107011241f0050000f61a100c4000441c04c1d00200300003101c1010340803580540f07481c185012082d0209a21901044036144403c4c0c04541d420480e09800a000c10071003081c00548070715001d030030200380008085486542084180502c4404603004000007040d81c0810028000e00907000e00501f0a03017020718002c0c0041d10141e980000664006c80d690030902011602c950000d40540d1409084100411100c1814031800c21520020400c00c1540c07141c50002e414841c10903001898285250324140761100500071010215070040c0c2c0030696141c0c2c00203c007070f900030001d04001c582100e030100e40070705140741e41c40c00950101c076207040421240d40c006c595100d10038002c1003c50000c51050101b1604a00c10110380b80051020481c285442d071080d10000044c0e103603403850074109004141c1032070960300d13107800440000741308100704445071a15881c2510258180c1c00c040081d40c0003500003d0600d502201d84141540c0b8035449607003001002c101c40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 795940809 1250 795939559 795939581
    0xb041401050c09031501080c0d06151523070f03110a0311300c030c0703030c061404020a150e0d050a0b01051f030b010e06030901060911090d0213 64
    0x82045181140b44102240c02011089001e4855440000340510034a01021b050300c65860003440362a41400130003035242c40c208011600c0b00d03120b800f0000c5c405e507160000405000c00010500c210006404000c00e243d0861541024100d448042d5210b40e0501408035055690891152440a41141020784000204000c9400507105981307400c0d0606a1046c461002d1316000803d54043c08040703400c400300701001000030312510f64105807c02002800c20300602e040c07240041a41d0030401d40e51610b5003040030310741c01900030460f158542010000e86d80b140003880100c0b1480700c002ea09050b00400e01201103805420201e40c808030589803510f004640c0324031b20123801407031a0564140ca1030043c1d04c0d08401201141c00300c20003c004241c40c07a010145a00116a2540c5070000c0b1000d00000c802502901003e03e06001e04442c0100e8991a0b580040d8801c1d40041c00200380346140848800484028401c0400030b00018400c0c82c1041e501e030504880344039012113060000a060b482003000400e181e040c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 795942059 1250 795940809 795940811
    0x60d020f120a06061416170a110705010815092e18091a150603010311011404150e040e01140403030b01090e070c03020f01050705130b0a08040b041401 66
    0x400030301100c0d04842240304088200082c80070650344d11054512891000c1400c590800c14002c001000003482a016400d500030325140c007001030306074031121480c0e2000340c5990004141c220444202c600c2042840000c2000303103014045072030050048101c201410000300e209081d41400f0a020041d101512106001c454034201d0310b0440c40603680510b021107200d42c100b034a01440c0d0745d00900c07201c6d22800d44402d82040c0100c440d494a100d81050410009009031610b00c1681900c0481d0f850303e40203503019611400440311a0904a000134100c903001c2c20090003100803c01051101c00072100051500c1c024505091483d100e4030400900904141e0014070060b40c6130503429407031a05100a19405940645c9081064030010001110f048003d030040d65008007029011640240c801d08076074040500070300c15100440825a1841d0940d0420782c2e034a0005003021450158030700c104510178000f0f005046070341b07150210540000d0040b00c0018000380030307140c21400003000c0c0f28070380300113001540d40300c40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 795943309 1250 795942059 795942067
    0x41d0106080d0320040b03090703050d05030603012a030c11010e2503051513020a06111e060126030301030308040b1305070506031005030604080301030b071409060d020f 74
    0xc01c080d03485400c89000390000b070a110011140c1c20010004041d80c9100f800101d24043c14030200f64a1580040c051950700d204921001011a109004c0e440c000c2d02d07180e0301c4540ea1b040c801d04141c04d446101105c1d82d1000441035040c48200201c850400748903c1030304000c108080d0035402907680c0c003201c000ca20610b500b489100f00082c14041440042d0301443e1400c0200946501000007810010f40001001688001c0300d01d94154100d04c4070360342c81840300713800e0203442c0a2940450301d40c131115404000480c1e0440604d0703541140170f20281d900d0000720060362410340d9254031125658041331103404035a603010034045503005843ca44848103080c40f442203a0b6a07595a280083c6010f901311404e60b4803440d904080392180c0c42d11441449180d820400070122241010200300d210307880640190302c50b840401c1b0004d0340751014000284203074000d282c4151250301d982091240008010540010408000001c510342941041178501002060740c1aa85171007143e101c0b4802071254000c01c50780610f01003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 795944559 1250 795943309 795943319
    0x150806010b040611070803070219030f1506120507050f010c05031305091006020d08150a06110f0d021f0609060909150506030318270709060905010905041d0106 70
    0x4000c0c82241c08a9a0b0003c00c840c20000c1c40d502c0300417600660543c1c0c0c200700014005403600000031010341c0700c041250a0b6059a0f9a50800c03543c041c42d40031030781d0274101008000740500b0741c401c61004040c20003820703a1403501691890340f2903056021341c03807049020066078a0540d1149415488080c4e010046990383d50190700e0401c280c1d646817003410b208210300000203150840c0f600d0b44a048a00c1ea030024441e001c01c01c2410703940348000810b880c142c611084601c018640d20700301e00100404e66a00d8181c400450029641e080c24a0f1045c1c080361035100621201015500140c80f1241442202c04034071588000d82c2c803000038010b2603000780296030800740c0100f001d00103a030142c02c28030f114014000b4048200c0e907000c000c0d00d008440c029410b40041c88032003800d0f6040300301c100f19640000e150b511310001043d05075a202c501c0d4900030f50000f6000c0200315205400003418805441c02d4200507110a1824000900540b000d000c0c0d640116100c0c0f140e1000401048605200c0d400c000c4000e00c5880d80315 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 795945809 1250 795944559 795944579
    0x1208030c0d110c1908250602181c021005031806040b0711060903040b0f040302090112290703090f060e060a060611060403050703020f03120f01061d0415080601 70
    0x30114000f61400340d0b42159442d605880d24080485510410300ca0500c0c0c0000452041c1c0445000c1c2c0c140c3c0c00c2049120310002076010701c0140f00c000c98500501501c0c046c1a024400098080074810307207000090802c2102507a10240c0405e03040e031842c9040c1d0350326503c80e00186445604840390081a00c00c050a003c20481c88a00c7c1510580c1c0c47e030f9841c099000c1501d052595400c042e191703490607800400c401d107c880850b400421041100525240c90329a4a50200d080000241e00150703000c4100e105030030400c0386c001990007070518510742d51450000854626460000e018046c5420f05580709001001c0100c0f002004060a400690030040d8000e01c103070141d1101da0032911800082e28095020500e140281030700300c00448510001c06076a13030f46a506a40680c8810000e50035440b030961a03a0407440100001c02460302e0548100240c0e040c602071810444030180c1054051002d0000d0300211100100c0030745800740710444010130307524030b02c030a400e48500060304090141e0181600100b844464 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 795947059 1250 795945809 795945817
    0x915090120181c0203062a0f04140d05010e0a0b0c121b070b0a0209130603110112150303050c0c0d02031c030f020c0115050301061208030c0d11 63
    0x7409012048950701031101c00c461184000b101d030400002c076001140340c10450030b002d0360045002041604141035800280ca4210b00301e40c1d44442506100902004400140b00f100c401d0031501d079428200317000f0070200282d900890250800c1e030714941190200d90350b203030100002d0040d00b100c001c0080c40c0b000e040e11a1645080103040d2070202c03140c0041070001d0310100442c1d164141d501c9800c0400e803254402614146108080840d078103009125500100e03510f0391190340151140c0341d00682e10505801800b034240c2240c22961400e07403900c001000803642d04211200541024684185a009040c803040010500704160b400164200071000c001c0503080b50040004014140071942030803852010000d0b240f242d0540250103801120f03a03030300f41d1a092104004188403a04010aa444201103d40c00301d8101c0038660001741e442e9142e5440d01d008412458001d00b030160024000700b03003840c020409a400700303c001408620000009110841c4100903074040720b04c0f515091107801c40c00584c0c503d150704 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 795948309 1250 795947059 795947081
    0x115030b0f1b18090c27060904050f01030b011a16051c02010b09060427111915030c020303011206020408190b07080f060607050a1a070201061e050909150901 69
    0x160100403d041c0542c08003550100340401c0003d8806c0ca0342030700040a448101041a900804280150901941c0d035002d514802d0800e210030301070641c51820080d030584010780c050003005804100d0341c1c080e4000a01261150340004590440400451400d00d20b000715064141e42c42200030407009903102d6040d0802e41d080201242d0b001000d80342c501c20030040340e5060f01c115880d0442d59040c0f5000020341010008a01c0c0070700c0480d0504207002004c00c6603042c60000f0241d90030044c880601c0021101c0410800c3c5101e14038042149042255020350b50344418001d820710040c441030750f1010410581c044a0241ca1000160381d2001c000fa8500d507801c0b61084000c036602c19603100003401561082e482d0354441d0110519220380750310b40c00700f0311a85610940d42a901405210800400304109a0307500741040300c4942030a240703103403909009003140c0e844d800c040c8101c0c45803004c0340f01001c00040508145c60084a0900340c07030701c0c0d5115503894001d200b0120b1407119121402c020180c0e60642c03110034446 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 795949559 1250 795948309 795948319
    0x717070b01063b011b05011503060f05060f1306031a0108010e0f0d180e090f07210b0a060503190606120b1611031b0115030b0f1b18 58
    0x42000b9211180310910128015240080765444000d9610850070301600302c0c603d5417041c4c002086070301e0381d900791400d040a03400c1000f00b90f80c00300100282c5100e0845c00c1107074690204442d0800070005816107140002c8244244102e101c18a0b201c5050350000009603444030040c1d46040380036000388000c880c240714443c0254078041010407100740100d89100e40c00128800fa0103d01500c44040d6400140307003440b4418290a41400700d8041c0300d610081d8050802035008044c801032001c0c4c174515001700c68207e406841c22242881c03035110481e482c50540243d1000100f06d4540d01c00050310001d00c0035901240c2d061103010100600d045011002000250082805200d003d4423000940c00d0002c420100801040b1444c0000c1c0206011000c0000c1c441611300d004a4240c0c40a00e2141c41d5400c040c41402c0c00c0c4003035004441d1141001d120307a080090303506030740c00320240c40d640700e6410304500107000c0003690031054001402c001c3c20517110201d980780101c2840d1210041c0560070421518820014059 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 795950809 1250 795949559 795949607
    0x12020127021002030a140c1c02030d1a1003050903090411030a0f0204060c061d1006171c051b060f01030b06040b060d020d110f0c10110717070b0106 65
    0x514030210440718050006e40310100031101c102c00741e20b195400b1b0442002d43d4001c8010b0460440c0b421150070346200e106034011604c4d1103072075801c04111140740341000d42c0701040b05244907554450884143e000c10722420006160760b10301078060b04510807241480ea109103840e4a0300407240c0d0f10b1002c2c500a01c10304004000412001c0c1c0f080c0304a10981c0035140c04988140740c020006000760300b090659540040100030102e100402561038204038405d0303840c4440d01c0e80010b1201807052500c444502da42d101c001d02082944800200c1d0554807460450100080001d608401c00025258154a10104030864400e4648403070042590380c02030104032031541418000c5001c520b410f004256010b44028120f030719120003000b6110081d80500310f004900d90721810400521400c44014080340c00300c0b1110b403513a0794010a043d80c1060341000b02415406e140400302c896860400c0d00341c400c075a5104544100400c0502c2e03c0d0074540c02429001001411078000200d00c06030f00c4446108040c1c0c004e05900e107070b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 795952059 1250 795950809 795950839
    0x41a0a020304051506190b1e0310090b061c091101030b0306010612060503032101080703111005071401060302030c01051c0c110a0302060f060414041202012702 70
    0x6a2000796000b402c0d44e4001c410603c440381d40300145a0700b060300103028014110701d140408103240c44139030050b00340a00c0818a40144d5041880300075010329040c408510714682103008146a0401e801007642c12660340307076244055140c981c2200d90f96000c0f64030601070300300d80040000c09440d00321300840d0903001c580b503c080954080d0144200081c802405806140e0811504131403045040e24074044990b101da01c00501900d0134801441c0609920030014800542c60400b80c10a086c10303801a0b480d9807190604002103884800040c020360f07021980300d40c0c0b148098408503554011114042d204440060381d1058422055010108a91080d0705940e004484500150b80c0d41c014603085880d0140b004c12003004141859100e15544c40e0141080100e141080c0440d500d0314031042400c03805a03022030103000506005814542d4000000c581c1802102400d1002050001c00030b4801000c2c485652100030120b07000b034015159007800401c0304d8031405001032094000b062014001d80c02a01035442100d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 795953309 1250 795952059 795952061
    0x160219050d0b100906030503030103140c100c0f17090f0108011203032a020d090902070c030f26070b1608040b070e10120b010903050c040911030105041a0a 68
    0x4640d40109182155040c5454010781014014910290120352040104038401e00b441518080c600441c015a20780d81103181a00b6403480e50210303020164040d25142c1d80740d43d92031a03c1d00b01c1c40031a1902c28044882c03450500c07484802c420b0018440317006560140c510302005405815800c00c122480e902104680c40191a011800e0080070707110491010000c0119019420051043d88586031806a03000342220813010034a100e0b03103907401a04031041090b0f19681c00390306c178000f914101c401181b510759280e4891188048034803008107504684001c44060000c05591080c040021480001c54048621806a655800b003c1c040b01c4034002a0007003400c41b03850111201e0305035040e40361004551629100c0050616005242100f04501080c00300c0c43e546031448500c084000c0c0d500c5911030711409038100d10646030038081050401502920400103d1400a0b0381c0c0704441043c2c4000840351000e0804040c07045203640e40c1a010340c205028030007003125006c411040307910300100c5425a40c4910303600301c2c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 795954559 1250 795953309 795953359
    0x27050c0d030e01030e0a0b15010f0207060f030507020f06010603021902031326010e01020301050109050904031218020a1206050106111506130c030b10030e030d05060301060b1602 78
    0x140000d0381c24000b094095010f5400203000000c0c9804483c1d62403540da071001190541202c000c0e00c0700d45802e031401e1030740d6001040310500b501180081c144690912000038200840b01104800b0992620045031070b04e80281f0950f070607100e0035029a40b407581c40d09000780103940103c003240100a0804144182a4404806d40c3e003002c2042c2a007045c130b9860308016295004480b0303500d000034205c2c0940c0c00a1840c0034800c160b201254200056180c0d89041c1c00500181680d0344114002d420314410072001aa000740b210004000d9004001070900c161319025000800d00344009400c48844030002c03442c04410030801d441d0a110b4003080c4900e030303200d4004440c0c1408404000003141c0c000000c800001c15200008c6620a80c098440078242d0044842c41c400e50300c9010034500802d0f43d441603003505040c0b000050404074190b0409221460f0311540313141d602e100d0541c002c101140c0d01c1c4081261032742d00f03412500c001c08170401015121400c1a1900c400400c16081c204d2003031102a21000c41c61652903952 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 795955809 1250 795954559 795954563
    0x71e021206041b082d030310090b0904151d0f031201080102070c090b01020a15151a09221b030e0c0a0302010c02193b01060c0627050c0d 60
    0x352184403031101c00b0718007401c04070514074083c0c1160096000280c4c000c00c0914402c41450035122801440c05201c0e8003252b188142c1c20303008018220402c0041000316600602c00060100d00140c910200c03084961140310a0b40001d906006045000824a0000000c2c0c05014104151106c0c140d903100c0b295401c074030410b00010104a40540200000c44696200400c403100600541d8032010390b41c2c2e20816485500d80d076040c252503a880c403036150a41400580c5010b020042c1c000350804121044c91883c070f019003446107200c0d05c0744c000c1c113405080d007421001c80d084803510024003c50f0b10307148a440c0603030744030031000f03001a03d0012104400440013a0a0101441c080e140e40d042c2411900119180c10986905036049046503865266555441d0a80001040c20000010911201103183c0c050035010b902d40800035078441d903942ca4412002c1440c01c1c1111242c0c03c100c0f041c03a03c540391030000340004d10aa490341d0003001c5002810b803001d2100d051006482202940c0300c9150143c100242d0700010000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 795957059 1250 795955809 795955813
    0x7031116031b050607120201200409020a11030708041d0f0708180706120b190b0c10090506070f0f17060109030203010609021210030503071e021206041b08 68
    0x800105a26607185000c500b920102c1c00421629034000c2682ea81c00644210f84490362100508200e66082c801c01048103082041d50004580e0045804000e0085000c1d070050140d001070200e4650f03015182a841c0720f60400c007903945a103c00e08045800d500548030703810325484e2015230021469004500c80d4803400d00d400780003c03240c56120341101c05040c01801d2003020310700c500f46290300640410084009215642d1400100084000c040c0161100358004501070751100514a80d24030741440e10005032845200c2c95a1100720a03070301103150454400c941500140b030542030034180180803541ea4881d803240e4071001030200d0380b618125080100100044000780c0350a98000c203004000042d650040340524280e0201612600000d0031100e25034400c160b103da0001b0346c0941740003a07840c15503004080b072050461341491512002d4aa205080c0c00401040142c1303020808171605aa03c0c3c8540d50700a0001041070300103049880e515203081e0740a8643c40c44864048103c0c42a030300b5403000360b0b041e080c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 795958309 1250 795957059 795957103
    0xa1505180d0f0c05030c010905010f0e070902130506120708070e010c02040b01091502030301050a051c080f19021509060709030b1306020c0d0f091a03090a0506090102070311 76
    0x4422100c2d920a14020810045800418808501e04201400e1001d150350000500b0301818034013542190501500b503c2c845081c030925800c3c4882c08110142102d94002e40580c0d101d000508040d00c01e81c00350009540f103c1c022610340c4100c0904051540304e080c1548524038541c60743c0400707a4489001040d958006038000e46040c005082c00c0e08403402846060418148154a405032071200b9408a1a03076070050b0320100040101c1e180c0802000010030068808000480040309400c50080f10385401801315003000034851641c0c0f05c40000c89402281001080b0408010194001d4503102c0c04201c01d13212030502c0700420040d00001c00d0342c2c0e000701960346501a81030700d590340b40f51000000402d460740b0194444405c42c0800e0b0140002e002151015002d082d030107900c1c0c0000b9113071020903002c1e4400c00041c26424480070190044060f0b5614030865000c2e2a90707a80d004044c43c1c03500440008104d400780c1410310404a070150054401035110391030380d11010a05503116a92200503100716940642441 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 795959559 1250 795958309 795958333
    0x6090105131e080a03020a1403040201080c0a021204030b060108060f06090d081c091b0b0a1d0a0608190e03030105040b18070c03030501060e090105010f02010e0a150518 74
    0x2449045a601103404034884046258070355030f1194014034070600100c2e80028101100c20303405030f0000101351301095410b00310300745900000c00e003107002400b003041075000045250507103008020f4190314070300c0780f40d980b5607403504d0f460025041001911050f02280070000030030b2551a185841144444000c1c01d8103060944a40800181e0300506c00c040d201150100010036107110015130100d8034681c00b8501003a040410300d06443d00d821010125040103022850500c198403d8208036500700521740781c4031450310f9901c503940301800d407000a590f6100d40e036120006410364002c40c80c03c0c410b40e100001031041d0050490f200c01a2041c82c0303850320403500100010f00c1141f0b0980c4c0900000d000161000c41d40c6d05c8052042c000c11102a10300d200406e02c00300f16182016030500400340074140310b2800c2011981600046040442d040c0903150501c07800d0406003010074400d502803074040c2d000c1800c4820b1312a96040c02c0785807202101a00c90b109003040009081f401820744c4250440325580300420001c2520 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 795960809 1250 795959559 795959573
    0x7061d06160b27030a0f08070807180905180d09050619090803040e09160e040210050f13080705060304030527060c0c0316050604121e030f020609010513 67
    0x1010300380a000380140030310307004400e114680f903500011801103030354104c0e031440600146510580d1404100c504810440d2407036100d4420f41d00000c02c0c1c10030248c1c0c09040700e9519001c0f02c0e15002203096610344010048003005400e40000c111002c0300c142e884400c15101c0c1103400349203a00895030080c804200f00d26901c4090000c444441c0c080f0726104503c640c0300c404080c207607070007039102d00c9060b49008180a41d46406002d2800e04824586119842602d4003d80c4507042d0030040c400787c4190100002000d04078010400c031081481c1d24034a40340d8802403080102c145181c0d40c0508040b900c40c480000c1f41c2410040200c03030059825480d15420010410308003210f000c03114020305203411460f01001069190000940b403214030210180a2511007601414076024042000c942ca000b5480c80800558649074101e60603503001c86443d9601100b0b5042441c554409403d2518040318954400320034198800741010381d031080d03035080e104507440340b070601400c1c1c1c1c0c02078032050b10084401010a00107400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 795962059 1250 795960809 795960811
    0x7060c0929040506160b07090e0403050901021f060609050409080405090a0b0301060902030f130804060509030f070e040b07020628090203010f021818040b06011107061d06160b 77
    0xd68001c0745003d4851010a9032900403940d02e03030722107402c1c603015000c210484ca8141e07400066860400101c5290044900d142c02c2c0250014050101c0041e0010580e4402d102400d0440c4200d600400605260f020500090040c1e1203184006500c0e800045800d02d0240294003110741c111855505150074a8100200700310042c0003050076076610a404582500c080c081c003401402e06600042c1c6900c0c0c0751691110990340102544030420003040303c400001e50709010342c0c042c0d500b9450400d0b150070301500800e103441c0000f941301d181e51103801400240d180295840d188240e1140c42c510215894500050340d4880c41600c50300c0300b0400e410025030f06903803040b00c2a56507180c04070021802c640c00c0d8001c17031308507035000c603803c03d0194000482da0611903500c0c480b941c00c00c405440384032650700d03003c0c03030016030450103000148100083c2c00416141d03071290585819140c02d800030388400716525580a40031050500c0c007058242e40102d4869214584001030710701007000c1850360400110301c0e542e11518124 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 795963309 1250 795962059 795962129
    0xf0e1f12050a05070809030c2104031a0a0b0307030c05090403050409020a0801170f0303130804030503030c09190509131b08100b030c0625150207060c09 67
    0xaa00c8205004012860107128094050349200107202c0c2010303013006140c401e0040010740c80e0380c81040006804d41000848028407000502882d00c0408241c002003d40e1040d50b1015140c544240c107a04801302c8044841030250003040c0081003403000080a042e150012840701911150b41070034100b003e81401400c1e90b41c018420328243e46003540700e84400c0101c0e0001160000041c85c7c5400522140a07c001d2a425600c20710b801054a40c000301d45081c1c1d00d01c8010a000b40ea10040921a0100100c0c0030a9402441d4043d0540b9261b00e4440804015a0407283d006442480e0383c03045c4004041c40d410f034140079603101820300c5e240741d565005440210003c50408a90101e0101980d07122140b2215040c4043c048070f00c007070114002c1d0034110b08e00ba1003500d407500340300e600318454040c5195160011500c021b403041c08001c05c20041140f0141c5916900600a0066500140c4408c03a5052a50007001a2842200c040002c990000300c1201e602c12140102410f038083c0e007402c0070030201080c00b00440070b2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 795964559 1250 795963309 795963317
    0x50414040b16030912080702101a19030c080328090905040c0e100807080309061e160303050405100c021902120a030804050706030506010509012106150f0e1f 69
    0xa1341da039075000d0f10084a000880000c50580c00e00042c540d06105542105281d00024405118002020710072841003080b024404c1030348004411207100c1c20a8194001d50300100c1075282540d5940d51035840741e05c241d417224000c0a0076002c0030180391686858010160740ca540717130110340d4107000b8407400400b40075001740c80300c0c2d1000a0000b10520f5a512281c8035200090001310500c1c5003090b580e240500540142205070001c0c01189815210441525a90140303140c264030b50505004000c6014800c8041c0850101031944680c400d142d010340107140102d10480c1260039040714980083c0440742c2000c901c40060308100d450440c1d60154140030982c65000404070790b80030310240007c918100c4000000c4000c901200200002c0c000d050000e00010486814240418580a00000c0c0f05104006540f03051080d42050212a00e1030901851800c8020740d03010044551100090703841d0710507123424100003407001c174400e2140314440c845106220b00080c00c54030b4003a5044204d08040107a20703018100304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 795965809 1250 795964559 795964571
    0x80910170405010c030c03020304050c010f09091118030d0f052a0c091807121a07110705240c01230a060b1603210213050414040b1603 59
    0x140c0e0385180c41805070703114400000b0b00100609015007915900744200e0141481401004013007400401c08039034540c824a08000c0d41844544251641c2c1c81d11b800811840340380022200409007000010b26010074208014039122540000301a03541540490a81c002600044c01400309401840a443c0940501c1c03400300126545480120309040c440004603010382c4030105082e513504182410030f4001919124072031304404c502c811296a01640d102d80c1c0d40301809492020180900b40b080344401004412050401341402d240041280303440f514400224064010009020325001500403040c0440f200d13191202000e00382d244030141c01c0070440d069295250a0124041401e15440002658002c2d42c84002c604003240131104072022908904034500080040035000e075030041515110561600e000c4140c521801d01804240000c810001c010500210703401401c0d441d001e80070401d84030309803010801e21100700c0c820b640441c0d00f0340b030160690b20100c01090315201d0f2040c800050600c0c40c107001c582 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 795967059 1250 795965809 795965837
    0xc0f030e07091a040f02070308070c030c0b040524090a02040f0e030a110f0105010b1c09021005040905091b270a0204060e030105041e03021204080106061803080910 72
    0xb510f0140700101101410340c903d00c030103407500380701e003142d00703d0011021800c1c00d00b01e50300504000d07030161030441800000342e03071a01010703c05c0300c106035500d40c41583d80ea01810700340780040d550341030b02d4200c01c5040640c02002c103901d10800c41c0d040c45401c5000080c031185440313400b07020041c0382000d2000195515a05c1c955174040d4100014000e81c2c40c0780d80c440416501034280745040140340e5000709150303418000100016543c070410348411152940c21900403400c141e50800040000b50f90094100c400301c074028801b80e4100018000b141e020800c20f120903510307a9802c40d21090f05d0310140c568081500600d50140c20414201240801d08400d900b11008291444420011048a103800d1141c1c001405001050f84203c40d079155045c1500244214201946c03804000790402d070b258401e80d0702001040c001e1500c200482000410b000308116aa40d8954140d140600301d80d004401c0850b20845000701d0044c25145881b0859420074000c6003001400d00800c0107840039010108100500c118104031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 795968309 1250 795967059 795967061
    0xc030605061e060a020a1b05011706150c0a0606150f0804050303070804080c1209011e0c0818090c03060a1508010902030c04080d0c021e030c0d0303110c150a0c0f030e0709 75
    0x1241f14141550340782c0520300800103094210b5207111581c04554101409280c3c0c95401e012000c00c04150501e0f074071040c1c50f08480b490719042e000050982c40c02e14000096800b041112800c8501d460ba07a005d40982d4803800554261405840040c070302c0e0300800000744010311580c501c5820030310820086107407401041c0901d15051025005038424030000814102941c0c000055200c0301c10415500b038010941c2071340107000c00024820140003100e0008009000d00c00b0201a0b1410314001010031803d41812074103200c0c540c0049803010301500601101054241950300400340703815459440d0300c400da00b4142c5100181d0000303400303030401e94010301011509400034095000201441d68414014810074010081d01e072010b84040284004022581300d00c42d203010403070f14603100003a110148034000d01d2404500409001c3e2007800b0030314003c1040700218202144c03c4900000355035004400b51203445000c0b040314800140580401e5201c1d4507285c0040c0079801424031100450251a042035990045034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 795969559 1250 795968309 795968333
    0x20c03040b07030c1b090501060825050c0d0c0b0a090807060e1c030e06181009050309061917060a03260310080601090204270213030c030605061e060a020a 68
    0x4400500345c0424400780c03002d403040a004040b64a080e010754140340310898804078000080d0710b000c0c4801c0c0340600c4807a01940884000d8154901180c0d241c03034500c040240020780300c2030101e44007102e000124001134494040d009c1e8058001500524002241ea110700040888510062007401104540c0c0c04d40a4200e10301e801c641c00750744001c14840c42d21030b10541040340c010310000c41000c00c0080c904000070000b842800c501c012031000190050300b418800e1841c0202c030343d03495000000049480b8265030008040102000e00c1d220303015400b06910300c02003084002c8a03690b41010710704000300040b0380300c6040c810311200d084540324941625000c1c810f2199004841c2210301c010400c10400a03070004210241c01021819002c50515040c901a6007101e280b4200300f400e002c0202d010040c84544c03c0e411100c20342d104800b6114082e940340f81c44c0d6004851840280d0b0301c0c03803410000640c00d081034400444181c0e10b45500e01840c5440e01c0c00c000c82c41e040050300e031045108083c201000075145c14259 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 795970809 1250 795969559 795969593
    0x91c080304060e0c0a08120d060e1e0903070f0b2203020102180603040807170c100c0905011106070f030b040e0708191a06010302090402030a14010801020c03040b07030c 74
    0x21480e80f00d030b03080c864034010004094a010703009401301008141c001060001d100c000d50408903a4400b05040e02c00068030142c3c100e0000383c5a180103001075802226105040c0e4086c006d01e0000e81c4c0d88800d096030310b0b4012032502a140c90f8019040b04002a07085003859400b944000c03000515000c0e40d00030f800041003860f0120b015079400150303a1800c030a900445241c101c021900140b861906c1e560b0000306001d505e0004181d50017000001510342c0610f019600410841405c6503105004141200c02a0003400c510401046640b4000724055105000c0e030390302c5006140040c00151580c6408031900b14900300340e441090b0b62640d03192400e544030701442c0b80d500d02440007496103034205034200e824503003101d40e0220580a0b2840c2c0c8000100c2900c2000803060300d080701c0ca10150384000068010744100e04003594001d10000c100310400d2000d030f0080c183c2003100c16200c082d6030780300e2007228200e2041d036980d2400c540c020f00041201c82183c40c02807154601c603181c6103030000c0c49651a0011414a585a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 795972059 1250 795970809 795970811
    0x3090614150901141f1704051005010b0304031d061e0c0d0f0206130c03020a03260c03070605040602040e040804090516170a0603050d0e030c090606091c08030406 71
    0x54101c9850101d542902504a01c01c2d554100907040b00082c040e8003c0110007101c075400c591030b80400390300403008100010210200b01c41a450070346030154035598000710b00301800e440c0a001240c0840306200b40e03845280d2549854110b005000e0300441414888480158406e40030800809060420450a08108142020651681081c208d12401c01280143c1d240030080c0c125160784189900044d00c0ba0003080c2980f82560358105820140b041c125103801c06500800500000810408000f000321000e411200d51615500416002c0e5200c5104030003030182c1651003444010041021076100d290803c1c8590401803a1035580c1512481d95001114140c81c04000440c040040303030580e0080590001e9400300a042c080580391010703000720390000c8008107488a05c40014200161940841c0203075810804035800c514403e03200800f1140c0700305071035020f401686414201401d000203218003490005200508203500b040c244480c14400002989401d1000d140c0040424188401540200d0103050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 795973309 1250 795972059 795972091
    0x14040f080c16121509020a05100207030b070507110f01020d0315080109030203031e010506070b13051006060e04061a070203030f0c0a0b010e190b04090611030907080d0f03090614 78
    0x101314910400c00a030240038242000034103070050b601c2060700820740b0401c5602d10307000d00191101303e1070000c907502700034044100d0030184400320390000040d21506115040d07840420100c0001d0001000f40c550915001da400a5a40c25900b80260089102d80c107110903859142c41d07981c00314600351466035074180d001d41c1001045c0902000050107114000c3c46136840b04078254900408240b4600c51140013400b02c1d00f0401c08075210120011400b00010b80180880e141658103c10040081c5203500c03038040880d4800c1d04014031400c0c039000d030200310b03040301c1088284000300002ca100d4a9010140480e814002042184201c0803900003515049031441c005242c480881d02e4901030018044c0c0100184600d00820040070352950703c2d0f905842d941010000c90f4100d90301001c20007a01c00c24030010865030901c4051207181011101851240d05044100c034081ea9071a1a11915400701300700803000560194007107030800d0300035004441001e1240200007810140040700300c65102c0c081c0c0d044100011001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 795974559 1250 795973309 795973313
    0x6130e070f0e10080c0f010c0f060506041b02190816110406170a0f0212030406260603060408031b030a090201030608070609120c12140114040f080c1612 67
    0x1910aa6119605411403001d01342494451030795450000407052080c0f10090801941e80d11890780c080f28117030f0245d0101070b9130701d5602d03041001d018200d0743c69002d14035003098080a84450180c0c040f4110710303a00a0115210f1041c030000c8180341100c02968403100800c190445c85002005603d41e8a02800605090020003400c10058452a6000071501e0f016400000600c80c2c0c0852551082d69200d85641c40b81030749440811004080e81c070030701c01240004540043c1054000d00c40c6504e1603459000c04e4449001e021400c5240e2005403110354140d8000d800080c009080c10f07004540000d20b036241003030702c50a10820880568421210700242a840d01c0c5200d0440d6018003810000c0c00c40341c0080e0011a0401c800140005200c1c0306070400c02d41c40703114000c107210b9404104009800007a86410b0030000500b01901c0307401a001141c0001d41c41e01c410000d00040083d08180501d03030000e0100790540c6143c0320041c80c1e810089081c0d185000d02c7e98429400b207148041e03480100700d81039071b48460311207034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 795975809 1250 795974559 795974579
    0x80f041e06030b06040f17100e07051c11010f03090206041511010c0813030903020d08070c1d0c030603160e07120b13110708071b05040e0606130e070f 66
    0x35050f550090310141300520442e1020b21003d020348080180e9210042040000f461403c5003c0d500310f0303c0d451070000d917842c6540300880e0347d80590b80c0980d0b10580c0301c26202ca00c014606241e0ba009001c0c031001040011840d8802e04980018400d1482c0c04121a4102e400290f5903074000da1014400c02000701c00f100340550002902c0d60b031442a04020800300030048070103001c00c071000f8580306012920105442c1058055102c0702d01130341d0040d020b078200080c180b4018410384d00078135050340c09000602c0b00291403d0091064684005e0303049002403c0d031204112000365030405000540d05024680007664105034148a1400416451252600701c0c01c055001403e1062981c0c030500484c2e080210042c1c0039160340703002100110300b21100080d40010400006514000c0501c0201742c0e0700c0025070300c03060000310403040030501e150f1050200d90560f03450802040748c1d8101403e82494206100041c4285007100a41041120301c0b06c005c140388010300c4585043c185260048418820001c100b0302282c041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 795977059 1250 795975809 795975821
    0xb01120606060512070305090f01050c09040b19030201050a0c1a0106031104030308010e0a061a0c10060815061507081b010c0801030b0702010209060316110303060d080f041e0603 78
    0x1890500c5850038200d44481300202400901e843c0c18541c5035404a403810f03000b00328800c584001c40d0001c012500b071034191410180d03c40719515100718105a2444c5441c42c283c0f4444030041c0ca1404003090480c0340d0340c01510142c004190010038001800090408a03250040200c2d0b000c00d0403412841e50360600354090100e60a03a0301e2801114414001440000d80001010381500c5602d00b005d8034507a126500c240241c401508101030311106000c550009020100161848501000a90700501c0c101d503400400c0b5000b41c03003000080c0e4040389011141d00304e4000c55a8008c02e000d40102400c0300301a00300d80190b8800c3ca412200b08100051035001c0410101800b1f0000e14524020f214081e403240c4000c29440042c040900891070b00400300d174440e030003507040318112440a000d184e260300d00441162480e2009030950700c0465001d11444000d5200401220700c0340d240200509a5030303500e520b594072160072503e0904035980b400c00c000300d1000941907261000400b03681503158000c0c01c00c64001e0607580 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 795978309 1250 795977059 795977069
    0x9060a1707180b1b0a0507080601290c0f0d0207090b04060303050909150d0c090f1118040b0303220f1208091801180b0a0311060304030c0b01120606 65
    0x80405502944054407160000403114500301641d1184400c20200340c4c001208045014a0b100c1c442c545800c1017030110f24030080b2490f903402e4480c20b07031b070f00c500384108811800140f0503410074041c01030440c2c0c081c400181c554680e00c0800c403154503e001c803445150004490300e20f03000d44d021401c2002124000d02400c001c100007600c3c1031040390300e50768015055000300300c40e461040b4103180024a03844542c110381d2548110003400c400ba60030042c100706881c1100ea02483c40c1d080e042c264140030300101c3d8044d2600085c1c190300d003e8609803403001601c405c080019200d69000c7c0e11001210000d940400103400c00510740c0360000140e40e04030041038075812107907200c1090140807560401254102200340702d001a00401030a559452010000700c012440f00581c131003500340700002050150404142c10031444040104006551141040000c9880d503403200a0148507500000c00c09802d0072405190018840d091800ca5030142c0d6403500c600600903044440920744045011041c014140580b00081c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 795979559 1250 795978309 795978317
    0x705040c020a050a02060f070804030f060f0c020718022205041b09121a070206040507080705061c0e071202010f1b020f0a0510020f0d02030a020604150209060a1707 72
    0x1211a50f445840710035038000684500c902103844410001d204088a00b1540d10004041c2c0e12a1a45031203400705400a105464582c074140d10407544029610542c00070304003e03002004014a070a101d240f240315100d4000d8241c0703400780040394145540e50079140e0401107d00400005ea1300301820301040320105800702035608400072400070400d4103e2030441c1550049080301c00e40c00a00c0c1842d55801c40e0301c04150310002d0141c020840603035030209201e8040e42c45142525003566880e840c8030707555135082c0140e81d070001003042010150250780403459815520036401042e00d42e524100ca9061500c2607103c5001451040301d114110340c0e00031064924031149081c43c160540b8464031081c90710781d80840c024014081c06031800750a80e155440d100050a000f403800303008801003c0000e48969068608082510440c4503000c119800072040e41e10140d007a60040000c0d5459458040000e04c0308210b0205040d401c20180324107860f0709c03000300800c0c001da4465911520500c1c914030899000140420100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 795980809 1250 795979559 795979573
    0x904121107061d0306010e130c1208070606090605060d0905011409060406050c0313080a090902040b3f0703060e251e2102040f0501110606033a020705040c02 69
    0x15a40d441708503810482900d000d80440c0089d140c91100c043c0990000d08071114a602903208110a10f0000d0040d1485404c051014941c1c510041d030554141e03000e580d40c002018003800030665029803108150f80e00840000c520700d900c001c201c2d4070018007a20001200e41000301080244006c50089603005a42a0900d41c6076150082e0040075440403a00000c258450000318040124071030f0313500350301400030020119070312650b45159415580c00406035000301c0a40c0000c41c400032900d1a02d605401d1048010800c1f00c0d40c02400420321020300500c2c0707500341547d440020501400b400e80203481051400d08100850000c0e00851486001c20000c800400c02405403030500304220149201100c50b09050403035809104000401c1d498040c0d400d041a127920105000840e122144402011103c2c00e0329407554020a025000c2e8584c901120216010390101d00303036a15501604114400c141c4072203060104038003200d4405601c0700c102402c81c10042e402000306119510b060b01c9250214400340c0028035607 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 795982059 1250 795980809 795980819
    0x316030e130b12150117031209010f0b0f0607030e031504030503040c09050412050d0e06090106050a05010c0f02060a0c02040e10050c0a090e070e030706020d020d0801050904121107061d030601 84
    0x108014006c00b4410810a250600980420401c2c1c8480c3c0504007034144c1e0f03074a00009402d00274800300280038007403424010203505500300007102c5402c40801400c6245041001c3d1401d0729948030180d14203801d4410441208511900454a03500443c130a50342d1070b5a070b05181c2040100ca8810350000f2021528040510000800d041080098000307903007000342d194905462124020807082c000144035010780c00800588a0701903101c54103a03841100d0200109031900d00461340000b0903440248400618038801c1c0c0545031820240003010100e251a210401081c0c0c0410266180d08801ca40d0302c4c5d0045100b840c10000f54040c003503008045c1e45815003440c1e10400e006040c0740c4144070382041a4040004522820310070840c0c250000401340407030f20015980c0500130358407140c40c01260018003500e02c02d20007681c400c662150484800400381403640c2c81d5516408028140f1010300c0c03044c8000050340c012000c400703000b018003d0115803100d420288a01e040e62040c812a109290b1180e0024001840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 795983309 1250 795982059 795982093
    0x70c09050c0a0806030f16151e1209021c0510021c0f0b0d080403030f09060e1c150606080112020604210c0b0a200316030e130b12 57
    0x2042e10b070b1071400440340c2c0c8403070010906055a1010810380c1c1d005181110b1682c00140013014229a90000c5503400c00a0711441200c2c174407088101d001e200c05220b000040c41078418103001241c10584d000001c4c06054980c00034034048e02d10700400f00d0702c0a02c0319100007800300901422100068031503040d480c003181c024042844400011024046c10b64400ca040b40b2203880c0c0d404007100c7c000c040c003030b401c00452a04001c210341d002440220005680c0a9005032900d202e40b000f08119141a1958006e3700324040c204900402048551195000c0c1640c108002c1614400c4410f010b40c42e1201c001b44250501c04010081f42e4140c10181040120403400300040c1c4524003110700300c0d8086c855581141d4518a61880f018240303010240201441440c0466400d66440041010389920385903842040d10700d42d406058030b864580d10b60b160b86c10030f110b19250b281044a0507096035119242060075500c009000440c1c090048002c18045980c55034000f00c281004a11040c00c00900c0005101e68451005514 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 795984559 1250 795983309 795983317
    0x11190320160c150203070c06020106060e090c0c120405100e0f0904020a0b0d05011403191e140102030406060509040f02040b2b030e01050f2505070308070c09050c 71
    0x28a4210300300c1c010300500820842250280498107012940c10300e80320320080da203030400303502501c00c80b041c110002505401403049800b1291252030b204140070f445002c1144050b0000d00d81c01e01060b007000150072692040c4000c6181007402c04195845034142414070101c1c071071540c00300f000d0211040034400309541d9214204448031080300c40301080e940e14800702d403070383c00c4942c070038948003001282080d500e00c2d07283c011a042e280d10031805020109004201540d80901010105c19005441150300103d241c9030103d0300460309440e0440340c003407619600e46160844141a13084141d41c0401840200b0107640149402003404980d4200300342016250300c0c40304039114000074415595012070341415112102040e003001e1042003003150804e84890007400116614100714006210301506240c15801032090328140800004990302308070240c180314440c0b40503000306c80b8000365111014400a0030800c1004061445250101e84a41d114900b040600700240c1000c1101d41c200810042c40c0100d402c199 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 795985809 1250 795984559 795984577
    0x507021209100c020901090501140d030f1101110d060807062102090103060f0806090c010305330d0503180105070f03030f0615090512012c0111190320 66
    0x40c800b044811009940c07042c2c0e200c00003508045070100006a84803d40e2001c1c1c100d441c4682c40242d07121030001003050300b00301400700a020415414120905500c513228003980300b40d40341e0000913003014900001403250003545480590a40718141404900002c0c005580100b150781411108285007907402d25614580c0007100040603404290350005d68400e070002c1e4002d0043d132024152464650702050f840d024202d42091f010301c641d0003c1d00e41c6520030b115181c0b141c00c01c3d00d00011500302c480d107540003041501702c452010302d80442d89002e490340e400c0c0d0044034a920441c0115510b15100d265055058100c02010381032120500c40000810088035140d1001039051400007003c0001c04503e10042078150006103070f403081c10403041e001c290020781d2042a1182102c1c558042e5110441c45800d85244441c244a403616103680b1350241108640204140c03400d0200210300102040301d84111500001214203400001452507181d0b00e805116903030501c260744405000d40243c0f891603818500c604044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 795987059 1250 795985809 795985819
    0x70f0b040b0f0d09060e0114010e01090902040207080d14010b0f07032109030504060e0f0f09092b0905010804030f0818030708130b0316030908091908010507021209 72
    0xc00c5403076400c4800321803c0048400041291160310709182c40140140a104a070b10f6180040e540d0380c2c48801040399048030614106141a42c2c00c08801c0000f410301174500b01c0c1c000750280890b200240485001d88a0100d14480000780311306844254009400180d0020000d03030fa08108041d01450342c50200e480007a0582007111807821011200e9881441c6030301c10000c06841d0041c0c5904040d40f103002041180c40d10354a1181100310715040095152500c1d00585d406500446034407040e040c1080da6607401f80b0740034195400304c10204181607130780014484043e21007051030174010b0703d01d400c4220b45e00540403c0c6040c801920f0300365405408400d2030540e0809009444d000074188903a6005030461140c0b401301900d071114081d00d0610403640000032a46480c035060381000c940c42c01d400040d03e120710440c04003100c0006100000f54000c1a0000c0306492801c1c0400ca5070515441d58100050f00c0034140055070152450095110708480007c0c0c040781c11508400031801010184c401610070707010080719 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 795988309 1250 795987059 795987067
    0x3100b181c0807050607020d0201150320180610052109030f180301050603031c0c050d11180102010509070b21011701180b01030605040c05031b03070f0b040b 69
    0x60072036046201c00c20001c05214000500204011001c12064004c80c0350ba0202e801c0818031035000e80c261010000c180c00242110041080030400c0c0c8903404520149480700c0703442060444010a440d5111001e203191050b2040c000c0c4160703810000c0700500d2846940c90460300b030501401c0030b5600b6103040b0520b0301100040b400458103a09050080781c3c40b561101445680d6006070106400820458440d020300c00c0d440c0000166084c00d010040b10003081038400440041017008510100810500d8510401c00c1014084000340582c144155000f200781581456210103a1401b40c0c071071220503120b0070b8110790516083c02043d480000300c40b4103803926540c3c03154036841480015240c0081c1510700d11f10038400b03c0300003d0034101d0600d260b8404003151009110b00e01e803440c120390f80000c800c6d1000b050580c10400400102e40c0950040390800d101d8021030b0f034820366400001f03140c0021800e0f04501444410160307481890708001e240c0041c40c4008020740c8207883d04000181340c0c0501d200361884000c0c002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 795989559 1250 795988309 795988339
    0xb04050609150a09050411030408071416141c0803150d0804150f0906020c12010e390d06021606050403080109140f010306180f0803100b18 61
    0x242c048098040d21000c05038484036064801010709845100f6035000300c1ca015049a24030100c072080740e02c542c1d0080e91081c5800034030380d10100d420040da8100440c0740603006405040301c0c000080ba200601d0180b10344c40d1001030000c10070005070386280055480e80d000651690000d1051820350380d01c00c400701e034130700d120300440c40108005404089004194206c0060f011410034840c8e8440500780003a07560304103200344110820b0f034040038a4082c46001d40d0002c08050020f2810f4441c840100c42000000b00d410040c5095980c0b502111042c240602941d20f00d040301d03480c1c1c2c2200d14203150451000060310b00030710071020909548034428042d1002e5000518850140d4240d680320402c030754001c404100c80c0c601820010440c2c4020f00884c00d50078280942c2c4130400140741c000c58052141e201421005918680da030600400c000440d403004c0c0d84a1035451004100e00c100343d0a03210303000c1d0702510703075030721340000080c0b0014107a070000342c04c88005200c1c0b0040c1e29029100c04003000d43c19a145000b03200c80c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 795990809 1250 795989559 795989569
    0x3080604110d06030302070b03040c30050c0906030c130f09152c06060d0c0f0608060f060304050a060504080d020d09032c012a03110c0303040b04050609 67
    0x481412900c0440004905030282c0c40c1d0361105044031300a070709a503226500c1e0303050b901c0548000d0f5000340c410000e0130340901c080c00c500301c0c16040400141881d001d80c01c08541898519101c50310b0140c5250704841c403804680e05280180b1588004224081e15408a40c1c100181c0780900c03610540c2d0b402030fa1250b02166230106503110201c0103400841409041c11500d210001600104031603c140e4401000c00200803d19580b440c691302278023a010700841e60b2400c0c28800d000c90403000c151044200d105000403910080e10f6104007a055540d1420303000d1a0010900402d100d4110029003d1142001080007082c1c021522110700f503480800811651520b003011085406240d00180100d84001a01d2942490f16888001400d10070b0701c903091300d402c50084084919040c02c003c0111841c18036581d6480b580700d5040c0d56042d000c15150729000711100c1c01a040e400c400c0110440201d81e192840c140155010003400d2103208040300207501e440c1c28100008514000c500c02d43d0700511020807005400c0d80c81c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 795992059 1250 795990809 795990821
    0x6090d03143c04030b0f041703090d140309060115050d0c080a180507091e0509030a080f090c0d0f0213050a2009010f1130070f03080604 60
    0x108a04116034202c810201e003900000402500c0120106140c180c1e0694035103000343e4080301d40001d40242e00e591401040e80130440010011202c0c900080c07401003000782d058001d0350052072500002d14540e18a40000790980741e81e00151501050309004000d1003540002c4e134241510b424007400b0103d89104041580c15004404034030340e95600308202d84d15455030088500c0c1c40361810b824240840300007142d160344c035001405000780080c2c01040081c0a4460103404c03034008403003411b14980440501c4211481155000d952414143d0030019107020420341c8580c5054010841c03104441d2181082110541d542c0d4180e00d503913009608240d9008180942100c021f81da698005d4500d000075440700d0440801002c0485030054002c1c50440c1010103d84d500050b00030741000318170f5092900c04000019070360006610703c050704000d81482140d10822050201401880b00c55074400c0f030b4140b944011481c0c0c140016080c0310841c1b018080d0b140800d4903606407481d102e800d801c0c40201c50315040045030103084 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 795993309 1250 795992059 795992077
    0x1802031e150a0b011d280f0306090302150f0402090402060d0e0606010210181103010b0d050a060c030c0203120c040803040803040e0108071211040603020d060f05010506090d0314 78
    0x8401c0c4104864a0356a801c4100145004d0382c40119154980c5a80003001d101c0d016900d801544090303000d14203220740a400c0403003111400d440c00303605560300181400089203400c11038010303403500812410541c04102080e000c20141c83c00c3c400500d44400c4001212000401c0a44682680da01040039500d4034003c850341212800001d00141000100080d0364100580351240140300390175208969004500c0381d15100303e0303c1e80c080c14105145869124552104098041e415561b0381184010f659448000460f01841000980480d00c20390401ca81121807900b20013003498101203807416203030703400302c102c2d0034002400c540170320b85848544a104040c0544d8101500910000401007094000000540121040d4121110f4103a8031a030203681c450680d88900c55402894520303c01c0010443d03c40d02d02c02e60405440024642c0d40c0303070000ba0b10180102000d44a085d500c4440500c803110070f005d0180074140c1540c400b481d10031802d002c5090345000e0340018081000c09101146090003100403994009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 795994559 1250 795993309 795993343
    0xd031b08041509050a0810050a2d0f0207151503020a171e0a0807110a0906080105070809060604020c0106120c060210090c0311030c040617011802031e 66
    0x692294000403041220000c030030089996500001014070f03060170440250b903541c4010706030311203a490503240900000340015494649646210684161031112032451f006111240b846231300d001e5804100b10f59600d20800d4109004004460225400e21a94411842c06c6030300014121038000924520300c1c02501b0003035120700200c0c00010a00942811004007040d1030003500c0e4035250020f203000300e8103840c81030224203070001001072010640c4200980021405556034036070004a160005084040301c2e000b480d911562405d051001c1c0c2000d1040c240d111806080240d003a003042a450740c0d80d14402080c06200326000900c1079000b101c03e40202c2c00401081e9030000d100b00c601d2404408a02560103520f00504c180e681050840005026080c0c445410055050300541151500300f42c5d4200c0c1040541c042c850a01c01d0411a1110b00ca400c0050024420914400c544a141d05095071309048907401c1340d0b04180d039a03078090307a40484c10b800710140e0000e4a055000601c6102400e00020603104401c00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 795995809 1250 795994559 795994567
    0x302010504030b073b0a24110607210e1b2101050702010c0804030c020603150306040507060f0f140a0e0909030a020c0d030804060f02090a030804230d031b08 69
    0x291104104a0400c050291600720341d44111051142c8401580b0a01d132600c182e064070000d10055000600d51f014030381d49008a03001d403007005050700e071032029140040042e0401c181c4016126443c0d1000100000e080070030300074001c5000c02e072503071001c440b40c842c1d06100889a075240603644a1011100155020040071002488185240c0c02800200d81741c0c00994208000c036190705109180d00e6110711341c140ca400c200111036400b4801c01c2e41000b07100b60b00c140480c5880450030781e4100085071247d403007000201040b604000004240303800d00009082400207420300030741001e422542090720514805295601c07124004030407240300810480064214098070f062108801003c001401d00103515002c5445400740d0740144003250803100e034058005001500840c0014215070494810303580c1c807160250420f0014800200b9183c1c0300c0e80101e03111000020300300007104003100085e00d0107000303009901e1000c111202168100c0d1841c200102000f00c040840310400f884c2d00c3d0f080300c00a81200800781c079 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 795997059 1250 795995809 795995867
    0x40b0a0906091a0108132609031203070c02010c0c030215070b0708070c02010e010c0c0f08010518070e1f09050a0e1614150d0203070f03060302010504030b07 69
    0x40c40c030780c058000c88504240e45100380103800400d281030050180e6441032640c5e1014040ca03125054058225059425407003440403000403c407001c40880c107420b004550f1801c206c402c042c500000c8230459140c0800a1040110385078014030285d10300b03602820010386150700303850000031105003a0002988060000000e0b8080f250f61000362070400d00c07a420788101601c9003e400d64035801308949100003d42141001f4005501c00c0908140d15101810040da0903d0650ba584600b03d1140e045440001f0b085202001801c80c00d008454108100030001c8075001d500703503041c070340f1030120f4001c121000680d0804908100c95482890b24040030741400da6000c1612039017100003a0000b40d4416a440e424849070104c0450085910800d0011500da40e403c15032030007010080d1004a0645240d000c02118010b0110182c030038003c000e04040c5020060f582d1900c0800903100440c1401400d0815191080510041c0d820204450640781c201c0d15100031035443c03807070484034071004a4500c0004e03048086c0c510701e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 795998309 1250 795997059 795997061
    0x60e0f0312031015020703080d020c2121040203060703200315040c0201140417250204110a080c030604060b0a02070905280506030102070b1e060d120e040b0a09 70
    0x1080d02c01104122425010001c0c4c101d980307540750700000d002d00300104040c03010f0440c25401032039140c46120550341009034054112030414170b4100059151400003036171580d80e01865482c0342c000320b03504405c3d09050606401003551507000600c1107082c56610404800f4000c840d070103215401f00f2080c441aa60300e4803c84010039072030711114160046081c980d107031001d18010b005400e8000361040360071000307130741c1c644450710196945110440b81d50340400c580003203100002d001455141c4202041d4407900000c0c4180f20848120243d0341c40340c2c110901400c51011390104906402031024401c1c3c9459445841c0060020003841d03020a59003800000c40c0d0101c0343e0041a8001105e4182030104007903603500440b2262882d64607a90310404282500807091040260f10068000801070001820708440d80c0d504144e289045d22450102c01440ea0300584500304450040d9004105954100d9011910360b50a8158030030740c0e031500d050240560700380886d0781315680b20320814503004244000c1e865aa5600c04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 795999559 1250 795998309 795998341
    0x50c06010303170a1118010e0d080903061303050307030e0c0d12030623060c010609110c011b0509040c0c020405010902090f041a06031005150406080a06060e0f031203 73
    0x901d50010783c00245840d10724440c081a03c046205982e1030300703900c0c005403901d030303c1c01c00d4105060000c42020230b0345507103424041c1310307046200f051280e03a00c900a808051900f04020040d10040c0121505140000e9008050f070f50030078001d0a000c1030f41e9070303166005414950b414140a8106040c54585000c0c05440c00c0d5441c044051500c080028a80f034002050520180c01c102c5458107160101d00003043c285000148a02c0003d0000050141c0d10b0b4401d03142514070811480420307100124414001241c28400c0b604811300380741e03201100d106c040c00043c1440c010081c600e8440c03a65001244a0a40501d170613848066000300704100307542e15001008001c0d0031005440d070084034426108151420300b44034400488004082c1035600321400001c129181e880200001039407480020001060389908001810101082e03c2603510303142041d100134100342004001c001890704041c020080140c03c000e41501e420b41c165007007044962100e020a02e0300801920501340103c1c00070401c01d1034040d908001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 796000809 1250 795999559 795999587
    0x313020103150f06200a050706080f0105090a05180d0f02120403022107030c03151416050a170109051e01030b0a02071112060106090803120412050c06010303 69
    0x4014100b41c601c01c581c00003040340990444595084814031100780180c00d038100c03284244030005242070224524904000300c80000b120305910a4405102070f5410a410503800000d906904a040d85800300040c0c2c804005041c030b00c4030301c1e56480843c0b002000790b81180700700040e0400f211070564000b4070041c11580f00d518502c00600031881c0740e031a1408840112002c03079030010035242c5954100f5128545545030182c0c0c0050502c24008000006040c0001500c001d44c0115100300c41110186145e1013502c2500d01c42242011000d0104131400030705018a0300004d20a183c070a0b11407601650517075000400c0d80e00c1040324041c2d4000068030015540050b071041c040b488a14618106c03110090704040c800f03020041c5030340e0f84000007e480b203d150740034150b194010300c0305460f00340144000c90003003d0103210800701c64100400601203240c0040e1004c00400120004518014555200600040300504014009080c0142c514025031259040e00e0b40715411400f44c44055030340345400b07001c01e01c4282c14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 796002059 1250 796000809 796000811
    0x4051020010207020303090915030f07030b13121110110d060506030c030117030d1118031603170909100306050903030105090117010e0d180b090105090904170313020103 74
    0x1412140c18001e4030185940540214107100d400020000c0300403004200310b600c595a4540440140c2e41080001400d90b68880a00300150542c2032000300010000c18031000e900243c6060000a1040c101c541001c80841c0b0f0614a1040590403407401c01c103045040803115401c11548412840500004104403c1070600c1040980d94a500b0b1102e02d000442d054072521905000401007044200c00d4901000b060f0001d0340d10780b40000c0301080442c0e1100700e40035210741c0046406101d154401803281803a0340200d00070070740420ba080152403a00c050f80402450300c02220b00c181e84068100302a10130000c001441038003146007003428045010f00c50b10058402c28140404115081d10200c03c581c140ca070003130301d1042960b08000e61308010011540005c0039030740d171b20003203944114800c2c0408087d03a8002e1350366900d0300e2103014045a58840c541c00840c3e0380d050812031030304544e80001c21580c4100742a647c1c03450b5503841d4181111a00412400d440d480304e0300100300404100d1078542c450310180300740c138 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 796003309 1250 796002059 796002107
    0x50f040b0421181505071b0b280c051b010309020a0e0405070906050d1713170d0201020f0315120f0102070c08010203090c04050621060105040615091a040510 69
    0x8003a5a60041c2c441d01c440071440400591011485040b803885000c9000c681c203c10442c0c2d80c0100e01c10030b900109140040b01d00c0c044190272000340b2125007089041d441d20f000d42c0700056035240e05440d8006214043c180e112120314400e500d900036000741602c15001010407540643e1130340c0d0412100021902142c2d14040d0786004124200070344181e905a92001c3c00a0b645441e25940b98681039000c4240c0128041084c000d600815121910080c0030740801c443c800e2411a0f201c0d0410700c5c200ea01c6801509590061000068200520083c1c03503202011704200d0002c20705030300101c0c2042001d138011101030b0054407201203043c00f0540042c50307100d00c2040c2c1e542c03140d40e840c0e1600303080b80016200d500d03440d0032080241c81d00e850280c205640101d4000d201c60260b0718600c0721324000242010908420b0b4020400400c25031409100d200700904025150501810401c00c0c02809582c06024446501f40c001044004451903030b021340d0701610380640344024600c000d820141c800085654000c40400c03982c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 796004559 1250 796003309 796003319
    0x70803031008010501060c030c0b072a2102031210080f16060f0815060d020d0b0306060f0d031110111308010c0f050f12011512050f040b042118 63
    0x1200e0038100d60581d544927200c0c5010b580700384200780090900d07410005200c46815591040c00800700e201f00052030581c0c8004040d1500c4c100030200107241c0c4080f0b540c2404121821038010049031a20070381e140d441da142d50307a9820310040c04100b1307400881851088003c1814201000185d041d806880c085410000c40d94510085608220084c1c0c01e00c0050116000b00344003c00b07000d61150540f030000d052609080d4902e504038101d03001384040c0320b041d544450401c03055013820302c01c2c541c0141c41503441c50751031211880032409035109220005c04001902150300700031340d800d01502e1900301068400744203d6984031800110b43d0003510a45072061840e103800194208148508401407903075171600340f078044203031000f61000d4008140c0c003444054100000b009007401c010900303000e0481d02c0c40c07000301c40a0810004084145580448881c0317480c18003840410418400c188d5400741d0b1206098215039102c2ca880c1d6601c0c0903424110844004403245c1e4001681c1000000050200e002d1042c110a41d0312 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 796005809 1250 796004559 796004567
    0x120705010e06042103060314160f03081b120d09300f0210141b0405060304060f0f050708011509050f0607021503040c0512010b2107080303100801050106 67
    0x7a10000c120707114030b50900054807014101c13100961000d04000981c16504c0c0c60364100550307668401ca503281c003c40d00700e01e604501c403010880a401071070b80c40c407a03130f50642c3ea070108240300e6182140f1000c1890040985142402c02181c4a0801d4505549481e81c08044164001d80070301141140c1a1001d52a0201d0a20704801070f500400548440307002c00d01134581060b5019290400c450b41180146803072a450003100307005541070703034243c0b0707901d020309103061884003210b80c1c60031540c1190b808040000300280d9407a0801d40340c200343c100b400064608002d02e019001010903140c2804002d05160400900301e820800f058100c40d10005400c00e903c000c01d80850303200c00b0a0081d0355020035002e080100078141440035150b1144054003659003401003051400107500100d404a4844141100c18402c604109010340d6038114490000d01400551400094441c0300038031b15100100000882841014000c00404009004070805e0b00d40e00d04105060321001291805044125030030310000203455482 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 796007059 1250 796005809 796005811
    0x120c1e0602182d0a0306050f0609160804030f030e0d03141f180e032704020a0f0c020f04021809010e060303030123060a02010218010509060d02030c040305120705010e06 74
    0xc0b8191641c01107154050000782400a00d0f2100d07045200741c0004400030709a482900c1c010340070402002070b180b5040040145041b4000d0050219801e4100c00100031500012580e03003260f81424901080300b00c00c80120028040000d500c405071052419012030f42c1d426900220044599841960080d541c420800c0b16880c1da81090f07880c80d1b004504200240b0038003042101000e0400140443d034003820b000e02c0c900d10b0b00711b04c15504c100c1540c51080c500c140319084c00c800b0380e03107426202941052800c40c40500f120258228001c280601c000f04242156950b1100c1507004100401c110f440c1c40d21031f014202032002a01c0082d020f0241900081841000c0700d91071480740400400540c690380c20281004401d03048a000703488802603180c4041c060307644040103003070207083c0c0f0740c00140c61701c07180903002009925500c0035905000382004009000d45500044a910310408000981e982e06c40b00c04103529849507900c06051802400408201070304c2c414024029a03000d84000d0015054240f21251100c0d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 796008309 1250 796007059 796007089
    0x30d08060310020c0a0c0f08060105180c030406090501050a060306050906101203050c1b09100602072601050f0603070914060409111f0f0903120c1e060218 68
    0x1101c507031075030780b4000030750004c041e81e03981c802c1941c00700c40c1c1c15625441ea1000c2c0303412058540d40c4484081c040c0d29002c002080c01403404413040c0112a0104100c214075400107002c0e05900c8074000001030501a0350b4025002080c1e01400070461491704c003180e41c0042001d4001150406d0401001c1090010005541c40c0251a051848076807146040d40044008403018002c40501000340502601d5840905ca40d280090300c0340c680c941c0402d10380b0200000e0303400c028090344d40d8085160303050007203c0c0d00041800c140c600e80594503101450503038020114142c1c101a404a0f5820b0508010140961890041c0500c106804542515895070046016500003400103110841c12500041007131a080e0800054075001e00003181c40242c0c0760380440c1883c00c01c0c0f0310b4940d07103420b450b0724040c0742a0300c501c2c00146007145141842e09903003141e40307a07840440da83c0c0c200c104021005266405000700040d0000c42d403080366108001842c41ca14149000c1e400942c2072404c800900940f003010360504510a0000130 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 796009559 1250 796008309 796008313
    0x11b11030d140301140114070f12030e0705062a3702040f02040b0331110411120a200901080f15060d090c0b040b180102011b0e030d080603 61
    0x1a0038040d2400310405c0c05a102410444804061004035526038020640140508440d051751107071428035031030300101c0c04110004c041c6007a40765110007001281e42410f5a108890342c039950500301d0042b0360342d0040103c4101040d0280303103080840900019401414100c000c0c00f4020707494000c00c4e24810381940401005040d5a4034500c04c006150681c01080c0c5c0e001102e03001414a03842d12054412500115141d8070940340000f044d4502c5c2844146103562021600e840211060f0180e54408410081500b042d01458440c07100901d02c107441002d4400f0800c5030380020b034403807401401510140c9440e186180c04404800404800309805508a038986d440684403c0c0c00c0303855041c3c01d91701456000b0014021040202061071041d512200103000d40e5189030740c04224501c2a04140b20009515440015024000c03c41084132100e0381c4260340700300d01d602c045035109190220050f405031805000d4244200032400800c0d82d01381d040031044800a07410f41c100d42c4a896a03400035250010151411a816 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 796010809 1250 796009559 796009561
    0x4170304150b03030d06030b0403120e0a0f06140903070b01060201060501081909060c090509161b050f03030705030f070c02030c0d0c09060905090d030b0d020f011b11030d1403 77
    0x840c07103908107030100e80001d82202d1406100703070740880445038950001c4411030703000300030704c02855440402c03201a8140104c003040905400d1003119078400d1010001010003241d05480014040c040c0d0008070b051110803002441c92500051650300c982c8900341c03c444071100d8500100b1b400384144114419a14183c4548009440c0d004041010074441200034131034548411200c40020514024031003500390940320035030030906200030800152401840482105110020003040940c40340c41009004581040d6078015045070500506000801c3d1040c50544000400d01c8450b44d8004011031180380704402c543d50075103070b51104403030016410030081e6165000c00002c040c1850b0840300d4038041886141048072040c0e507145610203840c09580701a242070f80d0341040000302078040c0104000720000340350403c0f40d071070355074001200305154410188c00759003660019811a4010880281940c0c2d000c1030b90061014903246c041580f1440e0080386019016030314050100500030340182c540003201c1e560440c21 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 796012059 1250 796010809 796010843
    0xc01021b01061a0325030608011d03040902070c030f030e010318030e10120f0b010e0319081b0307060f110901020622080d0609051506090108150a0e04170304 69
    0x43c0d50000340c2013052840e0002d0700100a0004d5218030703009a03406880c041075030707481c00b0b1500e401c40b01d140c05014003821001880085600b0080700704c03025510104c00051b102c00d65070a2601001c14550001809941120241c1c010301d038004030b984c940c41000343c0e014019105144070920042045640c014007103515488655203038030302514110308100980c545100003140048524003a5110007614a810b00e0382c51840328215644000001c03d03054060b0020900800400269001c100b155007001e0b04a80011800455500300149004d2078042d0481c01c80f0b44489650074100c000700700700002c1d0340c4038070701d814040d0041000e0102600d0311320405030050700d890390302c400951200d1140341000e0000c1010500d0007800045840010341a0f0890840c0006031071400d201c98a01201d0029000324a010a03840c0d81482030350703600085480c010000e181c0b04001e91204003400c401c0f074041c0341c50244c0c0b040598070003107802144082490b2045004407032040c0c0b656014892195984030a903400f5020860341c03060941 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 796013309 1250 796012059 796012109
    0x8250201050910020c181801060f14010e04290a180509150f18070b1603030603020402031f1a07021005043309050303030615040504020c01021b0106 65
    0x1c0203109070054030514400200000c1d400888007101a001070031399400c3c070a00160041e1100c03001f110402c001c028060401d8814609415a4481c1c090750303480000503159141d01c20000f010b503114001e003003030200c005c0c0b56a40760400480146001030100e007646907440645401d02c07400d070899201c3c14026103c440c107101060301804000349a280148103441440228100c840c0080d440b8414148070920503040980401d080c5880104482c6c00e40e500c440002c0c4242c0304100c08480700300a50940510000003240b405a018001640c00654001d1000c01048008541c80c03104a07912a0300c1c0c841c12110759250001c84140c1e203140010102c5e05a07003800203600504000754416117514042c20103c1c00c1541e90302d40441503200c500d034603d22901c40d155481e0342c00b9034200308010216480b402e11800ca1401c1ca000300350b4a000c02400640f05090450800c060160007034100c03805044094400c0d50b82e0410382c4080c5003c0c0d8003444d600c070400c10302214041c00f445418455102610340d0008010904400781c0c40820b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 796014559 1250 796013309 796013329
    0x140102100b011b05031303050f070e0702030301050d0525150503010e0a0e0a081603080603030702030a060f02040f0902040302030c09041e060b10031401050a0b1c1107082502010509 79
    0x45042c4400c06c00d07a0941c00914000c0401148544010305c000710703d100940e410b0036200e0b401040c000b2795000c18885c03c0c903004815281511000c5d61000886105070a1040c940003800741c0204031810001d038011815034004042d4410707100380440031404044081000c880b40d21092268001002e42840452a4400607800c40c04848002408850540b400d03521403411641c13200145031100503440f8004c400301a0003081956100000310055400c00c445500842e03103580c40c5610003441e1a40d50b50f98185d00841d1603041c0ca01800e03444081c0e03101942c0301c0c007a1000030742c4240826071084c4100860112249482202d46206550000b07a5200404c110026104110a102022035945844454030305a0707031204250032143d01d078035079408a0790003240070b01c0c00011035040e08001d010b610213081c18440703100f210302100c80720881807a802e20740c1c020001d40351000304941e03108804500e00009000e024072500c540070340599040300a101c04010001086040708101c543d80c028007081003030003182502d1034850880 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 796015809 1250 796014559 796014563
    0x90601080325050c0312030609010e04150c03060f0902120108030306010909020a0302040b03090d0306080303090a02011b0206120a0e010221071e032306220e01020301140102100b011b 80
    0x44402004d402e0002c3d00303004465500d40004640481040175524101c1903050050902c20620354141c00c183e1500d2074029000d202020310703580c40d0239004140c50f1080e4000c000404440304860307041074503801c04002035407040c5060310808014400218a02c0c0e00441141d0140310161111482030340b800354100042c0d000466000103140c1e090200081036440340e0700840c0314100c0c007005000c451400800c007070111681c0d5003100301c0d00c0e40709008200391480005400d40074107409003403510704201c2186101d2040340910400075041040841c110484103581250780d0700070768496105000c1e00c80540d06c0903080f4020840403150f11200d0070320540310341c0410f4202d10740190003440e0819032603e007a00402164080031600d0380001c1d9841d40310054500445041c1303103601071104140011410114001080300f07240c3e488080d0034080d2114000c40244c4154400386182d0040c9000b55280e603510205944508801e2002d50701601841550b80d0341d0019601c12a8004a0140c4078540300d40b01d4403000016544200c202 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 796017059 1250 796015809 796015813
    0x1120e0303010b120f01050f0d020d060c320f034206090303040603022a1b01020109030212030711030c0607272c0f09060108032505 58
    0x11421042400114041d001c0c0f02010356840d251440044144900104881100c2d10310400500035a580d03241c5c080044a400c550b0710280510720300019903282e1510307030001c148a02d0990127038044c9401c00d189183d0407502015044060b83d82800529900203140c0c20f59004a104000381c1a103404000061508030310542c9009822400f24012041110707000248a880409030301203055100042901c800552081138882d1401c107451080841d540b4000c2c0d00541c410301d038001c41c0d080300b0100c62690781111810040c800d401c83c0340d000002940c80f081c03098110220101d0440d003414040d4014000c1d038880a03403603402403199203006891a1b005820103001401081510001c034900c070102040900320200007030340074054500b040341000e04440c0320b5600001400400c0c2d03503004942c4c1800b2024408a910010400d641c99264409440a80c403036440e0b00400c1c1c2d000441844402116a0a0707248a13019120840781566200c00305c0d41d5490165181c0c81e04083c5196139000c824014040d4410b0090b072042e82 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 796018309 1250 796017059 796017071
    0x1406060324150603070c1b051f03021303110a09020c1504020109080d0302030f1608280f020a0305071d01111c1d0907090302040b0d1514061009050112 66
    0x400104981d0080d030726031000580d40c0801005000f84140214003045d041d80087d001030380307802c001c05c40115900102c60319903411004100b411078001e40454040c040003100c14407059071a0315004200d40d4140d0324481c0580e403840e00c0816040031510071140011340a00041c030185c3c02800a44424440040c4200e040060b41c040000c2d00c1d20040117902110320040c0c802585910300a6900d0000c03c0e0b0003804484021516507141010320b030000400d98200c88441e010184c0120b80760b460b41401e410358410000c02030300d00028005100c0c82507000c0c03c211602680e050109440f90003007180c201705000590840341c03400141020070f660003601c0300e040b00ea01c0c13101030b10030210708822614400302c2101e0720540441d41c40c020321034401c042c06500c8101c0d071070222800b14090411400043c4590107601001780103e40ea086100b0060390351500d04100b25500c0320aa507101c20003148030a01600c20101c07044182c0c448000460f05d245002000d4030300f0074103255103920300d8510746001101d04d440304040541c002a6501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 796019559 1250 796018309 796018351
    0x6060b0301050f10021e0a0b09060402010c1728030c0801270915060e012405090d0f060c120515010f09031b230f040f0b0d1406060324 59
    0x340f0003425801b103505c00782030b0135209810709a960180081400484d9044101044010307030300700d00c48610203900000d2230a40140441040581d40c450410046440ca1618244a150b0140d480410b403c00503140d44c2448405405031064074820310038001c090364401001c0c041c99030402c10020303680b6096941100415076600c0354840c0d2580224100b129050b103900d80c01d040c8200601440c0c41c0d401041c0080c49214006d00110010b40301d80151519101040f00c0016080350076a100405051780380e82118038815603100700d241c00304c010950100c0200120300e10192f400b030400228813030144241e60700c401c021004804078004607002c0000c5680c1609011520350088040348403112407410035007108800c090300d2400c0070240441c2007080a0350340300c0391006c1d035105200e80d10f030785d071001c824400141ca003c2a451311003207100000d000001c0250303412071248000142400800da00c0f07200322944500959a81e07848000902d62a1100d01c1c4a11010f14555408051b201c003120b5a81548021120340c0d00c030400c4146 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 796020809 1250 796019559 796019593
    0x8030703020f0705072c0402010e0a090f0b01080a02161101110a0302210a02150a06080d0305010f060509100c2f0405010509090a0b0915090a06060b0301050f1002 71
    0x101c0300340c4456010580c2400b81107200c1c08640403000311b01c60080040b1203040f844440c1144c00a00c001d040020031480ea00e1992541080321025110400062020f0500d041c800301c003c03c0e604036901d00060303280300030a101e40802c0c42220820600119004a51040c41c1c036004d58552044440a04202c8802c10f40c1c4640301c0c3c280030b40880c00c2e00c030340c0c041c1100c46c1c03c041c0301d440c2040c80c6c00d6002c114500100114034095400080c003a0141c0301690011481b9950200000300600403684450098050107041c101502e030701d98803d6042e03940482e10040d4680c1c490130200e95074012200e2458000700204465164240600d14030780c0c0086c480c40e140c0d10700040460404800d00701c3c11200841360440803807026110318007401050301400090359003001d240b4104005981d40d46088030003405112408000c0307840d00800380031700c42101c0c0791208401300d039061014a066031042031903002d540d118907182c00498420141c100703c038103c1d403008103200300c2a106002000380208696034480706521481e0b601055030300030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 796022059 1250 796020809 796020817
    0xf170c22170f07060e0a0311120601080c0a0f140118090c090e0f0f070509030a120c15020414010e1f080105040c020a020d120917061501021908030703020f 68
    0x289010340700c141d0180002c07902e40026600000c0a002100c032001e9007980320b0b0240c890490f07400c990181e0308402c007100842c0e43c091425504200d64040c1c2000410411000628030240d006c05480c41c0094030764031080594481d0300360192a500800126041344075611540004540044100200008981e100e0400301150110030407075020485075031080140c07142100304994803a02144407030a05140c107012011018038001e0052050200118130342c106a141005106041944642c807000d06100f40350002c0c0400e40480c4045078803004125090400103018000e03542107a00251090549402c00c400545100786803800d980d8001040c80510903010001c508400c001104036200d00840b075041000340815115070304040d0043d90b005030001c0c00141c95407540d2088081c0c0103182d07001615800d000c00c48401c50340740d101044051000802420b100004200c260040200c4040030710250000d1005985806004011162080b0448041d0000c100b4200043d07520030001d103401884c00c0c5004244d50740c9504 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 796023309 1250 796022059 796022099
    0x1b060902130e0d090b0903060a150503060c030103050c0d0507050f061207200c0a03061a100e090106030b0904031103090d0c0305070e060a090911060a0f170c22 70
    0xc80741c0f0400340b1039600302c4450b9000d015583c1015242c41120000300c0c2da07810001d0909a1055a6250b408503c12400381d081400341c0001415038086081035050040990000e0100f40d905005d66000301c40c440c070b4504080602c1651100c05480040d140504000440b90881e00154000104101d18a01e600d1084c1100b4819036554903285e2051000181c550611005801d400165074400c1d0000c050660fa5007411108036075204101107048940421018601c140581406400c064179560121190b504101a400394001c2603801c54110380e41c2e000c080b010340d0508441550003210791800309004c60f00c50366030161581c03105811286000c501002080c140b80711030400385c400e100031500601c10400309000e0b40d07000703101c06001b150041c146035000901800d403a01c2011072280e0380300014000c015100c04100380d12880145859100d483c8003402518941058000900040140c101c04003444000b0701e01c14000c42000c9901406c041d050310318060ba0000c014040e0001801081c00010421084210300361891 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 796024559 1250 796023309 796023313
    0xb0613141f06020c1903060608030301030b0604110409020d20040806010902031b1c020f0d0b010309030516170307090303140901020309060f0909010b0306010905011b060902130e 78
    0x21514010100c0101c0d0480528100900854820020694001651404140120388200e88440b07640381402e141102c0d0382c8000d041a04240001a01c500007201940c12a4013604260003a0356891007000111400382c401640344280c18801407042c40030f164040c02034240c1107140001d480c0d01c030042c540c219a000290a13440100d00090a1081000a10a1500500b0b0707042c000c0d81181000326606036404c9140000b00c1804201180d807590b1044920340003110340c084074004540d60f1016005940540d8000003440903100d041035108901c9500c640709019001c0d4066843c0380c04c0c03400701602000341c0e1080d110f040d40c0031100c0c8450340e50750703134040b83c0118054480d5403a0750f0038503491440c0c040e0042555024001041409002142785a40c011045400400040f118940e0340d00118410740c40f58000c800650360448a6000081140c1c8c031110000c5018003002d0703c400c1c40c0550f8410046400c1c0201c05c400051180b00300011500180d90340c0c110308070141c4010216200382401c900e264044a0346440e00340e4075a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 796025809 1250 796024559 796024561
    0x60c02121605120109020d030f02032701260f06061b030d061e0e0703020d0c020109030315030312050603030c0a0b011a03060d1518060603061d07030b061314 69
    0x703240c00b16480381c01201083c005e0205618a400080c4620607100e4003800b8000418205111a44244115017180724070030b1084401c084040c1c19000d0803801c0ea02018041180c40100d940c070a4400c030140d105043d5815410b03c11540d51803880c00141c0000342c0403a4000a0a1241d40181071104000a0400540c04d0096407a00207040880741500c540c0c2d40000e022039001020000c140b6880b9a070101552144100d460140d194200120000d106284290b0002481d00b882011038030340c103412008409001e80e400b4070810ba40b18401118a610500c00280480c80881d04949080c1098100c1a80044000c05484c140034040701d0039420202614030840f540c00c410310040c002e1703c484000c5001c04000d40e0142d1811450003001241100f01201800f401090031101140200741180d001458000d0000f03144c0d24100c0320a18018003d81080d000841c1e8142c107041c1958071061154080b440110815001030803035600c2c6440b0803400400c081c003021f40010000000c0300e408022800b44d24038125080340030780a5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 796027059 1250 796025809 796025819
    0x131e1d010e0a110a150305040507030c0b0a080108070b16020a0e0708010e0a090206121005130905060612190312062c0c0d11190206090d18060c021216 66
    0x40d5a443c543c00300e11484610009000c5243c0c008510b01115441d070800042c00c6c0c5407420300b14030388507551380014410f401d114070202d1030300d80400c05440380c643c65032039a112603600e4100c0d00751295043e000d032441c00081032000e000f401283c0500480c6e15400075000032402500c564a910301c441040b0f41c640040b8051100401000003000700050388041c240300104503141d1281d000400c01e10805ca2000310b91450800400c0340d000070311304190028180108a2464200340c0c2482c0320182507140003e8445003e82000100d8034105910184407402800000c2c00d44444044181c51002420400079000c001201c80000800c030340610503036016100d1419020106d440312910300940094001c000b0b02c20340d01a00500103030007813030801e40385001120900464041c070040000609405460b1288003840b1175505d040c007407150042041030048982d84180c1d6816542d0341000d540440610900f20150850f0210402c00c4034801c8009440036480100310341100b6403e20601841d05100f40e0101004c240e183c3d40402c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 796028309 1250 796027059 796027073
    0xf062a03040303260606090418140c0405090a060905030c07030809100c02090f180307060212010e0106050a050a09050303340b062e030902131e1d010e0a 67
    0x1c403c04d01404418440c1ca040001c004209000741450b0300415020034a44096503c54200d900c2c03400c040d044642d40c001443c00c01a18900403008562420f01030212000240d050500805100f060700308010000382140e13030341b0b01d4000c2c142e050003601ca501041c00b190440710010b0055000460194614075118020201003000038030300c80a246081c80411011000142c440c0b080da0395000d42500351501e6903948000c00c1160484541c244e50085010014882081000d90b40c05417010103114290202d1980e220440b103404000280140f0020544c21b00035540801c0c032600c01868418243d181c00389540b1b60b14400301c4e1a5401581010b03809002c402248035581c25441010160a0050002d0a4222505031160140900050002401440c0e1000a0202e083c803200ca4044401c04010015802c0c00b000f0700010700a0000e01801c0f4070503080925050143c0d00140070741c0b090600c000018074500140640340400411210f4600021402007041c8121102000c1c071901082002c2c000140c0700400580c54022 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 796029559 1250 796028309 796028327
    0x3250501020d050307320d091101020706050d2a020a05060907050117060f0603010b030a1803050a0f0c050d09050a0f0602060105190e070509090f060f062a03040303 72
    0x1008003c002d00030403070010f5103c0c40c0c4441b50b180110f1000e100080000b0200a07811021102012904001440c0d0315269602d0b4000e0440314041c08e0084842d54507a801281c841c82503100e507100180060180c0315980b0f460307502034501a521562402c54100d10079450f12005c054070350505002da0000c46101080c040c080c011141d1002d58200030700003481c1403030000b0f031513102c0d41d05540185410fa080060398503140c983c2c52b921210001001183c403581c0d10300b0900350b107900403549510083c1c1000100030fa400711a0710002c00c107a9041e1105402d090000c00e0881d00d1a200d28888810007010401820100707070140101008001c042e0b8842d0400e07800e0009100f51112994005001480c1d012010080e0790b40c0445d69606560007201c1404460700008031200d5a1031080d0090411720362243c00380f100d0180c010b8003d2a54010580300c0091aa5880c1d0001071980c00446142d40c1100c01c03103c04641d2407500c0401040c540c841c003031001c2e0f560b124200d1050401c0b84d0004002c5100c1e0300c001410700c20b2640020800d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 796030809 1250 796029559 796029583
    0x603250e1306050a06030e0f190212121605010b0d120f0203030c030a0e100e01060e060405061f0201020f16050c0a1d04141b040605032a0325050102 65
    0x103028480c0b815004c40c800f0401c81c42081c4c02c2580d19041650810b07400d0000888030000e0000304c2e4240989480d10078036805510a040303200e41814407840c0302a103800f0490400045018003614106100018164401a00035a080703e8555903013030740c6103e0fa500c84140844040c001d500110b880050030300040e18000c0100764a4007958414002c0011108034113085a5205000742d00124012840c0c03030f24075280081c0c4500c03c001031410810f501d2000030055020104480301e40e00c1c1d1314550b44400c011301c01240d0082e030742150071410051001e210540c102604202140b07042c40014901125408d650300d164100f006207009010308540101c0611900300038039203020100300c80c8410410b2821540c1c01c40e1040b80340280c001d02444000140c2806080c40a0b508101910001e031021071104c075103444041350540702d042c0e01c05d9180c4140030802d400c000406043c46842180900c03101d03d40d4a1a40701024940300c00a5030503c0b8000002d00802c47c00c00d10714080d1b8960180542140341004000ba041400020745 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 796032059 1250 796030809 796030811
    0x501080c0303270a05060a181203050711150c012906030711070e0708060306071d01050315040c020f0111070b1504061703090307080307110603250e13 66
    0x24290415142d0403900030780042c40c0708243c9188000e10124241c25002e80c040c81e4484000724031201c1464010020725450318120b15001c0c0c8842e2900c0020400d801641e00240006100348800c0d0001624003a600340c504d10028402698074044041c002c0703143d07000509404503a5102d602404001941a141c88800300c40700c50000c042004c0d840c040b6005002c01000c507000c110450480c2c020049061100b01c020b00300c5d4040100301490b0040c005413040c03034180d401da1302034881d01000a01c0d43d80305203103001e804444401ca205214002400440711904090440340700e08814a00c1050655101d03c1488548031803500641088440040301d1801c4680032600744003010340403c8990000b403148180035911818064a0b2401100c00b03801080040407180c0000c40580c5e04064007031044000000070300b5589904504960742141caa2035419101d0180a02c02080c03030543c42009103140c40d01c6d40c06580e00001080f684210160350405402601c2c0000c49070b40c1c042030708803100c03041c1424590a000019203229070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 796033309 1250 796032059 796032067
    0x30d0b04050c19090e10080625360f140d030503070e030a061a06190c050a050109030c02010306090203040c090507180b1b160b09010e10030501080c0303 67
    0x1000401601c81c810b04043c0c807a039901da19012290091101c1c101510051051529500d840301c00c40110901d28014a00e02d40300c1c41c400034020064940000d4407580d03040c84e4a07004500b070403605a960000540d01500641400c0b0220b101c0a0750813030000f400000100450701196140400c00c4003020300b503030080d0300341003a068041809901c489803907481480d814a840d075507907a140c100c100da41941c0c0c0c0581a40c1400f420807120248500790700416400c2d0360f10200d41c56a051b14000700140da11601e2844031440c14068280071581d80110743d42610640940180c82505050b0ba9980d17084412001048000c982c111603010203550340b5100349400f03000040c40c02c41c91418141c5501c1d001c00c50901ca001441603c400006903410721624002e408000507000051619480300b414046a0708192084280001140c1002541041c00607101e41010703036100c10032101905151055030b1952003610301c00c1c14070803500210500c1d40c54460f0036108034095503800203a1941418446030034034076801c100702e1090703100b40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 796034559 1250 796033309 796033321
    0x171b0f0105040c0f08210904020c0d0f030905071505091816110604020d03110a0506010905060405010e01060528020a120e1008090c0d0503070b010609030f1401060b0309030d0b0405 79
    0x1522403540c030f8800034801106c9400d2a0402d82c1d0320811700541c1d00a40041501e004104002418000d00c201c0c641350380520000001c1c0481c101c2c0c0c56190042c00d2070740300540401c1482c00c50182a000500c1c1031814a152080042c0442c1c02911b00b00d9602540240c1c2a041080040758515403048030180303880c0015403c100403030b00f075030345410140c0080d2241c265408100101405840c0149042c144401542c4c904031190400369181c9200744101d0720514100800a00d00d8580307403040d24180c0c0c02100d00c44005034201102114950480300c2c01c41801e501c40d80700e4006e681030854542014034041e13402803480c52168070384664215000d59292041c4044120010400d82e140304001c0c039100d0061400070703c00d039900c20015203415442d2201b650410032505098090000110041c001c2501400b01c040c01360340c4e00c0404452103e100d2101402d042caa403d0071500280c01e404071200d80703455520012400ca611440305194540c42540c1c090703059400010123014002041c0034601e41348800302d4080140b850a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 796035809 1250 796034559 796034563
    0x10212150a1d0601090302040615080c03090303041529130e07090f02070b040503070219030213020c0309090108060a0f140115050c0604060f05010b07171b0f0105040c0f08 75
    0x2040210010700c00301d0b4001035059104254010003540c00a005000c110369892504010358807039032400d400079071000001100300358020304036800780300c0d203200440c9150745903203402c0ea20500030300c0d200ca04513488480d40e5401008503c0c07102e905414072200400342642c100100154850203d0000500504102c2d800820180201d1001c0031200214004241c03100800007420013071140c8100181100140030a100900000101a1416030310aa4030500d000003007450034180e001680c0f00c0203522181003941c151001ca1a9006001c03108015402c40b1b0504044900042010000f60041c4980707a2111003001342c000110701441d4003040041d031041050060301340030f03002030000c14042d40011204e0340d4100f01040c0d01c59011a16000030000a0310341c036003000d00d400d0002c3d0038401d003090055402c14001250300071141084920f00b0744d004a5640d03900c00c0306040d22100307820040e0f240f17141c528901440600c002003404442e038400d00d4200005030503c0c281c03501c043c0e84156600003180e400702070001402280701c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 796037059 1250 796035809 796035839
    0xa0e0c010e1309050106080f030f03130f0212100b0402090f0d0c0e070305070905060c1905030f0a1e0806130905160803090a150c080c0a05010212150a 66
    0x401c0c038201c801d103490200410100b1403100d0801c40107610b008209001d0160640c0041d0541d0758250a84401444071200c90760743e0b00850012003103070f030b00801c041365503804090039682d000383c81640e10443c40350207500054800348020200d01903d800000000d40c90f807500344514030300c1d054103c604505100030794002c01c1c1000070b520001c6009441d210140c1062003500c41404004100c12042c1481d2482d05250007000360100b661104003013050340340049242d180c9007050b55a240321002c000c0c1440410091414101c1c0103440d000c0d40c1c2800200208225440008020050b000a944030700c802030708a00c0004030101e40400070b113000c111943c800d01c40d03035594034013014440307100e4001c0c045688419814181c0c18100c0d503095030010170028150000e40100c0c080040c1156010441e140070340e01d0b954a001d074012810714114280041c52003021800001c0041c2d0203020790b0444101101c5064207a56549801c80c1d00500e0003403c0940c8110401c00703041c5078000c2d4224450800e40340f4400e6140b07130043c0d4036441d0170 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 796038309 1250 796037059 796037083
    0x51f08101401260c0405130c0e15130e060a020403030e0910060f120507110624040c0909060f0e07050c030304030507060e120c0c0301060b1b03120a0b090a0e 69
    0x2210540440caa04200b04101c880e9000034030402071800c08140801d418282001f044803150340c03181d00083c2e004402c0c00c0c0240f00310518490320300a619600108003081207070307494002c2c010303503540107500c1c0c110800c02203903126100ca28001691a811420702610445100f070b841c0344079007100000c10150b2016191524100c032050304012441460000050720590b94400c104100342e072410042012035a03001301182c141c0039100c2c060b1200c5454807030381084940011840c042065083d00354000d030340d060030360002076080b8080c580040019124400c403402c0d40c1031a4031420540d03070b43c00350030701400d804980d00d20780202c143d0034418a0021034a00554690000400140900030042400c40511020341c00c111901c014440a070b4007550066003001010f900040340124182c415680c8400c03040c14144151001d036140801c045052001c044042280c2100060b80045030307000502500020703900d003002e0f1a0260a14440220314041c0800611000031001400c0d60030040c14028140c00b80311000c40c408144070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 796039559 1250 796038309 796038359
    0x40302060a0509120307060603030f0807020601060f090f24050403030c020f04090816150606141b06010902090306060406030b0a05040c120b040506010501090506030a051f08101401 79
    0x20701003c00141d2a85100d0407202890b01000802d0380402600b0342c08081601c1c401d40314100302c1c28640400f161503000480d801c42c003681c0408014040e8900070300b1200074105942c0f514130031180c0c0f681e5080b103403a4595440802c0c503034640070200e10600107004501000501303d242c4503052501d140c80007000400a040080d001c1e040d400c03403601c80b51300c0702d0b04004103182e005070705e060f91107400c9016090341c1c0d42e40381c50564645091280140d1070340b003a4000c0b2001c9501550f900416140021000c005640c010700e210030740300c00d034164401d001140600016000f041d000713100603110314600050600703002008052034481d0703141040510005103140035094020340e280c0800030301a9039074034000580081d02d400a885400e488011607042000c00031005c0e00c038500c140301355080350741e8460055822042c18000d25a0085c018400a003c43d030312503102030341c40898101e548030301d080ea0101c070315101c007581c0c2c021020542207480408200403460249860040c20072865803e00d43c54a5a803554181115054414007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 796040809 1250 796039559 796039567
    0x6140d0c0e04150c0e150415050310081204090c0f0503070e0a1e0503070803070b0c16081918060207060f05040b03010b0a0f0c0218061c0c0f050303040302060a05 71
    0x210050252081c0f82010b46070040110041140024155143c0c950301c291040b90544a03c040045200303054404440c0d9005010314140c441d09000e55458000400704824030100d9440024544000c2012140c1030140040d2070b541c40e401c0c004620207551a098801d0184000f09103c2a004e60307005085135800000745c5070002c0440d46080000303649010560090750070800d85001d880580b510b112500c07040710011001c84141c2c0f45d8404641e0348074000c40002070700030808100081c0714104040c0c01800c514402088030b08803121250368118164004a1b41d1000070150b080b1015121508400718141c07130160b041c004d010781490018000d42d1144640240420007035a49070a08046001d00c0c10341d00501012555241c90750b031103804088040e007104060303600007942c0301009074405001d41c0506c41901d8003d40601310b82c900c0748a180f04000b9025141035040311a8905507400b41c0e0400c5c504400e028410079041044500c1e140c0d41c082d041c3c901e90001c0e0702c00c0d00300b00420401a0748420031105607030440c0c20305e2625 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 796042059 1250 796040809 796040813
    0x30f0513170c0a0b0901021c050603150408070209043305090c151e0c0c04231b0c01090f330e0102071a010302090709030809010c0501150906140d0c0e04 67
    0x1900905940c1008c0542260f50300c07810156039084944125802c0d42107074502d000418124818010130349000e421900200304c100054280b0603c40350740240034446003030f2080b5180180304c1024201c0300c90031648550f00340e845001141d0f00d014964008900c0c0000340716010341c03400040c100740542d0a8140e205080007440d07140c00c00c0c804c1803111030f14002035031086c1c440407001c50442e1503041c0c807940203101d80d01d4030514031204040460380303900170855862030a00680c1e40c80d445401d0845c6c400d1030b5003030702c034020701c00c081416200340140d100a6105a20300ca00c12040d0345800550030b03a0b102100c041380c25000c1c14500b03030341625084410801d4000384c401f0903d64000070420b070092069039400742801d0b0806407240c0f40381c01071a40403070480f44240ca05866075514450215040380f01800010500d0204108040300c81d031013258101c448074000c2000107030300b00c810a4110701e40c0e03c003a4000000035455100410100c202004501c011034000e40f8010b8034406a036039510012000390007091386060707107079007c101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 796043165 1106 796042059 796042061
    0x61701141b09010207210c05010207080c041d06160f0c020a0512100612050c15040302092e080d02070803031501030f0513170c0a0b0901 60
    0x658440700d41c07600d04895000040c09030442c881d90901145442c20380044c03c0a00d01001d0814144000901d00820340c9290396100c41d0640d0442e1104114a40001ca003070264200202c80000f5450036402c0400c0100c5045c07000382c01036100b00003c100a0540c05280c0f030903203a00544416040440c1c88400f16041020518001d401c007541c46030030002c606000240a1070080c1c410f0540b00100c291030000e0007181d600e944240320402510303500006001c8284038150b410b2109547e41c0840f43c0000030042014801e51200174040c0511000045034100ba160b0f00040360703010081c48840904207041044002c2c1030030f000e03940213801041c05940e08980005480c030210303030309103000d182075a48404c0540c491120250400b0b06041c0c403103c44030f00d00c9185c1c0c80303014420042c140150b1311104c5542002150034007980d40c035410600e000c1010740454040080d065001540c0141501c1071582d81c3c0a00c14 = true := by decide +kernel

theorem cover : BRFrame.Cov 795863309 796043165 := by
  have h0 := BRFrame.cov_init 795863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 795863309 ≤ n) (h2 : n < 796043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
