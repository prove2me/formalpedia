-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5496
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:02:50.951885+00:00
-- url     : https://prove2.me/submissions/44ef25d2-6064-43ad-b13d-eefe91c098ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 988309352 ≤ n < 988489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 988310602 1250 988309352 988309363
    0x70f05030d0f0c081801180602070b0a02070b160512040305070521010f0e0d020f0a0201051c02130911031b0309070b1305010921080d0f0c08070f0516150e0d080702 72
    0x110205c4c40494809010541e27003c1064011104400c2d142912082c8980050f42010b0082c4c00c1001044400301c1d0440c2d000180400c0112a0b900860035604c0c0323030700701c400f0a00030352249000280141e4400b139010086800c00c45100181400500d440e50660140510360b142907500c02e0b6000103015031a0155a0507101c0306200160303288400317000600c50000b022000d240c5500fa00034000e0b06004001c5181060710407203241002810884103811235442c50410082c105801203400b80034440307440e01c00c00c12058070900d0201d80c0181001600081ca49201e03400b880281c0d440144520800d004008000a00601d10000781c140b8050381c01c0002002c600748000140020342c281e0009299402030014034225802e5a00340b0340003e03400480c0903a4230810403041d00058810f079500740050601d0301140c440069807040489004480035a51f499030307036512207404c484a028a407144000500079044140000c0c0b404000360601c8980480045a40c02210700e000d030501501030800c40201d03460300f04001d000caa0621a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 988311852 1250 988310602 988310627
    0x1814070c020f030a11040203060307030c1e0636050301020d140901020304030c11030a2f0108010501050405040902210303070f0c03050d0c090503030417070f05030d0f0c081801 77
    0x5058900c815100c80801c02007003103170107006603800008251540c60901400d0003864220a04020b0595100740740360710000c41940ca10110500c80c40d0101e0081d1043c0101d203d110010b451550440e200c80184500c40c8891690001070849604000603494500f80060141c140c00a440040c0103050340900300b6503100000e01c50180380e40304200f0800040d421012280c0155085806400c600c0c43c0b040201f4a40f280605025107101c0058501080303490071046025188010b0038020b03d01c5003228001034400b00310a003c1e0034007003072081c48140043c0c05d19501c0343314520700080c0240982e078a118020108001151004c58039504000f0400120642001d200840011145400f6500400c1034400810b180250100300d1012600d0f160f1110790310740303e0081e080142c0340c014143c950ba5950340f03485c0e03a0303e030102c410250180e0066620018140948649035011100040d000c2d0011820b24030040300c000b00743c055080248844030303100c1c1c4080703a084c40142c214108001006a002d081c80d000140c2680f54150 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 988313102 1250 988311852 988311859
    0x70501060f05100809160306050402010f0f0e27090309030624060708070212030a0906050403051c12090c060e061303151e0c08010f0e011814070c020f 66
    0xc000c0055450340c100b005403101c1030785080f90f9980c517468001e5007080002030006c1048182c920000c000d105082e882175016920036206c03581c0c0074801c0d55007135600c20714500280020403c000580195410030025105200040811001d9410030602c4408051841903941883c1903001240d140e2850404202d03064121100035001d204071085805420b800700034802401d800ba0402203007070003c0080201c191441543e00031301c0800907201d190b450958a03009008400000340c81d9180c0050044c1c0540700300c40550390041701900c0340c06001c01280403808205460401004101c005820304400b5034490700204901c07805141ea405480c10300024040030181301ca003849030004120580042034514030300001c40ba408420745010b500e0324089100104600d007070200a25140100820440f1500d030322030254130105480340d00690343c07070380c24283c8070401d01d0040c0032001460700014070030000c45003ca10228085a0300c04100754080040c4011188011b0300c50354041027030956030100b14540742c2c070400c50429064 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 988314352 1250 988313102 988313129
    0x4090c050f030402130204030206120604060b090108060402090a0513050108010506010806010519050904020f1b06060a060c050c0604060f3f020c0f0d020615010e06030a060e0c07050106 81
    0x72090910303407001a000a1040c0e5003075900003240400b40d0161001540c00800040d200c06120310318a40f40d41e011a551b502c1035140907004107105001e44292050200183e407041000c0d5135030010300000f9031148404990104a00c000082c1c00d41d02c2c10444084400349400c04100380d450040d020b42901d2010b0005c0707040c401d0305010010340c0d0b68042c007a103a15030700744454494000300d811310644451180703081c010380050000540071032030f000f4000100712504500c06106a0418041862030310f031041a03c1e469440080e0075002c0014038854003180244900071300a640c2501c40c074400180385a84039901400c0400d0307610344802c80c6150450114500c01882896140900d1004203002c149194520356800d4015610041c0c1a008019030381540c0250021600b152907480070030f03142039600c3c1d1641487d1801440360200080b0700d00c0080304078040300881a100c0220218440d001c100c21034100078100c2002c965241e0340050390b00c0c44604164040d2600040c1603903102c14505015083d51102c1d0450004403080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 988315602 1250 988314352 988314367
    0x904030c06061a12100902030106030204080601080105040c1707080a0c03120e090a0f0608070303110723101106011502121809180a2405070917190804090c05 69
    0x500200c8542c104180134104055640e6084031510280c59003010404a2000c00003240031a019401002510150800c42e0400c1e03923500c0c034190a950703007103d000309400c22940081100c00303046000301c003040b103c1c2425180c0c86901c4041c80c034a0700d840040c09880383c02084404005100079441c00a01c2d240b03207403030704141074036001011880c80200031305a203c0c0c980c2d40322000c0d4011483d030b41c44480a01f001d4419980c0701e43e581d08000303180814410312031810340624100000d03880d0a8284481c01005000311081d42d8410940c1002903a411500b14401030110146c62004050402e00c01d03107020b02904420454090601440203142410501d031402001208001407114a18810009610158200e6009106980350f030900c0c101034900f9015002c40f4803c1e44902805c010104c0a049441c8148803031200c01c0204d0784c14440c0680e6415a420000718500300740070702560f03100d00d043c94221a0079108640384640b9001054402404081c415210840046414088680507001d4a1456001d41c641f55040800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 988316852 1250 988315602 988315649
    0x3307031406090402210a020d060c0207050915150409020309070303030c020d02151b0c0c0112090b1b19021014010305061f0914090c010f021b0f0904030c0606 69
    0x1c0810741d05038140e038211060b00c4d411700401018103030542c060300140c034942d801d1501d04050f041040401025000d8000c02040c24107111110301c1c41150410142a40c45001c001884004103d41000441d0008100804114054640011801005150000c0c14041c0c40d6090040031211001c2c240e20441d0041405911f406078000344409002d8500d041d0901c1c1511000d8149041e242022030120201e0004a40e000b80c000020980d9400160b0a0701d61841c101c124200880803107484c2d1380010b04118441c1d0101e1010154414001d404100d035140311450009e240da03200d8086501042c180d8010307404683c1c0e05d0304d00c158900600700012030441c3c250b8159411992126215170300100302e038280040096102c481e0311451041e101c0100a10a0104503001130360921820b0070300d00b02c408010a00c40d09200c00910351040340b03203a015540307aa02402d90703d0040c00b00070b0480720036a07151507400748001800213880d07640c40c200c990040e0b00c6900c03104120411031401c0f0050324019400307920540b04084542c3c0851b00d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 988318102 1250 988316852 988316869
    0xe030d0e030a39140c010206070c110307050a0824040b0105060a02030d0501121e051b040b1306030209101508061201110d0614033307031406090402 65
    0x2141650034110040c90b0040d0302c0f0711004140300d141c0c0d4400c41c2600b0300d410301000e0b8290044200ca06003e07a45600c00b40c0f801a43e95103400d551450028a0000401740801c03030f03a015001c00d48000034180c414256940c00090380f00381c1180c2010f599a00002d88000c1d03107611809101034042d000c0c8821881602d403c0e03d42010000c01482054000c04000801034a0701c0d100340304030303004014103207010000c558460120203242080043d040b9072400d00103004490303101e0302c4861814020b50010041407014010f1004101e03018003800415045502c491182c51240e4541032105480e51001000040051860042201e4002c02400300e141e001403024041c025a05218411400140e6900304900c05032260800304040301316a0360800c605520308484054100c1071a8024500c0300c03d03040061001d00d032500000320041070000100303a0f156209115459801407442c140e810214000e0074044501000b5201c1004400d40072200c09001030b682c3c048000d0b40c0402e841e03e094000100b41c400c4441448d103139000c5902403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 988319352 1250 988318102 988318127
    0x20a0504110f1c0b03011e0b0111012a14040e06010507060c0804110109060c151e3207080907090c020a060e0606010207030f03120e030d0e030a 63
    0x603500d480203000070140000456440c9506080c800356038401100d003154015044640c520511401c215203104945014003e0204411080100c0fa94004040b000040148a148102414000003a0310105064401c1c85840e112440d90445c00200303080080c0054070800700c0c2d0a0b00c605101d85142d403c600081008281c0d07040da00403d00c03000c980c0d00c4500040c3c4240c0103a0030024442414400b84542da10b40c0a03110500032032113458441100e03620180196641d03d07140c040c010000e42c00c8400381c00401c801a00a8007410a14500060b0300001e02c5a1080041c140808031204507480d50b80400408a8881c04500c0000c048041c011000e444600c110780e040a025000c1400c206604d40440c4850400380321807001800355500800645250389406500c554802005a84840c0340c48007000980034041445442054140c1c0545820f508650720801243c0c01150180c2c100913820b100951000054820242c844850760011a00ca007c0c1c2d042e00b9040d200d403a5500d084a40040c0f200202d10b41e01b103038450b2001c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 988320602 1250 988319352 988319359
    0x80f0c03060301020708070f0606270b130207120809010912121b030c090503030304050601050607030302070c0b040e09070e1528030c0f03031d010c0b070327020a05 72
    0xc0352503000c0000d0180c0100d43d0050140324002070301400b001255490215954070071402444584d40d42d100d001d500101884010703001c9000708480000d06140ea034401c281c0340e0070040c4050701f8828603c0200c1c003260407a2004440103240c079250001c40d147c0010a131644081c400000f0b01440d00c0c3c81c1c1d60347d5021107940d1511802e20072101c417024034600040d000301c2800321591400e20f401203c1034800030007900300500d80c0008190200001304003414048100c5c1d12594001004094a900e4030f803e0100b15484164203030109a030a200f41000940840b4081009200010300300f41c450b420541c000840184c0607200d41800c0e48808000c00c02c04051180542c6e0104407a0710010300e4171501000301e00d0312001c01c01d80c40d041e050400e00e4684122001102401613034000e41c070742c2129a884807503110b494005400081c0200e021000e0001d92800b040d0b1000382e01c88418904003155845c1a0fa0300446460142c2d5940c0c0802e898054402041c1d03940b030314446000428203e41c2d81d0710130701900401c02810305401101d00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 988321852 1250 988320602 988320607
    0xc1006031202100e0a0b060d061113050a0e2a0a08070e060a0c1b0b03011203110f03090f27040b0603240703060e180d080c2a010c0e090106080f0c 64
    0x44aa486032000403500303400c0346d401d00c00e10841e079880c07107210b0b408422f0308140b10880210100e00e5041c221101000c1d1200006010300c90f403102c1510044120115001e5001c03808800d01d22130000c1c0070035024080741400c60325066041d04081c2d501404d90011042424040e503400d00800505e154030507110218030340c101c013030800400fa44840046041c00c01d50455081c05800000000c1c142d68003d0340207010754003a60340c14540414600e0a5501c03021780880043d0070703038428003043e84a45001d43c0d80c3d10307030620028171002140164003000d40428100069286026540008008c140462005640c0e4040d00c02c0b00580042030100d03002c261010700741004418581015400201180d010f41d000b400644124050a642492708068104a440550f10b6011440c012500c9250200703003d92030240c000d81c4188071940c1000b05175800c25096403103440b904802080c0001e40751401c100e00703110740c6510104507940c07591001d520390148044610180d0007501084041001c12400380014403006400c6400b0281c90350307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 988323102 1250 988321852 988321861
    0xb130b040f031e08010e0606040f1a09090c090f060f07110a030515160f1e02151801050f06010c080a0c0219180b030706050c1006031202100e0a0b 64
    0x591410002400c2030f48440c1c1100325144180d040765000f4100d6941d20141035903a40d4400a00019000700e2141110a48400c181807014032543c21120703600b6400f6240d058140440a800100d848406640c411005040050240c18500b00740c2d140030103600c0150b41e09450060b990030304203228840d01f5406809400f8503245d0ba5410340e03c42c4004401103421400f254820a0f88038182e10b01c00c1c105440c09080c0750809500302c00e69030b004654003c1d6501d00c07611407080312a000f800d8041c8604000b60b0030000c42c00b9081c5481036500058103018001c40c00407402032290000f8960745421540050040003203400044104207030303a0780c802204010079621018a45c0c0b1004052000d0b5800410b043c002544a01c070761000302e10800898040c10200c0361180070f5203040d10301841c45501203c1c1400314450f00750b0040d80f41801036500590040c1044842c0c0000c5420104503d00000c0440342d250300f0848102e43e0b02000c14801c158100a0702e03115412500c401c10041c140c0400041d03030341520920080080b2a5140040c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 988324352 1250 988323102 988323107
    0x90c0c0206031b0f07121d01080103030f020a0506070201060501020c0f09132103090c05091e101701020408010510140906010507080d0e16180b030f0f06040b130b040f03 74
    0x31444a541c1034252519500f107071030700c1b00c04039000026400011701012000d4494841c01c03507000c0401d2030103854541c156400c0d43c070126256000901d02100754440c041038440050070030440b1a1083c1181d074000a941c074203250009041c000c5050b0500d204504200c0b1051041ea91090310580014903044004005001490a04081e609607081c1c0140f00c0d8907e0031501c46d45402d900101e900768407882d90440701c03230b4403501044444901a154115030202c8452210710003240e18003c15000758484800400d100d59070032a5003500c07a41805840400d23500410708100d070490900071250403c1100b2a001c40d010705001c0d00c8024a102c06d4003240c8603411902c08900d280c0d002e034003146c2d007040d00240705591f1034804a460001601882c1c0000d100742c0b00301000c42d06080b5900800e10161202012029408118003101c2070251005102c40d0307038980100401100040c5e41040580c0000303409001a040610b05400d15035800c217402007150348144407081000e0b00154070a19140d42c440e6000b02d03001d20b46072042c2000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 988325602 1250 988324352 988324357
    0x5030910030e03030403081e04050c090703060807030c080d020706050a030c090e0c0c0c0609060d090203010e0f06041209050604030210020c15070c0b12040b0c22090c0c0206031b 78
    0x42c1c1c4a80d0000006000c05d26034890100c40c0304a8481e41c3c0000d500719514070684102c58100c1d40030300150082e2080c03c1c082c0c80c041030240d81040c094900802d00b1601c0342040c605102c0e55a10441d0141c0c9030030700030041a4014042141121181c2c00a00300e0145895000351451050f07042d104201591980d03200070843c00341da0a5009480f040e425034a9500e0074100509007a0302c0003014012074492000c84c1c41aa15103c1c085071100003010b0720260808110f10310601c007412150904990554981c114001c3e0083c0070084d000032130380410018075080c1021b00305041500c0d90713001c01c80100701041c0800d000341e0302e59004840c101c07581614100c1400d03280c41c200301d0500b40c2802445034454440c00f003036400d000d201e0010b09181c40c00380301118800b565032102c2112901c6804000040c0f01210340c0054041580080700c0d5030710081e0855250714190b610700c400c0703142c940050514988040d11b040c05200c2400d20340f0504a0030301070b03030605000ba035101c2e4000841500004040c05800d005041c001000768210005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 988326852 1250 988325602 988325621
    0x4020d080c120d0501050f0910090b0a05031c1b080714150405070602010b03071404151703211b0a03060503030f030f060a0e070302030601050f0c0c1c0503091003 71
    0x215607160f649038100b034005840c0c20f106980c4600c425200c0f1841c5813030040716140c0644440c004081415180407054009042e4004955502030301c2c1420010f26a01c0510002448a903580b820043c0c1791104540505400000d24065880624050b24813000441810494242507000a0a66803d200010807603180c903100b4811404800342501c180300c00c0020011b07000b07041d00c0d5280c00a10584071090180756680d0468499000c41602800c051340040c10258010380411503813102d00d02c0b90540702d290888094001c020450340715440020f01044142d200002d030050041c29113078000180c01d1020040c1a0980c05000c1c201000da000204420074034080d52181004110280c00e82380c03549540503003141035800803159201200e00d503030009000740ca02080d0200a690a040c7d540207180c49988040f00250402070482d41444030820080c4480d500403006014501c03401c2c3e000305802e4040780b00340840c2a8a03025058254000039215030005400442030302d2881e081520918190350402074202d016216a08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 988328102 1250 988326852 988326883
    0x50f040f031b050d0c06110c0316050a02031b101b0b15120f0105010602120703080c0409020d0203040515060f091e040320030405090a0915020c0a0501050c0304020d080c 74
    0x300500f141358000504440107400ba6004103d428400d0140400c00d220f004002c1085410400c541d100c8d800500c07620881c10780c0617404603088000c8a50100b4a00088011903502c1d0000c1c8202d241203a2500c25012007212440c0d01d0300d044000d4805440b01c00800e82918000c0640e5101d10000f8041e50003500302201c441c50044c102141140e80700d244a8032210801204003055007401c00104e819400001c0301180303000e8200350f41c1d1030941d03983c608840440015181c100c1010003008000780646407800072b0b05141c108030400507540d003440c0c0352142c0b0b08a416600c3c2c0707050075070315420002c840c1d07504c000c01084120262405020b51f9100361506a40040356100c10303913442d0100f0148000e240c1c0c080d8405105540c00c4c1544480d284054004507a240214450301b50f1141101002541d02c01d030581100c0b152621900700f4060007140c24030598182d03003144584a00550200e00c11009101c1d09004242c0c00c196280e03421440c504058021401100a610000d0400c40b000245058030b0304013000401c08100c02603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 988329352 1250 988328102 988328113
    0x409020706330806070c020108040c0509042d0c0b0f09040f02031e06060d0c0c050a08090109120215030c070c031a0702030a0905011103130b0409050f040f031b05 71
    0x40606400d0790501c03000b0715100101444002c5101c81c40010118001e0b4082d03203500d2204d03100f41e4011078003503000600445200c000f0b48400038041d20341d1115203005600c105494900380b20200c08108910340307804981e000c0b80400b0141e10b40810114a42441607810458009940b100c0170f404000840c4a5000072030380281c58510508609026640514007540c41c6956403640c0c5170440c121203498000541d030244e4800800c014036107038210240e12451b00d452007400c010100c0c20540e11620b040031a40130080d00c030300100094850196900c0f03110300014121000c216100410b41d0740114410180410025660820000205541c0708019080e2144554480034044e6403607240c0c0340c04601c806040c040c07480019668408100600d002205031a0b40e500c0daa40c5281c0e04500d480c004603440b28030308000410070300041118201a10304420210302904422141c1c0e681d03030b45011419000c40d0300c01400300305510381c8002840b0000302d69510505050340c1500d00043c40c040c407140542000c03201420020710078800c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 988330602 1250 988329352 988329401
    0x102010b06030c0c011407050a03020a09170d020c040c02100902240918091b0a0506040b0c0708030f0d150f0602010509162105010f0c090f050f01050409020706 70
    0xa40010300f44004c9040090220710100c1c10002c0c04a5130a031a0b03d00850360500061403824841c1d4003a2554031030f180f619446032640c0c0d90801641812002519049030004203491a0541d0100010f090500b4142e41c20007416101207002502c1d60aa40401841651261120303c03d6556600d010080000c541480d00f000c2c40841d0014a810f0340405041d90007001040080100d101107404a58821000c55029101c0070002200c00c080f0f07840d24170585640000d103d4004581d549544018001071310240300000d90f25004c00121602c1e008881e80440c2c0c181e801044181062020070307040d650750a0320844007082c00542c00b80311070f4040190350003001807200d540400040e495815003141e4021007000050b20000304000d03051410003025401518180c2c1c81d40f00c028030304a03a0140803a83d14ac0c0c02a00001440d08070303178079960305581c06038585000181d02c00b2418080540c0e5001c12500502d4101c0760300000c00855000030f01140118419060300301e501040340d60612006400400740340c445030420300351580d40f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 988331852 1250 988330602 988330621
    0x200102030709090b0a030308060409300305061c0b0903190507020906120319020a05062511070e0c090d0b070e06030c040b09180f04060c1b060b0102010b0603 69
    0x29544107950381e05013008400b250078209444c826054981603a6940582d07690801800054030343d510003160030010500c2144240e114000e84895040900300020310409000000101900c9005d407400b07114020304902c681c4c90003503864030f0680300c2e81d0050280e01c0c6965603402c01030840c0540b1296441c44410100c180c50030f10b81c814010703d900d5100301c90004150b280c5200b80003d02d11008032200d031a600c00c01c10008410212038100c0504040c0d4812102c001c02c8955980b07040c82025500380d42a15448188046001c0d0b000348240b11076002c074505049c144e602d407100503594000c240301c2d03440886c2e61180400c0c000711075001101c002c0031003d020071704e10302d030b0f903203006800710301c1c1252841300190f0f289403c800540340c24001c40f40601600203c0d01d041905003840e0818070742c48030010940c482d401c01102e0320440d01c1c021301c0034440c120000386c4030704900d014200754040d1086000c0c1075003006030a050490303e0500140350380743c000c0d4000c000010444000c10050b170040c80410b019562150010003045141078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 988333102 1250 988331852 988331867
    0x6190305030d0c0e03070501030e0c0a0b090907020a030806090709030f051c170613020c100b04362d021509210c0603010b030a1415012001020307 64
    0x300c4036408002c10f2907010b00803500e580c000c144103541034001c58001c01203507219401c100f6030740d2691800c3e80d030f07a0040c003c00141c000d100c40d4481100c01d100441c8807001d0340303031180d01545c1c0009280081c0840590b1690300811201c0c0040005200700c4403000170036a202d120381c3c0c000c809594012554407800010b030518955400031032030003039014552082c400545500c030348407192039036441c2001080c3c00d45400e010406600540050440b5141d824071028103a1141003100c20800c1c80502c40c0006c030008602d041c0015111141030355141d44800940000c1041c0800741d0a030703403503a9172050359030b0002068586810401d04140c0c03500300030108020070300b0f40c02955000040246100301e6640450301d1440c003100c07001e4091254a9544403688000600e40502c2c1500c1d5001d14218020070b03600c04201c034000150954100380c1000260b05000300400c01c00e120540b0810070b4012030701d003d4140380d240510002440020400c2503904003c00d48100c0858070344040301c003041d00010003000755202e1802d170200403c2038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 988334352 1250 988333102 988333117
    0x50d1514071e020f120f1e0c0111030115030e0c040c030c080912220906030c030213050402030c041104050423070e060403061d010c09050310110a03050619030503 71
    0x2e107a0181105425800050b0480030308804002800d40b1100e00e50803a2203980082d26401580401080280d9464101014034860b4610170000c0a40381c05200000d86d00f1500c1c5104468040c1000b08010300022101d682c245a00c40b002c1d28001c5059069541c1c0c8604194110f44c0560704541001c03134110303400780c01d60450381111005a58000c0155540007940340d64802440700700c0d0f5080800c206c80c980300c455920340131000806070340b46c203422290b5844501d41119a65801034600c03c603c0901401103144c50310070341408044914060055040680010f42c503419210074a41c8607542d64400b00c02d8420710203003568020000103104104514401c8a03500e900b42906101841410321800050384060244050382c3c0c13480e801820300c3c0c0c203280c29603554070006c100501342400300780001e9444e1030014400b4003e9204242d9280d56181d9082c0c0350105042c50301000c0070600305018104584980c841345034806464098070546404107040d211707030022520052180442e442e010450300c07000b00c00c0c440b0020040110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 988335602 1250 988334352 988334387
    0x20a0311030408090f010203120a15060f020705090601121d0622080d0f05070306170c01020604080310120b060321070303270c0e07030501050d151407 66
    0x142000d08504012a1008030740080c80c004050102c80014104460420500403041c01200d2a1044080590b46401400c4a07c000300b2902c0d843d094030307940381300a44034004090030700303002e00001850400a07490700741c1e6004050180c2005030018805030b10031031020311880700d0140308001c00ca02210020540040400c0c0e2071402c1d124150208140160080550180c2c0022501c0030105105e65907840f02160300403001a5101a128000403401c68614403415000794040e45001490310b02d460101e06440d0706d1003000134040d82244001e103a807660007064082e4801d901c880c10316030366a1960035840101d0041e4200b4401110051461000c000a0360a260b0103680c00320304803004102e00c00d034004686044801580b46014042c0300d00c1d00001d019802441c002100034080c0c1200010100c44140600c0c07600e80142c03946281007004110101c42019615000711480c41c0a02456043c10b0106071050541c3e0001401ea1140400d849005221a404082c401c440c40703020107560f09000c20001c00c0c1492680a01a2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 988336852 1250 988335602 988335611
    0x1504140609061b03130e06091b03070507030201320c0301061d061605160b030c1603020a02040e0a02091803030c18030a030309060e010e0c060c010b0306010608160c030512090a06050901020a03 84
    0x141544c9c040340d40c0340d00700caa2200c8140765950702a011200307500900001c40030b41d92140001880d01528002b54003012860f00c2050310300744002900800e040c7c10290180c030041200300014804194013220340c0d208e503442402e01c8414264100c0c04640c1a115500d000040e0100300c010f400c04004021403400000d02c1d081605400790b5850f0205901c1601c0151340c00501c0c100d04000555007180d0384000400d001f4002d005981c1c02c103a81d500420140d0794445092030454012408c1c0344110701c1c0904002c0d4100c4003146d41c4403c2c1f801c4001080d503481c0f00c0074042e417400b40390224101c00d91000440440a00c1c0d14040c040e917a00c04454030300540038005c2d1280c00c076000c605080d40050603c0e414441c00c5408421240180140c81c00700d000d0081680c8220140505952100c6650310191030411902c1d000700031a554400c22440c0624003030001c903041103100410041d2030000f03500440c1d0f0040a440e044030054051580c0c80d100c10351010b2808c0d030f41c1e52000301824102000c20403203180c10b60103882d401d81251000d12 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 988338102 1250 988336852 988336861
    0x108060907080a020103051834050a170f0f010920090117070f030503090307062303071b0507051207060c060e0c1504140609061b03130e0609 62
    0x1501c5103242d00507440b180e80200402c0c000f561081e00040e800000b500003144a400f0301e03035441424500d03500f4164003c1c505001c0680e001110900d43c0c0c1d0581c1c2c985400c0b81101c0c42c14003000401c5806a4400e10310303114010034900d00401d4003840f0307a00315580007c040b21059000d400c40140a042289400d640c0740c412000d04074291600e0030389840d40b1040081019840c0d03824220b9900c10100c9041c11407000748940b60012904060325000c840240d8020300040d81c8414104c002c0626000181e0045c3c01040b0b0020314101000d10210a0304000d044405441502da07650788608840030240d258926071060f2000021506000c404a0740c0d0090320000d84000d5000b51440781510780d00c8040f07204543c009071210076604080303034843d071016281c0303002e98055403070803d420701c0099030050540d105907000480c0003d040000c803c42d0150302510b00c1c0180c801a09102810f030000d80d0701d008800c00085801115841c0c01c640d12418022508032801d4040084080c0352607000e1300440280444039a4050f00644c00846c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 988339352 1250 988338102 988338121
    0x6010f05040c050a081f08011e0e192112060807050d06150b07030503010f0501031a0f0a0312121526012a0206071106060f0a03020a0e010806 62
    0xb03290003516110315181c1502c036001202d407070100802c0104805200d514144485034500d42d600018107450001081c440c446c00001c11002501000d6100303054a45032104202c18030105040e61441c002a89603640c0c55041c2c00c0c0340050000340101e10110070800b64030490015040400c80001d99403030740c2c0c04c120b11a11908601d0303680540d07015007640440c00c18003440001e001c0c0d4000c004414002010301c8039072a510b20514541d6080403400b20041000840184146184159218001c0c44246011300c840344107180c0c0c0303800604c45c1d101024001c1c0f0010344a908141c4441400500840e80700007020140d274100f100c0140200000006034003c20708103481e4145050fa00e88144055035041503006003404400081d1401c00004240d100089540b00c86451080e01e0150700316401c203c4520329040c0c800008043c0003414440010311000512601f40b160201c2c1c071200044032a4420f07410b450385801186401d0000700f00702e09540c402907000051041c007003110070400e810a41203440b902d088800d2a03e502004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 988340602 1250 988339352 988339361
    0x2210702100c091403120d0603050d09050d0204050408070b01091e050f18120705010b0108070302161e060216060507080108100506060412060b0118031109220506010f0504 75
    0x1e400000b0b400190a01c895441c00c14440030244e001021101d001268081311400ca800c801140510342e42e441c070b000c000380982171200784070410b12441d1046070b2500b4540082e0079200320078000381c0126900c3d0005410480e100302150003868101e00311703e1309983c1d10844400902a800ba801c403070403606504c0c05095a900b801542e00945243c0141ca14540d540c07450703d00040706014501503184900d134004c0003038940d00001080f445020380004940229980c00242000d10003800c5c200403d071040103140710400b81103100da00c00e10750110581500c01410803410001d00d19015002d0316080c400505000c440389140d0000c961288248010300c01da90740c01206403804202442000110b0300030122011500027107900040c1d1185c0014807050500d80c0312090903d003582c401e9402c4480700d9462090120640c0c10009010780c041101c01000c654500719a074426080c2d11401080703006100c00000f0501e44100c0c00e905201460119039500d80d4a10b050500315503aa00a106030340f140f941401010840e410709008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 988341852 1250 988340602 988340621
    0x1804020f040e1509160b12160c030309150c080603010605031c03020a0c0b040f060f11180a03170d050112120c0510050901020a0e040912080a0221070210 67
    0x80d1aa59401c443e031441c1d00c54005005a030207010307400342011240c1c00180d001c0040d0021903401501e40c0c2d8180d01580107454090107178000301d2082446000c4480c2d1242a8042083d41031401156403134a603e443c0500719540c05500c080c0c07501b4041094184c03940511110b11580084000b400019601c105040d2a25115107442c0c0c91482c070009031441580c0680c00928202c01d09103004003034194203455040c1c40b11807d482c00c40f956400e0550308014027201e0300403c0907044100c81c1c100911101d03010b84010038400d0004d0781590300c0240752000380559410b8600e10046800c80c40d000b195404030041d0701e604d0b510140c0902045803a1030f001007003403003940c1c1d440c01080e680704d6034030b6442074003425064948211500007101d2038854400e501d0513038482c46c01000d028a441800140c0c403404502c901030070b0300003000f1007180a80d103003105100114002c4c442541c80c450003030401140c03944441080350080c1c42007030b52041424a80303549444603900c4150010344500c2083d4203480c0e0411400c0d0b45074082c1c400c88103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 988343102 1250 988341852 988341881
    0xf130e1f020a140f040306020f030429070f12060f03020a06080105210c041e06060806060a08091e0a02040b271f03050c031204150c060207021804020f04 67
    0x10003c450994010014803a0310b0b1943c402c1400c0640d0b030750715201a039100070310b0b1601c03402c0044103110030040c20850010500240b01901090302c3c05002402400c00c500a04c0e4204003c05001821070b80c0b40200005201240140d03028002c241d11900780e04454041403200324001c000d03c1c000056424494081030741a00c0c0001d110620308c03c00a00390401c0c100224062400d1402012900031080da294854603c06410000d101c100d101502010b00c011540d040d0710400a024a100400801d6658403007142c80700c086a0404500689a68030b0003480c088202d0803060100390f6088601d80311a0300003d502036503d100b11000c0c0000042541030090300201003440c1100c41421804540d520800061460742c06010080414640b200b040301482041000354810b4445420482e4041c00500341030040b45000c11900610701d141c18a401d2004000c027155159080401000000141c1040344a40403200700c01c8e0020b0840d205d151010002d00b034082801e03141280314079800054038005003424090301d5441107454 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 988344352 1250 988343102 988343117
    0x80c1203090d1d0603070903020406080c130c0903080309060907091e110f12010f0e0c070b070e0a06051b01060605070201180506041212080112020f130e1f020a 70
    0x482c183c41c6103060000c00220320030000164440f6031a03c101031032041001d80c1c0e030300c4955484e60040c0030071500f440d04205210742224518040c1621355101405005000980c0000d0007000d10808680340c850301d030001081c0480010602401100005000d40240d0503802a903a91070790710b42a400840300500b95003100c070a070a80003030000e12801c1c3e201d01212003440b10401d150016100701101140d2003c4000400451031000501c40b81d80a40d0f4450040d1440c0000d100e21401d14a1403410389008100b00101090405c5002071442c6100c0c11a49903800030180070120103035241c1034060030030740180c011401e81e0084038801c41584203050090000301c0d80300c0d40360310780fa02c2d005400445408071081030000c900a2400000500354407958000d10082c031280c8000c41182c001e81c42c000000518007080b04041090180c018003051000c0010001d0440c0d048650910b0307180e003070021580b804e0322007031044092840d01d001c004003150081041c91084100710404070529081422140880c06111405400607080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 988345602 1250 988344352 988344373
    0x8070e0c0a031401090c02011a15160204020a0f02010c09031524030b010e070c02090610020a050d18050607080a050f070f23011a060313050703080c120309 68
    0x1003400408200318a868040f0303a14940c0715079010004004c2e400766580c44c0d6508004034982c1d6080c82405002403440240c5840765421500150858003020000c12003601c0c00503603840c060544802e0030780c1056000c1c00035034680700040c0c005000c0b040038444820140d401c04109200c2e0510440b280010389030f200300124440444250484020200344001104241c1d218030b0a12007407a109000c9030003184202002c031010360424550b81807440c2c018007144207000081d070006c0c0040e91400a03075940083d054409800d0b078100c40c54203d1408600200290150082c07180710381d03400758001c2c0c42440d04442d502407482c0c402c0c1d0b100306015041c070444001800513402130000111003445040208906210790800b039060071020f4a5040b8000501d4004a075075012400da009640c410b00c0e07a0494035100700000801140b00310400e807001d140052510a8403609001000a9a403100b400b02c2c403009039009011200081d4070380c03a08107955404100c64094604c111026207410310a40400c8a100b0f2004c14054400d4244 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 988346852 1250 988345602 988345621
    0x308040c0b1e091c060912020d021f060302060c0c0a0b1c05070c050318092404091502040602010e060606070c12030521070e120714030a0b070f0908070e 67
    0x440400a548100300455150034064a400e0b444c0e01315000c0d1a000907008010300d042084000080e4600c0c003036401100141070800d80104120005c2c0350360300f80401031700310001082c000405598200075440031001c200e21440500025402c2c02d071840569a004640c0d484030600b0301e0502400c00d041040c20301e009440300e940c01e10381e0801900050642000b014181d0280da074103003103807c564007481e13080b0200d20704c140152400c1e010494000400c0310000c82da00d00d104200802c0c000ca0002d15a000343c0d12041441c00b00030074841c50300039043d440c020840d2280d451b800024043d100221015100b403148c6c00c04102c0c82c0c42d01e281100c0c180c80e0f10601e10304450740741c041c1d840141d400704001a0140702092020a600e031451112900160307801c00f100040720318041101170041d02c00400c001e806520a03101e05018403800007819070581e5001b00000e0030b01c94450002038a08910800e0040c0010940002c0c0708155820220502031014540c551254890b111714115598052520601e20140b52440c08503a5180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 988348102 1250 988346852 988346857
    0x1b04090804082b05070b15030a06020a02010e0105060f0d030f05160b0403080907030c140604090204030b0402130902030d030c0e0a0f0602160e1807030f0308040c0b1e 73
    0x5215048550815540b1107049042808512150360b141090010007401448001c1101044000303d040c881e0900348503865410052030300401111b601003d40c10001c6a641e001c000b58282d96038400000e6584120240e0002c0c06001c000e0a07011080d800c05000c41d5844c9004604081d201001030200d11085e283d6883c110744c400c03154075980045c01000c001c401c05440d19841c06100860084e140e4600c00d05081c0b50082c90407100800300e4855401105042c40081c042d011868102c81c54220b808500055010010341d251149501c0340c1804c500c0000d0000401000c0382d0114480c40c001c9402460854505003040c003030301e0000200a41c5600441528543d540c0603900424590109143c500721032a05400481c07807204968005101d29041040100813155041282d000c0c4000d80040001113a460007094140001c005845000f24803c2125034400c0b4140801c040d100458018500d21041600b505001d03000d1002504c3c240d03074428124402050340e41158040ba400200c0101ca04003a40b401c401c00c1748101d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 988349352 1250 988348102 988348121
    0x2d0f0604050d03200708371404180b01031b050a05032203110c01020304030c030b0402031c03050403090501050a020a030804110a092702130c0e04020703021005091b04 73
    0x11405102c052000b01d40b440a0084070b03105105055031004081c160140302d00118062484940c00d41e40d04030047d420400c1142c01d0096242007400d090031602e480c800d12409190030110380f04c20b80038514100d10806421000c1207580a8908020050004121101034030746a1100c0e004104104400c251951190f1700650384410714100b1564086070300343d002004800c8804050700050341840e050854802d090224003080a400d0000717600e46490741d030737507548a4800b0f44000351031550401d0005055480038010360320b010b480302d1000640010044d00c064000c000542c0c05800040e41c5c0e01d40800c0550140f411205035841c55001440804102c1e5411680900d00a208030f533811410409800340d521400f00b90006082c80310400b240184144501c0207000480600007240030000310051809a00c41d29141c000c42049002c000c96100781c1007030140e074001d58010381190031601c001090020b260303000c9024005170003122010b000c992070301c007001640c600303104580c1d02020030080c900300b819207055030014584 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 988350602 1250 988349352 988349381
    0x501080f070228020301050609150616050a05061501210e010905010204270911060307020c0a030b040b090d05032e0b070c1d07112d0f0604050d03 64
    0x580079071910a03080800c07070000d20012004826042140b60038007c0507800700301941d5040c554506169010700c0d40c0c5000c000240540d10000b100302c0d0b5180f804070450700103074010088a0303400719581380c03042d0303a41012146d118442d560309880c18510740c0726010003580f17038140c5111101e91815880320031004203201983d180c40d540d070b51a10000054400e0000d40020302026445600000ca804503c0714110001075100c0c482ea80340a0740c040001d11406505941800160f402c130740c590b41c0c1e524080c0e1034418803601b282e40c00301c40018004100080002c9091040c3c0c860600c1440036111144c0040e40e6030f2000c10390801081003800014161003109840c1c42c481c20031110240c0004a10203810142c80d92f454001540c03000001822070140201140300400400c808418040c1c8410801003050f44400e01920031410800c07c404180540c0c6010000100f0f903026210700d030100c44c111050001d840358000300444a07140510079440f040f00402003055480b581d00000682404800c12408800030006da8880c4a070f07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 988351852 1250 988350602 988350613
    0x2101a100e180907080120030601300b0910030308060423041205480d020f0c09010312031b020114010e040327080f03041508010501080f0702 62
    0x280d520210300c1d001d207455001c240d1010f0706040701114185210b51308000325a078181080760340c40400340301110810301051001d0700c0e105d4660400485100504501035503242c943c413070710340209120f501072003a8001d040442c1040409000d20900c041442d0894010020006464082002c00d004900090f4841c0c001400001c4030130311561608075008940428030003803000d203002c12003005a40a2004158016400d1a83c00c00d106003458119181d04920000c1c0d08403140b00b150a02c250444109148007002d41038180c807205040514643d582c40c102071401c1c01445054182d000903200490311842e21800549503d80c00d81c01c6440f00e51490300c9240006003096950418440c03d00c01c0c0368000481d03002d0759400460300d02a41c12000001d90b006810102c5810103200a001c0041e401031201d83c85c030070004021407444014081403000300d0380d0f15409140c07180103514065100b00c80100040058440e61200512001c4480700e003120303940d00900859001c5109040402c650942d0490306603400031a6104950 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 988353102 1250 988351852 988351877
    0xf1202090a0905010f1812020f060c070f02040f0b090f0714071b03030f020d14030414010b040204091d060705121b04030609060b0d020112020a020102130b040602101a10 74
    0x20444a406c00061400c03140285e20004004124828040b220928401020762032544d24155458001c050101c0d9814800050800d0800009155811040781c004000f0084024003026503006415400320491240c1600e4000800b03000402411501852650b0741c0c564014084082e06d96130369200410554000c1208446140d100203442c0064014503c00d940d0102a003050200183c541510b4807002c0d03050140204075080c45000311000d4070750180d0041091004011104c441c00d0050207825009a042400010f011900340000c1e00884c170070721140c5c3d4600000c561004000c0351141000e96410000034010488107482c00500303480a500910b00050708030148030380d2814810550721940c01101e41700c0d110b040707560078081544160f2114202c166200f888a903490350000303000d40c08003c1c0310301c01e5941c0818840e004503c00d5050b41c0d8088003400350084501d884050b2461250803620400d4014460708580e200152030030b024203055085004074604c411841102005004002a00f036002041062800751 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 988354352 1250 988353102 988353131
    0x9051b040909320607020d08191b1e110a060b060d0516090501020105090d0f020f070f03020316030b060f010e04050f01050a080f030708091210060f1202090a090501 72
    0x8500048450409042003440f080100d03042c03440040440c0c0035900038003140d144c55030b007200c2c481c0d074040c1c0381700c203000e84003810b10300100018810b0154601c0c0e8100c84002c1c07100e45640154140c0b40f2260000c1a55050404540045440400c090750383c1c0590f0700000c2030000081d105400c4903600180041095062a81e06078201c02141c83c11580c403e0000b045d02e401d024000e40182c210740203403000788002c2c003080c5080b2000300d45e0f80031a0a0301c042080b1041e400d10a2051080c000200146200400e403260b0b17540c0c40c40c21543e803110600007a80b0900425265482e2a61070780f21080032039910003841d0001e541c07400f08001c600480703101070a06020300d02e410000b081d83d43c0c2c400c07907109860350000c4403215410401801400085074001c14010b03840302c1101108403100109640c945503006140340c0c0c1e6003400002080c03840140c10749600e064841d10365411615207540c1c00c20426141d0450240c15103e076268075207034814051307080103500500d6000c00308440c0d134416088542c0c0d55001b000040741544020404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 988355602 1250 988354352 988354403
    0x9013612150e0a1e060b1507111309080301030506070206100303030e0c0a09050a0c0305010503120702030c06030403090e060a0605180a0f14011d10200102030a02030109051b040909 79
    0x31022020344c040c03100e04101561148840c992800d5407040c01c2c803100b0510f41e040e144103000002d44101c00380c040c00060390356543d007503c2d0070541d1602c040c0a03103000c1c1d140070641900280002c8400d030040f4400500141e20009290344560820510455090b00d5a10103270020b120b03400e0824218020941503400980310240d0000042401180000345c5241480d421030840b15040e000008041c2000c004008503940050801404600380700000c0c0e581e001480080d191800100c14980c0000c07021003040f090642140390141298252036074001d081d40c5841c00c2000f40c403201d008031404640c05102c140e509032604031181c40100000740074220125143c0340a0a449042d542c0311099060701911403031010b5900001d0b280f42004100c85460b5002c2d014000070701084125408501000483c00508078000407111401e04a00b4106008540ea810b103000341e000694006d002d01140c140c00c0c5004201070943c958003100b480340c8a0345d107070750400d03082c03044600140c06254000d8030395a007241c242d005041040101d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 988356852 1250 988355602 988355633
    0x31118060d0c08060c0703030e15180c0301090609200907050c011508030c0709050f311104050105060c0601031202031e0301031a010f0b09013612150e0a 67
    0x6030391100c40c47d01e001400da5002040c0c020380d9030450800510050021071065401c080c0b403000011080300c0044480f031038100500040b950642c20001a00144010780e4810360031940605000c41c0309001f40ea144401402e03100b040503400411001c0003809a0341700c0c001510a41c4030150003c10512810b61034014034101c83c0c0c00111580c1c00011300c415218404110500007480310340d000f40085c2c9008190709849510060191519020040603001c5070b0040244040310200c030b84960840800c01801d11014507207110074018000c615010002c03695281c400140c80500c40e46000811070380c3e0031039640c209800051000ea409502c4203000e0080b903c580c2250a4a844443e00501c0b500c030342c51030400c0d20034000d04031602000102c01d40010311005800105940544000e0300d0303015543c000c00340040320cca454201100c0c500c01c050448406c2007008083ca40081c0071000316258059507200c445810b3381c1d19010344014402032401496580c1041c054005184105400d01503800005140d20f9000f1440741102 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 988358102 1250 988356852 988356871
    0x1091e09020306062b0c090f050f03030715020409060b09031b0321070501060b0a140711040f091a070210110d02030f09010f06060807030b0d0813031118060d0c0806 72
    0x803002d409590305485640f1050707039a4600020006e2802030b023188000070030b00841d07020350f4071205403140a880c1002292681c90b88440030704c0301400c440500d070009410074001c0b40c2c0003500300200055454003501c1a00c0100740018003404040042035800c0b070030080000780442c1c060148003154200303800640301c104103440e88645000d5941e1420f190090031154280c00c40c0f48604000d0200c040741130380c401c0001c00710743c6a00c404559521046e08000e007503409000c0c000795100c0d0a00190640c00282c64101101140c850039090114104000c203055809100704d445030010b900100781e00b81d4140301c642203804010010141e06141c4030031b540342c0c80180c0e80215402908585400240b11300540c091140007440c110030b440411626003407100050041401601e0002050b40b203000251590342ca0f04203e004d404da100c0700b510b40da5440c1c0804400100350358442501c0280306003550a020303050103841032020099803e00204503030355030002c000c0c01c1c04e00d030b00080d02c00190303080012454040810443e40140e04a2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 988359352 1250 988358102 988358167
    0x30c060406031d061b030702010216150b04060b19031d16060807050717090a06020c011d090106031e020304050109020906010f0806130f180201091e0902030606 70
    0x111038810041500f00b00c2c20564080002c1000c180c12210180040c031002424080d940d449241c000ca029015080c0144a44070b180e1f5280c03010002890828807403000202002e2205694100402040300d0840c400c44008100070010308071060080e000340d9480416509002845032100b0101d00312403005414040782c160f0143c0c0100c01c06915010030303c0c004101034508510185404100100a4091054000e10305122040401c011102c5141503c900c040d0113070134419001daa600d8000c0d0384015a04201d404905202413180c05250b01520f240d040360300c05411141071b03902e40300081f0018155800920b485994152181030881898002980101c2c000c2c0300201301c9040d14010018a5003000d00f246040c010700520900900b9003104850794013400c02c8442c0000c0d0340480c2c0301840544208080c40a03c1031802014800c007040d0452491062030003a660007482548030055031040c4040700c01295180703480d90100b0030048a843c2c006542c80b40c0003074015402c01d0b0103004884034000d400b410340c100c81907030f2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 988360602 1250 988359352 988359371
    0xa030f08180603010b0d18050f0a0b070f090e07051c0c030b1210110f04030c09050108031204080307090f1d16140d2d110406090605030402030c06040603 67
    0x48104058900c400b00c0d100d52865141100c0700010748580c41039001401c1d01c078044e1340c0c00207040d909100c800d160014261450310808030340d010f072551128101200c0904a0601003041240301d04291001400d0740c0c5c4030300303600c541060003070f0384400402401c0c20200032041184002c004400703c0c1c0c24120002c1220042003a0a082402500382c0b410718102c40c1c00380052041d43d034480c9200181c02c080032880300300000b81c0d08420501c1001144910000090302c0700c00054000704005995a003202140c4a0720000c2003240d0300c17403000944a1041c3c2146c1e0002c00070010208000c5000c11000350380150356810160a2140c0d01d1010170b108003810391022446007c05002c0410750180d12005581c014030074003400056070303008240540140340100743e010564101180c420320110150780004c0109072401081442c01c648045042d0088002114241c0034604040501c55100f5001023a2420780315140c071340212103400e1401c100c407103810042090382c0c075100c4e1549201c0c2d41c0d1140030042001d04503540e0f020540c50359 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 988361852 1250 988360602 988360627
    0x901110423180c0714031c060b07080712030e070303090e072c130504050c030f030a02070b0f1c05071b080405060309030c010c05030a0c020303060904020402090a030f08 74
    0x40812424080d032258003110003a84004140b65901080401c003681c3c94030281d00389170302d01c0810b00d415008680300019104122010302590440d81c410706a801b48000d548807042580c45000b044401042c01c2c7c0c0c1800000005030000350782841f003840300d190000c2c2403c941c06d141d41c42c08440f0351040d00800e42522003400741c0e236401d1848540c4480c49042000d149925440700c1c4440352030607110340060b4414103a08030820b0b61580b8018100c034440740c400341b00904103418000e403111071040f5a14420b103e950621820380101005441e40144039070060b140051400c140b41041d6408041914040b4408004143e00801c40515841814002e02c0d800180c074079000701c0c05003107a1144142d0403900c480d6024400c000030080c80c100c030103030b0390180c40060f22070321948510b43c5140100c030348882c110750a00d01542c910a0303004000d50300c82d0181880a00840100c01d8003a80c50b0711041e02c0903a00025000000303000350038260000c2050000c09840780344a0303035589d2a10071000c01c031a40c08854035040010911640d10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 988363102 1250 988361852 988361909
    0x1030c111f0b0f030c0f060906030c19020d020705040c0507050d02010c0306140604051009031505040b06040c0804020f0111150103060b0a06020615060405040f1410060f030509011104 80
    0x1202941d82c08480c2e03030f20100195603000740110003880340c880301504465940f40c507000d0725180c0c50080d00160312401c0000014116400521007644d409400d601d406c50300b030744001550b01041c41d064014168050800c002e02000e8600c000851090110411024000442c01c000340082c50007142e00000700034081e01002002d440d202d51021a00034000d0303a54005d00d40d56002101c1c129070080b00d9891000c5813803c41903c13109c40d90751014100795110014041c800c41c403600701c03e05c528404c00c900b41550303031220200411250746114440001e40c1103400107005041040070300c401d004050401c55504640c2804262402240400b111081c89402004000300421070158075440541100c07510b500909001000b50b5400c0000e082004d03001541150451680384d40040b28003406003e00b0034813020b51620100c401401d07200300d50030203032004680002d0306180326415400a40d070303450340da4104400c4401421005424080c24040e540d55032860948200b07450800148010718182200c54111050615a12001e1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 988364352 1250 988363102 988363121
    0x90d110f010e1003050916030b041a040f0f030c0b130b0907030b0f04060e061302011106010b03070e0402040e04030918150b1b070618081b01030c111f 66
    0x420b010b4001e01d80d0707950f05030812502c00910300001c40e9070720100b015141c06905c0003143c40c114000c403030100078049a9403075144514061104242c8024a24501d00e420200480f03000c1c2c00190301c0141080002d50000500400d00c1c040c0c50440110b9020b521001030025080e2605a0442e030002240f00070402c6000d081607109444070050b084a03880e6480d00850424000c0c103201a08007248006000c200c8242d02140002890314111106440d114080004410a00f4402e9001c03c140100c19000d4400000700c450585a1180e4200e0541d254110151510030840e20100c0d880343e028800841c1018400b10524880c40c0240d4410301c64a190010000c03503400d2803084030b2500ca0401005c1d0413a1610b0101c01011601488000f42e945d6151142d283d1240900b101400702902400c00c001030700070ba10004058142d03445400e10421503648056150362114607508844040248601280d00343d8000c1d8401c1c0d0505c40a410140303a03040c501110709003424043d41948a40c5031200e41c0800d41e1020520501c03102d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 988365602 1250 988364352 988364357
    0x9030d18020307031b0f140109090902031216023d090509042a06090b0423031603030f0806012604080d02072406051c0602090d110f01 59
    0x410580c012036103d20b428040603100100110003480d00c2e0003901c0e018401041c8a078000040c3c192515048400c490060340c005001440c0380d000030404c040d0f18421247d000758014000c06507509000703048001504050000b804149000c241840503894291485050001400d003203c0c1442d014440480f81c40001c000c01c0d100c1c1d8185401c100030701c1c1c3d0002d28113410341d501207610100c242d0701c501d020714110b040010441501e04121102c0340d00c0b006180812029101a6100c4050090721a00800000e0143d8810800286000c00814446d00a10201c020300c1c164007405560028080c0d6006c41880005036004030300140c010008214255401122240c00c0202407030729031f0b0300041d1018124100c4080648692080b070001020904210010040390201401c114040d5202c410b10704100704404040d5150000c0f100e1b4128603000f0f445564072544003039030f40080c450421007a00901c12215a640401c046407801d5081240c03c1c01384da180c581c4944460321481e0340c002c41140c0700080c0000315140d00c0d00304d0306 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 988366852 1250 988365602 988365641
    0x12050a1d1c1b0b040f120e0f010503091f060803070b01030b0f070c0605070c0b0c070201081006200c060424110c040b01180b030106021501150e0d060509030d 69
    0x210000800c1081c2081d6004841e8201d07540b1107003001100c10260343c030001c02080c0038000744021b09400c41e0400712141e01c2180c0d989800e015210055500f84400c031640c02c81d50700103401321441810000400c803021038850b48002845d6490f16109880c6500014083d905881e520f00100100090c0b59480c580c080e00e41000ea41480c14503420140405030444002445a919400000c100c10700c1440e000b9401500310f4550035150402030390a010301c1e40a01d01c00d90000384450300003000c85044100841c2100c401d0703661022044240321a2075008107000c02c26491034040c03180c0440150752170401401c00350000004104105010307030814000080c0015400f010300402c00000c01400f40d021440035400c1c80241d0f4046420400f03100101e40d24070114903000d42000440401180422030840030754180d402e13a400b1103110001c908811145c058091062840100d0200e2001ca00140f01c5c507040da10a03003014005804418450396070704166401100c41c0419075002207002a4442c000380940d60301010606103010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 988368102 1250 988366852 988366877
    0x150b0403050c09070c02190503120306100804081e0d0608010926040905090105040302071e0501140c0f161e03120e03030c2a0112050a1d1c 61
    0x41d1250281d0191510400480000801c800e0041260010305c40d4010b0440c001000074040e20005409a4000d590007803203080598007004412504030380c00340ca80281154521004070710b040302d44200042080368400405d0220380802c054074064a4186203441d002d0310b440d035012840b480101c400c103502a0060340c1c1080316039030201e1485041002950b00610490303040800c100800d1880e071286500007510319191008104c4060340c10b500142c000d512030350070380e401542c0d2658400300764001e140e944216038004c200200255030041e0a040a04102c001c10241010492100b050511228504104003034125400d040b100701d082c00e0203200900700076200c0031020020b44032845402e003030324003009000500000d00c0b000072074000c038232507160a0402000c49a980f1164082d407921014040907010000d088031300104403000403a4140110361006945e00c2030305030750691204001c1c01000e8a01c04189030307281011030542e440e40c180104e00341d02c40c03001000341c07901c40d01d0410f00b00c10b600b54984d820840c0100341c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 988369352 1250 988368102 988368113
    0xc030609060411040c3603050a0606140a0b160f050d1e0906051605121321020607060603080c010c08151809010b1f0807080f0a2c01150b0403 62
    0x103100c0854002081c80950f0841e0308603c2018031510b003a0700d50f904039506d00104004000807001c01061103070342c06010460ba15403c01c1319200b080381e603042d4450f1086800f4014152410007401d031020740d0445074840d071ba41c00d0701c80b060200e10008040c1d81b0b0ba04224044001c0580100f0b031b08200c4071520017003110100001c94001e006900c0d500521040100025031483c0340d1b07000c2543c10319842d400c070b0165886404c00944030502980001c0f400c040c00b1124580001e070001502d40851800700380c255402001201590806c5900da1100004540c2165280000300c0800da4070300241811416007800010f6148041a0141c5030328402414114041c01010103802103031142c4104040d6540602407045040c0c07140c03011300f4054100c03ca03105401410403001c01e06004800480a00960050b40712040140c845c581c08a9003803d081302d0803035402e0400780200349008d060b40c0c000703d0605000c04400303c4002d041090140c000c4800400740e42c09030345a156612806021003041c0004103090308085151600d15030703c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 988370602 1250 988369352 988369367
    0xc03030f0c0507055107181203020a0b041b170c09040c1a0d0f060e0121171204060c02010e1c050318100519060819050c030609060411040c 61
    0x14204501c5c080c030103c8900c030008a40580500c0c001c1d1102618101e01c008000780e0120707900482c0c3c0b01e5049000940d00e4079040201130450742590192074820000c0d1580642d080f000385c0121410300280301c4840340d10b00000030900141c0420000b1942400460441c02d241803400107a091040030548140800500000303204401c586100344a09200d10741c2c2182c500d014002d048040300003a00340941320166403840d92264003030b1070346522080c41a0b40ca5160700d1000e0080c1d4030030064240e0310f4032408000315248603141b81040d00c000c11207a00d0000d03044001034185000769000c5a40f141c4403000100001e03028021140003020842c01004c048000c15000740c40c11180c91045000d02400001040000c1d11410a88500e00c0c0720100300e505c80340048006000508085420b644d004d1501c9517051820366131030180c40111503c420060440300500300209501048101e41101c56101d9883c080c446914144800c40c42402014051f1100f0310380750802d048041c12000900e0320442c0381c085080d03680d603040f442 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 988371852 1250 988370602 988370683
    0x1151406070611070b090703060f0b03060721060b040905060111061828060e0d091406070c12140102032211150406020c0f030303070c03030f0c050705 66
    0x483c01c44803407480b02c1c40034420400043e080c401035174108003a001c40000c01e0b17400c407842000204151106a01d001044460440b0300560680000c0003152407503100c0c81301032080100e181d0f140c92100001c100c00e0303000c4880c280c6c01800c20350808034082110741e24500c00c1e00e5100c14282441480c44c208125141d171502c0c0018070111200c10b0180b80982d480f0010801ea032050342c8109618580001001c1440140890f0100b00700d44490404110b485030890214408520342016211103802e0360a00d5072142490b9954150640c0011050050340049a641c24002001744000d4074000c555000a060031000c8070380d550005500360380100144000085e080c201c003207a2064050110a03004000c1c0703420102c000001c110a03a100d641d0010005010341c12000404c2281d07a41d0b000ca40c0c5105c603a0050008100ea1100003130b030f00d40c205000090506000d803501040c210b22070710b8006000d00111043d50212642c0300c10090000f41d010a102c1c041280400c2100141125041905a21524010725070f902248191 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 988373102 1250 988371852 988371863
    0x30804170304030f0f140a0803060409110a150f0c11060a051204030e0a1208041e08190b0f06030616050705030705160609030305041e03140115140607 66
    0x351214504000d2055502440d0301c00385051000c07000e800e00c2c45011400c80b900b50f030300c0703c10000c1c00c1c1e8101e440007541145084d48006104e003035aa610382000010b0504200c1560f07160808440b01c0f25698580080700090203400ea03024201190b0400000d0802c0c01050080043c00180404100480d03c4503070184010502150292351340c0c144213108580c0d5000310004a03440b040b031a0709010400d0380060b541011400c0c103641c04d40202d0741d94a04c10562400313081c405000c02000700000c1c0070310201c4204d80700d002075600e0820301c41e040e99001c4103490001034801000c100d83da104442d004010200103503641240200d0a1a02c0034204580080d40f5600c01030007003405010303007080b0011824015415281c00e03642080a503600d6035413500f08a521802540440f101641c0245000b0503540e004620110a480d00f6a460906040c108400e0071031010704e88054605a41214600000148402400310380c100200030010030305000352500d89000710100d4000348003898051101420b2904d070303542a40c0c44640c008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 988374352 1250 988373102 988373129
    0x204020901050403120908060c120a0c0903140d030f050402010f0e1912060c02030703170601050405041a0f0604060c03030b1203040314061303091203031b022104030804 74
    0xc200688061203a0b0388000c210440c090803071000950060034540455040c081980c466544800a004440c42088002c9104d030100c540840c04106c42540907200c40c5020f401c1c403164803078032501d540c80c045155000800700c0c1e80c0241400131903e6450b000310301c000741060b54144028242980064880800c42c2100c44c10461288418002a41c400c1307124060ac8190301030540529417241c1c041606a6040c07002a1a46810540c0c9034a030075100204440d50340350560380324640b2401a85242c0880036001d48028100601800049203d541d1885261300d275804440c91081d10030840d40c18800c01c130000046c014412041804108425070308268803034171865040c500021004481e000040030030500e1908413205100c00310300403003001507450156003030500400848141c3c1d40c60071484c04100b4500c280042c00181c400c2000c001c545000300018440d90b21900300403840a01107180407690396a04003500c40103902c41c00d403444c0b40e202c8002400c40c11940c0848030f03d14242c2541c40f8081c05105074440c3c440100c518 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 988375602 1250 988374352 988374367
    0x1d010e0c0114030403120f151d0c0d0902090c0d0b010e01052a0d0c02181b0a021e0610082a06070501060f03062306100314090f0d050c0703020402 64
    0x640d041076a0f100e5400402c0151824945a10000b04240040004030784230b0301c28089030306211201016550a0710300d002540640d501c0840d07040b5500301800d0011026140c80c2d1280050344c0e0171800900c40c00e01c41c0b804a4807841a001e80c135041d00c42460301c441c140101d034910f48004e0307680a802c0340d01d07407018004a550b01002300400c02242c41e0032900d80b100b140c082d9012003e00e03107030700c0403088080c64021148047d0884482101860400c1d00f510390810240c41d00088840701c1c0d650901810040480d170040e1010460700d0101402c1e1040034021090050700801c0410000000b4800c08801900c1040700400e214400402411300c0810b441e20301100804500000b15125685c0504903121b8079070000090040940d1440c2c0b08034000304038041111564107102d140c0c40d5801141c8180000d1a004500c4032031785480b20401d1101e00b04400981c1d001b015100c0c003081b2403200780501c18a01a02003030005256180caa0807006040480d007400320340800c6010000031000900c0055101d0507030b50100c500580d55801c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 988376852 1250 988375602 988375607
    0x101d07030c020f12071716060b010903060e0a02100309020d0b13171207030c08060907140a09050f09040b0c0c070f0902070210031104090b040902041d010e0c0114030403 74
    0x440080000b40344941c420802544d013804020344040d070301c280008046035150350340030200f6018006000c984000c0120f07110000c070380b1581180c03482150606100300800d84946500040d01c01315074040b07441d94040e801090440c2844c1828031036018041c40c08000c40c0e00c041e4005200400140005403401d46d003a0041843c1d041c803904c44c00d0701c4c103501495400703c00c8048014204244c001d00c076000013a06400d00028140b500078000c241e07980c425565403200a5803410b040262000024240b0003c104e0300030210440d5001d804003c1c00504c07100d0301c0c2c51020514010400c03c0d21452020941e018601c008280000121007000094101d0400a00745456040002040b49008000c0e805403440c654017510008043c07001e0b90042150741d0090326103802c0044005c4041d030984800503a0200390400400c030070803003c3e6807644081c0d007508000704049001e811f1038000070269200382d5004845402000006404450700b40324410360100c020003d001001c1c00000083d00c03500001680760500d20001000408261 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 988378102 1250 988376852 988376863
    0xf05010912140a0b010812040e041e150f050a110313050c100305010e1b030c1b01020307050301051804030c0b0703020c07060917031602060f13030b101d07030c02 71
    0x11510440c0d401480f50b084c0821221420b20400042d0f02070307440b00740b000100c16000c8400f82c0d49140c0481d15143c4a5640314032032601d0768141c0711800e1080d545401c0001d040c28003104100203500c1c9001c11244d0080310400c0440784c0140141d030711180380c192002c01c00140138090701e50040710018807400449480c1051424032510f008520f600040509111107207642552019058482640c0c0d12080c3c2e50b00d040b01a100c89007900907201040c0402d00000c0d81c103d144c02c000384402802110f003401c103010101241030070790b0000c0e20318001141c8084014031140c141a4001e1000d40c1d2005207620b5281407689000d0540341c10000f010341640c5180000443c00740c000d0f0100c03500203200e0030850f44415910726000705484d0190007181d11f9481049004146184000150f942d20500039640c007000050540c20000e10350312550b00c40c0e200c01c405120094144544048140082d8041c0200400300d01d402c0b81c8070082881690481001c0704250202440c1c0b80c04000d90080e4043d0050a0018021103548426454403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 988379352 1250 988378102 988378133
    0x305040f0f0512030c030f07050a2a08040e06030c01140306060a0905100207030302010b010c1109040c0806012301031109191701292211160c0f05010912 67
    0x1800001c24000403003180c9001b948120b140c0e010b250100c2d21845401c440c41e10a8009001c001880404c40f81000c134044c4046401c1d0b043d02500b42502000d1356503980800d41c00581c40081c1c806140e10400055007001d201444d02105d00b440c0c0300105102c002d031800f025000207810907000e08404a4007030003040c02503d8050250030000c0c149100401c405800955410741c0e40422401075080132410580e9502800e4043e010944c04020280064440c1c0248000503000070300c1615004800000003942030400c1c001603000c2e0000f16140c440440305814156076030140181198109483c0040c0300e00f12089000c01d460707181400b100d00d0b5a400c00d03030144400000900b9000f584100701c0c01216403184550540c4007691040f81914000809501d80c00d040350714121030b100890b0041c0d540004160307102501d01010f06918100b150029551780301c00d540804980000841040d110303900c000c98010310070b1055500c4024180c14130140f40003410140001c0040d04648110080041a220380748204500782214245c41e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 988380602 1250 988379352 988379383
    0xc030807080c09060f090a0f0b120a0222031a0705030a1e0612140303040812040c0f0608010e0a15060f020307060c05030402090a1a0906011b061b0305040f0f05 70
    0x11040b1030b03245d0355215409114594450310310001d0010b00200c41c044403104440030810f5231814900f641c0d044013080d51008000c0303c400f0744c0c00c00150034101c640000c003040009502107800c40d0142541341c254001d509041c08200380300a00000c00c4020b550050803270398000190800440c50900e1106036051403d800020000d00500704940484e12003003034800001c1850081e50004010003600c0318403902c0380302c16140900740080030000090b80446401c0d04035002441136040d0b40000340e41d03061010b4a030055402c0a00040d5102004001c94140c034422550040700d922010054142d0450700400c01c2c2030350380b25003828002c41d812904c120038001d00035582d0440d0444c5052004c03050021000b0407503482140c0491043e249200801c0301c907903091050020040e8014001d0198503203090030008690782c0207119904100264500e110f00b0741c2a036040e048583e220ba072021800c2017060346030010170301c9100d02000c2018030344410000804c8100d00c0d0325031480e0f040106a080340f0403505000b41070a0044808040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 988381852 1250 988380602 988380607
    0x1030903020a0b0c030a0f0b0a1a19080105210c0f03031b011b1704080d0b030d03090b130201051b031201031208070c033c0e03010c0c030807080c0906 66
    0x340c2c4c1010600451256100300b00030070000e10200302c50350440e1014402c06401200b120014003060310741c001015000c0c00c0300c805d0207040c284084070ba030801052461084000606003401000305080c000010890545107501c080d00d072401d14138070b01d0340d20116054905c1c0304400310394185a2036102407003191050603113140b1110845401000aa010b071517003044406810781c0866040329503e21035007080c601621440d2003e440f985071a1101d600d00c0e0844074440028503603c00340d2040542e01000308040441c80c54601142408031800c2000a00300001c00600641305000d4007000182e921008440300300001c480150000912001042d02d180154108950240040000881030040010340406002308642c0c0741490365440000448450700341c01c0c8000c02041449100d0104402862000d00404aa143c20503900400c800075011155a0020384076010894a000289480c102070003010004009400c1c1004980c1e2650742c000e000c400b00802220070046a140450307400c0d07090b902250040d10b802412941c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 988383102 1250 988381852 988381861
    0x1c0f020a030915141b0d020403052d030708070c0e010e04060e1203271f0b0907050306012303010e0702010b0d210306030602040e100902030f040201030903020a0b 71
    0x3001050000802d448111800c400c1e240580024014514400740c4203411070f0303d58881c502d1305c0715440c3e21254140e14004051041c80c0c2c1040c110710150000314003a00081545245c1c2420501030416161181800b13034420401d807644540d0f00004031040e59a0112003181c0c3d40d50b007400c061070304c40d00d030b41c11076440c46c1912000010318003401640030340600e010740410004010385500443d074610340c0c551482d00314802440000c01e02101054014050002010b0b450001100d1b84625070509a1950810034941c2d20703980303485000401481102d070948001d40b410340309800c0650000c2c105010091604d8100060340b0300d5410f601c0c1c9c2039a910441e6840b845245074503941c5800804151a074221040c500540c0303000c00a840c180b4204011190080e004582601a02d82607440003000c610400080350034036454042c0000007a007140b009200500d210403000ca007506110611002c129010303407000d01c2d003d00600c1440380c0e9450400103184c00c164242000111084940f500360b0030486481c002504001c0e1031402c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 988384352 1250 988383102 988383107
    0x3120d1107050304060807050408190602071401020310090204050a0504020304170a030b0f1807180f171606080c03151002010c0f021501030b130c080a05160503031c0f020a 75
    0x10010f58500b61500b02c601c3c7d40d010011210f038000c520a003e103aa02c8041e8074200e100742080c1c0050164028040589410440d4445454409500c075484880380c0d400030410840954508030700b00500914201035280619000001c0c003021001d01030300344aa540000031a041040384180c2c00401c00c0d0000416072200c00f8900c0c084e0090010001c1c150150000100342c0c203a52500d5450111592094902c10002c0c0d100c00c1c07011940e80205101010710041035940104400301c41c4140e940040c280f00310030315842e24060800c6410401245403240417400e640030306000135030b001441954407080024509899a03a00342c030494200b2008030080c2d400c28070021020020942c103410814544030603032184501030780442400c0360340325001444640d890000400600010f0000043e66410441030383c60b40d1111750301d81d02d400041843c154011145175100044c0c0e48100003086c401c0a0202c0304000144240c5458803010a032a807040701581c402c400b00c000e4080d0a1406550702c01454040540c104541b2032881c188003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 988385602 1250 988384352 988384357
    0x5010302041503122115090c031404060f09020607030503090105010e010530030313050c0a061d03070e0a09050c030307111215070305061c0203120d11070503 69
    0x6a006a0401c0c4a00352244800d0301c030003080301e134012001c550886840d40101c1d00620049428610409800c200800c1080c140c080d003404148a144801402450304210030111020904180240343c24001241078021124800702e80c0150006d90200b035911a0680706801000b030f1460080d8420340100d0100e081c590b0000c0610311420791040200502c2c0d807201e00341e00307801e502441100da1110f18000310049144900c030200c00160703100a02842c86c0041085aa8103580040b070b514030300c080f001640380e001d00c20100a0107815080541c0c0c41c0070010301b00780d00105400103030424070104c200d0740d08010049440800c0260020240c85207090443c1c14503d5461000c0d02000c50103840510400010390440e00d00441140d041c558015100003c1585650070f001c1e18010b001c000e20840e0040c4ca140550034840c440c0703031310721480d0349035170010709850108100030800c00400c2161194224181105006850010320785280000e00e4003008e0b2600000c0500ba4003400880300b40800c103401c0860b141c000c01c0000000f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 988386852 1250 988385602 988385609
    0x10204080313210c050105071502041205070e06060a03230901021908060618030a12180b0903100209060c1005060406120506190207020423070c211107090501 69
    0x48a88034507a0f840240c2900c600d002000c2c1013090b20b80001c100c2d41d8001c000800f44548a10814a132100c1c4c02c407440000c9030016444109021503c007010800c0103400c3c071111020301502c00c0b0400c2c40781410710108078640501ca4084042c0756403003510319112080c203e0364424552191140c00c0c103920748540114042e420410601c0d0000d0340300c640300507c103801800d4070b5100c0c0a002c1c25040c10701c40c0b14000007402006001c074a0360107008140804002c1400d40704242045242901e48850f14029062103510494050340a0000c00f142408504203555022480000c560100040941c699078002d00007542c44c45032900e40c6555100740704c000d41e05003507e41c10007449002c04540410115540d1900002c003a02d03852401440c03a04402c00044140c0340589000c0d140c0c0329403100042c205405a030100d400c552070a803808000700c010b484429041c1060801166101081c1d1901207411000c958030a00b03044100c0381090941d40d20341440d5410713948201844003c52601c402202c003600c0d5030304040c1000382020301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 988388102 1250 988386852 988386869
    0x4270303110c0309060706060e0114030c0d12030902040b03030a08040b0f061c08160f0605070f090302011103090306010f080d0e010f0509150408070509240111010204080313 76
    0x111640030140c0d105007070b82d40c642e010001440c5031216500070000b913507224080c2150899500c1c500402d5009546440c3c50280881ca45032010900301300040624042000340380900c10605036844000140d01e4204094542000c1e0802082c11542480003601803e454004640c05200c0070481c4d2000700d03400f400d0385004a000300840c040c2902ca10394000c0f03070800200c400c20b420000e40341c0700a540e507000300c800c0314400f8000d1444a081243d0300200b008048210700c01903444400410880c03080c0103261041a4100b00b039828822014600c07201d01600e0b0000b070384000303811300c00480034480c4480f6003402190701c14003000f4295001903031945402d070ac106c012401103d070b15110342c2c2c9101e8419030141c2100591400d058450407013103101500111202d034000407901c2e4003d5150300e0b01a58400c0000d0103403001c1d0092401509109041c40107108a1002c01019402040c1288007280c4040003c10070501c80b0040a02c1c2070300c1c0d042c00220219000e440307076074441c4807180710005410402d8032070000b54809a480700d9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 988389352 1250 988388102 988388111
    0x70503010c022a03030307050f04050409080a0f2f030702040f0507090f05031c021e0f0c27070c0828210509070803040f091d061504270303 61
    0x1008242d00702074440003c6501580200081120385002390054182030400d0030940e03203015164404a803d8075514141141d548101041221146802207034486c501c6000d8a800400312044d5605d4004c0d5052032210441400c40046008a52003c14001c40314403680241c402c0c000c0901c100d00d00c000410b000c84840c000920150008219400c0705c0340084103c48000700208443da0503100c0c407030041201452800c040d8816400300c035103005440801540c00c4811070b80900700c680010340d0345c1414003070404055882007400240d94004a80743c0c070403e9000c0d803106201c003a103d0f039488005071103000c007040014090060208800041144032141c0e900c80242100820040b26038180c02903403186013240c8440107081c00288401d0341c2850381c2e03000b107504c52086001c50b140d03982d40d50242030650b4443c0e000351142d0b00060806006081c0e082c0210074102400e41c8060741428a004140b944480000c1c011a0084002c1e81c90f280c0c4541d01c1c1c2d0081d401e403055180380d03070607856148944580090784100303044011030b061 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 988390602 1250 988389352 988389403
    0x41e0606021908030a090b040c080d0f050d090f0f0f12031a040911041103100b090a0e0a11040603050604110c07121505070207060314010b1b070503010c02 68
    0xb0036060040607110345103503540503050303440c0015600000d002c80c0c80d10360707158400780200c0c2901003a903000e01e015140b80500d9030f0500380c00604080f1112040130611040000c507041d001e6102e4100d640440d2881c00000b101d007007902d072403481038441a401411085024112005004a46285e210500d2240c0200880340f5551181030707003541c52401c04444c400d40012503082e103d0030300390810102c0b240b107025a1030881300060b002078219440c104a10310010380120401007841c0400d01c405003e00a11401039007401d5042c4005440da0405001d40401c545001011601c005400d402890045c10380048054403240c0b41c2100070010720302100c20f40d00c140d040c00400d110303403040d040c2161003528400000c0c1617854142a040c9800d0850350f9811079034007164240b03c0c40d200229200d4503001e9100e550180c020140341c14002021340d06126000022040c4c81c400421030209c0f500b0481d03210100c00e08410b0001d11005d0a400d043c043d032503112981650030000b41c50b03030039640424204a842d030031880c1c1c0c805010320b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 988391852 1250 988390602 988390607
    0x1704052d0d140301090f0e01020d021b0c1f020c0d1208100e0631061706100510020c0d26041a0f04031b151805040e0102040302041e0606 60
    0x2d44001803101c0800030001071000101c0c68000241101c50f4201c0840c40a0515034013a0032a40030801502c1120303030101e035070340e0a8601850070800c4152507100514807005244e00040701581007142d00c4501d5240b02804c0300c86036009000a0b401e5480041802e0102c1106061044031ba03035400c410817001840400005424030020340320301d8160b401e00c81c5003800740d03515074007031001c0400003140807601d500140400700240000c10810100343d0452071000b040140c40c20600c402012807500460f182c6030015410000c01070118101d001c100c2c0c40480391076403680d82d441010ba00f0543d401e080c10f0f401c0a510850903003840600388c55003200051020500c290000d850341481c1c114000d5000d002181c0c0c185022108051901002800e10242104209440c1c650b6950342d0303100c0c035814079503907188010451004008941c0c0c0c22000030441c00c80360030a130185804c80840070140c118140602c0348600d603205003000300150250f054030081e40e8040c208208a00c011858400000e400d880400511401c10401048091 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 988393102 1250 988391852 988391867
    0x190b0406030e0f0c130902090103050c1203071104090809041b0e0a030305070204020f04051002010e0d05030403080630010b0a0f080307030c020d02062106101704052d0d 74
    0x1039243d0040e014048001c01002420450303042007208080d250b44907000541e40b4118998002d51060008011600c0f20400748030a08000d82c0f0030150b190024481107001c02c80c0a51104130840b02201c00142c41590340c9050100c178020300181640262070040386102c800041e1009040b22040c50711f410a00030f045100b0008101c001d4000100001c1003030140000505140e00541550340c101c1c41d1080c01c0036102d034082500300183c040f0580040c0e4440d241440f800302d050080c964601418034140b0b143d40b50545000d002c24002510700390264894000036900300860340a0f040c6101c3d407210b943d003030250401018034060041c102c041440f424148500141c402c1e00c03082e2046c01c0707a0555018506180f0242c4007560002c01c404c6080e6002080c40c480003006a0781c2c580102640e442c034002c101d40028030b08003040403c40e0b0040c04640200d441b2612030003100d410041900d1050180310906590b96600d2070501e042610f1051078185000307112009801c0c89400461007175580460320129602e810074003004031043c0c1c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 988394352 1250 988393102 988393123
    0x70c061e0f240810050a061203051c0b0d02060904320f041703100b030709290f070201020a0507030323030106050912010e2d010e06060906190b0406030e 67
    0x2907206800045000c130080e04813651100300480c0004105545030100262030011110460000310005120400d000080103030200e110010042007024840c02000700744110102180a4820700c80440d1031501a51560001444030200c0780c034a0650404594441d0141c02c164283c3c4c207044160080050102c02c010780ca4240f10750f4201c2040500d20044203020051940003620241500c180c082d00030811a103408001c1d0701030f01c0366550700000a8900040302508000040c0c0c1c0840449625070000500e01d1990143d9400c52103400c24030781c0e10042440180e213031010110004050340281708000003896040641d01110f1440a0031a54a403501a40078030072070b00c0b0074002d50300820707000d03c0b0b001454142804501c01c03000019000140181060079024601118602c20003800c00305d034490343c040700d0135483c0e42080300122840281b114040140d00e90f03440e0540145850b014913860000500c0d20340e51210014090381700d84039404e580c03603251480400c036035215010b05c4000c039041c840e00b408080c0340058000d009 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 988395602 1250 988394352 988394369
    0x20c060a0e0105070b010602070e09031806030a020d060b1e0c0706050a2001090203190b181c020d08060d020603040311010e011107150203070c061e0f24 67
    0x20404002001d484192285854504010b81880307030100082e03d120005000e005541c004000c1d0b28075009003007142040040601c03e0b175400c02c1c03018001b003000c901da074000d20b91421580303181c980c0c1d42d40c004407002f40a40261600030380e0811000080d010406802421001c990400236245848840d600c5100d0740310f103c0090403190f009a508000d020310520261451140d00e00d0440458a08407201014180d08400001206e96480000d14210f180801400405d40040680001c5a40c0b034bd4a03020003101e0014010610500b4018020011002c1072007004600f0600091400588c0740007040299681d004130515004036001001241c40d83c5020702c1d4900c10294010601b078950390b5590b41c210b40160100d200079035150349604600078042400e01070080f4010345903008540b15212810004e0b1804c46003218149030034410000d004d021648080c04194050f00400085070408101c441916000075100d8061141c91800800b0303607032901076802c01038a0141c0140c0b1031030380000c4d4100d4540b003448a0b2252540 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 988396852 1250 988395602 988395607
    0xf050d050403200f040c0819060b0a200d0f1b0210120b0405090309040f020405010f0f170f04060b03070b0307032c06100f03020d020d1104110c0c01020c06 68
    0x211861481d02501200b41c040c00090310004c03950081002c0c0c8134944c000c1c00200d0225010040004000440280800340344002804100e1070451251158440e1604135410020300b40c01031000b0414030031084044091020455850502d51480280802039090040001806044401e00524a82041001d1369a0000d00700480219452025152201c0703070410301840c20303260040c02c08075584511405101e200302d440a03554031452001000102c0e100b2030340884070507205000501003a40c1c00b000c010210920381c1003408c001e4a46038025601400c1c08115042e480504808020700ca1089580701c81c0101c0c4500003c1c0110100741c41015121002030041c106005c6045c00003502092080d045207085440b40c0194000c0102c1c02c61410090860411046945902107414082c5c140c0c00c060103100104040700517030120314110382c002898010744500103482503982e0010442480070001da60b55000d10001c004211011000551a81603000000340403050301840c1300c4100300b94004a10600c1140780144a9803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 988398102 1250 988396852 988396883
    0x30308010509070c1527060617060f040201110a1520090102100518030d0504030206090d0804020409150c020109260f03070917101a030a110f0a030f050d050403 70
    0x900600c0b030840024102c44282e40c04000c41b50401c0550075041d405800b002c5022070801d5084852581060111040b5034130070720400ca142c900e80c02c851b98200e542440c1c4070507803502c0d036803241e841c0030301c0f90381c01800d402c405000b00d0b0216849a440106501040c0b00c8155014021070640462801b511065901503046402e0340072002040f0303440705074400c111144d400c20030000000c0b2607142d5000720041c004401d6440041c40306051b010482580c1c406107000050140704c070720a000400d08000540000e015a86810501c003c00c41c0d0040f800c21200c0d803c81040020f190040c00080c0600b07002d0030191180d800350100300c0442d1104100010800e4806950303d45480c0c030f51024044164002003030340040020308000458842110a09101e001204000415141403200f01e98003c039210482c401c121501000441021a240482c1491705980c00052110320030704444042032424100030074490b0b10581500001c4200f03c0c100f292240f01e035000d00100d0705110481c031015034003889603010251481d4900006034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 988399352 1250 988398102 988398143
    0xa150b100302190f18030501020711060c0a080d021b061905060a120f0503040f0911032205070509070306031403030106020c0907022803030b090c03130305070c030308010509070c 78
    0x1131102c01241c6003445442080c1c4001e031600500b0b40d0021a05650001821b0303040c45484004644a80c0f0200c4c6c041d444c08100c11001590340346032200c014000c00020811000c2650b180d819541611000c000221603000200c00030b03a113490049500f00e4100307004c14002c40c0c150304c55100d503911034100500a8044103040624403910041010412144000c1c0040b41c40001281400508010324440310900c034860304003050482522500e12422601c0300c0240200000b0f80403410079055020000140100c00c1c0c28182481410000d06800c12a04803903000705001070141d05521080c101c078084d4440d5000d070018000042e44920017849071000503807007115164080d145c9500301d690070560740d004890800303060810b00a0314201100d11030701c04503020f10941c5d05040e0140540c5202d030404407001c500c0d03840e203040341426900001e0801d941b4118180b40c10400c08d4051000c4841994000c0c40c14003441c2d41d2450010250182400b40e940202d201d1404114030900860309400048d5009809900300140e14000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 988400602 1250 988399352 988399367
    0xe040c170c1c020d1d060f1506190e010f0e0a0608092a01030b030c0d060e030c0303090a0606080601030807080a1e1821020405090a150b10030219 64
    0x103004500110488440050385a8402048640d030344003c04108826003042c1c0c810035208505d07109443d9000f58040200c03802a01c4030450f4800860030380b0019288100000c2001405003802a25032103040360303007220a154101e4a140d0b003000742681d0b60b14a101042e83c0407241c1104c1c0d40040c1da040315200c01c06104650003031121541c0b0840f040c08035803d10191101c5581c00450130031a42440d08881806003e031940d042c0a00100c410050b070040060180f00801309820007400c1170b0151039140d5442c00300f00c000b1014030489008440910440e40c032410001540758440c08403120403104e1034504003000514400c0481c07028101c036000180c1e2410b28140380c990f20140d500050a800421024a00313002c1d40403505d02d40d0f0038445c042550340c0020f03140c45c0100300b411011540c10a02407160860003e8201c4401030f00002003203a410384d4045034540726001c985191000240e402440f580c0c4201d0304080c03072003069000c0081e8020031142035500040d00c6000350120310070140c520140010303030402c000704d641c001d500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 988401852 1250 988400602 988400617
    0xf140108010902160f080a0306090e100903020723030c03010c0807050d18031805010e0303070305160b040b040b071e0305090f03041707091104052209030e040c170c 72
    0x2a07401001c1139a9a403c2010403d8020443d503469010400c030a05690600c0b45c81d010300300c2c1c204104600807811440f44c2c3d603410300d40e03480c0e644540c032805000304151080c405400100803c101c00021460317201105d60a8403101c910050080c4207513400c01809103014054210180c0d2552a100b4072a1503122044031a684130051090010f9101e680460002c0c9403e02d04c2c800c964000e60745d4035038011042000e00c036020603030345c0510704100503e500c1700125903020048407141c030740c1420603681c2c034443ca200720007040100035000307449902c4c000200420702400084c1144501c1c8240050310040da100d20b01541d01802d01c405034060b5032106012140300034007a82c0140d410035103540460326206905006a455a40150001001340300c28002d80c04085004018040203008800c01c1403148501c0900f2001550050340703d20352041c2c09030f404285c0ba0000c00c581441000681107030521a041030350030054508581c806e0003a010320300d00350080c1c800c3c601c554680614810152a2003110340c8801520a20b103801081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 988403102 1250 988401852 988401877
    0xd2604080604030309020301051b0d09030e0909011409120f03070309020d0606080c01080f0a05060a08100504020906010815010f05130305070302030f1f2c0105010f140108010902 78
    0x10818080800039948243d229590208070030440f031051500b5983d001d003968900240b641c6407a94140c0864061300c4c40f411007050006102161401c040340c070a2a0448050b802848500c18070903040010f411040c0070030541548500316845001000355603483c42070440204040c14495a130072000f20710000d41c0c00c010141f0300419000080d0300018000400c10504459090351200c1c02c12a5450501801c81c51500034280300700246840d06108240c0100144031040865032030300042c0d010344e0b07107808000c040c020000489000180a03c0140c1c0288070644d8203a01c14074032400010a00d41c07140800a10400f080e501d200d199100c4580152000d40044043c00c060200c107000e01070b0341140408180008601500003021154998018103042800c0b070a064509900300d036104441d8034402c511442600340404000003100400030316001c40724104441c2241d071170301c105601c44000c1801500b245050b2074200c80000074070b036990fa0064040e034852084c102c0c00700740800010841350f05554044c02610f600790303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 988404352 1250 988403102 988403107
    0x9071407060b0a030b071107080102040501200a140d14071104051005120705040f020918090717030a020f01060503190206090d1217010f12020a17010207060b0d26 71
    0x99a0b1101650012100c1b2000103680c0c819425480d0b0003040454000e0260000842c038140c1400f00003001802d41808500b101030081030070760035180c070030000080c110340c00190400202c0030310180183c0703448078070244000080c601480365128032a11401c452540382d0003245100414100410b10001e030500a000d40c1d403096803840b000529484500c140541501080054a00c4508001c1048121800345900d003055501c10700c0840314079140d52840e40b401051840c0058120f03a00d8120103468001150802d0004080c0c111020950910000c098190585a9003c0c0c4103c0702c11150254202c48017803142c0742d8507901054000c0c074000412442590140c0c000b42c4400e1400e544080401c4850b00365020440705c1011000b14401c003a54405041c418001d0601e10b03c074495450b0420211200515014049881200b0400d8004559030280d0b10740c028028421003c04d242c0620f68414000e40000d101030320b08038103003d82103d1900d0072800d02096540c0c400c2000c08010511200e1400c0e411410069040800c402c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 988405602 1250 988404352 988404359
    0x9130605180316020109090b0105040b1b010f0c0f1107060e010c0203070e07020d0c0512311806080601091832060f0406050c130803030609071407060b0a 67
    0x80c402440b8180e0388030f01c078560070102480010b0680c1082e600c5070440303d01e0449101d0003680d00c03404840131241c1c00d200c1c441e1030b12061030008500490402180210350700e043c025802c1e103400360f0411203442600381c0304c112444849071004e540c0901c0010021040783c02c0100240032103800b450000310062018940341a10700403690201e4605400c0d83c1080a600c6888801c124503194108421000e1040350b00e010b0710b03c40c086588299840701c2c3e204290365a480042180398982070a460140859000000d14400c1c01020f205101d170521014091050400100c00104c444010140143c6080b1541040200302d507a1912003600b0040c51003d458191042c0400e01c0000814801000002d46026041040d90160000c40d0304103440141600c0607001c50300000708000c104500c0c1c504141d406038001c2000f140d00c0e50749084011042c4124031518002c4c044003000031414010000c0078520410041d2144d800316203851200b5907a03a8104c00261424680410540300091140e40040e045031a020b000020322a40303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 988406852 1250 988405602 988405651
    0x816020c130f0b0102030a0e101209122a1e05061f061b0b1b0406090504110c1b06041a0c010b04050114040e030c0619050609130605 58
    0x86200e080055180e07040c0b1018031026229400424400340020340c94064101c1c1e01500540403154001e10503103c00b90200821809007168890110301c1350000c0181c969586014001404101022400a0031400300f10002e009c4501c81c0e0120050017082524808030300e42c0c0d42d240d083c00074605902c80008919502070009204005060044242840c005504504c00d40826a16a281d07440324040002810140c605180782c00d91041c10b039034001030031014640d41c0b602e000c030001d4a207078840955403400250000350070390300012203015030300c00316424480300c0d80414002d2810300910140039000c0d0403c2808892401c05d000395040d1140c000b800d040e08003641c8181141100302c110b0b60340400c2c081d0000750410f0b001000e104d2102d800c40101c60400180d4100b824800c940340000d51520300581d6240c40300900c00c80c040060b603540c01e4141c4101c0f4918070b801d0703540b90954032040030501c0200e0b0508001c0b500c0e0b0310380341c4103491007141c406454005401c0c0d9503ea2101910002d820380c101c0c095006400c0e1154107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 988408102 1250 988406852 988406869
    0x4020402071406010e0c03070503070810230a09020306032a090a0506030d03050f16030b0603010b1308030c060606070f050a080310060905030c15040b0706140603030a0816020c 77
    0x142c90161206614010700e00600d13090041010300c0c074440400800415031f03080000d032a04401d451a08444561301d01c0c0740c030445540107070050700180400010003401184400c07075114841900359000613103203540b003210701e0036808243c42d81c84d45070b0000944100c19001300e0021440c4509002c0450580b000000f01140700000c00b42c4500310701d20740740d50030800a13060400c07000d543c680c0145401c004c0d91030108080c4000f800e01401c0521404030a0744a410528481e410402003050024840769480d45e407050181e0781e5610204024411008501001851400203c26a44524a01d81c05850144c1c3c9000030840785611a11045960012071941400829002c01c17900088921480f1120341c0c0e4240008418959240b0380d004008020102000307000381c4e1804074450003074800694500f010003a54020b202c1e058000c0b90040d00c090040071810b04244a11504150004c074885101c0824649840017031580320b11a29907801d000c91484004030f10307020114803115288410602c10342d01902c0c2214001141c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 988409352 1250 988408102 988408133
    0x406050a090905131a0717070e03031c11070b0604050402060d1b03050901060602070e090a0b07050a14070f020904110a060203120108010c080106081906060201150801060605040e0402040207 83
    0x2078075106580c10030030482ca188520409240c4860fa1240d01d811b00009004200264041508088450215140b540100084165000020b05483c0c40c1d203120204d0400320303004d025110401c10705141110556900d000c048840058101d1407211090351880184006040040d004a800490401c101c0b6100300862003013181d07281c13050190000c00010040c0083c1640e8020f040100360340d2410608101a50700002c00b842107941130743c3e0401465481c028800e0070200b8103003000d445030990004220a0300e0307001006000c03010483e1100c0703020f01e030f4026046080340505100281010b000081d000094541a0b52359580944604c514043c204044800300310342001c0b036070080c0c0160b400403c112052840a8010a01405184000b00705100f6082c20081c4205c4041c443c04040c020030002081030b2241c6843c40300420f03034030300f502840031641e1050000d008100e5003815058a070b100328808220140107028002c00c40e4441c0c4d0744c2c030f41014103103c07407481400009002240d1041d8200864030024082c035540c1c031500c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 988410602 1250 988409352 988409371
    0x11030a0c0e070306141309050a02040c0f0206130b0601030f0603050102130f08030906090d0510091a09070810020c070e040c0305070e06031209010c1a07090b0408030406050a090905 79
    0x181002e00c4082c040e40d455800050003080d8603c0500c0c00c0b501c0340c0c1410b044040400c070010484a0700390402e941070441044021b5006030410070103008094000300302e89402c40d05a0700f221601da440c05400d030180044542d00406155120001c10055803080c0c0001e0710808000c4400101c2d01c0c1e80c2d94a80e400c99200000010302c08101c04020044010031000000040c100040954640880c90b40080c4891003080c000d94410350502070280c0034401c0c108030548034500f020404110402003820300c0c00700f03510f900ba05e806041d012000000c29403900800e00b1400c99030350100501b4090740001c0200c01a400c040340792511846400341c00503212101d10582d500a0b0b004400b0400d070f550035820554107045094001045815201c8140b0006850000b00303014a140c9034407040e43c440842e440101c814500303a14001d02081c41d0f240028688407042c1001f00c0c05078800352a032011559035000c039480380e0702661261021a8109120070800d80d0b0240d0020010030380c4610701055002c1e15039444600304e51041c0e070240807 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 988411852 1250 988410602 988410629
    0x3062705011b030b03060609130507141e010e12010f142a040b131211030c0a0303090b0a030204080601080a02030c01090b091207080d020a1101050304030c11030a0c 72
    0xa0b408090780c1e0390341081c4128038080c040710301560040303542d5560141c100d80c01074000301c0009207001c1c0645824024164000c00340c500c0d1aa031580084071204d0002d00441c410707180d040c095010031000c00c00058000c4410384070360101c0b410b05007c01105079000d5402c440503540b103c642c0c0d04480c031507216035a9105e41403c080c6020341000102c20b0961a0010300c407030302c4410506101800c602010065804072540e11030705554031800070a100d000109030340d00040d4112240c030050301c00c002c80340c041222414002d8007150b5514440c601003040c45000b5200140100e1070b0300c1028007034400c01e40010440c0c050141030161405955000e403a2500c00300743e00c040e40d160081140401185018065aa0540400d1a05020742402d00c0c0703000c206407290590f4548105029040d40b070001c3c00503c150b40003004400c0c00e0f600d010010b010040d44625a40b0740c115040050070042e40d0702503020b075040e640181e4160307030785412050b8190341d91303001c8110001c43e1076450700c034256818000544801c2890701600c0d892503400c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 988413102 1250 988411852 988411871
    0x1011030d052a120702071d04110a0f0e06060712210203150f01120606030e0c0402040614071a0a0207060b04110a21050406090b010611070306270501 65
    0x6620101d4440c680040c80d88002110b00351210040640c0c4040308965502c020540302c081040e4500880c6501c8403d035081d100700d48403010104030101c2842503001c0c0103400e81c0740d44a01c2c10041c2c0090540581081290044000e010340f4210300b08550340f003c0080c0c022483c000d05521454901c410040c15200000c841401104021034070b582130309040840404198110b041c1003142059100001c14000c2c0504c00f00e408001c0e0300c2c3c0c40380300200d0f414080000104155034403443e0040c0540301a408580c481c0c072039422215028245442103c0441e40503584200c028401888054078552145106a8003801620000c1c560b54038045002402866800c50040e550119864068140c50341d411400d82b04506d03200a6201d113112800032250794110620700b812a140044042c1c03202c28079201c680070b42442c80e1008000400c00c46903c0b05c140d0301c1c01451500c049a0f40d030700d000c881440e00300c0c1600c001d42d081010200005000d5030416002d0203406c21041814421242e8000310b500803000040c0c44c142e440c1c4d2000b5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 988414352 1250 988413102 988413121
    0xf1f080d3b01170403021905150c04051e0913080c0327011706090a02040b0d0c08060a1d0714070c0f05060405060f0a090b040303020a060b18061011030d05 68
    0x383c2000c150729401507034a003603140030f5111079030610803420000c400001c0c10104030042c0401541000c0c0c5100e9620300341031201c910b0503203820901490307003d17040b1005c40d225003071100e100c0c0d5480d0810007070880382540c2d10b01000c60700c2400d9050003100c80c481c4c10704c02c98828240503c0584031500c0d04010010201040711504059051148d000c0c07414844118120010368640c101802e6003c04103403410f15040d2034514050001344250f40c03000306204000f0401074a1842c950f0406801c1c0d0000b956081205c1e2580303c00c010742c28405100d401c01e00002c0b102c3c4c0050500d0942c0d443c541c44107003820840c00e412104071a040c0c0355442034004690b83c00700800148a2a000d62504101409094903800d003418248004140284201311a04441082c0030a8401900d40310f1a182005042c0307810306a030b182d654916000c1c0d070360401180102d482c6800c2a0400304641007054003e95080b405821a0b0f519444910034030002008501942040011000001011040400040c58078041d45040010180380c01d81d02d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 988415602 1250 988414352 988414367
    0x3090103061409060f1306030507240c03111c0c0203012f0309010b03030a080708150a0b0d110f070c050d050a021e04050f1f080d3b01 59
    0x701d0010402a0071000b90707440d40380e2003550050041da208002c0000560001e0205007482e0888403405081c410088200400803901d40d003141d840c0011807181480689610108600b07104000307000800c0669840e010030303c1800280d10328080041601c0201c00c01d0048081c0d00321201e003211000c110f20100d50400c60809205c0e490043e000e039000d0001c41c81030b140090304084200c44652101010100101c2d00c214400c0d880071558101c02001c0325510b0010f404003408100044802c1c20204002d0b4001990440c260b48050000b00001400d2500301c5007040380c00c103a02d07003041d106e03040c1483d968080050800004402008241c905402480d220342007442e00806881c12034000602480c8100c00e8500001c0002035514001c0758102c556800c88030f24002152020703511240c80c00c2e4030500b00300500c412444080c480c580900340304d600d4490300e0010340d201c2c80d41541007480760311650750098440f060303040d1080c00310500b107094034841d040701483d04110340c0c400704807031b4440301c1c0c105e6140c6180c882c01136800054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 988416852 1250 988415602 988415609
    0x32404090206040501120b1305040309091a01050c030d0f021312151d0604060603020111030313030f0e0d080a1b1205030c0903060f0403020d020304080303191d0309010306 75
    0x20240200800ca0380440d807107010300e1090505100e035801b00003580c008150001000c2c00780c050060101e0642d10b01201c1c01170f08041e501030300400c0b6140008200020700340a05002e064408090070006015103004440941c020401040d00b40002e0180b0b0304188840c3c0900910101c3c902c40258851b002d82d1004103001100c0c1c0d1000454200b101401c000060604031140d80328021814001001010380c031520f00c1002c00047d03540200e0240d01d0401003000141d80c00340003940c0c000c0e40c0b106203282200034801e581e884181d421700c401e070200600340c1e000a8401c2c401c10506103903a1800c509140d50070004a490120b0403001251100800701e600c021240e4000030100c00185592000d680f051410b84403d0700c0c5100c840721100400030f00000094055084004580600d000602100c140e0300c1c1000400f04030b01c00c01e0702c0440c018000d05601040a40c1f00105841c299035203200514915115100384046c55841c611803560902d490341441901503c4020b8401b01a1490201650b6144000c01c0010222407880c2c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 988418102 1250 988416852 988416859
    0x8010c0e012705030312011a0a0c150b0316141f140417030304030e0402030601050d1d0d02070e09032718191a0306040b0c0f0324 57
    0x48844a20380c0c1d004410424019264904100c090780002038107003940e625030807244c0c240c400050030584040900500038100c1e803503602028624041d00c80008024441d640022000951100e0100d021404180207000c44440c0003500158001440012904220100e00e51603401c50300d09100300302850280c01d101117400b0084550300301c003260202000b029050301e200f010040212441c04450300000c81c070225070140030f4810030a4606c020403c0d500c0d40da548110381c1100056014650b40080d410f041c000d0f6406074030140c41b121b041400c0c40880700000c0100503071116401d030a406240601c500140a41c240c0725045502406a603070505084202c58070019102d584954002c10a484400c40c1055100c16452603150424010850750b100066034504400390b107400940a480601c50ba2900000504280b404290000d2140c040b0180b007103800b20301c4007440e103901500004000740010701005810781d8080c0907100c5e02c5040801d10810901181c0040719078200000c812006400001004281c003103034005c00f00d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 988419352 1250 988418102 988418117
    0x50609070e0712021e0705010e0a0c35010504021216061d032a010903081209100e0705012c2209051005060d0c0b03060402120f0108010c 60
    0x18594000000180141d0403c03c40710340303402d0600381c1a012240c45200d0340c0807001d6050075021454905a01ca44001c44171986803071204902414041081405103820180b0b209889140440c3c01c0c046a00c0882c019550a02e505100007140d18040ca01d48490031141d000001d881c40e0030f00c10300451603032200c002e400035031104020500082d222200070003515050b20b0000c14501d42c41e009004040071210300b890741401044c000240320148103140500541c12501c00b1100301c01543e00559100300c1178000034050f080104492040039140c2d6881640100070f080440300c0c1140c82450f550304440481c26140d00f1a08403103010003466900080e10321071503651242451841100200e400c010b035281c8c03188903022760011004007400661000d40914116001c501c144103000043c0740507070300e682900104400c2e00f4546000701e0710342c1c203000307148403151030740f1480f151a4a410003101000701c1e08001c190903802502005100a15100c550009000302c40445114a965051191079401d450503500c7c000e0401840 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 988420602 1250 988419352 988419359
    0x6090f1a0c0711120303040b09121c05040c0302091504060b0906070201080702100c08010f08031c020d090f030e090603280c17030703030b090c22030b090a05060907 72
    0x40c54101c5642c2d5074401003001021030840c012901d81d0f04140c058920740e00011042200348220822000d100d4951603050313895107241c00403440e505008007044c4000880074013031a5501c1245550100b50402d00400c0c0c501d907001d6403940091170707091080300d582e68009000c0c03c0303121443c10540681000740c10364603803881c21710807410080703410341c09001c401070304000600b070100d0b074241e00a01502000c2c12110f45d00f80a008090240030301129428401d00c18400d0103940300003514000481034030711401d44111058801002113140f0f00294210341d842e64807965903034101c1800075400111241441c1d2082d1107600b10305041d0741c100410400c000303112034003c4d004004512004c20b40d400196013a43d117051400b10300f14519041c8200c40c142035030030815682c82c000c04415810400080580060382c440d65045c0554026841070000050065a840c030900e4820b11980408040c90040d909030a090384840c50151a9203444020744901d050f07070303502e049422968101042c4442403141580c050214001003030640d15 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 988421852 1250 988420602 988420621
    0x3020f060304060905100b010908030f0f03071803030f021e030f07051608011e0908090f040b0907050a110c060d050402120105040c060906110607050a030906090f1a 72
    0x140a8102485140000005000c000759a400040c0381508002100d01102c0721000d0140101003903407505011851009001901c460008210740194509031542d0741880415a0764801d9604081c0c046000e010200007038a60b200825103500300298007a44d00e810440d404d0304400707410484c00540c0b2100d46005074604215500b40001110040882d00f41d2155803100c003428294100a802c007131422801810b8140000e200405420607001c0c0f03071640c41503914100f05011004100d038142e11008024280130300615440d454850711700d400745403024101050644804000401440c41140e82602181c4082180300e0425407000036420009010070007080b1340c1d158400040d085018880e82e80e0358141e226400601152101d080462034500094001e1020f1f0501e80f9000600600c180120700014500c071100190b624402c0700f1049401c0310315000380100d42c807a407804590aa100b41c80c0401816210f81200000404910032101d206001e02200b440c59105803400540c402143c09022105800c0c03c02804240039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 988423102 1250 988421852 988421869
    0xa05150606160201051c14070e01020f0a02011d0409030807030501050d03020604080306010c14030304120305150d02012703120e13090f17030a05010e010b07021909020c0d09060206010302 82
    0x2602421716a482c2d0083d00d404180500e16601c1c01c4d035030035080840d2010300990b58811203000342d009848003c046d004800049940700c101050704600d076840000c90b07001550062800c199a050038555000340005c3d00b80c0854151115110200d000800240400146541c9403043c2809403c04941403a01c4d1101c540307000f959010054400b80c10404000041030250b80544410810580d001004d403a082aa9000c065226042180c05545401d03600c0841003186200b485201d1150861400001e0b036244180300740f00841d42c9a510403410f001200e5580015206000303210b0810080209005050358210b2801d210281c16001a91050010340d11000c20250340b0a00c0340c003030080c00b812000402070880d09065804810101000d040b842c82180300480041094000714860300307402600f8441a640c517100c20509510902c074001c0c03902e6041c0031250061605a80a070416500c92a0980c07600d5254071101080b45e000390030b0025154842d02c010151550000c100c10010800f42c0050880c03907142d40c01041c00070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 988424352 1250 988423102 988423147
    0x204022118071701060305011506020106050910170a0b151507110d210905010e030c0f060936090c1507050316080306040b060403170a110a05150606 65
    0x4400300f0790700c80200300c001d40c0200300458000d0300921203090b84544400500300c00e03000710320065083c0400490325003803000311030b40944a100c0c9203c200b2803510180001684501c40514000d00803040c5c1080425480022940141c2052510340c12041c08003040000503c15a2901c02160600380035603030100300101c14860505500752a5028140f000b481d140e150610008881004061904500082107900c030341032000b943c00a0321044000b800780010107940d12040d5000c654455845039060845083c000e000d00346004002e400965140c140c040d07800c841d12820244521030356030b49111090004032a00b6055000a030f19800342c0074104211021035180d60409000010080c000035030181040810030841c1c0d19010000c00641041c5070514141c01203910585105101e01e0502c03008d48060301c0c007042281c040303d41c0320b4100041806d500d18004090b800014070030080c40784d1007815403042002400f000c0c00340c3e03105a0180211900310701401458080181a490207100300348543c4a42502d4420f991050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 988425602 1250 988424352 988424369
    0x103080c1015030f0c0e01062a0f021e090a020a030b12120f0435010e060a09050c03070e040204060603060b22180e0105011e14060403020402211807 65
    0x1100054140056a80241d521686c68240710308000907203240c6c010306045040320703000c00c14804021507031094040041101c00250590846402c2c620051820621501c05148812111703946254658002040e617282154200c003250303000034010315010341c540b2070f444444108542503841c40443d59801a80d030003040e64080c2800700001054030708030401e4802d440049c206503c00b1210010241041015440040e0001d100c900f12140d1034440908103020354003030b1521400040c06a6907c088071480a050b4108080d01c280c000c0c01030905450f1010300100018188800c05405142800c0c0306000072101294032079401c01d840c0180c1030003c0e5100300300308c0d080c28031880d9010b01000000100c0d25110030059028003401c81c81680d41152107010364000f401c07188080c90007009580c1c0c4c1c90004142d10f540101d041444102c50460501500441c0c81503d4010343c0302402d2541031544960106040347d000c1c04441c0c24076900e4200039404582043c003942d6000080d00d5008089118904c9082d41d01d40c8a070051500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 988426852 1250 988425602 988425623
    0xb0a0203160305223e0105180d03050315060f0304060510090509071802120106140408061003020f0f01080a18050a030801210f080a0302120103080c101503 68
    0x11100024000010140d4582074202120340034540140030440402900c52400510311180c40031014910401d11001c0e2032a0b401c5c0340003001a4011501948803c08a400d190042100e4000a0b01c50405020f102d52103600c411340c1c2c0303081c140d60340c540e114604031101c0e201e4142001040d42c1c612011054135002a0b0110012609440d01010920840c2d081c1c0c0242003420f00d08410002c40540c000707078140840d00e003110010a02032301c000c0010140c2c450119501240360101c001004060304c104442060500c280c5266401d1584030280302d800c0010544004281030f100310814000c0d440c0040d00c48922420440e07281900c51103ca0000c1c24081e802001d1303c2c000740d555115030807000700000c032443c003055000003507801c031681c00c1c078010300600420f0050011030601c00d0640d03132035a100c00c6402019942c202e1a01c9048c1c60f420f5a420300340d40d00c08464032007050340a016564042030701c000a94040d5200c2c1c10300c540c65030784c801c2002d840e25000ca83c818004605005450b5069640d11a145040d2a000101c140c3d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 988428102 1250 988426852 988426861
    0x902060c0a030207060e010314040201051b0f0706090801051603180804150f0c0302030f03191505031606051804020c0f0a060b090402010f1125030b0a0203160305 71
    0x50550003001103004031030290707030424000c0690200c0c1000070381c2c180d81c9881520245280c011000c861040b803483e84001018400729000d03602070000703000502040c86415160100c9103044500b84041402d400080303a02007142403040c3e503000400031015288100c000c0020f0301d030030750b01c041d0704002e2104240180342c2e070b450b00da040c080100d5508001540c0c01030002c980c0e5580c0c680c600d94031031015146044c00583d0404411400d503204040c103240190f0194015404d00185251600c050745c00501154000010854104e41c40502800b0781109901034014980c1c801785000141070518071441d40140c40c0c2002140c00f40451500701064031011500440a2035011400310003003002440742080c1020745102d828201001480d0000751092150300c80d10048c0b119088800501007800000d07500217000c2403800050503032041c40f90304e504824100080480c1c20070f100000c2e8010100f03040c2500c00b04410104031040c8240b140d0646529003064824004503c1c61400740044418010040d08140070151108040f6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 988429352 1250 988428102 988428109
    0x10c02010521061809060106210e0303070f0302040b07061d0102030c131401080c070302010b120f060907120330020405120c0907030e030d0501170f07060e01030902 72
    0x944000400c809504079042d400040c0c6010b100702122034034426000e030b00141c414150860b207440c0c004c14140713008001d580d0811405490481552a0301d40d026103100d800c105c0d10400c18001d168401282c58050340d545c2c1008880189404c900c00388603000d05004000c00c2010060711021910a250401070000d41e0141001c2400403040d050613200150398004024000d10312400001445112040001001d089a460700c0324072405003100c040ea8007090011000a03103581000000f0300b40c1d02c0c0300e4800000c501c40c090000641e4000b000c0100070b0f40754482d0a100d61410b0040203116008001c140040c00c0c1d0b02c0c40c0140c02061610402d030b008081001500c0780915030340da00000450600d00e01c0c5100349100c4a108010002504144909489a0b61401c064041c0341c0c80802c05071492140031788040400d994135001074002d040381e9884204288400c021200c52443e1610850303010f04502d00c90100e504031503213119031411013101a04a007581004d80100a9103400100301c201002d0203082c0800c039481c150000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 988430602 1250 988429352 988429357
    0x516050102040803220b090d210503100e01030c0b0f25060b0f0108150303092d06130e06041e1e090507090b06160b01080c10020c010c020105 62
    0x14865800800c02040303002011028010a05036032684050b80c4141ca070341105401918480e21131848010040c2e45410309011224000c40b50060200d0001d2510388007090348060401c15003500000c40101c1408030240800c04540010075420703001c0c002e80d5045440300b20394081c0f28442c07400449800280880d03070080c42810b6a50403c4102510b642c49100301c1d4031034440350704240741120b0313451074205c100c000c500d0900880e103984a41a501c03000540c0da00107030410001603100b2144e90502c0144404000c0340d44180d940c1344400080889418500d405500c0d2520040030a43c0d00c901c01c2e1001c0c0300742c55884440a0101c0300b10359985110034a585c03281c00c0800e0081460400300781d5042c15010b04001a0603081d0030043c50050700040c0e4546903400320018008413188520001c3c081d8114601c20000c0704403d403c03c040d04403004014a26114400542118070007a04008958601c003a5004204041081c00807a148280c00d4612070030401030b041c0001d44511400d4080c81c14800890462010769105009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 988431852 1250 988430602 988430647
    0x504060819060b1009030302011d1f0608190b1302060f0307090b030a140702010606140903030906070b0a0b010e0109060f090807140f0f06090d0305120703020d0b090f010605 76
    0x10014000820030b400401c50051750005601541c00d0a0074030320011404c0c20010f65242000001d0101244c0c07031000c4054100d205010242040e03240c0001096018041c48680c16050340e104041c8d44880e06442c01c5410782c0e41c010f0409800c042d900c81c512026071100c070200e58800004410362070b0303659102c141c2515080741c5c0d0f4001301011680070040218007215948810525510b0403050f0801b507507250002c03402e8a10900401e80028088400c00e1a07072103110380507140310800101641c1c14402501c0200380182c20500c41540e50f5006c002c2481b8400601e441004d84883c000e00c3c0c00100e1403c000d0018007034000c41e105403070410130710007201d0b40180e1181c843d074009020344905a03506180d9900c26201300352006000c1c0d5120382c08214035180a403610342149812054040c26160421481000700980070000c11425018048104140c01c13248041c14a00c500c00c06154900507115810245510201d4101c2210a400b4100c007105000300082c420310b51a0441d10170340b803d9562b50030940c69011016078980b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 988433102 1250 988431852 988431859
    0x1091406030f04140601121b0303020c01052104061e0b061603030f0c03050a0e0c0d12050d0213150c240212160e0a151d090a050708010504060819060b 66
    0x20002c20840c2d0720101c7d0444040c0031f0840600e24081d000800f001010403440001c003d80d014805e405003950042002e804254860910105d003d804014800e91040e02214201c80f580e603640d80100d48a401c1862000558011580800c0100007060114100c0e114003100410140320003600c040802d88281c214100303065410800344614550100c02801425054605a0b601410544641e00d1404006680d181a50000f481008080581c1d00c9600701c0124004c03d1004021040041c07504285090000301482600000080d102615105d0110050702d0420302e040104210b0405880204130b000c9420720088001d04194a09000c409800100920600c844c0a08128156081241c502c070303003c0b240c03601d814007034503200d450714404010030501c1c54031030107140000e80f810000e90050074810070f80c3c1101607809800140c0c0540c0c0480003d1111603046442000c255254000c10412a83c800507440c01480709031002d005443c1082103468540102843c0000750b000708021520030b100180d00280b40c0444040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 988434352 1250 988433102 988433113
    0x20d021314062b0209040201140301080d1701120209090c0409060b03010506040203090d030c090302150a02010b0102070609032405010b040e090d2001061503060501091406030f0414 79
    0xd00c60410091411140e181c4150000708003079040850044070221580c0c0d103043d030400c030f050f183d50030002c1d07002002d0800e038100486244c01980c500ca44100840c042d0900d00014800c40a188200510b8403c50081b810762002904004209031444d41c1c82c803003100b076412114400165110b801c0039140a036600d0f0019481400d12544c0c1c0705000c110741c40402c032800c0030380c000d00440d55900180400d900c02601d802600b0b501001c070091a29102c0d600400d180305061800210840c1d0b207800280444420b900c81c1014180001030020303940e0780910502000700d4082c0094101e030340c640603000c1d00e20422440040e18a00364604210b034110200000e5010740c519000c0100010358544105900e142c06c18003c9040c01c54108021070b84100c400502c00054135074640d24040315800202645c90f110402241c100182d40d21417001052080480120501410040d500094400c0c03404e4001030424078107130b00c12021031540341580c002c2c0f900c1d2101240c1d4868425840c1c25a591142e00e0616061042140d070600c0a0284 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 988435602 1250 988434352 988434371
    0x7140901050d0b060d0902122b03021e0408010c0809071401020304030609140712020d03030b0f03070824010803030f04020a0305030406021e060f0f061206010b030610090b0403020d0213 81
    0x1071b406100664029074070754444201c0381988a544103400401400d8100035800c1130451310003a8040140e1030a094038016051016042c0030261b83c081041064070007580201c0c09000d0540244070750080c03400300d454a160f441c1400c0b080301d0b8407004103010310010b40301441c42c1c0703943d00d034020801c03030b001554410300c00c001c01001410903008044c0362001c01d40190142a100280d4012856103c07104c05800400080280545503416002801008890380e0881c80403129030341142d03014005ca4008121080250207281e006030304640504046800042e0000710b5000140000413001013078a60041d5036007441541078480c0e000148880c110340d800141540710000f07011406542c0859902c241d4008071380400c111411008900703884050407281140e400c40000000344862110003481900043d02604c10403085500071042030500340b098104001030348000090050605049280100d002041d02c0c1890015040002c510b03190f214610020b80301c1c45845401e00159611b0740c0350024103180044080040445 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 988436852 1250 988435602 988435627
    0x160f08040e011527050405040b0405012702040b0a080f010209031e030313020415062610033305060a0608010510032703110607140901050d0b06 63
    0x12601036160300d01481c0300006202d49003c20319808106068452045499505000040c0040c90019000da0341e21100000a6161110303c5854022802000c92070400c1c43c050525a084d200445603482829100e021418001c1200300c0791405643ea041342c0c040f40c0200784000040100006400c505018091070008980001e015801410042415030590f0400422101e03d182c5904e00c160f40360342c1c190002c00c0001c0d00032510701a40110903200500c00680004441d011315280a910340050740424a95291744415400020900d00e00342c1004204025920701141c8241d03030101103110081030f031540d03148080b0071034400c1110307020844880b0b250140042072503810740f00a4502610440d00440743c81c1000300d4002d1148901d90305850000d04150103102420004030b00405507010482140816880031041504080300c2d0103001074000d81e240c00c903050044410700e04100c80601454240140400c01001228000d010b80da82070009003071240e2210481096076000c0c20344002c200e9408480051280c80014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 988438102 1250 988436852 988436857
    0x10030b10030506070207030804140102100614011d0319030309152304081602010905030a06022808130201021015091d0c1c0f060f0c02010207030c0602160f08 69
    0x2e0085086a8940c1c0340e00c10140e80b42c4085020181c058003042000b800207401100b20000e80d110180304076032200030303007a9280c0304940f20350b041040d40008080314280150b0703201400e00c0c25050740078081164815580e001a50390103003c00840150481c1460020905000341d100c4000c09401940448601c8800f0a24a00034092443c2900c0740160b24050740940d031410084052040c1d60044481d440c001070016005d52180b0483d50881c1004086040440c080d00c05202d0b43c0d140611404001d6210b401e000651603504c410000706034041d010390307d003081c803d80d801070405400802c09040000b030070100e0300040781444501c035030110919003400c803035400701d41666014100703c07445544104500b038154103041c85034004800301349810364851402ea80c01c901e8082c0710920344400140c00011400442e54a04150842c0f8503010f5a0442d5a083e003040d0a40c46801201009021403008514249155602030600100e0840140a195000ca0600503d00f504602c698501d5003102500c0d119090a19000c1ca055 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 988439352 1250 988438102 988438109
    0x9030d061e06050a020a0201110f07080c10051309021b010c080901050c310317130509060d170412050c310203071704110307060810050910030b10 64
    0x200c40d2640300081e5103102d0003c1d9000c41310264090241c0d0340f17007a00110781300042e84034000e425004141c140c66440404003c60401041100042e0424445200410a4200e12807124500f8040100002441324134140000416034030400303401030703c82040741d0100420b2a10b107510400158640610703070340056004201c6500c40c58000c00203120030380c0c5000c04500701d40111000c611102200c21340030540400c02e080d00c500c041c480d07109100c0e1074a5480d00c4600e0101c000d20b0621081444c0011407200c00301e00c2005070400303090243e078484520b08005001c9140e41e90a100054405120b410486140022003000c0f98024682081c0d40d03541c0c110f99041c2242c8903820603040c1845141a000340380c00c461144401c3c80c1d1700d8403020802d2400c0070501111800603600c001c000350208850111400c07090342c81d400050740518050040004454130031403d140c030780765540d0080c07410f0065030401c000a00c1030000781075090340c0c4140e80a09040c0c4801d04448400101d54000030315041c004000c10003080200d40c0040c04a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 988440602 1250 988439352 988439399
    0x3050a020415050310090204140f13050f010807080601030b0c0d0e0607120b0a05010912030219030509130e03040b0d14070314010e0103110d1b0b04090606030e1509030d06 75
    0x106942c43d48100b0407881180304aa24121107040541c0c2149824112062032b804090b00c800d0340705609084400c03c940c022200241d02d0080f500051000110410064001e0103400000f014954150780794260192001460180c4030000007a1041d4030b28600d41050240703130b007060200ca62500707044c01301614a500e100901c20411345800c400040c070740740030b0b82c0501c03c80e20180c545010706420f00c5203c1d0090900d10303030141d0940c440c030140e20000b8448499035904c118082e90f5850b8407852170f1010420f001003842a0305113503e0030040c4c0340c1100f80b0040210303800c03a007060304030942d6002c007481140d000e0309802e41c440000041c3d44c010411601e8242d000b004a010f9030050303110083c1e8032000300020100f402c0c000640200e00500e00e440312410b18000d400c22181c001d41d080262802900c85100c8078040c1c07500b0141c5441c0c0e010070200502400c9020f042c002c5c00c5d01f400c0034842141c40c503448650b6002c401c40c041201a06d10380106050404c180b08a500034511180280324298884001901d04400d40041205 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 988441852 1250 988440602 988440631
    0x507051b1617120715020f040f2402030703090b1b03160615030f0201200d120f0b15030a0b19050a0608010b070f020121050a15080d03050a0204150503 66
    0x12440f401c8000c80351000c0c0d110302141901142c2d912000000e402202c4907111030682000082880381d1103170388100003403a00084007000d416940c101d07081a040103090308015940140440700003e9000004542550b0344003406030b4659860000c03511003c02c1381042c0a00d50300000400180180c0a012640007444c0101d005000040803e110380148103100c5c072014000b28600382490005620840c2c1e01080b80e0b401f00300039811580c0081049007400e03c10380002e000300d10204140314040e05180034060610f01400340c10800c44800d000480e42150f1a025030202c807840020006030030507800d5120441d10a009020507070580d043d070080d16403210b6036025a6104203011440019094030807584107060311103401c3d699062043c5a035a15142e44881401241404000700e00704ea2000c02034103a5071101c641480f800308060a09044690803070f1012810710819a1071507a0601001f200041c61001c00b9415180008132960340e0b003a19002801a070b0403a802816284910a080590101c040c501a01081090a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 988443102 1250 988441852 988441873
    0x70f020f03030705150703060306021206090a1a0906030703170403030305100b040915090507120b1804030828020a180f06050705010f020309030705100507051b1617 72
    0x1030340d0f402910402080e6a01c16664030a06145940c04540c11500764100820101c2e1259038240c2a40c10240300039070b0016501c4108011894070090342d07504400032900c1008550b240705040c40c80c511100c4900750040090201140b141e445c00c014007001580c00040440b82e1420090900059130701500c010340009003480082070301108181d104100315002042182d19040c54402d102c4042c0015010110b5030a058003c0040c3c2040c4501545100340c50769500c440036908901c0c000c100721801920741600640191082d10440042081c0711a00b094140c203000b400b0b540d4400e0007003003402089201e140c0d151911060b503400c050342a00a0040820303c0d885008a8981081482d00c20203910300c1007081680030380030b081080e140110024070fa5607004100125006000044034070503030f8000d5a00080f00d82c03002808800340f01c410f1022202da40c080744018840303800c04840082c00e900400c0300441180505514000040c1000c0001c55400000600b620041c16607504941880b001800741840c05409843c00c1da1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 988444352 1250 988443102 988443109
    0xb06130c0c14031201060905040c020a050a141204030302010b10030b030606060c030c070b04090b09100e280b0108150607260403060b010e0915090714070f020f 70
    0x90940803019034944081414584502c0001e081ea5200c035400d50004102412012038070075682800b0309071688032140300ba07107840144022180325568540841d0420a07140000032408a0040211500090040004000350401c94100500c03600400c2451000090003c2090f80641003040040b2048500b0120545a2403041c0cbc00d03120313000b50070b0390705821000008004e8600a005010ba0103401c00483e4240795030030302114a0140b881e005110340317041c0420100282d6105014003c1c0c0c407441a1104031590400d42101801540c05000d00d440641c03156000411640c424000318580c44c030f80c002520f500c012056100e84c01820401007013800240c002001480c01d2039044001503000070007420039490407541317441d0030f20780c5003d0030711540305040b0042460040b083c403071016001540c0504000908540c003000090000252421854001c4070424204251000c1103400075a00b4942500c0074001980d400070112006001300d0425415100301013400d005001d01c9460b0b0000f114402d903190020b0b20b904a081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 988445602 1250 988444352 988444361
    0xc09050a0c081305030c0f07030501052a0a050d1812210504020f0d03020610270f0b1c020307050415060f110109080307180b0915160b0613 61
    0x720000310710404049084824940441d40308607000d101a01d0034841e100039000e003414644108901c0070341c405c4c0018001e0080a1151580142c40d204407105403911240c4085140c40c000c004880040d007020400c007200354014401c60b5410f041c518010888103400711a405c03c02c06902d9000e07204e10034007038990540980a0322085200d030900024423140400c0006d4800d0203800e000300201e0b0004440b02c00d01000d0780360311203078405161007500174208918042540d03000f51481e81d4050703081070654564644490014110322540c02d0f642d0030000c100076040340f1022001d8124010b4a9030061102c0007008030100480740414102c52080301030fa120260f43d041008150342c213000340a81000a1040100450350203040c00344500d48190406a5040d80701042c12421603a140f042652203590010412403519030180d0b81c0d1081290301240100507604029202c082c6006815003580034400040d00e44c0300c040d5003071099416401c0442101c010306903071468000ea4014055039424019144400c10341c410f01454040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 988446852 1250 988445602 988445621
    0x1030201020c150702030109050624060406122a0f170f040c120602120c0c07290c161a03040b3c1e0f0618040c09050a 52
    0x2842514010000c000c1410016942030103044810050000186c83c20300811041d2802400501411703e0140d40c0145d6030081c02c1080c005c2026848221030442d030300c0009880c15100d580c50180803070b0181c3d801c44402001e2605601c110407100c5090043c1004480004c1501d801142d96080e00c2240d6504050303421411400314200308070340d08400905000101e514040d8010700500c0160062540c40841c4401c405001005907940c640019084207401d81c00b14450b0b0b00140f9424141c3d03e008500c0800f5a100c03c0c0901410310040402c5090341d4180c0c2030600d0300c212200f05c04a00642d00c2e0b0700841ca0304d076100500c0120780004d0810706000241c1c514002044001c041c030260340c0f245103070303641d07a00c40488401c010840c110000009849581c20801c04daa50301d00d03250071030040010710028074812400c03200014102803602e881105034044410b1a685081c4d00035081e560f9103551500c07040700140602e01a0030a81c0d07940c01c061800c00c010300001100100488802070300402954a6410102d000d4680410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 988448102 1250 988446852 988446857
    0xf1b03020a0602012f070209040b0a0c11030a0c1704060302042315030c0403060204080d020c091e090304091e060504090c0e060a05090a060812030103030c02090912030106030f0b010801030201 84
    0xc1703880000741c0401441c2d9a1601c403030382002c0c0fa0501503030024603046070a417000e0740c44104c0d2004001d41a810362103496000d190a060840c8601849000c1d1581d03441494078440c10804405601c50411600385941001f82922451f61601e827511814001c0080d001445010039420001c0922150310400c1c444d2001b04690240c500c05090201043d00441d0b58009000806030400401001010588030700c0544094003041c000b42800e9003044600a10704410b4040040c170602402c02408440405964621505502c3d00042041692140e4801d404c0d07009641c0700a11303203070504504103940c2ca00031003030758505140040100065501c4409000450300e107004001c0241620000610040c0c078408070456010308002c094114068036174000c03451300d20342075910300519a180d4106000704442840030118101d0801905811585141c6005200c0b020b00707074000e4010301c1040c02154170004213101c407950305d001550141c2e641e942c3d41c01c0b0090060126091080e40c261603c80d042407a036104085c124100da4050f03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 988449352 1250 988448102 988448141
    0xe041d0c01050c0c03010f020a02010e060c0d090303090f0309050109080f0304030b06031009080904110f0a050a1209030f110d14030601050c060903090901050603010608130f1b03020a060201 83
    0xe0006496580c44400d030110030740b082400c80491070b40d090007026800884060701503100d01c4080c002130700791940f00b5030344070482c1c02520800c48004a50400d8518100c001c4001140340000d07804c2c1900103041100001d00700c1c82d00e08032a04141500081c298044900030790b9040c0010b13944d000d016444540204848020b5002004104003241800448581020f801000d49001e4800002000304540c0407000440b410074010a03c0c2038140341a02c507840349549880c00540c508001700100706c00328494800002c06110006c40c94843c5540f1803801300c2c40c0b00107581010044074070b4604016003010051103000c40099502040341441c5080490802c05003811902c52080d020300e40c1c10041d595420041c502410000e0038002d2000d40300041103542d000707000030340282d03035650312000c20300c85911016042140a014200010480c883c0e00111082d4040484c085109600d105481c0007101e01100000c0680780c0300b071035030441403030000440019045a2085442045c21903943c0c3c800e80c241d0b00d21180415980804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 988450602 1250 988449352 988449373
    0x3092312030c091908030a030f11040f090f142401030b0102152a031b041206050c040506040b21060a0506132103030c02490e041d 57
    0x7502d40002e40f00300820b416001d40d81740e09180b880e64120758420000288c81d181d0b681269503103441112030031500000b1180c6041e00700490000c800c401486100400d41c1e4494010302201015844000c0e1110741c4105030005040100901411071051212803c88100c02505502d40758001d1044680000c0103030041c0c80104a50b810454400400a205d03482a00b030229041282c8907640841d088401d450741e4541f0348a043c0400680d0920004080441034080c3c10041404a0011401c0708608254000408903041c0d503044040901401203500680d0452008500071a20500d5007000c0d000e81d00e00c1d8110794008588240010f0105c40c02990403d400c0340c440d81d0103222904101005041d0f1803c810340b0705403881c0d1307202040344166100340c1d40b01507440304070485a01050752500a00c540000303d4401000080c40a20141c95103200700724406000d940c034807010500400d500c030100c02c0d4511204812450044104130064404000000d00714803862804050b00324024003a1600c060806d2404003d224040c503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 988451852 1250 988450602 988450609
    0x5013209040602070609081c150b190509040f0209192102030a020901060201060e01080a03050f030601021507020106210c0b0f040f14090a02032503092312030c09 71
    0x4021002c4e0b0782c40b601d84900d5004a4847d4009007803200041709840c280600c031801c003508661608026080c00c40c4c038107070308000c0d05c0200f909440c03c0428507034150710029492070040d42d4a01c0741403003003074200d03040c0031444900c400c16a0140210180035038280822000307030703800380201e0f0342d0500403410320702103400c5030003000387d950920003100301c3c4040c1c22200b50038107903000104902c000740c1c422001030391604401d110514600100b140104a41402850204c41c0b59074080c1903405480c0030034a486401200081284e0b10070006c0000c04000841d00145e981004170b4028040c05180c0101c03a0000e201e403200701900100358a41c00610341d08107007620542c40c10030648000950007040850320b00d0307006000c04190103002c190020002d00710070100d00f00140206040c010400402840401500c0c414000c105541422400150964110b402c010b0903144030b5103025030080c01c1c2a1707c0603200b860607803210300000684616850600e500041140c44c110442420ba5605200840d0310110a00307003400b0500f410305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 988453102 1250 988451852 988451857
    0x70302150c251e0b060f06040b0d0c1e0813020f120a0201080a14070f0302040801020d1a060702010c030804020411300106020a0f050f0105013209040602 67
    0x400c1884040c50044500c200c60b58001c24920040150002041c10b5410010f85041d003042e01644804a80b0184079540c940d2a5018002024036014042000a104c015500c00080310060000c1c0e000c11a200c000078032804008044c41001100854080c0407003000001c5400d4441d000e40907250f03949240f40d0b035403041861a002e04900220381010082c0c444010fa50703074500000c1e4541903401c0c004d001c15481400014400d40025161a10040c80c15540a4a64a06001030b84e403003170f5141440c41c0c0410b02c110003107000b80326a40c03007551254801f003082d5021001e5900407080c11100030300a01000f154034400c000385481f58080090204031000c0750000003034040d000c1d180d489400180009003042e01c122035054507501001070380d030402442e02c444101c000380040c0b1404007140c1482008690303605102021350340d1501c280d030103030240b084048a0380c10014100041c13030000c12204028085942e6072031668891314071000c00500754400c40c07000381038803410090046995510081c07029906890365280c2c00d000f035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 988454352 1250 988453102 988453111
    0xc09050d110307030f1202101a0603181902150c0c100c0602070b06210c040f06031a01050915090a0b012601090e030c060a15080d0201090b0a0207030215 67
    0x14060f882d0000081640e88036980307080303801644050f001ca10381c0c0c1402820003840703005440b445031a020320a8080020100d0300820924250741031a07586d01c0c0c2c21100350420321030040c0e255180c4a042c0c0ca140081c1c65202e2810316182c03094400c011407000807521280c0030701030005d46101552001d00503504601d0314682c04ea2103e012401c00202202d00d544503034003a64403400301503800e804510709200e142e00f044c1807040d143c1007000f40c50003404c01c85241d505449d170440380d800074410340d22041c04162a03501a40702500842e4041754a40e060080101e14072303605c0909214103032080145c9800101c483d02c0c643d04480d40020700030a0380c84242d440020303440082c01c03070301003140c10424104403050b40030700e1010000034160031009055079190314051000e02600c00010121980341c0080c01000003691b80020030640241203010080790380c1c4290201c00b0002134966201c01094032900c00c004500035010760021864030301884844940350340c0c200c0e100381a4421084000d0069208a0248418900c18003805810 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 988455602 1250 988454352 988454359
    0x50c01030b060c070608070905030d0804380103050c0102070806011505120906090c060c070311040b090703050402040506041812051608040f080d1403070207050904150c09050d11 78
    0x418200c41c00f03c0b071400980f504464042040102881082074103c0f07891002006c5c00c070010000b01c0310201c0001d154180242008240038450b03109aa14141c46034007200140e551010302250f00035503c50120913034142848142d609020f021410820303544085400390503510528000e005607440c0091280704810440e420104010013403001140c0c43c0e0382c442c5500d008a441500612090401030a61400e050035100568810304040280c100c10a42c0418107008590700030140107201c01c019400314002d0300d170030715141d42e001d0742c0d000c2009a050b80603449103010740e0080d1401c000941e00d00c8280821250401e180c0d00100c2e0070704d40f940b800100a02e09400601000740742071810000c2400c500b00400d080080105e6811902040620240030381141050081c0081401091f01d0005150054041040100500c1c1c0a047c00000104042e0003044000001c0001034030b03a000d00c0c0307070034148170142c0c1440850940401d41401d0350342c044030344101100340c191400201000051000da41d00e001c80c1c500000c060540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 988456852 1250 988455602 988455607
    0x5090f010f12020f04050a0e0f0f0705010c080405040e0a110402040e0103020f0f0306131a011a0705070b0406120506031506120c091f0b03074b1b050c01030b06 70
    0xd0394440b4007506e030144a24490201e101d581d10250035003408151302515840f541b04446018210a00040720400c4400030300b001001200c00c0c1c2404e08481c41644c028540040c10440c96034000d0100003041070700b03036000e82800c0984101d040b041109030b12692040c0c40d00140c01c1307801400507280c0342880c091600c0009001c00c08003101c00000c00d0801404603000c60a0300e41907a804d030103002c501c03411140c145d0391900d0250103a605108034241ca245d241d0b1078100c402c0b4004074881c030800c50308210480240100707111043e02c0b031390340e00001005900311190442c58181040003040c0c15040000b000402100b540d820b40d0182da8440080c0032410307140c4802215513110b041107260303407500c4000811703000b4481d4000c40d401084440081d455500ca80354440e04c480350040042001a5502048281d460101070181e0001e00098030f0082c0316003950810a40d2240145000d8074403910329011007540f800d840c3e82c964182c40c09aa460310a0807580b0f915001d8110b8200d1034a55030130390b210340d05c2051590030081c007090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 988458102 1250 988456852 988456879
    0x30d030f090f080d0c0c050a1e1406100b0a090303180504111902120301030b1b180f0a030305030117030c061617282405090f010f1202 59
    0xa42c0524812400d0f030b0346481c00140000041c1e0b6500481c0e035a075125052001c81c01c9202d81d00d040d170b10100040040d02c441d0034a40545c1c460000c640c803142203960024040d03c4018600e900d21503d8803001d8900780b800243c2d01e400050745070f92003000e8802c04500c6031070b44504180381d5201983c81e12541038002501d01c2240c440400e0580e070314442c1400c66669101c00c9a259000c4c142c41d980d00002c00550b0805540c0820700c9500c508001c10122415242d101643d061191902e0102500703007061042280310907030020443c800802c690144000f44404d08079904581c00c004501804235400060001900113072040006012100c1207102c0450019030301000c607440c0840c085182400c01c0c500380e070030000c9403075a4580b042819510804e03800e0109440c5942056a0800205c040c0500450b81201c400c0c03d00e94210808810b21558042d07003281d140c19084680003c0051100301d1150f01c203004040c420414400883c822508029440e0f040c1d03209401280d0071642446503010391a4030390310b01240d0180d02c3c0b18100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 988459352 1250 988458102 988458113
    0x61504060203071a090a141005040305030604060f0b04031e020409200102030a0507110a080715080f0405211c02030103060b040b30030c030901020714030d030f09 71
    0x50000301000c1e40519191400751500204030078507080540b071160000401d21031224008515506119845040740220406003001141010384048601c81032600d00001c0005042c0c100008502c1014101c0c2c00b000080e40311061060f020f80c81d40203814981c0e40c14441400054140a6440b41823290a007070b07a10000e2040c0d000070142d0380703040c0040b500c038000d2401030080880510420003014109001a508041d40410010800c0c01100005003c010603c80381c03010a032500c00350103018200b1403003910011619145040030b00000c14a0312400595100001900e03804c01d049601e003e01c0d4010085c3c0b001c41556101d0303e0241c0c960b24103861501a08000041c0f021070740e040e90210000c0020005a242e41c95030400c0c108462540b8035150103641840031080c41c641c2c0c0c41035035035001544080c2146080ea003507540110400301d56403442c043c2d4400000d256a0864002020b0b1521042c00d13800c03200401d4a03080c5001c1c03450140d000007601035001d1040b0300000d900980008940d81c10007100082d01c100c1d280c0303e2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 988460602 1250 988459352 988459357
    0xe1522050f010c0f080106050f16050d081801051005040e030d15030b01050103092312131707270b030d0908061f0e06040b180f01051e090615 62
    0x241d003169522241c21030082c0e0000d120b07002034005030074030401540c54a88050070b9441030131524851440c0002d5611807030300a10380c15091642d0800c0c05c8030841043c00740080c0001006a0b9000c0c0040e04286405100184c140110351091103060740d0460000e00d84020300015000c1d0f44d540c002d0354041030000000c40d400c50b104448404603105403d0002c2491401d08000e071903011303040941003508200c8102d000ca80e00c0800909000a0707021642240e110801c031042c2068404815003020a400041d8044843e80c10305039401600c0507009a0400d25443c4c140f216564041c2d44501213260188085065002512940f9074803c03415089000c1003241103200005d08140c0d80c40310b00d10101d81803110500c032641082001580c054044481c41e00c94124295030340c1071185003032054821440c40400004c0142c2c8540e0086120624041c1039000940700754140d41d050410308845925218041100008051500205040d612112490040b042da1540800e1015500303004011640000c1d0a07540c1c1312150448500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 988461852 1250 988460602 988460623
    0xf0b150a031e3306240207080d05030f0106090e0403051602090703020318160b0705011103090607030e03030c0304110d02120127021813020604120203010e152205 71
    0x3004400740c0340050110300c01c48180002d0100030344c9080410b2010780c990b44103088202c009071854401d42c00d04040c04920f04603098001c0f000600400342c003641000c0e0001c010358055903a00101c2c12042c0e0b218807044403180781c0e5125070101c001000021502007402030300245451001316042c3c54a03403500b6004501201c1c4199a2400007a03400010010a80071341c0d180640b10f0541c81c000340500901000d071050b107556041c0a0303076080c288001051400c000c0e003540100c03100c90310540410303104c1c90840e83d0240c9414003258580f000c41c0c1031a01107008020040110b0b4824259a0252821360304c0b00d4440903070001040002e0790704206552001c10144c0c2c0e504901030f2000342c2690010071a00240c051040714468540203241100c100042c0500040e50b401074800f003c06041049101c042d92035402c419100c40003100040d4000c0320004011a1010b0040b40d6010150700950083c08415080f2081e260b407401100c0d4440c201080d0744010030030802e1040b03148003040d840e43c85000d40091042c0c5550341030018814 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 988463102 1250 988461852 988461893
    0xc0a0f0f170d05090706050f1b070f060216120f030e040f1521060b060415081605030906010e060102150901200c070506071703040f0b150a031e 63
    0x103a81d1142c510b18001c8590003134904014010243c41e01c4005812400342c002c8041d111f88001c5004841c02c4400704400401c40c504038200c4610690300c80e0407240c98040c0340211801070041c0550800701d030b000d5040d2102190103b1281e08800211919030003180c49046600300d041040d0003411044581c0c80740280b080d0500d20a80000b07045c9041c1ea2000c0d92908154040700402100c59540c0c4045108000f040d19695000400410301c0c604520008115100700e8000c03d08901c0344950031107108c0c2d8403c20040c4920500603441606002c100015507150004465181107035109800500a8040c5410341c1c9420034030600480f003411500c01c02c0300e5220314080b1135054541e952004c005451141e41e06c0c140c1100844280d0301c034a0b00d610b0401103500c5080a0160900034540007640104100c0404040c402800600350415140d0034145840c18000e402c8010660304400f0a00228510403048110780f03104040041040344d2071859641c032080d4910700c0200107003080d0100039201e00440c203060b80fa0080d0b4034030751 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 988464352 1250 988463102 988463107
    0x609080703090e15033007051006120f0204090503210417340b15010e0429040207020a0b0a1d0907050d0914010606140c0a0f0f17 57
    0x400300800582e00141344510a40300f44401000030344011882e003403080c2c4c060310031401029940019001011005070a2007070000000b40f064144000400c28000c402c0341050103001c04c03039440e1484211900c130140301801130030030800b15000620b030990048004600c01e10941c2d0034048045401c60044126800c80495100040100410040803295406100c500b05014a00384031400103034195040c020302120038403c00a2421100b011884031b07c000443d42e20a01146d094508400300b1700e0b41c06603d02d11030f4085500c000d804042d40c81c0c58000c480c28801c40e005800b2500311414501981e4054009000c1d4001d5400c201d0031015807102202c80015101000d010b60355107444070401008070314070340e90308d02c3d0703942c020070408849941c0c0d0103645070009254502a6240c061900f0300703000a06040c18001c10154030948010301d00d10041d044001142c100792206454050185010760152041e034215114a8005d0700e202c00010703903030541c031025a0b40100400400541180da03041d0110303ca0809800b01108003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 988465602 1250 988464352 988464359
    0xe0411040203070c1403120f1003060f09050f12030c0a050c070303020601030210180302010e01050d05010e100e0c041e030b0f0a05090d0801140f1507020301200d09060908070309 78
    0x568454149005c4030070045103416203443c0180c4108a001d00b85008521441c00422051a0590104006541c11a9041200e2840100035100604c4281c0303040360240030b500501001c4102c0464442d0702140c07112507091550f0707100145110543c2c080c03900345091007024072a03007900d41001c1003004017540c03198006000d1541580108020f0b0351487c80224104400020004480c0022100d90f908407617082c01c2190101d0000740060300d15010b0510b0980341d0601c0c1c4000050005500700c601c50181c40e48c040c0300c1521503128900c820740f44004580340790780d0000800c01000542002c919050b01c01940c11a041845510790f03039400141c0030103403550b0a5030308919083c4251345886100d1240c125540c0c20041a40741c0740c2c0707800500802014482c00681031011080c016854807098810000c210004104500c3e022444203008140c4e004510164080d61070f01590112400c20f030002c00040224a44116040c440030049000180c0145c4204564070390300d41060900158800c005082000e200380c4801104908 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 988466852 1250 988465602 988465613
    0x203060319060f0b150a030c1b06140108030f1b2e2a031a060c01050f130b1315020a080412020613080310120b0f070e01090e0411040203070c 62
    0x8122130031032207000c480100480d00e1411104840028850381004901171075a8001640c00711141500c1802c600035441030ba10030050170f5031040d02d40f050340d440c1c101c24030390703eaa003003035540c0c0503010f450803041c0c1041280034009003102800301d00080c1041c08844801c2c01d01545c16844080310b448440700c241c14990b4007160250117001342c1880c0d01d1501101e0a6006007032601c6005064220107100c01d0541c2c540e810000010f0081c8071a552000c0640320665400c0f5401006009000880f0140454505600441e84c10505000418011034000740d2a5a0310345440720f03106007101a00004407000030b4a100f40540c00308040c000f9010300400307600c4085451410741094403c40b07613694210320840d00300c041000090307104486510b1a840d003091340291280d495060000c654405034100e0107a0303191b8804400200319184a009124494201d00041c03d522812016a40c0405800040f030108072000f80074848025448030f01c3d0391141c0039055545242002c480820204c1e8800da0b00702001800e604000018801c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 988468102 1250 988466852 988466861
    0x1e0302040e030a09050306060a06080a0f1802091308030714070c030c03030e03070f14010207030204020d0213080c09060d230601060f0237080a050702040c08070c03030203060319060f 80
    0x15000b4024501e000e800054080e131540c02003000f400071110201e0103040cc0da8ac0801000c6d002c003c41001040070301480c0c1903003c420010708030300c91108440003a0042481400d014641c992101c101811034586080c10b0b80e804001411808441d00244655400300313400110050080d03000317860303c0180300d0840c00c00501c00744092013024001d510081d010001c204540381e511045890040380032049110360360040b8200141035101079400750000c940781641544681c0108060000019203941c016683d0110907269594194150351003400e200c001255410200c0b07800c0c1299100300e01e910500d07528031005609040d03017400214032503840880180708083e00021440e0380c182e05400105004881a0320a0403814030311072000c6141d80b0710303511446042c04c1c0344529464107a484204030f5110440103100030041c0c2c018410070782c421400e0243d54650203016112040c0182040d907622643c2601c00e0310706a000c1d6101030074142d054484c00b00c54241300711660146856031480b0781c8000c81c1ca94610501d000548 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 988469352 1250 988468102 988468109
    0x3010501030e010e0d18090614010e1203030106050d0207150e06070903110d020d080d050a0b060906030601080606131806081504030c03090e010321181e0302040e030a09 74
    0xf40e01d002404180013500044100100d18145044c90464000c0303030031508202400d50041d503856090003404207880e05904411001381e402070380c4600d443c440040c10000411040404503815400c1040103000c9144248000c20080c90040c0000d40303031214540d155804503209409011103583d445040c542c00380414000c031504000381b45441c2110703e0564a07400070700741020b220340d4496000710340c4080c00c64440b131750180280ca400c90051601c0c3c00e4004030140141004641d440440d601c0d05290b4a403d141101c2030b92075503600500300e2421961114011344952038040d00c043e51044d81401483e01003619500d051029220032203901d58448010651182503510350f030008001d9403c41c6e0071142e0403c425200c071580c03058052a1510301c2e582c04c0d08042e50032030740c0d90308500e00c50209800040284a2244114001907a415241040800038100b007141e00c152903401120f210155114200840020507400b18104845044550307080f9661380d001808981c903d16880503240c1003c1030902089410904e10f8004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 988470602 1250 988469352 988469381
    0x1107080703091e260706020607090509150420220e01080d050d0608161d070206150f03070f0f08010c0806042d0f06080a12320301050103 60
    0xc19511000c00d2180a2203401075840b10650700c1c0d1000c0e200d1000320013000c40c4680399825201c0701522240001e4a45100f124044049901494001480e007080b00740300d07202e4035034020010109c030501c0b020800500b041a024410b0600c5a0042c80c5140325204001c00018003002c0080080180e01785040340311149650250a04072030913001040130100106141c0e103140300ad45049a615620410014000c0c1100d4000c8412031080e440003800c5004188010403e42c1d05815400d00c580300040c01c1031544005c22036280b40140c000c0d4012450080301c0488154160a0041003010003c07071200100340b030b080c0113900140804c0743c101c00421108080d020480d0191508200a003c0c1030b0401340050a203440c080c0002380030300d64035904240c159003012664070300050000203241c40c44a031b5030100c1d000f802815480c1522145407210020701e00f8400a04030316100e0f0b04c0000100102803403003044d101c030004c040c510011100e0b5180d01c03242c4010041054891080c1d290011501ca504040c001011180305242201c0e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 988471852 1250 988470602 988470629
    0x10180b180f0d0209070507050609010c0e0d1a10030503030c0414090405030304030516020924010c0f1203060807170c15070b061201020c060105030f060c03070f03110708070309 77
    0x30241c40300111100c2c0280c050b101c14001c4c2d00c40600403901c0f44140e05010f06039000c0c400c1404003100040d04107802400381550b40c986044200e00401c0000c0050394401016100e0655040c1d520716185102c095001d9413101d000f80140ba0303a515070508681c02204c00030844c0100241c11311444507500c0e180d00b400c80003a20b4902642ca01070f641d4681d80d05c00a04050140030740440c0d094004001c0507421034070796074013500d04c5a00d03040ca207040442058034050124401308800390251000e511800c00c604074160040710003801c205081e22451034080300300c10a01c6c00c150303e400300401d8045082041d040104012020b4446c00c1d20344580b40c0d414400782602c40e52040300d0381340080142500030310039619010340091008030f0585401c0002100c44802c205448070a5002040f00d000c001f40c00300d04541290003d80030342d01d42441d0b04040301d44a40c421034403401d00000c181701140405108542004070302c3c041d400d0002e41d4a8158454045541240c407040701c00d00c1001070204109503200071100e00138019200640c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 988473102 1250 988471852 988471879
    0xa2301270312051905160f032d0e01180e0405060723030106210515090f04030f08090a050a140c041104061407060509010e19050601030210180b18 64
    0x1204e116180c80c480100704000c10803400506134400483c4000d94803218980540c2d400b4a400b40c8281c0010003030389803640e041d682c20440e04208100354501c002490f0f8414410a0850780150703075404a0640c00ba292002074500452442c1c171f2089580e01407405a801032000b8603004100034802c1483c1c141c440c055070701e10340124080d18005c005803812348842d03040c224184603440002c0c009002070b501c0511101070900c003e20185c10382032009000d1140d0b003510322804c281d64014600100010968006000610f9623407142d002c24401c0c00403540101030726007501c1001c003180d120035141011862054552401e030103001c4a0b0307182d08000e9508000720175a0140f0a4807881d040e00a5031b40614070508080c0882c078001001c50704001b008079505154000401c1166080100001c2c1c0240305e814005a031f00d108907003030346006101117a1907019980c0d116008100b203030b08640c28006000000c80801007408900380010300811089040c0c040584825280d090700c2d0800c81050f0007400200c43d8129009504288892 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 988474352 1250 988473102 988473127
    0x30f061905031509150703150626041a01081c020a0b010510030605031e191707031214060405060a05010210020f07150c0305060a230127031205 63
    0x11910844003e8a0301c41c50b69107040c098145028074400703200d0345600e501000000f1b901540117602044801c118041e11544520f0140e56507180e81c19220750031600701904035881042c0740604da034883d1203024000325001800d585203000c20001e0704040c100307822080c0e000611860ba0103003d116480c9610091041542c2611601010403040c02000d000d40609803118001902a070421401450f004d802c840d800c000c80400c3c0c8000c1003400210213980e01032810145e1203c1d02e00741048803401d412115401088402c06141e8000758000d0004074140320b52200000e200c40410311030300301440403000e120074039454250704200803500020145031145076041c8007401540d90015895814000b4080c00581d5000071041d003043d98001c0c041c0007060561810600d0f00c448100307401004e0740c0203690302e0a01090304c0c0c24041003981030107070080700c8c0c41c241113096040c40c46003200c11101e2030b0702060405249c0034280f00b02940807104408a0008480d020040c204204103108a48500001c8945002d0741840040340f00c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 988475602 1250 988474352 988474363
    0x7020d0b04140f03030402191809060923070b03010b0a05030406060503033402060d0f1d0703110d030c02010c031101020301090e011a0a180f02030f06190503 69
    0x2510340c059a000003020000250141c041c10400402103440c5404406070281c0c1d01d07402281e08a0040d55091b1003000c1038990a0070000c103039410401d030180c940d61041071203001880102010307602070340c17203507514400f0680440308030340c507440030540002d100c41418092038504030082d03201202c01c2004100400060987d8025210002090b03c0c251381d49460781d0604d0b40161441d50407a65042c00006001d40c01004901c0954140d8000300b000c24503069036011070b0013090401c90720043c0d000740b0200008554004a903104601c07000c5c0700340001030107030790310101d03681d080070460440d9100b80d0200c4000d000b4090b00c20404000d170f000845010b4803000301c658009200000c440b0000741400a01700388030040500170008200002c180100031512580d5907007807803020784003d0000b044507520f81205c1107070070340e10780075811195800503140001e468078203000c0d1003050b0000c0b0003504400740d0b121403074525502140025401040c02c0002c05403581085410042d24000149241c0d412100d048000c02c0f01d9100070a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 988476852 1250 988475602 988475629
    0x3011e030c1703130e040219140d140703060b040e0303010b04090b15070804050906120604170d02070f020f09010e1b0c03131503061d04080c060a0f110702 68
    0x85506004007a40b5100b481c500032040080c20200c2e03000b4002c50700c100d00303260591146000b1036540c0c0200342c01185c1910000c0c414060100103819100040159003404801041b485105080c12100125191070f8071303090949540003100c4482d11501d000901b0720b40390164464004a08001c0c41c5036514080882741144180e02c2216045900d407500c0c10090743c0d4100c159075100500703290050350380e40c2c945000722485d44103024241c403640c0484003042240c28140c11050350000603e0051070582c9440e260081c01e000c0d003c00201c801d200811120300e881720240040c1c4001303441014100200500382c410061484940c0184500410310000104030914100d0304180d00030b684441c40a10525a1700c0c0c0c0058a13205190315400c0030312001540c0c030103182110100200b15028861320181c46030b5629012003d645003032107616005e1100b0f185540800c210301e5240f90300148151146440c0a920f41e10751800d083c4211000ca0803281d807600f280d004076006000f1078110150340d4801c07501e001845d5001840c0e092410b031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 988478102 1250 988476852 988476869
    0xa08010510061214060d0204110f0702040c0c0b240d2003010b030d0f05070c0e06040e030306010c1403090a03080409180f061a12030408151e0a021c0203011e030c 71
    0x254006d09540790f66000c10350021000003041c0d43c801c40c14041c2da4044c0c0c003110341240610b15107152254000c1c0710301161950f0685c800c40003052500c0310600c044091004141240200e4000000030701265a100103441d030b1248102c050b005003041d4079003c580350708180c00c600c41c0642d0500055020390ba40c0842c8020301d00401d811b00c0282118a4a000c41e10303070080000081513943c0e0201d020030008410b0011521540040f541400011a03010b10350f522400165800c81c0421810600c00700061074004c09055005c41d0700741100e01b03215100e00044c0c4580081d40c0260f41000e40007900344000c0303505008004004414a401c501c40740c1d190f6440d00382cbd40c0306200d00680459a51752481c00072402c031198030340072200d00821769112142c01030a516100e910502c5442100c0c403030310030503c0010403010f150502c1884000c800454010b0004804651020018004820175900300280b030040c071080050700e103010b0380ca414010303265810300e0380a00c03c85501c0c603082030740030104003010000150f618582505030740486 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 988479352 1250 988478102 988478119
    0x1101060e0708070f022e0f2714062e080318041803021b04090c0b0c03070606080726060c0c070f090903170906060607020a0801051006121406 62
    0x1a108074282031600160f07000c440b0400030031840710f024000174600c0b41c6d007a421007004001c944000500c2100c82504000410008004108100050741510005894090707112015046079400d030040c24000101c9002550602c0340ca0380284400102003a43d224101c03440354480c1e02d40c102011540d403030081c8450000a403100c01304200c216150b94000402c811031451030754001c0c1d4403618010b0b4450072880207540e189130403000a12018030f014011070042d6034000032103480c07103802c00c40c42042d540d0260032110410b100400840e000030740940706040c0104900e001038042c0300c3c100440c00e25018950458204246c5610301031800140f808280a600a100d005420f556880f000070450b007000081d60081c803030b1525281c0c0c0020b002003a0341220014038030030380c0c40c09450310003914000507813501580e1074619035000100051850030310707000070300c4602d00052880c0310310356a4800740342c00d4034412110130000102c00941040140d80107003d40080d0142c446c0c0502500000042400400b140100000d205241c00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 988480602 1250 988479352 988479377
    0x180f0b0601090617060d1509140a0807060e1e161a0a0806130c0e0306060301231302040e010f0e010e151f0b070309050306040f08130b0301061101060e070807 69
    0x190060303099000e50005c00807000b41580d44200c03005040761123080e58501440301c1d142c0c80c1e501c80483c140210a80c0204024180034007915540020400c41c10903000724422141e4080c0315806007022010090001d20080c0000d00341c0d40c016040c1c500c0107034010180c1e0051180300a83da07458520503512001d0180c070300a51b0694440e0005a03c0340080305901010030300e01000e4409065024000483d001425401c0f1042500c980050500322550484510011440d14160121703d41c0e4224070306801c812250341d0141103106c0341c0c0010b412140c0880401110342c0d51400134a0b914001401032003660b08210000304030543e00d100e4500d49070f1f00c03948805020407900b000011500603183c5c40d10107000c1d19140c00303224142d4442c1d45040c25580301c1d0200340d020404030800052540b40015986100f01d520000b52031921019070b64040203034200d6004000b481038130003070205018040001950082685588011120358011a41c030b0855103150418001005520f0420600642000000d900640d56140102da00d8a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 988481852 1250 988480602 988480609
    0x7030b0112030e12070905090a05150907150c02011724012c130501080d0509180a050a18020603220506070e0a1401120e01180f0b060109061706 63
    0x20030740740ea0b00c03400c0c0408001507400001000300944004020801c15516102008d80c0d0b60180080001c1181d8418045141490304400216811880340001c0b1552161910080a007414441c10b52200048100c642e0005569100f03d00589440f1180582c400e2401c0c2840002c8507100c5500900d0700f03249481c01004d0880e407007400c1070b801c091009843d0003800f0b9041146000b03400c0044a10921a01490b05250403c1145d446014121111080101601d140f03168054556410003000a58007480c24408a0300700d0385620340300b9116402d010400500c500c0c10040044c100c90110030300d40c03a0b00042d85039050040e21000212600841c00360480c10076080700f1103110b4148406030b40018010300814051120740b82c0c1005121401d11000c9032020120340d158001c401c0400c00c80c105042c00500810f646001e202d00c2035210030000062100049000c0f0743d0f80111807c91100d611044400e0341103106240b0902000c0c24030160400c10134a010380c0c200d4036003100189509000c842c034940d812903a0021442c1a039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 988483102 1250 988481852 988481867
    0x9070c021512070f0c0b060114280e0f1905120105070e012d0908030c0601030507080c130f0b1005131a120c1b0a03030e07030b011203 59
    0x65008069042003600101e255056402c210071280700701c041d02010402c514011084a0041d00d00e40c0d8903541007580742d80721089880c4002c3c04603030500450754018580c0d0b0076044001e08054890000c451655032000083d06c564100023401c500404c05407008a48143d6204d24618a00c11011540e945540903c642090802d100c6503010a80c41145050007000303070f0308103400c041d12900c8651601591070101000560b8010200900621141640051296684034000c2e400d0403d800c20b20302401d000d0b448050992440e403140410b01e031198003200040042120412480c0c000c2c01503840500741703004460001c00e948005072078800444944480c5100f0300f0307503e81c0d840031302c0c6628014905040240002405001e60b400a269240c06a0b600303840403d0051034107040701c0243c150101c0d9180340c6903002c1206001508094a4034001910801c81e051070746070140d00c44000c440710341016080039170303103850050100d4866203448a002d400c0403000300081440002020b04480025032000f4100712107140846011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 988484352 1250 988483102 988483127
    0x6010e06180f030114040c0f0e0117100c18050d03051902011119200c04020a020307050a030801052706060c0102071b05040606090b0306280608070e0d110907 69
    0x15171074903200000700001c41c1c01280c0603502501c2035481ca591200c940304041d00344c50050034480b1295000411550840f041000308072000e00c3c09680e02d412520030907200b40d0b0402c010300e070300141300340c07034502c03801c04040442134020002102c281c03601664680d000740950103881a100f124204501da80a1101c4c000c0d0402100c100c1103121003952032510710049526840001131403000151014005000903141c10b4081031409040b4000385034581f060800c21000e5401a10307800214003040c80540c0002d00c042101007025442034592021030b605000501c0f03216480d6114800040081c0c9144221803246014510b800103001c0d01c1c0c1940d0f401c824007640d40a4424810000d2041341044040c4054024110b01d1a059800c100d80c207100290b07a4100803030b200c003510b01994245000c104080340c01d0f031034001c14002e1280080d00701243c50428211041072005801e500c1076001c41c0f05601000785103584042c403860403080071142d06904050640b20301400d104100c00490085450f800400c0380d2901906115410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 988485602 1250 988484352 988484359
    0x90905040b011a16061e020c0f16030c060f2007030302011a0603060d020418030203120f090d0c110604120c122402041a03060906010e06180f 62
    0x506061a201c10045002d208801d000c0c402580214180800300e01214040507104020034a010b03502c1c0c0324000140a603903410403424142e41c0103021404814005440603c0b40000a0840981e540103124246100e070018a2070a40c0c02d020f060000600c0580b035101521520b190103144241d8004042c6d900c00390b82c000507015400080140b4440c4d0000007540d5096901c69402404014004a80c0544220320300d84004c3d442001800015450304000c4090003080340010804200c4802225900366040201c0300241d005802c0000e0080180e401842403540212603840c601c0780d18034102c2d58440e112028030907500c040000c401c0592050041240e844030a81c8002403000390f0310f5a91300c804800d9440641d5044405040401e0006120280130800c0350005812600100440d404070a041e44180071913984286a41e6083c007011480300d0074540406001c200a8008070f80ea82080c000b080000c140003018581004040d1441c410765460b02c2041d2415881c852076511720914092000424840c61040490340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 988486852 1250 988485602 988485611
    0x51315141903060c020d140f090a1a071106040513090615060e03010609150b0706110a1106101a07170703020304030c060c0302070b07051912090602030c0613030909 72
    0x50000301e070301500c0071000a8084a00c6d01c0307407441056807640202c0c543d03510460000c0c44441050301d10400204421040240590b074004d4541d00000e0002181d803490580181000c110f03030341046075511681080742e008540013800d0510b00390005502c284116100306072070341c42e801e600301004101d07041000303040c40d021002956139844210040038507a08500707961080d801d0001c0041c0310800d40c0701d0701c003082c1c10b4807022060441c1400ca120b00154009407040703074000d40e914000340c2000c2c0c4100c050030540200380e039a0090384040c811610714110020784004992282e6207400c00a40c181086202c21280c501d21106441d0500c605019030782200014140d43d2282c00000d00c0c4080550210040c42620301c100c8a0b07203c516103a0320200d035024503003500100564401d440602c454003281c00904070041c8144221440c41c0d0080c3c2c100a01c11101900441d14030214102e509150307a0030074201009014180300540c20841c0c001c040303070380e902c8028000407454002420803200f850310031140308001d080c050300b041c0f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 988488102 1250 988486852 988486859
    0x3040308071a01092412020907111002070606080c031005130f0602090108010e1b0331050106080109031209020315070822030815060415090513151419 66
    0x500b2201d680d0300c80c1744426007032142021884044076815120081c004078080c1b003080c3e0a01521440113001c80302440b208042000d500c00042003c1c2c40c0a0b48241c8002da00e4035028503101c82134804d540c00100090b0040d100030851903c000030625010700e89680c01050946805014406041190001504070002140ba020510046800400389081d0a0b80c0e480c1c1d41742e90b40e601d2111141400c0e82e090f0300d030281520b41c206122503100003843c1c110780d01c4031102402d15079030303202c1c0781170082d8900344500c0c4042d86101c0c1c01c05002c0f0070703c0351000400c8020000d10801440ea070300180315202c0513203042032035640d0300c42840664a04004070b2046542c901101689410400b00181c070640e803c5900d94108c03007268030103030000210301c4001074240b036050300c820a043d142d20100051005c03094590303540203c010300c000110201c0311844014074804c10344411303210904180c24020352600003a0010007090401f9040119511142101800c8500609861505141010010341d0b0401030034004a259500c006022 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 988489208 1106 988488102 988488119
    0x120a0902090a090318030b061e2412070c0605010801021c0e0f030f0c010f0b03120d0609060b1207021507181214060903070503040308071a01 62
    0xfa40f40c4105c44034613044102290313105544401d090300522040d400c0c81d2400c0c40c041400110038404941900020400940c402e0700f00c0303030780140411241c1c12160040010355540f4818100e0403002410880c600802c1075400302c03408d48541e841c0400002e4101014401c649402e0294018446500200c440e6030000700100c2540003040d00403007810022604061004180b810505100c40f901c0744c80070f0340da45003181d00034940c2481c554900108007441e564005030303020401203010780c9103903961040c00900740940b0032640450029070500e030340030400c0049040548019182c0d040303140025075588030126600d290171359031981081105008511020b00c11141d41402c811104138104020760350f007103179002c2c50700350034800d50f02040704561810309111305016042d00508030388025400c2c42d006488040d01c900c200e200040003a440014194104400c00b00700b40c007400211780d810620307580e481946 = true := by decide +kernel

theorem cover : BRFrame.Cov 988309352 988489208 := by
  have h0 := BRFrame.cov_init 988309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 988309352 ≤ n) (h2 : n < 988489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
