-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3557
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:00:22.772907+00:00
-- url     : https://prove2.me/submissions/f23578b7-59d6-4700-b8d9-51488724b05e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 639568345 ≤ n < 639748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 639569595 1250 639568345 639568357
    0x1503060312120b150d0b010c050a03050f0705060a1e140f0c04090e06040b1f0504150b0a0e010f14120402010c020915100905030312071806020c0a061112 67
    0xb9480710b182c40502e0741c1d40010105030300440f5002c01d03180c065140500044403400c48549060000d01c00b0034101007840041c000c048140e0600e400780d40c41c04030001303280d5640184140240035100d54007c0c4080c401007600a42454540740450a0482619548400a84441340c41c1e0b80242c0912101203150b81c412892602e92101c4001d0b8501c2c03400c1d541d800c0c660110340c2c1c0840000d01c1600300100740420080340000c0540c002c019907011180501c200201032803034508a02c02c0512032540c3d01c5681c031402a4500c000001040316004043e01d6400003d805030000c1880c0d100e003800681645816442240507012138503040101c03850460074000c01090240d0082c0c40500140e0610490380503020040e5100366a2a1040d0f1401f0183c40c0c0303031000345050004c5821201900740600491001c240900c2c0c4001040c1c454440b864110000d0a03210f4640130341e0004052a003c1fa5051f504075004104940c0011361071494420030380d500c2d60785540d0340d40e088803104460750b088500c070340010041200c900c9210020b452 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 639570845 1250 639569595 639569627
    0x10170106020a0b16171506070b041a0402131a09010b1b06070c02042003040c03060b06180904030e060a03140903031308070c09060e0f0603010c0e0d1a07091503060312 73
    0x81c0e41c03c10100051f80c2c4e0300402d03401c4452440000c104010891500c2141d0f44030301c1451184082c0341029400200380003501b6001c01c14485ea100506038803100040d01d410454500a4802400ba58483c8a10b92403a07001e41e0f41c01c0c04491411a007501340b070000284040c8900c00c0b41da0b451140400c42e07403c001c090300243d40641c4001406001c19070002c85800002c6000d60b10846800494900e50b190020542d9200380e600e41c8180001d000e0040164104021410742002c2262101e140c0d548900c0c09031116035854002c00c1d04080b001c0b030000300858055120207504100c0b40740b070882e1a1f5924070900e58902c030841d101e2040740c240001880c0020b041c035014119041c17050f0007100c0a2520f924215040702e0b500c0d842042c1d50340c0d4100a1002c1c40e503c0002d640d070421402d500a001d805090080a40a6445414417502400000407000144840c14940340c000380c641c03000300c88507403e02c554020402c0d0102e0150312118200e081c02060528003c3c801c0b04212540046800c0c0c5140803594241d51a07003240148030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 639572095 1250 639570845 639570871
    0x50705060d090c06111014011703191805120307030513080a0f020406080c0915060c01410f0601030e1e01050c090f10170106020a0b1617 60
    0x4000699510b000c03201810303003a40e40c1d41e48000f807041824135100d240144651701a14001d0a0803150b00110187e40c1501d10200c81040c00e658103606403403451040490780104246c950960084032035104004000030001c0c07160004c0015120b204000c0c402180c02c0380c00689070310030002440000d0044014020100b80020700040e55031f5903003211403e00d02440400c0700c1c0f46603c14080d078118500392258a010b040380100810a021807040800e1042c900504103100300c0140d20f0310324031240d44003000c8901400d44178000380041e0403a600048200c070f0a000d0110f6520003e0103802e101c0c20643c2480307410003641c01c03801d001d4a8481102400e84000054290350402d0b072521a030700d42d24203080003e6802810361940c6000303503e45d401d003e90308607100603220500c0c502e4208084412a030700d40d0150300000404a40203a04200c001c0c006039401c09020719541042c8420b01c0001841035004102000081d0240104c01229600c0207110f030600b0b0140c010400201e8a1048101c02128100440c40e0f03219101e48504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 639573345 1250 639572095 639572111
    0xc020708060106080a0c03060b03070c020a1a0d1107080a080901090c06020318040605060f0d0f090524060105070b3402160302031c1206060525050705060d 68
    0x2040c1400d1090304220f000c620004203108451a003441000e0b50b5211500d01080302034101907104a6900c00030300143c0400c00310072030110555868245020080c104807903144034481c05070a11080903040303625000404c2e0301c0d000d0800000c0b105041210b40302584414891700d000e880880545400074081c04484d9113660b1240e49000051150150f14040c1c8115001182c5a480001d04481091a80b0240c1402142025020021510b42c0c1064a4000d440d09540b82d841d4000008218010041d00390505291400c0c005001d05109021030411011801c6010200768001c08a1b088001c803103094034214000380041200300040392000040310740146225504041248210802c0b180c4c08214414520344050b140c0c0e1070403001601088001c82c60051a0f803803070082460750b00001c1d00ca400c42c400c0c207401c0e00c40314032480141d42e2189007242c2d216168110300700304280d22000001c08640100d04510301c0910076804025000e502e0f060620f86141c0d10800804100381483c09000103a040411080b501503182c10603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 639574595 1250 639573345 639573359
    0xd020703051206010212031303030e0d090e0a2304051c030608010b120a060e0f0f0a061811100c02130548070501020706090c090c02100c0207 62
    0x1094218000c0da116500c03151000c5020400140c054a01030655211a1402200c13640d075000b80c07a4014021134007440b050030581001d501400e0090f5038103416008541d450303800942c100c000300007903074008042e881c03071390761034a024100704d440081303081c104010b40c0c3d14500c2c290080d203072511b68002e02c203105644c404501c20010140c0b503036890b0070b808c0101e622132806003c000c000744908520300100329040b0030f0111040c0d4420ba250110b1080c003924283c0c40c0c171040d422080c03040010342c085800400803241ea10442050254503100c51102c12921142001c0424a030401d482c20a842016006400b200540c840b500c204a10820184a03c00038041c81400c410050795940300809100000c40350046200d140400030203030102c2d42141180d691401503000c02c502c540b0300d0421480c1c1c070210b42001064010680c48181003a001d00040101150300000e01030080142c02c1d0072501c2040d205142200074103850389065810303600e00800c0000140e00c4040004038400094000441c148880e0040d0b51030705840d0300c6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 639575845 1250 639574595 639574597
    0x801150903120c0605220807020f090c070606060807050913060b0f03090601060c0506180309060403080a090b04060f12060905160806190e040303110c010b131116080d02 74
    0x40c502c0046203640c05036000f400001d000f06503005004c80740d40c1003021a241010f500022800780040e00c404c0c2d002c940d130411520382540b40811541c0041c459800362030451002d40c440c2d4410765044800600381340000031000e008062403401030700692649420b00c0480c405010001001c0c4955801c0b090b204c0c1c0c0c2c0080d94800c20001005101c6980b4042603a900e406803a0324540b0300107078010000c00006100d80c4001c905e0203e40a504028120811050000703c03030307081403a60084000b010b07402000046c00004200c6194014515400c15494001406d5580c2c3c400e5801801244504c601161005483e00b076214814854402906a541000203400341c48030018400c43d8011103141d034200905035030581d00380343c1141c0c240e94090340899030080c0c40e4146e140c1410044081c0d11407481070b12100c0e4080780415010741c001d0200400c501c01e5280c0c90320002c0b1042030180c401112800d000e0000c010280a030084540250102e904544002500d0101c10303821401c07840142c20381c165039000091120103070180c0980 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 639577095 1250 639575845 639575873
    0x1141c020a020f0f12040302060c0c040513050c01021f0b0a1517180c041e0c0206070908010608061609030f03020c0a050f01090b130504060f06031b0801150903 70
    0x40e0050100780d1403c50b1003803425650910b0f0352034562042c0d0500c2a103044900840f015658169000360319407400d000c84600e08500d0b140c0b07255010b81400108108401e030036120304201401042150f020080300b2005a80f00c0c010100000050700c0c0b00020400ea16035640c100c0e4140d0300c80a410011082d0750b500c0282024590071800c4800148055a48000c170040c1c1560b540d0494483c0041c3e01d0036400c0b0702d10311a03440c0b085110860055446418040b0040c0407008080101c0c41180024000b24803100c000a4454004644007130201d410000003040201d07051003024265031240340205020745801d070001441c901c0c46840801004840703540800050f00300d502c11b14180d03100382c008001d08403020017000103012183c0c0285000e040ca594240a43c0e1b13a01010180495144542440e5104010030380c0c09981000782c0c02035a0803030304018001405030712041d8090101e842540d810451034a052815400c070000200c03140c000034000e1710050040c004c00c0002c4400500d00e038100898019901c0c4e0f1100c00d42045a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 639578345 1250 639577095 639577097
    0x607050a060e060c0a080a2a03060b0c190206070c0e06030c0f03030706050402130914010507030603050a1101120606110c0a0602121c140702010f0b01141c020a 70
    0x50800c00d020030505000d10b0321140b440700003074903403450a265058124010300c01d003034040280d0b000100740400c58079031040301c190b080324000c92114071b0103000c0642d1040d01e036080c07500000d1400c2000200c00e005002980e480d4450b000160204003c11400001c1c042000001aa8000c5040040000040900c00b4810040510f0710301c003152442c0840c1050306145409142031301540300d015400140340d50100c01c0b164590b6100c54001825101e40c000b19000000c0491030040851814460340203000800380c03020b00000b00c0000900240e84c1d50300d0102c05075865031100078400d40c460307111140007555059043c0b2041c0410302d404180a1007240c0103100303440c130680c040300c04070f11030030303034403581417400740503d05251700181d0b5120b8003a8a0103100079030b07503104061032280f02d00c0081002540300c40e00540c280c5d000300400d1401d1140384c0380303515050320140040e075410015620306001110010214000d20444002c161580f0280d0f80c84040641c1d91035004030090401100119030100d9640d149102414000c006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 639579595 1250 639578345 639578353
    0x40612020d020f1306031803142b151409160e06031005030c0d03080115020c090115110d1e0210090c050a081603020103110d0c18050402091e030c060705 67
    0xf81a40c041c0447d0b01e140004101c40da119544980804d802280a0400c07220090340c0c40d95501031081c00302c81d160307400c07814994003e10401c801c00d009034050300606806d040340701c00410001e46d030b940c0003461071007540c11070354010078241c000031481040c3d47c41000d0321040074242403000c4818440010326580c001c5400b041c540c10800c8061000c1d040412a0328a01d80c1c4c00d5401a241d002d241d207019083d0340c4148984c12181c2c004405a4950314030a001c0c4180d04800944103a2007035840c0e804030b03078011084001002c0002d82c856003000d084040082c0b00004079546450b122150880307114050010032020110b030382944690710040c1c0c0300f20200e00c034040041303001d040e007072941d14180340405c2808107180c0d0206403e1b500c005200c02c401071441034214100c2e64242000a02018400306c0741c081e40c0501d00c01184802d107004180c880007508054001c2c02c200120705000714aa071200100400c0740105500f00340c1041607004800121001d0301c0380f840030640e000f41140c0e061810500003030410390185c817007150b81d500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 639580845 1250 639579595 639579599
    0x6170a020a0b03040201200d09150e040b031207060204050108061c02060a0528030f0b0102060c0d060f060201050901060f0815190921080108060a0221070c020312040612020d020f13 79
    0x9441509c000180110b0034540d94528030441d401000700d55401708403481a1b40e500c2c0040c038244d43c104080e00560002d1140c9986078920b0303003410402500181301301e9000c0380e951000500d1a151043c02035400c0d00380e41104029407481d640a0107542d80081480e001480000c0040e1969140303005520312008075034505120000c140d00d44000d0980344401180a1620304201000100d60303000b2401c107502400d0307201c2240e00e070084051740d0030142600340e100d260242c08001020078000c0e419008076200300b907204002d000c0e1075580d050349905c440303144c0304030010b5801480c0034083c9080303940d081d0342e0480000e4202e1080181c0042440048070000002164491544c08401039685034041d840c0710030b1581400d15540b00c5d0b140c2020103403100310080c0050f030071980c0024540c0c1c50a036030951860810582011107001440e05140c040d241c0c20071400c0503846403141000b0429500e410404035800d0fa0002e40c0d48840f1101c4035001180030b90086003640401940a01203005203016150281103424080c25071115800c4c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 639582095 1250 639580845 639580847
    0x3112b0e010305010f03030e0303190206041a010b091e090a020d06050a06090303050a1b03111e1b040207320105010302010f0807020f1006170a020a0b03040201200d 72
    0xc0c11001a5505240c20300004011012a025a03102201d0701810001c41c42143c0800003415032081c0190130302c0403820105940c1d01c030f55002807400d12541c4070f921030629400c43c000d045145801e09102e841c100110030060300e00142402560910800030281c2111658090240050003468045a0140d5603940c0440d410340c00d49031034010b40c40280b00680780008a142040700003482000c031404064140100020b132090418841d100807101c0c50880030240c008191103103001400c021044034900494400d18048001d0046c1004d0000e4480c1c0001c0018011b075201140d01100100148807103541c0300b03030709004180228042600045184000901140e40508201d044040400031018010f403513030316040c01400140d0b000900803a44039458140707035580d83c3c0c81c004100d141100c44c080e880000e0042500b241035030040390300000e09403107a6050180c50140d04482e01c2e90350300d480c103102a40c4010783c50010002e003110303a401150024018580640185400c000e000401d00b22032141c406242d0000740c10110301 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 639583345 1250 639582095 639582107
    0xc06110c010606090e040f08130305011b05090a140307030b0a0902040e070b04140f060721030c05040e0a0b030303040c0905162c0d0b060a170a03112b 66
    0x2802150410384c1c0e5090801c403040c260303120010f000916120003084c000b028844280b06072009844120100042d09481e0324013a4040e01280c407030940c00c21400202101c155008a042d60000c11028142502561410350909c8070713880c04440540e0035018001000c0302181805101a11503042c298000c2041103192040c04111580180c102180390050074041c0703c0042d5002c00c640440c0e4404044440b01c0b04400300088140c9100c103000e0b80d03c0100050400c00300920441103a400e040d0640110700c5c0508400000d405540b0310046241c00144100b0044c0300c01042061419084801c0b0040040c44280c80d8000c030f860b540c01a18190b41d8035007140810000c002c0e039402042e81c060001d0007034119114403000040d181103940c504100c090780c801c041c4002d00d132403209450503082c5002003000640015a04020003000c00545105004030801704000c14081c0c19801120503060010008003d402d0142e1030490f510710b520450701c80580039801007403280800740c1c0854100750b00c0d82400080c64194031a000740030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 639584595 1250 639583345 639583349
    0x120f060e060105030108061b211807050d0b04110d1401060b041809050a0b0c07020405180312090a0c060906081b091002030d0234020303030a09030c06110c0106 70
    0x10483d041006100c1c8540119210341c00c0600d8242814910803a01402c40c1c89003d07012030043c581d03003245d48000707418034060f055a0107100091800c0e203400307000e02a850b8030748255004040c0c1140d2400384120008203030b0300069a000b0301034101130844402800005503401c4440e803064418841091511320003903004c0c403030070300100031030342a1034070306450941030346100c0481232003d140f4540d54001c81018402c00380801d00000e944001c0f043d071545040b18401581390040101a40a80d15020000b0b0b00010b03e20800003a08841c80001d40c1040c3c66041000350b14100200280308038050180e14600062401d01c0c1c2c20f0240903e43c807003107562410810000c00c8428018040389000c440c05800903000448003040790715441017601d098240d032404010a07032031841552410000f0030700c0018010510400380205106120b900d8480c80e00e90a0700300da030018800b481d414040c1d4103410070404074140c40850b90205441701c3c42420300492030341841e1140800c940c1c4070288001100c1000031003880004080c454480 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 639585845 1250 639584595 639584597
    0xf051611060610050d14090d0e0303120f04050703050607030504140a020a03120302040b041530020a11031c0c0c051506010302040503190501060e150d03120f060e0601 73
    0x1c5540b4180e00041c1940710411401c206102001811021070103068102c401c4414102c0305459a604060f9901591003055040036400a0703004808c03102d0742d10780482221135400d900c1e407510003a0707100e910701c9101503c0081d004482c680300b036810002c001001806514424031a82d140044c2900e003c0c2022000503840d41c00724a2a0b411104040005036541c500103c01e5070740105040380b592005250a400034400d83d0403600f4001c501240000d120400d054481d0600394031592003e6a4124141800c1c40c0740c0c91040b9000010369414505d100c0040b4180e000d08202c020b03900d000a40300880248480c20342c0e1001040d0300c000b40320900403001d134054130302444001401610f08a050310300d41d912420744940750801080c0340001c510001c0344a50307107c0d80585014110050a03214a0308280c1603505001803540d03001c84280d42885000145424a0300491b40b040c0d00000c010100141d0000c10026160b00245080302480745611010000c01c0092007000e01480314404000b45080c148251004100340050810f4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 639587095 1250 639585845 639585853
    0x5060109090b1309060f1802130605011409011202030a0b030d02071202091b0f0a09080c06120714040801060f05030307020f1915080105090901060e0c0901030f051611 73
    0x6010b584641000c00e6000424a500250442207490060040c1038007208108842d0b00f0a45001d0462000d0780060010302d200711483c01c2801641e0304400e05a400a20446000c1180c002500e140c1801160003809401c2c0149040803d00c59110301c0c20003280c2080c2c82c40146140c0d03411141c6042d05042100b1144030007603000401440f49402050361039086c0211009000740d81820204002d02c0d1051828118115000c0040b070700d0710741808070311980e0f80240582c02c0003e0f0f0f258200042c0d1100201700ba1110000c00b800d15071401c400b4884002103150f02601103020010001241d80010700205d000d8030141c010302d000070030400c0c074242d010007000710580c100d83e2003904100074100c0141c0e5080200e00c05040c0903181c200301c4401284c11409081e42d83d0340103400d04038800404034261580590541d060743c404581800789515a400b50364200c803040d0040d91241c40840c0e0110344c10405103c064046008145404103d910410412070107075003054621401250080b2000600b10350402640119010340351300070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 639588345 1250 639587095 639587111
    0x521060f0415090237170d17060103050403020c0312040f140612100b07030309061b0f050c19211e1425030801080a08030604150f090506010909 63
    0x14103081215550000002002014040760070b2020b4840903104001034805a401540c0342c202d140c00c4011031b92203031824010729001440f0180030b600b5a03120340441029005695441200540040801800a40c15481441021800d59400f089422485c0d5a004041500c0314034001100f1090b00d0300e07400c9064480c0f5144400c9540d038446005841c1d002108240106982d03c40c00003845036032105401194044070300080c03070824540c064006003086403040b0010800031300071080d0070381d00d0a00000b44100040d41d603040d4020a5101c1c02c0903282c01103030a42921120000286946410817601d001143c4081e01c107016003c03800c02d0380404145c500031509088104013125003029100310f0129000c4c00501c05a030035499101c2600c40c00307a80e0031380038400702c0354004900864512541011075800b03c0001d426a03001140400000c203218488a9000a08a040d500e9010410010304503032041c45509045116000a10403a01c1001c40010714884c240020300341000f000061450000b500644500e0b030a2112f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 639589595 1250 639588345 639588349
    0x504140709060803190504030803040605270a0201030c0e12070305100504030f03090302010b150705011d03040923070f30201305030114040302070521060f04150902 72
    0x11661030705e140c40d283c0700c000508178400b520795004a420103005403a02204103c03c000390303544028000c0303203281c81407480348040e001044044140c4d401c400300385410458010006500a400c06183c1c4c2c21141418840e004800000c40c0320720380d80d00082c0c40f055001f40d004009019080c00248400e100e100f00500013450a41c4020b803440c141d00c46450300f0036503034507101d4003818401c2d480042442c0e4000c0c07104658240540c0541c4054000113000e8034507500c5d1240e41075840b41140300e1170f22144100f401841c1842e160890030002810844c0910380c0403555059405550044001c580388901d03d603444580e403d81c0f4005004080080c6c80c0c0e030300da10030f02e1198103040040700343c50026030028042180200f11102102003041e04400da420360301c1880003000c0780880200e24581e500340c050b00c0d000c1d002006034603c42c0b0313003541c18980140e0300a80503803c1044140803034200110001884045030001d12101da2903c0b401c54074202045071544031113411502404200903204085003000c40341000244505405900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 639590845 1250 639589595 639589597
    0x507051b0c010f050d020409020403140c0306060f0d0f060e2805100c050c0a030203033301081b030901090b01050d0c0506031e010f03020103060f080c150405040504140709060803 78
    0x901d83c0c2403200100d0004698000e58046402900b4281415502c0d90f43e80d18081080128088100e511402082c8240d1034504000034584d12800005103400c41440d55a001c1c064070820244080c0d030740142840c191804074806004100c04440305c00000c00c01e1551140154424911190010b2014084128010049800009c50365a40e0001000c0010403404c1020286c40e03900c29140081d549000e400140028141c020015500c6480e0f4112030724000d500c050407a000c9600b04000c080902040c003081480e00e944036128803548001720640301040080307901d0710a44190400ca43e5500c1603910b4a4030031040001c43d40e0844c0c010302080c0c0b54484200d00c1640d03920451901401664016440800010741071180c10890b5070b101c0c010140b01001e65619602e170202e40c0c090900059021034142040050200654240d440446100301c01030300c90161a882000f1428400344075500542505000208450340c1d240705950240388078002c6e10511506140c603640c00c00010b94449184149007071020046174030044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 639592095 1250 639590845 639590867
    0xa03020607081008060a0606080907081218060301030f030e061c09080919050f0f0a0905070509060a0c150203100303082e061805060406110c040507051b0c01 69
    0x2c00d100030740750f40b44a03100d00110042d600c400e00302c0c49000113010700c0d0340319644213006980295540c10b19a94a2485003581c8901a20415025900c213000e01803140e80110064a0001982c110100c1001a07203130000304c643d0000c0c2c105982342c0d039103440304104040e001034440d1005a4103850080c02c0c0020020100c2101640d45044017440e0b80343c40340341042249100c100d400c04440144200000140b9000b140001c0a15000702ca01400c403070409808545040c4c10a642500d0b802000040800e044c80001c40c050300d0701900c079006005040c00b40401594528000d040d4003c011b0380c654014001038144910500382a21141c0c0700c00c0d1042042c0100105001008000c1c2ca0f054284115030f5101c050309040103c0328540c5e00040101045040d040031034004088a044880c43c0e80c400d0f581280400c0e411104650701e00c50154089401c0100700070b0107000e18100380d000074408080e01e01c024000e001207425500304580400003d80c0c00030740300780202100c00c624100c041c403150050048041888c000380c5000461 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 639593345 1250 639592095 639592097
    0x1902100c022e0902040e0d020f0604020603221a070305070e030303061513080f1c02060105040b0f0d061e0510030803100911090a0e060a030611070c23030a03020607 72
    0x250200c524440b0503a045101810781c0a001000508090307800640c8078283c1900450060040004c000c9544500084c3e076802a07400030b155928646503142c640c0303900c03904498201c0c00d0b1a1a812140007140e103c4089042c603900d05d5091000c549481c200c000c0441d1001004202071040302042881c00d83c9002007038944c02001510341c0c43c0140072200c0d036a4901c0c081d003803000710312800e500004a15a040070070206e00c41c3d055242150f10b03150070003d4505d40321103102c004d840140d2006004114501d002e0b00226441751300580400740e01000c44010a00c0d40700303000815582d40c2d49504600304540d0001c100d0340035032090050708116a00b02810708200100c40e0744005480100c0103c0402c00341c1340c920340c8801c000c0a0080080000d451400124400358100b0b800e81da210300000400014080076041c01c0900c11000100700a013894110f6455a0081070259501c10000506214240c00036004400c0400a0b02140300d04140c0324086051140780700e220074000f2070090f0410070b0302c140025000070341c041c2c1002035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 639594595 1250 639593345 639593413
    0xc05100506031501090b041112062103030405011b0e18071701080609010b0f030d0c0804090c05031024111204060309031128081902100c02 61
    0x90400001e29000c00c1d84982d4500c0c0700044000201e000151b0f2140e08446002d880c1031101ea0806c0245407035900821072048919500000050400c2c640160043c0400f405035040e5040e403903014001510310313001180c040711169540c25400400341d1042e0020780e848462807414422a0030071001013043c000803510910310304407121012a20a40c0140c2109281d6030002004526a40c0c1d55001d00d0354407081070312498215445c0c50f81106003403c01d1150000c00c42c074040c004020a00403480c3c02c0318070b500060380c00d03a0b009405010200e40c0c40340a0156030000300c05a034400d501c80c20304144206a10041303a10810b881d1036501070807090f00903640039071000b01c2c0d00340c1004040441c14038080313400d0031014042c0340b4001070001004200241c06500181c4114000c2c0e5032603a103140c0290300f440e136981c1898844038641540c0214801003225407281c5c401c1c43d6202c0c8445904185402c503030b54086030310b10003a042c017607003120300c1246c0078a90622603000c0c191000d10007170501e0030301c10031088070f000c055503c00125505 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 639595845 1250 639594595 639594601
    0xc24030c0f22050d0b04020f01021501090c0e19060c060f151d060a140112050c0307020609010c0f0e0418110a09051e1012030504150c051005 62
    0x8158001d4810101d461207001e07a503552050b03420050405045024642105400000710707007030a22800011400d84d01c4030100030140c8545e02002010001d42d6200c07811807060310301240d04100004551402000c5440e40407624040c06903002c0c22001c81010041e000381d17249404003280340e01c01440e00c8119000e9040807030b802d014901b440c02c06884ac540e041d001c05418124084059003101003007008495901c1c207080c41560550740084002c92090782c80d10b03842040c058050083d031501c0c1140d0000c0300414180302d0020301202403021305507001200d80540980c00401082503031038041c8480fa82c458500e5008015800c00320304041c2c00490702404034410010441d02005558a541d0310a10902c40340c0d40d46111155a00d142c0640000c8020102900500700e04030001086602c60280d1030060090003051042507010f85403000100074010480c00007040301d000300064070307000fa00d421140c1d01d0199443c0c69807582040104031804415954800409c4031190660020881c04101064110045040402c00f51 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 639597095 1250 639595845 639595861
    0x42070c0905130b0702100e0c0a2303010e070311060a0c0b100e0a060504060501090807030204091a011502011401030305030a0c020705100509031015090c121a01020c2403 74
    0x10389450341c014050f03aa818140402183c000a0034103440381078200920010407801c0681d511810110310042d0020b000d1001445a46041d0320f207409020350740026001e00c00e4040d00001c4c00d403203041c26066240e4000120510078480da0065201e050a03080c2c614074078014880c04000c00340e2000e400050500b104d400045401e0911a40f600c4008000c5101410490b05081072021b00038400c1d449070390302c1940340100000b4154000c0204d40100c600740c0b070150018618503000e01018000f0548210342c3c031507200b540e41d110301a4640312a8060141c4400b0b44540c03041e990340c043c3c00c4481c48415a440d5801d41c00041001a501804807503005030606004030b0b440038914000e9280031616007110703034401d40454407a02c0d0551b01501804804004408942602c01e14000c50b50403200030391521022010304c40805e0000c07031460307008580c8054181c5007901c54500301c503103c0e004075454001c88119a403200e00d4889610341e4100700c80003904004a404182000c0d40c400c02c0b074480d4421010300d1600c0ca0021002490302 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 639598345 1250 639597095 639597121
    0x3e010c02040504060b100f0516110a08060712020405060d0f270312050903070201050a09150806030c01080f34170a02040605041442070c0905 62
    0x258081d00c1030256007400e1602e040074017001a1030600030a6408429804c5502c80c2e4800d9582c05000d44540c1d2a0000f1101c0350400b80484440903070300700541c0d1070f40d401da5450b410410300081c00e028015221500300090014203078400300a5245a00b4018003050002e5501d042c00ca501d04944040005056190f920700d24014104103641219243d2507003420111101840034141c48242c42a600c2c044a000d02c44007020413540d05803220030055000b030000100650040c0e00420030751080d404c0c03000d011584c134420036040041d413200c4240054151020300225040401050700301c4030090804040d039240c4490713190000280100a00100513504c03c0340120714400e0702c15042d03441d05880e04107104203140d0380c0192829083c0c00c1030701884001100054104142d5200361030a0b20001d40d0340503d0075281911800f4042240741d41c07a03074001606c400701c1038205003031000c200240344596400800c480130f0441b10001c0017100c4901508030441000b558001074050f06030701e816640000d4002800f526404d02941d05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 639599595 1250 639598345 639598367
    0x130b090a0903170403050d0c0216120807050d03061805040201080604112703061810111603020d020111070b0c030a0b0d1406010b070206120603011b030204033e01 71
    0x1103c0d2a4806100605a00c98002c0c00c0c0072140708020700c2022800b14040365a45c0c454500c503075000308044801d01c2107001c0030325039028540c0541d698070305000c440c0d2203036030410b52461440c0000c60341e1004100108505aa071f2610710f00f07509001000701c1c0c0303026000a081c00d0700041007544180d64070241c003101004120284d40040d01e1107080c4141101071100010107031002001d65611901c03070710740054402420308918031042100e8a01518140b11b1040b00c0d08083e2000310200d00c0c00050600803d448500b050444001440c0070b030b4001c112401404c90003a00f101d418100e20311070340c801001248041124105216040300303101260945c2c85e56410254001420584403165101160718008014020303182c3d08030040e41e8640c41501c40c40c0e6a1900761840074442c101000b50003520911126503200c4103841095400b5401070000301300d480107201103685510f00c21140f01301295002c1030510610000181c280e1800d80380040c44800f10560626207001100040c14844820303160301d071400c04c180d00ca02c000c065 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 639600845 1250 639599595 639599627
    0x150f08191104091d010203010605040e04060f09030503040c1a0901270b03040501150303080402040507020705060c030d0506060702010c0f1502120f06040c051806040e040302030306130b090a0903 85
    0x28031540c03180b00f25409040d01050a01944c82c0e2901070303101c54001807084034121800ea0b00d510349080d00d840345c1d640e882d41d001001922030b0390740c8440304400b0303011600035104a607220755115540d0340703030501d040c2c1c1c03040c030f400e0300090309281c8400d1136100d0b01204403040310126031302401d00801503400c00d103468212003012045040000c000740c0c000909409024003542c02148190000c1c0040880c100004400107000d100107000209440041005410903900064010355a407050703880854441c40460150f41c0301c0c0001c40d1940e40700040c0c045010036a4440e407034000c0d070202c5245250031140d80008008071502d02c0040c054860072072028042184040e8404007001d00e030b0800303644860300c041b0301c000742800c215144020741e6543d000140280c5007511a07000d6224464565500304141500c42100e07640300720000c150029000c120206a110716140c03681c0c03240b0301c070750b00942d6640f41880900611003500340e00407007020b00781401e000199403440a100d60158031402c00003111207050404444480a0740381c041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 639602095 1250 639600845 639600847
    0x27031b140f030712080c03040618050d0806040b0312030a02030c13080a02010801050402130315140901091b0f1e15020f1908030a020706020919150f081911 68
    0x844510010001e8441240641c1e071000da60501184c09880110040b501c0314900142000050006141780c1e104100016203070100c1c03a40100d0319515103140c005001c00403c0890041410840540b5103401101c20440054020748401c2ca035002000700320b404090034843d840c540100021f1188100c20064a41100281403075208003541c901103140c84842110059002940350760002c10a414140200c4440000030314607140c55500e186c03100c8003484c45122040700e01944540c201207030001e02c00d10003806000300e000000341c44134032403500c7c9019508001d81490300d020040300c20001e40f800b1030051b03001c4620000844161401c80b81061000040607000507070080703090340c0540030855002400034070401601b8115440c1413814040319544850100740142102801c20010300c01c00190380150005a11a14015081c1a03c0400049114061020255221211490400400c1e01406252910b0b44841c2080e160420400704001c1c4209801481d8a62100040380c40700781d545495400580c0d0048507051036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 639603345 1250 639602095 639602113
    0x40c02071a0702100923091b09130e0d02210306030109020d0609060c140a0509030a020402120f060603130f050f0106080304060306150c020d1a01060327031b14 70
    0x19003040700900074284004403a11002006400b0301c85149001c480040c211102580c94284641c429208c0c41001c142004045c07103601031a440d00b01c5603c01d456450031010480c40e286200440c42e00c080c00c464042154895540c03003410a40721903031004055a0782c5d4806680e0b49c0d1b0000841d014107d414130007500318194030b40a1040c07102c55031000400c00d10551b0f041c030440f03c2810044859001000d0396056200d0200003201d2003c1c010300007007030310410290039600d0041c1355400103400ca8104401c02d00354600b9000030031246018040c800c550001e01200c0710f5082d4248565504030290012000401d1440d5040c1d0b2030041c05002c1207401d00000080d402802002e86074a410b41d00c83c5c10074070420300401c2c1005404160011001e8505440403140d0741c641c802140c064003007100301101413800b07031140f246455090700da4901908109001e0811520045056854880a580080c08084c45051100c11182c52580002d40c082c01c0248618440c000b02000000c1e9410911014403807250108000d21550340c0d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 639604595 1250 639603345 639603347
    0x1a06070c260607080907180f0c020a0b0903030f0105041d0d030f11070b07270b040e0f06030d030c0e090103050c0f030708060106120e010e0714040c02071a070210 71
    0x40161020a1010b8400765101e001c41654a060103a5410b034040d003004500f40581c000406415100d25131070180421031368142d044450032103119a25180068108000100620401030f40c0e8541080c200001146103240103040d511890034180a4a48125100c00124a502100d240540c07095404101920052130f400200903000b00342907001d10300b1290a04001e039010040e02e0003500d201542000814843c0c0c1c0da0164202d031001c642c040d000507171000080d110f007821112050b521015220201d81c02d550b07281000894007100c20000c188540c0489c0c85801c200c85510f002c43c120742110a50308010410394080d0200340c2d02d0440ca82540c03600080c14100002c11f00c2000205840503460582d102e91904820038103254440c130a86c082c0340c01d80c0d800003004010503803050030b044098441c1d000d00000d240c00d00042c11800c1d107500304d4a000c3c0a60000c0381c1480b6000c0c03141055082c90404441c1000040144580a9111002481152101440825801062000081254000c4d43c2c0100746a00d14010128 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 639605845 1250 639604595 639604649
    0xe070518090f150d080d0504051212010602010b0402070f02150d0f1a060702010c1709040f0b120712030305061207060c050d020606010e09091c1d041a06070c 69
    0xd1282a52420fa100088160401e1004200801d40000d500c3d0300e0500c8603044074010b0400500101c078984500a241d222500c1e2130800303403442c60780044000340c255160040017425241d94100310303071050384108060000a0105201410f869070b055030300c0e015203158a80c4198413030180c988401c460a0a00465000996855019485480e00114008070204101051021501948900902142502110320041030f9000700d0f1840a480f034030700c1203180050f100b0125095406201c2a0395205032201081101845e000d00140c400040000080440c1e0b03107003012150503144110300140034950303180d0200d00320341c5a003460005140b0302042180c800607642d4000800c510b41090041ea56405407942d10400c00d031020a81500420050752084090411602044006000981902c7c500e10519003048555802d5107142541182c0319200c0e42c00c40ba0017840c84041404c941880c040c0705614003003418800d8081414030f0030441c282900c11076100d900500e0601020500703904500a0751482c2000c41c201100010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 639607095 1250 639605845 639605851
    0x70b070c0b0a05041a040306110a0e0d080a0f020a050703030f080f0c0d021b1e070b120a0507020f061f0e0915091504051606090e070518090f 62
    0x114212089a603a01d420982405110900400141c0801040007400b071005038242004210b001203524040d900d5686800b110840b1100c01101d44021031051001c6400c42844544e41b4000e0324640504030703050740d5100b191300ca0305021000344190030300d00d803070140d200300700f1040300c0c0b80d01000300c4280c1512800d0250007010034405440002d011400026028503042daa024010400000902d0926140c014180c002e50400400b0300500310311404085602c0004000d001e01d0b001e02c05140d0300696038400011814a012a040324060000401120290350307540ca400641c82481e00e1000a481d03140d10700100e0502a400745a00c100e4800c013401e000c1c1046000d04401c1955034071a81032004181c1d84c080740d5500c2c107000c40300d103241c5410504200091503160b40d03070264051200350940713541c0f00e1a031910b01c1c6030800070b070b80c19111540201c02d031001c0c2205800c005405880c103400d10041030740c60700c03d1503500b035540100741000304000490980b8840320204400b00b11110010511840c83c64403030100c4200c1c400071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 639608345 1250 639607095 639607103
    0x204023f06060a05090d0618060b01020105010b0a0e0904020f031005060901050a030b16050408030409020301080c030705032e0501080a03141e1e030405241302010c060e070b07 77
    0xa4045900c030700d801d8080f65080802603c51a0030190510100f102262001e84c0c15142c8a8407109010b80e00b04c0107840e80038440340301e80c000040b200440f10009003182d105800802c00000108034021502d90010f802c00d03104603003100c01c040d01c2c0d40d90b4804501c0c800c10060307056401d44a4803034000061801500281e10a00342542e203201a42ea0b01d108000c40c068691102418010400012641c0d50019080700c0e5040101400d00502d0b0649d1403403001d16503403003944500201c40c1d0200052001d00018410001440360460040071100d040000003525190301d410403482406444166014010300070f50008000c404034282002070f5a95104155158500d080045000401c28204442d03042c00300d5003540e01240c41c08402110780c04002c490711f0091303800403c041358a0700303511003d103c48bd410311004500c20380c0314402411214010000f056400100003030100e11400d0039804000070300a5820710103074115024603141c88106114140000205459403100300c55028030380000c030314841d5145c01010341070301ca = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 639609595 1250 639608345 639608467
    0x6010305060610080103230304080705042027030a0c06020c041b050c0304030212010c110f21120702030910110c210d09030b01170a020402 61
    0x1007104001600b00d10414683c0490501001030010484c0c1d2042d0468400c251402080140700608407186590426402103405510581d820320450406019807003a440f00c9494010b00801e00c001a940f4a001c0e02420654030703690181c40c80e074603c402144040f000840601a1040344a4600344002261040e006010161083d070109410904180c803465070000301a40f004400f10a05940489559100203140b104070b1006001c0400582ea039030074401c2c1100d81c81400069030841d1508040d00410f64903600341c0b1242c0113003224101d07012020406449070300c3c5d40c0c81080803030060700d0a803903054001c520002000304220000c000b10160000700801103410111030307000d4100c0f04080c0c12559200b48a18080c1c191b04006e02501c840e080003a540500d0300038446400c44800702d186a0f2600c0c080c5403004000c00100c9161041040c4680c280c0898054910100c005104a6181c0c0050355246205000240070710b90016080c212452243e045070780102517400d120b4050b9004410f8003c509801c21282a90111 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 639610845 1250 639609595 639609601
    0xd050405190b241e030c0402030a020c061e010905040f14070513022505010905030d0b0f011119050309030d030b030105090a020a03080d0b13290d17040b03090601030506 74
    0x28416040719101c90001c00c04070103080071410184c1400d4540e4046a094030500b000c484450362680003440c894015802c00584800181d030304a454440040d03c60b1f0200d00c800d00d401841190b114442d1819034040904c040f4032a151840d0034080362103c00c501402040484010900796030010481d1400c44804550506028880340c00e01c000720300c161602c059040e010100f4000c000d03201900c460f05002d002c0e030000650a511a199103007036038011080c1410460b580e170039102003840d140c070114074a280286000041c48450424085d030b91788400300345102d403101098140d410001c0c20012600028405803d07501002c81100004d0701404504030302a20079420000010760a220000f017201066030010502815580b03103850325100c2d80d1000f41c4041d491512000094102d403224542020019640000080e0005e11416030100050300042e8040e80d0b43c24491041c44940d81e24001d551195800801c0c541007146541030b109442c0c4582e5000b6071240c0c80120270424240c5022035080e040b00e00810680340b141e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 639612095 1250 639610845 639610891
    0x10306021e0d0c080a1b030f090203030417070e042307030525081207150b09072c01121109030a0c03230607080405010e06040803010906090608030d050405190b 70
    0x1d0340415036152005154512011203d110303401231a00009410400650106c1603000302c1d00315405604640392044805040b1245604200184d80007410003910002d0ad6040036507800e6400e800c0d42107100020700010b00300140d01c0c00207020032002507a00c082103614600c210790401410041c1c2280114804d107142000003000c013004240698013408248200e45858825610014210386817035000500030381d58010617419403524200c1c0350154045032602200c074800207407100c14802c0740300e544580140c54084c000c241c40c1d0300429540c810300000751010440104480c400411401407203405545841070061b400180803500d200042641e008442221180d040f9a200645000718010005108c1e8030000014200c0b44c454007880e03402030b104500118410b007161510f03a00e00001135a082da072543c0004010003a040c8144602c80042203c000300340055403034a1155a124010b103441e034070440c0e49400c0000c0c2040400e00604074182907e100c0041005403d0a09800c034000480e052205100f000494940782 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 639613345 1250 639612095 639612101
    0x117510108010c11030d110f03010617070519200102040e100e15042a02010506040c140409090323070308070309021320070f111206010306021e0d0c080a 67
    0x46244c04004525106c64901d00c00001d0a40c0126040f03070600070b03c0041000a00d520055000304040d0340d40d00b1009490701c201c9480d28402800310024068100003105517688040b41e484040b001c0c505040444640580d4000e02540ca80440a01d60b540300007400b0950144684419002d1000350001468940c1c0b01c10416403001c106640d0a901401141c01503c0c003480e050304031140c01442c0d11740783d6a0503100a041948400320395004800513075110b00400c501c6042c070740300e4003403000d080f8900704401021209a60340719100390b000304c16095032035001c80300926004a4007000e8003d0150414060306041340c00112460300031080840000d10720301e0100b54507901c203000d40440b058005060b0210003c02c031366160020030b043c0c46e424281000741c924801004107880b0203002d8060103860710980c1c000c620b180c007082c5809104080c80c89494501400f40d41e81000160702410340354400401a601c4070074500030108250054480c1d1140c08000415040e01146504240b1100d409501c820780103455880ca41000c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 639614595 1250 639613345 639613367
    0x1202030705061306094404061101090210020601091401050924030d051b0f120c01140c070506060907050a0309290117510108010c 57
    0x2040c1d10480100c3c14101d6030280c40b40c1600d01c501c0c0f00085840b40c95a0700c04003a001c00f4080c03100a805401c0709400f40e003180819960381c600c40d981140707655490004044146c005d90045808004c001420401c14000951212600d503400900080141104050003565404240144003545080c43c04a075a102c442581c01c82c10388000078501c004035075506401c502100c51040002104900c03214074051075031800d01c2075800c510b607140c0e030b43c0c1da48a4462104084c08090700b2a90002540310038600000c807440440c10380c04403440044442c0c2c0e90504070403014050407600d042498090812010f00111300c071004010021140305900f5070b41d01d46da840c41009402002107401c0808520200030b1240454820f031b20401d0401e1180d0203140007642c941a0072400241d012810b0780c1c03407900141c01400703c13401c101c13755074210801600400701520707008500f000c001103400804020030004031403820030702507400341a00d44d2806480006030300803200c2080d0000f15028030429030b255203000300016a8500c11001c40d49 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 639615845 1250 639614595 639614603
    0x30d0207150509061209060618010f0306091a1e01050d0b04030807030204122607030903110a0b030406090204150b031b160602030a0b0105120f04080c010606090312020307 75
    0x900d102040c2e440c0d91090081591001003003080020f000c280030b00d4940101d099000500e410300d00402441444084040d0b07052000c8600c000401c000c10b8030308480c2094035407116010401e2802403500f0111000d02d0011004545101000c10080c411307010000a07100102541c510201c2e641c0d40284540302844c09809041e01d801e8500140200b80100300481d000445860010724090303460440244403290210201d40300301d000c42c3e13460003070354040800010ba00511134074240390046995018003251143d1000804144409807c03076110361303669501000402c500070b18660b49107407502e00380c0d00078041e03100200e10a0b03141107442012070b541080d118041c0c4400492107403854445c40c0307400b082e03c1c00110b001d500003642004803082c800034131084920110704c41c10025803241800340c0010207650307090b025a4100300041c402740300d50364131240710590041420400d031081a10b45083c8400a8032610031000802d40c01e206000600c1ca600c18000f0044034010701300e00562981d403100c100d03202d10900f44054 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 639617095 1250 639615845 639615869
    0x40b0c0f090906011806050c1b06040909020a0b040e0402121f09230a1a07120c090306061401081308190509041a011b05060705090d0b0c09030d0207 65
    0x20140c0c02d0002100e80c00c4401414106030035450410740200c56807658100030f001410124640c03040303403020030488079104481d000c04424900c4a60202d0104d0089201e50060300307858440031010740d00c411460310068101045d14907a116110f100803001800c0541d8100d0080352100c07809041d1000110f42038118805812280000d510000529000303070003040402c0e203500004a06111006c21081000300d11085207a000c1d086034610307401c0a06648a461410100b940803610030009416481441c00543c05000c200000760f0b03d000702000c5550613840d400c010141842d01380c0c00f0460641e13140c100842484241c6c0ea40d20390f5560807051400322904000c00920742c0000303205120301080300c0c00250215184900e041420000070000240c181e8100c50940c0e0441c0c850940c031803540e56070000780300290b02811140d0740c0c03546906a80701a40c80c1d0303004260504024007c41c0f100400c0d5034075448523078842d42014802c04c0c1810f00024286c056400b160303600f8442e11403182071309103140c000715180381126045401c1d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 639618345 1250 639617095 639617107
    0x50402130905010b030102071208010f03030f03230109021801020a020906040e030c060a052d07110106031703010f050901031709010302160c03170c2d03070605040b0c0f 74
    0x154000d0407500004807415500c502100c2c406031400d1000d056a103000c1c940d80c03c0809040d0501406650041e00027081142418030180042500329a41d490042d080c4d1600003024940520b8040849c603001d5040c0034911050b40001500391050f80150074083d141070110810341c1e00080040ea03460005d141c00a4001d09403000042041c40e0030361046882c05440403c0d2807500ea500b00605062a5080303c0300c03004c540c2c0e02c0040c03201c40c00c240d0070b180d1140c99044c585645c201c03445052215581000410020800800201501d17082c0020340200d00255841115209102c00c81441d641a640090180d46e6944101c103500184500e00000503a0480c0e0b002520240c41714242c0b0300c0c41c03c441d405000c4080c1456001c11512400228080510031914059180814000d00310300c1c0103c01c03107516040c50750103e41c0500502401a42c04a1026404083d20b03070100001260403c240c0181080c03104180640e00004c107140d41400703c0c41e00150300c01c0344562a0a041c9540344c0c0e074030015a0040f4503120310442c0082c042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 639619595 1250 639618345 639618379
    0x207050d1707060501030510143c01031202010902010504170703020d050102090f04021326071d07031401060c020a0906080f0c06031302060d06030503040f1503050402 73
    0x40c0006090103607a000440408110351404980d020a60885020f0341c1d034001081489000e100c40052081c0341c407000d0000c0c007100050340c2d84200016108841c005040015003a02511562102c2d000110481c1d4010404143c002c0d8881a05000d101c1501e4018a1307409080c420745c81031041c1003203598141c445a0815041c115001d0b01ca16410a0101c3d0510880d0710100141eaa10b41280b448107100d01c00140e134034009502401103415218040f80d0065005111107913008051081403401e46420a41400c0460f900940c40c0d103640c070580d40005150300400c08080b5002c4092072906406a200f0b504002007910f808204808070780b02c04242d0085074a40500500c415031260b41c0c2818800d00041401484039110012881114050b034041007196000c080700060030101030000050012085582c00d05500e0300e21850b2020640c1c10200920131000050101d15904655118501858000085135295034541030008030540c0c1d01d014101071041503581000700180701e80a0184155409081092402c00c0200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 639620845 1250 639619595 639619609
    0x40305070309080304180c0807120b0f091602120c0307080307030e0f0304050a0b12150312041409090307031205070923150412110d060914120a020705 66
    0x404a00300700c102d2074001480141040508040d15010102d5070901044010000443c2c01c444907030780512103070008004582c1d41204104218503c034940100e8403061403000245441440c0c030a8039484030b4035401b48104040140d00c2e480100380e05401f04c4865000c01d030f44121180c040d245d04800c19510410006000450f5500a960030001e80d04020032180280c0000905219101064240652011500f0003081ca040041c5400400c8180e44052070114100340042480358020624401070440c241381c00c0321624100140d4240031003880c004c0340c0f81c50316055000b80004400e100c0da44071340031500c08602d503100c4c04011610304e16415180c1d0303500c0d86032148983c0c020f0a40240f4110500902c4000014014000c0c0000320305240403c089181c1c81c0070100800481e082840030409040c10b0510080c4104414250004081c0d40c00144030621080c0c000002068451140c5004101e241002c840c1780c2004034a40900b9540801041911a034490096054030706020b5805030000507480068100300a0070a40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 639622095 1250 639620845 639620857
    0x1a06040b09060706061d071d0604150e12030301050f040b01020307030e011803051629090402191d060a0e010809030d0509060a0b010c120e030703060c11061509040305 73
    0xf004030705550382c0c03d0b84a1081d085910400d006c05c0b62801009081a884058024650728080c6150541807500020980500844c051658031900c90100010440e010303080c1902214001403100c3c0c0c2e0b204203aa0090380301e81080c40b450780100303468880c0074204e24050155105441c010b900441c2003c90300c2c0c400f241e40041894005041c40702e2410076400403501e014040d00910300400c0200203040314904201e460f0728140d03020365010b03220b8001c01038072140d8080b42d0207144281c2c5442d45440c2e400c2140003070002c4c8071b43c02c00122000905440494802c0e0080c6140240107507940e103080384140c848090282c06c1c0b00319445a40007410340740030800258003445940d40c0004400b41141e080251003031101007180c03019101801643d1044040204801c0140104c4c525040c0238601400a003d080d901c1c0410b42820101e81c1d000d100c20503203104c5440c1c03400c00c500c40045070030510030b00408000e110054a0038510715401c040700e0180c80c00096481000580c00c1d103c0d82e00c05030402c00301d80c0d121788085070b41d90404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 639623345 1250 639622095 639622103
    0x210e07171908091305161106010605070b0c0d1505010806040b03031b01090b0112020901080a030503010603020a0c0b01091a0d17070c030b010b04050a0e0f15041e1a06040b090607 78
    0x1800780413145010510982d0320034401100324880301802c0c6107000d40b0016801c0c0f030700e100d01d034130007070050011a0b07000c0280c03040c2c0d551103072081800e03860710340c1c43d25010f00801d80c0803070b21140b0349034901d540000c1089082c0c0840300e0030303252901a5210301c0240410785908000d4190560710801c010040340780e05c00305034250251a24000242a5000d5940710100c074000e91243c00082d0300514400194074107482d0481c01000c0c90001000580c00351b60303018003180014820201803590200b60343c01e80d503000310b0680544a60101d2030490542c2c40300c0d80c034401070a48290200d4244402c024503001818050705800c1403d8101c48620380d0000842444016507003c19412140354400480000c0002c800a1200e40071b082182c4802c3e440f00e08110130b110181c4501c0c0e2064403195444418404202d58940706181c00c20581385042d00d02514081c0420043d2825201003a07800442d04212150030006501c9041c00ba80c001304400700703001c5800200012401140544281c03c0d40402414180d883e00d2401410081d200d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 639624595 1250 639623345 639623359
    0x603060406030b100305070e100e0c04031202061501030b03030301031502040317090108060f10080405030408030a1206240305041115030f100f0501210e0717190809 72
    0x803507440c840e49070800c4d181e01100013416601072081040911190014029203c851522444e0010344080110071501c112211181d00001190340000e402040350007854000c14018480e00801c14025900d9600b04e59102036200c513008000000c3d07200740070380b140c9404000c3c01141181d0071600c2d04100100101c0c19414591390070000080007a080c1d000c0c852000c00c03603030a0039451b017100e10005091319200401c0b06206101d13601503d80c6a035581e14086900d0b0415251180307496a0745c0c41c0451a500c0b40fa00002024071000c295440901d078001c1031041040e0440b5020311205642c0e50311583e1024031803031225a41d05a0a40444266200307030f0225500a02079903505540b0005080883e24072200020f008840d00800400c0001d02402050055040503601030819001440c000c0c01c1081580e190107858108038003211204881803583d6042c01c54904180c000b0010800c2e000c01c003942e075442d00d201d0a860300c40c010340f441c0c1581c440071841003001c00d42e8107491032040c201e60703441400b40c0e84170403401c55000030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 639625845 1250 639624595 639624599
    0x806151c0e06071706130f14010f180c050f0c0109020603040b0402042a03020f0405041515020f07050f03030c2d0319031d161d090a020603060406 64
    0x140501507100300201803000b501d007605010100401d002d114900508104c9000c0d010b12040381c58090613464091180d0100051401108100501415030643c020b900d07640d024001054200040d5106021120083e031040252041443c800d026160805000c0000c10002c1c01031442d00380c910b40080c40c40c1c0b00d42d03900004201005600042d0300d03820076102070320011014420030086043c18070404071800e0b80ca00700d03030040301086045054000080700f55003080540200703d40c6101c144030829030f40071f8a0000c00038414800b0080818500d0306452082e03c200c61010034803085181c0c00440c2900303210881101a20b0341d5070811092000d000c0131842ca03079805210400400c062050140500300611125a444108800d84a10201ca03260405800420581c200304040382e103090007600005403011181c100800d6010011134103a00c03030241c0e1806009103004403030710105400403605008090742c40410000c583c2480000d030054014404a4614a10f5800281a08c000d480c00d28082c41c1d0004008101041103a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 639627095 1250 639625845 639625897
    0xb06031501053c0705071e03020d05010507030506180106210f0509120a05090f150304030f020706030b03060601111c03020702040c050a0c060f02120c0a0f080615 71
    0x3004106034041c00000310100640c00e103400403c0810048840e203009420304c140c0e51181a116010307441503144141800554007a030030f405080110065400400003603498902d802d0090203480200c0344240085c0c60080040c0c01741c60080b40003100401c00d0700b03244503d0780c20101c080d203110700c405055248802c03075042540c0c0110001e0160507031100300000f0228050a00304c424a107040c14001502031044401e104241d004d9600505032120648105c3e4040d42803603004c1c000c075102039404441c015000000100300020300d90400200d54804046a08443d00d095580004900f103c16003110940d064101d100030412030f40c0f2444e030108200c41e2000075150440001400b40a600e00700c550014042034001c0b03046005d41c03070310348980c0c41c0702c0c5030608150741b829640303400041048a1801009048a07510101c40310f440004ea410396140b6491032001000a04102c89408110b4124521030780006107200d000480782031041003664002d04019143c2d1894041d52000a4100e03040300a5400c03151203400701d00d141036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 639628345 1250 639627095 639627127
    0x18070608060414070c0c0f0b0d05060a05030a0c0e0a0c09030f02012a0b0a020c0a0f0507050316090f0c021e010e100e070e07020718020d05040b01050102100b0603150105 74
    0x51a03640d210318600c13051714907000c252520590711412502203100e204019201e2120201e500303140e0000c500003115642c3c540003070032503213035600155018030800003940c04000c40300340094199140b0603400405599210180c00c00d032035101c503908000403803440e400c0000555003806040410300c1410702c0f100d04040c00e1580442c50510b40c40d03080103544004030b000b003440040f00c03240c0d0b040a80310320103501c0c00c50158003141d5510301450340242841a0810b200e024800b0030f00024010700f40042c01c3d01d401440850400c5000c401e5400341c0a444e6244c66080300b009002c51143c44082c00240c1c001d0410b1610020000d040c0442e41c040c15226552203040c203040c10b110500c0300140055120f840020407080400e007179454061030b81c104072030583c0380405010105800050741070403030785501030403075010584040c1c50001c1c3c041e6403a14045181840148010800c000091606a440030f03070072548411090070300c1c2002d6580300301e0510b411407010400b043c00000303000c0404980905c1030501030700e0308040342000105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 639629595 1250 639628345 639628351
    0x4050a1d030919121101121a100507150b0604170a11100203030a0510091506031107030815040e0a0804090c08160e01020c1206040b18070608060414 65
    0x61900002412074080c90110150003c242d007031031400c000c0e1070070104902e0781c0001c152000780400c82c1880c01c094142e03207d43c0140c1c511100c0c81100f405800c00550f2148600f00320440307214070842000d05400c150520074004c2c0c0d980d407078102050b042c95100800303100d002480030b0000e850b00700b07004005c0800c1c5402d0818100180c400050b0040009000c0d9003400300d0318a044088035803040c1c00c0d610b0f08100c1c0c03039400010f480c0c0000c084540000e5644510405841c6000240d0010400342d0401e4200c0041414140c201c074200d0386562401c0c010300400310103900c054820380b6001404145048041400c400446480b000f50600c0540000355018001380400d2901c4154801200c034031718001802d000081c81c0c3d0088040c1a0810300341001542030050200404007084800e10081203030183c00110310f030303208101c07004402c0e5020b0820704103c40f89140750764039050100c506132003e1801c600401c14000c8031580030710303102403864058040d00d4282041200c806401070807031548036880e40d44a926069085400b580 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 639630845 1250 639629595 639629651
    0x1504020c01090b04060b060a0804140307020d030f021c0f03090813032609060a1101090206040603200403050307020111031e03190e060a0e070e090c0a0f060e04050a 72
    0x10311328107841d100c0e0560360821200e600581050002030341b4550010901504a036100c480d400d2000c210504282c9180076070003001c0c0d400980b51a40341d05168200c0c0380c03064004110b5007540c03000368800415150341e682036401d400c002074000030b02c1010070b4402c2c0d0060742d01920070b10b00d4601d0482d2084002e0500301e401d410544805489207103a02c000c00900c0b08016008100c0c80025080c0422030001800074000c5000c51403c1c020030b08920f0311030300800c0d4092410142c0c0140a10344071600d580c00180103003240007589001d00031000f040c81201e003d5909440480383d029000311304e0940e00d40c0c0116141601c444001482d84400e0000c03602500f001680e100c1c1c094110740e82c00c1d03100d00e4100c0f851080c2040f41640130a4040c41c1118038410b0650103e0340640c0080c000001240000e034143d100303807a00406c0d900c00d890380c070441000d000c030ba5500802c40c0742c0c009201701c59003140e0940318050184440d145100f0000441d035650100403050409420483e4021205540000d25201c1c081d10b01401030040200c2103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 639632095 1250 639630845 639630863
    0xe0a021e03030d11031e06010e090a09051005190e0304030f05070b18010815010816170f0703050612060a1d011a04051018020306120a0f0b1e1504020c0109 68
    0x20003041b1038404c9203143d00c4c3c4116002d14440c10f00c6000641413070400500c8a004034414000a0b14511140d0400e072075079644a01210000c8003905007140c000c003002c0d20041e02035025244a5601c0e0030003402000c44244548001d5494186140d030f60140344001144c0895980c01602c4001626103e003c000e03043c2030b21280c82041c0e00c2440440010000c0c0f00060010100034100f07600011030380d80c0943e0480c1e00c803611002c04600c001c4851400c0c2c50034103021440c0840d0070201020426403818081c40e103401002c403920b081c802c40d2503020811082d0710b8086c44e8000107038415000240d48002a070441070b03451041c80724041c0036840c10002582554481c0d40d04984c40030322901c0c649005d0402d1b00c10158000c407194400b615060070312031481c0c80684011451080070b41c0100118005030b4407100031000c4101c0e600c084420803005031410f0380c0140000c0b98140c0d9522115400140d81ca11f28000c20000403004118030ba10f1995450800e034004048440450340060b824004000240000d106241866002d0f034550 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 639633345 1250 639632095 639632101
    0x60304021c03080105031c020c190b0703092306030708130206030103030503040b01060f02070306050c1204120e030d09061b0b15040506060c0a0206211003060e0a021e03030d1103 78
    0x106141074070282140c82140d007c80840044aa8045254281280111005005201c0744541c14981d081c4941085224680020b900d10801d900a2800012100020080c411940003040342c5004000e00f61241600000100001001d00b8880c04c1c000b540600c0380625a941c215541c3c000c2600d0390401d030001c8020400010a0005200f012140b0a0040c0160300d400c60035602c0b000c400039141c3c0d40510000b031a0326140c0e00414596500c5000b0b8810a8070040d18442c50351525041c903c074580440032403040480d10300324500703402e401c011031070911040070760300c41c490010300d440f008480700090b0b00c189040140c40100008001080720841602400c28107106055083c80c0808000840c0d101400d598030070203041061003441e690201e4664003d43d012200c5d6622002010040540c0240c3e04019100d08a10340c0100844200c441d06590190b134000c1100308803030a0082e103419600c2d5050321010b1b5100c070084402034a8000140c5455220050240030b9905145000414105803141d0307903800c44041c0808420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 639634595 1250 639633345 639633349
    0x1606080f0906070e060f0c03070f0308011211090403050d0f0f062705100807090507080a0504050a080903012415210209010302070f05011512050705060304021c03080105 74
    0x200503080071070080036220b40e0800100c00761610121610580c00391802003a020004442c000c01c0d00c14001069042c1c03a5615064500a58184132a1101702c4c0440c0740030740049070280400e03100b481115402000d002c0c042c9040d40820400880044c070842c20000104003440c4180150b004507142c442000c200492884120b4954406648003a0003844084682d502500707440c510003441c00380c40392540c44000480d52600c01108000d4007481e04840300314460b80704005031150b800d50110380700f07942982c4da400040c0c407012445001e9035415100601554000c40c1c40b1350100303c1420060241540c003e000081d0304940d4440075141960310300d01d031000206144020802e20046000e034500650641c07600d031030880314074000307034108121040c00c0000e03c1c1ea002c81c41d0344150b4020b604403a102d1760005c4042607042e403245402c90180036282c0f091138106110301d00000760002285c035000b0039154040042c0c00c007203040409010190304001e00590340b0442c01c1c2841050900b00c0c902d00042e580c020380c2c59055960400742 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 639635845 1250 639634595 639634621
    0xb0c2e0216120e01050708070f05070b040603060e090a12051b030705010b04140a0917040305010b03100209010504060c11060301030c030b090c0a0b03060102150114030c0d03051b160608 81
    0x20b100c10034420f182c02200d4082c0c3e4813900312000f55500c490706035100ca500381003540148140316401040c500c0740308004a00905140040e000b2120b950760207000c155240d030a000c010328420f1f59180e010750720540300078002803201d0944803212801480c00d18280703107050171020642c66018007100801d070400543c04d0180042130085242618013070340c051000528141c1d030300c1e00701d04004181601e0141d403010003008200e981406546604500300d999034503503860342001402003200300136080c417910480c0c0c201020031029000f070380e00b4040305071103603401c2510381001a10b106202c01c001f290140b8070512800c2d11a0748502c040c41c06140100318602089045241c0420300040207402030300f0b40d90200c0c410581c1c40c0c0c4c03107044200075514101c0e51640c0b26198600140d1501980554102200440301d0010614423020b11039400c20f07100440031501001095410f00c20fa070704032040050b0000d0001c102990740324092203d1903e5005441048400a40384222055608031090704114001801c00381070045085410b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 639637095 1250 639635845 639635873
    0x1015080613030801170a05030a05042112050c070b130501170c070809043309020c060c0318010501081b0303031e070507051e01060b0c2e0216 62
    0x1044000001c07040d48014200102c14030402c104081c0440c0c000d418004103002440c641c681c070204503a20380079182c0000d40160440d010300c1c2c03000c9400f070b5041002080c0303480148a400f908002101d01d81d6110301c10880321036000f90a84079070b510550300000303203900f0620b00816170b20740b214100c00052402d0600050000b00700c0d00c07a24003085040d2040c40790402c1c228048446882c1e1080c1c22940d40c4618401081c064a0207402031b82c01101c400001980343e00c00344c40c5c100980d90f0015401c04883e92260034260880c040c000c600c7c0960390100002595003a1032000440d0400141245092030851070700b525030966000f47c0005080c0c0d00000301400c104d0407002c0b80c41d040d20204502450075441c2c10700c40c0003203042070b00490505806008001ca41494001d80480788815002400d468030984941260202001c50202d94082503107001d10019008000b0000c0d0f800001810015103161070f480a2515042c01448600e40c2240c0c807469002011214a84000e001c120040c1a20081c034442074201092191090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 639638345 1250 639637095 639637111
    0x10b100203040e1902161101020d080a0e0a080307050a1d0d02040903030209131a0103060e0705090102070f12171306111002040b0d0c0c080a1110150806 67
    0x1012101105039004400d6a059601c0d0404840031641c0c3c0a00000030f0258000060045038400541c0603030317002c00d043c103a0400d14000d480d0200e46c0000708004a9403001e00c1100d65000500d00004200300750b215400207004603042d48112807618a0b50707280c02140f40d006482c500702044001917001652900b20100c10049014034110850f04005880811070702c11100720000e119540e1074200070101030199050f01d564107005003140d08031900700e58203000104540d00304444d06010104000010b98400d010768000d41d901c0008880303c0d41c94010b4103a425400c00c00c000ca0541c0030304c800108458071000c4400c4003d0100030703100c0c4c1034102c81f400c01e81140307001000c0d81c807215001003011544521030301c000102200c4080c50b0411522509489860910390b41003810325a50b800000c0011710901c402d8007821182000f8070003044208081c401c20740b540003c41e40d000706550310a00011148a00500d1b14441c0307441d5210a0321014800b1034619800c0b602404041c0402d04658002840002001c22580b90b0210348 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 639639595 1250 639638345 639638359
    0x301031106122a040f030b060603040f0201120207080307170a15180209120a0c0909051209011701060210060803040f03080a110607030902130b0108040201031d03070c030302010b 78
    0x4494036140780d0b0380d000f0101d1003202014540c02c1618034010b480c544800301c604003819200c0c0e4503000c00034001d01e4584070955901880c003012a8191510408503801203074003019010710f1161550040d1005003019a0b02070791a9401e104070f03008610f5402c0254404c1d0810394480002032405d040c005a42c010140212034500e01d440b21254820120010fa070003900e40000c41c5c442c0c1c1d014000d03084d00203441800b0003150440c1008842414011000602c00901e40c42400c5100f9000d8880366400212840c0400c00303891580a00b5040c5800141c200040c40c45400c10315056410868041071140c68910a034030010040e4845022424035402c0c9200d284050074110020f140760610b09005044285a140000b03000120000b914801017030040007103100c4000042e084e1451450510b101400038000c01c00240d010b02180888020806031600c5035481c4000d05842c3c41445072241e030011401403124880d144020030f000d60040755020300401c0a0304c081441983c60041c1d15045140003802d640c2c60350f00040c09891 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 639640845 1250 639639595 639639607
    0x30a0603061b0903060b031f020405120d1b15020c07080d050a090b09180c0d1b1d1926010b22020d0c120b0a05130509031902030301031106 61
    0x1a03ca400c503c1243c0c0c2010700455000c46110000b41050f01c1c20142940c42040407061108281d11500644106d850486020041d15403d00d01a51a929215568000a490151a1005540e038024882a014040c220f4404514440007006040b17a00003415198554032000c4100580442042642c3c0c420001c1e240c01401d0880d02103002e809442d090003102c0408001103000c01468468200da240507805036110103040d03003003101021006501c041d840c044501d003821503103070f110030440150440302d0426903100251003001d00342c2000e00b0078a000900c0e0748038111980000c0b04000040c14a00944151403242604200202001500f902d8140b0320f8000b0782d04141100341c0707940c1c44082b101c0007441105809030b0802405c008040c000d01c248034402a007a071034200006d43c0581c1c02400810307200d052040401000c2a00020046038028034428542c1c842c0e154030a850f214800780d046917402c5918801184d0401d031000300301400401c01c83c0b802c100141d10100040051140511508050b03820039902685041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 639642095 1250 639640845 639640847
    0x4180b010e0a030201110a08120709050324151201021308060105100c0602120c0a171b0f1603051c060305100b0111070f151b1e08030a0603061b 63
    0x342c0c0301d200107810300c0700144110034050424000452a00d40c854030041e615045186840b82d040b500b0354007500000c000b400c010445040c00102010701c410850340b501405080344400e0046080018242e00a540000c1c82c0e04e090b90f12070005041945003040009a10355407206421044100d09078001141a4804c10040150392141d021210903026249810b004c2c01e400c078180100a440b903080040d600e45002e008000c020b022030300c040d100c182e40f595101d42140760006400701c00703c2d03000e403000000c082001014004006040c8001c10340d0303011644c1080c2c20508814402e03d4601001c05041e00400c4002404a07118003000c403a040080c1e208690402c540303821074940b255a5a040d00d0304590155441410350003d1307024421601d107112070711003290721403522080760803240513191241e11340c0c0f0042940c86000f400e000b0442c034031440c4d44c43da001004c00c14061300d80603408544e0300811414501c5903040d01006c90080c2d00198816801c050001c6219480e40c54940125107101c0a080b200a2242c800c0741501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 639643345 1250 639642095 639642109
    0x6090d060c02010c051806070c0f14011e0f1107030506010e100602030a020c0d11041805071d0f0a02190507110d240f090c05030f060f0403030e03090604180b010e 71
    0x110320142d40f41601c4596602c9c00800700c3c2d8064002038412911601d0008000d42d82030203c200c2070000380e841024150741340f4a4001442200c141e180c01060130300c60035442c0e544c81201b00078580b501e514204c80d54540d0302d03114941829001c2c2c00c07900d50b10321410200300c0c982c9110301d580c500620542c0300031031034880035240080d203840036803c015114000040e42802404040104240c261800500811040d082c406a44e0401ca015000840301402000e80000d0f0fa507200d400300001c141e80d0a10650305a030b90b1740d8201045c844e4001e111080c0c16509101c226061284180c24250040542d241c41c0d650b42d100e4106003404010b882c1040f403080200b40c5140c0300054000c2c0410901110500c08000719899081e034a10281c1030007240b1580306460212098140050200300d5400c030740040d025105203184c1c00400948401c000c1f00e03818086656240846c00091081e8402185003101c00240c1c1c8c00d003411180040c80300c0d4030680c00314900180c0b007007400000000c40d03c6030144c0100242004000705143d24085404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 639644595 1250 639643345 639643387
    0xc020105090c012615220506040c091802131d01151e11120d0f0506010e0d06060305061006110109020307140307030b09062d011406090d060c02010c05 66
    0x402d2103030304c0800d442c0c50661101546900006240c1e13240e01002d003900e03908008180c0f000d05107880c10003001c03030328504143c03080401d03034891030340c40c44252401e00038040c500b8101d521203c1107503982048860310009038042d00c074020740803d20884040c0c014401c1c015040d42e0041c1c00c15040d0baa0408142d2208940101102c0c0c40c1054244440010110303000302070f925101070b9083c989050103500900084150001d004008803901410100075441c000644503048440843d840c501045c01d00f04290202e20700108c41c003051520400c1d0214a0588035520f042c1030541c2a10610200c90303510000b44440b5410900700f401c0190030030002c0002c01a903800007541c03a0341500c61504c0c55600e004507003959403010f201c040302440d003140c80c440f8682014085503076540c2d4202c500340e00c2d8889000c00310301a500c105c00c8031690381010f070149404503400c1c2401650000e50591180c0da02c940104003409031522885a1a00300701d008901c0010320101e0b0a10103400d444140ca250002c00c02d04001401c004e0803201d10340c1e14 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 639645845 1250 639644595 639644657
    0x60702011404140f0f0f010c110c0103180f15060e0412080c0d05090a05010509031e0a05090d0b04020f190b09030c060c010c0f050f030a0509030d0c020105090c01 71
    0x60f5408005a04500340941802451010301401100f40d0682000040034081c0d0b90380d0400030068005052011100c00003082c1d664030f001d0700b040b11040c0326980300350008210100402410140c010041c1e40341c081e074100d0103100719525403021078051040c1e02076114080041103070700400c0d03200707140070341d00c03240207203107880c0107806000800000c52610b00411098074050074005104111605060004503038440c040d00d0300310351070741c00c101c0000d14000307002c000c0c2c072000301a0840f800d0302d2101804071912560400c0d801401007180900ca40304645c0d0350f074401041010301641304010b0a040c14018421180d0b4a8a40180100c41154065036052040e00e110004c031100000d5141d212030001c400a403e01e2101d680a603030101000c208480303061410b620280c00d144840c1c4612034003e00b814000d440500442003100070210040c0001a09101240c01c80c940c0b0003180c034262071604842c40075440889c1c44812100005030b555108111552108004031a543e413001d0038a04031180304140110b1120442c0c02242c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 639647095 1250 639645845 639645863
    0x921070809090a02042d0b0a0503010b0d0212071806020118030309140a0524040201140711130608010605030309030a121101090303020d0b12071e1a090102060702011404 74
    0x781000310513415a0b000e010302c44840d6a0703c1c50740c50b0581c0c40300901c41e2403d0f98a841103400024002c440e0000302c51400703000da12080d0a580c0b0741925a074041c3c1003501107480c090340030402081d12344100400a440340c1e045440c4d0310140f00701c0c2d5403070742c80c031403003d401c05025680b426807035002c1120b07020720003039a50390326103400714522440b80307010010030103940a031011500c00c1008401c10000d02081c0b00e40f17900c0c00c60300c040c460003000d41c8a01c00502d00a5034007034042032841000b224440341080081a203035019050564000c80c0130004605aa000040c14411050b51b40c5828080c4400a02500c4001c0c40c0071401103050814050000e500c07800362440040c1180242001443c00310f014103c0e8035043c50703540000300081c01d15414054040e5000e0060403804910708007505079030b0b1034404041160b0041d441c0c02001001e0600f0a540f841e0041e0100310410120780002c00070f40523000e5140d0341d4032b0030304c0c80090b81c0d00c4628510000e4a4400040d00080969060102740c5900c00111344c14036603c40c0d0402c0d001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 639648345 1250 639647095 639647101
    0x90302060a1508010603081b0c060301030b091c1823060c0a0b042306040506010b091c050a0501050606041212030f020a03050601090909030905130e06092107080909 72
    0x5265082ca03698803458107542006000000d000111029101050541c45580310042604050580728440104034030b46c00741044c8014030110714000700c40750f80070400c18210740d0110301c468217024681d9642103031500000d6000b10242030b0100030981180040c201ea04090003051411015074642941c028506800b480011030221850001000341480707042d040a03003044a1300b0a41030010120105101d0341807066250b045400310210001111841590050040c0400e83d0920860304640c2d40300403407295100d909256103460084a1095030514144948014045001707540380c0b4030b0a6510051201c1d101ea80d0a01040003c1d0750b445542c104039652218090083d610704200680040841c0006c0c1c25810344041820150141c0541c0045e0042d10b098944040d296130307a0100790156499030300c2c000d001400403102045075042400603180f4180340880046003c0302a050311500d0900d0484000d00f1a602c192010400c07261203121980001d9060a0080d141c03604a4a90401030301c40c5031351880c0111600000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 639649595 1250 639648345 639648371
    0x3002070b0d0f06031211060105090705120402030106080304060804150b010c1101050f19020f061314031603050a03050c04030209010e04031205010b2709060111010608191104090302060a 81
    0x107240956444145e4500704881c881e002010200c07a4108510180314031400070039036242c2454084d1041c0d80075030310b81d440d100700c00302a4564144041e1040380c141d134070b44a0102c0d17500b0081c805040074010603515270440b8502410411a50014440103024551a000780c8c880e07180d0344120704191194010341404200035010004852a20601c00d034114a400e0214108603024091502900d02a880d9030886151007001d03800c0b151900d400781c64081c4030390232240c20100000c0308910300e0340e100140c2ca01a41e040641c0d82d020150f0400f201e1800b20001040005e420410725014400c294000d070108035024102421503010803800001800380400701070020b40000c0c1014810300c660480f814803500d040c00705585d01ca0a800c410340180380482c0f24982100420041c000319016259a01c3c80000e2900a494030b90700c006484046800c04041c04554a9860200e046107040010710310405036500412075486260801103502520303092024401c60805401401188d40002c0e480e800030740c540c9000511900103a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 639650845 1250 639649595 639649601
    0x30e01050c0c150c0c090f01120c0806040606060f0207060206010e0c0714030c100b060d0b01050d060f030212011e0f09050f0304030b1003120e010c3002070b0d0f 71
    0x5035580d4444070881d0300f815051003120203407030300202040c112031700c1c003141104001c5040b00444078101c440e01040d0041120203113004803042114080c41007400816240c2c00d03182c0c14010111b4013a6105912100304110856201041488084d014130107810410b00305070009442d040103110320341d101170003440480c2d55802c54200f250b41041d4010308102c0302c15440d030403072902c0780c2003814031088600420004200c008024018109404001052180741c492140b12650041113281c04480c10040f0a008120aa21140c4206d9018100c0030090b02d454030721710f104102011402071100142030741040f402e40c003200403020648a14030781204001c80c1c032000a10394030f030080140c1303036000d17255129455564091480120051080c0e070b00520010f52035039101802180750555034031004022040c01078041d0b8040f44900c14403400243c0500d4428441d8420ba182c8110320014010701d40802c40125502a849181d21200e40c2010825800984041881c00034101198064441d075130504640ba03260902051170158 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 639652095 1250 639650845 639650863
    0x503070819060b15070b2e03080315190312050c060f150d200a03030c080901030f0c0201050610030e0c1c1722030f030518090903120112030e01050c 65
    0x6a40035140d082c141486d0300b407404160f80c0f0221091b039506082c680701c3d03094803044c1060710428511840040c81c55440000542c0010200d8003180c4907410000010f65400c509007458111100e41960a5400d508280a0b2003c48103204400d001e02040300d484004800306805601c0521229548069680c80c090f1504902101d55465803201b4031008600c20404000001b448800079a5500d40400c1d69070000c2c0548013000c0c0c00064042a82036012400049043c3c009141001040c5800b06815a1404c040070684050742042c0d80942d454100300700050900f51100c0d82c9400c590324041c000c02c41c1200303a841c0c6600c0e00f4030410703001c0e050745070030042414008040524401e901c102c03003d035601d2041c28103080075045041003102d05050050880200603a06001c03c003543d805c0b8901462401660f901036905a1207a20b8440f090000c1e14a000d0141e500c00d900e80d0300c140b0140000d940d98a213031031050003603040140c0140e1050428203074860302180e4407031000c0a422400f800c0c0706946a49501d0424a801080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 639653345 1250 639652095 639652129
    0xc140a05040c021e0307050a1506151706041b03180819020f0607090510020f010501091a090c07030c020109150c03030516020d0e04020f130503070819060b 68
    0x10500d41140c080c0d001502281000340d5020700000841130388191604c9101d0807401401c2c50744011046130100e5440c4c09a50341c95090382c240010050341e1400400080d14848103107030040b8010600c808004061424140da0285c1c0c1200d040250000c0080b04442c0c3c204059920310070940e80d00c01d03541406840802541080d900007000d642c0b140c1900d404004901108030600e8014080c0c11101c41c0c64a40014200380965580e450340325865040c102803101c001201025081184144a84505451030031f204642c06851100b60208507458880c0701c0c580050008080c1601550103482004442e4040a0950b0202d0744e0515002c1c01002c0030b400101c1c0c0c42c111700e410504c3c0e407034803d0603168500c0e6000301159104510907101845665606940d0503900d10805000a000d60008103441c0c1036203203e218107058180000b40014280f0030403041002040c0c0060b5000000100440824072040c54200b06290007803002c900100000c0003480815400b0141c850401018207468400780c000b6a580d25019500441074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 639654595 1250 639653345 639653351
    0x120c020a06091b0e070c0b1017011406030c010504140d1202030a0f05030103030e150f18240f0306030c1309030e1002030a0c0c050402040807031104090c140a0504 71
    0x2c9424050300c0c1c03d580d0000151500c85154002546450300e800003485002c9a44030a1451501c0d500c80c10098000100804103150f41c1400103d010000e2041d00c0c0040402e120002504460244846030440340203040d00d40b0036170001c1d425045a0b80e0001c00c4600341c80f1500708031032000f2070b0480415150588200020b28800e19075131030082c00c0c2c1d80000601f0442e0311581d03440c2d96a0f59006415101c9100a000140014000c004442010b0908262550040020003092031030011244180102c03074104c601d038030341c03070503100c05821603146000c411f0f508944041020381c11070007a41c10100301c0284103001c18047c0e084000300010b1000e540900c02030098880152084403081380306900c41c0010000a942103000c201c08441074007030b600303000a0b1240b5071001500114171701020080d007681c81d0340421008413901e640001001c41c09443d0b900140000b428924010441e0f1130541c6000c10074120307000ea045000b00d1a1103580342c0440c0d0403d10190031a02d002001c1051f0b46111340104c0c401c0600c0c2e03042550000c1c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 639655845 1250 639654595 639654611
    0x1e03110c0304151404030804091a060d06060e0a0609061107050d0602040501080906161b0204231503070306020d0f09080c071a0f130f06020a0b0a020a120c020a06 71
    0xd1903d02e0b50402c6595100104804000d1000c1c00a010710f0101505107a02031205202d055030680c0201c0f0080d403134184200d6060900c1c40094403590050408544280d01d43d80c040101076001104484c800b0012106071020505011000302000540e20400042094030380c02440c50103010301c510000380001515400d030192032400c0440281d4024415540000c81c507000040b001c04d000b0504500400211b55003501907140c0c104111259400c0c503444a0040e04460380590050781c481c45544051801060f0407828120340c0c403001c0f1082c0c80000c19114660300000030302000380c2c0c0d020440d00300303a80e481540141ca4000b910850f5004102c404102c4074641d1500400788280304504024015414142c011940c2846d2a19090200f141e0f07852500d004992042c007170801d80d0400032001d00003e0b40da10030360b050010b079100d815042e10760f86a488100540c1001d2503510901403042d50159208002c0b5005618095486100030840c0d9206580c5848031540c0d547c801842c41d2090000300ba40741d8100b0000d1180740 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 639657095 1250 639655845 639655859
    0x6110705030c1b0117041b0512010f0c170c071515091506120203251d1816271509050a030b0c0d0c030c03050105011e03110c0304 57
    0x410a038002c0103c510300720842104542c07252119803c00c845460b80f100d4291201e64440c03412101d044103001c0003c001081c042095100c1c444800f0444800c000045080340c01a0800811030394034032489400c01c40a002a62002864100e00e03d810241c1c002d843d80c3e85030260300f000c110005016100d013071030303d0400c5035071105080341c01040e0b8140c0f6042102081482444fc95004440d00c6e280b143e40040ba40178440d02e014443d480d0f000d1544032408040400700307409111245440c0d042000012004a40b20030506a8003070300b0030b600d840840348240c0743c40120300d505403201200c1c0308000b401303641c4d03515107550b580000603c140c0c0080502c51010154034504e2401c2c0e0303920b0303580c541d05010740005154017510145041f4031450f0910112940640701d28241030840d00d030311442040051191505110410907211005400e2044c0480d003803290350001440d40302158020156081030b0320140c1040080030303603201d1121403407041882e01c07684c0d4140000d0890a0a104d4070643c0036030740822a0030701010800180311 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 639658345 1250 639657095 639657103
    0xc070c090e060a0507090e09011b050a1103030c03010b1b19200603061519090302030c0f101d0619080a020c0a08160b0901060f06020f0a06110705030c 66
    0x1e16161420344510340e4031140e900044a070100d07070843c0029036510b403c2081c18420408035400120380c1002080140107a01d038100480310a501484c0000c0c00026001821070303112030b4032062100e200020354514241820000500d01040c041e04010314400180c0f59058038400300c45c07980782c1001d00d042d0740c06440400349820814012003410f403040810740040c3c100c04041c280c8081c41151000307000600755180c03101800203140706141c8001c03c140c13041010400207682c0030007101d01145295a802c0005003548185424011612045c90003100c468920001d1a951005201c1000c0180c0c0b600c000818000070f40c013001124410b096581003800000c00940e14105060485450016030302c5601c41e9449407480e0300308a02c911400b102080c4c001d0003041d07000902550051802c5c1d81220b003d4081e0704510348540c203150b94180e8940320180c0d56000104039070041c0512401c02083c072400a402d451555004040e10782c20005002020642e440442c0d500d0f100314031003a00c1d20b00b07800000f16a12003020800b4180c4d0707 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 639659595 1250 639658345 639658361
    0xe10090812031b070201180801060302040e06040c03110409151b080f06010507031205130201020c031204050d050a0f05101505062a0f0115060806030d080c070c09 71
    0x100340920007030031030250182401c40b0300503404442040e04001c3c80b100403900503004004201d042094204000804848561000c0054203105c0000079405142d441040115400091040820303040f100402002c80e045901782421039400c40d03103042030044050b002030014801c400d401491044001210740042e040380d400b034039520540070880c3d02c85101200050369081d000302c512004200d22040060965485040900841071003424801c00300300321540d0034016100102e0f80800a15600c02c000e10647d0b90403c22150311150a90103001d142030508029034440c411402114025a00c0304181820854200030041c40507800c81e101c1001c90b4014074050391078030f20440c004400c01d2b0418081c46d80004075110b500e0122000180641e180141a0016101041107000c550030320306440d12403c11414018484461142c1d00301000250140b03100950b401d4035000b81d0000d03010003c00008102460300c000800300c8000c0f103c0d0408040a5607180c40605442c850001c00415030001c1d00d000049851041d000300744 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 639660845 1250 639659595 639659609
    0x70e120105040c050f0604060e0414070203070507090612140a0501140109061d0a0525181a07150b0a090b03150708060f0109050d031808010902030703030f0e1009 71
    0x10481c0c0c0d10304c200401026a00d00f0745501c5001048108141d6000d48a1140054401f820200361030b20105142455080125902c00140c0c0001440508108050100380060302e4041c03810007015040c04415059001e4010b8001c2c2030556001c1e9803844810200308020010f0750041c020306c454420341e1100c3c0d8807100c0038810461890b00300071010030a65506c0b50040007038680d850080e4900e680d03d0711040050400a000351040c1e4415030a200301018540a0400108003151900c5200c11305402ca40010403900d41d0141c683d40920307007004400c0310f111000301e40da81a00070900c1e03240a038030310b022180204804049690f11485021002400c12081d4201b40c1d61303540c0850640b804402001e0000200b684d048401e18001000c9800060040c0340540c0c45480745c44c41850325090141d01c803070210320444080031050700801ca0141d1906201d00c801d4030301e1030242c51250f0013804414400e60200350741f0815400002c003800981490211582c0c07142011040310030700100440c00005a0002c00744c1002964041c500d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 639662095 1250 639660845 639660863
    0x200d051b0a08071a072f0f0108010302090109050c130602011b0804021503070201060b12100602120f0a030902061305040f02040f0b0c030705070815060406031109070e12010504 77
    0x2d4604400b09902c400c03906000c0342510b1085814112401e036038000d4401b140e09180040025042420342e062110420f13110042c1d03d40d0701040720781004011240e4280990401505200500050b110100c40c1d50449003080c0d004103662321540400241ca010b42180a8031000c4200d07000a9619815009002c0d1840d01950340c0100550083c402ca4080c101254040d400000c1d89241000c0f0482c20002940d200ea400c1c8000034503251162011001540040c1e65804003030480d80c2030180c40208005864002d01d06c0e4002080800e1081e540a910707401070f4040000d00700c0010900050302402504181c80550b401001c8503610030f026010450081641c0c0905800f031450507000c00d01125180c800c950a0740c0106210305000c80c03138055038141c84e40c4001c544a046000611041c0009842000120060400000504101e0310001e41d27030410f17444010300a512a90500d00d0800100350101ca0b4044d403070109031151703501503a0305001528078a031021046600000d280b04040f03040481940f140380164800d45060b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 639663345 1250 639662095 639662099
    0xf06010909020a0c120504080d0c050613150902030109080c010e060c040b0d090c030609080304060509190b0423030a140405010206060d06092301050a09200d051b0a 72
    0x2c90051030f0000340800d1444c0102c401290309a1207007440e200e030b6845d09a00d899141c841060424103a500c000700850344008014007007000034071a00b41e1141003e180100413a0081d10750760380101114058034201940c1d0003c00382551020741158100d1900914401d5035003c599018900034400009071184a005103400b18080d45440e504890464120034051400c010020b064200200164002221545040540000000c103d405144141801480340c80e403a46000d041c0881a110024500c00e900c3d0044c82041c0804201d0810000116801007120b880a41e640c0c83c0c190b00400902440700302403588440344600d103142c00402800c0440361681c503d96262444d007402001c0d40524002d650241c3c05c03080005085061016209001c03a00500c0c0202c0d51049a407181c00010160400440b03184400c0c0e0150880755109000300368010a90785004c20100880c0c1d1030302408000110846c104591044910740e00d9942c07000200811250000c05580740826604811009802c1000700507000300105900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 639664595 1250 639663345 639663359
    0x50403080402190b0d15091503030909060f211a011d040203030d051b070c2318090c1c12050f0f21090601050109090b0321120f060109 59
    0x218600321161013803403030706110000b0f9241d80604603a00c40d126100600500000300140507000c0c03400307440d04485000090f2410341c1001400c20383c0c1034000010103820880c2c2002402da040c001c0d401111034a00300c0459070400114400c0c0c5081c8480c038060b1007440c14144421062442c1c1741c1c030324122943c2d0b130103890500c0d452640d5012001003c9030060741c90f03081403201120101464016039800011605503045c0c41810150100c0c0703a8100e07040c1601d508400900c02e00c059284e82200c4002c1d00c80c81c043c1402020b24560014900c45070300700f0800d105041803404504e440ca405c12040900c840c0080c500815a500405400e941c0012410155405015082051309aa0140d801c44800f030b2a0144000d20b0001410f2650105034488030f1400f2a0440306c410345201405519031840c000c0b0210000791010354504000100194490381000002c1440c04800500a41d0001b5131000c1100b075480c1400d01152108104100500801c4640c02d2058108010000c01800c0303d503034644140401d03243c108803141c6481d0307 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 639665845 1250 639664595 639664639
    0x10306030807020f0406080f01090b0615160201030f020705150f090a0b04020102120c0f0106080d02340e0a0f0507090302131d0102040303110303040206120405010204030501050403080402 82
    0xc0302801c005802c01160025042100800007403040c0a400455400d55481d191490f01c5c002c400a50442d966580d8017804120000009642184086032034441e458019920b03401d00313115103c0404515840d400340c070411a40643c200f4507032040414401c644444032818138540711440c07004941c049110b5940059000341c0041d0105004505142c01041d0b00c1020b0760b540000340c400a44140d040d0312030f0307100030300040e03080ca00105140c121820180451054441030725003514481d070130082003038003e01404241c20f41d0014400700d007500507030040001c00c1d4400054820041c404100c40c000e141c0080c03008a285502c4040c0c1038018440c008007007028102e0601c0540c1141c0040e41d081340050114035003040580b900840e034031202401780324000b0750010b10460703903150010714145480b01650041020400e040d041089488880c605002540c13441c6096070004103a44104281080310040e4280805d060100c00d5060350081c550100c000c01c01802c00b030501a01c0848122400c030312441e4608201200302182d14 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 639667095 1250 639665845 639665849
    0x1106160510090b04081e030a240602030f0f0405180609010b031e0a0b03060f010501170c030f130501020a020102040f0801020a2f0115051f020304230d1a06010306 71
    0x3c416070045899541c2d80d03003010791005001041ea00c0a41c3c440700701c00d102da14004e40c0241d4640c6000505d810340002c0000d80a201d00c4605070390141503600c100060b81d004400c4038004600070400590b9011a100c01140030700454016a8011940070748180c046a200400c450241e0812112a40c1c90f0f0b1341d07050009130138441100c50209802c1c45108600800301c00d8504244c01070440f60000c82c180c034007000801e15044003110408824000c4070f00402041d41c008032406044003a0202d100081d19161034109480d1102826046901d503a6000240d810032020207440542d9500c44021356981000e4007009020f5001030140742c10302407030800c00040b441c10504c21104108401d4079245c26041c07000007002c00403203c403004241800700441b804c1c90b40c100d0078400c8181d11030201003240700e42418442400f0303842400c1d81c4940c103403400044204040c1e9400005903001c50321035281e400840800320002c1030101c5244000740ea080303680c103000d5404104052809200080340102103e07155503c4600440955502e8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 639668345 1250 639667095 639667103
    0xf0b0604060f080705070807150c1418010c140d1d131509020f041511060f060114030c030702010e2107020319031e020c1c110616051009 60
    0x498a031020b281d010b401d5441d4881c00500b0450f0520034952211000d990001e0002c0ba8078030403034140d182c0d01c00b090341303d402e11069140c50909000b03503119811400c1e0748230300c629600a0711046000c240c441c1e80f29640300d60100d5441240409000c150640b0103564105a140c0740c00400c1400b5800040d880e000c0c47c5480ca8108000c098401d540350091101d030041a1012004513080d00513080401d40034524001001c5c441c40f01c0b41c017150380305d1601d031100300c000c10100161010003810040742c214116001451a402017840ca04202c0503449000050f00c2d40c12294201c181c031004c010041000000201d0f000e90700c01e815540080c0309508a015059466800710410001c100d0a5141b1607403012502e000908500c81c03001d02150b6488010030204181c03001c0802d0110005611a0000c40d8902902441c0700c18220390307030006041c210380d4000041c00c99510000d01c4584802002c0c030720010320001280c1003c1008e80034124a035120504c5450742403140707030203030241d54074412600e504000c001c09d8411540402d0704 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 639669595 1250 639668345 639668357
    0x80315040c0503340815120d0e0618011209060c030e0c01020f07170309040609060302130908160201021606050a110c03071509030c32012a150f0b060406 67
    0x41c0e44d07420f80d2620806810040d070451030885c08a129110179030b128480d010305c1402403c1c040c01000300240455a1900300c28007070342060261040079641c040302d00035600001d007001200e07072102d64498001030090010141400b0b040c008401e042c25010303400515400418015203840111000059036100703a10130f0100c001d0b6008400410044602080c0300300015100c5066900d0901c407500024141c1e0902e4200c0400242c1e500020001c515050f410307085102c80311002440b10303d011342c440103418014030f0201002c81103000103541c1168401d1151000c030460f0503406034400ca8650070001e190350000c56401021415202c00c92011420005074a00780190003001854414100030500c100b1154441500041c8a03443e80b010000038040391111001d84841c00f40c40d150301c454030401d05003609803103940c0301c84440c1180c150940744e40d2054a0742c446280c4110710160040c0702000c4035040e405061005007840d041801c0c200c4140c103158210002070840d141c02442004084010000e007840366110b2000441d070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 639670845 1250 639669595 639669691
    0xc1502070905060d051509010b010f0504050607020105040b12010513150b0706021c27050c09150d050a020a0f060c030c1b120b01080712080315040c0503 67
    0x54540016620003409440707011240069550380b854075036108041e4806e207442c2c0e4104140c4044c248034a01c03e018007441c018641803240e0710003820620590007140d0203054000f81c1901964000c0003100c00502203508c070156200d04184050b6224034083c0500b502c41c00d020307440c40001513000c1c003038580c2141d0b401d0341020340140780041d40166540308002c120f60300f6400b80003007031000f8801d06001c0d2510460340c1011500e1512200044500411103140404000000300d080000c03801c0081c00d0456554260340342c005a0300c625130b80d11001c0740d40e140229030281400c80ca6208010003c10034464041c400e480c40341100e500c40c1d180f07000d00e04140c05160001096800504d02181c82181d5001200c0d00030b140410391f910352181c1c42c0050060340d81260300307940302d690011b00400050010007401030405801900f43c01e424140176600d0711083e010003034060700d00403021603040021020103100c0641d00401c10001d41c030000d00090070ba500126440c4c1004040701030345440415a03170804284e541d078202c42d4101d00030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 639672095 1250 639670845 639670859
    0x50a0b030c042c0f0c040603120f020109020406060c17070f120c02150a110610091a06030117060702030c1c030b03150109060902070c0303050c0a0b130c150207 70
    0x800710304518207401080894603d104400800050303289032125000d00440404008094074040001c1203103809140750010410200da000d1401c0320740a21586000c0e60329607032001e4102d01401c2c0d010707800703540546841400a00e10b41c05c02e101070343c4103220318280480c06c402d2890f401610f02400402070903c0c00c541545100082003041c1a181c42a55800d0441043c003140c0c01003850703090130f0044112640c60010f00405281d030003180100e001403800000f00168500452049214415481052044c9480d0102c4591840781c25846010210010b840d103a100d694030700c10544100d2003141d46e800d15004000114050510101c100c0f00198010f10007020011307800c030540f00e03401d50021041c07401c055542070200c01c01c0d03406100155001c400b003000f4a64a504100219080311880d43c040752180c0c0c410020354000405d40c2c15200d0850380c01d810040d031101d81c054222410700b60031950042400c0031341c90400100081510750340ca001c501982051248545540000320b64034808881080136901001c010441e403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 639673345 1250 639672095 639672101
    0x30c0302090414060709031703090c0f13020313031e02030f0f07060203090a03091403060604050a02040e010306060f09020a0c140c03010c05031e04080403080a09030c0b0d050a0b030c04 81
    0x2c54803540f0400080354030860010b0902d4000e80389440000d82000080040c0b01c1c941480d080f001d01c491402c50f1441c06c0101303010782d40da654100000c0c06656400b00a6107290313108202e070703240140f909105554138507140c00e0603405444c60307800803008500c180058201882501c4d8030340c00141416001140f802c1d90707609401e00503810038070765803000980402c001000204180051800b6084060090604101c180340141071084a0b8003c80107040b0301004a25003650300040c00d50f0090340640700000c4644822107508080d104542040c40c03803040300b0000000300002c80d48a08129540042d400038240e444400030420391081900b41800100803076042c4010a1000d69180e2009005100312141040440301003401e40c0d080468400124402200b009102040c0e8002d96200ca02e00040c140b4607880d113135a810744240190300019100d82c07404543c50351120b0050b03031004061a0800c2100d000c1503542c206080b5144d004041c0c824240e410840410350782078090141503600c0f8001005050181058800d02c002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 639674595 1250 639673345 639673351
    0x20115061b060e0d1409012c09130c08010c09030201030f0e1f050901050103080f250c1509080705010309030210050f01081506090402040905031c05060a050604030c030209 75
    0x542020080007200080e03291007188584907400c0003504942e004024003034901840c61030701c0ca810217010001c80032603a0b07100380f007410600d40c160456040320307050007404098140c0d94100c0f250006042c00030b00030b050704040780070910140700d801c260b400720383c89018003804da40c003502c80303400443c0403500144015030294002c504070206041b4001030310084a941c2d03601d003101806507e43c40c0c070309000c2e043d401c03048540289640003440c1c20091141d9491540d485590f4452078403054031221010401c40d1070901080b010f07280c035024032107508282c0c41490801c01270200c4113100f9a506500b5070800c41907010300a0190b2802c4544020180400f980b810005501508100d40204c003107002e5000c90311068100c920546001e082440040c0b401c540c14206510703d4a9144030f101c1c501c2e91a65030070004070f0fa5603850074607449035040c1c0300410100180d14040b841c5010760019034522041d110f003040c0c900002e60384514443d1000702c813008000790340d0f002030100c01e116a00010380310704180d6205201504054a0060f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 639675845 1250 639674595 639674627
    0xc02071e080d080a0912050904230a02032508060103181502180a03050c03280f02040609020d0524150903030403080f0a0801050103060b090904021c1a0702011506 71
    0x1040c3c00c5e5903071501e06c2000d0a40ca004081803000c0341c6a15541418451480d0b40c031045001c41c0c210f16a00014821070020081c00b55100d203400100044c20b942640b07091200c0e80c1c1d0341c2054a220f12020480140c1786481c101c0e9503034000380c0b801c0c040c404035441c00c80709144403940240e80e03020480340031070506019520450280b1074485d00c5144002050304d48a80700305c0114050005040c18004c2001018100040b100b814401044411005003901984080c0e45448a0340241e8040701541d4902c0801c02a0019900564100d4030114100303030024201c0d08118440c102e0344ca60150040b000320302511229031003c90703054002c00c441503821002d04031003001b001802c01c018101c0f400e00340d0700d40c0d42100c1030380003250100441d0701c080303081000c09412851040c05081c003401c041c0056401e0060083e040e0103080c5580c1d2240c00c8441c0450150348400c408580c600e44201e0040242e05450b0800184040713082c4c40801c036085000d0700081c4928410703c03e0042881508404554040c07a1200844400c562960440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 639677095 1250 639675845 639675851
    0x80d0203060f0f0f09360105091501060f120603080705010b0102120f07020a21051018030f03060b03090d020709090206040509040314070309050f0f030606060f040305010c02071e080d080a 82
    0x850344800407000d04110702450b40140e06e0751801051014250f40000c1c2220a03550b0100c44800710800205000c241980d00324548548401e039018000c84103101c055940da4100c40c42c0820101c00d02c4200780080034030394068002400074801e08401240d1b201046600342500030b4041c807000315030592010003002100e0004180c80c1250361101c42c04441000c009141110346102407424104000b8240070850031220340a1081101002080d11041d001785100801020000491103100009001e41e10850182c4210031045803030340761245856540d15088003210000d440b6549000a180e0307800e0142a2107181d0107042d05003410b25140a0004141001d00100c0510000d55000000c0000200180480318041c5e540c0c0c551440c9410240710304841303050012030250b1107589003194980c800203204ea41022050758081e583d00d4451174018524011a04014029400d084850000517400030340300003500d0310f22415540740340d500301801c0084503041c4078403402508030080200146002e00c03000d80d8403066500c008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 639678345 1250 639677095 639677131
    0xc02060c030c0d020d0806030a0b0c0c070311180124050c0d031d0a020d11010908070e01060e010c050c0f22150b070308060d0f080d0203060f0f0f09 65
    0x658256084250646683d5200710141034445a042042644250342130520000c1e604041010944910b03100c0405061190590b000c40c2d058043c641c00c60f0310029070f0702c0640b07081c1900d0340b82180141c00b460000b0b901c40c140c581c0144400d00030b1504598101c0780c0044402c1c4110648849030200941c1c408222000c5c070006018005034000188112a03103c450f95900080c4140c40240c0086490718a0381e01a40315404400040c0050b00c0f01c481c03610406030070114007d00304c0034140048885250641100300c0c0b90240403000036500e540000941d050350859200d01c081c0d5150003004542c0404a0305c40502640d00074a071a20007800d0114100348084030152004210514144100c02c03201d080340f9140032075541d100e0918203500b18030340200c8050600501102c4c40d1151a0718002d2841c500507010341d100301c680c054002d0801200c0e40c45c403000b10350312005103601d8444c020410002904215801c1d8000c682c039010040c001d14104442e0651940000c08000021400e94103110000324001c181c201e91075a85441 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 639679595 1250 639678345 639678367
    0xc030e100e121305090f04030c0f02192403110f03130804260d091a0918010614040509070804020d0b2e030309060f090e01060f0f02060402010905010c0206 68
    0x30b094100040d44148503c91501c000d100c2600310003403100303c2c5c4030000d03801e00c000680d003c4001503289030003010101180600c0e0000074070000b8500da801e04080701c0c4910000d1800382c5004c00024101045400c0c1822413000074050f0155004d070300349103140110030000c406541c503164000e150091003110b84982240c03c2c40c1d03034a001580c4941c00140201103040000c0c00a41c103440c01006494030203c0c05031201984408001c0c1c2440d4903070250030198000705489001074004901921a01c0c04010f000e00c074010440d90103145003d03030a0241c000000c000003111004500004210f808443c03021b00079040c0340e911b80c14206c07880100544220b0340000340408580101c1d50001055014610210b00120b44a460410503060f000c90001d46401702c04800300c0c100086500440850f0403035805003001d20010030360754000c542000030354200c0244000c1c070900210300241e214044040f1246107803180400801803000c141d81d5110101d4000340040ca5a00092102d03500c15080c810b140303440a41000c0c1420240c0c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 639680845 1250 639679595 639679597
    0x10e0a26120103032c01050306040b0103090501150303020f120d020a0e130b1c0b0609061504030507050f06120a0f02071a0609130c0b030402120d120c030e100e12 71
    0x2105800241000d044810790f01840b0440e0340c042020001c42e0301700340041c400042d04500000380107902c00d540d01e207032100e1564007941007020102e61040003000280b4101000806503100e500041e00107100f0034040f408400320000c0d0704d00030038026401e0f0301d0400b110540603901039400720034001d0810200d41803006c2103460b559081520081b00d04004140a0000b0050040003200c25250030300c0a40220b8510001c20404240240c01000680314034206603030b210007050448426008200350400c000034000f090050210b60b100c140c1310200c841d1540842c014003000501e00440c0300b0b0f121040b20071004278003505c5490307000c0d400e541022100981005065119100e0b00400000701c00d0080c941d55041041c185800c600080d40100802080c10041260b600d8215100c1340c14005c0740510600040801c0039541d41d6001e1485584142e002c6a00224000c1c030014424a09040d80406c5a8280f540c90504c02d4043d003e00741e00d015404d00103008541200c4000b4014120f282c5030f440560080344c0030304003c050490 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 639682095 1250 639680845 639680849
    0x80304120e1206070f020309010507021002010b090f100518070c15060803180102120d020a180306090201031b270b040b0c070f0308070605060f03010c030b03010e0a261201 75
    0x18014012511380b2007000340003002c1e151380b0001190000c02608165a8000c0b013030741c401d140c0680d061034200b102804141d005208601549a001a402d003c104c030b40d00500134414890aa00000c4c6e1100c540e8a8060040040c070203807094010038601c00000340d07030501c2401c40005050040345c043c680e80b01000c500800b140c400c0d030400c0d0300a40001905403681c14500401d10000e140a1000703101d1615900c0b41d403e180e000d812007550076940c00244c0e1880e2a44520341d200b041101400040e03924550300c1c0762944c014a40c4080490110307082c10301c42d805c420702c006115211006661035400e601c0342801112561050995085a5425030028022400c0300300718003c0d201502000c508a681c03900c180d48c1c0301d80f82036080d40c01005144104401400050000001d4400300c0d0342c40340021500c8d8549000044500140d817041ca0703050361030102007996540e41900003031004141903000f000501c0441c10000c1d11007145110151940e10000108041c100c0c403262040e00c2c12007924199410301c411807030101c0302c1c2e00b000c0e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 639683345 1250 639682095 639682129
    0x31b19080403061e02130807050d1a0a09051209011206050f0f0102010e06090f060117150a1b020610050a0509010605070f0611040f0608090a020415030203030715060f03080304120e 79
    0x1b411050003800010002400901000c651071000000d140c0e5032500c5038580e10100d2032420120001098103240b50790442d100c003550041c01d0b02d29a01d407400c0181c04030342104d210ba500041c1c0c8000004200592442040d0940d08081c1002c0c41403000e80e0b046c001d12088008a46046640e111913005010000344210b41c0204000c40140810150080340d40380f5018060308044411340d0641e26060600f84001440004940d0700180035607181c2c1d800c0702240c0100344048419400c0f180d40b1031425861a40847c82620032115040801030440d282c0c0280300c1c900c00680102d54001e8034100051007504e00420241a00ca4442d902803c12120142d43e0798081e54810345405142c0140418140044070303c0c04075402c094035852514003490301d8410141e607510350210402a015075541e2140a03109042d96111002454010781101e90354481e030300e0580d203103080c615029508240b034002c0206071444101240320489800800c20f074103603292a12001c0b0880401840c1e0340500800d14031040c06510f80c498040303515100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 639684595 1250 639683345 639683377
    0xc290103081801020318010f1115070909110f0304022404060f08042303191d040b01140c0a020a0b030a0506010e01020d030e030c031b19080403061e02 66
    0x40b0388101ca015441c40c01c031a415504103002c5040240403170002071085200928001104103c88e42d42520544403c0d41c800300240601c0c24200041081325400c68080c441999030552503035500d040c08002c546c444002410000410002c503032483e04218042e54000c0d0008101c0c800035055520100c652020300da034000320244001c0340030000c03150454449040c2d103601c0e00b0100b21620f06503582c0c000c40e8143c4156007076843c0003035103074281116040040c0c491880b50103403101c8909038160400762a020300003c500e600c16142002400791400c080c041c10002c8581a114402e034090302c03102c2c0d160036402c00c034516030161140c0c0608070007580e9001d42c1c40d40141540b010095983c1001741100b0140d440003040541171040c100140c081c141d80c0041c0c1c6a8808509203400619042044105425403180c0c040440d803034800460040214551642f1810301c034290001100c01d10f4101d0224000c0000b800c10700504000c0013030100b0400310351a80c0100f86507800c1200c6880c400c6112403d500220f0300000d02c50b07984526 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 639685845 1250 639684595 639684607
    0x10140912061006030519020d0f02030901090c080a0b0f0408120c0a1206030b070f09030b040834060b040e0a11041a1c020a0f09020706050105060702010c29010308 71
    0x90b1600d0441c0074100514082c40700b8500484054010140303004030002071907001880d41c0113001184d00c40c503101c4a502c00f0942d56428a502d400c1d0180c0101502501d410380303010710000300880d001440101060f4809404500c0350388031640b402080100800984010034204442000102454403a901c20081d090072a51109a8003a000706003005a0700864840f502e8078034248041514108625440401c80c90610580309202d4400c07580d000b1243d10040244c41501c090008000e0503601500e00b0400c08166001954817004020550381880f981d03408031040012112408191550072422a4810183c0049a00003111800b14038000500f54196540e038440150941c0c81e04e803078062040300c0101058180c03000300c44400000c0f1103034000d401d001c01c100c402024000444d11100000402000c0c2c03d02c001824640c1c5855600107907012035400c0300d42c1071600c0000318151501d08199003449406a6840d006102140d503146511051003110380c54000c0340541c100f0114154034034080c040c612840d03c5980343c003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 639687095 1250 639685845 639685861
    0x6090b0f0f0a080601151e0e060319020708090f01050a0f2d02010b10050f2203080c01090308010909050303060409060b1507020406080703081e09040c080708010f051014091206 77
    0x10304101d1f0303480790b0b40c0c024009401d041940290304802c031000c01c5035000c2d6282c5038980c1c02070001407030986000f81c090010070303080e051104400181070b12490503a03032411128010001100c85115003c2d0400100c2d005920480165110b0b0381d2944608403200c50310510504a1509214402e03d03001e00040140c0d1100c0c00d100d80ac0c00e140640c011070309540c2c1419800d04100c0700341c00b400c43c002e42e0b130950192000300004c4250380402c2c000d444000c6400004085d601d040f42c0c0156400307042001d0051700072a05010002400740660301c5880d1074160801c01a40c156180e15007004050055108140c60304e989039055400c0582e00e00000a441414403041c0710f94034240d92043c0016200140d12a0380b19400a003030400209588908441c44128071758000c070600712003611013807a940150a000394009160940c084500d80e0030160680c060f61003502e4803030081e0390311007000c01c004001c0c1c0201600701440ca402c050390305001e0305120982c034506000550400845030042030300540750b813003403d040d03034400c005200a03c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 639688345 1250 639687095 639687107
    0xf020d05040516060504050108060301022101060912031d010e150c010609050f130c09060306050906090d02030f09212824140406020301060306090b0f0f0a08060115 72
    0x208010000300000f03500c0c041000c3c0850003035100340c03814004213900245440d94203504940301e100e105c0e01303540101c100411520801d66000d00030000852000000404d40035510518031000c2d5503da9030f02801d80201c004103a070f000c8218045c640c14026084080c0b24a9a683e03003038030880c210081d00c0c1c00d0311000e10071006400d65416510072118a460b18041c42400000400c1c40342d4000800c1408484145c01450103081034022540402c41283c9021008420448107800c800e01401e0384e8012601c032500c88140d06500c0302107c414100259104000d009140441d078005442503400061507180422048181d0b941002c1940300200c0094014103008400510b54041d07454848881041c880045c24031903403100c0880920403d03140e4019407880d801d05400c0380b95001007440c06e4814003410070341c0c1001d1801c50041d400a00030f000210b402c1c8400410006101d00c02c180272440c004040c100148800001d008546004060154204c41a01d501240c400020046a23009068a4030440003d80c000d40c801090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 639689595 1250 639688345 639688363
    0x20a18140c2517070f140a020f18060f030a0b0a09060c0206010312030f0605031006080c0607020a1e050306130302010b0a0501020607030c09080a260f03190f020d050405 74
    0x40340b05100e05070007189940c4151056070a06142c0560350304414107101c0c020219801005020580c07540104000b030303a01003050304e40c1610980d00720340c000603000208140c00548120070703481400c8513400a000c03880d01401600d032034100601074a42c400e18030340b101081c00d0310458901025a1325540c800c3d0030030003507100c0c040c101d0009201810710395056545030300401c2d800f481c01c0800c00d03841d102c240583c9006076028400a1100508542803a1160314142c4040e1000340715042c41806030010007607403810190116621320750700030010308050313091401d0b000c0d40d1103007501e9481c40c03036004142c0070499440400c2441e0051020a200281445140c50000d0035206890002c900440a81104001c283d8001946940003891820049030341002204111804107496000404030300c5080551014086405515022411003100d00130095640e1038100c40184100b882c003440300201040042e40c10b050f0242c4c0719424900d2910302080340c0a81007034400c1680c00000c0300c0c3c0205030383c800c18001044420018080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 639690845 1250 639689595 639689647
    0x50a090b010815130501060f09061b060905010207083105090f040204201c02030c07021c02270a05070905040c110a06020a090b0403020a18140c 63
    0x4041040d05000034500c00001d80b0f2200161081d400540c510343d40d040c3d0210a02e0320409003000103681d01e0f14001d11600c080010b00f0b01180d082800400c04038401c48403200c28101c9104150000c1c805683d601004040c0b60005a5907554207200601c0000c042000410104510490120901e018542c020510404040c3c0b0100340310850202008035072219100349a012840004000e170565450000c034014149000d113203445002141684079024036504080e0820301380b590000c0980600454240d27040b44416103072000c0148050210b40014a444c40721b0084600001d5501030b04c410032230380416080c070203100c603001c11500781580c43e601806040da20181e00006401050066044c11640a840b28600e40a8980a070351034411164103540168184294203070400100c0c0d0b03000e40d10b414108000d40007150b01400280311180e001803803141c0341c003c1c2e80503070b50003c00511035545448508461040030359000f85e821622090f503460f003d0124104144562841c031200d954800c01c81c038000880030f481e002544 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 639692095 1250 639690845 639690851
    0x90e041a071e0c17130303110c01020c0405060303070f03030c030f0b0f04110c01021804051f210b0c040602060105060f18040b060a03332102090106020d02060705040602030a03110f0403050304050a09 87
    0x14145032f0740003c015105440698000813140c80da0000702c0e01b10300c034208010301030143e0b0b0035140c000c040d4958050801044290360800001034100c0c0c50300c0039102d000f414a580201550328040f428a06079003d912011201d20940d80380031032207460326099800c080c1c040800458003010b00d00030f5042c18003e04d644001e090f070f81000300101c01c4619003001d9025000c1d41280c4c10b0b00f0007041d44e040411503000030f40c158000302114040c4ca40001040841d902038007030030f001406210f000043e60f041c02020383d00b0a007851480f0354105800080d02031751511142a2070713030344180c403081e004000e510b4040c02004141c656542c04039440c0c40010f0051405009808141d40001015011040540c10010750009403190541c003a13070024400781002c01030689214020358003507a0040001025600046c24000d01c4001ea001c1c0d030150b0f5140a03003a5024081c51060a001d43c100300076110f1424807035807002101820391000a810031384000007144168000b074204807016400028148980d20302950590700429074030b1400c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 639693345 1250 639692095 639692113
    0x100507020d0c050f0102040e01090c090305030f0c0127110102072702091203030a050603060c040311120d03020405010e040b100807090e041a071e0c1713030311 70
    0x25665400121200c04002c41070354403104216060001010161182000f55100c41e215001b50030701c12020320900340240d1502c580603120340e01503a00711080300d0304640036504042040c80e01100c88d0788203583c1696207558410340100e08445244946024a803800525043c1d409036242c00d03884112903090b142e0640d40025400c200c0e00d081c81c1c0f1000c418145800c100344000f0507031103544c03029015071380c00315a0004600e40030310020280000990b01c1070403248014406c50300c0d0034041c15190203050b20480d003181c500300002e10210302c000303040900390070000d420019036a845a8245042c4a0242d00390800282c00150420140d0b03404500d03481c4480c000c580c02c1010598810001c4d45e840c51100c003034410b0203111000151000c0c02509070100800d101c122784006803406241103c00300c10f40e076000c10603405e240320100b10b5482c415160f10301e8205903080c482a0811660b581951040440782e4215101104050042c1d00c0c91807a4001d0100302220056020101c0d0451030094003207600c44242031901d505c00411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 639694595 1250 639693345 639693347
    0x501030804090207080f030a0207030207060302130902211501090608010e040323121012050d050c03070f0506160503150603040f0b0f0609060f09061005090a0b0c100507 74
    0x210350454402d8680181c2c0c0b0398140c6000403040c0034a20310484800400300401010f50303259002000f0345442b03542540d030403d4950109404038011b500b01440154608a02440001443d40c000c0c07003600301c0101020301c024000d18034001954811580307013901601c0d250400038296040501e440140c101402e0081ca19810003041c0381080c040200040c0401812810001c0c40c40580d00d400503150703220340e29059945001c94410f0b102c64a050303801c0c0301a90509540040d01210400b001902c44d139000307001d04903180900104640302e4100807802041400204084070000700c612040100c0ea078401c40c060b200705c0c9404030004032840d03580c4021005015041041101405003e00e52005100085602c281c0700d4555040c00180f50210000082940340800d017403210483c0819841031040e81e0455005c8207a5070744109102401500c45001d07034000c00b100340421021f107000480300d14150030310b113400d0f818090740400040c0da8101d1544100b0003510b0015401000c90b60030b03c89402c0e4151440030520490506d058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 639695845 1250 639694595 639694597
    0x14090408090f030a06050405120f4e0c0c0304060309030210051e07020d0f05031801061701050907030b0112020d0c0b0c01060f06080123040f050906090105010308 71
    0x38444980001c09007030540e2008040c02c1e411001504855030341c4480c1c6080c1c0000d00c0180d4040e1800c0c80782d8600120b0000302002140c14550720406110b040041440c170802d9400b581070700850884811106500304440400202da044891581140502d0340c0707080312100d000395014040a85000e410414400c801c10000101c5088442d070380b5000400424904049040c0880c03200302c0d0620504200038009008185800c08000600c1001851603684a1000170b81c0c1c2d4102841201000c64000f40a10034254002d0001d50f9200a08a4940d0001c1070003420140c00c5421540114820f203035081002981d0410921480340c1c0105d032440140142401c60300c0741c4d0046001481000703058000c0c911580115210030301d98012441e80720000800781d0340ca034020b4500755045010b01e0f440561a22a0001c1c03045441c0721031a086034065211120f041c0d08107601d9900c072407080980041141e175041d40b09501070b12188107651086105220005041c10030603ca541071050180030344503180c3c10240180b0111340d0b020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 639697095 1250 639695845 639695851
    0x60406060e22020d1a030f0d030c09050604060203041d04020d020904050c0a030b16051201050d03110f06040c0b0903070e09010e0f0c04050906090a02191509050405011409 75
    0x2100100b000c0d10102c0c04050540444000e40c00c034500206080d501400c480d0009100d03845d480c1c44030407603058020141581d80c2c3c801c0441905591024880c00410340c002c1d07010b04910f1700710740f4200081e00d03210008505903030700a44c0218010ba0000904128000030800c007207003041041d81c0715083d18100340d0000303504044000d0000e0300c00c000c4200030808014081010203a1560060014410f0742d5590505000050382107681c11030030b091140d2414002d612400132200f40c0c2100841441d80f903402d107424403400d031420308000c03000c0c400d0100d820591013600b00000740a00a904009045900d014a0310402c800302030350003100c40d190140107005850360081003d50a640040c401003070580c1d252500710f405010b603041d50352510300030840c1c1e00c5540d102c0400e00d105c0100c41902c00b4412501c0381c0904540c0c030041241d4190042c4c00c12140c01005240c00c482100d03074608403800c2d14003007644031007031101c0ea0181c9030700c9040440c404400410041c149409158010440c0c076091040d808500b0b004101004801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 639698345 1250 639697095 639697099
    0x1203040915030b0901090203010506040c080a0926030114060c03031f18020408060709031208090102070c141305060f040f060312051b1b13110a0e09060406060e 70
    0x15085881074001419519001143c0100c25802282008095030f4002d04580b2000da0280d401c140000e4040e0130a401101d00381910799039902c1260b520307107202200400c401f510446050500b00b907000e2030340c52580381d001d589040c0c80c0c0003d540c0354509140e04400d000c40c110303882c2c0104014040c3c0007061001000b42c80d07004502c5051008840707040a98594100301d940c000103203440491102401d0030040358050710660f02e03900111203040c1c90b01301041c0c8414040c3d100003400d50312810f02101e409442068503075000315001c2c00150030000c5682e82c0041e0440207401c00f2661240d81c0f583c410f01880c0c410013a00d9030b0400c480c001c104071300305a004941307100710822410f0300454a0381c40b02851180198030181c02503030002503901c107150304008001c00c643c1c04101c000044298000c806404141d01280004404240500e4001075215600600103081c00d0003d440c4266590b5800c076000e0001c2c407a00408010800d56070b50030310380340c41e18104451030b2005489140105e1a00b0f50622502d60000c003803202007003007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 639699595 1250 639698345 639698351
    0xa031a0907030e0f010f02070c0b040b0703050a0203090a030f0203060711060a090c15030c0909020c0307030c02040f050f0a0c180504090203341212110106051801030c0512030409 78
    0x700c1c4665501c0e00c561308055864a600c1d0050400d18902c080c2c1c05030503414815024800303a983d5a0520394503e004501800100b4142000b4404c00280914000c04041d580c60040e00e042012036030010b003a80c407044d8019121041110714030402c6290038041d050348880941001c1404a85021070b990f175541009214071002c40da20f82540342484a407002c00d600506242200c410356200c0b8020040242510001c450b0124207070312004074240d0301314004c1c0ea04492008005608110b415202203403204541501641c1145d0b90f902c1c42259485a03004603403240000215048980c00c101e44850111080407060f04100304000700b0809000051400a20454100325804600b403e1070b800003904100c10781102c01091601400101c2c0e20708076415646001101c09034812038101e41c0c601c1c00c4c08100d244040c0040c0211303072801039030681c03a0107001d600019000300c0c00005112038403040800ca42c81d40d403004041e406050301004200b0098010f40c0840074081c10b0f9040004038945200c40c60366402035000300c050302a1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 639700845 1250 639699595 639699611
    0x4030c1101021006150e100e13090506102301080610110613050106050117070c26090a050a0302030307150f0624030b0d0209060d0f03050a031a090703 66
    0x80b0030030041458422111040101d00e9031115602a240c040d40b8800000c035048039140d032460714100c40f6101c421510740d15a0401c1c42140c40c00c12408200d202102c604407507542d8041004150100003080c455034003664400020380c10074210990056191440703102c100d0740481d540c1c04990f88004081c1d003000b07080d80d00c0c3c4000b041000c1c09991034854004486120b12032601000901002290b00c800030500640080000d15156001110074240118048c1c00e914800d10124640922a43c42e80b00e420b1b000309410b00380040c2d2003800000e40c82549510350f08218010030000554608a40d690f001010129898503c071031455003c29100d0090000c09040c9405c01c484001403007074280c100c00c0b04004850310400c14141c03540000d0000001652603802c003d444082c001c044140039129455107650010051490110243d082180d503810060a00f50070500d000501d8001581c94100030031258030070b403501601c810000c0b000504441e44028071082150600074030728040d4417031b40445e44d0000d4803441c0c0460032032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 639702095 1250 639700845 639700847
    0x10f020405060a0c0f02030f0a1a0f010509130209190b030601030f032d05030115090e060f130221091b01050702040e0706031e02031b0a120f0b12010504030c1101 71
    0x103203941c0f0081d407d401154480000200c0100380640140c0c07060300b4201c010030b07034413400f6807007807004840c5a503a0481402c018442883c04070750040e8842d040144071040300c50150b000c90401c003402d441007201105101164038401c4032a01884200c0c0400390010500c644c55030f102d040082807542405001d02041031100717030a0b1070407880312103074081c250703118100300744105d0714001e1443d4424429000c400200500707050a40d8410210309003140c0c40d4141c42044c0d40c5520b4200004c40c0f11017040f1590100920040f00540310080c0003030001000c0d5404914a14006100d8002c40c641c002041c0c031101e030304038591014405003864100d245e0b00200f803030210b031148054400300e0001c0c4141994602c40f48510000000c8981c0c1c150014801004000b80000c402c6505100300170582c0002e0b100c03040114011644200030303842013009442011100d2a0104490261108203011601e44a80d01c5542079254240b010b400d007014103030100c08150680003000b10340f074541c038010010301080b07d00905242840707551000b66 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 639703345 1250 639702095 639702113
    0x90c05040801110a030c050304050606011206080609030d0c11060103031b080c0604141617030921010507050301060c230d02010b28030602090301021306020d02010f020405060a0c 78
    0x34260800080154160b070004901643d08088a1003001900301b2501e2000b09108a050b28062035206000b88074649501c0010768407614160300300c42500d5030303079172000030403801c100300b8980209941c41c0a50394500c2400d2501c01034440d00c1030071000f440000a42d13824003110000d542070442e078062805040318064542d90810350004400d02401c1c02401007000316102402007a118000d610583d0440711020001100d16110000c0390f4803030716000710450b01044040159030404e14550540400d5a181c812040c001070100a4043c20b4810104103900f100c2c001100c3c240314164000002c2d013401c40c01c543c90264014031024851000030b003c4440c18200305004102c0005003102000e40006981c507004801200034000d0107500d100611800c490803c520354071514001d4042c0703a01c2204124840142180c854074084d50080103032a81640d400c21941901d80c1120314400058402640a480e1040700700c91b0080c00e41d44d6040c5000d4500c2e104110410040c2e40b00e01c21901c06042c40e082c6011050402c0c1811620 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 639704595 1250 639703345 639703349
    0x5070206040608180d0905011b02030604050604150203060f0d02120d0c110405060f10180608070f080624070204020f0a09090905061b0903010c081b13090c0504 70
    0x309201040100c1c0032034014003103520841480100c030084454180780d03075650700601150040410390440381400113507c6140500c103256400100880031603d10703800f091030008121000e8469820400901040141491003070400b441c000c1019815800e0407000030b1141141100e03050302c18000d4460344411515028542c0410060b000d098501e00e200001d0054901c0c882003108441c1080440100c00701490140300d21070203004050100c0707076034805010504c6090081025000140050384511500c2104041004c4010381920f540310f06080c02c2c0300c04082d080b011b02190580620980c00704101050311800490140300000740d08109007a802004101124414080069002400064892406e9410300000c05190b00c1964401925a03a102045d20840d6040c0784020800c2c1c01c001c0100b10000d1074120084007449030310780300314508088040000c0c00c58820360141c0c0c0115110008104501a065a00180c20b404c04d0032451300d0002050450146907009010701080c45940d81680c0a4483c400c40039500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 639705845 1250 639704595 639704599
    0x150c0d0c03110f0c030709021602041107080412030909090f170d0614120a080301050607020406090e01061511150c13031406060d0503160213020a08160c0507060e01050702 75
    0x480c03051100b40c03e5120b080100109019100310700c000a4079400300c0c421141441918000b2070700411169013040050116500c0829148a00340400004a041e0740002e1004201896902034846a0307490b0140408860f40d100003a59840d009284c004190641c501a100d01c2d444958406240345042c1002d050f4021400707055901490b0150104480d10440461b070502c4234100c070004080c1c0e40c00704800e80d4400380e0260082508400b0301c01004a0304180018040113032004001043d4182ca90380103000302c900c000c05007e25a03440d280d00b003061801d58941c80c05607255a00e00503140d040014211076640d030000084040310021100004c110b800c20100b47e07072520b01c8480000c508c0e1640c0317042001204d28100400c90040c010140400c5551404000500d4001d42c058007560610054490401c480347c01c4003030036600900703100c1c0352407100e0460b84024000c1c245a912642803a00700f2881048030a000203041605001a02c4c100e1000700e0702c001b4030b81c0300b203c0c40e910703100c00350025200049510b4003509100035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 639707095 1250 639705845 639705853
    0x20f1e21070f030507270c03060504050c032403030a0806181303030f02030118050a1d070e0c2110120c0e07020c0f0d03050c030703020a02150c0d0c0311 67
    0x30400c2c0420540302c2c012039000c0c508942e410390b16800c0703420003000030b48692105800b4900b0803591000342500481080703030703a038240081c04643d60800b060599500703d81740080c04900008210509803000300303101c10300514200d5010030440310300100369a840355009507800e014110000030030666a80782060130030101c205c40c2400504051080b481602d81c0c030b020441c0480e00f0100ca201115070603200f52412140360708805541e980f0711030512001480c028100848560325044900b4120b281d000131445d203810035000a051861522000003803c1e80054464412100b04200e001018460441e424890200c10204800280c6801e541c800c0383c000a40e0007a0120419865111309107c5611125070486004109211044d9502e0204903191040c07407040651024410000d05054140b0407041003c5900c2400c1141c940b80d1079128031072a41c0c0101b0400c0300184d2100819404508020301c0c1001c54039040302440d41400d042c92021078446101030821001c00000042403002d140c4501d5010045a545138188c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 639708345 1250 639707095 639707099
    0x18030302031017060402121507051306020c18060a03200f01020312010315020f040e012606070302030408090607050a11030d12022a0703020f1e2107 65
    0x180203504212a0b15102c07144000000031030304000050300f80d50f01c281001070f10140c0d565031300300080b0030710000390784919109023105015041d03d0814030034050300c2c0f151030312a10785845806e00100080650440c40854000c090f0035001030300c810f210521001401a5084107655400011900c03070b10bc40c0c0d101a0200c49200700300c441c2e02d549052840318903042550b100949420300f00040e1394034031401c003454032a51803c000400202da8251403d80382e080800360b0251500c0e8000a0810903600b01d40c004084010070840100000400c03004030318035501e00c1e4070016038906074240d19192207001c000d0100c001d2580000000d420080c0100c1101c40d40c401c018206503c905031420703c1940c0d9404220210741800d0014445840c0d0720b000264000c010080d5a04c1e150803400c024a0f68010350040c2c00301c4000010724103240000d03a880c40040b10305100710349000b840c0700307072460042050034001d01ca07025015401e003803d405003134801c8a140d00d010300b10995801172901c5000700362070020218114030030128001c02e440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 639709595 1250 639708345 639708347
    0x1209060d110c031209010614030c2b14211204030306031a040b01081c0e18010608090c040216021c060f020424020616030f0f06031b0e01050609041803 66
    0x95500517031084008205a50b1100c040412000c841c0d030055034158032000d50000030780b034030040003005406804c01001d00b49895101c084101c0310143c40403560203c8008180030071080400100c28a1b90b80300b1101c8040c2805c18401030540d05c283c000e44200c1c40c103820000741c02d05001e60460001541c0c40182c0c1e40303842440c488000c010744001c0e00c084400740500300002507044c40001e01860304041110500c00b2082c8004d000351020b1031000c42c0705400c9181c090031000210305484e00c1c107000f48441d4035000750702e280c00b103225400d00d828240c035684600c5c0305100107000200350350003100300c031903056568140200005501d521000841d08004181070308040701000ca4100030b802900480760000c01450002c0300141040981845400305500185e101c0c20001e004400341307d656102a19075410f0004941200c8030440c001d6130521240321401c1502c59208008100d48060b03d00400428800d012101a0424411251000041c4900ca11822000c2000d118580da07d600101210b03c883c00f0350750303803203c403450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 639710845 1250 639709595 639709627
    0x3021f05040806100e090111181206131a100314100c1814090f0c0c03071a0f16110114100e011203020d030f09020d0c0302031209060d110c03 62
    0x41c100d10385100344003003403001d21b0500441c2d0b030440c40c03002054102419044071510f03c7c2201288160310002c17a9006d1044c0000c01e100c4240034800701c910351050700060342040302495440e80980901100803604009518691801d0325043d00c0d805411441e401d2540f41c1800d00d081003481071890032500c5e15640c04a1541c000d10280d0502c101c00505400407136841180c1040d06a900c2c07401500074002c00c000400c0824018070481d440380070b46800d1818a1b280000c43e52560700b004008030360000d00004808800c00395001990351090f024152400d191130040c0c81c070001d5544c42003503841448040c0144512020303003900a1050240440054440c516024001024030748461281c1911060424004220b40174091f12060b040e50b01074005099060620104400410b0007408501c0e00075038415400c001680d440010315022401014010f000504500426061600c19007001d152500701300b00301052a00c41c1829500c8450002d0300c0090820806030b05891948605a00c040c81c60000050020301122050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 639712095 1250 639710845 639710849
    0x20030708090705040b0612060102120403060e1002090d0b0603031912050106030905030a180302040c0f110615131b1d0102060f0109021b330103021f0504080610 70
    0xd001c58450300c1da600f00b800100c40c4440c002541102c0200a2040701c01170498505400140601c12544a25500b171b00d142029081508101e40c000d880d07070420590402c080113030000c403c031124000c5181a071148000389141800c2140100002c16010000d00c090340c00b402940c0026a18149052002c500f14100518414900b82e10036083d03841d010008c00c900384a481404032182d802801503103004000030090b0741c3c54141d0b80960140b800505404001602c80b80221801d40e0382039240d1014002480b00082c0c40c1445c0f54060400c103034044da0400001c464401c001141c00a415507072459a0b009040450015144030703100e410301e91801482e14582030390b00c180003480810020060b40172902c0d0740340c012a11a8800e4420212068107031005110500480c2e008000003821a402030440c084403c013164105140302050b1407200e084415010003000380e01c0d1b004180304074900c2d18051650b04503400128400500c1202c0d05040070a40d844904082c06403040f1405032a41c3e5044502070b14022241c0c04a0517054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 639713345 1250 639712095 639712111
    0x50c04030302120301060c03120b0a030c0518090d0e030a060501060f021c080a0203090109050d02071d1006030e15100302130203060a180609110403022103090420030708 74
    0x10602032500268580c1524142e8506c3d59030a00c200c0507640b011941c4600340b03902c98403150b6903070380d40303000954400c42c04100940c0719041071800140760008201c0f82150002d501581000114104a60314ac0701050351041980d031400c183c0214001c10000c0b1b45400b814440c02444a46841c001103851500140340e1890344a03582d0031a501540742c0a8281d501241d42c0e41072601148085001c56402013050b0041c40d031000a02c0300029142079036440f600c0c0380070140310350000540c1203440240079841c1c091041c0311020386139031003419080c1171030b900003041610f03240700e00000c040e5a03104a001072442070180180803940003510080b42e08080c540341c00822200d00c000c80c03082905001c1c25002800790300a9901c160401444107800c41d1a2254561640804020f80c0f0501ca507101c001055865061040c0410080f250f085a40c80c4c3d415441800080c41c0d0415015841425407250000000400011104114400d68002c50f165400041c0442283c03050400c44180b558040100702c1072a0313001c0c910b00d00c2130b101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 639714595 1250 639713345 639713353
    0x90c070203061b12150402180108011205032208030c0304060206130b0f090f12040302040608160303051602060a02010b033003090c061306020c041404150b04050c04030302 75
    0x207482100d59500111569400f54080180110150303401c002200c1c56129803075080e40c649440c07007500003500700e90209225907420b0709140c00352001560300200c11405444011101e250780c104a4071056540c0c02802c404822500c0c0c42c0504c41805503c0c900000c00800d110012241c4501e004050300780c490b001f5020307100051040f40c0018102c0420b0140c404000e40e000b0181c0c5003d07403100364154609002c01003440741684240c501e00e21004400700040400b0300c140011440d151402e520402098402d154401c000c030344c2c02100705012031840021a0300c121703981802d105130342e40941d03e00000b40d0342c407050300a940100081845482e094040d0044110000200d060300c007020325000d045000e0400790314104440300c0b029008505085203800080d07410400030300c120389605441d000016031542c03115030054110625030608010f129010002d809680404580501c00b81e04541c5405c9082c550050000c1d1540e0003450400b0030004040e8401113007088003500c244100d28240400c10240d44c8a48421001449 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 639715845 1250 639714595 639714601
    0x509122704180b060d12030e06060301060806160903050111040306180b06100306090608030c06090606010e130e01061e06020703110906012106150c12030e010605090c07020306 77
    0x9054400c004801040c05007924107a500c9440f00c08039024002c04883e04102044105404591480c0340340c01c280c81241d402007520314841c01d01d10b040c140e002d04840d0007a810024140425400860b041e644003040e040e2881507444081001c0f244112540e1000d4515460501180c0c02c000c15500208242c0f40610401c1c008d04111502c00c1680c42d0810b0006444c0b1010030b00402e641389000041502481c03d1443c020a4040e1200b014000710349007a400305a055000295102e40c0150601019a021b024030018000f140741c8800040d0039441c21409407032065408090150000c8510b0340068410004040204a11034684644040d2080041c22070341d4003441c44440010913502c0000d02c0c206803507004040c003a40302040400d1280101010300954103220490101c1c41046600d0031801d80645181500072032400c0c58150080344808083e6801820803c03000304c180c0111b481d90b400c0c90507000091400260400d0b5200e02c003401004150440750b444040c070414005502354000152144600880603185907031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 639717095 1250 639715845 639715849
    0x150c24050903091e010309020a14010305161b06060e07120e0309240f03070e040b04230702010b030f010e0606010f09120c091e0c05040501021005091227 67
    0x10141524940c2d021000c50380481c1d1050343c0d43e421030740344d00c0f040c10041240d003025800030303200c031400d034001c4000c040200520407555070b45800b465821000506000c0b850003491107004280c3d44801241030070103022480c480c000c00019134003540c01400344a1980142c0e080174034000304a1410001c20101050400b0300103410060040101e5a000400402d440300d5410100140010311051000080700e4a0050094841140764000103520501d02650381c0003410401404003c22609503a075041d004919019035440d00140c2002640c1c1c2220341444c41c00b4082d65034080813805004220030403601800340e64420000810150452211300044500350740d61555188011030719030000002020008052000070410b07e010740001c245418002c01400d00b0040e11260094240c4015000c01e14501e200d1403401079007040e440c80707043c01044c4036241a510385880c180000355156210540c00600503605d00101c2c000e1742c81003141d08210405814150380b110000900310071800454040000c0c400306489003a5428 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 639718345 1250 639717095 639717097
    0xa14030901050405100e0c091003050102030106020a140102070f111201110703030501150e060a050c06130510050103051b12060709031e26120a0c02010b010513150c24050903 76
    0x46d2059100500c2409149001c000c0840c03009851400f55064641c00800402c0c0f080c0005c5020304416002003c40c0d401c40e00e002010f00380015003080f840d91051001ca4005440f909502040c16000107411034803809000003d10810903281e640c901350341c40c280ca110820044103010b401d4581c081e40b410802aa81c50284150310f20b4041c80800005032140c1c0700080a19298016040120503071801d1410000d0b80b801b41c52a1403c01e035041c42c68083c81144050030003104200181034064a00340c28443c9501d10b681b078503a18040c1d21034501034099425001c4e4001d80710000e0001c181d904510440b490741c10704802c05850030003140415112000c0c68107414000042c840b900c1440b0561120014100f8a040c03403540d036007001070103840480d0110400880305100c41100c5040e008181507880001d9212601d40081e003100c4e903500c115410b008040c001380c81c00f8104001d8010444171040f040401c592892a011100c1c00340c0b0b0b6400405a00c046a000d60007101140341080c61540c0109003007101d030301c64820361035507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 639719595 1250 639718345 639718361
    0x30f0b09070c0510060b0304020f030102070201140d0f020f0a0908121e12090723011e020114090304050a061106180f07030605060f0103090f080a1403090105040510 72
    0x81400300c0045880d962090080500d494094802c0d920000c401da8003040560302107520549038001c000c4103002c20361130140f030620007210084008600c0c2a280d50300281003e16112440c107110480400c8288020503142c0040991102c0414110340d92a075001070760700035410034207541c00020055180400c0010ac00604400000001001c407810440c1a220003158141009200f0058030300501c649120181c201c10700e1801001d100e40a40700c040d04085804080c0c07407650301c0c2940c0803441200301c00f40320798000c940010181c0300b43e481810b0f4041c2c00d08069015050191401c48003450031820014040c1010000d00103039401145e9a001d4581c0d5000f04480101e4003188a82881d00008041010100401585c17107812030040192804810305904550070021283d105490403a21001000020710300b10740b21a1000c0001d0904121000c420348800086d100c1100e401031108400180c011f0034035004509040043c80e800581665030710708001c40034060407003900c00b2141441000344140f2004114059090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 639720845 1250 639719595 639719599
    0xb031504020a240f05090105040618030f0309180501150503151c0302060f01080a03050307050d02041211030114060d0f080a09080f0f0a0201030c1b12030f0b 69
    0x58106054195054a400a0412684107041800000c3c800000e1411201c0d0032099468904180e41422000b82004400c54804001c00c0810000006107a800105842c181c0380b5910f001c154800c50800001d1030b5081e150005440402c141c40c0d08420075511090700b100f45c1c0c1e908580b44e4034a02c81e0400c5282503803000c2c01440084820700382a41e80c018424405954858000c501288040c51403102050880010303206c015410703000c03d5600f909240d010083e00360084605048001a5858001e4498944081c0c3e03030000c00700807002010402c850b2194041d61030045c00e0060031560396a681c181700225000b02c5200300d51405480d8940e07180380c5018890f10070280b943c45414140d50761002e040141d056200c0340110b6005000360040c001094004028000d1785800c1d03200c0305d8555003815242841c041d001d01e0000303c59031041c240c7c980b1a1501242c140001340e82070030080b450001d100c4c01501d20502520803059540304034680e250601c40e81068084400607280c4003008000680c2c64034005a904201c0090307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 639722095 1250 639720845 639720853
    0x1c2f0d020706171b1306022a03120a17010f180203310803130303050129090d081306032301180902090906040512041404050a02040530010b03 62
    0x4c0d0212541d0005071000e0000022041c07424030032220588000f03040307401000059200003801e5046680340c42104500801b024243c211918541c0c00007940c0c5d480d415800011400f0100e2912446405244103181105c0e10148003580d540c0c4400d81510441202e22a00c5c42c040e9184441d03581240c240d20860340030340704c0480d00ca045a0081124400f824800c40c007a440344100007424800440c2c00140558082c511401d0600880c2440c0d040080541798107030054888114181e0700900c0e9202d40303004a000e00040b454080d03484030080d1002601c421140c00000e0b290030000540b10391009808003203031050300d2050302c040007028450042003105d4001d211840180343c00140051005603072240c50050f69050010380442c0940c0e0590100309812001d54061555a01041c01e0204100060080144c080c2801505908052030b01d032090f4502400c1000003400303142e441000c580d00d5070180d0125005018040d02007907240c5e059058203200001e0f0203c2c41e14102c0340c01040414a4a01805003d1030040001c00038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 639723345 1250 639722095 639722101
    0x501080c0f0105041e0e06101209020a0b03070c12030e070501050d021303080301061e080f060f040606021b06070305030c1c0504080301080f1c2f0d02070617 69
    0x1100c1d914120308505070502109000002e50a44410003180b52481040840b8110300c1ca4500c03064000034000d0060380c850107001034035074400383d4400c070101c0444801110200d4060a90700115035804103a8204050702c00c000030411030159000b6441841d400d10440c820360341111400000c90864070030f8400c110300743d0030240041006621840c06000c2c0f0030b01046d4010f103460f40e4803048041c04015580200c864800101c010480c40313070040c01110780c1000c49811f1900e91098202c3c000d112400040103541382004410100d0301c03686620a0350881c1070070240c4200900d584603140070350703141d9000c02c010b6040741c4081d04000300c0e42000c0050321000c0b94180c448078103645a00b40ca00c1d4036500003810301c0c0c030200e071040b00e101e0503002c0d603001d20390040d4002d048040ea00e504240760942031140c00400101d241d4090440d0000302c8061900c1008450b040e46000d0b8811100c0d101440e502640da6100082141c2c129a0f0b1008065000f18464080d84150b03022989010341d5184183e4920443d202494083d5901e5400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 639724595 1250 639723345 639723349
    0xd061b0e0603130302010b090a0902100503010e040b0a090b0f060a060c020d080a0c0501060e0f070c0c090b01031d061806010303020d0e0112050a1a030c060403120c0f0f060f0501080c 80
    0x3d1010160300c00d000110766190080c0108000c2e200407994807400c203440b481180700350304040c02600000700f160728007130b86590705102c0050f460885c041c0c001420308001e02e00040ba03114259002d02c40c0300350300484144a5040148070007030440001e840d000d01c1420b84c2000001c015011702020859186d000e0700c03607516486d41f41c07a170440c143c01c20740c0c4900501510000b5040020030078410f402c090480d44000c1c7e061030601d07103c0240d00080007030070081407102c2414203c01090320400b000c01140e07400240400d41010880c012030203031280b010350b200780003401c406004c00040080352051140e0f81e440000341200c42802c42003a81c07840207110190150b0000e01c500c2481c244110512840344e04181030081806541e02c641c24122602110300d4545507550308480c08543c0d4900c85540c0000320210f0042c0350300180e54002038018411440000c01000e60300080e40c208078002e040c95036216401c051880704d0f0180317074104112801201c0301c04844140c40d0140310081c070780b001c0c4111170588580320014070b18491103c007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 639725845 1250 639724595 639724621
    0x1401140904020d3e060301230406090f0209031b01120c181403010b10050a0e0a0b03010b18091527070903110414240d061b0e0603 57
    0x303810b0700c0c440d803c1e44098804100034030b0100d00354008015400c5000403402c2c0300300301d1042645071481c440e240c10030040004081500fa4043c910303d0104582303503c082240e0001e0b000304002d034403405100b800c010941380804000c1c1e010f4040c1d100305034103649080301c8031800303a070250024950442c081264041c01200c40c90895101154201c0c1508102c1d8100e4201200c001100300150300014540032035503c00c400300d040c03c0c06800c1b0541010765000c00300000110020340031303004041200003000002e12034031074155185c40c0000c2c020103030110010390720350710340d8070114003030303218202400180b001241c00341000c0c00c040d40e4951080a400003004101c003d6081045164010791442403510328040000d03041e40700d0b1806006000301050749516480920354a0009820719401c40c09034031440c03820401c00c40070450016940c0e0300a00311740700300b075005050a40924454000940c0303a900111046056400c1005550000c4090300064282c06801c07003122108543c48148003140f160805018004207440508403a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 639727095 1250 639725845 639725869
    0x90303040201270812030106030e0624010e13020306011d06041205010f0608010507180b0901030507110a030e18060a0b2109101506020303061e040f140114090402 71
    0x1c911520907544e80c4054500d0a86070070b26040905800100400000d9014420055690260409800c2070f28080c81007000c480d864002c19180000c00620b02030440c1c0c85052054401c0000602444d0703c90429580714000f9001104d5950110b0419412024441400740c10580400c000400c0076261604040c4e9003480030000c07090442c0d4540d00c8814000030040c0a0003100c010b0600080002054505004018808194404100c00b800e000360024441455000211881c0200a007000305454403894022600307608103810080e0f403405813034a5030082540c062800007001000302c9421400a14000740c000001c1d40c150b51040e44054026401c000c400301141c0540225100b14004882c0c4030316a9032030200d00c203411600749190f5000520400071601d140e201d996800002c4140303a8841e18104203012b585d0380310242955100d0358114010b00c0e560711380c400800b00800c001030001d0051261416128000c2d115004131038201070070715000030807080f0b404840c950180900a046038299207a94007480420000c0e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 639728345 1250 639727095 639727157
    0xc1e0c0c091415011106010e041a010b0c010c032a030b3c010206071101021c05190b011b020a080604050609010605090105010806100e040606020d08090303040201 71
    0x10300c600203007500080c0b04028031041e040c0000451072801a01d0621000b1440303200078107000f5000c0c0c5480681000003655030565000d120389180701c0c0c440341081d02d000300452503c40300c5100b550002003441d260040107405141400d50082c03145012440c002d41c10b440e4000d0481d1402c04800c2562603007d1490310800404180d41d050003d02e81c004c01002c600d80b100c072201d402d5100b01085000048014804c0c00350700380319010040c1c8030940d1403101c0000f03444010180420042100f0503280c03144000c0c084d41214400b40390121180007003800710114601804003100d001030300404d428080d110800060240303c0c00070f501613460480c00a100303440c0032a49841e0182c10703070300450110f801007510441000054051401a4000d15440c90112182808c1d20460b0704020300070314801c0700400460b40c002c02c4007038001340100d41c0801e64074207020b03046428540140800d54010300b4003c000907404e401240704003d030215581c03201001e81c0d07405da0181d502d02c0195030090010f80104850412440c14000c511100242 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 639729595 1250 639728345 639728363
    0x5030705031309062106020a090b0d0b01080f090307080a0315092703050f071103010c082403070504110702311823070e180a02010816090f080d030c1e0c 67
    0x1500cac202c1480340c01c4045c00c00010350751481203075581d68000c030040d070748a02000c101040760724000c403100351680a200001403101070007003401030459000742c000020b0307040c242030080c0110756190aa02c0150040d20346002da5500c0040d1160304840600705558046505600c0d12868082400c408000320350214006545c040741c010f8001080355000c3c02641500d051343c4d0b071940300d07905040c003800c4026a01c4002c04002001c0741240800207440204040c070490389d0842d0006680b0341441541d401b10311440d100203500031840d840b2241103001a41c00522600070141d09003070b51030103003043c403400c95883e450040403801007480342c1400102c0188030800030b4101c0300a05040b0301d00d414105451b11200f6001840d1070b030101800c0290303041c2b1b03e00740514401008070040124450940018050b102c000e000603030350400300d440c2d44148034001d13440c45000b0554031407048030450755904070036104c1e44c04070350080c0002c0c100300098400d64840c1901905000491040300350081c42c400c000e80e000c40d6004812960700729 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 639730845 1250 639729595 639729599
    0x60708060d140708010605030304030b01061407020d050f0105071b0b09031c0c1418010c02063106030b0907082206020a081012060905030705031309062106020a09 71
    0x80004502c50841d000d8000615005041103002400d544458002c01d01940c4140004c0011400d0130305e4041c1118130904020701030b040c2c03400801602d446a120007035004214101c1e440e080150008a04510701d40900080125480d0700c1802c4600000c43c1c4201100f50f00398040c00b02c0425511000d09410221082c106c906c0c1510540600204a035a40c0e010010305965030b01c2e828000f07030401c007000b0700c005500300e01a24240d0080212591580039520050402102800356001c54482400310703a00e152a40310011401000904500d07040480c540c0c0410000001d05000a4924080d015059000b140241001c0c1d555490641c1200e4003000104082d0078044085511303900b0202c1c0e00700d0020120b0103070f10050303500c01d0385400103400302102401040c50340c03404100400c038207030f030108010703007503651016010075003000030b0401c689140030f5484003130900e02001a181c840c0c0c8103900b090310111801342c8014098980d036100d0180654100f281c807000d142000344d0a41d00001c0241d030040c0b00382e640a00307041070340c00d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 639732095 1250 639730845 639730853
    0x9011e0b3106020c090c041422020d1508060f102106151505090604030804060e0307080d0503040303020c1504060e100b0a050603040c33020d02060708060d 68
    0x10018605074446121040c4040c0329890741801400c2c0e00a0040d2a039800342c0c00c0106c80d1441c0f40c0b042c1d00ca007644407401610840423540d0346001c03180100340d1034660b8040d0045645030100095000f41c04a4121501d0301d030309070300b0039109a4603000440f00321001030b0900d5900c420b00708105140050010000060001c1e011600c560350014485100da002c0801c140743c0c045030b282010407501a0025010100d0302840c0c10000580300039200c0c085a030b0507240c0151514000e2011406a0150781c03c0240702410118020521a50043e41c8a4910b00300b01c04880901c2d6503220080c0e21038403841a03070b5002030020400940420300903002001d00200c25001c4901c000006100140710410649d0102d42998540a441d440c0708000c01c500c02c56411200c501304134546184002417014442d511a15005110200009041c061208116401841c80304003141082d089400f0b0b0003040b2418503003500701c42030100e00702c0b2401440002c420380c51086540040c504c5445104054420b100028002607110030401503120001d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 639733345 1250 639732095 639732157
    0x7050f0a09210f1211060903031b0406020a32010504050c01020f15041b0807230906091005060c03130b03330d08030609011e0b 56
    0x280280d662210880c5050814a0707000c4a1180080d81c2501d0442c40204049008590a83c507141da010514689001d03a1903000d0391909070f0703a00c10030403030f0049000704100060007000540c4600b900c004118280d040c003076003088160007140921801644049407030030000d0040b80e00036040300715080185100205071132103824072220700d0041c20300a035111014042004410000800301030400d001034840104402210703960303442c40c002c0584500420074041782c1070100d00300d911404c66441c4500c01d46940e44511b2400c1c2da403116403051949088400c00000c5041700d00c0200031500040052250010351107500c1046224040035041982c61003030340c000054259501c40c01070800b0044e00b806962550705c4180078400030740c0b083e48440c14042003041041002c54000000c8c000548603803070120000c1107103d114510500d031082da19030b00402d0081401042c00624400743d84200c10803a41b80c9401d03a2540d03021115000d89c0b5100b52039505050b4002d02486c2e48600180c10344802c002e07a01c04088075010b00505103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 639734595 1250 639733345 639733357
    0xa09060b13081b0f0415060507170406080103020d05010b0415080105010f080606091e0c03040b13020a1a1201090b03190b0a0b01020a06060915121a07050f 68
    0x405500011000c00700040c51008500808540b000f42c56003642c1840102600101c0c03e40c0310f4411850303030340c0c0c14040c0c1c5c2d13441e4070080b0601e120310a401c18581c0c844401800710751100c5010f07a5540d0060011041c000300d1942202c050b540300b2390b22000c0c980d18503405d0003001003554008882a54907801880a191500d01c10b0241101d070b04a040703840203240ca60b1060071594181c002060004541f43c003480f140000066554001c0300c140c0f0300a115566a1806d00b40d52400b01e090204074076a85828040008105009107024501440c078894040d114010407034280908880025007103e0511420000407410318815085004280a180c2c54000058122084060243c07c200e1403140d4801c2581c2d660b00b0100580c0c2d281019032080310b0100000c0781c48a1031414001040c201010343c6170492084680d1003802864401a0303ca80300b07110254440d26110040d000d44445030321050b8545400003400c1b001d03150400421a005400301140f0780b0000e00b00840182c2c018400b00c03c1c41070420807059012040002840 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 639735845 1250 639734595 639734609
    0x60f0607051f0b130209030c061309020a050a0e03060708040303051902130314070f09110f0703030c030c0f0c0b07030209033910030f0f180b07051c0b0a0906 69
    0xf0301000403004120480b001d4441c00301060f0b01c18800441c00d40c0380040d402a07904001c94245855220817150421404055003004540740c0c0080f404584042d0400c002c0c10b120070207500c03a210f05942200505555101c00c4030184001401d0101080200b40070342d004a400c180001d00d004242c0ca00424940c3c01c0e6404007010282d200250402081804545400ba40c20540310a000e0400940351020f5454120498018001110340e11500d802c032001d0345104079060110908000c684800c41c07828060004c02c22110001c01090400d0303c0d0089051050201601081071921075000d0301c409a11040007030740d0011b120406155080190240d9035030100400104408071a101c11000e030a4807004907050349260301552501c0450350100c0c0005e640b000c1c09802d07100203620300040d8440801661801401e01c2034a07a8452a1500c41c040031070fa8101d0342e20110306070045d000d000300f80d104c00c0030841c0e8034441d81c81d802c8072805681060300c1c0c004402d82c00c913101d100c1c002804031042588a03141c05003100c400d6448a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 639737095 1250 639735845 639735851
    0x53718050c12070f090b0103060504090b0402090703050c0f16020a0e010807060914060c011e0b030f152a0a030c23041511010903080618060f0607051f 66
    0x41518250300c841602c03648110180600c039150180c400d0855456000c1e03205c959172298a0001940d20a92101d401004000d0080c0101704040c200941620b1003580c090307001c1d030114000603486078060b02409000d070800c060060300c1c03c1c65401119102d5006400001e6400414030b54060150303607007505030070182040d09c02c220700951522480a140440390b60201c030604c62500e04c00c0080d000c1341180e5407602502502d445507641220340142c1d0042500d82c1c15002a00300050b08041500030702d5000510a42041c0c044910000300c1140c0340ba612440202491660504400041d004540121a00301505000140a58004078000e00c1e01c45070f802030000b200019070ba456a90a1031036101c103076001c2da2204082485420003c1d9071601078507109a003d12690b00307002c28156081e461140c0b100420f111b04c0f141c002c1050440c04d00d40140150000d80b4042c1c4101000140709035507a031581d040d01d0098400408006050040000303110f1b06420054080c2c0d024000c03000c04611070307001e1030920428805412000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 639738345 1250 639737095 639737113
    0xc030102070b16090803040308030c0d050106091419140d060c051e070201080a181b030501050f0903040905070c02120703021c05192f0405371805 64
    0x742c0700c18043e56610800c90125400c02030400c000c03088030252508903107100d41d00c1d61840c00c50b0381c0d0340c0305540d080c88100e4505000000e000d41d10900b1380c004c0d20140d06511030080700940070002c10711211615036091501c02001007100540314912441c0009029164807044000c07529014201d412842c0d40c400419800610204401180d00c1c0d030707204261509000605210b66900001e20f00c9000070040908144d0f2100c1c8240b940e03509850840001e90b2000030349110352a4100500e000d1440343c841160f0541c02d01001c070380007806c401101c0d840340821200650409183c01001f0740640005490102840650700b2540301603211240c840642445042c010048140755106000c0036180c1c4c0e103071184580703000020040000b0008680904645e05a0300500104800350415000da40f0069217400650800d0700c017180890165034046248000f01200c1c10401d40d030f6004031100406c0341032074254002e40e0900c1410220101400200c140c00150503000040c890400c02d619580c3d91940c0c507050301c455000500d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 639739595 1250 639738345 639738361
    0x10e07030309080c0d150c0908072c06060711150f070c0e090304030b04080f1b06090307120f0903050708010911061201060c051f0b01032018030c030102070b 69
    0x24604607482c10342d56070700036a4451b101c580100035848019442240c4801021800764403400041018082ca401641c600f02d035201440d03840e03050031140003601c06c0540d004810f2402c00810005100b210003410750f0f4500300d5a0b544880a40f4000c10030f00d50302a001c070000988544113200503014006051034110b41d1503800d400c0941c40c5c009203902080380e4460210801c0f10108012003540c040700d500c080d0130b46a87c1c070b491800c103c40d8007544015900440c00468010300041009105005144000307080d034000362078082199460384104040a42400d00d0680e0303180c9002d218140d1003201650f545880e04400340c030f940c1d50f1808d2610940c0b00010350380d1640c01000520055003071204d10203d080300c2003480c0a5008100c4400d0380c0d014130581090050310100c0b4028414107200c16100d101c0075029070000c1480c03da00d60303001800240d4200b8000b074500041c041c0ca101c800303203030b8900005d048410f003400c003c0030010f0038041c403282054058040c01000d0080d03455031030074005490454807400d6040076618080134 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 639740845 1250 639739595 639739603
    0x210f0b0102061003030504090b060d050a06290a0e040f0c02160b1c0b2e080a05071409011106010e0f100f090c26010503010e01140c0a02010e0703030908 67
    0xa0401015100c4001308000f98100044608a503c0f0300380100307240102c00300241003805010740b02075004d81882c00b000302d9880c450f400181903c1d0085c810b12070001c4d182001009600b54103200c3d00200c1c1c3c04009014044d401207613010100708005001240314807640565400390383da000d580700050f034424412082c8030a121000d01c006401100c0c0520f003421540e4902e9000c1c28078160000c03a0081c3c0d1000000003c3d168001e2000c040c3c221400511540700038005202800d00d10800041c3c0010803032004644040007501400340500c54650300e118580b6000405100264001c0d1802414007184455003e00481e081c402a8020305605811320b00e2464074581240c02c4403401411500100c260040500141e180c03020a4400d0701c0c082c85000980019098055034a003848070702c04404011090540540d690081001505980007600240014052000c07100d00f03071640c8001010302c2c060504005541d0580c0103003d01030701d40d224030012071502030110500c0d0410781c1641047d00020380c0b8440504ca000300800c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 639742095 1250 639740845 639740851
    0x15030e0105010803282a110103050618071b0503040e0601051c2f0703020c03010b010f08060613060c0c060f0e011d100c141c210f0b010206 61
    0x94091441e00c40c00c248030312100d030307014178000c0c905110900706116810303c039040d5925819009000945101c401e40300d411100403101004580c00004d1407004040c079407090081074002e010140121404a4814140c1c1c0d9841e07400500c000104520151a2030110301c0200e1121425405500551354542c148092400141c0c0c00510071810700100300120400350b084640441d84160318850001001c0303241c0001c03072454032404070018000b03043c0a041c0c0124000500003c0070354521a408588c4240c0100040c582070700d0306c0d0b40680303000c6251030741d1405049010700700f590740c0300e0360040c07226162052072407480000c107506410140000d41005016003c10540480500107841541003100d2504c0b0120780040c030704044001298100141690301c800d48071000171640500307017030040200d281384800305801070841804000954580545031030007940340c180403035086100d80100500785103150305c00c074094803d036200404407540480300f0b800740c40c0d010250b4071940d140450304840c04501200550002442d0080c05 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 639743345 1250 639742095 639742109
    0xf060d170a020f060601050a050f2206030b010c080a030c050f070b180105011415120108010f0b0d08030a0e030412030e0109060201021215040209040f092319020a15030e010501 77
    0x184288540346c5c0c0c200c800d4641118407480c1060b52461402d0081d1064019000d02407000300098800400d007803111490141900c03980e03942003203101120001101c02c2005007801500c0c080b801c10210829034429004401241d882e81840c0d840c0401c1c4410010843d07100440035180745aa034800c1c0056010300c40c80f050340300311005000b8406035050001e09804164002d90451040841c10b4074a035500342e0010644201d40003035003a4148035030352220001c4c0070b000010102800607283c5125540f8034940084070780c0b84140c018150324295a81e1a005000408003c0602c0045100900001501050b0031409100440c42540c903a00c0c4102c0c0c6a00150116060750404015a401800300c00c2c3c200700c3d4400d0041d44000d507800c0b003c541c1403181011038000d116000105070402d04001042c6007884698020300b01092040c510003101d058181c040040d120101c280c4031015410800c0300754502403148500c4290240010100341c0b074907981e1000c6401400d610f00c0e440000c00d071210050701491400384905d41c0100340c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 639744595 1250 639743345 639743353
    0x30304121d121506010f1d0f13050a2f030a0608030c011a0f010f0c021f050910050f03040611042c071d0118090203010303050d051b030f060d170a020f 66
    0x4844002d1f044815940b113005500c2c02142e2500703820b51740d41c05a41c0c150400a020443c89110504415020309000c44008a0f010304120a12141c080030011000608030010321a040c058500d17490040705600c003411602890b40c403100b000c9501001440200354081d4003000001d03645504080f984011400c60001502c00e080040b400c3c0440d0760072007142ea01e500018a003e030003000c800e20004004080d112202d1254074100e96048402e69000802009654801c44050b05a13103050001200c46216051007000000c1c0184003140015106410400444441101d50350400f42c0341c404455125a80007402400100302116140300d092414400c40d030422180e1401c0070302030342e9004001259110003c0b00504020004205440846207004410003400784110250340e41d5949080042c0340d030700300486070007525181c03601103002144519401100c5c1040c0201403400c65450135665403c030840107220a030070260001601c0c00080102c11552118400d800b0050344036002080c0080c9032500d102038011951b44 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 639745845 1250 639744595 639744617
    0x70c0e0105180a09080a020106050a09090c120503040e07050403140604171c05040c0602070803041203120209030d030218040203010b0712090f060906030e030304121d12150601 77
    0x252100390301810740001c0d08402054607044440d0b0f00a01d00c0d00d03005029100081805511a41d06410107401c550048902a00c4d5030786402d030311806c5030243c4e040103104040c90300701000141e04440b00a25514007a0050324201036480744403140383e442c200c41100000742c00003414010046008140f07600b50301700704020480c9181070303a107074208090700ba1a00192010b010516440b1380d81d01c6488080300c00c00301e0305d003485141050710f0304040140d507600a038409801656004030700c207100003080e9011244080d0709160920165182030f28100003041095135066020804841551400c0002c01380d0300300385650059640341e5160040320717400350400d8031f5803166004100400541c5698015103030041c0e000391000b200d904600000f07a17a1401203030f019000010030f0310b500165140e04030b00c4903c1100e8558400344041d040c0614995100e10044800808000300e030f1f5142c9103080d100e088007003a000303504d0300c0300d9460f2454480001c840780300e019044103030760340b01c1a40b88010005030018190051028245440043c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 639747095 1250 639745845 639745849
    0x5010203070f171519031101030e03030f0c0313051b0102010c021f0b0d020901030b0f060f01080a0c050408070b04080c0a03031b06090b0405010905010c08091e0c100203070c0e0105 79
    0x3000a4034804070401640c8021409a40f680782d20030001160604d60324120744c0d039103003240200c000c003501b032030201c0e161a85040700c0072b0000c01100c0c42919904e070401540d549a000c0070703240e60005041222021200740c80c034400182c0030130004044004103504195182e00040009003940ca080c003081e0304641000e601c0e03444009029401000e40c150050000c2140600781c404618903070b0400201a45c01620138000205228001d064180a00905e030b4880d003250f41d4a00c24421052480040180080ca43c080024a1800541d10107010a07402d403030300380c2c5840e41d1000007078941802500040441140090300f0468a5420040441281000c1e50b650b5107041c516240600240301c0305600d40e0a4020401a0400f000742c07070342c0600da10540c091301c1c1c00d549003850f06006008100e4050200c0700303503180c07800320420b96009204030361042d400e4400924141c2d22082334280505490801011a80304d8086441104e81c0e64bd9604c1c0e080400a50040d526403c003400c4c480c11a00b510352054106480c050010301c01d907 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 639748201 1106 639747095 639747137
    0xe07090e15060d1209030b0a0501030c0b03060a0f140a170c1504080a03110c04050105030c060a020f030a0809060c070c090506010e0a0312030608060c19090f0305010203070f 76
    0x1c8c0d030b1038441ca03000310394003800050003022000f80200110a0484001d580c008405840303801400e07600c0045682c10000da4101c1c2d01c0000d804000d01100e82051009400100a1201031a06105030034618580b50381d549002d041c01024a580100041c481d440110303801070100400b1500c46204070b0a0003400b815500b0165242ca01440079032401c20301c0e003030041c107050341c000a002d01420800e52013049441e5004ca4025020340c02014044043d5140a03c06403112003410b4841c0189403402000303160402e02d0003001142c24690501038240401e400780d2032007050342c1c60710100103070742e80302c0c0030051324000b01c01e40a1660102e0008408400c1140c0c80050b00032400f40c503102032003519194601213817110400c0303038682840c440c2071120400c610b001c00580c000c0111039081c00700540b9201da400034287d45050704165002e03900041404181d990058000300a0841031400070785154100590a542c = true := by decide +kernel

theorem cover : BRFrame.Cov 639568345 639748201 := by
  have h0 := BRFrame.cov_init 639568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 639568345 ≤ n) (h2 : n < 639748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
