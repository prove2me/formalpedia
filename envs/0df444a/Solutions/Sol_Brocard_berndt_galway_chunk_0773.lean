-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0773
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:41:54.707236+00:00
-- url     : https://prove2.me/submissions/f4792010-0967-403b-ae06-1bf1c2a979cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 138848920 ≤ n < 139028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 138850170 1250 138848920 138848929
    0x20403020402030f0f06010c0b070c02031c0c030806190b0c0a020916123308030d0606140702030312042303191106180312150a0902071208060609 64
    0x5448444d9000d488030140580c0d00301d001e0406134400400c0c0307001d0000c00c0c05034550304c461500140100051203402c0d09031000b503403400d020b1482c000c480c0c050034003c0c808040711700402c01c0701d65810940004540102240030b81c50043e204030f40c050f051140c85d200c280d00b890b80407401d6610815a0700b0a91046140750401a00c1d2180c515105c0e03009a20695084505c15402800710604140007020407458007804001e60098100078444828080101c0b44100703160007141c0101c1d80d038075004000c0c20b100200d144850315946802c070206a0b801a902c01180c03800107400c01c0d8440c025000300940c107070401c3c80009030944003a20110340c8240101c002802c400c0c1036010180181d00d02d40c1200c281c582000500016200d4410400303e4041e406140c10b01c06404880c0d113090f19540040c02401109020720003e0100c07400c00c00a0301c15074609560728180da030608892140d80340f035562850781e00030703a5081d03000150407000b4401c2d50182600420340b84807114010508035900c0c02c0080807294861418800305070161103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 138851420 1250 138850170 138850177
    0x5130e070e0c12010b0a090b0a030e01021819060903110109050402070309080c0f031c020f0607081b04030503030711030d020408150c1314040b040c022a0d0312020403020402 76
    0x44006207103540300f40010840000080507005548007010420001080c19400580d40341166801e181d81501c400500a049010b080c01d01c8403850558004a03284141c0141442110541d06080304d0460340721a038256800504030300c40c0f01c2d260124141e2003041011a000e080c111160031030500d0101b24290300d0328005005ca030084442a000a48104401e10203088100010510840201c0715101907a8506000075981d03840c1d180300440d080c1000014440c0180200010400036045600360703044c40c580144010086c040403146001c00c1c21082038400300c87c0803010120340640e07030010007451940c1c1d5040010346e4552865414441c0500c410084e0385401046407002c2c0c000f6290100c0034110f90303001c410700299000b03400750107075401d52410400d104030100103074601000c503400300c0303810b6414031200d00002d80101017181346c00740c04c2810f10448010f003a5003c6043c080d032880d03003e5074103c5420343c90300d04030300c40d00b098400b507410107004100d540119018000d01d48240d1040314015103410344035404581aa007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 138852670 1250 138851420 138851431
    0xa020c0607061a0a0f03170f0f1309110901200d030c030f020405010c021509150a1b1101051b0f010b03150c0306040b0d06090311070603050105130e070e 67
    0x107980d0121601c00581c071140f000d5030000100c030034003111400d01140500b4804c061200500111404041c10079042944080d2807a08075000b1a06840b51501580ca0200ba44008106c40385807144500104902400e48204030341101c0c820700b400c0c28404c14030011340b2036101c045440340401003100aa011407a1041146480c010280d5801152020580101800395142c0741d030705000300c1d401404184016640300c2603032031400c0c0d01250003408140c02c02c0c0c00c00303072144030b00710310350380c1100d1800032031103a5010800082180d40000d90724040300c0c90b485040700e80054400318000381900941c649809440d807090f002f0705120725100241341c49000540458038588402d0b111a2651a5104d905091ba246800c0c00756a980e290075440c1f001c500e1404002c01000c0e407100500291096a4513451b00c4940e4582200f180400780d0300c500d003048a081c09081c09800308040070010b0045210f000390214201d846802001d04842e0050000340800072200804406407202d43c48a0320244201c4500003503a0000c0350215000e070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 138853920 1250 138852670 138852683
    0x60c1f0c0905010c0f0308060d140109032a080f0c01090507080c0102030309030a0807050913150801090203060c030c070b0106090509010e0606091e0402120108011503050607050a020c0607 82
    0xc0350114060301c845070540c0b02d40e040c0308240400901041c03c01000101d2103038076140c10045695400c0008803170384c0b04194044c0540b800020714403564641588015005030080c1c584030102031041046a07602030108001c1d08034800c80584c1e400000301000d0103061030305440d040c02c90820780100d154600f1951004021359060344003a03001c03c807803002488003100c401d00c2032010394550701d004001140d4070301c05c2469042c200a6900001240303d403184007503414204008046e03d01074040c600c1da0202070b03e0b1050803038000049200700040d400e20144100c4c10141d5003e405010380d550780c2c052254982d007008040704004201042407070000b5886112030ba001c0e00241c0c99982d100345c205800e000c4660b005030808426144000240a00f55540f00140d071055101210740006a00c1c0315240b600480c0058940d40303811500105142c041600710700c2c3c000e4140c54810008000090901c0c00c1841c40301000d01c800b610540102000c00c2c200b42c450001003150720414011074a81c0344041001c078171b15034440c0000342e401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 138855170 1250 138853920 138853931
    0x201090506071b050d021c020109050405010306020c01050106020d020d081509280203061c14070b0702041407080606160c060f11070e0703020703030b09040c03120507080405060c1f 79
    0xd10410304500608010b54011416821590100d14182e00810003030007c038040445820446e0b00c1602110f000d8071029005003d80d503900d140c95000381d0050740c0c3c00a15942850004948c0c184002148035045110342d00400a4251441069032000009070041020300244c036800000b07501c0d054200f40c040c02d068540300c2074105030000c4588441d0541c41d106240c1500410912840c0c0d0b07140711340c02080c0020039a100c141d13a411450018815403446010440c5406040000220901a40d0240811500036203051000c001080d0200307c298008590790381c0884c105101007051824001d02614240c0c030142c840f6070384401641ca0710545201142e2040001802c030180381411036a00480e42050410500020100c0c80d04180700c0f00010f06008141108150380402c13200d0606110350000040c44101410521982c2442e040c82e038040b07691404242c2e41140d18001000f110f0784204122408a604200c199050904010810901b64040134031241c00388a02c0102501008804204584040005da800100d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 138856420 1250 138855170 138855203
    0x21e01020910020f0d050c070b0f13090b18190903120207080301030309052e0e090103080301030314120c0904060513060302090c040303050711010201060e01120506010e0105011b020109050607 84
    0xc0c1100801040301000400d000410081c000015588c090701d900d50121900c4024484401006000e03001c070524030000c404000003403101d400d9010485521054810b1284440c001c01e03041200381c0c0c00c1e00d0b00c6040a094110b0181309000c10350010070070034480e19041081541c007121110507a000f0500649100b00004010410190091100340040201340d07505240000d540741440540d20030031203402003216100000f0301c1a43e101d420401c80c2c2c104000c0030410350f940c59051007859a0800d0102b00e020620307607500c5c40c00c4103070b21105494102c0c0910101c2082e940c2c42752441c1540d6000903014a400903211900428540d80b0b1282031174980b10703152400100c440c42c5004000c006200540b80381407202c020041840400d6111007100d076002d4011164100800700000104e00500c21130b072119507400000300c00481c2c0800301000c0345003514000d03c125090340e62a0b2441c401c0b402c82c02c0c4100d034003107005c120180d108500c407064100c01d0207005040c030103034450303464000c01d0f50303580100c80817108030251550b65071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 138857670 1250 138856420 138856423
    0x607110108010501031817041503091b080703150941030717130312090608010e1f0503060109060315090305030f040602070f03080106020d0807021e01020910020f 71
    0x3401480d09103010b2006040403603c40755043c1500c07001a1400c24590848201ca1f01004200d80c0100301c040300180c070010041c2d8004004008044088800301d0445207000d00d04060312800c0400c1e0380782c540140c81c501d442d40d034500c0b071440d0480c60f40c683c089443d0304c43d40d001714001104419446404080c4080c0802e810b01150402c1d5040b001c00f1120030311f0011009030101800001e45e220300d80d00002c0d03944000c6071401401400d0160400d40b0b00b00c0f062441c40401003040e010b6180c0507084407511661400e9031507440070380351501b0900030402400456800100342e0070203410842c0d24807081504000030540c41c0c0000c04d09250f400d820080311182c83c0c034010401c01000444410000940f15803c21201800e80d4005100d8071000e40249103402c0910041b6007800710a5044482842d4840c101e005400349528018016900902c107440c0035002c2c2c12040d10900380a0b081903403041245501a000710700449020504003c1c0010841c030040d9824461300711503413540360040e5a0002203030024407081207102d4041d07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 138858920 1250 138857670 138857687
    0xe010219080301060507020307090c091d010e070e010e0d03050306100e0a0302101707030b040513020f061e040b030406061203090506070821090c0409020108040204090c0506071101 79
    0xe0940d2841400004042001d040680c1d05464491601035510421400002d2400e20141c03c190061454181c140f600c1641010058048801600b11a040c42440d1019070400603001d1084040c13001040d400520a240716035400c03003c642050500300c101d08940c10105600740451401280801d0380041808410300e8080c224004c2d01d4802c2c40d04402c08134141d40440c240e12181d20000307004400351024040650b005140c2d169070b500580c141c0c80d0091608440c020094074400c80a503000380e00d0314020608480b42c80d1070a0200c1900a4000030350540880f09000c1142c2c40706d51035a101650005112006007682c00060005090203043d180c1c403400c05007031920403038019500841030002d41c4016036001039003060252080f680b0440d6840d4036140b2906015007284070701103c0480d1200a2929500d01c84140d1400c54000d80150040703500b081c20003004e000484001441c041c0c0403c607107400203001880c0540000d00128440e0000760b00f00d0343c0d07510120300d4981040400711002028511620440c4d640318030700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 138860170 1250 138858920 138858943
    0x3150f030f0c06030901021b0307060c050903060f0603010b060408010b03070f060909020c07051203070b0105040507090302040b120609060403030b150f0c0726010b0604080c06031e070e0102 83
    0x1405054203041d0420307039030300440349085020300c03008000500602d00a41c152091110502c61050010a024242c507440781e100c5041190440e1030220401d240c548980d0a46580c401302038010940b41d12881030f80c44d04040b0040030142d0564031091007405a8039800042c3c030041c14143c0010682070701d05400c041c00d010300c0c0c0d08042d040c5d2102c000e003040140c0d070180c0f4883c2100c0703c010300180e8516a1002c89402e003c1036030401504402d41c041405d01c0210300000030a112030084003015500d9884d541003100382c0310f09817440d800103a03d80109201500d416401000446401010030072540c42080815060031021101d4100c141c000c0000c00080c540c05000b80e15081808a4601046001713200b20a03c00d03028042d07031008102004200400c070320300e04100f804c0c09006884d43c22000b45071224581d1600300c52100b0500c0c43c2d5424026503000d01e08100b01958280c9040001401081406c5d07010b110154000501d020051145012a02904054030a103540115103a90b103500525a034140060302e4124032140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 138861420 1250 138860170 138860173
    0xf06030b030318090403020102070c0b04031a06090c0d02040e0112140a080327061006030f0e031e0d0e03040303030b0613060e010903050f07080d020d050901030b04060305010203150f03 81
    0x200e003038604140f4041180c60000ca80400707403a00c8505049009000b400c500401d0b030008502d0102c0c070640c1250140c0b0482e44034401300c0c10429444113501042080990702140c000c0701e103901081c0c1d103481590150050071180ba00040c01c050341d8442c9400340c0142030b0300401c40500103114103014086a14112865410070703900804200c20707030b556030140e144001081c5020044030340c80501c105071000d9240d1a0f8000c1c182003150b65a0070310151900c801e409a06c51400420318204510198030004d000d90701c1d90800c090050350420071169000d0f181c1180064450702d00761402c004600d01a18507128080881c00210011a02d40b0304502e0003400b00c0d840d00c503550788500340a12410601402c8080360909032412494080d21901784100183d031414004e4000500c0750051000c0250400d000080d03003412a1808412101c96801c0c00340c060b6100c0c600d0a40b0300d0000f90007040b910360310f94040e4005400300d00c8060000110655640c4545003240c005403629001c40d46203940d0f0221600e00718903402c5e04010100c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 138862670 1250 138861420 138861427
    0x833010e0d051f0608060405010b0928021b070801090507090605130e031e090a0b0703020312060f04060801020c010c052b0e01021204030906080411041d070f06030b0303 74
    0x4581556511142240004483c0440b03042d101e4464140c004100906091045030110305003032a10341e0181c00840425405101c450000450780038070300504d541211402c40d01e03001d06002c2040e030b0001135440942d108040404244c4c4110000c40c0800c400e0300180703083c40c00056030302c94078500300e4100043d590101c416281001c2d42030215036248020600d0740e40f600070002a0ba40407000100381140500d1007a40507078070206401d20340100e0101c0c010402141c040300c4000126440d403002c4112030007840c034042d00603030081c04202940b0701044c04c2140c02402c01481c034101c0c10109800102a14000e41068881340d402080c100711807402402070804594242c00c1140c00c01200d40e02c1c0b81418039002010854940b220411502011003070740c004020a400343d00207650b1030440c0c000040710381c0029030301200000d9003803078006000c0c3d00c00c12626018551001c0d81e2802003403008204400703464406101d01d00e550007079040c01c0558400304403100003410b0790664000d440d86080d82c060111290311943c0c6009030000c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 138863920 1250 138862670 138862673
    0x2100507050f0d0218060a0c0501201b010e0313061805011209060f05040804051302030c040e0c130602010608010609090b0105060714070608011401020307030f0833010e0d 75
    0x541c140e6083d00e6070a50b006031565001c821280030810716038480d5422250019141403001d510800400f540c601a44c0244440c1d04103e000080942c0480c0d50088e240809100d601086803c0c002140d0034042c4080000c2403042100c50f41d01c2c1551303c65041c00281481a04042041903004040035910540400e81e03d40c59501c0d000000e00b05070481005140070300d507182c000004010035a800001c680503202c00c20003aa141600c3d000702242c2c018000c0500c160151010b02207800024000c40e44920202e20440b800c05103041004051000c01822451402d00c1c14070110f01d1681c00d180c400c00c014980c540c00490018030380315400f4216000b540100441c1c0d404c20b1108404030b06002484e5044500548074195a0606800c0070b94041e000308161480c24003c0500010b0b03840c0c2e004030103e058581d1041c901902c1c4040e0b000580e62803042c058020301051101c41143c3e00e0700d0050400030340c40040c0032248913120a030002d40d925015420841c02100ca02e00c40550025964800c618821000d402e07100800d001215 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 138865170 1250 138863920 138863947
    0xc0c0b16020102220302011b080d0c0306080118060e0c010203220f060203030714031509041e140c0103050912090604050907021509010605010c1b05030703030210050705 74
    0x60402500815058400400354402d604895212004158403000300e0150b005211088400d4401a8001240482e4015240c1e108000da505002d0b40240c00703600d8012000704d0503001d0040001040149565010000794603c3c00f8000d0780607146082c04131540d8500646058802c03559221031144070741d800f402d94422541d07000000c50b0800d00c540c0060182d00388a0a08128003070445821040900c4c44a400010301c1d26000409580200340980f40c6e0714114401c1d500b0002103000440f820b805c0140c14080403078590500c00001c80d08a8010000310f1035440303016980a583c5480a0b900700c1d00d501e5200b4540c0c02010702440804050142481c051105090143c2084e549005150304d082c403c14001510300400da070780b0300442e00101800f922604039480c0801c00a911418501094a0440082400a401a0810b01c030b840140da03c16110354141d8001521aa940c101900004801c105170715440850b1075501084100c0c000c40c420703802401807011401c80a030a85501030414001c2c400d0a0021000e039006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 138866420 1250 138865170 138865193
    0x610020c01020a08030a090f0b010e130c05060306010207090204080304051f0531060302180d02010807030b0402040e09030c120309060705030a1416030b120303010e0c07050d03050a0c0c 81
    0x10004500c036217940715010300000411010400800c5461901000810085240e031518100c0c1e03565181c071039403a075a000c0c5680603040c1030390b0000e2090310b13043c400303110524086000c2c0d50881010b1045602581d2541840b034101da01940042e5420350000c5002c0150745030001c0f03074200721600340200b040a8204040041c2042c01080c555503184064032580240701012420680c00340b00303403180d190b256642c0e00c540c050000d600c001c000d0301c9000d034121620540c2d410091080782840754103a41c0c2030940da5500d1011002040e880440c0d0380d0050f02080002010001d070826103008850800142daa03d406011059240c10508492428016020303c1003161441000c03030b049500c40903500301542d507650b505a5580040542d255094005000d403000e0098016010401c004020700302d4070200700000030b00301000302140d0354001090040e40100014071001d0011301205400141461043d402d0030b0850303440604016400700d5000002e5690020004407001c503020b00c180641d0366080a501c007076041c0d181c4035103a28 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 138867670 1250 138866420 138866423
    0x6080312150111030304060b010e0f01202d0606190b030414010e0106060801082109010e0d11130603020d12020309030115030614010e070e18070302030610020c01020a 73
    0x50001d840d0059008559408180010b582500c4c1da901e000d14160000785000d000850014964403074082c4107040c411240140c244058503030ba6109500005140c034208440c0000c04414003841c409561004000641c81d400312283c4a40f807003500707000721620b030b141120040101d0720480404400030040399910300305e54144c40f40c02c41499a20380d505c0c10300c10b0070032400710302104a03586000110450382c0350660040d0b041d60300c41e0741c405003aa43e90303074209981e40800440c86010111080b080c26146104032008143c0144107040c01501c0050b410b0010708040a840720546a0b034600000401442c50a05001900700c015100108040c0742580c001c1001240e030800000c0404061801c40b402c1103000b003080d80c42c1d092000f8001e00030740c50402c0350381c0f00070155480700720f984a0812442c04484d01c100d180c100e040e901714400c1a20700340d0700c140703049902e40f2120602540080d018103126040440b8484000d03ca04180c0d100540d6a08000c0d0602001404007100b1a0864100e08030186642e81e010550300810b5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 138868920 1250 138867670 138867691
    0x1a03060618060402040b030a0e0f010506030d110703060e030c060105101e03060302040501080c090a0207030e012303070804030e01090b0307030e010b13090c0609030b01030221070303110106080312 86
    0xb40d84003000f0800a03c265005003a602002100f041080078064002e01c94030752813035050722080c01d5079820444c00d84006031810b0f545900035854250309544504102c15004e40c0310300441d003045035207486560403103501880c60482d40d0030010304184518003c1080c24014003054511108244260340b00a2a03c208100c000e010a86609403164140340320341c021101a54004008000a503034554540346d49202e042841802446442c00152103c8110300c00e4130f1019405482d0684200303000c0c001115641c00d0309100802441c498400c181501c0c1a49000d1440f9030041d80340e400d090309103403d01403ca40b000300c10301030401c44030301d400f440149a4441074a4020816003000b11b034103120100128003604143c914a60028500720900c0103030007982c0c0044a920740a89841e88801e81c07a4034040710068074500000c3e000750704004c0104018200300d401005001e45031440c5102e42c1c4414800e1300e05018540d131040d0001401c1d00700700d0581040a01c1414020007032103009600e001e0b41c2205020034076000400c41d2354035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 138870170 1250 138868920 138868969
    0x131a0406030c110106080f25091107061b0813030905040f02070605090606091e0403080a020910170c1303110301150617010e0103080702100905030304091a030606 71
    0x2e860107203000340d0b2003100c264004c0c481c40d41c841c501540e0324000b0f1880c1440d24801c00c00039082c0c40200c0203d403810050b210740382d86405800c00000d08007070030141541d45250402085000301007040c0c1c0c491030128401c0d80e45903000c00130300039400030f1120f14040d25106440c1032100d8440000b940221040b01101c2c2e09840109400c003031508148001e0140200c09443e280c10841000011800441c5440c41100e040700c586510351a002400552050480076001c90500f840e4042004607000b102e4044e40058038078005450403618001280000310074003c2900030071048000020100c2e440ca0030f0590100f0410066810310104075440203144580c0d10014088200880c150b2802c5e8400390040e0584203145000c1d00545980c4070f1006010010840c007171462060400004207466040851060490b0b40111006003044190340030000d2000c0e0018480062000c40100029a51000d0001d84002c1008550000f18000c5001000103007600340d0480d5407090708503004020803580d0b0300500140284414110804 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 138871420 1250 138870170 138870191
    0x5030a0311091e12010e03090907030b010819060314011a010305060307180608160f050108040c140f090112110315070c0812010b090102010e0c0a090209060f070305131a040603 77
    0x410190202d8401035401d280f1b51035040740340003000b0b1500ca801030310021040d0f03444610403801c440076503054600141c04038000c5162169078580c4003140d07213045040021003d40e0b030b0f6a0b9205c0076100e00540101a5103800c0202114072040380c02d0741c8188000c2c02c080c00315140800000361124007600510f0304110004000040ca01540e03403141021f4644041110402960513040808104071841011152011a01c020a441d4480ca9a10340075550000b031482140b411300c26800c5000751000c4c8041e400094201a80035542c0d00c00c80031074001c200175004501d040b41e030350410900e51710140c2c181c1c41c0030303a000da603100c0c0c044005030114692001651401440c604040c0ca804021740c450500e8003201808844000b048400310f0900403d94104260000c2001c1103e4054864680580d104400d50000000c170042182c102d00303800030000640002c0002d8038081c1c103a01403205940003010300340e0009401185015040c8034a40700c003c06450606000c414506450300b80d041240705134083c5104141d104c1080d043d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 138872670 1250 138871420 138871429
    0xd0f030b0405040303090c0609031a06011107030b010906091e021308010e06010501030507021906111c02070c060203040e040602093106090213030f0f02090405030a0311091e 76
    0x2900c80300800601c0142060305005018000800e825148840c020f9800112640142d0508044076806040b1625956035a5008940ba100080601d81032101110520442500c1030201d00f0140d40708202103d91941880c00364005c0f02c6060300560401807070123141000300820580205000484402c02581d125401c2d201a10740c40040e6000c070100c2d60170101203051103c000b040b55070580740280e0b020030403a40e6021089940d251981405040c480311035501c00046407d5802c064110140c1c1d0800c6890200c6000d8034140c02503d021640c4071640c1e0106c1d01c8003c11560b2110480104042d10003181450f0401403d0340d5010005440204034176800104059981c8030704084291038009550f507965500201d408507100c00c4611569102c00c03e00c0c0200c0400c4078007407031082c1d40000c00040c2c0b0114000f0b06654030300c054200303c1941511005503002c1e00800699440c0d4809104034400c2d006503031600280f44002d0240c810740010342c81c8456061110545039243e5224004e8020306100710b0901303074803104001ca0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 138873920 1250 138872670 138872681
    0xd020603010b0a050712050306040506040204240207150804170702060a0804020f060406050715180b0c1b24010e0402091b0d020c0601140307150e102105090d0f03 71
    0x401b609503402040340483c0c0c0000246225450540b0188441d64403101008124401d40c043c070811410341090308005914401112209000d0a0044034801600e50510110040760000c00c0701c00501004100302c20041798a502a0b50508002e4140d42400d0550340040c505028060003941002041e400040039540d4407400d000e41c440c009068903540c0c5450710802001035009083c15039a20361004000c000c090040e11601c000201c0c8542c2c2e00e1115002550b07441c46103d0040e203643d801c59030034050501211880003407841040d00340401000f00100e2400d0010030b040745410074010070010780c2c004024030303404070782003d6104d541190015035a50355894000d25801c0408940080300c40c0c0841c0d6034100005e56801401c0c000320002c11182140e136525100c1c140708003003400d0640c25400400c0d003041480c5031100b8001c0c0f00440750511940001080c0d01061141d010500c2c10740c00200b080c94003040da00c0740030003504031030b81c00340009000c2d501d002e5400c2666010380303441c0d1104002511400d10140d51080d07005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 138875170 1250 138873920 138873923
    0xf050904030c021003050106030b0a030510020d0905060705040f06030e030a140c07030b1008010902030d0c1e030c030e0303030403020a1b0e04050706021507090603050c0d0504120206060d020603010b0a0507 90
    0x11303048a036141d21004004000c240a5400440d01d0400390613154900076105030300700c03035002c401000071400c40405000650000318070800c0300e47c0c40d0034940340003540c280300c06803103400b5a0f500d83e41c8a9252499440d9402982d600c00c401f03040c5003505910700f400c3c020045441c04691420010380811000208202620a0310344c150194002c1e07040200c01c1125141c0400d000f0344c1640e00644142d512420b4140c200c410340380000790315a101c40040c3d0315407402401030b03108031806500030383c06c090140c0c00071030180e0190400890000d0504c40b00d103030406030022a08018150140d006504503d882c3d0703000b80d038035450480040c240c1400801042c0500d81800030300006051241d80020981c00c06142290342c03038115004100140c0030702d4100492990b048081c0ea48101040c0d40e4402c01249824000c0d4018280038200300c00d0030900300b200a054038214000e01e80514030610303081c2c3c55003440440003402d102000e03080d50310424541c80d09c2005030351a035003500d065070004a0540d941e408050425600380c400c5100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 138876420 1250 138875170 138875179
    0x10506070201050f2b020a09050f040b06070f020117060105031308090307090207120c02060301120c0b0a0e01020706020d05120907080f06011503021e0c010e03031017070f050904030c02 81
    0x9515014203d4400543c942c0385c40c240d04105442d90b240e503604c00f64002c040c910b0b4002250b1020801c140e25041d4000b1038046070281c00050341485030b03404100c00350300040095801a048918400455a00000714200450301c0e90104804d400c001000800b10311020308101d19000400e11070700f05000101d411181c0ca400c0080403202c00c4c43c0d0391400c070300c041e4100b00c2c0280c4201e0000f5041c80c41c182d0044004103844d0750300611386461603080050f240700c00341201c0d82c181e41d000020000822902d00c6000207100c4c28000c2e8807041c4510214000091070320310150444800c540000c420076441941000c1038803c1c600c071504070071040d60303500000c0c40e107030528a5120b41c1c014415051144200c48020903a070f81030320902880001e0100d88808203070140c3c4900e41c0e002e1400081503401201c04c007000400b4020000d2441d002040d03400c0e541e6401451070b041500e81170413580340c45008000e81010090014459408031014280452601c140d44d00d43c0142e52040078000c0d00100001020140308602c0e07480066802071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 138877670 1250 138876420 138876427
    0x2060304060b040612031409060318010207170909070207150e1804080304030f020a020607020904050a0b0103060e0d0c1a09030d05010e100501170604020f0d05040602030417040e010506070201050f 86
    0x5c2d242c0b40e020007201041e004211110325a60360800600d048800255002c0d010600d9915203410344605c07501002d06040300b555082c464440003d034000404104030310387d105055100c011a000b0030040120160202082d503200d0703d020001600011003e005442090504c540d1a01a21000c9003e040b41c81001b031100b076501e07204000811128030040c1d80102d01940d150501c0c41c3c51b0740010b03a83c600c081ca002a41c809810b1254000510b1b060a1590f80036100da01543c2e05000c090340e4442d01c004c401e810031078045880740c19102c210541005008002c094625011081c5025900e948540c0d69a40246541c203204440010b60039000c00c001f01d83d100f1148800401c000e603540c201c00c0c01215015518030784060304c591400282580b0030340000c41d4051400703801340c0d400c1d160001000004c1d0b102c007201d007841c0c60080c170000c0000b02f1240304480c4110300800c40542e8902d06442c0104030031030b40d003404084035002840244000c155813080c6a041d00e6040d1500c0b5500c400314001a240d40c001c1c031451514440000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 138878920 1250 138877670 138877679
    0x207030311010b1f03050106181e091505150702090105040903020c031e0705010f08070825020c09070302071205030c250c08010608030f030a021605031e0909010302060304060b0406 79
    0x103004004130790310554041185076201d4104642d08411106941049171400400740041c222440308000c04034000c80001d01e0080d0f952080310160b440c1c0c50f803100140070a4441c01c01c0701e17013803041110f200b40340c210417203904d041c1003680028003000043c001e05001e242d0352401c8004050007081503070040c9500508070b0b40414000b841c0b01210181c080d5044c01e0340e00031a0b00c0020309501881c03003040355954545540002d66a2008100c0307080130018501001c1c040c00384030800c80350f200b0004070441880700d17074083c0002100603418403105503009042e190400d4410441c00011070200c010500d4040c0030761030025030340e4940b0407510f003042c000c1002a8002c03480b40c040424200b2590300504a80e54800d03003403100580d668007030701400c9513114450300d03200d90400c00c00b07503000317011903001580d0140302d03404c006040a00b689094003501c000c0303402c112010740c000100d800d0041904c4280e282c2c484031f10600c007071a09105101240c0240818400203000e00c002201240070007119400031018540d0150042142d541d48 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 138880170 1250 138878920 138878959
    0xf06030f01180605010c1b0e180105012112030f020f070515090c1c060e0f25121e11011404030f0f08040b0d0c1106070207030311010b 59
    0x2031040d061450b41c040c1c150300005805008400c21078a0584a000305001d4545a8074042805028070701c1509007c6000842c0102c18044001e0080d1071100050700c942c9004041c20f800c546040c0c001078a103225000402c4003007441542001840350f400110740c2c420888a41054010b00741c0601203030301d072500100318403141072860b901034030300c940c01101141c0910100082c1000341080503525115507130840c41d4000501d003000114052090549524403600203019107441c01115401881c400041d0002c0e210303c626905e00300001a900d90302d08400d502c00342000788440d05c0d0501503205100c105054050520240801d62419901c44c1c1a41c0040c40b541092a01d00300580400055000c1d012680f010910000000c104040d14250303540a4070006030a071041e19070340d8001211039000c58600c40300300000b09081c01120007a25442c000702d90007050040480d08080d024004603000391456038030544c00c001009600080800c222909401d01000000102501c0e0b4050020b13000c40940010091a043c42541407 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 138881420 1250 138880170 138880201
    0x412060207030314150f030c03060405070e0903130303031505130903180e010b090f120703020f090c1c11040303021506040c140c010213080309030d09060203180f0603 73
    0x10070f0350100040300301d443c0c00700301c40a0b00340c400c070548030600b140308281c50901d805040035000c0c0003022500d5410180000a2810500b15401c44150b001701303000300500e041a21040c0d0b08540f000c1c001c0d41c11310030b4200c0c041c40f40507100c1c80090308043d1a2f078403144c00c080c003242c2000090040504200301800c50100703000050500150200d001030b00c4200300004568426050000703407808241c244c00c9a91804d80c0706100d50700910082a4080500c00200d070443d5181c012410340c039101c0b100a002054030350300411040d14054127089002d100036408000c03081010000f01c0e400b00052a25240091210b0111314000f80200b800c4280700a00024000c0b00b8540c00144c181810000160940781030b5995030f05200a03180d04c0c06440c00820340e00e28030310b919080f0010292001044c01d000060820100101110400b1129803082c011900700280c0c40186040c14800e011041d50b55040150a5510303000000b50760b4841d42e131041881203905e0741103006607982d070b8094401c00e00d00105842c0e164205907030052003201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 138882670 1250 138881420 138881423
    0x303030f070807090506030a0510080106050307030201030209062107020d03090206030406050417030c0405030115030209070c031b060218101e05120106020d0f0e010903020d150606050306030c0a0b0d09080412060207 94
    0x14480cac107002440744414018031040d00c4001e40a0200c05140d68010340c041e402c520400c50b803001c820b220105d4807040310544c4194811200074200041e0901c20406810126009405020103041040c1c84000d41c0b1080d0450342c0056111400090355903031814168000403030f290500c2c0700d0318400020310004090541c040d006446089000300a03409864003224010070807844002c1d0071040c00000190198010304443c0003483c0070f401d2200080e00c80030b99041d407905081c81c044611550228041c0c1001064a90710000c2c0c140c10303608100420441c45000d4880c44e042240407403604021030719500140d10405c140c60400340c01144940881d43c490704069104d10f000715200740007501007003003400c0061280e40c3c45081c240f41030b15452512815602840580f4101420507164840e0040b00c1170f40309510f40c442c400080c00c40795115626402e10904040c14000605002d40c0700d000c030000c00b4407160380b005088814070404c1c880c000449001c00d1414082502403039110a8040d40f007540900148141c0c1c0d00100380c0507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 138883920 1250 138882670 138882691
    0x105090303011401090503100b060c01020a3603140a0506040b090d05040b0a0507060e060f0a06080106030b01090510052e030e190303022205040b0303030f070807090506030a05 77
    0x2030f00600448403140b0302d00c036035a4145e100a4443c10046083c1d403045520080c007a08407841c01420240703407030030390384219840800181c0340810f9460001842006854004020900940c09046101090107008450001401118150400e1340c0408800c104032004580d121060358010b140c6030410110b544c10841c0c0b0504580208248004124498421902134901c0080038a003040b000322421a00d42d00f110100311000796966981001907142041402e1048003401100b007424030b03200503e40143c811541c00541183e04000044c000039000400160544405e07060004807641c800c01312003194036095020076000240410125210740d00004000a11240a1805501103900000880464514640c0e05010b40c00200440c0800c08008021a8160340645409800d000455450b2140420701c0005081071407503080b003c0000b814035019160624204801560440c40c100d01c1050403003030002c14034002c101c01080021710b024052500346d0003800019120b07984a00c0c0c2001d112000b0041501c681810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 138885170 1250 138883920 138883949
    0x13020706050606030405030a0c050313090507030c26040f0803010609080118020906060a1e0203040f0b0304170c030c1902121209012a050703200904020f01030905010509030301 77
    0x460500404485c0a00c1d8400021072a00e4034921085805241c0b05500300e40a010420180b0340780041000350701c01507c00c0800c0040e0764204044090100e6240e180803200340700346840a0812058024081443c403505210210700e01e580f50318210b041c40c9070b5507500a03c101404070001c02c01d03640c4460f40c4400d0380c000b80001c01c00c0c802c001c48030100442c0c2e400402940a60b50000107082420031401815030001c40d030a0107440d2034000f8040131602290f40812400591012604025501034102e46c08020059465564a18103054a80c494503c4400500481240d0300168100c0340907000c00480745c801d1242030545a04041c2e141e5425090000c000c010b030302c01c1c90100f902c3c030303100e92000c038800e540d1108840c0c0e0030386440c40103c01980c0c3c20141c4003c0507009201c001100c1034000c00440d140f4103291094026141890440c034040c1800c44c840b0034802204050f0050140403a103c1c05209604150101c41c6101007104143c0102d01505046030028a107501f403c0500004680000182d4142c81040031030020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 138886420 1250 138885170 138885181
    0x603060708060904030302090f0405040b1b04150318050f0d08090309031b0406050d151103010b0306221802030c04140406240f0303030f05090a030f05091302070605 72
    0x4039800d0030b03521203a0001001000ca40080d002e54001c01c04580050720582d1203660890005045800890301580d007a40d05100f00600012480c00694184101c0400c05040034244110b804803804405010018141d642030312500081240c6040b189075a4031038100e074241040703031100603150504010108007144200300820110301c03010003912000340000d4010104400c5400151419290015646812550360034000c54a5116000c2c3c217a1428014181110b010880d010804201d54140d100c40302003e1050005008518500c03003102d4011004482d9218043c0ca00202503e010b80c0204884e10b100340f0b012181000d01c021032048000041c022802e8450340443e1100748401e89501c1c4c10b89d59140b11070b10002500007911a849280400007185202e2080710304255007220503440341e0002440320b84150300400c20585e1600440d07600d44000ca405000c0360800c0ea0340280d5801d52208004c09002c02e40011419182c405c0081e10340c0c81c04020241c1481162508800d4001c0d8031008081c0c07610381c24440000d9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 138887670 1250 138886420 138886427
    0x20408100e03091009080307060504120807020d111e06100b0301061403041514100f050a2619020a09140c0f09030303040308010518010e010603110903030406020606030607 75
    0x2600700c620351000c0c51801c169a020041641d00903000b54040c445100c002040248041001e080000c1c4203041c00941d9042c01c0c2403484185003420740c4841080f02060401080a5022550441003500f83c1132400700000c2c100403045c28450300e0403014a41081e44101c400c50880e0010b481800703400300003d00c0c425030b40c803041602070521007401075402248090303042d00300d42c801d200003c65015008140c4054140d401c1c80c600303000d44207101c885008045c030754010300c802882924100c600800038034003274014003807030900440d505101e14030914112850100c55642c0d0400d84032a04507189280009039900240003c1ca04c68602c0c0800409070300a503101003011461010300d10500640c05504000c3c0394031595000307001c000b60342c88903800a42500c400d0003940519207040000d14040d03482901c07020081d60400052280c0c0780d03d000d0000c20701050842c01007258000064065043d00d0180c0380c04101d005444080c000c8502c1544942038242c4400100008c21580c08140c217030044c2c20840a80e10281c81d054002c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 138888920 1250 138887670 138887681
    0x120206090319050702130c1e020d03091505090f0706050c060103022e030f05060607020d02010f090f180b03030f0d181a09010c050c07050405130f050102040810 70
    0x1403041d84200801150703a040059030a1200000d4a880c0c2d00c0c0c013501d5804182c002200e50244603602d40c490000107005a007000703c2041601e01e0303009490003120800d5000707541d07041308120711041c155105903030030030301c41c82039811081c0c08124007007801181032010065030354100703009059005008070701d00800c5d0a4850402c807402d0202200c014003141c1d09523001c011000e40160b16680c0d480383d040c40c4172401002c100d4500f901e036454a84001804000003001d141c29520700130306151180d03504100480050ba10400e06020a81d020702c0c0660b40d01c0400300b0159a070f91103c1d00101c80aa0b0030020020b41000c070544070440d41c046512080c0103510341c41302807580d03038000e500d1026106c21044c00f8925007115254841481c18034008110100b0a040b0780f5000d140c41c08680410800030715800c104115020240204140090545011483c10740c0040350b40c2d44406c043e009035449142c417240482c28002080c3d0041595a40200c0c18201d46034007450310034002c0d406807050210900650144001410b45031068 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 138890170 1250 138888920 138888931
    0x20102010e1501170120040312030e0d0c021c050c0a050301050601120f02040b03160f0516020f1315140f06030a051b040f030b0a0203010b040e0403021903030603120206 74
    0x5010b042c1d08009032501d8800440f0300c4c50519642c1c490306421031034030601502401100c542e0300c4956650450410684265000308010241820a081010142c00c0081c6510b500100391901003840d2103135100040d80c000504900500c40d0a52607904c03024800045617100c00010b0807030302d0501c1e03265034405050907127600700c07203050120740958020007a03216150400c03800740c58801030051600e510340c840e026258000342c1e0010340c14a01010b40c0e0b292150403520300011811a428400c0c100501c580a0031034046558000a00900f10341a82e10450b417a6101d0b2103c1d0410b170000700344181c4441c10004000400c161003084070070500381c600c09640d410000045440581301504c82461980e841c03040c140a0031001d0080046001c00c58084803818101c1d4003d0006060310081c400c007424550f0600e03103079060001e4007080645e84100010400d0444460480e0b007206c8210036411142d945604083e406c280511a0402d1100710f0f40d0100020940d16a2101044c1c80c46401d2070300b40f60038820812607543c0400c40700d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 138891420 1250 138890170 138890203
    0x18060603051308091915091518150c0c030b061f020d0503040201020c090109060f0b0c10090f0c0b0301090609020a0e120f01140603010606050c030304020607080906070f020102010e 79
    0x31385080303401c00703500041c0703091141018203030810b03540d411400c00807454110b40c9001403d182403e00000340040341d140f006039030500d401c03074218a14400604d0240010312901100d00d40a82c3c003d428180075500504016401428000d201c035501c1c180303881a1441103529520440a101101400702013440a80c00d4400e0198001c1c0303484202c400041e10756a0020b8820b0781940300e0017004030031655900e15920701070329803180085103542c5050342e46541c07900c0c1a0031407000c0c03003818004071040410007d11000c0c2c24500356030104400c1c1050074183d0440440340805084242040804200c540381c0200440c104c1c0c02d00f24040100300d07544c5000400328010321122100040560840e016a441d2001903100b140f8030003010743c4c80030710072191040c1c21103c3ca03101e60382c4008000010130040f0f00d400c5c41400020300355820800c5c41c1012565a80782c80c0c2c40000c2009228401c0425107000b030040c2d80e0f0980d00d1541d8050860396030b5180e1401c027042c1407003c00404030700540c02d201050b210014013043c0601180003405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 138892670 1250 138891420 138891427
    0x40b010807020a080f07020603040516061403061005040b0d090507091e0c020102040b07060e0f03030115030f09080a0c06150506090f03010207061b02160605040b0c0718060603051308 80
    0x81d1960b103681c2c854010a050b0700411b200c03c1015980302e200440c0950300c00c03002461131066000b00d01d00d40074002e0b40002c050051403426904411107000890307522034821500074a003400140e205a40d28001c3c1c0e0042c1c0d0103004003161201520095902181d00c02c0c0c0101c5c1102c05066681e8001019510000c441c1061103d8544c010b14180c0050781011341c060401d80005401c003500c40030350000c1604004c400b41c4140f603c038034030f84c040600e05000b24065402c03014095455036043c0303400c8240415051681e2001c05942d0340100b20150500d40c05620306582c40301075260341d1030f4070300700092821084a00980f22580350074940816685890450402c68401030142e504004c0c80a08020320201005100d40e01550200b00d50b10014600744a00c542d08180000e0864860148100c000c3c60201e1400744034550700c20300a81441000c0c0c205060300d049448001c42e541e80c691403a41c0d01424030030300e548800031081d40907841744000e10298001600350340030366500b00029510441d9075a000c40c42254064544c0c0c5081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 138893920 1250 138892670 138892673
    0x90c0109090b2b110a1d1302030304061106070201051504020f131d0a090201020a11030a0b010603020d0b0a03020f0123030403020304030b0f060a0b210114040b010807020a 75
    0x15041800740c107400034031200e00c554080001030100440d01c6118030340b90100300b16003c2080301d00b1200c0c41003210155080d4880a0500003200d282482d4443e0384c00400708000f000585e0590050703540c000540d406403d03661a0303560b03540041d10200c0c00000881c4039000301e4002460281c41441418815030303445003ea4030f00c841c0d110a0000a500500b190044000200710800b510b420310b03600d00f0002d100f02001100c502e1405019859185400307009090502d082081040142c0e0b8000b501c034141640001500442c482c2d14800680340918121000341550010400003861542541c060050300403026814448442403c0c20810070f14070b2400002c3d0301076081307124490303c0d51080f5800c45c20301c00060b5030311140c0481c1004001c095001110200c00690001500b442009482900541c001c40e44000c265a2410b01100146401569000e06803c4000201c2d10000031080c92020f0346450003400141c29803075031501108103d0444001c103141c0103a06183e8001c0c107030351040e90704a10030001d40d809003840717050a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 138895170 1250 138893920 138893939
    0x30c080d0f020d0e10200d0206060108040b0a0f020909100602010c09030201021b010507050312060307050f0303070f03020102130602060f0601210519020301090507080f0606070b0915011d090c0109 86
    0x2428801040000301d40d480f041c5244546c1400d50b6400b007120007020700000c44100240351020040c2401c0c10404041c0030b20000030300c01c2c10780603000380c01b04101060210100c00342900a010320706886920104420500091011602c4841c1c01c2c2c0388294002d0000c25828001612610010b102c028010391050a1524415109008848460605241c00f0380352045a0300c400b1b1864000c020011000c0c140c801c280a4a4601001403c3c010b100a81e441c40c8483d40b000c2c0080d0701c0c0d001e00c950103416004000d5021381010b20030360403590560314040c16044416200c480c001d41d500d030119588503082c803400e00415440d40c05802103e52000003c0f941000c4041c00c15012000781c400580340c0742411003094605417140845002441c060700d43c0302c0340041c035803031301d8a0000c08051000e800c581c0907451030380c10700c01c1e070340c41d41800c445246401650710401c031749440751030a10b0140712822841703040032642c0002c1554502101108061010300309908101d0f01d51020740d0fa21200c070855181d01040412804200c007655 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 138896420 1250 138895170 138895189
    0x8031302092208030402030c03070305070f090605060403031206031b23030307020d0c03080a032a02070b0f0d0609050601020f030a080402090a1b0201020a02100b061e04030c080d0f020d0e 82
    0x80030b4180d230030074a40d8402003407411407540c20494254000040c24400229401d00c04801000714086c103010749440c100c0801c54604c030b43c1c00701408210b000003070a0900030180d04048010356102d02400c4958041d0204048410403d0180310010071440c8036044482c038903265095841301e001800b035841c100d680e40c20020800000d62040b602118403810000c08903500c280508100398503510046082c1d01d078400107140211502003181149080600e40341005580000c0785400e039a40580d10325900c4400044050241c0603c11440075062300301080461480c1c2e05c0e8100600484003a000c507080040450183c1d0349030300515804000140c80b9400003805441e103000035680040c2030070b03000900030700c1e84400d503000504070022210150f9000595401916810400d003850820310b4881080315056140010340c961043d000003002040c8203030b0640d03a16200c1c1c40c044a0003540c5c41154551050365034104152a03200792403184000c01c0c00103d05416080c004130707c1c408480141c3d40e81742112079521040140070b05 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 138897670 1250 138896420 138896423
    0x1d07020a06021809090303040b0103230a08070c0b03041208071e0915020f0627070305101d0a0314190c05060702010c0507061107080313020922080304 66
    0x4910312150020400610080440e49041140740008810071000d210441c80042c252a40c640c0c81001000080307031400400605580c0c2c4010510341400c801c2d81010125282141c1040300360003584551020000c02c50300074032105100d0100d04d000d0301e507902002d0980d4041103c0240440c54014204143c881c0728240165100305241080c80421503200d01554070201a1191100810340e60ba0050100507105805500400070f01d20050002011407070300d00f0303201d040240c06030100e01e04440c04140344809100c0380a4034681018110350082e550303410020750300c807a000e2741d18003000d00e09602e02c41254000c00700070390310314a03500082034000703065901103803181c00c440c100b00e600078006c0c000758654103060250b500000d0718941e5241c8010a00d810402d050501c05000e140542e03140c1450b102e0007c2e0000b054400c0d07075411541c00a14030500740703125142840743e0b1000a140680001c10006001000c83c48110340f00c0c020366001d1050307500c0104d0030781c0e580400b4036400150b2141151000014007403400555115 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 138898920 1250 138897670 138897673
    0x10609050603032d1315030509030c150c1207170c12010b3f090f060601050f0c01050a061d04030206151c06021c06030c05120f0d020c0a0e011d0702 65
    0x50700384095014005c5160420b60140700f045403800619a071500034281c00c600c4260113149000d0303a0206243e9a80c03503402e0340c00128100c0100040308450410705444554000d00d52800b01854200e40051223a1000d00541a00941c61400304658640000279164180c5000c51000c1c2c02d41d0a00c65080b110340c21040521403000716a44083d010118003031031140c44107154880a42050383c03000000711320a400240404041e9002d9a1440e00c6000001007441e048002070038003075518050028402c0d003611803900f403000340e0760805c0148690500154000011140c142c81411458510f001c000e11031150305540113070042e400030012425840c0703080030f01e0161000040842d00f44c0100180c4850908542010640c0e05660101e001a9481300c00901248041c4a0f03110030080c290666994401c80c1d0058001d95001751600b006040c48074070108849040455150f049030034143c0c4002000750b4549203140c3c454043d10400c017000481e150103c0f5094182e03422180d410440300c0d101840347d908800000e2256003103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 138900170 1250 138898920 138898927
    0x60d0b0607060e010c02100e03040b160501230c030702070e1806150a0806100311010e180106030c1d060c071d01050f010c0b0a0b1908010609050603032d 67
    0x38402d4414030848690388400401d0480314010064208141905185000ca003006a06203c296001c030803901542c80c10200251101c1103480a80c24000c00140010102c4d882c1c000100b003250908805240012000d481703541c042c1d81d50702c4c0760301001d00054540102507440002d041c801e2650180c1c046902c601c55815800801051691842c41d00314107440e80c04210228241129460408a0900000d030500c40b000b4081c1d4202071045040005039840050040c541c4000789070000d80c0f05084c441c000030340c010101000019607180c034005011080c4151008246052107807020180070300c4144840807564032800003500030034400e00c142035004007600d4802d4040c01401180d8504d034013152002c80808034101c58459030424090218003c1c0031012a41444035440c12100051420f0031402d62000d00000040f64145e14040410415000840c07000e000101c00040418005070562010003114a500300c2403080d41c42d51403d264803846259126034004000c40084100c2c41003807102c41c1a501d0a56880515 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 138901420 1250 138900170 138900173
    0xa0c02060f0414100507030801030f020414010305100c020f120d1d03030702010e060c0301050103090f060e100605120a020d11061305010e030607200703050105100e010e0402060d0b0607 81
    0x385610542101160a800c4014a43c0301d0030552100380c0b0202c4a030500c40d140100e1610301038007050052100a00700e055125000d411900e40b500b201c80001110708060003075584900e84580c8526105003180d20311458001020b419510010f104142000580c000e8100100c042880508550104000c009000e450700f0103641344c000c04e950203102d1214804003968480c00c1c0444000d080d107421003010140340d44500c0610542101100c1243d0460382c0034240010342040d545030203280502c0710328007d050380f40303030411401040304046410b5802c0700480340c04100032925101000320703840f03c1c454418455880014800b006040c010307500040c2a0043c04060000c024080000740a03a02103400400410b14101c810403003560800307840803000900720054040740c81c2240c00103004032003075180e4040c80080101c01408522090080300c0280d90000001c0c0304ca86061080603141590300c0c401c0c50f0640b4600c0300000f81c1200d880c40114000c644c001c101520748110300100c500544403006840d41d00c005d00300608030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 138902670 1250 138901420 138901447
    0xb180a0506010e040b0903030c04150e030d02160b1903050c0403051902100201020901020c04150b040f033302210915060103090c09020310050d05010207050705040207080a0c0206 78
    0x24002c150701e501c40c00c3c1c689003a2408075024a80580381e44041e074802c0c418040031170050400c2c0c2e030070340e085690890a070054110084500b4008031503201e425010702c032140584568007040f0041003404c40e1034051030537940c840502c402445280203071103011440318002c20a0b2070cc40d410417a080641d20399171504080e225150742e400e00740704640034202440b50034038000842c1400741009042079000c0c0000c601f001405800030b503c03a951118014802c50f40d0302c145c0c0342c0200040d500080508180c0c00e100d40c4860301c80201c0f8000615500040c0c03002071000600c0f0320440301c010b6190070446030a07140800d002c1500380c0e513100031390083e04011618031500c0100b0b042103e42401502d104505400c01082180c5075000c0c8407609110151140741054201034114002c120950b5003a4126a403040f401039585d41c40c0b4281c0050b042c0c142e088581d000e179084032520107021054014000755406101601c0301280d81e0350422041f48104900249035810600c5a1a0031302d0080b02e20f028402d001405035441c145200c8242c070b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 138903920 1250 138902670 138902683
    0xd0c080d090608070e1e0120030702040e12040b091302030403030207060c080c07170f16050c0907082a1b01110406090320030709050405190b180a05 65
    0x50025526500401030075502c021540c4d00403070325081c8011008100f4002c00d4030f28100c80800302000c1c029400c0041e4503441401c3d00286603241d0004072000304691162a516540016800c0e4407035030408401c61415000030561521042d810f240b49403810f407400e900c1895a40001c041c607a400340740c45606066110382800258801d51095900580d9201d0728a80141100c00500e00361080009400c100080e108005c4101c9004580140c01d02000d4100d141c0450043d225a00107280700300740101e02c003010703060f482d2002c1d00c4051194068a00c5030b01113000b40f0200002c11102c100028000d03d0228041208003c04040c411015800c41b103110180d041403141e4650003503103900c00c01503400b1040c80d91014203115103046002c03100300061502e490440c0040c100035013408094810604280035510328000070001d014050b8003d0103071030f1201d41c0d0b91440401000b049a058685011b03000110b000072000000160345c4960000c10029517071100c8040c007022403450b0100d92514401c28040401041f010080d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 138905170 1250 138903920 138903943
    0x60d050a0c03320613050c100503070f030b090106050901030902030d080a060504180b101203020601061e0207063504050705010503090d1d120105180d02030301050d0c08 74
    0x101601c2019800a500d00804551080a0491075900c04080c0810300803903025084100d591221708040158140903081055100a055201c0e415854038900c0307640000142d0710a0195840d04403031641000d20540c261604410003503480f0071103074014405640500041e000c0300806140004040c3e055901091504075022001c0c2c001c00d4200c000c10004c82d40030f02500b03002d000280c0b0107001708400203140c0818240b1416004006003e8080024800508000c480c80140f92420032802000385a04019403614028059000043c1d03142c6510482c804040c044100007000e994000c12000c1d203401c00841e00e034070041149100c91112009603c2c07034036003401741b6071000e680c9603501e448007420907261a5180a125a0206062084c14001c01c0311141c1c0c08500c08962078006c0c140400c0c8c80d4810074200e00781408901810341d0042510000e00be040405500152044206200c5800c150300c044e600d456030fa240c150f8603c80142d10400061095040008405d40c0991140300c800c0c903030036241d09005003480b00c11040c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 138906420 1250 138905170 138905183
    0xf0314130515090a03150207080301030807060510050d1b050d05010b0916051e04090f05070f141b0c060a05120a180602030603120a0e0a1d060d050a0c03 67
    0x1030902940c42d1145400240d01c4034001040e00c0d12044101050306600948805040001060744e0100c040c95160101c0e0017050344441100d41d65a12458009c449400560b0709803181494800000c00b40c0c1c03100da03410700941e0801042c1022905041c0d50f060700c001e171004541d031070801441000181c140c88806002c0310043c847c0f4000b003801a103a20900c08924001410322174245811699010b8068101003220840364046503126440e20070f220300c06a1034803c50b800986441d1805240c0c203004001039011500a000c503075150004150b07442c2d412103004e40d01440e52000321600700000c0d580101510f400d09009000881500c1a441d007500000d1041d4100305103079008200f00082100344084070480055101480b580100700d4607070041d003407150b004418200240342550000204d1a09c0d03500300890941c41c00d01c000c0b01c6076105050b0238000e0100004440450094900500100d280b05a0f1f42c9072594410364840710021942d20202001050707041d0210035078542c000d90010402151034030a200d000745001d1207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 138907670 1250 138906420 138906457
    0x70606030516230907111c09030b15060a0c06060b0f04031b0311090702010902041b02010e0c030a03031d1b130207120f0504050301062310020a0f0314 66
    0x105605081c1100744003008030301280c0351010200e44d210003079030760407002c030f480c040c104600d080d452179107810101e01030b901040f55501c4c000c104c6140c2c090410b4040d00e1058410a1050700e03404100c186c4030f00c07003012140c0d110405108030003100384034620007101c560040ca000304106550b07004250181e480203140240d0420000b07001c0c02400f000e02d04200c4034070391103100010312a240d0f460b12404920408985441081440d020a0440e4402d4008201c000e0b0010410008280004104003031181c01020050142d4207010505280310f20114819550000140c054041071178140d80c228014080d00f01c081c0c40714402444048038201d0100300c03191b90103180c10b03005078802008000b0490312820102c0321000041c0100030001c0003038181ca0321001446c10720700f401c040b412a001c1090300e490040d508055059840c0000c00610418214040004c2d91103c440c020070302d40d101014840c14010b034180d0b0b1000340c0d01c80c550003800520007250301e26440c0c1c02850300b013201001505220005501c42c0c0310304141641c0783d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 138908920 1250 138907670 138907679
    0xb09031b06040b060102070b0304080a09090c03060302090a11090d05031903060501020111190f021f050604050f0603030708031906080a020112020c070e040c0302060c0303220209060402070606030516 87
    0x58071400e03013106013400100100c5240105161441c40002c200601e616800300b02c0c107890398015030928014142242041c0a00070403010028000d040c144010707031240c0740d04408640f140e1203510450741c555a054500c0c0d89458000e00500050841e510000c0700d081c84100081030002446130042e0310502559600032800b05d10303000c002825a01642101e8010301c104100b05030781304519241d200900d643c039041c203840350b5400e00c1c0b06908200c5680341741d4110301c03105030314642413511541c4070500c5031108460400041c2c4404038607440101d412611107405078020005540400c8500c0c000d158410040407668681c011f10182640544e0758581c0050225408488540115a04060320807000d1000c1181182004c51701c0c142d19a4490751342c8101c45252034200081800c0c008480e8910001d5600600710382d0365480d1700031451b6502d520486a07014820142500c5000d5a102d0784160701f000340d001410024940ca0b0001000002e504c00c02045600c030741d031190008006001485200302104140740170315162880e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 138910170 1250 138908920 138908933
    0x1201090b01030b0106050301061b05011d01200403020a1a090a0e0f1e010603110c0a03051306110c010e06090307080c10030e07061b1406180d0207030b09031b0604 71
    0x10317000001448000d00040c04003641c00481d42e04940f0341d040381034a1000c12402d000c2e004003201e034440100800c0205a1030f0320280d0540045140398500ca085808098039080720b03444074051400300a40c0300300041010450240c103041c00c25400c0d2240c0c401c2c9850421a40300095503000b07643d2045201c0085e01040081e04004d41c10b00c20390000d0207900075100381015011100d030309401401a00306040d600c1d151041210700c0c0c482640e134442d44100c115102d0180030705010b802a00300905085650071072080c041910f91007803c0c841d0f400107001d80181810b100000040d030b84081d20800c8503810000502c10321480b6601000560300521440029041c00400c04050107001072003110080b05150426000b003d058a0002d00101100e4451030310303c009031101040c03008440318060300503189040782d103e0141103140214000d4058a004032041340419684401d107502c074170505500601581107641c040005c52041e002d43d40d841010f01058030702d800c074410000048001000c04003950b0b540114108010041c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 138911420 1250 138910170 138910193
    0x30a0e01140319021605011503060615020a060209121f0b01090e0f150303071101080a05090607080402120a03020318030309090c0f1b0d1419030b1201090b0103 70
    0x207819155245181000941242c6818200054041540003950b00701030003041c4018810b490380a0b00070b001694928400c1c201466080c002960343c180b41c03030400075180e61a641085101d000380d4028040d11350030703503d51400035040089903070381084001d0031100e01880244002c0d0480c00d00100b0b46203020840c0b0020a04480405180354107105110303209220040d41416010b5000c034811f100342107950b51f10361035030f80c070324950401c6180c1603c800704500c400c102481245100f014020b030380d40b59840d1b0b60700c80440c0640d02d040c1e03449007032500007002040c44184555402940140003400100741d13041001c41240c5007010040c2d09500603080452104104c90881414190500c41100150b080c502c402c800650300c0ca00141200000d034000080e074900705001c5105603001c000140a100101d81e0450b2117054864040119070320018060760750003d0484060001d581030700020b4910107501c0d01c40c0c03100a41c020496001c0391503111600714028110403809015a0154a100b0040781010f54034501d0002180007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 138912670 1250 138911420 138911447
    0x2150a061206020f07170a08090a0809100903140f0c2e11010207060506040e01151202010309050708010c0908060601020c06030a1e1d0105010b030f18030a0e01 70
    0x2400c044042040007103032528200c20a40040005070707250400601c0d80d10380e00c11418001d000641602d00210340300400c82c003030421a200e503210800e0302d5a0341640241c0ba00c2a001004003150340074030403c00d4500f000700d41d180c1c0303400003400c1c100d0a00742c0300d41742c035400130203202c540d078403075a000d0001e5901d6498203118100c450201601c0d40300b108480100c140c000007080d1004100e60040881c0c4a40a02d44030f050000e05036000308000310b644006a003403042c080c05c41140c009000340d0a088a56100c101c05118211581c403560781e50b81c0ca000d04007017101c0c851146081080c0c1c1050344815041021940501058000f0314100c5e000003080203910201034402c2c2d40726404104035411030810840580d0700402c5104100c0000c862040d507036135405101100174915000c0282444420240a0040300250fa02c001d0038408000d400190303418002d41c0d40340c00e84409000c8c81e52841c00c14004501d031402014886600a05040c0c10800102460901c072407841c0c00101282c40086c42c4104401d0165030001320072100741 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 138913920 1250 138912670 138912691
    0x40b030a0c0b03061c150b091b091504090b030c031b0108041a04030e0f030111040504090501180b070306170607140c12120901092a03020901060215 65
    0x910340d86039801640340520540c1c0c041d920001c00a02d40b540c4802011204119000e13103114040784e0707810585600e401003940300710f2091401881e051146040c0220f2842000c05080b94504089840c040017000c2d000144100d4100c012607200d10000040340700074001070140b030b1000243d040350312402c151034640c0000a29001350411002042201007460301030a10001c282012141521380e481d0500b0581c40d06040030000740b60b804203003c101030740132080441184048410381a117612200805080b143c0c0c00c121480320075020170040149003015005071a4141c000c5000188032800114042c0105204580460b6001c0181c404c000c5515014070400c1d0103003000d140986072504e440c2c107900d80c1e251006031220090111100260320501c209800301c8007a140828140c507141711000311b80080c0d9802c04100d144060610500003504410144070310343d025904401040c1c540b0a403080c1d406070300d0103006400000103e508102001503203412958034020050307a40103100300f032a401310650601d0005040e1004d103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 138915170 1250 138913920 138913933
    0x24200c0a140303041e030c080318120a03031d011104060f02150c1e0d020409060b03270106150507020906010c0507090c1704060b0a1401080a0207060e06090c040b03 72
    0x1140c400100395401c0d50b080c0175540c0001078100c0f00c0c0d1407060134194001001c05e080000041480000807002c0c29103e0800c11740c560180c0d402004011a405411501d00c0c4107502100309080440e00c2134110614841403c00d5807a040d0b9040e45d2541d007074561702001310b880100006010071101d588007050316400042440600014288481110850500038210070341d02d01022400020524005c003c43c01078151440c14031f6581e034040e10045005e90081d22403440f01c54130b001c00c005085c1d64100b013200e1007032603e0448080000f525004031082001c110344540455961381e04041460600440f02d510303040000c5d154140c5030100e610400000c0f087c01800c65040207001d0000000144000402d0015904401c801180d660341d0f9040403100c1c1c0020010101880040e4800e0200380f01c001c0e4401c80302e00e1340941d08954095103401c4545030301059848402d0000b1030450008081001e82d5002d0000c00f84220310204503c1c0392002d0799403800c1c105690300602e940100101c8516843c1c03601c00c1940e13060054024059 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 138916420 1250 138915170 138915209
    0x1204030807080304022d120f101107050a0605010509090a020a0501050a02011401031b06140403021e040228020f03030f0601140a05030a140124200c0a 66
    0x186001d2210001c10702d10021001c50115910f00c098201c400b0422000500c0060070b580a1000c2d0312031541a075800384c030f08840121880d9002040226040c0c40c0c4100501c2e500884540040040c0112004440300400034050a00018401d01c00341f444180038210118095060104101400310081d108080a80c0405940b400503120f036030980040307407424208070b030b04c034540d130360302a40580310545488040203a01d40c00403040181200844041002000b0328000d401d1321040c0503102156220b02d42d000e421806d200800c0103180540a03810b4000c0144a1f0005411011000c00c00380e80003c031b50207182441075034200e004107403541106074407204540f00401d2040e03202007010340c8a2102030500801d21030b0240000e4030b96405030001c156544400c2e0601990384074005401029500140d4400400c103007000c0403401700c0550108454140c03141581c12120045180b540206145629240d02050203034201c2c20b1000007203ca0410b80b0094040c102511032401650100040b113500c1d500116440350100800c1d41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 138917670 1250 138916420 138916433
    0x3c030901030b0a0608040303050a0e1516020303091504060f05070c030f030c0c11040e030301031b060807170405011407050405090a09080304170f0a110c0d03020d0302160c0e0603120403 81
    0x46c1c02681506001401e45c0740c00341c82d10041d1040d2813001d0351034458602c6503d0f4081c2240c5030a07100341940c0c07000b00401000e041d1b04a899100554402c56140d205d00300e02e05190b07000500413500a807007030030f0004040031684001c800b80c035400c403034020200c1c200b01869414190402480b0044a02900d001c001c400700b1150f0241444000980282140d1007006c144c0c1100c1c2c45550145288c24128130482e9101d41c0e50345070044a40c0038116403409140740c00d200000362940901c0c04035001e040d8a40340c0141203007485469034030800c002481664103640f6601e510594100d1164214040c60203030796941d0f90342d07081105004403900003401a20565150190302001b25900c4401c1e690021b0780100e0b4030842081c0f448500e0001c0c010003d41d4100c103080041c40c045401c1c2c2121030448444810b0055840509001081080e03d00c901c12011380580c00102460028501c2a4000c08100d840510a45032414a6031150300c03190810350402c01c00da8500f0010701c0010301d0204003c440c514000c0c03a07030600c2c207401e540d14003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 138918920 1250 138917670 138917687
    0x15080901090b011a090604120212010b10080c090a06050306040e0718020705030c030d060504050109050601140a0c1703040b090a080414220c0f0309053c030901030b0a06 74
    0xd000078100070408004081e5030904441028000070801ca1f01c171511080781d0660f10411b420100d10400c004a2418460017040c00780302c140903002007441c0303918802030b4026103030000018501c20489104001d001410b0703855451503030240034280c0d1134585a01e014000d020840b00c07640314541c990b51050604018480703030f064403609410b402c0e0502503114001d40c82c0c000d10798041c06101c5225800086071140740300000350f206104403101100c1c00c0c03203180d9950394003c0841d03800f55a89800512042603000c0d0050b00301000b070080824900e4a12018000e0743c44850890769811502c511241d00001071000380903055403516040080c50020303040c0507856503a80702151090303200702003002816074440301c216682c0b101c0e00b208104541d900c1d01005511166000c0c01029280002e102083c100c0c034036140410b10074880c00030321960000003007020001080e21414460481111214550300c000d4002510a401c0000c42c48030100c03c01c000d41d04d41071b5842c005000d1300d8030303011380c1030080c1d03141e5404003c1d80707a100031003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 138920170 1250 138918920 138918929
    0x31e1b1a0906070b010603050a0b010504030506070809102a02120319060e01090c0906080606040b03092404060b0d0b0705030910060618090908030117100615080901090b01 75
    0x40c165600700072008600540500702e8080c0460760014000506580c044d04950b00c1494802c400b0804002c0c000e005442c14095408003800943c014400282068000c122094103c0e2104080781c2200803040050010381d444c4130550211020403285201070481b52900d00c82d6901c001c1c0c00607200780c200c0340300001054080105032100e070742c0100d0704410802510f544140c020b4404185030800325038591081002408891488074001101c216000605920070360202c1e00540c0d001b0000d9281500c0c0c0460701845410107003084000740038580c040c0e0b41e4049000381c021a00280c942c210b01d05440d05082420888000105060241000f5409400000c0e081d841403940180c0c40e060041c0c41e905c0300311500e0314007020480400b10140c070705400499010340000040042505601060300c03201e444604c0d81c030aaa508200060503500b00740018030141c0280140311210301c098104032071030114000490010307224140c0c0081c50f1858180e06680060354030121041d8810f09076002845000700a40c0c440c8a543e005106 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 138921420 1250 138920170 138920219
    0x3020603040f0c0801050c0910020c220e070906030b090d0c061802030d030e0706050414010c0201021015032001020c040b010215010f050f03070609050613031e1b 71
    0x10010092019420400b408003131000300b1141c508040800c50039440b0309a6103108070581007102c1200c5100040e424000040a403600c6090103080c0481401141c00e6100501150f0b111100c40d50103090401454009007052940031400c1d500d1410b0504c804200a04841d4031904403121600c902504840f02c03184607076000c00d00003880d0300301d00c51070070f003180c04120001d42c10700420729550b80542d1716800010300035600c85c0649466036502c0200750f64521482c0b260100780480900614642d40c0104810200700c0c1c0180199044c07140511040300c04c817022007a4800c0c007030542c018288180200c96980007417400e03504055190524000b0000b039620b00080c14554804c03602c4003201c40143e48284201a10403801c0c94001c1d4880d61100010080012903005a50007485e400b0b074010614940061148101c0f895511a8400349041030305200140c4c0c81171000e014850b180c040d000000a00c040580a90704551065480794503002d85003000b401510341c8501c007080082d1300700500900c4c1c100d00c1a41ca89400d42310 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 138922670 1250 138921420 138921443
    0x250804061b140a02030f011806090602090604120303060504020a050306090a060503150618070c080a0207050d080304170c0c0d021818070b0708040519050415061103040302060304 78
    0x101901d071006249000a000741019921820711800000784a109507108a05030b44440514003406401c13207058a05502d2080032441904001c144207030310003001da9000318009440c0140c0c071404500c041e40aa448180e5188186201c0c81c1803507817510030107001c0d04084505514107003c04100520b6804098011480b58035036202180d13142d070007580050000c05001c1c050741c0d9814400c6003803150241c801c0303c44502400ca413171501d03c07a505140406610030b5440c1c0c0c44503400103405407100c200c07a170000300400302944180f90340401d181d512041a44c00340c0744145e0b015642da2070180740c0764100f813b50104150300d0440c14000ca1600800102e0307004400d650580718001c2012460001078a000d10b0160ba121900d5010400e201c1801001d2103102c00702d003a21b00c00c4441140d55600d0352241da03c1800343c0a414604280001c0c00300d0f2600c5071150050180a5a6854003a0384a00c0003030111214a1035804510782c0815080080f1a0040c44400c10781688a01842c102851a0041400d0303101c01003001313100307c4080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 138923920 1250 138922670 138922697
    0xe061617010b0406030e010e10020403061b0804030c0c030516080d020c030712020411030c0403031407020901050f01120501061823090612070609050f0603040f030f0311030c25080406 80
    0x8d602802d2220044400c44500c030280350949002540719001c2910302a05010000360350014030640034803250107954030800207540f40e031804c5988500da49821680031048030400008038000700072030030748802d030842c6168910b464192400c2c83e0404100112082d07412103a41c0c2d40041d40c0c00b10f0003204a420b6030f1169803070f4851383c1c80040c0003000d42010403600d2400220a000780e21010384050b10070b5911986032207100b59200080e01c2e801d4003d0323041c025400801200140320b2410084241604d030311040c1000080c0780094950b00094074000d030071070030000b6204050142c600d0030025514000745801d8010355035050a5030998400141c1400c1428002c00c01003003c942070382c40702030794817501c01c0c180d1050300c41c1c0d55124040180000c29505c21a845005040c0c144400391405900b200e000d0b0f9400040d00d6024280c070358007078030720b0040000b1440c14199201e819802c92814100154890342001d2070b030340e51f22100c2c2c0f41d010f018803248001204501c0c030380c240c6010000e0328500440b0107079441800c0c00d0000b10b411 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 138925170 1250 138923920 138923923
    0x60909010b06030405150c1c18080a0c0512040503060a20040609050a06110a0213150608040203060a020309030a110c0d0303090605060603100501030b040e061617010b0406030e 77
    0x501e0049810403070001c100428010b012541c1100600c440c1124409034580200f0110140101008007a010075514a02c1c01c1c01c6c0d01342d600c0320801440d00c0f1240c1ca280c1143da141c3d6000c5820203a401400f00c1d01c1840b05c6410044144001d004050306000742608080c108008261340d41001002d5000302555401d290b0010a14030881c80005116901c030785a07142c3d190700c0c00408000451041501441c640704000c0b03011030268010140c40b80e484e80c010b0801c003034241c00308448d1401008000c02d07030b50390700c000714091400e89501c85c50140c0956122504d460601c5e1041c5407525100600340c0e0059131052003408031181000c0215140c04519290000e203010040c201541000310280105502050700007801c4100350b010307000451580d010303400c10401a56101c090020318841141c82124203800d40b201070211350700950290709409000307003000449041e8005407030310346101507400413020403113400440041d903480020413140f003107501417026140d41f41501010700d50160380a0181031640300e0079640e06001c030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 138926420 1250 138925170 138925181
    0x3010506092814010303050d0e010b0607030e01231c0b0108011203111b03010b0301091e030c0c030b090f0a0209070c08070c09020a09050a050904020409050724090801090b06090901 79
    0x2154103480c149940d41b40741c09071131640b103000200c800380e003000f100c084184018482d100001e940a0401840c181656408480d014540c0540c1810f00069a15a024240c1900d184400b20403030b2100c243d588921402586104206004a110a940c04c0c0a07032408070781d0b40a4402811190700905902c2c00c2e5816180c1980d030140c0006008503284500d004607009090211f61300141c000c070a030020010100000c00745800c0e9010300901400f506e0448a00c0d049842100d020000d132940645020250030000ba514a81444465070041e60722242280920001c5030091010499080003100249000c420b0b81c0c0c04504030f1100141540140000b0359184410701140b2001c6501050344038010841c1551100c0841d4029040a240320001031000880403909040c40b019800654000401880107550b9503030821001d480346010444003406903410016005005003825016081e80e5180c0c0e800000001000814110944d400507805138100000c1c075000c80c880f0b80c41180c2005081c3c95030444ea40d59500e045000d400b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 138927670 1250 138926420 138926441
    0x507170a21050c1b0a05310e030c01020d0506090405060103020603040305070f0b1504111602190801020301060e060a0e040506011e110610050a06050703021609020306030105060928 79
    0x101c41103e008850503c070711040104007281c45e0a1440e45031028031501ca859004803841040c0445080a0070b500c038009244003a1010385d1001c60b084c800108210b080d41c0000403142c216039004500c50030203039114080d169001f0300940b03d907900f61505448190340d80c9d0062002901401000001c1410f0520a10032600000d030045403914401c4028680b0b01d0008800b1078050806085040c078007901032400b4060140581d00c403201c0c0900f0860759010700c004000304544100e0f8080311411081008181d0152420001d02c6504001078503903150a1014010001d510380c49407107108200502441960440e507a0803007000207450005582d80d134600140da40c10144420481405200958045000c0d07204094146500c15002500e1480d12181c54041408900b4065545d00c0301c9602428019140704a001d081c4e4a400780c41100c2e8441d490346e240c00703c9008641c000e240b8071a000000c01000d03007001d0284540240c000d44480449141c40c01c2c48200400c180b6051000400000841c0d90752000c03660081c03100c42 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 138928920 1250 138927670 138927673
    0x303030c05091804030e03060c07020910080d050a1803080708222d0602151e070c1110051b010e1c1e0f0302030c1201030507170a21050c 60
    0x6080c0380203d540c404208403011400a4650112001a42400304601d4001e00e8245500c505004190707082182296000349004800401040d00103146c40040000c1c0fa9401101e45030103a075030f002a40c0040038070101034200800311012400802c0080c00203c1102c20749074001e441349444815130052841e01c0010501303030140d02c000d0b42501099011104032140c1498a4103074442c5c1041e180018174004c0b00c40b0074420703040582c02c84030043c0e60401c10202059800038000c81d51011803c1c0b00c868030045007905a417070000240f2542c03410802c1001201410000000440340d8a074102d0748180010000d20950302c4c05416034801c004c404442030382c2504011403070b084850540300388000c40f9208410b0742d007200150710002548402d900c0101c800c0c2d9a10308030400915522481e45004030300c020f1780a907001a1803101050020061428100c9890002902851190019051191070b05032003400022040c45154110b8110141e244000740c00100122070b82224196802800710310060190b6490050b20003d510310b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 138930170 1250 138928920 138928939
    0x206121512071503060b090f061303060b120a0507140f03060a090303050f0c090405060d0b040516060e06090d060b03030703090914040f02300304090c080c040303030c0509 75
    0x201d48000c1003034400d455200d8032070300a0180c00c0d00201c1c181c800c04c3c8200c01800c1c004105d0f07940c044c00d2406102c1b0181a020300030914005c04948a1506d980381c950040d164a541c0300300840c064540798000c4240508044010701001000783c45039512480315106004c6544c0c0c8179004c910aa40740d50040200e207503002401e072100d07442c0100401d00a0501520304030000b03880c10000407450f02903900e03410f00402d80030380058100859841444010070000c0c0815a00042d007103040c42c0051400d60342103101d98882c0e03001d0051110361705044c002e210a190048410b001001c0400714083d00c034141074808500741181c68180c8099241065001000c805407000e030580000100b0700e080c1900151140c044079002a0b0402c08000003804524154a05903130092403101921021005031520894890000c4400709030200246807800c81c60785604a4244124041c1d00040340c01c0001000c54414000707840c02d641404100340c605858008010320942c0401000d05944a200301a524855400c0d10881000a84409103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 138931420 1250 138930170 138930199
    0x30c041515030b0f12060103060b01170103080705060c041208160501060e0108070503070312030207150c0c0b060a0501020334031706041a0f030f0303040c0302100c02061215 76
    0x9841c4481c6043d020340100b000554581c00d04c0c5000100807000d17600500196400e5581d070601425200d038501d41003003450303c90410b0415182021030300840c4110b10003544c034681840c103182061001851080c0008080c04204481c0400c0c940003403165500080e580e55030a03014040303041c188511907001c1e24541c81d01001084181d44074003418140c5400782c0445c1c103155920f00170141d4445203400000c0400c0301006130001014000e402402c002807140355030003031007803c2403021000c40300d1031001e070000942040e240405000c0d030982820b410840584410700b120f4100740001c1d5580c4250242d010100701341c0c0c030b00c2041e1403944c1c0388480001030208000508600e000c1c2402806901c4045105241c500d02c01e000c16110f2400c0e104940d2624015000d070f8078107041a20070814102924003049405000d200d4120120080030700065200d5482265161069401e60040c058100349103910340050140c141417038005651003034241c0340502c56031841101e840d0386d201c9030b42040c0b070900246517400c0000000700c0c0c039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 138932670 1250 138931420 138931427
    0x902061216110703051c12052701020c060112150923010b15090a0302210f0706120207060b0607060608010e0d0c0f020a0f0e19020306030c041515 64
    0xc0041c69559a0503580d00b100301699501d5901c0c510004040e03a202d0005040c0100784001c01110011072800c0020040c1c5050700600309489044400303c449005441c2810300c00340e039000da001c0300c1c1700c210350086080c5200c038084950b503042c060054070610441540d0000401c142180c0c01d01c03ca001c200350038003c51146203040052551070b1150440030a802c003449050000d4144101c000d00c100007400d9812913012041c4118032075000c010541d402080d0140080050780f1000051059484851200340200103c810100d040c00e8080889070b48a0b00708050030030500398000301c2c180b01c4513812000140c1c0c8102c140390441c014103c0c10aa82d421040128240d03091040c141d0006044030a10002401030010502d062a00c0322681302c00c90021660020050006c9080e141400400300c1c4080c1020161944825001d4520190703035004880c840790540400042a40840d55002000c03e030300c00542c11401c0220010741c4620415041030b000b1599050f04003240718051041c0d2004268100403803200d6154072030b004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 138933920 1250 138932670 138932701
    0xb06130f0303122d020c0708060a0f020a05040e060a23010f090602030a0507060b0904050f0d030501030b04060507120507050702040605090105013606120c030e0c0409020612 76
    0x1034000c070f109071104643c086024001c58105510a0203800464071485a540004003941c07450341c1810b0794240410040306608014410240035000014640c61070180c1300c4074191400700304018003440c0144510085150030070140c8055031403a4034280c00c81d540d0800840e00c1c3c40241d40c402520840440003800640070701019812262600380ea4120f408071513400e01381c0d0301e079140c2d01c40e0b480141c0c0b04108a512082c415005801143d01c5103401260078085040040d607041c07000e4800350351540004a413a582010200041050320109040a008541c5191201601c1d031600802c00307003003291500001403040d8890f10740c07800000f00a0b007040002d400e2420000342240c0140204902071450f1042c00310356850040409412103005030750f1080f2500c1c120340090260104811005400f144181c400700301114a400b03103101420b640c3c0d075003455200c03081c03a08a0580e04440018410f00d440c01e150004480404074000002d0b1100396000b00701544540302190881c41412071064010f501401480254601c1e0001c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 138935170 1250 138933920 138933923
    0x1020d0504080301051f09090e01020408160e10060206040201140d0f05100906030206030a02070219080a03030f0203040c030212030d05010308030624041a0702060c0601090c05040609090b06130f03 86
    0x2184110815412450b031300351b901610440411070814081010f038406411844602c0c048100140c1443e80e242c13805407902807071120141140001f110309010340c91005c0c1d03c07a82c3c410034504070301c40ca651418801075100c10b406080a410004030908071640158110b0844143c2040ca03481045440300c151841c2000f00340a4500501201400030000380c024150b0013044243d1390014221880d54441d01400002540000000c0703030003040300005011074080a5240200034481c0740d0240c8004541803400504585800d0f446007130007071041c01400081040c0600c00c009807035042d2880300d900e00c07829851514600504480c0103a80d41040e00200c20000c244010714020101034480039801c118441410900b2800d210100c10590020300080100c45005181c403100c0c00304050056107050107580109240c0d9204100304036207075100c18010000c0305100d10446461200c2880c00c541800d052650050004500307114640781d5640340c50940e0b0003552170004441941540034400c101440e5101180310780d16900d40710 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 138936420 1250 138935170 138935179
    0x304030c0b0907081c0518030a0203060408070213050103053a02100c0302070f0b06040204091817030127060807030f03090e06100f0c08160b0a0e0c09070201020d050408030105 77
    0x5c0031040c0c10400551440c49440544030241006190071580c0205200d181da11030307061003001e10140141c2c80c1400424060713406521107542d1502240140202d69a860407400740c0700340303000010008240041001000310100c0085000c0c07444500b403a906180d40c4440b4014503d141c040e85240180350006031501341001f402e0006c1c42030301e21885040d002c07802190000b80185940c2900e69001402006295602c20002007006042a40302d0118404403182c0d90308000c0144044e01c0742d101802103100d0050428000c03041d00b50302e50343c180302c6040700d034080348c0382805403045640f20146801491600f01102814801e003c640b681584c2c1d05107465a400301d0b20302500422011800400c00310b40e40481c451080002401103000f081d8600070454420604100038000c120200080b40c0005d441403008055000001c049011b9960250416903544003018004240480c078260107829820804114105510700840c0e4040d40c5940e841700c00ea0180c841c801030420060b00d03003000c00040004200c05581681c1094a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 138937670 1250 138936420 138936433
    0x810030c0618080304050f010f03060807060e03060609011a070203010b03190c060338040f0f060e040f030c0f080304081309020c0a0b0c1c0e0f0d0807050304030c0b090708 75
    0x1090f0340d032603200e6401450b4010394801016009940162400c2d07100520380e180000325a5902d4200a060000c03a07081200003580c2141504064034017040016042041110400600c1d4500440076110020481c4c86a1030100003007070400c10340d68294020f005407138000d410390369401406801604541c1c01c0400c101c82c0c2d515020000303c0c44e58420b00c11183d0303810700d0450480c882c044402220b09811001003003c401c2c1702280581030700c1600c407030140c80e107854001307000469075031105000300095444e140c0140c089903601c8010000842e010f0000c402d09030350141006004032804c4d05040c1480404110013401900c000003d20040181d02002852a02904054050540e03114804c0205a210b41d0250030601d40c402400c10000c0384161a00c1608010410a01850010110b4150b2801010800d00f000c00396550744406e02048c805206c1206000540400303007850301c842107400b81c0002c0001d484d0030100900800040c0c10980580741440035030f90000c090424038500035020703580d5149a80900031a500400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 138938920 1250 138937670 138937679
    0xc0d020105070c050d03020304080c0d0c0c08240c040806130209011410120b100207091107080a080a0f090605090f030a0e06251505061509010810030c0618 68
    0x402061056984c848003400c1071941c0140214040e40000e00309645c66001000810900482048080c84030820380c0c50f02d030f100c1c250310f04244040c50358a600252494200c142d940380210200c1481501d002d918100c410283c1e02c0700191005180500d80040d5601d118881c2805481c0d1851001c0f40c212a20854444120382e8881002e0b2403001901c05c0720581106a010203802c42601492060032030f151040c0b00002c80307540d05000120002080c059030000743c0c01c103040038054000e02d0f000345108907041640305441c0442c165101c0d100c07482181c03e590100305240d404204001907540124080100681c0180035925950814200405054620104512801c1d0450111320408002d58492924549810002c00400c609010442d4407540070110310000e034506180c405240c0c5a00300c8035071341c0512003203802804445031000403910041c116611841102014061441c8240211402c08000703107410011600c4885801803440d5080c1c100a10303c00d8802d0020613001c0d44048034030319540010314034000380d81e0b03074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 138940170 1250 138938920 138938927
    0x18080d0609050c0310060f2015100305210a0f050706060e07031a060406030c0e06040e1b0c06070e040b090f090d11060106080c0712020c100302030f180c060c0d02010507 74
    0x40b0310360002329401c9a002c503900c000e01c12100c208906503000340c4c2d515500d40c0c8005111814211642c121015510600780b040c0a0104100760107210103a102e000752501c8040c2101040c016050324204100b9140000943c1034402c50680300901e601090a20407261101541000d03e1411603050340064a400c124400c1d00c050b1958010b441e4002914003450b060601d03000301e020b000080c203035005028140c0c50b95001501c030354000340700401c0411045495410640791010300d030b181c1ccc01c0450f0700011080c0601040c1c600c001c108260444546d061200e002810304001c14040d203501507071903510500d51001c203d01c80c1148a8102c0c4542d0420003a561044800c1c90300355500e0610124580300c950100005106441c020f0403043d4100021040c001e00f0b0062994810182000c0044d07100010382101031007070000d0402c412030885158260400b5401c501c0e003840e0741d400005c0e000300440e10905003113085402c121410b001a01140c0340241c015640c1c2e005440010f551600c5d040c0210740150b183c007001039000b510 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 138941420 1250 138940170 138940187
    0x106030312091721041101180b19030905010e07030318030507051005070203030408010e070b1219151409130302060403080402010e0901080604020a0918080d0609050c031006 76
    0x83c00080407a440012074a0102243c0080c00e201000c1000b034810343c483c226141c02c031a8851845207104010b40640c010004000e10510800d043c0d42e03c4250f2030500c0440b180d0390658425160003011070f40e86104580049002c3c1405003c058043e52130401000b90340840030602009480c06500c030950b800c503103044030b2400b402c450303c0064001c1c0c11203c000d004500e004e1020300710120043c64043d040c02c4068001a00350360007544017224036991105103100f000024000340000f01a10300001c0d0401c503450183c4200d90f00e000340091003214400074507070003408490303010900001c1d41c02c000309141c54441f042c040801040408140c4168680d2000604420056141c46d60250f810740c06040c2d2038403565000d80f041c04000e00100e0510580802909690301d80c5c00c149030003040030304c008061900381401442220f022541018081500705031800000101c01c000c2c2e4000d00d82d200302d0b00c0d541c0e45440b1004c00010049500700300d1225007170030140420700d100d00c0055406a4500e82c3c1c00071450b6a07808080d0b0780d0ba0b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 138942670 1250 138941420 138941423
    0xc0303060b0a020d030e030f12010315020a090306090311010606050409050108010c0e090c041229070e1210020409060302010207080d090b1c0915180b18100c02010603031209 76
    0xe10007130781c10021621940140b40c0300c8143c28102c130304003d503140010010340c109800400025800c00010000d1010a01030708040c0c0040440071072801103c1e0b00c000b03010000502000e07114540b41d00d01a82018402e0b06041c00d0801d8400c02042801d88a10000341198018400c80c164203080c40e0011504650601c100c011414403504c8060a0419810508c01d505031700602c0c540703881905000020b2220a80090710a2070782c4201d07020800d0107005420210a11000c3c961541c48440c040704012269400007000120302c4000c4070bc0840340c0c1c0200444510709100d40c1c1103100d03120f001040008200c06140c0040c001d69100b40c00b503440440d1104440e90b610068542c4800008860160070032200e20007000030851800f801e140c0e11104040d0710f000d002565604502190545010031416034107118a20840345042c0840300094910751032502d60f4002040013800c0b00d900341130494004a00003100b084401c0c96144008401c0c0b00c543c1c441540640200761a100c181c0100d2800f02c0b660b41500040c4c032a07494501d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 138943920 1250 138942670 138942673
    0x206010e010312090b0c1c0809101d0307050703110612190902030a1506050d030806060c0a05070807080d050301060516020105090301020f090301060918060b0d0c060c0303060b0a02 79
    0x682c610307100d5005500a0036504800d001d8551004510414080014400455803000905040d0182c5c00d4181d14609450110740811a2103c03d2056160010a1400d81d5009001d030224642040400100c1c042d46c041c1d01521240c0b10014442e42003010118044d401c80e405014451032030743e0050180007051040e1030080741c070210020001840e1050350081280703002c6240701c000880b029950701192410894a10990390420b00c600e01d40e200c901240910000340900b40d402202032a0b2540d030207040300c1c1d03016001620820001c1380081c410502001984800354001c0221a80b240e9070b108074680b5807445001e1100580a004034000e200ea0090040720f0490b20150380e10392608544003001100a031150100300d042003000c002c010102d0740d0074006000ca041c80c840c59141c1c1d80208100301800c46085501002c405814010021144642d003415040159048007020540d0503030f04000401c070256800005091102c90000401d96540c0310402c02201c910946080100325121202c8902600400450b075005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 138945170 1250 138943920 138943949
    0x7080103030309050313060509040e010608100906020909040308011a04030b060f01030908031501090905060603040807050c04020a1205060a03080301051201060b071b0609120210020c12010b030d020601 88
    0xb4400e0780294082c1d4000d00c10f4a08061310020703407440c2d410f0b055104a00082c004103100c056403426202d0305c0120384c02c4a000700840391428442d00e880e0790b5200c071140c400c0f42d0f0780d0040905110081d01101c02d0540c0090000099103810718020389040400e0180f51580c1c2801802241c407203803184106e8003680d1b0000d0303400d00c4940c0d5102c108a00d030380000101904040e1103110f174200041045000e1402180c104c89001d40d044001c0000401c0304030300c0d40c440b910b102c0c248410700041752200d108036600309400141c1607607901094280b84e8900001c0c440140c4d0000d100003450018954440252580a4603603078062086403125000c00c496030740f040c0000340c0700c25001c03c0100040d103401d4401027101a4070310000b1580ba0341d1181d480010743c05c102c2d015100e603040322204950b204460002d0902134020390602d0000e003820320104900c001c40707190f0000c0c000c0312403607101f030012802040000078131800209200f00d15404408050302900c00003040c1030003440f030082c10041e86800800c0c4181aa010690010320 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 138946420 1250 138945170 138945173
    0x6080c040e011502010b0d2102060c22080d090306050c0a140d0906090807030206011e12020a08190606061b12030902060a0302030405060a1e05090c060c0f060f07080103 74
    0x30440700f1002c904155944c035040d1540c241c03030300c40c201c1622074041c04007111104c8a00c54882043c83c1c5215580046400040c100802d500706181038038404408004a1030200302c1580800e0301007000f07500843c0603881090701c005100c0b80c0c404d12075006d0760b11900e030500090b03e42c0084128030f4002c0c5007008000c00c0701411a00301c1e0400140c083c0031700203801d010102c3e0400b0251074907011140c0c000d07002c3d140306e031000800c0028140c0400035540104065101c806601a0031031170080014810300038290415580144041959588050000603110300d10541d40e249200134220002101350380e404494280c140540080c01500402c1341d14604d00700c40224000501240d510740241070200740d0508181981d803030203100580c40e045c020307002401c1e140e200181e60341414244240741c860018006001c00d030a0100000714500c42103000449030300040000708940d1a5100510b051240c7c1c0509150003a00200382100d000c0f4000460f0b92000c4002001c0e90090f0300d6111030f11204020031200300c0042040d0500400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 138947670 1250 138946420 138946439
    0xb0703050315131107050c030303100b030a0f0c020d1e0509010c080f040b03040b01080109020609060c0c12030901030e0c2805090709031407030b01060f050d0f02030106080c040e01 79
    0x41c0b40c41c100070310a8800704201c0d14800304071440c00088040b0903101150740c80c2000700030003000942c00802c070021425440c1c02c0038806820101401b500c0604140030010540c11001600005010100503030284a20010300000a540d200280213080002c0c031041c2d00030810040b11120060925034a41c0c03503524201c030700e0005540e001c09800c000c44000300f04001d180c0841d110b0202410242031290076041d030701d092604040009000c10b8114894a9140401880c0142d50360812610700c0b8806450803070f2105180c0c04040d0510058215041d001a0100c0f2040701c04480400140780c0348209072002c0141d17a0f8100c4c0401c0e521500c02132100d800c0349401101d08480718910b4642840d801c22180304100740346d102c80c0455000d0a0513120786010500710281401000940e2401e009000714910080000600c1c40c0c4403084800c0e01845003400384007500b07400000040c0301d4002c407036401450440a0242c118031100c0000258000d11400c800203c211700410360050b00381d42113800312902c01080d000c1a07405d180812 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 138948920 1250 138947670 138947701
    0xa03151805190201110f03040509090a0501050705092407031103070c0e060a050301180305160b010e040b13030e0f040209041503150b180402010203041805010603060b07030503 77
    0x611094040011000081c03810001e003005030b14072a194241d946540d00c005061000c42020f01d50294006080c40e540c09800001507500b00d850460315146140c8508040a05050b000900038000b5424103082003800c5070090010302c0d0b2041c0070355106080c091111052403011100065038030005d60100030507004a031250545007804500c240a41f4601a0745680e1004070001541c401140600100c017000380305d14082c80c880000304403e1700240003003601201003154020300000d00900303100010504e80340c1c06181a4640b41169486000380440b540c41e1800e5503640c0e1070442e02150607152501c001096044a80d4012104560640319038a1801d6803a0800c079620960354031003a0056800e000407116642c1c0c031b00a41040c0120f181008890b28154240f40d010115060754243c10036041640d9081107031242da50004400c40e084a640009455070310040341140b145d5400801c06a12803104004031140691000e812610aa141000080e540741c00d11226030164100140100720b0030700010f1420310122815 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 138950170 1250 138948920 138948941
    0x110c03060402150c0319091205061305010b060409091101090b1b01150909020a06030b010c02061608030c0a020705010c150506040b0a09060602010b0d0c050d080d05010617060a0315 79
    0x103482c01c1c0303902c03890420f20395040f0042c28100300c1076100d01c1640c0071f0742240c1714102074910600c0c50803039401c9503161281e0780c2d81c0c0946442c0350380c40d0a2aa01041c0f06080d4080d071500c0340000d004640c0c959480100002400d102c140c2554205c2162800302e030150300074007205045450b14032106003841c28152401c860003001410641881d521200580341100113400c4042c00f41c401181c2c0010180c2c07460060060b41c1c161500404185840c05040c0c080300c1c2e0300718010514440e41210746903911010350003a40701240310318200801650003c420f000c0c03610710800107401220903542c212545c440d90b0304011030b81c0d0304240700040e290403c15066104100340c0c0da08120390101c4050004503810398a00e01069030101c07542d11102c81c2c0ca540302d07024881c0540c207029402000b2012281e0600c030304d900e910780d0108840389204283c821103500f0410010043e151085d20303071100908408209541c1c0d83d90016040c00c2108020005501482000407107a00c1c0451525081c2c07500041156070005480c0001c01c010181e42a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 138951420 1250 138950170 138950209
    0x905131505010e010e18160815010501050f1608040b0c060a02040b12041b060908011104050a060c0323030f060603040b040b10050402031f0f0803030403050904140702060106110c03060402 82
    0x100d1701b828007007002d0f00015032145517070081189048039844c281055000e0340800d2403030b07100041150707a03800303000d68034241c80c1030103211340c2c0e164458005481e2074001d08000700b54103004200081c10a0000f07002d00b070302015090030381e030444d13440c900d01004a124074082e000e800c0c03805104c4901c1100e10321002c01d5001c1d12640c0100c01c4840320241b80c000e07880f1540c0c0300d03200250040e101071002b03110178041c500c0ca1500c00315031203003068103042c002041c44103140545c504110001540d081410310620546105c20741400b184032408010360801245513004507140103001c0d045501060703283c00c100084900c242d4022480040d207403503683e2014070300c03800035210b4543c0c8502160b0200759603641c1c1c8003d5004505c40c0c60041801410a841c000343c402e800c1e4845004580085020802c4540200c110790303100d64075141080c2e56070080d5000400601d9402600ca400004c1401000703402500041c04a0588000d0b031030f003014030b4140c1e540ca5076558650b46581901600f00d80c0c0410014141161007500d100c20000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 138952670 1250 138951420 138951451
    0x60504080f1207021605060306040f022205011b031e0504080d020109060e0309030307062c0f100e0a15090b04031805010f0801050d0203070905131505010e010e 70
    0x8044868000790035440b14888a08140601e443e0100010701209010103030a15403a0711340800241c9a000003000280540d032205141801340410740d04640c403800d0360b99048910f15141103103e5034100325500551b4007140300b1300845480b0960f00e11501903da41d140c0e4440d05014140000c0844084038260020180314041c071001c42c00c9102400030790200700456000083ca2358050074103209842010310185010b030020815004951004011107401c15003000b03000c1351819030442c4154218078188075a0759080d541c4848404502000f0607046c485002d00740480c0c60246007117101d101226a88442c22400b54050080c240020344040c4c0c5100c003d114680001071140305a440f5924032400807102140000c450030070024010542d40d00d46030280c8000e1815115144070040040d00200042c0076840c03282c03034144443c41c00c65604002500c06400d52507401e004a040030500a603802c6003142045491110b00c03100c10070021118841ca604842c280e880d400007a91070240c422120190185c400111900c940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 138953920 1250 138952670 138952687
    0xa060e01110102030a2007030f0f0903150203160207050f040f0902120a150203130308090c0307060908010c020a0b010e071b030509090604020901020c120106170d140309060406050408 80
    0x80c030103103110340501307031006c500c07001c0f00100080c0c5117600c01a20341c4041003e0221001082e448140118108510300340b54042010f412002d82c0c02c062240d0004114038050f15543c03e9100b03854002d0340c021700c03490010321845202c400341680c480083c3d004658001210810105091078a0740241d142c210319104001a8000241c000c5806030003822208034156011410305020000300c010703880c00e03000b40000218154103102c20504001d121000c005020450100049142940140071760b1110910007001c0f2990955207184c040c01c180d03154031801c1050751800c1c10202c40b107400402d560a0700c552001c0c100324907a081c048003030314a500141c0800e041100080c903040400c8040c0e0b101c0000c0311701030313100c254032180c08074100150440001e141da805075005000001c802d90f00080d01c0e0108900c00c80b507a014240d822000b150041900340e00682e802d10760507000f00720030000819aa8070180f01540c0b010306101d01c903010064a844107540c0d000a40c0c0c440d0000401141055020640051060f003a07079181c150003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 138955170 1250 138953920 138953923
    0x902040311031c0c110103180606080105090309090412030603020d08090907030207050a11370518070f09050a06120f050c1602040b030f06010e0a0b0a060e0111 70
    0x180c008603034040207014015054502080204041666052005903032030300d9200c0109005441c440041c4182c10840c03203250316a019400404041d0040c00e04175442a080d400c001018083d244030b2414594078083c0032960401000c801c0b50591000900b881030251078598071201c250301c0003210b460816544e4280400182d46000d004e600c010f0203030000e50b03101e8000e1000c104c02d800b0003408031000d040c41040400005403010402c2c2c1d1003540c000c40f0340c000c1440810081090f400c4540715a014203510f44480019128054007215880c90343e040c0003415650300c1d0b5051120700040a11078564203d07a403400600d89a209141c1104e140c010352800820195503a0041000040e05400c0100400e84015140301c1c40031181c81149038584a006050025007002c01c0a0b080324400c09040070b18001e85c00c00588190f48858000002c8140c0207406c40e103a07400e99050390740c0c03912820702900394980702c0c502c00724074079101a0048040c013082c0148241040c1d442c159090700c40e07803009039001e410f10240404040300c2100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 138956420 1250 138955170 138955177
    0x90f031e0708012a1b080c070305010b04022d091e0306060d1106070807020a03060207050d0503010617041b0603020d0f0e030405010806121c08010909120f090902 71
    0x550001d01a05040240c140e003512580301001ca2501c001072401480e410b5540c8000c100c0150a003011100740c920801c0d40c3c002c1d80408034018000d40e03800980c0c4004404002520310807240140000c0142d40d42103420803060748116405105107103a0950040100d17914a070407051a907840c0e50905d440c103910340011401034007491460f14030507032105026500c281001e103c0f150f405081202c81c005d52141c0d50340c4558004044040c40d6004000105c1c001d4104204c000841c1d18040c1c00170000f0310709959030b1400102a52000b00100c9107030092102c4190418020026241664a41c0e154848105480c0140c5007a2800040054803018411150072504d8440c07c01c000004d4019658050303a40d200e20003400041e50346c09440000c1107403030b000301300c2245500442540d00f9500b003440c2c083e03495250040000d900309248190300d0720fa8020008101c2103288000c0c0494248001c031344071445c40343c1c1c0e6000b03000d08030b4103420b101508407100e001c0a4074030548a07426100010159080004d44d590b101d0341040220380 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 138957670 1250 138956420 138956473
    0x506090604020a0821090d0c08010207050c150403021507060c1d0d080d05070309150c0801090b06160c1d010807170a060c020309060f0318070605090f03 67
    0x30411014803055040021104014115541c02004901244030181e0190700c18142819064400441d1103c03590351600c3d0b07440702d60758001004400f9070b40c80d140858001d51001200310707003600c100e8510250f982000051500f140c04409840e50400f032858007805910a9000160352044608104280000e00248602011103da503501c0c04042001c40c440b440040f52880c0415224a0b44c2c00d5110b00003618140c00c560008010b01000b007400c0c0c070b400200350060912102d0040440210b203c2c6c00e030000303a080d1f01c044140c0d84641d64500b0746981c0ca21440c8121185c900c07400780c10041c20003203003800300a180321081c50b86120b078807107608803580c604540704400441c05030301050152920040000300340400158010b0103120030700400e40e0046140180da90014282d00420140d1580d6225442c1da0080c4203446600d04050207082d92424042065506503004441c442c80900380b810028800c80c07000215801030390700649885141151500030884020501e40c0300a50511030203503041c0c49503002104411815 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 138958920 1250 138957670 138957673
    0xd02040911180102061303031107060c0809060105061204030503070908030c0d120506030703030c0614010b03240112090c03061404050f0a0215030405010e0109150c1d0906010c050609 80
    0x180041504800402c05522142d07046600c6401800480c40c505c0181e0541241e040c280007640c640c0005820301d480c0580e00d00074040902d4903407105090b5400c024624030a1000000b66401c582e251410401903004000c10715454090050014001900440085820180074100740c5000c0baa10708403146564085c50105807540c02684403c455607401840404461000b01000e00c040e2602502180d56900144406400c22598060044c207208407540314056450340c0d00c481c041690b840b030071001c840d1740c800e81380760720002c812091207081052550041049860143e5500d40c805010440c0c200141c840d02500342c4100424810000010360b40b0303c034407203005400d40803105141c949800d0080c00c1480f81c1e80100203030740080300140010fa499690350043c100408000c5903c1c4e44480c100740e0700507c40c0c10803124039036103030003414820b11500c1c5030b2031491140320a40a1100b5040f0b0b4900311a0030940d9000101035605035000c0245030316103500300a501001c12300d424010710429442d61071502006441c0700509 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 138960170 1250 138958920 138958927
    0x9060609060f05010503040510110f041202150a08070f03140a060905010f1d0406060519050a09021804090f0209040606080c0109080a020405090715050d0e1207080d02040911 76
    0x2040d1414210401402e090178107500354a0a525001e0300e404004c16000241681c0342c2030301e024031084100b0795642c20f034040c81c10b9403659150700c000854418009416445131340740182c151071044251040700d0316140303156034000c22526034507010395804040144407420305850b443c0009040c4100010984a100143c502103803041c58051084115201078212541c0900f8440c800c0c00f003444d0623080c003044024898819480b542d510b003444c4000b0712868000c55403003050320000c40100010844800155603080700e82c9900c05079145800022441784540d8001c07002041c42850780300e0710f0a94800e0040c603000c0c0d401814503001c44d03400070791808822a01143c95542e100420302aa5a042115405444007800c068400c9420f281141e82e6070302e00d9143c001c2c4540d45a40024540c0a000d01992000f8400039900d05003090794004040d0807074104015a08006107411070f425000c0e40c0008a88800300342245545e4580a92034031001e0701c551010183d8480c41d80c081000003007501141c400c250008100d03001c01d946 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 138961420 1250 138960170 138960179
    0x40c08010f0803040305150c0909161215180207050303091b0102010b010e04050414030c0c0f150f030702030f0a0c03020c1012020705010612260723010906060906 71
    0x41d016225007080341907600a02c41800018400201d2032800b0203004a490550b5541074116102c5204806500d0340020200040c026415541d000600e070003015502c6009207d54070303c950104880c2001c2d100ca40e08015154100008440c50b1070340780c1eaa22110780058945036042d1205890356005856400b45035000c1000d075115500810008440c0d02c400348024002a4801400200152075001003984560358950120b02002206008014604d4019043d651244002c5405507140d0110580c802d000d090600b03040c2d461450096041a541d00c44011203508118076005a9401504000c10000640c48204030340c000210506000c0c018056a076520721204a0302441c009040070704000c804d0780158108844a181e00e80c200c0703508114441c2e080c0005848401034204540980040d4ac000c03408030442c4041e00302400700c8004032400002510036070181a00450001038194890380502a04c080d0b941503a1554001d40100a81da074001c5600c004521020283c445008540701c96100c44259580c4910410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 138962670 1250 138961420 138961439
    0xb0a060e10030207080f0c0a0605151e090103060b12010e0a060f14010b0a1403040c050a08030c030901050307030908030f0708010b07020321041805040c15120c0e040c0801 75
    0x103000c908610b41541000306581c0c608065008461404815610105407400401c600b00030400065800160511160a0080c01b0710003c42c145412a07004041401d071280e50490003041701610301c00045e00701c075216869034640300300030219008103e40c030000442c644422031500740604034030b0100d205c014000c07200561520301c04590b680c00d00c2c214028100030a5260704030581c41031504407100c0400d840d44d2843d03c050110390414455503070200d070703550100600c0203002079814084181c40083e20100052038641081540d6801030110807402a40100005003003548a0310145400c44441c2c140440d00481c65602c040450300100c0305d0346200c900034810803011079402440c1c0f0f80106003400b00b2600e0030f0721540100791607600300100f800c805500403160700c02000405088030010501003050500e01595108100044c0c0401d4809443c15880c1e24070100700151031040c2001060300070f44a1014054420050201900c1c540d08002e00703200c0381e03100d0401c0750307100d40c05007080d260429036410050b98102403e01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 138963920 1250 138962670 138962689
    0x5010806090403081b0409020a081e130f0501060905010602030306040b0901050f2103070f03020601050a0f03060902030f0d0f08180a0b1005030709020a0206060d020915040b0a060e 79
    0x40c40307080d140c400d01000c070b80c01c88100d41d0032400c101d102500d101c48121030b0300100d116551003d80300520005d07089120039480146a4000c1c0302d495181915080c2200c1e050881e820141c2e0b0307122001021440d1000012541000380300d440744a4800420215074034126001151400d80c012000350304000f0401040740b0340b6214244082400301d55280403941001d000c501d2461559078654092030321051180c2054000088240380755005904a0f41c2d54032051602c0700510f90342c41c0045015100b40c0340003041c14984861250181c901c00488005c800c1d07d035460303007000f6100000701640c050046040d00814280309021a41c092180c98691100c00c0c208514001c2003d240207000c1c000c01088070340343c090103d801099640e001d0703410000f0460303652502089880d182a09a01c02a414071903840b0001d08000c0c00d03009440d484d000c9400b61102c942d200030038000058110341009620200f4080041e40441d101100d1819054014100051101000b0007103240c3c500250003941c041014000115900e10f444601c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 138965170 1250 138963920 138963931
    0x6040f060e010c020d0c080c1603121704200d0c0f080106211712010e01060c050d030e031e030603010c1403060f010c2a09060f0e0a06120c050108 64
    0x8218114080d0002920b40c00d092085c80e04000c0412044428401031500756900f0340081c5080d03890307418902c4c544107021245480221860071a00700c0049202d8081c01e54200c08050041b00820310760b603581d42d12034940032480e504c040403040c0842c00d001c00b0745541d8280c505951143ca8201140c5003084507110034200d0a902100c05681000c9040c080d2202c00e1041d142c8800394500a400001c042d880e00140d0004803d8054040b82d1010503a0180b043d1031070311481c101d4200b5040700e82580d0b01e50750119882120407030090f00c0d41d80040c00c0080e405110f0380c0502240411841502d00b80107080754800140010000c0c12910003101001348000752a0130b109100c3c3c105201d0814004d81007a0481c2e0a509010040c019441101a0300300e000c0d041c1d0281110344940b0381d100c45408041945c505008a0340303012070841410071626800045039141507071081c801590b9004c607160030101c0c83d1035a42040c01d1401042d00c0c080b1a02c8040c00281c0da143d090001c20998442c03961117085908060004051a100a00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 138966420 1250 138965170 138965173
    0xf0c0e090105190b011407020402041502010506041a01050a20010608010b090112150c020102040306090602070611090312030603010b0301090b09150c161a07111606020c2106040f060e 80
    0x5413503503540c2e08094102c13160140c4100c450f0300c8651500000d0000d004991024203507501c0c5c00e030740c2e40005030706600c0188140c0d0704443c101304525041a0038000030816500f60783c04658208080d0b0709542c045c1080040c3e103459920880d0030b00070b520601500351034699020a026039101d102150143c030f4450000e5015241805100000b05061b0300c5203030150003001034104400d0b0340c54951045d280d00c03c0d0111000f55070004024021494280b500c0300003540182016240d251510000c0485a141e8108035051400e00500500c51440007000c50001c41d40003500d0184e1640d80c1e0360311400991428020480e1301c81c01010200003a1404221240c00c0800b40c007503001c03480300c0c48410449d07644600d0094540c50303a0101c01840400381186070000344075001c0c01c5001c008202c0501000b200d1035100100d018080002030542d01c601c0d8030715443c80c1481c15140242000b6030842817003590305044c152982100000e40d9090f820807d00075040d8641000d80540701030340c94030a00101501400001d00421018080080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 138967670 1250 138966420 138966431
    0x10b090105030115020a08070b0a0b031506100207030219080d0e0105070f150e060a14060306162d08061c1502070c0902031e01080a0f0c0e09010519 65
    0x100081140c401409130329120010301e080181e21364800c1111200381c0c0c2c0c3c01101e00e50380e450942440141755404561480810f41808800e0f809406c02007040c0d990f20541030844000c54482c1001c1150748500d41c03c4c03c0b4114440e0500010150b501d803445540309004041049042504101015040810300c0c00d00000744015000c0c0b01d407413642c0c01000c90f41002e4001c00040000400e900e0004d030003041c0741c4046418181031582c6200e00290214100340994010b1074100003000b501d141c40b450340d51007100c0441e85500032800088144200320605d00e101701a51500c420500c1c1155400c240e130840c0318040300d0030382130720340d039080c014035040000180c004104031038443d070504000f80701034160715210707230021301c0070340c414030b000d01c2000194059a40042d840044009400c2c1c0341e17460180250411603164515092201048410380d1501c0d400d0f41c141c0342c2c00c0010302149426500d50500f804c4000100315540d9009400000c0c0140b11440503600420908c40089031b03038200f200400c500c94443c00000e4034030a1904 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 138968920 1250 138967670 138967687
    0x602070b01050910260a0309050406050301061802031b030907081e1b0406050a080a0c0501051218030702060a0309110301050c0d110705010926070c09051008011107030206010b 77
    0x30011300007100e80480b8807801030039800c1c0350711648030014070701a0424850705410604160700091550240ca400350340c00c000e030039540c200b014242c507074510031001490800702c0001c0345500781c3d030015035000c000000c00014002c89514070b401e032680304550003121500216400d010320441489003e084814900400d640700c61842c43d1a525262500900d4054003201035900060780c4903608000700804009010800b1184e5a410319078980c01894002c03260300d280c2c1c00b001700d0198050010b03501c48000076910301e0707456910021035030300e906050000c2c410144814081c080c0182e44010082005000961300031849500031301c0d212800c0408018110300c243d060800300b2140c0481741d029a0b6024141c028041902c120f0b84078008003500c01d00a010300b0079420002c003078003408825903400c5030007944060b0044109080c0d808880b0301d40254503000304041801202040303d42c2d00ca4201542108003558146c4c1c01c00d40d0b61101a0031a810300e0401c90090780e010400c6000d140d0144400341c014600d51851a1030140003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 138970170 1250 138968920 138968941
    0xb1209120d0504140d09030303051b04180902090c18031f0b130e06100801060f060804061506020106080c040501050a1e0906060306051302070506070e0d0503070602070b010509 77
    0x3000081da500c1e030350380c0000909010319141404543c1c0303200d00960701d1003d40310500506000c4c45000031f8004c02d04140c0491080b141c04d02d8064005840c0440007820b00d82800d01b03100042c120040c0c5401202d45403495030015a031043c00843c001e03001480c0f070554802102010107000741511124a102e80c001c1c445010911030840d0112040c0f1178114030020300810b4920008281e048410090b4102038940104144c0e01782c00042e085004030f885003641c4001075a00c45c0d400d800d880e004e0085048080c50702c2c1c000c000c447e0203441200d03001440380d00042003003aa15400081c105490741c1c00701c4010b0f9101e01c1e0402c0005010301c42e00e0560b4600b0354050100790304240101e0305100c0706100e9482c0501c144c04207059014003032048200500001c03401403001b90b90b1504000c0142c0b4680c000c6034419540c1540350201503a0500c00c844006502c0406419144c1e202c61003911350f5022401c0380c2d50010602894840014000e20061203100c0c03003128010b0700c030b41480c2000c0c40e0240050b00207501500b0032005011a07050f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 138971420 1250 138970170 138970177
    0x1050f0117070314010f05061c030302090d050d020a03030b120601300b0106020706081909060204050406090204030b0108070503100203060303190c02090a1104120204150b120912 78
    0x701c00c51003020194801c0007203251046a900151401d5003100c4c0b44031516206402c04070b031341c06c0111400c2c4002d8498800300a03050345c50488a010300305180f120403001070300a801400485000400c0c211740c4030050303121a814010503150707001c0140c10089021f020582c141c172582d41c2c04507040e94460390007081e40e1006540e03010103000300180100c415990007442c0304a102c900500f0b100d030348081440030059150050448000380a030300003501a008001c00c407540f242d92103501c2020f0000d902d40d45d526200c2c2035a8010220140c06441c115020800491a41c640340680c01c024955500300503540ca1a50030040c070400c5041c2c00a070a1030b0003001041120b66000a03860380103800125006940e501d0307000c006851481210030010300d40e18078a80094a55820400e400c0d4064000c0c2d4560100e40d48030041070044840b803034042d0419202c01d001c10321002c002c00083c949420b20280000a48507010102002c041803d0751141c4400c0c41d000926010f4160022080c0350002800e00040103829181d07030f0107459901 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 138972670 1250 138971420 138971429
    0x90c0607030c0620030a050906040305090d020a090c09090b0406030c0e0a1506050c0606012d020a050f06010512010203010303120f0f0606050a020106051203040e100e0a090c060201050f01 82
    0x440e0b607101c0c001d00c4140d0380b0020f0015807401100c4581c00c02d01c8600e0180b03400032611600786515241c00240343d1980400c00703078412a85940d500d4504040d0f8000c105450900c1d00003642c101b26101001b041c0f604980c85401601c4000347ca54004140ca04800841602c1c00881c4260145081c20000c000060082e60880155521200e05580301d6030f420359a80000c1016514145205016640001c0d145130030000800d082621201a51007540d0390074015a20810622058901d0b00200400ac4d1280e0003c850b40004500c100d2042d2030219603580c440d1450948080c181500c5504080010046132a10a03400c0c003d040f1540c0c025030840d0300d0341e180034180403081c0c20b5400344c0c6515841100d290300300310b81c8544840c01c41d80c90704202194649074020140c1c0c000e0f10001015618107030001c07a80707203080c60400300d0701486000210300d403a0404545070070050b0040c203045150b290302d450114032031081d401d4042c456000510000f40e00ca4660030450032010345070744841c0070359140c01c05000140d90950141c0d810344 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 138973920 1250 138972670 138972677
    0x2060a060b0f07140f0102071101030c03020c06070e120106030b06011b0c0b090a15030c120605150d090f050d020d03050106080601030b030c06070c091b0c0f0f0803010b0c0105090c060703 82
    0x605044c1142001441c0c0000725165100180d0390040000e4008800b064500a0ba010030094106e00010303030803807280d0041d1590036400f00c4002481a07116040400d4613400283c031400319111001602801c0d01d0885d042140d013001c00e002000344030f5078000703100903d43c4001503051707500b1035568031450742c215018000c07030b802c0140006800c84a900c41e50784541c0244034680307040d00d03540443c0400600130245251130600181d02c4081c01d036403110741c6000e07030001d403100203106000e40032b10300c0e40070340b480d9102401c0b0010751504c4004150110b0342c0c900d0403000107030048003d0302c4500d91030b40000b4180001c1c007904000780340c41c120043c4645607004040e44c0d4420800c0c2400280709140e03030000391804400c030310215030005000405104000200404008890142c0e6003441806008110242e02c0700800c0d060340c00044148021402051601c001350808178020415014001003646410325294026081080001000244900030080074402e4541c000c0100c00640018000c2d1300018425100b07081c00507082 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 138975170 1250 138973920 138973943
    0x103050403050421080304050f0601052b020d060e1f020a0c030e01032904180302030a080c07081908090105010602030a1404050a140307060e13020d02071202060a060b0f07 75
    0x10349072048035141300b0780c1e001650152a441c0501d440ca564503824030302002c660146100001d05420661000960050b00030b201d10059108444050000b984000c000c0e41d020800000000100e18180b24079600d07440c88001501100303000c0034400d0244541c407510091045d1041003284400c0d40d00ca581e4005255041c41c0c070f00760000240d00128040c049144585050000248901d210807198403a01102d2000a45062041c0c0056010503046405800310103801b58004200d40e0b42054801c0b14229448001c5055050030300a2a031146221504040c04c05403440fa490307a00401c04941003404240c1c420360303400c02809150f0600c0e000a450b8018034059500344040720b08a04804150501918080c2002811489016668072490200b01c501420000d0003406110800700780c261103110705a040f4100078101209038544403465030002d5000c1e0100205003035003481130300c5c001109411a0440c001c4607600804241c1000403e80c0b0441d020f540c016086680104400f110b241011025200c1d1503420070152001e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 138976420 1250 138975170 138975209
    0x30f02010b040c080603120403110d021503010801050f0612070b0f04092a090b041211041d01061508190e0604080a0306090b0619031d150601030504030504 68
    0x1500aa1000661050401d00c0f000701e216400083d030b620440d81181102c12034441810904003512036804080d007600007915101015081c40f11241d1310a0b072020784001e0001d2810310b0344285542003031700144416510f030414070180d40040c4070f07210741041e411a40d04401c020740c001026a1040719104000603d000483e010401441d1002550000c002c108810f000002070b00c40085031400c0090304101112000710082039034940725050400c00e4810b04070310145001e0509203040300c49004100116088041004a03c0d01c64070b443c0110840c01c01c581143c0c60500c90141003040c2541c6094006402400d0902540711603103522240142e000506401500302d0000400c21140240140c0849400b540c0701d0003083c0300820408070300400400341e040d5070401206481d2820f1509480d104e10185902031000d004400700f00d92034048070805c007159409c000811109006200c21401034540b14080b4030340003856440c140d46081d0070100c0d03000d41c00f440d003007110303240c282c1e0b014001c1e01a6000c4d03403814071031402e07a01c0d8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 138977670 1250 138976420 138976423
    0x414010b0a061706121509151e0c07120807020705060c0c0105030603160305030c010c03060b03010501030e010b0909011409010903140d2304051501030b01060f091502033004030f02 79
    0x2240c00b0170040c26030ba400c690500038860040350907503003000c961181015030740d10f00d10301d1180d80f405405101440f10000d90b04900e05142c2c008083c000c3c0001c08002c00140c0300281440440c18041007103900d604101c3d07c0d010700081d060442aa00540c0181e40400050103010300210700c6041102090a28a072a900d850000ca407a25040e8959461b058031003500103c14448000041c05052003400d009201c2c10305600011001d40b503a611969010300303400c0c00140030640c004e4020b00205c4000c4d000006400d142c0400144ea0340400b601e420f441c903555240a050300012807900654041113020007801150074555009000007180103040b2144d0001040003040c41d026500502181c0c00d082d000c0c00a12030f614078405096640541c0c0888581c40b404c2400002c01118094042c100e07500003040c1280c0d6880c141003a02c04900e5038400e50104144600c1c0410240390f09420001f0944055009607191a10080c1581003052a00e60382a80e0150b2401551f90b10641d204c1c83c82d0b070145d49498800400301e4114402c0c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 138978920 1250 138977670 138977689
    0x513020d020c0303010e011d011206090f030f090b03060d0609080403050d030209090f09250506040306050906070c0c1802070602160308010b090d060c050f030414010b0a061706 77
    0x484024000928180801c1c40000514181ca001c06030401807643c0e101d644d000c11a25031032304400c03d500350030010800e074800d074000e07141a103000700c01c04603078100907a80d482c82c190b00300b031f1040300480d5981c005202003030740c48500381010703000c0980c0242c030318100040040d10f901540306005041607150f601034420040d151081e6002107130311104403090504074942c094003a41204602501900c545000540d030001d06518050080c45040007a00c20081408801602c003160626a14022685441d00244503250300307000b000110301841c00041c007070070030301101403c100340039000300208038039455203001041c04490a170045554184084644060840300c14000e07018035140540100c0c03021995000c80216107086c8200144280e8941d000c90b030322002c6150b010300410b95165007241c0c2c804111070001d2500d6000ca07040901506000c3c0c1002400210003080d5032080b507048032400c0c0c1d00714040011442c03d004680203c80101ca4070448541072402c0240140200703807004078680d9220010810302d4880c0c8000307 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 138980170 1250 138978920 138978937
    0xa0f08070c0b0a050309010b100507140c12060906100302011b06060506040909060510060903020f0f0303032d010513020d061a1201090605090402060c0f0102041d0709080304051302 79
    0x40d180c42c901c00000d81517420803134801c0003650905e10130303070010300e0400820350307410880703071a41401c103c500c1e1101108454940658541441601d00f200300740d82e942d481c0c0b003019240080080c00a0700d02008440d04056000d807500203005541541400141c1e0001c508462010380d4060400c46007001d4140100544099072105410420018010a102d0340c1500003861045c0280700074000b40e1034010103004071090606c1460005540070f00c0c28001858166001270903078000602e404c0c044000e620000c0d045500655241a0003030f551400400c02461410b05821103100e4005880c42c1ca6242401191410003000208040b030b40d4001a07d6914903526484000a882c1c01c0310048491001210502c2042d8081102400c10b540700c10000651040140191015a017001d407a15103152078039400d208a68000014100d486e0040c4008101d9154007403002d080180400d00040840688900c40e0440b00030000e80540200548103000340480b1138004119001c4440550b481c811016050072802e0084c05140c40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 138981420 1250 138980170 138980189
    0x30e190f060806011706031009080d020a0306030203120304020619110f100b09100302040c091206061a03090a0b06030309040213150207140f0103020d05070f020d020a0f08070c 77
    0x8540300c0c0d44002d80a100d90fa0a0700d45981d40d090000018490940498941381e165200040c01c402600d40754002074252072107548030324200580b81a254050fa082054045c1c0069614a403c1040d481c007040403e425501340c4c8442891818070f60045150307882900c002d001910303032581c001009903210b845040c0441d4005000c0d40c0389442c0008000d42c451000400c20315049062564040c9a0b1400c800da01c0e0141500c0c40c0380c021141e00c0c550a03c0003810400d01c0307070024001e901100140e407400584aa07500140315120019100c1d0418003030348081c2e00c8588080b48451000c0c000c0200e2a40b0000d01160410781055a080311903030340b034000034554815980240c0d0002d0000c146034582c404441c0d4500144e81003200c0d00c0408014820040365142c00505c03e518070001e0551940841c0d0030700c2d5500f40b403c920181340c05460301400e1700c00801514000d440c6200003a0002400802959041c4020b029850381407002d0310700c80740340791030301c0780d181c4031480018141c3c000019513002001071503090000100417100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 138982670 1250 138981420 138981449
    0x1180905040f2a03060e1c0201020a0210050103030507150e030d020d05010e0402030303070f140a0c02090c0c070918140a030801050102010903080a0e01090501050a09021804030e19 79
    0x2074401c007940b050900442c0c00d0500c03060240880541000f180520049040d01e0b03e050300c0c07841d1580d001905111007882d010f4003581c0d02602d1248550202c008004405070005070391030005100091411048002c0803075100e184c4401840000c1d401000c43d072000b500b0140240c0e0200341400c92800622070015401c2440c440001c0076480035900c1c0e009010308140c0d6941c01c00c05a0f995441c84e40d001c610407a4001c1d403503041040042d9003607004800a42c00b1540d0b61030002031059030281d10850381ea100e00300f1b180c0816060b1414604501d480c00496902101c400f02ca107003080602c0108035a901002d0050002c015280c414500a05c1c00e01d0403d64501c2d50003181914010014000681e241c0d03080e0103040e400207074000b001041a5005010b0080c0044d85955800080d540310b9861800403c2c0c00700e2070880c41d549079a2444082902405803a001d02c400000001d42c40d4500c0c410051800352501d107142402109204202c04a50002c1110880040690f110a0304103681414010307203040305c0c1c1007070746010f01c0903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 138983920 1250 138982670 138982673
    0x50d0e060114031c02030304080313120903050c010e060901050a0e041103010503150c091e2d010c110f0109030f050714010e220207080c0d020d09060c020118090504 72
    0x500c1160701080143c041e5200d802c141d0407409441403101c08144007503481000800e001030aa00d0007150f015001c21031a8a1540d00c0c1d544184982c6002c1a00c03000044c00754109005006d801d000c4d6041610090030700c0b008090f038840c040f44080c007480005505201c0c0110b0a640781902544c80c0c40d06080004108001d085005648a00560005e0140c540240305818122200c95190394111b80156040081c0b5410880c4030401c00504031081c0c00c0303545010f0322016003642d00783c44020418140f8a5000510107021421034000c00f200e012040d50181044090100301c000300e000512000c0768030009964265060320301000582d0351041942c001041c207030700f40702c403901440300204200040c4c5444000307188005141d100112214012200c3c150f51100301400ca051803062021001c241c1a62803110141c186400c41c0c41d00e0340f0907044502c1c0da0400b508121444a00f86606001d0b0007002c8450b410100c3c001810f11500505018140c88003e051100045944000d4501c0308501002800c04400900c02407505 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 138985170 1250 138983920 138983939
    0x9102c0406021b0601030309050d060b030615011e08010902030702011b02030a03230a050402041508010519110a0302030603150106020a0311010513020d021305040b0405070f050d0201050d0e0601 85
    0x207a10505442da01007802220f49400c082800ca04a0b07805540781081e1500b01420041f002855940803901030f0b030386810014080d1010700019100c1c0d500c007200b000104410b81c1c0058a25007074804080a0b280c42030240c10002504652181e05588800c1c5006031259150300c0705900414020000d0b0401442c81d45c00341c50000d40c00030042c00090203e6130b080c8120401c81242001001888181c418800c44020004071900340e41c1d404603a10900003017010444240c43c0580c1d4071007030060b8011040d60f0351200104142c00080c20041c481c9614240c1042100782500c540d100340c1070145090380d800b050b800101240d03040da020050945240c2c04800c110f005940d6550010790349119240b400c42c04070740d010000346100035041c814640702da00100780111540c0e10580c2040b012104000c0b04070780c0404501c14500149c40c0c144281d52060340b16a00308881c038142414240e1401445500500c0e051141c42404c1c0500d807a210300303800c0043c0c3e085c24216140c448400d401c4001d4800c07034144004034482c910000415519 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 138986420 1250 138985170 138985177
    0x30c08030a090503120d02071502040909020a050f030309010c080702090a0516020d080109090807050a0501020901020f070302030706050f07150f0606090f0e04050307290609102c040602 81
    0x10a031244981150f4034401d05484040c000f043c5201c00100344140281c0d5003d6070001d1818501c5202d10154400c440d407031a10403a005508a261a1a42d0b62a82011414404120005414200d60103040c0a01d00000030765a03104400e2018100240c112403c003c00001e0801c1e203400d141e00078004582e506e800c0d0464001002e044036401c0c40b005131070b10101400703030010030200d0840c1c4507551500074076802c014401000d8820408221008c007410001840400c006001708140f4501c21030000da504d00480b00020f182138041080390229401104080006070380001d5103404440050800c00d0b1681175060400d4064029150003400440d00c0340f10307083e00c0b004030f540f0020b070304007020004101d202c0e03c0f81012112034900d0701031944180c1042605008002c0d511860b50b61040c401c50849103480110342d1039142000343e101c1031412100e04400051100364403005c0c90b540c49041a01c20780780910b80121520b8094403541b01d420003007075a40c082081601341d120300b540705182d010380d1480214101883c060000390b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 138987670 1250 138986420 138986437
    0x10512180a0b0a021201151d01020a0501060902180a1202091801051e0a0212010b03040807050a030833090402011e02060615030601021b010903120e030f030c030f03040507030c0803 79
    0x746490011444800701340c212200c0350b440340c1d50341c104214201041c00301c408c1c203841e034107041d4490003c4500020303200340600005000340200161300e0b56180b03007080120000403101203201e4000c0700d005001c0144002440072260ba01240c8240d42074480c2a9403540c02c8880c00050306195003808100030000e02c004100e09150200c903003407146e02c0e03603940c5c0c182e078200d00030640d0000000c2d2803a801007040c0008000507640040c02030581c00e2600d4003641e43c1c0c0746055030310271081700828140c004000d007071120707132249418405074100440440001e4042074000b01611151161040c1d150102140543e403041d00c49241d041d0071028045620f094818019607160300c01c40e40f00c0e110740050174040380000c00c4001680c0c0100d0b410303002410030111502100d03848105030f9120342c0c1000b200550010200c0c051141207400350489840b041260745041d8280b50400103040780d9150142d000f000990201c00000007160680b80380c802c4070a031641c0760351500b1404d048007a030002c0c00310450f41c040131038189401b100900601 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 138988920 1250 138987670 138987697
    0x1303110109060806010203040509092d010501140a03020108150a3203060f1b0d0221040c050d0501020d02040801050906070206070e041d060123010512180a0b0a02 71
    0x356a030b48021910b40303000310f40290040e04144001c2005044c6992030039004030450b403c0c2c0300c082001d061400d100d5900034101c070740d60312000c2120102c44c44080c42118050b010450160b0325140d2a070000c51038803860762000a0401400c00c0003c0d00c2c4404240200518000092100d0f0207a0380c1c80354180c4010420003020000e1049221224028413149940d003451800060041c2019665002c0807005414004080c0c840010420600e0000300302c20708000c2483c000660b40041e1200340000c44445075002c0c100003004070b41c82d14005e01020450041040b401c039201100c8007025080207190207400380c0196501c40040c54004200410300c0d07007040d000700388280b42c000d00301c905940e41d80705c1c220b030340b11400d9a0740404501e907081c14206d81e040179004660340d0603001d00500d80340c20a03451010725054090307100540403104615502ea42c0d14030030074960380c44002441c050341090220041a81c1c207880280044200407140700110783e41040500c0b21001c09604020b503009140781185105001c0d61001000ca00e14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 138990170 1250 138988920 138988937
    0x81c110d0f14010504050c0c032116021b03070306060f03030e0316060f0c02120607021b130b0102010605091f0501051218070f0b1308030418090813031101 68
    0x901c0724074401c000103450703075005110290346070505000082c5406400c048160300d0801c103584040ca010001000759209458104468402c20410004d4514002e04425008100d48108c0304603540c1c00103090302440c2c05001c0941800c030361400000d00c0c0030546d80c0b000381402e06103030000410403803417408441140e0090f00e8100c3e19000380e07030400d5110004400341c500b00f0040310382c09100161041e0b21604070021507041075010f5900d980c00040c90100403c1c084034856001600b000002641440f40d07240c40d5880702c0c0310307880544028002810b0800704040c09201140e80b10300c854598ee100350803e80082102030074075900d900301405014a440003d40c41c161050004600008040d44581c040340d0500442c16400780403611400c0108200c00d007604501903007441815000b0840b107103101543c03002414100d42c2942e4500c02a007800c001c42d0055070141d00245c1050004102071031164851401c48858920006402c0f902c80c0b8140d00d05009407014100084403901c07002c42004050344000300041000d807582c081 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 138991420 1250 138990170 138990191
    0x203190b090c090a03060513020118122603070203070c08060417070203070b0d0b041a010c0f140102030103110909060402061b100c030903140a02030304081c110d 71
    0x140d840000415820100c80e00004503250035140140040400052035501c01c15a6500d540040d110242e8600b410800740c0050b0004641c0c0109505005014400746804d03080d140044080c0d9258200c60003601c1c1c40182c20703c007005650013178041707104092094010380d04c0381480c05000b581d0b0780000f078003142c1c13032500188046001a0002045031080d07510020320070b00d00f061030b4120489a00700c5203003240c0511540d4030200711901c118015121408960100040b0b4210380710802054600b0598bc0c0e6004d00c0c07810721809000d0341e0011584010940085440481c0d03002443c110f1164800e50744500f4441d44048000700412001da00580d89900088444d40090b446002c107990300c4400544000394408010001e403442c20840c2c2031005003c000d114181e40e8418809200041903c1c1c1c0c81c0284000255118504000c16800c080d40c580d41000f0360150f20b080405814010390359200140010340a00404200103880082d00c0c00070b0f0070008200076050049000c44840b5010303c2c0c110301c03d140210b9040c01c00e240d5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 138992670 1250 138991420 138991471
    0x4052a09040f020a1a1606090b09010b1309050d03020715090b040b2415040e15030706020a111e030a03170a02280e19030c0510021c02030c0f010203 65
    0x102820a05080745d842d01c0c2069a55020400b140c5000311020350f1920400030200314642156072040d0061030010404803030305030070050b4007546110b24017011f40c1707400801c5010a0000580201b060301c42c1c02c0050707590196003130804c2c40980c0001180400d03800c1c035402100f040140000c2c3c1303000e80c0c4586a40c0549407540180302e52940c2240344220559134a14000304414a0304905641810041200d500d15103602c850305105084000c44a49030703545521681035049050070404c0000820041c40909030f01c079543c0c2d9444c1004990429568480c5e0002e1401f4124001100c80d002c01c201d000034101c52000c1c1d01850040c204906c00000d002c0b050700c1d003100049410025000700c0d100f00b4802d0420f0380e41034010f003425060000c6c0c2c4907840c200304044481800016150300e400700da0b01c00c901480071403030309285142ca180c200505420a600034210350120a0050341c000502d080c0040701400384203240408400c3c04c914600444500b410640f049030603214411006600850141090080150f4020202c01c48203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 138993920 1250 138992670 138992699
    0x10b0717070b060f060f130302030d02120f030408041205160504051e0a0204050d0f140703020a031112030d0606030b030d02060115020c15030601030c030504052a09040f020a 76
    0x9012604203000140f11850001c0d41020a900b0007000981803d1482020321544e801441d10203032079412045050080d45020010242507090610041030b6100d0320250340483d070301506030907910700e4078044003007400c0059180594003c1e2482002c0421114181c1c10140c0e0750300c1d00c40c248609401c0c04201d02080300d04180c06800c0c422070031004010309244000c0203501400c0c2000300540b440603402d00020070325503602d2541500715805400c43c0030904115007008110307004503410540d402e82c0140001c100688400003184112070300002da80000826000c003041180340c043c00d00950034000020b00141500550340030100740ca149035400c101c1c20151000740760743c0700d50394480b01c00545e00c1035004000680580100c5900900c0b144107540658220701e01041b041c1c24031907098000410040300304419542c4c140b246101300d41180c9420f0007581020f4440b60344400c050030004a10078015110050b000f03a04200c0074140c00301c050000340c1140b400b800c3c1540c80201c508412031040c02d5491000030820041d800c7e4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 138995170 1250 138993920 138993923
    0x31505010608010b09010215250f080402040b22020309010b062701110d081905060a0b21010806060319050601120212010c0206010e13050718090803010b071707 70
    0x1484030b00d0b4208000600310350018590541188a03807c0d24524689a82d040140140d00c5442012a201615001c00f0400b51440b2095010000c64254041c4c100f076009180d182c000e034054400040442003440824030b5207015551a54042c1d00b90705c001f5010070420f0b4001c51046810310020071031401d00108201043c4105445144400c400524580185220070b04808044005051595907030036503030011407c00d81d03134035507684c0410307111810004108010700b20700c060208040e00c10041840c121000600039640c2e8060740040740004101858500492103555008108142400d01650707541c3e10416910441113410900900501d00c004e8580700b4252910b504450f4004064009a03003801c12101c0307410900305060b64000300386404400074903420700c6032a580d4461b1f580500070300c0d030501810110700c50700505001c0700e8050003120070010600c042860b0b000d507040a030201c1811002c0641c010054100c192016011341800000041d100c14644000c000c23140c807030700006c0140302c444800740019000b42c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 138996420 1250 138995170 138995177
    0x20c0f060306060906070213230f0708040c0f0f0305070603152102040f1d06060a0306020306030f030a0801030515010e04030509030f060106020706090504020f09130b060f03010315050106 82
    0x4504036283c6540900201003018008600784440ca800080c01040d000403c001955507482e14000703003581d080f680f0320309000c00c00150b0240e41042200e403c5410001400f000c2000100c0740401c04009001c807000d0018050710303898401040c0c42c0d856031110500b251100310b80511840100252913030103030080e40e42806004880b45d180e64544811003491510f0b000d05610030485140890b001a9198403490010035505100020ba8070058030315100c0035a403e420700b55142d8000001c01600e0f9990036200803c0d603074003c00140e1662140700c04640341907800388255045010129003107041c44c1c0c1c4008414101d81c080d500310364000c42181200328503171000b8007590013209070002c00200400e000350001c107440480a4202c506460709180001c0c10b1035001e030441001608070300b04c02c10041d170703004c98400d0203404111421498002400c03103000d80c61040348803c90140d880c1c1d00304000d03c0f2510341c0c0035800c403074070103841035650b0140c000d8400c43d01c0d03000340400c607030651180c0d50215a041c220320400b07040e250141c6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 138997670 1250 138996420 138996427
    0x809010605010e130905060f040204050708011a070c0302030f0307030f0905060a05030c070b010308040504200304020411070b0405030a030c11060a18050f010c20061302060c0607020d020c0f06 84
    0xb0038020001341c1140420034140d181d0410000140f0704015482c0300c0e035041c508070b5407241860701c100030036034030040c100ba000c000e0802c00500c040460003250445940c4000c41281d40d0700b078545481070707a5000d03940c0043c0d45406840c904035000c0300c000c402000c155220740e4031a030703401450110a60315404580581508444240b158001c03060203a001590008401c4407210b0402c0310591722070500c028242c0085a0b5410042010095418076000352000c0c41144800021940c24101d40b00c1060b000050020f48103a07141e03040700420500ba0701c01c568103250403501107000703460f05081855407a070200d1b00c10000070b0301e0700b102152200e02c605844c444d0042c0030300141c031544c1c41e00c02c280c40240028511100034020704902c00c00008800700801201e9002d41d0700041810002c00b08050581402185d819030800181c0001c18522540411740300e0740402030b01c1c84400c991409002003182170042603c00c4030103100300f80c1480303000c0341c00181c89094442c0c039500300c0c1c074001204403c0c800780c2407240030191380000d402e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 138998920 1250 138997670 138997697
    0x60402030a0605060a1707021b1e0d060509060705030606030a05090c040903090e150d03030e011104090902091803041208070f08030a2004060806131a01080901060501 73
    0x150015904007158510200321643c80300009902d56000349004404a5644007008a0860b001d81d1001e5004110f0b001904915100f6841c0e030220b480c0e5456598460b1045001490380640404000d00300301e000507112080b10f0040386882002480b090b1072003c40b40c810100040c400341d1150044074899200074080340e056840c0d0395100005404094502c00503405110140794450b242d91150300300b42c90203030781c403496681d180165098011170080e0a00c00d01c42e41030382c140071042d1180040390894a600d440c002441441c0c40e01103900414101201c00c8038504000340004105015400003a0418022581e84884d500e84695203c0c0d0f00c6800391304070204d034100f4007040105020303400480c081302d40203221482c0f50400341d03034943d07400e106003c404450030300010081c881020101e1254901856419421000103146041c900d81d050040e8440d5000300440180080c5031a150000e0110b08429403000501000d400c03003903c0e00354150502c03051800030b5422000100c20300814000d000880b20184c44002094115 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 139000170 1250 138998920 138998929
    0x4030807020909120c0114010e01030503070206160c0f0302090717180708070e090d020a030806040209060712080105010e06190f2c0a05010f080621120a02010e070e06 73
    0x40c0310f0b1a00b409880c0c1c8860402c041800140702d8100c113240002941c490301260740300d043c481078210614401c0660018000500d0000441d030119030100d40990300c880744903902c54019108032000a0000b4620721000907600340340ca00b144180c1b80300b228015256a41c400381290149298411408202c41d03950100b44912080c15207160348110841c1520159921512114070b040a10744c40101c80090400401030b00e440107220004caa035000344058515201562801800d15502800c0c1c0c80c490b80d800a4949120f9807804101c0f90165400030010f42c00c0240154050a111401d104442c0811141c0300b681a5600d081d500702c6140c003034469080d03090444044401c465141c00c4200c164280030b0b114201ea40942c1500100a44400040c03c0c0703c201da21818042c00f1207180c17150b000700e052182c3c4100d4216216000064540d024405130b80c0610034890800040b140b4240388196000b1500540500c40f0945502000622036034000313800038450f00c0305503480c45a50306518032600586040c100d01090b480c1c5030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 139001420 1250 139000170 139000189
    0x504050a060b0c07080f03040308070b1909050109050601121a07050912070501120204030503030609040602130308030604110403122f06060118050310180602040b0d110403080702 78
    0x48180c4006403081e1110807a0145900035071819495038052207040080c590208641c0d0300114024001d1400c20b80703181e60700c3d402c0d0f0141e01c2008020010040000d51040d21a4102c4003001081100a014500071418414001c00b1109001c3d501c40c09020004038031028442e01e0300c0c2400303138000516031040d40c030038035178a440c1c04010305036404120081014014176540c0300e094100e202d00c0c82c0d000e8040701d4034100026103000307541d0400340c40090061004102155004c03040e04d5000ca01510708220350740e500c0c505080244611b4400b8180905440004002c0c00022000b85108500a0301c0170010008024020143c030302a030320004080c00c92a4002e0180d50b84a542c070060b5801e44402c41d403581a005000c2800f43c017000c03004a98050340700000300030b0b030380d07034414000c0c4820250345400301c090703034103001c0480e031140d00440d070b1030b4001070300c501039140c0c030a48141ca03c0c21440d40041e030454445803100100049940b0000c0c181003854108500e0720f410304481c1c41110200da41c04a912450840c1c158240074001d075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 139002670 1250 139001420 139001431
    0x5010302070215030c0c060112120f02070b0c01450311070e04020f010824060409140912040f0e0a0207060911010f1d01110f10090204060b0a0801050405 67
    0xe115288061508401d44042d60068a10481046e118a4096009072800070142c0c00701001071520103030134010900c1c1c4031020b0300c180400c0c500340c0c1c1c99021600080c0e1505c00550310458180b0360008003000d0404042d0301c5030403109801300c1c0c011804490703000400440c03031107504640d903540709091094006427840e00c8240652480790410261812001e00c925040451640c840003880c8812002c00003146821400003000d09806d0030526503c0c05d1003958041d030b48141c07094400c08043e6440d010340c002d9844900751401017480a10a010940e402e20604604c1a0306444260b103900c5280d00b01603090708000140d07426556682e08624106182c106020361200c03000e00000b1601c1ea0030822640440ea00b0300425610764041c0741007191a046040004181500d0905010700f0000e03d4a01ea14940308540f06e22401c0103c01d01e0685070400513402041c2c108108600303500700c14840c9a44281100c3d80c1c5400c8500c486000312010044507036181e08500c0c1610986045000054411005014030307e06680110f4001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 139003920 1250 139002670 139002679
    0x23011101060e0103060522170c010509010c1106011d040201210b010e060a050706020d0b28060e0105030604110c071d0105030109030210050603010b18090f03040f050103020702 77
    0x1102021400c0c00c545aa810190111140c50300600c240070890140c1500003018a018003c481200d14460000101106c402004807007402c3c0c1c5001044c200105892443e030808008000b20309000d441c05000b06513a920100200d00c09003030302e0400040c04030b03a6034121820200491410342c48038010400c507010061040f4107025400d85680c50150700c1e0b00100d490072200c900c001822a003010005091202040704103407040d502041010740d66039106058420041c0d0088002d600c42c00c04101d000c028080d00c01c45103400018070600b2400350220501d030325910604140c101180c50391149800c840e585050403102e800b061042002c41c0050400e90312102c0c4145000d000c050802c0c5051074102c0c100341480e48100e00c68140503000e41140001e6241c4980100001c8008100011140d42c019480d4080e83c09a143c0c1c090765580010000c1c0c400390400303072030000002c00103803542d840c51040d0500c82c1c4080d40c0d54000751140c0444000007807400412941a11380300c01a10f0300c124a4030004401a620400c404c0340c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 139005170 1250 139003920 139003937
    0x30313020d08030903090307050f0609040515042c01051506160804061805030304080601050d1b09051f0b0f0a020309060304050c0102162403090203060a0203180303012301 75
    0x480c0550010f1030040b00070201850f9280807603020503103060200e8100500c28000141001803d9941d070301111049001900e01140d56075403010100d1a00c9541030089410a041994109080c900704000d507003c41001603100100c1c204981e54031307007224411285d203001c0c4070000c40031209038038242c000361031441041d00002144421030ba0341c01d03019411030750121740424034040380c01c000e05003211b003010003400041d0020341c01c0c1440d00c09e5241e80c807901807180c0f90296401d040c440080c0b101c240c91b00103010800d2010581d0441c2c1d00e049080040000b10f40580b9500481d4100f01100e0f580030200d90104c039021006c8a042c1180014125926070043c10344070700b03510040058401c2030b03e900380075511481c0150b000e44051000900064100a4070f0102140d80c3c85039101d00740900b98004840840400100c40e06201001c1c0b00075040c1d0040c0680000654984140b00c00c01070f004d8800c0c0c00031881080648072200345181b100078044e980e80400c2c001c00c40440d1f183d0b02501c042649100403490404814175205030b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 139006420 1250 139005170 139005173
    0x706020919090b0307051912051c260402090a05070c0c03150c05030112030c1e0c05040f0903270e01030501140105060405010c060b031014090618030313020d 69
    0x11000c8103070b40002c01164640100b80c001d49018090f07900200825101c40110241402c918458aa400d000d0749800b070241d01800f00610900704607402d001103405c81900c80d081001c1c60040c00140300d04030110040c0c88842001c1110451200c12680125805041c110580d190143c2e00d4010700b200070a01e000f04001082c600020641c80a98100154018404004034280f1114000141c420f004007810a010080004000c1241501e5444201d240c01d8034090b8032031500d0386025103548c10104880b102803032450094409001c1703103c4001003120030880313007040980c0340b001740c86003520060a00500031450031a20030903146400d40c6946408840d1400c0204e4864880006180d001c1d020781060310203a40d11089010140319070140700d0301604007150007500b07040c900301c0001c00107403200000520540e00d449600383e040c0c42c100000094400300010500484a600950407980c00046505c1c911910030400842d118802071136122050082d660055461540d95100e103102080703103d101203030090041c000220 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 139007670 1250 139006420 139006459
    0x305061b0c01020d0f05070801030209040314130b031008010507170a1d06040302060a0b0d031214070e030105010f0e01150504051e0102012d0c0309121806080c07060209 74
    0x403404441351000680c3c88810094402101ca00822200a0218000040c0007590b1508091030340154946020584071111800b80c3c94240111416504034950341d0b1000300d507021000000c0d5110700c5540c0c811002155031820303424240c84064550b400402c48034210045510380341080785601c010481d42c0801c20f0384090341d2140c5181145608800c0a4000d001480105581400b5083d0000ca031240c06001c3d80701c007540081c584e14241c50009040c42503442840e1003403100754005490040c21500140c545180403940039101c1da020140302840f0f5440d260001c030301c0380f148440020507070300c9158414003540e0910500301680510810b0000034040203000006a0346d50790a0381410f80b0b19402902c200312030424002a01b55111a6a0305480c01c1c0c0d0003078107a00c80100041284a41520050040341d54001c08206a00900e1801409401c1d0860303000c100645541103166442d19002032100c02c0c01180c1e59250441ea0035900340c404214024007080384802150f15600030b0502541c00400d00c0340752000205d0000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 139008920 1250 139007670 139007677
    0x30c170102120c0703120c050306040507170405070f06080c09040e0f0303010b19031b05030a091e03020d0f09050d020f04020c07140402070c0e100305060f010504050705040305061b0c0102 82
    0x8500b403031400a80138080642c0040c11411b105203040052291004096015243c0d0100404682c0a03540e6000000d5015110f4a2000300c40d00440007403808600b81424555110203407806102d035042c03e00b8100051030b521540389144540080080542001d902d5002c00c0040c04106110a40511074020010f19648081c0021802001c003086c18a540c0c20758000026411480f120380441898600911040084e000404407040c0d040d4618005a0701d40c0c9e280c641100030846004003800c0201483c2030400312340c420150314064107000707408a4080b80725084040354002c0c80781a0392400100009400c20807070401c101c54410051004000700000c0c484500460100c2e00881002c003e1750740015001c01c070129116405c00c0c60201d040c1c1d4198508503140d200e0300f04240e0f151240200a1483d42c0c001200d00840e110030401455001c001c0e129642070850f0241003100b000c0c000c59200d28038203004510928021011142140d0380300002d01100d075100481145586071348200c600800e10108100da601400a1004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 139010170 1250 139008920 139008931
    0x30f03090b03012408040201020a060b1909090c150c080a02100f150f0f120c09110307030b060412061e11040e06040b0303071e020915090907030c17010212 68
    0xa4510030702c884c4060b1101c80001840d0414400740409020140c0d9000c40d40c14445500100003040c2d403520040499034840e5842c01d0401c0301000000c010521900e0b0341c020a1905010b207122440d0340d0386514403202000d4084602d6004601c1c603811000c0080c2d10b40001e030070311010701e00590301020307912420001902d0350210048045c55031044410032194038030710807001620105221032451801d00b9060b41900000380210074414901180a204000b0310741e210f00d002c1c21074440b007846040181c0c18030004540086e500c000c042410151202c41e5030906105403421540184440201c200c03080e21104001c4c000b10200841103510400440202070250141c0050103408800381ca5a507850103040c1c540007140646542d201c1c46c14555072695581e000019102e0442e0040241c0b040000d5219030300d54480c00025000b50882c420b48100048000f481d8600282444c081d105882d6503910a400c0d10344800a5010040240d50803100901052003281c03c41340d40c51079180001031070050807050305003040c2c504542c2d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 139011420 1250 139010170 139010189
    0x509241504090c02010605030c01030f060b070f120804050619150e070f050702030312070c060e0d0f050304020d062003010b0a0201110c03070611040b07060506040b1009030f03090b0301 81
    0x1410089460944160351000d0303d84d200800a440c10840002d0321030001000980c101925048a40d0900b10564401c00040a01040707155544050349410b000008102006441b49598100c1c003007113085c000c0e4480ca11490780140905016510a204103840054031a80f0103032050359560101c074642c4c4810311600c050708004243e0082440d00700001006012150549001c01200703201c0040161000400c0c3c1d40e4a9002d206828441c0e65100801c580351401400c014001c642000c1c1c9140c00c21401150015070300609584040071020441004d27641480b05643c02500103e10001d01c0c1e0102d699580011190038481d809915001100201850181c2080c0c01c515020040068020f2955409200349100c00044e0002170b41001410343d41282c6038081e0039000b902154079081c0c90003404413850111800781590b03141040d119100c2e810b242000300303421500203001c0c51038102c0d07194840c60481d1010721080c909598030b4074454210359503603002c1d840f0501c04400f4811458000316502c068140514064044e11130b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 139012670 1250 139011420 139011427
    0xd060506190302030309060307052a070f1206090501020f0f0c0105071103030f0901020708040303020f0607030b031f0e06010e070813080d0b010c0c0906060905060405092415 76
    0x208104401c00400128001440c503298100300584000c002e85a88200c1216900e88035130361801c094420740301d5000894244408240009c1d21a800c142410710000d5144044070400d940320000304041e120b090013980c209007120118078001440c0d54101884240c030500026007404c425445480b40d85c3c0000d1a054164007000c21140e0001500340715041c0d0058061504121030880c1040340e0f031300c1e844058410305141c1045800660550400d404913006a5482080d07150350b80e90741d04000f52110060f02000020380110000f10300300500c680a003010f2110002e002c5d00080b0050861254200c0465486005031030b211000e000160100f8000d03640200040040c00c01d035441c00e040003e080300001002c0382c0c015403112a2030030101e41620184e400d0000c2409002444c00c01000042c0c59000222030010044100010003140d41c0500d80c00ca002241c1007a250440e030540c959007000840d000700e005540d007055142c00042d0007136802040c20003162403045091007072010b031400866808407280c2c1011904c00c0001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 139013920 1250 139012670 139012681
    0x19022a01030902100e09090303060609010c0611040e01030506090c03100902010e120d0809150403200a06020405150f03043309140129031f0603060b090c0a03020313020d0605 76
    0x406c40c1c0717a00058000c055841c0d45002c900244540c0200c165090410048118100400185034080014900350260554a903503650082d58201c1c0004d02048032a80140c10100e0a4080001500c0e141030030002c010b041c0002d00c10214600510040318164104080c01c04407003d141c49004c90b500d20840508050300b440440d0000140c080c07072000c2d0041d00b07507078411a031003005201d01c11501504039170716152040c0183c0c0079541c80c01e2800d11520f012a030030700a079552181001340c82d50040c0100d4409403070f43d080c0e410440400c10300350b01078080c01203209030b002c0002400041884c1010b000c500d8003100054400850018100c03031100c80c1c810028406a0380c1d070400c209021903d02d1204031446c80b50002d04c07140ca0b16580049048207640f40d854a66102d400a00f4050b6409204061840740d00101c1207510f140e80c40c40e810054039032840180c54913480d0014000d000d08140030518400c4d500c4e04040380c40c080101400300c000750f20003007404000f40718400c0300100590301d5402c9443d501e402030002040d1410503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 139015170 1250 139013920 139013929
    0x503090420040504050a091a0109060f060519140708030f0a0b1e03250e010608100e130f03050d0b0a18020c100e0319022a01030902100e 60
    0x300c2092a0030101da1040d00d6640c040365402c4400f07a0701c1c1558081410b8541403071440242c80c1003007004102101c103110300c2d03506d4403c2c031000c14100d8400083c10f00c00c05565690f07400c0e00c00c1a82c011040000d60402052047c04006011400842407070318140710b4104c2400380150a5401200088884440002c28001c48410303206e0f0080d00050035038410402505a00c00181d0003141c24108601141a0403070051816a01070065518001800b1150a0454501e00e0040b0307420200707008030304c0a50025000411b24134480c4081a20446445050721f0f1800d0602d244016032400050840e512644000315440010700c1d03001044503007034030985419441c0c592000d50300c003d543c510441140100181c0c5401c10900418a640300e084c0794444200507a940644001142014a80341103030a000781030807954405131800100409941100c0070b003840c4960744c010422078543c00032070303d030010603643c03039034004034621280801d100c0181c1c05040000c1c010640303602140d04a441c008480c1c001c51010010071125003070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 139016420 1250 139015170 139015181
    0xd140604050f0127060908040b040314030c060103032106140f0d1104020f070f030806031006140105090d050d03021b030f1b120309030315010807020715030b0d05030904 74
    0x1d40900a0128140348151010301c10850070000520728032085000041c8170081d0b202205032a04810506ea455850390340f00046a8400e03c0201c40e1181c4040001c907030160040140d60f031180700000640703280c0e440e64404070780b18224209280342c14000a00110540117082c070580d0b00500d20b0150687c200e9034081c1c200102e0b03564a196950080340206050400038074002c00d00003807040304550042e100c01c15050503075024040d80b4001024a80349042a909142e0003684075031203640100c080b10b400760700b00c0340300c0801d945042c03064051850041420720100e6008c7c01c003820140101600300c140c01007864440718038007918512201c0202c2d0340016494a0301d04075504005500c0100002186844417800b109000e43c400c00003418802c00e508a90309041c88403e00c048446410910003181e00c3e410102d12164484e80159400f8061550360f03031880f031141d400380c41d40500c195929000f81c52000d01d44015001e64030007000d802000c040d0b4500e1030121a41c0c41e00c0300c0440b92406940103644a03070411050108556 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 139017670 1250 139016420 139016443
    0x402070201111f0b031c081f03050c0405010518010b0702040e011d070605040602070e041407141f080f0402011b3909150b04060302070b0f0c070803060d14060405 71
    0x6c000c01102c0c808031001e02c0090b1141441031170080100c0d550088074114881c026600065075202c82000081802400580b41d501c00d0700c129010011640da400400c600e84203c400803460031208800104407550950028124850000d04049250040254980d00311000b00c3c00c0c040300316aa807046c0c404500b50800148018202c00d003002443d107810910040e41e01e900e070744116110b5410003400203041040744412440000102406c4429650300d0720328418014130704082050042068000303c41c5400e0500fa0402c00a00b22074540501a80f00c096103040301002c0180140d040c00701d510189841141180c4414032803c1c01461b114610b41c0c040759446002c52403006506d5999102c0c40c040e154070800b01d46c4200200d8889003800684000c001ca842c09191815511602c60100080340005101e40c050300142038852040c100070134150b0b90a00c07844038017501520f503c0341c040700a004441c001040d034002140c000c0d20040c503e561180c00c0d5610038034118100b030140c45403604201c3c01d0100b040801c000d1350003140c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 139018920 1250 139017670 139017673
    0x70314060a030b040c050607050d0e060a0e04050a110f040503010b0303191b080f04140a030c0b07060b0603090d020715020d030c1e02010213090504020d020402070201111f0b03 77
    0x2030400000141c085107207400003030a0300000a000c9010040704003a440d00402001d001d858440e1018107000703031202c0e909603074900411480c1c2d510384213624108085540820301034980b050024100401c2c0401040c00401501c031aa607104c41004040c40c084018050021007040c580d40d4441c1450306250035500c007401070b580241c0c0306103d014030408080d041d07048260140d182071007040703080030602c00c5c08648076980603015050000f4903100c820300b00e800620503642c5102403085400b646c0307024800601841d10014214401b9000305204074600380380240040c0e40110404200074210400040c01a841900c112119600080010322001d80621101d4020001c0c03508203000b502d10614080d449a00300c0606a081540c2c60500114090040103c051000490110047c0c10707058007001038001e5003c0b850005084041c0356002420090380d008035031145502510003030b0800035550a2102a40224904074140040e19014200c080e400700000303044d1414441050810031510344241040703030001c2130294041d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 139020170 1250 139018920 139018961
    0x2102070608090a0209271c02030a020d030b04090c0807090e0f030403151407080709081f090c0506030f1b120402010e150708030108060a0203060a0303080402010c06020c060703 77
    0x106280441d030f20b5542501558011507036501d40b44007082c009154a030788820480c00c401805083c9800040361240c6124140b4030980030407042206a03901d000d1440d0140050348221845140c40d8842d0700000c202280290000c12200c1d8980e46031b10300c080840d0403082260380944020004107001d8041c01070344000e2507003d03102406404880750303280c0c89140805460a118100d080c92105000e520149219001010b032502d141000800201100c1e4180c032034100140c00c800f408200c60101017810029584d07040c450500041a03144903801400c4008030a8803050300903c40001c1e030b5181c1100a40c81115250080c0259107449012081c640c410001d412800c0d0109220403864200040303103150300b064090034686102000d11000407100301c7c11201195480b200480c3c960104070192014505072031040041c1c0e03400d5603c54850384100e01084600583c4101080003c1001c2400b460406070400c0c010301d07040b01c40d4481503d440044e64041250301906901040801c4041c1c0da251142880028030610b690700e5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 139021420 1250 139020170 139020181
    0xb131a040c0c08040303050304030c02060403032303070f080907080601180f1b0c0204091e0c050405070507080d2d15030b010510030905010c0801030318030206030403030c05072102070608 82
    0x403d40150300000f4240000007010a05040c090903802c4c0c2e03100d0b03000386481c0c0c1d038a4803450000c0c4804520395a01702541c1c80703418056809076003602a40e100d228980e50b03248213054201800c0310102c5014000c90072502400e400810440c200b4012140a4140380d541d103c04003142075111070448200d40c0200e032600380303004154403813092040703003070700e134206581c03a091107644c1c102d00004000f04203108009040c80d00340e1413603540320300340440191802d5024401307101d1665520f1040c001903410071200c2c50000b910400401c8001140c2401138a40e04d5181000004c028a100c000c13010803c0b948800d401511040341005c1c2d00074559401481c41c0c882c900c480c3d10b841c09181d0390303074907540034010301a0034440c001800800c0c034142c0c0300341d10400d0300541050003400406034a80303015040f21000e01081d0000b89a401d28650107007802134400c001c8070740c0a454145959603d840c00c60040c8040404003041110400612000c5a001c18000c00c02d07015444a4114170b001c1014040d150460541c03181c01071001c1c8404101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 139022670 1250 139021420 139021433
    0x3060903030f0105092203350103121b050604230624060f030114030607080c090d08030405060106030501080106051507020114041d07110309040b131a040c0c 69
    0x3d04484069030340340140c0d02c07215100001030904903032000c0040710701451042403590003ca0384200b4805130b4801c5441400203045166240c10f044000e0002c102e14000400008402009203200e1143c94640718006400d940d8640d4034201c10400d040c2e805034054030501c001e03c08001ca03e41805800f1428030040049010151a00c1d0300c001007068041e01d1200700c16141c141e80c8008e050a031135000405031940c507051918035070001d8100f030054400012541da50110b1504000615038051500b544511b00d1641d41c0e82090b218035401207003042e8010071490b040c02d00045191000c2d5014910840142c030040d0f0500303a00404582050788010b40a80c189002002180c560400d00c0410740700d00d854071075603202d0341e00040e55090404021404a00400180082d00880d0f101c50001800c0f2080181da10b2600d406008480142c540000070410b50002c0005244507d403a504ca522001800303070102000c0b054022000c3c0850300c12103003000c0d5070041418415000d180030f1050034101501030070525190741c0c854a904 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 139023920 1250 139022670 139022701
    0x5121003031e1101020d05091002040e0f1509180d020d2c06070c060201060501031109220c09080601120c0e090319051914030a0c0c02030d0206060306090303 69
    0x21801030058602c1d9040c1e2034401d00d81d840340088204020356481c0482c0b01d517900202022114100140030b50fa100d00620089402114121011008020403035100c404400b140030074050a80400c030020001000b0700744d245c2e8060f981c840c010a000002d40049003080603420900449020300442d00305010300580c0e190054564440c1c5860030540094148002c1c80300840e410307200b091240e10400c081060000c1105020050050710030326070080c41500c1c1d43d14015010703036200340e0010303c0703841e41480034485034242146244030810b0031185800448040100c514219100424800006100c03000180b01f2060304010782030061050300000c03903a40c0d005407210445080079022b2622558024000700701da5003000c005540b10500c4041c03040340340c2d0401102c00340043d40000d0101081c10070f51156401098008c00f040c0b0380300210700340402e240d40d8901038802d004007000480c60060051420340c14016032010448400c20080c690024440c50401d070041503c2c0c41c00041032803c083d0f004000b0059000b0440082 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 139025170 1250 139023920 139023947
    0xb090105280605150901020d020c090a0902130c090923040323040f150c150c031e06030605090604420b01030501050d0c1202011701060512100303 64
    0x103241050201880c9403002c1d00b11a880140c0c03040000054030010100c1d0b400400e0138442c26000c403415209070100580c2c0300c6203074080a5610401c8500018888610b40d002140860301c001c0c00c45003004041001d40c41180c030b440d10388600150300c074801070121603c1403040c05c4400b030040e000b0043c05502d0708150603840f00014001420481d65040280103074001c3c07034855101c818560450798403561200c0b01c0c080308108034803c1240d500e42c1c1c140707100d61082c01001c103200201d42120070138907140701514141010f0560600107808250f942c031214a014111400c22812185c006c003008104a0b00d142001016250080c01040240c0c10a1b07050000142005e0b00b05e404001c2010103000c035812103160f005085210040400e010201000302003c4078000f5584031501e03141b0243c9042040385d894106200108102842c000d05030401c100e8244559401300c04005ca4091051603c0741d50030005e204240e501100aa12150106001003480c11201203107002040d8071071512852a140d041c40d5440041000703401e60340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 139026420 1250 139025170 139025221
    0x1213060c050f0d0e160810051305060414070b0f091003290109030204050403180b1c0e0a020a030804150c1e05010e06151206040c15020708060109090b090105 69
    0x1031340108040e0a004441400368858403142507540d580c000e40c0c0e220000c130107800300c1c19807a200002c0c5028a107800f5114480c2c2e00440109041d99880d950f04000c00c13140705904100d03100d00100020300c80d007482e008241145000d02202d4452003884e06006000fa10795036050305150610010311407000403c2c81003441064840070204100c40101e00607540c14980c1e03000650854204420007040c160170000d510908500450480903036580c0305503440301d80c00307910521104801c2c0c40392101e01c1e103200c81d001640c030070044009892141c5000c0d40021004840e540c0121034030100441e0802010221402d590640020341c180006001d038196240c810300e0100c11790000c0703100c01941c075070001c0c000254051007401c030710b403011180141400c8600e42003850000031450700c036035131a89a03000290320104a080c0144e40c80301040e980340e0b003072907181d0b440704100034049011482a1400043d42c50401c0080390f008180e5914000350544c500c1c142140344003401044c61989a041c0801c2c402c81032000b00d2030b540016005407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 139027670 1250 139026420 139026431
    0x100e01120b2202060f0d02040f230105030601050c011d01050115110a0308090a0f14010b0415060305040227010f0603020a120b12030d05011401020604030903080307051213060c050f0d 80
    0x4140d0390082c020303c82c820144500c0800e0101c1e00749e0b40d003c407040c03c0e83c242415024081c102062102c3c1b00322420085d15001400500102703006e94091009400c40c541e507040041b8a096081040b8a0460b100d4038400352240c0d1104010410071030150707040004e000d02071800c00038904003409010740d42d0650260080c208844030f00080c0d920181030149000c615480442544001e1003401c05c2c4003d01c0349110000740c00d5281850401c0f4503d0540700d40b44601001103a03080700e41e480c0050030340040000620036070b0000c403c0c540c00b049000982016600c03022954030514515410442a15074055840e048034040c5441041400b912580040040c00f00000201000c0f0b03000042c040803071816068401030010910000c10044860300d03058010f94141c070340c400407104600c0e40c4000120390340c1d241641d02a0201b81c06400500110350f080303004543c008030b141091460b1007050380c00700407000412204d05c8841580485501c082141501944a014106290142c10a40070100b4000c840c41811644d00300c903607958 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 139028776 1106 139027670 139027687
    0x613060f03060311040903020a02030607030903080105120a06110405060c010609051005060f03060303090d210809030f130906030c031a011a03100e01120b220206 71
    0x312040813601d02c501300340001800502010b500b140034042d00100962010070056011340080e541c0080e5089060038020b203080e0b0b041e00024842d010303180c1c0070403d280340094407071b01c190781040001404014810450295208a9010b40d03001a4041211440850103503c114101e0701c8540041c403195440041c00340814866010b110750200702442407244183c2628080c40e4448009002c80340f910180b2400200c00c20103d86048894441c1d00d205602c482c0049030a0301c0400800b4100300215040982e511038803401a00803031a07070340d02c2c0070036170030110744c000000a0014104001c0800081e80c403401c09401880740c1c4d0206070303020303445a810301e01904c5890440904840c0c02c51b01c807034108900616411019072010b00a442103600e1703c1170100300301d42804000d40c000c090924014031441380603c2c01036030301d0a00038641050420360405010150590840448000e9811500d465403504030 = true := by decide +kernel

theorem cover : BRFrame.Cov 138848920 139028776 := by
  have h0 := BRFrame.cov_init 138848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 138848920 ≤ n) (h2 : n < 139028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
