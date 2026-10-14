-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0316
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:10:37.625411+00:00
-- url     : https://prove2.me/submissions/d61beba9-6b58-4345-af6c-55e3ad218c85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 56654679 ≤ n < 56834535 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 56655929 1250 56654679 56654687
    0x3041b0303170a111c0204030606060215100b07030507051518100203070806150f0d05041b05030c0d03030b0a03030503040b13120e131e06060201090807170403080406 73
    0x4916a07030007103800c2c6400192040b20394000c000307040320603403400d92400b0b100d6451408056060742107028100d40800c8004000b4049200700c0c2d004141a034003614040c3c0d0b4030220110f50300030103003194101c498011400d122440c42141260100c40c3c3c5810716030f944200510744603081c040381c80c001201150312841007060001410000f02454100f40e41510844111280004200e010541d20800050b092100142603820300c0701782820341c0684446081d0921b0b614050084840e80040d0000851680340d04c2400200550204012030030001d071550360a480341050701182c0d68040c084580c03071045460f20000c00c141800b80d4400511004080c181d0300c102920b9040190881c0e000b0348081360701c4443c0311300281101d07561496145010b5400321b00000c8041d01c6c80300407141442c04160656204441d82034000320558188245411423810100065182d680ea0309190100c5100764032600669042461420000304000f040710b140c268001202d0003400d103005a028602c0c015604010616800000c001c22000e0708 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 56657179 1250 56655929 56655947
    0xb03100506010e09100e060d050607050717091005090d02040f05090c0a120f03050c0607230f03010308031005060c03040f06050c0d0f030e03070b0405160b0a030203041b0303 76
    0x70a0700c035440252110014407444080440b030340016219886801c0c0070721456030510640142d0000c0920800c0d44c59510f61074104207041e620600455030000e89607041165200441c05c03040d06c40d182550804200102160f55980b80c001c0540810000003003020f80c540d100f03081070061580241003046071000b5440507400600080e01e0032107040c4600d80a030145468032101d40c00c241c0b604d580c2402d000d2161907483c8124036110110032414003609002142c0898020403000f40f141200e60f4030307889000886030681180c075440f0b0341e215214490821039410030b004100c04a9044030f9002c40b48503640d070b4602c28185100040d50300000c6d808103001900942401c40000544150f0b41c10b1502c980800d5030b80c00d0309860754030880300d5070549a0070160400552500865034182e03061205c0c10045169000025901e045a00902c001c542141c03441c0c05200074480c0030850701045800702402c110f9800e0811a0750802801010b040c40c082640000020b810420000108904c91117600850300255442c0d28002d820115 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 56658429 1250 56657179 56657191
    0x40e010f050402190302130e090a03030c02010501060e0f0609090c041a0301150507020109180c02150907031202010908070c1508070503070e0303040806040803090f01060b120a0b031005 81
    0xe25800c0209092038144216450040300400c0300ca42050031071415401781d00800d43e881d40b69500d50800141c00015600c41c07a00c0fa000a102030046010140380c040c04035540907815400310780c54000140401a0482244061001d0482c0c6490350443e11500080d8203118202e8016000888171090102c102c0e0240040c0050700c9282d000d4078206540e04103e8103a0740024464002075107808159885014040d100500d007040c010700d050b10640e529a045610402101540500150b5856014000c0d441d418001103001c01c52108031824141800b0b064281d64140780e0202424004500003402e00c02d9000b54803c583c003e9000d52560349031625030418113100011442441005100c0402104050784940c41341031068290741c55150441d141c081d000c4509100050445405100030000401d0003001003040d1803190b84290065652460242d080509000c2004e50700441c0380c1c10040700307103d9010905c040c0c400c14544001c0351646650303503214035800f07462880c0030b503034041c007414150008a4242e608460f1182c9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 56659679 1250 56658429 56658449
    0xd020d020903070e0c09041802090403020c03010b040504120818010e1f0b0d12090503120c0c03030309070b090a090e010603030207060914060f0f040e040c050a060203030609090111040e01 82
    0x503541c0e42c8415604c8000321581d04002c40204000c4031145460f5106a41e410429452403040c501140d011aa139214280c41c20741c056070001c01a50003602e024050380002113800e540a20503401c2c50f90781c0d10400311607d404201800b04460029a4452100c0d110104020320040217100701458a16016110b003d15100d96040c50301611200391303d11220f006840c040345000d014001e681c0c16036222080c030440d8407003501042108040f0001142d0741d08020070050310786080103660343c403007526500910300640034441c0c0340260414400c0004240d00800d183e8100e840540d1069074603990f0b10000303a100c0c061500100d807807a103005401800301405610060580f8480e4089408183e04d50000741c0c1d1810b1980308a1212030058102c501c100d08010300681881000194540d08242e04104c21030210b4010350000d00e400900380303080005000301200f00c44010034003034490009290500c00e00a460b0701c13004081900400f901004500400000d42c0070310701c503c040c4a2013a844980701d030041820390b4000e200714042d807 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 56660929 1250 56659679 56659693
    0xc030604080901020601061b060e0718020408010b100818010b0907032003060d0215070204020712030606030908070b10081002120903130e040c0306060303110609150118020d020d020903 81
    0x87c42c01001c1d08101d01c184c3c4409038510b04481d13a1410003403c0d847c80701843c2c0d40a40c2e40c00091100c00601030303000751400500090303115130038200c0c040d003100c5d0010941403003928010000e500040e000146590481c40c8080a1140100441d14540c003401c46640019045032402c400c020441d985503001604541c2c401403403030021500541d000000b40810303101c050703004840c40651001458104d00e0290400358a281550512480e600014100e820114007919a00500029513070b4896040c0b1a001c0a000c1500b03042040d080300b520f52281c4c2c2d000301e45009000c480c60b0004a0610580c8051500c000c4c220b42d011641c00e4060160f410001e9000500850010100b00b0080380b43c09102205446502c0000d42e80001240d11784110180d10100207801990b45200d0b01c80040049051405010050f41c060b48640d1801603c402c0220b1034a0002840803003590414210340e849081111101d034116101d44649001c100050144a0004d01c1001c00d10283c040c8005484010448150090607001c0c000724291010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 56662179 1250 56660929 56660939
    0x905130902032d010e030a0c14010e0109140a080910021c0909060b040b1218010c020303040309050105070b0402042003040f0201020f0d080a02030c0403080705010b04051302010e09090c030604080901020601 90
    0x240c0710305c3c001148550708188542213609124103040c2005500450000340401212034034a4219000c455008110781d444003401000e0101081c48192852107000041c07081c80c80a03140c50045001d020320207841240da094250814138400c002c44144009000c090b0f4070900c0c0e4000010700a80940e1103075003030980c104440080d40301f510001751012100300701c0e1203a141008080e684040020010258003103080d21000c24840d0042c24401c89000850320380042da0b50341031509014250030007990001d81084010003080c40051111143d06412540c15540400c0e01c031614816203101043ca8008080180004002c00080c0039542d10380d003c0b05c90003a0251580c004002c2e00603503da40241c10701d030000c12a4080482d14107469540116803001071010f042d41030544a80d5010700d258090b05003910569150046610745192501c5055040b2280c0c200009204a070b6a001a00c503204001c0300911528841c1c00003202c041e000c5c45401003110000702907070154030307140c58100c42e560020018980148079940010031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 56663429 1250 56662179 56662181
    0xe03010c05161e0b01120b01091a01030509010216150b0d0b150613060e0108071d06030406060e0c070b090105040c03081303050105010f1e060905130902032d01 70
    0x20b00091640300200030030b00e0903100d07110302c945070388215000b1901d4000050085290303031400324007800b42c40c8601002100103041032184030340e06801640c2c1841c504030440b00b0710b032072640f20010154403c1c200441c00c0c1e5900c080301d60081c011100303105502c201440d50a403c11020800411110407400800c10451450b48203000c0c00240300c0308020416000900403030400c06600e07410003050310703000349980d140003011007041060803031035806040868603c0c002c2c03501c10f40c0c0041015500c03009a1904c1c10243e444404c410204030781d800350f2203000f10f80002c007003810b02207690890001380005000307503141402e0080c050300003940b0124054075001461408115001c1041c01401c1c09160840c203a100080c1c115100c40200ba403001d28044044003240e00c1c0040024000e024540c000e107084c40d1442552860821540c4100001d4105030544001c1c0741014440326030008640c03429a0019640c004105885130054002003d034144069454402d0b02c400003104118600e000c518031003848001042d040d480903042d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 56664679 1250 56663429 56663437
    0x11d03090603011205010b060a0c111504060f03150e0907140f060315030a0b09070504090816140f0a02040e01140a020c0c120309031204150302090612070e03010c05 72
    0x180c0d0000c010801040804c414150300c0c9010740c010400062164021400100305a024207041d02c0411500c1a00c0d80600c030044c40340c44d41000090fa50b10a587d235546c8861110f911a0340542800d126035030101b040128803da000f07203803041c099040c0d84252a15404100083e15041359030048a01c00c140d40454124140f00c40503000400140991158900000411519400003000d10707050824003070100565581c20000c0110480c0612504005400c1ca1482c40342403041c17641241d0301613820840d00750001544801100c4140400d0f400b40102a145440d02581481400c24982d0a03445840c1e109030700f001d030114500c03582c0c5200300e9041203e4078410764158281c58500d80031034a0030a00d01d0003d0703941040d54000b0100144518142d6a41d502030b0030002d80c2480d10349061b40308079070003c5454070341800c0c10800d00c100164424203440c20503161090401156001107090400c164003c2100d1031030340c64072000e80b011403040415414080c60040801480488518512480303507081c1480c1c1e40e4450b0040d004c1b5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 56665929 1250 56664679 56664697
    0x120c1903020705090703020d02070f020a060f0c0210020f03030906060f040c020607200d1205060402090901120201020307240b04150306020f0f0403030f030606090b0a03090507050a0602011d03 84
    0x2802c000d624200030820091801000101419000c100005410880744010101076206640f001d140195900500840410b5074008505000d00506110001d43d048100b400d420790f4100c41100709840b000d0320880c20300d41800070340c400c60b100c08801c0c4892541e010480c544158010f548194405190000f000305581c1c610601c40d0140c3c1140300440c0f03545224030705c41040039110300421400c0f06005841d10b45004c2100d40030100060300c1d0410940410581c2c055140c00100441c1e05508019030b04001601819041c4910a610210303102c64200316402401a16070b001e40040202120304000c12a50520341c51203006605800e20704000b1072401d103800e201c0d00310442d041c034840703420560070740c0c0c0c0c1d50b030095100c8903030404061010720000c0a110b04810040c03002d1442551203081c1c1030281c40000e01900c6040c0c0000c004d100d2681d02c148000b001c00411f95030325200b24a0f02048805407401c146041c10040d402003904048200d070041201e60301500405004240c40d51800c0744500e40c26244e940703d01450f000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 56667179 1250 56665929 56665933
    0x3050906010308040b03091219120902030616030f0f06030b0601020f190201050702040504052508031804020c16080708070510050a020f070e0f090c0d02040f0e120c190302 75
    0x910014500c40061580804411f04444071181c03030880300c004503040042900200c1c240980c1c09040b06610620001105603558018000800d40d6070001307884039001030a480d00c0c14101d070815600b0a2080c0c200070440d6480060030403400c04480340c0c3c80c0141105020a90707549030600301190955100280d1060500200006050046a400e110020350680d4a000780d0411409121034009a40c0701d108903801248540018500851248a040012150320030780c0014480401c20070000c110011088078a40100348100652440d4032500140081c05003031200c400921505111600c44559408400d00b82c0301c02c141120700341c03036580140d2659070f400390164680018114041c3c40e5554003400c05040c410800e070041e140c0c01c5907042e1000385420800d038008402d8003070481c18084101c100304076040d0080440d4020346030130b0503140049440c400700700000030701460f51400d002040005070f51040200f900003909461000f00182450100d0b81c000c2d100c103071800d020713800d061204244040c1c03080800c1641500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 56668429 1250 56667179 56667187
    0x105030f01030b070509090f01091803120b011202030423010605011b0302150702010b01030b0604030b0402010c05192a030b0a020d1d030c0609070b04230d0804030303050906010308 79
    0x2c3c070301100000183c002d005000381408180c00c503075941e8210510a074055061a240d544c0740014640548110080c018508017060440001181d4001c00400c0080c4100c4004215034014400480300c030354103102040011840841440300f00028a410401c05c40418005c4400c04801200500d08840c000e101e07050104580700c4400701400017034044540700d2070003030055840c207010000745401e81725011519500140d42d41c02c459000c2e0340e014410600b095100f568080e00f41030840c0d80b900c950b6407000d400a41030200d024511030070004200455118400b14209500114140c0d28002d03c1074100b401d0204c09021258109030041d03584101550304a0350002c05030085600c46045a00017940141c4e0190901ca440e0040c404002414000c2044504c42c450300031552007000040c584d041910241000c2c072950000403041003001c050a09903400c1e1404040480c0003074812005a4440145440c1d0035508203201c00f0000f001d001c242005482168000d4500303100c40e03a10640100e4a84000740402042c40b10144 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 56669679 1250 56668429 56668433
    0x1050307030f020d0210110d03020307050a080405120f04030b0a021204021c06060b19090812090a051504030506070905131d0a05010507120203040203030a050702030312040606140105030f0103 84
    0x546400b100b6001424129011142d500403600142c1b102c40340b5004101e0085400b441000e082040c00c1203001240703411415030900321780c000d0051041010701020005180e01050900800344901d2040e0761284031000c1d902c2174001101c1811ba0040d100a490b4040580d0000d0700c504658002c443d03202404005141d4036a903654204a030081c454007088121a0005602030000381d01482403001404210030615224013040c5480e88000c0c2001500b1810002c0703c0c801040b0700f80001801415003208110070756140c006200101d0702d83d46880c4e10190703000c42c1c050294507180150300700810a41e4020010340e9003d42e07034828140d80c070281c6880389503000907a600c22000c0d00061580300c1000440d00a0700e54003d021500300b210318040f508001a50141d5641041c031416540044c50744100ea0381c842070a605515064000070303168018a400002405030024143e000c65a05108603003494081c1c000800d15820303e410311100030000c9008230b10701c0e8010303800c00c102c1960080d41643d10a00301c804000501d6800c44e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 56670929 1250 56669679 56669693
    0x21608030f1e04030605010803180d1a0a0f02040902040501020d0212030106200307051f060302060409050705160302010e0d0c0b0a0b0f0301090510050f0f07050a090f080303060a0e0105030703 84
    0x80011030b421403006000101c0000c4d01406564000d02a120055445842140003880c0c143e01507c03405202e10b1800302c40030b0000f40550740907031a400030701c00040b041c0d9071001d903000d01400001e064643e420b44000360104290525901510945400382c1c200c0c1e0040d240d0b2a03069903a203803010200c400c0b600c3e00703200401481e48203600c400709a03851102001e2444069589951a503000050202c8180e0444000150444080500694003103605002440310510716008113003103205602501c10105d4854000030720160241003220b151149000805901c41c8041c02c00900810381850021128051925800e1002d0b100d1031030840b0043c0c00c40d0130b00d82d0a407100003900307005141d940c2c0d40c1c80e003003090010442c110344e400b88690610349001c2c01c00341020085440c2202c0450310010040000d0ba02c080f03045c403266108401c02c15500901c0c9091030355a07240b5000040c0e80d04d5095038080c000c0101101404983d0380004000b840c0070f07a10039030302d0f08880c075102c00b00c85c80d1a0a090060640560140390108081504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 56672179 1250 56670929 56670967
    0x40809270c030c0409050a0204090515090c1908060604030b0412111b06130f060302070209060307080a080c01060b07080c0c010801060e0d021302040905040309140607030f02030910021608030f 84
    0x81c8540042c039090b0b40d8a4000240d1307c003180d0600c0314400482c0c3c1d07903310b410441c07071040d400601d2080952400c04248070400303000106212040400c06c50f40d001038502d864000840f000745803c00084401460145044a14200a40d40e01400942c1040c0e00303021440700043d500348800c40c5c125029110740c03512410300c480b030f402c1891240002c05684c800052000c039868042800382456030340259581e20310340180540c2e440c0180c010360080d445954100464900425a0514140e1000c1140da0f01c0101988032030141036140c1104066030310000d0400100710342034000780701d030603280f00070b441c01172581000540c3c2c2e0060900c618408902020a880700340e00e0140448020b40b440145005651410304083d20104d82058220401d210760340c500348018144c00000b008010500c1180d07070707a9075109010104800d800342510013428080007070408003100d80207005480740804094175580740c103c54031200a40d182000084190300203466072011503e040040100c1d80c03403000d0600c0d03182c81c210105601040200c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 56673429 1250 56672179 56672191
    0x60108070314090309012003090418060606080601030605010201090b0a020307021203041a010e010b0d0c120216110a0f180204080708010203040b01121505040809270c030c040905 78
    0x1e51101c65082c2e640e0802c01141c010700000c001580c440c030800740090400c14211042040c07044800d680d415010070000200c03509640d06880120fa41c5c039050142d501d00d001c81140041c0803030300341840490423980c0702890307510ac0c1d4002d9909002d52580c0d5401a400ca07403201a003d0b0840c0d0502000800d010301a4000750307000460f47c4110ba400d54000000180c0680080c2c904a40c691401d420310f80244043c00c135810302505260041942951405990794228030448002511290f01c1e0083c00a001e03004640c900c504803610501555585c1d80c40e09008043c280108044034010346600c00c003252400d2101d40801039485400200000d6800d01c0701d00c5003c0c1501544401009400300f0010441040c240400c100a0220301c001503102c0c01c0c686001846450141c0243c007407441c40c004010040341954050368030040c850318000a042d110b505105400348114440160040004417084100a50424090b01c1c0011312040c580113a840310001520a407101303076240081e500040c00148020fa12903400560410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 56674679 1250 56673429 56673431
    0x105030f0636090303071b020102281203050717090111040806010602010b011803020907090e010b18030c03061b04050307030b01080c0f01120207110d060b011b02090601080703 77
    0x902030582c6610000742404228115072070200a001ca0a2101038281e400001c900e001d14150b143c001d100503d06600180500031851209076602c0035640244141c00301160050741c0b0389020358007103408440080e040c007802ca802d524061840c41c2154880c2c0b10360350248a003551250724000e40c0c44140c4c040000c01801d4102d480d581da2b0045d01007003c512004000800350700d4050b045541c940b45c0d002e801c69030910050b50500250307200c40c04044003014010001e503941111580d036240c844d01c1c8201c84084075034209140540720030700045051500308001e01030b05650318203d8032400004074181500e455800c41c50703903010392001d40400c280c41d242039840d40039048c075100c0c0141002d40c5e0b0f40009103000350340d500c10340f2014101d0005020000f800d00c441c021540d4143c0380c0064407052030f4002041403a2403048c80403200d6001c1068002c01c5612903198041200050550038660f4042c103040300100110242e0380d01164510f1f0807125031140f0020755001c4c031600205100071540e1044c0040d01c200f980209480205 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 56675929 1250 56674679 56674699
    0x51b010e130605090a0516090509040201050706021303060b190f030b13121707020c0102070612090203030d060e010f031505041a0a050711150105060a050705030a030b180103020105030f06 82
    0x190b02c0d540b40c8288501c5208001103a01d08000603060110305850a401f0304015010038144115190207600742d422650a1902a0b07640c581420804000e005107082c0d45042d210001c800400d01525030490b1500e00740480f400e00040048081e0b00c040600380740f00e02203061410b54020408509000d9100354841c0d44426185032030750095403034203444001c1c40025408103a034060f00610380a101c01460758000340302c0c0000d000500b101700c001303555105644103078000c00078490844070300d802a603000011800e40c0a003c494940c84031407121405081d0b503001c0c00e019051003000000c1c455004042c080200d0f5081458607426028085683c0301600d001003060f240160310074a40ea13085030000301510b04c6841d07000800509400c0c03507000100710b91840e0303000303503982d61011002c3c40c58401c212110700c1c1114001ca40190b92404141170a644034001d42c10080d109010219401c242e05801d40c001e80c0b41035404840756500e6207807d0303501c0340c2031090030300000e4009003050000900d040d198620550308485c00408a01c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 56677179 1250 56675929 56675939
    0xa02070503070b030916080a020d020a080a0f0506070804081e040f030b1e3c04050d02060c0a051801030e060c090108090c030a021309061107051b010e1306 68
    0x1d00400359000c0c0d070b80300f41c00004000031510f090002c2c01c80000015801e21030240b83c01c2c1c0345581e030784000300003074482c10000d41e9039021541c800c1c0c0da079001005410305032140100706041c5500300340c41d104402d640a000300c00002d60401d21500c00c41c0e1142d903208023154148401e4900a0881032142c40a40c40540d00410010803034402e5048a04000c6100e04403c455500d401c1108404440b0f9403480c81040d00111401c0c4111207040a4604c01a81100429501c0210086074100c0034000c6a6018003150003491041c0000e1080200f080c00200d65142c08607803031501c0e560300e451b034544507203000270000400600269424141c0310b9125021884140b5004c40e11030407840d13031141000015200c500e07801d40000707884401c030358000e89020f900180c40c102601ca09000240405d4840010000c001c1c42017000840f00041c513007482c1d018030f1455400c82001c108405180146100c1940100701c143c0c1c641c80f4034078610308012a55603104036543c006959036044a101503044c040039242c05091000140c2e160800829 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 56678429 1250 56677179 56677183
    0xe07021504140604060603150c0504051c061802090906010b0d020a021f021e09060304030c02060706020c0d0909021804050601020106030b0c0304020a050a0b040506090103060314070807090b0f060a02070503 90
    0x4c0a203015400c0014034524525010081d040310040c100b601c1c81c02c0908407103490340c0000582d800c0b104161042200640c0710810500c0b040005580140810b1824004040300e0642c407000700c0125100381c800e64000e8481c020b00d03645e03c450034441d50548420130841c10040ca40960007401041d207a034012210050303001ca0084d03400c80d80c3c41404500950380412482030100c92100003109500c0440001d624060304c0002181d00740c40014005000c0c410441c41e05011501e401045801d1315070840c070119110444801880c1d10390303140800388400079040f50030100d0714140d90300c2142d4254661844264901c6003020a0001400c4001d040c0d0b41955070350100040401e0741080c800d4420b08100074003e50f01e00d054410440c0e03564940d00041c7c025181c05034107000d0410a201120195030741190303119116810140100c018080300c0e00000c0210503112083c40711041c0015546060702c003604c1c140c40b079807510b0b400c000c2e00711500c02c03028550246002c08086c030541085c90040002000c0b0744183c034400343d00c48000ca4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 56679679 1250 56678429 56678431
    0x30b0406091419030e01030608070e060f060304080703020d03110315060f07030504090e0c0102030d2703020d0305060303031b0304260a1704030c020415090501060c020108010e070215041406 83
    0x2041e0300300c56003c5401007541c00012000074010900b002c0001e94184140a41d40b00d2080c080c8140d10341c8144080f4815594403492600000703002040d4942e00c1c03419150190a542104800328050b2141010b80713604103019010703403c03002181000e02e80c1140e84070007400c0e0302a030381c40380c810750000306c2001b00c001d81c09036000040803154000d49036270baa15480d240c6440100d83c90455040910742040915070801d070b9000c012903802d20146500814614000300105004074520712126206007103118401707080580119078034a000e60103440c00c0106036156418103849110464200030f00300f0120740840c140600e240e0246800c50300409560110391442704140141811902c502000c8017000304071607050b0740d0706c480701c9002959503112a040e0340c101607801a15107900400300a206075141c855405454500341c04a100a2900000500442d6034507040540111004001a400107041c0d80011500c2c94103418854020b8655a00400d40000300c5401c182085030081c0c0205d400c00849201051400401c200381 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 56680929 1250 56679679 56679703
    0x10203070315050604030203060103031d0303040e0105090a0b06030105060715050a0516020d1205130507030c090f0209090c0a09120507050a0602010e1f0609060b03040219030b04060914 81
    0x340329498021810b564541548002c0c40382100300014001a00c006c1410390449505081070302c5090f601442c0f0215054010000c1500341c403000c200020710f00040c400060482e141a10203118580b5500501011740d002c444c4210307042101000100100c0c103165000300304c41c50181d4000080c4240001d6800d050392000d0302e0283e06103481d03400f880150300043c10b01035000d400b24001040c100c40d503968041c00c54901103140d107060998620000381080754032070000e49519480801d4900c400e80300c3c03402e003c07490483c3c00340800341c0d031400007a12000c0a045c13080300c8130101e00900d115115510210b01602038ad2000120f44100101000001000c604000084400620410241070020304000c1444034040443c2d1106085a0511640d1384900c000440e09901840c0c014044100e42c00002044102510700c1e0303401400302c5442c0580002d04182c40c480954000c0d4400c848607007050245075481040f0102e6408042c080d40c0c480c502050010b40c8c668040b0010910a03080401c1c0d000085004500780f224011035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 56682179 1250 56680929 56680931
    0x10216060603020f100f081503010c1d030c0901090b0d02100207090b04051311030f15010305160b04090b031203070e04060602121b070f0b0a0809010b010c021306080102030703 77
    0x105200f10311308000c8908030b00005540d03003005030f140e4540050001110100c094184102100440e0f82444540e0f040e040711000500248034440c1c1d0346400401e440302101a4a0760a0a5420a05031903d0702140c5900001c0008100040c980d0a003480b00000301121100145d00c0040b41000034016284d544041c101b0a40907000380c45002e180080100984940140080c481ca1404040101d02c0301c11020022030300d50046041c0c88004a0709003c6490700c00c140c07100c141c42d413003501030b6182925402455076050364403d00641c1c00d8924144040c841c814070b40c0c080c4004c010320511013440340e55216031100b03072080b80041c1114210f00c0f0304400d0450a80c01910790b807002811a01420071542007038000c44005000e244001c10100d00641d04025a6000e42658040c2c0840510301d1402c00210800030400901400d01c01521203e0f0b4800b050031481d40650071500100d01400005003440c581881a15030110040e11603484e182e0700d95007000000c0610648045845e40d4407100420101c1c2c0901c06180b084485d0380f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 56683429 1250 56682179 56682191
    0xc1b010204170a0c060503040b070e03010f020c07060905030106030302030a0804051207030c1115180103020702090106050705060906130f0503072a090207050c06070302120706050a050702010207210201021606 91
    0xd28102d4204c4941200003031110070014003000416a500302c0340e01c9a414a00b0702c0d815030405001074054110000f42180c0b040c0003180b00800792038003045000450b062a00d070301c10b155aa030000d250903144103100140143e08103219215a1900030083e243d8054030500c02d482c2d400c04250340d07842080d0498030302076000540b0903081408005060007026403d080841d0120a801c03002caa0840482c0b2560390b000b48040041003841000742d012b030301601c00366540107040042941c3c40c1d400007041c17034014813002c0d21a44205000322b0401000803c0035405290048441d00314509aa200c880c0042040981200c0c036110403c003001c007044401420030200e02a503000c007050507c0581a842d28032200b80c001c00c81d5240304205d1400026400185a044944241e5030341d6107542c85810140d0505280e0f050180e040b079400078500c420040d40f6440030340b00f015110810001a211004100d01300d02403964010002c25400000390380c0a48819036000a41c035652002514010305500300800d449458901214200e45901e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 56684679 1250 56683429 56683433
    0xb0c070e01091503080a0302040b040305010f0c080403020c0918011b03060602030a05090d0212150405071203120f06050d030203090a0503010203100b0703020c15030601170c1b010204170a 82
    0x260700610703440b00c00b44070342c80940010307841c07596281c0f00c000c2c2150000910941a80d01075016140240200d10419841d566a4148180a0444c090056071928601a00d5052076030040030818007643c0c140d8020544e0b441c00310203201c0800c40160440300103201b0082e144241b030809003c0c107180c0c60346040140070501019400941920426000300003550401d002c1070160395408429a0400319049810800492007400801c0c43c05c001f0302c1c925660b9009110904030403403040034034176003d944686d0880389925529011a0010112043c0060010304054000400e900460300810b81ca840b40150008105d0b03904c5c000100e036030703000c0740d01280960004034850070b1300c1c03801120300f200916054000354a0f5140106c890721048010b809404920000400c44406140c42004610450100642102d004000c1222400c1150b0021140c05001604602e1080154501c6002082c0105407146100e800c14260040b03a400d080403048400c0010341d800c1c000011104801506e06850b00a02c901500890b2014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 56685929 1250 56684679 56684699
    0x20d0603210212090d020604080307030503180c01080c031e13030201050a0c050a140c0304060804020306060a03110609011115010e10050a3b07020c04090c0603150b0c07 74
    0x14160102550052041d4503104102c00f000c80d8005034080310703903c000515902c000358840c000d03500904050311011031800d08140c0c10030000d502801029282841c502e20316060107a0b200d1050a07100d00140040f00032908070400400599001403102460055103000e4011400716004210340d40648619481a040145602031180750307000a42c00009004030a003c2d103000d4250310401c00c0100070084105041403510200c1c005403021001d00c4000d90740c0c0d407980c4050007000c510064800f0b920a00655001ca00c0da0320b84200001e0451b9808843c40329000e07044002c0000070341140452074103000054000300c0d40003200707010304445195940e0140c3d12130750502024904200c0b001b4110400c86050340340500c003998a858200b02150110303000c02d100700c44c511100007100624400211001d1340c0400b0403030115000c113a401442803600e6400c644240b800e00c0d04000903a061510003500c1142405401e06c07150307100f6080368000c7d03148804580d001c6036650301c80d940180d05c80307019000960089401030040300300c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 56687179 1250 56685929 56685983
    0x2a0e03010905060f0403050403080d0204171903120e07080f070e07080a112208010b0103021201030f141902040605121b0301060506040306050a0c0c051203040303020d0603 75
    0x4190020030040110741d0b03445a580001415018a80c400d41c0005401c2520030000c96010356844003100c0d488074010324880300079401900401d044da20038035840c5070310300e0030000782d211300104149503600b80712400e501c054903603036044080c0070a402e8891406817160b040c2000483c00a046407401800008e201b20300d90f41c00d081154105030303121903c407424441e5041c0c1c07000c121038001055180004410004c0c0441104501c100d02c1c4503028030710701102c0ca800b001c5110801c03600300c0b10104000d225800d000c100441c128420070700d509065512010041c8089940710f00107188291003400c041c0544817400b0b104921300b0103205403001368540d04000038021404c2a000d0300c801400d094420b41c4100e5044000603441d0454139950010031100c11103625402d80c2d00b50403c40c0200b01c06024180c0d110740f43c0c00d0000207000221030010169080072410102181311b59140c400d07654002019109101340503080c0e0b8203030303480a0000c4d41007680030b001200030001e491043c00000d503c104402c460394903040f6544107074406 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 56688429 1250 56687179 56687207
    0x903070c0303080a0f0603030f080a050106020712050f0a1518170c0a0c0824040c031506090203010b030402090604090206040504091e050c0a080c01020c040f2a 70
    0x42484610001440959098203880e41030401100543d42d2401c2c040c01800650040000c480c1400d03400024560001c1c241203148540380d44201007544d5042c03e0506951086c0300343e1005078806542000310031452902c45015900c0340b404c2c1c446052041001c946050b511100c29581701c070128450803c1d448240c4681244400031b04415100c9a0140c3c41d014590040b0400c1a0242c400024141600210500c121040194003102d560a565100c05a01c0d550701003648603081130800e8508150241084d5003a550321655001d4a111001030840d40d50540640100d000d0412094540304007251001c07150000d18060010128019181e03d49401008044a006849180501e10345289580940c403240c0440d0155079007503a0101d4483ca06252201d141c8184900e900100554460f001c1700704040440d02204c0c0c07240844540441644844606448000c02050140035901c49415241c00b03040c603401c1440558090f080020344c84e400b0711201074000559101d5803820411274420380450940082c00921210 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 56689679 1250 56688429 56688433
    0x705030709050705070212010b032e06030f080a1101020a05090a0b03040308040204020313060e160e1315020c01090f0b0109090b1b0c071202031203070e010c020f060703050301050909 80
    0x403d000300c010b0300768440c20300064010084010700c01e050550940103250466405000c490304e40d201c10203500101b4020303e0500411850449080d00c082203180101016a0782010301c084c400e8400b40d031380e61070550003854a881400201c101c404000030081c400741070301e41040d4454956541124041020340e0b24641c01c4403441c418140180004070754848080307a8860341c142d900517500c0d1181c08040b2004991100d000b0120341c2000d9990382040408103070302600840040030442010384802c5200d10307000003140e10032001541c00d0b0f1a500820595200d00020307199090340145000c0402c1182c50a6640121041e0381045209040004100e000141a4010600900701300140d0070b00f66510504540701510f11801302c11706021643e0f028103420111044215070744100e803c0a6075401c0c442002c040184802e03032080c0610380c100032210741a1800c072441503280da40c480c024006041c00640f4031070030111090340c22099562050341140c40d4400100b05850094541c80d40385c2d8034003400c0010071080208100c047d0307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 56690929 1250 56689679 56689681
    0x203030108010f06260c03070b07050d090602030708070303060b030406050f0612030412080f04120b06030a080405090712051503010e010902090606070809030607030c030b0111190201031508070503070905 89
    0x81500091102002034101c3d9150385c01d00b0501e108610304000c5820540d0705015881c40094082d006100134020a0310030425219980e1030700f4015a02c9034070701e100e0304c40540c1003040301c000003540d280001c0034414172a0600086840e1a0301d04104c45800494080701c1e6103030f4a00034041c0d5100080441640800125403040100414103203c680703d0180b032003580d02d4410f0750b04129082100304002c0c1c030170b25800550169215035031030007040c1300144829400d4a81c0e0300c01001045250401103542d052982c3c200d803003d4542490002030001b40f200080920082288502e6a02c501c13080501906010b8502402c020071140a00070805003103807060849410355038584498040180c850500c055845002100c581c1d8171100b507400e1a400d01d00c40c070041d8550501032036040082242d00341e4840d550040749580c081000142e9400192001d00707a203085034840340c0c8401c0403440e194121040f050341c918818075010a040c0d8840780803901d0300300d5a810407000c6412480d030600c01400d0410181008120340d11061000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 56692179 1250 56690929 56690939
    0x10206130c0506070c090e0102040612060608010506090303120903030601090501090302090106030506060409020a0302180616060e0a08070c15080705030f040f14011e0b010203030f0709030c03030203030108010f06 93
    0x45040c1d10712440d4000c0030007140c80d40520524a00c1c0800522a401d014010110b000b04058001d5200d4003d03000401c9401c90b0b803000d0050188a001c055a440382c60710341c1540d00b0310007000745980203012401d0b8036220030880b2919048d281101e4a000e400314800654907803c10000240906829800a604121100300c0800c05680c84101403411038120342000610f43d290003010800b1031265400c0720a80500004605c00c13010340c1540240504400e4150452280e012081044018403910b0036544008804c00441d9020480b50742c068010b0403843c00445554041590300d400ca00e4000c60011b555000c401141086200e00600051004a1043c03801d001e05142403e0080d1541c00b000d02004da032400e4481c0020200040d05007003120480d04481400341007c074550300d65010b00f07000e210000c143c00c2045800ca095038864007546400510513006181143d545403207001b05a440100044100501c0d070380c0010200380800f444d0f90140d4041e80c0a140c0c1d0750304200c15542500e0200796042d6013940b41c0881041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 56693429 1250 56692179 56692193
    0xe1e06041203060e16020106090207030518010e19080f0109020109060e01090f030809041109030a0b0c1204030809010e0c09011413020c07080f01180201051303060f0203040201020613 80
    0x64066032200154030000041c5508030000c004640001e84040044018405c2c1803290120010145456900a203c40740d15410302106a0041c07070b00081c0401c2c1d080c09424000060042c7c00d80c1006418500b0038400015400003d45d440490400103856482c20402405994070a110804206481300700074002031040342d0009184034a50b220b09020080401c4291005a10070380400d4010301615100705600b82c1c480c00c00034919403000c1c131441e104602c0d001d052012905028192000100010701402ca020500d413100103030a20001d200144603d820003d103019140300a02080c006c5000703030f69800480c40e0001c10282100c00b0110140104d83c842e00340e00b80d036903441191190540b9400300744024000201800301e91182080b5116889490000c104407140c5100082d070712080b218260b08a07a11480d06407081400c0b150258600314510080c01000800340d4018001030000f82800003148a07034a56a0700c0d0070003220448112044103540000c00e11042d5a410445142c1080c01e00c58131883c040032980d1004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 56694679 1250 56693429 56693431
    0x1060801091a0408160c08010e0708071e030203010603030908060705030405030d0c0c020405010e070f0503010b040b070309080304090f0e1506040507020a241508030f07020d150e1e06 80
    0x6070042d52501d00007410003408105031a50103a4000c0410504040ca140880610b005400381e00303c903603e0f1121020901030300003140340c22604540d024195080c01c00f210314006241050724454036298040c00007006071824401d28005602a40c0c5d4020264200203602d401c00c4405800c00b41001024010720021400100440d4141d42000000003080a00000151001c000d0b211000c0e51203840e00000003403c50340f840255125080b244c0e51100c402c007850400b612030f0302080c0104005010180418458010044000c10b0468020701b01400c0a40d9100910f80c174641c02504142c05060b10390650801c00012409180c03001c010300d0700504a6115500d10780b6048400c000d120602c40c80d2120007041c1124001d104900c1c4460f0400c0038100c159440f00c0c0341a50001e404018000e02030701e003002000c2492080c1103d402924980c0d8055883c04003030202c5400c81c2d4208000a80c0d100c0031071701154001680c0e0f00041c49002d6000c14000c070b4006401c0201c1400c01c4c15031003038011980c0c61032a80000740702000c5412 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 56695929 1250 56694679 56694713
    0xc04140603060f04050f040302010c2a0812090115060c0201050d050a020409020a090806070201060302090412050d0204121101080105060904050c091017091b010f02100204090207050106080109 84
    0x126481c1c0c0c2c1c500300000e2005080c02c520341d07007142ca400107108048015070360040c4554000d8009001e19104000215009002421213484010518040c02c1108000580c1031403003c0c028803009080204101030071142400642e43d4840583d500d408103d501154101b180000f040c0d103040540d1340d100140c00291152240c01001c448156a0700f00007100f18004c0d40c155805445144021500c1d0545044064110b01c9140211034080c40b4a500182d4014814050502030b80c1d405007a281c000e869079521420b0304291000005c081c0311040c080e600c15016140f000c0d000405508140418414a03801c1500c2040780e985e41c401e041050702001485182c41d03900c11240c03510010b42e40094039a0303d0100242150180910166010300da00329000c1a5a40c001516140498004848000c40d203450312010350b100e507a69284507070020031130800030803580221003003010144e2900654908051408850003264400e80041e0422030740401c992080c002c0074810f12020304411b0000704007001260b01c0f00e294104044020b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 56697179 1250 56695929 56695939
    0x80c040e1f03060f0b01020c0402091c050309090403080402130510060e1203070b0414210c010b1005030702010c020f07050f240912151503120d060603050c0414 70
    0x40e0120a10310648000b160041410400781c4a58004100900440703152240148680b00b044c1d006031400780300300c0c0c000d040004c003400800c44a905e0003400c100900c141c02c0c4c40f580018003440090f0344070f50302e4941c800d0340b081d0f81d2280285005d00c108140c4480c4a840399000380e00d0311040044801c14000c031a42a140d103410590a461720010001e40001564045010640808a40b2004116140362071a01551180b501c9050741d24070108440d5441104080b954020100c02c0d41c4107101e46110790041007181482d400101d5518810b0f80400d010702a5036030700000003440003007082040f59080c407036403e1100492000d860321402d14095540d40360b51501460f80300715100c84042c031490b40c544010204400d803221070100d18410303000808031139070408002c00f4081c0c496102d05a0741d00901180d103000840407951140d6190b2501c84401c0414850440482e0701032003544141600485d141000c1d0120701c0300b415001c21040d0419000a058502c0a444209084802c0c00300b4080c3c64007030b001c0d1050090055407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 56698429 1250 56697179 56697211
    0x60f090c17190e01020c061b04030210030207080c06040314040e2e080604060b01091203140c070e060f0102010605010c0f1115070c06090605120c07080f0a080c040e 72
    0x60041802c05076400c81e0684900d05001115122819005000d40314242c1068031000d42c4c402150194508981d078911103140e40402c0705100528003013081041c90412031900505000c110b90311800160300c404918044d591100c4100400c00d81d004194010740300007a0045401c061900405002c2e81002412000d14001200d1103044103880c01801090f10204000c5c0c1d02c07a00c656900c00441e114142641d082d20b9503810243c65a0306540102c5021080b0340d200341c0220b9100e865610b04544502450481d041c0c1c14204100d000200b000800920340034013550f0690003001e05010007084000502d20700300c40d0642e41403900800082c1e8200740503443e501d4000b40c0703208000c1418540200980905a401c40c1c3c0b01ea1690901c0a1440c0000c01600c00d0500c515052202d0b5a11101c080c1d500e42d0b0940305800014408010140c1034182e900c0909401540c50044181030400e10780c0d502c0d40c260017007811840d682e44c011502080c62507000510b103800a503601403c03407416041c04070f5501c0700340005029a0f081c0c6441c00d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 56699679 1250 56698429 56698441
    0x11a16020d02030706090806010605040e010905060a0504051509060f0d020114120c0301030204150803030115020304030c030b1021060506030c2e0905030c0108040302030d090501060f090c17 83
    0xd81e0900d2019030060039204007a44802c4040d050303420034010b000a62198100110308680184116401d40301c81e140c0700c81041e8600403014018110043c205900003050400000d41c54039540111030080301d102d09018a041d038001c050154808005221a104440c11084c4400303a8a0300306d90590941c0d02860b00745490300b08500d06042c28803500303450901c450844130030021801107010146058a100711800d00c603070081080030b5070044540b4080c41c005600100010404000c231540141600502401501d0038946c3d02d80383d8041040107588207803980c211401c01c014842c440c010ba81c002400c6280c0c68501039041c1c81444100e003070f2025400914081d44d650200e1701d580d5040110500d0148014200d6400b070709002020318004800345084038154000d4140c0b039510f903005041540903500007034010f000c880c2c9100011035242c2d2014005401394002045800070440403400303030303a01441c0540300100c0d100b4030340b800d0f01c1c0f0785400c583d01140d54a0310b4440d0a40e40d0301c2d8003040a420031002500c1300f5409840b44 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 56700929 1250 56699679 56699689
    0xc030a1101200a08091203030402150903070b0c0a03140c060403030f06080d0f03050a0e0a1b0b040605090102060f0103030e0d0201051b0705040b010f080a05150a090b0306011a1602 79
    0x81003400542d8800c0c2140e05042080030350040c14403010582e401c4081a58403d400c580d24003060303600035840520942c52440d141c907210058441c15030014119070745141d032a09520042d920416801000d038000804000900da0019041c42e4050740c40b40c0c03c186010040038101c0e859440141c802000c054442c000c130000002181c1082c4054000078050341d00058116030701800f1010800340c000c0100e42003c1c0040c5014090384602c511a600307500243c00e01004070307910010180b24112125807901d8020001064481d9600003606c09401716450b8181e458208000192400324000c1400c02c420304590010300000c0c0d4405510506954103884071507107003840d44010f035098084d142d000e5060b44035480c02610385281c0003481c801210800d55040000186803001141c2c403407690028078010904120219052000c3d0b42e1100d9800501c00b40b5000c4001202000650020440d80c000e02e43d00f601c4003900044c504e0244451401802003000750307020001e1500100000380113a210640c00140d00300c40310b400b55210 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 56702179 1250 56700929 56700977
    0x3090b0c01092001030509030903070b0904090b040302030c07140a031506080102030a0204180b060306010f09030209070504060305060103050103020f0d020612091e060c0403020d0312060807080c030a1101 89
    0x2c0b110500040803803200d103001c0420f00c880c40690000741004045061840c02200705e40100901030094000282007182c144140d42c44505207541052355200d040020800450499000e40d10a501131070359030031910b20603454402c65400c90b400c1c5120083c2c140304950344608100080701e6201201d800340c01c00074095003000b0304055021107803a5000008021600c01e50f64024000d0366007580790000b8000390301e050030040b10307511440c094020b07408002240c0d45601880701110f4103451441c158080d1a1280c1c045664401c040c0c44a81c00318101140512600d0b4150140d154010404e1a040081d58135540014403062490704400340a1900901c0e4402076407a00702c200c5403041ca0a0010410504000c205550b942140c400240e00c00e011040c11034500d0540419000d02070510092810306050454082103406481d02c6412402d00507180802400c0c810b45018040044c01d0303000142c44d0940c0b17002001801d00e158005024443e41002c2854400140090300014850b0707428a0882c22199980f508000c441c01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 56703429 1250 56702179 56702183
    0x1213170a0b01080102041a03010e0402040914100203040201030506030105070905190e090a0b060a0308071704150806011b0515090118061b0c1101080c130602070305060601050703090b0c0109 83
    0x100d41e10010075455015002042110f5140b2194080450701c10f510300e040780000e001e0b02103180b1034480030030051f107040c0d0441300b541c43c01204003107240228001c0152a083d1452128000d07107401004001c1550f03014032070aa03104100b60000c1c081c6240c2030301c4c000c0c20052113010b400d11071031316800c0004a100608104401814181d01c4003542411f206640039070f500302c1c000c4121181802030b0005001820700311640b84c200c1e584030444a05140d1a03941d180e054078100c0b02c1ca003000b503c05020000c0d0350b910aa042144001003a00c42c98502c0c01c0007000144140d106000343c800d003440f1001c110b00002c3c0005111203200f01c40b03e03080105034a465503800e0241c9072500c440400e143d4201103407410300c84a90710031100c94412001c159490140000b0640d0400990003028104940b081c61f0050154003c0110710f81c09104145803d14010b41c009011500c007569400040041c0d03c03e403824010050308006983c0c100c0402d00f0b19904280440e036005051004034011300c6400440818034410b100025008942c0b0702d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 56704679 1250 56703429 56703443
    0x906030819051917010f0b040320060a0507060522030503100806010303050c0106090510090b0102150108010905070b190c050a0b0c0307020105070f1209020111030310081213170a 78
    0x2040d841da009119071514164054990300c844c1c00041c4400c444404601110b524005a17400c161443d01c07110b0118061311901d216214000041401d5556a10001d011031314040d101d4a0301d409440c2006000c50707400a18031241c24506200d00000311080031202d410707196040c90f05950b41d5445000b141094500340c2e01c4594544242c00003c0100354211001d001e1101d102d200802c201b541e41c6000e103064640a807509529194564000d100890241d00324a544100c10300461704d040d4a580005840f1030406d0f400303801244d5441c1c0c08001000f4050120394000d164511103d420700300d90000e070000c5082c4101818041c4613400e54440c0c104001070168440b0117801203010109032601940030310040e4812614180154649000507010a0059040d1041d4111030740d2054608086600c0d01c0c1d004042452069043c0010355204001d25442003000758414012481c0c00d0030594540035400e4540000d040d0500b46502080c070003269000d041c4a0f4960854100c50b404d40c48450b500d01c0341600b06450744001030302803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 56705929 1250 56704679 56704717
    0x20405040609020c190308060402030a0b0a060e1009050901050d020d06090b0f0c1204061d0a08040501020c0603010305031204030c050d09050901150e0d03020f0303150a090603081905 80
    0x1807007550f4081d10083c18840b003900c403503641d0114142e82480b400d000c003c010684034404030302c6608069003e5980042d003c240041c003542d9503000110966055030143c00081e03102c3c005001d480c102000a0040d4140034140321940f00c0c10f050010b540007205024090050400800315420b5540d910140302503590000340030803104060b42084540b03080304441e006a40701509000c1565a0303815400c40308440d0790310465042d90b441d15510100541010901c00005154544094486d000280140200f00f88201e082030b640d10700e00701c00603082c0541001c2d012f20601c021f2004001186003c4100c6050181c080110004c075951440c09442c2c1440c003450241072807280c00c042c504030130b82110301d0100b90340d01218104100e80e40d0b60082c0d401546507040040c001010b10035250810700f03028112005551190054504c4140800445803030368004550340300c5403c9000c0c110100d01e007030140400020f41020a01032080c0c030708540780c10940341300d55001da150303100c100707880a82810700c01c0e000d0f281b0380c1e030401ca140e01007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 56707179 1250 56705929 56705939
    0xc0f040209100e0a060c0209130302010b060409050a05010f0b19020111040801050702060901110d051003120807031b050f030406090602030c070519020f060309151014091014040204050406 82
    0x214110a46860090000c1000031441307a000320246c20450340d0003044010b050340c0c0d03d1011440d080300140114155902c0c0d0420407651f54460005c0c001418544500003103901e405090741c020b070744040c4d1100c0100c1885860621106256008541301d03400c8001001c04441201d090403801030120010701d030011080814003103251807040d001580030301001d07404c5501d40c1d126070000c2801c0b6400c1c0030000400c1c3e0003c00072405041c0300c84d040264442c0204041461213a41c80d01c5441200300310104040006020100300003807141c01d84101c40341520307000b81c0c030040f0f02600314025040c2d01c40d4511044490b0b0000c00000e0400505421840349960b000d9029512030030510400102600003410845007400f95041002c55038011120300301d44650000c04114203d52040b041c82815800540448014043c8400140080301980542d6009059a984042c0c04518009000d10359070080f02d1802d22801d4404140100402044465000e4600c1d03151a006e8150382c040000f0300901c201e170b11058010b402c010000807 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 56708429 1250 56707179 56707187
    0x305041e030201031a091302040f020c030705061303020a03030f24210b01060c1a250302210705090a0905010f0e0717060a03210f030e0c0f04020910 65
    0x440e4401e807000d0102200403050310200340791750381c03103540c11603040e40000f1070f43c0210012041c182400030f00002895401c1d090a201682d0004000e071b00a44d00c0054048208441080361951064520030b24040420403654020740b65603801501404040d1103000f0124006083c2c2d0183d60a80c0100000200c42c1c20705071f291081220403032049001c0c403d440e48141d8042c0c8119064030012591000c100340141c0e08154040da180d152648082d100c880180a1024140c80c00c03500d028055000c829a00e02111090151119102c2e180c903000030406005100c6805020002444d040600546120740002580c0c0d1800c105c0c1c40307028922096610860842c00040e07203007459400303d0305a6130030405c10035030701d43c499840c000d0410003914001c0010b4641181c0000d480595002c6036081f00c0c004040b11007280c1d680d00c5400c060366650381540c88111002101145203500402620003500391401c0a02840d2094019240c032251000e0041d4001c1c5030001810a960741c035a4115044a880141042414428408010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 56709679 1250 56708429 56708489
    0x307090e0403030c20031603020a080d0501030501061512050408160809030f0f03040b03060d0f05010212070e22022104150501030206040918122105040506070507030504 74
    0xa011901800c0f181307610344524142120017943d2903005500d040400c41c42612460480842601103004060f038003400198200000c14001c00d10941c00320b00b950544c20f10343d003101c0069201c2940042c0500314a00c003541c0064285000020540c0300044964850034503150317a00c65120882d0740d014a02d8807030b03001c00405102030107540758151b08584040c031220613480d40d00c07111142c01841c1c0c1d5009000c2001034666200c001c5900000143c4517107007050443e502c1e483c44174499602112903940204054038105850f038001e503805101460046003034040c20000c41d1000005140c90b400c81e1080102d00d40b00741c2000e030121010301c803440070a99485101e400500c0c8a189003941d08854500c203105c03c2c0642050a4001c50781a41e03001410346151034a1700090000800c10b00f0684910264251400310200b60880700d4907441d03050a4039032081c81480800d1404c011070021880e594560700d842c0c2032002054000810070340c0000709040096031401681400e486a009079444015201c2401103030f424949a0f54000e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 56710929 1250 56709679 56709701
    0x30516090e030306061b1006060c0302010b0d0b060607030509060403050d02071208090607030c050a110a09020f0702010305100e0103120809010b011d04020412082805030a020307090e040303 83
    0x4000841c041e0050380d8403840103644469000c40c0611041e40e203180b000400e030030031441d000c0450f5500c225020b500030030750301c0c0c592010b008115020042000d154082c050458149400c4421003003920440c0d64003500c607580a010740c1d02603070020800030b00b054000c0048039200d410081c030035500c46699203000c544d9400581c2c006d80c0140106100016003a001090f0142603a80c010162030030003000c0c00030301406130441117080d01040b24035902c00020481c10b200116119000340348071851110306501344420307414544d0100181a1041009000b1031511600f6034142c20740c24a404641901e03118000b488001c626007210340d0f50301548000000304051480528a0510581ca030100a0307078480c07030450f080792002c03101c450204007241507546100ba18402d1001721103d00903c0103041c82c0d265201c3c00c03011074500754115080180010400804404c40083c8074811109002a82941100040052031400042c20945038280c002c404101010301441c010405860b2401c20841203140500300203019000072411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 56712179 1250 56710929 56710931
    0x4050a0f0503010615082202041b0305090c0a120206090907030e0114070f0804050f0d0302070c0803030408040306050a060e040602090a050922050309121005060103020a0c0f060603051609 82
    0x10014000301c44c0345c01e1440c20109911000d02565448185c980110401950031700000d10403001800165141c2c0f0420340324a00c00d03520103088000c40000501150800340c140d110390342c444840b115096481790a504160382a90601001e131240510120b141401101480d0394811203000821940a42c1a848130299807650002400394000ca207112000c5460284c0d110400101d00f1100c421031079004e00399240e006842082166101c080040200d41840c50851510000070b40000780001400501c00144000d0407940002c0e52450800c1e5035200410b10462100408243c4c0ba07800141c0c4082155004600030030601240518505c0c042c0713030820080d804240b00500c01d1845000100741c60400319503c9104035500b21038400050398485c0905600860034204607450b100400429255850309520f0200c01c00340d42000704001035203070301c040c0160b8030000c110720b0416105020300f01919503c101600300c0560000304001c0d01c4c0c881030030414040c20641c0c0000e0042d1007031251400c80501081c1c0c20008a03180004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 56713429 1250 56712179 56712191
    0x301090629010c11040513080a0c0213050705030105090405030d0f05011d06011202071b0e01150206071b02010c050a03081801020405090c0901090e07030f0c050703020d080a0204050a0f050301 84
    0x100643d00038003003040107440c14036803010341e245a0900358021904203082c802c00214041c010341d100c5800e5404501010009000242c0420842c145000306401405d00000140151b01d0030000090007400b0500c1078a2042829001280a00c01c007403044818045400400348004048607801d9006803d003840b9040412985140002c4100c5554078501d005040503582c0d4141d607869640214081e400840302940c0340c02030080d407800300180440003100100031190341c00215615049804400700a10003060040d50420000c0141c12503000500c20008011180d2903481e0104a00049503c155030500003031141c40380f065a4010b042e08044080c2c403402c94010381480d65030b00c2d84035681c2070b801584510750300b1080d040c01189075640c000f00502035a000600d08883c06076503911040f8083d18041d58024046139803928182451903180c02034000c0f514407030030b00b1741c17800015640c002d40d5100d6841200040043d55008945514031300c0d01110000c002c010042d440cbc194550300a030407058824401c2e80d21a600e840 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 56714679 1250 56713429 56713511
    0xc0a06020c0112020a0909020313030305090a030c020d060e010203070801050f0109080718020c0304032004110306040507120e010615090e0406020f091002030a031a10050903010906 79
    0xc0310610160180c3d03800e101c0f10591061480a900314880c10000c3c090340c0d042c00b041d00c03070007031001e507115008a0054051000250801074219100606000000c0e00180c480030b02080c0c00032444030b004c9505446902c1a045141017020003001400210001c030f50000041c00740c03481d849041c0905898080310034040e880707440001520585014443c0080c95000700400708a0007142d15520000403092400142c03034403030744159080c11079201d41c1042307900b4a0204001d958184e15040d4450300c0c07500035181000140240600304da07041c00010520740c07141da00c0e40b0000b41d00c2c2d48038803508640250300010034030481d00b12401481c040c0009009060500e0b6403800380342c195502c6507030004115101a0340c0129562160b442e010082e61181e101c0c00c0010008210b100d000343c07036034407510740d1501c000e43c0910380b0342c605113100406582e000200d8498a490075240b041403991444082c104000386070821a94914a84010078007500c41a02c0160075a4940300311510034030410140d21003c821034000000200704d0030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 56715929 1250 56714679 56714683
    0x905010918020309030c010c080403030b0307030f02090402190803070308150901061202120106090e060d0203030d0e0a0503130303080f0c0403022709010c090504020c031e12090c0a0602 81
    0x24450400c40c8201c0c080070882034000c6500550300807440308143da181000d50f190031429a6184021400040c00043c1000305050b418415500200c0084014206441c034644402d04055502c0c0d10281c0305030720368404642156039004000030340c810740c030585080260391400d107251070340c120400940c08100f503003000489040d00300e4041003003080700030080b00090b4200320003240c0d640340d840e200e500308039820000000c1500e842c2007810b00805c2d80d41d544490003800e01c0031030303944040041e11240c0501d1030b2001120050f0303004001da030640300440100080e4501c40c0340b1070514000020001401d24000020540791291441c03040304207481c000c2d194032074252135000400b020742900720380c0a400d4800600040c001403815840000e101030850144803482411a070402910704020390b00302a10ba9960b0142108070350300040e2500081c00e040b0313011814500d10581c0540c41313201340342c081030920010003011214001807406a50ba4900920b0303550701c1310314004442d81d60f101c400d0744a0501c40d40400500150803840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 56717179 1250 56715929 56715947
    0xf030e0a0f08040b0f0a030c020307050c04020915030a0e06010602070602030a0c030e19050301050c07081b01060b0a020303010e0f070518010e0d0807020910030503160303091401090201090501 84
    0x10a0080251800c0c5803918041c10344200411104202c0c200800100c1c800c00c4406091421040040c40b5911802c10001508558440c0c0c1801c06540090144a01088010854030b01c0200c0079140540c3c1d9103182c83c000750800600e40040346640401005004500200e50b0004440540b00c3c012645980d0726450240d0b0796101c48d10a003401070784100007001441e4401c041d507600f11031003818542d1064840380b000070150424107115003150190110100400d150074050181c008120940c0305240168a0705d40c003000744142e943c0010b041c2a60130101e0a100c000750304c410004d120009089859617080880251244c1c000c0c41180019110301001c00c13800e0400e00c2c50b950158225841d030710f1505511029112140d80540745442c144000c10031000f2150316441d000b40011849103040c160b87c0d0b4100c0c41084984c030005015a130020020010500014000004440780e500d804010007000348600d00d01100a40444200244110982d80384601c6200341500b0200296200340c81d4420f055489000440350019 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 56718429 1250 56717179 56717201
    0xb0108060112080f070c030b09010606181703040e0712110a0f03200f12090c0a05130207150605010314160309030905040c0807090b0403080a0f110d0f0f03 68
    0x6402c0040000140c0d518014a05a8000c0c840b490510b031507030b103030f2080102203540706643d1382e01e03020100107180c0407e101e0000603003079909024a04024061038402e0401482c00380d80d001100d061801e03100c1550400c1a10001c001500a038900b41c60318980040819010702d004501032410b1460215410760400251000759006941d00843e0580841089001d01041810790b00d050b080c0010203274000412100030522440f11401569413100d169901444480e0000e080050a030820541c0d1010780d6100c9500c079003100c0044844120a25828031018028890b0305001020300301214907d5000c16408d400401c03c031907098800308130101030804503614204040318040240324502105c524582e00950000e01c0301c90203464014003140d200c20100341140c07202c480b03400c0414080801c0022096006039420b0103082404041070410b031440c1d90720300b241d0003010520001d00914580842d2103512807020070241261141c100c5002d400c04c0403003d44101d24503500c3c040011b4440c461026107500074080d012140c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 56719679 1250 56718429 56718449
    0x20a0618031421060f0301090605060f0103050c041a0d0207050c010f020102070f0b0702010209030a05010203010e0709060f20030d061a130302040e01110c07140904080a0807021c05070b01080601 85
    0x6031120040403004200420096000600c17124008103a2024441c4440d00380c071078403001509042600800c03a0210901902e90f04150034541001229110802510110350340c0040450300300b440e4100800450140a5549a40070b1000c2464028048001064082c0c04400e803612701201503540000c81c240d10a0702c03000380c00c0c0c030307400e404440010765409a540e41c4140d140c4001420482c200c0000303814082c02480a0f16181e40110040c011001241c07222908041da900704244007501d0050302800404050100d84240a90102c1c4071030a18650f041680302800340c1404d6075503580101c01100008c04c458000c10441101681d028207205602d802225400120310060845031490340c1c1c01c04c03029040c05a81d0f10069502d03910a01c140000740c80c0036125141d02e0102070121641498030040c00c000c044003d40c1d104400360000c0c000070450742c9040751260840e0b490160615920803034140d01d00403070b10016000703491080300c1210301e1580c01406805074910503821485039136a40e915465a5620a00030a1046 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 56720929 1250 56719679 56719717
    0xe04020f0604080106030f1112100203090a0c0303080a110a140d140c03160201090c03110d021002070906170303220c09050910060303020616020a06180314 68
    0x1500d4603412400103400001c0455203456281e020703c1d820343c1e2165108450b600d82c0340107058200b00c201d0103040130400d030940c2c0d5020128862090543c1e200a01307803952055907400000300b55801d1052050154007508409400020750b0789113070040c07030b03c3c80841c0c11800c018580309450908401c034900310303490022190b842501d076440111420800c2d0380a40d02d09250305035980c0c81101d0388080003441610852810444a0300c0740341c4001070b02a001d0700c100075002164544008440000c44100044003a29000280d40d0501e680700004100800f14001002e90301664121106040560010721001520401c010900800703945034940d074100c0340d00c980703c1c802c3d40e0014400504458074034043c007041c810100c0c0c00e0b44001c49094072611843d03441500710010040d1a0320030080c158804109806070503000c914108466491500c00940f40c0401500749842147c0f80d04503800303820700c00c1044603001504120200501f0969600003001c03c05040411404141c40f01100402c480d051000ea030a0004208034120031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 56722179 1250 56720929 56720933
    0xb06070803450c0306070f0215070801170309030a0b07020706080606030c28030605011d030a03030e12160201080c040f0e0403050c0a0b0f01050a0b0403020f1f08010501030507090e04 80
    0x5007001c0d1140d416141c3c03060300c02c000180e0350100611070242110381c40f022016101070100904020039007058001c00101c00302440221540490703258111248010300034204100c2a0416003148107418816038103100f100c05c44d00601442c1b2040c2d6003c2d044039000c44540a98580c420b45030100107c0b01d842e032141c002d100259408001100802e080c404075200100c1c08503880790b500021019200c40440000c0e5141c000f8001035070007500200c0f81d02d001d102e90303100c07074a0004002540e030b00341244000d0030152107016820b10050104003258a509001400700e4641640882041380c00c42c00c8001680040e2200380400d44207400b400071102610803501010501504020004e8018980600200c080202c00c1026086060050082581c1e082c0300c0c52042c600c605090000040b0107006810542c0b080c2800b050412001d960201100c003201d070706070b900248540b0740000150854513400d400660807400341e6210750741550301601180c113880090302e0410664540d10b00032036030340303c0781d00030306404160003030200700 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 56723429 1250 56722179 56722291
    0x1d0604030305061f0503040b0a1b050a020606040b1f0e060d09020406090b01090909030e120f0d031a0d020f060f041d0114060706060b0c070906080307030c0b0a0b06070803 75
    0xc0c0c010385027000800ca00380d40c0000c01d038503551702591120000b980401d400007081d506008007900b103081144c1c1030150300d1080001545901c013500304c5050014514202c4011076000e80141d4881e038500500305501c40380110490006400d413140101d100754501030303012a003500948500c00503080182e4800c8601410b00489400500300400c0075810301c9501d440b180c500b561140c9220604410140103441d02d520108075041c030b413480031203204041c107007004c000c81140f61000284c10300242045507000090038441c004a8801c107055022950000701c006808506444803e00900442d04501c1a044032128010b02e880f81500c1d0a001d000521000c60640a21500c4c10001a12465001c0d181c00582d19035603400b44003c1c1d50016014400382d42195400704003003130080c07090b1402000424003841c030300403586e503000740f034036100f03907001008070000d80701060035103d0603171000c000b005010345031598030309042c1004520340c0c20840e100780101f038030702d005840c41446028144d07a252855041c840724141c140e4080407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 56724679 1250 56723429 56723431
    0x9080106050a0f0e0415090f03020c0307080607030c050c070303020102070203150903030609060415090c090f032102030d05010b04210209010603020f090a0b090a0f0b0406031d0604030305061f0503040b 88
    0x601c2c420030012040c1d1b8aa4464030501041a2007a42d401c0c00b511400e00d0040c1c10826103212183c4650000c00040000d914081540340d409000e9150000cbc4581d80e20718245e030b060059030481406032082ca240481055015801488800c2c0210100e0f0040c000c00628150507440031583c91549400c1071004c684541440800c0c0341d0030600082012403814130440d0040705402e411341c045113429407201c42e07003090141c10206500c082c00400c2e40802e140c0341141c40d6061030592140e542c0c011030182d40d040c407104034424002e564010040401c180700e031b541c2d00e035a40c00282d007260041d00381020800c003590805001407404100050344c00340c012801380c2c0c6081e03c00d0700250410200002001c01c01c0180f4480b9aa800e0784c41006403040942407601ca170003003424440600c00c3c0b070300010700ca080f000381c00307014140381e000640d4103d0705c0c14138011030030f0f0b6100c0c0804061000c07960090400ca1041c08140410160150003180c4241006d0711006046411310010074150b0030f441e4426800301d8400c00114002c02c00d00507402e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 56725929 1250 56724679 56724683
    0x20a020112020906070c15020c0904021915050408011a0108040b04020103180b04170a082a19110303010f09020315150c010501080c0f1e06040609080106050a0f0e04 72
    0x41c10f000c42440800c11a40c0404001c90303045042c000f0a0200c4a1100301202c204d0404d88010320000359620042004444040d00103440346443c0d800207548441112403003806091040c5101c10210416000070713100f03410a000d55070300c1d54200715038081c5800302141d41001100050351a0351141d16507072125124a000604240e04068880c4000042120000700d490036062091203200110305c3c043c1400c0b040c02c00c8560100041c41c004003c0c03400304541c8980a15001511400c01010020780003803404101c80f5611464050240c0106e5445c141195005c0c03082034081007502d425004170010040a03442c2c2c402401003d070128100481807010000c00d81c00785502411580112084145a5001988150321644010841c03d000584d80c103841e1003c0c001c85006015410080804e0084040007648029800884502500100320b044030f100840084010940c4800f0b40416565503e03204010000071a50058181960030080c00280070305004ca01d0707100b214070401e80b070440c0c1410500080c0e4603000c00f8100b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 56727179 1250 56725929 56725931
    0x50711150f0d060909051e01151706070c170702010e0a080d17040201050307030e030d140601140414011b1a04060b0906030d03020a09032102011103010303020a020112 73
    0x1841880c900ea0500802851880d00c0c0c1103a120320b002009002510390a8000188050400c41ca8a00103500080c80f00200c454207144800762401800905004003c0301010302000705002200180084900c0c81c0c10386280058429a480c1d44e8664505550100c494100201038100e000300804070b030f0081c040a0910a80b051501c00f10544100f070010b8013082280e000300015400000c41c003d205a0000040c2945400880d084059480c06400203441d902005040e181810380714a0100c00c0b02d1001e104403030240c0c4c2104010450707074010500380c0091081c11a2218081404080840e11410080050b541105d840c2d24603940c208210600442d40d081e450441070101e1311128000500140d0034022002007080c1e42ca0540906140904101c001d9403566100fa034010700442040c018581c40104450700c440041c1c0c07c01583da0903140c04115810091944064016190480014445204907a145001d03819a6000340600800e4100c40242d500c000e110050141c0d01030001540154000e07500360915003035410b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 56728429 1250 56727179 56727199
    0x1020c0402070809092206090206040801020c07080d03150b0a02030c07140316080303130203070906140f040b01090303080a06090203090a0b1b090405040f05010c0210060e07050711 79
    0x201150580c0c000360000c8440000201c1d03032500500704800e15591003400901006103000340d0980c1000001c40d03107040500519120f079024400d41d290442181c00030b1410800855072680d20706070150b250400e40c0030707100450080c1a00140720522900410790103070a60860070700b81c5841d10000078150fa00c42140401540070901841810400c01e0000c0380c01000d071812685106ca01c42c80405082c1051031420a64810540d60144089240001a40e5020718070140c1c0741c00c2d80e81c01e400080c0c5010744551181060605051001c221103181e0100c4200388001641d41d5030892000f6410002070340d408815081c0001d90440d070404c086441100da803a0810810740c80000e0250301e8400c82001d0360f000f154050210340c0540a1101000f00111060340c0c40300c000b4290904115100040001520070842c078140304a48907000308040c030541c2c00c054500076500500800a000150700044d454000410003038044902d071840020b00a0b2003500303070380d00c90020756a074145000d04603500c5107542c080741071402c4c1c4c001d40241 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 56729679 1250 56728429 56728453
    0x402070f120c03020f010c0801180f0203070504060e0f030a03050304060912110f010c0203030a0207030516060509060a09050d081510110c0411070602030405030f07111804110f0102 79
    0x6160710411894030740d918400c194407800c0c06490800300c400c03d6032040c0e241810100ca8154051001415201c001250186004250403e840503021302001850070910010501ca02550010014012141980c850040061a0000304083d00d079000e1711081e01a000320f44080c0001c0d1140001b1079000d4840c4100091400749600e8029001ca6960381d4440420540040c058044e00304101b17a10310440280c0085c410366186050003501c0380009003400f01001c0d0007240003804c1500501c151454004032041c400c0b500f6065040040c0640b4041d19051010701661012800c4418039001d81441035400c0002480c10030781190f4119820b800060225904036080e041c0c03001540d560001a000e003d6042d59207008183c1c02d001c2d014100500840e0301442640b401a011500840e6182618200c580105005840395039038240325086126265140001a00005640040240c15032000e000a1000e40d41c101d641c4002c1c11119007000c0068a01800540005c40c00b148180352250381c00e540508184180c40f1910302e05 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 56730929 1250 56729679 56729693
    0x21071a041701020706050c031e090a05030f13080a0b07081302061606060f0e04231e07050409030509040e0f030c07030203010c020304030f0602090103090c08010507030c0e06090402070f 81
    0x103600701e54150350001502014404507016054000d805450000c2c42e604003020310050689001c60140360030a8000c0020319100300603c0090030094002060f203039a003260020814641d846041040880d2f4007024000c18000400990301c036109901085035012610380e100142e0703410341d0061404000484200500c001038403182d01500c03001400315180f00f08210343d464100e040e40e1103a041140032054543c020001c0d00340201c1300c903410640018aa181e0701c1202400d2036800000588000c45a200c4e50118682491519910302042100754083e2006c054032403080009442c10760002a000403018000815113280c0341d40079000c1c8000200807543c40c50700c00313540581140c201a100140c1030304859010000e5040a0180f5140e209403440554909802c40c0d468980c0500700c4040035042c69408901d0380301c0c40e4040c0d4044807415410400c181141552110003c0c060321044804500003401c01c034803040b60710700807503001c0407004005219508040124007404000d4004903030075103451052800030801710304a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 56732179 1250 56730929 56730959
    0x60609120102070c081f020d0b040905030d060803180f01031e09020f090408030f07110a06061502120901030209060904020301150f170a0b0102030d050106020c21071a04 74
    0x2480300250326001e079802c00e010803103250740c046180e43c0c000303483c559824021003500403035074201c41100584600309040710900a00881d0200c3e50481d01d0200604140701c4000080c000355182030800b403020903110050240c50b2300036481c07003521030345005201601c145803282941c00701d0300041c500001c182050500c1c2a44400900b446081c3c5540e59030015000d43c14004158440c0b04000d95411159040940e240049440010b2400b21521034840119030b0880c40b50a80000f04852441240d80b24521410a2130042065105020194610a003070520550012418041c04a0304800752410481d81100540196004885580e07204904214030604c0c1c0e40c1c1d42c40a1400b8084408030700850200c6544054071400c44090104280040350000010800032001400e038840030751403000c2580700350100180d24601610303602900c0103041030004030340c5a40c00580b1409029081b280d40700d10340c40000600b00d20080503801e076040c0341c200c031400380079861848481010b80145403030f880f403405a50350701e03001410b03513 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 56733429 1250 56732179 56732209
    0x102010f11030105040c080103050a020f0a2d0501020a051f0f090c08150f01090207080405030109060f0b010f080103082a010b01090b090d122f0d080c0a0305060609 72
    0x7030003200602250800f8414a024000d10b414001a6135045442d80c039540d80144a000740b05401c64680703c40300e512000c85250003006060500a10f007806008407101c52500c44001855104c202d40c000110796100181d4038200303c0c2c02c100545003180030391005414154486d4903a6130502d07140c201000c5a414103205060159008403c80e0b241c0505080d4000d041c001012136900c0e0801811080c020f00300914400c1504685a10f9070050303035101d8a1600040500403540110b5055280c001e80f40140141074000c0d101c00d1112100800c81e54542c10f0065a0144460807407400280161300180000b4008500500c1c0c1d0070000740b401c084409492421585030317895110700036000c0c0d45924420a0558002c241c3c030300507240324100c030b1f410140c003680400c000001d144405429590b004020380a20741c020040c100c8440706d0703026080a00341c0c0c802012031a111040541400724400c400240c5c010358883c0c4841c3d8040c00310800d086190141c01c000c00c030041c042c0507240e00e501000402180c0d41c19034a1240d1582da400d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 56734679 1250 56733429 56733461
    0xf02090c0c07140a080f03030a090302010906020706020706110f09010c020a0b0a170a0605010509190306052701020a0206010302101b12271203050904020408030304210e010e0102010f 80
    0x602c8040c04e0081c01410b0768040340b403e50081c000450440c80c04000d49030700c0b1103400000588040b0758101240501960a000381c041d902c0040c4501c18007000c8c0e0014440b150043c00c2c1442080314204038400540b00c1c200d81c0d12610107040c00381d4a141d602c54030301c1200541c001080403005a8499050340c4465218029010204030000c04c00b5204104801120f503008401d00b0301002580d240c0000070b4610f00c901c4110034428600b068070036600a10700e000c0d8601860b004541089586000d26080c140b50040c0b0180014042ca2a0001251420140222030515505601920280c0d00e99402c1c843c1c00d00c092085501072005424407103c41c20b000c1320003011100e0058240a841084141b0043e00e02c08031038101d02420a6028044211640c00d03010747d03402c8031101e212040a180c098141190a8021140f40341e0b07200d80000f6000503040b4000000d580150302071029040b45a0f1481ca80b000d840c411080140c02154480812512941c06121003080035007040c0000301e9400b2070551148112405002d0802c846 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 56735929 1250 56734679 56734709
    0x9140402010f0201060305030405090415090809041512062a030c0905030c150306030304080a06020901020705060705060601031d0109060507080703020a140304081603020105040605060406030f02090c0c07 89
    0x5503034001c0c1e4040000d00980005c000040c2981c403007603128441e9005071400750880030302190800420381001c0340d2099080008004040051030202400d600a61460f031055080940c405c0b03842c18510381a030200c1c0e102c0c0482003640c0c030031903407001e001d400d81c800002e900380264040345140c480c501001c81c2071a0000e640001e0303005c0c420540074091410725007102d402a44491000c0c10f40d52105192080c5401c1005001500c0c2e654034400246075100300e4110030070741d008008000e800c0085a4000d000020b100360291102c603501c034002c5c000340e80100e04000c0d00540c80003020400c1e55000f50b000c0901101d00c55000b65010502c40000b9003542c0400300b084030140d030344400304041658080f03003094100d040b03407034250b02d8014540350060a06800303803042103c0c003000101050400103410100c9a2081034802007983ca08400c1c01c004c0d0027450100c0307050307a46600703100001d01285010f12980043e41e034027400700360908442d070f0240080c00900a0101300c04020030001800c80141c1007080340c1c01810203280c51488 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 56737179 1250 56735929 56735933
    0x301080105070306050108040f020a050303040801020d06090b01091202030709060e0a050f06010f0311040e0403320a0c020103060906080c13050f010b0304080f0301120201030e0a05120d06091404 85
    0x8444008100b042014a8150240010782c1c1c071891032608160012503c00700c80266000103091105641d11281d1b040c070001800007046141034016003e04070602d0410007095035036105880039500e440310458002254584140a2200d5150f5600c003140e0000e41140e69294440c01280c0c100d40d01c5402458084211404100b02036078180211380d40140400100b81250412200180110b1420707844d1400b407585400700203500c1c50654050342c1c001d092282c2041c1c01400d0074240a0403d02a3b41c04828000c010b4a11010040d05000c813996400c2c145801c5061400e11018070895a5009000080341010380340d200001d0f040710725014403070242580c04050010000d1050410042c1481c40680c110000d0400003000b03080103807070a41904480c8032010090396075840d0311b0105e5103441007000000e0882400b00000c030f214410314020340d410b140300f030300c0400070496620601030340c5030064040240203501c0041c2c000d094502010160002000c0714201150654450042100381c8600c01c5241c160715144030100703c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 56738429 1250 56737179 56737181
    0xc09050604060b040521060703090506100503210702130e0d08010803030402120f010903030c08010806090601140102070302030601030b06010e06040605070209060d02030f0d021204080309102303010801 88
    0x3410540868007040800c1c9840a40c20701ea018510405105403503a40c2c6070340c2c00700038440c100b41110b90001c05807130139450641c1e8003070010500f500d804ea0340da115200c002041125616039003004c6c3d940c0100180905075190341e0301c1103c1185002a4080c1d01c409201400060316084c04003565211410004201028070b08034171458078060100c56010840103034010800454013000700d0341c11030b03010b13140000d001c080c1420403441d028480300b04c1910740d0310b03042d1002c0074160b05911410342d203e0384c0e6544034410390b40c0d00901c5684220507a101030081d006100104640b0304440c010f45401ca2060050740c40c459981c0c3c000904000090348182d40300b840035000c000a40d81e00115410a010382190380c1410715080c00d0000f00f107030240b000000e001d04c3e103038004100c1c1d81e55070800e500c4505600400721402c1c1d8009650860b21010020441c0c1e0245c802c56210b040c2c00c001c40026102501c901000850402c502d000070482c0070341c0d030703c50544284407031000c20f03550300c036014600851019140d43d8a031307a1f294944400a8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 56739679 1250 56738429 56738431
    0x30c080a02070c0b030402010207031a0907060e060a030b0a1806050906010c0c12020f040608100f0614060d090515070215040b0703020c16120203160302010819020909040c0905 77
    0x186200784108503000000c0c510712000003c0c2c41d81801002c0d1aa95180b005034504100341d04082c1c0442000d0400700120031010340c59512540c1044180e40d00f203641d0b40c1054a1208015540680c003400c188030320a40d0600ca540a03051461009260440e1a5540d6800f00301c581c0c5511002120283c4034101032107a030401248050f0003000a10700f541e0000d80c030786c075100080032182c000e0b106841829402d08055596100c01041c3c280c0e801401007060503a1485541e0303071801c0900d260324009041204070b440b60b00107842100121900781d00f10490b107041003020014180d100312a0320703c0181c5e4070f01d03200c00810410014016802c3d4003200000c4d01e414080d20181c5807151207035005800c111600d00f04000116000b1201da003061b001d040c0940c541d10300058440c2401301124840112a0b0f00c1480010b0040030240f900d4081402941031302c82840c441007540a600c081800f02a020a904a020034141c02000190101c00184560014240049a40080e5001906a03025660351304c50361f030140400f83c1030344192 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 56740929 1250 56739679 56739691
    0x9040b0619081306020f07120e240c010504110a091a0f0105120a150e060d0b0c07050114040303060602160308090307030501021605160b0f0d1b030c08 66
    0x15424407050800341d01e0440c89110303400d4100460900850f12000400441e0482154060015034903840c800f8030005840c3c01c82c10080d00c4044c2440500000380d40140115903101802901803410b00481d1101c21006024068070050700c5c01040001341c5030320101f0310409001ea0305c110803131014008164100300c410704c0190080700e41c030307854498001c00600420520b800004003d0380c0440d4010701d070000503101400303948211740c4400c1405042011130b00c2c46500502c0c0e84071200900301074081d01c4504141e83e903401111803035040203c4280000204d03c112401c150300c04803c40140c4e113040e03150303540d031400c1d03076003080386030301114941e1040c4001c042d003502a00c4041d04551008000b18040c0382c08280c5000358a10000d0299000010703400d01035103043c8000340c00f07507802c00e00a43d41c50890540d629817071b030500340c0151001e005100c1007031046510306100c0c0e0304403a40010b4090a120260144850560195120840d6240c4d1081c03103c0040c11803d1100c10000980d4030700058141c1104d41c06480300c28001c202e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 56742179 1250 56740929 56740939
    0x40501080c040b01081003240c02150a02070503040b030604020c030703260f150604080d050903100c0206010e060d02091f0e0c040b07060e0f0a0311060c030f25030209040b 75
    0x40181c1254141c6803081140d17001240e230045085825411070030040d08169291840b42000c401a101c282c0010b201050034601c0030051480e640c2c2d000c1010100d01035218014415002084208a0b1045a07400740d80c02003001040186043c40e080041c603c0d541c45100101d01052050740410035264000052900c2180d40c9407418071709203000e008600141030028092030550740300c03250580440e182c0405490103080c000741107032401c0d0f51a00c0c6c06040c9801440004d4440e10803003148801c11080e03070041c009541d0154004010507420003540d0003040307200401c565005083d552002000d60795a5510303900a003420540c0010700c0d0480320b01c4d14034101481c1c010b00300751403030329043c40303e0781c0c1c0550304640484403c03901140d210b0010385440c01c041c04003408072085600c40c61030103013440c2c070f404100030380114426100d810110005d90f20150700c03081c0482e50a40c00301c2d028000104c0b000c50310f010b010782c84061541d004880200c09107007006800280108540040c1e0b010a9002c2141024414039102e09800c40d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 56743429 1250 56742179 56742181
    0xb01090203130807050f03030a0b0f12031b010e010603080406030f051510020c0a060e09010807051f0201090b0117010e120a03091b060f0f050c0a030f020a02040501080c040b0108 78
    0x410555070030180280107202400008051040c4002030002c00d11041c50301007a80da9a0a10310000f6026000901925104544a0514a85500d401c0401d3313110000c00c0700c003440c10540b6480c00003083d6030f4084040d1032195210022105d100f0420b00c42c80340603502c01d0b681d031078603981400070040031594100c600e01c8941c0e24010610001440440c640c56100508a40d4440352032080d683c12030a1000390340106811240ca080040b4072241c01c11203e000e205820b80702c984542e80e0300e040c01650744070315203d01d6801c20059140506080010519880300301c10394000803803400d00d1035541400a42c0c0036070040d92040e00618009651783c000b070042c0c6010282240c014501503800d11810341880c421700c0c01d0041810744d0790303102e1010000302c01401c10391407440301d106030500c90b901c007805011100109850700020f800c40e600c0c02904e5000b03c055610340c0d00710000400c00700c12595004d0f615601a00144405c1d84584105000180c1e15401640d02030302c04880600781ea55407100500c41030301c0102d10310328180110720b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 56744679 1250 56743429 56743441
    0x506040209031209010e030105040b040317040b0105010c03111501030c080f1002090d1403130905090a0303110f041806050307031509030e13020903070b160605061201180b01090203 79
    0x2500c074040c501c0d03d02010303680d9400d9500596101951010141d015402c200c00c11050051445000d40b02c0d43c02070300c580e8040d543c03c01003101e503ca01280c00030020203400d00140519480341500c2c3c80024443c0c02d002c03004030b400000180c90001030040048140c4a1301c001402081000b40c0c1d400020108440203100b450846c03075100d40c41c1c528150880700f000307901160081d09650381d10b156030702c110307000403902c0420802e400c9280d840f84d00c0f604c41100006001400095a1440c6104140c45003010340007401030520142c0e81280030b4102204004074001c23045c40700e10780f4140464020320003010025040c4584119021030b22050300c0f4150b000902c69082600200041040260141c5406400030b100040624451a00b82c0f603a0f0b45680360030303400100d1618503400b0150030394000d00c2c2080c000c608a80b019031303652001d4242d40c810745030341c81c1d00290301c00010400610503811403074001c400207007148548070804223164215030300c620040d0a147c80d10f440c401e0a002c0c40388100c3d400361802031720640c550f140803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 56745929 1250 56744679 56744683
    0x140c0d1107140f0316080a032a06020304050715120614091909080f03060f09010803090118080322090204030c180207020a080f0f0102090906100918050a050604020903 73
    0x2107002d28007030080e80f14100d5042c4e60038000c218a070071000883e01503c41d140e080841c0c0c0e43c110320b40200d010615803d15030800b050f031f0140d08000c203402003240f40b03280f5410b627a603036020303400140040b01c0e00c1c402d5090216001030f03105108c0910b10f0844d56044812070390300d0b40c40304c04e440c003a901c050092003e8a070300008075118a040198846102400908119000707549480203060540e005801c0e10340200782c406459161000540c000d0074100c0f40d40444a00f55810080b1900c020f1284011580c4104102199540181750703400340d0106070400e580c0069078800701c0c41d00390351014150000080070f01d41940185070008164001424566800310305080c1035940712070b0740c20001e008070040701d030f001d8035003c062884c07070b4049940403940640910b039220358031424507a9411001d016041e050040c03100c0425803010520a5821b035840040140f44c094850800f80110001614110000c212221502042c2040048641075011051040018980c07620013003100484802034a014400ca0040110707a00541c0c1c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 56747179 1250 56745929 56745959
    0x4051008070507060c020c27180703140604031b0807030818011a01030606030b0d1403040e0c0c1c080f071e03050103150203100b0a140c0d1107 63
    0x1880c149800551181201995035000b5a07a00a00050030448007601c030b1503000c43d116546640036601101c41101c1e0110b003204010142d400c01410b0700b01000007885880720340e8061200241390f03000b502c2a003502d03910760800c11216450003207140d078003900c14001099403003540da540054449210543e10b005035910510a072203101000340402400b4004214602c0d0301010f0300c5500070019000f08805200c00012608490135002a240424588800011868024040c949440e07a0040c00049000f07807a40e94040002d07110004a80984801c0c0300c04507920180c0002030303001e4020110b500303031505900d02c0b0803841c060091900030800c07604ad4203060315480d0051001c07a0404010f103c0010f0540e00c003d412103103501480c040c00400c861240c00134042c15050b40c0f1150680e8051020f01000691032a4050b0591005607100c010b2104d03410401c101481030000501200000c1e8a400d040050031240c41c1c1c54150048221f50311103400c014000004150805c402100035100305002e0040301d45400c0d84040a900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 56748429 1250 56747179 56747209
    0xd1406120708030403121b0f0501050a0c021207080d05070918020f03130303150f0303020105090a080f1c1b0f020d080a0e0703020303032503060302030307030c06020705060403020c04110405 83
    0x2c095031364401c1c41c040e01d20010747d06203042d0844040140f50521300c582014210007590203520b0000450340c504507600814950000640051010340030440010401c2ea2080a05882c001018041c0303c08401c914050240030703400341da072561040d80c10944403a4080025900d0aa1501c0c41080141001041002500d030f20a100145e094072202150500750064014a0410180d8015a45001c100c61480b6481c3d00c0a0b2170003540208491303036451700d0007551a00c2d80c8001a00752107043c0891140d00561600070030602035011215202110f4040c0c071082039514000d00c01c6040c9101c2c245850002382e012221950000ca1803004201c0c1540c4150b02410080000e400240031b0750326405601405401080610004c40e4050126541c0c0e103000c11030081100000f00740458800320104259401912074054041943e800501841c030f841b9240d503066078134414800d0116801038080c0406000b2131414030100744198000e402078000c240d030f030804000494112180011400e8002d01050000ba21041d4003e84844 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 56749679 1250 56748429 56748443
    0x6050f1e01030b0c0c0c040921080108060c0318060c090103140601080609060a030f1b0b0f03010b0306040603061b020d170604020901021903030b03060601050403050d030c050d1406120708030403 85
    0x600080a06c0c00c0108a0b818290801e0508201c0e20410100006c581003400b03e1031200d00910f00782090441e2450020700c203039a141e60210b0041111062804011034100804540241c20350015940e4181407801c01c60b11180c0106000c42c0d80541d9507054000c2515500340100c0100007850042c0c0040d1203200007416150155040c28009203240d100c080b50800916005814a0340d11420751602c081d0303c2c2d280d2030118641894605d000a0300e81c082070151501614248012811a0300b0400201e030315420040c4155030098850200001041291144440c0d150301a802041c159240520182c6007080f600280e200300718002c0c1c084900303101d0405049400c00412900941d65841d0380e00100d00d0300625150b038a410710a68403c070800c058065200c02030004003601070703609943d03030140103440f0f43c081d52001401d1074020040000280344250301c00c2c035040e40c00341041810240b41d05048800c49500d000c04805090030f4400b44001403500300b03018000e00b05c510380241015030800c220144c89000e6880000c03c0300b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 56750929 1250 56749679 56749687
    0xb01081515030d1d0303070b0405070e1e060a050907020f06010509070c0821090607111c200729090627040203040b0610020a021c05030706050f1e01030b0c 68
    0x40d02010b2244c4084c10801070440e41c83d01004d003003010f03041c0c138103131000c40300d604c20040001041402035410b00d00c1000d0702007078544c001c50300d103031805d0b1100780007028540c0c068881c000c0800c6544e119070740f541c0140c0969004160250660b141c1901c3c0c141e040e0010780c0705140d200108110b80d90301040ca07904096200d11101d4a495580341c07851440c102e41c20304036918401e840c00300090580001150340c826503c5603602601024a8010651076401000c01001d06403210303207040007881d00613a102e45180c00394582089182e10300415240c00e14007203402c480080108201c11622001d00c0101c0ca6207070710080328049140c070a412000844510450013401c0d04442c0c007010103c0c27841c0c450345110b00010005001135550f864a03280c8100c100408407075042c400c0103042c01b12003603540300162807200b807940903150581d04422000501d035034050310b03c0115071922040000c00000f03491030182501922a41d900c0e03880500700f01d0044406401c0345040003071503008400c0100003003002d0b240c4950304441140f21155a0f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 56752179 1250 56750929 56750957
    0xb060904020d0f020408011b03020f0403120c0b0c03090c01260705130602060402010306090b2211180a080d0806040203040c0509130204110403030504090e01090b01081515030d 77
    0x10306500c2c24a043c01d284045400114048113401c0410041c440b41030440d2941c6892406900b00e005005808800b4002400103000080b0401e500804036222410030b00955170340c0c3d40e0364041600d82207651342c003036240100c103110701807a00300114110400d003400c1a88444e501040d00898501c10113405d0300d8040031080103d59a140035400320307404968413400a01c410ba0302e07a18081d41d06c1005882c106c0c0000d2034102c000079040340c81c1c80b0f04504110b00602100c01c280f140199591101180720601a52a58504400007400d011000803c0103514400c0d03a040c11444d22020481c0e030507851340c403020b02038104005480820354030140d03043e800882290700607103035111402d244a103588180c0115030810715000034412a220034031441c00b20706200325030030701491540c1940c5000d240190301c0000c012820030320091018040c02c3d00f020701070007004000010480c42e943c4460b001c145007a0700081e66030300502c01c4080c80c6241840c903d6400001c030452096001d000c00082036440607045814000c01c028036400c1e1507 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 56753429 1250 56752179 56752181
    0xd05181c0212060f06040216020904020411070b06040c080f040b07020a0f03031d0c030703080d0b060a05030f06060702100516060e160504050f04020111070f060305040b0a0b060904020d 81
    0x4000d5402410300080105018011039840784140d071181114040352001445a24250084801c000e482004501c1c180701141d00b4001c203a01c0143c0100c3c0d0140c0c036080034030410131814001e09101c40c001c9451040782c3c20b1038410702044410a9880d68100a114410485170b00d4884c070500741c0080d0301c84a1044d00d65602001203081c10390361034004000d0b0425a40030340615901d50044002c000314124410030b4002c61900b0103035262004c110b0980c0642000f0f00400100701107401416420225141c046401002c2000180c195803003249031b507000c80c0020042c400401300303452160380d101d0001e80c0c50501e0060240c002540c2510800c50240400000040c00c00b0300c035000020796844182d00110a102c041c80400d10540c580301a212240b80600c0d66100c002024501800b5040c01100c0300c1d1071a1040e03440c0c40e001100e8400c0b82817000d48151141c00b0300040c4100800d40184028082943d002855007014036000c0ea020501802507004d85040414030b0300c40d6601e00007140e1250104450050b0f0f11050482184 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 56754679 1250 56753429 56753479
    0x40b070807050304150c030f0c030f1209080a030e0d031404020609010e131b02030316051e04080706080603030324010c17030109050c03090c040207020f0904140d0518 73
    0xd44100d603d95070f500b11030360304138a0031801b452003616007a42d41c809508080700c00100751200540080c4100440c8800913004500140e01100d0810002c20100860f0b200e2104d154000303a501ea0019546100b800d0400a00340170111641000d840c00f8800843d00301100584800c000d4406807080d5000508120168010a008040c1030400fa000040e0142841d00c46030080c08a00c0340d0f8010040c3d101504c400e00361005c811a0b06c145e8000c0c101d000a040c5441c021511074120511845003c4130021411074038003a84000381008050000051484074100800184105c10141c80c4038000e910134414086000d00d082e8101d40207a0100807601c02c0f111501c0012038441800082c00b41058810140844101c588900198143e03a5003c00134005511211481140303440111040c95254020300144511490990001e001060004004410303000c0207200252400340c09032400c403080c1201c2000c2034032040081c0039801c00c44e101800d01605003460461030707850508104040314820754000c54500501a43c171900c507 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 56755929 1250 56754679 56754689
    0x3020307020411160f02030607181202010203090306190f09020105090d02130f020c0c0a0e15040f06090902010f02060601020705121203040f030801050d0807081813020d050903040b070807050304 85
    0x5107100320441c20291060003c4110a0b806406640b00044d4881d002d080c40f00ac0d1a280c01669400040c5002d0070414404201c2d10120304500040100441d199400c2084038014400d0103d5092614042640d200440311031403080742d21030707062031840005030780c001040d14100da20035a040c0b80302c5101c0d84005540c00f10b8024000341e06e20715103154030004880fa03034050700e408184282180d8128014404020301030317900d0701c24110b4042c03081002a81081c0c51400751103080c1b10141c0301207040c603d50204003041c2c0d0000d41000f00c030303075640c0c00e001402d6691124100c8010304c90390000d4800c900b41342c40004c3d21044c0d81d02a950041001d0b00040480030010003180a01044030f0303000341c0d02c6c2e007058540402c80002200b01507002500310400820365161203040303845841d90200d0440d2a00e08a5565a503203900501a4541040c00c3c212904030207868401842103d01035805005036181c04184054044800c09041c940d01c5a00c18402805407c0b80b09007103036000ba03004841c058840c0000e14095107181f080d5001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 56757179 1250 56755929 56755957
    0x40618080708030a02010b0904050a02150c010c03050f06040c140a020708030a080609010b0309060109051503010c020f010f0203010f1403030f040308090909150c250807051903020307020411 83
    0xc005000c00b4080082c214149582d4001c2c44202030802c1008200d82c0180e030050123540250041c00014580714080104078140f0034400e070300344101c01e0390f101c2c00c440c035411011000c02d0f05c410070008801c205a09150340190110383c00c20541607081802000402012a00c080b48100054981c2c0d51340d008001c3c1000034460360b01102d03511000f016006020110a40f1114007941c1e001c000826440001c03000c0d60320402c1d4540051a0582c41c02209901810001c1c007800c40700d0707295105145568501b0b00401030315401e181c000300b0400b0442c0e040107084400c1903003100925403041c030060000085000d001421603c4000f40712140e8403032500003034114861042802000c4100040020400400d000503040511040710420015968056020307166003e880f14015032240050015111401050203800300140d40300450310b10b032031982110024401030303541c2513840d443d010a0a5040150801241600200040c8802d0f90000b01e1355004e90340e805001c13030080c070442c6c4800b04448585100c07800d5844020480071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 56758429 1250 56757179 56757193
    0x100e0a092d0b010b180307030b150103140a05010e150a05270702010501140604032402160302010e010b030c09010603050c09091603060b1309050603010905030304080301150905010504061808 83
    0x800049070b4801308045d070baa40a108200c103010b24020600d50110f9130001080710485e507850400316501110105a07078117156460548018003643d40e00c0d820300c51100303407400044a50400300c401c010311000030000742005054440380381d03840d128103403004201e4605a41d1140d80b8008139180c513881c00c69a180100e00a4084400c00005542c1500018102c0703450120030158003d45000b800b001d071160303000151a080d00c00c04a001e01321403050a4441e1030341754140c018101002e840c801305030304094210660040c0e4460600c640301110a00ca4240143c60441c0104000c00c03614003c1007884105200d001e00b45a65903001809424826040300d0b41c90600178041c980c2442c04c040c40704070000382c03010384000080c540003000c50882d81840482d00300210b4545481000c82c5011100801703800300411058040d500c400855002402c01c0001e18000c91103150800d440c4c1d818800480781c081d0080e18024104107030480200f100f641c00500b1a000c2d0f500d20305e0400c1040480c1014148143d6055001c052180f080355 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 56759679 1250 56758429 56758439
    0x90f0402071a070905090c040509090a0624090b010e06070501060509070504091d06130f0c03030e1201020708030c030a0e0d03020307030c09050a0504020a17100e0a092d0b01 76
    0x502e0300d02c12403c5441c0c01c2c2620307458906103d06d5100403030310300c150384004100500440c83c142c1c4c1c103194003000000c11907002c0b0a150741d0780360503504813801e607002008041d5494114201c102d10b10101800310a1410044c543d00c0c5000201440220705c0680d0092100241c48414010700b90051005080c000c2c25a50340ca091242c0c0c0105207074014703c06e0741f40662030001135012003101001502c990f11501f070024446a1103000c6039941d0b00f107402104843d4070005046400000390701140c02c400a41c06a19414070b603541800a10842614031148002e00d070f40704020000c000707003442040d01c0d0000b502540c805d80b41d58030250207500820740b03082202c103180700360b0314282411941500254800d250303a581c14045580c83e003e050354150f5060040950000c01e440c0d0a00031801d00382e001d070041020038600160b400748071021018400c0b5090b01c1040d1807208418090160709142640580c010029080402c2172501d152941c02100f010355402d503400206145041d450006070038507591585030088551402540c0da5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 56760929 1250 56759679 56759723
    0xc2d0703080d1103090a020f030102040918020315070215060d0803040f020118060e040c0320070b01050603070c02210f0a06050c19030e070308070501050603070b04050303090f040207 80
    0x599180c0603070030f0030200e01015000019090b64000c3d013041e07008084a842c076601300700103050801e074410740540d8207010000c0c40501c1c50150100e12588140066070310880350040c142451182d5a07681000551700060006195000950101c01042e80401021340d440701e01c001004d012042c0c43c0540040e034003000340828440c40701040d0841602c00d8840842410070183c0c81d10149001e44980e2010414034185100142841c1d0854400e2060300d1400080003046400841d40d40c80100d05400d040345000300e582070400c040c48030000d0250108440d440e085150000d40181a050161402030049c100390345454850140b215101c2d0010166070b040c0c4210242003000d803591080054000c0e2500340c100070101310b1034508082205c1c3c45000605920140703402c000c4064000c1c0840310144070581c13190103070020120381108080e00ca0b05110703a0001c80c0364141102010325001442d00807820a4408100801055030000100c809686098408907012003aa40004d00280917203c0d0107000000071000c04280c40d030304 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 56762179 1250 56760929 56760937
    0x40302151005030a02010e04061d040314040510030c02010e071d011a0a0f23030103140601051309030905130605010909020309070905090f070e1005060c2d070308 71
    0x14038900404555101251049035941501c112601a0495a100c0016520a003442c00b503401c4050400b0070400d50f5402e011050b001103151a0110301c02540601c000c069100700c0d200103829001231041d050034102070000d40d061000c410301005055445022088090027034008100301c200890075030340742641e40c001240400f89185000c070910b00c44080049a004100280e0a000982a00c10744c0d0501d01030300c0050700c1840c25046210180940c10901140344010403c1d6081c100c09603100603034981d451850a041d00d13442e08103d822454000d1001484591200540541000361321074000c900c4a010b401c0a4502c8e00291700310a411204410070080003a419410100881c2c3e4281e80d00070605648580e60f00c120b0005807035071640d40c2c100c010300b080307520442d4000c203800c05d5200040d0303031181e800000c071140740c07150aa10010449004408100b070300014000924028103090300c1c0c2c1854000c10708101911850130303550320b00c09501c103810004c0030302d4103050000408018020865131680d03140c0c01c01c9901a08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 56763429 1250 56762179 56762203
    0x1503040f060e0115090e060a0b060f0c15060409051c030b0402030a09020a0b04030b04020d1a0708060102010515033406050304110a08061515070c0302030f0304150f050403020405040302 81
    0x50131074000140e003100ca1003003100504a10300a001c0701e0b10740c03000c03c0016080890301140e200700c06000b400c036180304c00c10007010320802d403100408440d0341c040000541c1090003444944a5490514130502040c404640c141c10a413844140c0c504404680800368000c1c1001040c207500030b4804400c02c000f540999201c039014500848010601d80c2d0703949150f05451080b0300005224210000c0880c0050030f0084541c0901c512400a40c141c20340e0306210700e109500c00700e40180010790182c040c040d084d41c0a1180540044502840e4081c0d02c2045020035603c0c4040003200c0b078000920510300c1450380d100001901101d00e43c1d905007602d50380c2c078107005100d600140c500745c5209024041120b0245007080c099801ca030003010291079913644010311950a42e4005100703a401558140071708500000c140001c20046100d000c032500360703d0843c0181480c1c80040c0c40801880c1d03104000c184100582d010b101085049a454005402103140300203c0e035500650740f00075002030a103401c0c00101600450b41c410040c2c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 56764679 1250 56763429 56763461
    0x5010204120f141612030207030f0602070204050a061406090a0e0117010c051306030207061e02070302060916030b070c080409020301050f1005030109020f070b07050901110703021503040f060e01 85
    0x20b10141a05901e904c60082110112041404100881c883c03c00000721aa4045d005807014036559071100700345a04840c0c002c985890f0b000400c2400c5140500c6100c0d00100141c03020001603007007400a50b240ca1038420480e2190101103911f00242e510070010901034030b11140451031659650001018490002c0b03d241d409500f805800342c401403003101a00c1105402e8490381141c2450044243c0003540000800c1e00c030103856090b06502c00a00c040184184080b503040181d4035030260400a00b880d0011b425440c03103411400300c441c038581350111840150790300004000d509440b1440c064691103500c04000380840c2c00840c0c000b441700003031350255040341d8041d0b84071040704030340108100c3c4207810a01e00001007241403006000000540d40030301540e0080c409120b141041c180c81d1000e1091003265000002440000c1803401075a01c00b00c80b0801841030303c002c01c6094250340c0090044040046800c20305400400042c090000c0c1c1d2004400c0039400c40300030800804040c2425018180100403d0421 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 56765929 1250 56764679 56764703
    0x406030b01120b0a050d06021905041e03080d020309030c011811030309010903030e03010603080d0c0e061c0f0f0203041407050307081908040305030d020a030617100905010204120f 79
    0x40c0a180241c540054004100d9603040d400c2c0010801c109a0345441a07410355400e20076001455001844c09d100c501c000d8840a4450f4540b0104a052642c88440400320030b04c0a030701040010360000944260b24821a005a200e0f51180e80a502d540202c810202241d8201608100c40b90342c3c110080345914000c020700080000c056090580d03a00c1401d144a0005441e454204042440792441c4194101c0007030010071682c2d543d48880c052500304206000f00550f9070701c042185150440c04115009100780c641504090750b00880070915015040350701c1c102612a4030304408403400b0345c44003480d11401c0c6c3c011500d03424541001540c005c4050075400ea144201d5201088515000900a040b20324210040818404030840003000d502c0d045012500504107000100008109001a240c0703601148001600e61040e64401802d49080b036104d040303c41c500d04912450341070b0118080e000003801d0310020a1a031900d152030360080c032465001c90095400d04a0000800c04180300c0c071200c4a02030b441980320 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 56767179 1250 56765929 56765957
    0x601090218061c0b030c0a0303021b01020a0312020a020109080409090210031503030e060903030a02030c07060e060702041806050114030114010807030221010606270506040b0f0c01020406030b01 85
    0x400d210729418500c04660201c4103009100d0f4903045a44d02020150540780e000401c00080784400c0310a41003203000d40c11054005003c4251544041d4041c0003d10042c940c03116035403006051400803081014080b6000244a0300c001c0c001d400051089074841c1d02140e4581d5241041c50060065885c104e104000c46074810302d80511901910b44584001d591103900645980c0d000d460450a2050407a0081001c0c04843c6540d5000c0c40900b81c061280d801031030351100b03400c003078074100080c80d00301d18103100301e0792241c4503d61150800c1d1410958107540005200c0302c00041d1111a06103194020039090402c00081210024884c041d00510b0b410f4001f4400d0a030680d041e400c00c2e070702c00d01030410141d122107800c20140c6402d00034208041d20300d80c0f40303d00b03500c142004203007954110b80001d0301007001042c05040d0b086419502c43c04081300f4204410401c1e080000040840c4503501c5000c00002c008aa4040d40d1000d00c1c00726403c48801400031540c0b00d96030000500500300000480340882d07811170318091 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 56768429 1250 56767179 56767189
    0xc100306050f220b01030b12060609090f030307030c0c021306050a09061d041b030506010e0c0a080a0f0b0406090906050105060a08070807030b042d0606020a060e0f0601090218 77
    0x20f40c0c0041c803041c120102c0901126000203080c2c00b640c260416440c4d07083c20010780ca8120000007402943e8001d004285000c20900c0b5900e10040c01d14000c0340c2c8400003040704007401106903504000320740b5010504542c400c400311141c820520000e50300c150495401d40c461642607102000301c501c1035500d45181a61118110101c807024490f550307402040c0c0c0313000c03040041c51510855001b032003841655081442099814002a07150300200e880c2da025900500543e5100c19801d1b601101e0040e000d440e24041d80c0006064210245c20400c07040c1d143c1060300c040141d80e0700704119502025200300a1302c0e0391921058040e000041c42a00c0c507a150a0010400741040c00441318007440c5900c401e030554a1302c00c02100d0041000f004ca03030806954111060311a074445c040e07511030a003280550620780f03000d01203000c0f0b21000c40240c1b158803898004108003258001ca001c0780794039000100010000850329070942070244007084513105000c0d0304008180d42d8040d41c05001c058a50203801b400700708030001802 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 56769679 1250 56768429 56768449
    0x140405010207030b0a11030a0b01030b15090909070909050c0f01030902060a050a030204090216110103020301060c020d050307120f030606030b01080a09060b04020a03020c240103080307020c100306050f 88
    0x5401030b00021030a0010500958015801c50f0f00c8060010316110242d002c2032468200755520800fa644542d003440d910344c0d242c000d80c3e543c10007c40700c01003454185060000e242c410200d14070b000b1140c0d400020b600300b41c18408070006285036001030005140d10314041740c8a104c0182010b01c0ba1a86600240c03040d44039105054100f640a84150300d006034600064503190445403004041640130000031680c00280e0005d040381c0c0500c4030000b07001440600d0050700c1500101c00e27180c101481440100b003c2d650003070209240c580c05440c101c64004050402a0030f500c100c01c40900704c030704910039199049a005400c4003400d00ca540c1c007085400e84881c0124190303038146049900050000010480da0319040e03100540e0140b00703420000350b0083c01e034040341c1a0b03040000218042075001c510a510180c0c180a10130480246c0171480d000000003074001c518800c0d040c00041c0080501000040d0014000c105c9507448407402080d103260b150004000034050402c1d8000c55014040580800c070711410025134176 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 56770929 1250 56769679 56769689
    0x3060b040312080c07020a06090e0a0504110d0f06060608040b010909051c0c0b040b01050a081908070804030f0b0105100f02070303050903151504050f011203080a0b030f0a031404 78
    0x2600da4142c00300e0219020710000e40240001c0f01c007040000010798030100b01800030b008075102d15494901c0e00400300c02c03842e0018030594140d0708040401000481c0d5000c4095416070441e43d100d400c0b0301d541001c554050003407038014082490100e000c91084e0300404220311a511034210299103a894a800500b901c6030408020856841004e580104c4e051812009401c84070394500801100910b403115401024156410381c1c40d040b03c1c00060110303003021403411010300012002016100c0c010380449040c1d0707040307090103481c040000c00c2280070460182d0880d401160801c000c12940d05440c103140160590a20545118421030503544150a009a01c14501c45005030083c152a92954605031000c1e440007190a90502815403854003000100c0a62801a6100781d442c03079902070044144011508050800700c0c99440035001009401c0c0d400c845010f450364585404440c0c1d48503a085100a8000c401005606016174000d65020300070004517840d071103000c1c1d81c0320110503010100002c1640704501038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 56772179 1250 56770929 56770943
    0x20d0f0506031f0902010e091005010f02010b01050d0203070c020d062711100908010f0e15060a03031202090a031b0509060d030c1704030309090b040c08060f03120d0b0103060b0403 79
    0x907142100d05903034402244d250042c107101d080d50030400f0002d016001c04075161920701e0300080b070510140d6444850b05011140a000030040012a280007030054040d524444190303030340000006c1c0311244030b21210a1103640c05000300340101d24600c0c0c0390300904401c29010403841d81400e0350511095400c01c0740c1010b207402011200c50301c03080744140011100800300b8030050003d8180c0c0068110000d03c940e0340030070341e5103400040340041890450f040004810701100030303030200e01c280b04199551003465070403aa030504115046001e0403d80340c010740035201c1030300c0d44208406800414080248080200c400c00c4011104000f500d41c0e0412040d0107050b548580c100d139000041000080c050040144028040c2010541c4c2000d040807444240c0d005410490000703040078001c1005001d54002c0140440d402c80342840300712020580100b04190052545100300b08404040f802603c003480a41074845411070415a40c07990300184002410b4222503d5000914107840024221410025102540d0707000030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 56773429 1250 56772179 56772223
    0x9110f0a051b030c0f0c0603010303081f0b03010e01031e080d09050307060c09050a0e070e040207021212091206040803070f02071e0f091a041509020d0f050603 70
    0x201d8098102201a041482c1e2801c58102491002c001030700e036815a0310020910705000000d11401c020b540940b46008582c1400180002a0401d100c144d1107248104403085107074540c690070341c500055520038401039000000205440944090160603a40910700c41c8652800e4251408001009040f01a0100200f4040e0554590280d08813800e2030740640d0840b4240201619a1400c4400d0303119880c0200d050500200f02171704000c401c0380000c08040c1c451281a01d00584090304405600c00094851580003442c98210b5684100d15500040640e0854801d09066040000b040e0f02020181d07110b4000c1140c0382c40020000501c092003180d00610142c00c0d61134641080d25400405403640c015406010004500040030060b812400720300c0707a5420320902e20307068140800360445d0301302000107030802681690140300e42c507080c03182c8502541e0010341501001ca14141e03030302c3c090700030040c01400010118920000c68000c0744c459010a50104240c0c0c82e90401c1580e035100c50b407409046450a55 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 56774679 1250 56773429 56773447
    0x21120109020a0302040503120903010c0f0e06130e0f060102010b0a0303020c2713020a0609060c02150408030c010605030d0c0b0406020309010b040203040303020d061401090e0a0b0d050709110f 84
    0x1d009041042200d040140c140f079103c400103410f003084203102101d600c4020401c03140300e2400740203018010702a81040f0403400e003140c0e00200310107142218240607590000d1400c681e0541c0f00004001030500c09a1440142405d01c05803c400e0000d80d070f44c41c010b40c02c0407507071281854244403e004a0b03500d500140400f15402c418000c0c654240060705809079502180442c104159070f0785c1c00d21605005565000210051040051420a0b904142e00308002c072078092284940100e00c03052025011a03000442000c50b4030940418030440c0c11212460001140004806105410017416103208800765032428134444c0f011140b008003c0c402401180d645800301c0e01050099000307581202c009400490b00504c0f04000c138050381d00c00e07203007100003a41c00280c260b0780d14010300c114070143c10b50515100003400841c0000b0706a0700d00c1c4c0100051015241e022074100d1000344d1000c2c40c2c00b403020301a60300407007950034030580715a443d100301011542440d040c4003455100b40308840201211250090a151440f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 56775929 1250 56774679 56774681
    0x60504090e0f0a0503030106120614010507020301090212030c100b090c0c0a02030303040c03150c0e06090409050604080408060f04050a0b0705090d0b0105270a0c0c120221120109 78
    0x30380c0000c00c5005403841802c2ca00000e101a002803409100116980d500d0900000c010001c00410024054900181441080707040514600c8a0703600b4a1b000d511080341d400000e005011000b002076110746207003c64030076001e01002415078090103030180d50340201e102c91420156001079400a070300004103800101d44c1e20342c1d07001030210071802404440b0301c3e0482e40d000c01e185501c00e603003d44240c040380008104110604031201050341d240b07041444507800e0004040c148042e41182980301b0790000c90741c142191200d46c0002555504601120b825041c2400c0907a040d9105014a880902540b4000f80643e000c0284003801a5803000062102a529403034a644040c00640040100b110400405180e50340e130b881400c55560040500c6203155260108122101810003480304d015240c1000c01000c2c1000800741e0f59009880c8040840c030360210b1034007102c0141508400400d1403d44540e1510305e07070f900103840300c080b1114161035001080e03844110942d90169003801070354007102100500000810f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 56777179 1250 56775929 56775941
    0x180d0801091a15070c08010e06190902090415092001030605030a03080a050711160501020d020703020105030f1308031608010b0313060b01021f1a01050310030305070206251b06050409 80
    0x1c5d903c0c42c154548a4680c2800d43c0d05805060010ba0301c80c4013132000c0940b44c1440e080d07942ca40d00380f0030810b102d103941c082040c10307270010809008a07840c00601a88030700d40e41c004115087e07106400250310f02c1c1d101c000071500c07524250a00d000a00d0903001091300d007400980f004030140c058807850304c9652040130803c0907100040080d4100801c500d0040d481c010700708101040c0c51800c480801d603280c10200020304c0c01d19170034510011503204000400250b600030b4101d0303401512085010601d56910050303198400a018002041c1c020004204210352401038840a138074541691070402990362400402c7c614007058a003401d00442200c4000c1c00039045a02c00024280d060050700e03500c0c0a0503101503140a000c4859540361605d0701c0d0580e8941484181351009948242001c07829818007524103110304035a4003000301071010015410b4203559034a4141d500e5405000c2064800070b0902d01c00d4608620b0380001250107100c000440554000d0350703100c0401b0b80b4416980c25007081c3c5042556806006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 56778429 1250 56777179 56777183
    0x30203190201030b04090305070501050c04060906050c0309030d0504090f1109061605160315050907030201050304050114100806090a0201020c280801020c0706030e030f03180d0801091a1507 83
    0x25640c810150704d03480724010307818010301a89501d42c50b030b0365a00b0140e080d00c50041800414400810051040941144900d0140e410601d0306684840d400c42e4810714600c06c0c1001142c0c58450800f50556240c5c0c4403005000b40c4810032070a10006654184103000e8601b0f075403880f8040c0f0000d03c8800000d0800c40003400d0f9180c80610080741c03410664864030f040074140000c2014815032800240148031007072101070500690781804005618000350718903154525804000d0400c807002011500b03005007500118400c00c9191085031303490134006140035020420784104040b07070185000142103980042800c080003901a0003074009114810200561100a80108030352601c040d00104c5000c61890520005011404e00041e600c051041c00035180650981c8072500300340c24044403c00240010007580c082504080b01d02c0c0c0c0700d40340e02d075042071141c400800d09038040c030500031444546544002203034129420118100007019a0107a2002c03e28541c040603600502aa40c4080d0b004030004002c0103418 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 56779679 1250 56778429 56778431
    0x5040501030216060c02030c010c0810030b0403110102030a0903080105240313150b12190312020f191b020901181103071e03050103050d030506040e0708100e0703020319020103 77
    0x3c569070b442004441c09665004010b07030010500c1844001d091060450320030301381c1052115880c040703542c1d01148aa03030000130306d0b01c2c0410700802e0806004a200c00c1318042003200a5440f45056521f150080086000a40005080302c0c000181800c00e0141c1041c030301c003030794803804140700f4070002c13044154009009241c1e00d01e04c075540d44c00032900c6001d45a04007800400003042c445010020080702000000c945030352500b203952003a11740105000e417645095450f0a0008a618101000000031701a154210300c646c4c00006001015140d030942498413210540c6400703441c8412212400d4000d4a01c81c0000d4018644400500c14170854001c0b2612209035640003080c28048003014941c00d81042e00c800f004903a4141503200042005072940d920705800d0700d0100102e40c07454813650358034200070449506059944001c00c0041d01c1700d4000d43c14010703c000858640780e9a802002d5901c1d03000c0d46a0341d4032180b0380000314101040114071581280d4000f00208050250700b503c5401410101104a0500d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 56780929 1250 56779679 56779717
    0x13080408030a030e060f01060c0b0603010624170903070b100f120507080604030903021011030a11070504200a0302070507030809010f0207030302060c07140f06010512070303050405010302 82
    0x4000400003000b01001d1a6004503c0a03a82d5820740c1c508800074018074401c2c41910b0062106981c08203441287c650030141480c0a0b84075000440d0040c61a5080362400a0b402c0502c100c2c5590304001480243c01c00b030b6541d4082480000104000b4042964000101d030000c00a220200d00228020b5820802280080542c0c981d2002007070a0788140354054020000e00042c206d05124040c803c802c0245103000c0585007500e07241e90020030490081c00000e1090600742c003a0344981c1d1042d40a0b9144d4003404088964401d400702c0040d00480c8000942d000d140700352500400e19092a0140b84803030300300b450b42c19070f4130740030b140c00076920307411019149042503402e002202c08901c2c00c2004500841c058840c90350f075034644400040a4090104070709080d50b01c100002c000080d400114640d0010800040315100d41c002e251840704400d80e5030001d0403070320800c4104d0552160110300d0343d0427280c048038900340307905045201703e888220922019002c40c40c14401000254026002860f020640141c46850 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 56782179 1250 56780929 56780939
    0x306021908090718020c0102040f050307080d20031909052701030b130c0e04032d08060d060e010617160b070c0312021005060f03060103060f0e06070f091409130804 72
    0x3240c004ad400300e12041001b4a00700316a08060010602504104000d000305140c1481d005d41442507000e11000c0c100140032030f217103a415040c400ea445948040c40742c001300000d9000000e00102d45402040c2c42540320310181101c003e448100c108064020071800c030381aa1844c0c5850022610041400020480341207549000801503001000070f800f002944440320704141c20028445403c06a032000980700410240210a20304482c1d038409041505d000c15075680e8243c0803920b04600d01c980106071500748007031790101480641040c02600d14a200030000c03403003240c1082395203090400c0b60a400c0110b6680910800740c41c00010010140035040310301c2074550320b550701ca410790b654980040040c1c2050003100c00c0248107001d03154004000f01c541c54562040f8600180e1155418400100055030b10300b01946804400e17048900810540701c15900f0501e48104042c20745c0b0480500c0500040d440d4502068042215925424510000e040004155240101220304004244007516040000d000004d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 56783429 1250 56782179 56782181
    0x5090406020a0e0a05030a0f0606090e0a060f151203020a080309030a08010602010e0c010305040c0803190e06031308030601031103090c010909051509100e010306021908090718020c01 80
    0x20080344120401aa42d81e001d807030007855807031410101407082848010410641d074001501d06a025002041c1420b10b580e80d14040b8002e161541c4030340b4030f99003011018030b032614010820824550050405101c07070724010101d0011649482c00f0400070b011001000d021039810450380e80140c5100340102c40340150b0588400955403c21905001c85038030000d240d403500ba0340003400e50300510460000f4055032480180098441c40903001040c100f540d1100080c06000d1014524401040641c00703881c2d07a2405075000c803480d6141111a81c010a151030b00d0400c0038104041205d1040070b22452401c011059683c45420a9001901890405449400308003600c5008070056000e0302102005004003070302000003525203042d50740031405e0107250408100d000c0d525a145000d0141d002c542c0d03603500c0d03613070503d00192035009600b007011144122400071041040503402450460007094204602d40410042103034500c20455804400790081d51b01004180442d10f0840a810440741002d41400c5010358224 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 56784679 1250 56783429 56783431
    0x20a0915170406020c0f07050a0902160213022101030f0807110907080108100203101e031e1403090f040b040204030b04051c050a0e0112020403060c08090c030705180a060509 76
    0x10f14159030004000d00c0c080380801c40c02e1400c04007039000e040c8076440d2500260303500d556032081c1c4c0c0506400141e40f0b40040500c402c800c04e500e60080940720300040c5520594002d4102131843c1e180d40b01c010424032001c41088800c20304803503006038a120f50050325602c9604a400c1507504480f4000440003052407940c4004400d4855030f01c81d80d41c1d200030340c5811901450010a081090390203031041040c8100030407400200002d0343c0310311003281940340e440103040c4a50360182c1d001034010641042c45901c098070038580e0402c0c540c080ea40d001c02026080d07010603100d214540403285d11840d041d1040d0b4541c2030541142103030f103c0c0204014100360341c940350f2440780303803084a040314690850080c41112008a20041c40c42031800c0c0752590820a107490b000e0b18260703034401c3c0c0606201c402500c1070310340011074044501841e402102840081e08064020301030040c10745104034180035000c040801ca0400044080c00c0b01d0700201080d820702180c000c501d5141c8000343c400795149440d00340c04102c51701c42854407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 56785929 1250 56784679 56784683
    0x7060f060902030f090c010507030e1e06070305040905010b16020405061507080304061505150706061503091a090a0204050402030a0c060c120e0604181b0f030b0301020a09151704 78
    0x4800510b172480c4468140031205500a051080a05c80e280100c0e500104540d0401410380b04100d01f8400006896041c124008089500080000c2c0900416030301502401c02c843c501041445240d03240d25041707103d405022846c0e461019061211005031500d07030051034204e0300c0901016224505c91038101a9a4400982078552400010501003000014070a04412003410048090b46604000006108410a402c00300050601095400600200b54080f82c02400180301c3d801c070b81e5001d590b0182c0500100f08003a00c01d045021040c1e0350380c1c1030003001c052050131040007800706a00c203036081100402e009082681c0501c9158040c2c000950b1050415000e405103488101e24030526281012101d030380c241f9440d0030130168207100301c1d07641c5940040d503003681c2d060781401710303200d480c652040300800a98a06546049500f4980300307240c0c2d001108502031400f166418440180b00c4010300d400e0f4404ca10b41c5c400000da0030081084000071f14411004c2440003403403c80b050703085020312100d1900c2c00b5581 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 56787179 1250 56785929 56785951
    0x305101a04050112020708070b0a0209031009030809070806010501030e030c1009140f0a02010c0f06110a02070602070b1902030d0501060306050a05180708060103110412050106170307060f06090203 86
    0x10b1240f07603040b18002c07600c004410000d40ca468421b950b0030502d4099810000c2160f9521404508949810b0301580c030180d00c0079086035000c46100e40c2c0d000c00751429032000d0303000c80c182d40085900c160000c140c44007964410380c000c03d00c3da481c1200440040c1030458200404d804207000940c041c080600c4003600c03030400100d020071540c620f824104952050420001961f0b4089e0500d04061240441c00700d192a409080104603040d003030400ba9182148000c1c0107050604d800009681c0c040d4407000744c03400001903400c6412113074441c030b81070340d8071006406a01c405c4041484003044a00030400b054490078452f20589003400840010081030f80c8007070700f10f8008a81c1f150414465800d00034002c100805045454801b0f84160790307584400448040c110340100200c0314000b8690340d009230030480080c5082c06006540340d80d034040d54200088854004c41d000d5003004c100181500100840b952070b41008405989003088980d5580024003001c1c1000d40100d4441c100001e441995202451040d8500d01d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 56788429 1250 56787179 56787187
    0xd050c030604051f140103140702010e191a06041103010b0306100503010b0306090901110403080904051302010801170118030309060606031512060209120307050d0215070305101a 78
    0x7040200369580140200b031902c030851007414007091040103076001c4481c038059070348180d1a0480100d000d400000034a1401c40801c2040c03080003a815882121041c1040c01501c000e241d0403040c40000d010000d2001e425000701080c0350ba200000e24080303a41080f4014800035640d03c0e864604036698209a000c00810103010040014600b0803c6030300d60580a03919002c2d24543c1003c1030104c95001c09012117000725141c5001903243c40095000c450099010545030b51150b6481c80e24200544c801143c06000d64100b0020582c0307406944004e50941d03505854000c1268244510b2401c0040140500c003079a43d211104d2000032100d0082c0180e2050080d64049a44a0740f402c1c503600360381c1507900000c109441e20b15407208070491100c50034107481032015003031600105408c0c00300280c020708520907405444800d04020f0340384008000c1010a10803820341d103400d01035803026a01e40c000d4449550340d8209000000d07018a1007640582da00555950002c2a2251602c140307120280b07505114182d11b950010f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 56789679 1250 56788429 56788441
    0x7020910060f0215010b0a09030204020f07030306050301020306060405130f1a0405071e0e0d0803400605071107030b07020c0a030507030f020102030d0f0506010e01020606010807080c0d050c03 84
    0x15070041e0b0300340000d000030301078440484601000c04005210f103260712080131850404051080300540001c5400501c01d54507a50410041c0035036502264044010a190040c0060141418020b59110b024000c0003681410300d080140103915140c890441c01c0e05035502000c0c210205d180c410900c80300500c0c1490b2040c045a40d00380403c0343e0f0041d1407602071200c6000e14401a191410841d5a081401d280207242c008e80360021410405403048010242c000100030410b03400e0b20240c030380200350420004203800c0c406603403441c030302c0030180128541d23891045100e04002c00d60a402142c0c001c4c40170318000d0b00c0d1034901d082c214180703140d5400c100c600c02401024410160b03410009640c140c1c5003126a83d492500d56520a0380e50060f52000410100301e40004905580c024015642024409182401002070714a00c04000700340840e43c0d18046029001c5400030340d4400100d05115120613103070782c111030722400c0042d6024007004054000250080041060036a0140202e070b0081c2a8524070b6900d83c1080c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 56790929 1250 56789679 56789687
    0xd170c0703030e040203060a0b0a030914060402010e0d0b0408130504020c01050601120c1209210f1205010b12090c060a02060109060803130b0c2802010f110d0806060702091006 77
    0x80350061344030303a0050041c8111552100170240444040785100c1d59144030030102034000e00b0107508081e10700c006401080074280d102203a8a445140700b680c07000003002210003002407048191a0141c41c01030444001130016078a0b80080035211034000520395155074500c00901a81e001c0a105d007026512002803180d1960400111780d0040d00503c424405103503070703000090a09501c0302d280300e0340c0b603101c205070014403110515a8102c4c0d640c00d140d408145032000c5020300840000c0c0402c40002e000010312641c0980103105541c140c2e041c0d2110301d0f150100e40701c840c003510000030f030003840d160054048070400e5176542001401d02144075000b0704465032614000c8030484d45543d000c041d0a40080007903045400400c040710080e00c488031a115201c80014480d9480c000904500c0079000e04000050442080003165a175100d6200740d8a001451007804070480b1000c2c00f00c070480866a216116070510300303010b60001580004080c05107030828805400203100080c080e910703034040c02c00140080c003016900c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 56792179 1250 56790929 56790947
    0x2502040f02160b060f0a0803040807080c010c02040c030609150f051005030708070314040317070914040b01030b04020f03011701020a020303130516140f03010e06060d170c070303 78
    0x41203821400d142010207180010450124010480e1588200140ca00c0e9115580d4001c030f1580600070159903a1a0080300d9075950090090210900c80c11100042540740090304014020040c0c3d0b8121488003242d0a00c00607018065000c1e06041d1030b28000f0922100f188102d071001140290001c0005203070066a40d042d2009422140c06031000402c03204d900754200c0122900001c81d803900d02d1150303543d407004500a02400518007240140b01c0c09003c207142d403200a11415198020a003407154542e518280d8604440c0c0c4100d41905001219060541c54558441c1400d1103040c1408110320304a040000c04980c0b00c2000010b0020003c070061285944518010701e810b011b0350021450004414000703942c9000040c0754000c4021040c0304101084014801c008280400302205003111391070713900469007000240ea15a0003060102e000070b01a19050148441c03014054000d03048985840080c40001c4441b010b0980301d807000b0858518a0080303e03801000310341c0d0384c28007402045003180742c0280444c203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 56793429 1250 56792179 56792201
    0xc0e030102041505090a080a0524040b1603020c03040f03030305010e040807060b0a080d200304060c11012709110403021e1c0b01051203030106140f250204 68
    0x701c180b006101542c01c80440022120b0941400343c1c0b28407140000858002d480d402140c15802410f8a440420500141c142c18902500d031141048100c800b8102ca503900048030f01074140d8103941c011960000e04d4002450040c0c90710329002d40b43c006454251407650f07001390300615200120388010400c3c1685481007a0242441c0c1408182c0d0742000d031030700300b420700401c000a041c0350307030703407444208280d4442010b40c00801010303040e2100e0011194014000b03a10310b5020092840d8015070701c0c1c3c0a14404004c035001d880094452180340300e0f294980702007104601065070b040c03062a112032031014021004d20082091401d0b0b2108042d0305041d081e600b40e508605c1d44402140e000e01040c170041c2d4460540c82d9031505100b0024410150301c0f000510901c1001030740140348080318127148107000e0780d00f000c1030580300c060360070204502c04401c0d42c642d01c0c4000d01c21400091240310b280c034400e501110082500100a0041c0d50900311a040c0342c4000100f0b07503081c1d0000c110722034140c0045040601583c21400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 56794679 1250 56793429 56793431
    0xb010905010e04060b01120c0302180102010606020312100f0e10060926070b0d0204030b060303030408091905040f050a0b010309030e0d020d060903020f37020301020c010e010c0e0301 80
    0x1514000c03450b40800800b402c000c01041d2034980240051740300c0d6110480d4015504800c0c0102c0f001080050700a6002c1540004034045070142c0e06200d500500030b010484215900031441d0082005051151034000761080411103485600050300e03490340c0c803009001c0c124401000020b803c20091100042c0e01076804001407122143c0d081200803614003042c8411003001e944401c07861075082200c0d0503d0407640010004040106602c030b903008542d806401620700c50040626162142c5003056980d002c12100101803080c10440b511103070402c440400b02613040c0050b007a81d02500c07a4002400d4940c90780e091054550780d078041000c0c40a440c02803880d041d1003070078100b0000645071402000400400180c500550b585082c0c4421915003444500351a500b2280400001c0e1030762400035101e484500400b23050f03203e0031000340440b21703244010203070b40c3c12441141c1890f60129406900415242c0000780e13415503090142056040302170056040707800204000080d000300a40c0050500c86000841500903 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 56795929 1250 56794679 56794681
    0xd110d0c050a02011409040f0b0f0402040302150c19030203032d070e06070f080306091008030703080c12040c03120c081204050c0d06020306041a060909040516120b010905 75
    0x2040012074a0002c07a502031038034420406000c1d100074840e1040348401074205140030000d1061311695030000d5610b0004440d000c002d80c0011081009900903404083d40c40b803c0051104001f140c41c10091040f8612030003030b241014070034204158034a906160075005030b0400410400c08845c024455604404245000c1c1c408192500340c6003040400200080c0500c010301c0782c000c000340c0d180c07016110403d03803002e0803604540161400c951183c10a42e000750040ca1410049610400000030480641d46510011420304d1080d0710101c0358408041c1040140d0340b400c01810b81b10b42488c0d103150340300314000c06040c001780b840c5103041540c1d1070301e100c024410041e45500840024040000721010f00810f611140440c0d21f076410840e0030100303800886944040700c4c0150400700902034018620a00b0300325000c20500e1a02c515145100340402c1c5042e5026404203d501002e00c4d003540c8198025015108a81980750940441c0e1072500301a0031080c05040080c13a158100710702800e03c2805460040414046 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 56797179 1250 56795929 56795933
    0x5010609061202010804060e0f03120a0c0516020a050a080c010206070519030506060d06030308070801051512150406090e0111070b040f0501020c060c0304060b040c050306010e04020c0d110d0c 84
    0x10800342c1c0000904110110b0040740030f000751904400200b0444005030713603484600d000003d982e40c2c403400c04080c40c07607003d900007040844248034010389245280c5401e0b1a00110882c103082ca10090042264801942c04011503203480c0e102c04200540a010000c00002c07050800191500f10020505004c001040000b0500b54072400c002016001d20b078180416940c40c0e0000080b41405040d0202c2c4403d840e0020010a0542c02122a4001c072840d445100943c1d0701d840911010100001c050016584c00304000c1f56044444040d8562085806501d03d080c4240f45000500352081a0b20004003113031225a014440704082c40b48030061807030b0705806443d10394290307030303180c2440790042000e000e100800012200340513080d0100c51241e4040b1081e50308501c1d20590026913034005480a54140340382a907014424205441404d01c04145034070750301e0541d81c8407001158500e01c1242125006502071220040080040000011401c01c0e5100c4a40802184110500e42440700105000300300c01a565400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 56798429 1250 56797179 56797199
    0x308100b0f041e0b190c0b130b090d02150c0c0a050601050a0f05030705120316030206012111040b0f06070506010e0f070e060a0309021915090b0d0c020a020612040501060906 76
    0x40d02c05d482202c04040e200e0501d0040e60200308030500070301150001c40c00c04c940d0000e40044101c4192048101c1c410a44503410705580d100c002c0d40031003015901c07420f580c5032000b2046c003040d81c2c4106d040d4100d514020f41030090508103240e02c101111726600134801071141d49002e0821101500b1036200034000241740100280d41c0c1c002d14468107020b42d0310b8003141c012070175051003180c201686900030503050030680d02c1e0003540d40c0d009119100500741c00c2c0400d41007000c0b00b030058040e0540c04c40d103021288210201040010807404c4e94183d804a00e00604545a8a4a1014040d030034040c20180500d90314102d003000030247c0060444c07400900c07220030800141d400038149465500d081d10747c5c646403408410260010549008069449040046920b103005189000d1000703940d42c0b82c98082014110a0b010307201c1c080c542c0070740d203070340e031414040c0d0500e10400e41d101c2c8500c59100e01c12a800b402454010904d2584400c115001004201d0100030078054240a943c005040e4400d080126525042082d9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 56799679 1250 56798429 56798437
    0xc0f060105060f09040b031608150601080f15060426061003020603070c0807060608030c100204120b130b070503040309060c080a030207050a080315031005130308100b0f041e0b 77
    0x4c0c0c81142ea606941e88903444c208005007000b21440c41103c222902c8a00d1143d030f07054210310554042d840e181c001101540304110140c007c440882e049011070300c0304c1000c0705502560248141e0000410b0000003802d9541451041200d0410500d0002d090180b04005082c280000c150340b4400d40040c00400c0140c480c9002c80f41e014010346407205240d03407136142542d0036100b4040302520407810000301003041c0074084014462090224221512860080b032a103040c0d014501c229500480011020070208210180c00340c1d10001514003001282c074103a8030750f00161000e44000d8000f6034048200303c00c068104410b2400707050541040c40e0031035520364695603e48180401d44007055004141c507130403c10100001ca40741e9034040d8040340c69140c2000314240c00c160300030030325202c0e210705d1209030103288151045a0082c0c00042942d40c09a0850714152055000a450100708519001c400110b040c40000a00036491404894a96441c5400c11003c8082c0001550158055085c03000304055481e000480d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 56800929 1250 56799679 56799697
    0x1e0507080f0616030612030909140603070b16021009050102060f0c0a030b060c0d080613090803010302040905030c06010f0603060b0c0a1511030f040b0108030a0f080402040905030c0f060105060f 85
    0xb440003c03591200072009451365902800d0000340b9415030004254119400070181d4507203101c1007202c142056000b0300c0001c01904c00c260540c000c00310510407030311144010720000c1d4825001c40400c520781d601088495416081036800920b03141001e0040b0342e414082d098000b0f9203080144998141003140f40d2075071007511800000d05541d03800c40440f54030303050243c07010034481e4030a0750200110b035600a0070540044501c07070300c24004001c0350300344a0700c580b180641c81c03504502014110fa003958207207c01441c42100c00d558502c414003600c203162a00708015030282408207042c4411502e00980641915855001051950740501c07881c41034403000980020180d4200349041c10b4200c50390340703400090064180000c5d800d40004100280c10001c00c03074250180d0310403002c100e050f130b0361528040e88900803418a000041c00d010108411144075007401600140000e200041c00c2c07017140e42d80303499584141742d064071a4101c000344208c0d03804c06002507030050a0a441c030301d00d000714606030107102e4801c6041e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 56802179 1250 56800929 56800951
    0x712050304050312150d030305010519061d19180f060321200604050d05070203030a03110f0406020a02030c010207060c0803190203130605010902070b04020402161e0507080f06 77
    0x81c101200542c2c00038517507001030108031a0003403030b042c000c01510007406894001c41011981d005840800c468010495076141d45440f07001075801c003804012560140704560000c4440d00000c0215100100341c1c1c01020400981003a80007d901440240c4081e0310250001628100040000c60041c1d03a034414004400c040d868440304800c0020364400c207446220003071181d06d50381d2a4200d1440012420701450042040b116a29030b24407003282e4074412454001d42542083c440910a03038040e4110286ea0401450030904104640b0080001038100d40c5c8514010382c001940c0b075042d404c0920024216940078805082e20300d0a001c0b01030860914044014460301000000815400041c0e47c0e015280003084d0040d941c0303045c00b200205501a840b203003542e0035031610b800040c0200d0a03108039054154030a402400641e202e13000c22009401407501c407a08105001104400201040405d607400320741042d5020f01c844290a00501d045250307003041460b50300c81d5100fa80e86082c0020701da41e00c022070802c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 56803429 1250 56802179 56802181
    0x308030403020f10090b13030504050904060b031c081003050c0d03050c0111040302090702070e0a0f02120f0114030f06040b13050f0d0806010e1807020a0213020712050304050312 78
    0x1c0c0c202e1070003041c00c1050860340110a02041400110b030004049103000e42c0e040f02260711006aa051440d00811005000c00e9080004224500306440328039400780c000c44000070065075034400329003840e0602d460748904014005c640c00c465500090004d8010390758001d40803880c0d040d03640e41965501c1b50311110348030381e0380d40825100b007520580446d40c4444ac6c80000b40700650803516078680075005804124400c05202d070006034503d10005510b4122044900d00140540703032881120000c1080042500904e5002c0000c0c500050303026903441e001d031a202c400e030b250f258901007042c200010440c038958820b4100c200c100c402d07200001241740e086504441104503a403510000c10400411242e8001e045001d01003000828160104120784002410788500d1850380d144401151070100e88184942d00a00c500707091f000700300204400d1a40491a40100e50a50b08540c0000e0f815031080150f0400c201c3d000640d503020802010054a40f4060600b815811410b150b034515031a40218500d802ca150751000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 56804679 1250 56803429 56803433
    0x406030c020d020c0f12011d1c090e07051b060601030e0309030c040b03030c0607030c091a0307080a0b0303040f080706030203040c0308070611030f060306072102130503150a0b06040f03080304 84
    0xc1d200c0ca40e03111000c00801523404440c04110f4070b80390b600200741e1140a98a0a040c2009116011121464866070f501e00f40604002074001c00910181c10101080b03418005c25003541101c4200c41c200403220310040c0100d1130304c10001002e841540755203040c66042400013140c161800900e070503445d0012540410844180d10200b861800358040c01e000605c0381400703001000ea0035602c80d40c2d41d04219981c0a15040d2200c40001b28540c511ba60003444c05410000607041701e11404409400030741000300801d40c19142400240303550440e8002d003100a0b10164200000d03c003c10018004120074201982189442d84544030003010600c40540312260009034002001010703800104908494244a91a410420600100604100e035554064400d10000c20072042c01088107800d41480070710b148081c0042420118041e40200600b100d94212609022840359400d0000f0403007041e204812000c1c900c0c0011400050b6010f01083c0360080074200b2003480000b4580d400ca50640e0303000801d2030380d60b0b2224 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 56805929 1250 56804679 56804689
    0x60415060b0d0b060f03070804150b0109030f0309030c08030408010633020106090204030f050c0405010506090f0d080307020a120305010305030405091f0e0612010506130903020f01020c030406030c020d020c0f 91
    0x50b03103070607140310300001080f200b1504002305501a40c05058410540d082c0550090115400402000d006ca41400ba040001070f48441040912a00c245881501d281d03072a83d502401441d5600310f0b8100790808101442000000d10400005103d404013a0b01c00d4954500355080320444032a000188104c0c00f10f40303031078a60007500450014007070600c2c11562180c2da0305089000c0310b041403048440b400360341c0b0202024500360280ca07040e50402003555282001c1401041144081c07244015000800c0c41003082c00701c0c0c0c20101540c401d00e5560040e20001200d80b40c840303010054190341304140762400e0010f1010403030000545055480a981041c0c454580814490400440c3e1104084440f044040810032071841c0c2c4500e03000c0d40e01640d150405d10950104d1038240c82089440315000080c0d0300401500007045d400c0a09154005e0060302c000b182d040b40294266840000c1c0940d1641c070024080210a07414441c3d001000094800b80c1080000240000d454032000740a440c400c01001580a425a4035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 56807179 1250 56805929 56805937
    0x70e0132040b0d060302040c080402011709010f0e0d0306150c02010315080a030309020306070302210403050408060a0501030317090a1403041e0306050703090506010e0910050108060415060b0d0b06 86
    0x9540900d500c3d45040103c000c0584000d0104900030b6051a44040d01c80380200350040c041d55050312402d40710507400d0245c07101200000c10102280d0b4a41226548407412807240346000b1449070003030055480200030190030741c0d1203580b00f048036455413440c5180042d03000102400d0b031942482c0100b520f00e8031140c090700c403048a4000c909071f401600d0f030f82e00030150140d001b064410710a40076a41d45a41d03500c0c050b0304034022200302420783c01641204c807400c080003d6103151700600c2070501508040e2100c45040c43c141c0c0884513405159950300041c801e16422040314003400c200703800307060001d1807c4010f0903180c0b054448020310460030601d80003070b410400d0003500c2c0900380110001d40d120400400c03000d00c0b0142e0703100c00c4c3d6a41c2d00c1e00000c100f02500c6805000300d41600203000700001e900e060888101c104000380480c01c9401141d484014001c000c1c02050b000701038a030b0041207142450b040400390050008202007040d4a80242003100b110300d001950b406030018000041c0703a90120000c240648a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 56808429 1250 56807179 56807189
    0x140a120b0402030307140309041d0d18090203070c110303030c1603091701060914010f05010c060212010b09030609012a1707030e0613020a05100e0a0b03070e013204 72
    0x500c0e80603a0708084000007501548c0d070211404d004609e54a6442041d110700040e034030f03400ea085504110352130745c02508031001150071061203000b4659104800800c030380007603c8450008800c0c1c0d07211b8040c000d440451101c00001100510f145052216140d400392241851414010140203690b401f49030103520107000a220b09010001302e103800c0e000d002c0c02040301e40034410140b0700d0074200c001d414a26100e042c1c180c8000f01c0781c8045050070b20307005440c101c043c0c11049030713940e80070010303400d236613216110650080041c4820f01c1d4990034050101410054010504c40c0f02c2c3e031420019400310b0508030b0512110700b40c0c0701000071030b4803040d050483d10402402c040342d015003841d4050000c0300ba40b43e441100018805001c0e251070303803541108155041c12401d006903000e0b41c000c80520080c84d1a103000321020350141030141d0f81c07841050100d107800700c43ea0302c0a500d01101008000000760001c90040c0031031401d107420b91401c00d00c04808a107200540191500d50021040d500e050340d04100100d5003e46 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 56809679 1250 56808429 56808443
    0x3070e041b02030316020712082206030f0b01050315040209011716140a09031e1a040219181107020a080706090b0403030f08040303020d0207080301140a120b0402030307 74
    0x740c54900701070f50366801664136218a4800c800c0c100b018901c0810800151a00800300422101c06d5881e0f510749604035640010400003484110b2010b52125082c19000b80496100440c8a40e035546043c03003103542e95080345050000c100104020380881d020b0b00024204101c3e40140c541c40100300480302c00e4140701110424182c0380e424000750311a1030300e401b041c0c2303e584d03a5030340c4100c4412501140c2901408900c1004280c01a4003440014084108541803e141021410018107a078030340c3c40d02e2030188050801001c210100744000c1d4142554403449c00c0d40e1802c1d201154914014655038850345030310300c007440d080e6250050381703000407000b040b0340b12030350002c0c0609070f07046d241c2d07000c6034954801344142c0e4040740c01600c0018184a0542c00d440481380c06840b240824458a40c0660395004003c0044081650801260200c82c0041c80906010b0b13014020b100d40b2036041c412028044408080c00622030003102600704003550034003016811155000b5641d001644071b61002c139155000d2080020301c54 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 56810929 1250 56809679 56809721
    0x1020606040f0213181109030a032604060e06061c0201140d11030106030e06070e040b240d05010504060806010302061b01060b18010c031d0316080d021b01020303070e04 74
    0x84c0714400c1700c1340500020300c0802c00c402c0a480b9100d024450a401560075400400c03103000840d00034841510010b0750746214420201138061101440c074004c40f411140da03561803004031070b40070003080581c1d4042d500340c440c0300310380b048844084c0010f03e81210081c100015002c00d00827050b00c1000f078882240e0014401c4c89107603804e01c0c0d0707403940b50000d00808000a18210a04000700d000250079030044844d40c0311400f40308028024800500a201495074010404210311901c4031000c0c151007846041808929480390114108031090751810380c0040c0c0320b182070000a02c0025004101c560442ea4120f4030903544030002c60351501d80045004116085501e44600003607400150760003441d240b900c0c180b0143c2000340501c01910468240ca4001d0300140310034000d81400a80f04103142c804420040440f8048640c0450303a090034a16604000b0342038000341e010400312a01005172a001030201900d8030440c00d07824000035583c0c0001802c0c0c00421921100d01d450300c0d210707a0300c16404011019614005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 56812179 1250 56810929 56810939
    0xc07170304031e020102030705090d02010c300c02031b010c1e0c05061306030b010e03010e0a02030d05040b0f0306060702030109030201240810022101080703060c050901020606040f0213 81
    0x46003000c40c0029110f8100d00903072807080d1040c804c40b407055117a502c419003408000814003600b040c02c0c00d0100d044c011061301e88000325003d50300700c0c40509005a945118030701c40e001d078200041074216241c41480601d810000059a0200d921074a03456440340404150349000012035100811342009800f201403608070207115031410001c0c6000c14010201c1c40c010a03a11002d1020341e100b104050741d00240d11142c18403641c1d00c40e8002c0f210303801c0149405d82990300f0010000b8216020010201c02941c441d0805004600302071101c459103803c6828154105031412404d50300510800c9000b4180150000c0004d015580c5e03907003500d8200e600a4002c0113100c2e9035160107802094074907441c080c4001c04003024200503007807008440c290358201002d001d01c0400210b60002039000a00608000300c1401c1c00c40003c8400c0000c0e042c02400c41a0007846264994203208041740d060506010408c201080b8100290340c0014049400c00000c1c1c0707000403002000546c2c20000e000399210f84203048000c0c040018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 56813429 1250 56812179 56812187
    0x30203010911210613020d0501050307120201051e0706090506060405060a0b07020405100302060a050418020702010c02011b08030106050901020106050406060c0f08070f030507060e06010503060c0717030403 90
    0x4140e9455007000c11407071807007104449040c003498901d0315818400e0303c49040da16004181d400d4121030054031116410240421107802d0b42c1210040e40c510030ba44000403c640d02d003c028000c01410720b4156440031280907000240107100320008504282d007600070011803502d45600311140380ba00200100010021840c0440d21200700b601c04030321481c14040401d1003442d0564602044800100c0340341c0c50401d1302d80c24030000d80340041c5417240808441000201680321000205034142d5030303030340c0e1035a16030400a642150305c0c078400c03960062a1040c0300d500010307600141e021200c82d809090204c0c1d0030300014648015901c501800400710324003c0000031305250032a01420140307800340c00078071045464000344001c50382144542000244d82d0241000400c40c03889004190302e020315845441e002c1c0b1500c6003541d6180b1902d080b4005000014404140015403240c6054085414083c00709075141c400000e642c0c0c0e00207006507400c0040051594100840c4c0345049440f540104101c580b60719140c00c2c00b0f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 56814679 1250 56813429 56813431
    0x14070302071203030e1b09180f010c0c12030e0a031d0a03050106052e1103070c030305120a050421030b0315040b07050f030c070c050405040605090d050c03070f05011b030203 76
    0x20320500c040f000c010380130000d00301402c0300701a00811484e43c4100c04519602003403232140f0824054020300501694080c029064030801c5038440083c004018900300031020f13030f884400e004240c901501103100e00c10114002e0f4200d40c07d49019000d9903a0300409464440382500c1c038a501408802c0c0010070080c2c1904440101c03601202c4812000c154500c0b1789212500103001205022480c0c00035282890207016000302c09041d6108403424443d86580c0c551050a01e0f8200385c010850220740081894220400c00780c3c0b0501c600d5052080c0c6c180303541d074496019224241001035076155040100a584280d002880744e800c0102266640c551034080d405400070107030f03420794148200ca00020811801541181c2d81695003910749443c691700c0c00d4441700281c0041ca0100e81050b00700d4800a050f0b51203000b9280114002c1e50b0005a07414506001864852070300041c409020051041203250b1201000b520402a0802c040202c0d06c0160300e00940105900c8007021503d15a800080303280c1549a07001d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 56815929 1250 56814679 56814701
    0x20315061207140703050405100c02030a050c09070c0308060d060b030709021b030310172b020f071d0603030910170108010603020d021018060512161407030207120303 73
    0x34a5005003201c3d02c6141d94400c0b80030103008510301f0041003001e401c01e0500c00032100c1c141d00d00140d084000b507000a0a103055400280c0f01030380400b09180c842d2070500e43c1585c009186007080849085e0039900500103200083c4010b20804840f500700c418810281c00404003090b0040c185e86009032a8200031009410002140342c28428411000004800010072a40100d05016000140e52314004000030051980740401d40c1d0760098440350b8650901c0106ca9006104010071031168400780d40c03400a280c42800b0b811034803168491041040391261103803180070042c0c2c404002054580d41c4002080c40e5225901900740c01030101d0360103c203416801360403411101c5c0c40a00c565040d903070322455142680e41074000070703601001c0c8801000040c540700c040114184002e042c80340541d00b40511074503180b00607038041d201084000031120090b4a050980941c040041c1c25a0741e0b4880249030000d000005d04013030340180200c000b074070b0020305000300100c60080034a06c500a405c10840e14004002d480c000c000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 56817179 1250 56815929 56815937
    0x2040f020a08100e0f0c0d090f0203060601020a080912240609010801050f07080405010b18100b040e0a09020a0803040f0f08010504050d050d060503070902030907170304030204020315061207 83
    0x40b8404004000c000f80850f000e161102003151120f0fa1107200c881006080307020f8042081002082c07030101401000d841c24010b02d180845581580181030411000606403070442d0002034181d00040c0c000019960030382c0c0162030b1010011242a442e038907043c1e0425034030300c00d4ad4800da04001c143c42c508481c3e500c13613041a917161003981d0b84e40b0a2503003642e4060b40d114104012010004000324468800c2a62190040c400491004040c41c0429103405500c082004428584420488806403080040c801400c0c80c80d401e42c41e01e881c0001c0341941031000b418042d04242c07100c0715031040d55030f810501c0000e09000802c0d0382d031300c40da03c00c0e01140c00e0310300e449184280c0c2019000020100c078107200d1640b00d030f074000000c0c0c4004200100d0494207030f4031140c0c070901c08a0b60b0300004240c42d00c0400c002c901500d20400d005a032800c0c80c41842d4034041843c2c0c800c100a44070800c00a0080c500402600c0849505a40260b100c1d200d46410090a11050400c1d50304018042038282041100801e400c4c040c0b00c06440d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 56818429 1250 56817179 56817181
    0x103110a05150d0c090b07030309020d08070303050a0b030321091f060306110705030d0e030d0c0c0b09060402030a0308070203190c03080f01050105040b070203030405040212091c09030305031302040f020a08 90
    0x4252440045c91003011007409040c021040424069040384584510013011000d100c500c03641e03036503031a41240005500007a614820407581e42c40910a45045080c114021403c05090f0400f03801c000d4140066010290032040200e100b480341044032002510b1070a0340034501c0d0030402c074244000c20709884141d5401e820b00400540d440c96860407500ad09030000701540c40c0000a9020b4405003000300c42281306840b01f01321125034014584144030940186546142100c1600d080185811402800c1c020081e0060400d11005030760014601c000300d68035040840d0150744000081c1d0541c0101070720000b03180d5490480f640c400d0340c00380503000914401d4071102c9050f142c070121802d03202002d024880c081002084140040c080d42c2015040c264801000c882c074041d240c1021078180c0c4c200c1d0480c401208088002e0054099003803110301105400d061084020f904486002407180c4914030001c1c050000c0040400c950059100307120000a0300a0014000548801340c604002c0d4407020440c0002160390b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 56819679 1250 56818429 56818451
    0x1090803090d090f230d06060803180303120f07050705010c0c020306090c0906040b04060b0d020702130507050703030e01150807140103110405013b090106030e060103110a05150d 78
    0x42000c02c11740b1304420b8000c250300021a0f030480e121005c141c1071075001d094020690005141e87c0541d0000e02030720300185884507040121024034454070507180b40300b0b4005020003000d141a0a0440e8ae10031030f600c0d66450103031103c140036940303031207501c0001e0450350914203412441500100146015442602150220360700c8954441d2507014680c03d140e40300501b940814441d25041d007240c00100030003880014480d42da00c800ba16140d00011014030b900750041048425442c010a0b6024240035490061001d441c00e600014403920a030000181071503a280b40c0a03845035825400300508041d01c03060410840e85078150b103652480e2030302c5025603140b40d920301441c01c0d5109000e00c140403244030013118105810480150740e404507842000995014030202040030500c1c40b5039001c014001d04550700d4803e01d039201880f01410050b000081890304202c8161841100000c5850450360001d002c070301d01012940002c0e4056800740c0c8100c2c0d0040e1068244002541e025000f03020340a455007007000705810306 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 56820929 1250 56819679 56819699
    0x10e06040c090e06030709150602010b0618010c080906070b090c010212070605071403160806040c0c0f082b05060904050d4407050408030a1101090803090d09 69
    0x78603800d4001404000c04004100c0034149454201000a0a9030344290300e40890801300c49074940041090310003d4410050f0b03540a01c40c1003015801610380300e2400e007072043d01c001c01c8403042c0b40440c100324070700c202c00081c00b4030103054641c0f100004009903610502d9041000c00c0c0da405036604507150003000e00300341d550f600000f020a5010307094414a03017800d4035034880c14001e190040c910014022440740d00da100c00240401503100b62604550042031802e200c4005184000c020060381c000c03480c0406044000da0007110a160140c0c1c002e400c090300050902c0e10380f016003e18034091075100c0070000702e4124078980104e503036005001000200442d580d51004c1010920b0305440190845c0c000b61a8102c04510510342c10311000c281d0220300302203c0c1c10014151502c070801b00c4032481c8200300c1d100c1c1303c18103115100700c40d0080102e180503410241011942c5881e4815110f620043c0702d2501415010000e003904040ca0640c1c020800c280c0301d00c0c00300c4150b41c40d40075001c8540005403802c00c01088103024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 56822179 1250 56820929 56820941
    0x180b0301080a0f0204060e01240503190b0307050915040506040c081303020703020303040b1801020a0201050a05070302190606030c1508041101021507020102040603060b0708030601140403060204060503010e0604 92
    0x1040040c481ca2203903480b0700ca454240c4640691700315840b00c1d00810000000c0c0c5183d4000c040000c010f403006824200a8004002800045c0702044020024801c2c02292000d0840d080c080d40c250006603000050b0010b86403840d0380d8049900100c1100c1040003d003980d0442103a100401c2c0e80c14840351740c4580802048401c0500b02402007421000856820080115410051032090044417141512a00002d241d50000e505c00e8021080c00103244002527540c41d078400d074902d02800100b69140312980040d000e030040c94100000c00c1400f00e400003d043c801c00c1074a140810f0081e940784284190f040c000f010f48103902003500c996404240000e1007040d0b00c0c44200031100d09030760fa41e4464640d03030785018074284000d034518114440d40350001003003095040c40e039014150325000103a60b549455809000d0340c01940c85015016018031822010030300f0102265072114013460701c1c45085161046610303003800385d900050300d840e10201300484c40c6c0e034001000b94165034212044410383da80e800704000a49107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 56823429 1250 56822179 56822189
    0x608030301050904081b0a06051e090a0602030a0b040e030d06081501050d060b06030708060a0b0405130e01060b0403050a150902061b100c080103111005030f070c0210180b0301 77
    0x80070f400040c0400c011902404807980701071011a40300402c521180d2600e032840c032041d20041c0da42c00921400b20b1202400c45000341c2c5514000b40545041d00c699529135090803400707130119400100084d82e10b60140d0010f442c3c294014401c0204424440c201a506d07080708100c0c030101c070300c0c004c40410740080018a50030a503102c103034000d51503824001404002032035440111503658035185214a541c1e104030155200e1040c5994410b40c1d882d1100400030071921503480300070a900704101c00d0040c0d440f0300d42c03d1034200e1607800012840c02d0546800c140105165030098421503404903001c0304108000c64072000207030159009800180240a4000840302c6a1100950002040240c070f10710000003410207070b21840365070030b44d1b02200440000b00300ba691180d81c2103001443c0d0700c0c018800c22120301c8403003198503c240d0350f03010003103000e00c0302404a100140400050805143c00500668814200e06504641c050603c09600b0400403010f480e11046c191840c04c201300d6860085400380100090785d04031b034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 56824679 1250 56823429 56823439
    0x606091005090a020c03040302220c03110f07020a0302031204031103060709061d090a09150c02072112051b0a0b0c07030504030b091c0c02090c0c031c0e01060803030105 74
    0x10b1643c0280c40001e5100e482e4111007400140000400350352492500741e5840c0b01511441200c030215050403044804100e82907062501d891355516500910a0540d681358040e0540c8503510b004a0000481c010801da1000754144507c0041d1109850070318064000c8910525105042c44801e008054694004452680010f18140e100b048400d2061b21203601403c0301c0c01805a03018241d9000c0f80100c0d00440f41d1030007141d1911501c104000020300c2c400d0315420303407000401040130030b950b000792241580e1044100e83d0250400d5980903150644480b05001e900201030b0012040712070014140b900000400100c0443d180001c0300c3d00c45010503803c0100d44d02094498a81d81c070350b0041c82c0320350460103007542007150030b00c40800021041e94400e80503240000040101d80c80907a03003607440451000d03005082005440030305005850f50303d213040e08100b40d042000c4c0c48030800d000003403540c003c0206014070007120444040320700400e0b500c0000c4092551000b881800e80745c24426070369100038441d0507008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 56825929 1250 56824679 56824681
    0x70608041101030c030b0306070e01020d03150b070309080a050a030906050901020d03020c16030b01380a0c1a1f0b1210080601030c1e120f020301150305060609100509 73
    0x7540c4070703a0002090765400d040020700301c1c844202092401104481402c0400c0d020ac0c038a80c042e680400407004001310340c0c5014052400001840d2a1084140c41342580c940800314810003054042c4900c00e020b001080b040740e1070300900303013000caa139400d08400580209040700d00200c1c410307100c2d4044488012060700200100780350740300104d000350700c00d000f040064002c241d03c002800032440e030642e00541c00b0303012424075075040581c00d03100e00e0000e2444050050126a070b59500c940a0f010510780c0b98010707594243c588426039010f40d405058050b008001c81d8010300b003407440d10905c1000c14010b07190245a803150300c40c1d100c4102c1003120a8010007541d000140138603100c6107001031105174400a0014943c0a0719624490300b4a032040c203800840f641803419a041c08403114042d12800c1c80c03045044c140c140c440c03815603c200222203540c405482d2224113910042951400d4020208509507107141c0b201d040d6403420f00c079442c0c2c842591405d00c184509000b160b64902c0d03020300e990544034014081822 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 56827179 1250 56825929 56825963
    0x90308130606050d050313090203010303020703110114040e0f0105040c0c06090c0e0c0301080f011a01030510080601080a050f010501060807080a0627140103080306120a02030105011707060804 84
    0x1403146030403038003035403614404034060320b07040b484031101882800116182c07550001c407201d0f034112a4000110a80c818001000444d5000958804076074014002c091450010001241c00e0384081541054041c00000d000031681c0d040411603228000402c3d69085590300c1e20308100580f034007000c141002074002c2001360040f42041c2c1c8141c90749846000072032072a945d1030501150366001203d03500384d84c104c040010441172074140a038503030301c1084400801ca03121420340021000003400014070304040d50b9000003160440c080c0841005043d50100300e40d11580d550741081e03030b40c0c081d048040700e880c003071017114894a40301409500d0590b01e0b00c0e16060035569490804a8011400405000c001c03038a41200240c03800403d488000140c41c18203011403480300b12110b01c1e00b940c8100c4800f4844401c1c0400400105490109507904200101c0e1b4821104002c1481c003441c081403801c0107035041d4600400000d003449002c50303640181d1101e40c01d031040f09694800a0b65441000c03100135040440004100d91 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 56828429 1250 56827179 56827201
    0x601020c0901090c23041d010b040b0901030b0406090b0f060304080f1c060303020606120a031d0a17010603211d0103020d0e0c0909190602070305070203120913090308 73
    0x9040c4d15510303014051301e5040140781c0212000000344801801d00203001d00c80200000c03980e0303181040b502c820031615403400a0702d080d40d21403803290302842d90000c07075200c103268446d4000740e9114000402c1440010b0b00c0d1911507008281c11a00c40740300d020ba10790422020306103802036900c142d400484940c24500b06111900b0198880c44100904460b114854070504a5502c180d030051402a030050103d80b4000050243c0707102814202d90055001040f82d41c0002c2d8070075940036400c018024000e10300f101402c040307000c240761070f0411710354080003000004001205600c081e048134081d11241011014049180b42602145003941c0c0001d034848960305680124900c00c186400010300d070040c03404802c940448211042031000b203070340e80c2100410a48616050340c9540e0003405240c098440c7c03900103002d00b030203c080c480004000640104107a01414021000d0b128090707000f4096a10303251902c0b07041d601660200d1595449030005c4505c000c880c90041c0f05601d00c096141d02c5a10325a11b460014103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 56829679 1250 56828429 56828441
    0x902030a08030a0903030c11030306010e030f01020a1d010504080607030203070c02060c010e0c06030123060408030406110f0316060203060d0c090e060f09071a040504060308120601020c090109 84
    0x6a0584a08419100007030841c0000314810440c00c3d074000754114652600a095424a81c03425003007001110008107028000f01c00c42c0e410003424244642458080d04c007181c1030001200001034a54400b080d44080e564102d50304403910215601c00059404d140b40054030140118080c90304503620000c005403070f15000b83e0045410080508002410034241ea0004105910000d600400da9440b07000c22010a5020460000781034402c890070f0341150b04040e0720340c08520b5988d01036000c642644880040646400d801c43c0d000e0a01001035030307565500e034000500307003c520382c2d11850244203030810201140c0002c001d07610340d2a540d1030020785130000d58503003901035000500010b0b40115204440c0f000102e980a044008000d256004540c0c0121803c0381420020000d1590002007000001c101c0021000b207050026203102c01c4e10f00c0038500b44500080c810740101e8005c141c0003403511401006101488c0058030394100003a01400c89940c8003001203071900102104e9581040d415001402001c40c642c005c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 56830929 1250 56829679 56829683
    0x90a0c150311070606090b090103020f0d03050906190807021b010c052a040b0d080909070513030309090f1b050d0e060130050c0f010e03160905070e0109030609 70
    0x1c02c0d0040311403896455079000b6501211481c0d501c5ca01045a40214003828503800000c64809800b9851500481d182d01040a002032041d01904d080070700b058003038800d80e0349039500a480e09072500b01203225481c80b078240c0144900860082000100b42610016014500c030300d0702414407011b03214010064451034140e001c101c41502400d5448681d505400310342112844410302d2400d401441c00c000e02088402110095000d07017080003031080424407030350482d01440006d40d580b030a01d03660008103c0d00e90180f00340280100c07a900000005156004407014203441c1c00200800501c00d00303d0f92002210000c41c0c01912800c1c202c144414050f0240e000f40c040ea000e402d0b0041082071107100c440342040d20036089400e01c050395a5240a2190b851070908100c0343c0e000e400340841054580b54942d80c1c0b01e4210300d242c4038122a01c41e80d590382c2d100303010a4804000103401c0310540a02c0c0721801c6101141d901882819614010010b20a10700c664a15031000030184c4174012094115121100038160b000c0341 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 56832179 1250 56830929 56830931
    0x319050703021e060307120b03030c0703021003420509070c020a2d09090312050603070302090c07050105070e0f0d0501150b04030c0515030a02130b0d06060206090a0c1503 75
    0x1e50f0035610340600441c030848041c0d90301c00079522035070300701c0080310301c8420301500980c02440704040125002074068156901140c440307402c0300401d0b0046001c2c1c01c1c0c42d00c0420b168000c10010868195013969000d0b42c00d111901071000b020007042690009000c04d01c034081d0710035640404249c1c2a8081d80c0c200074000e001802c0a0440c64071031b07846800380107004603009180380c0c84040400c41e00c2e00c0e56200c80050080946d05010300c00352510001c02c00e03440c0c04640c50340c96580c0c60105119176000c000042c000d43d070141c100d1016242c20f0002d41a02d81001105803829420100007840041c0718200d4022525001401c10b40040c1580040c801668002141210a996a580502c0078070164084010050810b6441c40380d17124110b00d010414103074180d00a5001d90413142d0050350003014102940c1d8480e00c003010040c2c40312030501801103640c8840d40308079050980002d50200200c103d801580130b0395450b07003c6410707a80342c0d154415a00d0740341e080050509003440301c2c140844c45400d44002400032052034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 56833429 1250 56832179 56832229
    0x603010b0901081608060c0f1605010c0314130201051602030304090e03040513060b04030f0204180305090a21080c0a0804090615020a020109030b130b010b09031905070302 75
    0x8040703410740c0000c0c0c11000035036105616030a45002600341080c0a060000e001d0031443c149006488207501860780348504400021441031207800c400c0450411454218009106036008440050000c105182c41091030358040e4000810300c0020a0318050a15410307914203144c40030001200f4501ea00900040b641030000300700019540d1603500800d41d2000c0e045c3c1c050b5941d5403401c401c00040c41c0307500c1002c419031030a22104000d0400c140e002d890840743c201807103a030030074403d01c0000e0041c010011000002031141c1c0040741419400406080c840c882528000c55558840b5140000d41600d58400380c1201c4041d0307003400c0050004000741880022000031103441c0303042503171519130581241d08000c001c15500c4408000300c2e030401c0c99070040d002c500c0c000f8120a482540008044a0703c5000180c000c41d4000c000c581070f000c5c090f8100310f0458000d0b15010540d613b419601040303601030100b461103886403c10b00402c118403001ca55108a44c000002c0000e10310307680c248039440694813140d8001e108124 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 56834535 1106 56833429 56833451
    0x9070c0b01050603060a0b13050a05010c050c1905090f06010207150e0d0311030a11010b030d09090c03090602120402150a02100203090102130308041401050909060603060301 76
    0x2456803070756599003c0218400c142076a1001b52001000200790600246000a0a090b00d80844c2c0302b8081c20754a4004481501c0402d0002c0e1142d0000001404946080308402240040038201d020805680d04e001440d01141221860903070348210301041134941c0e06002181c0600b02504100030006c0d11510001c000700744441b94603006001480412041c075000d968540c0d0044600012a0398070049010014200583e00c9940e00440d070928081c0354580c038010171200c640c80c205664400b00e0929009840f80603049000b080f0040c1aa6a004000814400e000030131841d01d4100e004103141c20588144400c8007174400b850154020103104400341240d005c241312400760311030a03001d40c907501e030920100d0091080040c03c0728200b80e0321034008100f01002001e0800c42d400b00c0944494503211800554991003004060355105a0420000700d0364030304140510340103070700a000003d18520203 = true := by decide +kernel

theorem cover : BRFrame.Cov 56654679 56834535 := by
  have h0 := BRFrame.cov_init 56654679
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56654679 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 56654679 ≤ n) (h2 : n < 56834535) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
