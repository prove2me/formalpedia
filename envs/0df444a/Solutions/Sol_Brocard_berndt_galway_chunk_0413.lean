-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0413
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:41:20.187859+00:00
-- url     : https://prove2.me/submissions/5365bf81-b5e6-4d04-a46a-016ffde18f6e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 74100721 ≤ n < 74280577 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 74101971 1250 74100721 74100737
    0xf14030703060b0d0b0f0136090e070503010609021c020d020f0d02030f0a05040b040212030c030a0306080607020102030609040b090a06050f0f0121031d03070b0418050610 75
    0x400c40c8a50080740003000501002e94031450b61240603000390002c13402c0c0c0c1c0d0280c80c0050210b0455131041c1110300320420400c1e96070000d406a00100c225108004c0710341e100b041e51000001403910150710a00120f0183c820180c041c05043c102090b003550481d50046820034018481490044118080c1d843c031905240320043e80d502212102c60080d00035010f90218940e800315022203440031540045201d000c005070a482e036540c40707003d442c0450b881030760007402d45940c5400107001401c110400920107a0070308201c0e801d0804aa0906165921032591400001e4454404021800c0708112190300030080780025820f51400c440810507441004001400001c14800820070281c0e050085d40c1d00590402010b010030b260910b4415240384064804035108240b01000040070307500ca50401d200e4120394030500c05e8040710380e1030803118401c0f11001d5215001c0558200707485554100300c3c1074020710604000381d40b140d00d8400c8003154034030000d4000d4070480c208420040560b0314100c05250704d0190703080c44a6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 74103221 1250 74101971 74101981
    0x20c0c01030b0a0302040516030f0615050c01060f080304030c080f0c01051303050304030b0105030c040504020121060e01060c0b07050901020c01120b0d0521090d030e030f0303070e100f1403 83
    0x100f0029690000e90041c0c50a000c1c08266442c030070650340882c44540302840040485c2c410b072404c0305c40c680704181a00c40301c0709000075091f00ca00c0040031030060680000c0ba5081d1201c04918900d401a4842050ba510000e010002c111140500500070409000500b148480c2e414501c1d4503420304509440c10003000041c4501c070072001c0f03401130b40619049801c9a4813942c99141c01809101e0030302540b842842035580b8621145454003405d84181e5060352003006e220400c19484510a85000c0400055500c0310404900f100115031414005c2c5201e6403681c6000c441420000e40080001e41110b00300a800c0107810450798000580c40c2000d0020718004a031008145045d000910300906411345c0681d8440c1e00c5414040c002950314a5980400150b804101c903082a0b00b00b40c2c468285111b42094691050b1070110f0700502d4651203a003406070980da010407254228034190780c4100d44a00c00b00c1e0170729816070250b0070401115411030409080c90070f605504074602402d40544410825262040000061 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 74104471 1250 74103221 74103229
    0x915080103020a120c170a0309050301020913020f0702030a050c01090806070e10030209030a0609170a090302060c071502010603050105060109050108041202010b120606130b130e010914011e020c0c01030b 89
    0x1700600052000d004070880d0204010344500f035150040d80001c00505012030103141c184211109400002c00012110000c1140280a0340200d20020b40c2030809000480c0075803800c2c020200e505216601520702110f1240c00940241e12581080c10345a001c1010480c0940e003012641d0b440c8041112283e20b00550380b0350480c040c0c496803481c29050300070700d10410300304641a001079443e030307101d200542c403070641d01d4200c035420f4080e011401d400116000004c00c09801c001d0010300d0300303d9249007910f40d001c0e114402d00c0008a840044840140c0d510034041007840741c203201e00754002d00246005000c05140c04002081d44801800c0074020800d003040350b2a4a034002d40c4440c104070710140c48226101d8000c0b2145d80c03548011141e00d4000c011031582485900c12500c142ca101000051541079404210410200102254160050341d99a00c103043c0d0702040302c1401c40803800b800c901c0003250300b0151559038401c44040d00740e01c1f08030314014046002d005c2c1001c11603d41c0a4000c0c6000035540034060001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 74105721 1250 74104471 74104493
    0xa0807050c071a030402040c030213050d020f06040b030901060f03030e280b040306060f12080c1f020703031407020714030309092703070b010e1905070915080103020a12 74
    0x40100050783e007032100c4042d0362078007852045008803010031034a26403000640c1a0b01c20143ca0040541d8210000d01140c60810031403e6010b0014111801268042000c5200c95005400005131140c000c8200300f44400c090040c0d00251035404524105e0a1440e5406403040f00c0501100d0320402207120134000d201c4514a15859403400d0344a110301883e55211b050200761b029000942d201c40c02c024000c500482003280b08411030740210f4680c80d200742103403039204076a08400c0c0d4002041c050100404641075900164402030801501c0060b83c402c0c262038098101d8400e004640c1c260f58004e0100419607030081610740c1100c80b4205d4048880445400180c00c40c8182e06949501c8079080080c0080c0c89000e030151001c40883c400000c1550607a600c030f031035407401400c0d40180100420801489a442480344140d00007030b110204a210086a40d148000d403441160340000007030546000b04545a03090022034200b1b507e5040c104074075411500030801c1c0030340d00d01815070400c0065481d502000240041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 74106971 1250 74105721 74105729
    0x315040603080d140405120c0f01090804090b270603010209040213050114190e01050c0a03020f06010501090b07020d0f0503070605090d141206010e04020c01060504050c0a0807050c07 80
    0x10010107032203207407030240e64000b41c030107605052800c0c9205900c18200200140240d400c03000400f29520740900c0b4000c1540506201441402880100d2000460901502e000c0510802444e40c50301e0802411408a07012042e80612501d02e10f07120307004403ca24800e641030006100000011a41c0f0080442d0192003000d9019411030310000382d04400001a005000a5401c260f8070b40303869649a030302100081c0246103003421541a100d25041a19025010120300c0e000306041c81401c2076244000181880010002900503800c58801e00d0514001441458058602424010400c0f41441d2a44c030721030040380f800a01940d48119140240441ca49002c448a07600008403942c0700900c0ca4882c01900301a0341e101c0d41841858080d190f1203001e10b940c00700c20820040c4681c00c0000b215440d403001e060142c00141030000e40f030080d8020340c56030b0004000041c0e144001140c42d91504040c40304482c40108200d00b510000d001240050ba80b1519198002d2074a14001f52203080c04c0713151900301681980 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 74108221 1250 74106971 74106979
    0x30f0c09221e0b030d09030b0a0903090b0a020124060909020c0a08030405100609090305090409140303010902130503010b0105041a0909010f030203010c080124030905030301060203040819020105030402060315 91
    0x3207142c1e44601580240a031201e058050714100c03510034206036600070150200503e1040400005481c03031815034442042d05029107007070881c00e90703035101c1d0004a0b0303c019103000041c0d440c1e030100840b00003911007000440c0050001800c180703140c440010300000d081e00030100c44503000101103107203000400440e42d0041c2c004140c1c0b6034a0400c0d02d40b165035144210b10005d00345d420f201c80090f201c41c03d4850b503001c864150312014a01003109007080014070102c00100c8200c110340c0c10f0b1440c844000c20180d406481600c4005a0700d0310024040f2410014a601a51081e030401d00419010b036401010340742120f90704200091100000300c451030030390007a5040780d07410022840000231070500d041c00e441d040720f000350002c00005502800c1261034400074003454944410500c41c0301d80d041741d14a00140220002d10340001c141c0e4065940500310307030082e480000140e00c0801c061103200d405100006600c42104c0340c031180c4120f150f00103040d5001c01400a032080101100041c07030030b050101000c1640900034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 74109471 1250 74108221 74108261
    0x4020706021b010e070803120f131205030612071d06130c0306090f0509210904060314071d0a0c11030c0607030501081b130b15030f0c0922 61
    0xb00c140d8000c140c65004221103200d0720320001074085020049403492035005090f074031160b1301c0c0c1d8100c01c3c038a1400f90030b6810440480704a030300801c1c5101c2c0d940280c0700103640c40c680d0300c0c2451400c11000320301c4004600c550b82c2200340100042404045041409411000001c00a907220000100041030b5a916040c160b810b1860844a8940c564441d0082d5010000d0400284034843c02c50400c4860480b01140310340c0c00003c03a280002080001d1500c210f000200581ca00604070740400c003654101e51045882c07081c01c2e80d100e85030358414440c60010381031136010b02445000720300b8160b034541c00c00f03840d80b1175040e07031036040103460b80c4140342c4114410415400c8958903000510b807030740c0d00c440488030400000e20307190011800440218840b00d1420810030303038810140400301008a28114181c02444440d0340340d0481784240c50701e1075580a00e1244a4580341c4a01e041019849103d90040c801308440d8820401407410783c4d40c20406e10b00c01305c40100c04446148c0e603004108000c1000400c50920640e000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 74110721 1250 74109471 74109517
    0x50d05040801140c0702091b040e0609060d0302030406080603030403020405160206060a05010c020603060d0212100f1515021509010b0117040302060403080901020d05010e1e04050304050402070602 86
    0x10000034411241c6090003089642210150304031044030943d081280700340200040d07405071500080903030708418900c140351030b141040c0c1d0030360503613030b00a81c800c403c007100040400c01a440d0004001e541719009480042001409580003502c0c1e1046010721010700028201141c41078a0400a4501455020340200594100b000c0355803024060020300c07030018407540b8001486820048005401c460042c0c5414030101c4455082100f65003000b85010b8000d0902e151b50f0002d60f80e9203001881490120700a840c42e07031505080c8005450b00f110200d03520300c2c02e00001301c64010008100c2c44c12185940701525025150a00490404016640c1c4005014243c410300880c1c41c010750240c128070000f600c42e08035003491490194205041114041c02513040b4a00240210f03000e00381c0d8591004207100014a4660300d00f0000003207480a80203c00a01c901500304005206003403000381c1041120701c1501102d1403d41c0c0e946036a88100d0003400d008035004680c179010408240c040e02c94000c161a10707141c010f808 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 74111971 1250 74110721 74110727
    0x150509030d0c050c030d0914041116150e03031311030706030b0f030f030316020a080304030206060f06120601050a090f0e1e01080c06180d0606090509030c0c100309050d 74
    0x10b4100252918000d0041340c03543c41c50000f9104840c000c0613202c20b80d120b403904400e1190b8150a44a580c1c019403140c02c8038803004204802803282c0342e064161107407180b40310300303240542314042903a42200038540108004500740020a5a80c01541201130020310700c694134060b40c08a48048103e0381510941502264564150b00540c240c81c40c19607140a0712071905003010b41c0c0c0c0d0110b60406905030000c00204a11002042c59401c80c00d0050040f1410007480380c1d10840d41754001c61f41500160041030512007149080713144071080c83c10485940707060505a0a2082d00502e002d000b840c10b0000018040c6a401d0085112000400040b1003640c84a130342caa00007007034203000301c03444100614400d00522941e00c0440741541030352800001003440c01d03070b95410321906600c01200303054036146845a40510740d46510400c2202886800d0204040d07161154070350603294003404c0c01c590f6410a00401c16910030001d82245103160071204242032051990080d8010000000090420b005101c000901250 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 74113221 1250 74111971 74111987
    0x11b0f060c0c02061204110303040f060305010b040e072d030b030c01080915040602040905090c040c02010507270504050903070b0108071503050709051c0303050c0301030c150509030d 80
    0x200905061007400aa00400c503001005036500030340c030100912140c83c180d042c0c1070b45103034004e11481514a0400c0c16400003843c0d50403540c805c00010080c03200510009030305004450040000c1e651807801c1c5070400760b06e0f2441d640d00500050401625000842e410002d19018440b019600403a0302110240000e006010300b8203019058043d100c0d0011120307842d481002100e110308118809000c1c640b140800450b80c03032002a106542c0c19400f80000309481c2840d1050b280514005070040003c41240c000340b1041d00e00c3c1740009400e40e49810308000000b600144e50000c110000b448500c5801c00750200852065040c1d000590440d25040c10441e81ca200040203100950103181040d0f626030b41c0d141082d41e00e81ea507000e90620300b5902000a1095800380d04800e80020381070400b08105910340c000301d42071845010203910303425040c02200042c140c05203d482d030040340d900b011900d10341c10b54031b0b000b9a00c0094400d60044807001b49155008904c5001961310300d030b60040650741103041c3d0180c01420f501c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 74114471 1250 74113221 74113223
    0x5090c040e0c0f0607020f10020109060507030e150c03070c03020102040b0d090c0e010b0403030c02030c030f0303161e050906070b010608160c05061909050a050607180f0e06011b0f 79
    0x100c3d0100c5181d4482c9801420fa030030644e07008106604000300007040c0701c0e10500c00c10700003007599258081180090894040c141c0f10780100c0e90002228116840d01074904800400d140e459484203005100d814503034042107950001d010306150040740c0117403078200d00920980c0d000521660001c01d13543d2034511a50401d2000c9401100c80d030039a10b840da0941c0608407020f101d1181a8401040208000380c0074503200d031110b43c00103050382e55000901c0f003c030f410031600c45298000b81d0000001c1086000300c2a000807042c07802480c281c802c2040d450cc030200c1c0c403080d02a07840140032010400991964070709040f41e4050368008a60409075035540005840c2c0d800039034080e0742568a8450383d0350071a1150110361609038225008103260b8450540c0490114a40500300420076254052030001c10810800d1802c3c3c2ea108a005000503d0007400080600e03410f0440015090000d01c020810401d0003a22041524441d0080454030340320796006954010607a0080806200e00c100a441407101140c540d4001c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 74115721 1250 74114471 74114479
    0x10050a18050601110607031802040c02150a181719030902010e06070206072004020f09090711101523010f0201050705070b0907031a09010608030313030305090c040e0c 73
    0x181c82d02e2005503468142100050202e501450025110901c203030010803119580321140c6820001680114040e1541c4840141c0980c1c481c3c48002d003a1009020620703440745020408010880003a046201c10343c0107100041c00d408090021020740391891412a00d558102841a04940f00c490401a000e001c540300281c3c0410110854a802c60916004580d042075004101902d80505030781d4050700c0c0b4103610482803110145044641098485100130540181d5900c1c0040d1220807041c10003450007030040c10a0f0404c400350f45040441980010f0804502c6009080400d4503a094607100d45040b52a60003c034440080c0005001001d961545507016000d0a9856001014244c0e80030f0f402e80303000340c0f480c4000480c10011400406c8800c4240c0c0e400c40e14010548141555a454581c44154110340103980b00c02e4043c05d100714a01d00f4030551001b0f001001c065421880c3ca40c021841001c09000064240b58664001680d540d0003400007071000d480050007040802da65001c2c840e0fa403004014041c1c02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 74116971 1250 74115721 74115731
    0x3080901090312020c010b090a06051f0206010302151e09030f060606041701090b0114030601060e01050f070609120206100501030605062d0424030509060f10050a18 72
    0x284010300a11900c1038041c1c888169052520500200a5100142d100c0c501d550b40c00100078580d40b41d4020744e02501041c1d40101c7d03100d041000704030025050355805606514112055141c071034010500d907045035011a07200300b04c01c80c00c0c0c00b03c8407a4403a010008910400010310001d5003519a000750804010540c11aa1325110390340c00b02d5035440e0140c0300b055000e84244000c0090706810340048141c07026100c0003182260a031390b0ba03054001c034280c202085080341c04211500e05d05081014074014156440c184a003a4030307120020301b591007200183c3c61030140015007401808655040650340650000f0b410400403c107003402503d945055a1054a450001000040c65031281c0030740426607200511180c6008030200000c4c5000842d050f003505030200b1198440e60205003d005040281a1034078010000e02c810b503034250701d005101200030305052805040c40704800f030005546603c0740141c1008015501c6000310401c2944040d8088e90b80180080350205140380600ea043c84207003851841440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 74118221 1250 74116971 74116981
    0xb0f07030c0206040512090301020c060901050115050a080106050730020705040902090c0c0712030504030c05061c05101a0405030c010203040315020f1e070308070306050a061110020703020a0308 85
    0x1c1c5600060710017400a60000e0307070401c04902e8020003007051200040005250642902c00c103810031404540740400d80c2d40d00e41c0104002c0000c031307600391000341d00d41c5441860161085000b030100700c0d06014070010000d010800c8030070883d45d208100494001c0f198981c0761a440b220381c00d20b40307504001c0344074014001d9000c00969414035010391080f80b030340103103259601c0d902c200280c41a078101c0d020550280c42154070024001ca040045d40b03101a0007683c0303040d03440e42107040c800d1282d24a640600e0080600b0402e00d4032400c019100d41a01600d40003000c215529902c149400b0301c1c419400c507a080031a0140000070000d82c500040c0f0444409a05a640d40000403005903200d00880c40098517017001e001e82d4000d604601c5e0700415540d1801c40883d800e02100340411903450710300058403071a00c900010004245a00110720030b030f004100785000c0c4a41070403c40031501100007031140006110864400c00032100c801d110b01c14600320207880c115241c02c00c03420300a40c0c483c000030042c0e0100b0b11450100f5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 74119471 1250 74118221 74118223
    0x301140f100e0402070606030b09030a081e07050a090506040603150806010302030312091f0203011d0108120c03070204021809090606012f0a0302060105010e0d020d0605060109030b0f07030c02 84
    0x1d10448450301d55104a01c0c2100600000e03500440c02115126030351070012001902c40b0002030300801c943c0c0011912040e06036009452040050041460766203030221104010702c072441b01c503034040b20520780151a081e582005840c3c2c06119000154004004200414065450360103200070044101d61a9891a80c0b440500d440301740030f000280d0903030401c00000403070451030307003501c0d420240050480c0d034200050508a9800c0c0720400540c840503800000402960814040d41d60402d80c00c41907034022540740500096513086090440d0000380c0001c50f4400007001c05100b80c916941c1c000c1c00c10340d81c64120600000c010102c1203031070b900c66083d20b00450300307801b000140b00d4403401040c1c59074a4002c85041c15021585004c3d5008803a410b680c070085018044240a11502d19100350000c10750f0354104000034160b1111440818001c650a075550f10150f9500481d503031005801050000381c4d80c8416004030748903900d41c4c101900c0c01950400780305009504190181c810006507500f0452041c0390003080b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 74120721 1250 74119471 74119489
    0x11010605011d01050313060203010305060412031a12030c06040503040f1e14041b0f110a0c14040b030a0b10050d02030624040c20120d1109060301140f 66
    0x10b441c41e20040d5420302d595405a001150880e22883c08078a4041280d134a10040e42d01c2600100c4c0c16070001002d220412a0450651a18003442c2c1424002a60001900298401c0500c60300d0722618400c41050020b2409008648024500b40c0a80c0c1840ca0a03007011596a40a48251f4500d115190303c0080d40058a40e041d0000900040d460302d04180f4101e050582c031000d203e0410341c05503451885500d11180084811200d4000e45c45080303101200001c05022118406c40409043d0010b0f42a0390000302e0051004003900c06403c00c0141206030140800d00078550950f01581604c80c201070001800314040985124840c0303a64101c6d2003544503c28080000d000e204025015408a00070a540b900500c0619605254652008989150781000034094407500c40c0c1900210342810303803a01c80d5560352217008a610300f5000082151294445211585204008100d090b4540d142d42c00103080302c000c4125407007104003c000300d8680d40c4031030b0300059182d0211203142c410801d00c0c10381546420040c90b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 74121971 1250 74120721 74120747
    0x30403200a0c0f090c0507110103180f06051b0d0509010e0f0a0b07090f030b090a02042d0b010e091302041409010507020a050304140a08070303030203190b030a020607061b1101060501 80
    0x9003a00f40421032361090140b0032841da0305414580c6400710000d02ea1101d5814600c1e00d801801c00e4004003036103041c440102e44025144201f01c0c0903801c10902d0141110b0210344101900b4507000a40b175031000c0806004007400c9440c001c45014803001c0840340b600010741c02c40070600a02c4000b030a919200400c1e541010b8500c5a801205210a801c0000c035510008513640601d0680c15950001c07040e900007002c0310710003510392441c040c09842c0100c007285030799020040c0b042954800c03c8501040c0380040c020150417200d42e031284007043d00194090312441c3c0d030300002c2c0741e0191050003c0c07105680f07002c100901c12a2202c24a41c0b0304000111401c0c80010040340c042c2c0c01002035450542000c0c480d4165424032509980c02c0b0300c800d840042c14020401c000d000441c040c0e500140c581c140f02c101282ca0308200d4035a0b1200310b041c02054100c9580102d210311043e54100c684a6803082541360040280110742c247d02c120f10002d1b0f00d0855050b400ca400302c881140c3c940001c01019450b000152800003480ba0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 74123221 1250 74121971 74121977
    0x6020a120c11010f03020c1c030f0504020f0906031009050a14060f011503110408030c12070507090b120d0201140a0608070e0604020403020603160320030403200a0c0f090c 75
    0x107002c0c0925400b8081ca03000013002e600e005842c000012550310724112241c421080f403116819400545240e06200d001900c10700120180403908094002407195020308852501c925001c0b00419080e540c01c0001d00c2c0303141d000c10800d102c0d2500a0810301d48461851906550683e02091451094000170a466210300519066507415900f020100c0c4030345446203012500f45540d07028810042080c100c0034000030f11070b903402980e41b2017a042819060207484248a0008101070101d240096400325181c0c0c1643e01c242d01c000340d0144600700142002c1940340c1180f0389802400c80d45144194103410034600040c01d1101049161510502802124054030800000d0b8110050901c0405002a0040d0304504c00500c003600b400d840383c000401540c000e444650501003020030012000344c050140c01e0384509514040d9545c001300904c442242e00c0300400013802c000903520b2420074540450f00f105150340464089400d201c4c030314034010500c1c02550103031007001c0743d0007040000d0590144c0180711551035195 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 74124471 1250 74123221 74123243
    0x310060b0313110d0b011703070201050a05030901141501020c01020d0e010813080c030c061b03070315091b1812020d210509180106050306130b03060106020a120c 71
    0x4038000d441c416070303031400715a5801c070243c808149a0300c2d400200040c6005580a03641d651502074007003414007810303280c118107030030600410002d80e070402c0c00d5038000c90003810410307600d42d500154540107041c05500d4045801540f400e01050303d80b41c0c0311203034540c00203070200c1d994407403440300680e40da0100441e018002441888100190f52107603d100b0f82000c0b580d03103003080c1c03010350b69110040343d00700300a0015103038408a8414220300041003a035401c95014116101c40307684008002041d40320044c000018540c84d583d100101400341d100c0300c8000c1080910400c9810a204c060540c400c840c5c40000001032039a0240002d1000382a40d43c804170740c0f2500310307581c00c4486076092100c00039131040280c0d400d901e00d0001000002c410b1641c0200080b817651115550f2000c0d0041050f890750040d504401000c0c81001400380a40003c11282c014004a440d64104007004607184090002a07059903014007403c800000c003644c0020303803048414480d0803401c003240c9803c01e04032103449080c28050a400600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 74125721 1250 74124471 74124481
    0x10f0f14070e1e0409210206070503071d120115050a0501030b0319020118030f2a0902180301020d0f061a09010e04061e0302010f0f021b06070506150310060b03 70
    0x19510491183c019101186007132840e2988424038010f42841042450114a07082240e03a05124103988042182031007800c5041c035910007481301152030216140c1c984e1a51111515a4507140d5280e0910f4140000f4442d00f401075010fa81c000d8400e202d01c0e0b000d540c0341840400c041d0302070f000c1d031940c1c1c0d10090f004104c440004e501740103920084034000d070f0621a000c0c0815103200e4100031090095030141290b1100010140f0b40b01882031942c0440c2c4010fa81154602c034440035406502c2c608072101e01001680381d814010a10050548451040c1d90561001074202030300c4d00c0c40c0c0c2214120f4102407108100c2c0540c0c40c10610042007200030704418130388042244a03250743c005c051810058002810025880d91240c43c1c000a80c040412000326400070340c0800c100315030b8450001c034180501c070b20306030b940c80d5004000030b9035481c030401216002c181c0c6a0015075041c0c60b082306503030925404c5800c0b16007a00340a0030383e040203800207440901034003c0c0381d41984a80c003680100c0080b07640c1c00b900d8515603522 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 74126971 1250 74125721 74125759
    0x1905060a1802041503080d060513020c0d140c0304080f060c0705100507090320040b010207150522060503150a1401031805030f09010e030615060705010f0f14070e 71
    0x44800b04c8100b64041e881c02001207016040502200071500c0000100182410104201161710710740340380d641401049110781848011400d0900700c9594184900d12400d9142113000754045d2001620040c0700c04100001d50040005101d0b10300c1962405070349141d25010702038100383c480c01d00007401a0340f20480f01d00e21240340b0340c049a4800c030a131038185050b070307103940d16406502c0030030301d02c03411000d1098007142107403030140300300460050240010510300307241805803041034018480800a001d03012a4182030030230050b5001c00c241d0f402d000f0401150ba20b61130b0251154105840340040480c50f122100e41509011034802c0684070846044a90350700084011000303405510082040000c0780d51070702c0e0015000b00b01512500480c10441c40e1100544000148002d0f10448800c1c880ea210100348207100b500c40c0d448002082c010340b641680d40025081c0741d0301601b03c0824801d92540b07050076801c4008400d500041ca00c1708140f4203450180c0740c2280440e00c555610020310740c004010b0300141d1032004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 74128221 1250 74126971 74126981
    0x1103040605031b0403050a0303050402090a14010b0c0309040905060723030a02030c0712021b1903030c020607051b04050a0b03060106120e0604060209090709080a12111905060a180204 80
    0x2c0748040304c1c507083d100d58400b4140900080d0032008651640240000c600e00002c0265100000c2803041000304a507140d5102240010301c50700f10402d00003e0800340325203003407080304c0510310050002d21100d4260f00c1c185950300740840d44503000915555610301071521130644010320070f4400c09038608646403c600e92009505c05800d96841c550100320f0388000808403581c00080140c690040c0c07001d01c1240f000c03030250b001d404500a100300d00059140d480712200c00c8206060741e405103080c580c68482440411118842e003817024100d8814a15500002e6407000d5041e51208402e44007800b1580710240310400b6110300b940c0aa9041d00b1903c0180080351140d0300640c0f90b100d50722000314031565203000d0f250a02d0020784081c2e0f40c032a00001c0c3d041c5d05060200505401c2001480c00c0040d480c42c1070100d549030000158003c1010b00d8400e40c20007030920a90856100405003425144084041d418407001030700b287d0811105405440300084030464140302c0c100000302d4042ca5401e0700da00076403c0200400c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 74129471 1250 74128221 74128261
    0x606070b0a2d1401050f150315060318010b0108160c02010909110d1802060403170d110304020901140307030312020d060b040f0906050a031e0215040303110304060503 73
    0x100e00c141e229055044514030040c03055852071000500c0f9803008180a1041c10141c02090180003e07180f000c0003500c0710002c41c030072869140c55694880c1c45220115025541403405140d010a000c0140301c500010414441e0070504560001c01c0414122801901c6c100f104980040343c0c0e41c040e00342c02241601807400301c50341034030500d0f1000d640c0b51a00e17940000c035108005010f50340b800102c1d00b9541111144900f100b01c0780a2206000c1d6030089074005109445a40801131103468000301f420100c414040c180c0d0f100070714a003403e000b50f9a407030301600d41603002110180d00c128548400010300345a1544a00700c242400f40140000e1411030b01d095841e4107a100611104c0d075802c00801e40400040e12a09018296a504003503803140f8102d800044030600e5080324031614a070078000c214644e22608140b0842c2e41c0128041d1451078003030003101000e0300c61980603401c95503404141e20210160070041c01541c0c17180d121106440c0b400018a550b90040d4040e5401003a01000403a01089031003008544031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 74130721 1250 74129471 74129501
    0x105120a06050a0b120109080405060a031103010312120c051b07080d020303010f0602030306010203071101050d060306060914090c061b0d0507120804020d02010f0512040503070b0606070b0a 83
    0x1100c8a5403800e04a44003180e1508089030780744071060181c40d080580c004025400c40080c040c02c01151600211445144100c1d0b1141c6400943e840940740170b078115400e00801c000820341c030396035a810030200c021100400c04001410183d010102a00d582c40b170101054050345d20603040c0b0500c000004100c5911180109591103908000614034904100c02c0150301c80b154044c64481d4902011140c112109410410554100303008100541c1d90000590300c2e1542c0000b105c06803e80381d480103030740e140310b41c4201032409420180044180102904160111484d0b01810040d9161501540110036829038903001c980d00003109800341454070b800a00044580418a0800320319000362403860300c40c04100c0440440c8012801605200301d41e08241d55800c490b00b44038020389040d0303001850200714054003e05011000504031206d034400c0d001d40b101000400f0790700c0c201e41014100035599810039141210481b81c0c4000180d849d0800100340d4900075407040d007100498450082d9040a08540700d032181d11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 74131971 1250 74130721 74130733
    0x18060609040e1603020306070804050a0318030b07020703050c0609090a0504170a0806041a030309010809070b0c01091104110d1109060f0706061502030a03020f04050612092103010512 80
    0x800e40003444118034011298002c0490f1070310f9881030604150005041d00e05101c1b41074100004501d001c06e03c4c41001e603061a101403003400c1c000584403070449a4001400c203081c9070703007000320885d00045d134001680e010310110740c4d80141c0e100c00c0068910410000a41150814010658074200c03900032a070400e2283e40035100e507074666840c0b900d860300108040c4001030b100006114071800d00d48120030000740050390a140050108021079664401c1c9010306041143d8000060540341c000d01568014203000009503664a00c1540741901034000c0302c1e000d9031a250100b040c494a40b500b44260366095644221b25402d280741c1c45240c2e8000e00305520611890842044034030f40e00e0b1381d0400101a200f5009509907103401940c03c006d000c60300c0540000c080510f84036109400d032600001580c04000c250700d400350380c442c50303e03403031448501071a07011170380284000c140305441c09035181c00b0324450b0b52505d044842e070481210440400d00703c0f100720300c03039450342c2000103000c681000b8003a4105054203200310740d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 74133221 1250 74131971 74131991
    0x2511030102030705030f0c041a091906050c1608060c0a05040e01030308160305090c060d06080303010f030302060906100b090414150f010c021305060310050f0a05061806060904 77
    0xc207aa00440d43d04000070000001c01c0700c0d0303040a1526641101d41e8032034183c00c141c2002090b000c10740ca0b9001d1200203413804200190300d40c0d503504081c40344509a4044602144d91504042c04940007024846624003070740055160100b01003201d1000c40350b07107070000d0050741c4410b030f00e40172150b011010b040c041100410010511181c0105000d0082d807288d650b5602d50324040c0e5107030308441213008110302014108400d100d801ca10000340303503041c0d0b4000c9803103d54a0405003400001420aa404030080d40008000020014941d40000007140e010b9000d40d02241d40d030701d600300e465041c110744508990b01807000c1440b042000382d001d451002d1001e04009000701000c55901c0041208950b640c890b0b00811400d4001801c200070004000710007070030440c0101e40b1a5000850549464031500101c07980c40c0c000480c5580c0c02c220808180a407540d0070070190070403591b603d05611040b03912050080c04d0002203013031400c1100540070019048032000382c5540301c5404201c0f45900044c1866407158581d40016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 74134471 1250 74133221 74133223
    0x204211a10081b0112090c0b160b0103050a060e0706080c03070e1905011409090f04061107030206070201060e040b0417040801021c05010902040f0b0a051c0515030102251103 76
    0xba21052112040300d140c070f140000401c45402c400600001d14180525071001a1442c0000c00a50741c0180c2c41c29110918038040c800840d10039000a402d112417a000001400000325002d1101409000144122022420010740e03400540c403590b00010310fa10000351101d0140405036800c19014075228001004c0030000411514003035814a00c0c06140180c01c10056812080d0313001d800c13a03c900000e04001441c4005034074004020308800500d60100001002c00c012a40102043d022800c1050b4a0300c015040c020750f0f0307030000c40e5090055880c01101082024011000130b00c565031003c2c2c8a0103595807951065900c04200004038500c280920000c518100b0a002a00c2038221180a500d10314689040303880540d68180c0c003c4504034810030042c001202540344110941c2c0d0010041030ba071380c011072800c907018400d1140c003203601c0346600240d1040e40780d03035040140100c0145205681103444041058201d124081c00402c0c0c41600c24064103491f00000e080350b15142c081c040808a4003000300104e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 74135721 1250 74134471 74134483
    0xa0b0a15080c09010806010b07140a05030406080109050903040308030a18050d020d02060606040506040302120307200909010e030d0c120501080102040e0108070608010b180a090204211a1008 83
    0x90200c0b500b0042c072070115070800c0b030b40190051261400902032940350600100e030900c50040064000b461b4001410b40d90030f006c1083e044c119a0240031240e5407079807010f0080880303c0c2800f5102c1014202404070701c132113800200355026690400d410314950b8945039400c00041c81c01c40307410615104906407485c041041409003e880342070580280c070744c01018440090404500a000c03920510080c0014081511260140d0b42904d50669009402c4107115640c20b141d405104e0000301040c2c1800901c81000b00944250b825016003582c1c00700d0140c988200c203600743c4040d100300010b15841804020f03648045500318440d05412070605d5110181c007640d4000550340241c00483c507680d00010200b0030940c4164080d070060007604041d06101e4100070009001450622546030214800f007506220203403844c14101600d2401451021b45aa403421503101a400501c24541080000107031001510414001810503c3c1d2003490403450721070340403291200100152030b03181c07a5454400c010869110402103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 74136971 1250 74135721 74135729
    0x70c0f0209090d020c1f0f02031207020102070215032a0c0303090d170c0301030602090402040503031201080106060507020609060c010b031b0901090606120c02010b060a03060302090f090a0b0a15 85
    0x150101c0b850021004e442c00700085119400f9100451014000500001e1041003c0000b07203001410410184012850350003410408040720859a050200c0c1351380560051055030302c00ea0b0b44a0310b1000004000d03c103404100d94404198203901c4c0f00c00411000002000c618500c561102400d043d52180c143e0b02c0c40d082210503107925882042143c49081d00b00c0c10200156a80300b1001f00c1d640b40c106d1001d10070740011b1000800f015008105c0301c00c01c0c0e403190107982c090003010701100c0e1036a10300403880f401c2d0102031046a2880d407038000003040d4140b041c02124941a00034180320f240034012010700103a944007510301040b9550756000c50b41075036020300414156105804203c0b0f0000082000c0040d00081a40841d6006103084c504200c41b40c1c00c0302c803607510800175103000103069024030760907405407030681d01040d030248002624440007501a03026030305890007a039009038130703503246a520b0031035084c10388403041958450840100081c3c82406000c0e408801d81c0b81c0426900c6161032120004a52900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 74138221 1250 74136971 74136973
    0x30302030a061a0d0b011b0302030d0c0809070302010507060b0d1b1202010e091308030c0418020a080105060706020903010204060f020114010e1801060e1003031b0803070c0f020909 79
    0xa00071104114081c28000c0c080003509049024000d45100c1d50510034500b00e00e070420703101d043c09811680116402100c002144000364280e03030441c98029100c5c1c3c0111b00d400106e40c98190540940c51080c40ba0074841c2a0300c03801007100c40d003150015a1503400c280c03000c4034142e4031861026066190032095600740c034440d205c0c00401c0380d00c903143e4200f075a0060f0422802903101d8034400000d80c0e40045001d4000e4010f9aa003c080c0d11159144100c101c024000506585800001d1116412003000180100e030071030f83c81b5040060340074502c102684106d24686000510604c0144482c0c604030b8010180c040c4103500c01440c000408001c1b03070990f0490351141c17010900d00120300807013540a00400200440e4001c15040750742c14a0504c4400250241407000080140194104d8480003584900c01a210b01c40e202d0a007464000d0b812200300c1e1740d50204900007950f211840380308034007074880d00319007030781c840c5041e8119500c508080b240c1d6200303090140e03a50400c10141e01c0141c0c075000107050007812510 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 74139471 1250 74138221 74138227
    0x912070509010803130e071707090807140a03060b0604030611030105090708090607030c180f14060a050f03040602040504020a030b0901080f03040504020a03020417070e071403040f0816030302 84
    0x8100115032105030300080c1640c100f04100720800e0305c020000400d4612008050320140c86500c2c00f02c401c0c01420200b1400c40c0710b64002c0c01012500301e4000800c84040c0700403034410640b21808084405240b80c500c0c1d030805107410092001034a0f42e084000b0b0300744040d00160804d0390b40d803102001e0b130310402800070040c540000140824241040031550144540c1810a09401d0903810280e884000404d84000c140d82d4440c0120401c0c410580c00d1030354805d8600384c144082d10398114101c600d24901c00c034480d904004802c4001428000280c0e00c4600898076514142241561104025400208100ca240381d00f00004146030b078403031000c0d01d030203c070540d40094581181800c1c85886801a04800d41d0b503803024800c00c07010f030000001c45050f80e20695001da107600d58940154064000d9800c409241c0075480d001300814680081c440c012a81c5284400081d9200d4410039a1140c00400f202d2000340b40810000700440c55219080394040e11428a5520340340380b400c01c800320003c54400c1100060703000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 74140721 1250 74139471 74139479
    0x307060e0f1c14071e02060405060f0318120403060b0d02060711030f010b10050d1503140607080609012d060c02010e04021201030201110f010c031b110c15091207 71
    0x40200c1d48858202010700034507120791380c0c40e0303d00322498010040003a600c81484c05021511500300b694014071000c0c104980790349e9042c40c0950990402c5660f00898115a1240c40741840e000496041040c11301c0070040c030b000c1c11511000c014101480310f00390070462601401006071210717801065010300504444005043c10010035044c402c8004075911283e0424180d030b1010781d20340c0c12101c03040456050803a40e400041214901034100f20b0502107041040000c000103000501031410000f4400f5000da42c482d5403001c3c01598155000d03100c00d6008841c002c0103008101385440705090740640d1800300020407010800e0400f03c104940c00c000d0005902c04204005c5580080c0d64010700c1d001118154280400c1e050941180c1205110282c10088040d00030000f00106106008662f00c942d0b009101903054000040c0151041110030340c01c0250300210390506c10300c6135000c01180c800700c1c030260001110b1581001405030007000c0b40103070388204106400c0b1603514a00d54000b800e0502c00503010152038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 74141971 1250 74140721 74140727
    0xb2a030a0902180c0307030c0e03010e0601030c120f030309060905072601060b1213060e011409010203090a06020f04090519060b0301081c050d050f060a08070501020307060e0f1c 78
    0xf001c8180304441c0654050051051401d41525444001458002642481150216004001d14410641552800d00d18030702160010034490305a031300410b074082840d43d40d12040301d4410702000c009850200020428000644240c00c1458a107000d56000b1820700100d4941605218480d031003c0300400111001403c500d04000d94007070074480700b038020031000c1d142c04100103840c418640000c0460740407600140d1003500130581440d0a07508500c0402040c6007540c1071600070100307100b070011248003001c00118122014000c13a480b8003003180c0540303500f4000796100740194201130307400200c11209202c081119942486a10300c90030b0740d041d85402c0741003807001c040c04548094100c00e1002c0d0742000103120381c023000142c9103c0c90b40d240130744120300c0414500485050080c005003030030031800c0600344001d0310030711100d040c01901c04852850045545418140d0341d03085a01c2000c3c0940c05c01c0c001040482c01c50f80c8035075440781000c01951482504143c0181c10b004884041741401c0240c202000c41480d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 74143221 1250 74141971 74141989
    0x309150518120d091703090706081311011202090d0506010e1303080403080415060e040606080f070b0918090f0c09040201120213050a08010905190b2a030a0902 70
    0x41d900181006a4980d20000c1d41e03845006041c0300d80c2030b1209285020802801d411414552100003025103070309109030b0946d00c5020502c0b602d800940002c2c041940c03140c040a1301c5500369841542da4441c000b0318401514194030035120001011360901001c09180c840444144059101e0350203411075605001301800901c03c05081542a842c0c0500c803130f000660400c7c0e20503007080e098140880030f5507443c94455840c0164000c1d0600c030710f044c6040001e80f0351070300c0103240c021846420240801c4da2030b545400d50301d2040a124440c00e52100f202000f00402040003041070200103889050400b11817a6110400c007425100c5450507846440c0d0112002414444104d48a4045031401810700302500020140202c2000c051001d59002882400030158800c50300c00034600a45401c1615948810081c002c0c000c4000583e00760064038080c540f420400c0a448000e1980a800c0e81c03010345800400b0740e007414056844c41911181c0e00030a0b07010882c4103001d1403003031140440200329001a8814400405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 74144471 1250 74143221 74143261
    0x90c0c05120d060905062110060905011401030c0203030c070302151e0c09090a0b1804030e0a1d0109020f070b100f05040e0a060b010e06040810060501020d050405040c03091505 77
    0x30302d080c080c00302503a507001001c41400091440c189501f10032520309070a2400720304a58a01750300d4040e001800404070303005a4104d9600340112400c0c0c0f40d0719001074040e00c900c1003448006800400000d0b5003480b0b01000391803194020720448400140c501026210218140d4445460b43c0e02018a4031046185455159002441510060501802902281e42c580b000303007178550070b640ca4181800180d21031103100345095100030708802880c101800c000d4168201d9100c424091802d03000040b0f00503852070238402060800001d180135903880d050441d0004c2d0841030300c100c0c0000040080c04c010030001891755002d601d1000803401d005150104540d40c113541d40c1d010761301841c00c001c100d46180c0c402192000b400343e0000b5000c070f503182000004807203401304520544e074464800300e40450fa070303d00054002c0020340070300703810070205403030700010b81e0703103d42c1a0060320000300104800d1006080541110144c00d086080c00f1981c44095a40d02c0081c040e2000d12014a0355a601042002c80300c1aa40c02c00714 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 74145721 1250 74144471 74144489
    0xf0201021201350102191409060a0507050a0b160e0d080c032b18110d060e010903051309050105060301030f030e0406080d020c0405240604050306040f060b0910090c0c05120d06 77
    0x402013035400c07c00302c3c4c01510b02c1540f00304804101c8420560140c0d00312684c003a44071003503941da0002c903d0241c1064806692484c1c2070401d071802c0f16403e81c0038216000c1071040c0100300b247c00c510035680300f0700700340c0c042400001540401c0c00f20b02401c070412408800f00c41804500e96980c8200340102c501112502424070b81c9400000d2958000719200c031a408007100c0c02500c0e001210341a41c01c04001400001d6095980c540c0b8000b541e40c28160302401130f1465038455509058010380c4c0b240c8030001c1d20000e00070258040400c000400c00170b040d000745826040d201c0d0510100482e40900010200e4020b90301268168118040000f1354580c1808070007a01c40f41124208036a00740440d49604418541d000005131000e110911186540d40f1801e82d0b000f000010100c4d00c8602d042d180004010030704060490f80c090900300d401403145000b272000c0e0f1085010300040092607140a0050001d8010401d9032414800007007414404514107000715280e01720a0700101d47d403006464414803c480b001e43c422816 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 74146971 1250 74145721 74145737
    0xb0a0f06020f0d1209170f04140d08040b0307030605090f0a1401080c0f04090203030301031a0a02030708040803060409020a06050c0c0a0b0412150504060c0f020102120135010219 78
    0x3d068008818050703006040400007864880c600d85071505113268a055004034030041925005400d4040041040da1000b02112844070b000700144585070920040c0204220002d01050003c81c21403009158082c4182ca004156240d83d4402304042c1ea400307540d20700d00141100104000c610036070049880c0d40d51303008114113041d0324001c0800d80310b0025000080c030442d0302e48070140542d80e9a0300305d40710700d07a001422341c0c3e500c1d41d40b0b00d01803079407a05181c0c403009040303a20b00004c1c0180b540c034400da80c41542c1c551141882c030b540302d0307a4543d03056200800c001da209035035228070005038603010614405040c4030740714640c1d1004180c2065242c04a80c00c81d8038400d1120079424052030400800f980c04035010304241d09a040880d107482c25441202c28a807001943c5444100405d0041301d40280b080101c00d0344501d40321a9000d1012401c0c0e200303007409030302c402900b01d00402c25540c103c144042480c40005031980f64079050b07100c1030440c410126100807244c0d0040380c00a80c10340c01450b0452100103034106468 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 74148221 1250 74146971 74146993
    0x70807030f0c0c0618171612030e090a090b04060506090109090804091104380a05070f140f01090b0c0301050a03080d1805010c08072a02040b0a0f06020f 67
    0x81d00f00e6030041e9810803503000f00321010b41d0840c0080b80d02500000341d03c1c4001c0282440003c2e40ca03007400c49003148010f013030600003c008030030420841409805035684043c100c0c100c0180821550b0141614844651342c0c60340e100400c803207000300c600580c880d01d00840d0608103036040012455060700402c0c40145070001d20360010b12018201c4045880000010a00b00510100b1014901480d0f21400c601010401110031502081104505580120724504540c40210f800111503001d05980000810003c010000119009402010321984540d00b4503060040000314907040011312002e000181e07446902e00810003410204240d4482c8450054030b046626240c00504103651900c0040c0c003550340003403000210360752038021034040307440ca2140082c1a5480e1601500800480d804000018a614042003040b44502814800c00120640040f9126450f80401040d00003a00c070032a0f01603a10440c011080e00d03507178800b03401019410100342c2c00a25006c006403d0400d01c42e14400e8a030083e2071560 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 74149471 1250 74148221 74148233
    0x30a0b0a06020c040b0303090a080610060302040608070e0301062c01091b080709030507030c0305060f1006030209040b0d1a0a0504120818100509010f0b031005100902070807030f0c 79
    0x341043c011100480e03183c9000021070b0662181407842a000000880049400400007501c1400b0794558410b03901400c0e0ba40344110101d01490140b10001046840401d041e03074815042e43d00d40d501c00400000c0d500b170b51020aa52901da4046440080c0d000c906800102541500040da0040500c00000c1c002060002078544046811f0314003081400390200116918610440a6030301565011045404407600c0342010154a0070b1f910040b500b501c15040003400302040c102410b030041d2070a0489207007490800c03009030b000e5004840807903000350b43d48400644d540d844080c2100c1e040c0c018a120b03120b0244d11000070407841d1380202454143c9080c40148030000c1ea410810240351041441d00719425140e41d0003201c0840680340c83c0050501c290f09544a420b50207a10190249040c60020400c450b5655054015a840e01d00c980ea4143c000a01d8202c0c0004c664010036070184200b0340154416454200c04030481e008000c1c2503581c83c40c00304800c400c150b00a40d689603042014207098507848002d6a441c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 74150721 1250 74149471 74149483
    0xb03040f080f07061401051f05030a0b09041202010b0d03050f03040c0b03091b030a0b0a020c0c030a03030e0c06030f04120e21060604020307080a0203040203071a030a0b0a0602 77
    0x910005032030268500344446070040e074410540d40d50761556580a50308000c8068020002e81d1004110700c0000090240b030040041d82c042046200b441c500841068401e070382940004120030720203611180400da0654071000703a24442c07071148a14120031949540c0007402c54181210b0b140c06441d0108446000c07a401c10b00362011041c201c1c00c40c4c0d580b5512441c0440480702142e104c149414408001d0142101e000319000d0300c3e102d0280c0b0066541e0314001c04040e69004c090a01a003e18503000103c1c180c100707a50010a540e0310340d942100ca1101241c0c0109107001c3c07841e1740590003c1c0e42c4810800c80c441d8180214280040125003a40c00c6080051136800100c001401c010451401140e842d42c0da24092600309401c80b0006003020401c044500404c1483d1900c515029803900502000503800c0c40d0500c2528040d00340f541c0e42459076500c04420000950019005903403511540c0c10004100848008100c0c1e12492900a592641400250750064498030034041d486a402400c0901c0829800a81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 74151971 1250 74150721 74150723
    0x901090b0d020d26180904170c030705060c040605120601020a060f0c080606121602070b0409060e060f060d1508120301060f0306050d030503040312050a1e05010b0304 73
    0x800100140c00300e00040036515a070300c0083d0420300740c100c41801d00c100701c544e1180b0f41e6160814000e07203840381410a0050300c9030051011042060109942503400e007199000d9002e8492818020308401c1c2d41e500a18a42003000303d09d5543d800001c000040201c144801e075040310008403a20300389030078600b01400c6405001813a030341c0200c210b400100a40c0c4204800030f54503400039002c0044d100402911005040ea01c01c0c040701041100000c9015400c28900302c820503a48400d040840e500c03001c0d004100c0900358480c1c07204510901002140d08445000288020700602e0000141c66140100c050700d004401480c00d8800e0140e034080708400d0b01c0782400c40d80c5039000d45000140f240e00788401740141c604d0700d40280e00310b480ba504601b2124507480c002181611150744840f10704602815045043e1409405034503009400d10fa0800d0020b4062070185030014443d00709400d040d08242d20071801c82d1022642000e45c40c0e1100141e803c03103503074141c0b44621210a048140315641c100f90b0a900c551101800c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 74153221 1250 74151971 74151989
    0x1505100e0f060d1e080d0e060606030a02030618090705040b030309130b0127080c0d0c05010e01030e01020310030210050c06010e060a0b0409020a09090207051f06050d03050705060709050901 83
    0xc01c1c0c80c1005000f00c0d4044502c590b202130f92035840c04034100701c2225080403c61021840c901f80c0c821592031070000f00c00b8818240100030a141d9928000c02d007002e500080c26581e00000d1400340351500c03c0303030316200500c10741200300141509498801000103035003924000c24001d8104211214a0b522351440c403001443c0c1d2410040780b009031400040303039010042411081000c0001c2102800071500f58004002c4882400856420050182c2080348889040200038059045c2c0d202c100712a50040e246a160f5540505001884041c00d10f0240d09a80c4200d540c10030840a000c0c0c14401c503e407040c8820760941440c5013640c106a600210b09039543c0c010b010300c46045400b00000b40a075560300c0c518402038204600215101c5944007201400707500015010b00219509001c003043d01106c605c2036409007a0490010003101c159400240c0c01da0001320580f1038010f0300c40c6d034003280e961191104408414403941e207250391046107041c19401d113200030b0b00200070070048940c00c000a6840e8101c450550307003451 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 74154471 1250 74153221 74153239
    0xc01090b0901081b0a090305010f0203060d030810031a07030e06070504210204020f030a060501051306030504060608030c070618030f02060a030e0d0e120703021507020604031505100e0f06 82
    0x181c0131300c20481040c4c1240528203400502c5800250380a0030b1030701240d101300d00078070002108845480590204940450704540355846590110788580030594000a88900b0220029105e0b211201504103c01c000c610900040091060b0b4981c1445494010f01403034003d0304c42414017060041c004c1c422071144400e400514420308544601c004207440712290700070003c640d141040c03003101000344c0048a518610b14902030700041d06501402c11074961581c042c00701d16155041c0403090b070080c0750151054400d955a048042580c43d4104001c19030207441308010202203103000d03c024661102400e04c0d0307203e00c0c101c85041001426411116103029030499145032140e854a030118020101c14401404034450101c00301005500108031142074002562070203108074856500c1c55846407140300080d0824030b96505624042c654001800202c0e100a182c240340c550342c0d0f10b504203482d224200c400d4800b5a100c1c1400b05060080764400010806a80304a10902c2c1000c0480c40809000b0580e0b8013421900e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 74155721 1250 74154471 74154481
    0x804060239031914060c030603100525050d20030c07030507050a0b01150c1104050c0706050a1406100816170906010303090f080714010302040503030a0c050c01090b090108 75
    0x40c00f11030400c00050141c00d40d0f4120505240103803070000000041140140800319500c070009904507445000058000c01440c44081c14000c001c140042202c440000c400801008030141601e1400c0b841d00c15684403612810101351017070858600010b0319407086c11031102c2d00e00c1142c4c0f000a0301e6001000d03440c0f564541101e82001d40307203131294400081c828001e0f50501010402181c412038140c40e031401c046040390481c445c0990b483e8595060150003038120f005489010700d000e4014640c8500c102c4040c1e4100941c1c2d64a82c000e076013080d5841551240ca82e1080b204407246040f1260b40704500302c1b15014050240780c405400e81a02428041c0c025240c1807580c456640900c2501143e5051036005d1000b03072030002551038a51500380400c4000030a550000500c0000d07544001040c2c88014000e080d04030b1500c0d040c03000780c00000080d14103140c0c081c040050180d800344058044040d26840e0214070800b036280c25400d0924141507e818801d60580074030060b10000c094031f6841c10300782003c14690700e075 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 74156971 1250 74155721 74155723
    0x50901061d1302060418050610020c0409020102030405100503061201090201090306051b04060c0b24061317030414040c08060d0203010e100b0405010e010608040219050301020403080406023903 84
    0xa128010750000000a4000794513802d46c0e01e030b8440f01c40341003401c20a88d00c0b81410010301c60080072030341c8011ba11560038140035103403a5000c82203017441401241d00d0580d0383d6020030615881200310304040381d0003004000a070704020480d031152400c880300801c00100c859001a103107040600010f0407169075980010a0340c000038107203900c5403002d031038400c0d10b072641c0e094010084d5549100171a16516180d0200b2400c146c00340f480c220074120200c02401c5100010288241c0d900180002c80030041c49a0000501100c0c4d01c0b000310950050201560390f481c00c1c107105c804190a00100382e406940380031002d21805074043c1152f6003002c0101c85040e009000d6000213800340803134a03e007441600a0b00142d03041d0341c3d0560b11a6424040a94050045030b0360758481e58070400e400d210307078408a421907000030300614001940d88204100d14030320540042e110130220382240c1143d002202c0800001500344405601008000d083d03100699000c5843d80c5c480d4112105c02c41c3d0811201c03401c9202201c0801c050f03134 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 74158221 1250 74156971 74157001
    0xd03120b040207060c0e0a05100e030109060606020f160b120604090209091f0207080901030b011206030b06090a05090a02040f060b07061d0607140d09050d03060603050901061d 77
    0x41c400d41d29060b040c14007400034580c0c200d00201245030007001c01e24504102d4100ca00712400144240c00f40000c0d5074040e100380d0f0700b22152030340c15541e55160b140082c2151003a8405010940e0081c0007400a06100a2614000c1d81d0980380c1c0904407141089042c011004484200c816403421205940b0f6600115000c0c040b00c0030001d610100340c6042004507800050130000001e00c03244240c0d0350032102482c94041344101d10010f041d03954100310310f02041d4001d81101160480614042036914014142c81e01142c0c0d2a0700116183d00d05101880064036004c0031454102490074070412250138070034235072541d4203040038000340141c0d02c494881000b9032040d4091700050058030803055031683c80d840c04100074105207030300142c4a20209000c0d104080001165480b600240d00e5041c074a0000d607901d10016084910f95007007807512050110001001884900500025a200451554241100a426a240201070809580c074041e000c0140741e1200c0940c94600491a400c00440d8560840750100344c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 74159471 1250 74158221 74158241
    0x1b06090f1406100902040303020c061b071d0a180b040305190207050a0e010303050307120908070302030c0708010e0d0503100924060903020105041806091e0e0604020d0312 75
    0x86151403924954080c0818114410042108a0f00b54107454a40c074104a004900002c1c00580c4001581c0700d140c1005d000501140440c0f41c403158030119118103031841c081c890781150500307070720404115001d00700d022031068000c912071406104011000c02162030305070b03008002500441442d008901494003a9080780d1100b0000b101e10201c82407403000c040c0d40c600d0240716060084d401500001136441850075031906072a41032b9226850350301c840f501115401180110b601c0400d9603541001d0018248900a100d100d100e60061520741c1c070304410301c500f00f144980c80020143d0404c0c40101007040c1c0810750101036070b4035007030194403900d94401030710b4984402c0c0c100d94500d0786084020041e921600e540ca54044900250400078140c032038204503489210f07444002e0101d0014801401180c04521aa40c02c3c400000e81c0011055034840b1100190f480140d444480c2642c5085459a07050481c000d035182c100308080200310b03171b007001d901040690f000c20801404000700c070700c040c504038a966040402c0320 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 74160721 1250 74159471 74159483
    0x240e130609090209010902030c0f030c091c030305180303010605300f1b0307051606140a0e01020f031501020703150c120504020a0603050a0b040204080703020307061b06090f 76
    0x80d40701c0701c0980080082c41c0c0181e00c580c2e45100006249483d034001c9a02c40c8982d1a00c03141001000941c05500c0e42014180d41680c8038180001d81e4961221001c580c181c510102c06156402458140917044981c003401c410403100460a0700c2c5440c15001040b20704440701450616a00c1249200c100880071704601c40f101d02e01e24007400c2456004526107014000c900040140c0400c0d2101016403c0c0b14500c1184806140810f10010710f46a000c2c00242c80c01440f10144440c0d921142e40e00c1d101100c0c15a00b0740e90310041000144400d0446522076038140d144d004008624018844400c00a5400000d100c000c0314040d948103901d4036403080c000000110390241440900c40c0203214200302405000f0700c59400201e0314854140003001a00625000d01e8020300700c50002420708800703c0181c00000c080b0f00445484620f502e8440d111440140002c005441c007426419003180b04260501e902039021300100441d9020300c1e1154044a0502c14105a000900040c065800e03d0236400b0b0141040002d040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 74161971 1250 74160721 74160731
    0x1106160605090a0303141003030c020409060c080a060f08100b0312070809030c040506010c0f0327080606010203031e060411190908030307140c250609240e13 69
    0x40400005141c140140c420b131402d0046200c0704480081b00201180ca810001030840000c001103405600201c501c5800648045074842140e290b42007584d01914000c000a8000e80c03c20111030090310070603000c5d16000b40000e0321a4a0304880076612001c104c0c12089559560012414607907041080402c1d51140041103030310765441e41023042658102c2c0d94224081d02404010314518a42031107224401c40c816194665640080e4950f590342d00b85900089092241c0007a1030400144442040302c1484240d440400d00e490401c03003824140100078080605660007131052015010081082a02d203508105185030541c1d200c4001501070008003070310080000700021000d844000c00781d51944810181e846844403a69100003041d03403480121403510000b01704004240c21004284020604a84010304840d0120309280c5950740c1121a5481c2c40c0024411800400801c0d41050441d402802c401d0020740a443c075220650008034400c4440c0810000100e1480f5041c1c1d03121811441c10b10072040c0100a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 74163221 1250 74161971 74161981
    0xa050c03160507030b0c03060a14040e0106080c03011a010f0c0f0b0f06090f07020303240a1e0603050403020309120328020c120a030f090305010509061605071106160605 74
    0x921040c1d03e000546503217140c000044d0101074810f0449001e0a400307828a6510303460b00c10b0412a890540349540e5215407201002030000509016100290110b00080c0520801900415086030310b8040f61080b0312032203111912450385c10000405410000d800d154500c00403d05e000030414640150080c8000b84440901c2481344024041301e2003100d007551500c1c1c03951148030030104d40d000210303080070050b0f000700b00160003850015130860008030401d84071560208414002000f81059030000903d80030103050803107400d81d078103111200801c25814104002d007803649000b52a44a101403e40c064103078003030710103040c5d401001190403800059402c0e41c60081d2440e000d80040c80e41c8903001d4018824909010780b545003100b904030148510400a009010050341c0c160748481450b42c3c1182401001080000498803c0c081e00e07200b0700f6504050300c10f42c641060302d150a0b03918484542d041081c06d0090b800060180904840f04880440da4070351214140d401607442c9441804005005ca401d0409100c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 74164471 1250 74163221 74163223
    0xf0f070201030c05070b04060e030d05040809090112080a03051503010f150609060804110a03050f0d14070f06051f060309020306070e03100e0a0c06081009110a050c031605 75
    0x805554030036078080c001200c40403c00c98440c0500e5070041c055140e15800320380015550740c019407003202d503d0241d03818401518010710485004407001d84500ca400150300d1110325114003400e015101d4400c2c007070720110071521501750901403804428241541c403004501c002864030b40c95800740c04014024031041580c0140380c400340281c00c4804007c803000007000b1955500442020b401d5410030b41d1800310380c1e50741c3d4880d50340b00c00540c19480c1d0041030300440440418428040054441e600d800100700c4c1042140009001045c09482c3c2113030000c2c14440c3c00d00050350b014a04801170341299001c90651509101601e0508800e2003040c0741c1e40504400140461301500a02c0a4600032400d58074070f56904e51080d03529011701d10f95960b061b00320410404030800c440e401012101400c01c1100d441010f50f41c1c40c0d170b9010781d280e003015010a0403041080100c11604890b400035010071142400580c0c8800d05800c501d010f8a00c0e80d5040c00004100c2440183c001c100781c1e0b50503043d52900c0c803c0b05c01c20b401c0503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 74165721 1250 74164471 74164477
    0x2040e10060603110703030b0a210512120f0a0617011d010e0d120f06261507140c100606110a03080402040903030f0c030506030c03010b0d02150f0f 65
    0x15055041c144400020068080c1c0700e02807100c0900301010340340c6551950100c1c000d010881100d80c0c026400c2c1c00100b4113042a048540c006070740385030340403a1440c0a05002c3d207400715403440401840307010401c3c0b1452126015810360000c5850455a81a80700e28150380040d00154000041403084000b40d441c02103415008494544509002008280c0721607070b11900782c0c0d40214103032466521040344c0d201e4041c418080000e21100380740d800240310740568840d505440b695072001e41012001e0060880b1240c0758050503098070781c0000108001450b000034021401001810b4100780031804070340e200c0f2084400111032101c11500e040e00c04100e51104c200f001003403280a0b55000417200300400310328001c0010000d2100740c0584039203c0a0b070700e0342e017004080d0110406c00c80401d034882c082c17442e50303250314050303c240c01803a0707200410325181841c01c0c1490071002443c04d511a0707042860140d443d40300c0183d01071000e82c06442900341c2c0d8541506441ca02e00c24415001c852042c0001c03400c1d03090310b040001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 74166971 1250 74165721 74165743
    0x40f32041428053903130b01060503041109100b120f09060103050304140a0305010e010e010528021b0610031e081c0b030d0503011a0408120901020a02040e 68
    0x440b01c2080c80b0a080b0380110341003101d64a6241008541d1803480095210414000d10700746803d01c82c82c6011010204d40701e400030741e605180c584180140c1c80811001094103801741c070403494050300f1440d042e140c25010309440168180142104000300d1140c10340441c40784040c09056010968a640848010342d0407141210710a41072204400843e40c54080401c9940c104c0307402078025400c050415200740000c0182410843d4006408180080001c0080c040d070a0f04025180000405040e80d942c49404d4034401440c1f41c180b4201e4200a040401100001c2003414040d400c0044e2542c00480008040d0b21002c0c00d4a940c6100b1042000b003400841000c200c2039900c1409850052208418000303010600700c80c00921030b81051003402050201500c08408620b20401d000c54100502c401280c20540c076001820000750b4008010b0103258a402ca02c88001c0080d150781901d01071800c0d51450b103a24188880d00f50f01c04000803580c84d00d038070820540e0126034008101708820f8a00c4580c443e982c2c400317211 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 74168221 1250 74166971 74167021
    0x5120f071506080a0f060e011e0b01090e0c070b0c0a1706190806070e0d08030f060d080a1101061a0a1b050601060503041101030b0120070e0c040f320414 67
    0x1a182d12807d1041c01091310301caaa1644a007061115030344444040c0c075071482d0250401401c2c80303000072044000c59405014003890501a6035490443c01e24660b070f80d0f0b00910f91440e250082001c1540103a220701d0300314624a100d04031480300e441e1200040c10342d90103c5800d00800c18004c2011a04660106d10a4001c04e05503c903005030b460884240b01c0b180b42d4a2001038031001d420b20000d201007113085020390744540300501804c0b40324030543c0c440241d90000c5000b1800115450250300e4008000d20030440505005100161100800e42c810039051290a025108200e04452442800c1842e1364451030304583c01010b5461640c0c440c0e600504030f400c204c0d000d89501000201142e0307294064031540100e014103035075218a07040090a980c0c006003000f40c034035070300303100d900e20004207400e1021149000310f5240c2d070f03565030b41d82c50000c0000180e1401d411149403d0100844050320646a03c0c1014440109004440385041c1500014000b440c54111700d0151149000400c0340711810030421a40304080341d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 74169471 1250 74168221 74168231
    0x50306010617060d020d1a1b040320060c070b12011d0129030f101a0301060c08040b03070306090509010209060d02070c03020d0f05120f071506080a0f06 67
    0x10400722660020308200c44440e00c01c050200e40203007420300a80c8095400581b540c400c010255071071090403082e085198040400c124103210702103403080003210042e00c10b082c456088c00d0460b144c00702c3e200004069014031016000600020391034000603035190342500400e80d6003080e07903060b496600d5806044900055403541d0300110b011000d680ea00c1c50b2484200c0980b6400381e0800d00c4420519003200c01c00480d0034480600f0107104080c15000f1840b400140d244030115081903e076140c485107080e00510780440c1400c46000c0700031800d90503681110000e241071456454541032800f21445250059413020400004120009801d40c11000864a03040420007460769051003642c200d019900069134480c03801c0202c0500358001d500a040b4007030151100100c880d41e00d50000c2d42e024143c04007101c608410046e084c06000050043c1440d41e07003800c403294540900b01c0300d00d14451041500c000d081c000c500e02c0d4000403407816404000a400f40c1012107003500541e04011001030402101240d00e0380c144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 74170721 1250 74169471 74169479
    0x608070207060c0f1101020313080c0a0503010e10051902181003020412030c020a09051608150108040201050a03060f06110106090b060f0304150203040605061305010501020709020d06080f030405030601 88
    0x3d9612410003d03000544000b1400043d507506000054041e101d60451006100807107851100c100f20400800740d031001030803140402c1c0d0034400c481c1c4140c2d12087c8641d161610214081c54040f5500d8900e0b078440c90700140315540c14640c03c46a05050345d03a0f40f4090710110300390001020194802c42034420459602e038402c01602d00c100c0580c490350256060303009844000c070700001c1c041d201b0a0750301031008210899154035100c9a00031520200c4261014500d0700130010082a003194001c1c0e0845c0086550f201c1052a803800a0860f1101400082c104100040c1c08010144a0fa00c0031024242d520000d10020740d680c18000e1004a03224541100c5510f00280000c60309e2080c400c0512540c00903024604149009550020b02d8000600c15280041d1030521078008845070320056108510800703000481d800c0807028003019074a01d00090741a603242400500c501ea070002501c0301284d040d00d00c0565680400755461000c1c0002354400301e424400c2c0c025210301c3d03500c0400a801074901c141d0441e0b00aaa031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 74171971 1250 74170721 74170727
    0x703050f0610030b010c0f030306030c0906050303090603150d0c0f060206010e01050d030c15020304030305011202150a02030702030f0303071403010b04050d0f05061003020f0307030305030c070f080301060807020706 94
    0x41e155079070702c12111803901e40c142c1d000781c1081c100d009050402c07030590502034580e100324450078001180081e96900b024010030070003a1a0801624080c40c04020641c203101c046650303441904c0f1700511940c00400012030520b101400311031002c4024000041d5a115450441c44e0b40300d042c040d0419000c451140486e40394400a16581200d00d403181040c0141d00c0d20741405840501c0620035410010680907120119009207401501c0920030400142d480c0303404d0030010120350060308420000300e21914420301503654000801d404190110304282d0740d40c03a0040c04d918522031480c0c004d4040c01110002080d0f10360100141d0f200e18080d45620491008200345050107100074001d01003000d00c2808240b20b00d08100510a9410b8842c400641c010a000d440d640d01d0110100e4001c1001a411882070003103061506481440d5070040d8000c0124500710303a00544180001000001120800300f4000144040d800214400d40e070000080c5031b40f542c40e0000145442800c8500d078015106000000900d07501c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 74173221 1250 74171971 74172001
    0x41a03071409160203160c0608100b030f06061309020405040509010605090c0703090b1b01060806060303070b060a030f0b07080106080f01060302070302070b040b09040b0a06140a0201060e070305070305 88
    0x4010302c1034009a4841d80d000c600700d20390343d0814003188400d02204501460503500c018815000341c0145005038a090381c01020160018120340b15003020b0801000342e0f4944100343d1703402211444d207040f180e940b46000704005002d090304001000901c4d8a000640340c038194001c00a854098a091242b6510210b0250a81d244c1c0c2c4523058000800e40002022142c01c0c10140c11194828030708441d075165640144822500320302d034010800100e0f443c043d000490244105030007096a9805011b407458010001f81d16400340905c0601188110030010700183d503014109400345501031010701c40d000d82070801101d0013000300c0b8402e0204141d04004141e070303030180300124815218031b000900240e091150840194218a80450951055600c0401c8050b441c0000d0f03c09005001d0800d40c448014100f0401030b9158401506c1c042c2415500610555a0084000500520007503002d0303903070740c0d40100c124010f01032503206162100040c2c05201400354540c124601614280d074081c4510b03103d10500842c0740c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 74174471 1250 74173221 74173259
    0x50c0906030705060d0902060a0f020610080d0e031203090d090e0405030a2601082401080604240f0f050f070e12070803040308031f03050c040504060902041a0307 71
    0xb51000000708410701d461001001c07007024504010840d5819035001ca5074a4004200e04001708146540d21281513504208065100041e040301007001c40c5445c03025612030104000403410042c07450b0501c40c054070b04100281055054410070f550324500800b00c44d441755158590b51001890580c2d001440b210307000c0c041d50180e07400c14050b524103850110140c1c1c106034404080301c03110007040c0c0c1c200281030b0915101c50007000368102416260883c038041d034100c10800807807440c1c1171102100500ca00c81d0300080c003607403080c0d0150000c1800081407205400310030103d00309081c424100764203102c9001080e0802d607074605035200300b4406a19800b00020b054001198500c0018500f100e540340245045400c540c80400c042041c3c0d0025500c4080040c1958002d400969500e600041400854030f13000c291022500301420212944a0541d40e50585070300c8400c0c1006e01c00c0382c682c0c0102c0c0c1442000c0c0e02180301298020000c101c0b4945191006440c1c00340c13441c00134130a005000000405400700b00a45840d2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 74175721 1250 74174471 74174473
    0x14060c060a021e07050106030203010c03020a200a0b0703020901030b041b120e030403080702030d17012d080c09010905130206070f06020a0c050d020312070f1107060903050c090603 79
    0x350352001007490094000840c44481c1c2e120841c0383c2e200846030b034002001c0d400d004000101c0d8160550041c9403d4a0100210500305481048215920382d400384010302c810f911111040c0310803c588401910b4000c8164014141400c03681c203000700e150f00340d4004c0000e00004c0c0c80a001c4c445900e010030080b00c0440d552400ba18500c03140d42c00400c0d2040d82207403a419416031001600c2e03c883c45205145802c540c104032086440020380c2811b526080142e07a03640e130b0581c9825a00115100182e074107a40c418400c07007804800b501c1046a50142c80c09200e00d94450b41401251071b10358680075242d44120794607030240034044807000031400360740c4c1d8003601e0321504a102e01d10300c80d0802603003032144551101c0c0007a509210020400c40c00614240001c2100c5c00340f69072182403400d40d07414000d05044a0000311800e5520400101d41c4921600060f07940c40308042c14041100f2200300b60603204021504092000c078040c9140108880d500b107050310301500d000304111402c41d01c0d00c0c01032254040e410348070540d00d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 74176971 1250 74175721 74175733
    0x20060106082707090915050129040e04080304030834050c06040605190b09040f06150b0a141305190314011a010206040f1209030f0c14060c 61
    0x245006510341d032110a000d00314801010785056402c0d070b090150070b800c11550030b038031841c038001805140184008041000701c3c0c1004154903140041866204c5464003c00c030004140d0300100740f02c140d0381500e004240b81c41302c1950500d010300d030915040c4d10860341103004c1103c080201340b10901c000000d00c0c040c5506040b0041c290030011803003d00c0c44030841e295080080800884030b50000c00e01089005900c119008681410b1900031140b034500302c0110280c26a1030140351841c941d540c4803482da0800d422041101840400f41043d81c00307480c000009241d4007030602c0e03000480000440050201900b2560382641c030010001c0c82c405184a2004a002c806003070f520309000f1481c00c280c1c0703030040326003100c600103400e55290b03501f072004540b0340006c9800340d44d64030501d58401043c0202914444092001e002c0e40d250550f917054244101e2507000d41081280110401d400c0d018658403c040e40d0040100d03110140c541c9410b40c50840d850255480000041c00590f403641001c03810b0320802100c20024080f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 74178221 1250 74176971 74176981
    0x30201061706040f14030d140108010e0d050a0e04020909091b0f01080a050901060e1e06090105060327030c0303040203070b07020a0308030901020415020c09150a06051b0d2006010608 80
    0x214445003145140e0070380007c0042841000562045518a94000c13490b503140350316002290b030031907800301d0302d140494010781315440401d035000c421140300e2500d0307041600c0300c0714160380400d00a00400c00d41a4002c80044248500030000041d00071801c3c00981c02a01c1042c0358000340811701c1e0030010b802d408101c48401191504030540c111310b41c4844184000600342c2e9443c2c100130745400b000d9840c3c03040b0207036403c00104102c6904180710b610940545412a4651400c0041001448014080c40340300c1c190b100100320081200142e00d413140d003c881180c0d1500d040b01c0c019505ca6100ba10124030900c05e01500141e032691a10944074610380051003e03507500e18588603150079038402010300b03106550030400482d010f0002520000f03c0403141e401440c1880c40c0000340700310800054107001e01c0e01d80060b00103405545155100e02550102d14045480359000c0241e10a500c0000003204954000c0200c909000b59208005483c0003002d880c030300428803d00c41002d42c440300207000329400145640c001071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 74179471 1250 74178221 74178233
    0xe07080a0b0c0705010c090e09030a05040909030e030615030106080c060304020907031103070507030f03060311041e0905010b09071d010f020a0b070504090e0c131805010603030201061706040f 84
    0xe0b5010050184881c0b508809075141801c6410500b101c1010800c41402804259607020186034043c0d002c8004501d0000d20100281180c0524403540b1401915500c072401094400c040740c46440c080a01229070604280400c07000e0b41b80300f8588bc500961030110000358800307000035015100c8001800f8503180d621140c0a01c420064002c000f1818152201c298034007000301880210303c201415554141c49903224680104408a0841414101400c18009101082c002481e4103044601100c0c00514055041440c1418031140305034540b120b440c08140d40706210301904581d217440411503803541c56070b5440006a540c110240040c9180a09042e507002d0300d54003d0b92450202e02042c0101c4d0054080d9a80c0c070400c01e03e08440c90000914080740400101241d40602e82080c1c48001c0603014159600c0301040d504610314048411640d103030302d1120200a880c0d18840105074003e4005d1010f103880741000f81c040c0c8454070035401042143c02d030701500b80702d0214003d0b010390343c000191000140652182 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 74180721 1250 74179471 74179493
    0x21816030f0b0f0d14101a030c030c060a11030d0207050d1805041503140d0f050f12060604120605040b010501050304111201152702070503030a0e010902150d0e07080a 73
    0x7125900411480340392040d804110000003203c071b032800420078510b00003c0c0000324000044c2680294070048141105650100b0310400031001a294680c60348045102191007202c18008205140400a40310106020a800808031140104211100860070113000c40b041401c0c12a00c0c00f6030b80e05280e0070702403880c1641021215145081c0544403e9440e03840f25041c2c020300e500e10100d80e511404811540390f8015000080440c402d0030b1080c00c0040135843d0700d20603c03030110f400083e8020500000c00c0c0d59559010784000e442c0002401d81c40e401d01d071809a0080c001a00d00380d41144c23070300c000002e02e51302ca803003200d00c101c0d80500c1c58201d500000c024050160904210140781e5503d610218564018052140740200f650409402181003a0080031000c142c0040c00600d15500402c5403c000c900c000040f03030b8011a410400080324845200300500420100c00020b5210109244001c1d0410042010b08154010108204061813100301001d940b48043d200741e00c0503030010384801c07010964a07545 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 74181971 1250 74180721 74180723
    0x311060403021507050c0402270d0b0f010905060402030705040308070f06150302040e03280909060b03070806010c030207050f04060b0403061e060501021207021816030f0b0f0d 77
    0x4a09260701da500158944003030910a48540001280101c03d010082040f51200030b01520f045281118001c01000c0a8026901170700313113000344008440090700e80302440102503400200c03c0140b400e003407208440260003889025142411301021416900d003920889000b03095513203030680b801c0d26568841600d5042082e091301c98007204000ea1012a02600480300210564190241401c1c00c2d481004100d03002111300d02e6003a44248421719401c10009a00c0040386200c400d111010394225030122a007140503008640d40a00706000024070302a000701071405407190781c50702c50f915039511004456485201d140640140d0141004103c0d5013030075400c203203405602500110701035849400c48000d81d84641d00841e240c95407031440c0c0001346c01c0305c0c26404080d00d240000340152071424000075642c40c80914030015140d070010700c0c10110b5036404000000e648540c0d55054040c45c1003d0003c40d815070401003100400d080114503042c0241d03d104002c0c0c1c1c64801004064800c6030a014072002c0301087c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 74183221 1250 74181971 74181979
    0x90a03080a1826040509010504020f0d0e0106050f0f010c140c120c090105060c0a02010503130b04030804050d090315020a03020c03122d0601030b010e150408010509160311 75
    0x800500049038a910800002e4000e840304001c2100d04000d5410b01d41e0101c0b1500710000d800c0c0002d0207660380b11078500741180c0c0200c074056142c0f400e0300c1900016201302d00c00c09a02c54500803030b0a0700828190010400ca4008a450020750b0320000309220720b1302803445889000604845200300014100603600c00c10103402022507035001401c201003444c041e134a2415180035448003499156900c2c04040310b0740501021364040d03060807181820aa5114110040241801004400505c15415428031443c81030340103801065581481d04002e41143c0e419541501d45002d41c96500035024000d403410011a0b6002e0420005e9112040c4514000c1d0041c2c2110b4042540803ca4180000e030200701034101140c0c0303c8480035690418080422180c4d4550350550f8190001d41c0b030741721041d5101600703158001c400b82004221928003000494a00d0035954116910203400301d100710784640c040003c0d1003035400000c000c102d0703600c6030b64099565404640c800007592204e06001c2c03001400c00c3c2030355448000c002d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 74184471 1250 74183221 74183231
    0x609010305070e0a08030c06010b0406090605031902030a020705070503032106060705010606051305030a08040b030403030b03071203020f03180d0f080415180b0412050a050d02060717090a03080a 85
    0xc80050030744455603100303042607840410008a190008e10003140144085041c9a1501d443c001c0f001e8003220740303442240140074001c00012304a034038405072002941c2e69484210342d00c0c6404000341009400015003a105031144c03200200daa03060000445100c0c102407000103502c400907081465880300f00070606030b0010f03401c1c011800003035024000d90740500810344955489003c06910a400c40c00550b000394401c0d4400d40849000c140c00d4011201a24401e0074100e03560b9445040c00e41c094080607921030f80510815000150079030890034031182c01403099090340c3d00c03a013060980544d240640e002d00480101c4c01001c04003039140c51190404550700c10320741c8910419203500da4200a0b04190b114803000400810360320180d5601810b4040e1700c0394505549030b48142449240d0025000703034084d42c0c802103941c0241c181481f0301003040e403184a0307004c411202c44032190100291550800d031000004540041000c82e16110024145413042e0881d00041510300b520ba1022202c500010b80a01d02e829510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 74185721 1250 74184471 74184497
    0xd03020a06020d0608160302090117010e0a030801080d0513050616050703060b0108070c05060f09030405060d021b032110240801140303030103110f130603021e060901030507 76
    0x50000d0900c3c1ca109501c0007440302d1810000e60700342031014400504031900c000c002c0c00140d5070120b0150544802030480c031420b030005800e140c01003118074407004441c82900540e10401d94000c1200781600d55010942d40900c110941c00e4420703000b2480c01c14280202c074041806071781059400f80181d800f5032680e01010a015485081c10f04803c0d40098030307055111003201c07619580000c12641c00004503c2d00072241c0015480f00d44e12a1000f41031021031004a2000c16072080c070400a0b20042c100040a01d030380e81c94038400500003540100c80000d280040f80300c19949121021050704d0321101070404200302c4001c2d803000aa0850350041620018094003003012448a01a42c0400d0614615070301c041b000c00d208010241031401c059103c0b034401c0300b4044030282c450301e000c41640e0459520011920030340d00100001101d09411201c9a42c001000c45950b0400b01601d401c0780049a0003542c90401c510611070341405a45100216103400040401180c500d95100760300203030780030040d0320f004030303220f110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 74186971 1250 74185721 74185733
    0x140915090f0a180b0f030d030c0e10020606030105070201141b0d02040303020309090c03060a0e0603030f030f0403030b0f0105070b040c080d0c030305090606030d0513120606320d03020a 81
    0x4240c1021908500c40d204040200d0018841d04c3c80704d8004a0ba605581000d00780001d0b598450003008104154842d541c00710300c24000c070401e6203000c0000344080c8101e00001ca00940d618011100f5030301c84e60911002c550520300600c64615100b591030004074141e929010000d0303c41003400040172032004202b0191452820300d1020b00042c42c07007607010b19070b60b0081804001e19404054a04854060200140100e07a030380c80100307400b00e409248a1049660350701d0002811402200d104020016001042007040d041440740d642c0305503c02c0e1001c0008171288400c1c04000d44485101d107000ca40c0411102d0b0100f1003c1c000030b540544a954002e0542c0d032070f600c55504154240021170003052104840d003040580500803640d001c81100300500c202e181520000745d07100a036026210501200040c09407401207240543c80c091f01154030140c040e0445031a01500170300c81403090461080222070b007468003000403108031070f1042401194803007565000c02000181c0c0703055001281540f065051036400104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 74188221 1250 74186971 74186989
    0x31606020c0c01030e0607030b011803060b0a090203150609040e070e15040e0a020405060a090c02071706090d210504110a050a2106060b0304060606140915090f 70
    0x1204680241e11241e0000e0329038640901c68003218185410108100001d81000981035409105454040b4246882d0001a03500e0150950500d000d900d5070a008802e0013100e401a600c1c0141c25256481403655446500080b8041550b06000c90b011030107462240386800005070994100003040091035000c8101480d01e05610380d400400e844100d8000c208054144280301060004281c8060000b01e0328207113101d84480711090000d1040b036580707011880c16224102d50502a01450004002c00c203403a40f0040c0d60b07004180706001c1400304032a0710207642c51340490003a0050700c140008005a52690704240c980c005016415114001540a0002098014015140140d001c0c1700c03600103042408041c4a90344141c1d030001401803800c03000c200000a4805030b4174010240d407414018141c92189841c8001d01301d6540701c600100d00c00710500c801c0c071043c2da00040450300c0c01e85860b00c02c400c88000d50301003805184180c503807081c042c030a059540c0000d01c004081c40400285001019095400011070403c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 74189471 1250 74188221 74188223
    0x60a1a1e040803070b0a050105100801030b0a02071205250209040f060e0706110c060304051b0303090d11030c04060803090d0c0504090f05010b0303070804030602090406031502090a140303040b03090316 88
    0x41782e401d041c005c6106ca113103d114050441a54440803d0031402c1d4003610940d4184001000c0e41c0689001a10026030b680c10b40300010b52020540088100046004245800c83d52000b004070011400704400346c1c240f15480c1050f0303035003c6d000b10460764454444030b00780c4118440c02e948403515101e14251300c0d20107203c0b050140201d40c80b0078000d0251441280e1400c039141c0c5000d0300840d0200140400b24600040490840642480e114440c440c004040703819070060317408084d00194420300010030404510901a40d544081d0100c4007034404079800c010540301a8469004550401c00908003181043c0f483d04251038081e00400b4601c03a40c0c1e1010a0072501954400d1718044821085c00c0c00b000020701441c0304200c0110010b41c02c09155440d080590f02c95880010002a40021f0310b542946a40c0c00540045801c02d20340c550041404621501940c0314507da240b080c00840808205050082c0074520000b50103001035080604061a28000ba48050403441413031005000700e240c004408a6502015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 74190721 1250 74189471 74189483
    0x509030a1e030809301c02030a051f140402091c03021213090218091f060206090a030f0219050a03030e01050601020a1e020402030c03060a1a1e04080307 67
    0x3001e1801d00802054010b0441481c641000c03900d50010031070200c0c0a401a4291085c007840048000d011022034410621204904061120084044641c41e0b0183d482803002c0c090030310103607480701480c454108a911448000c1c40c030003a0148203c0b205040100b80140002e08018a050399030400980d24000e138401000700954402000c1c010941e0501404a41c490a030405d14240012201c03000c074042e01c18010303100080e0b8081954030750130703541003015100c0d000044c1102106081204003e02406812013061943e0744e82038400250440c030000c0e480d071003036078050003a12b6155250754048920500070071050b8210b00c941e0340460040d00b20100c048024904c10340082c501d00c100c07481c001d020303035000c03050584250b40340004101e4540d0700440d42c10440d50380034624282038a07114041c01c40304029590041e41080c070102c01c101501c80003200a50003140c0c122050104996248940300104c0d000d0100c004110506004554840100c1040310401a180101c61400c00e500d42072a0340c51a04855000d60366 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 74191971 1250 74190721 74190773
    0x150402040806161e0c080304060f0509011505060702061602120304150216030201171b160b090606400906061703040605030a0605100804050709050609070509030a 71
    0x14160811280110031413060450040700c160090050b10100f080c00b400b800c0444000001000c000465000510740041d9003810452030600c911664020100120740342d0030380480b100c000c912413812509942030750f0303402406c013881c1c20388054401d842001c000000701d80240c18013141c3c0040321400d01c00741000d042810304810b400050003900910380700e0940c05c280b0458015510520150f41c1c01290490030300c3e4542c40c4007200c2c1e00c40c60315400c400e02101c0d0880d00030030307000700e0782c0840d030303241c4602e050700d0341c1d000c0c840d9034079940c9909919030b80320003066404982c404d81c000031118500d640e000c24144c5074999049003200744a200c40c10840c0022030350100074100c59503101c01c20100304d86403040300040d20703207030340c3d490f0f03040c005908a60790300d2049025100c00d00c200031000851005554010310003800000c0c264000081c020318010b004100c0960702150907014460002c910984a486400c2c130619000700342d00302585a0150650b8140e004ca05441c1d018003c00204402080c1c081c0d0080c41d11410919240720 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 74193221 1250 74191971 74192011
    0x180902031c080a06120602030411040c050d050907050a061d0d060605120a080307050705070f0b0301031e0302070303050a05090a0b090103180f0209091e0d030501060f0206150402040806 81
    0x104140e00200f0303a850007841c000c42408030101e83c4812480300781d40305c02c00507541c0d00c071410004214041c542d40c103580310b42003040044d42c096101c80686000c1a40032001c0c00a0340f2540c805644070300c814007880f60400e6048808000b998032450f07041e42002c295200e6054498a4000031880b0050340c4401622101e03141c000801c800d007841c1c00b001c400403000d40040e000d100800d0351a500b080c40080d10110030405d000c620007003800801d001c00340080101015040016980e8031412081e82c10074032058500083c845442c1804649813441078060960550141504606650341602d8a0300011800c408020052060b01142e03240c140c0c18601a124030000541c0310340f5070350001000e6030042c0c60050001c1f01c880f4000e0002a4000700800308242e070441e204805680c070010060300e496413000100c0e10b502c2540fa42e48607a88804522256020516601840030784c1c0c84c0d4900307490001e1131480400050b072002c000540a6428441a5412044005c1c4090318055403184490300d081d106452000d501c000d0581240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 74194471 1250 74193221 74193227
    0xe070509100309020d06021b0601090504020f03060f060409030512070306080d020a03050409090f0b10050a0f180c020c040e0309190b040303080c191d011107180902031c 74
    0x40392500041c0307000e0200e85059804555114064440140384580220380030f01c50400001c10310f0501f85230002111103940c2d6418401018000641301603000d10707419841c040302420007141c444e101d00b80303040c4035441548a41c0d00b0300004004000702901000001d00000f40c1a40c0c107034040303d004508a40c0d000c01c2103400d10030000e00b030500c905840b605540c0f044124a0000b0b0304601660b00300e41d60088001004106402c0110351610400d02c0200f29003021820080312030009100c2a041e60429191440816241d0000350361241040c020168200c0492540102003091341d01300035090070350751056954074407107000401c0543e0341040b20000d458001040c504814103104d1022815050401e0382d0b0b418891409281700703800d100742c2c080036040111081c0041c4181100d03504540e010071a005100b00851480c0800a00199400c3c070341010094451001e400250704c182240b204080104001d011070500d06003216200d441d60001071411942c442040c5c030090b980900c02c14400d400c800704940054a0404402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 74195721 1250 74194471 74194489
    0x201090821090301090807081b06060105090409050a051002071506050609090a060e040b06030d1103031f0f1d070c1113020d051602300a090e070509 65
    0x3020300d5104400d1501010403450701400c240d03004070791003039458000e40e01107030150071078417405400c2e03030340004a2800700113640d0024119400714004060814500804503500e0300300503107840340090824021048a4030f4541d01071076809224504990805000b81d644504080344141a03104456001c243c2c40d0a2103000d009840c49911522810040207050400086060041d604203600940808000a02c038000d2540000090040e10491034210710f03061070000c0b03c458084600d0340c080c1c01000f006000d540e01440e1165003e080c91005181181d40360a00202040c2024550003204507040d5000119406241c0490000e030402010314900e03840300015101c0c9001001d0000010001c042074180e0128a101c2041c818808044032500001180300c0003c030b0180c020700042d0610f4901e00400e2000c020765814000c9001c442c1d40e000e84001d02c4e1440c60408d10140c019600040006401001000708401b040043c0b813080c801e800c240039483d0b29102e01240c0c2c08811a40755011980004505690f4540030342c030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 74196971 1250 74195721 74195729
    0xc0a1404060905100e1902030a0b0a05030a030c0210051204050105010807051915030f020a030c021b090402090601020f0f0705010923010309050f0a0302060406110a09030f02130501030b04020109 85
    0x1d20490418292404c107010491240a11241c2d040c00440d03020582d20031511045a0303024030964980c01c041d51540d00809070309036081c0c8606156000014182400302d120100e0075095281c0301000480c5800740008090074006100c1004020490301103040c6c0b002c0c01060045000e0300000459604007a00c617841c00346560030403440b41c50818010014000000ca54805803060500300d1840310390f406009501405090be91113400c1d81c00410380721010395241d884198215182e5089422108280c501c3d804040c402802042d00300742c550740000c000d401e1003a40503800900600c1111410a0301f0200c8a08001d01c1c0b18000a45810102c420001c9603403104043c40640345590f1070141043c0000a0213041c40b110900d882e050646844c100c4051140c140441000d01c4010300583d42207150a01d0002d46481085a01b103506900c2d00c1000041010081d0980381040740a880f003000c05800c5441c4c42401145900040340e0220001302c5440d1000c11074001e40d030003148039412046050416100140145030755400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 74198221 1250 74196971 74196989
    0x30d0815060f030a020a030902100203120c040503121e12040309080114070f020a080a091a070803040f0f0618150902031b01030f0608030c0706030b01120e0c0a140406 73
    0xa20005a01031411250800884400181c6c0c3d40f910b480300750007078100668082d5000100401e5402019004002491f01c000c01c4004525a9507030b5101e010071038000c0740100780c0c040d4031030001e0f080e40d100c8440082c103502c108404103001040035a10301060340d41c841c85208200821801c00c1c0800c044c0c100e900800076062041c000c1c40b8407103001407035001e0020000c01c0b440030032494110210301540244120091a5040740d002540d41540034070281450f80c141c841c0080300a914008407070f00e04100400c2d110302942c070409003469611203440f0740b1580d2074103a2040c1c800300722115646000030524421440074901141c3c495910307400c00c3c148003d001c20103a50309e104460414440000580e00030402f500c01e440400312020007101c110004800900d000c540c82c10085188c130700c0c0410703c020000050400401c084c0201c642081e1030394000c805842a40802501140303c1168608500f10260042000540c10b1000c0b520000c001c1d000240c07007520564000840300c1d40e0b0b000350616500b09809601c01800190b8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 74199471 1250 74198221 74198227
    0x3210501050d06050402180421020f030a030e0708070909020f180109020c0a0524070c0305030c0d02090603040c050a090603050a0b09071505031f1202040f0b030d081506 74
    0x1401140000040440003444155130703000103401c40d5200c000c1401c0e0780f40c00242d210039a140501e4a285003004880c0019400e2a004604901c0b2a10014420040b04400b002850609403d81c8064010340100c45d03040c0404e01450300e012492602c01c01c2440014149020081414400760041c02020b01d42084c9540c096000840d400d0361058901c000141100e1911000681d07a002c0c4030041e03403c14000c20700041c014014002450300803e072a5808540d0212500c18451a40e1280036055a601c2e200c140018046442800020b40781a00c500c09030100344200200949031040c004002603140d881260116620403546034103022074100503001d8000360a030340c0420010141940c607415503c041101e0000c0411038084001411108140200c200070701c04460040240ea034040703070251070703500200c034581d03010703c54031280901a0801e03240c0c1c1342c11240003002808016900743c003488040d01c400c0c0d110300c0a90391103003404842a103013000303151002a110ba44100d5241090512103521070009801107105800c24 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 74200721 1250 74199471 74199479
    0x6030c071703010501020a110102010617100506030c09150a0909080a09060e0618121906050601020304050a0b07050a0c0603020d0b0f0a06050c0106050a0603090506090609070b13050306010303210501 87
    0x1070781f1040160801c144071940044580100e0161440390000c80c0c00c50f880c1700d000d0b44e213071f00005042c19a85117000800d0005030f07903260130b03d90b44025180041d580b245000000c949075000c50356880090301c0024002010326500d82c41d05405482851104850031040001c0e90701d00c0304e50040c2c40d1800703081140341a00810380317140001102c0f4001e00c0c2e43ca40d40300b01ca2030340034030040d136070101d4003181018071406541c2c40098100043c1c1208803082c005440759410900003582c0c540c030110444050780c40003000c8444281c14a040340d8040d4120314070860f440e02c64030401501082e0800302400061645560150fa5030104d150148142c0fa6001085c60140454080c140d0b00c0790780b01401b010964055181c01512000d41c0f4090074090a402d5221790b80000450340003103402c603490f40203200d01030b004a04590498865140c04d83d07032810120f07909045900290307014400100701000600b600740e4045080800591a07200103410007000380d00032000b040e540204c0030142250407214a031114010b0301e0400c469850 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 74201971 1250 74200721 74200723
    0xa0c02180405010b1504150e030a0302030403020102070b03060310090302190c140105031e090703060207050d14070302071403030912060703050c0c0a03120908030403090305210708070309030206030c07170301050102 94
    0x5540a46c03102442909005461203204181c88d10a40a0050844854980c00d080103900c03503002d800280c0c0180a07070003000c1030106600c422a0302448001e001401284090a20074005020584044046000c2c0418a40540e1108480350000750701440945000070324000031345148004650703507141400014001c211000e540360007140081c0903810003407190f580d650f0040508041c00b07a00003c249501c04121442400740000d8403c1443c074403502c0b084401006600c1d240154000d143c0002c0040e8405a014072948e00c00592a40341d100014003182d04095513540020f441044201c0841025401481000002c82d81801b525402a801d6080325151507aa81156030720f91154010244c00c1c00011800d2032492940d03544154211604018801d03101d080c03903d4020b02003c1c4d81d2100703640c10301c65488645040c07030448040d1440c10070b048164a1400d405951101c4450308074880503405c0c8502c1d85030000168591400440c820560342a03036a907a031101d0b1501c2611851000416a04110180300500c80c42c0d030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 74203221 1250 74201971 74201977
    0xc030f140a05060d0c0509090c0a0305010c0e0a05030c0112060b04090911010c02031c02070b040b0309070602060705040e09010207061805060109050106050904050a110c011d06040b010b0a0c02180405010b15 90
    0x4007030760f81c0e0701c1300d23660310100310f01d03001a00c141c6c5d54101290050000900c4030640c0074040030002ca07034948652403003d004124242246004141d0325130030568107a0340541c06030b06c3d5031003004105400410603e030748843c0c03119160440e0703018101c2180c4400c0354500308641c1e5941805c44c00f50900703201c0c1340d440d41c64001c2540c0d945040500f50b203d0034800c080549a60082180364001c000c041c00c0503940e56111240c10429410580380001d00344142c2502240300f50021411901c514060f98030b45040a20f082d400810445010f080b001c1595420071401001c11070902a00f4031902c5001c200346400525840d103246031020580c803501156203070200600600783e01c80120303904600200e6002c43d4139100c0441500003400400d0314140c010350002401c0c84048010f4004201c100e5071501600c000d01c034250010b9440f89021070b0000c041000e61070041c8552010342016110101d86031801c0504e0302101ea02180b1416000364048800358520382c01c003c1080002d000d5100003a00644801d41055121208c440140c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 74204471 1250 74203221 74203229
    0x30301050d0f0605070c05211e12010e0f090307020105030a0f0f0626030921030409111201241d0603010f0303090b0307120c030f140a05060d0c 63
    0x89081d24414000071045000300710341c02c0071040045040c10034000e000d4041c001000c0701c0e00c1c06101d03451040d0300341c0040408400700c1414403252401300c02c0d00381c035008140080005541d000c82400038140c6506002c0201e40600706020306000d1030304011100000000c8000c084003811740c01001b07a400180d0303101094a411130407010340800d20040e2100407402803d090a101060a40307011400641b21590075240b158026040c1d4103070b0b8800814000c1c041e240e118075010240c0103160121448d000303102c8081c0c2d0703030071410605050700d00b0541c50340c004400f40d41f039480004c100c03440302094540c1410040c14105004003100d14a88250981613619000301411b4a4489014031090b2241764111400b5590210360140004110b9a643c0d07850311103107501003c0760b0000358002030f84a01d0202d080c440000c03c0303d008544548880c0c0c00a2203180c008000751001ca40c1000826440b00304406031503406004aa13085803440c0300703122441c03605010f240c08454004040c103110f611140c2004010511213201e2105403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 74205721 1250 74204471 74204479
    0x60f0d050a1b0f0e150a02010f0b1002060f040201090b13180506090a0509071205100c020106050319050c0603040809042d1503080a02030c06010b1215010201060b0a09050102070504020c03030105 85
    0x2c0142d000000f800031701000340c0c60341c560300001900d40f8819030660100c0c4d01810b001c1020400c505215050050000d5030b80c9403040075038800c03008502c8040314203003003a80c007a10500d88600c14545490f02468190015035426000784110541401280030f4955500c214a8030280100402c0c0f400700002045c105024200c109103e50b500085102c0240610807a0054551a5a0000041c005103402c81d07850007650584145545486003c1c1d103000c3c818000d280071900001c006200f0009112032184003c0d14010b411240341c402d40e8000c400a032200c201440c491030007546001d8850001d403080c00103549071583c0f031200311030b01207020f1100f05840c00c2c1c241d02c0700c44543c60001050f4445e000442030000c103e800c0079142c4403000c591117010680c00001070000004520a03114640d80c0c40340302000502907110103543d58100710000801100b141c40043c423940301d0500c000300380c299454040700e01d80d901029000c000135054072800e00c41540c0410006004100c19101103240152450034581c6902041c0145442 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 74206971 1250 74205721 74205737
    0x30114070c1119030b010509010815090c090f0402030105250c05030d020f040510030603030e01110a1506150e0303040504110403080408030d050106180311060f0d050a1b0f 75
    0x748200b0000e190322000e000b901c62290700c50840c030002988821440120762034501c210004c40c003401c280410030704a4141c3d400400130485041800725110b500140004110b00ca24407110f210707a43d034400202d014941d00090455281054014542074410090465454885049040c07009180c1c441c40200080403d02c3c0a11220b0214605141144594080702d0500e81c00420031707151211503030740240101c13041241d00000120b003030041a01170381e10921018000c42d01c2d0b482d418800394026850540c0601c040340039200030101d260b4850259800021400c00c003980d940360f0600c00034112a604000f44096070400c81805109400001d96030b100c2d6002e00c600071902e0746c1d102420545250203607006140d105030901d880b26140c601c056521f400110011041341d05220000a1040c0540d0b030b003030340010051106180c05802c644803003864031003480b18180c1022082211011a00500c009420075459000020034035050800071340c41910849946084402180c041400905400c2120b40d030781c0d280c0900b49061 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 74208221 1250 74206971 74206973
    0x703020c010f0204080706020703170d0605460312030204050d05010c0207060503070c0b15130e070501050306030703120201020d0906090308010f05030c12120c06090705030114070c 79
    0xa402503000030203440d800d10403440c280030304075000340040d10260700c1140c11055590f0800caa82d1441403001a0100304002d400140c491210030042c810f5000702140030481c1680c41c000f04035004c2c460a020590034103050b014804069903036055600304000c211410725242e2103401010341219051100411598465800c005c040b8001e405807401854000e0412800e1091802c01030b02808900c04d0440041c090340c000820350328040c80a0b01c0c01042c40e0f41c1e5a44601610355100509500080e21004020070f810410f81e116990701d02c0e590401428000c1c0206150300e41052041c64a00c0ea44c000605000c1c05100b001860313100000c3d03e0080301d801044200340f00b12514010384c024803030144a0b03d203060402d0030040038019140c108204d050b11981d141800390380e0b01e030f509144001250154903403603000203102100b01c1c0707002c20100311b01480c0041a5441030107210210304440c0d009040303203461900100c0800c00e5080051141d200240000e40007400031500e04c00c10a4043c0d00c0c01404507051044880d031780740c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 74209471 1250 74208221 74208227
    0x303060406240804060f0501080304060908070e04110d050106140f03150415060b0f07050f070b040909050c0406030b0105031207080307300b0a060507020906040209150a05190305040506070807 84
    0x391b140a4004802c11a958503000899103d9009018510114580010014914400042c0f040495100f5401d110041c3c48941d00c0040100e0880c54150744244038080030004aa420f1054100909510406c600c039040d1840505c101009070620451003500501503070841f940701e21601c0c81d445a80060202240e6000035544070042000d600589621070010480d40c800c000075000270903420380a070303003280c0d034400c0d440d20b01990b91038280c01003003090700d03050004221003c0c15800061102e841a02502c50420102c804541103070b803103074800d44038202c0c0c1e200100401c0c2030030311108801100141c044c1e46801510b803103503105d61101510a804110b40445540b85110308030f00e407038900c80101c141d2450b0310030001101c90060030000c050741e4452101420002801c070300a804594410f5405484404240e84d46c9080000942241c01c03417582010500d0180241aa01d200003480e000803640c640b540c1350904a142c803144620311000000501d031802080c4408030b200090016404502c0e03261010301940c03124000c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 74210721 1250 74209471 74209481
    0x5030402060d0501030b040309051e090705040923010e13021005120f15010e0312090301020702060a050a03060605070b041410060303020604050c0a0b03070305090a0f05030306040624080406 83
    0x500c2e907942c41d0000200c10080041d0b0807601941c02555035544403601d030000c1010207031130404004840b007100204140c2505020143c542e11014a0400d00d003007640e2550307030005980381c0d0142000002c3c140071600b00011007500290b409000010000d001ca8034229060040503c001c480180c0f1603c05020401b50103803241c403ca4222143c170180d400c146040503111251400c405851200c800302c464440c40f0f259500c0349900b4508030000400130074112406100b42c80442e48039458194255408004010142c0c0300d500051406000c1035076504d54070000e02500804840d0305410103010072104002c107602180d20000340c55041a080851901c09101906c1340900e001003c0c0340143c2102d00f0a035001091580214103648114010340030383d074034400d4841c2041504041402092084102400815803803882a440035a0262555049541c046103544034652041c0c5400d400711220f42c400005c001e014185801100e00810070b030700000120700e04142040036079007010b03030188081002440009060181c03a03008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 74211971 1250 74210721 74210737
    0xf0417010b0414190c050d0f0b0d0b0108070e0103020d0b060a050a0f03030e03010219270306050106110d0203030c130509040609021206060a050105070303020c010f020a0e0906100503040206 83
    0x82101d060600d0904142c848200c0d00040c075182130b48500c01e2040000c1c00f410341c111010350340d8585042c10900c9018005d040118030300710360b5a138920300e1001e03503220b000040c25854020b812500b0b00d036150180c0c26260011a8105a07034524000380100010f894401c0c800e91501da00041c5004a030ba0740c00c0100c0e022080c1030b801141d102c64882c0d40001d14801e52484001580c0c003954901403509100800d0500340d102e1000801851889040c0501d4101c2c03142108080041540200307010f211a0303081c1d521a4034120344c0085e40d0266682c0c0c01002401c2d000b840e02c0c80742d0f48950b805400741900b1184040e4403400004d180c114800310015008609400402240e0b01034240101410000d0406003403000c02000d510104a016040f1000e41c1c450700b030b0002501a200d0794001f40416501400c2c90011541500080b10440a0540034841c900d5120005e0041940711003649400581743c81e40c400e8002e201c2d0b1071400010340038880400502501d0340707941d0104441c0240d58200581d0360b4480c0e10100b0910b20800d10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 74213221 1250 74211971 74211979
    0x3120702031903060f1e090e0a0b040803010f06020609071401020a02030102040e22050604080706020d0e010b01260a020313020d1505010b090102031204020301020d0608071a0f0417010b 81
    0x20000d00d0300ca4040e4007400a6411000b242c000c0d035074586546e4420f02c88112180740000c040e041081001c501d003504040c46211100c2e007502e056042603914007181c00e1003660211506031003c001400300c8043e0192000040a00344000d02c0d00f0f0902529058031074546e405a01c040031400640491103900030014509030660107002155280d60f551803446c0c2152055071440d0201c0368810041c1e02c42d03143c2c0040202d20355001806007000d6150381d0b96094042d0700c1000c0482e0250340a00c00741a03c051180f04140403504848000f00d0b0601d500000140200c0d4036080c8003043c052400a210424900514940d6005d90b080d440140c2d01d469121000866003200000250b2110515511a041045400b0410300c00c402008040c003803030740c0315100e00ba042c2c041d540d40e0a00691040c02042058800440c45030b400a00203000185401c001585510664040e9000b4590682c07028000700058440d00b4443c100e4040c0340c2c01210308004030151051554425480b50040b42d402100e40030002e990290712020782010024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 74214471 1250 74213221 74213257
    0x120603010b1c05060114010f0509040b1e01030506040507050403030c11030a05070906080a08030a05040213050a1a09070f080405101505040f090203060105060f0f030f091e0312070203 80
    0x7245001140b4a0142100ca0307010340b4000280c008201500c443d0000016196606060705203501250290440d400880d4029107401500019464030350070110f03440280010f40344c421103600c0014003500c001a00d80c5004a00c0c2c0b00401184a5008040d1825241d2600e4854021078503170528401d0703038401da0000343d45030040c11542420040c0c0011104200c800c0b080c0e051100d903036200c4059495004018001c4c10080c410000140041d80c280d0045602a1000340118401c070f070542900e404840c01182d800e6a19139641c14102c0c800c04a0071a0991198822100c23000e1614140000620102c00c42d0381c01414405148040340400c0800d0180221b001c2c1c1d8250204178050403c420103105103043c0c45070340d00841c546050340644080074003c1c0740b5601c0e000360003408075904c1c000501c51260b201884c03c2c00c80c03000038484c1210300d00f4210f0096000e86100e402091540c14400d6100307007030141035410302651341c48121300001003030b0011044d00c103500142240d89100b0364462900740e013035105203d0120300c1000c0d48 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 74215721 1250 74214471 74214499
    0x11d06031807240f0801050307090b060c010e010606020c06040b07172701110f0606010503100e0109020a080606131404060302030f0609010507170c0a0509100905040506010503010b120603010b 84
    0x5003000c00000c481d59072603410b000c1000c0070580b0411703428010203401d42c020880500c600c1580d0f402403081004050b008600e00300300040154211b400c440d0659029035121081048202d50400400107002411144c1602c1c02c1c1c90040b44c0d100512070504000c01c2c40d070100154a050802a100380c450030f6603e28285403101000d0114641c080d40d0501402e8007240c0543c001205100c00040c01510030161a00181900c0c1c030f813140103540d550401071100c800c0481d150700c0403c0080c1d90b4040c09000780a8417001584803286d4403405003001400819890042030184520304207206020a0003048905444003815031802517000b00c1c0250146410294141c4201c2285405003800080c10500ca1101d60008000700c2d11400c40499440340301d100b2032040d10b0201808a0020700c0140000c0600c502035081c8a4030b020300b090003264071034115a9210006c24086281041681090f014080d4400f0302403030118070319810b00720204000d0048543c4000c40503255030010304551008d40c40303552200c030005e1030328015010b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 74216971 1250 74215721 74215769
    0x609011e090e0103082106031015080d02032502060703050a03020f0a080703050a020309070612091416090209090a05060a0506030c0d0605030d02070e0a02120c09011d06031807 77
    0xf02205a5a461050706c202802c00d45080d408103005500040140c10a210000c00000107440d081c1c0c1c0d801c41e2423000b41e40010302082d08100d01034408c041c94021716159280c20314000600c1007007421142c0d2090030080c0e0300c8016a19030044039000c59150829039280c1d000000101c2c028091085540d601610000303800784180d4101b441f0f503104404d20f42d41071010f950380400360f00c1a4042902d00c1125a480031405021300340c00303030496004520984000050088481d20744004a0522103549580d5070040400315160501c120030300c00240009800a500c2c0200810110754140c000516540c0a180d440020030030346d554040c924002403800407c02d5440307081041d0340c582c42e0703407289000711501880c0c510300064904010650098404840e00030b485500d00c0c0001c04640303550b0042041e029181e08010114608181c4000310703000300100000c441d151501c1c2000035202c40b0215030f182d5040a41c5007800c030500c0d80c5840481c1e81c00302c0b1141342509490851407101c3d00c0c006c901e401031010306966105013250421 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 74218221 1250 74216971 74216977
    0x1909110910180207021f030c1b120f12090302070611010b06040e04020a12030c03031119030b120a0803090c0a180504171209010b0609011e090e010308 66
    0x200c5045825440da070045041030109485005426201c1410300300880e891030340604451070019040c42c032080b20000200180303111040002c4042540e50b00000c81107603000410200a0010313040482ca03040694980c06440c02003c0c07080e4040010a039000c0c041680701354044000c0c3c075200e00040c00700700c0107450007a46407042800340030009a40d000d0350400400050041901c0c200e4058200c40c503240c10001b0304104d0500040060740c2064201c04009491140c030111005050700998401d020a28a0324009040d81d080160302d00b0200c900348118102da540d08044545800c0890800107900811100400c41c00c64200b54211500c4c000d440800051004110003184201d01c000180c941e28203400b0b00308405802c10340140d0908a81130a0542c6904410ba0b0205e81c001d4000c1e50500141c004c480700030a403941c07089890041c01c0b0711480c14008103020034087c1c0e04000304211145400c0019000000b03108054015048210f082c41020094160340250042c43c05426185d07042c0001e91307103a04001c4120342c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 74219471 1250 74218221 74218253
    0x2040c09061202040e0412030b130506041503020f0d06110406080a0e0303010b030411040f0c0c0506180c0402030a02090a06020724080420090a0605030708060405151909 74
    0x11510b05418105040380e10031207007034a44844100340300d40c441e9110010a200c0c0445c1880915644036500686541c5d03424541c0f07249a000003001c940d520381203040c0000d580200015900c02c84050700c041c001039030b584850480d51501561003c5901007541001d00280c030807032021111500c0005008107445a01c018402e20809440d4400e10514540d00b103195070f684000d11a0140031242030008c0f500285c0c000001076051b4900078000700710025050800403c98090108550110311007130100341c04c001c400d00003694080d00c440e040101c45061100c11035141c0141240c0b5600c03a07a400000948052030b01d40c1503842c1740c6406085e2010040c1c5608001c4d54030602d6000304030700c100d400c1c5660030494040181c07510081d101d60f6140002911140e650100808141d25000c80815040d00602d00640703030081304e540300b82c0040c0c40201d02d80c1c0c98141450300303014082c1c00156590300b260b02040042240000c05041800c190010030710603985002100440c00368507400c2111050608c080d5130301b4440712141e440d03401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 74220721 1250 74219471 74219477
    0x412050a080a021608030a020d21180311010507020c04020d020d05040c0503100509070303030207020d05101508010e120304020a150203031009020a0e130f0e0318031b1c02040c0906 79
    0x110f522800d405031b50340100840c500059100c542585c0200e0700c90100020340c810f100a00390303480103540d00f1040545803151001140c90004150b40018150f000707800d00d400000c600000c204600b0a2803000751a906400031050040380c00241100c0d203a5003503070440d054030008000410940c1841d240100d0030030054841c0e05c0c440c1c404c004901001d50542d2084d00c0c0280003903801020780520f183d8099002e0340103030400ba680310103a0041032021800c1400102c18103c940d900000b00d801a4540415040129401503c0280c3c900050821081070014600700c2072503070038000b02c1d12990340740300081e513900c2150000001415036483c810740d001c0e0000050741c0038402178075428240382d40b0307442c200d0122700a109480000900740e0f101c0f040c0c0c3c0d00f03001c0000c0e040007441c0100401c0704140e03445c0e410261403210102d410a1740c40028404600c024111020700007960860240c82d00030f00b21042d0340c0381d040102004038030a0310b4901c0745482d00081d103005d841d85194090800c1c05003152010010703203284140e200b66004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 74221971 1250 74220721 74220763
    0x50105011a03072307061503030f02030c0307020906030f0a0803040309060f0806010c03120213090e01050601090b09010e1509040c09080d0305060604080712120302030103080412050a080a02 83
    0x4000c2107601664401d083c1a96102c0d1580803180e003c191034404c2c0304565412100c200301003404540f00d4029030b05c08899103152014001d28601e80100181500c44101c41107410521280b42100c10100c01c0341c01150f011160b016650b03c0da8400a030520361403414030700c4248031300d0715030354100032400003c1d500c40d90180e20b64040c450340c1c40c8419105204000c02c1c5500003074003000011690b6000d86140e0050b01d01074a0403045a0240e0411030b0102c3e071100b08459485510340700d080050160500070140c54420180003403205080c08000039040355118000c2111552020500c59207d0348601e0b5a0444090018450380c034034015400c803081d050b404944400d0049040c24030488a4034003411046081b503c4400c02448001b28410b001c034002c18001c4e1842c0d038050800c02000840106c20080e5002410014450104c0e6000b2072800300302c4407840c50801010b150040c0010008540b200e0282c80445180c0c4000780b42021843c6002810310b5145440240441404128206d103d41c0c0002c0010564803200c840c004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 74223221 1250 74221971 74222009
    0x40b0406081b09070e01050703020f0d2c090403050d0e0601180b0d120f02071d01080607020703030207060f021005040501020d0f0218040c180303021516020a170c0a05010501 76
    0x80039501100c0480104079450174014603540b1034802401400c3c040d00c180e8002008e600604ca00f4007250150380400030303144d640450310044450030306004aa1188000030041144000410b00c5910024009010301201241a100b404916002001500141c00541d200e40da191440e000110070750844401030b00e071420b2000d00540c1008418140202c0c0c00c20b03a41e107100103041804070b8600407407040100860091044c0041c8030000980c215020b400c1d024051002507041c0140d880c507004008120b80115482041e08001094010034000d060b101146040b50030f458036140103070324206002038503a070060300d402e0411050013010350152005400d46a01031241500d041c40c804164001e00f24800c8a101c902c2850001d82c3c03900b54041415800113040980252000140d5000141a01c1c1d0050b80075812070010791040028071100d4a5001c0910000000c00c1c1140c101c0081d500c48101c00000c1c69200c55242c4208074000404c00c0c0d0341c00c440d17400200d84000f446882c043e03000e80b41c203100304032803d089026910 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 74224471 1250 74223221 74223229
    0x30b0409051b0604090204080d08071404030210051c1a0103060b1b010608060703090506010f032a1211090f04021e0f0405010306090201080703020c07050f040b0406081b 74
    0x20545a000300080c010222048824010a920500c11070f9100000300400902c1c8103181c00900000d041d52000f8040034035000700b025104900017030001d4204030000c44c02e051041d40200a13039094903010345015500ca84451702c1640c41e4898900400104560100b035030303502d05002c2d0022800524a008240d134414034000c010743c141c4d10207000e102e04d0001c044c02030078040b05c007101170305c840b40d20085e0001c182582d0b1040d8160038500d05a0b5075400280c0c840c4002010310100304803042c0140050030111003160302e140c0300c180600745101f85100c45140714645c1c076074041c1050781d18100508800300c410b06e01c94030f480c5001d80440d1001c940844c010f00401000a081100d1048428407440d00903020454040360414240f0032808070705040d65218000302c1c0540056112480b940b4069842000000340700f80e002d000141c0040c00040401003018010801c41c0744081c0c0c0130450301c0031a40142c5030011120700050014026100c660a415049860501c000980038800100148020020840318a21000803000e01c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 74225721 1250 74224471 74224481
    0x2512031a03030414040605061606050f060117060a0e1905061905060307030f090818030d120b0f09040b0609090304050a0e0403050d110306011106091e07080601090c030b04 75
    0xc980d064100740300401160700110755204064400420009103143c59100084458202c00d080c456625550444a402c20446114075900119076003503001c0185003040c0024501040c190b0b41c0300702904035001099a58603540c40290290002c04032181c45841c1c96414928941c19002003045201e04040c0401c1e410b0904118500400302c00e00c90030302055040c101801001d500c0504082d041581d41d0b8035003020110f583c410319034481d104464090396000301c030516507403001051216074801c1c0c021203811494681c11044d000408014030318007280c0c4a004000050100c081013488c0c640169803081003008101051251500c9440300f104c1e03030385094442c820201d540b40250701810343c1001200c401070202e4213048400640c468441d03d0528684410b02c2000e0094980302d2140c00e100702004018400c89607040781c48101003407c1d8100070481403030519201c45d80c44128808c42d42d00b0280568545901320420300803c00030344040e20071a1680d5948071006d4000b07048112802c000646400d1809015150501070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 74226971 1250 74225721 74225771
    0xe0f011b140904090312020a020c0a050102060f06090703020708071406010e040b0403080c0d140402040b04290409050303090601410102030c151b03010305070308251203 74
    0x20281840003010030f0100a0019110940920442030a4010b090f01c01e400141961078a590140060107040d03024401810381d550450b5040d50841d408020031110902400b0343c2c0310718129003c4500ea2503286054009100b0054090040303a40041d5039410710107520201000a8800e108131551603984240d1617041d50816540105645421030203e0301207407250042e10740014180304c0c80ca04e44a05181807804540048807000807a21104080000b03510780343c401c1f0320140d48256000c2c0440c1040d0724000c0310202e00110a550301038a0403110a103a501d555020481d91036207c4c040325a01c2c2017128005642315402d02c40c2c6c00d00a441940c40c1c5d05046056140d1110209141402040d1280d03182d454060311856034110741c0c11440240981a250017042040c4002c44c8660407001300d8509254641e0050407190001440c1c0c0903201b0001080090030008940003200d40040d90b044e1141d02d0580c8c0703203503482c690104040c1103040d0705c038699007030050004203e20b803070711107880800081c44149240b02c3d014006075a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 74228221 1250 74226971 74227007
    0x6031407060c1211070513050412030618020c01140c0d06080307020a030b1f0b040503060108010e12030c090a17060a0c020d0e19090b01090e0c1c0e0f011b 68
    0x5078510f40c0e1070042610381603800000d0190f0760703031903202da0101d0a00306140c400c089240383c49400340000d1045050804070540d1040c60705000407402d040002d00c0c1c1c14400c2848c400c0840d070004a00c40c64250039072007102d409418050000c0b03182851210440150803492400700351750b1800d0320000d61520b0000440391003980c0500880000c82c40c0d40c0310341201d0600240081e0341d4000c140b82c2034840c821a10306500c050840c0700f144944070307400d01c8207051a03c0380580025001c0c0c2c0c9810800a00b586002075004030044000b4030065403691400b01e81a0240543c45415030013208203840400c6034081002410180041d503422208030b0350b258940401a6000d0300341400246e003200e001d00e813250b1b01c15104101104000b41c1181c20041c1401d44403c281d0785d180e0320403040b8650710ba015106540c0c0c0000050020000f100d10325a503803c1c01e006000392440b0b4510110004000d100041d40d600200342c215019000300d00c000d0b40c0481200d48074a502a244110200500324400b500d03d00b580d5028048100e5400a490 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 74229471 1250 74228221 74228243
    0x61a070c090506030a060c0917150a150b040305011b08060f010f020312040b01063203041a040507060905060406020a080c0312070507020102070918020f011206031407060c 75
    0x208070028a40902000d4140c01095602c5011034841e000d602e0032443c80d9640c02c250f0a103016040340380031424001c0e4440e140c0009034120480d408120225410643c03105d0005000440d2000c15000c01280d0703800407910850104000040c040c06520601c000c0c0072074008004094200c10040320856000c440442d40710483c0d440c1d6480c2540b01e1605905103440500459151209201c061120813008441c21689200e1130b03c01800b080764011100390402d03120082c0040340c844001d603140e4090402c40c0c248017202d000400001c052204942c0044619000c0f6041003030349040900704691154118000e88000c034184000000786802d04008890455924dd03028204148042c0da600728140c3c848650910548414403050b201c01204800c500e0265100303448441c3d43d4085131001904003102544101e920a00e4245203040f054519241110102c1c0d0440d00034514098040050310344441c46840c504903213140c6800801004081a00c1c144500b01500407521000d40d078441c200d40d1000708120044c1840004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 74230721 1250 74229471 74229479
    0x1204091a030d08040312060909050d140412080708030a0524060a12020f0316031a0f01050a0c0b100f05030607050912010b0616030f110c01230d061a070c 67
    0x2a00390f1030380291003032400e424030060310407280d000d0b80c0e0310790401c2c04007a40d610785003420050104140b010010190800e00105503850322220140c1c05079218202a40002000d600c0400540c01704075410300358011540c9440e0309007440244010281140d8848080d0720620701c00f02070300f13a020f4800305081d000401c1d60340340c01c101c550110380319851a00d04c84e00c00350f024094510800c1d400d0026522424003402500310100083c00014141c0b030700034a041801c4040d03201d081c0515101c02c000d00c0301e003007000e00b071255451540d00c5049480001061005c0c12040300031052003203100d200041d210440f43c08005802215458000b090340b00c01040c0e550038045141000556010304015076108040908440005000c0b91510003042c3c00d680285035211504080741d003200205900042ea00c0d84008592800076004c034003410f0143c4e03803101040180341c10f01112541003030840d9203c8032100e242c12484a0442d0b204c0100036050700c044e1040340030b0b2802c40711441803612290b801c640c0940380040c1c3c20800e103100709854 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 74231971 1250 74230721 74230727
    0x12061c080d0c090302030109030f1205011d090a0210021b0a080303010611030403060507020d03050a020903060103171611090108120403020607080906070308090613051509070302031204091a030d 85
    0x429030300b0760140080d9040000251381c0a01c100010741c0c2c00394448228081041d4001231100e22000441201245850010b104220404120b081003501c40160003286840300d9982c42d15000080500070740c00300b00c044907410b460b5404075016203460604520311142001c400100b20a8003031074001d250803a40301f4001000858800c0002008101d0b40030309881c542500c83d100e03541030310800c0ba011405079111171a209041541807240650120000800b141082c8040f000607071140d00610014021281c400207441e02c512341d91085610f03804150714512103c03080c0386442000e00248042062007a107843d400040c003004003040313084418415164191516042d9401c1180075084a0410b65100205020f0030543c1d850b114000c2c4841806911951450314040b1041c07071602070010034a0b14507039919410100081e6000480b000c1d5106070040c5417032181d60303a0014034039042e03003584007a5040c4030391200c3c0011000410010000e4420720311043c403408111140d000154200958055010743c81030702c0000c0610700c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 74233221 1250 74231971 74231981
    0x20c040903050403140309032b08040809060a1d01020303072a08180a1a070303090213050c0c0d0e0a06080a06081209040e060f011208090612061c080d 66
    0x310900301603040c644c076600d9401a140c3c03003030300407803c651000031081700a1804001611250312200000300c0440c00b206880340b50141c1c03021406003440b0350390001c541000540f13402c0e00e401030b50141465854140c40007008015680b00c070903c52011440070481c0320154030102c2105c0c03080c01d05071582c0300310756104202030000030310024071901c80080034150100051040c034000c114a04480d1140300f0b01c5e14500c8108910b894183d480103804001628183c0200081102565089078150400040369046400802e410400e842d0901645520345410803811010b000c001d0544c0c588814120344e00c2e021203503800c0c1d0741c00c0c2d0701084865001e44031103000c000a0340b0402d00700380d202c00200c10128040d40d0700c4d0b51b824a050104035034a1256003001c81d60100604182c07041641207050b281c014000ea0410b008803403050301060040b6004115100d14801c1442590003c81e8204200030700540c5c1d40b080000802c41c4466030039121244100b844001800c46803805409111070740341c00a4203e0300e402899030203840102 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 74234471 1250 74233221 74233223
    0x604230102030a050105091609150e0604060c0308090102040e0604020306040b040e060a0c051206120708031303060e0d0816031e0606030501061103071209030b18010b01020d020c0409 80
    0x8000044542500001c1c000380d4058102d2072001324403541043c0070442c2e24000140b12000d00d48103400c4005d00c4962001d034440031a801086500c00a420b5080d04844020b0840842504401d00090010710154440080010f01e4041d55030000ca988407805054242d1085104450601c46402c0114140f0b28040e40219017143c402000010b00034514404038042da50b00307401c1500076800c41e00c20403000c4401030203241c049224514043d0314188503052400841e40e40948018000c1e04010a240c800000070003441002e01107030411661a5452013154003030854050000321102e60400b0a030f200e003040001940321442d0500d456106041c1c4d92000341c4425103038904d0f8078108054999141011144510300407985510f089000410442e0a1100180c00d440c4181e106034100a00c5a0311400708000c00300540d19003543c0401c03840d248852142c0112151203042d00094a80007031041440340003001c0400e00940c4034018402031212002200059880d004840120b4000d6002400c441c07100c2e142580c01002c1c45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 74235721 1250 74234471 74234513
    0x105090f210609011401120206071e0203100905030a0c080d0609020316091a0711060a050903060a1104030b0a060b0a052503050a030f090204020a0c0b0604020c0604 72
    0x50a0404009024401e0840100c040c1514044030304009520501c8003682c484030440003803102a02000075020707070102c1449010031040d152640041107603504021a60035641190301b0303021700000c481c00d6246010030a04200d100e84100400a6440450390040e5407013240c0200c007450400d24803034820740ea507041010080314510000c000c4c1109904451040c2805030490354801a1203185c05554940d0121241c0461000d00000d0302040024241d41226090b03035880e1176400740c2c0c8500d0300e032403c86040c0114800007030b070025000c28901400c6601c800a00900c1104904403011a2298000601100e004180a4407144002c1000384085019924456080802110f000480c181d03039070206081c0c0e070030841c2c0580c0014400501c13001d1002c0000f8026003003685500c24150140c9581da0041c04034801c107110305c403c3c10703101c010a0408034003c1c1e018602d8079401074015503640c2013854008040d645003400031a0b000e040702d408112141028800c1c1d41904c0740c90740c01031005807129251018000c000352903100603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 74236971 1250 74235721 74235739
    0x30801090902030a0b01090f05060303280e090f061905060f09010504120c05030d080702030a03050612060a050a0c030912030b031f06090605030a050709050c04080a08090a05010903030c02010509 85
    0x1c0c0c09008171a00070081480001804080040d42d4010369402a016911035071051142030801c0782d0400402d890040020542c0000ba06440010b5400c1044009555800f204240401030b0034034002d40340512903141101e1000880900310309583e2042500c2c040c0070342080043c440d07898a0882e0000030611380d00705041240c20039076506040f05141d07440f000c00f00c514111902003000541001c10004039192210305049100e0328104e00002d5580c0031704c2c05860b080603200e034080340840e20340c110f00c2140285030b202038503001c3c0750464a002c0580b6050b1822206c3e0703480c101550104522911035014a20352040e41c0201481203004210302515859607015811300820651003000742d00ba80f10301c1600c0c240d201020503640c0c0f400300d5003001c176489648218000d80101981600140003c1007140a40f404120005001c0c8c072214140c107110b00032604000c01c68880c5000020500200c2006060680c4080b2810707400251644011500c1700054400180482e08404c80c14005601420280c480244045c017043c030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 74238221 1250 74236971 74236973
    0x1b0e01030e1006080c0105030906040b0406091211190201020705060304140a060f0b01050301060c0b0403030618050402030c0d0b010605032211040507030209130905010b0402041e060309030801090902030a 89
    0xb0034000c40b020320500c5540e8803501084604001e0241d4030900c40242045402c6140c042019510380c0c200400080060345040c001800304280c95011241a54100117517082039118850023501c4140d864050254520030074004448580890030b03241541030b4180e01900a42d45408148003883e00301030411986040310303110a02d10710404201641e0400d006500200708808050807000407215500c0d02e0030304001c4100010300c20981c0060714101015408a880303c002d07a01c47c1421001000c494202000103900c41d00210120030359a00680e010790b000f201610b200c3e80e14002080340191014030010b0100360342000402c9140c0c040e4015603408440c2224600e0a00b84844080782440100d010842e00c20284032501b248504003803003500d60107402e5080031450201841700085240d01c410501000c030b80e13114070021042090a401c000c2104401600c1507446586440035034142c3d800040c0701103400d030040400043c0c40380c824080d0360342464052300c8e130270203903401c012010300901040f420030ba80600c1001d410310 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 74239471 1250 74238221 74238223
    0x30b0a090504150e0c09070c2a05040b030d0e0105030403020a050d030e0d0801081c051c0b01080906130b060303070f080301060306050114040e060a03060507170a1b0e01030e 76
    0x1a110b03920640a600c818001502c2400840d0020440740d4119070112000841036100d0012041d00040541424604441d031071070203d0001c0c60500311420841400307500c9641030503130010b00b801070301c004407001d201e1a0169001d050351035101521501c0011407041004646500030002160802d02910540341c04403aa9118249840060410324000a5440e092002e8502e01072040086e004014a089102540741520303040d542c500d440c0b82c1c03c1e880511201640c020724028070443d4980d40c0c2400f104015403840008803c0207090300b01085000c249401c00048800d078000c10001e01c5080c44000028622103142c80701070000c02c1c028006601480b0801545020407010044c20700c4c020705c0350b03030099038130360400c0c0004041e00c0082e8003040c117100340c142d110301d607403c1d0700b50a5400341e60034030004a6541d5507007030016440c0000382d44080c0101d0300d0013013070150340755029000c040c42d00824914000282c80300742c242003c40340c002001588141c82c076034144500c541300314165802050149030108002012015403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 74240721 1250 74239471 74239481
    0xc01020403080a1716050c0c03010501090905010c08040309030b07050c061302011827061a0a1d030d030b2106060901080a08160c0b041415090604030201030b0a09 71
    0x9070340b034200c045244a00203901141c3c2c912451005000ca40e62030501400800e40b58603d141880b003400000b141402084504005452643c8001802070009513504c0c19031200038040603405440650802801c4a49180110302d5540950361683c0c40581030340c40c64071200800c803405001d5a080250420131414144010031200d4010541d810400302c144240d0b100240000d2a486030101c0c3e00000e4410030801082007080082c481c01ea052800e006440c000d190017401031005070004c00c04004800b00c801405500c81e40030b0a07004005450f0b0441c0010f40342e0241d0794010000c1801541680290030498502c1e200b600041d404400240c101304600001e40c003a16020143ca4003003c1c4154411420000c0524041205030b0041c80c00704003070944400d164403035400601c21250704e80c0c0c0130f4640e4070030368040040c81070210317009006100802d0f460f80e8a41e80010b241044100d09a481074801d026107001e00e07508a0102d802d40f8100400540c505861580194054030044d200309902c01c1400701c000404002c14011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 74241971 1250 74240721 74240723
    0x3030f04061805031207020603041109180c1504090e07090e0f10020a0804021017150f0406061e11070303020d0f03021e07080c150106020d0e0d11060c01020403 70
    0x2d00c12401605500300e0b040d00d00e181d40041e1103940454140110581110215441c903601a656650b50355505d0811000c1180000c080030f40149405040140d008500020031800398081000d03030341c0007483d54080044180450000313180d181000c000410010300c0c9980b2148a03040700c181a148407590b2017944104580840512040c00d8000114080380b9880a0084d03100c0812a24400c50410803140070091006038021f00c000e000740c114010040300c4601602030800741d6400f0400c40c150520b0190340901c550f82180c1821405a240806034803510300e40381c00762400340c40095a40da6200304a03034000802c00b0400c0301e0350700300340301c110304103403006c03490074003010340514020f400034260b20700c209100400c1c00c0d44072599041010300c148102c140140c040241140d0b0402003030301054940355a42001e03c0148506ea0f1208103511410302000044000e5460150403100c2c00e809031104026014000e5644e101e51180080d0700c51a003041040000300282c040c030540b140080c004a0034681020986422640540c02c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 74243221 1250 74241971 74241977
    0x100e04090303150f031502030921040306050705030420060f0f0310210602031b0d090224030c030403050403050703150b04180222090c0e0a1e0b03030f0406 68
    0x20300b0032540400c0c020035008100328804e0802c581c0c076544802c92501902204098410380020100f000303e48100305950302440d07041005022070a69150426040e4044e110480d1024105000110303414094801d8a00c0746403c02c2046403003010030494410402c2c030400d006540103006000103400b100300c900280c0800c4e4401070b40652b0341d080800d09640080e0241d8005201421454412840364074041e0411308419805540940c50382c45030710442d4041c0e03100c1ca882c440303100d402203030a8071014000d80250000c0f5001382d1300181c0c80c000d124a015480ca20740e0380044002003041020602039200200190b074468000c2c5845424552665221403d0140640c02a0340c442c41c0000300c84081421486080010b070b100b2942008580070002010210b071004440c0070388105900c141c8102807001e014611b030080000400200001001132034501030301e480500483c0740702004000018021101c40c03150b804210080070190858544101013540500125031000ea010b00007841404029074041c0702400c09030410391 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 74244471 1250 74243221 74243231
    0x183b030c0f01050105030c01020d030f02040e0a0f060902090a030f0f051c030606020d0f031503020918060606040509010b07030c0606060c03020f010506060319090803091606031109100e04090303 85
    0x2205603425910103170080d9100350840f500111260382c0004040d0f0081d00301c0e00f00440c1c40c003520303d2210000e00a540c800f801b46030080c8200305078100c196000d6002800240030400230070b9140d1198034100c0c0107100038160040040c060620124580c18401404c0d0f91203000b82051582c019681c450914005600d5600004511105c0d50346107030709401650003810f464802486c8040c01e13003000410807099010645d0516544d22083c080743c003201c0102c200a117401801103d824108410301c480b4440b1080507100c190f003c1c0801149003440c1c410221411100001c1050843da428000a0a4a42e00c8950110140400d441800340006c1b103d00910300145003a40341d80c0c2d10050207040103801c1841c031289400c000d914110800c0041da0b41d12007625044600240c055410001d529644402404e020102824511003c01080282c000c0092405804246e4109151070584d980500342e065512480c900c510250303041c8010300c041c0c01d1442006050320801e1a0803049070840c50080f40c110b80004200707030002501c41c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 74245721 1250 74244471 74244493
    0x3030903091517061c080406020c010c0c060806031c09051309170903030d020408010c0908070608060d06090605040f0501050c0c0303040f0f02150301183b030c 70
    0x200c50301d0300900078581c0c1d4a0300450280c0009055111090030604141620004504580c40300a0401c4440001543d10102026141091070036504540300d03450040c424014001c4295204981c002003031540010102c41036801c1020642d0b0020005040d90307014400c0c03684030300c1a040004503042c032030072007a100c0c0c4081600740400d12002c8581c00c004480b80d1801d0034407240004d01c0f01010940d1440c0f015201e03070749580040b000217003144100c2c580da01c041400840c01040014040d80003000d80740858503544c0520b45e0b100c0945444907864498400411120000038640b82403001541c090540315440c0000c2030510369446400b100d000340e0302030314000720200102c01004401d201d29504a011001142e00300802c3e00d550654070312009000a2070341d800228448204015204c8201c8166801010a40b800082c1030680758281c20074459641e410002d030300302040b8005180b05001780c411461821614641c0b4910328403145072001410b49403842031080d816580c450052001c0c0101d0300350384c0c0c09843c82d9044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 74246971 1250 74245721 74245727
    0x908210a0e0309010e030f070902090301051005060f0a05040e07020a05010e030c19051c0503100b0f07141006080a150e0604021e04150602061005091503100903030903 73
    0x8020a004451840c2034416151680000305540341600b091030801611074002000c241008107420b12074601344600c060100343c5050b42c2d005040d80c0310007070340204490b40d070344000c01844200610582e80c010400b08034865107480050010910000b5500b0032900c1c06540d0240001d98041c100c039000c00580010301d42c2c40401c1801c2c0990442307080d2a80043d81011840e26100d6160090700005100400055150904100080c0003480d10202007408100900001000c0a85154022149108141c49002010440c65903d1050b40c00c50341c002e0701c409040035a582c3e6042014840c901c283c1e00c40e8445c24001a07040031603070261002426005001d0300c0310f1000c40c034040c0d0403403009681044181d4206044201c0c0d26000040040d4031580449056a007004544005c0701030641d400035068100f81000c10031010300c25208a180c007110403682c2226102c1e0380c0c001c1c0e01130000181307004087d4001580c401007200c0b12420204802a034200030180c070190700e68540304508592810320100c0100392194014424960 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 74248221 1250 74246971 74247037
    0xd090810050603070909050a0206120402130e0c0904080d2d05161b0506130b0a2904020c01090f02090903040305060f181609060f06090306020309010908 67
    0x41410428003031800d00d100000e80364203440c040e841d280f03599034465500313111042068110b230780d13000b501d02070b6100c0b200c10010b000e5a90403582a40204144118102c4643c0c2c035106078020944204082c0c04061031510401410120240c03081e2924070051100c1400c0191a01c200c03038a090460b0080c0000c0790880c030b10b1b10002045003095218991401c010001110075002180032110751501e0314519030341903550300008001008001a113144603040400c440c0a0a83c1c060242c0540200f0002d641e0780c0e11010070400703840c9252001034056002030105a5290b607419103541c44640024009410656140302c03090841b00030190503581c0c20400440c020a40c20010842d07508441080302039850141181c664a54850024145107212a00c1000046818460742c51403098014040e041d01c10354014040019601000c50090440d003a01d041000100c0d0340000302010b0842d0b1041e111011000e155480c0d84000750002801c410465480c1d030600340010b03084074001d1070b050340100c00e06d9403040302410000071102 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 74249471 1250 74248221 74248243
    0xc030603080301050f040212090f01052d0a0609020f0316020604030801060503220b04020a0f0f0306200a050409240b090102011409010b030f060417030703020c0d0908 73
    0x1450014103001040c00030080324103403181503651181c2c0c2c510b00004a0300900c5002e01490096201d4018011041c101180e40150300348020001d2040392115540d021180741c40c952107401d203230481d2a10b0011780400203012544a502c0910014500383c0c1c0f4019403040c0c0e403000c2c17865000d81d0400020401040c010f0513041070600070901c010820303490142c0d006072071030006001e08000c0c020003100151741544c41004104411080c4000d5088050f00c1c0d1900c0000303407109480403441103808184c007043e05403240f1441c40c1114004984108008d03d9515854000c00c185207201b184800c11810750140390098400a0014076050307078400d81e541d454156000c04403810525505040e070b02001007141c0851080f45c0760416114004000b80c0d0314150f040060303004200c540541030400070701b10300b000400701d8107500c1356103c808107600b80e07210580c9211203551070383d4080fa801451903070201c40c103110113041d00c005182c0c4a1901e040040c48c11b4007941d8800d02d4070030030680010025514900a01104c0f0040c4a022205 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 74250721 1250 74249471 74249477
    0x5100e0a0b10060525080d0b010e04090c1401030b0904030810080102090609010509121608010b010207180c020f0604050106031106031302010f020c0a1206060503031809040c0806070e03010c 83
    0xd41440ca00520384e00c50000328260a4403035000490020b0108249900440c1e030015006c1d5907180c2949403080604654802c05011528803126003880303041c42c3c000c0b240c003241e0140806030300b2828031031038131a14201d07210301c40c0c10165158244100703038858141c4617000d980240c0303d01c000b40c07820310f81c280c40342061a00b0054a990042c003004406840340019240318002c00d0030803d455074442c2020070780d520048440300880c0e01c03c2001c00b480c0180199107da00380e0700e895000348a610b0140005a903921000d1269070042d2600200c00c2e02c00010300e42c0a0480094a841911209103e07104114500601924117454a9544000410030040003100c5600724032402d40d0014158075081c2120038110907030030406030500040348030b0f8025141c82840601004080101290399164a401c40070b400d095040c84201d491900c0e04c08041905e2400000355140f0948498491101842e80c1041c020347c414041d10494445103400404510100c091002610130130055613030807442e8003003808044c00d46921800310028 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 74251971 1250 74250721 74250751
    0xa050a0b0705121611150907060507031b06060e0103080a08150607020405090106050303072319110103090204020a05030f0f011203110f0f0f12090a05090405100e0a0b 73
    0x83c80107501c5420351140d01020b111407081d91031035095411103050b00107a489401440514802d0132090b02038540a202c041c0b00303d49049460304070a0301daa2190342005800700b1003174200720000d0010320710b2030420f880c071800020594541c0c605c01d045a01c403080c0c004803444a008150b07602f113141d005031000e5000d00b810211140d25416800400c1c02d03807141d8240071740115150000161406025040740c0000d00001e821203540d06031500b40301064140241ca11107032003416102c803070b802c0c04000030116003025044000c10b00c00b002c2591030100b24480d200e651030506440d0000d010141c1d80314809001180d44607110507a4a140410140310400b1005260503180315007000140508801c0e60004203c03d0b90508141100e882000b0f002803038126001e5410000b071040915001030340601140c419890f03100c40c012115030542000d0b802106006418a0b1604102101010055840c00d5002c541d041400f03442540d030850703039010300ca009481c2c0d114142c40e80e079030060704e11004000e01c070000160310404039400290 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 74253221 1250 74251971 74251987
    0xf070e0a0203130210180b0a031103060901051e0603010e0603060702010912030b0a0b0703090e0907030f0201031e1104051503040b040204110408010e010525090b0a030e0a050a0b0705 80
    0x2e110f07180c0740040d004008a849601c140d0f030061070103482d800e000c41200a100d640e520108421039009800e00780000c0d0602d10001300c5da200903c180d038080c4070010028107840e802c0c0018010031042c0c0050720882c6180780005030001e0b8a44000540c04bc10b00c240104110b480c10106042c94054043c040108680c13421094401003070714565040c16001941c034001c295501e403c00040c54804464011106845c07000541804058001001c60100c0707889152401d2155100d0001a40301c3c1010300c00907117807030020030308000150700c00c0c0d002c005800444202242400780d1400800e085800404443e0140000040d00f40020320740300da01c5070440e07240314850510354900750b5984054000c1c0904004e001d140c60380308086041350700200703031005062854020801c1480d0403080707901a00b41592141504200c0034420001c030401d0b4200c802c441c09054070b4462000303140000155036940074049038001c2603540c4401a800150604c0200059030142009281d00040390038142d9241e2400340401c018080100013080c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 74254471 1250 74253221 74253241
    0x140601210c1d031b01080606040506030901020705070602070609030308100b19110c150c03040b0a03150b040b1209070b0f0d0c0512070c1707030f080c041a030c0c0f070e0a0203 77
    0x41c1209401e1030020304603251140400c10318010394208ae9844180402040000c55055000e0015940200c0484e41250303030f90182662207841a02580001454000040c004a400740c078160382c0002c3c20101c0700c149665580c0e22485160800c03a05025203c4000c41e40081961703108000c440d400b100000600580644e1200103032520f02240000c420360007011030b90642c0090117009035401891785c10382807030361801403801c010010031001d0181941560072034004600c02607007001344c038242c8000502461520001c4289549180c00082c0308417041e04c1410340200d280106c4d04060b003110082080102c1d203d07800c03511050305491342d10075103508005003400808070240c0c918603496007080d0350b414492084c104078181206031400d01c0b2181c070074400c0006445030401d548041e003035241500940c1c03681581d84038201000ca01c1c0c0701c0ca100c1d400241d242e664143e21320b00742000055400041c005e00b01403600081e00030382410700c1c61210344030100740c0203444100810700c1803054880d07101c4ca200004606d1843e04c00103407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 74255721 1250 74254471 74254513
    0x9060405130902030105010b0309060c16060f0e030a020a050c1905010c0f060203010308120702150a0c0903150204050a2112030906050a020301140103140601210c1d03 73
    0x854452101c24207500d0000c0c50070350090010702e4019000b44220b6840381c2c10744619074401d40f00110340e4803c03000060700c1c03d0071000c00d46208544c012414002400d0580742c1402410f15504000c0c1040c8ea103284040084000700014001888640c0140c81d807e680c0b41000c0c1d003007120840d41c5500500c520b2844801c401c0781403400f8400e884003424950b40c034960b24201603c00168010000b41503600c000000310501581c58082c00041810081400c40c82c0d840c81c004a07241c8203c0f00001da12264204042000c0c420307140c0080504030b1151400854041d5a929800380502410400305e042a5000030148001d040c40c02c8520003034145007000310402daa0400144400012407040a06540591000c3c5610035210350400054150030150911160808017810740080d4000e00c180304411090300c00f608180d5000e4028241d070300360810010b01081e550340c0015104104030050000d40d5000109603144101003900c01c10b484000c0c541d513135110200c9000e003000e00680914411601c41d03800b0340c894510722880d030054 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 74256971 1250 74255721 74255729
    0x60f0708040c080703060b0a062c180a05070806060a1d0a05060d050f011a030406050c0705030706050916030809010f090f090506090117060c07081204051c020102090604 74
    0x8400d9141e40c450500c0708402c2c00c503801500060040d0180041884200d4004058000b41121005481a91104242c0e20702102101c56000500d10120340c282d28251141100c0e11000d014021100d450260b90289406200031030b0540a007075136403c1840703011644410310560000050f6080d601d405162200500444107010440c00400f40300104666180c54085044008103400703002d42d03850300c0f5000c0001c406030404488210540c24290300001305403c01d426a5000c81c50488030f0540b03192101e0b2540005050b00400c00380312510100725100c0001c0d0108000e1095a003d500000390030300b4a001b44500b4030782136010844682d6a81601800030807040e02c01c0350b0005d0750900741701c0d5200180071410707103a60f450f5a0000c0d0074000650301c00602e01000d034021a1040a003103602968980e00c514550701d04140155803014154840c3c0b000500c01c2815074001c240c00c5004817152424040648010700d8055001c54084503d9000240e81d90360310090854584000c0606000a41c11b12200c40b01160300c074025482 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 74258221 1250 74256971 74256977
    0x80705031b03070e040f03030c02061005010309110d15050601021c0309050703050706030f0b03030a02060708040c05030313050907030c020d140d060b03070f05040609030f140a140f060f07 82
    0x300c40100b07075020000301c402402049100d030b08038076203424841c2e600c1c1030a080c15404039081c5495002c4030740c80841c1e50381c446d0245a2003151001d0138100110014511904100c5400d41d080c2c0c0c0009980e61403001414040d031040c41c02c16103044500000800380d50f07000e00494190344c4507001c8245070344041c09944a40390341c05e240009510006080480c81d010142d4070140c403601500d00040386055158210b40159054408103011050381c0d13006044c2d0342d100b03030b0034803000503004907011178004c40c40703001c155400c0380c02103003111a40d90319400024115441182900da0b21000343c3c07010000340c1000c4401c01c0e44050241400c1004181e6080041d46030020030704888200000c05480000341580781041d56100e4280d000204100354484400600990040c0d4501b4040750303070050284440f038803c40850b03064404075030350140e01c00d1843d51604412000440e08a8003c001101e20b4461316408116801c81075009444841d6460080300b041418050040c80c454960740110342000003100e04000360942207042d610f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 74259471 1250 74258221 74258263
    0x80a0906020706051f0f05100f02122d160b07180f0f08070b0a08040f0203030c0706090911090d030203090904080a17010e150105091c050708070503 65
    0x450203800070702c1000c00040201c0c3c5001c0038400508103403540c00d88500c1084002e0b0042c240c8980300d59190141e5445850307800710404060624092285516601342c1d00103004441030810369184905050304410001360980f003151690303042918100d400716505583e0340607c0317031802d040903500e807665040c40100904007951000109004034407a0a0007042d131800842c4252603207442d020102003140c1684105030716100b000703101103680b0074042440e8084510f50100180340c403041c0e0b80d0580d451940100141c48030a2035100010144e11b05000030300ca84400070000c0c101040c01d0443c007a16600540d0040300d00149001a0500c0b440340c0038041383c2c1a61700485110624503070300d20f03089186200e841358440d00408520140705c1002901d00c081d1603a010291200030407006e5104802c180a0024032900040b24840008100b5030b20001582070301400341803500314903100355075010403491828442e0142400031904c400c2810300006106402c00f03070071204054134840b89024006596440c4011980340580401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 74260721 1250 74259471 74259473
    0x1051f03051f03060603021201020a050a0c021309120305071407020103110408150109050f0403170901140c0d1a0907180305060f040209070e01050301060f0e03010207050a12050a080a09 81
    0x9091004540c11111081a41480d02e80c9050400382086100423801407c030811030f8003c0c10018001d480c811902036131040e06000910104907528a039481080e60007402103140318520841d14040e104220b0300030001c2409014100100400f2100c00400d021304115a40216085000e0700e1011903007030b07580911b404200d254030310220340010b210f40e078440140b51041030f6440b244c0680030004281201c1102004001580d5502c12030800b40900b01c0f00240092011140b0f032202d06a451941038109440100000b520400d10076141100101a15207264030007010030640041d400902a460410500704080740341010014040307212004d0251844091003d0b805c1c14000a14a00b101640155082000c5903500d05050400c200308400a0b503042e0b010380d0b880b034001484039003d1200134000800603550b8600d10380c40d006003254031150803140c1c1c2d403c100782d40e5002e00960f0340c240003520b0414000c0016000c41800c518041d80e203240411139083c180041801184101e941090380715070700540700c0d180801c040c102 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 74261971 1250 74260721 74260741
    0x610090308030c0f2a061e0109050c0705010e0f100e0601060503070c0b13030905060c0615041401030b090607020f03030a0c110a03080108010f0e1f061505070b01051f0305 75
    0x2a461317001d07010000a400da00b680c02c00042d88050685802003074440c6c03910b500c10105184407c100e810075600744400300400c4a80b0082d40b003107074443c00c1c80078114104001582d07031600f074858065160072250b000d03040c50300c010304050200440380300781040c0030002c10260201190300c2d0341051151a0900002100091805008500c0d0316142940090411030915111200400000103040290001a0506008122414480204c480310f0340b40d5001003010b0790700d01010942139011125510307000340d02c54400451000521034114081c0d44a130400d01840d00d004164246010713001800369046500455200d070089002100312030b0803448000c40031074405020032081c0c645118001203521a449000c0c2601c051603489001e080c182c3d0170600092007210030f00c0c3c0c0904180ca03480d624444c01504000c3c2e0100b18030001400c65a8801c48011002c10724a5540209140c0340c50260b90f44000700f8800506d060811034010700050142104541240181c2d101c107812007650b0003810340010906544501007864440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 74263221 1250 74261971 74261977
    0x6032a0117190b04060803090409030302130b190e0d08030a140a05040204061a0d0b040f0501030506090706080717180f03130503060103020f06030a020c03030f0610090308030c0f 78
    0x1c692252452810b00c1d5a228000340c2c02120816040d0386003032035088040c9001d004040c04c4030b200c00000c0d418114003804100041c012140d044060503401c001c210900009045000002c10300220519160291a5090022651f0341a00401000401100d01500c1c0e900e0112540c0c005400061181e08c90342c880c100000107100390159070104c000003108108628040c2e030000c6108502c02e4405205455980920310100d00600301c2005040e5014082d40b400c03042164070214201d44000c3c000709450f402140344408030360080c1c0081c2d0b00c3c0d4212801300400724108000e11001040e480c03901303100600d0b01a00042030340c0c1c0541d10078098080d4101c04540b010210a0001440a880c801940d081c0e41c4900c0d07800f940e0750f0019940c140c1d286c166490005040c903010684504076074020340820f404100305010000d180d400100030324803180c0c1c02d0181510460042014510440381041c1d056214146801006409011072012004000c000340b018000030700c41c2c0084d02d0b005100c100b44143c0b140b0000ba1200a180 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 74264471 1250 74263221 74263247
    0x7200303040306090201020f0a03121a120322061209030c06060b040801110c070b0a09030606030f06110913020d0902060c06010e01051c11060403140d0806032a01 71
    0x480003041c00b20a21085500050a00d8803d80803030300a10718903c480c6450b003000380c8028000c568206420704410a468224140c44850034400802c1c494030a800240d50b010007404003855544045605c500304810041c0a08541207810b00d84c00c0c02902e050001030055881d11072081640b40c8440240017014080d0307072440c0b2450360000062080c0d61b01c400300304c00541c0113882001d1443d0700f884070040001105000304c43c801e1518102405a0500704109400280d2040314401d0400c0400c41307000006c1007080c40380c071000d144108102090340c241070a0840076030303030015090761a0303400400080102d591a9074882c0510420380350056251800842468000c000204002e904810006506400d1002c0454031906070341101708564081d0340c8900c06c1c803034030b50222000a0000ca010a4854010400da140f419200642c000d051900c0c240d20390f0b45003e0513130a48003a480c03556004d2503c20000f2a046014198801025801401e000805294031000b608a141c9581c030801c1500000071003507440b8214400f915 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 74265721 1250 74264471 74264473
    0x112020412110f010f140901090b030708090c0108090309010c140f0303041505040f060e1006180e03030712050c0f030f07020d0e0108011509050429090c072003 70
    0x100440d003014400d0320101c4003858400c10b40c01d000c050896010703c0713000002c05115900c081d40501d110301b07009011743c4800aa941444814580012081d840500440c414003256903010f0460070480748084c81d1610081c00d071814089880100b151241d00001a40c00414091800016403a110b08040d200800c0074200301d80729000f0750b0707082c004002c80000118005c511440f0040640d450212001c01120800e440040c50072003807d100e41e000c1031154109040311001032060341c40707491328400d801046441030303441000080c68210b080b104011103031244c4c1641001041c051865480c0c080c2d0014215001d03076540510455464003c5100c00300700030140c540c85401d480a0b20356a05041c4617520b94182c00312080c0006100301030f848400c992154804c08a100c4e81030b141c00d6100d90a000700c108404402407440b20410103150000205035699014409405501c1202e4820016150b8041c0900d100082a118080d65110040c0075a2101c0700c800c076216540c012811451101503a110b000c2c221603100302190b45 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 74266971 1250 74265721 74265749
    0x6050711040c1110020a090f0f0501182c0a1e1a04050406021323100309020a0e0a0b0102010203010302031506061b07052701150507050105040b010e012301120204 71
    0xb0684c06030f4020010f0101366118000056580c0c4104854070f686802480203003d00040100480d501510200b1000c0c0c2e001070340e416025481c0c070001030b62103842000c680e40c1c60400b04000c0c100540c083d220340707402003441a4244208504030f070300d819141440c2c1d603084001a59031400b114840ca440c007004032004a004105100b2818a8100700d8040c2d040700d84806e43e01305c4140c2000450207000b00e103641d03240503111040b03e0004141410803808040e40708041e814142c40700f1061b00160382c1c444c032540281c284514060200d080441c0074104941e81103645505583c8100010f002503540041d50b00550f8900314401da0b510382c0c4940104006020f150076041000c072400c00c0301c060600001c80d80340c0a4030801c0e59005046115149545180c0300100c41e549001413220340148000310003c4032000300d0302c03201d041c10352500c14503948a50840f50102d07026919840558018000703c9554180a4010201c00442488000521090907078018a0340d280764140320308021941c40d4013104c0e80681e40200582d100b00b01d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 74268221 1250 74266971 74266993
    0xe0c07060f0b19080703020112020d1805071d0c0c030c0a03020109020301050609010501170a020405060a020105040b060a08030d020c1e011407080903070201030b030a02270106050711040c11 83
    0x30b444928145807141404285181c48100d030007445004030b907001c5006080702403840c0c00544580380401076480c2c540da004c01c05003024200740d003d0314900399503030103000025107241d0405500300069908420403c1c60100704c0c080703082c14511045034020080c5016643d0301c5440080461952181c0146a4510b0062040201c145034042d40115503240c0260021b0000d42e8404003000100b8009014031404160f0040d40c88400c0b00c181501264050311010006107051380380c4002503400e0b04482c480c400182c0d1158108400c0048200c04a9003000080e90300201683c20b0600300d5459004450301c00c50328030341c0401d500d1241c480c20004045075600c5104071a00d40f504442540c3d008e0302c0da41d15010b81c103090000c0400c0c81079118030f0800d4410708011000e503040ca003280e4011005010340c0400d150b4136114030200e0700050b036600f0304112288001320203030350038110705004400351001c1c050744843c007808003d0100e0004180c4810320603c1111084070b0000349210444070070f4803d101251440070075032040060043d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 74269471 1250 74268221 74268251
    0x9020a02030a03150302040c0906022404060b030f010203010b072009061207030c0902041d090c040b0a0302040f050603060901090b01030b070c0b0705090102120408030a0c02061207080a0c02010c090e0c0706 90
    0x278280d5441d80d00344c5502407520460024800041d1304113180c4010088001404074015520050700d011008081c1d69800900244903030981e0001e80142080f01000034020742000820200c04802031409103030240e81034159400500b100400502e418010f403403030750041c603455500344078040140d03501011940d200750300d4203c5100290403500803140d00c1ea07646503801c0700c80c9414080c0c1610a0800000400010f0310078814040603091800b0040d07041010b0b9100440166114010002e090f0342d0040300081c1e526201041626100029000e40c5003649000389003008600e004403400d040d070f500422620701d5a200c5040c01c6811208881e005040102c80c1ea05002006910000908610209a0071202c0d1401c40c800078103568412440340d141e0301d6004000d20084540200c020648460000300003e04004100020002c1100b0031140c0c000080c0d442802c211000103184a00c800340e45040c4002c100012000384003410011084c082c00c0d5120702010006410701c000070040701c9040d030748000c09100f440000c107005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 74270721 1250 74269471 74269487
    0x60902070b0a0b0f01050a05040905010b09091e01030b1b07050c240d0b010302070c06090503010f0e0a030c051006030f120f05120a0f050408070c09020a02030a03150302040c 76
    0x40380c1d11800c200106100901d00e0055a103410001019199144100c0005680c07075800003100c1014080c0c00d0200096075425440b44c0b130700900002115070341d01c5000342c041240a21006101003613008114620000c2030701c3c0480b0713080c10b50741e01001c40c00d07558540d00803150f56000d07108210302c41c0380c81c0000d00804201022412003a445030503a50700d00e807407401411140c001c03280403250100d40682840306c0c80c00c0b4030050308004846d21040c14010321344135440c1c0303601c0780244003900302c480800d01910081100382000d21074000340752070b495401c00000c44039082c00f0b5100c10700704c00003408101540302c2907010300505024035a0b4202c030348a8100002c80c2c1d686410b15100e0010482903481e82c01c41800fa1000e94000c0c001c1e401d080700b0a5a03981d15200f10a4105201d800340a0911400c861342c610240000d00464820680038900845942b5111005482e200c9480441500001c10b894010300c00e030102e20741c0000c10b0b903076860740504011804d0350032906a022a5010303a4000b070741c0b0501b02600740d171301c00741c1150310 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 74271971 1250 74270721 74270723
    0x112060b0402090609010e0f0306010e090c0604031203050618010f050a0506160b1807270902010815010c02030316140703030c08030c07051506011b021804020d0606090207 75
    0x814400c008910080004034003c4002c1c094104904000090080d885a1240000d0b0a00103081d521511026404030b85490401d8100e11420108041030140b82d00c0c08100c13802c080403049034172a25103411507442d40301c1b44812948210034182c603030010540329500c2042d0700402c5224455205025a983c010907043d50b081d42c801ca50140352942008100c500f00310049400c126103607a05040901440c1e40c400d0320101004241030641c80c40440c17481800001401340d031000700b480640648040100b00101081940a0150030080618100003840141d07040300400e5030002d04900c0549401d001d850040e10308907405400258035000005030301c0d0f522052035007402461400303440850003401114a034140d585540c0e010144c00720701401c03d850005411200107550203c20709844505160060781c9a03803416011113500d02410b04148200010ba5911800214900e24640c0c0a030f040d4121703a40114031413505c68440c0d0808d01d03c15070002030039501c40060384481c0c41c2d4411001c1012907510312001d0000d41003414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 74273221 1250 74271971 74271983
    0x5060a1101150906050a0e130828030b060a02060417070602040b04150c0f060207030512070314091204090902030708030c0105010603060e0402032d010c020724020303011e0e0112 78
    0x104c003180604182d00940b05139140080c001c48651600649081b154800342006c494041d000c01206048810103414003550242051040000a4800308060241d070490955070740903040c1030140c3c04d5000c0d8005440e5420503080540440351000c10b2b920300003540724103d809450940000740024903160248010011200070f1035244c40000e48054080b0f0f1985c6030b081d000f90200d508481c82d040803034459402031410504c41d003441880c001c0103035840072072524115a80001300e039407024400ca070181c070303800095802142480900030b0344110803090202c80c0964095240202d0366501407104548040081d030003d0308600c0c04890701c400419005034046c10f030901030100005e090800001d04d4801c01c0004c81c0c0120f5005000e485000928806034a05a40340036039510443e10404c4010b9802d00e00b84540c3c400f480300c80c0c1c00740203203609003005030030b43d4440d28100206004c0450940c4684a6020080d40c1c156040050521040c51a201d85405521074603002449101580320001501d05c889038030019032a40b2403a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 74274471 1250 74273221 74273231
    0x3050414040903050a1b02090a05190b03030a08061804050607020c0f0a090207030e04060605040305060609010501021507030f050106030e010c110c060c070801020c06071e050405060a11011509 84
    0x1609200950b100c031680240440c0042c440c29010600038000b82c070f1300402013603003005610703101d4002802480d8150340c2142616507070310a1040240ba003844202c042c181d20034043c020b620607000845d5480c407800c13400c14200024100400c50507583e100017040c40b0030b407081003182031703060a0520320341329030041d00c06030f016220788012181c032828504130b81d0050444c010501e400030707450400440081e5000706002c808204031282c0c11050f541c1c844c400e03c2c02500050b907440e504c0d00e0551400382d1902c0006020240f00f06070b854010003003607a001031407040c440f510380507184032911942d80940107000d9003545401c540e428280041046035060340a80300c175842d0a0000d0208200240003941e15150a521070b05141c1c0004240311100e06000d0000e0440910000031070310100c4d80c42000b9800c90300010030301a02e98000b8014442d44640c4046989041410801c0c2001d01b90240003003d04103219620401c3c0c040c07000415401d011318040e00202e035640c1d400200030700c20a80c080a0380390001c00c0324003580c0c661300c3c900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 74275721 1250 74274471 74274509
    0x130305040812090a1d01030809010e0a0e190e07050402070203030f030103120f081005040b180a05060415080d120207140708010e03040e0c1305060a03050a050105120a0b06030c0d030504 81
    0x362186002c680c2d081144201031303407c640758580140d0115200905021007564005090b0312900c10b220000c4ca9220080026420400c4128400c0c0c85129490a030007801d100282d0f4050f03e01042c500100c40c5d00f10b80060341d81c80e10344082802c0d80181e003148562410040000014401000c18031100440103030748500090101c03d00139641e403a419103422444096000d428441405d20ba84501124000200302c0100e00351325801d29044110115031032180e490706c800074007103241003600462840c80000040080a05d04104945996a01608804080215030f1117000c011068560403207400541204440080310800e29031269140010700c074200ea15031800074103c291800200c151010b0383c154005020081c4c4940c044003146800c11494103005420205c0006020b40d565001403030708072065140480c3d40d1034078000c44011181c0503070041340100d0704541e901e519120041001c90003d540900500006e84400300464504000100c8032a04007550b0703503280052503003260141040b01e08900609042100f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 74276971 1250 74275721 74275739
    0xc09060503040312050c0d06091e02040605120c0708120415020901020c0d050115081b1c021306050a06030e070f03030f0c15020d020c010b0a0e130305040812090a 71
    0x704442c040d00040d4900b10070801014241c0281c3d400c1180c05a00314149600407040104544d6035a219001340343c0d9800340005011703912542e05640310701c013a0b41181814500400a4114494103104041d180701c907100144520060000303032054150040322458840d4584946005841829941601c0215419281480c40307121402107903052381040c0d010b0300e10b0f44501c605100701e41e03200e83c0c1c04441d15501e44aa0891f0a2001d50404000b000c2c0d04000f040401c000049daa000540d03d603c1c418019500007828440d00c0300242d004070360703055042e02c40480916801d66801c0090204c3c0cac1085e43d10943d41030780000c0081d40364204251a910a80507600c0c07a03551030940c008034030303850f100050100704120101000c050003a008415514000c00100000540040180c0100da0024450a19076070380461001e4001801744207090803a4400e448541500e03080003d11161000010610740080c2c1541d00031408041c420010784000f442c00f03204a85211140e03824509142c0c10040d01180100003895000510300d41c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 74278221 1250 74276971 74276977
    0x90105100803040611030c01090f120201020304050d0e030a06050c041a070b0604020a1803080424020a290a1406090f0a0f060b13060f0201020403020f0d020409020a0305010c090605 79
    0x14032034001c524213454010241d550918444641140d4001400200d580e41400e00825059611450389400201d82034603069900e03812904c01c0c01d0441e071042c8108000107000289089050030581040c8402c44403610000c0c0c0f6103800034800810321400e0006108002500740090000c0e260a07400003c50400f00240328000340c0100307030000e45115010008584030b0705040c0c0c001c2040f0111031800447d10110389200b1400c0208640c07040b140120006020482d80043d50810f1100b5500e05898030341150041900139a00d05020303102a0521083c6203049100344104255100c5001e01d98045840902e019500c02c0c0040c20000c80d00d41400039500d0008002d4078200810510843c8910030f900c1c100d0b200c1960100041010310210481c0b42d998800c04522112590060024a117520604080c800d041607401007842083d12711030029680140803c2c801a55403107280f80d40c000003904c2c0074440400e140002005403000d10740203500020002c42c0402070207419080302000c0380e540d449110301d007a130380c4c00200c0f8184 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 74279471 1250 74278221 74278229
    0x80604021305090411090403050d0b040203070c0b0601031506031505010f0807120204031e02040c080c040302060705010f020418150513020304020f060a12060b2d040902070b09010510 80
    0x10107403209000d18900000304a40060150030352042c0c1800a10100704400000d440a81c00700700007007004012020306025000d00903006460070350541c200707840c0207030007080045402030a02d503506001400c241d120343e1012500c21511400d1800099a80802400400910000c010440329803003003c98123500039025801d001600344e85900c050342c1c8280c009c441c2c4071490400b03803221540800c0000302040c0c8481d01c00f81c0f8200755007030703052440c15a40b0410017103da04214200a1010f007400f0000e03e00070082c1586c0840c1c1c0c05440c502e03070b103081601d0301078010010005842d01d40c6201240103e468032240d100303240e00c0c00e0341400c02c00c0444501c016103c000d0201e4402c2c80ea001038100400c01020301d2680185403c181b001d4403100c2c0b00d003907200005074242c01c0a0100d4000a5040d0080684500c040c0030301c0d002060036024542c138044188a8a401024030142484240c0c2202400c02545148400c21140200b03d42e0340c003107446591a1030010703c00901070320709403129030034079000c201008004541d0b04102c3e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 74280577 1106 74279471 74279497
    0x807140a03020d14070504150e12070f0902090a05062206080a0c0306050f01051e03040c060305090102280504092301080d0903030822110108060402 65
    0x102c01003038205450903010405d110445030818111001c0c0c40d20151003002c00589513400f0f9510100042d45990003030b10a02400b9481840420f009043d611103480056809aa4040c0c4009030700600e50b1255200c910700c80204611700c0c0440061506003802902c0a0030f401e0020200c10700201ca41e4006400302c1c40003820000c010843e40f0030110684031606007000114140400b04408a040075401414028000b504001c1c00e0118a144200c000c18180c0b825a81c1c90f0624002448100750302c124000703e42041c010500b40380d018001d4560800c40451540003031507030038040100e9000b1030003407181400300801010501210310b003c0d90807030342d0300c048250750815045032100c0c140340750592148045030404201d5501c4aa0f000540760220381c0c042c506803082d034440004105503449900c150205212400b010f1100b049420002101c0700c02003602c41c1d02103640d500d17003844140d20401c5007007001 = true := by decide +kernel

theorem cover : BRFrame.Cov 74100721 74280577 := by
  have h0 := BRFrame.cov_init 74100721
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74100721 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 74100721 ≤ n) (h2 : n < 74280577) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
