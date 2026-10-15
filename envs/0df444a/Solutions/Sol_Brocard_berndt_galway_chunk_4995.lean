-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4995
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:24:24.029776+00:00
-- url     : https://prove2.me/submissions/25c0413e-abef-498f-a87a-22c4113120e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 898201438 ≤ n < 898381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 898202688 1250 898201438 898201453
    0x1302040f06061d191e0f12020f0409021c02120102030c0304030818030a081f03030e010c0302070f080105241815181801061208030618010909140f 64
    0x5400c2e0724079003890300b08014003503602d0103155000140c0c0c501c0643c00a4000c42c50741d0040c044c40005c904180390040c443c0d501200205460454002400c0c4044000203100e0b4940d01c01a0000d40d40740d400a40003290024a03002c0754803503120301c640004003400012809a2007442c0c1c00c09080d00d061003924030400c400e548480c07860b62959011690500010f160a100d03140e0b03160000e070310800400c0038001c000e030a5192054107050480703480c0002c00d0002040407805800d41d2007400040c1d401158500c0101c002c0c03d010854519070b00e004d0b03040c03203620b4011700301c02c1280d2400000c180300c054100500895030701d21395100102c0d4515401c42c5003300c0300c1d0f0442d082a041c8001031280c05940d080640c2c06150143c05100384440350000940b2030310109400c3c08162080720611a805801c81c17085144e040525000300003081c41c0c1030b90500d04d506511800303807480c81d001c40001c01c980c5501c0f588107440380452084003c2c079a11920084010100c086050307507100341881c08200c005400254150465440d6402004903 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 898203938 1250 898202688 898202717
    0x1203130311030c0102040e0a0b040e0a060c0e1c2604030f080913050105041113090b0f030d090806100806180f0f010506120a0b24091302040f0606 64
    0x22100740c080404034841000340d90301c0300310280301800251014842000c1d50b4280400307940c084d504c04103611407145181c0411060510000585240c86651040d000702d0728040e0a80190b480d554a11030f07254200014002e80101c1082503040382101c0c91188090700c28002124000030040d6030f481030b4451030320300b08000a2000c0365401944c07003521840391014903c0c1c0221203000c107146054040004a03403644075001030106103000d0103030804070303606140d02030f062915100300030b002c07103407144501907034160303611020302e070903140e40f03060340c40907003000c1c0440b60350504810f1700401800c928821202039000c1d42c0041001d605030f4000e8034044401c210000d00302504e400c14074100d0603401c00b0b8480340c42d10440003006000c08050152580703419158000203064940348051111000104c5240c04041e0020032004001400118110307400000d150721101c015140b400c52220000300c1909a00c4e4401180800c00088e10711050ba001d00944c820750b011301c24440241e10003401d84203240122404038640110f103608 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 898205188 1250 898203938 898203947
    0x180c0a061110022106010806100e03010617060109110f070312060513060801060b0c06040b09190b06030c010c0209220605070e18090c1c0507061112031303 68
    0x381c90556040d1000250341690a00490348600301e00081e0350484120121070380e2242000a610a001b0308262100d842c1800018241c5a12079680f24144250680e030040b05807002d5000401811007840310b0689207a420381440c0c0d55103003d200c0c040401d4101107401c802401c21505488403a45c5d80380d4a235007000842e036005d4588201c0d100c1c40b828010f5881000203002d80d648030380122582800748000555908060b641401c0d40c1041d04440c007928020860146240000514190f0058000c400700c80c0d40d403280c4c9002410070140720324448440c035046046805002c21303c82103500550007101120222242000190307220403255402030760010800300001c81d039404000c0d846200c5480f407124010070780910f0303584a003100d00603200200059400c0890700880d007014075504d11540f87d1200d16232814500394800390303901d20025041d180901c0840c00c94003502100e051044074010340c030400f55074802d41c40c0e1400034031500d6000714054180c820794402d84850070036401200c0c00b900200e4004c0070311907020345007903d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 898206438 1250 898205188 898205207
    0x20f0c0c030f011a0105031504050a0608250909080c06070f0905100c08030a0b15030604060e13030c03110f06040b16080a0c0509100903110a081905160e180c0a06 71
    0x120103100d40d44150303455521030ac01c0b01d201e03200300f03440060601d0402c1001b510f0030300c1000c807003001c0c075240015882d6030a1803525218100c5580c088046110f64007441d2102c5a8010710010143c00e2288400f44420203810484046404c1520703a1000009030340d07241048121050f401c42400800c001895640200b0301c000004c50f844100101c000c204e100700040030480c0000d14001c2882511004000e20000e49003600500f4000e200e00383d800e02d40e40c10040d10300482c2001c0240011b090101d171915000806020f020480080c101000c15100c8045108031240c0e01d442c3c04031011640d40c044e03d40002c2e40e00c005c8022030441a20281d03a090f0495a4251441c0000c0440ca001c0e41e080c4682400204c44694030031441c148800c1d8a540d41100741403440c43c0842e900402022238034030500e0341d5442400010f030001101d00301540d100491709142a03407800d03e90b042502040001d000c0d043ca038500440c811401814582c06401c0c400e02c00c1425009414140d500c44a03102c1a039507000561140400c0014072509140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 898207688 1250 898206438 898206451
    0x60a030c1e090905090102040b0d0b1c080307110303220c030b0106050406020d1e0c02040f02160308090109050d050706060f090c11120418020f0c0c030f011a010503 72
    0x46100c0354800d40704100c4009000c0031540000c100d68414040706156009007504124008002d50620342404510034150042c03242031019180d684041c01c540344e5407041039149101010f04030094003851824096280d130b20072244d00c4081000c10a442418080000c00c0307038401c200c2d0890010509500c0300300034101c00c00c0d9110543c0d61000c02600400410202030381640248100e0702c61740d540d280341c150060b00b4111a80f40c071405010008800b5209101c06014030001d801242c60b001d1901100d5100142c0181151580815014400b050442d080342241d4030041d00e0034083e48600f1035560f5071582660030380b4540500100650840083c14800d240a0800f0f00070b00b0f4840c1030003003496500c800141840b00300c9039201c03104494607200c000c5042500309081c054071460260281c55481caa50481000a100318443c0c440c07603205800310701c0e0980d25164155041c0c04404420141e03204160700b540b541e038002d6000711307030301c40d000300903d00c40b12840502c1000180901c03003020740400723610070340159015000100318 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 898208938 1250 898207688 898207697
    0x71e080c0d0e10020f040614070305030103030f1b0c05012c060a0210020c01150506070b06010f050c0616091d010b1b0a030f0305100f09110c15190b060a030c 69
    0x212509903c180050511400d46a00d216142c030700c1d0510017030051241842d0504644070801ca82c0380480c0c0c1c414200d80c10740e50117052407100c2c03807000c2d80c0485580c1c114180f040400107070080d600c01002044049641200d000741c1c2c034242c58030901a13900004c030240c801c9401c9204200c07034406405041800107420100001d00668500d01c1c0700c640a101aa44010b46e00480d5941d0b440c2e907100c04103180951000580000c1d0350480c00c00e416075968030540300015103168113206100907006212071140c800c03111083d0098056034614205040d000d51040c42420b80f02020038001400892000c40c901c00305028034805900712209a443c0c03414400c0c0ea42e00441c10810004020303482e150b0304020030404981c0d12846079803408180000000c0003012a000a0900c10300c4410b141c40c1002651700c0312000c0001e036001e5590019000c0500b40c00b0b00750921902060b00c04601a103e1092510903603140e115100b0020301e02c1e101e002e400c0e18505039044645008015a00200500c629540c0610a901ca04085e000c6030a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 898210188 1250 898208938 898208953
    0x30f071502130e06090705030c03241302030a050601021f0903030f0e03070605160c020f0402070614040510092d02030f010209040605041506050c070509071e080c0d0e 73
    0x81d03191408180750040c500000d01030060003a05c0c141040392903802400c6280c42d0741076082c03000c1340c000544005010004109003904400042c02c2000211070b048040c000c2c26a0300003090191440c0c040d4004030f9041a549291000066041d4000b01b414034105050603010170704d003210410ba650041820f58400c0e402c1545e5555899180e030441d200341c0c0d00311150075000355240c20343c2d032402d041641c03002000d09441c500c084030900a000c0c0c00900c0e840c003417641280c0c50b0504000b4500860000d014808001d000503050044001c00488035000305409036016405440a0680c2c0c40c40c8081960540302000f010041540c020004180c990a0784800f2a030706802100e12100707942c0c0000c0c1c5803810110542e000c0d6540000d2044c40741c5414829080180f005480610040c1001101092200c1c280e2080b8414000300082c5211140d60502043d80504001040d8031031504007220002c0c14aa82d00003246c1e480ca5103070f100da50095018015081c462520a513407a443c019001421402415101660081a105440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 898211438 1250 898210188 898210207
    0x8071b05030a0c0503010c03140a1802100f120204060e09130203010e010b120106030b0615040807080d14090d03030b0604050301020f07020a05060412020607020d08030a0e0c03030f071502 82
    0x880c007074502821103d000c443c107000030182140c0701e4000100c285480d1110079401c51480c0e450941d4001d1020100081b03140c1d0a030135020120041800c0250300403446100c055015801c00c14036690a40c8a07500c4200c4100c4001c40359040307115a01403c00410442041000c8510345120701a902100005208404e942143e01203400e48000030b00102090f5100c1e4510b054504241c000d030302101581030001d014151844d104d6011760700000d80a0b602888809011015501007001101c00400010303044520746607032540201c0d1140607246071480012107440b00d51502101c0c0d00140c52003500e004000c0304401c4010f0350240c0060510342003068100c001072000040e1590300384050885a8424203c41d50f480340305104104001301d81d42c01c164030443c3c00f07002c180504982002000125070f41034600c6039a92909000056004c0d28861006020110000801c003200403550012521000032404480d29528008101a01c03805201e0100300e1006092142030302040c441da8102480a2003001c00524080306003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 898212688 1250 898211438 898211443
    0x6060405040c0909140f01061a09041b0809061e18070f06050714010608060a09020d0c03050f060a1b03020706060506130812030403050f0a0908010e10150308071b0503 73
    0xd80c107032910480a1045611745906100525086191b80c008203e490300f002001800201c0b0780980354404100414000c107592150b5100c0d00342110380010203500405145002807950800b21240203d0b07008a901040300c1042003001c00718008400c051005555450020703c014412940b00c500e004c1e88103050000030900039582c100f901900b816541c090f84e4844a0406140b51319032112441070f030b0f070f140240c10808003001080d03841d04005861000b04031441c85000103001000c481d100505442400e00c030000802c940010200d010307403000c1c81641d803d551070141c80c1e030807070300010880a012510682082d140d503109500070004140701e50400101c3d643c41c3c1011425542000c00403080055900e0f0050001000c2088003000104d00320800030b166140555008003680a40190204080c10100308880301500541502029201c001c008018181d5508010350342c81107801d01c40780405103081140d940210b210060501940d812540745494089180c0c0c2d10485464000c1c810100c0d00c01d500d40c045480c1e9001d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 898213938 1250 898212688 898212701
    0x20103020a03142703031b030c0909101d070815010207241206060f0c060b090c030a0b010804052d2d06190c0c0f061a010206070206060405040c09 64
    0x70400d1020b900c1c43e0008007284d150301200c0c055035882d0720500c1004006040002c0a0104000c03600b08562079807564500001ca500401c40e241e544100b00408024800400e060b00a00319144001c0a1190541c481c412201441081d00e03e00006004500002c0750b0401004806900d28018411141d0040c0e4510400c8081c2512403044000400720500f00115160300c41415400f1000104042003194503001c3c000c0e0a40106065030380501264074001020311400394400c0080043c090120342c0280b800c4201e040c040c0e0f00480340d542007285041c0e004d800d2544100b079150720031039008005200b074000b07000706003203580d01c0bd404403420310b2404629800d54003030511808440d0740d02d02e5910000165244519111640369200304450f07a40808100a40e0814588411207844908480000d0703801c0500702c1103469282c2d151000d171171101010315050411400f40d0000000c0c482009070480481c0a03103004988840d4213682000050340900b0100b0b000d483c4c9903203c01c0c1c01c5440707081c0c8110100c0d03450708503a040d02d09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 898215188 1250 898213938 898213951
    0x1218060301030809031e2508160306200d0203091903020c010905010f080711011104080a120203070804030618060507030e1b030d1220180d0b04020103020a0314 70
    0x1000c1903044071801d08001030302509490030841d11401107511b00d460341d50046920b0b6800d0612910003e00030b800b042c0710700303640600305250545640d07820304244100d02c0358061104550b07041c58480c40481c24100c6041e200008000341a00a140500070200003000c1d40018007240180e004291036181120301e05446024810710907000741208149071000505079940740d6120b581400300c0c91114825455000d44a103a024405040a00c0000f0b0300340c1c20306004043c61600038008100c00030740403c07664000244001003a1041d131079025010013000080380c0302d000d03029008190410610003440010440d4101e4074420f548040e42c42c401541d1911410306590b400e8981d140825600c1007261516202071110307007020280e080c4841e080d0300d80d40012a60750b101800a036000c10810810044602c2c0c0503400007a01c020301c1860b0035880029000c1c012400344d100f601242c41c1028002e008000c02d0810081300c3d0751081e0441802c43c115545d540041d4080d6021a200c10704160760b6a541e2050048000216070040d031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 898216438 1250 898215188 898215203
    0x9150903020a06060e04080a05160c0b07060e0d02031c0f0c0305010e09010c0815030f030d0606180503072106060305100b0405060f28080102120a020a02121806030103 73
    0x9560f8200300e0308442d600d03009904203200000401002c1000d5008640001401c0e2414954581a01510b82200070180c0b400500a00b4000800984401200040c00b440390040d5001c003c00d10002100302c2c0d54980c03280707049015030024495a1581c4288600e01685004565408554500303481210800c45101d03a181002103030f901c00050100d0014200c0c8a5405a5804001c21904c404c0c0140134050000042440d603400f0300c00032498031107440502c00340d24090864801c480d280e44083d0700000c0a01440d014000004024400c1c4c08107079580680c2900c1203031006000782c0403840c207141d8000d503140322004405a4276281c880c0001c00149561140d1002580100c0140030058505152a81a501c0c40a03040d4407503414041800019581d12650310b40042c8102c0340c404900d1000309811070807040503d1a0311041141d0b060001d90f491040d0001c10800820780980c000640e203a0944070704a004440c08000141d008144a00341040010b000b402049610384d4156080c101080000350f080d03100360130440300e10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 898217688 1250 898216438 898216453
    0x9083307020601090c0c1a060a0b0c010902031c0503270307050a0203100c0e2103120703200a030e0102040801020d0905010606081603090201050720150f0d0915090302 73
    0x442d50320596620030424640b07032070080c4440d00c0f0345e4047d4412411104441c1180004500f0341d42c0d40d814030000400d91000481d4450f070081e07842d180249007590059010b0300586100c05a004680412942000025121941907850346c41c400d00c9891549a51200005c10918266141c1601000034000c400c0c070072030040505403807a1061505000d803807803042029070304001010307180603000040040131000542e00317030070b00718800c80704a26140e0f0a900076903034034040090806017404091403024482c0486840901520b42907003580c202401400c50007803030b1b84000740070b0030005511039002801e03548543d1002600b081d4a441600b03003240d118104d10001d842c0d80e01b042c41d080150a02800000f0055801c08003a20328145101d1080d00c4e0489c41046c04243c1e4900d4924110780c081c400795900e50340c004e00764008411180c0d0007262880122600e1310310480c01d00c4240000e580c0c651049965941c10518007905008c958000500a810440c40c00c58040b1f100d8000c0d5013502406104031401300c3c2c0240d0061020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 898218938 1250 898217688 898217699
    0x40b0a0216081c0218060d1b11010b090c0d18020603180f0102090a05060c10051006032a030b0d0609080909070905030c0618030f100b0109083307020601 67
    0x21801442850b01c8401c0c0144041c17070a0b4480980101613000f026181c080d0f440707411400c424005e2001e02441818860140d01e040300d850b030310a40c00c4040d041300c9002001a294040200b10300d0b48403c0310111614002046241d02c1400650090321080d00d40c4440c00101000c0d03580001e11781c0d0003c0324052104410b20201c0b540b80d071410801c50604181d020021864009420086145503d40f4012540283c00000704084014410000da11031240300c180d04100f24100060110032030903180c40f800713000038103007608c400815130030b10300c035104020592414900b040304011041c2c020b0301c550018030354090210380c910f1000c60058018128401d11031100c10303070354000800801c400a20050030750410045c49820070301c040e40300003409000e44502190311a4489401c500c4896405c83e80700006500342c02041c40b80101200c0000cdd014003900c90b10310042c49981d54140045802c130b0640c4c8100e41c59541b1084001203079030329190b1080000f10654800640d01b1407021070200d111a8107650a100580c400d500402c035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 898220188 1250 898218938 898218967
    0xc035f030a0f111210081209010e1e0906030705090a06051005030915060a0909050109020310140105060c190b0f06010f050904050a020c010f050a1d06040b0a021608 72
    0x1c0d92012603000b00003844035045451042d00802d1384000d0601c1d055400f03c1d070703450702e814050703402003802c441211324030b000c503030300c00c0c0141d0f04104101408500342201903803a81c50058120031401320f45180b1100302e40107031801c00c90500740240c181901405a0013010841c2c0e2104803519104a1038000c02041d103a2510040c8910b441c7c1046801040080500501c0030b441408201e504840800c260040360320b484000004280d5140c0d0790008680ca032402c4614010404103401418204e4021419102c500301d041c80c11805650241c081518403180410050041d403074030102038050810503c08071096015405591148000142c00946c0c220003900204032032100100f1200358480c0d02880c002048060a82001d03016014800d070b034a00c00e9481c2e400056600d161681502c2a0340ca648000344101407001104800510042d20529402424950a520b0900343c0e00c0580c41d00300c401710010800c2d55615141d041081e200a01003002090b000c0007c29550307101441c101d61214055031185a482c0700d411903825 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 898221438 1250 898220188 898220201
    0x13030c05040207030c0f0c0b1209060a021819030605040f050f1501030308090a02060a0306091b05040e07031e0204081e0c01210c0c035f030a 62
    0x10301c40c0340100041e40000e54004070b2010b0081d8840a020b06807000c80c50714035514003240d00014000c210100d1209100c2194030700080c01440c540040e11201c0c0c0f02c00668005038420359199001c80d50451a0700b007103a0400911711901007225044414a0035280d59402050301c205a8058810000342046001440740c1441200c00c02c000d030344002d007100704401e48000000380b8144005414411010005501e01d0014814030b80001d50041101c3e64580c10450702800510701030003062555460030010000b00c21403089548a0000284c079490b0800346011040710410200030001c4003010703194a142c501c6e05500092520300003001e0350025803100d06291481e4648000c01c5068104110121540b001e140808202c45880400a00e8030000201d1110310084e07400c0f071092114140c151800ca41d4841581e880a80c0d14181c9100e591106452003240c010f80c080c120051002d01200c14110f6030460b04c0f1006401e03090600d10780340d00d92200000c511407040103500071007540020780920020401c039845005120b9030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 898222688 1250 898221438 898221449
    0xb0a0905010e04020609030f0f060106180308070b1008030c010221040c0e130203071e050306010f0b07230a03030b060708090d050106050306160906140712031113030c 73
    0x4018030741c90720030140c41124020700081c0c0641400541035070161000d001d0b00104002c40002c0381d4584001400d5695510702c244100320004070100104908400c914a00c1c2048903080340c0113508002c12515100500d15015003a948061542c01e000210341c1d00c180003800104410500040e101c24035040c8444582c10080300795500040000304100000d011100b081c0d080c1c400c0065507440ca50303900924040711400c181c0000c0d5051044000008a00e62050040c00c0d80440d82c00104140c582d42d4028141c3e2410700b800340460200340080e060001d0046000076101031805005e5031080c07181034241510b9803804408624025400403c101c0c2d003407503010f0080b5002d0800980300e035441d10100f5100c42d0001c2c042d58192511400010141d101032000942050026040050955801c1e00740300c07200740c5c41c00c28900800d1000ca03030380c5080000d0540c0943e01c031354503e001403010185820107503614000c0c069500d00050051503501c0e0a154684c5001a004d402207120f4420b1a070056030950600900350103065101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 898223938 1250 898222688 898222691
    0xb0d02010f0806030c0a0314010b09070f0e030a080f09030111040b0904150914010e0906070806280b0d061a041a040e13020907091401140c100b0a09 65
    0x1040141d03408000c10240c100d1a1504107403d4942c000060304102d104032141e540100f19a1001c418002d08401842d840310900d0004c101c2c1c0303c408000e0000710107044030342002003113505150403481801640c640580c60401000d0b9a844245036546110309e0b044002c5441c0c01280108200190b4282403240016003211002c0407030500d0724242446079640310b80c01c6614004d030f488204040b42c060302111101c001d001d080900b0b1200340d80008850007901d00901c100c48155240102003008803d001c0741003030040407541e0300c2410564602041c4809484410742e42181042d400400840c4615200708140c081e0011000c0c01d55120200c1d80700005617107ea41000a001500503c0301c61400d50380030803102140d2032000c80d10100791030250000854041c40c4d1018000e0302c2d101c41044803007101c0b03035100c072a180c5c82121188240c0d214140101d9003410f05008201c17600103c01c85400a560043c001d00100500e800c48503031800c04000348490070302c070400da40d81c0d4001c0d464800c190160328002042d03d001e442e01400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 898225188 1250 898223938 898223959
    0xd020301092a05090103020405270c03040b010311120114070e0a0e0a0b13020c07050411030f011403280203070b12041e060c0c0b15030a020f0f10120b 66
    0x200c071200c1e8100e00000c005001c00000c1c0e51184c0c0e4000d405a80c02058020710081142414009817007032410344880925106488400250b901d040b03440640f03000316008494150a40c8c21584d4a81c194914030500c0c80e40302584401c205e140c83e00c02d0080c1c4100030066403410105041007240642011103140382e00c0e1103240c199a003481210445042107501c2418100082402056400480c0002c0740c02607003031302802c0c000500710100320340c00900003044510944080151285842102001e0f00003610510384590480004019060400600641c2101c0c0203059600005000040100d0071017401101541109080e1504040d450107001001c014502024045d04c4d04252044140c1d030a1001800184400740d281c120800b400c901c0c58040240ca0b5001e07204102003000c104000e0300c07000c943c1e40100c4a094001c1d002880c4000b004004882d08000a00204101035841e0f080010100d4564600c0340c00c10940d14200076640e840318922160b60745d00f500c9280740d141100d50107400f130381d210500c15809400141d2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 898226438 1250 898225188 898225241
    0x30a18050109021e0f1c12020c0319050312061302070c09240b0703021c05090301150b25080f1b01140f0702011b0e01030b0319020d05030d020d02030109 67
    0x140c035802825049070400002030703401c4c88a0b600000c0b607000147c14804034010030380d201c40c0c00040c22103540c5421000c0725003042003400e140030707030380702e5501c0c0104503070018800d446440781c0d48199503410100050074050003805686400040b60000c01040d598004400b01c01c0203c3d940b00e102e0902020f119419802c4040c1c90380308051988941380c03250140303222000540005040c401c0c06000b10303241448450180344032103900010308940240405a20035440e100c40b202200d00507044540440341500d0740581001c0c4d02a01c440b45442900101540340265540349400141840008081c03c3c003020644607202c03c070030b240e0820500003101560420340e04d0031a400002c1214038056543c002e0381590a0304075030351007150403409840d8803072551110020429000b210140c001901c3c916000080c0c4c4c0c1006290060710405581d0701d04502c41d40d0100598440c50009400c000140c2440d00740107408803460603072109590742c00c9901060509410b40c0d4084014450003031a0f000d01d82d19018218210741c5405d0805 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 898227688 1250 898226438 898226449
    0x3020403020411360405010603050702060612120a030b030303070203032406030a050c07050a0c1706012306041d0103211d031f0e01240605030a18050109021e 69
    0x20100e4915501013090b04007190a0803d010407014038007070400d000300c2d65186409070185c04103540b5100540500c1000031134a042c01f07094840300c8014a401000840000e40145000707522070300c0795004058492100040c60b8500300700940c000c0c0002c1e4010b590f81c0c6400640410100c5e54800b0700b082105001500d40c070340740c1c0c1d52000e0743e400c42940280040c0c10307140c4140c041d9081c892908020054025000090180800064001c04a58695081d80071901c1420348094030345609010300a507404414801a43c2560745d4200501a1075018080d6440c06444d0216809428000c244481080250000604c02c00c0350310741c003078101014441005101ca4852000180044800d18910302445036803c0441109039810020085030baa11000c4480c1000c040841e01c03406000c800c0f124000369070900d4448640900701240c4222202d46004054001c0c0b820302404568550000d48040340f80780d10380406c41d251915014001030b0782c074400c000000e41004948180108081141004650b0108540e038811594958 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 898228938 1250 898227688 898227727
    0xf0e04141803120c161505010312172d0117010b0a05060901031a0607080c061e0a0203071419120c0c0b0a02070807050f010b31061503020403020411 65
    0x21010f48031701c0640c807503417000e460303a11018201808034080c5510031141684150b06030384c00342d0494000240301290990745800702d00075810b0540f80304400500348016110713860710502060510464404c2d04c0f100003c0040c0420b030402e11640040040980070804244103c1c0c0d0340c0c86054440082403440c1c0301c0061114010240910306162300d89041c0381d42000d07080b040c42c04000c0d0007000740c0c1c0c03903400e80e0801000c0c80c2c02082032000203210b0040840e520384060007200c2c4d1402c1d4841d19030100d030340e60711980c00041e4101034921410710074502000340038940e82101074002c0c1d0780528004000000c00710401805092040f1298209514016000b569203612001c850749241d00a801c030f800589507200528000d12404030054120240450000100200803c08014580d61800248000da18142c104807110000340b0301036040d14025500e240081d051008112000c0c2e600c4040090042e640d03a008482200030321603040000fa0340041d01f4402c5280c40c0c4240e0705042441c425180c200300c00c400030514000d52 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 898230188 1250 898228938 898228951
    0x71716080f0612010e07030311070b0307140705060103210806100e0a08060106090806010e0106050a0804053a0305010b0702090c0d02070503070606140f010f0e0414180312 75
    0x20400d00103802c1d9181c07842810080c20516000f0850712211107050f540301c10303d41c0000c400013101101b00c04180c0c23900003040410307900d81c206041d01d1602c8003507041e5081c1d04410b0380b030307100b040050042d240800e2040c0207990096000ba2030803290601510f0341a15040d1b00360030b8800920469405111450300c510fa2850721170082c600f00120000c11840010300e0102442d03003c000640f1501c4000301d040703075200e0444011507143d2030440f481c0703036210003005241500c00d009490024205001d0301d10440e10412106401500400070390303415040302d03001c1c3c00300c030409801c0c1c0100904c625244401c07007401c6050b080021006501d810066541810803803489842241c0001c0d1060150501080b5208204012100071041e600c4d8115075072035161030156200d0704800b10999a080c80c05800140119500c048018420320041046c2410808400155105910840410200038224a40115030b840d28030800c1c1c100c038502108051103140120780d0490040606100450076003060010212240070031000b19000391 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 898231438 1250 898230188 898230211
    0x1701021e0a02071a0a03060501020609031c02090310050f0112230c03100b0f1005030a0e010b12062505040317070c03030f081815090a0b07171608 64
    0x62402070124548011a005519040d42d00314000311100d490394014030340800591028440140e4420044e601c0744811070300c400303141d001000300c00c10358844d0020000c414003290b04010b0a03c0c6009000c04e24000c500289452130715a640c051003003a40c056101c0f03e00500c2c0048181e40b407942d40e580c400702c41e48200e0b680c0202202c0040c55402900c6002d1107204860800541102c128052041109015040c851181401180105003601c010305010001d18000070443c2c0340c140c915161120b1020080151240340c001070f55a81944a41590300c900c11211142c806000030700031828110000e0342c40b8041300400300203040e03041910802e400d81110a6401700c07900110b031080c001c1002c4000781000c0c07144683c01800b60820440100c00c05400c102c00f4a0760305038594800e0405c1c0c1c0c407000300c00b0030407510380c10034011a8007541030000f011703003440410765100310f07a04d054a80c5241d20796558030740e00c201500e209000c58540350811711882d0307401016070750213550344030201d1200c00c2141002d0f00d55a00034049200c0301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 898232688 1250 898231438 898231447
    0x106021b12150a09140a031d011b02010207030501290d0201020c010c0606030b101d092a1503010e0f060a0509070512040303060f05060c07060507031e03061701021e 72
    0x143c0b09512050049030441c0c0e01000050303900070480d88800c2d82c0701c2d04501003101525207100131680d40c20301000070001078407401e46050343d15820302d142c0703581000700300c2c118031804030044005413080c06140119490250314000310b42908811800e003407074030b446060041c440742a0000c0540e81c000381c9615509000c2c00c01d40c9050000d400c01b2400340a1903080607202001007018412a4022030405008680840303a11030098400d00f100c03020694001e07980303481c0550104100c21910084c900162034080741d011076501c2c81d0401030012a01c541600c20b05038040da10040010080401c0c00d200c2694000034120b800482440c1ca103000411740011405000c1c0a00d20344800a60128010400c40703040030000c00e894403840c0780c240b4005020740214061509503610742400052142403080030b07110015640c030054420b00b07040010881301500030f041c0540c2000107000d449401418283c50502c004089641d001c9030240c14800c18100c900900c00c50401540c1c41041030a000c208044142144078048400490780d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 898233938 1250 898232688 898232701
    0x10905041e03020c09090c220213080102040303180b0f16060212010f051203031501020102070f03020f19081804110d1e050c1603170106021b1215 64
    0x2100786500028460452019401060680000c1c0400310058201c0c1c94503290741d54120a203441e1604000713119040800007503403a030000c0c6d419125240307078417107003c00608014445c284003492100303981c40540982d500050900500d0350001c100720683c0c1000000802c900d14100e0444e400d4462003903281d08545001c1110104802110381c0140c00d103400c444e00795190a902d004001d0094020310508800c80c4907042d0001d240d0500ba642518800302140203141156101e01d0781691603400c1c02525411954200884000658038101949183c0d019500800c095160b100c0c0640c6014501081c2600001e01e000d1800c0001d0201741c1211252890505d00131301000e44500868058201d0441c00010078a000c501e005c0b444907168442200c00121006d850024100000d03a00111401a10b2104500078108010300d008084820600300c528880e01d054122a40500180c07002b6690a03084107005801c00e552040c0d80010f0072204251030001191500150310110079600d81d109440030342548200070a5000a00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 898235188 1250 898233938 898233953
    0x6020a030b0a03140717120c070302061c0506010915030f060512010e070b030601080f0429010e0a0c3204080a02090a090b040b0c0c0d030605131401090504 68
    0x1e1150040c04800106850345080400c159403c2d01d4603a5502c51440002150841840b170b491454604602030410380c03a48070343c207151660005c4c202c040d040c440c4900020058407007600408289062400b8948621041c0052200b52007025006c03504010308081c1c14021094900342c64500e00f85503090004211021a505102400321640060b62049841c0803203044102c064200304450482001920005900d07042c3d0b00b4000e000175110240021000000500207404496980360800d00400c02c03840d080b00e00000c02c103214800b210101051300002c078010170009105040040d080400100e007440099884600100a403481800030440e055180511404001e1500ca03c483c482101c050706d0740ea2192200d42071a0f40360440c0108078001e07000720000641918451007650907017035104240b00d2098030b40340c0b1400c44c03005c0040c1200e9041c07101049051000c1904001c545546c000c540c1700810198034040810080c580d990306880c403034504020034060b900004500340340c10348007256000074042d15070382000c1e032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 898236438 1250 898235188 898235201
    0xb07031d070e010905071112090307060513050402130312050406170712050705070606030809010f110d1d1f1107060203032a180a0b041410050903010612060f020a08010306020a03 78
    0x2e41c0c3d008000540605060003401048419400e4085070bc0e2070f50f03140e40c119000c1c4150041c1c03242610034044207000601d8640c008059441d20041d00307112484e100d45030000b041e040310382310102250000074104490394102803901c03402c0440202440302440d1150000d45009804603038031721001e5840000503a03060042050b24034441c1c100c0010007401ea200c1c600b00420381e0210b2003480c08107100c11100020a03110b18501c080300818940034180c0348484090030389001c00c208004600c01041400c1c100d08607155254043ca40c1e00c0c4c24086d501200107114006009420000348800c20b940051f4001e101c51038000080302d4120a103540300d0f5a14034003200001024025005041c000c94000280c418101402600300030044442110440100c65450101110391301c82d83c4a468885080c0b201c0180d902e16003203001071803518082c2403407440e054013040000d00315a0b5540164203440d50390800842070125512a5101c07103c01c0d41811071900071524400b4104480506c00201b0081e0005140c4000c82e02c01d800c1074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 898237688 1250 898236438 898236467
    0x5040501050103020f1621050301090b0901031a0402030c120a03030606020d0c140f030c070f140d03181511060c0903071a120a0c1e0522030b07031d070e01090507 71
    0x41c007c40000420081140d8400c2c4640300107076040c562554000d29103416427a040366805401c0400d0190140d40c10480c0140040c4242d0f818018201c0700c1d1090348803421004291110304014144004103031401600721000c5070030110466004000b41026941c100250000030340c1c00442076001e18008000c003c2c5017500304141c41865010126880c200a440080c45000ba12104121282d826407210100042007500030030055014400d500c85a000c20b004240b1a0f441000151040741e180d600d499200000424821454000030440380d6000d086180c140106c541001250701034900d401440f00c0040c0e641c000c80e024a03c14003144150740403131000c00404480b000d2024040c24000303485c045481d40700520283d0f84804c0403c410b94100d16880b038103c01841262110740e12840c2c140f407118100c240e4071070940051402c10006105010005c54501e1a070540b1a483c3d9940204060010f01d00ca0000c0699040000016920119060019207101e60b102815180c01810000300741d981d601c021144c20b80d0740c8044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 898238938 1250 898237688 898237733
    0x50d02061b0f16050f061b0d0c0e030703110103060603110d0209030313060c031e091802160503130e041a1509041b150804060e0a170405040501050103020f16 69
    0xa0000b0031102080c090850f010400507038104c7c0d80e41e20360003802901d051407090b0040f00108401c40203410300c1e500c0350400b031fa44c42c0303452144e451858010a1800da1a60001d42e400c410f80f140482c0c3d81d41e07041c05800040c180320700d004e12540c0c0c4094403c50580c080c1c44051714003942c003c5019141501c0410a640d035850640390000342d080d030b45103405450a150b008095000031088540d60014078072509450442c3c1c41c0c00c0e0b660b0b103044c91500030f494800140c0681e007198035a400700241105400e000311007074007c90051003d5076403403108407191891416190311086000e02c5800c03c01c8007103002c059a103c8003120b807001303410721561500c800b958004d0304440290b074401444024030090200705421080e2841c5101100032180751201004060343c01a482c00d58005503400000400007040da030081c0507100850340845003110200c4c0d8440c403201d5042c85031031129842c042b604001900e803070b0240343c0c010a03080c20210315150080c0c80352815485503a2151407c0944c0084070410032201031121070141080450 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 898240188 1250 898238938 898238977
    0x11280f05190c240b0402070816150c051b16090c05090a0b07020328140a0b0123100c03030b0f04020307050d0605090906130606120609050d02061b0f 65
    0x501048804050609000b09242c10001011400c11b80300700d51103150002d2886080c89201207060254041c05101100d00050700010700541c443c4c9030144001e0f035012610ba00d5181e01400d0700c001b491001c4620046015800f1010000307407002c2c0c10341c0f03440c16284060000300d02510100400d64040c840c1c9036207944c0020101100140880c0c1d018054030419200300d0907a80e54099034089905040d07840c040705007104659080c140c1c00502c401444a8a40300f2200036102c62000c0c03511000e0504c4801d92052440c861545040f140840c1202c1000c00e400d8011142008070440c500c0009240c08034100d0000e050660316046004a0b9941e0000038061807401001075541e803408402c0200150058a444401542003034808550380c90b03c1c0700301e03034800c00700e400043c0f42581d5890420300c03140a8500055844682c0c405000c40c03900d498003600d00046005160228144e0f04c2071904500d407103060000c01381190405030a05c0964800a12002c07090814a44001d0301e5088104410040d44140100000284c42490 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 898241438 1250 898240188 898240223
    0x1203050a02010b060d1b03060b31090501170726010b0d0606170106080a0201080601110609030a080f07020a0327031b050a06020a1511280f05190c 64
    0x20041030403c10300186e101038004080105805640302c0d40102c0b112060240008540072800c51107907808021008454988004001c0c000c000e16170180d0045d480e443d031140e00610580d2410b010841607224680b008101030362814076007400c11241105440d440a60a812090060000b50058280e40da1700030580d0048a0751850318030020040351140b10300d4a81c0c0c00701040344090040c855141141d452001920322406641c1c01141d00010040050f0305002c55005400d43d610f0382000000d11915030800250340d42c1204c5170020303001c010020700070540174800500304a00c01d540800c40080450b4141001502044a0a80002030684030f4000303582d0040a00d000006005200c7d40d0058080d54085a5208090301c7e1828031403003504034082c00c400b50b8800b030741e100300144d10304022000102d89a98001038103a0a074030701d1003003507102811400b0102032a0b108101c0701d84800c4001c500d0700d02c590408900e00c402e0087c0151031030150b10229209058001c007a4103005000c0c031b10002c10580e0042c4600210b41616 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 898242688 1250 898241438 898241441
    0x50d020609090f0a0b030c0d110a030c06020d12180b0402030102390d02060411040b06070803060405010602060601020c1207080a0c0e01050f0a030f0f0506100e09071203050a02010b060d 81
    0x480f5075207559410701c400e80e02a406c1c007164006c0614000fa08031740049103180c0b07801c00b903c9a003038036560b00300500d041c001010a0340a914140504402ea0140000641840f0700520146951260f84203075840c03d90f00040c40310f556081c0300e07840d030b90011000d0360365902c3d07000003802406014000454908650380d120464070314244040700d0b04c2440b55580508104450109a8a944145461000d0382c00f000200e00815002c00200360311503401080800d084003e2400b00b05d040d040603c04548014001c400c0c0051442d01e40940b501602c140d00c001d081510381b07100001c1d600d44030242c1140c0038011040440502c0074007841000c0152049504441d42c4000514001c070f0b41005501c80d10b0131845000f00049201d10b00305101c2c0c0b14400000b05600340d02810b586811002c0c4030010303401c03039101a00c0c80c1c4500c0010024401d0900c284003449110a01915140860425500c001d040005a420085007808002c1076a00f200c168184c0500d4501d44480c0416016401007a4000c1000ea0061001c260f2001c010f445 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 898243938 1250 898242688 898242691
    0x204080c18010e071209061a0405130512130f0e061305060a0501110316030e13050405060c0306120604051e01020c0c060a03021c06030b0702030a0801050d020609090f 73
    0x2aa241da001e055200c0341c5001c034840038066142d0600819000c600c01c603104001091030020080d038006083e40c0e055135500c0c119901c80c2010041207030717010108003451609104083d8408062000e40250212079503400343c5a10744130f03a0042e030f00b00021401030380c03e0030703140c4541016183c02900e40400a488100c9503106082c05c584003403140c4410000a910301c0450b0044500450014041c080490308001c01924610304c1000104130501c0180400001802e2164201e40741500030303114a1130305059901070040e0002040c01640c5000c1c100002d10000480000361140e018000303040c40c5d9101e440e554005960b2003013601446107944102c40074407050001c04130b00200c0e50540c1c1140082d001f1184203205090380624501c0d6201c5070800d4100c4010b50410b50024104a840d40c5401450700b0b00c24408458054510003207560107541d1000c040c030030005440700c0207402c140340380001e500740300c02140001d00000d81401001e0080040d501c1a100b1902c4072001d0380d103482030050100d503040c904070103041400c0a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 898245188 1250 898243938 898243963
    0x5180c0a0318061d07141521040201020f011503170403050609010f05060d0206030a0f02040506072a0e0406020a091206090c0618030311191a0a06050f130f020408 71
    0x144c0100700b422844000b07031003022203040c003000b020000020800c101c03240350800c0da818240700c0704001c002c0c40b0400040740c0c0040315035004030b00481410140002841c10305110440f2503030342c0c0341c00f8000c00d0800d03400c280401260b51200500004060b2804c26200e0b50103180c1c0014a40e20070902400307030081c0190050400c408124504100c0b035619081080b42150a150001e9040030080001c20100621a000007502850f14440549400e648202003083c0d81e01400d0150386000e8109071040401a0030a4500d22250750580f0700c2002c1c070300741243e036947c0820160004006541c00601000a103005840c00801800c0010044801e000d031404d110002d08a07030340080314014207030305d000b08149000700001800007200f020341d24282801c50368160340116541103546414443c014400d000d4003500c8140c801c3d41e80c800d02e541c17007280c0c3c038040e052460312030701a2202100c1d5043c0721041c445603c84540e102c844130000c55085419403002a0288010040b00c41d076030344101c1c0000790104410200090030444403d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 898246438 1250 898245188 898245221
    0x6040b0f07031b0305090d02030c031605010206010803090f0d110411210c0f0d140109150b0c031602220e0d140d090201050d1b0905180c0a031806 64
    0x45841003d903012019101000b80401c1082c40740e4040c03403c100002c102c84610103412540c00d11003901c0000c1c6007806600001c0c40d00c0141c0d403003d02c003a5905000203801802c01c00001c505051040c0009a030040a00c41658050440e1038003c1040c8164003072020f40066002c1c0041003c40c54407268800a03501c03201c030b282c20561398514030080c0c1400c003200c214416608001d0326801c0901030450f50a030341d8060580e680350140c5072030f0800c40d80b0814441341c500802441c5d90014408940c031180d9007a8540741d5100440041e8103104210500030048200c1e0f101d41c00700c01c10030200054070b01c009058a10b040a811072004c00b903071380031841801303203a200c0350750010b5030713001c44422046120045921004d00c0d8401c080310741d01804100d055070402d4210080c0310303105041c49428115400d0b0080c0c2211441041c21018005140074424402d81089540b40504400d0702c0e00b0241001c403401d894481340300a4440d800c21000090400c0750148030350301008990203030403810b90a20000e0f060500c0070b4107141703140d08000e4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 898247688 1250 898246438 898246457
    0x90c030203150603130b0c0403050f060703050f09060103032a0303090506012c04020f06070c051509062a0102041202090105012d0c0b0a050414031305040b06040b0f0703 74
    0x30702d800d50940c0e104030b51081d9080c2401c0103d981b03803441c080c4043c1070f000f2190b909200100018a0511100c5403c0b10b00200502c4a40381440c030040540f0006000421140b50340c00a1041070701c0c0114500b81540d07050700f030081c8514220300f00000c80340c06120000d540b88200044040c00c0541c50b402164885d80254210341281c2d03291071228610702d880c0c4040300c2170060340f9007000098051000b14507034014002410000452600b00100f00d032903002d41422200032045007014489403034548064200c0c28240e160340c5040080c40c07000304045208402040800085148202d020000203c807038aa4002c0c9020081d174a50340d039507600900b800c2c00c5080c100e102d100e6060012500394840e420301c40c203d6212001c1d030802441564403100d5003080e0005601c0c00c1000b401a24ac000c81c01c4100c1540c00f81d94440c40002e00b0f480e0500b4036601130f26040c4404013042c4c00030444144c0c07494510008005450341140c00003003506031b03100002c03d070380300c1c80d0301c50b4542080202c0c0e502c403031601030005000c016010b51582500b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 898248938 1250 898247688 898247731
    0x415121b031116110f040203070801030c121109060301150b07030201060b0307050403140c04180b0f0601050405040b0d350403050a0b060402070501060906050f04290a090c030203 78
    0x50340150701984031040f03104012040400c0001108100c00100600301c15883c503540000705041e40c0c03088410b503002ca410302c0010410440d000c2d400b17800401000c03014100c40003983e5039407404401240d4400744100010004100b4540c0c0079400400055030050140121981e107440f150280d411041003500903510f00100010700c2d81000080724400c3e80307907944c4ca914280c156507407005903541750304040c0001d106403e0401175644642c403a10040302c1250400030014030307051030329594405000b4034200c06070007140c052041036608182580c1c20740300100c502003000150303103012407582d2401e040d000e8020358420305198039550004240141760307452000040d41c08480d440410303c00d441113100041c1641e01c03940c244400b0401c102441c84d04600c0c010000351074400d6a41740d041c256a101c0e00905001e5550f08410020340c82c04900b15188540e09403410700107c0b403260500340c80200170f0ba0981c488903022407080f40d20399030b50701c005d24003605d202c1c0010440900c1402008000750070884000050340b0021028050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 898250188 1250 898248938 898248971
    0xc3c01090f05211606020102130603230702010e061303030b0d0f0308070302270307050f13050403140301060215070503041221020f09150406050415121b03 68
    0x20b6850150103c2803403860600b624180d81603105000c080740c003400c20001c40d00d4a1049020004003031941c009a03c5444e0300300e000c50030100742c0e031000080c03528084020081000400f0f81c00c1d80050218001500b0740c1d01d4010507805484140203c00c10790154208014070303d04140c00d402c40c400d00076a010400310525006000806101d40c40150400449680300300000e4466000b0650083d50f524026040c00500e010a00310340258054009403151403429062135800c042080800614003228490003c012440100b281c100220a800703aa40d0341f5a4001410303d07000c0c41258140c03030071015496569696500e0025180d144811600030034001c64000704102610480a1700e02440e00316440090034201e4030001e0341d0001c0420710410700070500c1e65054104099900c054460b0b1a0710400681e0703a200158100f03e6440d00c1c1d00c001c049442f42c20b11003881555485001d803001e40e48080091615440c0505c01554025070181c0c0301c00c1940d040410001c0740c0807511203a01c00d60300f0191010301c5021a1118a880d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 898251438 1250 898250188 898250219
    0x4150605010203030a0e1e060405061614070614040c0f080109081204050a140f070503150112060e01050c090111150c0d020c0303010618090203090c3c0109 68
    0x41c010707071052010410b001c14030b900400103180e0000468404601011000c03070a1450040902440d81081013000240041230000c581d0115607800b9040e80d440c01080081c0420980c2c0c0000c48804601050300000c20100342c0c42268041801d0302310280903d800c1c5401b4989000d41d0180445d0082042d0000561580501035802103551206200b07040a80b045004468200c00810580c1d05105d1141000c002c90b82111204101021990203440e040c0b0180710031034509102c6610050181d44030501400d01d101034021a01d0545507245000140310006080c45009082e030f14180204951801051220703000200004045c108400e03211070000c1502c000d4103d8491518804420745c0801a80008a49200b110020300032540c1182005003400031032848149950426008500800c50003100c40e20350310300c50140c800c000c00c42d05005500c0c2d4030700680281d845003903406020740210000b507072402080c00c0540e00c43c42020f500300e0307010092102800e20104080c81448055000c07590054001c142d000042c6c1503072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 898252688 1250 898251438 898251449
    0x109061d010f05060d1b030c02250303050c1e07030201090509160f020109140604020909240601091206060612060303020a082d031b0903060a0b010210020a0305041506 73
    0x50502614010901c40698031200ca44040e10b5a541c1201030f50506c092454540b02c1c44541c0c001511114018000c0d140c90030000c980c0d1485102c0550b01c1d1140c040020088040d00c0d41450526110030480e10300504e00300e001c11010586000c408806c90441c400040c0341000c49000f613071940140f42c1d4880c2480310780c12041e1034405801c0107001c80c1018107070140d414a410071100f1310001074404256180e080101083d1108040c280d00071b44140000d500d01901a15000700d44078000d051a403402c8000401180c20030105000c49812000c0040c41e81c6e80038805c114010724180c2840c1c51524450b161080c001e0109000e11b00103d85802c43c40b54081d43c243c4034840c182c91b03258008080c0e610154441100c036400a00c00406590407071201c00d20f50042c0c4200b9207004080b8504055101c0c100080c000c030401c040c07595140b1500a040c403074a540c9a0700011400d0f001b200341d10340003540c01014030040381000705d00c3c95142c1410f400020300ca041654140c0c442c0c0e200d940a07a00208800700c008504806980d41440344 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 898253938 1250 898252688 898252709
    0x3020607031112070f021509130903090e190501090e030d0506040f14090f010510050609010306170f1501080717070e07030509010b180c1308060109061d01 68
    0x1503000a8003410902d82801c520b40b00300c42c1c0c0e881045820071003d502140085540721407450310b8504504001c46e000850100b4140418142900c00b8003150840041509100829840b5201e5070300b4103006109080113480768200b0a150b900d00091401010311521011008403481c01c000007803100d000d403240940702c0f4180d1001c0c41c9041c148a181031701404028200e507038800d54416036001080240c3c4900c480627651210801034038600540a10300705509840721403c5c2d64104001c002c00142707040c085005840701220361540743d5000c40b0040b03006051581001d200b400c989002d00044440001e011710000c03014030212140701c0e29048100c0d11414017803042042d107130700c2828144200c841c03018007604407603880011928129a10625403150100680e04103021a50f80c1042c40103120080c02421000314007603442d400120660f401c04640094014800e01d0b50800c0842d491656031510721640009295240407105696180d003461b4008080a00c65010401e510396075a104107890303200c01c2030480d00c1c00d40303030b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 898255188 1250 898253938 898253947
    0xc050a1b0312150909032a0b0415090c030c051c0c1518032d021e03010b04060b0c0f0f030702241308010c0908062d131209030206 57
    0x1400060800809a0030030101d0110f03022032068802d11134805082d0007507480d90f400080c461414407030001144661a5010380d800308440c08aa2030000c000d80040c2d11411070952200202030b218010700b010303007001b0801421900000148100300241034260380c1c084032801a07840c061154181c4070310708003100814040d00044200321544040e5903a0040507202d0403e41070070310ba1003d203149510141c0e0422602626081d90303991103a40905824a43d107008030400003038070565600001c1201c48100300c1900d5031141d010804403c0e40f000e4106221007a006002841000d440d8002d6216580250321900b401d4404d90381d0310442003900042c11071703804484401035880c10840b40c09001d2002041000320020246c24030015140b1080007009049205c080c62403004204e0618280c0d500f9560a0060070081240385d400034001c142002c0390058004201c080c01c071030481c01d0b9603e0544004d596078800c500c1704d40303040c00b0015008140b180d9103017024811404941d070340074101300c241c4840300c1a00010350414000e02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 898256438 1250 898255188 898255217
    0xc03020c0c0d0218190506040902060d0504140703051b09060d0b1f090f0b030723040905030703050c10060b0d1d0708071a0a0527040c050a1b03 63
    0x40e801480b50380090038800c1003040300311105031940420349003101c076196201c2d11024505803900c40c40e07400c9841120180090002c580001e00c441c02481c1e4402d00c030030750380c0000c82c0802510307980c0d282541424805813507040d5030328180340c0e8984003420164600d4890407200c40340503261003610035100320802000788031802e442d610341e03d111000003440704162100d190030700c0000030386103c01d4000422031100d000c46c80080c86d220320029030b6400c2443c1e0303021750300c400028042d0002405142e005250152800000007208000280c00741c02d078000003a1550100040000034141d0141c001c004c0003c070f0200b25190082c0d8070711000100c1d0b40d603125180070034000f8044440007001d03a41000100803220581d901d2400031000280f0b04101c05903025103015800000d08225003050b9003440c00d03a5410180e04035040582d80c000103011803103007800385000b25403100c03003004401907071505180300c000700a4001c02100080140240840c3e2102440c4030100b803482007a9600d441054151a0140d0350555032102000b6481 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 898257688 1250 898256438 898256449
    0x10030203100b01033b1002031303020c030a05100e0106050a0f03140f0307031115090f010c0503060d12050d090606092906160b0a15051005040311060405120a060c03020c0c 75
    0x601341d45401d000e14807051b441a8410700280d40500c4008100095080b281c1c50040d00e85070291080c43d0094100801c038a01051010440c41203a00300003401040650280000c540108107a8006943c042510702000c1104524141c003881038a00c660340c4060952115441181e54199040707001d0031640c0100301540000c0d100c0c2540c5408588090101c5c0c0308043d45140b04400c0120440d400d44007640a00d031041417144003401141082042402d016180d0304141012030480f0b94903440160146030000e504550192291045802070006410100400726040c90014090601449201070003800c0101907101c440c040d05003c1d400b090030144d02031040044409100840d0044a050707802000380700c0300c2002183c14101e40398402c0d01d80900004220525540310800ca107a1500214011003014079490314040d049411103050369000503407402c65440c00380004007513100d240c101c20342000d1402c041c07090311400005c40400030307032180600f401002c070101c2c01101280180744809000307034442202c3d018a420917 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 898258938 1250 898257688 898257791
    0x913080a0e0a2106050a06030b0f091c0f0e04050126030c0d030e060109090c0306050a02190302130603020f16110402030705070c15140310030203100b0103 68
    0x1405000b01107940d2250000422845852544200950003112007007000c1446503070783c080c04070181041002d0940d15440700c80b83d00104406d5104403a900410860700302000000d140701c14004010f2903800881e0f000400c41c40c0b02e16061004103c40b00c12006070b61909000d01c3e4181c0740680007040b00400c40134103c0906030908c502d150342a0000f0046c0d40e02c00074091000761143d5843d92000300d40b1800000c0c2e068500741c1c0c140c0c00300b04800d140010400000360101c018104594000d040491940c075803a103050024418174009403869001d040d03220b0340868040e0080e0000700300c080000741c102550341105a051703200d203540c1802140d90412001d2801c011382c50500d108540a07820940c00d000582c000b007002c85c1d106448140120300f01044150400c404202040e000c2e090003003c4501982e040d55002e0240c044183c0e01d1699940e01100207000004503a006100a6800408503071507100f036035041c1c4e401450110902800203040c0b5080301100443c0140c1c40711294012101200c81d240011040100c4901 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 898260188 1250 898258938 898258967
    0xd0f02060c1903021e03160e0f01020c10020316030e0117012414030f100828050c0d03030203011a0f07020f0a09090c060f1d0108180a0506060913080a 66
    0x154955620b0b503d900d01e81c09181f2414803030311319800e802d589003c05858001e00303411440c4260080b4400301c0050364045141542500183c50410703410310300c0201a41140500c900c400000101c9070312420038958062001528403800380ca842c00b50240a4602400c01b170002d00a600b0341051911443d801070224070781042d01d0031858905541071006042804109030310990380c0c5030302000343c001407010905080781640c006145400003401e01d4010071515200000700c0320480244000036403023581c280201403103000c9580e10000d00306042c03901d603071401030020741080c061030120516400da0000003202c003000b104d252407080c4206a0a00d0f19590030003a10415002e081508103400880009410f0114020a51451301c100d41001c000c500b41040104010301a062001c00c208100001000702c0c2ca00440d031610136882031a04400c0c03561000c158504240900e1040c29880c0304d41040d281c20b10601140c0c080c01038004543d154295180d4800441c5410603514002d070080f036007080b04040c194000e000c031101d50003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 898261438 1250 898260188 898260217
    0x50f070e03060f06040f050c030103020f060406020705060f16050a12023f13050108070f081306110a090807120c0915170a030e0627120d0f02060c190302 67
    0xf00e42599054840540707180703840923000300051007146429810004010403e441450403d4a0300307034000e54400391381c443d1601035040082d8804d5801e06540465202e0041b1080080c00d4403014a040c540c0d4405038034060b55850100050030810f40d101007038141045402c8501c7c42101010070b00084090440c0a802d45008100d12502c1c0d030703559001e40040d01d000c21048107100000c925090001d85000710040c4a0020400d1705640c1048090304010000d420105070703051005110410324208008203c000b650042c840c41c0414604080c651251003070040e1500002900c1901d542c1e03c0c44540d00180600004054a042d41014008000306501c20903101c3c114081841c0d8982d613030610b540380c00f4202c110b010140d4011021050074590401c4840b4200fa00075a40d082c586150403000b14039403910000300700440c4044100e000c0c0503030f95912000f4601100c1c00180ca85000801e50048c000d45215400c84000d4081c990006000000c24010b9078050300d034003e155450507502200c224001d500c102c0340e007190817 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 898262688 1250 898261438 898261451
    0x11091b04091505060c0a03140f0a0e030a0f1a160909090507030b0114120f0a3c1b0f050111010f02030c030421120c0c120305060a0807030507050603060d05030d050f070e03060f0604 79
    0x886070a40b52400b280586007980c0c000f0984840c603f5034150041014400c006090400c03860181c2c03012044c0115140c00c5400162104031307151140c100b417269030000d0941c5400c0e00c0003103034445503444842000101201c4420310141c03040003054132081c90030442a2140c00490030840072509100200310140481503032041655005c1e0114610480c90305e045035044400020504100b240184080195810038140094824500b80c143c0c009000d481c01118104904181d807179103c00707002d40140d0411048190300f9503d9190035407640440c2d410450b0191989034281551942441f500c5410213000500c90395011921390300d005440f0040c11000003400c0070050030381180b001059660110780e000800a6401003143d0508004020345401190000c0e50f85401a410410005000140d000304403075090360700716104d40d00c0c0000111641600c0b840a012400700290700b0080d10380580c440c074460314041ca0032100d90b80340e05600700c800c4143c80b070000fa0594044404100300c041142d01c00740d40024000c1000c5040c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 898263938 1250 898262688 898262693
    0x8090c030a08030109090c0f03050c270103030f050421050c0105070305030a0b0a08013306023007030206010603050705090f09040602130311091b04091505060c0a03140f0a0e030a 78
    0x800040c0e0040e50355070044400c0e0a900c1c5441400d03810000d339440c1c03e1290052229078042c0c0e00c041d040c1b000031705002001010311103440c0200181c4005140041c020501d820720703440c43c0c10303256414240844071805410090001980100c0070f840c440794060340d8090665540d00010f600801c4103c4245522014003071700011000700900406011103207018031405254022440a008045001c08031842c80c50f00d828203005080e80061110302012100c1141080e40488400d07001101c0d001510b8000c0c001400079202c1c05040c1c000921034104d890584d02000726640e120b10403155400b5014203142c0c0281180d0049117540307840403a460f00035020304001454085940500741c02c141040d801182ca018201031040ca1621b0f1894009602c4411030302040c01c000c0c10300040200502c130f0b5028042c00d4980e2031a200c0c1c58524030300840e2010780409840e10b6920100f4401060f034501d41060110b0001d03e410b1f6409402c00740f0b0400f522084411018481e0504000741020303142e03081440d03120b5402d1310070081648003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 898265188 1250 898263938 898263959
    0x60f0e041107020f010806010c022b21020601060509011128030e0609030319142a070e13021210020a080f04030906120f0c08090c030a08030109090c 65
    0x3441e1a40169003030780c4200318070500801048451003217052060342010040d4030798120040e0042a0b40c100c44404100d00740e188441c040c095003509845031040720940e0001000144c40d4511002004804044000a15003104a13a02c03002405030034000340f0107101148140d402009107401cad1004c25025a0070323505411101101c000001080303031700003019480c520000d058100310104200340060312003601c4d1611040200390303244a007070003202000380b0415208118903c0313003486442d500c1c25800807503a02d901c8101d8104c9480000c06444842d0801c55200040c0110002050412140400001001c554072094120721030710100d20f00303a03000750091410302100401401710400311414030400584407541d424009000700300090010728040b611105120110b82c01900d0756086401500e00b140d404011114904060300388410300903a03250403e075041150b280c00120a40c41030100d102201c8481841e9130415035a0040703240040e000040400040c00b2840e520742240700341c0e6014030380c07882115680344030021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 898266438 1250 898265188 898265201
    0x307031d0604270c0f12050123030a061e0b01020309030d0e0312160b060a0b0915160c0623030604090503040b03090307020a0e06090610091a0c07170601060f0e04 71
    0x130002a00c0d542c24850842c1c200c031003501c0720104140b041100d581841d40e030100c607440e60700301d00c1c1d150301d009101c242550782c04000300180740390710400921545a041e00b406c8208036000c42040b8110342020814500c55200205071303410800001c004102d010149007094501402c001021601400f415100e2442c3c0100071008001c440f03616000e416044020b410b1130f24490001401035031003844511b104100548101c070940e082424121b40c50000412504441d1055114541d96900e4055501c03441d0000d00c44082d52000489030341d501d503542d600c10541440d05400078024107025129005001081035802d00c5d40c021074006100700300312031034141c890000100c1c83e04111a0040c10780e10000300c40003107062a504d028018010129400190308100000491096005080074082c000c40701e0000c2c00c541c0300f0f00f40d0b2402071178000d4400400c404030240400d4194050302040c0d10920516000044108030302120041b012020740c06003040ea42024800c07a101d511440002c4100105c1030004140e607071b101d12403c1c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 898267688 1250 898266438 898266461
    0x2718050a1b15090e01060201090210302310170c030304030b100605070f020d0f020402031302090c070321060803130503011b0801090902030a0b090307031d060427 71
    0xc0c03845181011558150390140c00c10021a4100702820300140c2fa01042200725110070b080580068900012101d1a0390390345890758503854548071502411a410360020842045040c6c0a00410508200c004400101a0f51040c0d01e0045140100001f010480b000000840414151462403844d4400286140c009030404d036540101c020a000a288000c0300d110014040d0b030a0071030a0911076214452040c1801c10301038050102c00200340d082003c1656401005a4028000c540724140007a03d81101c6140035400c0303016428410200e100c40c0c84000540d51442d525684030721500c03000b40c0b01ca00f8800741500c040c140060b240c0c0c20119449505001800e00c4011854007100d000e442c0000701425540f40f12800f10110301c0312075103044040d6001e4000c0303041d1921030303001084464051000c81e1038030300c0f0b490024000300808814881c1c82d0344040020302c5074900a0351110341c01c00030704204080c6900c0c91901c680d1310181c00c21042041e22582c003102c1510900035028691440d02d42c0d0380c1c2409603034004580 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 898268938 1250 898267688 898267697
    0x30c050f0607050d2d140901030b03010e060a060f1404090212030304030f20101d0610050405180307120302042c0a0608120906042718050a1b15 63
    0x250b101c0013800d030030407034440101461700342c003042e02d109409050319082c00d00c4d0702281080000d9214003039009420610910030013074020051260400c000e6900d0340d10686000029078201000040d001c0f001040241c20b4a20120710500400c0781710080000903c4141802c82c0c01c2550038900ca003c103007007440035600c1680a52584086500c0d1a6001001899409900e40700300700740100004042400084070b0203400301e4413800282e941010191422246000c07071140d05a0310503107040150350700844121004030785d03094601303000a4403a0901c1005160010410600d554400d2000d0404101180c0c2a41540740307260600514140d00c0d05400c805e0458020545441540d00c00088003081d4500704100d90f000403400001c000b280e04100c086505e40220650103030044c1404120045203696034011100108216045500c203022a02e6042c80d8080500300c482c01140d00e04112040358030380745038005103243e03400806450001429510446035450341031820303140000b80c880c00b01d50090707400e01102e03141500e41c96 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 898270188 1250 898268938 898268957
    0x6240d0f0803041203060e25120c0512010b04080d0c0c150c02011d0307050603060402040b0c060a0f0606080424061e121703090f06070e100306030c050f0607050d 71
    0x81c00780d5106d5807152602565040800c65116040c408a40c002a2000c5003000c006440304012144110060f40c03c103002481c10b001c00705455000402001020041c2c41c031480780340c0e03a42d03185443c2d81c046c2d803080f005160490860112814414051121000c0c4680404901ca5455001c0314400b0b01c0200014004592a007152005568100d6a014920441c8490400b0b8034005400465210065445443d0180b8070210200e445951142c06840240c446402841e032a80c2c041032400d42d0320308003a50790644851802140750305180142c0142d00503170f1000e03150141180c80b02e584000160385006035201602c011a644080400303810b0150a00901644948040081c54100d00c03400c003005030383c0042c907900f07040141c0c0b42c000354694211082d5550b070500103980720b0f55038450703040c14007a081e1089500c6010f02010030044903009400e9540c3c240003920511086111110245e0840e11140405048403001c85e07400c0011f031034048440c0341801c20103000d0500380383c5180d4170145012003007405003011039030040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 898271438 1250 898270188 898270223
    0x903082b090510060b090f01110109030810451a040e01021201060f0521040b0a0b0901050f01120501030f050f1f09060b1f0206240d0f080304 62
    0x1400f207514010440401c007080c90925a001c3c1c0303100e00c0210038060b5008110705201c5d0b0303000e0380c40d0080c4002d84d42c0090007918014540241801e4080310680550030b1288404502c2c0903480f4071914000031084d0b03000d0300380d030603001040d0b070490007400a04c180c90a0b00000164248200c0c000c00a0b220070480d01d002191042c11304010648080b05222685070384144056040b07408041402c6046400d682401c03001d00c06400c0046400c2c0c483e0340c0c80440c002c0041c4840b45503120141c01c585200d1801502090b61a40342c071340c41a8241e4240c02c0c10954006412401400103103481c80d02c120142d10141081031002c07103119128010350b0700c26481076900d076451580007801d0141c24040360b8013000d018800b80c20681c0120038005030407a5181d00da0006c2e00c0e0303282808070401c6216440210211300013002011456010720031401c04040c0c04074190010300401d4085110315054100c40a03038004a81c003c9041103010b1000d001005e9115401501c54031071009030440883d240f200114052130186080260503003014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 898272688 1250 898271438 898271443
    0xf04020c15130803010b0a05090604030311010c050c150709080f061b0c060f041e0b0709090b0105040512010b04110d140105010c060504050708031801030b06030103030903082b0905 79
    0xb001009441c800c03012200c00a2141c03400c60381950144540b19480702c00340c040450702d6010300704a064100a00003000701c20706800c0000a800c8141020003032200c900604004c031414001d040c000710090f44186140c844549243e010039500528074602078000070303a0746c00c5492400c1c25a113003000340394018400380001c000c225088401c60504200a461501100c040001e649032402814a41200e00710b4020404208000840e0040d08860451642c2a6015402c0a05d04c6a405407060408900c00c00303000031345643c10b80107400c007903801611f6980c1090316000612407410303004107488081d550f071750180940c07655862242c14a40000d40003d1038851400d245114111120103000f02a06101c0c0001004180e9028040110b0381e81c0c8100d010400e0f8403203161292420f403031a080f401aa0001207000003240000345645447c04000343c0e82884004080014000c03588828000035000401466080c00400d56141c02020314001b81403e03140c1005d50b00320241143c0d42c010070401c88071500c40d0102c2d420710204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 898273938 1250 898272688 898272691
    0xb0607060518100c0e100207060f020114010603051906031106131d0402011101050c0d09051c11010c080f152b150c0905040b03030403060608060402100c031b020f04020c15 75
    0x65030b00c42401b03401014040c0d43d6505038450307141007000d11460107031018804c0d0003820380c00351401007001c405c0d61100070181c0908005c480c2007040510595003107200d00e031030b03002c3e100031a03811807541c400c1040f04006201e007541c084216401042e0310440e001500e41e0700c00022f40e20030810160345a107a0b040501c001800c0e100307460319111846e030400090003000c1112804071411450106c0000074400d04914029081c125043c0300390325006509410a550943c2207643d403d9500003a20080041c4120084213a8041a09640038035107071858000003040d6800200030318100500c02480c0306681200b200800801c046050b190101c00c960001e0034600300402120381c0301010301520424001c2d484039500080000c20300f44903a5204544407401c1c0000750f00c050003100d015680000d030621050342c0f15080296260000d07602280900c415900f8410311520600c28101c0142d850741d00c1202014409607610064a0b4484003a40d11804a08079052203a540744000d020381c2c14503002829040e244000301242a090 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 898275188 1250 898273938 898273967
    0x10603050609100618080303090109120306060e120a0f050309010201050a141b0c0118020a0b0405010504030602070203070b03131101020309010f050d06030606030f150b0607060518100c 81
    0x542e50280000c50700c0100040054458500d41008054052005000c00c0c4003c3d52069150340000418884030382c8040d080640b40d01d00078064030750b00c8020003038210201c1d0341510804000806880030140300d403402c076100040e8007210500315482d20f40641c560a0740e100201a00311940c1e07200040752511541c0a02400c1c1d4001054401001203a12001d150401c18000a00605c481a940c02603101c0f580020000d568400721207400801c5480f0300e00031805401b40c10300b50281e00c25045c0007800580e80c003c19080300c040d00c0d011703500c0c141014903650f1071b0800f9421880f8100c0e814020024007040703019941001d14462181d401411034080050705100c0c151000e04201581103400822001c10f403660030140c1d504082640b03107843ca0344c0710101c00000000b007066400c010070b0641069000400d01403940c01119031180150f001010300030040c0114000c03164102d11098201006021800100c0d05030ba2200354061084441c13202c01480b90004281407100d80d04807081102e1b03580c80848015580b10046180d1000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 898276438 1250 898275188 898275199
    0x40f08070e01030201030b0a090c05070b010e01060c030f090b2115010806061803030a1e02030c120703210606020d0302091810030b04030801170a0f061d07030b0106030506 75
    0x1800c003a100750300c04805000181c107240d1a10f64188464032400b03c194003c000c049010480c081401c0f038000c0c815070240030240d0f846058070001095640001c00f5090483d40c1a440d416131180c5250b4040e610b034100c00000b0810f00030f900d580003030055070781c0006003400350b0b03c05001c018042c094a030002203008054060390821680707554074007003070b6040207200745c00510071542c0c21b031601200048214064a4408055054000481c00c90034464200c20f51041a48208010741d0310b00b004404102e980c0d000c0c001f890a1103a00404e104202c2010782401454a603000c0e1804c0701303107074061b00006024000d03003500c100c103001c1e13484004100c10ba034188503042c14a4141c2c0340c19461310a003440000e11504207400c06100101d1401d01107440b540300606400c1c015580900511400d291038100940483d6092249040c031440c06441030482a0002c42c449205591282c003056000303609440c0e400c003d084281c8901010030402c204500004820001c4900071840741c489852198101003001781aa84054482c40c00344 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 898277688 1250 898276438 898276453
    0xc0201020c0d050d060906090b03010c020f0c0103050403031b0c1b0b0711040b0d030203040e0f070f030c0908010e07081b0d0f21110c12030f1b12040f08 67
    0x3100402c80e400c1ca400185011520740c603030546490000d001950040036485e00d80a40001c0c00d030032030340200c20340311000c900030003105218580a03030f25950b050602461b40e4108410412056019520554105000e4580090050704142d640074440d18616034600100e028080c400040181c051440e40c20070b014400c0c441c0c54a0b180c400004940d001c0c1d500003c000c04824005152961a142d0103402c034440020590070085180e81806034aa030f20900580324859010b400203004a048020307203d01800c42550ba44940d44a40ca1044000301101703000101041401940010746001c02d000e14000210310304050980c031441c0211061900210030401c0d01500881d01344603529a40340c0d041c3d5080d0700d40180c0744408bc822783e454031500c0c0310000060344078805a00d502005a542d031060b81e0102c000d2403503080300c920726200403c101c00101c1140c5400b03401c0d1b004129007442400c9050140248180c17030700500c059201032080c00c0d400d00407808035164841401040c00c0003100320b140d007820018640396000d095103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 898278938 1250 898277688 898277707
    0x501050d0207080c070f0e0a021207110c0a08030a0806090403050913020715052d0a0908070210031514060a032c010606030e0f071502072103030c020102 67
    0x90184851045089902055030001e00c000c0d20204c8007607980c110181c41080c0e40b544c258240b12401030258005200d030070310004040c10118030856100c80107800490040390707180f00d02201c210083c1503070740070913001d00341d400d08040c1c84400c41940503240003405103440350082d83d4000c002e9280207101d40c0c8600541028040466080401c441201d4000d491107601c2504045000c0c000e031007500c00043c1544100d0b4007040c1441d03c2d90703210758041e02801a46c120705251508203548042000c80030541060400380c0401c803514a40d501c2000081d04c46c00105041c00010b4000682c0d0030100c4c0524004281c40d6646c0d042e11148c0e040120000e05401e08604500e0040d130008244580100c0300810203155842034102e421104000d141e0054a000e400850715525403c0d07101e6000e03003170074401c00d004a400c211400c00d10b40e001041528126611000620200c1d142c44689100ca001c105040b400358003d0300c0300807034007880e01d503000342c00d4002d00c1952500c0100ca525005085491034440c4904591052264095 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 898280188 1250 898278938 898278947
    0x507030b01020c270c040f1202010813030819090f060f06120b01060e0406030821070e06030f04110303120702120c03090f0402090a0810060b1c0c0e0423010f0501 71
    0x1c04c84600c4c40c02100c5585092000780940b085030081042d030316844a000800d80700141100348100e10031381e10012103480f0207645451303403042d000000b004070f0000800100302c03000d003440d081c00070550094040380120041d150810040601c0d0001d4494645440d0305813403500301d80c002c0304020040241885403180c541d8984481c00702041c0101420000350030140f855a54907601321074041c5821a140981e103401c98a0343d40e20300d081d010001100c200d0400000341c2000d00419404070512406401da40c95075507507410102085c60024011030f400c03d094640300c42540c6007040174108044901030707070642e1803c20716070107031030102d00b1080d80c0c07e00d880801c003000090ba07010064403682c002c166414165000710800080c081d00070075550079004074000100247c1d400000a44044d20a6641020041140c840014080702d02c1205007144541f803180444903a18035444e40189a804611300d01074952454450010781a91054102a880040c403a82000721f0600684405030040c4000b107e4449510b00e0701c40081c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 898281438 1250 898280188 898280239
    0xd174b01051516050c06040e18010c020304031103030d1418031602040b030a050d031e0c080f070908010c0809060718050d051e06070f0504050a05040e010902040507030b01020c 77
    0xc41c070050820049007044420032640445d4400200b8050f25551140c540300d480050840c0e01d90b1900d45110004106500184200442e030302596019503c1c0c1411a11091003c401c6142c0c1c5541500c0200004050403a8601c60846452001415082c060401c02030215542c1d10055151b220740e00100403801124803071030300d00507603a58142c401040054517000040d007449840031002c0c140d0b014009510700c2e4283d25a2010345020450142e0207807004803034100c0400c4540c50b45040d0045013603000410b017458401c0100541c00405460300314041078540c0061401e54905007040404260184184050641d0902600303510080e145070a4190401081c500c0101f180c0c01d115175409802941038203800d006003480090300c4a8500c0303154042d200b4001d6645617940004035184e4001902c1c0b109a11a11880b60013260122440140191280ca0400040100030001007882c155250741e10400c4200603180c60160521a007a1a03d00003980000a0006402c0c03091170540c0e40d01c141500e800031400f1508030307055170 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 898282688 1250 898281438 898281457
    0xd0302131502010906050405030c0f0304050915120307050309010905090609010b1c2c0703050c01080a02210a0b0a0503030409050c0c0f0f0d174b010515 67
    0x71445001104801e03401040f8651014100508180400040c41070020040030060303800380886020b211041c441e951240540e009140d030210b0f0b8034004c14001d43c480c81021114140040c218240440021003240c615401408100c0c0c0d50381020911549960300034911030024070055403007204501d81400007401a05050080540980703000c5840c80f0240c03030765a5a5503c07042809420008090612840111100b90f1506071001c40c00035111075400e1040450440100c950000080031090102401522142c40080152a08507400e100641c0b00c0d442400d030020001110110541d401e00780010b2100030765005a01243c05074404481c1041151000001c54003114042040003405031220107000b9407038402c1c0801e50705c4074401c0c412000780d144ca01041041d10004800c0845120a640707640a4801c240b050510401178141c000000b00390001010b0740b0f41d41e01c541403400a22070030b1003100b0200c01c111010700c1080b90184612000440d0007401c58810b024140c115088542038035604801d170360314828100007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 898283938 1250 898282688 898282709
    0x1170414012d0f1d0106050a051210050c1612020610150e15031e1312230a020106081009110d060b04050c0c10060605040b07081312050d030213 63
    0x8010844506a0000030b207074014a0030950600d00c1325041601070a00d50140512800000000003410b18000d804004d5604e410400380c4250143c074a1640c00502008088040c2000c04100701510500491484500c1c1803250f240200100481c05000346015401021400c020751800c600340520002ca0b2130034041c03504145000b40c64000b0150114003036039009541d4400c110008802c0c040c244030f40c8500710142400481ca25207080e90f07480700840380d613030040c840a0002100a210181103d1080c0305042900035065103041d1241100002e000c8a60711450b94580140d5440b88184042d6105002c5804034200e00b040c1070141e40320071b80b80c0102407410019101e200c0d148581c04941000160340007001a071030001c0c41000700d840e10305113a15541e8010004901503008560502a1841d01c42c86104140c84456a0322810b05040c9440440d242e40f01c90400d1316010414402c81661418004400018140300181d2006020311482e0140c5000e84082c41c6c030060500600004848031500c45ca01001c98192140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 898285188 1250 898283938 898283951
    0xc120714030307050f1c0305100b09030f060f090d030615030b01170a02030703052d0612070b040611070b03061c1208090723060901170414012d 63
    0x60702d1441031007002012805a00c4800c080d80d503010540216203004080f80503040c007030b2450b040341101c0b0704440c000c100200e0400c2c103105013090340002d884805405404c407801c09003003100c05844c100040b00c4c03900b400303820001000306405060190200c140c045040a110060402590800f0b095400c00d50400300f40d59a42d0251030344c0e00c110b86078102021100c000500d24180409107801a50049840c000441d003040080307407003401c424101044200e050140440c0003005610b540b00388840140c0600e61000b000c0c0390060247e8410b2120000030004e56009594451401c00003a00500400140c0321903a00b10b100200000d5480c1d10480303500c4501295492281ca50341e000c03181d0100a040d1002c1c116069000e501208150050b00040c0296010001c0382d02c925901e00901c004440301c0900c801d540401c08401c541c0038240040581140007050414031100c00010021b0107450100305c03020b480003562b911011a034078a0038496002c0741070301d00100c008411125001148a40780349116829a245c2e91503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 898286438 1250 898285188 898285229
    0x30b100e01030803071b021021020c0705031603050a12050708300613023a06091104050909010b10030c2a02150d110c0c1207 55
    0x245005001090000d25a07541c5904080c5007941040324500c0204101c921208003001c13110416201d4994000c1a03e020030000560071101010303681808040321525030b11000c550001400039004450941d0010b0034003600c0c1400301441c0c52030388003600040754188101030001c01c8010989500440e0005c4410021002e80340c0116064400c05401402d02840840c5007501005d050140c0c43c1220071f061120300b801142a06868214070302031340e11070351000c01e0b540203098a81d402d40140644000002500c03140c0351410100192020002d840202190900165412050b5085c03207060094085403400f00b002d000b10858600c13641c0303d0303401594410480c0f18001580508250031111032004054042800f0080b000d00107030107404018120b0300450903c070001c3d86a041c0c40103092480d10b0784502001a20341d20b640a00c4405d40030310240c01101c0100f081042c90080300d50142480740d5844500d440e90750000a18841c0c10f08181d044024810000f0458584518000040040503550041098807100312081e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 898287688 1250 898286438 898286461
    0x1110c1b0a1a180d0c0305100608072304020d060f090207020d020609060d140702071706071b0c0b120708040314090a1a0301080601060f090b070303140a0c0e1504030b 73
    0x40f00482d4850b1002607075808100180215400303ca20400494140c4c807003c40c0b4030382c2650400d02800c1c00980c4000c00070860018070440d02e07980d0740103441032a90143c114201041c180d0340300d012010006515248100803150510314440300801030820300311b0900340d581d40000d04814980034081d228802c04580f404095a5280803270f4050340069401b00f00f040490306842c0c0d80807500701d071b102026011303c035400a03188200e64001c0c0150380041000d04090f5031140340546003c0d400f50070b0b2421540100700c144001904419152020b170079030702042d5440b22400c900d00940c00720001c200700c08214509044c0300019030003044600c2c0700c098031100d0640f61440e04011a46d0509030f60700ca19610b240c14454445400c80b4a0001d6050b01d00d5107040e82c00903070721044107441d040d401003402030004810510030010019000050801c062192801040b84140e841c0e40e030546030425121030306241e0b03640008840b9281c00003e41029414183c0f41481301a40350000c4614600441c8400740150510800140c8001410b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 898288938 1250 898287688 898287727
    0x313050f1309050c030d0e1503040f0b01080a120e030d03050612031602040f0c17040c050402030c09090f0709030f140609030c010e1f0b0301110c1b0a1a 67
    0x7004100800c601c141411980d542c0d1090390f03603019028540325101490720899404504800150280311020203821040019030700041c0b059900700a02d10081d400180303c4021240200ba4030002031040b00e08a05050083c5450594494184420b1048070700440d1004240901031840901300000d031661044040356103044645103c3d485800009141d10f08151301c80a0240003900940d0200000c1301259411b10885141122040125060500c41688900c50b100005c1c0e0091040c0da40b40030031503a5602041c160707082030742e450b0780b944804111002c142c01e00d001c0c0207a00800e0b0300c515408034146090041c1c141542c501001c0e100012013454001804200b0304401c2e45501c1c440700304d85c0389107020001d050722500041a807140c0355003080203908030050000b1740514811010707580f90a0701e14a01c0c0e020743c020010682d9503a01035483d80c1500540c425040f015103d281444000341c461181d80c110549035101802d03556503c00d142d941e500380a00d80e10084003800d0803410400e501ea4407210100c0c2d0b0f00040c41c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 898290188 1250 898288938 898288969
    0x10621270627170a02030910030b0d080418060b04050d03050702190f060e030d121e0f1404051002090d081c2a0f0e04020f04080f0313050f 61
    0x240c85541082c501100c0c9071000ca014002d03040b0303140c0340001c03d0b00200248201c4078108010f910900c91400149411660000039080390700300061b41e06100c00c04582d0742c0204400a0701c1d55000846d003003124070081090203070030400c14030041203050304000d00c682c4180035034050140644071891100d801c16024408803419550000e08403a42090140b000b1314220025006002006e22001030008401d03000d280440d071618802800381c180323214000b00441d440300d0a52200303048151a1082c0043d141500003844109484074800842d64001d600d45c94000e846100c074006000900c2c0c4020000801e0020074241034482e0f14402c0940d483c840c1c100020007060719142d000c0c3c40403c1c00035000662000406800c440480b40305020b1050710244101b02003489003005012f45018802840788800074070980c0c004409070000c0c10920515000600890100c2e00840305512049070002028003840c1010072160407010300f0203004524014108840100342d180c5881001d000d554a9403000000d99612054486c3d400d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 898291438 1250 898290188 898290221
    0x1703040305010f0b12061003080f04091b08061c08030408040e090d03180f022b063908090c131e111b030706050106212706 54
    0xc4074a843c4004042840021307104010b1040c110342c2285000c01d006220f00d20b00c01880c2d80c41880d603215034515600c0030210f503a1101d010440414095070610905650002d40c0c1541c2c0c42c0c5424240c805041e03840043d0406104030031117041c2402c03640c503250509940750b41c0512000d0300ca40760b628000105000b00d03080f403403500d1038170000c0110541c400511300d11111703da0b035003d01000403282d682d8400307082c80c084094050f203d0901510f01508146d8010300c1001c6100350012074410020360a01003402283d0421901961200048502c4044031700310181c2c03400c1e0382c1c41c0100341c44941803480708421004401e040c081c0020200000c003404414840c00d40110030240070405248141c81c043d000030001943c910440c0280a0080700007508544561100d81c004000258900340112440d00d40071201c40081c01602c0c03204100c44c000081c01c034050540280110b441d440384415440401c9800701e00c030340440b00b14142c540f000c204014858181d00c14884003c3c0703a01c0881510703c5081c01c20182203000c65442c03010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 898292688 1250 898291438 898291451
    0x30102040e040b0420090103020f030c10031a060a200718050f0f1902090301180f0201080108030a0e040939080703120302030c0c070b091810170304030501 68
    0x2003142da42e8484c6101d454803030649040740c01d40350092500c0d0003203070390400f0303c6400510050070540d8074042c0c4008010300711380c0343c140f80c003001480740e005421968000030f45416144880c1d02c440c007910700c4400d9044500b103040040b501d034014a00880c440d111480344079170b03517220003a000c0305210b003a0182c0500b40e000218200d514100501400d015170b42851303030607a040d001a0802060742481c81c003950032264400401041500b0784806074004d0504d869040d5607030742000703500707804d0a000c0c4030246109483c4000011014000903010482c164800341281c2c20030082c10350f0003540019955407030342c3c00f00c0e40010303071984a050003030842072000c0706405a01d2401800c1c01c41c0b402d001c2082c41c0401c0d01140b261410f035444421031500c4040512004044540c040555402a402a0081d50740010102162030800744025081c0c0d1801520382e010150103880020007500e6418540b44000484000c900c1c1010381d0300f849400c0340300070030291082c9001102400e81ca84c00c0e45906004035002590030400921a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 898293938 1250 898292688 898292693
    0xf0c030501050f0f0402030619270209091203010504050c0c0d020c120a0503120a0908070b0f131a1503070815060a0b25080a0c0b0c0c07050f030102040e04 68
    0x740003d031080c40b032441e41c0c00c0000790b4490071102d080d489a035001e0b000d0200d40e150780c03031800171002d07084460340080ad8030313424882e0a85003403a0400c928290002c809080301a07203030040c410704074006003a59481e50424010f0038889580e5000f203a044410aa8001400b07554a0007900010301503c420140c0ca401082071a41c0100d034002000700c0d0500040b00c400090f011500e070441d41d503040c140f90081c80e40c0c1040c0100550b40001401d6070b40c0c011421a004503808646507108a4079174800383c012210082618244941c5a00d0358040b5540420130321003040d411385803a104c00e8046601c401c00300240e0886c41c030014540e1403504016100030040039013254545502ca01150352168a00004402c007509000001500751525281131000c403122910388614250000c044103010b101e103250000158000303440c5590000384494000d01500a03644d4071301321903c00a20345032114100103081c2c092484e400384911101d410000c0744a00071190704840d0030030000e00b004c2c0401d02a004691003403840e80d868400300810b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 898295188 1250 898293938 898293941
    0x210b1e070f03230414031603031d070605120a0920010c0209011401140702010e0108151302030a0e01060501050a030c030f020c060105030d031a060c1f1506110a020d0f0c030501 77
    0x6a0311800f110001c1740d1003140001c0d6a40a120f140442d4455006e02807000f19000c1da2204103042c240340e2110703a20049284000b4940091030b07000100003240020400d50786510502c1258008490f020180620752207034072841c9840c0342c0601d0004880c1c141505101c4c0580c0110050b00610380e02500d03c0442c1e69640b000f00401203420b200340303804500c2404106c180c400c1150200d0305055416115101840810401110000c800a000345008101200c03009401e543e00c5021011040c4280c1016a80e03203022000c3ca81a150741c101d0000c1207070306007541440581c2e00700007921a031518600d40052004902c410450103001c21202c030006245c400200c050b42d4240c00310360745040c2e030f40a4049410752018034100b01c040b81d4840d00f10b5900ca001c1e00f0002100380c80c045008010b082d501c20100c030020804000d0307000500c08000c4100c01c4c5a80d50700442501d015101d11054001c00c02d40c10500d507501c10a009403038440d045a600240309140704480c00c41001000281403042681001903c840142c0740e01d041070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 898296438 1250 898295188 898295191
    0x50a03021e090a021804060e04061805030706020307030c0e090c1c06080f0705091003060203060f2701060f020c060a02010e0a0f03080c03010513090c210b1e070f0323 73
    0xc5c80d070b2442d00281e445d0b414107015440c1103548101d441e04150340d13a138032014020306005003121050364250102e040458010009040b045000f0000182d4034108241c01800303c494660b682c9050000c80c0e410501281d40e4800310951150081c41d00e1070380d410542009075050401500f44021480c9460704c0462a807100181100b5042103510465400c591521700304010503c00f01c50382c17490845401001e200184040d0041c5402c00c0010f890f003410002c01e00000760040c0a02c805641e43c1140c2042401034146036102c88600400700c80c10080109000b003c00291605c1600003554080d4a000860a4000f4800d41c002c9014840da04141c0301c2070225880c1c844a1307240c4c0d0b61000d03000240601d0201d1100030740c00d41160b0403508001c100c000345091800030307403018040b41c5c4415a44a1030818000640c14120090a06e81020a1008201d03940884c070f0140001c09018180c0700050f900030280340e800b02c400100068101c8800e040c8103002c00c000120440141089c01141510001503002c28611000c00c0741c1c166 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 898297688 1250 898296438 898296457
    0x80a050f01060504090804090e0c0414070306060806030a0201180b0403052b081f090203101d1b0d1112041e080d0f060f0b0a1107050a03021e090a02 65
    0x80c0304490b0f42d68200825a0546500a40413030010001040602c020303502510611103001c0640f401a18400002012207100701849079040518500b00081c1d107030b240c40b82300060091420081d05900f4440042980ca83c03940d01e00a040c003803031028181070300071030710911801041989506562070752240b07005034540344100c29034001c8041c64603014044003802d140e500d552540c0b5640740b166664460402c7c42d582d0007042c0342c40d03080880c03260001c9000681d81c00118810504070501020892800350724088001d8101055034420480e50240101e400844000c00211a0046011603c4242e0890100000d1060341886100c0500c00036200b0001000c0020452007540111081001780340c400001d07070124261100020403540341006142c50301002031384801043e010307600000402030780f80c011489491001d6044130800c9603010981030002640701406020903101d0202422003145042c0200b40c0310552800000c1c81000d42d400c140c50b50400c3c84c0d0300c5480b038102c014184240ea08214800030000c0d80f052154 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 898298938 1250 898297688 898297691
    0xd1d040b22140903040302152a010509120405060406111903200a031211070611180d08070201050906070b04030e0111010b0d111207141c030f08070306080a050f01 71
    0x1801c1c001004c429502140d802900a00f41c0c3c1301ea0011a58180e4040240005841181075244420300c0130038040180c0030f40c40100028a45c241700822a18180140b03100e490408000c00041c820703612500e0985081300d215003020500f5a03040c82e0401d0500480301c000c082c20240307840c011404d060b4002c0c04808540c100c4410b00c116030034003118003920703054079101c081c0c0030583d1801090307540304456000c0315604240a10190416441d569000182c8a124444030240340002c10340484e0480306200b02c85400d10201d910325402c1c0346170742d52803000703024900002e4140400811003603000d840718021110301503032103240219285442d2501404540040041500240d808581c0107200201485601170344070004109a6814030150707510b031449403201d60103503004456042540c188080400c500d9000d4070020f50308030345000511044c4080106040d1010110329803c48040001c203400c00800b040007581c0c4d1501d00703895581ca000940140c04503601c01d024610940c110390082c8900070603240340b10380b00d8400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 898300188 1250 898298938 898298941
    0x61505010e03031e1b070924140a031202060f06030609123a0c090e04080714030408010c080a0b01140c070503060a0e0d1d040b2214 58
    0x441c0c04a54000081d501544100f0801c07200d00c1c0c1c030b4134030b80001c5803c1200451906100c907074240345a010811400c5402e07480294140107803440b500420403c01c0f1180305001000300e007000c041022107814400d0210320803402c84c0c450b034203403548040341000c0c40c1c210704210410001c01000a42d202d2044800b00c00e405901c2001c110240b0f00454014013610070807008001030301c81401c0300b0060354461200140300700c1d08003d811491000c8801900040200d4960030b000444c03814101e0415202007400450401042d85402d200100940e40204d4000b80c0000019494440314640341492188411014210380f2000c07800044072941500f04403d110026551980580c9071416040140c5005c21500c40c003040c00d101c0e420401d00300c2d03032018003144001c0c203080340d607015a15400f103410b204068400030483d07a210000c000b9031000400098003a081c036803030f0039110b00321080c1310403004c03440070000c0c00c0c032568552204886560707440c500d03050040903442c10fa1844c0c4c3d4042000e01c000b000403e00114000c00c8400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 898301438 1250 898300188 898300199
    0xc060a0e10020d0923070609081905010e160906080c1008130c0e04060c050a0806060f0906030f0117070605030c1317071406160b09010b0d0615 63
    0x1400041903100005100490428a1107030103034101c041ca28104560311408100811505505199006058000704941402c00004182003280c5030708945c00307100c440241041254000030709240148a60306150515184615020f07000d06205060610a4410041e183e40c04514400e4404115120001d0420840e42e50b01da14a440303281001000d9401154108040a1240142003156007d80c1b100306200429003203a85400300c0f0312254001d00c00380300c00c8404200c100b100b94454815451071a00b0030702e0600980d503a0041c00d52500504480c090b0710b000c5040740d20300310860150f449501c4010411502e900d428041021152400d11501386100d080345550b02400d000841c5203406c0e1481503650310710310380d20001245d0550b4080030407242c1506035500000340305040c00d01c3d61301d0381c0315441c00605003c600e4a00f8200c1080d00300c860440c40781004110204019030a2072481101551000a045107a5601c1d5071040c010829400010b4001460620203801c1100544c002e5950080300f070700d0b0f48443ca4840707 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 898302688 1250 898301438 898301441
    0x110405150a0f0302180a02040509042a0e06120111040b03060310050103031413090c02150a0614010c050f0a031e0c0b181f02040302030606120312130501020f0c060a 72
    0xd03c00a03401c04090100080c3c0c1c0b40c0c801c1c2c4007681c82031207000d000d480c241e69007000c17920094040b40c040e0b400c05406490240100400c881c044562465088440101070410002e61501c603401f80c0b400c0e2150885003e00745146032700f908070390089100c5c1c101d2151250f03629107036600180e0040380c502d8403c0c010301203455008091441624143c0c1c0c0c240c1d54040c1d055043c4000c01640743e100ca40c0146111106040000742034040b8040d00e07250b180141e01800b102517603075845080001b00500940306160404500307101004500c491611401c501346007882c1104510b0500a0030881c81001402090084401c20804d1641041c02c0c40320f06603040040744945040d8180817182c01c02010301c0280b01c0751402010070070780355604c9040702441c413110080e0351240340306517010301311005610440414617402241c108258501441010352141c01515039030b682c0d802c0145160b45a1084a00b013075191000c0501007010b60000d10180d0240c26400002155641804255006c040c1c110761002c0340070784035050000d00c00c01d03010b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 898303938 1250 898302688 898302719
    0xc050f070819030905031606110606100c06090515070f08010807140609030a03180b04050603041223070c060f02100b04090206030f0402010813120c110405150a 70
    0x80600350825600c0a5040302c4200c1c544160704200c481034002c50035583c24041e601a0f03064407896029264501314000e001c400e0011158a40707500070350104170543d105c1c072540038800c10003842c001c40b4109240c640b450050500c1d5a01800612071500040030b02404c0c681280e00450040c0c070b40704501c105152048501d0482405003d1185c0c010440400c55201440401c911501d0014401c0e82040c1104004c280b808140c500c0603000601e031000071203443c05c0d10340207440240c032a00516a14140c00d08010850034800640018045415505d0009500344602000401d00740000210b129610a950308185a508081000c0c6ca0344c006c03407000092464000c7ca0350b95844650368009c0c190007104840001c0042c0b036101c45103500551102251001030350303000000d52040423290400c00540c1090b0000401c04603004200d904a41001111000070035080a4605181c100c0c91400c001039a000d458802080321581c1070700f075041410007003400b03a4922406009602400300f514034030742c42950341060311505101c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 898305188 1250 898303938 898303949
    0x60f030c09051014060a170a060311010e01020703140a050d0e0910051305040309180f1a060412051c0e030d091a1605030a050715060e0a0e0a080a0c050f07 68
    0x504c0c0d0b5a400983c10540c010b849030410b6403d0030f050811800b01d9655070703510200e403400010759a40394240104045801050003c40c030070710304486201e11560020307688909501002c0d21050460140d810116810021416015402000e4808003008600c0241099403c0401a4440c124480c00200078081c04c00c041d80448100500c2d0200c8458001c5066006008c0640b06804201404101158000c004c029a0041c0c254001c400546034001d04400c10864008120b4100040030080350420240c2d2a5400c0e81c003a00e0b0780c1403065411051038a000c03850b0010000c1c0704020709d4015034007501d10303d8120700c402480040a5040c1c0c0d002c0c0c0300000c0115101c912038080da0310745450000d03500d5051403030300c0c0140c1501c001c46495602d40b0381290316410b00d150007107040c0c0c60002ea40080d90b6801c04c890780b40203443d81a101442440b800d41850281c040c41c441c02001d554410b0f80d241e0110544841c1000300c10100d5821500003603030340d007e1980040c820403130985c00b03842504c076034450910105400160101240c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 898306438 1250 898305188 898305209
    0xb03070312080901050717040c03060c050a0908070b0403170c06100e07090e24060c010c110303010302100305130c140307080a08030105010806130606120b01021c03050a060f030c090510 81
    0x70a801f02c1c0b010a00c102600c241d87c84004c10002000256082c4155a486d010a8590035202c40d00341c040204403030f400c0d030419251900700580c01c00c0380b104107600790342c20380398409140c0c05800c44c1040301c4001406500064240e922460701805140f03000d40f035040b41075541c2ca42000b000c0b80d031a52030075106c5000c0c0d4458543c1716802d001c00980001c00c00032001c6010b01401d40103a8101c030880c400200380f074000c900800407a07507448a001c1c4a05800545881451952501441c00d540c0345400003400c840c28051403c0516403507100007111810030740e2240090070740c01940c5845503900c4488140428110088141c024402d80c8004100300b900015000c1a041d40031100926503800e110045941d0903015150a8004960240c0780040c03407460f0041300c028100302d64448402d0350816610505a41410101505541010040b141c0c07003031440d1101c11000c50b50303090101b0315864503140c4900801c1d0607442204400b401800100400452002d0141214040f0409000e903403a0b02c1c00d0a005581c0500c52a40d001c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 898307688 1250 898306438 898306457
    0x190f12091a0304050d14070501060b0c1501030f0b0c0909100302010905060702130e032506050106050a0206041212090501021c02040f031104090816260d0905010b030703120809010507 80
    0x224810802e1b0582201e1480e40c1e2420003400e40d07541402d60704242c0040b20104000710782481c00303003000c00003080140b0205480b82c58951550315a480c00907200c86024191080e0400010408141c00341294170514003d003407281c45181c00b40f0084450862400b080340004c542c3d110000301d80c030301141540d08003900100301d809a0f0186407140070082802c070803040028001400070003a070700d102e4082d580b0303180d5401218613568822480d010b8120f40c0140c0000090000902244031400c3c0c0c002085a0300c075610600840e140c030a5070801340e0301468103007030b035020740b1b418018010100401034018006000d0420350311010206111345100030307401140603802e1040d42400c410000314101803856003a511001e400002e44d0750a43d120044254050144a1044e038180c41075a01003084202601f01950801c26426840c0175016060860070720131200b0b202d115a840d8100300050020a42c8560a5568003d00b100c00c0b02d40d40740381c80d03411402c2016840020400c1500041c14500043c090310f03119041c0c607520074120 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 898308938 1250 898307688 898307713
    0x3160b0a11010f0507080103050c061810020a080408010c020712031b030306030b0a090203100e030a0c03090b0705010b1302040506070803131202031c020903190f12091a030405 77
    0x844054589911150348410b2000c40e10300b00341c404c840c00b920143c0d448491540c11406d10501d400151441d660150b00c04200e028a52a401d0141c00c8614100b1030715402843d082030005c0345803a052420150415000080005204805502c40a13011625800380c0c1d504d51390320800c184e10304402800190110b07084030324140240c1005c002e9034000510909000500d6912510355034081481180c0641003165a80c420105618081004000b5107002c024144035004020072101c1c6c0702d005600140c0144102a001c0d241094046e207031070406030118041d929140e500c5410218041d150b41d01916000301c00550f080d91007071115008039426070360b0281006141c082e840c2e4a49100c2e42c401404805090088424030300041c5003007010710248007040d402035840d14025114090540c43c0310410440582c81001070810544000c640805103603000da05000e4018018102141c00280c1498001d00a00c0c3c030088a84407203070040103d4081c0c401c003a2464919621070702014600744419a0040d040d5404268142c25 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 898310188 1250 898308938 898308947
    0x10e09040308040c0e19061e05040c0c0503030f1005030a0302030703050a09121a010506072f0a08070e13081b01020904020d1a0d03173303160b0a 64
    0x800c28032605488900310b94070545c02403800b005075220342064111429140c0400014001c103005082c0c1c00300c600502c0e40c070090781403101800a01c60f21740203986820100c9806801180580081e68000060f07a980f840c5c12254800c075040104c0d01c80101380200117000c07449060000d400c0000c3c55060300118070380035150320103031101d411402c480750400640c0c1d50042000840c00f400300c50558454030408095611010240c500c0100580045014050501c0310340041171450400c105012007c0c60140032060740000c045a800110201003504880c1440c000502248001010303004c41d4101801d81405440384040040c0640302d1800240c0341070380600024400300d100e02ea14041c100c1161000501d0b0a00303120114090b07030800c5807250020780c3d858661740e000d1095904100c0b100d420446a110f40310301141e902600b60207041103101004006070b000102c4801c20b040042100c429801d201c40361a10039031150060108900d1101d502038020704190046000c1082c4020040d03548090905050080c80d450465 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 898311438 1250 898310188 898310191
    0x20a0b0f06190803030702100b011418060319060503030306010804060506180a0c031112010612150b0406030c1812030c120809190209040807060e100b0f010e09040308 73
    0x40e40003010181482c115145150600000c05045000d07646a2410803c081d0074280c04207801d501d12810070b0302c2c2140c580e9200043c0c1c9208076140c04031680300c603560010070b20b030700e480462071a401c120004144809103001c1400e10416509150b014032005071207105140d20b81c00180c9119001c1303031401003c9000104c458100b594415009845000c1050300529400e1100c0b80c01c0e1a041c4185070b4441e13100c0032255250080390058505021081d10b0f1102c0c08401300700c1c180d01441440104040e440710026841002e400108400a103070f0704503840d060710341c526203034035a11903c1480c01007440c08060303460440c02680c981ca03d00f1342a04500040501d030280803185c0d4a1080710403410088900c2356103001414241c55000d640c0300c555101d1015161541e00980b0f45522501110030130683c40515200580d01c414110754841d80c8080b80030b03281c608501e4020050039010030408194069240071110155103680003130941002203441000000305071005582d0080d4001c001904010400b00240c003003030041d0701c441d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 898312688 1250 898311438 898311451
    0xa0204031e05030c10050a1a2803080d0501050a061b120c06090b061c05071a040902070302060604050105040e07210210120c030203090d0c050715081006020a0b0f 71
    0x341c2c80d02c1a0070051504140c0510301460f0801da1ba1001d000c44140310b40700d04201c401d2020030b5000311001c40e100280d222500c1c1056804e2000444180c3d01c0003500c0091a28001c60b880495030b41c0326903965a400c000340000f4060140102d080340000200c940c800d1f00b40584000c103918441c0031001e0310b500d1302c00329901ca0400d01e9044c0001120894001000d600c9010000d600a8441c50001d003401d40411001041485d0304200c0d10a0f11400344010910100320300382103c040d03010301500d00c14406800101c07405150300a52000348049030000a150b0041001841000308540c200030580e22241000708a0313044e800d841e030450f4480642404441c0201d02c07106440c1f4986031507050390002d2540000c2c11f00100d9000100042c80d501525002e40300240900300d0f000d200c9042c10350035454911019a6900d120700c0c0002c041090b03000164082c044c040c000c0101400d9401800340f841c11078007a0207490400f00b5a03080311054007150001441c107101148101426612601c1b0100075221841a000c2440015104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 898313938 1250 898312688 898312693
    0x316061716030b040b060409021b060906010608130206071a091b06030402040b061303111f050702281a0304030e091815190606122d0e060a0204031e05 66
    0x20b00c4041e1b5980005003008041c0b00302c01503035400d990300440300b0840480002c81c006500c1042800303285080480c45a056074100e1070030080319030301c030019403281c4034031018003a42151002a12000340885410684400c0180d40310100258a5a0386072545d078102c0c40d008099070303d450844c4800145807510041d41c10a00051012454442010000300350340d02c10030113005580f070010801c00c01c014454001c6100c1d2081103070345010303801100720740042101c440d0742d03043c04103e00003508078110740e40c4148942108500b203609150501c0015215610013403030380a51a00c80d0300c1b40f065640452240812079104a40c19aa241000c49140090203100e000c0900080c03042202281d0b603007410310b8200a00c81001c40b49444119080c10003030003581c0c24040c04c40d0440c90060a14000303104282e000881c1e011303000c0c0380d42d100040040803504640903c020320903010703000c0f503000810441080b4068000c49442c0380f02401b981c400b43ca58000b440200c2c07090307120040c080c0c411851248081032011003c0c0c0c040c680107509 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 898315188 1250 898313938 898313951
    0x4210b0c0c160b0309060a020c03090607030302130306060513050c0a030e150907170a21020102070f210207120f030509190f050117240316061716030b04 67
    0x3a202242103c0d005001c502001004000b49040108011900302207070040031860903c0216036143c40c1d106502000340600300000b03100c02010b12030340c11502007004140c01d200810341c4900d40000070702458880c0f140b0402070250002140200e0b8400c00303005410101c20030340740c103079600810341c00303802080713000d801a000704020505413144000f0300030310940055024010450808090046540442001c0304081c0d101e0340200c00018012801c0304800645c80155001b04211b202003240680b01c0c589000b4012581c07524080704101c05035121005210401100820305010f6401c200e0303690071240700e55500451083c0750318000c41c4518055000880c02450201c1c94130038008041b41c10b140000820409814829034200451284181401c0103070200340b80c03250780c03540300043d60071180002500c1034000c9a0900030f0f40b100c0140402c100c0301c0d030200142c00d40b484c3c0d200c40322242c200840c2900c9014045a000c240030b8207070b49001c0c030342031b44101c045010510f01e80840c402c08500800d0348420058000b581c440c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 898316438 1250 898315188 898315213
    0x7030210020601261005190c0201090b0a021327020a08190b030a2d030f26012309130606050420030c070b04060204210b0c0c 55
    0x1004480d031001240c000784203039450a800d6810358000e0500c0d02d01c0000c4404100c15501c030b0041819181400108008240b0362204510500459000d4100c1c0345260328000d50380c024141c041d00010300807402103041803019942c0c2114881a41700f22546200041d00101041c080f9010000c0215120382c65002c2906188819101e45800c9070700130014180420010b41c01c101034034100d9044502c400841300d80521820304400c0200e035031010304041c0209486044e1240d40c1114000f0958654002c0a00c80f0f00c0b001403040c1d060150243d8000c6140300006032030703032200d84000a82c104040f10740800070740414500f681b80c5030742c031417204000e0741918011950410000a50f41c0d600c0180701e004041c0c1c0034000c980c4d5490362400008451140e8001c6008030b08084d080d40c1c2e11405940045c0650840a40159495841d0803504d01d003407044440003000000010180011700c2440d501034000c2d140700703e40c40000440e0300f4488951101310148000c10780c090510014180c0844d07003024044004406040311400807214 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 898317688 1250 898316438 898316449
    0x305031c090f06090203160311010509031005010b22081e16030b0603241f080601030809090708091209010207080a0f060c0801031205090609090a090b01080c06031503070302 76
    0x4050596400703031130f940d0140a528007444a0003070102c1d00c0a0601c485842c55039910704103040d00000e01e0520070301051268160322b0500c5081c000c6211000108015a11082d4010f0180c00800b03480c8000f441b0191540c949090445000c1d041e980d11400818060042138040c0010b8112508480001d00135034032082c030940704010011020754811860800a8034003401418031703000080d0b49404240380c1048031000e0700b400f14440c0c5038000c5082142200181c0001d2419010207001c0e41c8120014421403000206019110000e4072584a08481d90140c80d190343c1412100c00000b6a01041c081c0c1244602c1000d24040b4002801c1010060064502c4195509025070520400c1074003030f038180015000680c20004248100b14140a01e0301702001503506544850a400814103114400d001000030170a03000d544800640b00c0d1450000c190304a83d103040c03803400c0c0c0038001d0254202c6e001c072901030011800000c00324038604074030b01c0a0041801e42d03030369070392400e018211700240304c0e0180107034030700800075841d01d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 898318938 1250 898317688 898317713
    0x50d02010e0118030c0816051c0e0d030527130b0f090708070c03050405040603050f0c0915091306091b080304050a090e10150e0f010305031c09 63
    0x45400006810461240c01c900b51085401c1c104660100010354100080e0028000c3c0403154020584a0b100e11181501712085000800084d1440c407030070981c06140103018004010301031450369020a10003542041c0000c4854104000700070800a03c000745a04101e01e4000044c510a5a50700181704400f202141144902c4c05140c5201d648688040c41c0504190440690305032041e01c1d420103d00d46988024202c400141c0f13003d0800c05070900c20400d1511507416a030207420018420040140e90789041d42d0764407005110101c85000703112a01c181840c00340c0c01c1510a030800e040494000b50700c2c004001800200411901d1505001004000030821521551070094450080482141d81d0250210301404003588a105250720801040c46161074100590007140c0b860f1002007000440c403606076017070044030075107010b166203018061000030f003000400c9821100f02010f00a080e03110028541c030749100034000900268020070107410080c0c00400c1041100c0d05070400045c07015525566a8011804c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 898320188 1250 898318938 898318963
    0x10518061602280e07030905070e0f070906020705041e090c05130e0d03020c011b0503070e0607050d21050c09012607200105010b0d0605100509040906020705 69
    0x500580300d0342141041d40c9000a909440100701c0d40c0c0e03c2820001940304a040d009000c8400215804100c0940c080d810010f0042c2d400000c1e40e8115403a00142c0511040844030811990b46100110f1541070080c0d03254000c2e9003039940645201d50424040c0030107011103800540d4110401042481c3e1081d03548034455005129401c1001d51629181c20000141c0d165144000c1c5c003403429081e0040d0090018414640496504001d40c4851400c01810300512940441004c40a2002c410a10040d407080081d841070911707450b44265003030030380240000c0380034609000b0030540c448103a005290340130300d4458005564450303110031a1020044180d0070b40e1804c0d1810b01d40244007140303109503076800c40d000d0400880300d03080c0d44204211003d41c1c1d1842c010080c080e0300600a001c04061100c0003440005101841d0300c1000b4403c03540e60f803022441680c44444505101490300c08003090510740704182050040341c47c1d45540c1400403060400000300301f007400440c0c0499003009420001841031000d0141c208 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 898321438 1250 898320188 898320217
    0x190e011404080d0e031c080c0405060705011d0a05031b1609020d20121b070b0105030d020c0105041502030403061d06011a04030602030a0e01242301051806 68
    0x100c40c650060102c42040d0034040c42074120950005090706c0d014010f40c100c81082c9000761240d21a140c0d91280c2c0c2c800d6802050300288001040000c0c04015003004080c01500c000008106224903e4151291120b4000504542003040384441d2165884000840801d4040a4440980c00103e411a0740305155014900d501d0300851100d140c1010b41c442d1000c4180c0c0e900c0b00600700c0400002c0c103403080c41010405042045000b01241c0403d11003156030421a40c09011030303a43d80903506115403040024442e403803080c0b0503070005900052003c81e4001e17540318103031540c1e4202400c2490b5103850140d02c490713500440c8401c0c0000070116007503001b045c3c400081e00c900c00403c4072401e001c560030503070140c2169041980702040080c1d41e40e9101c0481c1c081b2070700718000503200d0710b1724071032940601034695000c0100e40c2480e4120f0110130380d01c20000c08600c030300d291500d90640e1303c3e03130765483d9101824a50f0401510704900300f022940600c006000049412014075070003883d030000078140340c208414103020380c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 898322688 1250 898321438 898321453
    0xc0a030b0a0605121f0b06160c030b0705121b032202090a0e0c040504020307090911090103060c0210050906070c1e050706030609060302090c07080c0304141302190e01140408 76
    0x140c5c40b6509140c4e112407490207100e12000d00012800601c1100002500d2980031482c000c140202c2051580140d039101807a40307820300384048014440d80142c241c1c0d10036040038401043d82d42510700d90301030b281340394800542d04540e681d000a0f80c5e0035043c90032804504000c2195a0010ba840e40c2585106140c4450001250403203443d51520b0000c1490030107018500c0c200034070015a0340040d907181200c100c104080751042607442e001060403500310115802050040009c401c0240d0f42d04600340e452f080d94200c1306c0d1401d001c408102a20b2094960700b00e9a000a400f044030503119242e0500d156000300c0d4010f021849150316070351306007560102510711f5008000b052214550500880300200041c4a003482581e045800003240c620010300040840d030b400061980402007420b0940384a40310b21310913240c6031581c582c0b20101d16503002824074070801c841c52200303c0300c504d2413017510485034004101259540d1010005e48038003a5480115040c4403100340580303288041740008002408601020f000c0302c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 898323938 1250 898322688 898322713
    0x10e070306060804020a0e190e010e06061008060d0804051306080d11100513020d030918060e2a070302070f08030a021f020d0c020a0b090c0a030b0a060512 68
    0xc4a001d03411440c200b1581c00d0501025959403040c5400380c1c1c615048080042d1503600081805294402c1403482c0e55081c0900b45804100642c840c3d030340342038108140c40ca59074441302000340807401e1041d4440403603043c201103030503400e040d00100715a5104904280c5020b4031640041c06891241900580040d1103480601440314140f01c0b002c1e15090504049407892107002089172036407000349080f080030780c0c0c810020320550728000b80801e04640181a0091081542c10700034040819805171840da422254903505110030540300d03510403102144074482542c2c0300c261407000c000344d140c503400c94444e221045100c04090395000405089100350000d1100034030341a03229240d821103512041c0150814001c041d1525001b04840701d0303400d403043c540134659110900e564024010300030108209890090828027407900041c0e000e6045019101d03080e865035910400941d5404008230964101c902000200001400418050703002000118041045500d440c080340e0a0a40d0143c032006139400075034107501 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 898325188 1250 898323938 898323941
    0x30a06060203040b0901050d060f0e040501050c030402060a0f03060b1308010f0b0315070c060c03020a031d07120303140403020604120809070308030a0f0f150603050114010c080d05010e0703 83
    0x510302400507506007454005180307024040e070b000d040e05100f000030381c0c6581d907030451744084050501c04501942a079154211480886401c9504545075072034240800c1030740c6040005e484c45154020a40c500e02800d00d5822031b1030aa20082c0b520506850b43c0020949803a1900607101030144420756081c4140b8003c00e44c2c0c04d40b8040c1c0325030350180341fa01201c0000d90b10302065891a0b41066070314901142c440b08030881d120b001ca0303240904518900400c1c00c102c0756050300200940f0070295000e210350f8890702e40c1140d102e2400c20402686511200e02000005028491050041d01a040000c2da0460610b8440c1000b00c084904030016044502044200211440c1508100c5101d1038030102034030301806101d03510305d2140000751404101100042e45545030380c000c149540d80c690018000a074100c410030b0046d0008007524020314100398404100d9500c02d111700c0d8104c0300004400c5072034504180055900d030083c81c1090302c4041040040c0c1c6404c001a00410f4001c140c0000e000a2a2401940080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 898326438 1250 898325188 898325201
    0x110c13230901021306170f270a2109090f0b150d14090d0e040f09051c030207031205040804031407051903150c030213080c120712080a030917030a 64
    0x4043c4903846c880600390740c0101c0051035201c2042900c0a846031214160a008900240d03030b010b040e001d640108040b4034030003061203007000c3c0c0b1032110310504d21328515034402000e0030240c4980000e1103c1104020310403c0b50050240061580c3d8005803808510000c1090480c651220980b1742e40d0000d14040c81c1002c80c400d444655140d00340307010f400d05182c0c0c212034841c1c4005000d0802c000869495504503a120b40c010300907100c0b00082040200403903c0c005480703400c0030f1444404090303403551061505000b4002c44007000c0d41940c3d102032408503405250010100984142e41140c3d0a000100c00215005071411081d00c40c0740c014400350740751400308030310303110314801c1c165032011202000c10010311142020048034030f03868000b1400e081c40a104030024082c403c4902c02c89110031800142c02c1c03602192604100348251400c43d040842140da10307035545001e21410b040e042d10080d0380000310b103403000580031008080c03801280c01c0259840e504a201c500e0990102c0e03051001061151404041c441d40b07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 898327688 1250 898326438 898326449
    0xa060812130e04031b0203240a050105090601020a0b1807061205090a0b06040c120c0e09060607031b0819032307050d021c02120403110c132309010213 66
    0x20002c41c6810381d401020031704400c0030245101d41c610703055000c66400348081846600044c41c6020000c6100161004080c0b0a0f80c440400c00e14110001c61203062001901c0e01c114010f030000c150509240e40c0d84261355000804040d03140e9503c621070f12440d038003880100010700759941d56011090000d940c4104441000e000710701d656000070342c1d50000422510200364002011500000c10300080740059a0385440c007030022801902d000701506505820240032081010207851455540d030b00c0c5002c0c0700c6148200800500131410b0343c0543c0304400d801d00c02c04c83c0024412401541000c81002e9616281c0c0300c0c0071000c0b00843c2d04e60214601da400700c00c88408988684490000e0316090542c0c01400c0780c072541d040c00c8200c07500001c0707210510840140700d0456034400407045646800d091b54000352241c0903202240000c118144a001c1e41c0b4000408602c4428010b000081840300301c854a4020705041e201100700c803102d402c1003038080c007070340c0407542c03062079840c00241c3d94840d6400070120440094010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 898328938 1250 898327688 898327709
    0xc091d01080a061d0f07062a060903021c0906080c0a090608061203070501060302210705011d1c060501061b06090615030f020a050d0b06090a06081213 66
    0x4024101e00007414040494000710300060b840c8102001400701c80207013100b203103a403080c090100c0301400f001a03001e084890030350b1900400401010900070f850500e007081c030304440302107100300007083c000c3c0c2c4007152080c07090049403000e41c821085048003607032403a400f0020a1030800100b0031103411448042d4040040e00480d498903070000405481124280200d60810802c0000515144c4030708588001c1400c5c500101e903100d048034035020b8041d2055020880c0103608154007206c1500384052800303802c183d228040d00d0800e0801004560042680040307818051034076035418041e440b01c800e04200980a404c800e45d2414803400c1000c00e842040c0e208000b042103107041d9014041c5410b203030a030115032281e40400c01c540b550034000050301c00000c04070203900045030000100075001203450700aa1084c2c1c1c0c0003d445994404201c03000c800050042c224050341d4001908502d01a007495600c182100c2c1700060558036001100d1501c4582558485041d00c00104c1124a2190b82c00400c0141500f062 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 898330188 1250 898328938 898328941
    0x903090504020f1b030f0c0c031e0a0f060f02070308720d02150601180305100212090a0819140a0504050111060f060d0f060c091d 57
    0x520203c580702c1d80c080000310b0070381d18144000c071850900484441d210b941d580746803980040b610042d290500c03034244500c64410b00f44845401c61403c400318440c148408041c0010070182e482d000480d811025003101c0c036a85e0ae28441d0344220161015018140c02691540e0513071400c0b5802c054604070742d4450300c420061410184000c4050f01e09442091034080002c0030340008640001c0724a0707110150001e4000c124102c6048840402c2d1182d2100040c50401719601c40c4180481039803104480380402c07800310508800030300954014540c0c5441c0200031000b0a4100365a9290310b030a0040803407480c449190005041606110040d12032a00084d0302e0003d40304801542c4d6501140f44541564050350440034030100709802e00030412043d04107022041c0681c0d0301c5140400500c26445809813502080f41c0c45440e400403d000200141300d4028200d0408050700d41d802013000700480384000b1100383d800001100e00142e00c5002d241e4142c411502c50480b92805c125030540110070004503000500301c800d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 898331438 1250 898330188 898330207
    0x20103140c19020c0a17160f050d02060d0908030105011119030e01230310080c0d0204020c070b070602031012120f0c051518010b0a031b030b0a090309050402 69
    0x1021078044415158510300c0340c0740864003e9043c810340380c8001d544030300700040020350030f00741c01002d028400c1204141d808800c0c00d000f101403401c3d020300441c03a4400000c132040c070172070800d000210b843e280014507803070030100c1441622081c0c5921000c02c40d09000080010819035030000d54186c51600c2c00070241c4058242940c03a03121110b02d03c2e1001e0308000c01a0389010581e405400030b400e172090b0a080c0c080042c2d481002c007281990050b58801d0f42c4103030744140014078a03c080307905a0000c42c0103183c201032200321340030800070350022401c680c03403030180590028012204200400d1903520690000d61685440c40320091200c500341d0002c145031000000342c00020300c01202240003100c0c1810501c511401c058811500f403a02000001c04500c551414904105100c10318148140c0e00e0402a42032441a07544107401d0740d200c42403254000c2d040d15001e200264000d80c0d4060301c0009240820740041d0760791140300100a040d10180781413071b906d00d40c010074103a0142c4030f403000d400c00356030551916910b00d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 898332688 1250 898331438 898331461
    0x2120c01110f0c090705040506070305041409060f0907031508070512010519021e0c01050a05061207261e07050402030f010506070c080d02070501021615050d02070210030902010314 79
    0x10b001c40c804d1520a0018441600810030358010700310151800d03484140e11b240240c000c1d4818001c10b900c13941301d0003003841d613442c150044034401d80011382801082182001480121903000d030082003031507168008005c841c60707a040008010300c601c000030180b030703490403040c00102c076003c00320700d4250b9040000b04403016440c11845050b030082100c006070384440243c09140f1540f400d04c59100700403000121500e110205400032801900302c0b440c1040162103d4041042888007100902510340241801300040c24041010f0800e205514803040034549a43c2c95242c18024551038942a0300070705403100c0850901000018003600c0c09a6007107286052801c3c0c26050201c1c144180c0c3d1291000042c072030100705040e64240c0c001c00280d001c5a0740259281c5c000394440f030050213001e0051160000c508560b0b01041190021256441c8155500d00c040420449095010448401f0a84c0c0c007081080016290301a10310401985a940014100b0750b80c030004003652004200c00c03600d4682d82c000c0c0008084070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 898333938 1250 898332688 898332703
    0x3061018020f030c0d1a03060a0c0507390b041701090203060114042906031b0403060f050106030c0e1207050904050c090106020610140a0302120c01110f 67
    0x100212448540c84680c404406440740d240b010603010b5002c07080c40003101c1c41801512040402c1e641c10300a581d46003080d0040b4100700ca113050307410340c080d90220f160021a0342c04205000c0051038828034125407602e607910f0101020324100124602c104540011000d20b1010301290521401d0402da002d1514613403600300d01030f5002d01380d041d0200081511030908254408080d0950141c2034500c1581e5500b000100640070010403400340d0704056440e6807403980320f18803200d218585480060001d184d1414000705800040138150300c00e56590000d281100c0300c00242002703511034080450701c2c540341c031001d074107031101a4409010705003803004002e0801c0c2c2260341950017500a0303500140111f08255114030b800a030303600407500105520107000502ca8082180f0b400700005980340022643e075880c04030381e03d110850784194020081d02c000c2c411940b800c1c41c00081c0c001c0c004c0c41d0000715600c80d00001d005490400540750030b54420002101e07556088003000800121900c0038001c0490000c480d56100d104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 898335188 1250 898333938 898333949
    0xf060c0d021b01050601030b010c0c090b061201120201020706030605010c1502090604090603061a0a0e0c1b030d060b03060a0b030604021e130b0f160f051006050f030610 74
    0x6000c03580c0c506003809541624844242401002d0002d020080668002c16081d11106e0020742040c510060950040003903580c40ea070710a60b01c1c0f0080780b80003020f200401c149544240e00142c20446803a0505644040074007a04c400354200180c03038428800a4074002c030300c0d40030f8000d150030032804020903a00300c11104070b925004241c801c440035002101138001c1c464041459881080843c001c10007a406030b2000043d00e00c5004200b05e108041d040d6032682000246280d68050180360b070911410681031400b070341200040440608003000760302c01c2401c034441090b280905034400320b00043c0a001d2802642e00420b00300f58064650305012010440e0381312640100d8100768000408940c0036282d5a0485140d18103054150320703807440800d15080343d540008001c45002c0e40e0360f000411041d26007411180c1262540302124a400900e050284040d629880d041d21504081202d0b03402140b420300c0000e0300b0100c1d00c1d60000e101ea0620080000c28900742d000d40e4002c3e40420200544070580d800c04005664 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 898336438 1250 898335188 898335211
    0x200c0612060409060c0c06140c0f1c05070507021e1c0212060f0f01090b01022122081218120708030d0b0901080c090a1104080303090a050c030f06 64
    0x340d490001c81d0290030f803602c00512035450a945428000d034082c4140680a20402d010303c1542860841282c88210079181140d002a04211250000003200001d08030701151480c134051803420030071030200700d0310100c98540c00b103640003c0ca5803c500e880702c401c0300034030300b0800740d0304071402040003007140014001481002c10145c5c1a503401990303101040807070030007001c0e01101c1c618a84a81012a004400c0e100b11101902050000c5080b0b0247c0c0070b42200141c06134014806e083c4c1d64281d6018807984c406000000a00411140610386207500e502d91405c481401c0801b4144d291440c0c1600c1d25070540c0754043c41e0041400791b4103000c0f401c101000900003080b1054092802400c890604000c800da00c141030798400016420b011038402c0e0806080d10f0000c03101c13050035a907600d818645844e0b50314001039000c070035030f00001c105418030f0380440c140c03843e01c400203030405844018040c41c0d81e00a903448074055200c040702c10704000003008545c0c1e9140e4140c01030000316010343c500c00d80e291006004200b099 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 898337688 1250 898336438 898336441
    0x180102120f15130207060e06010e040303050a1b0207050102160605030c0a1b030f0810081e030d0c110115081e190b070212030c12040507090c200c0612 66
    0x9401c045006000c241c00600c200c0390b8030090503c2d00c000b5804800100d030321900380000c03160400d00c0824a1812150b60313803499440c90751381d5a07044008200041c1481401640c070020515105007404064000c44c00d11340061484c1130802001a01d021b41d41262000303000c403450350a0050030750041c01c1c3c0e0741205907184031540700e4610340415240034010541025060302010319440515a015218101890441d1a2980161684460440b10700b043c1c0c0942d131081d503c00c3c00200c200f10700e08000359403800c000100360b82c2466010310500040d205512401c0c00010845003039800f400700c0c28401d178a01c410f854240f100c1914030781000182c4540082c03c114513641c04124001c000c1d80700c00d0001454104030100203200c03100c0c003490b185400c40c80c151659401403103240000017000036450708a034081c030654002c081c203000c2d141c100040d400700014812100c500403510300103980d40c010f0181c1801282c890b124000f0644003000b141030124025041c54040c1e92024180001da625801c0440d100754003141e0a07030000307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 898338938 1250 898337688 898337701
    0x20f090402071e1505010905010b0316020f032209020c0706053f060907090909050f06010306020406110304051c0f0f0c1409040b150d1703180102120f 66
    0x800303d1210300f0307074208021501e0010810058442d00140720804103020070499072100c1e099011203030f00b401541290710040000c520601c0180e0703090740382004036204031240006810199800c542004903050840906500f000c949003c0703003c54040500025107046081141d10801569140d0784d038402e1000340b1200003510014488803100c1e2501e40c00509040c02c104505040c41c0280300c03803003882056205a846404202c9a00c3c01100550040e00f00341e4980c0259400d003200640208804c68080fa110b1003401004107404c40d0503c12a4001c0d805410010380b9a40740500190511a20141118a0740c00411003400180d42e000300c58200c3e4210140000021011442c00700f0b8120040c160207810704051054070070070065184040700542d81101c5150000c1203190017801000c1800741e8004043e81c402000080c03d84620b4400c1842c0320000812030798240032240c1350f552404c64641070360007281c140001002200900c03013015004c80f071081b4008615101c0100804054980040c01650010307141c403010444 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 898340188 1250 898338938 898338953
    0x4030219080604050309040f090c030602030703020c061006140307091e0504140108011109030606093d0506040303020613030e030706030621030813031b0b19020f09040207 75
    0x41c00d0034408441d6141001d0403e0342d0b4940020100300e109605008050280c50124041d20180541c0040c007814100d0441c0c0d03819019400041000d81015804c2c001858442e10400c00e00340169201d030703d00c1f00440e08009004041e0181c3e801101ca03600e000b00306000e0100d038011304550071a16003891507400041145103081d60903a1030341c01154441c5c00c11070340300c450504560441e4102c6000c0b41c02001040030705000790205008444209500d5000540010120304081d41c1640c2c1c00b100c02c5068100380c0c410303029103c500428106103900381e030080c600e0300c0c0c44260b0b02c05040800351004031030705030400b440c0d560700035901c02d4000d051698410015060004150080741210701400707005061f50341c22034440700010020400c03482501c1e2140a95400c800456413601341040c500c5815a5a8400039511302e0b405030313024040900c08404110a2110f501c0c1c08d2030002603c03911540c4103d014000703d0030014000284a0045844980501d01c100705003902c2404c500100d0301c10f214103070340142c0c4421107070600c0c80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 898341438 1250 898340188 898340239
    0x3050c0d151812050c1606020309090c2104055209290f010810120b06010e040e07050f0d06060605031605090f010539011a06040302 58
    0x140700211218040ca1041d81200c045e00000e8402021204800700b80070882a0b0320409100780c00150300704200c1d403d41414220b03215076012a80820f003510704215040c03110080301b0f00170b90140300c0720f1812050004104003480000c42515500401d40d5000c40203511042c58030341c8a100211000e058546520148034072950042504083c0460062450707685d1402c84000d0022034408424949020703031504400c1903c4241c2c0e03148418003816011003409408015500040d000c1c00b640e040340c22039180060000108080d140400c1e11402d00b200e5942006e0001511201500d680f241c0f0a038101140035104100000300391045440849680103104d40c02c2c40818101401003101a05480c14800045400c42d082801580035003880440881c7e980e90400381110380d80605600c51b03a00503210901d6005949c0302d00041c0c460f400851007464048481c0b5055080c0480c11100301104052100208104801083c480c0200034603100701e04501c039884540c001040c0e0310960000904c0364107520380c0c00c00080907248044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 898342688 1250 898341438 898341443
    0x2502030105090105011703040e010e130c120c090519111611010905030a03080a0b15070318050a03020d140309090705030406050c040e060d03020c0312030103050c0d1518 74
    0x20001070501c070b000b40c0e020340024010a03c2c0d00c00343d0100307841c286000000300c1301214500703040c000d40c0743d0800c0050b41f0768000150450b02d035480201c00050100380e10001e207000410b5400902982d610b2700b4544100d802e6115404140c0052404042184001140b0449a5625508000001c01004100904032103000d00300205030441100c1d0031040800c9040e2042000e05407007621044030441e070342c800700340d80ca0681c0d480c010b000800c10000b0601d441c0e140d80041c5c00c1070200425443d080c8521000d0140c0542104000f54006003601800c0c880250b10044244060102039410601242c2141c0100368110100c550091074400da07039141c26100c40342070041c0d5440b0b4400503c0d154207804c24080c0104250000e860541c7d00a10b0480404d6076018000c00f00c8040704c1c110282100c07c0d03030381c0004020800c024240141e0540c028907080031043e0741c05102080564140b00c2440e500c950660078104c0c90a600c076103809010b0040307981d400c00407138040c400042d15005000000300da4000554004011a059441c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 898343938 1250 898342688 898342691
    0x102040906080f12030c180f0d030e12010b01020a0b15090709090b0a03020a0b1b06130c08060c1608130b030a2f130b0a020115060503070525020301 65
    0x8106844041050314600f000001120f03641110100ca85003d0712042d07400d108008001c104007400d81d241e1781078000b64104000c1042e4034045101c03005c140843e000d01011000910320142000440c945400121440703d942c0008001001002c000030790380d41d100d098090a101a07005c000741c410881061011a545009031944c80e140c04c181c2c6020b481c2d02414080d00c1030b040c0c00d04a85400e581031100100d01202e40081040000d540380c075580c040964081810707440c5d44000300300c04006503441088568040c3d203d4134000e01a01c080c41c1000a044007081c2c21980d00c030b0300407405101307200760710800b80c0302125061241c5440d481440d107008406841580402c00c628580e0000002c2c1181c8440f02031441510744071004c0c0224526103405817070842c04010a0210501c8038050304405d51820000b8002c2c44945403c80310308651100c0d42c00c005508505020300041c2e4503080381e1200f040050081e10020076107030400c103096080654020b0034a0040c16003580510703649030a6500c0788604a10031a41d42d6030007400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 898345188 1250 898343938 898343951
    0x2a0c0305060603250302010507020607051e0f06100b0903100c080f06030d020a06020c100617010e030406050d020d060e330d110d0b0a06150f05070b04030201020409 72
    0x280940c07110310407540b96209002c1d610440811062000c2e29070f40e1440c1c0b45904000c864155401035038160014171060f42c029209114090004104024039075000d954580342d0610051807a996030f1401400303c8030004244c2222080c0092036500510801c20b85001c1c2c41e481d0f0320340b10440042854922030200a65a0ba414004110005074224003524041e80b1280d940005607510315007403540d2400c1c400b400c200103130301003071200d0041005640617140010b2000150f440c031030384000c01501505e40742c5d0020081741780803034017400e6846024840d0075413080220340030310300b49840d005000d48a40034140e41e25540a80010340c443c60214543d004201510002d01e41070041c0c10714409808103012500d8281d01d4021400090050a004250310b0703005140c002468070308410340741c1ea1000e90510766264042d400040102e4000c002403c034003103446c0320711580000000c0305842c1840e4043c0c0003042c0000d50060000392459419902ea001d0103d400c0590010800d03c003a481d1450300300e0080c403443c2e0102c52a40c1c134040c1c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 898346438 1250 898345188 898345193
    0x9040c03141612050a210e01030209130b06040911120a0b030a0807061b02030d06240e0612042f01050904020a020f19151107021002070503100e0d0e012a0c03 69
    0x22403040b001000755940c007841f2070070b01f070055040b4414202c500b41d0010941c0d28007003050311141c0150b0b4040001411150030150350300c1c5079505907070314140900b916590102e0300c459550b0110f240c1315032081d2104014041044858080b98450f1200c242c081c192600c000f407010184003a580019002030061011003960b0200c41300c00039220381012411440c840d044c0710001654501418486443d03011740e510742440300c039140905844603208800d0b255000f86003403240c04500004085090300c40d601500c1d6250559288007072149100241d51460700e481c010340c88421480e80d038020140c0707840f09015100143d94011811080e032402103811558000c0e03100e015016843e080f5400106a02c0e180b0681d110340302076800301220002d58003100080d9207040014020000940381509502d0302007000c50068400c2c45d51101c000c6030400174104209980c5503281c1d100860620000c120583e60700e59249442143c808110000911603107074429013440448208400446030700118040c601d084e80c1c441c0070050070070b5692 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 898347688 1250 898346438 898346483
    0x150d02100513030c0824160c2001091e0b070312050c1e09030a1101050c010f090c05100806061812060106030c0504030f0b0a02040509040c03141612050a 67
    0x40c005d40c0303114041c81d08800001c1440e481402c4844202d0410307064542d5500700111072141803100e039030081000f503000c5880460480c2d21a00100a0006610020070550800140c030303101302980100420715101244025000c07071500c20006954070315040c0c41c3d6490041c14100c0b0440010074848145500d400140120040150018080045003d24103083c1c0810300044401c80d0041594041c0c064204007440c20024200d0b4042c4405810141095418100052107641c01c4412448040c0f1200760369904c11020300070302103006002050121614440c400e598900201043e00c09804c85010720404200b00c0304034010f440e80041815406413080150307600e0300000640d0307504203102e20700200b4581040540498850402c85056036000792410000c072541d03503208140d0700d1004105400203503080c000410250390f80b25031030b8020740c020104030b0301c42400e50501691450040045816640c03180503040c401c0918040c186080742c071075005400e40c2c42400e00b821403d013601d0341030007480040400c3c1e00c0403048505 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 898348938 1250 898347688 898347713
    0x906091201240f0b03070203121617040f02010806030715020a111804120207051c03030e0d090e040203071a07060507050f0708030603011506020304030506150d0210051303 75
    0xc090308250780c200c00d02181100e141141c040d802c803151031003038140400713280f06001310341082592040702d2a00c003c9400d050a40d02040d50300e007035640c0712114180c800c00d5200180b901007500386440c0c0700321410183e9860240381c203000720003414085200700089040d6024026000100107010989401003000b001c020345421410808550134003411a1641c1c290414a410064a0481f00041c14854549880710011106034211040071880b8210020645440c5c1d0f00d00c00d004a0112a0200c41540c06403802800b1790781110a0040c056100700401400e0300e6109201504a510180344220303652645d001085c24100306d0b411118400d06448443e8006e0341c038080051a840e80508410010358a51850441b2903105a40c00c03070001101c20700400f808201400011074002900500000c0c000e2400004040c030407419600600168201140c10428402d09000c01e44e889004103000070000407000700001e854241c5910003a014581030420848454021000c403a200d080c000320154405a62f4582805c00040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 898350188 1250 898348938 898348961
    0xe060d022b0b0108030c031c0204080106060c0b07030b010504121a04030507020a0914040b07021507110d08010506040603112511030a1208100b030a0212061903080906091201 76
    0x162600001141c84c00442071701c071040070020140d858142c071080d0711151000d81c0c00c060602c0d07650030000052307400d00034800c1e0002450a501c540d98000f00341d050104204900130001c400740741c01c142030010703282c1e80030007200d00b66080c042c030091122445050640c0c02500604100c0808184007003030100741500b0002401d1468801c50700418815100c0d40101c09985d090b00c2599801c03440840800e0001d0360609180350702c02070501c1161040c2518400814002e5001e40e00040800e2200160400100007808010881c100500704a2055403410300803c40d240302c0e80c42803004240d40c4018820ba41c031024011507540c40e180c0341c000f02d421814050082c59a010590701150984030444950742c7c241404580c80e0850f6070000345240000205e0803050300c21010007008410000b001420102d44030381c40300081d50203003c0c0000c005845284801580e4021038000c0c00c01d074070800100c1c42800548070100c403a501900d5020501607255444440800d025000e420115075100002c11403030a60048154407004842d070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 898351438 1250 898350188 898350203
    0x10207120f0315091a0a0e07200303070804020a120803040204020d0617010b030105010e0403050313020f130905061302060724180201020c0a050303091e0901060f080609010e060d022b 80
    0x1e220000c0104100c1c81d40314007035000104c640019050749c040c0c6070306082052007890104d40c19660b03030009070035030344211521400b20b0400350a0000354242050310301c016048100903405100030a49604100b800000c100a02c80c0e0b0300083e0a01d08040c0381e81041000301084108080030320b0f610502140a0046100058001c1d031034040002880c20045007214001c907050780b6014a543c98dc8144400b0350600e07440141d81102f140c042010703860315041440e03800c00511100014044c6032a19042c7d090031005814038641160410700c1c440985e440c078044915140d48500000c003500184440e09070808403004071103e00782d1411041c2c1c280e2900115049a000340f00340c2c00d031016914a01c080012404580c0641a019801848140749600b405529142c0b94a0489140152070b000d4500041101400740c00030320010300c861003500a00e540280d43c4030b4010340c0c01c6480103480d40c1400340c1183c034410024401c078800c0058040f64070540d01c0328605a0107a690410348181d40641008001e6180259410b04a9900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 898352688 1250 898351438 898351481
    0x71203080c1c0e0106150306031e02031c0e0607030906030b090115030207020109210b0f04050604030c0201050c070e1b0c0709111c06140102010207120f031509 70
    0x100c00700c0304559940b6a4030180c020304000c81c80c0d0400080100c1c0e04011401d650742c0202050095076604170703c451880b1a900440c20303904524100c009400d8521a040d41c100742c180c12140140c0d40032030705050b80c5650b001c030306515a10005044501e20b02d0308041ca5001440041e030a01450351155081c010340340c840d2070074001c820b140000d000c4154000d10030700c44d00710184850b41c06a103200350000d09a5600500d4090081602d0b106081d841c0726030304510405110100d0344d010100f1101c4402c040d804010b4028440749403a141c0c40d00d03512444001d01c002c040009280302c8a04682c003442c25202c2004010b801c490a040d1250b566298000003034450105600d413110721600e5038070142e4200c030001d040700000b51041c01d02d001d02d64805491003141d81d01c101c410a000e98000551100300448a511440001107a09840c210702020410010705000d811a4010407440380407690091402c0050051403030941444240c1110850040c02c1c219000b209003122048000390b014503d400c030b01c41d07140d080303030200030034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 898353938 1250 898352688 898352701
    0x21309060305031215030607270f0303030501050607030507150e0303070314010b040f150e060c060a0c0801050d021002010b040213030b0a0606090b090103180b0a0501090e100e030c07120308 83
    0x185c442062419031640c41180080d61f054480d4504a41608040359a01ca544e251240c3c12151010180c21204070b1000c191010800c1c5a418010700380141401c0c4c440624013820794070b000b0120703c180303030b005010465410740103003000000340d20000d40c4144000640307880b0300b41410010090001440a40b0000461400100700701980c4000c850032a103001800d580d441346007030701080c144c00c03d0392102014040c0340d440c0c0002c0c0d621490300074503822031940c1c050240351034241c5c480401c071a1880341d070b04204400040107000507250b2010460740660111440b02520602c814201d006d041e00c010a03135001400460001e85803d052402c0000b640e11451240f48266900c1118104544030b43c85080f002902440301000f0b51140704c001401502c50600d004104210b07800b030a01408110b117142100c0078580c450030400440b1341071041d980506180700c014095441300082c0c2c0e5070f81710181d044d01141e0b15603402c0c8846c008401001140c59031000c413000d60b00325031b503119000c0424408040040e00030030704c5100010354 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 898355188 1250 898353938 898353961
    0x90112021f0e0f030c060901260f0711061003030c020d02060c070e010905101e0504090c05011b0b07050d09050a0302010e1c0903120c06050903090a080304080d030213090603050312 79
    0xd24026200b141442e102c8401103d40701992070341c002c1103d09c03049142d0303100030302040814800c904104031078040c0d080c07040d40100340050040320042c142d009003090203060100a00c121040329010300c0e095850350340034000244c83d0342e50711400a621090001c2d0181c00c155001c914072007182c4207030b1803a02c0079030790b100030300d9058400458125881050420040c0196401900140d0000d489281168107040d1503030042811a0081039040c0da00c5103600c042048150b80c0060040c04081d0602418415105107980310058410085c0030042401004610000389040c0342e880450196004001c80300c0b40d581905003c1e00a0041c1b0717005241600074420500070503400c500e5134032008070a564a20004520b1611035000401c04400305104205591b510100402c40c203000300c600503a4200003451b9103030245130800030600365540c0b008001350800c0c0010441c51001080728000c152141c140560794201c581c1c0c4c0620703a0b07001c940010a9461030000084140031000002d021400c00055500e080341d00d82030102074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 898356438 1250 898355188 898355203
    0xf030708041203020a1515051f1d03011a01180e010920031501020c030120030a0b12070906090614010c14010632090112021f0e0f03 58
    0xc0ca0103104001c108215010303040c40801c042e000384103944294196541d001418852041c03540903e948501f4500d41021a9400c10300081c4403c98092203030074401c00c202e02c080c403084242c1d40d050024510f44a4403800d070f120700014005400400030403410180107044242507041075141400603021840d07011444603248544016180c0c1c60084610300c0c2e04c1e10310880c014200e0171480700c08021001c4154410a000c00e006140284080200c1d08401003421000901d0403010080f1030344a40e04102c4400c9441640940074401e1940380c0424560b69500e00f55200080d080000e026500401d044056601e1030030042034003400d0755581c031002c0c082155200d00d000c068820350700440d50208600d9141c40080d40c069140070440e00d214020a0440b50800d00006085500079801035419140420713480e207040e03141c0a100c040d03c2c40a00003070403114840e03401191080005001d505012503085d50200b040d56901c241d485459590514152488402144002c018041c61b2200300c1c060f22080100c5500c9140210380c0c1c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 898357688 1250 898356438 898356443
    0x30f0b010504081e070b071101020d020c062505060c040608010f032004090c0b07140703051507031b030f0b010206060622030203071202130c1e1116080f0307 69
    0x500d0b003944040d90070030380024103501c00a400d101c0c0f10000079006c41042c02034104680281040d030007044149001a007880800e007a030100315004071110a42d15903896050340c05da182c4401c440350707c41c45002d0a000d46801c25450140c8184145c4040000c10b4030745000820540e04140e8038211180d1340d0b080d0b0031174440307607038000203000c440c40c424544c800012800381c522001340b0080000c100382d0340c0340e00c400b0201c40c02600600340700280010050b041c854484400b43c500f41300c40f00242504e0f4515203c43e52100e018406a90003c45031101091030184660401070000c40400e90803d540382c040c1c58060b0060408580c03100100d42840501002036001055075031107000068200d5146c4400481000000c0c40750f0a80c0e010f185003070032008005a00c3c10418280a45246190000c01500500410004c8242c000c400e002490500034410f480c15402100074614070240050080c49601200054546442c0071030407440a100b800d648901c80003030071040d0000c55984101b6614400281c1c81c03007640f24440c2d42c901 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 898358938 1250 898357688 898357693
    0x1c0b01030b06060d0e060a0c0c050c0420180913120e0102030d0630030e04051801090c0e0106090501090b0d1104060302120a0e100f150303030f0b01050408 68
    0x400200e907000000a0b441200204824034020740c5804840846005414400007a442070342044000302c154421044031840c0782c03d0011100100c0ea6859686584004240d800b03151205038010304001030b2403a0011208195050580310520304000440381410320407100c0c8150a40004285032107040c49000918a4000c8001d0f5107814250000340d80122048490504521080000a000c0380980c45140003070542d230750410500c4503600d040d41310301c15450780c0e10b0b6a808944a103400000b030b420540d002d041010944e0046100c0d42c0304400c1209140103011015415400d0003514400c2102c40d103091025110300504400440c3d88400c802c50740e20903540102e42c00b16100c0780b400d000b900e00d41d2011b0034003000d0203040403e0300d24119000345401d0b003103a80300b02c02203900490742d5100212003182555011700341c0c000400c01c2d40030310101c580e500c0c4001092142103582e40c007510741703c1c0340e443d421400c198010942d075034048654038034005004020403103615500c02e14280b40d403100c0350f10139021a81240c070712070300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 898360188 1250 898358938 898358941
    0x20c01110307141c02070f090c0903110a1a070308090c220e03040e0907080303070c021e030106060f0806030115150e03011815110f09010207051203091c0b 68
    0x110f229031982080c40b005035500c541020b40c02c014040c011401c3c038184080c2d0150030400c0c9010a00c100c640702e543c015180182c109000001031503404003000d4201d94220554802001c0300401280ba1890160010010a0000f40c40c0b03080120740140100324081c460354429445075100514291581c5e1b146021917400221040e04400d44034843c04240740216801c032000444902103d181c41c03956100303a000590020038041007100c241010320240c40200f021102852a41c0780c040e10043c442c000f80f0340c000f4482d0118400201e40b0803500b0402d84100b9102034001c0010a40b50030028000d00144101e080004601c1d41c0000e400b0308040c0101040307040d0301080c84503001d00b40754805003121044000d0a0401014188002c0c440da024010602010000a8080380050b1103051081c2000e00d014091600e4038107203030650458800320821180b01c48581c000031616880148c0040703007050b00541c0300b10b92141013480b1365481c814020000f0f0030740c0041200d8000094481154041c44c80304050030140407221041d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 898361438 1250 898360188 898360193
    0xe1506150901030b090a0c1106090303070302181e04060f03050a03080903070f0b0402210703121718010507020f030720091311060c0c040b03010605060712020c01110307 74
    0x41c00e1004070505000c12a1241e1a020610444007124441952601da03030640c201d45800483d030350308500a4402502040c640007030615564030025118800301580003035603000030410320125501a8900600816003040303040c0b90183c480110079070591089203049400100000089412402c036a4410050540e2550f15102907a444100603d0012140410800200003640a00c0e040850900c100d040d00c80c1e038101030040c0908050640c1944400014814075542040800500e450440742d01c05800c1c9401c1e5901c0364100c4911116050104074601c3c55400c2c01440847c4c1a010400b00c104180200440e90758403400b00d0f69503000c00c180c28842d40041013171202090395481103030040a04050001a81c0d0101b8010512140301150110080101c0300040c1040040b08036088140e03402c1243d509003402c500c1600907444d41540c258482c071981d0365a4880c2807903202904014010180104801d484c3c80c2d00c1e0074102d520201503000480107000c4c019800c1943e40c00303030603030003501c03190140110f060007900c2c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 898362688 1250 898361438 898361479
    0x703080103110a080a05010903030c09080613020406090f0e120f03070e03160e0f090609030d050a0e01090c0816030f060c030f0509160f05032802030a060e1506 70
    0x40c0b81a6411408207000810307020010007100fa4800e00c03c0340000f985280e0783c2801811544440b016004000701071001b004403c01c0094113940000b40040b4140c4014000c0c4005001481d80398004610300f4249400c2c01c54071050350b80800001d0021109403105490f04030301c9080c407445081c4034440014004c2c80840c0e070f48c500c0744580d108807400c09401c40d01d148040000c030000d85045540070038125500e0300e0411100c142d2082c9100d400080300002030410341021407185880c1d01030904824101643c03840040c080e10190380112a03840c00080003040b00200c0341c1080700880c5c0c07050040c0f02c61889200085101404014004400c45c0c2d0403c00c4e036400c1d9006699200c0180c0b420040c000300b055121320001d05800d0380d034855503002e650000024200706418000004c1c030b00415501c404512220300508000d075807400321769840b4544541000ca55022a600312490036940358a0020350144607403030b141c00802c8180c4d8032a0049603500c80440b00c2d041014000317400e21110031501213411007062101d100410341c0c1d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 898363938 1250 898362688 898362713
    0x40b0318030c0a0807060b03060609130206091009080d170612030903060a1b090338090321040c06031a040f05070806060712230a020609070b0703080103 67
    0x100607207103400070845165251081c1d44105452081000951070200400c51040068011060b0301030300c1140340100c0010090a0010301d00140300c464644000c045540303d204030f070102e00c40108030040212007281c00504280107401140d49a10074500b8002c80c8900410050482e0240c02c40c100ca52a0788510074007001c4080b44079511840e21060103000b00316a0709200700c40c400e510310312000403000010b1402e540307644600c41c0e01d00f091140c0e040d82480810399034012840d000d0055a000020011610340030402540c96842c10703c0658045014070100c204048000c02d80d13021448240c0d410b95404042c1c010392030409942c001c000303d2164004100c014081d0304000e581d840312141982c600c01b80d520224054942c480ca2215086648c0e10801c0f8443d6003040e0b040d5080034064130380e01d081101d160780d04000507680a9042c0140b1060540b00c0c21541001940300101ea0741d0200201d032200494000070350f99003416a42881140100080412410181c2e8141c400503030f0140e54204059185480c1c40000106 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 898365188 1250 898363938 898363981
    0x6070c0f0f0c03080c0c040b0d0b0f040c05060304150f0b010f0f050d09050c18190b030106030f20030c030a0303020f041a030103170412120c0209070f02070b040b03 72
    0x580d0b400000c0841c02403c080c0031801e1550000d01078822141c0100000c45114180c203600c940c403009800b1010414442d07603242e0048080c050644251168101402000c146a0217558085c2c400804c1104001c407030301c01100502e020000903c410880c018010080c0e507104e195041c00030f0300caa0b0002180512404138400c200f070721424000c0c80d0910000c041800d80d000700806640a51000400681c0e9003000b0381100041d00061031926460b040c17030072180740701a80021008482e65250440703015190b900390301c540029548a011036040b8085031074900c02c0541c00300301d801c0118800f198000c2260402141800049400401074401803c0c10781c0c09070f00a4002c0d00c081c01d1400707018480031400e00624501143c00410a402e01a180e624501e401141c03a00c84003e4000e001c0c10900082100e11a03070308109019690000f50b1920310044400201c0c1c1c0003c0140340a0f41c000a04030902030115005100c51041001580c01c1d03c140c3c580340c21800700644103512500e88039000130800500c00c81e8064100455001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 898366438 1250 898365188 898365203
    0x7030e04150f15090911091002070e0103060e060a060b09060c161d010b0406050d05090a0c14130b030703060908160506150f130b0d050102180306070c0f0f 68
    0x80d1600c40c2d1804240b407507000840c2c000041025a44540d4011194200900300d603442404440411165203110380109808140203100201a0440c958003d110110107030150941e18603403903a49080c0440034051526024510307014100225000322a94020001038680990200c1d10300b4810006100340d65012081c11201b0b4090030525000c800040c030f85010082407075100182e1600020b00b00e501c1d428806900260020508000030070400da000300650301c1c0306040c0703000055569901b00440b401d0003942031009294540c1007078081001c450703038000d4100881c070075a81480c032502c46400388800ca0308680d203110741c0350380035200400001d916500606415441b0304c540a0400262110f20149805081c0c1d04840c075030031a40c10403c0f00c22002640e00d100f42d80440e1413505100000010a1701031450310035400b045030301c5481d070040c1500d0791407108a105a104000715940c00c1801034582e42d001c50041d4a0388640100404507140d0b81c41040d06051701c94010f80b01c2607034008203544181201444034000c41e040e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 898367688 1250 898366438 898366481
    0x30903020f2707080105090405060f0c0f03100603230c0901051605060405010b0612041101050c0a21050918071707020d171506030901090f0f0c090207030e04 69
    0x40d95001d401038000baa4585409010f41848034004e490004141c01c964011000b003010000821030004105401040f400c030100c80c0f545410b4520b420364420032100880e0171500005002106c1090315807941100e4030b50f6410410609040504092420350303030311600d04a000c80d4041019a280c0c20014070132424141850343c50700703141500060001036514400c0d1610b810120821007440028041c410041004482c0246000c81540301080c072294060b03c0985800c400c6001200c06034000c3c02107496011080c0d084900e2004945004460310100034455010788400c11100f00400d402a8142c4c2e600b618010018070754000c60035890907020000403d00002c0181c00d046404a15218a40c42ca0060060f0303030140105800d080c6015100c0750854000c0a2190720f0001001004008440d41c030b003c1c2d4000319061070340d03074507903506c000d02401c0c8100014200c00b005081040400c051200b06080030307441703002000c40859561051404901403240c01801194000c4070f10801c1380b5141d8482075540c0404410303084c60 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 898368938 1250 898367688 898367719
    0x60509040b0a03081b01020406051c0603081b0c030303060303070b0718091a1e04180206030c04080709140f060d1506140d0f08161b030c0e04030903020f 67
    0xb07001c040e070040e101c4000001d030440c0f102c0351040104140c0f0f00c00500951030140fa0a0b00100706100e80c000850100a0340501401c40e5003668010384000c640200040352210348140b20281e05030750101d0040c01c00d01c684a007254103410048144d038401c2000a000e0f41c10101d40c0d80315510310440c0106290704201d203415000042980041900c0003521840fa400141ea120301e510450844005070342080c4642c0d0b0304030055100000d034080c1248080000e0318003090b582d803103200c0e030f0611140300346000398014008400c00c0ba8400c003030806801143c07800c00031114926a10744540c0c00315040501e03200d05a06a500000348185120120300d40c102c1c00240c14004040c0c3e10361504401c0944020701314803496154902000501c0651314a406100300c125a00703402e070380307a66031a08030200820200400008000c9289a01e000100362082080b075044080f40d21300e1000d1114280011500740000c5036001c4a2940115900f0f5070101d06130b00c0b070360307046d00d81340b00c81403d5408204e40c410480f1309103940452280c200509 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 898370188 1250 898368938 898368949
    0x200f0c0607050c01150e04230106120b010803120a1e0905160b07050303041e0f030c02040c052508090901090509070f260f0304090902180408030a02090120030904061707060509040b 79
    0xb4200be00c41d8407020303491403400c84900340040e4840440c0354010b0100d8050812059030080d001301c10701000191300190300205009611074002e0b9128280e16150401c03040c01004200e4905a03c2d402c045220426126240d02500d80191038000d4806d90080c0001400511242d842c43d00c00c009840c2c01d0075030354489944204080401d900c04400003032007110003e003142410302400341410800c3c1003041c1090100000c02040c081e1440c4a20902644a5011010f12240300221741040c1c0300035083d101c0668554120740c02409043e504038005c3d1089041c000b4288400d22124810b86120450103c1c3c03200c010190034001c0407003615682910701461a000b403d0103410030040000f040340e003202051500b128010807000203040c112415062240008200005611400710b07940301810140050f2900201c0d40100c3e049030301d1519100e0312041100e030b81c540f16a00000908151401218244549030711114000e05900303070f0009001c11a070012130240311103170040000e8103c4201c00b810000c0d880350400001013 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 898371438 1250 898370188 898370201
    0x312020a02010902090a1401050330070219180504020a1e0e070f080108010b091f03020303160210021516020f060c040303020f01200f0c0607050c01150e042301 70
    0x1214996481c1ca00ca07987c410b401e00380c2d0040c08218054088228045000c00a4480d90062145e6070b0040300c0c40c07402c0700c40101c402d0f0341150360080d2901440e26140211084100714078040d00102140e10f500381c010a80701c42c00b03000d10541c0d010f0204000c80745003400c08034011501a0003951b8541c500d0304040303604840c4074000c1e80b194480d550760f08038030511054003401005068000140301e90405560840715164104600c0d00010386840060461000c1105d030742c0a017200e0381000354580000111141c000060300c80d03141101e4001c4412259a007040d41d816a035400084102e907007218440070000c0c1340002604e4000020315114011b603078075030405440c22420080101c51465042c6404102402456810031010142444040c0200070700d83c2c510306200d42080039500c219105c40c4000452039040b60b1400f00707550b070350150081200da550800c3c0d8400f8000350040f54028015628142290300b816035000865411108201c0580b00692110340310303a09003d40003107420041080710710b004560203809200b840d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 898372688 1250 898371438 898371451
    0x4020a092a021b01050301050303072315070f0c0f08030601020f0f012a020601260312011e03081b0304120302060415140a090302250e130312020a0201090209 69
    0x40850f65107082c8504200b800e0b480415040000900040c4141d480c000300322a03445410034020020750034814203079034620ba05105c2d204000d000d0054501c0c480c40398000c42a002d0101c40c0c4429011040f03001003121120001e40d4050030650511240401080403840190b070481018030503607602100070310506203080041a04c0200a0f9074130080984c0040509411010246100f1010200c007266420000d41e90001805170355080004085180201030503009014000c060040c1940e03242d150707204a51500d1082449241d4413407070a00d1814240c2c2740d0304c00d0343c00c003aa640b040b991403c015411159503062200000e2002041c8010000803d85035603002076162168401e60040c80d0502d03251400c891084071101c4080030503400e00c12080d9a0545030340219a0200c4804030000c0c250945050480c0781500c0001181c2580040450501d000c52581240f4401d850340350110070700c035450f4140d000f0720440300c0c0e2002030005100c0340c4090160b00c009070014410001507100125105850340c002603c45141030303d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 898373938 1250 898372688 898372693
    0x5010f1d0604090e0312010501080708010e060117040809040f0209060403031b0c260303150d0f0b09010204031a0108210f0301240f0918110c070e0a0504020a092a02 72
    0x44a40d00d2804401d142c090423007880c00004c03d0600e00c07006040b00740c040c084c61240c14118000030707405901c00c4600e04015851695140c003241858244030344c0d2540f15241e03450159041c01008a0300e81c0050084410813100509441d180c186552021103007d8003400c1110110b0440064240101c5c141109900103880c41603107004101521241405400c480701c080c4011f031760801c1c01007000b01c0500030624000d9540c26141580c12126502e040c4900a1846000400307009101c011302919000550103801682d1262540d514100d14028031448040d40034441d034003265001e2501803803168814244244607482254419090031000c00c40ca011542090700301e0131451240c58030140d0300031240650078888141a090501242d0100c00d0010400c0742c49000e00b2a00010481031107203423214960100060308040d9944a44580ca44507103d0707140e030010b229205003510b0420208d28030080700d1003501e024550080500d450745140140d0107000d49207617070482e14a80b0624410102c00700305040000200150340e0702 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 898375188 1250 898373938 898373947
    0x130b01021204030b0709140a05040e0c03010c0201052a04140d080f210f040303020307020f0604081905040e0114010c0210031d0a11090402031c09030c05010f1d0604090e03 75
    0x1004014030f88550200e10300700d1014074082c50340e031950074141c0c0c00d81d02700f41e401155200840b580c031441c001402ca0629055031a05282004c00da41c10740c016070007450030304529030004402015800c8020b081c800d1296141000b08010002c00c2c0804059212840740a0002e181004681e00c40203a150000c400b8446491302c00907002c03560362035a1019030411600955400c045080c44644030f4040c400040005062541c0000410750a600030026a50141c0023401101c620b460503240440f084e4200c80c403070410288141b01120346990091054506070f0791301c002c0c81c1d18140c1c0b9200fa03000509080c092200c1c18840741e00c80400250702c0b0040c4151400c141e6407400704c0c00022540703628001c0000d08091146a03001650841d0001e032034540700c03170030844084400c0001030b1164000241800310342087c004415109500720040180c0040d00d66040b607010701000146150b46900541d91552841450360001d024059058220803180a03241140840501401d080544419481c0200c3d4110440d6142d168400306 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 898376438 1250 898375188 898375201
    0x90708060405030c07120f030f0e12030c010b04051e100314031e040b120a0f020a17060108010f03120e060a020106080708010c0905241206040c020c130b01021204030b 73
    0x11840c00180f821060074503e06109480311002155002001410408189c0900340c01074030444541090640080c0441d407501035149440d61b40740d01a2340a05a0755081280503030981c0307001e1203020300c50b410080102d16550040c9200b071002542c01403030505503c82c480008800f02d42080b525607210195a002180e0341c3c0d80d0454088a610407240503003c0c0411b0410040c014492004295001c032051010540c0320754035401c042e440a80b035028403019100e0300c08180001c1d529400f400c0c89294501d68040c01c8802e460700c0004480040090065001102c00010100001046050110207400c46403405500c1c2140f00d800048a03940074002200050703459141c14070031403a050001c4e40040540e240208800580404040c040080601c541751050300290301e06140c040c5208081010002c032440041d6031400600c041c1400d50720240c1340d09020b6864030800040b1341d400099504c4603030b03500504031b82c0640b01004c620310142618180300f034118040e00280308013900481d00600060f5100d920008010318024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 898377688 1250 898376438 898376443
    0x12712020f09042406050d0602040512060115050702060903060903090111070e0a02090312040b12011211190503060a02120903070f0204020906210a0c0224090708060405030c 76
    0x607160314070815801061100180d241c0700c200010035007505440c040320302c0881101d0000c001690005402074600000d40d03042200e03560040003510f40498407807000706600d40d141030355808240a51001c0103002c22a002c0c225000304040c2000c184020045460680c06c01c02003030501e003081c0d4008000394800b10348003100c0e43e003101c048440c08121000030f211803440c00c16000c801b80806001080050790020f1410040d803024441d10b8141c148101240340e0303580e42c0750f46100d00d40c0d101c0519224040411000031403a1024100101c038541d0f000035030610544c2d0114104a030b56201200d85c44010b61141c600019551800e201d02c0e842190700304001610342d20281c000b040300d201d00815610454104010060002e808000300480581c0c0650300140c1300c83d154408110b2600c100c04091041c2d4001c00075011200582c08130041c0f05d202100012b01140c0c0c04810242e9460f400002c1d40c54090482c00c1d41110380b20b910440c042e0340301ca1404221050203139910034031400c0101c199419640d80c0c00c0000d03804402d8508 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 898378938 1250 898377688 898377709
    0xc020703031202070f0b100e09030d110a0503150f030f01050a0605010908100e0304050d060f14011a370f090b250c0609060806060f03040201271202 65
    0x4600b4150300d0305030702c0c0e560180e24011001d0b008112512150100b0300e5101400201c401811040341c1415a0781007036000140e980d0005800c5540c22800d00b4051214281c841c0b0941d140c080540e211542181c0f1041003001d50207103130700b09258004806880ca503c02c6d550800c0407510303240c1c0074070000606040000c6e031503060b00d441e80c10450501105800070000118009100c0d01106015000014108080c24800f0f08500c1150b0203994000d0000e2000000e0003519403000c20400c0101204020382594092121066282441743d059111140511085148041e17002403003140031305102d2030450a00314102e181100104882c081c01e81c5884508490501d80004101720f002c1030741d00341241524a000690105031040d2020941f000147d80d940111401004e4906505294040903812b50079480700e070024070280082c410701c0c0c0060703200320200e0301d01e0509208956a1003085484280347d43d41c0d44d00152101d5030142d210070001d114600560341c3c0c2d4503104828501074030054440005a0001c2e00402c00ca2118 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 898380188 1250 898378938 898378967
    0x9040b04020901020a291008100b010504050d080d0203011215021c020901110f010509070603060807060503130807081305030c09041e020a14040612120c080d0c02070303 74
    0x10411248001e40c2c1c00181d040c241c20f502c01c1c0741101784100c0c0740f0306c180101c141200d000303009071103001070020303202c03542d00c1110503200c01404071403c408110030700000751403102420601040041100380081d041c1001100841c40c014214180780840722034110040f64800d0303002c4414140c0030360884040060781038051402110000065080c64090f11001886c15802400344800301d48c0015144e040d0390041c66429414a501e07826a40303480ca29490450280c40c0855884c00c180c040c404c40400d02038024887c2d501500d403010000d005031818000243c42075030000c0d11044000181030740034400280c6004c0104802071140c84110307180e41c4049540a0102d03c1d54105510036082482280c60685807400c0361a401900018011607241d03a0140007030b501c0c940540084d402402ca8507002c5000e1080e9464a40751400940b800c010080e81c5081e81d0091640d0400010400d00880e00c03041e40d2070344075050a14035680105c004501d0902103100f0f040854002440342000b5801c480c40400505400000344030740400c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 898381294 1106 898380188 898380191
    0x40506090f04180302160b0702060d0612120f0504060815010e0303070302031806280302040b0c10150807030b1806101401180e0618070509040b04 64
    0x20f8840103601520581c50030310b10b8400c0341d004100444103030241c280e0502519070300300701c440e60201e04110000c0e500d55802281e803521660301d13807078400d1080780e00e1220114114800790580d0901401d14081c48020b0104010315a08650801e40c8004107105c2c04c4608480d241c0107895070000780e0602c23909440f0125020041580000040120700c1401d085070700908000010015984508100241105854050b00c1c0c040c203d2503801c0c50101055090243c1410b0719031384101040c0e0049036413480d03958400249111a40e049100b61040300c1040040c3c14074690505140580d502000d101c002c0140c4802c0e07002940e04454444011000c020744400c1d00c00c24104080240c204a009024210160810070a0000c041d0f00130100c000340591034440041c0c0c00b0b894100040540f5000038400343c0c0021801000c018180741501550b4071400c0c2945030540c84420311030510040395502c0d080140190b = true := by decide +kernel

theorem cover : BRFrame.Cov 898201438 898381294 := by
  have h0 := BRFrame.cov_init 898201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 898201438 ≤ n) (h2 : n < 898381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
