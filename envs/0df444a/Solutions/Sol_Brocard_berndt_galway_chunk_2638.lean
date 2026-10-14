-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2638
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:18:04.354068+00:00
-- url     : https://prove2.me/submissions/63236241-8657-4b61-8f47-923ef603802e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 474280575 ≤ n < 474460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 474281825 1250 474280575 474280577
    0x81b0a0801090f02011b0501181b08060105011b060e0607140702211f020306010314011d0a15120c090b0112150b070320030901021b030f0a050604030807 67
    0x41580030020410700425120f02980a280207020440a8009804002c0100600420340c1d881c0c02648a92540b01007845603605c2e204004035900751000a1407210140d2041c0154105178014000410403580107980d00280c0501c010b12074901303203605460b000708072104e03007440705c0780e641000d010003102a0f07002c2101400746004a0901341044440d0300402c20121001c0e043c0d000350708004448a008080c2007000c803151601c008050400ba42903a610040650415103940b4086424209200303001900c404485050350501c4000031407101144404000110016000c200a01d9941d0480640540a001068050101c00c0703005600010030f440c040741c1c0028a5408aa007107807600000d2000b980c0d00c007104c849605903040002c01c2a003c030405d40e480460301507120000c4082c000903024201500706d801c8a0031421132a21001c8d200c090590717101c0e202d00c01c2e002441d0040c2c0060b600c2030740c2a03100d41c00a400d4918080d040320030516464460501c1d14a024070180c03850b5000174108800c25910102e459801865 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 474283075 1250 474281825 474281831
    0x2a0f020706090909020f090c040e060607020906010305070c0506070504050109080705090415022109010c020f0c04020a09031e0b0a09020a030f1a010b04061209050d0f0207081b0a0801 80
    0x34001d40100307000e06501030184016100c500340e07020356030303030010f1122243d0300107014421500b030024031062180e00501ca4014607103005000240e65103055401e403038a80307130048c00300c241599802c0300440040600620500034030242d20742040100b0000c005080c440c40c03044d191586d84900700f0300090404103c40c5d10400880c1c0c0200028021a1248201d680e04140c1c4108110685141e0f108610042e024582c8200c503403e00715010103401d1610b4005e041d0160100500803c442d001401c022a1110941d2104011640c0650030030300603030030240c3c0106088855407800355000e50312955900d00048201c032080300c62526180c0c2203011302c18007022094004815a404001e030f41030076408034001024500c009460385480740303880824004024080c00c2030b10318408540d20303290b848064082c12070b00300340540d2001840d400c3e5840d1410f0303094480d0207141307500300000b440c0310035002c1003c03038100c07844481c440114007c0420004211208001d0044a24241e0b02402c030818948402e000c822015903000042583c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 474284325 1250 474283075 474283079
    0x9010b0303193c1101050405120c010b04111b0d0906081504050915010501090311090702010605060705010c0216050d031d030f061506190804062a0f0207 67
    0xd01c614440d03000b01c90034108802e01604100f1142c0684680c1d060030818450015403030b1010031800c80c2080d45040e00d54955200c00084918210308a800440e4001d0583d40300030340c100c10f81c03502d00d000f07450583c084c0380000c00c0e0704c141d8001081c00d8448005590341044004160488491207080c014041c2e40c5040f4000d0180b10740c000d0b40103060400920864080c047e81102080342c440c1c0e480d84850200340041c1c0244070900b44581d0650f07440342c82d0555a585180c070880041400d40c13048021104a980000c1c0c00303280a21707131004001091101400000139503681c0e840004582d100e00e400b401c0224014800003480c0c94600c9800b07420b05d80c1455004400c218844030074006c581c0c4065034081e604d601850008034800040b4401c698610ba00788a45601d8072510790b14403d00034000401621031036004480140a80c4040180841406052148035814450030501c0940c00d1003800c0c07240c1e0050190070302044490f40004000040c4a806018415801d4104c0d030083c00c0325044400282c8101491000b4108c2d54 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 474285575 1250 474284325 474284347
    0x92806090f0801090515100906030f050d090501022509051e07030615080411031e070b0a2a081603020d021612021906030b120708030313140f0609010b0303 68
    0x41401034003040320550f80700400c0390034609070807c0c005807818038410851700e5120300b071004c3d440442d990122818401c403842900703250321546583c003c81c1c106030000c02092105a01c20321102000c500500664403240600141890b82c038041c00e0302880004004030803513140070716880c1d0030070801440c010038982401d2041055003040c014060024a043c0b4142c400c545503868581c107901d9101c03e51a50605c6145142c44000050404100c8205101000c0741c84442c2d444030a10054000c6403c40004900401c02e00c0070321410980d025009248844203596924140c0d45d10b10a40f50421462003030000d102c0040c60040607010807001b0b808480c240000c1040007030003040d42d00c1007001c03402541c280c100c4030900d000441d00c2d4211040071408001a04040c0350b91500343c000c000f4000103240328490714429030101080718001c100d074403d49105401035865a0340307010251460302d0f0800c1049820070680300661103852400d02400c820f014882c0003030407450402905881c00d4a55030704109209400820880c0010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 474286825 1250 474285575 474285583
    0x909020c030927070503160903080708031b0d1a0117060f0303070206030a020703021501030b070806010e0301090c06021e030711011806030c080f0408092806090f08010905 75
    0x16040480e4800e030094181076200542240d0119180f114800150501c035003141c003c0b01641c401c0c20b0b1035207900f030304090b400c40844290600f44009449c03000100b0402c008100070354019076100781103201c4c100101038401da0f17001c0d95500c000f90b0040540ea80e2594060012003044a15142190074a890240c0c051200e00240a00401134007d0381b00700c0e1400b4204c5034a84047c02980e0b0301940042c04d068880c45e007082d00c0c1000e0350140f08201e0050003881490005011807104040c180d0350846004206580c0d0680c0a48080c1400340000341440f00a0012901e6540c00b402a4480c40c0d10a400f440381292070054040d2030030306500080e40711555428108006844004107503442d682d00410300803414200100142d030007104845a0021107a18103401151441d055000740f41d03521170951780ca405a0f607802c40b80b5119000c0c01e40e8010035408040050302e000d494500b0442c0140301c507100c10340e050a69864407441840d982036001e0408281040e000b0018440b6000340c017002411000002c1c05491210340d80c0d1612 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 474288075 1250 474286825 474286837
    0x3020118061b030e18010f0501091d15090a020d060e07020c190902160308060d020d031d100216050a0503070302060a2a05160e01060e010c0b07030c0909020c03 70
    0x1803451080003a040c10311843c03600c80080c1300a40700707154400c00002442e0101800740510200c21800c00e400180d40c0d407144124104031010b103885005400902d104a003c0342d20080d1260100b22540c2d6180074036a07482440c401d00801040000594170301c0300c50300103001d0314066403110f8200e094070f00c02c100b209900852076001041c0200c4154030080110030394010f280342c96030801400c041c4045000130b5000040c25124102c14041d031100003113030b560f10040204810352034000940052480101c032000174041c08044101c208483e100302000003c800c0030074100c1600042010060340a04107010a83c508680944040e040035500c200845040a010039550f40b035900c00280524800039402410500c03448411010b541500c0810201400d40a1104450401c000d1b065441340a004007100702071800d40300d02d100f129030291a50920b82c2c6030200c20b85002e074800602605114140c101040001c403481c800b07a2099200d600c00246e011a1603070001c20f01e5161703030171501c03520b481005030301054000003041c0c0e00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 474289325 1250 474288075 474288107
    0x207050907050f120a09170406200a05162108071b03050a0303020706141005040e011d060f0c0a211b03050a0b030313090b06091503010302011806 64
    0xda1007624465002d0306129040b0301c40c5081107000103201c10304171030790092480f1500848001702c03900b0813410001528070482c803a641c0031804e0f03031030502d641c19051140762800c3c0c64141c05445201040e92101400c08a42960003041480e00c0001480b050781154203c200125407110840815440c6580c0c103207281c400c1400c040c0c540c20044401d1180f06105100d5038014680c00760035030358071b62031515001d000b94102c604115445410580030342c01045000201c1031049400f601d1903001280b030302d07040c003000b484032409480084d503c40c41b021000340702410995a500031040000c154502e0400c80c3c00c40c1c5500e010341045100c040400200f21081d0740b2148881c020250758016002043c0c0c0c0c401d10b48000d10080003c144407181c801070b140910340d015400a8071440d42d10000340034140b40d10040540b00c1c07180300240451400441414040203510350301c030038040080030340100c1c03030886100c000940c16045203040201e000000001401196404a1100c0c010709140346011302150030000081c204c0408000c541c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 474290575 1250 474289325 474289327
    0x911031e030d050a060512060f0a09150504060605060f120c03040206071101022109152b0b030109050609010b060702220f0606031d031e18090a0207030f020705090705 73
    0x144c0a1035607a0b115030300926008016200b13a28944100c0e41d00c03a0412642c80c0c00c19441040064604503560190300d40155010742980c9c4142030250244004250240003501e100c2d965070400325150719400000c113911003018906603250004000200344905000f07000e03010f451010700070b00c001a00c130542503490b202e50003c454240424501c0040f49045600c3d01004950b044080c5030040c0002003400170500c4002c15a01500340d5401c0e040000d000b84920441100c2940b140c0420794040348501d600c810181814040110ba80e104040000e4250345d4122015151785c2c11400a00448600c01d1065841d070440c241c030041d00309516600064080b41501d0288200043c03140e451403224401c0f54482100340c54114010000142c40343c1c0020000e1405002c00f1591504100c0c03270050000c400015034518001c00540140203210b42c1e42c0c0f0b0211600845650b0600b9000e4030803421507903075a00e030014450240e0b0140142c030b0300c180e81002001520105101415074006400500440c0c40e420340c0345501c41c960b42801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 474291825 1250 474290575 474290581
    0x20301120215120f0c0c01150311030f031b010e0106030302070501081003080f03070e040e061b0711040207050f150a0b040203070c1e0b1501034a010911031e030d05 72
    0xe22030f106d5103980c0c110551801d403c604807915500c0d611030540713001e420b10207000c20040050580d246401d80f00c0c1a8503a0040c400034085082c40500201030071070309000031411440c2140d0a5003505ca081d0402c4000d40c00c0450103200b50750b40103003246d912401d045810020b1901e191070f0070910707201d1034120300b11f0540000000b8501601402840b102403601070b104019905098840549400c802e46212050174440d25039140922000d505659600c0e804c1158461105100c0e401c1100035441400f007217485000701c1c503100300c1980b0213021070704583e068203007034064610300a6462822241101c50f001c1c0b18a106100b4032503c01c0d0710545200b90180d00a440c05000e0030400301c41340703050001c0c0348010402e440f400204070081d0365012004200c0c00d000c2e201030126541c1070b03000300700307041e4030035681d21181d044c08000d02141c940740c0720300e1241110690803d00c11000440165400e5a80e4048240d9080782400c10740d00709824100a5881c060303150075000c1e10f44111034130340c3c07540740e00c0741c02d4850203125210804 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 474293075 1250 474291825 474291841
    0x80c0a1838070605040c1e03031d06092809150501090308090132070b1503060f130b01090e0d0305011805060301060b1b010e07030210080415020301120215120f 70
    0x15210741c21420741f11203800024040d080a03c1e00080b800140d00d200c01341c0da28011345003000799290b80140361a00f4481a40140700d540c10b41aa5440c86040504c00000c0742404101c0340d0b02c0140a4419010030403130b189c0324201a000c2000c3d03201d2410018000c00800100d8004016540880d01c00d19040305184500c2c0030790351240d00c1107140d907400e8981c1c00f00030350000300d0700303400400c4c402c0c0c401c0d0010311403562400d02652214100812094254214a00041d44c2c203c804104950107400c0c600c03120a40c07240d90702c0f10700140c1c03001d81050345829075400d01007864280422130a08012618502480158100381040071101042c0244880342521034000c11074680c0c0a42060000d045904032070b0740c40f04030040310007244c0d4981c00c54076a1954606624000d0305d5201041890540390007908501d00c900b04041c3c219074880c0c0c0180305170b500c1c01365103501d140c8460140c002103001b00070580d4517510507003143c010802200d180074540d2659800030480308010301207030028240d104c2c050072030554180c0d40f5003130 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 474294325 1250 474293075 474293093
    0x30a03151505030703060308130302090f090303011a0c16050906240c1005130b090a0302070501080712060305030a141c0b15030a060e0109090201080c0a183807060504 73
    0x700410b24036010900e6089280940f6109e01285c1c0200d81d102c0060311146180310744001f00b5a5400026001000144224041c810f900000f1a4183c0c898138580951a0000b030305001b018007a07054011507440c400c004038580b4401ea82c0e000401207803034040461740d070b14060264503101007940d0640c42010424500d051000c2c40030b600340030801e203824803840c40d103041148441210000100c40d080c80c9000412164900094920907466140e001000094203003c019514140020090802c0012040c0c021318680c103540a240021071180c801140c483d4442880585814104505c148070b07850306001b004900444803004801001d201c1c000000c2114804d008907400c0c1b0b1041c031a98402010020600c45580540d521043c11240d100c24000020398840490009854450501900151a21009c00c48444845004204402090401000c008150041c0f0700110300554800e5051002c0d41c000d403800c00401011050302c07046110104200141e00c8641c4203840e00902c0400b0f0011a9250000303001c00c46144 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 474295575 1250 474294325 474294329
    0xe090c040608010c030c020706080c0904021b06090c180609070207030506010f180632130504060f0908071403280201060603050c040e04170c030a0315150503070306 72
    0x303002401650b480d103190320b001e80103201ea00c100007407034030f0305090302c00748085041c600796411995803103210b80341d44041c01c0d060780009042c10307400740c0d003088800e0b07001c03229080d0741580034188000b800007131510101c1d180c14907a1050b421400340000750409101040003240300b944c40002150380038007944680000321316140450304020014800c0d400003207694109429840200d43380b00301080c6040300048040d20903603000e4412021b02c3d2004c01008401d204000c1802111079907001c414481100201e070019a424000d2207044010683d10710500c0b00340061400703042005100341d00180003850180e5180c07085486810406040081d03582882c082081040c01295448540710003019580714800d103404042d40c0d00040140c0c050340c80e181e00041d9440c000d000300f6204054564a4504003071070302168181d009030040c42103410301350b964400456200c00c01d000c0c00c9160b5200f401141c0300c00300c468014081b140702d100c80c031540b40f44441040180780c03288400d2031034615003894181d4480d2030b00c02065000d002c2513 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 474296825 1250 474295575 474295579
    0x1e0e0102090d0c0e0108010c0806040b01211a040207050d0507050304031a1f150e0102011145010509010314010602010f06060c0f2604140406080c03070e090c 69
    0x100d03040b6000e0091400c9000213031180c0700c401888503640c4415942c00c075510030140c180480c0c04071000074035524250b8401c06641d8418103000d40c00c2c90000c09241e080d034141800350701503690349204c1410343c032204042c10609524152002c40c038248883e10742d1682d407084104000708120001444000b003000034000d07034004690100c0c665007080c008001d842e02d441c9040b283c00c4c0c0d12407465030201da184040313100e10700e0032a440b050102c01d101012410480c0c0c4030b120b540704c8078103564075450440c662a00e528002d00a1003182c04030075010301102e04260f000d03079801c409400d00004201d449900b1030a0f0002c02c815a000302400c055665070240300040c1c020386010301c251651810580700010f402034041d0055082038000c40e80400409840703584c2540c1510900fa0054083c1910626510000d00c20b083e00c100c44608000f4100c0062136800f565500662150b00282c2058105400c4081c080c00d040c007407580541080801b500344510542d010a0783c40700144100109a0102d07800700c0c11050341803020b14211140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 474298075 1250 474296825 474296839
    0x5071a1605070e0a09020d03230c0304031211070909140d171b0d050a0e06010f050f010923040f0c0507050c100c030e010203090a03051506041e0e010209 67
    0x880c00d2458a030203240c0f00b1111140d2503880007860000c00340c810340c48259802170101060b07000584046902004140107105444c9110b940244042c3e00e4070043c06990905030300440d40c0e5030541c5403610813410303600d02d141c0c2030040410400c683c401020800d413040da8201d2500181a10090425284000110440d08464064507140c0c1049a0b03000c503840d6003200341d5601c0041e0030b40f1564040c1480100300d0b4200d000c2c41e00c05000c51a021100c90300b02c541c01c403103408000701c2c007100702d1800c6600308136080e40002d203070308900c02040010341026011030004071001d00f4000c004a240c02d14140c00e0ba00e008040791920300b500301c01091903958036400390401e13540300300d82000440d507161005406d5500c07400c0103542c68403800072002001d141c12038050310031a0503580c0d0080a80e04507178068030440c980c480c2031070640c00309000e081029100d02e00d0210086000c2d600805545815a91116800384081e1007580105e06240000150b02c403e138003014840c0b070b0481000504a48100092802405260310072540802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 474299325 1250 474298075 474298117
    0x5060f040303020933040f030f021906020d022401090b12010203130203070515191e1707080421090b0403110111060f06040903020a0203070e090d090305071a 69
    0x70a962480941581748140942880c0d034038001840c0100c2c070404039404030091040c00000c07000180c4017180f900c0a072440d41c0c40050100d020704003011640201e0010381c080d080082c4a140d0401a110840c802c20100c0480c0724400c2d0300740504090140140c00115403a00b610144039110004e413086441141030085449080091410a0101c1341260a9210348100c074008202c0346486000c030083d500003032203040c0c035140c03200c0300103100005100800c0302403107400350701c510b40e48000400c0182500600d58903019092074407012500d00c2d0101038800410171a0000801002802c184150159800390b5001c11901941e0b1701d4044034000141d030450102481c02180000810602203080c08420b24241c0b51a807510158100e0240d9510040750200e101a000c034001c00c6850915620024546020b1b1059500841e815004246002241e6102c13100c103010a004000c1700380c100384102d4480002e0391411250725450754452996504080c080c404815140c400d004010440100031107011202104101034000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 474300575 1250 474299325 474299359
    0x906120a050609010c140301050d0605040c03080f03041208040507060503091e0a0201030e1203190f02030f16050f1c020c0a0c050f010c241104032001050705060f0403030209 76
    0x126142a41101190b40340032031031b550882140581c0e040e00ca026121410420680e29080003030a13016200361840302c405000400841c030038400800e4a4031003114134564070705003881c0015060840071110707000c101940040c400090780104075070f4110760203031420544070b40301c40081500b091420b420300d21450910f8086482031000128405050900036200ac0000f8150012029140d111505030340d50101ca040000441c0164402012074044910840000d02d0031440d680c1002260720645501da41c407104881003066002500f0300608000c5098585036003040d41c842881080c9008513503154604050006c80b007036071744800d981078641407091501194120316403401c0803000c1c5691170050342d0141c0ea01d5600711210394020700300484000e60110001c802d00780e00d1100445841c0608040048081c1c607841b2180300719410401810103140100848031000f03003040d4052154815000c441c0d0306229040c42000085035000c180e06038007508407140800c09607140e281c220700904c100c5002c140e0000001885103064 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 474301825 1250 474300575 474300581
    0x30a12020304090c02061617070c08040510050903012007030c0f02030604081305032116021e0405061903030c030903060204031239060f050703021e090906120a05060901 74
    0x18002c422000c802e6047c1c0c440b8200c400c00148013281500542c1c11010900c01c40c4608a4181c2c000c0c05400c2081c10640c82d040050140c841105155001540c04141c00e40c0c1032500b80b01e140101702150614003101141c08001c1c00b002e004000000d0203008640d100202442283c0034803440040d8000c082d80c0f030b94541440d010750541c0155006440c2c0700498040030600d07040000786240032000e841c410300070031441580c800506500184038080188c840d03840c42c00040e25420b18618210074941c121040142ca40c0040c0412104014001c601c01d0061000400c48240596282c80a072501403600140d51f48842c20151040b1001d40e00003041c00c1d00c0081c001042c4411802d4000044d03660344e5a80c04030520f1030000c4150210340c030071004010045181c0800d4452040e07255141d1007803281c28040389060441260703070200d91b412580380004c01d40002d900400340003024816002064206030f0b0608000e81e40300400da0114000700503501400010031514040385042000320701e416488001c8941d9841d10964190203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 474303075 1250 474301825 474301831
    0x70501090c140312031e09030a0f0306030c032d0807020103060b0703090b030a0e0109080d0c0507050715030209040219020c060403031b0206040e01080703020a05040209030a12020304090c0206 84
    0x80c8140008000c50910107852040a801c0c2c401001050044500d0144403255032001d000500307403074920000384603100d520700701242c400c03c1420091500c0700e48151001c0d00e483c01810052040500c0d00406100049105c03500609580c0c01450840c00b01032100080101140310a01c02400c4402110901d400c201c081c0c070007000c0a41c400c0e41c003800364940d0381e2501c10260140c1c0d58000d0206404580502c03030410341001450380105442d80104858440701821421903100f5141aa00940002004031104001d030041c403010752000c1c81c146d86040368544074213440c1d000c2e90080e1a0580018405880074500c00d40542e1000f85d4010011540c035400c9000c2101913210b5209102c015004a1140318a1480c089080d1030880780c0548800c4900d0a80480011102940c000201c2e4002810b120211750010094601406800001c00030004d81d8210300412aa07030655a001912490040001c048c19807004184510707503036031141c041440c000d0407060a034114021a00202d52080c80d00410302181030740010141c0c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 474304325 1250 474303075 474303083
    0xa06180c11161d1e0714130905010503190803040c030818010305010b030c0435060f090d0e0105130302040c09090b120c060a030908030124090501021009080c0307050109 74
    0x1140c0f5121150035421208210b44440c5410b822000d04020010034803070151703020450349006614000e508143e100c20b500210300f21118140003c0381440403034054131039140500003c400902d0b010388007560080d010307081040d00405400d400710109081107aa004901c000d9a030014030941c0f42c0c41c002d490403000345c0048010500081c24040001428141d080440f80101c144103860351405007000d09801030302d02078503000300061022483c00c2e8250191708559007214800403000e40083c2c108009040c1541c84003410b000c44e180c000f400940801600a6081c5996000078204035403111301900e0350f0f01c151885548083d41003818510481100c80d0b1004140d000c0d0764542c1c00401a03400d00c0c1043c4418242900c0c600e408561000101845a14220001e401500f44502d4045042e0541d40e0741c4a0b95504281c0c0114203080c202c0d01030824031607a402401104103028540510b426151000007551103103101c0760003819a9803180c0210500050700d044507010481301003229640c900915001340201608031040c0c07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 474305575 1250 474304325 474304349
    0xa1413031b06090308070e01080a020a050c01050c031006090501080a0b01021f0e07090203040b0105042a0c02010e010f0206150315010305100e1f0b040209041b080a06180c1116 77
    0xc1032680111140781421f501a51651810b80c0c0d0b821a090096004e4082e05050000c14818110400801d01846210320001100180c0b603051241d4800520692030700309100384100040280480e03640402c4050384041c80c040c01107a07c1816900613400c09074000c0501c00b40344001d2041408a800d40d800100784100d20400300e0394030030f070b40d089008200d0005403001410420320000410941c506600001e0b600700c00810a03140340180926100c10356094000590046a40d40038000250b60300b0040703281150000782000b0405a903141310007900c3d040000c1040c2a042051032440c0101d071420854205c080c800000e4551080d6100d041642c7d4918100300342e10300d40d6042500401c0208000b18600c08016941068402030380c1780b4401140240007440e98058100d5400d010f18039441c3c0d82c80c06100c4001ca040c6803409410003904000a1442a000301301014083c02c110003004504d20b078a825401030440342c10b0005604043c410704942c1c0fa11094034980e080e03c1000c980c0c5005502e940c0d483c0c402c540c803141d000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 474306825 1250 474305575 474305581
    0x110c010c0906090f09150b0c0a02130c0e040e0f0a0809030106090c020601030f0620030403180f0e040f140303090c040510050d060e0d050a080a1413031b06090308 71
    0x1111199100e0203138002801640c0000c00000d8856000070800e1201324001c4a4101c3d1510701c480c4040e000002240b0f40da600440b21201513062800c0c403030b030110040050034400318075a40805041070200411141c0101d544040e07070340b07001405010401c2d00d9075602040c1c4812642c103040076042a0802400c852103035190035000034026460384100d0307104204d65006045182e203961121440c440e54401305881003a01d4044a00300e0103041407410099a0528144603101d04290400406064040c0d080c54116480700a0900500780b66500003011540d8860035040c2c595510f203001411086201c0d0000c0000100d5103281c800503201201641c0724481140031502c080390808100010b40d001696118010341c00c2190602080c14030325006d07220903004403000b02d42500349030092454941c8000d05100041c10104100268503402200700d90001c011700001c2c8818203940b0086151032030007812020721401e40c0411602014050007207140c0c2499100d00e840404240f40c2000000761841e0803084002528600c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 474308075 1250 474306825 474306827
    0x604051605090f061329031506010c0b070302090a2408010e0105121005010608180601060e01030506040e0a0321061a0912060903032d06012709060816140402030604110c010c0906 78
    0x8ea94807a00c0141d44000544a940e11581044600508040300b01a020031030340c400e1b40c6803100d440009040c1426050154080b40d03481ca014105510310401c00c202000700100040031007403640c4c07810b483e811115410a40c903100a0580b0340013081c48040506400d283c000902a90001181d030b00c070307010485190189610b20301d00e0b5911403000f405480702155070002c4031354045d4030030390207594001c001030400900a610070b016145400318481003200002c011000c2c650654480382d0300e0701d180c0421417105100550900c2d003030681307400900b80404091900880c201c3d40c9175652403c0ba14071000740e8010340f003030340c180310380380986035401281e044001030300e0407440c03041090310300b800841080d100b0b080580950b00c88034011141c16581c001c0d812903510848600c03500a0521032305440c0140070503080081c2035032404e4821030400c40c04000d801c804c00341500c4100725604030340884014614023190b00507589c2e6210380010303004115903034010b42e441c0707008201035980040540c01341d03407107540710b072581c00c0030701e41c3c6981c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 474309325 1250 474308075 474308113
    0x190501030c052508091e0a120809100c021008090c09091b040f0c030605030c06030903040608060402130603150e06060f0c010e0604051605090f06132903 67
    0x20005207020580500520b0a5032104640f0905407140c25914500200c1e04000b811615484a01c88003114a0186042c1e0a14040f114480100a0100c10180c0002540c031202030383d000e41c0100724040c03403030800c10070701702c911403908542140e600a00003038000401000040130040101c94588061117415501046482c0c0340501c207218000300300003044d206000d40c03850340760380c0c0003074001d030b5040b0792035542200001d501c6000b004000000c690f000112545014201031a00d441211010701603003081050110b840d00100486040e901c0504024415480740400314000740704040800022204851000c0f43c246d81c140c01030440b980400103014a000d0b12420f05044481c0240c809951000040206040038041d4002621520303000030000110500341006c0a410300304d04aa045a0540060800c41e0070380381100d00600c050f01c000d940d8a9042d141c061400b040c00b22014000500c6a2010341e11520400d803140c021104c0d01203101200740e1411012081c2390a803140300b44940c0d110780202d8100c40e0340b00202070703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 474310575 1250 474309325 474309337
    0x606020610051507141204141906140a1e05030f06192303070f05010206010e0105031218041406030d050304020d2a240201020c120d0b190501030c05 65
    0x8140c0c609411591540e06a81c14000310420310b006d00713003840c10b0550b10340c8040d0009228918806030502800750400a0110b030f0a8030500f41d800c0361500510580d51300c20341d4003281c4024004160790700c401c03100c03090301d403030000070700c01d0801e0702660340702c94941f6034010061401400341d200032a0385520303500300f0000120240c0120744900040b441c4104070013086842c0b00d65000e1125a9080c2a0640e58000300e0708090045c2c00910750f402c00020204104e59041100c40e0040026000c076072050350404002940b101c2a61101d401081c3c40401c90340d02110300074444411400e0014420000c9880b4011408248601110310b80d107c2c2c005c5603034200d0003034082c40450b0300c500d03401406200c4c102242c0d9214070400031448040c9090303100e260154220384039600150070150283e040c0c11901c1c40b1040f0921419494140016030442e4014028069421400210312034400da81081d02912811800601d80007880f5000280e648048040000c0720014642e0384210161002030fa4288000c002601d010b8500348616 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 474311825 1250 474310575 474310609
    0x90506030d021c090801050a0204051206101a04080118021c0f02040e0102070c030302060a0623120309040207030c1502030741030603060f06210709060602061005 71
    0xf6140e507a202c420468403490501c00d41d0514503580758884031079508445040718407000741ca50000b000c0c4410700e42100c6400c4140c00e104001c01d580d162035407802404840174402c1088880c246d081e10060b00c00f04201765805400148002c04c80380d078845400706e00c0c100306500103078001c110071720740382c54068061100064250f8101d125400c200300d09600348002000c08400c40005950300b484404009400c034180440214041e5000f403c01d41480c1008038202d5807a40d10001010b000c1c001031400c2d2007501806d0400789031007103e070100d00b40300d056070241c19813083c030481d1a030040c4005601c404054104200a9204d8004c1001d41c10769580740403040100c3c03001343c409201180061903200301000d1407800d00b400d01b121001a6041c0c11001a040400c00c10f03841c4640e00c0c2c0d0714004010488581800c001c00766020200c4800c00c2114240b90021600c2540300c81c155030441920314580005540e4108072907802440901010041c0e80d0b91030800a496101c19259040070f8040c0c40c0b4000303800d00d00f180e0200000011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 474313075 1250 474311825 474311833
    0x120e10030507053c041703160b150405012c01060903170f030f1509040308061009080a050604150b031209040b040e030408010b150307030c05040e040c090506030d02 72
    0x2c107151400c000d03085881100b80340041d060f0102501c42089103141d901c0305480492612141041d030340003010031198032903010690061241801204080c8c052002290b008503003246561555512035102c0c0c251500e4082e002400d1000005103411909980240081e00b00003208a00340c2d00d510030341e1803040130300c2003000003043c940c001d20100784c4020914091040510229142000030a13046404c0e0300126080c3c00d400d649002080140400c110002241c010121a88401031070aa503005d424460041c041c0e90041e07501d07503a8502c0042c021000c5101030301c10803044a0018006107841640c802c000c0350b00700c45c600410002040b07e0720441c0103c3d031803414003c029088100002c0b00c2204a60007100e0b4140d8056140e98204c0c28036200e52203004401c210351303c051603543d0700305a58903082d640000c3c01503008582070400540d80012034000d983e005013680c0380c0030481c1341c403d0310111003030f000c0c07a001604a02d6004c4148410812100005000c07115150300501c01552660b040584500c0340511b400050b0f04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 474314325 1250 474313075 474313087
    0xf090112020f13061211120714150c030306030c120c06070c0e040f0606150e040c0c0203060c22060203031501091a0705060c09150313120e1003050705 66
    0x2e00426906280403010301200089411115a8010360341c59a01c00034103080040886818440d140c41000c68002d07090310340b4031090403000031159032540180706021070003004c6903103a00b983d6119002e6540803c02c100889031180c095110007a00c961094074410b100303110320a581249424180112440c001c40d0001815090b6a00c2050000c9503011004c111560030000d0800b20b001e1324010740c81e5006c2d6008039401040c81d61280b602d176088030030f941c020740c00700e0317141041400510342c0c0910700080044059030003281100e410501a213600744000c0c2c00a60500400c41005002c440342c0010b4100300c209456100030035100360031040400f609034003401c0016082000000c0a43e0141c0310304828402c0c0600d4141d4040e541c4005040400c1098034240a00c4403000540b00d0902104104858006507a002c110f86808441c800080e12900074562020303507000d01000190761a442e20f18034100c02074214034070070340307802c10a040180101801d100552003060090107401000344688503107482104592501c1340340034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 474315575 1250 474314325 474314329
    0x6010b0409020a020a23010e0105090d110a050604081305060a0e090403230406030608033f040803061f050412151b0206070f0203120414010c0e0f09011202 68
    0x1500220300c0c5002d520407440803c00041a00d00a5441802401c110350b03641007101b42c0c8642520320701e00c60700d105a07042c80140b10503640f012031036111003805424450003484000890760306203410100301900c6401050204020b1141140041520301ca00c0f4030000b100c40c1e1030310100201800740b0b910004c00203031002c00f40c5c000381c1804c3c500313290840c1c02800d01d6a01d000704040c180b02000380b03000060806030008201049029010300409024280c080091424031051410f04240303080d821082c550405094600403494004c4181c09198a0031503003440d040b51b01e024180181030b07900c1a12042e006407415800c0c8212900ba00d26520308200940c5d440c58a040c1c17820411684076101134006688081e0080300c107800c4400d23944903d05c0191030703550260b01403450fa02000390034581c0080201d0103020000500241c540d074040100c8510031401d07880d140c4140c03180e0030064a80d81603034400c03800c60b62a000c07400b840160003610141c9101c0044a25010300c0c00000e085c0b1088078030a1181010712525214084018 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 474316825 1250 474315575 474315577
    0xa21020601031112121c050402100309080d06080304150314060402030717040b0f010608040f061d0f0109050c0d020d060504020409020d060501051011030a0c02010e030102040f0e010806010b040902 86
    0xc80000c0810004c0e0061100c1281426070742e10b01c4d80d0702c5100004800c41c180302e42d280ca0f0b803801c002c130400c00c011600d42500030511803144a030071101059a11880341040290600948204901c80e0500b0000ca5840303000c0c1941d02d52003801002608608601802003c5210340039400f82549011020911030319000e0501000e90005000c10050003030044c54402c00c04540040c00d445136004541454407420884403c0880d07400681141c0b04001c010f00400000c10f00342c14481c0d42282c1e00844c0081c130441520a200055800091202e0060081c10849403c54a05400000d407241c0242c042d5280400424108030002091500094000603400b90304004501c85a004640c4180050300c08510402c0039400038181c041c203207808485440ea038100500180c1804032900b00740801d90300f041d1240502c01c00c1e10759075a0050141c0f0308100044d81c40d1140444e4400c1032266100c29015000355211925060040e82c000c6443c020480295445000040c40c00800180d2a049070880c41c5001d103000d003007800880207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 474318075 1250 474316825 474316853
    0xa11090c160c05091006230c1203011d07021b04150801020a031b0906050f070b0c13090c09090c090503030d020c0613030e06031e0103030f0305090a1218030c080a2102060103 76
    0x1440d00280103052000342c0c09d104c0c3c14510640a00c21981c3c07517062014203201500e468101150310542942003245040d0002080308010050030001281062240005006403580e10b06c0040050880ba03c0080e800e08150044d2100c8072258905100801158056062500700030401700300181580100304007103406200100302080c1100005450070490391650001081d054418400d481000100c0712070b100c214100d1000904a410300621900a010030300a024002d039001d50309106584503013784080d4000c030711441c01001d001d000d5076119011401c82100941102c044504d8a0041c200001c10280030464280c400640c10b4031103407100c41c20a810f000c42d54000070b103402c54008103c089001c1c04402103506500840c800c3d694031f08501e9070318200905980d000b41501c4001c0d8003c0341c400000a41d070102440c00c250f007a24200d880b0f82051003104821a01a81c80601043c000740400300b6098400305452512500525850505480300c4d5052996400c01d064410016009000140009808024080740f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 474319325 1250 474318075 474318137
    0x40206031803040915060f02070b07080318100501260a08030601020f011505011403150405071418030c22050604021b060105120a11090c160c05091006 66
    0x10500b0740b00c0c480041205c015071408004021a03c008101c12540084002c011040304e1015181d0381c1e14008a1840034062203c2c000c00d6181e000c00010020070110083c0346400318801c0071520300940c8148094001c2100380035110300d412080f44010304c0c6100d6001d0709000e44020390024415002c454031100c0c010f400141c0744034118003405034203101c008005d02403005020245211107212615040000d403c000039002349940300361040c02000b00b141240c2581520340e0708103440104890340c6804044460041c04d40c20b0780011a0b0204820f04048032004c00c2c505c240c101070b0f080b204017142c60400c0000060f400c80e10301c02088407c944a14400d02982c0044e600300d20041e0000d41004828a1160b058040601020009034060030040000d4542041800391407200340303000c0c0c18142c0c60b41d141c07680c52040c140302e21070080f61110080340384801001c040315800d00c0300e43c490304003889440c680141500c1c000e205035881a01583d006c18040150301c04a039003254400d80f03551884a01c51803450410010a0074a07030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 474320575 1250 474319325 474319327
    0x140f0111030d020307120504030e190f0306050105130509060711070306021209070f14011b080301080d0e06160201120609020a18140d03110f03070623040206031803 72
    0x3200c158001c101038030701004044005030b10380c544074200a1540070314098110202d4140010701000c40d41149140580f08402c1d191045110140021140401c541341d0003000080340d9803000105202a550010f4140c6e6412600c0c40201c0d58039498800545000b941d0b981d2103a080a804140407600500c010b15200445106850755260341e921400c0c00ca03001080381e203184103c8181000b03440f80041c018480607009066045d40641c0c140541641140b4001103106d051000d054032901c0001442010300d1311041e0f102103004d03601d6840b05240303030321003511703e107828041088620156042d240074404d9a6001e07200c1503141d41002d020b40c0046a4945110702a522043d42e12240070070700f2007080c00100750100464a44071490503a0701c80d04074140741d0f503910103820303020190b00c140c60b10354072003000d1181d032070b01407402981e100c492035001030404040b200d040368144400a0400100078254120410020306952850a030709407500c8400307c0c000c011140254030031400c2000030b041411070140034a01065180c100d0f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 474321825 1250 474320575 474320597
    0xc0519080a0c05120a05070b0f090a12030f0c151116050f07050312030105060f0d14040312050609071202070c0305160b04120305090f0301020315040510140f01 70
    0x241001800c100a0760b021404035001d10290030070005480e1944c01c60b20040070718450703c1e102c0e961600e00710f000300360100308000f8032090918042d8040d034607080c000410083d4050b0b80c031146e0075040c901384241100452140b9504143c0d890181c281c0e0703292980c025100b4100380c4a825140c000900e8501c0c0407010108041c403003200843c190036481c20a15200d075004210f82c40d00d000085140592075480306d44a5403240c1148140c0110701001e03613044500a4510980306c24030060b090055004000c0d204101d04d2407d1590302d541d4240895003409240251100c10750400026400425140c0455401c0e40101440c2e01090040d4402c1d04402d00c45040c1e21001818070406544003c100380340741e4007e440c69400500500d0b9081d201952010041028a80180c90325240031103a803907004004d807002d0107119000c0f4180c4001d0719a503c83c0150000010021942ea10b8604d805090080810042c43c0c0102e14000c0000c44540519010303009842d041e00404040e00d0601d810480110451a4518104810380003070f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 474323075 1250 474321825 474321839
    0x504030306030b040501050109061a0909220501021201050103060b070b06010302040b04030b010810020702180c0409020a031a011d040218061204050d0f0f0503071107090e070e040c0519 81
    0x43c0e00d00840c400d100106065140061400584070a50404005200380d05a400d00c2e00704440c00700d40700c0c1e000580d154070081d40d4204002c2c0c9400c0540092200c8040c1c0c0c2d201c120704101c4198014107030440b141150096030b0362a03000440844050f030060b440240c20401c106800f05406100d025441901407401514050b141c400c00d015980281c2c0c4100d07502a103800052140321402d0211a445000b480c10450030801150000303031095041070016041900c0d81c1c00420041003524044401034004040b096544401540004008205540080718545408151040d440d0f229032850312041d00c20001c1d0000d03c2d020f40041000035803028903d5003240103040c60651498132004003620310b20684440012881c40e160800c1d034140f0070940b030f880040004005070142d0084d00944008030210861802940b00e5803030b40405e90701e1196507000800644201c0c0780c00507103499a07401c1800c201d1843c1054a110320781d1610781000925094030024044840310380e0500c01c5086c50100620748040d51715502c09044d80e1629 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 474324325 1250 474323075 474323093
    0x25080a420b0a03230c0405010c050f0714010809060408181f030506211e01090b011e0e09120906300c1614070f0f06170c0d050403030603 60
    0x40420080390304e8102908000c5440c66005658140e156140c040d00d01d0203640303403c454480d500406052140c0c414882080c020f04000342200d602c546130883d51907a4580015140b01c490028030103000072160700000c0c80b214400700389140160383c08049141050b0303101c0181e1021140e522942d603000180710081c410103291203440c0c0740e150203d6071800111410b2171000d00c21f100500203175012700c04441808a01c448180050800c4851f24005c54019072800001030007400b40c50040c0d00509048007081c00804e8001c0c464a01d21305006180003030100b40d0341c0d1005442c0b11004112100c09264010302a9850a13183c030200901c0160001032026140074100c03001d40700104000f0f40c2060440300030300500321801410310082ca4202c04120720301401c0800f10114506c40e04036040e80240001400f41030164a210300b0440c40d0090b1450040d4540700c203850f42200500366400f44244d800050841c0d9040643c80c0721030351494003802901056500d40a0069001400f03404080e104500b0903540344000401720711144 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 474325575 1250 474324325 474324337
    0x525201e0108191a0108010b13140a05061308010c09031a040203030408120a0f0e0d1104061a090f1c030324030302010b031005130b25080a420b 63
    0x69222404d481e00c90000410f1200160040005010100301805000441c41c004c0000c581200c80f0840e446595203000c10205800b50348a540c00c20004201e034171242d48072845140549030344000030003c1602d413440865401c51540f00c0070704094001e6002c03009001086a080354480c3c0003808981c034066450411514100c0780d50300c00a210350b00890740910003a403081749507600012a00d02440c4440028001812101e40c01e200142005085008600c40b62101d03005100102014080c8214030240700880006030f5000702c82ca1032203000305034401c44481c501905000d2909000310080101c03515a603609400908011284004000800c51040c0d03e41c2c0403ea4404040c502c1fa600100e803400800081c10701d455641800d4036921400d02041080042d94501c0584d4001d0704a150002180c403001d028040b0000b1300c24519055070308000b45410b0458200d4056801004410810000b0b0200922521540600f0200040fa400c1d09060740707c2a18819880c0350481e00280d500a122060b03072005050455400741d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 474326825 1250 474325575 474325601
    0x1b092b02100206090c0a06051b100e0c04060801020c1903121a090a0509120a182909030a060e190b0a0b030703020f010525201e010819 59
    0xb0f0401c204d00c0707107030500808610314401d607496200d842c1003203800b500c2c50007100300041e06020303282000b240c034a004101110380c11501550403c0030200005d030181c3ca84418181150255044c40000215600b05100300c81550508001601e40003106142902030781100003c01c0c1d0402030281c0c0a0410641c86204001010746c1d030500e80d4141811400a01ca4042d40003024090124904810000d0010300482e200703072000801d8003c1581d600034017406580811a942c241440d4507aa03200100302c0d10340314503100e60200510b1200401c020598a00218244600309056401d038010080d0300e0000350003a084511006510000d40700b1442104024900c00c842c00c02060701c1801d070010912062000500c2120450709040d03000d01310303842c215008181e0a1104000c2a410402c0004907803000508482c40ca0903070305601c5598035201d0342c9600380440600748094041070b03e000221a2842c6c1c0b450170f150300e000035454168640101c0e6442400650308a0001400c52101041210000c6084192441554207456007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 474328075 1250 474326825 474326833
    0x120306130c0306140d030806010806010507061103090111040b1206040b030d03150603060803070b0c0c0604060b01020c0117060d05031b06040b0601020712060203130206070b1b092b021002 82
    0x391106502042c1e00c80d081d154010440e17070380c00da80403c0c1d1006c41c081e4010301c00e092080c400e4441c0c4004a4552041020142c130443c60031500385d41d0203111200a5000c1c00d8810b000703000300302490211522030300ca0b0b4841c00d10003000401409180d0390340c107104141c0c420341c020720009100c9400c8001c207080801e01065070000a5551140d802580c0146500c00080e240614080260500740b6110954a20403400090002c24a0030b000075001e009010468108a81407420340320103081c1440e080018005031111240540142c2040010300d510441b000469040110f20044054591409003e180b4034214400d0f540790004000c508800c6801c0d4601c50b100d20140002403005151506003540d0681c00900254115080070004020700ea8107003e00801c072035044440107a80782ca03601094100b0810ac1c24000350040b801180020600046680c0d0074859008080300381040c040041154043d88119214280d2214100741c110b0101c02e49240700000c01d0190001103d4082000d030000350060000407410401030744 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 474329325 1250 474328075 474328079
    0x30f0b0607050c120c030d0302160f080a09141c0314210108030f0304030810031e060507020d0f030902190807060f03110301060f0519030b190305120306130c0306 71
    0x3040e1181c04100c0d6900c1010b070103500d900705c0000780c840d00c9110603441090340100d40c450186e10702603041c0215640c0101c0aa8024181d460300490720b070481d0345c3c0c04001c80d14a03640003480c40010461040c100400500c0307941c2e10015035070416440c11150909604219440c042d050f00f00e0082c44c001c203070300b40c1d00c4a5400e40c0100a20b510300400c003416000140660001e102c60301002e0180d40699800551604028006541d000e94200c50103596910113444803a60101d81e20340000c420000d102c405004103c288015600d1150903690342c1c280c2d906610000e411b00e20411103c900c00c0d13020350b10691006200314034091580c0d01c0e828a8078a82d070402500c1d43c0000004000c420f070480e2032001519103604003407207071007051202c048403400140f10342c1d801d2103111040000c649200e001107810810070b1510f007a00d01140042d00a00a000c01c0790141e00524114503000c001005a0840004503a03011000344400042c02c41e403a2003a42026200c550485900038059034203000b5405010744d0301c502d0703541c0025114 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 474330575 1250 474329325 474329329
    0x709051503040503120c1c0212280609050a060905090616120504060204090b011812020d0f120806032118031c0e1807030c051303030306290a030f0b0607050c 69
    0x728079085d43d190488e04c10000700031009001415154400c01d43d2200400260f50f5403100c1204010301c00c6891092460007101081c0c0309801e034081070044140340c0301040010303290380c0110b045450940b803c681076400340001501c8002003040280390010036262110100d208070140c6801d80d0015902254990707000b181c148450306551082e48035035442440c1c070303900a202c5020440704404031800382200000300118900d0654403071a210000d100c0c0d021014004281031070a150075091120a11500004d03030242c0802c20a1a0000d03001e001450310806900341030440c2a0360068a511201440704004980fa078452102c0c0d8060250300c804820b000080a0040f028170f90003042d80301c3c01c04402e84990a2000721341c084100d20007219a00130024100081c10307082c10781059860b40565180100e07182c402040c00700c101940354000c442154241c0c0c0a880c070004401d0041e840510283e52816020941400b00c0000584203070480ca00d543c06550000441c401c0003004a221035202d0071f02607800d54004802544d00d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 474331825 1250 474330575 474330607
    0x1b070b0921030414011401060c0305090d0f200f040216050d0906020f0d0504030809010315121403180d080c010203040b1906140103150905070905090709051503040503120c 75
    0x1e400101c4c0200862885c11540301d00906045c080d040402c100c0000c0030003018010000c44811350001005040208042c0c50144e142c0d100e046002c403a0032010380c50900105080b5640b81c00040002401805040300801c280f00094204080c1c0e01100c51002c051140414010b00250340e040c5003517926440d03010304121010340b6158040c40701404c00e90040c0719104200b45e2102c182c5003075a40c000781441e920f040080048014045880c0c10100b49220401c0000708502c1c0c0684c54650940701d02403d5145181d40301c0607d80b6801004403076842e1303458000b480100d074030b054480c03400003621416400303080032501c04403582281c1084408441021014043c880da144c6140b54104002c0340b8014140002414890311313080781141009524145903c031201007000c120102c0666010346900c5504000ba8603080800500300d20091044a00035007441d400720b040c0038801c201c0c44082e50000391009442000c503d190110951000307001b982c403804240000500c02c1c0c100010305001e44590400b594a54610f22120100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 474333075 1250 474331825 474331853
    0x501060f08010e071b11040f020405030705010207050f0d170703050a110c0109090b0409050a050a030306050a0312080c12070201051803040305060a0203040602040308040801090b1b070b09210304 85
    0x6904041020015a03517809890050b144010b8400d0b0041041d181c9000340004004c044080c0d401418240e460110302119409001141c50490450310021750381c400590701c1303500a0107031030303001201c02c061510795060848010701002d20a05e4245442002444690390907007104804074000ba20020301c3d4204950302650345e030320501e5682e0280418550940c00a4034a48007486901401a01ca2000080d1036586a0042c8001030b0494281c40300e42880b480d24541b40c608a08045003c40d1500d039001c241810f1000000c01926440440c03081d450003a500140c40b0890b00401c84941ca5904001a81070109010051406000305800125032424940310058403254100c240020702c0e070091104001003080001c1e0f49402c0518950016900e80312803d1041c0030380304c0c540000c0c0c6002000540001c04600c1540540d04c00d030f01440c40c0340b05544501c020445c1c0008000303d6094030103414083c20f008070b4035407902c86030001c00c00801c44440c00040c0201007409118040141300010006c410002070104100704018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 474334325 1250 474333075 474333089
    0x9261506130b090403032d09061b0c0305130302040f020c10110a031505180f0106030b0603040809190b09040f06210c030b010f0602010b1009060c150501060f0801 71
    0x1050118840200c0d851000044c0041c04060b110042e00d0040b800a0600716209042c80388906007040182c00e2100280580300c0301112207601d00708100c81aa00d60901c440243c0c0c10360b540304c10030400140c60843d01500b041c40c07003003603008840c800000142c0e41d500c0b0708000030301c1030280541c03079982040d0b042b81400300d0454040d12003810f1001070f1100340380300c100b164081071040c2000a043c45109982000281043c3c1081342c10a060109030b07a00700c9130540d0404d104a91284d40c40900c0ea0f2104400c5041c0e400c03191249400050130f10100e07000034481c0c4003901101e81d003d07001c8600500503c40407a40348000d580414582000000c4900150409008041030054416030510196142c01592002c01c00b00b0324450041c08800440402003200101c03030300005503003140240143e56150b90680b0042410791103150003546ca804540c003210b05260301c1c080400c030302946414921b01d10302071007900c04205c10a8100c4002400c0542c2000400580c42441d020301240c0d80c51008220345900050180a03060700400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 474335575 1250 474334325 474334331
    0x201080903041203033e0a02070905040606030209090705030a080903030913060f05190e1b030f07091d01050108090f0616090f0b03190e19210926150613 67
    0x410b00102006a00d403038811b0001466644a01b100750880c140a21500000819070902d418001480401d40000d000d1f00d0088403c1e030405d8481e5034075180d64100510407150150891540c0801042c80f00780902081900902620f28168010740000c0c810814060075402e49a658182840742c406c814030085c020742401d994406140031516040e0b6404503040c42151403801e11200007411010300c03919400610492500160f460342403604240d07071b40540458a680c001000c0c0503000502004906802e044841c0c40794940c82d0590034100115154500100700c032030f079441103e01018040508000d01881501c4000400100782c3c10024000c1902d9035551021512120300102804250800300840b90860711411100041a20040c81d5001a00c0001c0311445076028071003405086211050f200c0382d02d41c0c40794444c2083c1c00e5154281e0000082d819415800041400b8810302c068501c1500f08100e04d031601114982d40c0107070350000d9142210710480f841d5425110420321505040c03408621080d481c0703040c418 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 474336825 1250 474335575 474335651
    0x4050f0c06090d02150d060e06040207110d0809060408060105121c0516080c060a050a051506070503070606062613030c0f020a120209060405040c03020108090304120303 74
    0x1d5981c010084110f00c40c9111020103c115511070301d1003800000020411500c400b42c140c0840010101c0e480384c6c081444036000000c4551520380b080303a01144e4800500c0307002c420414107028000344441c030200d803820410071406007030743e554801070300c010079030300d002805e00d981048140800100c0300895498150b1010710442403401417503100408601140c80c00e80d845485414441c80c04407400003000d080c01400043d41070350708101044c41031192400e26403d00454546d4000c420440f13000f20340340440c0c0080d950031840706240100040c02198040c01c00c03a804e282294855030100c606581c08900400d8440c0c1c1900c081d039803000248101040071141c45103c600d0800c00c8205500c0d003200c0000c0800c0311480d902001c20081002030034204d5000341c11281401c0d120107483c43c0d0f040182070240c0c0b00b40100c80005041f45424000c182c80f07030b640400c6032072030380746507a0041d43d28420240850030980030511005c1345965200d011040440e0180c0d5010524018111050007005410300d40c0710b92403003401c41a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 474338075 1250 474336825 474336829
    0x1305060304020907050c030403061a030105180606040f0e03130f0e07050a050f0d060e07110604050a1103030408160f06050c0c120a0b010308073e0d050d0804050f0c 72
    0x3603030303610980174201a9500d4071180f2140382584202e0304014000e03850903d590710140c00c155002c018404058008102548941050003c04e80c60124070350200e50102c0001035050030180c00080420308001008a6408080d020040c10368000c05426484117468520411801550200c450001c0500060380c0d40c4c9410880360040540c411018404240705000030308840c0302c20000c0450f600c070004188104201c54403211078514190b000d8401900103074046007655958100490030741d026a502800410801c06c47d55140125040781c0e05503282d140c00148000101c0040c284440c42402e2001c01c05001220f0a10300100e12001c85500880304004051100807800318002030034014412003110640e1031000b0880c506490030001000c010300007030b04100000308010008010340280d9125034030f0000701006095409098003520203000d20900c07903880b2142211454402c0340c8044010142c0074401100c5c098035050b10b448680741500c0f00282001c0d04100900030284020203140c00380300c010b40714909243e40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 474339325 1250 474338075 474338089
    0x17120708032202060d050901110c06010312050747040f02030715080108010b0103050c040306050402030114040506070207090e0c0618040c110d0201050421030603020411130506030402 80
    0xc1d800c9150a018407a240712a02ca52040300078a030700500e03240d5990090950305002c0c1c0710584002520350f00781030b002405182c00c6800c0e6903680800c0c100802c901d03803035500c41c42c0241c40740403400c0c0140030382006114041548504403a00c0031040552404240d2030003880da5601100010f8405000f06903620812800b56000f48016082900a0300300249005240000790a00d64281d200c5d030700101d80340d41f00091280d0042411812100804001c000010041c2c00540075994115852400180204010b200040e1150310441d00302d40040e000141c0c85441a5106004d1207003502c06580c240e100301c00300303e1070701e5040113580081c0c018031100307200c02145070030300301d40d10728104030074030320500e40032030412404507803404c0c1d54101c0700c0300a1080c00040030106014154100c45061080540160402421b03814014042e440c012580640b80c40224051000d81c03c80307111000c14610704168480304004003581d0343d805101300c661104c0f40110b59030428a540740400980300d40c03101b406060280104000340c1d503984 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 474340575 1250 474339325 474339331
    0xb09100305150604060903020f061207081e0a0506040515100302070515010f03020307330c0c0e0a0b041802060c1c0203040e0c03090a08130509011712070803 69
    0x4140030500b80ca41e228000700103035840300d03000e8000c0000314002942c0b1b0340c00011301049a0003603903800c50600d0303c0c0051045621400d400d2425580d50800071407200c911400a0981c44513401c1d40345426480040c4084030407107803da508418540c0c07904240166841c02d03100340ca402013615506490300702e0604000c10490b10b40761003850141a404a04002400f20510000403804042100e081456841d800d103040b80303410710301040e4001e04c11000003007100c21070940002d2103809200c507803158124840c00040000344e200340c4503104001d10075103510006401414400040c00b1001d003000101d00e007188100c402c64180c0304465200358100f504030790b20543c4070190050780b203406075041640c070800711000c90702e043d40c000288a20003501c26107641030203071b0120107441611041c0401044688400000103d5400309a4442500d40c10620500d0300181c828401018000c14420307a11694036503c80029075459401d9111400d1841d83c1c0c40b602180c0541403103843c5000c0031801c52541042c0c282c5e2240340301400f001f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 474341825 1250 474340575 474340577
    0x305130b0c1309050115030b0102060702070e2d01060f0c15020705010e0304030609111005090d1401060816061403130203070b0c0a031808100b0604050a08030a090b0910 74
    0x1551800c02c0c00c0c2d91070450103003120310030034401942d4031000c10030300c0c3d05000c00c83c500181c50050618040c1d840402d080d0b01a0b0380d55401451014204004e01c010340c6030160a010528a0a0a07142038610710540340d40c04d11138240094040d151f150140141660b2250390754441000a2002c0e51740010726615010b01b0b1004e03002c500182c8940403407500350300400310918500c440c0d00c80030400104004c445d0304000899031040c0d5040200304c00303120070700c13660265409076500815014440c0301c0722030503c0c0502c00721a50003400b141d40d141c40040005400c481968028060682001454034800c1c0e450300c030745000038441c070b16026079240d045030400945400003409101011504c03540590940d901003000c00040d12036031181d140d640e5090100c43e039840ca2a10b4048020a0094071400e0304000d00c40b265004407881c1070054141f800e2500100802019035000311a0700c081c050201141e181c0b10513680c00040c080741030042da43c82d283c1c1c00e070107440184c0507403100f400417004000f007107681e881d107111000610400d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 474343075 1250 474341825 474341827
    0x80a0b07022427071707061209020f10090303140f1e1e120a05010602120c01060305030d023402040f0209090411040c052701020a0614070305130b0c 65
    0x203103c9040d8420404820b660b11462015006410501004901c1e0000c88050b1240c00341c50035040300c0181d0700d41c41548110400308401420002144103c0d400081ca094070043c194110741038010009507034202076440344e40000340050b01c1402015000107500900c2c4200c121407a0500060100001e030741e00c2017420208440910007143c0405d0400102a220703100c08044044040c03010302014001e660f00100da17007000408440c00030900e202d030140700321816074003e50b020381401ca103001e120182550201e040c1e081190b688820000116000b0300c00f41943c0107000001580c1c0f2010020310100c048141002d51950390a4080005c910002c03d2170103040c030590681d4003141054040030b201000340900b030710564000303510030100300402040340040e011046044401b0440710309401d84c00c894a0003103449075010100f8040c0c0340d000000003440f01d80e88100e41481116440705696840e0020b8178080b401e40c0411310381030028010b0507501801031b0b40d072180100511000d200300e981c0301d000c8281340140043c005000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 474344325 1250 474343075 474343081
    0x21002030f0c010b0f01030b030709150e0906070f0215060d1a07030e0f01060617041e0f0b070e031b0111030a09050324040b060f0a080a0b070224 64
    0x2009100751914000e001c040c241d00ca03400d8480d03560107440503c801601c1a00b844080140c550f0017807181c0200c11501a0080c0811800c0c00070750f81c0180f0444180c5440c07071400510003e102659940d0940c4a001800040d000b1410002c2c0302400000280c490507042d0340202d003103022052180e07002103911906c01c8071240340c59940c0b0300304200b05c685a0340c06020b0701c006100801c1401601034211032810203000c000c48004950200009007221198003400c400540000d5000b06051b580201540d0401c0c002c0c00d017100100380c640600311081820490032114100301855403020300c40e20800c1c072903122841d0f0400d0001c107000e080000c1c1d01e602090600c10a5078400c070f20600c280b41d109501c1000759030000b4040369030b51924950302900c80c0d041d51281c54803d2240c11500049004803842203d58000c580380d4102c01912660380e101981c1c40c0003480d80380c00c0358211040c003074255251060b0700010602d404c041d0201c0140c500341400340f04d41c0200100e05551000440b04007284400082252074400c06c444240c0c40d072 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 474345575 1250 474344325 474344327
    0x40e090d14160b07050703020f03040f180b0303070b150d03170405010608070b120a0209060901050f07150203060f041b030b03030c0f150106020d05070f030c060f020a1101050f01030210 81
    0x100d5001d5000d420f01072004100b0007803d80040080080500980031503080c10f22086425690344030324060115101304202081041d0a001c13030701d900309030014080118044248034042455500140e0b42504c003964600d061014031642c20464401c82c00b42901c02101d00401c3e6107021b00080c0c50111100e000d2140302c00042c0c140302c402c0d032241340038062490940e602030b45d5441c4002e401c0c0e007141c0d0700302c0602c0c6000c0000c182a528a41f080303c007045070140406041035500300c0159a19042010f165030303060b4003088002c0c00220301010034944c60440034401a00d80c1002c00074030030003580045816001c0c40c0303402201d088070351441c1c1c02c00880c038506281c0405c82c80110302c00319096000303c118001c1a4070507803070070690f00c4001048071030a54550003001a51030f03a0340d0a040380c0da0704601c0d140c1000b14100308004230128001c205010811806410030303840c40022951180100c030502038401082517030110340d0440b050b6128004000d1030400344024402c03400c040b51000000c02c0180f000078403c0e042440c50350501 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 474346825 1250 474345575 474345607
    0x40807020f0d080a03060603090b040831180c1403060a0306020d0e06070f0f0f05070503070c030b130803151807082d06210307030203040e090d14 64
    0x203260007615691140509191000d442d07013044c130307407800828104a00030500d0740c400e00c1800c1001d80c0011014821351107580b00c580480d80301546084480c08643c016154841d05142c4614544a00c4110001c02d0b81c0361034003d400010107460400c2000741844000708840358820849007100d4070308680701e0b944c1d88807000015803944003a40000c000500100e0504110902075111400100302c0c0e105a036416503039101c1c11074050186c1d80050011034034215407040300621414124140020a0610a1404900e504c409103140c03c080e00460721101d4401c0300740304000d001c280698000f80321508410000e0050380c1c402c24140001003280f00c0070705111050310040e503111080c9043c00340d50080384441c0c5040c1900c0041502001312002030002007000c3c00c000d100605041064954082c16075500d11984489082094030000540d004020f031801580d085482c08050000341011072203a0000d550307035468001007455050300202980c006800444210381c3e0385411810310a102c000f6440000da807807444a07088a0303a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 474348075 1250 474346825 474346849
    0x2120a0b040b150d050a05040512090a050918010b090115050f2a0c032a0a05031c030e01020f1603050409051e060906011e02150a0518010507050304080702 68
    0x405407000a200300400800c3c0003c1554050a0000b8403161380c581c49510143d500c240d800400c035a118600003119544001c02406074504014010280c50356950000f5280050a4071410304401c04000120b00d600c50910070006147d20aa420103043c0d8900801604030200c90748988091020000b1140c1c136054000d400ca4000d640ca042c10781c9140e4141515001c03070300020b114104402c3c442d041035900c151900066070b11101e00705240600c0c48542801e00e0707030502e0b400c100c0d02903041205484041071594092004400c000035450000c410030311602c0c001001d440b0050a00c6900e64410440c80380110705440132104a840611900c4036141c1c3c8602c0e00700e43d14030641d40008100f51420781030044503e9140d581303280500c01510074282d5612481d0421100301e60554906003c0f42c070b0b601c00d0610030303484400385200c5100240161203004070301c044510b402c00000c84441c28090b560350100701200d4080c405c1c0308480d400040081040385891400605144400703003015000e90804200102199030760070a03440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 474349325 1250 474348075 474348079
    0x213090204030606060206070c110d0203010905010c0809011503020a1e03050703080a0e010315060305090307050f070509160e0d080c1006030b0a140408070f17040e010902120a0b040b 80
    0x50780e240c0d20304040c03000340483d001d0580140074034000b20300294803641d11004402d80102e500140d1803811402c00c002000740d160100d03015500c510344000031030400c0c841c844200c8941c1d101d018240c90544401421070300e481d60214400c0826660900242e01c2d0000341c03c05680c01c9c07000103904200c402500b000141140c0d48024814400c5200c04400c00042202624900c80d29844210941c9001001075081d030707540480c10785a00d150301c0001c20100d446600700301e8002d04402c01760f038a454015202d040c1814406254040158012a800c01c114140800c440b1340c0242c2d03061207112543d00c6203000904445d00046202d12404402d2480c0e070901403200111800d40c80403100319204400840c003100081c1c2102d1100303540810400000840000b014040e0f447d1038901207105881030f55035561080d0301500680c0080e07805c001d030715100c10009030994214032514120544403075112803500041a40b1198140c01c49020306005214144485a400c100560040c2c190000410840101b50101300141304400c1099 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 474350575 1250 474349325 474349327
    0xc0a03271a01030f0b07050d090501060f080609150910050a0b0f010311040e1909050601080115030c290d090c0801090809090a020c030307210e060a02130902 69
    0x1545a00844080a442810388a02089a0114100440000340f201400b68400044802d001170002c034040380d0700c5440c0f41403050070003050021b003004442c120032048030706a54941c018055564880346d20300050117032100a201610300450010b403120f0140036408010011040450f003845014001c550300f01500120400c881d07d4600140400744c41100000c81c06034141003181101e0b94072174000c010031119041d014901d007503e4900340c441b40150082642e404e01900d003907034455840d514059484824020783c0100300950400c100d1908440403d201080034501e4080c0070030002c2c3c0069440b0080350b41c9031491a800241030700400170a40c1c6201036820b080c810000b81e4089003c060b41c484850a40108035101d51151100400783c02c03031741d142d1405000c2d40d03c2480b00907528a48101c00c44ea0040140c100981001d080d140501c2c0f554009649076404109c80149003144603129040008c030b0801c914800713103c8078811017510750300c5440103800095542d40000b030340000e107006450000000c181e0741d2021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 474351825 1250 474350575 474350621
    0x61214100e15090a240b042a02060c031f03020d03020601030506010b090d020f0607020d0309080c0402030f150114070302010c030506030303060f130209090408090111030415050d14041a0601050c060c0a03 89
    0x208013040540c569841d8207908c41c0b454400a8400180284a000c000c00b1041ca0364403080e0042115420170403640d0000e03105020080016144d0500c1d200c0707928482d0b0024080f6504610b401d40c1010016040369045500030700002c88281e44820285c1d06558054429162240200b400729030305204181c0b02170b41188100b40c4203c02c00d030744a40b140089a1260040d03a81140b9050300b00010f92000792080c200600c6e150340425034540108005468010050400a80c0ca1400c0b8070061004d0704880740c1580540d5450352030341c0d40184c041c000c0d10750081048025500c0c1d0302e020710024000e094801d51880c09240101703400700c00240340394125420300c80020032004c40f902e85450402d03032541c0403024035400100100040203040304004261005c1c7d03007108900c1203100c203214200b2241500903410380326110380c81e00c0c1d4020400070b110b201c0a002d5030046503c1c081c90404560b5a0b11800742c090846410810100600ea08000021413225049041140c025688444008003140035160581e26211413000480c12 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 474353075 1250 474351825 474351851
    0x1806080c04031406040512071110020304150906140a080f0402121b120601030b13031202030a09110108070e0d1b0803180103061214100e15090a240b04 66
    0xa0980f2486c40746003141c0020720b0001c6400040e00400c40d0013460b5003c0a4045c44181c6011180e44141c41d5030b1f481100d05041d070f00d103c0b0718801c0300d49071444030110b418842c090007042d920036400b45840e400c0744d000030300e064880c52000b0013600005021a01c8034040c107002c40d08541e282c1101e001b618886100310b40141c034800503401c8230400c0c075400644c8100c0c0c001018521801000c20182d0480c2d420400c140c1c6595100c0f00c01400c2041c102c80c0444c204040360902c005400c05900c040d60007924240e43c00500341450b0b1034681c0460f40c2d040041414049400b041100090b03112607080030203101136400c48003904891074403500a40c0d00040300e5140800103140812010400000791828666184a02000c40088401941122401e000c1c00c00b039456003a84510224841152500511003aa004c84e644042141c00300d800705c9100d400d030035409030002990981c400041d00b4055800c05c0e0f407080a00304420b500c2c3e80f15076541441440350b80125403110081c42c60640640d221b00302d01c2d00094070a22600101c520 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 474354325 1250 474353075 474353083
    0x8060d061d030409060905060d110d05010e06070905030c090f010b0f1c021309020304030c02210610091d0307061113030807020a060302160201200a05010204030c05011806080c040314 80
    0x42c6d440141c507000c0082c60a02e009000101103d400c0003402c6850569001441001e503a1000c080e10b00d50b488443c1180710410420403248140019951428850306080c00c0601f0b10308450f00b400d00c10101c2c1814002c10403450f14495045499400300c540d902c40c45c10f030764442c25000d4203e2040c0c1000c80c00e001c0c4620611507800078600c024541d10642030b039a8407040b43c0300490006480142c0004c2c049010351006041c1000000da8030054480c00c000c041d01e208920342d10701582195400401d4a000300b0803c951185c0f1300519100d401c0440ca1441d4181d02500c07090340c0c1b40031f4200c0190a0319100d2500c402c071030103090100d8140182d10a040d21145441e400c0036407840d80409401c0b4090000d001001403114070a00c02c4d05c030002e61800304241c90001507001103c0b0b009010b0107180080308012000c2d804003808108040e85184520000b41c1c0307462650a228544804d00d611241c180468021158440840710100109450315410040b03d03079219049420130a01071a00001c0c81004803031921014000002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 474355575 1250 474354325 474354329
    0xa0807090204090e072d08060907030605090309030a0f0206040305060903030103032a0b060a08030406201c05130b070321110d020f0c0d05180108060d061d03040906 72
    0x1050500081313208000d030540e90503180c40b5510001c83c040ca0010f504004003c401000060065844190705844134409400e0450a50708000c140e846038004004002903405580c1d4441c600b0300203182000c08003000300b6210041c144d4020001d0005c91082011550b5440c103403009503800c0001c0b624545024a00e080c0c0d070b50b10070f0005401241100300c4942c80d9180c0e80f00301d042103003100840e01c080881c4966603c4d040000184c201c60b800280c018020844603400c0003d0001031006540d40d84046403099904005103a4030043c0e0610382d0001801d0074689204400c1c0c20b04143c00b18a4219910b43c13543c654028510810342100085da8030000d44007040c5507000c0c00d064001030440750071041403016550070300210b53f40c00061000191041c841c0c0140c1a4560703020b0b2180ca908965001d140040d00c0304218106580764240e0008268003141c951701840c0c1803412010401020300b4502c1d400d09000780000c1103004506401480c0c0b5449490342c2c103085d10f050900c005040c1031130045a490f2511030f01d885020745418 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 474356825 1250 474355575 474355589
    0x50a0f030308061504170f06070f05180603070e0f0604081c0e030d050d2405130605100302032202090a0b0f120708010b030c2b0c03150b0d03020c09060a0807090204 72
    0x390702e800040410115048c2d018120360b44458110703004600007a182c5400c5007040301e0b01031200d01c910040a885400c0158800c010941d1010542e0b100041004020340481d02d8840c0544010320007070054401c005031809040508101041c29030645000c00c403280e100311804c00b501800b48000fa041581e4000c4060505840040010310000e100e4141c2681d54012144080b001e0400b009401c028600f0480344441e0b529044290124481780c4602c080754a40800780708010001ea030000030000b0304110424810340c45210404529082070041e00021200d10010b0200310111f40e8641c0101226901c11203241c0503690090300100240c40c07542c15564030390a00f442550090f5003442d04400d61480c012841010440e8000c0a019694020072011407004410075200803800b02c50003078070404940c030340100038000c62040c00052843c0d0640300d2072030191174000090303d02805420320644000380e004507a281c10428242c074613802c9550742c440042c413100c1c0745902c18410fa0081c04000b152802d2590001d0082c0d03924 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 474358075 1250 474356825 474356833
    0xa0302091305040f0b0912040b1e070c0302060d020903010e1f0c05031303030b0d080405180c0714030d0f020912030702010801090513060c0f09050a0f03030806150417 73
    0x29048400d440c1c00320fa0080808240c0b42401002441d0110308a4001902c3c03400c43d010a040544032011961181e0490501900082603061130b403c0400190b00080e840b561155043c051659911840b22103d0301000348030b6034011407101518903940d81681d144103030043c000c1c402d100840c1007080d01c8441d982d0060204a0028080b80c003e0300e154001d1b08024070099403032618580da00100402140340c1c1c01021410107403142030514076550303102d9115400d1030040001d196558a02000c021002c4102108010341c801100200041e2602007001d9a0345a604080040c4821881c1b6825504501c54800700046040c0303820211146010243c0c003414041005844104d840250503c10960b280203c41c3c00030700142c41c0200601c00b0400c1c5800c0203030082c8450744504200c3d04a60340d41019102e400c0810030000708003001040f40c1c0395100d8881e400500042e10800d040c0c90500004003404200c0e4000502800008008150292980701d868401e41040302401034503591104176152060350301008a14003889 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 474359325 1250 474358075 474358099
    0x30f02030129040b09010309020630090d090603020702040b0a091d120a11010b0312121005030706050a020a0609050f0616050301030b0603160305010e120c0c01050702150a030209 78
    0x50742c002282d00303444411404504121101004501800200d00101d030000c07420300c140100028905249540c58510701c0c4181d0380304009088548100303000510401403580300280304048190001402800e036509850007680d00d1030030b0300114010b0721542d900650060b102d8a40001c1d1074030b131a4410140380d00003139a041d169178800b0200c01c1e41d90984918403042ca000400142d00a54043c0030041600b40e10b0000129094120f1000682003149400300003041c61070004882481034201c14a00758000010260140b10303c2c105004665100b11900444080c03000008000307441c0d07402000014003e5510140a00c102d03601c1e4076106460fa800a84080040e03c29940800c0150298803a4598640312603a203041c1542e2a43d151003440d80c80c041d0040d82c15004021607245207080503075025005d035000d100045044400c0c6403100c3c0c617221105200b02c02d000d0040c861148007100228524417000024600143c807506903000117001c0c07104c58200103600140000c0e00b4500250150060524140704844c1c0b00c00f010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 474360575 1250 474359325 474359399
    0x1c0e010f0e100e030a080409050601090501021c050d020903030c070504060f230d1a011e1a0a02070f08010e0105011205030306100315061d03120d0507030f020301 71
    0x301c0481d909550200002a851201c5403244220607418180102100c1d649200c940b58000f1304c0e44030340c0114804035110000c010a42d40c00045e804000c040030f01c01030920b0380540c4c0c51880b075615806202c504110000545111084964064901c80035008081c1c039074401e04414495034851141c89218010742c103101340010841c1c0d0450a00040b41d00c5090011003a080094007900d102c1d41f1151059404021500001c0104220081e50326403105070322150070940d4105102c01507003240103500b00c030f580c805d582818400c0c04001d81c2001d0301000b03850300f11504c840d0030784020b0782450b5a0742c0005402c0d140880d000114520f05401c007429036400c0000030020342c1d881c0c2010b8000c01a40c03100150440c0d000700003040c541d007040294240e00700000d240004006078880400054160b82d41e210304009910000700e004090006010508040f0040b002096040020654211140218120300b1481a9a4800142000d009030015034191645440840d03403980c48590301568048200020303690b17100c0003000e5440746 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 474361825 1250 474360575 474360587
    0x18050c0307090b0a090b0a050d060b030912131a030103060c0507230c040510050406091505090903090d082d030109180623070804020915031c0e010f 65
    0x1409040c2d988412190403d0250341840d84420704010405c45005000524080305002030060028540d8480d5034580d2007405060a459154001e0048900c0030028801800800600c03800140303030541a113500c842109d04d07080c11118565100b81c0d8100007000c01c0400240c918001503040e0b030701c120000c0045d0011403030211007a0062610080c00203101b0b680600c0180c01451208040a0300d260844000d038000401050070f41c1c0003560300b011505c2c03140e80c050001d807606000743c3e40079050844040044420070580c2c00110410b42c843c0501801860340401c11102c41070040f00d0f0702074800b03022000340a0440c60424410744c03200342d00040d00901008904448403a1031103403603100621240480c2140d00b440700e400c0c02011594543e06014030403524900005041d07002d10702c0c1002c2c03168445144414070342d502040c5100c0c000c000da02000f001d50108001a81c03941c2c03150703030000900c001e041e0f42c803503001c1c020074030344100103024400810782500a4488c035030344008001d503034000c00c0c1c0e15481100c0c610740040d00c00e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 474363075 1250 474361825 474361831
    0x60212040318080a1a190c024b07090911041410150201230108060106050310150e03100b030c0102011406040c05070209040c1410080a050709080718050c03 68
    0x551a60313402003100368aa0806103400205861100310801d07514a50b031b800b1214500321140144e0041143c07004c00c0b070204843c0411000c48800d01d0802860141001c2603900204038008502d455079100f902c032180b0080211102a260b0b0190400040380103090182d180340c20a503130309100340d0038240070328841c0304564000d601039814807600f0890a802c180304540c2c10745200551a0440d941d42c58a52a80c2880015001d03070260032001054281d410600002d09100d0143c01000034000104144005182180b0780e1a0448400d030403d0154400e11003003c8496500c61405180e00d8480d41003050503040a0b9803041e811000700301e04844500c641040107909a8000304441002c0c1c405040c001500741c03d05800080c80c501007850011310701503031540003503882c0303500740c038180e600c84180f03d410700030340c00c02c0c400000c1c040d002181d600c1d940c1c2140180040c0010f000070000d20f100d07620341000c911068050f440340360161203a0b01c1a201001d8650b100b03031803400e0300100040c0d9058100340100750f2040c40c000c01c480c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 474364325 1250 474363075 474363083
    0x5150105040b060438040b040905130804210c14011706060d09080417060108010b041802010e0409020301020f120a0c0c0b100308030a1a0a060e0d060212040318080a 72
    0x3011103840150141081c030180301c1c17100c181000700050311451103000c00404c05888000800761300c2e50f0800c80c5440854078000c0103169024401003040001c15808025a030403201c032810010150f012a4018540364100030000800203088110003089181018000200099007aa5102e5140c1d281d070f81e4171030581506541c1d20b80c004030304100c141060151500704859407406010050f1038551303a004c5480441c80000b80f52a216040480140403c0c9000c0c010000c2c10708044809002c0310400c1c0c114000040b011440003410b2040982100c4110740721a081010310b0f6400500864a6501c2d40c03440076901e81c00551155503800b080000601c110b45540700f01003c850035076650388803010345655078a4101501400c219540e49220000000150800c030080d403141075000c80c0414109039500101020030404883c00741303e8049231005101c5e2940c00303140040140c00403560b000d002002420440e009108045d01c12120100b04130400040c560040d41c0d4030144900c0c2c41c1c210541307039603070314a85442d40e0858400034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 474365575 1250 474364325 474364349
    0xf050126031c0207020123042108030709030b01060c02130e010906110903010f11090609060d0504050c09070f0828020409052208030105041d0a0f05070b040f1a0705150105040b0604 79
    0x1004100c0c40c903101082c012405c0d21040c48019040e151a000c079002120b00500180c034050dc00e200708000e0b140c5a80c01014542440110266180d000440800300f207070401c1030503035542a020400070002d40140d4220740e0071040400081000801c240e61547c80082c0d124001d6003031481d111600812489150f0000421240c11030411000300104059503000143e1607034044414803420b4108102d5100d06c900492190000701918280c01e418805400c5008000c4418007134429100d08403030b50805085544000c007080364818804118801034944620720100c00340700351020802050200c2c1603448a40980c921011104c0c2400301d0101c204000516141c004001c03400501c0100020b08250b001081e002c1b01100041c0707904e041041301c80345080310001d800d40f02e100714032008400f4000c040c03061001611801400f945031a040c4040008411800d10031064510610040407099008000030b176000540d00c0b4056900144004448109050702070042ca4411407400e4a60100c03460203804440c110b958401c6a1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 474366825 1250 474365575 474365579
    0x604050c0613090b0a1a0d061403030a140f040602060a0f0c1706060403211d010f110102040906180e01060627090e010f0f050126031c020702012304 65
    0x7080607000d40382006030000305d000c0c0b020a10014108201000603064002c0e00c4e2544a0211020143c4000c0d5000e48114403845209900b103880100458504550034144030001444280b11a03015210300081c03ea00d0b403c01003000701e44681d021603844e01a0381101401d0050039a03881920080300c0c42c50701c40401090151003200301035442840d4455000100400c160300301680e0340c48200040600d8a18941072420311900038507529004000001103035074480700451035000b800c0000c0d101440c91160702050200c0014140c40450382501110054000f441080c13040c00d68440340d01c458031300d07180c043d01e5069090240301200d580c03051141c0012a1040d0380c50b06040001c10750246514020380108980200c86842c5c045805000c80c012100d40d0503043e00009003409441e01c0c010116622460010581410000100b200d821041e000e000c1c01c0034205c42084c8080c40409032140785100750b05ea06404005c1e44440f1101c5401e00d80d0140c41e00a000f070302c41140d46074412114080050341c014414503412014001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 474368075 1250 474366825 474366839
    0x2030406260403080c0d0c0809060a060308160609140705030715020705060d020d0608031803010b06040504020313050a0b0609070816140405181803070807031b140604050c0613 77
    0x403260007444105c140b510300003888140c4000d68861802540c0890212000c0c40040c07841004800da10a000501c100841c074150394034544c280c410080d00090323007801d030181502400480d41c4002419540114450324541c0c84803299603c1c0c620398401d0501c03170701035810000703480600302d262079040c0911031f8040c050b640e0900c0c0400109401048100025941c248488481c01d1440c0c8141c5015007007110040da1101c0c0c480c80c036042009108540c5e103010ba4140031625505440d00c00545069540c100d40c0982c0766039507460150717008000c1210141503407003028030040500100700c0900e40140402d48060006075618002503800f030805a40207114410300c0e03590100035a100d80348014409040c200c003145400d40d56000601c040d4031039007041401407807581c244150700d6000c800c856010301c0490003450502c1d601317440e01c02441c0206c010217000c1c886540c510b0704440080e040383d4200240e0012003440f9080c1704a00c03803944d44404440c11201c41c418068803d2480c035100b015148207404017040c0c000c8540c20051 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 474369325 1250 474368075 474368087
    0x60c050a0f0c0506030a1b03020f0d050402010c02090f151e010c020613092403170309070509010801020a0201050601111e0f12070c0f0302090a0c020a1202030406260403 74
    0x4802c2e11085412a8045a02d5075464001e60164581301c001040d249405680c05060001715070310f49080c503104100c16412485944162500301c002c80c00c000869903a40e0005803400a0301010007541b050001041104404900c920380d40a8000703400c012280c588050300307114007018803c0320240b4000c80a10450b1b040c1d03100d0340995140c1440a08418203020709a003001c081f002c130540242020544415100704804055581098003005010000200510715250501124075550480b0100e0030004001078070684100038880041001410420782503a4074031206000b5046005050010b50030000491420761040050001c46d4010001801c80c5c03420000980600b030705200b0010255001d0340b206140c3c1e40005010782e42c40178031010750140e65810700e49010011041203400c2a07800c40c4a41c0414005611101c90480d44140c05010019103000c4520041c0e1902d0017401005024801c018201881e0943c080042c0c4110342c0d081d1141e00e5508182c40c00601262500d800610f0b00c0c2c10316900003404244198 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 474370575 1250 474369325 474369353
    0x140c0405060c10020313020f0603010308040b0f040b0d2306010915030b04090309060206070503090318030a151e05040f11120304060504060e030f070e0601090905091006060c050a 78
    0x3211140c46036008480283e81040340d42c401b6104072525000d00313500708003480e03000704441280d440e40b856040d50b88416460144d03000c1c4000c40c51010034507000c0001e905089601800c05150300c40d4031202481c0785072003d082900b0190270280904e44c1c45502e045415000c2c48d00850f016102d1144860030300e01801120207000040000b0140c803410340600da91100d1060280c603034040c1d40ca00e50a28100f0501914040000e081c6200b040420010080600d10100c20380390383c041c64070700100010380048002071401206401c049c2c04000c40e1129032010180d50350194210f80070501c507603582c06c9007004c00b0100310b8108840141c810200c2c0c14100c400680411822070222000600362a141c00102000c64910780260300184007080e0000b80601180350440000c1050020860040078400744400d640d588036030a500c11400ca406460010918603070084480700d0180c440c58004010a1800c0c110081d41e4000b0300104100091901c900410b6052180c084900c407240c0060091041e0b2440359510410082c0507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 474371825 1250 474370575 474370597
    0x30020d110406030606080106050f0108040b041106041d06030d0e06040e0c281803080a030f0f02070c030b10051f050f0f09040c0509150c072601140c040506 68
    0x980e03804000201207104520144c450306c0d0001036564206400e014807442c0003014079041c4401541088001303a03c11220591190303000a050254100d03150104202c5d010303a4000714140c807005058644201d501901741c42c07280a0880440b0075420340d540c426030710312020050b546c0e0000c40c108024820040c4408050740c2100000b03002c1c51500030325001d180082091582c141c0350001c00110240c0c01e199001c4410307011515144070f44041d961465035844201d02c2400c43c000280f513128600e0841d0040c0c80c7d445a00c54408955003076540f2134982c90941c50f01c040b24001119604014408102032040c003051001c241c0740301400034803280170505811349070104504d001a04009007000450041ea04000c0542400e00034484107a0300c89640c4030800041e075500a502c4400c014013800221542e0f0b484d0300a421100c3c030803005103580e4219503c862030401010303410015220306034005c13040c0048020b0021841700c000300780c02001104030080c004000d144040d42e40e40b480040510041c420f919001e0010404204a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 474373075 1250 474371825 474371831
    0x60604050d12081f060807020c04052d0f040f050a020604300b07030e0a020315100603060f0504020c031b0d020f0604150b0d080430020d1104 62
    0x1a400025041600800701211112140082451126002090300d03402100302c0c1c1d6480180ba14920700001c5940052042c001000031000115110328001e018144420708040d00c1030100b0314206a180640d1068529a03c00c80070f194000c0c0030203070b03481c0541c282c0900703000c00302c0c82e046460f20b4403030504000005800350340500030380070f0b40f400507034400f0b0003440145011010b150b039401034105c006805a00e000300440344100b4000c21b0000050800e44219840700c19410001188a8203400762442c060042c3c40c0250144a0794030081010340f4541c0185200b02005c66003207089a88406c01102a50388a1040403009142c180c2c061056203419009801c03403c00040c101c904081841c032094210400031311104c411034100b10007003c00e0540c1800b0441c07182000b0342c020074070750a0682e551212290803a880c0120300365203c441000d80c0e81d40700c16078500e0325005108552a291200411204a9000000c01e0300c80106040301481c01e503842074131880e1490f001084103481c80f001362546c21001c03100c001119881a9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 474374325 1250 474373075 474373079
    0x7120312020c060106120c080105010513030602041e050111060f0403050f03070c050c0f090a0903091d0a05060f18060109090e0c0406090506060d02070206120108060f0c0f0a0305060604 81
    0xc50361028003404022200102119490702c400500546200741034940c49a0402800d103c0b8650849919411101e013807034600c1d951000b441d5110141305041d00000c00341d03400091300151903640c007840c5001c800040b49030301d912030342d4070300040d54550300c940c10f820704903040003001642a010300c10205d0760081c045d003080c03480e100c07015680c1c285c25841240c400b4042441d0045e01c0b0240312041010201111080c3c0303150503843d1019000031902d03039006050340304403a1030366150000c05201c0c4010400601c1a8500c6080b1410070180b1041c52220881e034820301d0034507100000712203182003200503200030000f901d154144007906c3c900d10030000f8010030b454103002d002c8900103842c4000f0301c51102401c0007003001c0c0180302008410041514101ea202806c2103060005100b403a5513081c089034510782e0304001c01a40c2e49a5480443c0090007410080c0c480c15440388000544020301007840c6108001c040343e046601d55402405111a0103128051041c00c1030500413014058001c1e032141d038110b91b00a05681c01c0036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 474375575 1250 474374325 474374357
    0x5090d082805040506101a040b0c032b0c020a030509010302070203160801140c0a140d0b0a030602041814011e0b2809050306040201050901030f1109031905071203 71
    0xc0c109440c00c03500b82d840307101041501e201c8106441c01912101207048003019840b080d191140c0158080c03850740080004d044001c030201081114400003390030f040e0300c030043e8444100d100025100600401904100c903005a4030b00c007103200c0003110f503d41c40300c50501040c00c0c011002500500c404a0300b5116508444610036216a513007c01005804000b0802d01031340c0744480c1c0c1141c000b0300000c5004005129007121680c0101d40d05175070b90042044503072901a528030107030150040801d050f8112030590004018490303036030000d1081d41d001d4500c101c0c1c51700100810318200c80c044485100d100c140c480040c010b04c00c00c1d50011120f1903d8040903030b402c4c2d860350f2840341942d02061240800c005002c000c102c40c01101c903100c420918450801e0110617107010082501c4800c000c2000341008000600d9001340c1e03000707502c2082c8010304807404000e85005040c02ca1015400410719511034400c4506064861904038201040310317a1048c080e0440600e0045482d03200414501d0490910420a5401e5104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 474376825 1250 474375575 474375581
    0x909090308153c03120d090c0e1e09150f060d1b060e030f07151b0f02010219170a02010b100c020109170318040209100306030605090d0828 61
    0xe9803040c00c06888080300744062512940f00c406803140650050351400c00c108840e20159801944c403100c012039a20030510b0000d94503000358201006100b041c00c00e0000307522101d860404030700d03244100b0398884d84914920980e02c80d85040d05148540032400041d4200460459541e0000d030082c1020102c2c0d08150b5901107214006c0da040d61015107080000c0100641c09907200201c14002c0d40a032084602418145440708041e0090364044030740e00e520b4a8000d8401c0c0220754000e403030394207100308098852414200766003815000346d006114035000c02180c2d065549441000e0340c0d1156510084500d5241900d6031b940001c030004056541e6146180c13029105c4190079101c1e44040e680c1c031000c0056074070001d000e601a507081280d02d03a0306803c16490344600002143c0540080d0350346806216002000940030780304a0313030301c030750000400d036060f414503034164102c001582d1081d1001c1c081e59540c0c00701f080c0d0390055840124000f680460206e010070f101d01c1070803401203462200d036a2440d58a14204419 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 474378075 1250 474376825 474376879
    0xa030807021b2206091406090f040203060403050a02150103050d11030412150f1d1504030801120c0b0c03040f09020f090607060609060312030b030c0f1003021c020703090909030815 79
    0x2e4646d0081142c2807070314860040d40190003080d5400b40b070401d134010a54a0b0401080103041c0000060310780040343c001c00452100c0d40c80d41c00503064a40c0c40b0301d0095200c412080402c00421003c0c008507003050000f0043d5015a10600300c4446000003d440c0d514808501494950401d5950031564680141e117010f0109440342e2142c00c0942c200440c80d076640b50142001d98803440704903460610002a522203c0703641103c04050408091803614200212564200c0e44401c15417100000c4014010728040080c004542094100c00c10035030741d40000c1400c3e44289140e0080b5624204041d480f03a18103840503001c068021000001e04076107400100003111601d80080c3c4848015040c6012141d5250081c00d00d400c5064025012140310000855941c2e602c00d40f07501e101b4400b1100c080c00d05071191381601c08440c2d08010303c41c044070200b0368aa000398402c0d001940001c0b00c01d50007080d0001180900354a4035855615003409941703445180d032800c0041141c4c03c2e4420101000c0c000401078140106c04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 474379325 1250 474378075 474378101
    0xf0c0311370c0b0f0106080402040f0e06042916110709060303050306150c0714030a0b04060b0114190302130306090302060118060b070b0702010e0a030807021b220609 73
    0x1802c1221400d0010a03000f000340b9101c6400310890040c009154000745198106505035400b14803420b00700d9440028241106900100d441080304000600454405201460340500501155401e5001c0b0740c1b801c030072080700c43d0303d005244010202c58081c4640101c01d000c80c41401a20152030701c540301841030b10b400d03900a40000d540401445a1443e00340030000320300d14503c0c2d01c1071501c0c120401403a22808180700340014000d081d02e2640300ca840500070403103d81e40c8104106c500c3d01c0d00d4904080105a841203460000740e03140b0910701021480390072243d409c0039045d4141454003803540c04502951145099040019000d0000400039180303014012031680700f0b030003a01e00d960604c400241225500f8a15a017075504080081044059131000c0390340d9150064040a2a55140c110070783c003501c0e80080250441c40703046050414982e11100d00f5018503042d80c00c0e254050300302650079440c80056050590f00c00c0501071314516081860301c1e8029142000140801c0d0710382d4810181c021200e4100480e5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 474380575 1250 474379325 474379337
    0x50d050307030329010c020f060d0203042d060e15041a0a0b0d02130207080a1106060301051b030603011b030e010e010203040f0b0c0408100f0c031137 66
    0x8043c0c2500035411a0b50303a6100c005611200b000c024034007411084103150611001501980030340d2100b454210004001400d0190781d11041140800251310488044d40c803268921680d105081d061282c100c261030070007902c8d042401140d112940101071907610003009101d41c03401d07030217416004c038081c900c0b40e405001503000c4030324031400f03a0840d80e800820215480c0d00e001f111800030781c1c40080540c9040d405a41b200003994482a50700000d00c04c810004d00f02d4603021400e8250694044400080c100d4800184c03080d60f03c500d01414281c6509540030300c400d84a200c1c5818000301d85c0409154014801000414903141074044084281c126102e0040065183d941180034591b09003c0c400304103c00e08021499403501d03407110f582228403c8001001c0030310110200f060124840c0903100034205010a80e1310f50304030303100008020200c14585404241c10012214041800783c418208041c4401c0c00446c60103000c92100352100d0201d4000c01c4007484503450000c040300c010a200d50884805890305 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 474381825 1250 474380575 474380587
    0x5160302010e09190c20071a0c0a0f0305070b0a1512080322080c100e0c180a09060e06043f0302040503010903090e13030509060c0106050d0503 63
    0x50203104490042c80c00380e4040c0c014040d070300d904450b140e81c0303030f45400b103000822581d03806044540a18204821030b515600c5440c1c540481004201c1004495032840c104215000010720b0f8140b42c040d02600410a8000007508000300300600c04280f00b0034800e15040b440c200c01c5036201030280341c0945101c4c042650343d41401c2c400f0081c6400c207501500d030f4205009031510702903441e041184001407055006500c144d41400ca0103900031044103c89912280417a102d48604200c250b42c1c034140c42580c5055800c1005d80c5d101c20101141c1d83e0200f0b40040d00039031081c01d91180c51240c1c6c690140c809000140d80d92181004552248280c407486041600502001e00b0a4249080e08856401050301c002e4842c01c0100382442c1c100d00301070043ca802c07108404080403603401c160000d001c2d69001a03015428000c02108140c0d01428550035110b02c0c01d000c0c0540d4603022203e240ca0060200b000700444c10420103404503182140141200244d4500086901d540b1174010800e1800800310407280c0382c0c004140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 474383075 1250 474381825 474381827
    0x309090212041202030903100b03150703020c0106172a060c01020705120301060c0b07050f040e0402040c09120f02030f0f0d110c010e04050a15061205010906050622030516030201 78
    0xd00840c3c880741c401103040011420000e610342e81802d400b1001e05d9034598002040e03803028008486410340180d090300007031074642400b4010f0b42c8021425101c9510b0100c0104171034041a280081f585130b600b0080010302ca158528160328840302e185861018044049965181c2e159402801a80d80c24000903850b6580b515000349407440c620801881c0450a00050092950100b01100160340012109001e600c402e10700760342c50b11034076022109007840000c0110310951032000f500c0c0120310a40d0f04019121009004482d5102d00303000301311a155003010b2031000314800e03411045000e8001810b55201c8410f25055524001c260b24100800350095410b400c0a10f42051030802d1042e1181701509464040000090000c01f003600054804e6075100041765440803150302103070240f00f1458000e0001c82d1100006008417900c611a0f50006040800118841015025010840c0c10190520703091545000107500341000c0086080310000d070940c00080031950810240140c410300400fa80c03151419400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 474384325 1250 474383075 474383093
    0x11803030f020f03241f0807110606060a090f120b010f150c061d0708101a100219080706050703022b1509050915090712030909021204 59
    0xd12100c100d1043c04a803403070350b1102c4201c0fa40821445581032080c0d40c00e00d089501c01d241d81300119000803004940c004400400e0b18881c810111070344441c101541c4e1814215480f080106034041e0540042021507203c0c2418806041c070000da41c2007100000d6141c10441448407000d501905084000344894818051030b41c82e014058150090903161950905a60043c402c81d80540700041000803440c0d0800d00140740c0c030802e40301400100c1c60700c8038034090b440c1030b644030000d00910542d802007208404000d10709106102e50509a810a208103a2684040000072006c0010b9141540610b540842800c80400b07100c03c00c07140b08080d1181c8442d22810311004945e07005020400345481041819121240c9035100400803080c003007060078402c403030f55212028000082c45200501c8035403401050061164102030301c9100f8903070440700c80e11b40c05c000d83c044240c030941e03652210f40c00c1144217210a0300d0150006000368001e0914440c26940c03510000100d034422454000c1d4003140100380320400035402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 474385575 1250 474384325 474384341
    0x501030e03040b0712030e2103070302041203020a0b07030b01020606091b0f04210809040506040b0a0303020c100e010507141203040f03090b270d05160801060b0f1b0f01180303 77
    0xa0700074900c3e091108c210502c2050380c502e00f03109030304005c0001050035102c0d8040b240540003482d007011140f071036490040e40e030303410400341102c0c0c1d504a0000034101a00c24400c50102110590080040b0b841d00028483d442c038000d40100c0241c0a06c80c1d403201d408401000810480307500c1441240d840b4944a07a5000f80c064002c90040309502030700e182c401003140368007070ba554038000f00c0f000989521200005802043c205c5080703a00000c42c62400000c1c10703000b00b0b01d02d40410342502c0101c101c01041000721041d524607410705003c40c1040c451100880c400303c40c141d9502c98103d045030a20f018481d0609955001103408503080004030302803070100741d40070044800410344840598248405074290100f00c0d00d40d6162181e5880a448070303640140c0e41c540114020030307080b1301507030700d05a1094008220f0823281d0140810a42c20303c400001c00c203c81e1001c888811115081300d1b801c000e21004101c440c40002c0c02e264125110700040b41030009020310801495500c19504100014918075015040d03513289 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 474386825 1250 474385575 474385601
    0xc0602030a05040504050a09021c02090606390a0803041b06081501020c040f020c19030804060c270807050114160f060603060c120b0a0501030e03040b071203 69
    0x41c0032584881d80c111081c1d4064400894000c1001c2d96107085c0000109007801019600074124090f415103824169030b1080c1680c002d0320145da86695400501085115406a501c0f1035688082d440412048070b00c04042d1005801040c040c11040c2c9103001c13403403c03c411a017524032840004c02d010811120840c000d800704c040c01c40d0f2000b01c030b15007400580703080390050003040400806107889080c0c4e0b20034441030342c10b0b001c0244200f1004400211800094100f00050401c0d403183d40c943d0f200301c00c07802401c882c090354540c1d039074219a580c82c1e41d96000743c0048001142405200e0280310724200341c620f4400740001801541d5144603203000260b41c5082000da0056042c40765040103902506403a404179054403403036a0403400a1049441c0170503a2010642c07015001926244d00401040305c40e8018030040311860341e035001c0301001c000030141168004640c440d880303010a0300030000c0d94069004210000106070940c4d04042e5500809400c0e640808002c880d000c01c8044406491030300352241c1d007010031070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 474388075 1250 474386825 474386827
    0x5131401053c1305060907031406010308071e0f0501050a1d07120309051009080d0302040b1801020304180605030d0c120813080a02100501050f180c0f03040f0c060203 73
    0xa02000c0b0380c801c21540c0c1e4011080811200000e0803801c03075034416002c0d15848021204186407021660b6100e21040c0003ca40c0754644c02501d1107440c9002607414183ca4025085c6880c041d00c958a2114013010421001a03c001b80d00703c0c4400b184091107019001402000080340c2890301884200440704138030480c007030300c4c0040fa0a0f05289070f00010000140c540410452980651a0805075004019070b401180d10021040700c581c5110f5000000004807005141212001c060700c1c6000c0e0164012805500030b02d20041c02807030030458100e01c41c3d41c5c1c2001c060050701e15203074807440c40e00e440c880d020030b0f203190750303074035040c0401c61401c080203060651a0b05103404940003601d03583c0c6609907044001c51208120010b804240b03281081602858503952102025541c2c004030300c806500d403605107000c1d84200e498040002101e041c019030b242d0711803000410f00401c14a85461003846c0d258050004c8030744000c1230000780004007244000714000c40c050081c006800040e403800010000d00d9400100031908 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 474389325 1250 474388075 474388141
    0x150a11010615080c070609080a080a06180b0a1809140c1c0c0b0a2105010f09020c010212011721040608061f030c030f0603020a03060513140105 63
    0x15080c4244514010340d0315225400c0d80704c1d003500d0305407409030745401341406140c14108001c00040000816400005803107510841c1d64800d1400100c849902c1116203003461400d50106542041c0d0204810f840002c201003255911941c0c42245551445802034071641d0b00c04100c420312103005405040d070940c0c900101084a24240072411a01180807452041090388a14004001c041984a000780154450b00c5481700c0a1900051030300d6071072502c60203610341001982c52010168012103050303079021106941260300e40280c00d4029030144081114556007407000106050707111800034001d101c00280500710320f034030301041400d01ea000308881414030500441030700700210705400c0d1821141303181007501c0180e0303a00340402c00d41c101c0114103040e0403040300c0c0100a4107406505c00154031443c0d590070010407910308107010841c1c2c45c60001075403061340c40c00c04100081040c1c00071540716203070008042e43c2090075075842e0036040d9400990003041c0d465404004096600d51644000c0302d2005c909198541 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 474390575 1250 474389325 474389339
    0x1b0f020114061e03031b0a03080105030606090c030c0f040b040e060105072a050301020d0c08090307050709052a0702090a050f04260c15091501140f150a110106 70
    0x43c507030020180040c22542c081c038645a80c14425500c541920750310308100c0f4100c45840765252140341d0b41c100c002c1441d8800100d00c900f000265103105900107021000c1c0c0b07848040c0c07500c0749a04000c0c08807030341950070070000c1c41d407089610241005100c40c2c0065610785050a01c00e915035003000f0111810040140003001c081600846a0f01081e01c1e140e81d455484500400c01c1d014044d65504503580660001542c080c0100c8554440d0308450070a1b5210540c2d034440421300c544034402c17040094000c2c1d0080d03d040c003e00c01950711146e00079150f076210078160010300b03505504880d0b100c0d40c20a19060007195200550904030210365000c440d1107001c00680c940510f01e00803030176001e00003800c1818088440740202d60301640d400c45c50041070301a0742d01c1d00443d00c1090796800c2e28110102d045001c02000c10414100010028484207500c07506110a07801e0802d40300315961240c040c5035101c84101d0081c040e0b612424203044800304101d83c0340703540e002c0c0030202a0420101202c0c640c03550b07141c444104152 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 474391825 1250 474390575 474390589
    0x2030f190f1502041e09051b0c151f05010905010c0809030a060f0c0e06070203061b040e0a05010e06010e0604120317090303090d0306081504061b0f02011406 69
    0x1440d0701402852410400d818201005904490012510380c400039000c0741040d0f0142145041c040104085921561142c08010079160180c884016100f01c0c5100d804d02d0000307030342c007500f4a06020000c0b203410510708420808100f0301922107642e041c404100c90b800e02c528404801020348804c1c20103021703561900000914043c5226400b42c020031000c20140386543c4c091007800d8500780c00240c280b10703040400d04081d008000d052081c0700071442010b40055a0308140341a01d5015400401034811035866509061101c00e0480d407035500014200408624100001c1a01d800b0302028100000d00b5810820100e0003090003a2150703040c07102241d40c2c0002c5039a004102c41c01e5802c060071000301c4e00407130300d030a030f030340c1361180700f607500080089000c204407100000b015607c9518140211084c14590f0002917040395001d0107070000d1504402c0600100303481d00007500e03410034452031000906141010f4030b006403129400c1044000b812500c446203496909004140394840c040c0340480039420001300040c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 474393075 1250 474391825 474391873
    0x6030b060d140a084302031011070201090819081b120c0639090409030806190f0905040501060b040906290315190b0702030f 55
    0x11400401226004006804100341c02048a0340b089a07034250003442d281185400102c0300501c07101400840c4002401211210740c2d42c1003410140e414014401420307518010b40383d590698061180300848003c1c6c103141e00c038041d400c0c0d030300700388280d10b43c580c3c1d200041060308254882049035020620031048907d6a0441032080caa22405031540d41c0720094201d04e01c034411841440a5010b61080c084110203100b0041c50b0380940f082c1980c480342d4a4524008540c042a40b49034104c03902d03020002050f08007140c0d18007440000340149418245502c00003070a4440c1024101c0018000f1414805107040c44140400b0550a0491503400142400c00564280785248a00c80e6002c0e241c2000c1424071000790b2201d4060660107003d161341e940c807448548040c01880c03280902084d811103070303070070740b814000315028560800e654154915103550b030312001c00e25481039155070b01041c20170b1044104d8040003120002420700b00490307030f112106401014104410036244c00c120340c100c481d012803074548190700d950b4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 474394325 1250 474393075 474393079
    0x9020408030d0c03150303030f0507031506030f0b130902090105040e2802040501151b0309060f090506030a090512130b0a0309060218120c0f01051606060902070b0a06030b06 76
    0x82c0031941142c120007405c0361080c40460804201c50100a059050300441c06940c14a14103012544034240c089003124104201c03c00308144010060009902c03035080042a02044803010072240c043c0800614120080700d004c03602e00c0e0340e4001d44030460a00c444410b00404007107600308450000d84102c503884a40c808900114590380850085607101c1203070704104150f8014004101542e110100d0100c0c108109000b035000c204180b100c2c202ca44500000000c2566040e0345120107245843d8064450581d2980d1090921000a034040740300c0c0ca410380a503110b05d005010200e4410304506043e0300f1326880f0004011a107000700003114200c04640c000d030b801c40d0f22800741c0c942d41d5110044220010700300035100400260001038486580d4490701c081a112020850303071749402c85400020255118001074590b034100040c0304505071a580203402403c506028072440d00c101c0c00559076082d048880541110f1f001d0781d40419580140b02040d11400d40c0002500010010b1a045480d064800340700105024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 474395575 1250 474394325 474394331
    0xf150f0e0f010201061503052205120f090409050106060e06070804060804140f0714220203060a0801020f03011410020309060d092103150b0904181b0302030709020408030d 75
    0x741c02a4400d51004004102034114056442e40c0b0000041c013900042d105901940c5840c4a103000c0f0040081c0303000c038660740c00790003060b4038041480034016942006040c1840480700f481203000d83e0700c0d9070085c60007040c85807000058950030020301410a0717000c8a41c00b4007682c8148100340000303061904481c169003040c00c0607001c907501e514000c00c05213600c1c0d0300903600e401141c2e80316031485800560541030301c5001e03c1c040d10340a40c0d441800b0140c50103142d9601d02c5845044007a0b0182129401107030046006010301007026150038095003640d000024850390103000100400c144200784445412140049600c903420307401a50b00207560340240d85000c2c0c40f800000403501031415041c0d12060a00c1e078000c051609001d950310014146400c0d08ac416408030b81001d40082d2840703000740750380c810307900d040c60740350300f040c558a05101c0240f900400189800e2102c03d84079010a452541c0710301c44881d1500f1007070407141940305040c10060154030405403d0700600050046803004401d0f620702c010070348400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 474396825 1250 474395575 474395599
    0x50610080318132a0f030e1009080405030109081b010c0c030819180b06240d0914030a11120318160801020705190201140a03150f150f0e 60
    0x81d00c0204448442c0e000003480302c10344c00100000710010b012a15140e0b40703a00420503000381059003680c01c1110101c6458002c80a0303400c60040c03991116a00c54000d400300780c00c2540b510301113401c48841c407406950180010566610b04e8000c211050001d914420007480030180c0d94401800c40e00e0142d800600784680c1c0000104001800030000180d0310b50480144425140c40b580380d01042e01006082d14040d02c424001015410020030b8540c64541c010801071140032038035000303c980c2c0c104c801c010f2031b40c81c3c81d50407210126030160130681c450a01c0744080c5035a621006805095042c15012003200f507000355800f452a007820700140c0c0c0e032004a16021468410784074001508042c1d0041d40c00310055208031002c80c400034154050310300d03584a8402c40340e21910180c1c0308141c00c41600e500038000784a4800c0e004440c2c019101600300c1e1801d50801041e100c1c0d2139503400780111010382100303e00c0040c0c9102003020070030808007a03001c079086082c01c07444c0b0700e200700b001061420242c2d00c5500034036200d214 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 474398075 1250 474396825 474396859
    0x140f09011502030d0c0509090a09021c02010c020a0305010c02070e090d0e120f010501060311031009021b010504030e0405070329120105040803010302040c111b010318050610080318 79
    0xb00d80c0e211350804010014041c5031080540b4580112801c40d00418240c0d0003d071444100307102d0b081c160303500280b480f1800440c3e01813103129246900012070400c0742442c20407006841d0103900c540590311075000458281000032000b80b908810f5800780e20b41c40010300501c0000480170440805800c0715240001d980c8005401282403000191001c100301e210701700b860a2a0941075002030b0503204280c0c1d09000e10300d100b16101d519400107a031480c07000c200804080100381d45035401042070f042e07402081854007043e00149400c4940071541940850a80c04c1c2542d9a480e103031081c250b02141c14201002091002c0440d05080700c02e808034a401c51210074901e280e240d0b11014009025181c4200034031452800d80307011a40d5420270f1200328015401c003904e800c40c00340650a3307041401c15105c0100108101d04000d01c400724000302c00b29050544e1409480c489604660000700f805003d00020156800c4c44400381c140031301c042e440400207400c24082d06115000c154000c1c0580d120072540100e0061400e02 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 474399325 1250 474398075 474398077
    0x203120a14060d2105090918060903120c13050d050a030e0105072a0f080c04060501092d030b07020a0c0e15210106030c0f0812030604151e140f0901150203 68
    0x5503903004480f00100700a622a440e0202c080c04023400584020b0f480341200503650f0301507070300098039107400200041c8141401b803003d005504190480394074255a500003045291010581c142c3c0c09030444c0c3c102c48141500079004009910080c68403601e030800c191901d12030601c40d49089409843c070302d0300740c0c041d42c40035000c5500500070310442007440943e02c14455940e0700d10591311500444c2403400c00074003036019200810840d4100511200c16144107540c6107019010350b080310300d490120010100c041902c43c0764003440b40a10b500101003520b814240780c0c403510a03503031101c010074004000f0442c0300c4442c8040c0210084c8213481c2e410302e10005880f2543c150586400fa001c0719840e000c2c0000c02e00100c1071410b421034890900d40c520709070711040510785944041011200940701000800d030181041d60201428440810035503401a4541c0346407c3c80340921000000410410b5405000e401c514283d001c82c00a4101c43d610301e14112140801c0c10351030148034081b520890307820b820b03801e68001c0c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 474400575 1250 474399325 474399337
    0x9050f010203010f080c0414010e09011b030605010315060e04090804051522080706110339071a130e090105011410090311010203120a14060d2105 64
    0x2000075912580c44080d181c045609030b00c980030107845508030400c15400c151103000c58109080043c004140c2c2845c81c86070440f540513013400080e42d03888c0ca80c4090b030141c03031881c20940e0751182d83c0442d000d46400001810f90b15040c03100c001000f843d100c00c01020740c2005e000084140207035008140c00000f401d00448074015039200580106255101440b10074284000384a80c00c4031362654150214200c10907404a080d5005210003544811400c1c04082d00442221118000074000ca07842c00b0610802706d182c2103886102401514441c07501038182c041943c150300960000b0800400d600c519107503e08079140d098006000b03083c540018007e00c1c800f0402c0c3d003140a888d51800101c1c0354100354a0103402030900340307c0d25040c100d12000480c102d107400c17540d8a070a640c09607107400c03015043d0b0300c070109075510140a00b4107512040060440c01e4481d401e0780e901c144100d540000f010314101c0d02d40e91000d68010600e44c81103590018807000a600c5d030690308000103c0003020015082c09000688081c4103c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 474401825 1250 474400575 474400603
    0x10602030a2c03150417070b01060c060f0f050a0c02150c0310030221100507020a2316080601121502030a02040909080d060f06050a030509031e0a0e06040312030905 72
    0x1301030125040505400440e00903842040790045007000306859400c14001c65200a01d500402d8004210340b83c071521940070700a0042000007403c0600c10424000c407940040804403060b2602d0810040084d94030501c44008600d002414029502068403d00c0120092a030b00c0c02a10101c041041103010038002030156034060082280c1c0f10030208403099500020a07040c6492040942144016500b401100c0c0244010703001094406025511104901c03070ba0b04001c0c1a402d003c5020b0519010100545400001c000030008107443c140540d69080403c140c000d1800c0e0b054480013000094101c0422041500541340c0040e106d40b01c4a801c0301c040c1c0300d980d010499440c01d20203ca814494460000c0035440d0b1003520411040e40e8903c030303160325400c1612505003c1901070000181b040d010350001507002e08001c0561b1f241c030f14007500d11031152842132160000d40002085e0304101c6500a280451584800c489050400380356a5a581c040e80038110303038000f0503032140700c0c1c0700411108011a842c3e500d02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 474403075 1250 474401825 474401833
    0x902030d0801091b0c02090a14010f0503120903250312050c100902010509040b011404080d1106091e0a06091b140306041e06060902040608010602030a2c03 68
    0x8500007024007400303001d5a003030b4618003a5a4544020382c900414095140c13500c0e0180385441c40d03004c00299040c01064801102d4441034501040303c07441c0344807406000b03154030035210f81e4101402d040c41c11400c5200e50740510710030403681d40d180c0e5000079031150101c0610a450710a004241c01d4524800c010762000303190354071403035100c050150050090040003080c00b00f140d503210400c1103c0e4040d00e4403000c0c0a40030840400000045080c00d0700910100441814422101c4228407100900b903031083c0d0022942e900210070320f000980e407001030301c0c481c84c0340d130802401e45041840c40561608001121601e5210304500140c000c000c041c48051403c40d04031030200b2201c1c0490400311000f102801c0e10b007481d00400800810901c11840c2c0c00e41d008400900100481d990b59980c440b900041032101c01c0001000c1c01a901c0043d00f107004000103016100e1001d41c8407441c1c0f801c064004141a000081550001c0c001e206050341d008280b00b40c0d0780c0d58515a840f440d1141140d200742484000e0003075402d402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 474404325 1250 474403075 474403093
    0xd021503151203090d1709030a081b071505030a06170a050c0a03110d1109040302010204060e010c12080c0933070210050901030f020a020a02030d020616050d090203 72
    0x1800740780c019114055a2030450038002c01121500c0344148040d20358020b81042c001c07008240302000c00a151000001182d00e07102c101c1001034034001202200316039080e0001180c0c2c50440b01684002074581d05403005003803460906845102000380681c0d61000c1240100008000f16040d80142000304429041c00c0314090318a25040d84410740c00760b00362480e2150803035960050400065600849800c660304c1c000414a150401603d039038480d00540d520302c161031100c059980d4582905006520a400043e0f44070314010001e0302d0103519400703503414030200001600200d00640012040340047e89091b4550307036110703104002e040c001c00850a0304070718a40b404072004c0f6400794844900e50b02c0070302c055248814101c0551054420000002e4000c2010356085190a000c0d0b0090627682d00d0504011584c080c0382e40440d012030704048403400040e88141c0c16481503050a00460010f0009403000c0d2145180281d480900b48445c01c02079020000002400b440c000d00d9a880002020340c02002d0310b123455 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 474405575 1250 474404325 474404341
    0xb0d050c010306080c010c030e0f0603250207031a09071e080c04061a0c01020909040f03111203070c030c020d1a090c090609040f02130615080103020a050d021503 71
    0x44100c82116010034500b003004506841c1c0000d441000d10301c140c1d902c4403c003107159822282802004c0d2032036007104824003400c00d40d60b50b010203540300e0380c4481d080941500ea00c122000840b003c03a407800055404c190001d10200300c800444480d078012034400e00420761a101176582c078044d80b03903000404079064100784c10110605100d40204a44404c4121042038000c1c404200446d10503229000d802c0100030103540c1510f01c800d001c0c05450107144001400c0080381c2c80414220581140c1c02c40d81c010409048008050b000051600f0000304100200308030f1558211000040c17001a005c0c8090000c1e10084400301741c4202d607036070710442d4080d01c00024a006894071210401c8140440704861800e42d00182c2000d00004242c1d411403001802c01c40242c4400741403004940c03000d442500c20340100154080075844409022035400c01d00000001d11916040004007200c40c0f9100f07030310411050380300400140c0c1c0c075101c3c4c4800fa6141100c414203414980d10004d2218092020a0020708a000c01044490 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 474406825 1250 474405575 474405583
    0x6180319020c0a091104090e1023010e061302130305150f010803031e191b02010612023a060e120703050d0504080f13140402030601080703020a030b0d05 67
    0x2c014142d48a00c1d103181c9843c4204159003140004040c05801448100070111007a04100a020f2011054404c0000e0514040050303c0440d2160400c068642048544030780a0041480c01841c100710b00e050b503810300347c002a1022540c48062112a5004514004004c040004040055a010003100e940001c103203061035203004111000301c049005400001071000b804000c89224000b5104110f00c00c092490b40d07215400805002c0200078110343c150303188103401e541f040e2003094012804a003002d1084180003070955820b41c100b419580b800044490051712900022041800152100800c0c040321840802140b000f00702601c04000d038800850303042c07041d02e9200c00c2c406400c000076a41e102a0101400d10584100c04004000035810412100001403130340c40f154005108100b150b19007040c4445081840c0c0140300c03056030307031345d903084c81000045d4a203030007811446020b840641c00e5242c004000380c14140000c08010034160005101010984a940644641075004041143c0258141070160382d07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 474408075 1250 474406825 474406843
    0x50405030d03050f070504031205072607060c0207050f060c10060b0307020c0303130e040f0c08100b03010903020c09071b030c050607090302030c0d0f0c080105040c06050c0618031902 80
    0x24109444010404161140003101d081e42d4018091a5492278507000480d40d035401a54141c0d5030035045040ba01c4074400c400440d0814072044403075070341c40c0c01303d0341082e400700c5103440c1c0c1d80c40566110030f004100d107882d14119400980c41c01c40342c1c2c9498001458900d07003072a12a03e00c0701d104620306100454030100c588040d500490080c0d007110041d003140c000f07041d900c1c0b20707203900e21545030740b200400c1061441d000b1a241d40503105d01a030304010340b1695a400e182040c107422003112034006404001340701e00644140c220b2694101c0092008e001d16440c003940b100d600c0380c2d07801d006a91050006000c180200d1614240c5a4241610340d035080c06030400404190010004031514000d8a011031200c9100c0d2070b0a106481c0c0090141c55220000402c005001d000c1d11030403107540c1160424040030604210001d002402990700220f620301e4986088880700d02240c02c03c5040c001c043c8080300510400284050b402228000919500c249401020380741d802003803405c260000115900195655001c544644 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 474409325 1250 474408075 474408091
    0x7030512090a0201050711130504150b0612012d060c0b1f050f010e040504050601030507080f0d030203060d14010903110304061b060e0d08010f0e07050910050405030d0305 75
    0x5541c0325501c48984401d000b41c0d010340000c0c414440f070340200304645050850000014101152076411a000c80c0a980741110295038004106800c0c0e0300202c402d008400610404031549032520004030340210748100180107455001214030b60b038001c40000c2070b400304041c005109003c0c800036640c00004060344e400398011a4180c440001040c3c5400d030500d04054803407081452021454204020311000754006850300741004000d00d5032808076115445014061400740c006001598118200149071002c2540090b400e0b60200c044148914408204c40c80e081119143c00342c1c0d00e44075180042c1d403807500c007800540949907680c05d5100c600313015807026000500c03980b01d402c1908035a04119459000c0d5210303042c0410300304074800c6165031503020510706083c405d08001134402e03180c0c0110380c5000b02d2a80040007013070400300148400b00780e090552000b410b01d14554101c0346009507004003280901020130b0301880403644212503050040d425240504409011030300700d0320521900a001c0c7c01c0c10b68002d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 474410575 1250 474409325 474409357
    0x1e081c0c05070201020a02090615180306090619051015080a1a030d0507060f09080421030f0c020102120a0c0309090c0903150b0907030b01030c1719020c03070305 71
    0x3140390046040d1441d443c2c05030050030a40700c40341c00744034500500418840d402001c0103852150015420b002d010703070080e400780100140f06903006041c5414000741c4240e09a9102c50f0400c0034100c0103a400d0070401d990994081740a80764061003070881d02103a0003c2c42d9800b2103905c81c00c03e555028050611911001005005241c141380e1040640c01c07140c5489909134001e604480c040c0741c085c0004041c0d0500c2100b00140002a40e030740a8102c0d5030281c000c07111244000741c100441000082041048c2a4512444078a00150354014202e0403410f0004420701080321032000c00d680c024000408100040803140e9a200e041c0000104103c080320b1f4120040703034419a01160541c0b06100b01a0760003400c0e11001c0d800740c2582c44902443d1034001c03481880a84130f001d040c0711602c4a0803142d029071710300c2d1000724a017a0a480058291403010002d201002520580d040d0070010000072a078100c0c0d1f203001c448208880c4086043d0281c45014056001d0b03102c005038000800d507200c0c0050680c401030804017 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 474411825 1250 474410575 474410591
    0x303070807170702061f151e03050108150c13090e0d26090a06020a0201090303050901150b0a0207050406031b0b1204030e221a030c09041e081c 63
    0x40c10305240a880b0074005170700c1000007400c0420800c031000561051005140302e6240c1d01c0d0400002403011004003c00200c400c24802203690005025006081c01030906006540c10800e020b9a1031a4440010744415460004542152500f00803900c1c120020320303100d15000e4444001d800503214901e0381e14050f210303400204441d2403145811a0b0503200000040c41034176164402e00081761006046a200350050300e0b1000c0000d05144010202d80318181c001140303044c920f08024007200c00040007003d03681d041c185050380300c28600650506031500c2e0b031002503d1b540c0c00c2700124a0035101c0e40202d0780061400001105000c00c000c6100801d40301062600010b0340c03902c1c000716050060404e00729009a0400110380068025400051181005400c10070820b50f4000f541c010050041c000ca2043ca0390390300400345106681c541013549100aa00600302c684071040444c1001c140100003805030030741c002c0c007201d16400700c403405003c1541000c0f1003a1100011680301100f014411b182c00102031a00c992 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 474413075 1250 474411825 474411857
    0x1d010207081210050a14010207050a0e060d03030e070803071103010605030d1202132408090309040f0914030307110106030c0e09070b040f1703160f140303070807 71
    0x89900c02075100710000d05214001c84806103200d4007400c02080045404000700740f40d160088207000414280e140d505808050343d0019040c4215174000e01e000c4c5c4105030041c044240092042608070728199201600000d0f981000c600401202290440a008407803000400d0f2000001505e107041c0508044081a402401050300b280c0c05446101d0700b58101c007141d020704a000ba60b01190102040c0781c05072520b1214129210880601d80003414400c01c0c49446034160812008901000152800d180400b810505085550303400346c849142d1150f9203c1402c2030300042c85421813055030f9413000800c4840b00c45040080d03125001201e40f080022840004400c03102c03014000d0340e007240c5d0019100c42c41103003090b241b034210000062040e9032910980ca4002041346a0384018801401e45a00000b040c40c101201002ca044100508513019402840682c41055111021818003980240c5281145005261208009041c12403551103808003004000055800c044954454601603840301c284031800c240f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 474414325 1250 474413075 474413077
    0x20f070b07031b020919020918010e0a090b1603090b01090c08090705060d020f0c070e100e06030c011107092a0c1208071103040801090620090405040606181d0102 71
    0x1401a40c06400c010102d0008084840d46006d60080500c0141c5800c0c2030130003142c8800c41640c154401580c0350700c01008084261840150810b0146409004082403520380c11403000c1d000d403600c5005618601d07606040c3e40203a104954290780315414002a60b5100c0d4a800140300340401600804e0103d0002610484041142401e0350402025141000d18800c0d58100070740001454500354002002580e08414040082100900000039144182c3c607110010071480307002e0398460104070b100c840600c8019030300803681c0c1403101f1081c60b00442d0040181d504c145440d01d2136002d210b10320320300003980c00c841d641c00e00318440c044008d07040040d00c85c50b44001100d03508a0b64002506401c008043d050b401c0b441088d0303a0b07400c4030740c616180b41d42d0101500d546040d50b0095001c00000c0c0c1d960074030b100030001540203103c0070400100d02410100041546e01ca65403027490b072181d120b1036554001808100702603100c00040e00b4203242d004450030f034844000000305489003090038000d020170010500e400e0140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 474415575 1250 474414325 474414377
    0xf05090711070608040804180501091803141e0d0e0d050304030e010818120c061602060f071407032706123c0c091212020f070b0703 58
    0x14040107240c000d00716100b004c05081220079120410000410b0406403050f031200481202e4001742a5250064070300c01c4600c50809003010201c20034400c8046508009854800c507a0015566a03801d40401032491494250241181c6001c2c045011110801d0b00d60140a22240090458081c440c21540c140c1c1d1500003202c1c02000141c00201e9400d00303510403640302d40c002c6d01c1c604e9100e04000b0300981c03090501e0f104000c018110840400d801144a004026072a04219100c409540810b41420025140d00d401000e44905040c00008501b00500c104112107078481c400b030300e8545076105440d005001407007101d4030f284410701401c0010848805a4640e0084511903100c280c024403c02c0e6400d00070340950000c1c100c540d0840f82c1c400150045c0900d074840142072020040c00c162580300008402c07a44032030344007800c0207900d940074021104640030224130f150b00000c1003d02c2d21050b42080349032030088410b81009000d8224001082c400b00c801802e402d9100c0d450301c3c040c801d4400c0c2c441d8541d400c55 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 474416825 1250 474415575 474415607
    0x1230a051009021308030409091502040e010b0f13030305040e16080703090201020a0206161230150602010507020c0418110105040b13090605011b0605060a09060f050907 74
    0x221420441e2654607802051380d0070112445030402907031105802c0c2960041d510003045a03441301840380c100110b99220346d030b022007081c07000c40c14941030029111000750140a00703014400001005400140d205080d1000b12900b2141190f8498892400918581052007007100e040c0d05880810304058000c4485604005a55518401c964400340110098048000e0030303070550044a46101c0541c882c400140f07014240c010421542c80194035101484440281040007001017202500d8103482d003041c0d0901c6084e41d04108500d40250f1030051200408110328015103001d901b00000410741d406400c034503c81c440755001d03500040704501c2880152201c4040310043e20040c04012400116903e000c0c1070900018504141002c0c0c6551054895505c003442141024030f0402003080700055500071480540000e1900588544280c00003100655148200030706042d03d44001903041e45503010105c0c0142140b68090200d2a0303075003428840c12005020b2507000300651070000e090540241104807025140d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 474418075 1250 474416825 474416851
    0x71802280f140315010e06040320030c0102061306150e040b0f01090c080105060c031c090203060a090f0204051503010c0e0414010b0304031404050402070515100506040b0c010e01230a05 81
    0x11340001110220400c205242d4401030500c00400810700e4a8904000324184841c0c00c80544103d00c101860a1605806d4904541c80841000854075207543c00e00580380e072004010801005040540d032030410285c109242030b241c038100b0041400b42c11110b02d4020641107083c2500c598850035140b0a40d0000d80054021488000041040d070800500400e000042042078904054070b5400765150080e410340b520751000c0e00c82081c2801c1d4a0140705c07540d0422884481003041310381d2603440301c0d000624400f004e88610750364400614070480352040342150300c0d401802000400b0ba12100640108450a1050301640c500200c0404107690401d000341a11000503004e030a681e00d41e80c0446070055000b80b0402109018040002c160319180058010903208030050300c447c4102449061001c1c0303000300b6040f8400d00981e0704001300c0c0c49a004940aa454003210300380e503000104015400340040020300c0300c1d1503290072404043c1c1541d80881003442c484882030001d8545400d006d15065420a03680c1d0058051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 474419325 1250 474418075 474418111
    0x1050a050d11060409180501050a02122a1c0e0604110d050a02060d1d07050a0603020d06051c03090e0f0708250e0a08071802280f1403 59
    0x103140300c280c101d0b040000304098a0103860300000760945100d0a000302c0b910810b09245401c00000780100e590043c1c80500443c1441504122810204000f810180c01c20a080c03a800c1c6020000c0c0040c00428500251115540c54000070494100303c10b058107005074034949503000c41b00a1003c14494091904181c8403400c41080004100c0e1415800c0d404840c544114280d13140140c45d00310107052407080c079040c005900f0082d01d041d12040440d100348001d05410003031040c0610ba6501c0841c0080d2410362400688a520b18041031000f0659508540c0e4001260001a0450210012020031441c801d6964141040d61045500c5000e00161188140400c0c050b0003d1f065078410120140d1080303c02c8151041504401001081802403030061b500080041038440c00e5402c013001c408000f043e07240024041c451030180804080100f10342120f00b555000110b40131000c0d0748910320b42404607102643c0404240d00c25014100203580d030810340100c3c2152075445a1600e0b90001d91340b00c0c00d0094402d0b01544 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 474420575 1250 474419325 474419333
    0x10527150619080105090a031101090b0f15030f0a11030d0e271f06091a0c0c030f060f0f1909030201110c0a0506012c0702150408070b01050a050d 64
    0x100150740d01e000514512640043c000500b4005d09015031101005005115100e040050801210800c602600e82c1010340e1170300001d14040c58258002c5820302040420b40b0361320b1101580c120060301a50341032240c504004003500010400070007461140300d0700b800380c90340141890786880018044501080b800126076000d814443c0d03501581d04005034603078068060307111380751106c0790040d5030310114085000c1d90044070408542c90040034000c0c0782050740c040e5142100d1000031609001c05085400e10114240c90402410002c10101610050503288296081124243c4e10401120316180e00004000403030031030a02c0002c018000d40304010b001444044040c40c44d000340098400845c110b6603a05e40e10403200c26248041e1120503840b8000e800c1415003418154035040c01a003101c00c810340405a1402d142000c017801c9171640704024501d5280da13440d103009905040c01c0030707240c0001510743c508100c10000c1c010b00622141e88111800d44090f40c861051048000803802540d4001d40540d42c0388001c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 474421825 1250 474420575 474420589
    0xf120807051c030b0306060301060b09011d0a240e0d020607170c010b46030501093504060c020a0314010504050d051303030f0c050105271506 62
    0x800c0c020703000c84084000a08003400c0c440b2542e030388903000075a50074900907240b6050102c00d81040e03088000380080b5051205070106803203080c130404e0520014401600d94400f450345580c0f841c031002007400414590390514800720444614000880400384131107200c07410701500110704448000381c8a0604604a035082c808268061002602c1e00211740b4140c1e00b58240c14001030400c000f0070b10020a441002c5000d0101210000c0c041c0e00348800c824084840600c04c80c8155002400c511080c0000d051024001d050b0006458001a0855090582000a204009104111614041e0b4000042040200c00104400c000001d8041426820081000000e2150113140d0660740002c001d03194045c0d90f950341c038490100d000314a5107107175150401c000520005000d407240440d41800c00c00d20300700381c4141075080315005010007000d00000303d411400d84c1e032103400c2d100d8040b035000c0d00070031050074050b189040748107103a8030030109207820402000070000302082c0001c0d07070403001c440c0d0101074407410104000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 474423075 1250 474421825 474421837
    0xc0308070e03011b02070b041809031b061505091b0d110d0501081e0c060307121d0c0406060918020903070b0301061803050a060504060b0a030b100f1208 67
    0x8020265207801c20581c0c0a00c00c8981451549900d656190000c0310080d00303107565544004804e8034148010031540c00200c6801d141c0620300c000001d06540103207020796403041440700c0702000010074100c9508000303565000704022004040105d5241c5e94500400203141800c0350303100f40e0300030701d5008452021809405030811811920300420845041120a600c41d003020030700e00c102c02c0c0c4030001085007400c103000b4403100312845401045540401d80820345e4038036243d090787d40640000000681c21f01d01c81c0785540c0320f00c0d820000074803018449564100018172000825443c81c0501295000750745424400c0c0d80c1140d0182d2900c1c0c1e045850103d0306034208402c80703100340c1125001c0080a605550500901015204c0f10162545035410400024182d00038000c4c0510903400b40541030000c01c0c07000400045071a030040020865580d40c2c90a0405000e002c0080783c3c004900705c40120803c400e41f2091b034401c51203002400301440d500c1c01c0080000700e00c6d20810a40c002c08580300c02c0410545402021 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 474424325 1250 474423075 474423077
    0x1051005030d08061f02060117010b03150702150a090507080c13090215040f0611012d060510020a021503221a0a050a0c0216061101110301060f18060c030807 69
    0x6031040520b02210f070517040800f807900141c018100602140850881c0d40c1d00704540c0038000c200c00c1d01e036580800e139102c04448491030103103000400110514802c00080d10350152040301c810207403c12b00b004038003808103250120366034092540c0101d0301c003000242c00c8040780c0000f02060081c10b01c10702c00100070802980d0507038001410020340b0b0340c0185054000c0c8000c100d070bc0c0c1003030156450081c0003804800f10603903203800c0713906115900c035040c12000e0019a0b12680c90520000e00d0b8600340300180101070f40d40c41950441d202a540b210519000f14121040b00e0003030390042c1100303100c440e0400c65444201c07042c41d40c1555200d10790f0b45640c00d5064030941244a850001c42d581c1c502c04d0b540500150841f00c1c4880d07035443d6010804003035000e0061500e8205140018400600080307c08040130f019070103660200110007800d64000789003500072ba580c0d4062040c1d03c55a03035031548001058000c012030400041745e00140147c1a0700d1080030007404454065417058585100b50b50211015807014280358 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 474425575 1250 474424325 474424339
    0x21c030e060a08060325090b0d12020303061801180c1106090109032706030209060724050108070b0307080a06031a040507090b0d020f0604080601090207020301051005030d0806 77
    0x200258a400000307014400d810b4441400f10b140c4030042603c0d1401448a042212a030121407144480794850f0b00c0040e01e400d8030b004107104443c0d4003c14000c00200300054a0801031507050411716401100550054000307803460800c0e4000c0c058110200745081c884d075490054002003009070541c2a52011000c540e241c50001800b1020a50a500c5d001c0c060340d1042640e59100e09020030940c011044c070041006001c1c5480e401100465401941503082c403400307050540000c0c101c0d905566200464401030f601c1000054010342d000641c24410f2020f4000031002483c00e0000305012000041c4001140c0240705040d2543d568440100e403d10781c00340c400e400301d9403651070100000e10810400808002d05203034401451420f8200b00e80f40c058070380e02107003099107005407181494446403161f94659405480c0c29a44841508c042940d42c4120361040d10b0380d01494002240780c4002e90002c2821074021402030025880c2c00b0344101580c81d141c484c4681c0355114800003100d140c0a0580580d119500070500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 474426825 1250 474425575 474425597
    0x12110d08030c04080c01031b0c02120f150601050405090a1104240f0306050a170a05071e06021501030f0203160b09010314041a100504090f0506090a021c03 68
    0x1184158205072100c0384078000110b81844450410005c10864510901c2c0074003c14010011940c50030780c51000f80f4040000c40c084820a6440310094007801080782c6040b50000c036028074260351a080300b0454009501000000700b0115071042090350305585009002442d6925401155002400c000c0301c1d6120b005014400010009100003903030758620700d1030b4601480e151000d00d00a0480360070000800901d494800103001c0c0c1d031541e030740440c2592000250005c298510714885403801c2820302000301244201c81020844281d84074005100c203c6030380411820715283e80b000d03a2200009011039100e0a5000010400308a8102c0e04511180c00641a1403501000b0000849a03220310342021004440004220303a80e9689846107900a038a1914800c1039410a556404010b00c1d40c9400c0e480c040b10a40007080c040412115020010000200108070302c052518000103500702d10749042d11f00d03001c0d0100050134a4004585030101d140c2c010301c03004150401c41e8000a00c1d52107a04150308029075202c00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 474428075 1250 474426825 474426833
    0x71a0c071203080618010e130f02061315020a031409041d1e0f0c152b0c030b01020c060d0b091905060105180405130506040b010306110412110d 63
    0x11803140e010f0f95650340145001410700400340044546060042100c400410000300c1c03105100360070001e001c0180c0100304981c1071000305940c5000004c0d62003040052903c512203583d0b00598211070484c3c510310742d80e8803648800e07619818201c0700540400c0f8140700e8960b8007003030307a0000c1504600050001600b07144070700348a10009218040d540c0540e200000e206603501d8212101c0343c4840860005240102036080e0040d02c9140d5200554052030518605086020302c01050304e03000d0080c50700f8640c0c0810402100c1c4c04000c030010400720017602d0944000748451217400b400f4a03642c810b030010082c1b0b415000070b1004550044d203503544480d0384d8006a00140d9150039449e40600e10722403c82c2c1000101294071800c583c00500150305004041003090a4410b6400801101c0d500481d400074031036854000d204540641e40c81b001b0801d010f6041000204001c0d462802e06807406198100411105441042c506201c3c50240485011000840c500050710124070443d2916014104c0010108280d407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 474429325 1250 474428075 474428099
    0x2304030f0c081b030f030c07030206090409081606050a2c0f010612020f0402030103201f0c03020606010f0512040809040219020c030c0609040b0409082109071a0c07 72
    0x402001e505203441180e0216140c01c05c8540702662040019510306114502001c2c3d50785240c0c0700080c0030362004150518181c4d29a40480182500312644c02d0380c03204000303090700826040341c03402c803501458140031a040f20100d1244498408241401d1205140100c4d071442c0c00b50358540c01c0e460b8921603800e0303440401e1003e0107a48008d2014000304c00640b41544100000840182000c6016620600041001c550f95103041500700c00607111074511507141d0070209009007000b000080c003000788402e400007944da000081d030155a019074251a459129000110740318114141c400d400290705121413208a00e00da42d0082d042841144128900010400031070140d8110072840d01d1868114061280501e0301030240d40030321041100602060b0400200041036030080c107110a003c2c6a888500e40740c1d588503036002040031a001071040740c6480503062440412000044028040d24117200401e000c804005892000d880b160080d40c5543c00500200c040c142c0c11250f03a54181c0e106000000484004001c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 474430575 1250 474429325 474429343
    0x2030a11190e0907140706150b0307030e160513020403210f0203090a060e19090f060803040e0403052a0a0b0c0306030d0f020106091b2304030f0c08 65
    0x44100c045a4880031030192040c104420b1903402403250104001040368045000100720042d02641510342d005c03820711170024807504514610550052074040350302038a03100030710b110740d81a6906001484070300700c030309481d41501c60001c40302e08000c1006101d00e1900700c400300c41045100c4801130034135540381c48410f00c1038060400192140707680303246d01d00415808214003881e0760060000314a0255800003050044256210381c1c0100304103041c081e10b103996204490350703005000c48518000183c482d04072200814001200d01c10f118900100015041004030594044030b10755441c00810360b82c0c903107050f11203901461481c1540f0000454050310640c9441420000c2c1d00358074010b06c400381e0b0501d40240003520260140c0510344042c01001020b540c001011101c00c1c21500d00f00c02c0d0400e0000080e400740415400c221059410000c040b81c583c0c8504c10f0980d1080140da42d183d42c000c4d220340340c65142e6060940c024030b000004000500200d460003010503015803055aa070000341d50ba5000d9641000722270 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 474431825 1250 474430575 474430597
    0x21908070c061503140601060f05070c180509010629091f020f01060f0b19120612050c0406030803151318060c0f021f0204030515041703011802030a11 66
    0xf00d1020320a020f48541301d281e1100c4c40038011300c10381d4180308004c2c00114034003800c030041140000307814081140c00e52074100100b54551503c040d40c0c00c0c0804c1e81000d0039044603010ba4540c606840014405e55080b404480410141c01c41e40c0e40100c02c424803451540700328440d81e00015000000003a190b20000a0407150009501a01100c400100124251086940480451032a00005000c40500f05084034060308240d0a10041d1004106042e41d0441a580300d04103142e10b85580014040041c003510405907104005407401010b1046c1003104450142c0005801c1540600000e062018450700021007403030700510601480c1c1500000d8420ba0b501018817003004150f640f038107030030026640030b08050205981001500d9070461400290f60380c02003141e113170a15003095586e0704245403c1d41210040e582200513075000a0542c2d400b03e02150050f1070484940d1500b402c10541c4110104c00e0f06e040e180050000012207103c41c071684080c2d00007621130004d0a0b943d0360400e9801e1481401040d030500c403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 474433075 1250 474431825 474431861
    0xe0312070e0301020403080405060901120516030e030a1b030c020301020f1809010308030718080709061706072c090103050706030f0504050601030605041a0f100504021908070c06 78
    0x9080010610700418015a0207a80180400e00000b14031506450568005a40e190303142c00d04240101e480c21608940308143c0c0b0b28260510561100d00740c8000c3d41e01490b62801e20400a011000980c1e91296081000005e540c1000107903a4400454100c0300c554001d10700500170300099000282240c2c00400d09054007007002551016503004a203c0504030407080340c100c0344e550300d940c8881020b880014140c0d800c110b40c0d000e10240d2061060201c602030000d94048850090325081000003e0106009107190055007029280f2a0070002500901c1403145948982e03c9281074006c21051544440031002c03610410401e01000d0b8807084001c50086020b40d004000491070305030050111a00741c241d20b142a800d000411000ca03800103500f83c1100d90241c00001c03c0d0b0b441307050807841c00d0700d6041c545910300c09420620800340086821a0f00440c91842c1400d1815540c00c1040104d06c182a80b055841c548200680b86041c06540215404402c0e810320240b0b1216541d521400c03204810031003040441 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 474434325 1250 474433075 474433081
    0x915090616030c080a050a02070819090f06020a1b05040f090b0604020a0921140c0a050f130f02040803040308070506010b13090903030207120c05060a02130b0306040e0312 75
    0x150048440307408070190504116501c001c410042180070000d00052034a03440380e001c40e007070f843d090781224074542c2c0001d4150b0321092644030b4501c80c54541440b110004035030400200d44d03003a50712140d408aa60343d40080046203a00e0340da14030b08508035043c003240782441d40000205500c0b94003a10f15074005c20b950009110310285010700c2c0c10400a40b50a003c1e500c1442000140c41d00b100201d000c0c4c1d50104098035504000040609000164000040c060102d02000803400750001541c5c0c664003508441100c219500c40003481000c070305107610359621140c1d0740104992190654803600c03000441f00800752400d5141c0b0b0b071940c81c40c1d005900448030000d0000f81c1c1d105000f42400164003524161451900c1e08200580103640c1d440c16000d5480c50350740d190070303440030140030364111a009603021101e1402c4c11500c00c0041c0102001600645488c082c08002422000e01031007160040115411004005814100040d605410042846400603580e2102c02c0740c913942000505403008843c450361480d49 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 474435575 1250 474434325 474434341
    0x27031908060103110c0a02150c030708120a090f39090b041a1009090f0609050708061c0f0b09010b150f030606090103090b0a06050301150f050909150906 67
    0xa8401e080138002c0c200705102c1c25681e4440801e4282203242c04403500c10001260680c0041c0c603110704910311005101c0095820b0401c5074407030140c1041034050588030398964a402e0703042e09030380e40004000c2076060202060707000030b00c0c00d00300c850001112503000b070344003204e400307482002501000a10800414003001003006004e10302414000c50429213081c00008460400303100180c050300030071445455032442c81d2600511400c0c0d100010301e00351030288840220300b580d40004000314044c0c0c0148505100011701c5541c05000c007140100c4028025050048402c0000c1142200c1701800f00c848000720501400801d900958183c01402620b00008003d0b0b41a410001880791401ca1580e03c044188903106401c00c4100c1601da02201c00d58406680f243d00c0310049004106446006102c079106a0900c443c0244560000055800540007000981c651010454400c0045c1c480c030088041264410712550030180d40050b004943c1d4011078031804145151861005012201011076a103d03078100218a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 474436825 1250 474435575 474435581
    0x20a170c01030908030412050d1b090905060d0803090106090e010e0f0604030207091d0d0905242a07080a050d0801030503030718050a080a02090a0527031908060103 72
    0x5480e00342400c1040410981e5015203d010081c0003826009460b41c600980c1d030301034011103110b20840b680401107000e003d04191004108650002d001800d40d213000300ba421143c0c481c56001d9000141400d000c0b6145599203003080d80f0060044116540382d940000b50101e203070084a2480018800119050908450b41840e019a80c981c05d00c0b40d6020505010103e40c0101e110307400e5a0b0301e040081481e0507224070b60a00c0312101c060007019845043d40342244150b002c0c0300081561011500c64040d120901100381209c00a070b6048559801c0c20042c90058610303184049030040000300c8080070543c101100c0c24100350301a0f000d840c850b00030301100f8003081018040c0f0441010075007005596035045888841c0d8034000104624140310071903503031495144480425100a0000910140c4559140c0401c1601d400c0c141000f20700a2000b54040744018000c1d006e8644107104146070180e1603400812403200f507070242c808030403080c0401c0182c02900d2554000c001d0006029444d0f040c140c6c01c00600060071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 474438075 1250 474436825 474436843
    0x9030d050a1202071707080d0c02060c0d021606140a060b03040305030414150c12010b0c06070f090305062d0105030d0c061d01090201020f010b060d0513020a17 70
    0x8014040207105141608541280d41101c4080310041e20748182d0302d000014000e151245102101e40450500c080214240c0101b8080c5800c5a003405050f40c0f40e501a6500c4000f5250002858014040031a0b8610280d01034113254410a0b0742441d000ca407502d4400881d02d00307070385074400b0348001810454540d12502881c4001c7c42820b018178a54905520024014000504010311108d0b0400c00e0b40340c0c0f25410018070490f4400c0c2e58039400c3e141880e51180c0c070300c4e62008503d800b0742c0b0806000060880c40c1001660a50080c0700058505641c440d042201c2c51800050302c0d0007401010310300800410b100b00704440c410088a000c48104085421205902600040380601c00c0c80030300b0014045034038040346421060008ac1420030040100d868010050800d031012031400001000310b40141481c15007000702010b000b81c00b0b40d241990f40c050407c1c01d85040784401078002d6010000100080c04560103031b54480c040c148003244206055000510f902203540c005140c3c0700c580f8841c90300741c40c400e01c11021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 474439325 1250 474438075 474438077
    0x309090c0e031902060912010f0e060133080907030804060810050d02100305130b130c0b030c090d1110031509090b0606030402031501080303090105010f0806040f080f0d0209030d 78
    0x3c030815880d0f000a98520800c20ba89024081d684e1584c0b01507402508040c10105c04400d09020703042e46808016641d820901c80d844801c41e08000d07564403034004c207001c480415000c41d420040004802c80c2074800d07810250810340e282c0b00f0752100101086103400540050561556540d401c1e04110101207020140703600158400d10584d1042c000690310449490580714041c1004541980c502142030308000007640041e210403035940c01c1010b11809401940d80640c8509404410f0303644070a8030454902040b2000d1400c00d0301000f0843d020b1030318118000000d445410307100300c2d03000d0580100714080803800030310021a45541341c0c14040d183d010030681c007402c110181040b0306000741d19804603251014203400e02900700003010405645092281c1c00a40e21840c075250f00f2541d4610750300780e0707a134011951302c04207510303220010602c40c1e6080b8014040740c6050004108036241e644404c0d0101c0700d2144101c850b404200a0b0f0344140300510082c0c4000d400400300183c81d1918942030500b0604218070541c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 474440575 1250 474439325 474439363
    0x806090115080619080a050d0c1a090a080f1201090b0102070b0d020c070f03030324360204170d0f0c0611161101021c0c0309090c0e03 59
    0x802a40c911000038400748007185405a959101c140c0440c0c050400d900301c028100314440004100141c0025200d11103038803880072201c0b214030844044401c20041030004144a00e15999820620728040081d2740060103441514a106400d03074454926134401041d00300b09000210307000c030141070900701d186e005200102083c000c03080d4200000751a2117640c060039481100118010075152007a505031131002000710102e40d0003e46840e90030041c0741c1e081c402200042d0070107205850070415007074143c030114181c98000b103056050840704100c40c034141c006500c07a9807104c2080000715000d1607455100c010043c00041c3c0e210709204d4150310520b54401e141200b54042010000301c15800f0000040e03c1c40746250261889403d85000d001520445540300f031148408110186403403050070072000014846d010030450710a01c1401a42c685565681c00030802c000c8043c49191607003e01a01c4000c0c42c42403808600721510741103610216020b0800340360019108100403400e03030508001452051200c12408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 474441825 1250 474440575 474440579
    0xa0c0501050714190504050a0e04021e03030d0c021501032102010207080904111e0a0306080a0f060e0c040518010e070b092b0b0402040b0f0f090402030a02100c0308060901 75
    0x110b00e1482065008003818040c0c02003d40d0440c85035042c6c4025041c001c1103d081d0329602e07120403c0340ca00a03502a80305030036944141580d40c60b4020a244600e0001d0061400c003603070204110010b1094480e80025402000108503041d9541701030350f40652711400c403004000b50300e10104a114203112810b0419a0302c10045400860214010f0390500c502c01c1750080b4010715507072010340440c00340c000c244840d01115040307130380008a50380107040c0d200328595040040da41d8641d07145030340740c1c45501c000d000111884100004030300300e078000c100f0540742d0b8803c81d65140c5018022604940049410304000002c0c0613a0b8172640388280919410800310a00a02d4064240044800644a035401c01031040303a2444007010100e0100450160744884030f2144c6c846542e06003816004654219400ca00c03d510340800310700c181c0762100c0500348081c000f400c42c4117648480740034010620300103001030f0381c5840740a0070900140c2e580c1081c09000c0c1e800d990f6251182400b46030240402e5030140c0014420b000c10001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 474443075 1250 474441825 474441857
    0x81c0c11030702091503070303120c09060503061912060501090b10170603070905070503070e1906030f0e0f031804050402010c06021b0f2a0d0f03140a0c05010507 71
    0x603a504550112140c07a01900c038035040175040a9005e119a4050040510002c00e04d501300c40b03141c415450082040c0b0510803905001c03106500180035602c003140381480426003e0511000c44026000703280e5440b0281d50b210003103105950b07a00c0c41e04550b051344138001807005d01d20354011400f404105a400c00d04529500300040d00d080c010300c0d003141e1326010440c005212543c08028010051076805010070180c01c142c0f200602c154022106500850f500c007143c025682485800e002c12030402e640d06188050a1880880c007410b039181880980d141c40304c400c83c182000078413444003400b1003040210b81c4d0340b0000702d801c042040790241d983e204920348410400941d82100e00203007030aa10110060b82c9a1194640c0007103002c0401c0010681e01c40c4011042d01440e00050304100d944a442c3d00308420000003a107940c04400751401c058221094905820020b400c21000c112400d100c2d08010001411400510031143c01c100d803045e00044004040d101407010038403440380c021100e03140411104040c010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 474444325 1250 474443075 474443077
    0x506030303070c0519030905180c0a0302070303020c07081e060f0c030601030905010510060228020d05100c080103020f030318010e120303090304030c0e010612020a0c081c0c1103 78
    0x801d403400d1000d0243d4040070400c1c2030040302c01511415006008618090a00520300740c89400392034003680040c0310600c00c9144842c1c1c2c061191200d90403030352030316028101c11030180d0095041102490340030310003a19081c130b003440140040e00c1d407000207020445040941c640c1c0400e4140841c8140d8108409002d0703402c0c042045954085070030080c982e5241c980f400101c00070030811402a01035480c28080c070100000b10060380b803ca801541c202d807c0b000c120300e401000c15642240580d40340b80b40c02a55801420300850345000c15000d003041c0d0300c02c002103102450503540d849000c1f10000350040010710441c64410020400c002e019002075003410f0044ad01a007014002020343d43c18800c907800d6104007983c0d0101191141e500c1c55084d6501ea0410341d092130340d660424082180e11801415000c9800304040b032460341280d01603a100100c1100708001d5400a5204044240c200005040c0780d402154800c40180104003c4403496100b00c40c402c00318008a070520704800040003120b2003034030340e0408004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 474445575 1250 474444325 474444331
    0x152313020a2006040f03122306060a022104150801062c0909010e07140306060f01021e330c0406120e011b0206011a0405090a18050f030d0f0506030303 66
    0x1100d28403810345c1d070030159110031041c04507035041c0e41404408916501c80d8221045503111800e00102c440e01c451707040001500500b6001001648109480305008900e0004c1804050000c41c840b85003136100c00f61b82607c00340c0c40c42c6000105084000400855074070001900d81c05451200d510015007030f00795684142c9481c0c840c02d52184401d9008903000000070740c440004124180d0480310b182c0d07640c1f01017481e000403104195201740940c0d00095043c1c1020f01a140181105a000e003400c0300b11501c11b000c901c0c0c00d06107419460710640c2c004241950381500011500014910302c02000c8540142d061201074009010103041d4034107001c01c01009401403209000707003600c0d600114070f01180f020141d00400c2c18000320700e100c2c40806c2e509044d042d002b26035035060751940c0c0180214030728020002521845580300e8290084400e00010303010080561002c1c04000000d0b9040200000303a44a031454035181610300b04843c2c000113009000c4444030f103d0000200401d580a11081c07801c0000280c80780401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 474446825 1250 474445575 474445583
    0x180b0f100b03010b070212010c031d12040605070c1e09200a030f2310060512040602030603011e020a1209020307060f0c0c0f03110103152313020a200604 67
    0x30500c51700715035070000101040c50401000700604410320300024058a1000940726003001d0002032401782e214007040890f9540c03d88541145400d1030b040c0c0c1200c2d1940403007029105a0350048003c103100007107042160b520902c1c810f100901608007101c01044a10807500c5c40003845648142c4100c010300310080d07540c0b1030010f0a00040214010201d400038050480c9060b4504481011041c000b444041c40c160040441d40035071450507844082c2500d0901c50401e0710a15652a607000130006240c640095501c0200507001040740002074840003401914030100841c415000326401005507404509011207003560a003d0040d040103801003621103200340142020009010840c1c0396103400341d103052100550041030b45242641d01c0d03400c10020050ba01003161946a032020b501c41948c485d000d41000c450388901003c0500b4903280a007029071081d454265066120404102981d0340d0703805294808460710030303000d1394418520754020802405e440c0503c1c00f8841e00c20362000309601c0003c899034001c0d44 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 474448075 1250 474446825 474446827
    0x20f0705130908030f010f0506160b0415050702010e1612200a03060c120908030f0702010b040f0605090105030706050a0e01020304052215080c06030a180b0f100b03010b 74
    0x180e000d94801900d030101c2e010b405014008103000599840d248200c0c125070520760286c918030785a00401c2980d00c07030035403440400030820b012000480c118841b1142c00a01c24032042581d13001040441040e18000c813400e10150b590341d101c0c60300f00c40d42841303c0200e11406003220100c440c10300d280f01a0b4171124900c0a440c0035010002101c0701441060905080b01c0e00402c000f4106a0728036000020744104d40e21b1900160300c03110315086900103401a545030650120089003150307640c0702c0f1514103900041c1480119900c80c04410321645440c8180d004070300844401007045818403082c4003100d001a807015009034000002000b40da079000e070a4a07044411031030101101503001004030b04e140070390f40041da484030300c1c402102c0c07c5114029903251600c40d1624281328941d80d4003021412054a031007151100d40040c0503e000a00d00074004540c014401c107000107010f1020710b03141c0000e1010003401c41d40001c0f50801d11525810b804105a072040840400c80c0d102828103050b2202408103108101d06050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 474449325 1250 474448075 474448099
    0xa0e04230a030311070b1006031a10051303060515030615010e13060807060c1a04120c03180e220f1106070501110d0c0504050a03020f060708041206050601020f0705 72
    0x4c044001c441d03045801502011304c6003003070000b240718940f25216017004a407a04400c981c44141a030701403036a00d0401881c0140c0c1c00070ba807600351420f03804501c0b0444082c0c035189000c00001c00620403140100008818058030341030f05010306240c003001424131003106010168100381c03a070b403003c0e5900d51083c003919180200701980308203202900d0741d50010724403801140e00100c1c2a540c841e150421450049800380b0f68882c241500c4507501ea4191009092540f00040c95846140a5440d03000e59603c40e140040e144121080c1295226507590807118420403e0803c4c45000500c3c80009042d90001e41134035110020150348401c03200302c0444000b480490000f000500e00c0d9581c40a558902d2380080081c440d00c9800041d400d2954403002c2030040340d41ca44503544401500c14070544050b1440503100d5480141150200504003104c5041517078000b40401544001490200c0030b03100905d441076050300c11400500c0c0070007e8801c000c28050455000107903401c10100006910b00c11184260390076800ea0f2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 474450575 1250 474449325 474449351
    0x60e1c1121010510090b010807050310080307050703110603100911070210390b06030c130504020405070c02031011191107080703150e07050a0e04230a0303 68
    0x3800c0440262034803031801612030820700103401441c40b4550451394030040da40c40340d90440c02c43c0c82203040240004c440000150603680200700943d08420901d49102c81d9540d00c1c0030003445c45d40714074000c03103068111510400401500c40d440c10080d48085030070350b042d481c1c1618920b988188c03d1140c280483d86602401001050081c12203070100d401408840c070a84046101404007500c0d403100003103104108100140010303112428001440c240c007501c0704500c80307071b40f1001c00c0c8110203002141c0c540102118101e043c0c0d01c02c20b6022201084000101c0e40d403030180100021a5401030094040c030404082102c0180c5d4040707603000c49030b071501c4400600000700900d0441d281c003c3e41402035085e4441a1030410f0035410481290644125904079901d039626910a1519807015102c0200321001728000c0c1c0e4050840b5401c8000d403107c0002c11070301d141d6070b10000640851003681c804404d07140d1140c140024494100a05140103030301708c0c0014070a1000310302c410342e0303680303c1000a4105075071400710985032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 474451825 1250 474450575 474450589
    0x8090109030c060815040e0a0201111905061b031003030c030314130c0902092b1a090c030a0b0a02130308030a0509161422060609060e1c11 61
    0x5141c100e407005000940f1000064000d82c0305484110f00d0918260f11500c140c649030060000149810028201d2080700340e0056a4419112140e101c060046906c070307005c01200035038681304403400782e0010409801c10f080030540030060422052650002002004005c0751202400c134216541482c0002251159060450085c00c0c900f500c1503450380c000e400c0c007003005242861401024040c580300400f0940c0e500403001288140c1d00000d8000a00641001c0e245081c221380c40c449031202c24000c00708101c142d9a9003502c1074240e21200503240c440c0b060281801e8104886503441400b54001c00940b9010307143d180c82920f006000701521600050300c0b41c070a9000c0060382c401941d0110f0696201d00f842d44521001d000308458008191140610785041800c0045110045031003104a41c0900c4502c02c0900814001c81040c2c4049845050300703900c3d0504180c4140c900500e8260366000742503003407003001011780400c000058815520768100b8807923031031038010140149511281c607070b03c05a8480003140203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 474453075 1250 474451825 474451829
    0xc0304050f01090c0f0f0e130302070e0910050919080a020f030d05070216030f0b0a241403150a050a110c03030103060506060c060a090501151d01170a08090109 70
    0x503508103c01c80c0100071a000c2008140d03003030501e4009500b915903c029528010b45c0c4107070102d01080ca00811040d89002c100801594024815074034140d456100d103001d8024203603242466680b0200701402e0035581c030310440360464a044060000c102e1094000c039200460888046c0c600d03400000e048032180d00030030560040104e01c00c00d6a48a420700320b1400f0040c242145d5403c0540204510b0113000642642180152076101440d02113251103919803600b64000100200b4100b9034a0506a40c02500d81d070514102520b400c003036146031420950005003031025440c819000c0c0d84038030503814540394031a04403540942c29101c001003c0d40c6881044014100100941c1d0780048005500308007010040b00450613240a86014411900c03450148501807142c4103140205400c290041004ca042c0d070b81003111828060000418050801d500c958407060265000ca40c600718121481d4130300d1340f0b08020341c5004000c8404100c481010418038607071224254000140040d070300041c06180d90303008480041c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 474454325 1250 474453075 474453103
    0x203030a12180308181603080d0216080306041113090504110d03050318031c02070c050a060e030c030a02010f1110020a03050a0b040b0102030904020906040b07081201080d080c030405 80
    0x508402c040c2070140c0340250980d16103400c0c900b440344031000000c0000308184038004504680c4105413964032040c4031a00140544e203800d80d004c201d2140f01d681010034a6070340754004c5035001e5580c00c1c190200011241c40d4101c0e030030003200600071100d4106141c1042400c407046840040354660b917034036061440d0706140c003925030721007081241078082c50351050103988160160303081340084895030b041140e96405412004520240801c1d90300c039800107190003410500b0f02c1400304402050316800050b118881d103801040008034889021880c9290811940318407500c1900030380003501107500001e00d441c1c0c00c003500100748905100340d104107040c1040b50300000d00d0200c43c02c5440d2104140002c02402040e18014211400c0c50344100f074501d040d124081120805800451600da0b481c0b041c84007940044110b0380e80b01c10140000250f61044000501e0300c80e2040b407a00c0c3d42c52886011112100348180c1101140c0ea002c5460704600035007100906800030815602d080d240c3e582c6140961410701c812000c50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 474455575 1250 474454325 474454361
    0x80c03180c040f06060908030301151209062f0c1b28030b060103050906150d050601080304290313082b0f020a020309120106230301180203030a12 64
    0x19082c0e0000d0740c81340b42503810b140d0f02c0d0081d440e80c484800d40e40b0300080c00381c10011601380058088a6024003030202403400c17aa01d0200f044015038030f80c0e5080b1002d01c1203641001101c00e05004a121580300d001e910008011122401c003145030789900d42e138600e102c82d408403115580500521039510840d00c0c04c0303015000c03031840c080d4102c80c01408030b54815074401202d9864082012907550740c00382c080c051190681c10002e020306c0da103100c030344014000301d4403500da00030016203a40c41c04034105001407806000c2d80801541c0d40c9140176503840042c022009025a0b0441900d0044410004841142d80007419171980f20840105c0341040c0455101341d40c460952854809480705c0c0c82031309003c2c0b090450005a0341000f550460b42c288000740c1c40b841d6081e50043c0c20400000810b072404400342043c0d614400000503845440314650f240388801c8070820313400c05290014a18191509002e41d000668901c81115810042356001c2941c03070040130b4808003403080c510400c002e491455400318801504080e41c00e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 474456825 1250 474455575 474455591
    0x621021c0902090a0504121805040204080303010f060c02030316060f0507200c0f0d05280606120305123301090806040503030c0c03043201080c03180c04 67
    0x140c01811030403801c074022450840044c89241d1148100c030300c1250800002c1c5000700f48140102d9541c0003004503d8016540000041241c0d11140f01030f03c081c0405000a564a50400e80760907181d54981e0701200812514424020043c0c03408400e0f1000c1c100b100e07a56601c00c1c0440d18200d00074201202406120a20304420080305070390201e0b400710001031f901e103241001603495005644031240700200d203822588280701d078042410720b10012070045c0d0007202942e0301070707034280c482100705201005102d04400110540c4814080303d40704440081110981604201d0219900900306016a1444044c220458800100c02c2440e9082d400d10b441d00742150100c0c3c1d50202d40d210b2283c09400010580011607241020455841c00103103503015503007240c011410342d950040e410109911212007149107000501001410000e01d0703041c440706896202844006420b03ca8030820085207919400c0d0400c41401d0a114008200c2c0e0300310303500702620081d42e4000080180700e00d480d10031400303e4141c0080c502400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 474458075 1250 474456825 474456877
    0x71e0e040f0b090609100b0d0b0402040906030209090307050d03020a0c0501050f07231b1618050718060f0e090c03090f030f0d0b0a05190905010906062102 68
    0x19240c003044480030001c4d10b0b200c06002d110b410481340d9205801d41e2000034099070807a0409082c3e411040c02c00403540e0a04000428281c0e08690700040d81d0340d4a81d0418403c42c07802884084c0e2110440d0011410080b241c0c0740d182c0d81d10a124569024560b00203151801d01c3d00c0341c000102d2190300440244840c0c10b040c48410391424084602e40005460300c025101101201041150b040c0e0300c0052590601209444c15004110210050f030580c0c45144c1041003604012840200101402040c1e204000d0740255080d003034901c000c01d18070803c0320100c40c8041c0001b074900440183ca115152030a4a010b80000980700140759010250b84025160100450100e54074000e52280740c01c102900c103151030b429417031551fa000700309015061420900081443c4910365204402040000f4416a500380d50b42c000f2a08100c2103600c901c0404414070011b00c100251400b50600410b070111040003803e00e0500000d14010001c0c42209100c640003a030718425031043d8040e00c1606042c034070000c01e0201c00c000c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 474459325 1250 474458075 474458081
    0x70503070c050a0609080c060306010513090516030605100c0606080708010603051e03040e0405030d0504030c0c060806060f031b0a05042309040605060d050d020d090b03071e0e040f 79
    0x451039200f03a000e41d8002c20040d00c102d003144100c0308010020500f84032510704001c01d40c1c00007400c2904000044c071000724842d00c2034427a0030007005001c800090908010403992100c058601c0010203060a218007040345031a414100300c074525652600c1c00d01c5016618090b400303005158400080d078400c0d80004101128194030400407644600100ca0a206030841c42d05002990390048050030740081c48104007a0700f803000d8032640300d03120b94144c9241c04014440315080710401e46058001442c2507101c4401c100711642d40703401402050600c407541c0e01c0c0a01c0024900d20030201c3c2d480b50041701001141d01c4842c6012402a00000400600c3d111442ca0000a00c1908a4441c50002004c0c1040d025071014000481002c00c540181c40710a142d03680741c5400380038200190206400201c8ea4240328080fa005120240d0112015405059000030303402004043d041c2039000100b00b00802c0003403001d850f4020074000c11440c2a407071a0100401412001e652004400303403901d810038141510008540f1041c1c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 474460431 1106 474459325 474459329
    0x5090a0e0307030e010e040608280b1320030a0303020a02030c0703030509031506100f0c051002030a06060f0e040222030c05030d02030a0e0d08070503070c 68
    0x4540307941c2c0071032010f40004048501c640b08940c2d020300c2148002c0701c11101070000a080000a07500c0e821180b035035040c40400309400100d80c07070b440c08514400713541001c40c410051a2003540413003110940c2c0700440320442c8440b03000d0030701442508003800c081000b80045c00d01416a0341d094000358080c0d04c1c11025440244000305520b41c04102281c065413007503907069118000e00c01414506823014800c1c1d20f103020100c08008003900c0f8920081080e841500c0d01245030840440162820111301c43d015116006007490242d1a0086400942c02401075410400405982d5501120810021464400052103100c10149207150940103442500403010701012401480c501402c40750181ba40216612560a001080945000e010842c4c1c09a024000745181c0700b45440d004065040b0028210301c20803d01c5144c2c001d200c000390030307502415403020440f50344660714200710003141e04078 = true := by decide +kernel

theorem cover : BRFrame.Cov 474280575 474460431 := by
  have h0 := BRFrame.cov_init 474280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 474280575 ≤ n) (h2 : n < 474460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
