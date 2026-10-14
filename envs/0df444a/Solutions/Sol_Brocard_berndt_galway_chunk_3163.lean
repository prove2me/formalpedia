-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3163
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:50:41.356054+00:00
-- url     : https://prove2.me/submissions/a28e1570-0aab-4d71-a3df-a0c8e816dc8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 568705035 ≤ n < 568884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 568706285 1250 568705035 568705073
    0x70207080610030c0e040809101b0317150303190306081020090306060f010201020705010501060f260c030403020f03070f0c08030a02060103060209064e01050d060603 73
    0xc440f40755041003003081c0070300d170300c20142c0380c01d120705001c04920810219280000182c0b100708001c1ea04c40303812aa08503004090300c9820070070500007404c240d401280007a4902680300002c8050b10307950715030070001d00590503556050b802001007600005003002c1000c2824480e080000d11155245070302030038900001c15041403203aa90b0045003261041c40310340f8945030601e5082604180c2d201d07010030713914407020302840d10441d0000d0000d0344583c400d40448803481e90240090004e96504c0b413014040c0e14040d0458400706880740e005028507001c65041e03850b040140d00e00d11100740c0b94503464441a52000d4800e038114024800007005004041000380203261007030415403071241090804a07684942e60300080c080390020004402c42d90350024055054035040100142d5400d860800600710b0b1007042c1b6801e900450a02841d80d140c24070b40d581103810044160300c100c59041d0990011b0207940b86110708290302140d080107000354100031b03d0341c500103440348100191164880d06d65940c02154620412 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 568707535 1250 568706285 568706311
    0x31e05060d080c07031b14091b0c070e0a020a020a020d0c0e0c18121b0a090e060406050c120415091e0c0b0405030a03080a02040b0f0d0c0810030b0702070806 69
    0x420000d20541c40ca40448030286080b840d2410a080c0c00c40c0b4210070340e81c49205040750301c0400e5a4143c55421480d100c00e209c1c0125a40f054003141007500c901d050b110f0880c00c5d803581303400903905501c0d40c002c0b10404902e03940907003500c4901e6030030441302d42d5031004191030f010614900410141043c10080707000d403400307065440e10b94100501030f440600f4145401c9000e24403100c4817081c2401d00107000304c80c0c08503240101c1c00050003000421511059a030001564a040042407841c842010038454000d80c0600307800d00481d900d6084c1c040c5280f180703c0300400d0080300d06c0700050100d007620070312006036815642c02041c03aa2164487c400700b09920b007044c404c0702880b03201c61030421044d10500002000c1c03d0040500b02464180066241d980c40d04001e010300804000007461480c403035044401808006100b82c5c4c0792015034070303801c409820201d58204260310f40040195082c1c0030307101d0030303100d00c20841155a90741d0540c0d4482c40100e1018100c101980b0030504003249050042c030a41c5c1c440c4110f00031007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 568708785 1250 568707535 568707539
    0x12603090909071502070608241e04050a09020f101b1a09010e030405010509030a020301020301030602041d0c0904180506160909020301080316170a120c031e05060d080c07 75
    0x84a01402103213039005650055200300100760b003101c142c42d8084011320010020310030441c40d2440c0501202c0700d5279801124010703400c40c0d0100000c60200c1e000000d0f13400b0026a6503242e001c0089441c02c08002e980516000402c8005103003080446001c0364092038040072261030204208140e00110f08100c0f030046100982c8100c0c034482004507607114000000a0021a0b2480300b495200d108501990b17040010000c0c40c0d03552518100113444e02c5588c0a00215a030751b079281460380082d0040e010b1751350614141030441c031a80d201c0d0080c0d98001c0d04d003030308141d1410700381204010040c2a0106084108442404401e02080e400e111052054000f8944c1c0c00f125802e804001340001d0141c3c121903400e07403040c001440903540001c2030b10201c60b03440c0c0c0b2405440c446c504140c9084100d2521204007501c00042481c034040c4c3c011000391300301121550900c00c92400c544217600351180f9655980080340b1280311a01e021540e60480b1f9040700002d000010003081341d4485900c641e000c104107542e0383d17102c45e1007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 568710035 1250 568708785 568708799
    0x20c0118170709090f031d090103061a06121b0c0d0c0c03060c080703050703150e181c0215161d060d050402130908030403080415091b090501260309090907 68
    0x141d160980741401c1100101f101100c0021466038060101404060f6102a2070501440e0040440c292440040403140c542404c6402a130003044205e03500c12101039850680c081c402640c0c400e8aa10402c44405040b1428003d20b0859041409140940700d1100c510000004540c440c42281e8100d100c9545484c128584080054261203014050030101840c000b0304024170b07a07500d4001d5056440c0616100c3c104c1c0c948124609585062618518031401036800c20b11484070036070000070003041c003602a5400400d049924506075441140d6403c00d00d00c2840107800054070030050070441c15041071081100d1540c600210304071742c00681407402641d948105000541c074224203203030302a50340e825062103001c15a075510505404050401014016a41c002c1410000180101e03881040300c040d040207105190300f4665040801448a0141c103050000007040c081c81030b001c0c0074140c5c0e0354200e00c1e0041e500c0b28401926414400c1607460228002070114000f113950314200640902d1106000309003803401c2401c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 568711285 1250 568710035 568710047
    0x7090e0606040c141c0b0315010807060807090501030e0f190209130503071203140f18151603020c10020415080105030a1101030902100906020c0118170709090f03 71
    0x83d00b0000d0088203040c01030070480c0202240c0006030449105840b111801d60090301906c0f44401c0b82e503140c010308083c00301e00d58594040d541242e411404a500a82c1d0b01c030001d907155042038482d000000d401d4101807003154000c0d00401131483c504000c035503071a42d02e1303001d0390700340500c6880b01902444043c08220a51500000c0e59030041d610f4a195a01010342e07507686aa0b2381b00d080d400416088000c2d415644160180e8071088000c3c0200300310b0380152134503a40780072034900100d41401441064540003070f9030400c00140c00d803a50341e03107107026415501c1e06009201c82c0b40344803400404258082100b10141d407000d1003620741c0641c0046000d40c0362824000c01510200300010824104045c0100400a039076000591100840d009038109005540d10b0004030042d01e078040307010750028220300c803444030782d030348154a407084645503800d440301d40c0160740046400600d140c03090044402d0080003070007490903c0240100102c1e542007204e040507580d1341d82e0415a20007d405030390001140000d8001d15801034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 568712535 1250 568711285 568711301
    0xf060907060e010e0a140135090a0c0314160f03170d050406050f13050a081303080f0904060510050d0f020c0a110901060309030c0b0702010605191409041a070504050612010504140105010203190207090e060604 91
    0x1520748053b6030030041024078107000e522000d8201d10300d0300041011040b443c0100c1c1c0800708120000d01c05c41c6000c0c180080a400181c669200f80b50408000991038150035045890030f41d03000000e09a040d006849481d2142c114211701da000f048210b00000c000399928000f00b44141c072195040d51107003249401c100841e041c590105004200c06803400726180e40c030404403404207400540c005a5848a000031400030b00a8000b145030520820308135006102002d286800e4a90084900100581e03c84404505844c07a025004000c5425200c040e40007070381800c07000d03901410318070001601e599a82c0001d1b80c040003d8081c03407804042c02e4018070403184100702c50480c00406990b0040142002d43e1a0003450481c2400340f211844000080340040748240102d400401c0700800035900c6a00302e03003400603150303801e1241c4e0388a94904485880e00c420140300050407540c0c140c002d10706041801c100e80441d0a0032055a0301140900c000108441c211031140c4d040020490006004070b182c00001d00003101c0d500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 568713785 1250 568712535 568712563
    0xd030516052103040c06030c12060b0d050115090905061206130605010e160302210c212214150103050f060907060e010e0a140135090a0c0314 62
    0x420400001c541c1c019551806c9078440e1400041a0351001c00403510324030b0907a103040c04182040400500da50b00540600700001200c03404100f203907650544946040c41010380600400c408010810610165600c0346621800280851001001c001710103414403504556250130311041c2607060003848000c2c41a14050620200010300e54200445485a407181c1541c0700d4040580000d0b400200d08102d211041c0920441c910b00b6216080c15a0000c01c260000c10145005036141d018202410800b0030441e80901c8206141100b040d5801800c100c00c0c4109907000d5502100c0401014620711041203e03d800c410498000c150f103506600c0c0c1242880320300100c03400664050814001400400304070002121241d01304441c104a01c0340060322155450541994410f040c1c01002954600ca210298a60b50090303039a40060b0420751444000389a01984402982e2840101c184045020101c083d800140c403500311f034010102ca5584012030701e81600126906420000c1c030310700305001040072034100341c19 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 568715035 1250 568713785 568713787
    0xa05040816051f0c140d020f0601030c030209130c03030305070e01020d080a1a06030903132102090403210b01090f0b0315040204030c06020303010e240d0305160521 72
    0x41e14000444164030f60003a07000200102200058540c02030325581101171744a0b010700129802c0100003900e603006a11450094001d8500d080720300e00c0081a44c034141d9622500d5000b141e81550244100e0000003007405100b80032658002010490202010004500c070f650b0214148c03600c1c41004081d2071400c202d0714192360042d511410f070b40d600035950b554801100400040d100c051041020b04180c02c0c5409150013190000a104030642d010004080048441c8903c1c0700003983d0740008114910900010b02c2c540c0721116180303005150065031941c01a000b49808a0318400c900004606044101c10381030700d050b42c50103501c04558000c0d0450340105006401026540d2425406500ea4072004241c4284001102c154451030358480c0e041c1c07030156401090414038642c0746c5802a5990f402800340550f08203200380081e40103298480c8a003a203403846009a080300b04c0032010b00c00c0c41c03400130100300c00b409010302c00c4240b1901141803078026135010348024004094204903203d400d040140c5562042d541c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 568716285 1250 568715035 568715039
    0xf091c080909060f2101060f06050d0b0f0a0e06150a2a0803010602070f09060308090603070909110a170402010c3e030d2c0f060a05040816 61
    0x1255030569000c4001540c2c040c0701541d625000481520b0b0301388180364482c00e43c00307010f081c0b07003a07094410201d0004100200f220315102d0b07414441581640c0b11b4600007400030840b11140e02841d81092408482c00340c0b88a545000c0400044c085100341e41003a2031144001d401c000044c0b0307001c1d0400440c8030a41a815160030402c6034010880c003901140105280940d10380d00100c584542190111240c2010b80d40d034076542c4481000351100028803070640403050746034000c2080f0541e482954201c0744c1c0324007004d01d000030100a1110340e400c01443d990070f01c1242000010f0801c0705001d6588841d24a00040c0e5481d0040d650140c801008003400e140b125000c6410400180d804c041410324090b0400e18412901d02002464a81e8202607450b544480303200040301c50b5003480f481c078002c1d00f010f1704038140c40700c500864401722840e15502c50020200558002c4a595001d450401c40b041040d02906860032040e8010200d070030350340400002c400207600020100b107a0750090040405c82007414040d400024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 568717535 1250 568716285 568716293
    0x60a2301030203100b0303090409030e091005060306151303060f0f051b03180d03150b07021e010e06180301061208090f0414090c0a1e0e0601020109080f091c 69
    0x5040104e100303c1c983d02d45001c400b0365010010703116941402402480002c060349030003410300c0b0b01e01030003e0042c05c0100114500400c4e840d42107081e100090020303030441c1c4d120303002c01035140c12070307203044c1e0b4600c60810500021050f200e01381c0d8081c0d07008007004100302a0341100c2d5400c031224000c858140918110610101e40c8140d882a031083d00c030f4282d0f85460b44c8920800084a85040014650520075280c4450025030107400c05030307815501c44191611143d8078500342200c0e1081e044001d61184082038100603621051400040c00241032400100310a5100045075042c0d022920100c00e07070036902408245031809000f850080c085600518549440d15980c0d07680074080c6080d2288034601c04052040140c80320307448000c0a40407481c460029061801c080c0780c6132445041e107103004030b014900100b60042542d1040c450040405044041d107803a001085034084d101900703290455403108000d41c04900c618014100d0f0410041d0860b07966000741040265001891100460590f0b56402280c003103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 568718785 1250 568717535 568717543
    0x40819020928020d110304032303040201020303130302011803110c01110709050604090f06050402030c01030203150423071e020109030e1306030219050f030102030f070507080c060a2301030203 84
    0x52042c0c20160712600240b4101c000385c05041c00d41140604d01004100915510100783c00b000c2c500401c00c4a1030320006020000d02e0300c4103e4000c0d015a00800c045241548840104a52140280300010344000d03004500c0c080705100d89000c0d00055100b80da03460080105000c10200c1c1d102c01d003801e61920340e0702244203840d4140c0e841418040c9030b0341c00029180c0d445980005032a151300800584805145140850080105860523030081c030401c195128154000c0c421a03000c0d1503203498101b45800400c2c00c00c00502407a005007031001400f10700602d40c5a60030250540600c0c416201c854005241c2c4002c0702c410440901d00304116814803020750080383e0010303140c05080c0e0f01501c060804905032000d11010b440264002500f02c00b1110301505402460380d00f0201703981d03088401140d106c2c5c2501c1058240d00043e41c444102c004404045a0020b00030343c014030b2154401c170800c0f402c0c0fa041210650500a00f22003070800e1035101c40c0040441c0d4071100a007568001107450b01d95aa50454000c00da40b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 568720035 1250 568718785 568718851
    0x120203010501050316290307050406110d0e0d030915030518210f090a060801180519050915090703020a08010903090506030c0d020310050f09040818060408190209 71
    0x2004a46058084003906e4070804a804200480400e40c0c0d01d08084500500c1a403044c801c0034005002e0001400c101c0d6404110321201040d9999440030141045040054071740700d080e0f086090058015000400340c00d203c0e0307034881c5105a03440008081c50a10300781800c60015505000d8690002d9000fa100d560110264148400114401c142c0b900c0e01048581c00ca40309610061b64081c00030b50000641590100d9294161580c14405d074200b045240c01c00e40a0701d0094541540c081000d10f00c0507100034141d80680e500241a80841c0c80f1070044d0810b2680e0f40ca070070303201c00d54141c000301c500348290f00701010311500800402d00200203500c441e49005013075040398003c0c58403540b00040410b844001440580c0c6120082000071135881c280030110f071100c80e2103131280c80c0c01440c02e1070f090900380c609071422601c40d5800520440c134003900b100011441d569041040350f4000f4081c403002c00d0744042045010701482d05041550b800611034010080d94000050903100080403000c0000003646401c96903d072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 568721285 1250 568720035 568720049
    0x506031b0706110d1d120403060f0209120307060c052503050f0d020c1e0607082706150f0a050d02031005100f1a040506030604110301120203010501050316 68
    0x9260000c52070000c01405800c0f9070740882c8072001c2002c4040c0080c590240d11507000040c20700c07504111040c00f6545a01d00301c49004552002407204001042c15500045c0342c0d400741d000c0061600b50007a0004145880003019143d2540c804100c40e4108502d601c1282003032001404c110341400b000c9c0500e107540340380407505c822401c901640c419007014000c0c020f450a544941c4c0e85951905500394101009401440030138006110301318242c8020300300b00b1130384d822401d101400303008180d5600c00c0c2560b5003240601084c0d10269013600c01c5100e0301d01c201702c40340c9114648025265a0509401d02a084d4030340c50789117842207001e041204516a601888513007101c20a0b00c0007207090402e8000241014011116400a9414501084070b4410300424507416906c080742400042d584414250005076409001c01e40a18820002032002d440d090010356400341008201044420301c0003020fa00c0c40c1c2003a400501c801081100d60300c11450280903c6001d08030550003480604070307942c040444042a88180302d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 568722535 1250 568721285 568721287
    0xf090408070f020310091b0509160c150203190b0603270a0b1b070312050a021c05010609080c100507030912030f1103030603061f050d1b0506031b 64
    0x101c01c00551602d082046600281550b402810304072411015081c5108219251010034404140c1d80c0c060740541c505840000d0b0441c02e66940312111480160003145840007406a1800e00302c0019480c0002141280d00b000d1025880c0d0405540c07449000c00c648a119140d40d0a002e41240c81d5200c8206903644240c00b49003945851920700400300302e020980036010342034000c043c03000c801c1c000d9844103e03003c2c54403030003121510b1620a058945e98001c0c4107004000a0070710302c21740024400c81e040241c2060100310014900415480c00d840020750b12071403105460703118401004089d40180742c1e40003c14000d405444603508010000340381e101884952424800042048402d05d4845e400c6036002d400902001914014242805002d41d9804051000010100d0240070541c80c0c003c402d42c0e02800000c0c0050190740c85440c21800b003020700428070074011804900014032940c900d1480804140541a403148505080c02e4010000d41e80740c0140380074450400c03c0c0303d403c10380d903540000705c603040d80181 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 568723785 1250 568722535 568722547
    0x10e040c050912010605030f160909031e08010807050f1315150c29040f02031006060c0501110c0304060e04060504060905090f010c0203121e010b0a09050f090408 71
    0x241c800d80110105035821840c000ca024840b0a415440001a5142102140c0c01c40030100f00313881da44c2054400701f00402e44d00380c1042240303898603000004020301c2414080f011416881c1070660171042054a040082d071031000400c0094400e02206000e00710a4804c2040d00c01e440c2c000c56628403100c240d8035109503a501000e032490707001d4804200074042c0d6901d00e4002c0d10b41d0b40c500900303040300280b0545c0c0103401700f8001d590900204985145d82102c2e100a138503259696100c0d0901c2c0034a11005a0f0140103141c81a40c040b030f50391180e10098034090703e0b2281b00c0350340c034144a800c403035164950079400300f4200300c100c89200c1c00000f038900301c800c2450100d50800c01c02d03011034080d180c66813100ba001030411f140420209846e0700200d21171401001114185c0324003003031140c285c4440700e9181c070241e00b080050140c000702000b203913a03012482c5454441021540f01c0f1003c40040b0076440440044008190300101c164820303400c20090108842c0e48c10200c0c4004000f5403145009000200058000505 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 568725035 1250 568723785 568723787
    0x20d23070c0305060406050a02041401050c0a0503160b0a06030519050a061415040b0901150e0a030507080706080705030705070f05070618170a0201110f070603021306030b010e040c 79
    0x311031805034011440c036041a640e00c3c0c81c503a00d00d400d9800704c5d010340c240380000344001010310a98084507180c90b14941142e00a40040d0b4055210200084407401201e96103004035a0400c000c00280c0e020045d107100200c0ca90909000740e10002d00820303212801c060040020403000148003801060000110710780d4070031071800c40d14000700140000c000c3d500300b003c4101d00da450f82003a10301c07404100400a4002d0740743c0c410001101d160184040e80000130000501c150440840750300c4a1603d06e04108034081216000030b00c00040682c000c4500d544440e500340030305241800124020203203401e046400307042000c0e001d030003800000d0900080041c046a60014881c1895070344008035045001d440c40251119030040c10410344004101d1740f141c2d40d4500141d024143d4400740ba00c04990390140c0810042d030b0340110750903080f20f0b942d840c0920581048485030f500c2400880020003464500694601454070480e02c2c150403517000704c052520341801d84403540d030012500c0312100c4d021940055080d0306504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 568726285 1250 568725035 568725037
    0x418021002071703030f15030a06050c0d0617150114090423010c110f1e01090203070605030f01050a050102102c0f1002030106050d02070302031204150c020d23 70
    0x3003d200307200c4140c4480300c2c0b03900340400218000c2c41c201c11000c9485c0d440d190700c2c1d011164a8101140c0560040000c00042507040d4000fa81010030120b07124600301d010742c0c4030300949940d9001540c0034200f0024030b4444003010000d0f80c03406808840d00140b290b14014901040c0c076215880a0b00490202d0006400c0089070003c1a540749000d400d020310071640c61038842d000b4035860362408003080c18584040886080028201d038400c45540c024501c00494860b032405c41da50109558605640341c0c546180160760501410004d8035696540729228a0701d58510f09601e84107900175806100040340a121a0b680860744041c507401600700494180706a070001d185403d40c0541c941c0c0000050014001a83c00c01303384c100a05801c001182d4440c000159004106d100a214581c003050302000003025041c1a03070003604070305000c1e0040d282440350403001111400b0048030308588800215041d80f61032034561003890b0845040c1d1004110300c101240b405040f1504504104480d1600700c0311002009121070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 568727535 1250 568726285 568726289
    0x30d0c030b062a2d03090405040b070305060603010e180a12090504152d050d0303050a0c0f05220530030703020304030228030b010f05041802100207 65
    0x7800d00c503038822008405041c1101000b10100003085442a40000d01c00e00144e4a80b03000d8284800301e80100c07203901d04940c0380700480d0b101042800f01340700d17903c4180e43d50b10516104030700070f4001c06054600300b80d0080407540001e011500c40c800501c0184151001620005c0e0302680c2405600d210101c0c0c804458980f586417140280301041003c1502e0340a07034070039482011a01c0031384050000f6142c644460603040c0340b5000d10f807071047c071071400680d81c00d0454441000d03d00009c2d00d071800b03864540d00130944170011148141e0210b0b48690a22510103041e1090310130b00b60031071502c1c4c00c1020300c49400400620450355120461b990150900341200245030b07080c4020300e07001340036004a17018035500d00c0c1044161461580c3c14200160f83d6005c0b00808022285816411b6019515290440c5d0030000c21030202ea0031000712000103800903002d180d18000c41c1c4051805500301c001b4540c07416901640410740c640145010310706150202041c2803a540078190495811036800306c8000c60b043c0120710705245a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 568728785 1250 568727535 568727539
    0x60302031e0c18041a09130506012603091509040e0106170601080607090302090c0f0c0a021c02060415030212070306060906050405031e122206030509030d0c030b 71
    0x500140b2840307045100051190040c3c0080146140c51441d04110855186203c01d8800182103188024107203001d801a175070281d240c20324450190481d8071040d180c46001d8200f400c1d081d210322007907100b04612420306500d244501000b580b134000781c40c010501e0b6000110841d1103110010511030340d030b075070785412010903444400300030020250740f03034840d0241c003000901c800384a00400300003003000b24011490720b214040503190000c20504c0d581c2404100c0c00e00600c02c000b014401d120f400c40c118410b0700113042548440d0005d207003042032401003046c14207161303001403043d501018514005031103020a5400700c80d42410a00c0107090440d03000e40107407085c440c850351801040c02c10032550702d4040d0f000000b520990741c0d0b44082c41d43c0710344042d5654800c600960f03038150b101c000000d900f503600c808400c3c04050104145c6203d83c2018604142540080c01080803405902c0b819088050102107030000503d44c6182c180b0050429010b8542c80c3d114404240014a440309d2001d4001c50203600001310302180 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 568730035 1250 568728785 568728841
    0x50103110f27010f1d1b0d1109030d0e01020703020d06060905010b040e0c09060f09010905060d020a1e0e010c1106030a050a05060924010c0803010906050307080a0c06030203 76
    0x6012141071220b002409034998810201501081022031107100f00039418401d10100800d4482070071461400600d900071600529082203c0400c2d00300c18003481c00040300c00100c0e00d403114504400c140c103001003240590300304004c4c1c1c880940301d0f03030b800a219011280c05940008001ca41ca08249024020316005a8642803c00c000082c00316484802881200c000d401d00c49003a80780e800446155114141800c2d5100006110f2450102a0f4038000d0a8a290504041c080160760700082111a0864041d012555038041111421140c216218403d960f401860a01035040740600140850706140c0c101410001d407000480708001e440c1d0400c400400d030003880280c80b45052000d02029240c100d402640c0c00d402c090206820b0304007082d6642c01607600c26004076003102928a915051403003450040d040011f4120148042884040198080d0105810124219040400303140c41d003441d50b0700c05080740d0704c4408014085002d01c00000c061340c1d00d43c9005a941c0c1c5a1104c420030740128007409810340b4503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 568731285 1250 568730035 568730089
    0x10b240f0c0a030f0201020703050403110d0203060a0e0d0e030a0602030705040e25051215030309150c01150e01061b02100c0219080c04020a1715090604050103110f 72
    0x8400034401d200300b4801c0e81c60300e81440303130343d407080303090303006418004000c15070034030061000402d20500243d82490140c000b62202d621500002e24159042d00d0380c1c4180d580e02d8095011900d001e110807441e0512a00342800207c0d64140803d1b0b031015141d0700039102940c00b0020580305480307481141c008040d4880788960b581030032011a1325140400340b1050016200c8140320300c2450040041e5080319140c0c0d050f4100b1950781d031079207100749100d4404d90303641401304002801c510342d10100f020240d03041619099481d041044643c60031a1390b40f02c8030411841c0c030404200300a20b146816641595642e20b803a159601c101c480e02030752940c9503c0d0003035100509200c4040b2141e0710551640c0c07440d00031180d444004002c0f448203014840c0034060241143c01801b0300c480f01e0b0600350002c0c901c030003551403c071014401940502d8010003045d580344154590904841c03801b40b40c26400d054000c0c10454080125515540d10b11040002c0581d6040c019588078001c4200d6681e049900c8001140c2d001144078550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 568732535 1250 568731285 568731307
    0xe060f0c0d12140114040f06151112040b180f090c0720010c021e0402160b1e2205030c0309011d100c080702060a0e040b03010b240f 58
    0x80b49002c100701c01240761400310a85640954407160403105800341c918032080504040c000a001c00314a0b00c2d650b0345c0c44444c00501580100810407411300181d0b2015030503101e20314403500307000b40d070003071000d0840d4284010b2180b00c11200440701c960341da00300601031040324000800c1144e082c1c80c0e0402d0b4041c01f2141000f01400c40314000b0240948928501d82c10408907081d40f01104031150700050001e0001070700b0000508041405449103210714640301946220340740010241c1c0e01100035000348900d1490a502003090a042494102410b01446840b41c0c040040085801800a18540d030074000c914180004001000380300c5541034104090700c2d0345544c1910200c1c0da950003080c1c030b98002000210f640001420740012007090000041c4060b9140ba0501c8080320b03040000c2005542e984d00c10130052006039070701001004120b006d034079084102145a41088101c84c4a00c10b55400380e4104a00f00341903550b08035100614150001410b82c4901c40f012902c90f8a004903440741d13170134020014030f4000d41 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 568733785 1250 568732535 568732547
    0xc150302030601020f0f0d05180603070903050d05340f0605010617010e010b0a0203040b0a0903150e0604080d0f091112070f14040906140f09010902010e060f0c0d 71
    0x914800c1c0c089a005101d44407900f5625042400340c1811504001d0503a1f00003440b60008115245034540c400d028002c0c02e8002441d10380c0f007a5401000305000d200c0810800200748141d50520685082c610f080504c108150b12903640104241800d142031303805a41040302d10100c814800940002444103c0050707854100f0040000f8011100071400b05000d149622030701c90001d038113880000314450f040b42d2030b000c54a0820340003000803500703501040c040411446460000340c1045507c69035a035604034a582051400b040d0f0f4040380360b140b10f0500c00f401503484800504250803980c805d466aa5940c0540f524000401b08410301c00348607408c0c101144140441d034500012803070000c0b540e8000001c1c440490360340d2105640f10300380002c803d02c0ca0403c907155019110000845018202040c9a0301c0d42d9074482c100d0304084003024a41c29800c0900018a81a114042e80a04200020000c03d00c00341c00280c40c1c2c01c04814a039206da0341c006011860404020280c8000140d03c204840c0b0403001c080000d094 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 568735035 1250 568733785 568733791
    0x90e0f042915040e1207060506030a020303030a091115120603280c050d030c0609020a120501020a140a141c0504050a03030f02030f16020a12020304080c06070b0609040c15030203 78
    0x203c0c50070200807400c4a40e01092903a450182d845005203041c0b02c035643c030405403400502484d8107024144002016840c14001181301d40c813903103c000350041147c902000c650355200c1545015800d002e030a010340c07441d030404484440e23540401c403254950318440040c0c9015403102d1107401c1b100d005c0c10403021010041c484140090302c0380c420120443d0301c48080c000c1d4503000d650003030009450007215801041041d072100c6034071400a8094181e8680f41c01d5446040c162a000c11142c40c1c1d400280d812020345d00c03041c214018006140300501d44a0700c0704000b01070031403001034144180000a00e500800d141e05200c0104113050000500c180d2515007001a102d210304201600803909200c902403059156100f00c9200724112034a02800d5100c801c0c4003403000032102c16407429072044048034008107809445103c0500314990055580302d003000101800c203000d4100d868040d00e8107119010002d10f215040c2e640c855000e4030243c22a03907440c203250b5440406688081300e10b40d210042011525415002544 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 568736285 1250 568735035 568735039
    0x519030b0607021201290306090c09192703180302090106120209031c1803020904030503090c190f051f0507020604350a0f0212150c03010501090e0f042915 68
    0x2030ba9589c900803a01c801c03185440c0781c2d001001c03600280580340c3c14030f00ea0740d8004405200040742e001c020304580d0303000350412600c80105011082407080541c09400100120041c4001c0b9036580e280d0360114024010600511060041400c14038000824982c1500c1714605c00400b00d501d088842881c00107505480316442000502164041000000102d4000c003201d03405020003807503503203030345003200d20350405041e040ca54040c1184400d00360707840ca01c10608003207066218040d130030710b00b00720754130140344c00d5000758011100d4000c025510b0100c0c3d040302801601600b8517540d6903250f880043e00c548996040059034202c0c200c8400d00c802100d240000d410420f041990321240110805141e480b240380c00018800c3c0031080c9010f006090240c12880e044109404890340c86a070710070402007059013242ca16a104501100402041d0b07400480507000b084a06009642410964000061179900901c06808850000f1003295602182c91103190000b862f201104c20504028508030440b0702860b500c14 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 568737535 1250 568736285 568736293
    0xe150109060f03080a0507080d05040c09180203100b060f0301030516060e030d03110c070b0909160f050a12060801020c1b030705130603020406060519030b06070212012903 75
    0x4256840c1041002c000d5a03000004e10341032070500718085441e54050b020448140c0c00c144994665509a401007030b00070303032080040840c0e050809500d4402ca808209400300d020000d90303250740158401241d04100c40d140407402103250740305400440c0a81c46500042c101800c4000000010320002090886080a544548003200fa070340700340c11200d03c02e8542c404c0b54590030201100c2e5440740250300440e038403132010040506140d01c2c0d98140c0c1c14000b1a0b803107040540c1c000144000c1c513140c4032602d251b0003211082920b40c2c2c00d02800008142c810314980f031074140b10001520070031048c00780310b1600160803c00414010380c0c2d180c000c028044d40002d842c5000d1840b81400c8031265a40c074060b001c4001c01c02600a1a0f502d00d803104007c002c51305240c60303603800d0b5501c90020000d84c90300c1c0100d0000d0140c680340c6aa031200d41d41e4803011411254903490081520704250014240d99100881e585140c0454511103640c104420a50050240713000240000404200040160030014034600c943c2c0c02c114103071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 568738785 1250 568737535 568737539
    0xd0509120111070317062218050d0906090e0903040312110319020d02060912090f030102070803010518090a0f14010c0807030c020f19081606050105090603011b0e040e15010906 77
    0x100405668901d1004801e00b10760100181c1d690f1954410002106086048d0704280000e84a480c02c003060070320694001503081c08144803a6400c40c24082c02410011240011440e2a00030240c59000d0b501008007141900d421031030384540300d40d13400814181c088040e695601c2011511051029119040c02e001d4041c030015552003900110f0b1a80c4103100c607002030301901814610042450303116669070ad034060b0b2059a4009151001d1000d01080c6100782482035413541804200b1030b9080049001464905045c0f0400440c003e020650982c002da01290040c4142042d00d0300d9080544039035004044c540c6003040c2c40c1950381d480094940113070305c9618100203581d000b5504907260190344112280c194803800c10719206085103401004018010407130681000200c901d50b03071003014500e10075514030342c4603401401a40740446056810000c00c8000300182100b200002102501416908060103410303011282c030781c0c9854204400911058050380c00d00d08900c0420f040e030a00a0059444036072420b200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 568740035 1250 568738785 568738789
    0xd030c03050403021507020a060e2107080904050408040b030702011b020c090f0a140f04060b1e04091e05030711010207060801030f08090a0b0d0c020d050912011107031706 75
    0x951809550107134090302010f5001a1040805000600408118820a130000d00410780d588210b01c003010000e0050030181d88981510400384041c3c80d414280103800304035510000b40c14500b210043c0b002903130086010741c1c0b581801500fa02907a400541752140000070005070b941d042d0b00416942ca49410400e4000c0e1112900301e03501c040d11000203407c20003950114903400f44050f100d0b81c0c4117004400c0411072034141902003d0501c8150340000030034016005001c1081082d01646030118800c3c0d400c9080c002d015103043c0301b20340d501c66801d8000c075076031796040d0b051180072407210380c03003e03040380301d812801e901454419902d500030a000d40d0a0310325014068855840032500408881c0c1540d20304100d40d08688556500e03540f1108102c90b0442d0401180761280c841303185c000d0042c03074400c0c2c3e815240d0302d049949006464910f2540011500164100e0703107055040400e4801c0e514054400c00002d107075401e0b00600501400b0046032032141f0200c1c01c901015440f10540714081034540500b0216203030842 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 568741285 1250 568740035 568740041
    0x80403031a060405040f0b0d05060f0603160e10050a060c0b0c04082a1c05061006091503020d050f06120105010501050a03230a15050a081b06070c080d030c03 69
    0x81480c2d0100d42000100124607041c0c101c0c4058100c8441c0001d43e20104a0001da00070a503401d00302c85a0f08020308100c05500c49034851544540d0a602500c0601407500d0030303103102c12132801820159148903011502c2804151104005040302522550360305071100343c0a414810640400c031005420b03800040d900c5a0360001742c5044403c1c0900602441068014642c02003501101c9194400000e08032003250740e403100341d481c007441000d555090546c24241003460400700001c0048500c0f8503a40002c00180d60300010140c1103070300d190fa02c088150000c0c902140a48a00440c840805080c2400c1c8049030036200c1c0018001c2c2030490f020b19000700784510150a03501b0911405002c120144082610355010707800100f0007220340603190400c0c0c400d2059540400c0e0041e10202c016035600c2010b04041e03140e00141901074001154017a45c0300740307001c04003a51445d01c0300c440ca5400340322082a0105441d4481511015640035082c031801d030742c45a072803554030401c1c01060000030341440d10010f0740c00e000784 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 568742535 1250 568741285 568741331
    0x10204140307080c0922111305060a0510031d070510080c30130311010908040b0c071203121404020d02040903120c0309020a05030f2e0c08040303 64
    0x40042d06881c190942041100280100340d0025406c280c90f0b082070f0350440c40740f807000c4a40315107002e8080d10780040920044051041140c0e410390b1074007040c0403180d0784014a007411510116940d074030b8084c41b00800c0303014012503800c5001d2480d2a10070603c84040124120041c0c51042e500a41d04504d40c103400c4544410070788482c450f50404001c900010300215940800d46000e80e00100d4280e4a903040e15010082c08030341400880212045517000c041d40b0500d044030000034030b4000c0c0001d0701240c81d0316505100d14491200607400006914001207010b20601d80100355450220b0760041040c14050480c400741c407402900c4c3d907c0d101d510346112011240c0e0a005540203441174100780ca1030b40c2400000c00407040103900b8840c60701122240c8085030301a0640d21680e5940100741000d40348148208074025400281c8240c0144100c8000340c0400500d46440000c441444220140c0d443d04090000d01e40c110100c0f085400c1040d1424003d0304400a1402903120340d03400c009008200c4a1218010412 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 568743785 1250 568742535 568742549
    0x4110402120708040812041a010902090f010507051005010e090f190602090409020901060309021302070308130c0302090705180f0310020d0605040501030c0608090303040804060f020c030d02010204140307 89
    0x1c0030229100c0741c070503011140d2180c8a8025180703004500d4a000d050503008480807205441c1d0000c8100b40001680c00700750040c07e03290380c150f003440c1c01340c1c0020b80c1a51038a41464100580498000203100d810040e044603080c1c0000b0801407075031030304911030b5000e0041781c00700800c1c46240410020845e00080c1942c95200c03003032040f4a41016aa6000003950080700a1039100c1c0c1c03106490780243c0d0302c810150307008010641300014203091500c10300600300800d104a11050f441840820301094110442650207401e55004540e440c02c0c1e86011010102c003904003a4020b0720030401c12100301d070060000d01214039901962034450380e80404000440811141040c1c05800c0616142c80000c01500038000880c07400801240054076040454100d0340241e000755846101d0300801c102054018002c80d80040845010718a10310703003a00e400c5100e05c5540b00341002c000e0305030303141c0c01c07140c3c03003030010501496006007551048044c0c40740082c083d4000340100709a08064592802041c5030000741a0111419 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 568745035 1250 568743785 568743817
    0x120307030f0f11070b030a150e0105060705070306060311041b140309030c0a11010807090f1809021c11030f070311031c02071503090803131704090504110402 69
    0x2003180d00300d03400c07080860302c8028441032000c0d005210201348000e00c090050400314944a15040d207005083e036481c0500ca01c07101c0d03030b000f03810300c0003100140310641502c00075103501c0d41e595190300c1e105140881a50025000e01e2801401000300410b0502d050b28900b012181030008150140741a003442c4100d05405000c6000c88840400c0c1d1024400a10b6108a01d0410382e4184042402241c0c01e107d020700080301c40d050440b5503101c03039603002080f0540010040c80e0940b081c03401c1c038070001c031010654090b004c100e060280d10380c06603500741e40165501d00c0e801380414248410f80c000d03480309804880701c02c0310100468039403801203050000d0400c18201d00500180707501440c44d1511107400c0080c207145601402000d4240c0b180c0b82c0c07042248462490168014092030386442044000b9458600400c41003504043c400c1c1d010525441c1030b03d070402128540300320010320928205030500510040040f0300b5102003000604240c0c035612041c070490080c94040001032000d400c0004a104040ca040f8800c64 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 568746285 1250 568745035 568745057
    0x40b030a12120e1f14011208040b0a18050102030f0d0f06030c0314010b0a06171509180601170604030c03140304060f1a060901030b04020910080612030703 68
    0x1d0600ca018810740c5990802d512040d0b4448201c0c400d45400c1d800c2c41d40c0c1c562000012400000d1107401000740c05000030340c108500b01101c55000c0070b81c48184142c0e8030f072841c030361441400e1028242c102c41c0100003502c09581e4805c54042c02070300700ba4800d81c0342040301d400507c0000c1d46500200403038080c0b50100b00414640a94458120b00610341d445010303212581c1c444c000320010b44e1344003504000e50b0040d04207940301303410302c03c1103400c2d141c240c040320b401450005410001c07150030145107049180e600d0b0f02c400d82030b41ea1071012080385081c0040240d00840c110b003400b1008000c4146020404880d41c143c0e941c903070326440c030703860010459081200154030900002c0d0110303101750b1000c501d1612134075041f08449010003009004c0d8100761f802341c4440d40c0e0344403611103200172403061030703071b00504011040084e5103c0400900c103405075410003418991150461000c1c0d550307503070441f40c4501c07004003403031441a030210707000700407010032176040303001d1656880b10401d964000019150125490f942d003c621007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 568747535 1250 568746285 568746293
    0x3150b150c0a2910080a060f0f0606090515030c09060a020a12020102090a06020d0c0b0a110c0706030b090910020f07050d020604050607090e150a03050303090c0f040b030a 75
    0x1d03000c040c042070703140a8000100001001d06010a07044040d44603d804014150700c0440c140040207486007008101c0043e08114881010800742036a5070003160000e5030083c0448550050310b22541074807a11840c0142c04900c42c1d80003081031041e114107861201c1c0c200e4079515044000d2200762148040c0e180b00780544100d40c0307020030080c2000302551050f103c4070403060f515110700c000803103082e5015075000b142c84072890821800207001840baa02c0180b01c021101c0c18007400149d841c400103007180b0030a000085005955801c80c9501d802600711a603078607240300d09540d4940c6494019000000c2c01c1030300000036890048411030195154101510300302ca070414401c0f00035030180b070072581d200d1380500c8140041101404101004950758000e4107080c6020b203800f604082c00108040c0601c0030303001c02130114100103509030350301c44c07444007011300001c0010b400249200c0032a40014010300c00001000664500481c00921405040e622903010562400412081e104080c600342e405600c00000b0314041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 568748785 1250 568747535 568747537
    0x241b0403080d0e100623090a0509010e0f01050a0b060a1710030c030b070908060c0a0311070c0305031903060501120504150e0d111b102703150b15 64
    0x10340d801010020306036203c10b4016080030b901101c0e007100c03599141c40801c0203c5951803210700051291050b114040c0309032001490410000c0c0c51150083d07503910001d0441c010941c4854945290f04048915016840708900d02808088580b078016608284100c50b139400d00c0c8058520108480c2c403945590810f200441e4005400245140c0c440c8414001c0040860081640d203c0914003510200c03200785800c0700c0107480400b00d6842483c0c2a03200004000c10040c548041c4c2d85010b40904d40443e400340c2119030040c0034001e40c00d000d001e2210350318000042003000401800d0f002c0200c4580c40d111022208140d003210030500c41d250100d13205855a001456860380a03d900602c9400c00550310740421406000f110000f0390b1685c440e0303200c401850000354001d0500c42a450720040182000311a00700c5030040520b20030300a50042020000c004240da00810b070341c403000200072420381b01c05032000c40190000352a80c401591224404110031100c0c4007203004950346410050100b0001156032246e003010703 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 568750035 1250 568748785 568748797
    0x30f0c03180f090507090302060912010b04110415050c150a18060f1d0307060c020a0501020d0c0e09071d0f0a080c04110c0c1011241b040308 62
    0x40000e1041e8011100004000100180002030b500040440c00c01c0c99807001c50700090482002c0c0f0182c2401000140c4d1600e084565225060300d0303003c1c0c0014842d0300c01c0d014000d0214039a5200b070030b1803980c0d020038070401d01410031a640070400c11045016050107441c1403056840200e041d8004800d5038543c50407403280243c026818010000d503907200c4191003884034441c801e088442e141c94165665040c8280d0149140d1a2a00401240d202524144607a913a10542d1002891390b5190000300f81d401e4020b000d0b4045094000f8005d65840c0300c0c41c40018014481c0d0616079020801000040c20340f41000d1a02901c5000d445d22101d441050340c0c1c40c441d40354803114910300d1b485018414800010307140c9004410007041a40000c118200140702040180c4070f446100c0359402031b00340070303c3c04101c400180d000240c5005036995415041122004c886a9001001c08203191003a441c60200100c02e00c10100c070040000542c42a441c0ca505541004c00c103810101600004001e00080c00400d000b0300007045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 568751285 1250 568750035 568750037
    0xe0906011b030315050109060203070b040804050a030c05031005160e0f030706090e160c1104061703030f2419170f0f0607050d0216021c1e030f0c03 65
    0x80c41a03680c0c011050011240450001e80c580c0c24001301d00041d15011406000242456003c1d5410312800a40c4da0090040c0a0108043d4402144c2440254002c460103070801808c400c00c400e07168188151034000c20701c1580d010740700d034001001c0c5074007041c0b1a40340605941500100d52946940080715401750020315075a004043d410803e040c2d680c108400390040c607040d10707801c0d1201c0c44e005220052003001030030390961010440c01071040741d5008086500d95070340400c02c582e2501420b00810014881600081e0921031010740296183d41c00002440c030800c2d001000c550180d03209165010844c0c824981c24180c400e26141d4401285084103255003184018041041c540e035071550360041c81c0e10100d21000050304074401215074850244220445480144001c26282c01c102c04010540e210b4802c0580019602140982500e00c1c0c802400600680003490004002c030f09005008001700b8080c070032500c0c41400d15118040034202e01d107140700075030962600c800c10f003028181039803e9400d40c80214 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 568752535 1250 568751285 568751297
    0x40510090e070c02030106080a0210080907080a0606050306100f06030f02070b040c08190b0f04020d0609110f090103080f0708210402101d222a0c030e090601 69
    0x1045801000c66401c2c460116562128140401c60041c5401c41d580c6802c0802540c07c50102c01c03015864803247d10b254800a460310f80310701e03600c400700b9500300304081c0c100000380e008006040c3c0c24803c041d0400d4069540171800e4803007603220342d206c070480d010040c81401c00c00302c086101045454000d034040540728904400141c5000307a16900c2d07a4028400321811038400e1202c030418450f980d02081300c0f2030000d100f08121030749005592500704d80c511700107008450f400104800601191580f00f082c1c501203034005400c1c0315000c0503182c80c581d40130f00e00320068043e25a03000c01010134940b07203419504030f90700001000e02d040d2111440c00c0d400c0d40018010343c0c00400401c8440b5600700d2016005980c05038210800b1885e040910401181c0e003250303450403003040029881d014409400070446400c509007110b0906040c2e40300700c5445850400380300918102c1d0700d00340120369130103030041c03c080d00780009810340441013408060590302c145c450000540050308941d15294079050944034a038221300141040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 568753785 1250 568752535 568752539
    0x60a0306170f07080a1e14030d1407020a260906030c120f04110d06290310140403080a020d0501030503130807060f03090615120302060106020c0604051009 68
    0x355844481922034140340e102c4410054440c1c801c1c880200980a0703030000d03220140298032150410b0411040fa200c008505a10310302c100000001419038000d15041665180c00442d82000002c00a0841072080f0440807000140007a20102ea50f0550980c0884c41e594504192444504084803440c41070b01d6a540800140c44903642d400e0285100f10a09046980da91035070b00300e00b820454015020700c0090042805000009107000b0540312003c4080c4c0e611000ca21160a01802030f240a14001805c2920303003c00001d0740270798108045545c507054080b240a03410748506101140c6d446180d400418540101240020303110ba500035400c4005240d015042c14802620903080b40d000b07a004a130f81c3d5000140c00321112030440e180000402054000d008001d00e00ba201910b14421441030008040d6202001802c00c079080c3c0c003042000f182c1390700c0c0314107407500d881142d044074a444500794013621990000007034283c03000032003030964040581450f0806103030009210b04050103000940c107008880c440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 568755035 1250 568753785 568753799
    0x306251809060f2102060414030a060203070c03170103030f0c03020a12030f150b0d09020301020c060405210306010519030f0f05061306140f0114040e070909090c05060a0306 76
    0x1884064081040594012031518801d480d03044c400302c8800b140c1c0c600200001025a1380c400c165003c43c0c840720003016110941c040000d080400000c0c00525052022007401030b11030340b0419070311005103e92a01010b00032580c01480d9100024400140040c40481c806e00a0358440c1300c160000754460300407100f4084682d502d141a240801d55a407000075076459000480c3c3c0e43c24011a0032505016001c107486904040744046242704002070540b0003074540700c3c4003085407025411a20181800c0707081e1011811b2501c0e00c10788441e8403010b81c0c02607106080415540c8a4420103d0703020f220141c507442d1a08011520ba4082c6104c07500c0b405c020f05507030b001500e0506119010b45000c46c41e00f120300041c14a0108100042c3c05541c120703402c80545400800d0040003040151903980010440700340d440e82c0c01840c0125a170108403000d0300050100231070000340382c0e02040c000c6406003025846100b0019121410441280ca8410340a442c0e00300080040005042c503c00410328240d01d441e001c03a4058650130 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 568756285 1250 568755035 568755041
    0x1140a020d080601110c0114040308030a020a110f0a11062104021207050117040f020310050402010e1c0210020c04060602160801050708040809010207031e020306251809 74
    0x91040268204610198000341e0000b02550f20580900745035000380740a591309079592190100f440e060003540700154000100e40001e4030025644000c070190f6a181003203020000e50008411280428100607000000030000300c1c014440c5078401c1d00070910718040d62204064501c104102d80c0e00305104000e103070003600c0c2003992040b825440e900035a41a0406106218404900402420f41604413038814030840c0c3c2c1c00071010309406100c1b141101c490701d4909010b940c9001c0c04a00a501d03100740041450491296000144164000d0300c0f00241c0003003020034008003004030a141c80b00ba1070030840200041c90481100070f2011180d204403004a100c850100d4220f6406803c110b0160307001c2005c0c42c11814051810034003412080e4024441801c11441c050101a80a04002c0440c9000308040b002d9901c01c010000003142c1160b494203c03680385001300404a11850302c142d00a004420009040c0340481d41a074090481c1d9170803403c030041c40c240c02200c10803103003201c61600745441c100005441d41a40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 568757535 1250 568756285 568756297
    0xb1b04030b061503100e04050c06040303270608040204022208070f0b0f0a050726032a0313140313060207240503130c082125020114 58
    0xc200071074203050900410101840445018159000400400c011504035990100c21104030040040700f9031a24645141051801400303540c2103a004100001451b500040100180e10f071003840e100d000d18038010121141da0240904400b08032920049401030a00354010400c05c002542500400c01000c0c3e400821250154048412079000c40710901030283e4030b000c41e80042c05c400d04041c0c03a141e0703841d0b9428094041c100d83d103420700001023919018003d41c0002d502c0300c0d404d070042002d00c2c50200124021141c20030740d4a101c0c031030780c81c5504951100c02890b07484000152407019604503512020100c1d4a4649100210303500c1e0700781c0c0c2c0707080bc0d04072042001d405036116424009507694185400245012440d40c0800c1022903200f00710f814a425841800c0400e280c40c2c50b1050340c1e5078900c54494403d40d10010010004111001c0000760000301003500e40050513441040705541c07d0060403055280034103c0c1d210781d440640d000303241c40d20102c0e440c00c1d44c8862042c10000e5880036900b017009400d82041d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 568758785 1250 568757535 568757543
    0x7080606030c0103140606030c0d0c020d1e1d19030b072c090a0b03030703020109060c0306060806090a1d06010602010606050301060c14070504021c0c050304020d0b1b0403 75
    0x600034442203190074014450482800c1c64100440c2c58080a49401030360040d00050083c00000007144e04400c09034100e42200703000322000d1000880c0b80710029591044010742c07000082032220300d0f0285014030040c26520012079600c480a0840c00d0214111168000e0310301e551000581e04101804000c90a03103100844c019452041285003036a8060310401c081413401194004100700290b880c03246100b14900d440044d180d21420342d0ba4460340000500000301d01c1a032520021550000b01941500b1201206205031418414a0303220481502600c07005e004502c0416090800124a4280068000d0f4800804280071407405402c0c0d859100070403507207072905c1050b04050018821a5024010700e0014110352821a145625100700180440c00701c41c0014440c007080c07186107440000400041001c0e2100601c219503804650390644003e54034440904801414080c0e1216814064025039100301d4020304814900390035551004002d0000034650121000040855111010a980540003452003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 568760035 1250 568758785 568758793
    0xb04090606031a0c070b0a02131806061d01110a0b0c120f0c090105090f0303040b0c0705030f0c061c1a031c091202010210020c1c020d0f0e120708 64
    0x2c504104000351036034101510806111414440f0001c0c0d40c0c801c44003040d070484014445070b10740b10f882201911940d08403415040c0891408510803210125128021501450800034540c1e600d1054503c40300c1d100780340d000d2490b090a41ca43c40c4d40510116001d401450007590b401ca00c0c03503640c074200e16000361000e00c56007201040c0b584080c2d1301fa000c0c950704034201d800c00081c0d6290072a41010180708000310b10f4100b080101d850501c6448907000107015440040580e6280c54481403844e071240c1000201000c0751040800000301403c01042c104800c402c004040c01c4100c285c5010300c089a4404000380407040a000c440801180e1244204000e40482c0d03c085588510b4074800c0510b0010550b200c850100c1045e0b011601c0d95410030011011035002c1111005024070030300041c4c1c10207048550070091a4000075603481c1c46000030800741c82d01000707009100c81208103030200f2070b580e915200120300894003000c4c0c0120320fa4001c2b0380c00c0d800704070024074486080031007035041410042c8035030150240e90b00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 568761285 1250 568760035 568760039
    0x18011203090909020a230a0308030a06061706010302030c040905011202120c010c020f12150403091505030a152c150a03020405060d0f0b101a0d0f0b04090606 69
    0x141c485030401c000e1542c0c9105201401c46030f0001420030050b80f24040081c490410010400c80c070740c01c020b0316204002400000850ba83e41031000e601e5008840884103145048008560f007806840003400f5044220001d43e010b0b52282d00541c0258409440100e03090320620001650007603600602d40030b4220301c0d0801c0c42c0d1303007107510500402c802e00d440601c00ca07030484c1400c2d40c0c0d5a40d024424008041d0103e0348443c0c1d64078140041358080003200c80c800401e02441d03400f1500300d0100c5807807c1c0140d22a40d1002ca0466496181d084080f01c100c0143d000a142000031401c019407680001c1c9140f060710741000d00c400d5540402407440000550044000242071b088250440d40c01200789500501148c0c9000340e87c8401d00010b04901050b010003480742360340f803010843c2626440c0880c50000c1e80602c401a00c81d41c0780c02c3c12031250404440d0030680c5608044003040c000d80f40e0b04800310185295030100d041c6150700701000c01500d00947c00007621603551150205558403402441c624600400001829034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 568762535 1250 568761285 568761287
    0x19080304060215010b0a0c02060c01060f031103070b0706020706180501050a05070e061e0f03040825080313050a0c1d0105100804120507060603140f0d0f0c0218011203 73
    0x8120f801d40207850042003c01003002907007107400c440e20264685071505000441d4030004103107006800c00d032000e9602c0c00b180401c0911070840003005403030003003000c1e2442e180c01a0030183d4400742030040004014041c00914000340290300034010580c451140410308083c00c41009414518024003501c2a070745680c140950715525100352038000a042c580040001d1400d000b00b051441560102c95509065100d10b8011615500c20349409000541920707a403401c181c1407200c02d941050000040301102c2e88951154100100100411150b000b5285070440d981c150485200340e50b0f00350306942d54084d410031800010421038040002d010041610a2012440800c10b820004140c10040c0101d0301140562051134015032010352145d0702034103550364601c0e0604101d6035801250802440117040100c04030401c030403d010070f13620f8100ca2040b500600c007199150703696601a00040d00100c1c8440d4140d170120340c454001003281c00c0c00030b0070000203541001c01d55101440243c1c000914241d141a56034205 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 568763785 1250 568762535 568762543
    0xf1407030605150d060e0709060f090513050408070212010c021e0a0b0903160b040b130c0b09011b0f0b0709030507090203070c05010f0507080a020a0806040902190803040602 76
    0x104949810040241484082402818080074903c054000440d68821604442c2c10060103002c1e03080004a1a08100002806411241c010303c0e002c030350340f2081e908a05100700407160454200810341d4000b00d0408041e04000d2a0181c0243c4422208004000168440031411020781400c0750000803a180d14150090900792003c110b201070801d0b02c00400d4641800040f0100c80b240c00a100b01c509896840c2c1c0e0601d144107008240030070f400710b40142400c0c0000e0310416446240a40b50545440e5101060017080c050007031801040c0000d120400c0c0b01c1240150003038a20100d040c18541e8100030014800e8400b50b16840049441e44501551039040000c81c209950b003007151407c1200580c1c0c1155202522034070b8a000c0c081d243c83d40440010360f81803291002841176070300704000700103682d8002c4038a00502411200200498000c10100300121110300c2101c0141100707035601141600c81c4001c020140c480da0f407040c1d90140927151160f80880d07244d01d0301c4d802442c406c0011603446190040203810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 568765035 1250 568763785 568763791
    0x3041a011202180a2307021c2102090a0b04080f0102280c02041d21090f0a081c140306100e03010e0d0f030e0102030606070308090c040f14 61
    0x103403142440788000586803424080702c01040e042c02c020559481024010080403102c51004800c1c01d501c81c90095880d052481e10700400c10f0f5420340b00410b281c4594640d4107550f00000d000024032801036440412240c0407201b690344003084004d4541000c110005107a14000d130003800402d0b030001010083e0400401c400400d090401c0025800c140c0746080400211005050a500180d41c080003020014480c0c0c0b031031403400c0d50080c41000140c1c181c109804582d014109040325900c51110007020400078261181d601508100c041460032550300300344941214072203022038100c4121680860386e40700500c9007001480500402016018580400400803000298100440c402c01c01c00c4c05403584418001c400102d0712410044003018000c408240105181042c4880c00d00954180400543d440484054248400e03035040c00144179882c455800c0744000d81d2020b9000300308120680010380030780411b40d44807420740e09540c0d10070700c1c000205058900c440b4081d01516a5160300290105860b140d07550 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 568766285 1250 568765035 568765049
    0x60c0718061202091503010903080604150e070f020a050a0503070215030408030117251518060e010507080708070c080a0512030c1b031e0316030207030e03010203041a01 74
    0x1051401d500a51103092100002c0d0213922143c0005641c00b0720b000c0b19104401d0041d0007040070701101c1c100200750030340c10380d2102d200b82c0c2458440c0402000b20350a40f0b06503420440c0c0303440f054980010649040c40016924029070040a02403c046103041c0b12620710a4092806550340702c681d1320400c41000848942c9000d4110180148408520135406480c155020103514901d00c04456250354a005400d40111070311a40c01002c880d05140700c40b0100040369002d11410705050300c03004081d00c10741940e080b086081180000104055441003045020401040c10510301d80821629101c680b40d018002c03d5402c100002400c004000d4000c00c040c0042203140050b0008049035a62030740c82d042e00340d034103103008100440400d005905190854540843d449420418000403103084d9880f90402040c540791890058030400300c10500800f240d00c20000302c0c95000b0b0710800300405800940000c10309030100721300c52101070f2107501c09100450181e8010035030f0030000310b805880328103900416000701d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 568767535 1250 568766285 568766291
    0x1812030908190605070c0822060e090f040809060724020c1f060b0403030309020f04020307021507172a040f06120f09080a0801050d0c060c11060c0718 66
    0x59141000b034420014550000020400340c80d42c0004540345c10801c80054a08140017407c400d000c6c02d100310042040400a81c2c2c5000c55607294425600c3d00555010305800c442001c000810801800c24220392003445440d10500b46070051011540f241c11001085610b001801d840c0324000402d0031040400c00c2806405500e40450b03581c1c1c00b40c4404000005440740d9070305c01150549044150403000141041c0030f01c0300e0300c8540d80e08004000c2c18140320213034040d0303174a032060740c110341800d0088911844680d0024490164240202124281d0081ca1402040124802c90b840030400c181c06a00404150f5036115900c1b06000b82d140e9a1090061112004002000100690304e40032142804075450350908a10900071004c40901419040c1114204940b070490780e1000c00a650f40034159240c01c0340d448050a07a00c4d4401e10000e1b01d0048805008554040c008101640c8540c1000b2036841c4070300f080d4107a440c1c090021549039001031b40c42c00c0441d040700100384080c0c1e2050410000c0c001c42c0b95824 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 568768785 1250 568767535 568767553
    0x605040b3103030c02010e100225170307021603031d010314061509030d08100e010602150a0e01050c04090c0201110d0b010203070b010b0712020f0d0f1812030908 71
    0x1908525001c844001c051540300c00c520f0044034001c0d404001c0f201d40107000d45410803902d000510080d40494001c420156010302c0c01c00d411424204508203066000d41074417500364503a858010540c200921200c218482d0b40c405d844a40400701a8034002e512a403250055007048031007144402c03101a1400b410913103000c0071068060390811851342c0100096072050503401c036207001c002991244640c0a50103209000e200c1c90489e0b40180724502c100000010b14080a48550400340b101e0130030f21914005a11555200da40c01e551034541641040c480031001a96006025195007510012211440c00c8000420b0400c008110fa001d000210750042c8005c0120001c0f900e001483c500490039507068580e96907060080ca80d000700201c1d401643c1168458490f50380d03c60384c5907aa030303100c03600c22a60000007015441406000046d0036412007059009480d03020b41020040761a0401d14001c2d500708140f402030b2125064206403100d01030b0900410007800442d180c00c016042d81100e42c00404030b03038410203123 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 568770035 1250 568768785 568768861
    0x1080f09070e220b01050312120406020a030b19050111030408072610021e0a0203030f1504060806040b0105150345151003020d0204090605040b 63
    0x1d2425180c149045061a0720740a4008028201600e600320f0507021000340c810a210101407154121402142294003c100c0d000004c0020b003d004051545082c1c0000800d00003901038000d03041c2051140390009110b060302c00000c0c02050f50b0b045c054041050391300c06001d556401091040340070408801103107090700d000d01c500d0b0b4413182c610850458184118108044058490060980f003601c003007150402409040c3c1e0000951186929004045100070405a6152071100b40e805400c029000345003182d0303034900c184030030580080200c605180101c0729059280c0e500d208100c060300c4400000c14191425242825000806800051240000381408140790007a041101d50110040403036104c0c940741d000c07210344281c00000c0c101c4020414400c2c480b046c040c10001048a01d542e140c1180d000040900380201c58040540d59445410140d160034005400c2408829071810320107440080c028a03161500ca00700c4030250790031501a00d22100307016015900c2c40c0080d1070641080b00072911050304090b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 568771285 1250 568770035 568770043
    0x309050a080a140c060a020d090503070b12060d020306070e12010e030913020405030106030f150606021b150406090807060206060306181914010f06050604032d060b01080f09 76
    0xc020f00340e0a00c0400c83c00c4412040c40110550040030309006c0d220344000401946560341c02004000050112000050600e40000c0782e0044a41e03440e4010b103000240c404d41d4070850001800c05412070040303003951005031000c000c2d003031041d0040c0c1c2d645001d0504d080100096000200709004550381050755026404002204446842074120340409902d203846002a000e40925446241c0c55440c2c10400070034441c4501d01c5941d0309205090503410b8540301c0071a00c0480b010707402410010b9100241c07801000b090076030b09404000c0018070400c925030303d10402824552040d04000300244402c1e200304010350041203500c02603c028005400989490008030355a08402000c017840d803280420840c034441418030400d1052103225078980b000034000d080000b121003460401c0c0310f803580390881881403042d0b244540c0c1d05484005020034501403440d00c5030140b03d00440c805200c0005220400e038008444202181412845960302003041a507420000d41100c1000f05529900309145081081c104da0110b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 568772535 1250 568771285 568771303
    0x1d06010905010f050f0a151709060a0c17060f01050d060b090a150c03080406091509020a0f030201080a0914030711040c0f12110c030703050408011d03070b13021c0309050a08 76
    0x83c030403074129000349001c035444c800c01c908c5c0c0074090f04c1a0061100d59800400e000744511151403080c44050000e0390304443c03240c83c820030320500251300804141d0b589800c0000d0100303200149485c905100101d084441258907960211f000c50704006420703009820608850401403407002c403110761076040c0e20f1010b40a4811018010b08010001000908001712a80030403140c0d03412003002d00c02c1e4440256440c0040c10245400c0e4030840d501600000e090030b01403003200c2a00c1e41079507031581a854440c4014090700401e01c0c200c45e113120035a6100700e000c0041014010050003404000070800c00a018003003107681e4161542c00b0042c8203880f003000c550f0040b801c109084000040011141c0a800c500e449070300800444404a010000c0c2d40018140d2000c0a841568181c4000b001100c65440600245044285004881e608207000b54004140741500c1c560b405104600899080f100560014180700e080115003061410000109000e2517800009030020f0402622000000e80c1003120315070f6124051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 568773785 1250 568772535 568772549
    0x170f0c041206061203020c150901020c0f030102071a010303080a0606080103110307030804090204080708010e062d0a090312091122020408060702210403061d06010905010f050f0a 78
    0x21080c03402000328683c8004000c01c001815501c2a58940c0b8000f5181c504000440340302c1e81d20009040000b0222400b11505407030f050300208070b910702c10f40070701100d0701e115000c0307580c103540c28041d040201d0818803000340c0180030100b46030b4140d0b04602e80070700543c2014001007812407a000040c001d494101303800300e040d01e03002100006500d00040001e40350a0307813600006c0c40c068000c40c8c00a48450b07580c02030030546101c00d00383d646180e150b1804600f00d5841c04519549640007101017250700d8103242051000d511064041c6203030307219a070822400080c0c180c42d0740640076980c1c0d1000c1c0c20701d0382c040c0c00c005841e100d42c40c017440740003841d40303680340b46211a421803841000802180243c80039107840300703081003004890554035180c0d1400d1031a03e4100c2240c040015014035200c070080820b0300b50340e4a0040040c82440c0d8140360070350721081c2c0100301c50a410000703201d42c8030120000110410800e03009104c50700022440358101140a0710f111b005501850150700f0000000c40e0a9880318400001c1c0c543e1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 568775035 1250 568773785 568773809
    0x2180118091e0203010207140606100e031b130501150e011b0311031e0c06011d0a09080405031f06050109080a2d05010e0106051807030b01050f0a170f0c04 68
    0x1400013900a1045007001015605144115000440f0116100b80326280440781c00b5547e12020714256070591800c44a65855004041790001c60f03090b201b030b030344e11010020302101c000201041c2d0960480d2003c1c0c10000007200b90501a516169000020700d0b00752000b8030300040170408a41c0c599203810710401000301071001e0024402c49031030080041e240d03078850750400760540001d0740301d11680507800b0b144a4455402100700114000800d2040503540801d02c03413a403003055607000f29100c000d00c0d044c0d00489042c8010400007a581ea030401005101c194820062200e100c01d0844c11000ca0b941a0301890621644040030021800007080b6244002d0700074051101d9a40910b041310b40c03440c903002c1034464030b590103104401400415441806603101c5030000304038098452041000711428003e401141c01400d40018a805200382c012010144060508034141011380c5455011508580c2c0c85100052070515a281414580c81896030003142d18800c207c5141401c9070301c49124469801040b40c0c0001c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 568776285 1250 568775035 568775093
    0x15070f0201080702030c191a090a1b050d14010507091409180307260f0a3207030305180309090c0c1e0d0207080c19030218011809 57
    0x10085c41240c0c009a01801a140080042003524070070020040702960318204c12249100c0840c3c0e0944418001c02d050b80041c145210a60f44480002940d589208284948494001003075101c80170905000b07031144000d40110150168071600f1183e0040443e0100100d03d0380c00c200124150348015a602402da0f00d40300c00ea03442d0502044a103441c0100070000788000142c200a00a05180e002d4900b17510069428079801c240821a40354002c000107003030803080400088a045000b41e0103521403519401c3c0300c3d42c0001001520810341c11045041080c06100001e4a204141d410b1043c51390003420300999038070105150607526a28010a02d2940c0500c2404010502c1c01290720150b51034110504121280c0c1c0c1c0300005000265024070002c80307081d110314111a00030034008103505081c2e03500b40c4010200900311404100d8603110090078500c3c86c285004010000d0f841b000800f000302800c80c0060203895252101000c3d401c0c0e145440d01c078015240c035030b2950010342600000c0c12203105106200501031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 568777535 1250 568776285 568776287
    0x503040e01090f09120e06090a060e03060901050402031911030d0203130b043f0302241605090103020403060f09031407080a0e01120e210a0801090e0102042315070f02010807 76
    0x4410808e0305980301680907400104264002601880040d0035401c0d00c2d003544900080c01d0a9500c10340d00254107800c010802c1140a0a1801109840d4021401200444202c10100f4181001d07400070000580000441041700c00c91f289902c001404081285490103282200c1c00c0c044842101482e44134480d49070344502c00d4030342114800c40351b280405102030400294640690342c0c24200910141000c500300c0100c2e100000510002e118500030306114011040c0c06500303c80c42e510040792141403550a100c044040741c403a1140c0004525040c0000a510800d07080107070914200d0148220080070812001001034090401d940d0f00401c141007840404850100594840221400d00c088051070281041750106001030380c001021000d620401e40c002001d02560780d0307440b910300301501046011004100d003000a50154400c0000310000508060300c0b941e403003980e101780007143c1d000368000d400b103200c0518000c0c1001d440c55400c0c0d05c0040ca08281642c4003007140c1542c5402a0622075a0000170741c100d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 568778785 1250 568777535 568777537
    0x6050a0519140315240702010e1903061d0610090b061c020d0f05160c020f0312040812090904060f0e070b0714070f030b070c0503040e01090f09120e06 66
    0x80e2052010640f6454494903c40505405425062054824400c0c2400c140032412401046030f00c031284942c6824900d400654501069180030344c2c01c1017201120848000c1101c2940d0041c6228110101d1004e42c1c03401c03414003140d0a080164003540001e03041c02881542811240101c501104e070118420010100045245c0522031044408c84440e1020704241001907000341050381d00501e081020702200c0b14600207c0304101d40704002c1310081046010603a0140b01081102c503c02842015900c0d918400319003041c1003078040d0502008042014440c8007818481c102d8038070100850740d404d18000c440040c2c9082e001500c040d1045175901d243c0d0000d492541c004c81c80c2040032400701c3d01500d0b0345840601a1340e00440050311910b58550300d10300103060108a81d8100c9849c0103417407440d83e0954458040c0808003a010400707110604401e0701c001079090010344000c003659401004658500b050800c2645c1405590681c00741c6441440000548440c1c0c090600c00c0407454403441710300c1c140380802c0c0a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 568780035 1250 568778785 568778807
    0x9050d0501021e0702011b020108151c29040b0a020c250503011a060a032301060201061706090d0503130b010308280c02060d1404030e03010606050a0519 67
    0x1011842ea5010802c1d680040c0043c54118400c0c7ea50038800403034410310019210000400900050348100410307620b0307a1105203c42508070080403441101c1c80c003500c0d61600c0c80e00c500d04942d4500203400d0301c9a6880d500055680604207580c1d1803440b4a4186d645000c400001045e28001c0c40d40400c0ea4800c000341001b0701069641002e82c1c0b40c06d0354900002e4240100503910820307110703609004c9035142a07030b40040308000039040504000d0130281061001c1e405010f01351809805820101c65a024215004040500920340d40d00000768481c1019804554030075009911410340c0e020f5010f0100c0f040300095010710080131450519100c5e01d075548031010064515801609030603440001205004045004120560070800840041e0440c06034041c6a15010041c28000c0349a04c1081400f42c100a001441360695003080000c03801e0b07444001002ca6001a1030580001e40040039020640c01c09200e01006403510341401400c050b40d1010003441c030b12602114500301c4602041d9241440d01510420070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 568781285 1250 568780035 568780057
    0x14120d052508040c090c09030807030225050405150f0907120606030e190c0306050a0b0d080c0115140d020402071208160807050403020405190c020109150b0109050d050102 75
    0x500308075140000b415414165000d031a100c000001c00103804d00c65121303000e0145210785503035031a0751454940700000e070405d6400b502503026401030354100005103400003094648038500350864500307000a120854000404843e0050082c200d4141983e880c07007815004640120ba03040002d07612008122480900702000c48640d50821802095454054000c108080040d9044034107203c0040e05050b025148440b0140440c2002c82046c07012400c507400c01c590141c103d038004100c144105001c9014440c24610030f84451102103458002200203008a603a4540e00042d080f6146061205c01c400303145440c29031512890700c450030f00c401c5445940540b05091b03001003c000a10318070f50400740c0039440407104000840703128989181440e0081d03484078002d0000d59100c034100347c11542880028407001e008210f41c1c0c20407080e2400000c065010f900400030310f581c000b042400341450040e000c890320710141024a4144100c1040990b8400800c0003168021103104850f501c441c10414028400d00d01d44007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 568782535 1250 568781285 568781341
    0x1612090306020a02010921050a110f0316050c240c012301030312020c0c0409062406030b0f1f050d1103180c090c090613030f14120d05 59
    0x40f1140c06600c9074281500800811420a00d18200c080c202450030030000d0101d01d003400b03000309040c400c000c0c1084160325481122058031f00104d01a00d5a0440407140c401c2103114140001000f4084c02500c040000680d00d04010800e6004a10840180450b00103c11240884c9000c00d81c0c209400000d1014064401c0b0046140701c03040c41a1451070900069010817501c62100c0c3da0b00d40544201c0d4040700160001c0c141200c81d00040102400700050103449090b12003031041002c180f12000030700842c54000c1401c410910305180034003a070314001c002c50b120320542440e034015501c60820304407984520b0b00c0440d08074452644182d809004408000c0340452400c3d0f414520784035858015030240c244000060000d180d400d07071007a502d20304c101d601c035000345090f4041000380c12040050504c031a402003180e4140017040010041100741d40d44103462010320160b050080c00500759800c05051440c4003d4031101c01ea15008841603c110b04a01c240c090792240003a5008213211509101c0401e80c1041e5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 568783785 1250 568782535 568782547
    0x915091603050a02121b0d0c2312151501110304080102040e10050d020f061908011a0309061f030213020912010b031e120a021f02161209030602 63
    0xc181d44482c5208124061030034080d621012034000100c0102e11606d0005013005004220288500404034102c1111907441103000850800540480365084850850318068050790960030802c040040e0b0007522140d4001103c00349480642d1884554000103880011200d0074118004031142041c0141e040303801c0c0008180402d400a064008100702c4800c056014102d0711109800b071122980380c890305a000300710f440100010b081c13038074500da00000010140c03402c04110300b4403040c164401d811a000022104401801b40303c0e00310b10101c2113048001e00380c0303081d03140c4141c83e01e58458006c1c11101540c10780343d01d0041803002900454015590140080c46004510200f810180d0008003209120b49a0040101001e103014440c0c401c490500070014001110414503115014807945180c03612401100c50303120510701d01c0350042c82040107941c02808c00c0c0c03c0302816070310b418010700c45228955004100421469500600c2015200d0b0004c81d006190860103900b6100120103a100400150003c100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 568785035 1250 568783785 568783793
    0x12a030b12012d051014010c08210a02030c03220203120d051b0912100905150106050405010c1104180309050307090912030203060d1502040303030e03030915091603 72
    0x35041e007106040540140583c0303018a541c01d54000700d030282d40e1004101010011030148040580301c408060607d500c5000b4191a56031040d8403003074052440035804034000600724038600c0d202c2d5014030b01400031821420404bc08600324800036290071074411f800300908410849510111004542c000c040702c1036014a581688a20342001c0901414103242c0701c00107042035061800310f40803c5914092600d0081d4034000c0011002074184d00d000e051140b4504001250038911809001c0c41c090802000300d000304040302450048160480e004100f000d0008100301c0e41c0001550302043c0e03004080407800c601d008046402423402c02501d030101e0441c00c1d000c1c01072540191418058071800e40984080341d440b00c1140741500e40903180200390400c10f183c80c0b10000e00c80d601450300154002c04400b1529126211103810000c060180c000e202c1d07001a0800c2099058452078012900b104042c5080d45802500c5c00c0d1a403021240019102c03140a001075116001800302c5206042d10b500d904e000e550312810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 568786285 1250 568785035 568785071
    0xc0d11151906140901150c020d050303040618031e050c3a080417090607122d0f180f030c14060d1e0e030c012a030b1201 53
    0xc010010310b20b880c00102d401104a80480700c2d0380009040001c15902c1e29296000c031404080d142010482c4400c03040005944407070150603c540544010f58072030a060070f20364119000f6030880c990049074608940d0003c1d408c040d42c1c0c0000d14074441e0842c04208019400c2c0c45e184504580a4841d0040d002d50800083d28258488002501c07440501d00748115501d05064031445004201c000c44d140c140014009124140c400b04581e10506d0080d00300511200480c0c815003004508131072852020b0300c04007001e540301d15001c0d0000c86488030301c07801521190b1501c00b4151800d461a0405ca00c0c0142240b4407401400501c451100d11b90b12260382954a0307503140700688040c081151504641c032030018840c1c038a05c01070b6010749802483c0c0c40c60400060740f602d00900003100c44072061608052001500b8a003403040c40e50311038101002e07680e02e00c1161121403c403801c0f24955641c0358080c401001c030740c0780d2070030004e050610305044c002001d02044001560300b0001810100180d03081083e8048001e030085 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 568787535 1250 568786285 568786321
    0xb0403030b06162f040509070302310b180402041533050306060d11040b0304121d1207030803010f0819020105070f0602120a0219050c0d1115 62
    0x31034012000c40d4803d0b401180d511340c0602c2061288001d86940240c942039004680100004007203c0c1e4055490f40841c1c0c100c031000215030782496402d01d0340100c0182081100c1014450311004000c00824103002030701a0300000301e44164060418001011900c4691001e00400c603091105000a540d4a902c120408286542010000e003503d1541d40900e50b0f050b581c800424007a15503a045030394820600646421030003807660501e40b6510001d030000300a100800c06081c148181550b2481c0ca420b080200c180003c2034942080354a40300351a000360001c5004040010440d00c42454030204400c16107801e1250304003504496001000103910021001f244085039400b030107544120f00e420600300201d4030b0071903020b40814810400e14000030103186032015510f02ca1003006040030f102c0c401d40c144020045071100c200507400280c03000c0300c1102e070089009026262074228540200c070700c0740c161075000302000e1005002c41100303e68075010080c420341d02d070080b8600000742c1c24070303000940100c0a0500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 568788785 1250 568787535 568787543
    0x1d0f0601080d08010f06110a080f04030c080f06012102130c02060105030a12050a050d0f06080601090902060f03150904030c020f0d021e0f060c03180604050d0b0403030b0616 76
    0x205082008043c06884800c1c1264010341c0325610092409500343d5091a0700780c0300311000c1c084c0001500020300c1c0f02000d03000c094411a05a40c0300c83c15841d04807001ca1a80e0040c2e1110b80c03000075104a00c5400103015410f481d064041071f8464414a070340320032050b8401400035408000d4071008500d886282e4400b08131440030740e084500e6640e2f180e01307254480c1e5044201800d07040030a040528014019002030428103402e1074003a1902e600301110600f02c4e004104442526500d039181040b142c0c0040141e140941050002089819007950029500c1d00c03801e1400030208a001c000942c2c40034403417401c03076038103070024002c00b00368038042ca0000c0c05041081003c83c8140b80d520114400c0b0304140e500070201d41d41c0940403903108160b228801e1030218034103410130390012022184020ba601c40a000d064114030320001551100c526040d4a0050072004640d01d00801e0305100401c030719565560401d4420790041000c1c00c094403903050407000741c0280010150040030020705040c0018583c80305082c81401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 568790035 1250 568788785 568788793
    0x607200a051024030f150c0e090906150f060f0f04090606020a150911031218060c120c0a0c0b0901030e010e07051e090c0307080c0703121d0f060108 65
    0x520100003c0103050081c24041101550002d00004004e0031189103c02e01688611000c40c1040711140c040d02e204c0d01c004000100c642c0042ea2081c00d21302103140e005254140944094942840c803c44040882c44109100348404020704200791520000c0b201c07064862041a41e40340d10180c1881f41560103845030842052616000260144c07002c1030b0b00440d943e1201e00c0e440c40110750302854026251005c0d00f130300d44c0725003100510415541082030139425a0288680d6445502041c41074082c040852505070041004001c07560a015002c074140c080440d00702c041c55182c81c1c4501100389015800c00d40204504c440c03e5001c0340c068000406041d20710b50981e001d11120702c0703105c0b240b03003039940141e15001c80303502c0b8030024031041c5444000404501c03030311070542000061880001c1c205a105440341e440094002090044c40745d401802964400011040700340b60a144d07a07402442825500368800d0304d50754030099108901203003c0c9501190358004126510581c0d0400416100d030020701c2400d0141c0b003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 568791285 1250 568790035 568790051
    0x30050c150708160c1d1902190e1009080d20060903190201090c03080309010b04020d0506040e0f0706050a03020c011d06070c020a0e090f151b0c0607200a0510 69
    0x41c101c4e107001c05c00a0814a003210341e84800c02800380132007084000880d00f80e000e00030001403d86081900d1489480d5a9441000001c0c603c1800f01200c2108484400c004246005008441c4005803200d20018280b807e1540001e0521800c1044174007080320080034080d00003031146074100000600325078400041000321000310200182d089500d0010001d1864181c0f54041011807180e00141d503010709903a0000c80c42c0c035100c20020f000c0340d01150b80d40c40d0a13903803041880141d00300792103900f035240c4040005201d0418166200360351450303184161410000000340c034104a621980695103400d01c0708000740520100d880d08a20241031103490f4058a12890f400256024031a5600b030b040282c000d49156941c1d42400c030341248a620040002e009485503803d0f02208010420641c005c3ca002d44544030680c0c20f100d541985030481070f17035240b01d10020521a40404c1080401c0c81504029541040380080d030802d10444000f02d1598100005030241d2241305042c00004102c040c450380c842e100800c9030207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 568792535 1250 568791285 568791299
    0x14060f0c0a0206150604210b01050904080d0207060902060c01090b150105220b041e0b03060108010e0402030c1e0a1502150a0b03030430050c150708160c 67
    0x8040d4507001001640024007040740700d2078288500c2609640501040d02e425100c18682141c49200d08100c03c080a1004480c02403040b10f42c0c08502401041384d50003100c0c2890303190700d9803600800071090754a07a4001468400c02101c0d9001001c0d459000c0c2689840301c0d101c600e81030003017110340000e0340c01040450025842d00300c403103d00c0b001004140c41d1a0308044620485c50840030040040001c042240c3c00c000c5946031091000e040100305084582d40500c4540c1a40d8032424100e0b80500252803062040c4143c0340c0c0c1248105041d1a0110005c0b401b5a0382d50000a290400710507030927421810110010885152490050f1903008082d120302c958079a441965144207202c805010005800281d00480e60b101400c40d06a0090440100803c4410340803001034290740c02644a083e0b42d050306c108240c40d001481d004e44c88000c007144400400f10304c030740d156030352100440d003907003072041c3e40c01820310b00c05048000c140c0d038901d03800c818060384905d0212500c400a140004082d0b441d6168004001140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 568793785 1250 568792535 568792537
    0x10911041503050618120c01020406020708010612020d030e13050a060602060c2b020d0510050603160f030f0e0a03110d0215060f19050109080a02030a0f0201090314060f0c 75
    0x103d5009008100d80e50301c1c0c512200d110f02d881c0108000c0c0d07009462503800e040c0c41c2c120242403403051007000103a85902d00080649001e00c26440f195480c3d0400030304000c01c800f01c020540c419501600c84130340c4c0524904d02100d484104800250303000301038820a003030202003036102c5840f4000c4000c1c1004800c1e01c4c0c2d2016613a0b0300342142c00d2800401c1c1000f41c103100c00c040220200072071280440e80321110007520100390983c8c11140340c41040590f203a04004100c07c2300d42104001701004d03991240345003044440282581c0e5101416003c1c0401c041548040500c6544240140c01d9404000c000d041181c81c0702d43d8a89400070019800110141240c5403050300100308a500304401c0c2e0014034410012144400318014000c2c0402d601c60380b04c44803940d407501e492088a480341d001e481c984a100d401e100001d80301070120303001386049502504004005032030000c1d5103490150081c10800b6000e81920040319018080c1d040204648089448070f05000c00004d940c3d806a8495032044045554044500d409 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 568795035 1250 568793785 568793789
    0x30a1505030f1e010902090406020c16030312381002010c052b050f070f020c0a03081e1603020f01021216020a06020a0c020a0e0f0601200109110415 65
    0xc140c011a00040040303040c40a1030f11150075007400072400c10341540024003d5501160191040c1e40c0008034892001418440d40411300340480c1c0b651031803425528010490060100c0407101c0d6951442b0110f50021428440096603000c4c000114030410703d1405003100d50740c1c01c1c00403070040c1180c01490300340354010b0042c00c240d18010703a601405c0504200b2003811820f104105040280348441d80e00358415920700946103d9030000f210060541403480d0000c10b2084101000e02c115000416503040a5440182c64000c880c0c10aa400e600c903d20300610141c88250700305001040c03080003d040f0002c00c80700000c1c40c2c00a009800b9103524075081d01c44c01d4243d1003203000f01c03240224480c000401808070365400300d00510151040f84c82c09a181d070b440504a0f40301c03548a001044c40b1074140d604526003091030a000c1c1040982d058840e00300505030805901d00600102c1c1440b11040544203221034059146d60560006c0000f40411042c5040452494490400e2980607508002c85040d0104c1d14041c1751b02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 568796285 1250 568795035 568795063
    0x2105100f0212061c15060b030a1d060403051b3a0306031a040615230303040f0905090f0703032115150302040317030601020607021f020a050d02030a150503 68
    0x188040c3d684032508412103c85c61010203a8580d004a920070b500d9015602c20342c0b6942002800304c444034038655006080102d41045540316104100c0000c4e400750648800e06851141f000d001d40104070481d05100001e0300c0c0d80300e050300c42803800d00c154240400e1304500341002203110440001c440c004906407009800042c0c103260070074400e401400204010301c0d9105002e02c40c0090015640020040306825650202120b00301c120414900081c1081d441140480114025841c081c85c1201d00b4500c2c10540c4a00c5171016640c0f400501103403414808804124550425038151544031718020300001002c03030b0349505e4001710f19042e1503011200d00c9800e00488a1125444011740b81c40817014104201c940d207101016007d0000100080c4c519001c40b04150303c240a2035120f1400d54002442c0c940300034440740441d405481701c4a01048032540d50300d0148051480542d44c0c0c030100c0000d980324400c0380341001c152071000040140201c1540e004034010b1400b20842014650380390105035623076810303500e921 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 568797535 1250 568796285 568796329
    0x10f0609031109060a0b03040f0c120f11060c0d0f02010501090c021b040e0d11060a1401030b0a0204031e02011101060501141c050f04050d0201062105100f021206 71
    0x44000d191601840384d001c0300090190201c10348641c404006904295011160f5040074040242005544051100079180801a100400d00c0648039200c10440400010385004491084101651210b80c200d403000c10303020007140c0e4586d19001c002092007950122000040d407030400045071071101c074000c241c40c42a107580200900d40100c581e07000140308911115900c9a5924840c09242006200d02c40403180561070f501c400b1122643c0c00ea0030b220006006103d01c6140c0f0104100200450149505580d003001044410765a2440c01d40c000744941c0d08080d00c0d03080302c1c54101c0d10741004807014030503180c402e0b80c03203102c0c8040001280d400d0340c4840c000c0c40d021a180081c0200c9881d0100081c09007c60042c0c0d08402440c401c01d500b00440c0c40640307a11044106010401007803081c1003042d000d1105291008008a9141030706001000c040343c44001480c400b43c600e000c0500008100c1071107180c030481c00070070a100b05020000001c0d0310456410903e141203800081051822038010903a41128040e40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 568798785 1250 568797535 568797563
    0x60807030f14390603011a0d0b0415170a0809040e010f1a0127060e0102100e0c040c080105030709091e03091a0a0c1b030515010f060903 60
    0x42c0d0160140c80303821040307031040710f02c071510080159070700510840c29158040c10b500c0d8103442440c0148103940c000b9010303410400042101d6680c1a1a041a00303c2d910003040d140c6002142c010040d2180d03400e81a8487d051048901581181801c01411141e48031503051400220785803a5444004d9802c1c0513091020503c200440d604054010418100c010000003034006003403010030085a441c0c01b01044480d070036045150a41d600440140c0c0c0d03641d00075503400800b005e0b21821242090b0a4080c82c41089807070301801000b07034003c00031404295100203003403005a1441da81c903a41e03214132800131071040f810040c42000490103400c031700741601c0e03000c0d0140074802c0c14051100060080110215001d14204404a0110222042c1040b105120f0345e035072500d4511303007900682c1c0c100c85035005d110207072000c102d01c03c41a07030001d0800b5039030b0354042040782e49031a54074858207000140b03601c0175149029041d22440c0d4844000d100718140d45008264800d0b49132120400c80b2004494000108581032003440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 568800035 1250 568798785 568798793
    0xc03061a0f09130b0c0906071a0709080d0c02060d02030f1b09091b0717030402190509040605040c0b0a0203070203060f06010c061524080601080c041a0c0a03050c01060807030f 77
    0x1081d520201703111400c0e1030001081c004c1803aa600800056403000100754002102400d42180c45130843c1d070310704d0810405170501c840300c0d45543c7c84a0400c8107008409405204544590080e51054501c4000854a9103000c6140007410301c02141c0c1c10301c020a02102c0300000066107810380e40e628902a200024554034802c40340c84107000030031070106501040c840c0c0c0c00002c10205182d09500b0071100915181d0034a44140031101c050900001d428034030302e81080c841070301c401500c658800e03000580800c050b01c903410405814001d03600258101d40c0000b418201c00f80c0c0020042c0301c154401d908584041d0f807010302e040d0f6169000c0e43d074240040e070b0140701d800c08645c86030012040c60f445214502c3c0203aa85900c02d00305180704008a0b020101c03a410030060a54000800720b61120f401e0070b020305280345c91000740a041c402c80c02014040070708001c82803010300060301170320b05c0c0c0c03c0d4810480d01101440c1c1805081c135081719102490544c00c016020545460201d15107080320740c0310146030118401551 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 568801285 1250 568800035 568800053
    0x609072c0607051c08100303050d090303060e0109230408030f1509070807030c030c44180106050f0d0f020a060f02070e060604120c03061a0f0913 64
    0x90076401107040c80b40c6400f240c0b09200080140240c0684c1108110f000a0060041c1c0343c02810480000c810550400c007107508081200c1c0550004e1100080c200d045140c103900400b1583c11107902c04444000210760905546c0c028002c02c0c04040c0180d2903480c0550380f200400c182100c004205180c284007107114612124070b89030304100241c0040d950480c02038086080307003104441c00c00014040106220140d9054850002c4142a51a0510410454034400352415010000044840341e203880082c050010440c0415224015045c08605600e10030105082c1200140c031040c1144807040c05508007541d05104807801c03120042c3c6090041002441013007040c82c1e04180070f4a88240d0203082d80e005075204a04900170344440e1b1141004d081031542c0003807a29030349400c01c1c45401c1009051011075aa1041903c08031950800891600365452400000750581c030307071000308010704064803400252045520901449400d66603402815816400c0001c2400d080d034010340c4c0000303080e9412000c0b9034401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 568802535 1250 568801285 568801367
    0x61306020f010f0e0a0f1403071208061c0803071403010b0403020a06050309060127021b01061203080604050403020f0706050405030d08010303050909180f030d0b01080103050601060513090c08060907 87
    0x11f000030780710101e103607107072030469104150450f08a500003d01c07031056074021103c5600254252140e0007140c030700b610440317002c80c103c0f03402038016000803001a0107075101d9660060302500f6043c0d442c0e04d0307503075a0080c4080c03504680812031060040803404200c5c0e0b885a020b0300c0c40781c42c960307008001c0b507460030b62440a1b00100101c2016110214444140000c0490006094070704001c584a010b10484055580c00c441c516040020f05d20414135070b003c01700780e00c618616000301044500085c2034075245000d81c07800240e6841103105d0b01421074001000c5400001134411520203800b81c0d48617840942c0200c0e00034509000c0140803880c02d21224280d0300b0078090f0780b60702c05991f02c50b1469001103001e5062408040c140050340550002440010240c0c0724000d04a0505007800c0c10816035040d0360710641c0794441401103504000000c01c0b80706c0700907110b403038550080201400403c41e051210794020100c003411580342c0d00944528011604c5a0b1081c1c6021101e0021101d6100701180c1d07402050b01820010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 568803785 1250 568802535 568802543
    0x1103090a0803031008011806020d0204030f050d18050913020109050613090f0b06030f04050a0b070f18032f19081b01020d0e061306020f010f0e0a0f 65
    0x1400008400d4480c0c080440142050100854403464000703080a40450144c00030300c3e441c0d0508401810040e031109424142940c45036000d40c44040900c030010090003150b1011b841001c0f001c01c03800034401c0c0411003245111056a580e02513029a1280d0360580c211403152640060030350303001810304080c4410b00c0800a10501d010400d0b95a00c0000070321030340010030481c5810003020b00070004c4551501c80c49040391403800b414407000814070700003611400000d04440b070101442c07001170200070050040f01c0c001c80d03010504103110b051840009125122048107a80800c00071a20711111001d0200c4502c01c4a610085c02c03140380c03686107441083c0c1000185a00c2104903d4011120a070f51268002c0c0e50b92280071081200c20b030324107601246806010400c0200303000290b400400c442c0d034046a0081550b043c0d0900d00b0400702e0400c080381c8284a846841e004401d588000400c10070340c0030400d00c81c034110038402407150980300c51800b81107550005801c4155845108803c0014500c00140d5202c2801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 568805035 1250 568803785 568803787
    0x10501140f0d0c0504050a05010e060702091b03040302030a09080604020904031d0904050c0f0105040e0c07081b010e010c301b0804031d091302040b12070f0b13061103 73
    0x10108180301580c8803e050940031840c04103060000b810a0300d0038800a050034607050407400b0b0792401045581c447c0600203401950f00d0000581e2100c003100c0390840155145d03040307941d64509400c00946a412418230413002600080c0001109040016664020b42c0c0040c00c0080319107455900307841c0701900005100c9890756521a80762280d40754034045200b0340c0103402400492411604200007001c0b1140c00c9814800184020f002060080d5040c6a1120100c1c84590b5100038506002c0d1080c090b804910082900f50402d5440841e0117401c400800c1d600c0300e000b0301a2035070020082e920144010340c0009038500780c1c8150202004100c40308000c1e14280c08c0002000c40f6142131b0100d009540800078408034140c1002c2c041059840607152003a00b88801520101c2ea008400103090740300c0260100b10141010303002c03082907580300c2d84044000c21004022805070041207001c40d442d48020b1003200400759401400181d1092080c0031650000c040d10308000354a0b0420000b0f40364a1044000d01d446848 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 568806285 1250 568805035 568805047
    0x503030d0c020c0d0c260d030b032a0316050f0d1406160801150905040b03100f0b0108010519050d0c080d091401180b21010609031a010501140f 63
    0x2144401e51484900544205e1407140c1801070340c0246a410302520003d0790400440ca40340c080c1302092020700c0c100c19181c045500b00c540f10009140940c040010f001c5294010b04a000042c2c8108841880a4090342174480d05c07600c00d982d0000c141414861641c00411110307050300c0901d0114a2240058801c0f6001104030140702402440c10b0320440f0340762510700e0146404690381e6000900705004060291241d00060341c0c0e8003004000c80d003241706da40e0240d0340760498210329540030300404c014050384c08000c001c001000d2500380090014503aa660214000d0000851a07042440b400c1c0e28440b00788002c00142c070300d0001880b4000303102c600152546134050101090080f07081c00f0021071403143c0d41c0ca250340242024001d05c0304040580c0c44174144001200521694001003160a04440c5584960b0341c0b1507000d02e003044903181c0c10402c49c15050f020700d400070a156800540d0780003900d00500401e01182e41c0c1c030700c00c007280100a0140b24041941032031164a41c00d1f40c2c1d802800c00c480380445c0c04c4c0c1007003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 568807535 1250 568806285 568806289
    0x9040b181f15022503021c080d1e0f06030b040b0601140304050705010e100903110102031e0c0c0d05280501050406063b0402040b0d0f06060509010503030d0c020c 71
    0xa1002000801a040201940460000c00c8000440190241410300c04d042c59030b40050429807404070980031005901074640305011852041ea5000c1d20440c3c02403001844280c00d040c41600405801c0c14a28a882061004600b2501c03c2c001035a50180b40744441ea19540c840058641005200c02d04100700f48160f403503851442c00203103001d18490f000400d00300303003060005401404a80d01c2c050140743d00003400e8000170340c0202c0b46021290850a007025410510004038210700c078492302035000241c82d0340480544412200100401360000b0242c0c0e400f5a08542081368001092501502e01e84c844022405512224488072a16007451368810110680c155185801d5401c1110141d48407680d03900100118241100e085a4465812004800500038109000044000c0d2204055003805c0000001c1c21504d03250320045003440010055250504546008030b912551034004840c171b2410500e00089500b040200c00341070b00c0c0014050f6003400300345610b410007000d0302d0480b241140320383c4040344134135 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 568808785 1250 568807535 568807559
    0x908041203030615170f06030c06120f06010302210703060906080105060915131d0a0b0907061b030813020901180509030a1b062009040b181f 62
    0x1840c801e4a000c140f1030f00e13018114908100c068010f00a000585008440c2440c5e1049110f5000013003840d04c0c541621108003007460201c640000c5e9810400004007882081000940d451049801c0030300500d0540c0c41070011000e0b13002e81c265460416022801c29042800b51460070b943c403c07a18a40009c1a698951440341030311421761100d4043c2e55200d041c098103040003804181d1140720b50291503c5100c2c00070205030b9824bc0300ba040c080d00d80d940d43c03d02514084d00946030b030700543c0c5234040b10105a440e08181d0442201a0303005c0256100c0e801000404174002c0600c83c001ea015800072030704158594806440310a8010500c1050038051048280180d40f51000300e070180c803000600f001ca088540110004072440900140015881442044940c59000d0320721100081100020380ca00c00c450700e000c50241080e007254180c02c03140001d903058080c24078009801c200c0c2c8225014003603c00e40c0d90620041d1090701e81c041ca645280c1c800003440080c00c10540d05a070390104461000700c0c5940d02228644 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 568810035 1250 568808785 568808819
    0xa050907081e10050112060e180703080307090e1503120a02031309060918150209190e1506030f0a0b01120e010605010908030301060c0609080903010e16170c04090804 73
    0xc40c0d02e0004090200396800102c404001b50100d1040081d203007480e0248900b0030004042c0203017000c810600c0c0143c00410b02254004503400806980c8030b080442c40500058a980504a0040c6660002414200c040703030340002c5501010300a03103032003907002117510130300e030b000d0040c041c10f503c0100030b000104030395442c101e00108220070b00011800d040c4101c080586801400318200e0f007a4440c8110b0104200b40d00d20010040b03080401a59202580c005c1502c051182d40c142d00d040f00c18900000f60f4000d5034500034851700381100e90074540f549440030490b880c0070a864040c001c05c0d10070001001a03905911501ca44541410039030195182c0402800564424006c03005169446000401495801224800141900901440c110342c10400003d1401d081300e83d02602442d1600d0600c42400745d802c1c00c0391401c41018000303110b101040446180c0d600e14244500f8510303015000d000600340340382000308010102601c007400d0180c08550810025000a0303c09803010a0108000204181000d85040c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 568811285 1250 568810035 568810051
    0xa0c06060e09010e010b04110d020901030603021203032505090d05120f040911090d080f0d0207051f0c0e010e0a080322060f05160f05010f09020f0a050907081e 70
    0x130348011303c544041c00d548524821500450030710040380700e0380c8500c07800c2d510400c0380742c40011f0b00c51001e40012030161034aa48080d41084d00602002d094080110045100741b28040800801c04904045038003001040c1a620000580030305c11030b000d61604a95214105015804462a41c2d489800e038a8a0303600024a030712809800203000c10140341c1030300a4920854502240e036007403501a00204401a0900310001c0007141e0014204145415035001d0350703d00c000410007151104001e1925665032183c65146154040e140140480b045034280a0040085119540c0078005603540300199000d50113002056071140d4483c101056000c0c1c10800f52200b400c240b4060321124003520680a204c22061300b0031004c004001040c00101034204003151441d01d0201680c816030841030600c40800440000f00502550804880d1040b8102640159201c94002c42c1c103a6090001f042c20001c0380302c100d2054613001000d0340c8c00035600500441c102c0e07a0000e09106d01140b40901c01e515070100b02012a2480c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 568812535 1250 568811285 568811291
    0x303080408070c0329010b040308040e070903060f14060d12030207060906020705161205032b05010f061719180b190606110c1c08070c080609070b0a0c06060e0901 71
    0x200b0303505d41c0c20b6880e005001126141b450b180c2103890704030341845035001d10750408441c000400c1540703200d160040d004603000300013000300300c0218600c0d1010300b0811004204000040001c110240707400300c1008406548044841002d105006041d006508100c2003130362841e0b61011614041091400100501352041c40a0030b4881218240024069125004005103e9449801d0300c0003a034000200e65402002c50009200d40c1d00b0129034004001c003400c140c051785400e1a000241e444100303900d032020366031a901d84c0d801d5200750500851101c1800c442c000b00010604c103071310b000010150302c03034010382c44154012a41040790307866000c910304007590030140044d24180220401c40f042d100310005040c00d0302d0f00718003800480414541e00c90304600454420521407403000d840e55424914400c4580d0f03c01105510340029003009036400d51580704484060044200003609001c0104259040e103060544c00d0742400e4485008440442c08408100d42041c0c0d600b401043e032841040304c545c8502c1380c040003c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 568813785 1250 568812535 568812593
    0xa2004090608031620030d020d0806060909040f031107030c032904110a09060905010f0e01081b03071805090c0f010c06050c0d09050a06150303080408070c03 69
    0x40401c4440a610200300c03a00244003181d0f4a070480d01d16680380542094504494418440b0310090045440d980190301d845440541041950040b5a078600d08810f0b48510307060740d41395424014103110301e100e41584040c1c0c900024000070381d1b0680300d4010034020311704071001154418a00303140c40c045400503900c209820340b0800402000707441c5450403000c800c444010320441071a9081e130041020304001d0000e0006000d0650907140c800c6c041e4000c080042080c03254555810b140c3c0005d0a080c0201014001c0380300c0c003c1417a008801c1c003070341201c800c00014040d0081402400c12040300f484181070b4907003c1c0c8078002070b00884940a03002841425600000c142c20111304062070110790928040c01100210301c41091381ea0040001d80d142e070380111002c01c140d17613424091051482030144819007a864603000d5810720100042140384281315000411420000c00300407a548441d40c0700060000704490005000140c03950b010381442c40c400c500100b4080e48903a10780b10b600440301801004506e00b0032035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 568815035 1250 568813785 568813799
    0x51303240621020607110306240a1a030703110d06060e090421030b0406030807050d080603060c0c030c0106030821090c0607030c05030d0c03060b130e0a2004 69
    0x41c0341e006040e90045036440034016a4190303858001c0700006445988081141400d001c18018099070010008098604a01c1d200001081d003108504541e0f0340e00580b52030030102811b01c000700700107445002030740320f54000440900503071030381c40140390320b08064440c171b0501480b69a8102401c4005504600030803c1c0d420508003c0001140c01c5880380720b0410305043c800411000340b100c04420020030314140110501d050103401414403001d81d1500a4540a000014482c0c010098500b152150059500e41000c02004031081d12040e105641d0507007101011034809500c4100074910b8220701402d80f030030801a011281d08440306940240d54a80c5c00044c900300c800405441e0f102003294041541c80c40d81015842207a8918410340300900030300b0002010301c2450301803080342c44443e038000e040b2070791004400c95502c0a008100c0d05900400d0414001081c00008181961340300c4c003103910300719155458601a6040c00c070001e0402c1110f41c0c0d40381c94101394808400e6019032035801042e4070507070301c3d071070211 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 568816285 1250 568815035 568815041
    0x5060601110109021e0d0206040e07020c01090e011202210f0c04021321141c0903050d080a02041206090c0e040c0e04020423060306060a050d0305130324 67
    0x1d0824030707030345414680e20042c1d95800d42035200175042401511030000450200317100311000301c0040d5001e0302c040340005101e003480405503c112411703420359a420b8000c50064170030034a1406039002551080d80140044400c04458440207400144072800c604400380d0b00d55241100304600300d0942d000401c100f202e150040080d198400da06aa04610749414600543c0c03081d05180130b00f0440e89004000d0200b840125000301d4460394000c003080d02c1c40c480610003595155202007040007003200b0721003003043d03042c040e0590b4000c0300e4201c400740034602c14000c0101c614000040c444440340303a00380004140204a00401800f492051100082206003401d00341440026680314a540320f610740200800502840d03a40e500321541c4011081d40d589643c4001800b505907800e115080021a00140410f000f031801200c2c05100c2c01d9040c0e400382d444410500c11810160f01a154102480a0349440040d2040008250502e1071a041c07188040d100c0da583c0c880c922070006800e096140840b5601210350144c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 568817535 1250 568816285 568816307
    0x2010f0606170115021f2004031a010302100503060120100e010506030a0f080f030403030b04050a051b090d080a0309030906031505011d0a030803101409160210050405060601 76
    0xe05241208000b000c0d0081d0748961440d42c402d000d529449a03400e100701107401c400c3c05070401102c062004c00c41f0f06c0d80d001558200c1c0c48140c8203250380003008028a018180b10328180c0f50050101e180314400100d0980d440e038400380c002410031180009055001c1c00d414528009011548003800c4c0422500c00101c2c1030302c05d00031003009281d25103800e0000e44d580000350122859400f06480035034600608044441e40a00c50740003400c030500004201c10545d248d440072158180464081010303864000010007140c42c1250088a0b14401003000100160b842019042c20703100103241e120301c40003d58450105070013005c0b00402080e16248003004054100d110500500024a0300f0810705800314070b124001c1c541c03446018144480c0364400e030241642e07001c90301000d25024004440b419600d20b010031940d4811518641d410302344407004280034042031064008072038014044c012544a002c0000780030194000001c09600c0380c1c140f001c00c158998081d141c4a10b0003500509118a02a4000b4060340842e07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 568818785 1250 568817535 568817549
    0x30b0f040203270a080d060501031d0705061e04030b0a0e06070507150209060a0210060609050108010b0a020c0d05060615040e0a0c27090b0f0d06090302010f06061701 73
    0x144208660f40310740000e01e0809840351101d402c3c1a00d40d2a460340e0500112000140141c0c200050440d060329050f00140120741c420303030302008140c1c0b0000c1e02c1d8005c00360b041e40c4c0c070041e034018500801c002c0c07038520044c000100300280c6001032100c15803009200c0758820b0b1300c1100c0020392103080045801d01c5201d14424154480c000d08a00e1030245e20081c410f1049420082c44040316000030b428207895a810f0b14111040a0201a81d038009228040d649011911200d00d0301402c001012528030f100301a000d0813203106844000d102e9003404a2142c0035007100500c04214031481c030700b80c1e519644030340900125501400c0030708580d00f010024041f14041c0c400c0001d80c4031100300003c2015080d2b13070400c1584181d02c00340000702c142036690221841c50020501521034560741c806a80780644085443d82221a84c03401004020051003d1040d500040d40c4a254030254440725200810101d1308481e038420312a2000058030866110340908031651500801d000600e08000001e5442c0032020b154007601032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 568820035 1250 568818785 568818787
    0xb09090a0b1308070209041406160c02150702041401031b06080f0718060210051506040b0d090605010e01060206130203060a0b0a030f050d0221250210030b0f0402 71
    0x40c6440d00071070120041c0ca140300402ca15000101070010020944010a80c0280004c001d400c0a003407d0941c5010b500654070b85004a0000c01c080c0c0c982c07082c20207024105600d540c000340c4400d400308200c141c0c1130b07020301c0010b8108010303900040c0c1d44c070710503a0380031245241c01c4a45075065041c090b403840c2d0107102900c1044100b2405004103030300306015991082043c28610995903608a0480d107051401c92409003203002c1d1a4081503031600420031142900300340d04100920342e9081c850032038180c0c2c41030381d25421440c02c21040c08150b41c200c000b028400092000881c05d44400e41e036903000c07207000340d012001c24001c3d1001400299814080c03680c11400740c12090141070030b9030f000203480b0300d0060003600c82c031aa07070200c19031a5110102c1d000025a0080c00b5002c0080207428115210f05200070014014042d00300c101c07004004c00c07100300d0b00e001910b40c046410030000101264400030f107c3c50a41340301c00b030903d2050050b40c1e0040382509502041e80d01280e841000d00a20100303c1079108442d2080380 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 568821285 1250 568820035 568820053
    0xc06010905010321080c07021908060702210304032303070903020a08031e0d0b040908090a0b1e0d0b031b0102010617100203040204090c140f010309032717010b0909 72
    0x2600400c015007011b04000c039503a1b180038501c0001c5610505010502c1d1003036151500088941c2c002c18480e11956261f000da400c0c91010500c0c1c60240000075040c899000d20501c00301d00401d119401000d58107035038519102910710303642864407084d00110741c41000500098414030450404c40000f00080c180580118100324001c01c00740000c1c4c0e410206d25160719008607401e5400115604954951203000d4030070031044006003030090480e446042d4942c012500c1501c000380d1f4044903000c480418440c804003032201030310300140001651155070006546520361041d1907403a54107200a0840282c50608803980d00c0000f000a425100740f41d0000380e403445000c00d004443c01c40480c200070030710205040140d480d40c035480004c1c01000c220001920b402c1c1c107d103000c01c0115411000001100c0101d5400490b001104c00440c107480610b40300400007444001d03880ca8000325025200c1d00480400c420f60b0781691142c00c4064641da885450403160381d1183c03040140c40c10984440c941151030280980b003076034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 568822535 1250 568821285 568821287
    0x80f0a050d11030702010f05130608010306050721050405120c10061a0f03040501062c34090b0f18060405010806060f160b06010e0a03121101020c06010905010321 71
    0x2000c0c13044040d05101507042d03012042441031007200c064981100c0c0c0c90010a85a50009003c1d03032003400120748113413410003c076841e5401200d15801c40050300e0944403089003081c0103003001c0c100140084030f05d8400c1c241e01200e070b40d003004c0180a0341c1c00102c0052a82c000710b008410180c03022603110a0508002509040302000401d0440300c2d0254900c0055a507038444e46441c0c0e0060001c1d9202030751249800d4882d028046001141402500e13100010007415150003100c50a46a4540071160070451446c26103444c0236083c10f00d006001116040c2410310a0348d6044058280e4407031641c44482101c0080d00709549000601800c200d4901994190304040c2440d001034113004c009132446119040105640103980d407040c003221021450305140d030843c05894a080130408a0594865000c00c181d80d8280c01e46042850546040300c0c0c0044002c5002080600f0544d50150203420f0002195000c000c8220260f900f001101e00800540c50002525855400c0005030300c83d07540c807009001e05042920708010b07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 568823785 1250 568822535 568822537
    0x60a0f0c0e0616170403031701081b04050a0b030f01020a030e03040b0703111e010603231c180f05010f1d09060d020904051f0606050d05090304080f0a050d1103 70
    0x110809207012030b12000d0b1800c0c500640401ca0b01601c12113000050084101035101c0c501030b22030000d031f200302d0006903201c0480a4556207a14421140313000c0e800e1650005281503040340b5000341800380000380c908450004642041c05801000e04260740000340d0303c02240d4188a08501060050003445c102810a002c04103a440340b1070300541000410300c82010860300034040300146c141805c014101501c00e40203440d001e84464442a036440619520701d10418a5100c010360000540402034020041e01c2c0c41c00290040e4a4800c1e641041440b1f10080056954001d07103402411004100e0501a4035201c00105090000e0500d0320410680110000050303103034218540104000310341090303080c0d6644002c25078403181030901079031012a0710284000d2103000300d01401c00481110204024404002c0041c0c01e64446204100001c1c1003044440f9680c01c080d40102e0300940c91600382c0e0719040c0c0d1040d0242c500801d0850700309680e00071340481402c00c003003001195941c0c45142080400c00b851451a681c032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 568825035 1250 568823785 568823797
    0x302030f12180103060b130905070804050d140d02160510090803010e13080f090120030406080c07050105091c0e010c111807030b010905030c030304061b05060a0f0c0e06 74
    0x1840018540300d410b41c4c001d421410145c030658680e40d40701c402e400d810b006015041e119102229242c00045088103100d403150500c225040303402000c4050850004a580b4443d0013030340452480e0038408020400820700007060003000380e10702d005c40030f030702401c0c010b0030a4111003800785c40d01d00c0d09101c200000e0090b01a04c2c115951310496160300d42d183c050703000312141003100040048900007100c0224004850103020708203000c1c0c1c7d416200010324010002c54040d400340c040a01d5006010421280b8452402c6c41d610407501d40c3c04604140c4282e40d06401e40d5010341d110900754001202c124010302c0060100000605a07152003103081c1081000030704403501241c030140c030052550300344d05e140340c0b5140c03000c0a000015880e9000300b8500381500400400c4400b0201d030000f005c110303000406140001c0c440405150040286241034902101a02d00c4101e0340204c1c602014860300242c0411010300c8000e20420540350041180d4043d00c6200b41290840141c0c3c2003400300c0e1100d04d210395181c036819642 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 568826285 1250 568825035 568825057
    0x706090302130e0607080103050f0706020319020f0a080c0d0302040b031302060c0d090609090e28080703020102180d0c090b0f0312130602060106020d03090807060c090302030f12 78
    0x11108140044100a440ca5003070f500181c3c4294402c1c8504d00d5404140c141c1203a020340c098401d020380b03003800f1070740754040ba1103200f005900074440c1403480e03991f030700e980c424003545070045408410303904044604101c6105403d8175050001f041c11240d002c0b051040c01800d2585282c00c5181c1b90401b0b82904a0740070160101082e46400b40740e0a0854807420112680b61034160202e800d00290603c0003481c0700c041d801643d0008000c0030700042d542e480750140012002400000d40400c16800540003660390002e640d00c01d6020320200c6c0321011455201c028a1820b00941c005680c803417074440c44015048000c01c20a0107421344210720f20204400e00707818000d4402c5100081a22a449000502c40c03c175000d401070b51501800c2c1c0c09110101c0a03600600101c400d690394020282c2d030755101039882d84424403442c80942c010030042c0d400c440c869401200c0040c4941c0c030290918085489060494038004080c3c008a2031012081c019407400304207002c0c460b210345000b881d0040354200d1a850f540502c82e0099 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 568827535 1250 568826285 568826299
    0x809031e090d0b0115022409070e0c0a09150c02090a1b17090109030c030f1e0302030402330306131e14070e0d1502040b04090b030706090302 62
    0x2045000040112001940002c2c201101c5aa040c181440804030038070038009088510305c40e02d0060382c004121f2180828446103e0380300c540d1101070a501d41d45004103800041c2c015004041055036166100c40e0265800c03002e500e4442c03265071b40203031100c905070700804524003410042e030051542c000700405c1d00b941d05542d01c001c079446000100d0060320006100403204458440069400c1c0d6101c084415441e80400ba501403903203400c5415800c841c40da80014001640806019000c02e0082a802100e1401850100c42403440c66040396204c1d0500d140072000603800000f40b0095280c04604231030300d140041c1c00c140c8041c4c06605440c004001007c0341e60144500840014403030b80c1d4003403888003031140d101410b000d0074584500143d6804401050702200740d00d080382800d22502a84020761003145e8640b1610048000f0108202906145a0045400e215403003c10700d524503ca0014000500010355106e8450b4100a4889e0580b00303101000da0080d03000b41c2040040d01e030302201d04030413030b03070151006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 568828785 1250 568827535 568827577
    0x30c06032205030f0c19050604030c030e0a09051602070806011502160b120c0301060905130b100206090f01140703150b0f071101020d1d1207030b011401080903 70
    0x30341c0007000108400391240c0004950000386801e240b0080c150703461301c481039440c074800e8980c804521600c0b001c006040c683c010f800003000240103100b0307442501d019003850440e104030840003c0e203200c02500035510407900c13617040c4050112a0701d440340d10060180003901030a07040071101136462805114000980c0c011200c2500038070300900202e03440c5200d5824a1803041d0301d0b561803c00310742c0154031040c8130240c120005047c155042c4281c0341603500c1582d90615152421003040780314103038541d0f18189155211520101076031402515130300c0d241d0303036009040c0ca494084441414007401076145030703450341403c0e400600800b080d80c80700c0e80001036040c0011200101c08844415080e160010340d035201b800203101401d18005005001424844c00c1e0b0300003005420001203031a8828030031414003003804510310300b10301910031030350242000e40908040c0c80300c4401840940f5100741644155900d42040d001400158504250400c00440a090001e09800e01c820303c99607a100b0041a2003080d0610f80d14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 568830035 1250 568828785 568828831
    0x3090f1e060e150a1509020d020a0906110312071119030e0a060905060c070305030a0519111b04020c0d0806193b0403031401150c1104020432030c0603 66
    0x40171014014201c0708540703d201c003e859030001c1d406110220f0124030b8445000810501c01c1194045890303880d03019506009400d0702c4d10f100303004013420300e500f4082d41d001500c1d66990100440038000d244122a641142600d040280c031103c00c45603018021200300c202800b005810081c61021900240e6009170f0700c04481c200705081055a4200620768000054688003255014020b0300c0303019080381d0820b140c40c44402c0c1c16038141200340f0303016425030854030421583d821007100310300543c0c5010b48050318010120f8075450030040f000d04a00c0c0402c07800c4051219034200515504000200500c1c0301000034100882c1040b240040d18503100748100307200180f4030000e08114400008101d508554480b400c06280c054003900d1a0101810050b4004000140c85c0701c0c20444088100e8440c2c07101d1141000c50b8503100e0704c3c044028816600203808000010b603254003018246428403452281c5031764007141aa202840719911a20039110750b0100c05901c0007aa5201c0803a900004942e240140191034050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 568831285 1250 568830035 568830071
    0x80a0209060a080411010c0314070f08030709090b03030408031902011506050409050702161505070203160e09060103020f0d050a0c0314010b0105070f020103090f1e060e150a 76
    0x44401d80005012441040c00e60f0841c50080c09544501c00208124040c02c0044800c0c10105002500003410b0f401400398001e540401440304502985240a00349602d031036000d119401901c8002c0040c8214008004c0910580303d4880b0707896044020394a807030714000000307a49000708000c140708400c0c04100c03042d13901c0c001d60001004a00603450078400c540d82c5c21000e8440c6c1c01c81c0c8120342d141420030000901c087e2011a1804c001e0164240118445007030601213003519181c0001001400020070829015076400c0003200300030500c11056680043c01d024080341040300180030003078650701400040c001039941c1401c0c1c002000742625010441c04071070501c28640355120001038a1184624004014032070901c4648101929204c0284140c00422004403154864240040c0400407261005801584a500909080c900a4515100440712034845102010010b0441810440e18548200c2080454043c0350300020034800034280c40e80d0081c00381050034100610303a45c00075076114000505107850785 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 568832535 1250 568831285 568831297
    0x3161805060a0306050c030a32190e0303070908060123041e0c0e1909020c010615020304030506060405150f220209041103091203071b291303080a02 65
    0x9101504240303000c0e06d640da20030740c3c07541136849c24103410380201c004901e245104800001d000c4203d017940101c20140300300014100810b0141030b10103040c4000940d003c1c00d00741400140155a407401d000710054140c0c45580c0c40407000d0b03002440104086042111120940c1c43e2140390000c401e40c1c2400040d005100403104071202490402c42119102c2903580034450072a0b00303880300d00001c94908200004144200021000e0200c00c81c000c1c050b8400300d40203080c141480400119191752940c4207804207011a601800050780040b070200240001049080d030042000c0d141003141d03081107100203051113a440c040c070f80520300310044001580c40d449001c0b1a5841d0210054410701900341c18107019501c544800c80c800c0c1c2c00c1c82481e0400403142030489028045a00c01801501103e03803c1c8085504020016024070204103945468900c1011062002c03502c140c5191100c011100c9040b000d041ca80c1401e4680041d100d000c04c0385030300c0d48da800c542145030582446c041c1aa11090000041c0c490b036 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 568833785 1250 568832535 568832543
    0x6070e01050706181502040b0403060b0a050a0621021c0b03070e280509031218100509060f010b04050402071514060a060c0c0608180f0c03161805060a03 67
    0x200c22454494100513600740e113024440c42e41690503828a0785150103902032030240e28203141d02048204009030303160740918510741001d000c148001e13a030340e00098006446070b80a1004141c5130004044025500714541c424058540e00450902062a07010032101915001c0000c80304c1d40c0d04080002941c08100d8a03004200b06101c0805628005410481040b801d50350026072010543c1500d80301e060038003803e0b1045500c900254209005043e200e001004042c10b1242d0f603a00100014501e41002e100b4520a4882d1a0000ca0f260610451403031500500803d40e149880500340103110820010080f20704850040f0740168486c0c0e2242003560014844054000f011480c0800a0400e603083c1440340340304480c122440c0045542c3c46900750b580c81d00d410b0300100403000d1110706008030350090380526003040000b0500b08a02c400034032407618001e202118142030740d01111301d000d203038a02040300300500d116404100d03000700d00d052403681c0340c11042e018200105845d0400500c440d214607039248029604 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 568835035 1250 568833785 568833791
    0x8091005090304050a08070b3106080609060904171804050a20040f1505040b120f060609011706030115030309080c06120601030b120a21080906070e01050706 69
    0x2103a079285940798018401c1c0d5014480480c2c002443d403c001c0b8030340089420b101c145600e4414001410728002c462040400c180c07a80c001080703c0c88000c50a040030140044bd100c01c1d903681070034410410665002001c01c1c1c85408840b0070400000d800405201920003c050300e240c480c3e500c800b0109820174407182898110380303410b04000117007129030482c032050444400b8080b0302111110391415284070b640541a54100208001c00900443d100c004008101a241c9542030644980c042c00040e03000e05120038519a44200740442c1910080d10f664000c01c046030744524180790000040d000c1c0f40b01e4030202d21207404402c00218291020b4012500781c181700c0c1402400315849107405002540e02d40178000700c504c47d0704102c600d141402c90464142c0c10503800b200b12955030f4071004502134004900c10517008001440c0b16107144c042046004003491190f2420220340d6500e1401007002c06440b443d1104000150040c454800c0f40402e80941185c1d03280f5091045031074920050b211481294001402d0390f103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 568836285 1250 568835035 568835041
    0x92f0315040605010807051f0912030302190503010501120203090a0506010312080f22050114130b0c030c09010c0318150f03060e0a0f06081209100305040f020108091005 74
    0x400da2005910a910a000c10096a6210b040c13150351040140038468210244464488800b2541399051141019500d0000c034000d80341d000100d0780c0c03a4240011008a500030811f26014203001c100712080c0e44042c50424219031400300001c1508500d641c900b180b0903800804a50180b0083c0075022615030420221462540d40c1d01d001e500c100600088540056000702c0400d1030030401280150041e140002280b45400040303000518070444207a04659540d0f076070024005007200000d100d44160200599032003440034a05042c4424600103000220380f400030802c1100d83c6423128280c482e801e10a00e045840ea000c80e01d8241c80c03081c41c034480d5902043c00501c00103000d1180540254128030f941e070310342181c003503400015001e8441d070380950309003d41c00000180d0b4000070382d4000c4403103c40c1c000d001301ea059038070700381a402c00084190f40341c84504002041081410280c0341040e045046207000c2209140c6501e40300681c41c1200c4000b410454050082441341c03030108011200e0540b0104200b003681 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 568837535 1250 568836285 568836313
    0x9081c06150f020f0604050a170c060403050d0b010203210912070b04060608030702010c080904061703090901060c0b071d03010e280302031209070314031c092f03 71
    0x200e0454580062203540d1001c13035002c0c00843c4a0307000c2c6070f104000f461307a28980d60301c140c1c021410003a0160400001c0c040070490182c2001300f54003c0c0c0c02620342c55500c500d02400441039039103420783c0d00d044d544200041095034806840800322091307400302c1641d00740c81e04c0c0390342420b0000c1070780003001e454400b0031600d050080a200250050344038410401002d65a0b044494490140c03d0010740400c500700030440200301c07280000c02c1c65240042c400142c45480e406052144003450403007003000d90020909440500b40402028050001c80c2080d1814100c41c1d130b240c0d022135000a02c48820004006105101c12040080075044141c0060080c048403401c4494103545a100000140f49040c00c0b6001c2100c6665225201880f00e4055001d14600a4414111030542d08003901e040410320a1680020118480c091910510030171078020b140d031410140c01701115243e0380c22144103400e103004482c40c0041c4044058800458641c0204a1007403d103003942d031000c1d48031071203a64142c0195190b00801c0c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 568838785 1250 568837535 568837547
    0xc020f0f06180915030a14011506210203100303030b04090b010801050a0c0503060a12050a020607030906090812070b0712050a060614070506011a07060204171009081c0615 75
    0x1c0b100a8410303020340d40d5540e00c140b020310541180f558241d0800c019103c041581c00d02c0c10711801ca0b0b07140000c1200c6e208140740c0c5a0b503121603888800003c15490114420504030007003d03258a41100f825402c604200d04040410700d084c2c40014241591001c023006d087d1115001400e007036811407180412903a44805040c041c4c00201c4916007154a00003258240074080c005480c0a080064800101d65046c4280144090745058007520b05204140c00600107954250051000b144242e907001001031411001130700c2401e15810580458200980700e03204650800250b8103029009064804961607200f01900c1070780c418002c0c00c0442341090208841c40506030480000c803805640d5150301b4445901e000404d50107038500082464100c1001004002c03040d841803c822129a0102890010242c0d180001c9902070b0380312885544510718186200f4006000c0b6201e01000e10b001400381740701c5951109404d11440035200211001600c00a40c002c4555100402074001210100074450b0160405451 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 568840035 1250 568838785 568838827
    0x215160206070f0e0d0606090221010807240c02040603060501140d0c0e040311160509070c170f2205041805060c07030507210f020d0c020f0f06 63
    0x94032075030000c40c58043c4941901000200f42e95901c00140c00c001c000c0103910001e4210036280300d6200c006c00303d4800313564801081c1003580d01d200004105400e4100402c0c80005a100002c6604600800c11516901419420601c803180061600d801510300040da018600080003a4000d0f18002c000b00400981d542b1450503612418564020f440128040144400c00c0800080241040c0d20042103140700400103981c000d48a8100390451095440c4064904407c2c50f10701012006003030030030015030404030f86454001e14689050710003480e007901d91010b1000104d510015a07500013903441c20311204107042d102442c00102242c0e10114410180b602c10160074022107205925000c010380c03041c02800741d00041103a002d409001d0550700c0000d145481d8016007010f80500104100d4000062010040c90848a0955003e6081c5080d1110001c10020f1041420070965110f19012010b0f950041260901c05504998020101c0f01c00703400310300d88480707600000303400c07580c00700b45e0790070100100200c0d8107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 568841285 1250 568840035 568840037
    0xa030306090f1811061e0301321509040906020c01052a070c0b070501020a030c02010605030c060c0106080715021c0504060c020a030b01090f050115050405060a021516 73
    0x40b0388071200345a0003c882441c50216155283c016003c00015100100c0b140c0301c030780040040b418005588034121903252001c50110728280b0020051101400300c0080d1400c045407040040e00090710010301d800444541c58038203105040b0045002810404c1c1401c4039a1598040c4c428000703404a450090f029400a907415601542888005242c030907401112036910750480a144044400d01e10701c1403665409448152848100402c0c0420854060f800501c0303401c2c415800180d9620903000e0080c101c0c0d1004041c142164100481000540c0d000155017031550401c6545555606c54040701071f0040c0180c0d40704400c0c038050701c040010101c088440711140c1303940700d07020b80781850085540c41c0b003503168000900c00850310600003400207a10880d040c0801351303c0a0010103036543c5940700e00c05a460240d000c92a8292582002c080d6041c182c00f805004180c42d500348031401c2d90490700648180150b0151038000d40002c100103000c14070802c0f00b5a41c000c04528000d1140c206078120442040c13860301d8101c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 568842535 1250 568841285 568841291
    0x1020c0f0f191506030819030c08060618031f090302100e122a0d0e040506060405010503040c0e01060906320c03090414100f080c01030b010309050a03030609 69
    0x50000724198150100803461000b094040e951044200f610804900d5103c2d030780c81102200107106000205182035450f4902205041001342c000d00361042c0380000303010080c1450912a8586a22041e034400c44921609000301030760f5600824a00005000c030300c03041202c000107848182c0303020b038010b20b80e0030301940c280c54a95100d04600c2c000d403902c40d008030189510140d0b4a103d03101120340580142c0054254100691082040b4071401540400b040c88460300a242c4500485401803900045801c2c04d403000d00407480c103100001d0880c0600d200c1c460500200000040c20032800d801418040c0c44001d16600c05540c650324000e1403880c16028210100c0d083d1506601280101c1e034034100034a0004001450143c4803080a95441d001600a43c0c03285c4428041c41200b40c1c0e580c09644e141003500d1035075910910b010641c3d0090609550703c0b99107030410018040c0145800441e42c0000f1090a0030049058080240120001d00b511640a0174900525241d80201580754026008036804040c040c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 568843785 1250 568842535 568842553
    0x209040f11040302090c0f03130201110f0601171207020603070c08070305070501110412020f15220e01031a1f06050a0e030f0d0c170c030d06060302130902180301020c0f 74
    0x21101c82e102e0011a50b01501f400c6c00040da24540c0c1c2041c0b6030080d441854400050842c640c5414a0501da40406404a402900060102542a802c016250380d0110000c1110440705004075180340b0848102034090040040046c825074042c202c05010309038003210440d541c05050030003c0035a0003403441120154200364160500e56548030645096804215441c0e10b000410b60802590740794040f9420342016941d5a0b5288000c420006414181d400d81c00658403c0f21072407080c00801103507082038500c40d51900051020400140812044410f040c051107080d8032070004915400c0c101c0c010380c1148880d05400852060352140103800c0960640d2180400b02c110741c010103072140e000c1d08106503254021240080113501c105401c241c080d0103940702110400c00064813258544c80600d0311585540009200e52140156100713280060540e07103000c60a04400e405042501800c0d03101d03103080e15402203410000c108081d03030b41c03104201001340215aa11a5004969141c0a4241d070782d902a025540308 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 568845035 1250 568843785 568843801
    0x5150a090506031b0702030f030301060c020f03150601050711040906060e0a06032612010e061003021312050c0904150609060308222c06041503060209040f1104030209 73
    0x10f5901884a000301100b500d44c0c80c002800f21a00700c00c3c8180d0f41032155190b801c402a00500055001c3e01241d41d078443c0b409528014080b0800508903500e000790300500711001d0740f001c038090198000c0c03801d103085599980c0c642031072508161501c13100380d0f00c6403510b0901010000740341c0c0003804031041e0711142078580d61011160806c076400d40c400a0132151302102880300d241c41c58080540e0348803000c4259810058801c084141c1084c09801030400a4092418050b491820302e9007000700ba1000d140035031514441070012548a030840c41080303049482c4d86040c004000051105003482c00001d0a2405640360900b8500640010303200916078030341c40c01c000450040b4680c0100c0341940e400600880ca040d01d5443c62034481c481164034204202580040420408000e102c2c000d079141c845c41d0040060200b01426100d03800c0c016100d2031040d417072701c50f100000b0100103d1b900b0449810403030051b201c051031004500542079003802000708501e41521402050703504005401601d00030744108000340e80d80c2003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 568846285 1250 568845035 568845037
    0x9010e150309060130030e06070b090714100c0b06010c050d09061b02030c0f0402040803030711073c260601060203120a0510090f02030405060c1e03060a05150a090506 73
    0x50510421080821008207000d41f016008203200940303900c0c50302900781c60780c214210381583c01a2254000c15410032282c4054241c100745180e0896543c0a850040c3e080508001c8981c50b00501c40242800003400d1603000d0050310b814242c001e0b065804600d0b9030301d0003c00c546c0a501402011510051403465490340803a03a0751400e030303400b40c010510401120100701e03041d0561302c01a81c1c015002c100c0032a480ccc0083c00030318000e0380c09071200480a20020380843c140902c0381c101800b44660015107018030141d4084d25062a100d8911201d01a18002d01c0312080080301d400c58100246016520540056a0240703100c1e0481343e9002d8034081c0c0d803102d0040384c40384644d1134800b10210031600481c0091400303074401a04170361820007400c089982c444101054aa41c0241e030b100007030b40031080006100e002e001c070b140e01441d4000d005150000c07a000c0c0780b01c0b86880c0c0101038000100440090019100e1410f44030151800502c0c10040e12031603000002603600004181002a024000c00100d60078044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 568847535 1250 568846285 568846349
    0x6040201270e0a060f030f0605011211010305060a08010c0906200c12010b09180d080405120d0b0307080f120301150302034b04050309010e1503090601 66
    0x5000d1220091a0010b000014a0050f0a1a500e10760700c000000b420000e12290000442c0f15034141c144940c1142408070031903205900c01082c429122042030000340f44801d007002c040e4000d090004068842d14041445910150072020066103005c1c0364610907070b00449160b0443d00240c0c0c4a155440758100700740c210b1903c91691080a40c80042c230122107140410940c8501401400002104200040080c0500e41c040d900301000491480008424030b0040c0490020040c841c20403503540c0c01c0c44e40ea040d0340c41c0c016100003451411b01041d0300700345a801d40c00502e400c103802000c640400740c50323039241d40e1640f8400c54120902e1150010300704020344d140b420349049038a48041c7c00c031400c2d90250f0540280d403004041c00441c1071600d186600d450007141b0a080042e030040f601c084550705070401c62607040e80c40102c0502144081c1e0401000030800001c85410650030308e00600c182c2404000b1940206284041e003200a0700030003000710740100094024100c035440d4041600403c41c204000107058101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 568848785 1250 568847535 568847597
    0x9060f0c0e153c0414040e0d0903170c070905060301051303080105040203150409150c0c0b01030204020a0903150b01171303081f0602030c061807060f050f030906040201 74
    0x10b1150070150030749044200e041035203409541035040f080080c0f141c100c0d0303000c0e03008800414900c410381d149a003841c2c411900c0102c0300d840101200b50015002400001e114400141850f0100034401d4280b10382e8020b031505115803d04603a5103948624160700076040c101d034842c1c007a41c80d1100084c0401140d50310005482d0705515400d00300d03401c18085c00702035030000b009041041c4007000050f41a4449201e21800d8500a1000e01c0038100c0040d2460150b034140001d40e820010010060f202103280c03e00700b04d0461758103c60050740c4000c0000c0954010200e42d00c05459010b08d420406002d5000c1c0e0808041d03480244d807110343d408031610134080341e0786040e03c0260310f4880c0110f4002c0002d00401c00d050300720b0061141004a01500034514402d03d4a80c2c02c0040182c1001c075402c03017410380803c0555000100f1307800301c41c40780c510303c520700d603682600b442003034100b0260a02d00b40b10a070117681220503c81c1c042800a03a40d1a040451550703c141c140e40890000303000305503c0d21a086510355a031018101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 568850035 1250 568848785 568848817
    0x180b100309020a031e0219060909091a0c1308011a0906030c030f0d02011a0d240912020c0102010b0306011517100608090307020d020409060f0c0e15 65
    0x120108400800034090200e0704401c2110010000c1000b9141207160b8091080c4a518400094414480070341d420f40c000c80d0445244100500c80242c0048020041e46c100280002c2ea20009080103440d84451484580c10700c2e000d2001c1c404620290340050803009070700d00c1641c070926640c0010074201d42074407500d25107002c105078003d0401d14020191503005178004040b2409100040300003410a4040c80d04a01198406e00380031714411740a0040c0e246031820078928004c07120780703000400d460b0030420100425481207418514280e200c0c0160a80c50910008000c201ea100c1511702040808481043e040141c4218841400d56610501401712418030181c0900010f900e050005140c24a84d00d0720b11082c042e80d1070307003004402480c0e29240d03c6480d404134210340507071400034050440b41014149080a8104103c00c0d000368455099110080d5815140010380002e04d05141c4c0007418810380041d07030241441c0680c9025580641e024240e584100d503403900c0f26111140e400752503c9032031068089140d07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 568851285 1250 568850035 568850059
    0x314040302030622050d02010c0906030e0a06200309030909010e070c0212150408040e0714040b031503010c0e0907030e0604110d0c091505010f080a0f020409060b04180b 74
    0x125100508002c000ca1038100c1389410481d42c41e10308000002ca26100140e41d940c032081c1c0c20301e9000540d403000306018282004503a0803682025194800c05501410064441c030714070025081d150031104041500c00c480503164244070740c1c42916540700d401c900c1d00c140c80443c004110f0380d600704d0109004016646541100d43c5a030740c240030543c0c1441c1d410040501500d041400e04007081100c45200741d200700082d80d99241001d0b0404c03520040a85002c0070000b02419501c10541c80c401200c06890b190007425440350f0f500b03003c140c1d0b1094080540b541550170803041581407504000d0780d00400c42c0c121082036160b550110210111005c410940859502a00c00b04012803214824458030b0940505805d5000c002516556101d0005602c4801020741d54034910b20300d090101e9002c80641001d19180c410b1810541c40200000000b03481705a02d42d03980c0c0c000d0100815194121030060000314030a00120340d4504505980c1c5d0842c1c410301d01100035080c8800b2000150b8480e00303000d010300502c0040000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 568852535 1250 568851285 568851301
    0x6080c03150105041e080d030c020d0305060f100201020304110f012a170a0210050c0334020f060604020a09120305130b1908070e01181a040303140403020306 69
    0x1c4441c1101a040c408204408680c540c032284800405426040c1102c01d40746c0341254451408800b400300404062070700001d0155250301080c50480181c0c07070300d404100f545851001840b100d003501245544407486103444d5000b160190091840f4901440600504510071021f1002c0781c9040400e0302d000801e25045601c4030001a40a40142419581000130444071991600041c40c0103c50b0000310b0310011500200305075041050718141307031a0038814410740c01d0560004565020161071140c1e400703103101280600d51541c1d80c15041180b400700c042003200020b0702c1e01948501200b80c100219024000004550341024001c03514175214654541000502d0480310380c101e14100031040381000310422911003501001400840900104084a51b40d030342da469011695090044102d0b041c40281020850f10580007009814078140030709101c1402d019901c2c09080c0001d2507001904c0c1000781c0b0108107405518070001c3c1058910a0f2201080a6902755003e03000d401503100003035255010b100000e07802 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 568853785 1250 568852535 568852561
    0xb03010c0908030a0c050f0a1a070e060d0b01020109240e03120a020c0a050d051206120d140705061819080913020c0f0a060f0b03060a090c17060103030906080c03 71
    0x5503008200b647c030140110100c50b42010140307441540d090141d144454118816407018035007003400c3e401c080c4e0640e0724400115145000e00c64045004c13981c0e4811142e0140d00039007007111203562040240291520390400c41d62280310502c607503001c40380b80011600f0b69050010448802000042030340301540e9642000340d020354415813039032240e8000d07030f1400c00c0003680800460444840710f850b102d448401c255640d0340552002044680310b1800000360021510000c03540c21060196480c0c141d404003020132050644e44500a4024458440c2e102040220303040b01c1074036003c03070030b12406039050402030000000020301440c40282924804000800241c90041c0501c0441c1c90816000350a1001c56070ba42405c08040e010b0320010f942200204204000ca1b503c1004007101e40a2800c20001d0945c8022030b54801c07004201c400441c0da00c210707144c180544030070348a0042040e4140100341074685001d0b80d4880d13000384411004034481c0c0c280031800310300424101c2c0c8111040302d01d583c15591070301581250 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 568855035 1250 568853785 568853807
    0x5130503090915060c0d0201390521060a05150a03180b04110f011b0305030606070516091802010804022106090c010e03030c0a0b0414010507030b03010c0908030a 71
    0x5807241403807880f0342584070207001e460000d071241c01400001c43c40315000303030a40d54810b402e441049002c1001d280828962400204d07610705200c0415080500d240c0123907107e110780d00702c01800d18090b40f1108240c04402d02000c0c4030381e030f040e10304000c0301d030751041400641034100000c048000c801b407000384401da00c641d00c0b4011a41d6652034565110800f80c64080780c19105403801d075204440002042402d04200c48000070034442807825008010b440c0d00f0401c05d141e0760300001010050008003188030350341c400066030703540c3d80c205055400c44001940030340d185040610aa1115a060444d20444c3d4401740f2044540107806031240c0a0559440d401c00484a03050b0f10001d84410240b020341c10110001c0009510840a030302c01003001c0380110000ad40110020014144a980100070505000c03038041080b07400c02e940146960fa5a48440c540648241d0f5054100d6408d503190004102d94150b2680042182c540706400801148007000d0085844512600450603943d00c10010b8590720781c407680001c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 568856285 1250 568855035 568855051
    0x307080325030306150f020d02060609270714090a0e0a0305031806040303200414090705160501050a0609051512010e0714090c0c0601030809220501030501051305030909 74
    0x46041d05c805403400700e0076480380104009a2150400b1000640401510700d01c542a400141707090315100300007999003440204100c00c241b0b15982d4403944502290b00c80001d0760700341801d41d6542c5440e83c0413281c800610309041c610804071034000ca400505070f442a0710718002c1c020003800c0345401c03c4d1030030b564651015020030107120941c0c500081e80c1030180096409644a41e40101d03410880e00c8a4640905440d0411072070342d00304110400207611144800380d80305c081520018440d95500c20252580d0098400e51507042e08010005410401b0660080380b1540d00030700c08000301d540b10042d171401c0318002c56034000b9465000280c0016407524041c0032086890410006c9510b8624620403130400c0c6080e800344400390f120b000700380c1d400d1070a90344e902d5014134040c903403e0070259100c0c4081e1391004180b1014180f004002124583d94880c80c8035152078514519100c110100b100c40464000c03c024070065030903500e02804112089486807008400980000c001d504000c1c034842040340f02d010103084c682c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 568857535 1250 568856285 568856291
    0x1704080d0203040c091d010b2209080702061c11040501020316020a0b04080106030b090c01020d0e0114030c070627060f020405030609030c150f01090f1d030903070803250303 76
    0x1d04a10f083c0151404200901040c0c0d00d40032100b8100d81c03c2d210000740d514070840c410f0308203070320150410000383c000102c42400420303031075512f0a04100340d11584402035080240050094101c41450700105d0782d00d140b46004104800b045a086602c50203140902070040c4c004008d040d49000c2100b014044890005110500329651552868860307403166201e030075643d442d41d00400c14884000a142c5d400140b01028100592680000030b46030344204071002300f4402005004003082e48aa486041c0c0040682c11803541d0b81403000c0025003a4100c40c400f2034440b0f081c07034284030921011070920000794644030000a07400b10b880d503c110103000641f4a01050726400e10002a0a6800300710b0203000d4082d40c40515a6112404503507810300741014081d00354005c04c00305001641a1294032241103c0c914400040d504090301c0c2d5041c0504240e000c00190245410000d40c2c040b1004801010300c904e04400b204c040319560920640c83c3c0c0956049440b0075040999841ca02d145420800e4040e40d210f8a800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 568858785 1250 568857535 568857539
    0x602060907030c032a2702030103121214130b1b0409020a140406050a080f011805040203010906060608100f050306131a04210c0f0816050f030a1704080d0203040c 71
    0x81145840d800399125005542c0382e440c1320040071b0341c544028145001c1c19841c5604507120b00103c0080300608004000d50489900f4000c4800c0e4408003404441051140e02802c03c859100b0f98440010015620415a040450390a44000b00145142c1400000513801d280c903041202c4029044a8440c07001d0045e41039022a03102e0701a401072011f4003183d02e80130340711002c1640040440e980202150220040d1000602620341409590030040c018880c011410340c0d514400b04e4094206806d00804150410502149003500400c41034445c034000038001580c00d0351003951181c0d0a80d90702c0340715019004170001c504521954000c464446008020500e035205440c2c940d062547e004136019503e0011064908014030014582e48a180c2440d00d0007907015143c0381c955445a0803807010040000000050405403a000302159a4240e504035003610150b61284010940303030b5101200c03440025211001000c517010004001602554011024600f07086410402d00025032001c4c0c41981d202d4051040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 568860035 1250 568858785 568858853
    0x311030904020d06081e33040609030e0328080f0d0b0109062a210e040c09030510020304030314070203070b0f0c0906160206130602060907030c03 64
    0x50100059031035001588900d428806400c1c826036010741c0044104800f40306c003460100182d05008801204182450b404c2114650341d0584001c0300c24490100700501000b0078070049511204200380207464614842034042d082589610464005190020281c40501192081d558580c0d40e0540300f40c0c0100e20300500c01c0e031841c3c0650840c65912081d5a21000c60b8041941d00c007042000410581c04d000c8901c260351a1840400c12080c1c180c6543e444203640743c0340c28400c0480500a0340c080100300342940020000e0000e2000209000138dc0c00303181030603d4440900e01c00d00766041101d8000029083d9101460000d034044c0d80060025030405841c0c001004001c400801302900a000700c0e0000e6680e10070300d2400010303022009200c64041d00c041001c110610224204551714400105c0d90f143c0d41e004218490308420100180c080c0d042003001c0b610360394110340f01c1c40d41e00c1a40c0c1d40b40c00300c1d801566111003443d43c85645000080451400c15400c00c00220724085c83c0750300080010038034041401101c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 568861285 1250 568860035 568860037
    0x415051e0d020d1209060512011e17030405010e030a080a0c03050c0d08070201050a1a04020d060b030a14100b0904020c2407030c0513120c090f05040b06010318031103090402 76
    0x343c16182661001d5034001c0382500080c100d0700a1801342040c60070308102610f10800c4050501c60140905000d000d03904000300d0800d03140000e04004495100724008400d1103a44c2d0741c00501031140843d8038504003c5032480e000904ca2601790b0310208139454545140000c9400c441d45020403001e114080c003024072800f030f0034001c244500a155451010130300d01048001c0c2551405020865000e241003091510a0b02c00600381c184070400740c030050f90780c40d034145a1000501044c0d2104601d020044280311030945640c10412902c04810101203950b1540d83c0e00700e52982c03c81c07041b003440340c0c010062201c4600306500a4072102c96003405540113002e644400146083c8890140304a1b69620020004101e4240c031403c104450302d0300d40039040040014503100c2400c1c96000b14040048156104003c00900e500d0a4010b4101250288051501c6010103000761105035002c84240d110304d00040c60952292003030000d50b22071450507070000303001918103aa030520507049051440c00f0401c115045616180 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 568862535 1250 568861285 568861309
    0x30f030e01051621030c020a02150705100507020d051201030b100909030e04060801060803120a0e0a1a06040b0105030406090203030c0109050a021008060603180a120e0415051e0d02 79
    0x240100c100301c0f1031003540f0241c0400c1112134043c586400300100e1091750000d8040c2c0c0d1164142d480b4442d403810403042143d03034010504001d00d6032013401d2142002c00394580100d03000754219022681c45098015060b603060051074503d5000c030081000410102d0744c856511a0451000c4046250321621481c42d60241d90303032108140e0100e1b040400104044c203007881224000e2100000030014282003480280d142d10528424442c2c6090400c0440c5100c4441e03404075800380b043c40c0880f41510240d107001820303052055035040b0543c174494009912800c02d40210181c2c680140e41751840c60361240c0d9650004c102000090b40c140c030040c86602081340c000d2040f04802030043c00109100000ca1041052402603416140c04220060082c03082c035803203079410342e900814940c03900014400603c508500c0c1105010025007080e14007048a032149402c41340a0f49170103004e49003404880304a120a4440b44c043c0c2c8602500560484552849900440300400180750010f09902411400e900081d8172181d0003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 568863785 1250 568862535 568862543
    0x50603090a03180f030f1109010609030312020405060f1b1006050307080a050312130c060306080c030606060a0309170f03180a1109060126011707030f030e010516 71
    0x1c804424160020342c00001d4404880101c0f0b00c05050400f0074100d10310300e11004103158003000c8044100920030307446104181000d001241690303940c283c0104000100e100c01e802040c0721065070080080680211030607502c0281c202d901e04107190f041d0001d164040b040030030b030042c0c43e92000084034906000043d40d084480c580821920b042004042c10308015600098a40e448140d124002036030201c02d071129a61011541040d41d0360b0f0045648501504490042524100d000040b40d0581c140d84100b09640608040b0f5100080200501d507032000140d038241e622507024808000c0151098000410a91152143d480001c401091145041e00091020309031404007008000a031000d030020001c1c0c82c6040d0300240300310242030b150a013407008041003042c01440d4402c00a02203900507a15803504289111121115041a642c03801c0107c000380220780c61440b4016030040a401c0025910f0192908040700c008005981e980039140e4016542c5450306115090001c0e600c01c0e400040044106801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 568865035 1250 568863785 568863793
    0x70b07030e150115050705070e040b0403031d0a12090f080715080f06040213120c03030201060f0501021209030127020103060b040e0a0f110a031b020604030f1805060309 74
    0x81e18510078100100944403841210b4110010802e0104070040d40c081c0440c2403d2980e0b0742d500500380581403140c1500140201c14404050004000201c55282d103d280a59402c00c0004049243c51411240b869007852140d8003003d00c40000c21000124811701c4005800c0040d0826501c0300081540c80c0c150740006016000a242005031068401040801d00c1551811013400d00c0c0c000046001c20700701038001400f60340d0104050b005520400c980c100500b1a07a10035110b1041c06240008040c02d05000031001542441c100181050b041c204e900c042e624140c01070300d100009084105119000000c05075410b44d290510540c02102e0400100c0d00c0010140003161114414000541640c40319804200184400c0008004220603111181e0304103c102c5800300d0424404c081c0710004c0c11141c0d003401402c1000040040750941c00d5071040340e20810901030a06410348011069883e000c0855014000c01c0d0380300180302201d403240c1c1c05603103010b4210b40201180b0713458074041000e135001145c2020460348 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 568866285 1250 568865035 568865051
    0xc0d08040c080606090403030b131409010e0714120a02180115090f030b100314100b0319021504080d0e1306050307051c0b0705030103021c0b0c0f070b0703 68
    0x10700c10400c0c4050a150001000c80c0d0078a1000300341502c0c4003d10107004c060f501d00d9801615a1251600500202e0009090001041484070403400c40015100e00d4015803030089001d00d003220100d40c0c181202e0203010640310120052040c805840b00b9246404041e0003400c80c400b00590f00c0c80d42039041100301528600c0d0035814214000a2144e03601c100c2c0c1c040c041540310030003000b1803980c0c40c1c07401d40713901007290291501e44c0b04000880000a800050455030108611400700d0740008440c0b081c90b04800e005d2100b200c01c0c8081c1601c2e00d4002c5000c0083c034108501a0026040c400d4860100c1e09c1101880740c40c213640c5d1002c840c1040c80160300c88000a06000c40703200245444d0440101c4200042c101f0001035140c040041ea4804213482190b005003014000418155a40c910b4817050781e401c69200c000d20310748031000800039030003400200d10030400c01000800c00c542c01295907007913607400301041510b40ca03031400709001500b1070740110304130710b100700f1000d000981c45420860003000c0c10348000c02c10388 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 568867535 1250 568866285 568866293
    0x702040501091d0a050604350a0314100b03190c0c02010906020d020d030c0203040f0306050a05011a090f0f06070f0c0b0f090420120103020108060901080c13020c0d0804 74
    0x8508520b00c0685940070b00130728030100c0e4002c0303266500700e0343c440c102d000030856600225118503c4412030182c10078030b0004000320740c881140105444141035404000020780c0311010b10211070103803002d101d00030341101c05000c02c0e881d10b0011030f00900c2c000d01c04803c100100f00c1da503090701c003040100c42c0042c103e5082e8008658010034404090700441c00a00010100440e0003581c0d40c1c0d8002402d8201600c405000d994a0700a000f11400303000040e207001c0d040741e01c904100003e010705036100720000d842c2c000005602070305040300030341c01c0f01040006840d00a00d481048403e001405400d0361248034030007115203035503d01c0300814596100390103850341c101d05801c01d07200e500f00301c1c1d2012100403010803403032001ca20900216100c3e14000c440000da290204080c0200d40c1070600040500c0c11000103038000c60341174107a50207040b41d10036038032040c459441c5003c0c40aa01801c0c40351421b16030081c00c0c04000d6252480010382d0701d0101076070050400c0d84c0000680d20b07028070500c807040880d00310000d01080c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 568868785 1250 568867535 568867571
    0xf090f0604120b0112020306041115040b04080607080c1b1e010903030b0103020a0207261f2412060905030f04080c0a03110d05010f050c0d0b030c0108070c08070204050109 75
    0x400400017100015480c035000300c0c0c0c9454004200070028444c02d81070342c00565801c00c505946400b1158401d03221340d01c0d25080982071703200d80164038030340c8110400203604900c5032408510842c480c1e403503a17041281001424400100345510483d04e030240a88030f0a1034101400a01c4080070507600124120400b170078054100c900c2a0102c40c101801003050740740540d000101e100c221000c001c0307500054060000442c40e900f0000800c001d042c0a1a80200d100405029040c0c1c0c1c04854040208217007a207901d031007010003051620226691103062420000340952078202c0c0ca64a014200100d0080350556030b15056502413041007207850300104051055050400c5004450002a40e84400d0103041d070325072566061050700e000f41704061000e48101081000e4100540103000074000744498105442000400d40183c0c12a003172403440d0a401c1d004c20305d40085c80485441040e160440b440c0c82d18281101c8985100700d00352031a51003008202c00507140c41c03003050700074a0341c00f5002400c80c018400300c1c007907 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 568870035 1250 568868785 568868789
    0x506071101170f0c07060905030c07050306011e03030e19030c080c09190c021609140601080708060f0411190e0a06050301090c1b0c03020a08120f090f0604120b01 71
    0x6510942d100b00841c49007902d0781079811880454031541c8640343c62400700c003e00080c800080284c000450b0f218982c0c0070000d225000d80c1c0c0114103032403440e0780710880d4070b10844284070112240c1d004600c041000c0380c0594039150142201900450305081c419020b448004d001d036208440a559500d0708000c4c0c2d14050204401e1800210f40d04511800c1503d140300f02d44a07078000c88d548080c0e5420701c03503400c40e00030040006c0010300c400c500480b1030340d240315400042c180088200c448060481c0080c80e150710030840c0502c01d038a10303240d4249030340340c0d2014408001066401c3c103030400ea0f96034802140f001800082c045112081401e0000c0c11010382c1c00814034100d15001902070058a0000d2246036040b00903079042d2981c5440c0081d200c001c0860445010481da80c0003802c0c840e0040c460000c1c0505c1501c614180d900964242d5030703866a604d1556500c0141015041001c1e00030310400ca00304001c038006000b207940c01050725141a1007000000c2c542d40c41603100850b4090020900801c225280803185c0c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 568871285 1250 568870035 568870067
    0x180607150501120c0302130212010803180409020102150402013f02120c0a0c0f03030f1401081e0f0d080103050f03030f04030302030a090602031e13030519090506071101 74
    0x400c03409a610084d0505890000038410007103a1a00004446a541a2200c58070f50740b10328a15545e40e89102926071344004004071230f41100045c2070440c0c1c2003900414040c15810b90045c00c0e0001090540100c02d440540103c0c10016118203807401c501d001c0d585204403560904e0200709ea12405032000201500441070002824018403000e40d000d040c9115140c0d205402e50501c0380e4902107a5003c40d80c0c0c0305100c000500700c41c81d40620005050307240c0d100e050307002030380d0034200590365103070508178840d5109103d44c01c810340c420b04e44003290310301520310080502102c3c1b00302c1c0c541003c003910341800c000d441c02821002600b180c00410a110040040b2a00e03051503070040c501c3c5044c48000440b07607200c01400030b02816000004500826131603072100c6c05042d0000002c40d103a040c03264030643c6000440f81c50582051811780403c0c104e0a928200c0d1007255810707202c244c0fa01e03d910a6446c00e5460f4042c144085c07001d02c807000a40d40d2240da0080c1609441041d00700c41d41558600090a2000d8003c1c00c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 568872535 1250 568871285 568871309
    0x90f010303020303040803070504090216021e1003090201110d0e031504030e09040201020a0b0408031e0c03040204051012050a02010f110d12180b0f0105010512070302180607150501 79
    0x80401c2e00401183c0c0c00c65046844c05569643da80300640b10b034840c0c0da00200c0910702c001118201da0241d81d40035400c00c0d01c221204002000e403400c2c550481c490107400294401c140e40c80d00f02586010340c1c0b01110491041c180a803040043e010301c0c5040a00f442400d80106140b051038500600c1c05001002c41288420068149800d068400501513506252601c6c05800c1d4500801e0540e070081200c140040d501000043c2645080d1402d91210707041a10340329562003482205200c520700094210b8403d01403c3c0d030507815680c49030200700180c01c0c06018210341c40407230980810003c0c0a81495030701280150020411000c45100040986144805410420a1000c6055890800440e4004100d2103a14040d18901c211542100050003802040c0c032a400410741c0301020005607680c814401c3c00042c0c246a000ea0b41e5a0040d94180f046074141915507000000045c0d44500a43c090030040210980140d401c031001d2001c40d68a0340100c00503505050007150081d004840c40c0546030140c0000c640b80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 568873785 1250 568872535 568872539
    0x6020706080412080403140304030905010810080604082512080c0301051c2121050408040e090c0a06050d1d0a080d02090d140705150702061308030f09090f01 69
    0x198040340f01002100104041440440c00f0705100d0928807081d41d1071060956540d043c03034a40641500b03018072032180421034800000b0419a0710030400b46c00c5070908000707040b00340d959655580c42540400052108903440c9906142c0080710415481001441050404840c3c0a0381002074055032005024640c94002003006109c20b8449840340314912015448400580c0414682016030703c1c00041e191245401d01c0300709009081d444805c0301440c0f00c40c0301100c151a0080c81c034503826140125000ba04820040004006192107002111740c000c00c4003080c1c50b5003d140c10002100703a6255071010300041c10201c0d005004110350700c101d401104c8561080c4800210802c095038403982c0841000d081940045400080085641c0440d60310319002000308101160764544420400c1a01030800107030300c1707507480100d000d04100b02e4900300c008034500810f003406000e50030013e0700d52000b060014070030840034000640700b400f0806031402c0350f049400242c640000c01e003405001c140c01042c00c01140142801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 568875035 1250 568873785 568873793
    0xa0c090501140f031002031003110607170a020a0203030406120b03010b012a02030a05060118060b041a090a17010e1507030c140403052415010809010b0613060207060804 74
    0x601204a5068030b1a100f100c2180002a01340180500e03404600c034000010040f1208107090f11f0000e0701d10a84103c41c001300ea4034144810750190200040c0300c0083c51031b244001d968540050b0229803082c0c0704440b009802603000c01d0464019030f00c51002b02c1e014841e21141c001c0d26019410f00304105078020040b100030381c0c0c0002d0400b03001c2000384104003494504000c075a4603690b40081150380140c21198408054170340300da80c0320303000d1040608074455039013801c0d00c1d03a07007a0107140116030111130898240f50503c00302c180124600d04115070b22400c20080181c081d00d40c90402401004500e040c0013405440d8540b490a4a011011014190b04040d18000b82200a0304400b038011480d4540000c3c0c20070140015240b40b0054200055a014003150000070880c00046809401c01090959101500d40e5400b41c0c01d006000d5820a111078200c1780d03c1c1500b940300c0c5031166400310380c040c000709440b8080f001243c05540031202c0810f84c0c0a86460621800c0d4041213960010301a80ca004000b514154032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 568876285 1250 568875035 568875059
    0x120c0c12031324020114060f010903050a05030c0d170f06060408010e010501030c06030207020109031b080609031309060e0f09120a05180a0308040e25080709050a0803220305010204080a0c090501 85
    0x101148c0315a9007001120840e901c150030481c061a40310301203880b40345030703410416980e8001681420051156102d0600142d224001c0d1144014100c8a0311045817500050550311100c01040c10750056803d1000042a44090244052a0007628000100c9504504014004180d26040f56060600402000005036480240001100c1e081104001e55450301c03078140346555103581c00715400340f0900b8140b0900720000b00c020406184124a8162010750350060f000a580c0948514403104045000090b4180650401c0320f41c1320090341c1c16074001c12071807020303140305400030a12400010004a1001100603580d00402c4007210102d608042062456075503d996201301d00a910441d8074620114a00c22088070b03054039200c1e0800c4200740c000c24a440d0082c100001101c291340020700f1004005828140008460155496070014600d402e8500701c0705c0e52610300c650310f1094450410700c40000425402e01c050409420002c015080c1e0314503d04003401c2081054005401d581d03c0d240c010031441d00924 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 568877535 1250 568876285 568876291
    0x15040e06091810021c060b21060a06030b011710091512030c03050904060b091c151505060f071a0c18061201090608120c0c12031324020114 61
    0x140076a40c5c3e110300540c19120f10441c400e02468a060120200c0c0742e142d060050100740070744441400e4882140d85100c40784044c2900c46a4022000303030802d000b41c91081d00170202c1540c060404c20005260000d03800061030044442d111155010750040c0041030890292442c001444403540400f80d00301010a9584c90241900a040c0040200307500100b60044040c8e540c0120000c00c01c02c4026555419a0004c1d4010448a40304803a00610312034020040e0707185144140e0440344501ea00310707490010344003c2c90140114050401400760000b42542ea4000902d800c021244000b5107500c09464102030090312040c5629a841c083c408022080b1302680580c1e41714000070302690090040d000215072280b16066810301480f181c0c0002094155158200308200c524100032600d00d600d10000094440c00746202116146d0003200c0ca004a1386064451494001120025245440410a039001c2094407039440201008001801e007010169038024100c0c1d0401140000c0c400c5006004920110b00401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 568878785 1250 568877535 568877563
    0x19150605070c0e010b0403021f1d060708030406090209070f052b0c031a03030f090f01020304080613051e0d0315050d08070c050a0e010b070215040e060918 68
    0x204001c1c061007080310140004140c000b12124203940c44600c02c0030340780d000b4042a4050494201c4e0340a544c0340d02c0704841070491455490f48850201e40b41030b00c3d54520603c500a900590501040f0007080b050001503000790300c20719001039134044da0b105000d420310300100404103000c3c55032003041100f5004012500301c004460b29010070003100000c900003110202000050961500c01c50080241d09588151a0032100c01c0303205860a620758101a83c1e84100b52200c105444184410313a41420300c040c50034170424050058900f4151504195481c0c444119400002c0c2c0d050403941e5000e10405104500352a24881c0c4107101c000805800190b80e040030b0003801d0101907071000400c02d107070052907860002e041c0003841300790315160324102400c2c1600240fa0680d107645401d100068940307025a2480c0413950b14090701c00c426071034601d003810541c21006007603801400c903e2002524495050007400070740140180c44d2050b007002028407505100c002c3c0200c04606a0382c101e01341384000000c1c0d1b400e085da44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 568880035 1250 568878785 568878787
    0x90c06120603030403060912180b0405040b030102040e04030c0c08070e13051c090e0f060f0603073c110618120a0f020f07060c060f091202010519150605 67
    0x18903012a18504c200e600141c0160b10b0403195004000030300c86403241c9101c1a98030b860141003214407510340d400c1c0502c9404580c94042004008d2824140c00203000c40c200100014205982c1c0c0754903030344015040301c040300020301d0b0341d000d4420402400034440c06042810020070101d4113080ca80174030fa25015190382e2803c20810302c444108142040080d04840b03c0c8131070000c2d0301e000003001070081c40041c01001d003500741c28000200c1d44108800b4941c42214000d003204090203641003401282d80c40500340c4400c000005418030713401c4c069241080302028072428072440032110000000804a2110350100030001d1034201d881d8006c1000030040d4100001d4000c81740070842c0c03000100d1a285140316107804000001c210003804c2a0080c43c0c3c2c1d038900d0361036001e8071346a81400040340c0d00c404450082c40003154080902c400416290b0b030044030804910b0070005001219501c420310040d0525081200607915442004101d0f9252005d40b0942c54010703c091000c10000c82d1151203803030841c0502e40070088 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 568881285 1250 568880035 568880041
    0x1080109020d0b101e03150605070302032704050901051b09010e0904050736020d0902030a05070f09140115140c07080616021504050c0310050f090c0612 67
    0x1c0d40c1c1c00a407128000034100444c00c1c0c00c610340503148102040c0c024610034030720101c41c1100c2c0c0c02805810035608464280304401c90605400391103e0b04002000da04600c0240a40c843d10f280140b5551916000582e45182e801a0310007040140c40000381198940c3c0d0416061211b41003001d14181c00760b9203c41032040d203c4c90080c0c0100c65560800c0c0d40154040300d001c0230710081c008081600701c2540c0c000d4001c4a50b128050078030005c0e03090449501c6807031019180800900300c02990243c041e40703641c6200454200f005400080c075011662006aa00360845502082100540c0c8440700041080e80d6060090301c12002141c4040c40051260305941c2028101c1101485d128030070b0327415803504100c0f4540d120424145210794035030580c0586c05a42c4284004034101c0840c0030ba4800034807490b54014444846540449854400003800441d480e10a4009130304095405010351511480b685000062514040349090000b041c0581400340903007045034140758648480341100d40040c0010364882c1d46031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 568882535 1250 568881285 568881307
    0x5040506093609010b010519080a0b06030718231203041205030403140c060a20030a020d0306151707090801020a050301050102010f151809210f09050108010902 70
    0x1c202d40001c00307449501c0c202d80240780c2e9000007440c1d0090300d030030000704840c40ca6007005690b01d10410010003034a50718004400401481805601e42c4440206000314403003442c0b8002c610107800503118107000c15025841030031008005812440200061b0b0750200864038241c05800da0200b0003ca001d002342524090300b941c81d00d0400440e00186103090551031400058245580c880e0404d000440740c0290111622800143c0001c0d150740e0100028455890000c0402080e01d440000342e1503606000481c20420221820031b1029007050305503900030780b0303030b0005400d001021226190010903d0090303010f04825850391102c0a00030600448601a08a45900c20190741e0740001ea440034071551b000041ea0b803802035024001d18100c40007030f002400000e0080324007909807507001d036000d44000700c038a00400011030644800b00540c10386e040300040c4d40c0d1454840512014009038000c2081d410b416104c11709580c00003c41c0c401400d41e2414580407801c00000801d000c030184504501320313402007640160710b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 568883785 1250 568882535 568882579
    0x31e04030909020c0c090720070b161a07050306040b011701330e1e09040209060402070606120b06090408190519210c0e06030901060f06080f070504050609 68
    0x110f4028003070119071410f0540186100c40c10004004500808d1542078140140040c0d64401d5414040c180c60600119106040c2c0050b0280c500707035140750035540c045030600031201029009007182e5035550344d2481c01c1800d20042d00d10303442005042012049411003e02c0301610040d05459038a881c28154180b03001d07100204900020150b03010740d0303071440710740e41d1aa042060f54911800584404030001703c01100c00c40c220000d0205c4130b8006505400050061920b01059a40030200500c014109a0755803034100484419410200c03042d050802100180404405020740c4040700719202c5103146808d0752810394500503820002240f030b254004034141d143c02802130710560b0015920f0780301850401c0200424107031070441b1580d002c41205151100700505401036880c0c040b0b140d2501104140780714103200706e43d40001c100c074000795038450b0301049602c3c00302c1e02800142100c1d42d44100500301003801c040201c00c050514400e00004110800194807002d06840d1300700301c01c031031071040580404203000340 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 568884892 1107 568883785 568883803
    0x1050115020d0c05031303151d10200a050306040c03110412140303191a0f010c052d15100b160512031e04030909020c 52
    0x2106024104440740f0364410b00c00c1300d2900302c03203000074100700d400c54000301d0380002003440e240720142c080d024800500b400c555101610b4104d1035a200d549181c0711442205603900c03260101d680340c10391040e090302c55011261660380c036a21404010b00d16801142c80d2803140d40351517034800c0294400d12480c1040700b8281d070403500d45820010707050100e12203404100c030300c140c9000703000f0304400c001d002841c02131064000c5001084400100c8805a4944040b06010b4515290440302c02ea61a9411600c2020080c20141c024a20358100b8600704102c105100062030302e44150040f54a240c810384031800d00d0361505480c1c0700319002800000b0700c1000e4981250698031001e003031041f0520301000305146e1102c2e4400700c414040580d6031a00301100c100381800d9640021080002e00032003039015a94921000b11a00114541690050542d10081c014141100d40c04980c558000b0410000c00c04 = true := by decide +kernel

theorem cover : BRFrame.Cov 568705035 568884892 := by
  have h0 := BRFrame.cov_init 568705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 568705035 ≤ n) (h2 : n < 568884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
