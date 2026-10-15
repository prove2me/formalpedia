-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4651
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:18:04.682983+00:00
-- url     : https://prove2.me/submissions/15c77ff7-26d1-43bc-b150-5cd75c861477

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 836330935 ≤ n < 836510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 836332185 1250 836330935 836330947
    0x30c080309120720040e0d030c03020d0f0e01060806040507030f03020705090901051009020408070b07020a5603040609050d020d030f050708040206030a091a0601120915020d11 77
    0x1402d840181c8048404800301c801d145030510781410302a003030b08806d00d100601282441114241c0141000c1880541090b42c200420038020020748030300b82c00c220851000088090b04a02142c3c05c65030b194002081c06e91061003080009100000c45106aa0780018804501144e03440d0a80c50f20b1400c0d0000c9600c40350300b1080080c0c8041c1580403074410b25103c8090030009990705405000c0b032081c3c1c0030304000c642002d038080c01072524070f900506da1148050041009039613961092004085030341c40a941002c2403040100b40344441031440c80c024094071440b490f8100c0d0035005030b4200100d0444181000c54040001402d1108650001e0103e035001810f07550000590f0304020b45400c0103200113030109180159003100c08200c2d210b014031840c0345461300c68444d1a02d0302005135942000346400c980c981c80f0701c3c11100242c1241c1082c08100303960103552580342000800941041a0000020b4106142c840604c0215003410802901c9041030000141d81e03640f1091803901418801c541501c40716000200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 836333435 1250 836332185 836332193
    0x813080d110c010f08070f12020721110303040f0f0c0303021c02151807090e0114061e04020a0306120b010302120f0c0114120403120b01020109030c0803091207 70
    0xc1d8038000c101c444261a851400b0500643c2c010000114020001d02032000151045000340034074680c1880310b080000701c4494114041c400daa025400031151307a42c1c003012056101e92044d44030104001c0a0074400003140140b072117251f5a003c000c10151074003e07102c0324039081c0b200d1403210850a60b001492131034a60b03120705001c0d5444007101181d10b103142d820004208001c6c13000c41c01c2602c108043d00c040324191501001c15000e8004000342d00241c2c0910a400641810b041c0f0440c122411810000301d02c403003011180c0c43e004240242079600640c840781c82c400251251088280b00c031001143c0060300c0d441909021001400150000c00b51003081410030818000b10404240c101c83c0b0842c0c801318600b0101070242e1300c42c000c00039603445130780c0705000c51000c80d800344080582e4814201001420a800e1050400c1000b00a0360190003041a1f0950f90300e04c03001134052210900400c0c0020b10640c1456540141781ca90540c902a00d010740c00b0002c28400001030100c0407231101d0245940da20b444640c20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 836334685 1250 836333435 836333447
    0x61306021e07031424061c0f0201031a0307090e01180309060c0201050d1406030c0102210c0f070305030d0c021c031a10020c0f19030813080d 62
    0x2458025100d200495295030503201070801901e100700c400340c02e0700d074030316981c44803075420008520003580183c40300111901070000700075514034421448a5541c4c1044028440390352050303800c06224064240b912400f04100c103031080300450742840c000806411038040450301a542140407075240c080c80c800080d00306519002014000b080d04002c116034096030003001079155400f08001c010503030b109800c101031401104010210703070040c1490341c0340c00e140782800c004a61044245c2e8410307030701d12000e208240c20108405005c2042c00c0c001001903120700c1003010f03034203113141940c0e032a001e20000f030b1101140018051070754120145805c4454180e20b81c074000c2e4903a080f200c90300b041c103450f16040000c0725100041c0c2c10306500d032131105440c01032910b181c11409061a0325a01c4101d0340c82c2e81410b4017648070f030000c042d021380880c0d010303040e0505082d00b00101d003201030050718404c100c001418a00400050b002c1011203910100542c0d8414081c40d00055104003503018243c28007482003045000740e0055 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 836335935 1250 836334685 836334689
    0x70210060612050c03280b03070f032102100b1f0f080a05040b0601030b21161a0d0b0a0801060303050405180915060d1e030201050c0f0f0a0504050613 66
    0x20a02c400c0c0d86603070ba0901d460004440d01840740007850140820381503807850b0740586e0240c01d5408520211100c020916101c0d4aa1044a0034134960904100f400f0110035448448144480941c3e240303120800003d41d1400b5880d1620f4007240c0e10461040b16681d82042040e400007144d803040c45030080160094500c0002d85070510102c0d00d49400680d00c283c1d6445054440c0da4800d510384c0306a1260b100460040c8011040e0a03004080e11100c411601c181009801001740d50704018002010074220164404885911040000074900c1a01c8003807500b007070540b4103803030f00504001003805c4a08002181010154030003019946080c00c080280f550010007481962000e551300401000e1603030311700c15203450489103e41c45810540942805400d01050150002001055542602c40d60348840403c0800e088850118100e00603190302050380a0080682c803e1109451301d092140a00c6506014810708101640440c8001821750701d0a006a042d24060300001d070070b9a84614510800030f000d00614 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 836337185 1250 836335935 836335967
    0x915031029030703020c0f0607110c0a05131d0303101202090a0906151806080105220c0b0706090203060603030301120b0c04030501090f11180f0702100606 68
    0xc0d1a0115150400051000031814003402000c511030340014854000d0b040034081c0340c03c01d0b40800c00006c060904019903111149040b001d420b03a41031401c03002e44070b40e0302064800c5060b0840c2c04800803e0380c1d0380341c00c0012184261a61a0b00c00100c80841005252201280c001800c41c1901030211240001c0610320981458070000845600c0303146034100086004ca00941c8841e1060000f4004001d43d0880c1110504c0385402141c0407000480741209002d1540024610300b8001006890303840e45805038100505c0340718000c01541c00e0000c4d00300035081261400d00a5400744810100030000001d43c010000c0c1840000b058a8a4040c507084c0050a03103102e041c3e200388180408144149400300440e8101c07000a481040e50b5045035403031201c000d000814483d080e540502000001c40e6081c056200400c0c860528900c0f24039080c030346050300c4400c2c0c100040c06080c50600800082c0b81e003141d1540c100c400280f40a40d01d90394000220700d81155211f11410460802c140081c45070381012445a0003e80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 836338435 1250 836337185 836337211
    0x9091b0509211e121804090204050a0906050a020f0f07050304050306010e240901051507120c1406070e0105160f081c0e1e151311010230091503 63
    0x600e64a440e550b02d10501d021401200c00c0103e2800020f000618203d114001b404c045400b03000c94000804607901100c806120645030107007c01040041d100c1c2543c40b004804003182412903240380c009140c0140068481d80c1d0100055071130a0080800a66005090080481b40c866031280c0c103003504070000b550010030241000090401c09112029496009040030341b803106568070704001c2001c03045180b9000c2090480410100300032482101032525000301903200d091020304285881c02d01074650760144100d907000030007481415544800b025680380024a800ca454014012a0b440101c400060080800515140c5c80d0100114170b00501400d40e08282103003200c042000052044c2c4000b0501c5003500e03000502d5007140c000c0c0c0d0312826079690041d00121800040521400c52036180107035040403042c54100211030030000090101d400e007080a1014200d401c8400e0580e0030f1850300c0d28180000d5185050b88101a180d01c541524041d00c8010228030307400c1c0803c01024059402501d2a400c4861 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 836339685 1250 836338435 836338483
    0x70f0503190311090114341208070503060607140318240904090303060f081c050405090610030b041a030c06130e060f150a09091b050921 60
    0x3d101810780742400c106840714649402c11840d0094103a221802010f0100040e12038412201c0020302020704400d0b4082c82d5008260203420480703503542d5000500410442c0c51010002c029074007034141c941010040d54038946401c4686044100202a4903114400b0321000c10072001b0702a103032522001d00b080640d002c0e0303d580c2c90000041c2103007040090049a0f41c10800002c03520741840d511400c02c0c04d0103403a0020b003c54940c18045854001580725210710303840784030001d42003400481e44040345d03941c1381451480c10740781c03901092407410300519103441340c0c01001c07480410902a1b00103035205240200100030380b0141d6200003040500002c17005000303201e9400e1244e00d03414010110390b040c0b01400c4550344401d03e0100103081c2e02d80020101500182032010781c21182d120100502080020020415118190f000d002485c041d6242c0c803002c11507050028488509403801d0315522070020905c5c107196581c00c403402185048140070b071034000740341011300c011150a60100f6140c40391340000d225a84012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 836340935 1250 836339685 836339711
    0x8120f071a06130513240c08190606080a0b040626150f040821040c030b10030c0501050c0a020607060e0d08160c0f0f0b090115030c0308070f05031903 66
    0x601c102d038400905101a855500070400d4254041502000c0c0611001c1005214448909603141f4400350b4011418080a100c0054900307903403c51806c455400400410340707400001024988050060107110341c0c0c8881114031500c660304580e01074541b0206404180c03041e000b5926a1041c070040301581030081c0d031100740e0114068510540a4105034004040710b03180e0f0788604e0b0781c5a01c22a07410381181072049440300482c24498800e48120f02802c40300f00240d295061149940000800514034203c200505200103038110004c001620300030b00c1d000e920f80301075860b01440c2600c514400fa40c007010100b0b5540800c49642c03c51801240f0681c261402e10010100a6480c881c0c2034400c200329214405c803400d6410700c80c81107201c07414001d040f00081c18886031200743d2901400c9030284c600035204000c001100109005108103802c400c0200d00f1250701d16141c0031511141b03400000d0078a4800990f082c01d000b0300e1100300d00110b0b00882134076990328000b50b41c0b00c0c06400542c230004c04a4180011190702d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 836342185 1250 836340935 836340941
    0x103240f06030212010b2101031b1e09050709092c0d12020702060409051303110703020904080c2d1005010b0702040506030f0a0c14090108120f071a0613 67
    0x10b1000400d04401c81e400c00201b0606500000c03c48106000c1c4a0300c8100300c190b13111410b40c000c60003220745511b4030081c1c0c8000c80c040040c40e0807040700a6000103030750b00e08521410b174040c1115044540000c054841d114211140422075100340455814012080c41e0f080422a074803008a400100c0c640307007105a804110348074203959180c040403803416a82000200c1031600180b12003071004040030b2906444002e80c20403120b095802c406400b03244880705003099002920701202010050040107154030b1580040c540e008020801818103130081211141d4403c10040c148091a50ba00940b0309020144400d00294101d0a1400410312401c98034103100b5210b84a69810394070030454951070189150280409030102400d565098820003001007840102031040b540c2440c400c89034880540c0c5409848401140c038034080c10f2246104c40010011441d0002c0c0d03504c503921014600a8031448501c1c004c0c1d01034004e070308010340100c0003c0304150f03402540301ca226205890490303101e00c101044120407022 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 836343435 1250 836342185 836342197
    0x15030901061422060308030103030509030706210906061505030f0a0501050d020904020d0b01140a05090f1b0408160602010e0109111e04020d0209090a02160f020103240f060302 77
    0x314400c50507401c003083d072410a910b0000d00740c022030565036039a5010095842644181e00080f000314100400c0d260030704c40e0000926551810240c223203884076482c0d140003c60802400c100d030752007007203000b00242d80c3c0050300186034080c1c021006440000e03016081c3c0d8008c9590006540c881400a00324035180d220b40ca05a03400a01510320f80c0d03400342d0910800c400041c1090307134010722000070007001074000c54035a806007020710804020102a201444070386d004507001540f10b24a40410404010292841540e10030300c903003080107180440041d8101c0ca4410b54118030b503180640811200c1000080d0701d410111083c0b40e00800085c0007521713110382210b00c880d00041034403d04640401551510340d100300c1c1041d2107200b102e0060701041d80010304a0b80800360005010341c01040b10281c41c42d0140c04a80d03c4510800d05625005501d401841110003400c0018a0384849004000c2513920070380c82401280041700d11180c14009045007184100d00b5842003812428250700042526842402a205 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 836344685 1250 836343435 836343439
    0x206060a081902100513060e01030f090812040c0b070c05090c0a090e0603120711010f1106040f060902090f010305060601050c060114041103040803100b0c06070e010905150309010614 80
    0xa10400b40e820400340c00b42120740f0004000007480f103840119002c10b800c000070010303138450b50000440000050140c4040c10910701350189003a403a46c0108880d041143d170011783c071050703416540c0d482e854400000115a003102d0408030001c02c55100b0050300030010070640e4022507240010b503071449070b110000c0c86014411400030716080820043e21805044542d00101c0040175a104e5418418844296400040c805d840701d481900381004156013103801030000c030380346240c9455140ea0041080742d4030440908018280f0003810966420712205902c209981d030340c001d0020000b400c01c116010405402804241c075640a0800498090741c051411602000344581c040c0103c0d80c604014a265103010707030781c49a04281c070340c1046111018500000c602c183c1c4111011034490a0050ac030b140130799281c0d0455040c040c4200508030074040c001503016417181461038602d0700d45140c100100d5032114030b0360111750480e4850310011840352065028520440c2d150000700f02069403410150008440404030503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 836345935 1250 836344685 836344723
    0x6091112060a081009060b040204050d03080c09090405150f06030c012d0f020c010c32010c02010c081f0612090506130311070302130f1b0206060a08 65
    0x4510821040e160320340c0020024680716050b65500101802d00f140d10103801c01e442e035070340300b907508114407842065186070059804609103400e06004c20b41c1c00511040240c1840340c4c00001416405210303040f40c0f22043c0291200c4164200341c5403550b92010144a140c1c21510010001030341000030030f880ea071091200500a154645803100151828407045281c0d0002142d140452810204099903222442e4107656918010a003601c000038101707004450b0541c10000d0b215040380c04079580b1403210204503080c9400440821264400007004075100c1103880717040d400c00e800000860b07019441500c139100070b6102c110f19a51041d101c0c03100d111201014900380300190006102c414030900200c03401003e24200040c4ea20b90325281c1904c1c0a030100e80e801214444203840f001010307401401094909055001810103609640c000752181c0c40d0079005400c0c6030340d0b41540003200e0400e0340144000c2c00c2c603030700703244010401c0311070080d1101c100300d0308140100700b4440000350604000820350000b0f000d4240d40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 836347185 1250 836345935 836345947
    0x1b032f0105031f050d12021501081002250804050f0612070809030c03180a0b030702061f0e010e040308011a0403080d0902100c050d11060610030e120304020301060911 73
    0x4604a00f00303442034070601080c1201080e03980740c0c40015011603000300d50b104c0c00d04000d281c000b0314052200d400013400c1d107401c400410003140d0000e01c507481c0c08410358016866031004400c042c0941e88143c00781003206825401001440340f0407000700155a42903130400000c0000c4424071000341b2950290006190048000641c8030384144000c0707820191601c284ca292140c003e61007444c3d43c0050ba9892840c0305403c0048500d482c00000303c5004101d0b5030348650452038109006910380900900d1111507499280020001e40b440e00346000113031500003210700683d40c48040100c10755104480441c04201c0103000810000d402c880984240321003120000d01d0641107645500403600a404880062502d03110f07201c006945154074a492441c00395500d4135140701c0b038101945841c455004e41014010030010320034012102040c9240d01c98402c3da6202078008103e0401c90007000400d80c8404580188050101c291003414015409580210000d2200c1912002d800c812036154424044c910b00c408c000c0303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 836348435 1250 836347185 836347201
    0x30309150207030f060203010f150c110a1e080d020a080a0311090d14121303031b05030c030301140901050f041e050a092003070308071b032f010503 65
    0x142925500380c600c10b81e07035120b07940e5440c10059002c0c1201241d0b6203401000622016640d00d0a070710007040c1207201401c0c400f401c2c5001a0003042d24041c040d148448220030f4003101e4450000b082c1c0102281460000720250402c0d06440c000c070b6500a003c0c603406124041c21090340300258524050380c02480c141d00d00f00d5460300070780c003c1c00260068056a103040c00034820303aa40f0719551902c071502844e28411400304030102c44c1d0401e01c00440d6059032540502c900711409180e06100810b0780d07814102240500300a82d00b10781d8000041e60002c141b4400018032101000380880035504803941440c140305110a003108000704400700b40a42904401080b1800301c0740e10745500259000084000001070300c05084d06400103544080b26102102512110075804001d060008800c0a4103401c0740a5240a0311000007611040c00d0310018010340307000f01d402c9041c8543d000d80da80389254010001000d0940d20700d00003144c00c030011030703205000030003031141c8080200e0f00541015005051307607054070710384d12460 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 836349685 1250 836348435 836348459
    0x71a0a0809010b0402070b07120e1f0e0d090806010e0f130f0b070f090b030405060f250806090108011e1508011401080601060c1208220605010306050105040204030309 73
    0x1601c06507403240381c0304580740c446200406070680625800c90461403c81400b40040c00c041895603c842d15182d12403216110105100304104001c2c58014620340500780c0000281507c01840d0009009004480140940043d4440c048540308000c2e1180740c1e03a1614822105402200c030740034079a4007940003a03400d11036100202d0300310348640004048100c45803500514450100d4449003c224007079441400150065140d07001007000c180071a1130361500d1390399070f40c8a01d006000244035840c9480822149135400c0412601c2042001011824820007080200303003800a540b0580201085400071410000600807524000b00c0c4020481045044185100041203841180c19102120080100c3d06900a0092003003002500003803814a50411842e58204001a0b21101c01e00008400390780004d45080c01c0142080c965050050340d0760342d075108400c5902d91000c000c81c12a810440703980300300003269010034140c0f4000e0008003d141c0e02c40050004900c107501014000c03923400b410800c04103900036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 836350935 1250 836349685 836349691
    0x3020108040c03120f021605060723150703050f2a22260d0c0f020a12060c0e150c010e0601080a0615050a05190521071a0a08 55
    0x78202c110403a0f540e895400ba40c00b1106040400540da03102d18084103070b030401c0120240c90803803c0800c0c855140500154030792040d85002015004c0d40514030040e040c1d02c181040500c0400c800b40c03503564110459110300d041c012203111001c00d00d040041408046001d48141c0708404180c1183c80c4d5016a008030441070b040d40090b0215044208a98142c101a10900207904404611801c05450130321210150b0070900c510799408480080e002c0c91640c000001d100180e00384603081c01e03030440791581010040c40080d020040d401c543e140500090b21054100b80c000a00d00030f41040004c030528003003c0b5484803a070441d103130340400d0082e00f840c440b15180b0014100210010000074003020115085800c00c00240e0080e03085400951941c1d00b800700502648811440500915400e14100f07030000d1903c02990284a00a03124440072008034003008101d40060f000c01403005036000810141e08050307550500141e031881c040e2003000200c20b4094503441c00072412821a00c3c2c20000082800ca510355001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 836352185 1250 836350935 836350943
    0x803070b0709141c0c0f03050606090c0a08070504090204151b030e271305100501050306070e0d021905030d1d040203060102070b031609060e031b01030b192d0302010804 74
    0x154500c000408076007070b4000801b002c070340a101103450f500b40b03a414030000401c514080d140c040300700133403aa250801c407009080d49003000706a54590560840fa1401980c1000002074400500400c18042e420032210302c10400c0d079200401c074580c207420211507815526008020401c103241d031802520341844040c440046d4880c118109054202d4520380825040d0303209034170384011241c10300900200380f145400c1d0400b024003e01c469490040403c0c0e4504004100d00100031800c1030511a07651408520304000e5001012101d200080d500038660034020b074403c5d40d00c00d00c41e0000040600340a4218801e4240b44060711a0045601d03a0500020303510051906045020380e42c4003060258240000d18040c030360840c1c520000c00c070520805440131101d03030090b006100c10030300b100429681c0001d0f62071000703400000300d038290042c9a0060703000e0481c048603203900a982d203400031059003000c0c0d103c4040b1703150145c0705241e40b10900c85100c0c000c403508088150090340c0e00800c0c000355000f40c410541251003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 836353435 1250 836352185 836352229
    0x1090222020c1c080702030301030c12170c0106180e03030f0907050a03120306050a0b0a110c03190204060e0712050709090c0e0f0102030c03040e0613060803070b070914 74
    0x100c100543c1c00d00c100e56a00d00340000c0c2e0055182e100c81e60051003c2c0c0c2c407034091b00046203154115116400700036040d01c16a8504c1500340b00090410144401c140614549002840e03101d0320b06d81c0e402d9020702910700881c902440804001c4407280c00d5806403560200041018500d0750319403145056444070000c000000b50b1050078000a00d80d02c032011441c00a500656030460203900b20600282541c80c203a101a1240e41410801e10041410608440407012182860380d40d1070904e60060341015407010ba0164940112101155808004040c05c542107108031001c005050f1101144807041d80140e808000040f5914000c0c4014a026408690407105505108668960301c0c2d102d0030a40e1031910103000001c01c181c0da082007038141241c1c0755040306000d0014506101854a04641c0ca001e40c0c49240590301800012178100e0316000705403c02500152000d00c05c858507820003a581e42e20040044230380120250000b00000c0c03103503421600380c81c02c00740d0030000b15002004002c10541006001d054a5070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 836354685 1250 836353435 836353447
    0x1902090f030604082205010503061009080d110106081504200306012c0103031d180901090c0807060e010f020c120d0909020921030c0f1e0109022202 65
    0x140801c0194401d61080d000d04e640d400c040d201d0320045045541d0f409182040610041c0156a0000241c0354040c6c3d068450704500c8080c18000c072a40c036030f90f03448070304039000b030400080e109035006600071440542d41e0300070720269540d10821a910036070030202c08502000a804240003a08801c200b900c00c0c400e009101c00050300b88c10000381411420f83c8030744070302c1c11100d030000b040341c1c0c5000801c6142e000c194401400c2e9855074402a0812400d000703c00030901030310324800c00c1552040c0c100c1d90303c004d441c54606c1d0f1501d00301840500030b1640da1020341c0e17200c0814a0001d1007400009000d400c1e100030b640c500507283d482e84010b48140350404800025409540031814242d1a601210200d66800600902199004410283c4134100355084502c18500410600e00e00f522800d4410703004030485801103201030a854509419802055510300c89030048202c4140d00950000c1c41c0034041154203881c488038480c0c41d550500302e034008100290000700c040d510680100301c410075800d0000c1c0008015241407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 836355935 1250 836354685 836354689
    0x60604080d05130512071406070609050a050f120409022a010b090109060b030c07030512130302010b18040b06060f0429120103080f0d06090518061902090f 68
    0xa40c0e0600c00703000042022540c515200c01821107078004080aa4501001d4000c0c1000c1a840d40b00360b0080d000105106007040d0384584505080719480d9401800801c00c20010b0315103030380c40b940300c01ca083c3c9280c803620345036450310b030030200700d07000c0e1005100c5c00b1a03d400c0c42c1c9610070020b03400810340b4014015040340516084407000f00f030180022500000000da41622004200c045441030300290300181c0352560500c000500c0e0411242c000407180c00b03158a401c89850304941a00ca5028222440039545003846025104204a0320420340310790000e1040c04020700c148074100014000700804030300700001150100d800e0807002d40c2c1119018010f146802428681c02e41c0b5540305900926244601e02c0d5100d004200340880182d03e400011481e0f0f00d07110807200803040990060001402d036250000e64507615425010032916017030110340f01407102c02c0e0340342c41c208014581216440f070340c81d01c280d0352a0142140070071107a120705a11039a02200b41821203501b03000b034200401c81500302d480c1d0225480c0903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 836357185 1250 836355935 836355943
    0x1902120c09041505030c04180503040f0810090807030806030c150406090504060510050f120c120a141f0302030a230309010e13090204050a1a1c02060306060408 70
    0x1004404441a0380e20281020b220440341d404180c031821003480c0c08280041e50700890034903000c140848000c100031440c407082603007550102200400701d100004000810800d0101d0310f008135240c040a0b1804408040f03415801c0c0d4044c514001c20a00081194200182c001c0c00440d402c03160150848070802d0b00400802c0b6981c9070f86078610000030300402c0401000d6070103c03010780a0f000645003031102614207400f041c880e094400d84e000c107205011821503c10b02d03081003542d024030b82d00a01003c25042c65040e44001c1d6101c035000d01e200d040c00c8400164074007524010101e200b8500c21403500e140d91414098076601c0c03170701c1040300580340c8110030000244e40c0400c9243d2800d0701a02000c0745005004030042001d200c1700d01c015140d60010301502d0040c1e070300700e4599003021038241c40241d1214040200113004240d4a540251b02518084c18402c00340346c1648400720412190a9005e144417008007000040400b00f002e6240f8031180583c3c100c01810010051508000302070421340c200b47d1141c5040c1c2c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 836358435 1250 836357185 836357191
    0x111012003091b031507050f03040c15051e0f040b030f070f0c080f130510030b0f010e0901091a0604120c0909031b050709020a020a15050906190212 65
    0x103044408000e000c0d040d50140050030040d0342c1c0c10307401d41c25109004003113601c8004101060100101d0070340054104c500079011541003080d0405541e540e80381c02d01c0c040c45003413400c2c020031101c0c1c1000307655103206901400032030340c28805564411146d01c0b20035a411080303034406100c2011000d418000000c0071100880034501528030341040080c10301c1d111000600c070070030055041c0100081e0014420205802d070303040b2040c891080262503521600c0620025120046500c0340390406268000b000d4181c0d81503104ad401003000316504011840004011100c0000b00e44690f540058140010000d000c242e50040c0703401d900c140c4d412649040d1100004626401a9008884544540d41c9000030081806421005018622010031120149450081080039002e4444040303103581c811310300502000f000b01c60000c103910391080d55500a1004029100e50080d1411511002036040c01c41c0038104034010300740f2500c00c2034010211951502c0300c5036080c100200c440542c150742041040040c0000d101e1040c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 836359685 1250 836358435 836358491
    0x13051002070804090c0503070f080406061a120709152a0c09050c0708071b0506040906050a08030a0c02090705070f060b120105010305121c021b07080318011101 70
    0x41c440703207060504404c1ea84084420340410100300200a0b6454124902d04000c9c8910b00d0000d40365502c601c2c090000304034030303040401c500242d08110780142000304020201c0580400410000d5140d2003010764142065000e094000d6000d8844940a20b01c03600c0511004004040710f00165101020110250b480d030b80400d8410420002050100180e60f000390344c0c103c2000000b151510b4540d03101c280450151550042003480c000c03071f120b485002c1055680001c4d01e8010a003d0b5510b0340d5a500030020502445054007912112900040b090004002d440441d140703920784246401d59542081141c05008040c00c080c844103008034008104401c007503c0455104500015001010000304003c2411010140c4002d80c1060010f000241020550703114a401c1860324544407500e01c1407401b484900008401076182c80410f4420b000342444010342c440551030b10a80d60600d8488010075102d20401116800002d4442d104100d107500c11066090b410003280700000b00c0038030b201f017610781031207130310516031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 836360935 1250 836359685 836359687
    0x10030603031e051314181b030604020c01050a0b040b03070b071b090c23160b09010f141611070510170a1a0a0e0a0b0402220306140f130510020708 64
    0x810241046c416000b07032182491202c000502d8685001104c1c110359100c90f106180010020585a071507035019074410b090f00c7d0009010900d4036142c0080101b1b070f00d003801482142061501e29503800c002c00c14809445070041c410303103803040c0354865044040c044103051a60402c80c0348002901909072180481082566468441d200300303010004080c900f41c03400d5420722074000c0000034980147d2007000018503520034208280b65807409c16a07030051484003090040a424151f20400d15902c5010151081c031000944c0c030404507c0c0001140c1a1400c520301440c1940440001c1c000385c034004480d8600c4450a20703090320341281d104100c80c45010141c40d60015192250740805844d00e040442051a1308191844c2c212146849600c020300d0102400b2040380350756601c2c0a142d251283e0b011507107525215440b8100820124113802034540007480140d800038900410503120f1050203502c240565408440c4403101e071244c51820801e038040c2d00048a00f1320a4241c41c01c7e050031580040e2804a01450081e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 836362185 1250 836360935 836360969
    0x180906040312020a1e02010f1404050601060c0201020607030b1906030203091c0903060b060403050a03110f0d0f050c1e0c0310090b010e0406110d020910030603031e0513 74
    0x3420b100045900d12054a005100e503410065000440044a80750010f060f0312800099000b68010600a001050b0903401d082d1550003205041c80d18038060352251040350702d00e83c1c0c0d51400310f03403441e1038a4000740181c1012022581c03c9120717030028031904100406550070302c502145100081d40c90f0780e00501c0460b801008102061500b803210750410f407003a400c4003450f242c207004c0c014091155400010b0015944807001460380d2141819a000703907038000d0440b000c14120781405040d195840154000d90f1190765181d502c46000411000c04c10b802d03544418041d1400190280d866402003c40c4003100d1080601c502d20f0940c01c0180c081c442e0307000388003816001c0c0d0f55100341400c0c00c80d00314a41b074031582000094000106c100b01064111041e241002d186515145800000745c6907124520090000c04194480340b912a45e0080180035401c60789500c46443c409800d0f41030f54102d10010340030030381c7c7c1c13000c03284038000300004000402418680140346c00154510701c40030f038000d0341002104944202d58 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 836363435 1250 836362185 836362187
    0x40213360507020c120607030f02210121110f190303350a020708130e010609050f10050c030c481017190c0507031407021809060403 58
    0x84c40340040f0590700ba6105803102c030551541d481000d41a0002c16035a040802d043c001d440d03041da1000d054480342a10070b01c45545203024010000e014810118016035000261989108040b4042ca42e001e52108076829072601041298203c0c0c90002e50000c814020b544500e41c07000305400051032003078503048580c003007503d050511010b07034044840058000d03401d214140011400c3c569804138104030f0250f42c070211850110454040d440107601101c0500d503020840404855000b4161005907403444030303d80e6684100000071203c0c0c0c0030240c0001004180c4082c0c20304c190014a51031103404100c0385480c10080895141c01590b010002c250020a00c20b40c001c1c2001d8403003c180482812404c000d0300c8824002e104c0030001c01c0071034500c01c0d046c0340c08007004140607d842c64000000900f0140d910314080103010300e481c10450114003620310304144004158000c10a6800c02901a42c030380700403207035021010b04641d00000342030743d00c100148002c54100004240d03640c414042d5030b010b00107904182c64 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 836364685 1250 836363435 836363443
    0x521090c010f081f05090c09091b03061509060d0203010e061f11010906020c1b040615120605151902060402101d03010c09050102070504021336050702 66
    0x88504000c0c1030650091000e91010f1525001250040e20300d00e1103848042c0459481c0b42a8030864020710f1940804c2418070f0100c0103400d040b2020341d40c90816999611071005441c0c0f400c0700398007540c5010700105e07149081805190341040050400580740102038000514203401914124405c0358002005007c065840300c2460381200c07094443c003000300905200e041e10408000440410001207100ca800854400d40242240750b40204045648084000526496410281c008040310483c001c1c10403e0b0306041c0304403821140c4040c43e211400444c0102111103286003140d80c541c0c5c50303d0f060702141d59a40d295000d48402014040315585400000782c098a0300808c180790010754000008200250300e0703109030500346440c0c0c1e01d443d107803d0400d881c082c0c48900e00070b130f041b980641c40c1860400c14190004010004c0da842602180e56469640c4100710691280110321144204c080c00c0400045059084410b103032407a00032006040c860034184800b503e441000303174100880d00c8400344040150144 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 836365935 1250 836364685 836364703
    0xe28060303030f270f02100c020306070f05030604020903011b0e0a1502030304030507021305040305090310110d0903121509050a090b0414010608120304060e0f0a020405040201052109 80
    0x1d5814041c840d602d109183c282118401c00d54112601204c6490030482c003900301030400c42e03008181580a0f00b000350014402160007500328040d10400e00810350090140d0500040b0500513500e1501c0c0d5986c03030341404003a400504000c0d4141d0340b035501502e070b60442810031415400560f500c811110124408010b220411503100d0b1800440c02a03591400580c04011039a0058240c1010790b622215440440c0c0592009561600020302d0482480308140d8803800411205004400300c0307156103104207005044440d049070f034409074207081000204a80e00b0740c00000b68540607060841a204c040201882a1064141c03d010310364001c0e2000d215262007072042ca6045040c0c2c000c1003003840b156603122092008094000b402862031000c0d90519080250011406040c0c480c2c181d4500d119130200000b001d4200743d80c2110031908040c28003640c004002488d440c580740c0000100340b1201d0580030b210050401a005904016042186d2000141040360300c8400c00202803140340c080c50030001c036900b060011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 836367185 1250 836365935 836365961
    0x7031107140f060c0a12092414180c0907110d0801050103140c0a030e120714011805060403110111030c070b010b0a050f1602100816050a090e2806030303 67
    0xf808110f03002a030181c02d0742070034000500001615941803d02340c00302c1618022003c580d481d151190300d200385054029141050700718205000325242c40b4605000f4480ea4250b4100941c44040c10011915100700201c0e00901c00342450b543c07100c0303680c0702c480c20330703070459008004900c0100040145503130511445041060148105503c4d0414015580301071144c1400401003544403072221001d8101401144040006400031658031400c610300b03446050741e00506001c01d940791a40c021600502d400001c01103551013000741c601e039a1a981c0544100c0e900d007041401c13a42da02c603400e250b1148c1c10801140600b0303840310b00c1512842d182c0703042c0c84c900d40160080502404144240c402c242c0d04501640c1403e2104410151220036401a8100c00041104c0296011555107200c0001d1070708040c1d41c0380264162401150380070b41c03021040d5528032800f00d2140020300307100c00030851040d408000702c0d040496030b8560907004000c003003220440c02c00003205599943c2d1f1a80100201905031051100101c21 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 836368435 1250 836367185 836367187
    0xc060201050c04050f22150f0303020706050c0f0105070e0306100b031302011101020d05040b010f23180a020d06050a05060d05061c050c012607031107140f060c 70
    0x82ea41c00c00e600652044074001c040c3e641c5100d84079910f000c20310380b810141c0c0641030011403030102c0000240984100807010b104e21107a010031400014017440003580d4040e0001c242d1245441400c80d0a5845158440d16a00840000f08500380080c000c1d07a00500e400c2d59908408102902094206100900f025030104090b90082011b50b4112701541d90000030b022840c000101c2500060302c8044200c620007080794070025000042c2001a80901c0c01107005940d48200d5a80742c0114000c0c0445a001d145c60021007040003102ca02c44264081c003d0701000f0301035070507000c03400c50b02151145081c1c541d000810b401040c4844a1030240c401c03c40140f0301100c00d0342545140001241c10361003184070700d148841d103d03800140a0b45581c0e01300351042c1c6000b9a0046812481d08066443d81c2c4841c4d851070024031085d088001042010080286400341c00c104a800d64880d81005d800030416108100101c1d0700c00c0c02490003003000303501901310701406070002d03114540d000c0c056a405c203040144440e21641e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 836369685 1250 836368435 836368441
    0x1011120f3c0c3108060f041b080a08030604180303140603121e0c070603140a09150c0e15032e1a04090606021015150521130c06020105 59
    0x20f1800b0240b411440320400840c03111090a00c0501030085810062462203100c1c240701d0070300c0f0707088001403240d80a01007a10000300031803550310b5860240d1180121a81c40160441c000c51221801150000d600400014103041400e2700244900080710042e8040707940c0e0b50b5558030b00c51340b02200e10f911110850240040458140e5418003d0040c16105590751040c041001c2c1e11601c003100715412500100c1c122010588d030b920008000e1301030030039454040c110820114090a83c00d0103100100d540c4010041c1d407030070355001280001d00002811008009481921236001e454145a40d40c0c50f00c0c43c0789a05076207251080d2059032141680700150a01c6540c01032071401051001412803e49a852200e08030004050712031400b00e01450300240c090600e071500000f540d43c1c00080e400b000441ca10410701ca400c40d80002141c51005a01c2030701a17440b203c4280d80d0f1424401d50050100307400c05150400b62542100104e004188119040c40c80e044101065106100034042120003c0500348001d1240745 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 836370935 1250 836369685 836369707
    0x40219020d090801020418050a0902030106030f0c0e0c03011e0302060301090e120c0a080a0201060810060806060907090b090118030602090901080309030a0204050403050c010e1011120f3c0c 83
    0x50585990603188623594004030390306601a40007000c0080c1c000f002031100b00d0f02c03810a50100c2c080040b0440740030044450000340c0c96001101a40709042604c20703035055a103401009481d1f810f44000004080b21100b002100591391440550302900001d400018400b071070b03003c070a00c0c16040411000c041c013410f0005442d00d03500099106c0e61580e02c103a800d0349490b44c0c42c400740d015100c103402031300c500c0c06084440718040b500740e480541101c2c02d003411a1100e031140400e00c0040c0d0402d491200001d0450704042c002a1540f00082c40356010600d01508120401410311412400c11307002107030034540016911070580b500083e51400340180d10041c5103030520780000640d035508940c1e80240620340740d10004c0e040c0b50041050703881213000680240802c105100204c2d8803110480d500544607881c084e800d14102c00c02e5030940e104802e0030214a030090b15000d1400724606030061108888034070078000c003031162000e0100e0003010b003420300080580400c0003070b2034001d00c60700511122446106202c815210 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 836372185 1250 836370935 836370959
    0x50a020c1218060c0703050105130308060f0a09021c021b0c06040b030609100e04030f02010e0c06030f130f05012304080d0f1d06011e0f14040219020d0908010204 71
    0x142c02255480e43d0b038a030100302c0c141003c0666101911030b503c0d0200b003114401ca91650324160303a209903030b8004107560352401c120541860101558120030030781c10074400e1028650003004041a01e61603402c01c001c0000302c4100f40d0340828592003000f85604c40040204d80d00700700c1e1030035844046840d141444d090003c042e0301c0d1f000040100381b00b100e440300803400461303009904502400700c02d00030048520b02400c01801d1914030040190041d803806c1304004040101107408c01041c1001004203203141c8503602d0640d0b841c2c0010388a424a00c0001c4800d00001d90390304964240603100e01c00100300c1c022030103241a002c0d090f4a56007645030b00421708002c00141110200d03601c2d06000040010512214015480204100b040f000403460144103812908140007031583d040701d0882c49401d00400c5c1d42441300c4041c071518816400000d4003080c081c0700fa41ca483c84d0740025410054001400c00d0031161030b40d00000005400d080258001c81c1900800c66440721601f4080c1000c82c000f036141030b01e0b0030314034080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 836373435 1250 836372185 836372227
    0x8060f1c0c140105031515161b3209040b01060f0201020307090603021e0301170735030c0304060512060a3002060c010222060207050f0112050a020c12 66
    0x8901c000c555007003140c0e01c40302c1562591400707007901074480e0900300c0329549612100e41e095601c0c27000e0700000c00c0d07000710004a1030b0507201c605401c94060b0404500002c600c0e0108000d16601c4c00d04403103a605213807511526188501c7c010b1494881c154903201000d0882030807450302c1411a40104104407140e40c01079591b1007110450f140040e506c0b00520401000e03000b456103c48020103000000140010b0408083c1c210f00702c80c034054550090b6241c02030204980c82030070040320712000b0f00010780c002d001d91103040c20001d0701109580c58400040d414504662183d00702d20041840420184d03290041e032076000741e1240040d40e58803034103400c0030034451134403203415112040380d24003100e072107070718402034480301581e9070b001d0203c035103641d5002a0315010b0740200c4900c500001074001e41401c4000740c0b1040004407900c5401420841c0d00344030501c80c2d0007011480c810305020750740258003480009031107102c1c1701e4515000010780314940001c1440c280701c00c440701040c4030030082c0030f0314003a0034031000f030000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 836374685 1250 836373435 836373451
    0x3110a050303010e0702191b2102041d01050c0a0306060e0a0905070903020d050604120c0803220503070b0114030d05090625120e0901030b0708060f1c0c14010503 71
    0x110a1762a020300b01c1c80c1c60140000742c0c0e01424003002450400011051004250640f805001c80b800d4480003003080d5500301c8020004c20b000b14440d20b4001d810183d0100100c08c5140118554160340c00c101c01e42941d41c181d03402082d042d00000d0340c3d00107660501c1031402410307541c41d2034841c0b00302e10400a0310040c101d000d030711b081954510106940d0b134081d841d1140111f9004d070905046c207405060441d00d0f01c2d011902a40c100e10110f0074220261711500319082c04a90040039603007140c40742122400749070324140800d581a004142d58001140040001c1e01e501072003860f841c1d40c20341c10708031603a00c040c1d07041000e94002d81c000c00c20141c08a03007190546161040541d0850703100d60105204040c0d042198403404016a99082c0103005d01042482c035a0260009850300906618030342c052055186013480050048541280860703d080d1080d06065003000004016440310005440065003100a04001c5402013420b00440420020841e562a0050000e440c1200c20000c40d40c0011780548001003600c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 836375935 1250 836374685 836374709
    0xf0605090718080a14010e0d140306010c0f060c030b0f0d0f0f0615210c05090717090703030314010302150d02072111010c020d0e03101803110a05030301 67
    0x542e2045030b00380c007000106403107412100a00308500b054014442c0702e80454a055082c004050100e800014001c0900d190315528188070008248020038240c20250400e81000b010714170620210341c0c0420042c4155010790700c001082c0080940280c00c0b07902c06440b16000e4000d01e050f0f120305540c2c0320802d80000b41c006942403c803440c185851410752940c41c038000c101030300d441c84010701c3c40015540d0300b0a80e03800c500e00d08418044070484e0b1500c0ca6180b140100081403071130b811f000070704003114034582011190600c10511a000000c025640d00202d0b40000b580c2d020003410414107505000382d24402c1c000f102d0002082d41103802064201000b42c1729072040c042c001400080b9031510317074104c510858021281244a290010b00041c0341140c0d40e003968009020000b2120490130103200303a040c0074105030001d064014040c001a1490003017499903d62600a9515545200344280034032503218009550740d0040031005c0c40c010b010502032400005087d4080e078010300000b600042203c0c15682c01ea4014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 836377185 1250 836375935 836375957
    0x507261306030c2f030910031d07030825140c03010c0306030b0606071a010603061401260903041703040906121709060403140c1002010e0a02120c030d080405010f06050907 75
    0x10503d5032040e1b410342501714441c1c942000903039601d50301200105c0f20b0b14103080501c018811449940310458000688168010401c15103042940341d40115840d0380c83e0203d9055a02644070456a4452035203104034a801012040100d890284103080d140540d81c1010807a060550311492413052000309802e009000001c0d2020a2124103101d1119031a0507505101c00d640c3c603004000d018210500c11140004050348a180a5600960001441070b0380c03076110880c01c0380c216200002c07a03200070b000d0a41d81c2c001004040351502500e03003071060400e2620700656032945094284030445007681d104400c2c2c0041204803100084010400b541d0100541482540742c0e04050001030780c600c030310383c401044441c40741182c841c80710001c90703089401c1104a95409070b0480c00789080e0300781c0b10213002010740d60300081d0f000c00062401c52610304001401808588100d00c1c0e02012034a481d0321f09a81e00c000c079030042c0c20481049801d0180071315441d4000c1081c0300803482c0ca03000c202c206102a00b05424071030f00e4050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 836378435 1250 836377185 836377277
    0x30809032704140108071503021206010e060c1b03160f060c02040b04060801090b10150c0807051504050705031b040222140913030507261306030c 64
    0x3c1040c00300c03240240303d030b40303035035143c0020741c1e0b81c200c0e407260f004184a40f01402c0b91181c0288250fa00c81010400700c41141d60750b41004482000752030a442398454070178480054400010800d00619558603045014120752510070146002443c5041107010204044180500340403a040f5030110b810320304204c114030303060f41b00207400740012a2070343d5085840c0000003d01c0c400d0540040e60010b00032440410b040d1515004588820520302034034804c0b4011000004030b03c0e101e1201585500d0181040a0915075217a4030282002c07c20300b4072125205d0020305010900c1400e00546006003c21801020880b06240751041155802782025200d264081961070b540380f0500070f0030b50080c604481038203450752140640a18611400038160003a0f0054001520380032000020b0210309405881d843e091820607a07950481c503154800d40e001d003c003100c0c62140044071000c0644a220190080d01c069503041c888010111410b428102d001c21484001400e6000d85038000c144c140f01000010682d0350311034142c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 836379685 1250 836378435 836378441
    0x519020a0204020a0806040f0509072c04030e0102060a0c0f080a23100e010503071a0d06060905040c0807140d150f0305070e2415070f030809032704 65
    0x3001941050000565070007050740715503c4d920544045800300700c0e4580000400302100e1044482c182c540e80081420f1002100c084001d0394902c070700302100d80000210450600c4004020340d07084011800684006019603010300c09030341d00211000003004038186c00600102070011501d403140611942201040c4080100d400c0106030120303100c0042d281e11160918021201c1045034018646080203c0118482c000807400b1812600010000c1078800c0c1819445401001ca240308501728400810211000e0740b01401841c0041c80c00c0d40364030b05054a844103000079038140155400070001103404000115800c400d40b521107030701041c440b80d101c0d011201042c0060448a8042e408070035070820009510b2100200d810075248190305440806581c1c1302c042c90000d10a41f10304440f451020555606041c1502e10b40b042ca44005004007800b003220102420550701c403541c00d5627182251207543c0c0c140b54111005070f8002c0d0145000354036080b007a030341390b4030a20765103220184000d842c0c403550807950741c1e1a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 836380935 1250 836379685 836379703
    0x30b0613120c0b030f06090105010207080c061b06010906210b040f0c0b040b0408010f1407180f0602030c011407120e2b080a0b1f020a0506100321051902 67
    0xe28580e600c5c1411010303084124812250b1512504890001042c1948046104030032a016040105042c204020411a02350048404a02c502c501d00d0024100a80d041104c10300911405100161039400c0014540d602c1d142c80000700341c00d110201d411400502509003a5610640200c84071140180c0ba10300b50100e181241d0019030b45410114012864100c94002070040b550498001c20600c988a200c030001e403a0081d00300030090b5100800078003c640100f01307244107400d40e40c038202c0754991035200b500074800c03040e00114016031010626015603e001d20071545084101007007000b0600e0950801031140300c00c21610a0081d8407642c44410000b030400003480080c4501c440b01503000310501c59200070b20039895640000445084c0422040e5255114101035904054030100c900c508088a4104400d80304007400c04602c64010700300c011a200f80301860045444400c0814064550b0619180504038115070200340703e990003006101540000c101d03940749001c030301d2600c01128144001d80c00c215040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 836382185 1250 836380935 836380949
    0x27070527010c0813061205090d050f04050303041d060f1c020109080d0e01121104120201020a060c110c030106051e0d050f0d08070804030903060e0a170a030b0613120c 73
    0x810281001110844160300b0303a03005d5515811030031441d00e86032068607400ea81c0e00c240c6030007410700c142280c1c2c825401400001c0d038001c002850710f0364038004689980d00c240d2054104c0294004110b06c1001c0f40d281e0250024400c0700e052408902800c0010200304006842008101401c80d0000c11640039200701e1009080780000d55401c03040da2007014000d004038181081c001881c694261220407407512401c0881c8030030310103407818681490b1640a00c0b4032184000c0c0d0541c0b049560300390024a80780141c18150340b050b91240b13070842c5082210b80c03030815452078080c4280d040c00340920580e05c400c04841c40043c9410b400c602500d103100d0224591465005014209005443c0008165100095148088003d55a43e0450f96a034100101e4852030284c9000300080e16080080020900300e030030500f00440080d041c0e8180c1c000641d035582c21110804000240910301007940b8443c0c0303805104014003400140d0b100c601e419114114508801c3e2036010320114003464801200c14400d00403041006841c50b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 836383435 1250 836382185 836382187
    0x1006080c0a0e190e01020c0d0c0507050609040603061508010c050a2102160b06180906130546020d1e06020a03020309070b091003020c030927070527010c08 68
    0x2406400e05e011790300000650360248515000692810b105880c07000129070481c001e008494200410000540d07c981c036096030241e112800880403d0fa14803403180c8004012040a00b500e1030a49100c1c00c0d1800d240381541032010034000714000307507017080300780d100298450603e0b12000311004030741d130007401400b4840404034082c190342d00420010f0361049000303101c00c50f91041c480307001d500c180c943c00102f00c1c0c001c1c074690080401f0a680c0c80700581984c000b00d00c5041603c40648061381c03580b0840500c08010b04440100325007444601e8454000341411134003180d55200ca80116801081c05000060390051903407462800c15101c7c000c5983c00300080d5940f101042d9541c001d11100200650010303038102d1542d0141e20f90005078189007408403403440e04054450003480501c0702083d0002c2d08003070003142c0680010045414240d44004461185014a0490204801c80c1a600d1200f1040040500081c4103007001000c20b005044440c15501d00074049404201c0c030b1240d40101c0c1c0d5025011801454160 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 836384685 1250 836383435 836383451
    0x1501081b0910030c0b040e010503060c0d0506130c0c0605100f0314160e06120a1205090d0203070305071e06020c100c020a0b1b0c060304020f0607080301081006080c0a0e19 75
    0x2117100010001c581c0c108040156690f203aa0405440380307010760385507500c0c003410008a00341d5051034000a07803000009014104140f00001c28000b9909200003030350002c1c181e00b05200c1003040b80c2c49600d0700009200c0030190b5141c20300d441c084459943d03000182200740f0750722400d054101e00700003e01481c0006035045020365600c0303c4005409009890107449061103022204040300005090f0030b220390410000102d02082c210140c84030b510130100280c114a42007805070240c0c034100403a0008610480c0204040f52505218800d00d180705448403c0b14040d85504015640c0e00080d100e15001045410056945023580c040d6416101601e00a4108042c5180096405405006440c2e0781841c01054006203043c030309010f0701c0d40d20000105500c040144041b50150030042554000d080d80036010524212058890200e01e810983c0f028005a00041c45c090041a03140207020042404c0001424045000c10000f28801503500030303c50003018080010f40d2026180f16110381c4607100b82c41c00c1100f44 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 836385935 1250 836384685 836384699
    0x105030607111015050a0801091208060307050d0b100501080c09010f2001090c0504091505091504080c070e062220120f100e0a021306021501081b0910030c 68
    0xc10248107a9100f012608400100447c040c011689200e03806107900700100c103480344c10f891000300500055050b1007080c101096640741c8134070384482240101c1d59540180362407031000840480030b070030082c1082250f005103c0030113100402c1d00d0381d4071030900741000d400403914800c41e21350588248014034400b0006007450842c0c0d040d80141066406002e0300c1000d00c0d00e6030705101c15135040c010018044c004da503490b183c0301002903004075000300c6a001a5403440812900e0b044030300406440940e24200c00145107081d500c41003218000510a100d8040c019140800008580400d0444582d075410f408440301d80c2070050f01e07400034001080b14440c0040b45611040741982c01d420003d1207401441107140400e9049001800b1706106030403a51180c20305500340f407948280074201800c011180e039004c2c0b00c40300800388004000400ba12179540200050209a00d41250310380060f4020030703071354001c1000400c2c2010300b0040312280c0329081d1120721031500c401c0445488400603600c00b9250355043c0201080714 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 836387185 1250 836385935 836385971
    0xe010920010914030307060e0703080a08010e10140105030901090b0c0c1207080708070c0302061b190c060f0207090501171b031b1305090601080f0601050306071110 72
    0x1080282d03180d070704454440031150501c0761807501640d80b5920034088440010075540200405803c10401d51300680e80e07a689030300c0740e60400a89000030903102c00050084018032100039502500c20309800801600d0580556000220074078001c1c100440000043c0c0c0c3c40000750030280529901c211079041c980b03003407405101550880800c01005010b44003914041d4417150003074852064024640e18640002c03940c908003103601182c4102d5148402000000141e50340001070030f54140341c0400742c00c030039000010b9542058a2940000383e0002100e00181c00b10b2150707000202030345e6483c2080016141811f200340d10f4aa0a0b0348201060344c100400403410780e0740d5052100d04c11008c3c0f0b007100c070b81c268424410341031060b41e1404039806601c03055800c10854041003250000310030240011884c1049603032410f081c2ea8084074040255800364004016451042000c1c11a410700f030406400036505141c0000d0715030401800d034004101800c00c2148580708244031603604a800c000041204603181484c501e08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 836388435 1250 836387185 836387243
    0x20607150509010b0d0b070c03120c031505010507030c02090c09130f0b06120408030a1d060103030216051f0224011404060b09010c03020c100801090506150703030e0109 74
    0xb81c1e5082821660b0b0303074144000c5091507907500142c92003269581c901d04540454905800307804000103902034074125001886410480d0025a80110b00600d0502c0c0600710803845500403810080104945004a540500c0380c0884c29412100c0300c403203031591042d0101900407a1042d031342c44a8032445c0c0703640d00715031544136141440c006103091107100100800c2000c0341c0a10001c41e28002c008a001400186000000315888400c50400240c1c8007162406202c0d07102800301400550760154005100380340d010021400b54078442d800007055942000301241c81c00061401c0380100700610710352956150300030300c07121250700e101c041c100c021030a00381c06841082a00388507544041c5100c1c4ca90120a003014080c032000daa110b4190705141604a0004407407035030b41c03104180c0460154820403990b5a0b81c0501c0741114020301e9507944540c0d41014005822520085c1556100780103642440038054000030549074a5901802c002440141c01520640074000110006000f044070010351690030900c0c40310001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 836389685 1250 836388435 836388451
    0x100e37021b030304021f0309080c1b06040b0915160f1505060a05010c030e0a061d040207020a181404030c03031a03061902070c06090611280206071505 66
    0x1d0004815421252244402c0d10040d40008480041010b40503018050103040c4171a4500061a0b6400da2140100b0341c110007440c030f0140e00525112481c212b10b142c070701801c108048030a94070b0140b91a002c8040ca108601100307010305091b24988100460b0791040d10402d6440c01c060001003a0285894280442e00000490715409425941880ca000500c2158440c02e005409200c086082034010b683d200c031904411001c1060f095050b407055251040c0540c01001c103501c07258484e540e002005112010380c00842c030301551052028101590380d1014002c1103a041000f8904c01880c540f400f00c028045405080c454209400c0a010426a02c40c4e2112010341c0030383d50400c102807464041380a41c0d15880c4030a5803661144c03020922022103040c8100740e400d41c0f02c03001031500782c0540e03448281c0d4510340e11040124240303030030400000e1740042c2c0c0d030030009a0030406803450001c01200c040c0983c04000b6110a20013440024208548405088502103a081083c442100c203040380801d01419080398456 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 836390935 1250 836389685 836389717
    0x5100207051201050112060506130f020901020714060706020c0a0f050307150e061621050f0c0f04090903050c100c0318020f1002011d0d020105100e3702 67
    0x2062020062013100d0594030040051110031265455900103440e01605160380080e030002c900354003d0b1540b1409000341280c1d400940c4403010710002a0504040d503000e4122a101703144400842e545503030440d40d5841e44088016182c1c00f91110a03807406101c00c000620039020301000b1410f010300000941400e503c1141d4042e442d4510012003800e540305512440c100340d018001140301c0501e03045818120941754500240342c9111495070100c180701c3c02c943ca040300c0d41d07618280803111001d20b2466900c410800013807031130000600251000351040b0310440c00c0381640d4807450b004052160041750800114007007220310b000a1583c41e0302c0104501c06441000c0384c0362010361003013040f1107a08850299001042d44269406450600090461100c01c2e20215582d520a100c1c039070000034490114505144000c0440354400400642156030161800318002d441e804c0c20004800103514a951088030342e0f010428401c074140340742007840130011240403180c0f0090849030400d80306502406c40300325034010320 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 836392185 1250 836390935 836390959
    0x6061406090102030703122d110901050a320c0d020d0504061808030f07050c09010509150111060c0d060905010605031b190f2c04090503040510020705 66
    0x246201d02411680580c10512540003c41e004002030304102103c4240400c00e500c0030201031920411001d01074401804484603030302c0c0500c447c81076000c080740804826240c039444100280c103034003869a0100070801c101098407800008800e0f10903c50240310071000b00076042d68102c42c0c1b2178220004805803071180481202c4a03d20010ba02c41d0051900e0300e401d0b00d0107080c030504684c1d084100380d42e084103a01c940c40000305408100002c00c03400205045840c1c0b120140c2c0390403411700c0c03900c2c20100c0c0f02c0c400ca40010302c206e03510700010942103040038141c9801700c100b000068a51121425031b81c8041e003d00b800300501d2000c45001405c0c004400c900c100035007515044084110f5000303004410008800f4030005804001440030602ea890550940303605190b0014001d01e002d100a0048100189110488a00c030a422120f980e15003080f00110411400c5010080b1800402c030301c06281c4283d4540b5141010b00130207000700c0d0007a080181c00d10040400113070f0069504c2d40c2511a03640180c1001e030311 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 836393435 1250 836392185 836392189
    0xb150102070e15040213080a0c090e03040e0a0b091614040e060103050907080a05031209010e10180506100608090f06161e0c02040b010306030f020d0501110403060614 73
    0x200c4030a46021401c1c0107219111001d400b03042c003105031043c80d0000d038204401810303840440c0c0084c008007a00307002000e401e0340d5481d0007550840164841d140d0942070030f903140503201d40401a07401341c4030080391450407030381c40c010343c0f2001e40034200c10386401c00890014009091b4590710200308103581521001c55601c2074200c0721581d889a8450707810350900300c1000c54900e41c03080c3c00042d040064034085540d1151150011420090328030000c50300c6071300006001846445142120742e000c62800c0007001851110b1620310f44032000040c84950703071a510079000c01e002442c2100c016416402c101220550700e407c1c640342c10f0010045c01380c08045940c680000300b0281001801c44101d400e00000341507540c4505149296140903069610300f0b015140c42c000a2401d203110002003214119660007a49801034018402100d1010707041904050910000344049200c030618046942c0d81603d107010380310024202640180701c1000503040d1070900180c0041403280701d81024094034404d00c051000d02c800442 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 836394685 1250 836393435 836393443
    0x9020f010c0c0e060f33040b1c0f0c050405030c0d1208070c0b0a020316020c06160c032906010314070503090c03010e030a140a0c0b070e09040b150102 66
    0x18000b040b040c0c08841c18040d6100c80c06605030051400780044001010300000074038265060103041178182d0020300d80104200080c1c001001c246a4010110f03d8207003004120034161007000003000032203c82c0e000381204071640b60f012100742c44140000308207a0964040003083d65000b48511440780c4940e014860980c41d0000c000d500c500c2d07102d00044642e0341050780640344284024184418010b4000c0c09401041c40b00e01214030804412200585c2d034505003401d8142841406003a4046600c030503100f40702c82d1258000c4035000c020004841c2c3c00c2401601d81105a103c060700014031001d2208c4052009480301c45a0b251942c01010700b03000c2a41e28100118102c42d1954600c10f088404080810000c0740aa001990041a0802901c07a40159400820309680d2100c80400d060743c40041d05050f43c55105e140c540081a54150f002c1c9400c60390007000301f40d0048100003810034070100000c500e100c1d01510703403030100d2400030f04030101c5894242011311040f0030864a01500007800903001c010340d1301c046 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 836395935 1250 836394685 836394707
    0x1c0b060f06030f0406020f13031b150e1512010f090b01050405041a0d0b01090c18061815081b031e0a1104030c080111040f050114070f0609020f01 64
    0x29085508541c2c40003200810301c0fa0103013040e1001a402c0015070381c1e440340007000b030020104c103081c0707142101d1641c545031001b007409140c3c0306503004620005016503180c2186040c501955850844035410807a00042c05801001c0d800300b1a06000140034400b00e4100303415035040b500c070814009a525540c041110607101e408580300c0c000340c8204030a20444c0340c01d03803018144440c10845c2c9a00418010042170321040c0c2d00c2400d81d40c02c0005e1004110705c100c1401290340407883c51500400360404d500030528000442d00034042803201280d021490000900300810082c04420fa5255141110f980c3c0501445420340d4051184200410503c2040030f81c2d0381201e01030610f00c00e400d42c41900120409640b58009085600001c0e240e00b010400e400501d00948080c600605a2a00d21403404c201182156085800c200642d88248810003600c040c0e286501c00300d540a080c1800300c0c1030f10400101c2c013445070070717001411020b015480b441400081d070304c4064442c0c400c0c1ca94682c1c11b1191401500c0c800201 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 836397185 1250 836395935 836395939
    0x10602030703210b0d03020a0210020a0506160c1209050f0607120809030c03040e06090a060b1b010204050604091a03030414060c0a29010b090a03060c020c1c0b060f 72
    0xe201c603d940e0601ca0000d43c6000c0c1d544240011007401c0c10303002a02c1300b1034100c411740050340982ca02405600d804030048190030454001400080a65a102521410b009012000c0c569019031109400c034040d00c6404a800d91081005040704c0d8107038000781041a490283d540100003019090641c0d0070b00104440e007054129001341108900c401e41101c811a00506c40c81d1030f03000c140071a600340c00081010f000a032010051a800918026060224083d001000c0400103401c0440030004a142d140442d508003e01300c0c0c0c6507002181c820749990180c4182c0d445160409000140010342c40455400104c01c1504aa89420440d00240c105a0f40b0700884c0511588600c84000f1621940340c0700d4024204213403040151200b11075141ca034500004800200300554081b001d0515422030f80010a007405071a0041d0201d017403801000200b00341d1542400b0040005035074140100801c4d0003008804030b019001418500c111080524081300011071000849004100c00041580c603e0710850100100b040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 836398435 1250 836397185 836397197
    0x1501051504090c0306091b030b181b0c070e06040c020c0102060a0b031203130b070c11010e013f1b0c02060708070f120806010f140d050907050405010602030703 70
    0x2d044107940200020a8040c0601d035940c1000180c00700c036070090240c4250780c040c10b002c2680c540e01c006000d075111159440d1050141007149a0404021108140c000301404005068049462507500252099040755481031194190015004101502a601c510400c0d1014007500f41c9840c42a40d0f104c2c0d4000000307026030000000580000c0300f0360300c14034215a00808441c1400000601001b480e4001d03a20b803c3e41800018074481480603104032540c026169140030004e40443c1d8490112030041c610740c9604021603482144456885040038002441e080d03807480f220107103042c040002100e03d03c4142030020008183d10b0081300681d100d81000d510120b45800407401c00d0344030071200d55003910700403a8418021301040002c120200094920301c1d10401c00640b081000342423a07107400c1c0072201c0040c2009504010044140d174441c8405041c50312609122400380051004940709000715050191010300e80005c00050079030000c1e181d0304031007083d14204050303606e4080403600c92150400103804118 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 836399685 1250 836398435 836398439
    0x1020304060b0d031e26090f1b01120603120e0906010e061c140921030c09241206150c0a1106040504180b0c0306030a080702060d0203091501051504 65
    0x1596505d40303640d070b0340b450010440e017150002c145811014105130390713450700d940080280c0503504021302e5403011811401070000346441041c0d00d140d4043e01107850f0400c090030031071019042c042c0c2c008001035903120003000c20940f14a14000e12003640b0840403403061038028080340e41540903158a82d190440508046d01c1d040340d940e1401c1600c40301d0b0030059040740d9240304401e0030000044002e8090340d22540689100349064a211040405120590500c810b080040c4008410300700d080f688610000d40b030495603002c1c40c01c0241d00482640090201091000400c454001e690861381881004100c5e104800c4a20f4500308040d140103510044549030712440721500445c4000d50750800b0201c0040030135107004e8544d4041020340e940d418055a40e000130001100800075440c00c8580d00401e0010914103520b400c00c0025540e04103104054035100e000211170081d5180d080488114159900c030070365403418004000c0e41d0b2249441020b02040c8500d80000c41c841c0351048100070301c40c81c0358000a007018 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 836400935 1250 836399685 836399717
    0xe01020d060b1e070507051206070f05090603071803021e030f0a0b0f2208030106030f051b0f070803010b0405030d02030702060d0507210501060f020c0d06110409050901020304060b0d03 81
    0x5403100c0b84c26106485200400159070384c1c0e026000700c0310124103000d400c150501c154064402440c2c0c00e5440309000003031003049115121041602d600407918a00310251307603500964010440700540001c0e41001303250312841c2000010070134000c17008400b40d0440e1035200394a0611031700c1703c17030040d00208590440e00120320000d4098100c190420313402420342164140d1000540d286d00300c50042141ca600d07010004100c1c43e034040c4554110401d802c1005d0060b440c11001c5400c6030101883c040e82203450214020303215040081c02d40c3e0700030368081c04495695848041c0c0c90703495082480f0b940d1080c800d4803081c030701e02480441542c0c3d03c50b074040d081c1c50808141d502c01001a250040503281081890703040002d0b50480030b64450344a04d41000d0004640d410090010000045a0300100941d4045d6003030310035984401040f4074001e074204400241c01603024490b401700388525440443c0301401e200a00c1000d040c10b40c01103010710b12a40e8100190100c8006000031450701e41000b4010032071001c00d40d1800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 836402185 1250 836400935 836400937
    0xf010302150c0a030c0c0815040204150f03050c04060f03032a060c0314070203130b0f0f18010e0a0b070308061c051c031103070e130e01020d060b1e 65
    0x18070014000541400101c20300c091800705003500a030b001a01030712084040c46441000030000e055008054420183c044610080c0070001400090040c1e503038200400140648824500242414101c3e00e44100d6032810b020b0341d101d2030a00e506210314500310b40090a4005004400300700c1c0c1c0c3c0341d150f81d5403e1501ca220446c0e02c0d000c1c0c500100b000048000c00f800090400c0c442d1041d4070003142c8001491450101c403002c0c04080082900040d5401009400408079002c81d803031048a450315400c0d036440c22000094015400b6403c0d08400c0c0c0d080110340e0724002c070a43d12240e1901e071420790300c0c0490110040100001580e0a204601702c1450400c014404207208103080c076800000545462010034200f80100800c5019200907603a64100701d01400780e11801100240d80c0380d0107450103000c0040103140c2d81c0c1c0e0034800903020320244201200e0000d400d403550382c021200140ca0403000c11000d040042c0c803a02035405100400e19103440c100c0d000c6800e81104054070799241041c40110803840069407001c0311 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 836403435 1250 836402185 836402209
    0x1c15030b1e061f03060b0a031a010318020409170c0d030b03060c04030b0a060b30090d0f0216030b06030c040c0807030207080708030c120a0507021c05120702011d060f010302 76
    0x80640711030006c540400702c031000b820103410710741d0001043c4201104400007c0e46030702010f4100340c28090055110580340310300c42041078040300c000035118000c0c68a0908010404d0010070128030200f0b0781111068040782c070300682921901c2c203112802400d030030192107074004c072103040c000041440b0900c04901d15520b05070303014103200c800040464a070b401b5402c071034002c0b4644044900742810030341083c5048029504030380d0455510a8000e04001c04401d071103174a17202c1400e04020b81d42d051001140c0c130030852103400390700a0050300407054490a004e5841c81d411aa010301a115404003446141004d2041310102012595260196168a00110040d500019058039850300611080740807844101c0210b024116000d105030313440c81c00e80560b54402400401d003809651500c4204a840c50300407c40126040506592140d40781407000f050b038450240700201d5424602000802185540552100310521003264540c01c1c0c50703920851090395008211440740c180c03c5958010401414190f1410039 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 836404685 1250 836403435 836403437
    0x2c12030702030903061005030706030b090a09030c0602030f0a11070c0605030a06050406081b010c0f021011060f18071d0403050903060408032202061c15030b1e061f 72
    0x128140070f000c00240340500aa0342d13080e2490005c0820001482c0810912000f4036181c10309011031507020000807507a07400141100e450f141c82d42c600da42054495180b41d084254440007c5482c0c0c01c040c24021618041103c0d2400707210320746420000c0800c4640266494254041c01e50140ca6043c054111116000603044624003038680c0804216555540034400141001c00021308000d42071514500b08004030155560501c28440b68641c003040c12840c00ba0252601503d44410a541281081b1050441c03032690b81898041d640500c0400e207141c1c1d40e001e010f1502090294a0b80a900c010591524001d03c03441c4001c458070481e034000c01d6040c2c0d0240340d0090017410170ba030802540102080c10204215021a6902e00010821102441440c004050013503a030110b60002200d40d40411400e1140c10002440c2c0c5a5101090000f10129003280c8141042c03101e1804103155a0300e0a4114031106130b6052102d48a004100d0000c0002d20036814480c0d8402030442c2200700c0e01e40000b04418010400100c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 836405935 1250 836404685 836404687
    0xf04091b030515101a0a0e09040b042d02010e06090607050d09120804090b0a0801150617041e080d050c0403200102120d02130602012c1203070203 64
    0x4200145041440d1008600450161aa05000d800301c640f82983c024101c2c14480180343c8140400b5031351074010b0042e0502a0103030380c1d507803c017003c080d240407000c0700034158042071840401c410002c040d905075000d10b2044030f00c080c1542c898002c1403a241d2441040200510b01c4d80c242001540c03080c02c5125802801401c15440c043c24070002c105241e01c80001030b02c1c55840340003404500d99001e0480001040b01798111040c5400700d640e069541c1c1708501c58601c1c1c0301e032114211480e658400300c802d001800c1a10080040120a5889403c92001c40c4149008612020035406a1110586807207204907845148240e00742c0f4803117003603141551280c20950b980300050201c10440e0380b03d17100e028002c00d24807000f80e80b510300d146001252105040c2e9481c00c0e288010940c0001640c0004118250b8050b403950039485184115680000340524800720000180e43c1d00c0015a00d5010340c4009051600c11441030075a4100027211400c0362070b5802c0a020503400a100d04052040d000302941e0484250710560b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 836407185 1250 836405935 836405963
    0x303060e090706080133050910020f01060f03020a151e0834050a0509151b07080a081b06100509011d041106120106050909010605090f0409 61
    0x300341510801c40d40d20070158400b110034010140c00501c40c40c010507090411002001244070041d80706100d21100041440500003881915400f03007082d18642c04020b004503010b070315401c50003562034854001b845081c0d480c5c800046100c60101844800707580d009008800750314038055100b2581021040c0c103404110f2040700c81c40c9802c0c0200380a10280702107540d126020304080c0101c1c42107021446c4001c0301c3d60004614000800624080303803410345001d0a0040d20303000c80380000d440d2803041c1200e50340d00c5071f01850015a03c26042d006000c020042044170450440346014060b0f960b119801241a43c0e4408803080b40082c000c000105038104400d803440380d0608010756818500101a51083d0b0b6142c8008000d01850a150f601e103801400500b600e46800c0701c0807081d0300554440640b0180040045214800450700c44600b15400301045445100c001c0da501c41c001020768018201d01489200c1140c000202c0038030030003d59203110340c020b01104007a080501000000c054480c41290402c2d04d50b000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 836408435 1250 836407185 836407199
    0xd0e0603091614010f081e07021908030a050703061805071b0b061906090608041a01170c06030c040b090d0501020d020702130c0824061615050c0313030306 68
    0x59100408901941c2c80b10400e0840000d410203281c1700001082140d2401004a401d00a2160880003000c500100d8465114052301320f06002c59070442c00c407810140c01250040104044c0154480e0304034260401080c0c4803c01d0481c1072b2480c5109401c04400e110381c51802c0245981d00142d040ce0b51400c04407900e020b24000011542c800c600c069880082143c02c01045084c0294268402d00802010368002c9040003009809090a8040e203802c00005800042c1001040400d0b4603001d214514038440e25039585090b5886155550780d684100c0c0030307210200300d0500307042d8144c03400340a50b030b40e00a05050400f55591843d42104070219842401d459812001c40d03000c0c401031440440d030280c0036a40b200035006004910000517095111103250542140f021a0302601164120080414000d110789159074002010f105440603640d00440000b0100b801060801000131140d02c00c4c10700f102c80a81741042c403001c8a0301220100164101000015140f40070001c542c007541e842424002907003030319400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 836409685 1250 836408435 836408473
    0x1e0a0b190603050a0b0910050115121805010b030d050c060106031a040c090504061a03070804150e07061716030e0304030c0306050108011d19020f100f0306080d0e060309 74
    0x195008002c1c5c07002c0c01110036050000006103000d00c50709004c2540f501104540404544c0a00d034200a18800c035024103603096080108200c03800341801031f0340843d41c00d08034002c107040040d080c03007413240003500c00020b07010b0000e60b940140d01c1d9000c1c2c21268a40401540030348045007000034400260700350b900c100e030340714400d01e001c10702590356401805040c1010700c801c07500c05402c10070b180c041c2c0d650726100c1400000308880d0b1180a40c5004011620780d4a00061a800c0943c80c3c400054101014a210b440d00000c0c00c408545459491380d48a1144a140c00743c034060644000d140031401c800074800050280e08032090360794803e42124603140d960f0b02c0d46000e0550750b80045403103549550040212020074040c40d05c2c03101451110007411016400c07055500c46102043c000c8442c1c20415001c299500c1060140d01040040c01b46100c2c02e14065000342150b81407a010004280f9041c0040385110001584070a002d06070b8480020910070002002416000204242c00341e100b0503180131000302d0212 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 836410935 1250 836409685 836409703
    0x909110412150509010e0c04090827040b0108060306070e0a1e08010e010501060207031502120403020d0230030a061203020f0d0e061209010e0f1e0a0b19060305 70
    0x2074192102e44242080c0d030054a101805076015a070510303020b19110031002c41c0300b068182003240d0019900d4214509014240242d0a201e10104030758003501da0040c140724400c1401120484040210240707440040d64507401c03d80311250154003200014607054091103004940a60080817281034540c1c401e00c5400c41c210303560701910501c54555017005100c0c0240107081d40e00801200a0042d9230501e03500035030b203209503c8090504803d20141181c220001d6046aa1103071680c24940c01914060401075070b00d4980070072035401403146c44040c00c9415034103036024804c11041c080c1c0b50016950300403140c005420280c06a80c0c101d66569000070760000c5c004208140700e110350080e0821101e4104006d041141d86040041031116051460b516503540d20120b80301030706400d248258139260700011a00501c01c82038901d0182c4605910800c0810001481c0203190742e5a5480c01080710a80881c1c6840b050380c0007000308800d0b0742202194440094196030300041c60710400000e01c03107541c3d85901b450040d10b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 836412185 1250 836410935 836410943
    0xf1b1511030702070f0504020f0909100e040b010509060d17091c03020601030b0f1003080c010e0601090204090c090e0c34150506030c0603071b0803070e010206070909110412 76
    0x13800c020480c0c1002c00700b602c401480220303421410031700801542040c610904848902c00c0031004000381002e588044400b01a042010048001c0c0c503007803419100b255020300480f8801d414000c001a00c134a020071810580320f82c009500c8059511410a5000f141c120b5a00d41d940031b05030241054480d19114000801503020b0742c0180341c19407640c2000741760620003030710000c244600c08040241c142002c01d012007c8a0344404040e07a140c070503060060042950320300a103014001c000c00024800326980107001519000c900400c04a448148169550040c500c1703106000d0170488001601d09406201070840001c3d074840c05200303840000c000301010101081d4070180450117015960074858003600760f009000852808000c6410902c0002ea5034510000001e0710421000001400081c4643c5d00182201005140c949881815240201301600300301c40d000c00180204c142c41c142580700145950141c80c86844481c6450304101d4042e0240014404011960740d04103c0080e6030741c04100c0b140841409 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 836413435 1250 836412185 836412193
    0xd260d0911010c0b190603060f060f0801020403050a020d140d0201020a08180616020c210610051503040204061a0304050729090f0d0b070f1b1511030702 67
    0x4645003204000101c240d0240c100141c1d200003800084001d04d0b800d40244150000c07040c0e04400c80c0c02c5401030030090700010b06041c145402c4005a401d690464815a080700070340302600c6444070000c034202e024a01c00502668001020a40541000c0e260524810b0150141c2c08ca8035045425032850301f0800e0014030010707940000d40003040c60703026034525040100030850003044150b541e103299592801a060240c241d24081e07165003218000c1000c00d6404001602d59134841c07402c0d446004419401d074461221600903a030000d00758500205071003041d0781d001050541c11503984545005103400c0140200e0704035540c2d0b8004100c1c440244640307914110407500580d604d05e031a1074140e0030068541c1c4603060407082202101841c40f014040950000e80a2285030b860380b070a03174005203003111545035045d08139010715800e005010281c0106446502036407544200810000c4003240c013482408201a4075040107070841c00001d03103846924513510003c9001085841803020b9030109039005a4000c009644 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 836414685 1250 836413435 836413451
    0x21008070306050603010b0406031e11070201030515010804030f12050c090f18060d0f080301290310030b0a140f0a0f020c19030504030f060218030c0d260d 68
    0xc0c1c5805168080d01d001d86103141154500342018407a0b01940c000ea000745502c80c0b03c1c4030084076289040301c1a40040d0682407000003002c14000c4c590f9840640180d00003803c00d0000790400f402001d61800585040e510b01c402540c1d01e4900b00e550300e03e1507050030300300314100c620711350541146d010320390191000d842c0c55580e600b41d1008000900c528203031428062660180c454440c41000d801c580c1d8411007ea0f81c0d0700b1624010300c3c141a06100070319004000840200011584401661550b10780c51481e126160b040e912090303240303100d40804c8840b05400d030280101400020715400b0300303541004e0f0350480400d00c15201c80d10384908050484080c2680c268120401405013028080c1400000340c0c5038045241040c04040c039900d03031a4403441080400800903400c401c1601c240100c800942e002608403810f0142458120084c0d03208142603508107502e03401c803450385d00c1c000c204002841c0c0010440e19042d030b030a680e018818507505981030500b2080c0042824804c0d0140000c0488541e00b44000a03040c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 836415935 1250 836414685 836414687
    0x120d0305071101090b070e0a030206030118052401030c05280e10090b031503150f0f060907110f0307030203040f06050909010e060f0a090e1507020718020702100807 72
    0x100b8041491160b814420344801007146142000d07000700c0c01c1e14005115811280100d8500c0c20160b0000790400400070000403800805c4179480e1040100c002c0a005949901c1e040d01182c030411195101d01c00341062548e0b08660080d41720303a81400c40c900780b0034140540303101483c0c0013001d25000f8811000124195140c5142d000d00b05002070002210743c5c1880307000110005040c1c4406000d08103892900001091050407848812a08200002c080f40c0074070609000e403044c01d80040d80d4900b100361200000c07074081d00100c0320712445003801901d2842d4070ba81d9060219014824808241404d00441e641951074020500040007801e0080d0015136035a403904004000341c0204e54410020800b091140c0c0445540d0310f0360300c2d411100a00c840d1a515203031000000c01c001e01c40f41c02154402d030a0b0400140392041604000d012407116415126a03600301180010380350012a00c00d80183c119180c20b0090520000c4c9102000c42100001410240107502095481280c04401c4c40491031401c2000070417 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 836417185 1250 836415935 836415947
    0x312020709020a0f0309053c0309010f03020a17160e0a05030a0b0702101d2a120307020d08040509090d08040f030e0a0e090c01020f0a030e120d030507 66
    0x245100e2004620b09108100000c0000002e030030280c0c00c046e10b0311100c07820b1081c200814036511000080e03441e0401d0703411381c01560402c010081c64091090303982d40075130100b50200c01e071010000180c4900e00c190030a05403c80003584512005018401e82a0010341c2c1034140c1c1841c0ae1181004030500c00d00e1901c40b0b60060004d2090103240c501c181c0701484180455103012565180f50f0354040403002d11034072050b030245c1c2048040c0c61818050b9180051030350310f0460417000084807000000640d03250555480019400300082d940d81c1140099064200000341080e0b000c00e01038403003884c241d17800c00d03000342d00050004102d03603429900448042010300543c64056a1150090540340007880d240c0c1e00d01c58081e220000051000c0c01c031610104954007454020103080c81c207a035000700144406074030b400c02003070101c0c0706994640e86481241d00340080c0703500010700d00c0700d54100790004100e414455130703045625055244045810603407001d0f4010840d0800c2000e50741241d12510045000d01d0811002002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 836418435 1250 836417185 836417189
    0x423070e060112050907050415150203130608062803080705070302150a17130204020d0c03050a11040b0703051308150c03071b05011b03150b070507120609020a03120207 74
    0xa18a440c4c14049078180000354001200c1007501d0201d41d40762a038400403242c13522644006440c0180b000000e0516034080001c2c00304004070802e55880d03e03100c910489542d00c00315101a0814440d06209400011003a80104424030a42e81c0161182d180d079541081c0350005c2070f0898860b031058009000f1443c00c1c030106c12400181740107850a024003083c00420a49401008403505482c800103d1100707424450180324041d0040c00c1507684100090401e0028004100381c840028900804281d11014500540385101c8080e4a106e042500b008440384066008080440502c201000303040e561a1854803114000c280810140c02045012604071400403001808003440366000c1042004080d00400400b82d80041c41c8402c8044844034074200b070041a0002d07a00a020001003c101c000319450f810030f500780d140078150706141507541d00f4072003a03a0065201c000c20580002400780170703006260004401980c080c12010541d00c4080d008103540c0d03200d940060701d1303d0b080250b075a640c154041110b100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 836419685 1250 836418435 836418467
    0x1092001021212040c03140d0e030f2e1506080a0b1011070f0828030c24021b06060f0a0605090114220e0106080423070e0601 55
    0x224202c0b58494010031032042c502818804006032021034248180c2100e90380203954460310746080d00100c1c012031030781c0d8605030190703c002030f060a980e045103080203e020002c403c10603000b81042401c1d80051080e89035080b14035080d00310301102d020103100b228004c0c05a0485101a0051540c3c01c045000300701c201c3c0108048241030400d21082e40c0c58642558010000540e0b242c606075070460f200c4040e090000036400740d402d499520030040380142000c01e031500100202c1c0c05030411100080c50032540c1a0303901c080900414499002000412060707524440703050440064481404009002c442c120303040203042d00c050000080c10402e0850040241ea900f040d030403a07078186044002030001c2c00b40d84407030040c9030400c6030106509081d0303405a48444100800040300d15100c560402c1800c08540c401480c01e0b034032250a0304e00159000c500c2000506a4010341e07500d00076a980c80c0c81d1382d8030709486118400b4407170300e1480c02d509410704280820005000825104903c505107003000501582d1f809800341 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 836420935 1250 836419685 836419693
    0x3090510140301050915030f010c020706020609060c030603030f18040605240d090213090b0f04030203040621050a06091113031106070c1502061006050711040204080109200102 77
    0x480c54602800390b0f81140c90488260415a441c000d00e11086400c0c010382075054428166190700c42d000641250381280099400c50b41034560307c200890b91148152001c0d901c0f41c000101052503031420310000d6900040140440e8609001c004e078030542c42d40280300c07030462102c00c42070343c1c12607103094000d907001014101e4003400d0310640502014881c01500c24100305589001030040c1000c501c6402070342c0001d800400c4100d90030010100700001d440506001c91b4102220070000d078040c102c20080c03c2c040e0750554001c6003440e0428100741e0303001c140c0e8159080100b590300f040c03c08024490241521032201c481000c20000e00d80380245003900d0100205040000051000c0441e40c001d10340031900b200e8001e0302c1c4c20031031000f80010400358440c545000d404074450b900702285a040c1540c014401203038950032030b070b5141e40d41e00310014200018001c0c4000903208204250100e142d101b40d0030810a4010001450141e0713810103c0d08541c0004011680300c3c2003801041101c034229008880108003e001070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 836422185 1250 836420935 836420957
    0xc0304030f210e0105060909030a050d05040c0b040311130e100228110d030b010f080405070b16020109050a0509060105070609121715090a09050309030a03090510 71
    0xd0302058080210004101408003a0315030440010902c10401540c0e030400c2100483c1c0e0003a007030207031034202c030301502600e80400424000380d800402c43c0c946134078035aa0a420201c02c2d01e40000980b0f80548192081c40c186000440e01d4050b45004200542c8500e10902c4440505d90078131802802104800a401e80f03410700a03598524085203102070b0400124005a40b401442c102156081d451200540b4038041c1460384800c01d1b03008040c10410818600840e40c0075450b0303500845c203644507041c60b2400550025081804103008807500c40d0064450700c15030b03404a803100090445500704500c4141c0b40b4241100480075940c000c0e031400c01038401641c4203210780e401c01c00443c2d00d0002c09000c207410007200040d91410312000b0b038800c01d041507000402c0e00e0500381c907001c01851400b111040842c10303011000400c0100c03c8440741281c05100c064031040d01c0e555200c0012008103100901a203c80c0001c001010a60f0740a102000c4558426207a10b00101e0401d401d01007050b11000300407040c08240012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 836423435 1250 836422185 836422187
    0x3070501050a0e0d0602070602031b030c091012151a12180a060c172d0a0204091d06070807050414010507020d030801051e011b031404060809060c030403 67
    0x21a41102c5443c20020303c140f0440010581c3c80945180c05080244080343c3c0303c0401005400541c061680031b4200c08039060303410001c241d14801959200d144050030031094880e401d1000303104402c50807604100e4105505208640283d642c0f50156000340850680c0c02e0040511903070f0380800500f0810b05041c2886100c0040400d00c0380003400101401e2509081110000001c000142100390b10072018401c0c1d250010014118414502039180c07030325454400220034581100c2d480100000c504250f59864410260b80d00c1d0300c1d580a00034510241d005c00c804a088503143c014030b03000b100d10a0400d00c0e1055005200c074205003000d00101d04004401302030204081d44441a9401c3c1c80d03980300181943c11f43e83d03005130303140e03c102c0000940000d0704001d41c009154000401034102d59080c1ca01450b104060243d000600500383c000b01d000c2100d00e690401d598603640f13034084642e1321904002284c51030b9440614002d030040e81c0300c0d02c00170700c0d1581089003242c0c09100c05504035000f501014103608103035078 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 836424685 1250 836423435 836423437
    0x213150902070f1106071a0a06050d0203030702040504021507030507120305100b090d231e0a0605090109050102031305160308071514100e010f030b06090c0f0a09090b0307050105 78
    0xf00600042d02d2000952034941e141c0b030880741c40b95801510359140014564155114180840f80501145c0c0b50040010b180c2c142900e4035108554010003852502880340d00b00030007800b0143c403e0340c2000b0101040d44510040034018044203009443e02501d60902d850000441100c0c41d501504045c2018240141c1c020001e0082050390909404680c4030707220180403030340d20316000704060040803840ca01101103148a01c0d1000c000071004040e122001e001301342c0c2d000030028500440105d5070007420400c5c0454034075400950000115030002c140c0c542c4c15103031142a07030810784134040c2506020011100300501005000490071409109000052a60701c1d14440c074020f4450207006d01c540c1060b00da5003042c099004060500034520440481d00301400d01114083c22805030354102d2450b040081904d0a5101e020400c4a40c08801140159980001e20940311350107046e5000c3d0040a002805211003403401030145244159206182e40e407501e4400819034215a00c0680603406c5070209221a0b42d2241c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 836425935 1250 836424685 836424713
    0x9020904050a0218120a0213060513270303090f0501140a090209012709030e01121b1103040b07030e0a0501050a080a0b010e03030c0105070305221e021315090207 71
    0x1d90761a00c00c0d41500c121420b001c40503400070342c45a540c1002c0c123007505c881d0f8080d50955500b034400c0e0071110100f20303800c003c881c01e09410721214840324051805180d010707224000194843c1c94041820aa195209004d102c48054216026512901e0840c80d0114980d10a6030000c1408400d003d030b003600750082440601d0600509003010152100e021040801d07188000002540b01000c120b02e180b1418000d04082e8910001e80c00616002c030b01d003c00b040c60707000310201c441d14075100c0305007031641050950b000540c500725001c0c00e00080c08002602284030307000d84509800303a22034592076490b010401445003403030b4010713305000062050319103207903000042543c80240c000740011a40b1454005a0b41041c100302d8480e414840041c0610740300d130041d0071a5000d60655101030040d5121152940da20951001160150465515841c000b16a0032144005440e0b898042c402c8909180d0f00031505807a61200c82040c1c1ca62160498040480078045800013000519411030030880180d55400b0b502842e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 836427185 1250 836425935 836425939
    0xf0f050a030e060405150901061406070215040b19030203010312030b120d0c11030120070c0504050108010920060405150c030c0a11030d080a02031003060609020904050a0218 76
    0x318010354590301036072048101c01c40e050115080351419280c2955244581c5094064030192a0b000c600b070f041d4140100426540300c4024002101c2d065028080c01ea00f1036001a40d11a07406140c00c10395443c9240240064003e6030181c60755050700b625841400481c0c116004d00b00343c410001003010a10340002451440690301e000714100c0001400203000c40c000c2104403403d070140c8030301c01d00300c16040a403221907184584056041c00442804041c01c90b00c8426269041d60b100403224491140030744010a01d07144940d425401e0140c039113004ca01254030982200d45540c0d5541d0301e5000b440b40703074544a81c0302c544c3c05404100540c03070382000c038070140140d11485010380e07051442f000c0200ca00c1d030107441e10849910700b100e8441989850103a40c03070907a030200f52114030359011462400d09012824203181c80c60754451181680710807026100a40c4001c0003044080c810380f01c0030000503241d0013020024828030300050f0f103504140040000304d445c0941500344051040115210300e143c0402c0480000f941 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 836428435 1250 836427185 836427187
    0xa12020d0806041a100302120c070b010e09030403050a1410290a0308070c031a09060f1e07020d0f1b0201181802130b1303110111010f050105010f0f0f05 67
    0x1048041241a0f424074038865401085c82d11000e200750f606034003414101e041c403464201140c0b995400035030148219000135100440860051141c0990004c1c1c0503001a20319046a14141c2e403500d8042c20700e40c9040c0200e9850143c440c0d8880074600c204100306400b40b040504110301c004032a5408617011500083c06030082c2903070320401041d50f0343d80060000310340045007503503a02c0f05458003030603072442808201d91009101400c600740c03103481a00c2c103205a6a050040a058a483d0003411100f20010030312642515400b48906013600480b0f9401e01607a0160003c00381d810940c17030040c0c40c076962180d090b402c100c00ea5620360717600941d600300840e135a902070034030024540f500402902c403800c854210940f002d0a80c4022390b0419495802003025400c80b600340400d103925070505000501c00c0c072074004800304130014103002081d0501d0280d003507280c0506001c500701d45001242030030366643d079405a2015583e0381c01003040396004032100c44881040e14010060b000800c00151502c20507200f03882c10004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 836429685 1250 836428435 836428451
    0x114072c04020408190c0f060503060616060e0c0a0630141311100e10050c0a0b04020f0904051c05040b0408100b010912031d060c0a12020d080604 64
    0x2030741e50450b0040d145060603107000700c2026201c0545940ca80108580712000c50000244c41e403040308001d02a83e50b01d07903e0520f940c4a810400043d60000890b84100c03980d0241c0c407000003000c620800c0a5201d4080190902c00780c030f842008079051140e8040401e0080702100d03c0d00d60000e150750043c010f48a9007005404100301010309005040d110340d4941c803000d11100307011040b094665652900c1c0e10800f80550b42c4502001441091059000e201c1e0225080191213505031400c4540c00e0b8000195190060510264100b03d9142007560103060712548a400d0600081d400d20a091000c040c9059130303126001d0a1a0795040d0f51407c0340c1d8014070441284c41080d01580b4030880c106d800034020001c03201d0f180c1d91103000ca1621103511014490403d45030241c01e080301c1d4060903040c0d0441d08510075607600d01c9800e413010f45e01c000300f0100c8540c680402038400041580e40e980a030140315001c0009121005541c0380548840300c5001c01c503002c0d03511211000710303019405005c00364013181c15640130411803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 836430935 1250 836429685 836429689
    0x6120309150933121512120d0609060501081321030f05062409010516230a1e0f06060801020a03060f031106030601200114072c 56
    0x1015401101e5400408030f80a02800c00701c4580e0039044a400e860740c024041c0207540ea0f11002d200d0b201440841402c03400000303044000d01c1c1500c2501c0a405010007010604c2d01c07030207900780000c108a6000c8003801040c0c10004603020b102c0c1a002d07084078981040024101000a030030500014200300191102034105002c0000c440c0700703080120b1342203e03003220400e2042005000703001c06081c004003082c58940003078001e190031041120300201c0d12a850000c0161400300c2c50f800d40c400441541401801c03c80c0b64902040d6034541a503980c015580841c50036800c1c00c1d02030031a9503484100105a1114002d400402d116200071480032101c14508180380010307140c0b080b420301c500b6901800d150301d071180c0024600c106400070188161641e408102068541035040140a84c078003010745038501c00841d41c016810408020341d00b28405050036011201030728001d03131040700d00c000c030041d03203945903a510754900d49812022900850142000d05070b0300c00e082c0142d0100d142c8005a0103548a61044040e031075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 836432185 1250 836430935 836430937
    0x105130f0206040f08010203150933060c010c1b0b0a09061409070e10030503030c2802010606020d0809101a1009080d0305070f12140412080612030915 66
    0x41000d43c14000b411a170362891a13000317400427200400c8640d05401c0841481c50950040d81c8a101c031003410388000e1207036090140c04080c088030000703081104911092116070311440545508039502e400860681c0c0146001080170b400d180c040504061041007410016120b402d0903580841901c07000904841d01c1c4c1402e0300a040010500882c4c540c200003808100940030031100266820800c2d0715082d500c4050314118481c02a200140c004e41042c0049480e254150004241280762841c4c08880792070050305607040030340c421050102603903403200c00300080d070b07010b0240d02c4110055007007002c014505486103640b680c0c0d600d092040a542d0fa624803121b40400b448a0901002c0040c05000000d40ba21030003810600c401d000b0704039a4072880d045c034030f0918828083c1d03a11078421644d030b80e500708003054030503541c291720050350401158941000d003012a01d0400c0c400e1107240610f12003807001072020400f03418908080c2c1828021290800120711300380c0000200ea0441c20244c3c0d001720f04407804c4071000301c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 836433435 1250 836432185 836432189
    0x40f090c09090507050c15161817030d0506040c0e01031e020d060f0911040501111207060c030f06140f010e0307081c02060601020607050706090b0f1005030105130f020604 75
    0x110b180790200780021250b0085c040c0403100c0d078007006c80340c41b00c4500c0c0b541514070508880e4650308982214001406511410120003d643c40c0541d0708401503c1e14503030110288000c2c0d0320400303030340082412500480107000700754100c02c003a541040f4038021310000806110880d2540d41c10305443d00c0324260b02200c8402d43c003013100c2c6060310443d150b00c0c4107141d1001510080c4901e151502c110400401c0c06440c52040d12840006c11034010b00d001c0c40c2c00019580103208607078003245402103001042c02155003d0041c82a03510880001860780030918010703044400c2840002c840d10b1a2032820301914240102c0944d40340381c00c484000a0404080040340e9804d80c46003440d4050040b000005156400050881a40d02c0642590710b00070030194400c0342c3d03882040301c103d80141d0112001c40c9929005d10000c007401809400b0100b5501080c3e200c200343c03000c099071521840c0c0c0c80a001c0061780e000e65807501003c3d00d07044000740b00034244840c0100a20012080c00380c103c90b4840108004c540e9000300b2100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 836434685 1250 836433435 836433449
    0x1120b01060522031b05060f1204080f0f03010e1609090b1903290f0c1c151505070b06191a040504150b0a08091e03030912040f090c09 59
    0x83c180c0f0b82c500300c441031204448900c1104000140031816103400300559004040d4194660308014503600950521500500709a0302140c040101c4144a9400001420701140750245039030f9951405803003526000e402480c0e0103101140c0c520219410f42d001c56030104854038130f0f0010130100518000900318000e0500c07400c5000c007212000004022040c0e0784000141d1007041d0b000d403c00c0c20074003100c0c1d40c208102ca0032a000c00c50a07002442d5400706c10040c20085d40400b030034107040440150103104032080074000b2030101071510010040310341512401c940d0a0f12629000d4203103442a6944c01070f50034054420752144003204104680001078082c910b004241820b40c80031071400300309103a1090b504c103000b1140118100700c05481200c4491040310121803040d1814dc0c44c00c50b107114104d80004001e0036420550080c4451807080e09000303200e070310004225602469507800d1404035586406845c102100b401841401f0801c518160001b00c0d20444845007404134810240d20030444107010309400c024 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 836435935 1250 836434685 836434747
    0xd03050403172e0e070801081504080d180c060f09090b03030702150309010c020d080a0f0902030105070512130c1502070b0316021e07090b040608030a030e0601120b010605 75
    0x40d410503c40360b07444088407242c0320400c00301c0c0c4888104854800090051090070750000507007821003101048210b60141c05040024149401340e00c8030401e440c10f252074208032031107150101c801d00c14202c1c0608000c003005d0424031022100c0c48000b800c6803c040c480c90046aa40e14204d5129407030038021940c80c46d900a1640f03c5412000c3c5034049150400e541250b07071586040b4514004500010301d006c003d44190311404c02640c1d580211001910141070303c202e0444d1100c81080041c0c0f001d025145c00b07000310791503c0e0b80341c2e40407103006034a03641c006000a08000820010001041d20f1a50400540e00020030002c0c0c8022400f00c16403405407194030081041c4000420420350f00300c003007031070340c1030300050342c01d45949450248010019401d600160758150f000704004102e41d007210386c010040204054404a1500e554000745402d540104c10840013180d296084508a004184844d41c0500040f41249650103a01d899201103494140034078002d212000900f940b51076103840e0419940d1074060641 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 836437185 1250 836435935 836436001
    0x81204050307050f030c0703060b04020c0d05090f0906060a0305041704061d19090507030603080c01020406080f0108031215090405100c09060c081e040b09030d0305040317 75
    0x81d60380e03400258280c41c00c0c01000f1810850741d20100c1151241555880205647c41c1180c4400c0014001c020806900c642d00b044440008a001d01c0340d504a041d55032500c40d10380c052002441908140c449071707244505103031010002903507241d9040d00e850610303a01d40081c6954441c030704414802100c0303c1804582c0c00116001450030b81c02006000f103540e441300200e11055010086c04410560340c61050154080e12409000d480280d41c032156100459241c049810f9541e5102d042959001912200044e50005010301595412069281d008100b1143c0341e182c0d9807408010945070700400301e50540403420900401d1003046001000b0002e444028040365440c1841d161080e0780305405418003030303c0c07400d203c083c07d0310302d0049148004540140c1c44039070749040160f40ba20a103034407031140b505802c104404d06540b00c1403008081c1c001350852150583e9250401400c15181640d40b418030010507041004010020390b20143c050949104c0354525400b6881d10303200c00241c80c4000720303013101071412041a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 836438435 1250 836437185 836437193
    0x20060108010b0f1f0e060a180b0a02150c040b03070804120203040609061b0827060f0a0503060328060f090803131a01030807121701050607081204 64
    0x40141200c15460007000303401e03a0710041c08441040086002c0d44960070700c2d1295405480006101c0c644070356450041d030702240c1180010a0341c4c000c5500b40c800100113401043c0a0803d19030a0806404502541420b107480c07281e00940c0c030038a00002241d080401808503648003408000da401401900300b020340c6a14103000c000b48640c000700e03000e44602c45040364200259002100b01e90641d0b08039a140c00b0300351b0400c0700607603491115195418034901580404d00125014101501c01005102c2110040d080d0300c061525104100e0340300688180000c02075580c6860022040b0345400c45a42481c6403a59526000203050100e50000000d0a9000104c5100c000091021190b10035229850411403400900100f900301c4558060043c4035502c1007010a0711401024000d01120744502c12700100561108120082594283c0c0300710b401c10004503a040401aa040d04211407421514000c0c0d030040300360340e51400d20101031084c17a005d00740020b0041c040c040e215048400800d14405070741a07600301407034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 836439685 1250 836438435 836438443
    0x15060305100f2d020703120203130201110f0d0e01020118290c0703030e0f011104090509031303201905030705061606020306040b130c08010605041d040320 68
    0xc2c400482c50300d0711003149400701c07002c4003202581090101c03600000458000450095000741010ba0030310452456041c084c810f140011031050b9194140d20340301c03152600c0003410000740300c00052159000030354000c4000d8000520b541000c40c0e5460141c034200c03c003200503401003410341c42040040030400d0030001072100140e00c1031840c1440240d04e0713084d40343c00d1042142d03d5005485200080008014003004681710350840c82d080030302101a204103021350900c060845c0c51070848032540d004042010800786074248680e03603005900c140507514041a841c0701012600e05070000514480080000c941010400082d04c4140540501400c44001502818003903a50040c8140c5101c0e03c190200460340d41412001e507848504101d00f505515000c2d9514400650402041590050765445000485903607441c1e680c40345034858580081d500c1c0b41e055004200c0c8005800c024107011042100304110710313442d444600d2018003c2d600fa040d548991404903607010090314005502c0d00882e80f60b8850b52008a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 836440935 1250 836439685 836439701
    0x50a060614030c180c040b0d06060f170f18030412050706020705010503220611070b2508041703091f0603020d1202150703290307031506030510 63
    0x614000c200001d9804240e40c1d050211151908491400841000302c04080089600842030309852810191107180038000307a0004242405240d0702c80c001046200e80040150b08140000d240041001d0030001c40702403080c002a0811540e04d03c0d01000030b00000001042c1d20b4075050020540e60784580c0d80d030a0008a018080050342c050083d0100080e0b610700001d1400219501070312040c2c03c550324480c03c3c540b111800481c058076030007405c80381e000081c0d16200c0c0f100342000079200c81e620346403517007440180d6940040c00387c1c901100c641da46030328410105e40701c1c000841052804a66568507441d0044e800e034914400355000f07190104c00e00010280100704412900c02c1c8091903199114101c0e0000c05030359a034803000c0e404c0707007032058040003113012920b00780311890050045075a0101080c9144195010880e48407001940d610400e80a0100702101c0d1007054184c125161a03132121040003a403038071124840140002c0101689100003e8250081c0d401150000c0c25902140d10241d078000180000d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 836442185 1250 836440935 836440949
    0x3030b0306270f19030c0c090f1a01051e070c0b0408120a0e211213050619270305061503161403010b0a0b07170a020a02011b050a0606 59
    0x4850340d0b0028501c0000d0481c0300d0f110030402080d03d10910b030440200038001c450242c04010301090403c0106e00c80040320300041074560f40005c0d40c02230410907041259801241e028140100c00c030f1881c101d80e40507040d29155400240404609501207010f241c0d00d1089900007001c40c150010000741d403082840c0980109c503850000e40d5010110000071801c6441034140c500d01080c03120643c0d00003030070000780038100400c80a00c00c1c2141030048042078507002621544410f0030b01c0c0000c0041090b8142884074008013001d81d030003070402030301d07204902056824030080c004100c0f00100c030015040303101d26410f052400840c003454a01d81c0b80c1c00c02c42d4642030101c0fa1350040113000011110203060000700c40138115008990341c10428207110300c0c0d038201c0600a42c4c49074150348480c0c80d60b8503540e88010b031b00001c1c601c85648960f1400f1528200111801d040300082d1801000c0c800c041a09402040103600c9990929089980b002001c0f04c89469454080b07014000e8403d54019004009030340d40400269949 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 836443435 1250 836442185 836442241
    0xe22050f010b09101809050f0d02100b0108010911040317030402031614100e13020405120303010f090c02210a0809070605180d0f0309030b102103030b0306 68
    0x26480922014034404d0342c900e15403403c03401c010000c0301911545c01081e11403420000c01c4040c002e0700c03101d141c0f10b4206241026030300000c1c0180070540d010082030b0300716000340301c081c4282c3d68001c00181c0790703007414400c002d909031312003882100054402046801541d07002e041d0f00001108410780c0c500702e41045808038080d03c184ca000e28102d00e140d0303028104a036a14420b003801181c51109001105420750018414801110a40c0d0704507500c7d9405d484c0da002c00c542c00140c03501d19040801c00449208280c0c0f030026003040005000c0032681c0c40c101020785040141c04901c544090030201d03e0119129484201118407002300940402004024018088290f9800b82282c60704000c0710348540d218031035000801d90802440900b04410f2100c0068220020407080d44801103803100e40780d03801e00c1e080440002d0615001130080000148200750403075409050401c103541080f0961b0340c03048086d2182075091110560600802d4072940110414240240544095051000390900034854200c1c94240e1500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 836444685 1250 836443435 836443451
    0x50f070512220e0103020f011e123e0d092a0e060118031e050d1d040209030115081f091a070c0f051c0c05070e22050f01 53
    0x6494000c2a034400d50f0044030a40d2a42e8204070b140600d071200c26050240c041d5204885809003d0611041d44254075929114450b0300c2caa0011103210b40043d80c0c080056031074004918000140090620305800c0c9044410441c0d109103000b18042e540300f180d59141080450740400c0381030481c4004168010207000111a1071024240001c2114025103410504407000581c00d0f62144c940141c5040c195407941c2c01e502d80742d0b00d0b2420902181d111010f201485070b1081d100304a810068402c0110740d515103c3e42c001586107040508001d40e680b510310460300465001c1050f80c007035020651210705260f494580950702c040745501c030b8448040c0220b100810845404844001c0e01642e41442d074480c00d0340c960011f43c244801d8000c2c002524540130025007038100c20000380b00003403240480340141c00078800c9409c42e1180d948250a282817030810058035a21000001d1000101d120a84800351214004c0e030b074442041c0711004501540c02e00d410200484c0c950148540462800c4081421100074400b000e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 836445935 1250 836444685 836444737
    0x1501031404050a080d06080714010e031c050d0b030d0c0302060601050a140d0b030a060203091905030d0f0f060b13120f031101290f031c050f070512 65
    0xc08580c054425045072035a03100280300c0400810b04200d0310200090301c0750f21004c0c8245405d550b50820481ca07410643c040401d983c010071400140e907011401018425078101c02c09040030707150000760050081c04102900c0c4600e00340c00c801c0d0011130150849141c1c44010400421320440d030b00342500980200008a6600d512548c115910081103840c0d68103404c1240b000300d040395106107000c04009966403447c095960703091142d40e004500901000d078a07400c01c41c800e1821b10000c0c10107216907000003803032100041c02c040140c902c20f425088000030b4111101c42c51310054000d400c1000e14113840c1c0540820016030150140c02c002801c0350315020030301d07210500e06418601c84503001d400079600b403000313000103403090f005010180e40940002c256920110000e8500e2800021140300b010f026002c0d10016080654400b99101d40c202d009011402c01070f41d40000080b003070100001008800503485e0008281001118003441e407000c221220f0184d00c04801d02250007103210304101d2600c600b4510303409 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 836447185 1250 836445935 836445971
    0x41e0f0b0607110a09180605060303120604151503021b0601051f0c080f09030105070c030527370b0307211d010f02071109071205150103 60
    0x5400e020304030501d050169290f00c40040804030207030f54400c10f400030220f1030050034041c8015802403201c56010300c3c480b40c5041d10940f5802010540282d0043c040a00240440d000440c1c00c90340035900051701700c1d6000c440400050240d004103048481c49201e515445526600a0845040c048031a682045041c0042c6494050030701c240c030340c1329000d01c082d000622034a82c07d5400900550611003000016540c8401544d08621601c10510602003a8446d0f18103083c09040d600141d00d1800b08032502c140d9801034098041d811500f00e16080c07108860030b44c030b11510305070040820000c10f08050a40c81d40d002d1042c5070446018848016070752603044c8035001e000c01c000e9054844040145086565880b4212801e0980010100e0072082d10070307149486901c64801c0d00c2464050700c1880500d500002e582c6800d442031402c0800000d4410460080490800301649200100407190540e281d119000300300d4441d00310b1020a403100d442c000c203005443c07914030ba800d0610300007a00c0511408a001c041b070131003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 836448435 1250 836447185 836447201
    0x4060b030612010605280f030309090b100c0b090c0904260a09030305090a03140d0806010504180c051908070e010c03081513090602070204060b0307090e070e041e0f 72
    0x814200e048080f0b4909a06c07540741032407414103030380c466125030728403494011040c3c540c0150302240d018041449600000e0250404451059420203034421103204003e2803100000d0014016101c29000b156541c01e0a05c1103280091008115140f50f003040c1c1000d0814100c1c1d803540c0007130055840c0c8030f8000710b04401e084d52007059543d1985203840f403030340d2016030704c0b80e1107074240175070140710130402000040c00c07484200c02c1c00060340000c054100030810050003e80b4090f00d914140242070004200c0d50394403100000206040701c00116600200d90406d075160f00900200842000c2c01e006803c86140d409045c8500c034400a039903594004c03807044015503140202407400342c00640b503234000500342408a503d51424030783c090b1612480e4170304480c580d0100d40340c006084801c01d40000717410042d403402c1c5c01183c001d407034a411141e242d0f00b8148000361003500c892046082c486004000212480c2c001d1205415950300078006221720354800482045000c2d02c1d81080014625040d442190103960380f20b600a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 836449685 1250 836448435 836448439
    0x2130819020616050a0b040b150f0a06030221010b1216080f06030703020901291815120c030106030e010501050a17011b092c0c0c030904060b030612010605 68
    0x3c505207000d00c500710a141100c0f419075082c4079003c0a400014581d103d8148103c0c09100b100d452400d12201861500750000406481011110705c01c4106540e071240c05022580582401a665144546440403800b9040c2c50400382c00c2140c0000168070f9450401405112203c8a2030703d000c0d0b40f00f180d10b0040b4140c00940c680001e0400b0002071020500c01c210329000000281282c000641d02d500058068800342c0102114510f421031009415000303100d185001d1540459080c14107810041c1454409981044c45200346580281c840103404540c04131b400815840c4070760002898820a244c1c2580d00c203101c2c00c0c001030300c0c06204070f0320030070184202d5042e107900805c072901031403400b820020003040082c1002c03801d543c1e50800e07d010402100801401c2d03140c039201c080e18645480801d80219040359401140310303401202d9007055403045411550f0140103118410313181e415048003a40b1f0350054101e015040703850902c3c08076071808410061482230100320f8140ca015462049001e098854521a4507 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 836450935 1250 836449685 836449687
    0x30e0d0207030506100f0b030402041e020c010c05121515040306090201120209031b06090402040314070519060f031d06150414060904080720040606030203070c020f06040504021308190206 82
    0x2202e1f1034015001543c006000500c0030904051916001c9455603000000c4e1610b01e41c0080c0720904d02800b8014016070b0340c5941400b5040002842141c85ca4100c002c02c5420170402d035041140c145d40c3c540300036a912072800c640d0b550f22a516494000020494484280c2c00f11340184c00a0310b0464450085038030212000d0081c0c030755007048500242048140244041d07000d54144100e042646482c8007610086004025010b0320940f41161241410240d0704034901448200c01c464010b60b08501c84241104d00c031745003802d4000c8507100e0407002042501450802c40ca03500e001d8070b5807c00c000801e90300034a2035414503a0801d69400810088841c440d03142c1d0390780e8049074000380c01460318244440e4058000d12801d842e000c240c2da101080030403140300c200300081a2050b0500541420311400000d4840340c10b00b140740d0f0030010b0000c0c1a05500e0b0303500a103e051007500302031036a00e90300103440013000701070025912440c03c005c000c0035501060165480c1340c4241d6800e5100b081d6440700100794182c010b4101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 836452185 1250 836450935 836450939
    0x1a07020c0f03012706050906061e0a091e05250309110a030317070f080f040606090218040e0106140111010603080315010f0804020102030415030e0d0207030506100f 72
    0x408000240e1086a6030b05550700e0001a000c60142685216840112541581c0c141a9031400c0b030102e41c8040c2610201d0342c0a0800c0001c141c882c407840c01c0c04080050111440c1400640005000000300d0704814009428055400074a080c04000034104200c100018011540c0c1c5584645484814116126000301c050380850001030282d4042040343d405183e1004c0404007040200c0d00d08600359100301c0005000044040d486415603441d00c0d000380f15850440c03860030500c080203103840005000000c1e40c2200001103030401151303a02000c010300c2030002c1503444504094401d00c48006410280b40a0350414010b004d07100418030440b005d803801c0c2003c00c0340e408081001107800072113520b180c12140d9600c030404408141254041d5108803000c0600c124081c40d40400103005c8520b1a0b0018140010f00b02032000507038010081d181900c249644440700000d4201c001c60207030403030504240c882d029590001c0445035002c60940156805082102c0305900c03401016008140c0c14454159200c1300a002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 836453435 1250 836452185 836452189
    0x812060315150a0503010c111006030c170a0203010c11070605070c090506030307050105010b070204060b0a1e0c0221060c03130f020609060a0e0906010e0d1511161a07020c 75
    0x102d0840c0e90b1003e0508683e0a844601090840300040d505a0100d102a90740e03290070345040040c500b0405040c481880454034594910038409603900441480030103441070060b0442080040e4140385400078001d04c1513020707001026003010709581b17040c80c030750040307000c0818494021300445050650050300700c111289000e00240080102500036070f81070008004072008246c003401403a000e0100135031030a50f116420b2042004440003540401906501071243c24000d94003c02090034145458441c0d003107003071902900f12001c0c180303984029804980110034045079110b07400c2142d100e1214900311105512003807900c10460004807406030804a00226071000603485854900a442c80905a181003801c05c2e80000c030550800204440083d0069080f002d00f86480c4018680080c02030074035a000820310404100c1900101c640030308003001000052002c60090780c400103084e40310384085512002403004c1c030482407507824415244440490140d000501c03200001c83d0260010350000d00341640d00d801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 836454685 1250 836453435 836453461
    0x310150306050405120d0e010f06150e0609030a11210706050d1104080102070c051005071b090c050a0207060914010309030e030118060501090908160c0801090812060315 74
    0x82103450740550038984005e180100054148030705003001c00f00308510401041405c40b010010000081810070300100407034403252900029100301071074440302021503100030520503c96903464070340510510520006104041d0700e4501140303401c031020301140e100500e030055010a820414507150300400000c101c4a030156000345584040d15101290440312240b4880c1a504150f12202080c0d40024180e42000403400780343c0040c190860700102c0c00202d5102c020401e0103845002450505441d03032940612102105c0070700200500001407040b03414101b40200315802410f0110094070800e41c002c1819406101181c0076a04403c0100a0b500d11944c0110042c00d6600001c1d410711950061180a6440c03e000c0c04064946105000c40740c0c0095181000441d41305034082281e06140030000000202140201d8214200c101780d0240d481420382800c002401c22540540c3c0355602c0c01990b042004082d002510700c0412500c4803003080e546007020f06444182c607036100c84400740203000040003041040c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 836455935 1250 836454685 836454691
    0xb0a02010f0204060801060f02150a020f07060906060e0c090f15090a080303100f0b0306122802040f050f0414070b0f03090f0a050c090a180b06031015030605 69
    0x1100108030803101c81071100481c3d1040e0030107000205000c006102d0107030494140c0d4070780710740391009250a120005852281c008090401008660002101b00d081d08600c82034414254010300700304051102441e10300010f0000b4400e41d1603002036500060a2010700c0c80c01e5809106020b44440140c00000042040410b2020085424910b0038000c0e840182c80b0100103502034500d00c401103650781480040c084094050360710003211125802000c3c03188400080c1a00c0d04800c0654807035a103240049141402c1c00c0211240c81048590000419452902c400602007118000d45040000c081d00c0d00548003542c000b11003a4000c90203401c08a00021b0315420400301a8581d5003d5651158030f500c040c40040d13103d100d01c0040802d001c4180004284240002c99520b0790b00c8000f4200369465903500e580b540000c10310355208840050000d86040d0081e00017448403100e414925801c80701d00d15000c1c81d03032941035594074024411000c03094580300c21403051824084080d01d011400524680d01d00c00601801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 836457185 1250 836455935 836455937
    0xc06101d060603180f07061404050a03020d061b0320090904020d080f070b060f0901030b0c0c01110a18050a18090204180b04110118060e010201270213060f0b0a 70
    0x56202146040180b003018185c103031190150440610f007601c01440100c8130240d9900d410303420001000299504075080040f2039055070381803558451420040014681c255000d00c5070708400118456450341a4805620810040e0a26000300344418105566008250710700b40c000220703001007400342c07a00502c0100d119224906035407a20404030710f40c81654100030030803203401e46400140400391a1413104104002c0054812200640c515201c2d040c42000c05003030940142d0001500e8082054207421901008031088072041d0740f01400e02000302400008401081030089003100032820340781c0401e40b00212020b411400301000c01100307001d80245821081264402e650384400b809201d41504070b10703021402001c07a11428135150030171800301c140c400706117810000e00709050602e8441840080d002e44071140361210342d031020b10006034010809190010361010382c0c0340f41601c1100516282103111807003581c41e0368641541c681814241c0c1c419015400861b801042c05200442c0d142003d0000d440e05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 836458435 1250 836457185 836457211
    0x100b04151808030c0309011e0c080a05090d2103140601050a0e030a06020309120705031603110a140d02120d090201120e011505101715060c06101d060603 67
    0x1079400b086285600040500350203410100d00202070f5a040006d0408118000c00003003954418103a00608105840310001c20300a008658148000c2c4039601b0344200316400b400310102c0d01800e040035404d002d10484041d0010024100c051803da1107070162240d001c84001c4000310545404c401035804d90060100c04040214104003044c242e681081159403144c0101c070010790300c1c00c08581c081d04100400c5c1000420071400c010301070004e4800070469004035070340b205490351f0f8240740c83c04940300d1035030009200040c41000c0200c400d20140b511803018a5180e20f08882d41142004e006988130500c1c20501c82007000e0034802c0100780030454111140b651710502d0100c640460184180044849280c846061a0b64541000221000d03103610075001c4c00c000ca645800c0c07403440340c2d801841e8401c070380c0028401c1c0903410082846503c00c402c0c122903158009045548605c0b5200d50540d035200110b5007580840000c400004a10014130142100f17540d000500980301d030303211424080c66510180038103511a071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 836459685 1250 836458435 836458439
    0xa111002030c03042301020f070501210c08070306060f021203070219050d0201050c04050d110102030c0d05030405010b0d0302031213020a03050309040b12280204020a08100b041518 79
    0x4070610041020344080c602c1103a104900c0340000c030385c24440b99044c2e03047d580f14090230015400000703820000c4480910b818801c04904243c08034209048406161000b8200301c2c195801da80c115006a1144e403a955041010076039030302c1e00701c602109070000c030005a00516400e07481300c100d10f402540c0c802085c2c012200c1a10150500407200d600042054078140c0007054100c610a50a004075904903080250a5060a0400c00081c0503004500c03801020152241084811a40280b054842602c00d600c2591901440790901070700e1644112404c86680d441e224050b41a45840101c048065400da4000c506080341251080ca212034060074012012441208101c0140d0b1a0312031880554452405952036806000a00090b03561110070340344038014040081501c3e81001440c5010070302070b800d00100d14040105040c41d840190000a9002400044e8011707025811000941c0580c1003000c0d80c070401c0384d031500d1403d014000c03170043c081d07030009600b14180d4440c4030340f032000002502c01c1d4541943c03d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 836460935 1250 836459685 836459707
    0x4090f11132105070b040e0703050105010e0d031112070209090f0a082b0905010507090b09040b24120c03040c030f1110030f11091f0513060207090e0a11100203 70
    0x2045541c40b9814045c400141404134031009a103003a0444030505041c062075040200203415103c200310200c1c0928291010181454440d0901a030741c1c42816040c0d48c522900c07500b2070070003540001d0040c1e0048102501195140d480051500350720070051011b404810401c1c3d6941001750704c26511a81600ca2046007130081084800070103001440c0c1040c00034004149251950a441d170051000c0140040258204a0304140c0d4080311980282204c00007080a80140060340140f40c0c0c1c149202214250030310220782030547c01c002c0c075124001e09840442c0f03541c0c1e09c07106080d500c01142e0040c240c041c03246007000041c1801c400c010015200e024066503003025030001c1958903d50340020800251945845801a44d562058050401c940c2014500e0500c1326400720321001d181c103200000e0190040d44042c0443c1c07091058440302402200245030a40e61564000e660700c0d42030090b04519880d01ca050071400394002850030240354443c80240f0314082c05010044d220300c80680c0700066000c1004040c1e055 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 836462185 1250 836460935 836460943
    0x1003020c100c031d010b03070e0c0d0608150907030c0b03040f0813032306010e070504230103050c121503010e03071b05090106052205040204090f11132105 68
    0x12525642d0005604e442d030802003c0504c1c00800c2e50240c0c3e9144c00c0012110b91000f00c1d1580a40b4070b500003001042d102c64245178402d1252900d00300c000d40c03902c0c3e40131a64402c0411a840354070841491060300c1d84485040d10303240c0c1500e00c0002c01c5404005002c00c042d040540146030b100f4014005a12003145c0f5803a04030361030b4000150514460300c10300050003040740d042e502500411240185e04a8210400c0300280d4821040c01403003203100c00d0200103200c4921803812240505440034100c09407414100450080d10b10500c116070100c7c1c14000003c0c0080c3d00001a03d4034044a041d8000287e12600c0905005002500d05603070155220390720000f00c0d44c01013008240b130902c1855040d521190350000e00c1e021900303641019200f50f00d0700004100950740b2400b40c03518225007519031241584a122020352044141c0d20003030b04180046030011340c3c000d03264403031700714504903100c1031114003440d4a10f030900d40315910341c042064421600c1407041e40c0d281035420b02c114001484840e0066045d0312184e1074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 836463435 1250 836462185 836462201
    0x303010306090c0f12060c020c0607110f03030f0406020c0402031e0a060e151c050c0907121112091c032711030f0609070b0f1207020708010b0d021003020c10 69
    0x25102c45c0c1022402044840c0c400c0e507088a0032032002d004204021400100d40c0d103c0c200c000303072450050500e80404c41d070f910542c09132110307802401c580e03540e0103131025800d02c0d0b0054400c4002500940015140e10700709402142d00c11208088500c400c109880040486900d001c1c141c10f800b03030743c0e941d008203110b4925028a80141d6a0300380718854804104208400c08181c0c00c95010318490105501000a00006019030214801c032005001540c82c002c0480b01002400241d2078003078200618443c91000e108010503c900080308070b803065550b10701200f640c9e41112400986402d0110b0310002e4200c3c4207910000c0000c030101c146080c0e10303410104c401c0d070250764080152415400400c0c0000603140030070000380e100403e000506818680703110207036241c80d418030074070301e064500140750030054401c003044850740c0a0064840d61b4030306003910025070740c100c140540d110561800350014807a161007040d00705416801810801032a828050840c0079411010030040503110300542c07012111260f001d1881 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 836464685 1250 836463435 836463449
    0x2031921030605030c06040e0a09031202030c03070f1b1b050d0503040504050f0c031b19110d0504030c0918080705210903030304120519021c09080303010306090c0f 72
    0x82d245040400b018113081e000715000744644410001002458200704050340d210781c01e240b0001380b1030740e0360078141c51481c0500095038449100208010400d28103502440c01100179a0300c16920f085408416540110130b030900e0001c00e0705500f01c680004070840e15503102445c03080a00803200e680d4201285a6450280003114107030804a014411424144180c0303a02821821240603c0c0c244071215854510010b003100385003800503601c003c2085844d078215902c0341c0301c4000107001c0c0c0310021001015070500078005580b902481e010558010b200f003090714190f80c3c101111510321450042190002e02d2002e0300e203c10020103100e44030100b4038001c09001024000c501404400d2414a2410803a0501842e043c09880c02804403815075107002081e240d020f0b50110465030018481501511940074410303000181d21480455a4801c0c1c0d401301c5d040040054400c02c0c1c2143d0062100241c8810000d80224101075105100420120704180c1000784514098010b0b01d260702d841d14114070b188000c0782c000236 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 836465935 1250 836464685 836464691
    0x6132102030c01180804120204060b0d0209090702031309150e042a180c0c1b0323061b0c0115080d0806030d11011b03051f030203192103 60
    0x41146103080c007861340c806084040e400403400f59036450710142c0c00f4a0140d61241e07158548900119181c55000d100504119000d1030b40341d1010400c0710380698449c0e0240c41c003804031000480d2429000205448851001207140c4552508100c0783c540242401410205151000300d800141c8603400401d0394007d50080344850045010651f24111302101607801d0b000d04490b022041015002010402013140d44544001c2810502e00d5000c60300b45400e418090400038128400c00c1c50765002005100c11607201e0300303420080e061400784010712200703030814040098102500066800790510231041840300c1c203803a5141091307034044015007142d8600085407189011020140640740e8100400c03400a241460700c14001e21348207004c65150004030700c5030402c1c00b030003040307400c5450130a400064a8200030b281008000710060f1008000d4002a5407a4610002c1000041c1d000a4002d0f829001e036a0050002e1542c041080f001c1c0c0e81001d40d4900c02e80e000190f41d4003540c20700850401da044440c680c0e95000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 836467185 1250 836465935 836465947
    0x705070201020d0f142808091b0306010506090111070e1e041110050f03040606030201030e3712020604020111030a08010302060c071a120106030903020613210203 71
    0x1a20f40120400a4400e2101028490038a50f03800300700c01899158a09040d42c85502001d4001420030341c0c0502d0045d8640e6514094084561141c1094803e00b81d180c22155a0300b150145000f0101030041001d80603000315005010030300b042c0000300400241850040b00b00c0e4804010755082080507001016800c28020600c07035442e40c107002c030261005020081485074180390356a170007220784035062640100203001000301410b000340e00341c50040d80b02c50728451741c91410f4a8880021314407400101d01092604040b001d10740000580a130307000400259054245400c0751042840807aa8862800f540f600202544c00081340c2d511100420411500203182e141070038800036002c010501441802e40c2d100b4807029041560203540a0304694050307a00303542d1002303d0034810b804c0c8402034011484810000e00c2d00c0201504600c0140101b01e0204020342d07160341c0f512012020f03070f0803400d00a401070740582d011441c0d10403d500312101c154458a980751510324880500b25214621240780707800340e0808111 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 836468435 1250 836467185 836467187
    0x1e0c15091f0b0112150512010501050a15050a0810050604060c020909061302091f0e0106031b0903021e0a08010212060307030b2403030d0e0114010e06060c12030705070201 75
    0x14841e80d010802081c0203195240000a1a03d0480d00340c5150280c2c0700c031021900400340b1741c0da0102822018189600340c41d04881101c0c0a000d00b0702c03802d4007401000300c00042034140310716007404400d0240d9130036141c2814404c0841c3c001c88094800e10340302c0c0cac8909000600c1e903542d00080005011985031044581c3d00c07401045214140280007178107070381100741003028412502802550441d41240c3c4c2442980350742c80390010442404469048044543c0c0020501c00740011856040f102180d40a1110904a2203940c5900000714600e00200b0740450085c40145080804a82568580c0800d825107450900002c0c01c0b11440d075100200c181d50000e1680c0004005482565210a007a4010f04001d0b03d50380d03d40810880040036140340c81c1448050604d014880c86294100b000c00a00716074680f040c0d484d45500401c1c5010017203950350310703100c2e81c80e507201c0848203e00d0494100c0b603080d02c41c9582d03e00c1404810383c080c00c0c0803045030050b66a1444000c60901c09940540b40a07911039844100601c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 836469685 1250 836468435 836468473
    0xf0614040b18012c09061803040b040501080c0706060f180905030304171e090a0918021005070c0b070204150b1c0b0904050f060703021e0c1509 63
    0x611240074040e078000074690042c1940b0514110303100d090200d8407030b608640500c078100d440102104582040b5034140f00250b80001600c6000b01d0081c0c5c48041410407aa030318a55a20032442000e500d0801400200401d40c06417051030760003601c0007e96481d1488540d6458111202d0380c00c81c541c4410410014040c241030710100d03405418940308c0c00c109450311501c445541e03000090004044070b2048280124624170b2401f51582c100f100703190780c5520341030314102000c0380e00008461030241c6080c280000b545410b9001d55908d0f002400c5c40420311501c43c5d0240411160407140c21404d010003004481c0006600c06084001060300da1a61500d40ea200d10410007910895a0400d2881c1450034050040100c241d00302c540641c4412000c00754007152940d02c90242c644000c08a52045a0074100824014040703040c1c1c01c0d1000714001d451044e640d03944180c040307000f60504201d08004819601c2982511240184401800c0d201250104c41800300c010384403410440750a00c0782c1e040703900b2820340104054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 836470935 1250 836469685 836469701
    0x20a081014130908070f061e06061d0604180b031c050a2601060e0102010b090108071205100207030f030501080a03140a0309050d02010207030908120f030a0f061404 72
    0xa944800504920000100351030210a500c01510790780f203c00c2c40800980c03108440e41294004c5d10203540c80d070309040240c020303c03c802c000100602140b4407002144940d02c5070f40269156a1030300b0002c5004906d00c005144032785030619421910400000c9489000765910340000c0c1c0400d28003080140140741414241848000190703100b441c04140140166000b000341c50182906152802c0e41188002c034070000072960001032601d007041400046001c80e0710030f14a20611130f0a80090261840f0081070082440092085030b10541046105000e118164001c040311540510110349204200c0c840b0b50b001c1741c1c00404102d0210725502c04186005405011b1030340100402d8010302060003481d140980322003801c643c40c00c4e0318100003548200d064040e41c42340d003460380c201048468802c05540c010b4001d5102c46001c4d40420041072001800c4580040c1410001116a0600b41001040081c0c03001039080904096a2a074840c141210351160b01d118100061841c01c4c0b145250b002d0350000e00c4100c1d4401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 836472185 1250 836470935 836470949
    0x40f020c07062606010819020d0f0e06060109090c1101141e0601020c13090605040c0f0b190e0a030506040c0f05030c010f0e030c090a060609063e01020a0810 69
    0x44000025141000344101c4c1e1184007800d22910a07610b1001200c6103026000c0b0441519101044d04000c0311020307402000501a80c54041006101111000c0c0d41d41c007003140d403140041c2e42c7c0d40060215200a406c662402205030038258042100005440d0075a003410005000752030f00a400c20416208400922081a9100480d14200d0134100c2c0000d480700034000c0e00a00440350905225901d1102d0307808401d000d50440f1081003142800c0c98050708401e85441170f4500781c042441c0101719000580110ac24154030382e8030f0501200c641840540749400c101c0c003803560185050000001040d018407025110f0303442b4590b0030418a05124415000300e09603000710380283e02c0485074059598000c006680021041d081c0390301c0c1c7c0002e0900007464045007480b09900560007a0500014581030740002d025640c0c40d4075041d1400b03881c1c2038205d03001c4802c541d40040c030107983e40c203200c2400f054040f42e0610045090440011065405015082e41c0c006441c0100050302d0108106000003c2998200a4464 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 836473435 1250 836472185 836472227
    0x2010b060a080f0c19030e071e03112b02040515030a0b1f0303020312070e06190201061a0a02070e010f0608092103011401090b0a0509040f020c0706 65
    0x1c0410062040c01c00410320842c285072071010580c0c00038000251002c10722801c04c40100b070000c011005002c1c1004e81458800da200340e0780003090848401d2503038480c0710780700031484070858a181c540480542c00300890340d8003c0c1c060b82446003112401300f20711000d9284a101031a4902d2075105001c1202d500174600003c10b010010860003554020854056241d00031050403416111102d08a54540c54498a103240303030040100002059008030141003600d140c940e005559680c2c21400f0b1341c05c110030780c182c9640000100484680104040041200c400e20f1b031000003905501d5030403281d00c04a640b1f83c5554a000086484180c980d8100240b5004e803401100500c0d56500d0103001803a490300b031303000c0c841c103000c0a180010b021001c100034800c00c841c96804002d50540c00c1c10700c0c0078001e03402030241c400803070314148400d1901e50285e00380b00c0c2140c100454003490030000301c5044035150800c0030f0203944070b40c480c1510004c480850016102010b048409481c14903d00380c8083c100c08100d1404503a0094 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 836474685 1250 836473435 836473447
    0x1608010507080f0603010e01180201180503030f0a052a06060307061b060b0603040c0e0a050919060207170301081005061008040201140d0b0a0618090b0d0c0e0702010b06 74
    0xc1c2c051003668008205840a510946410000074054004000c01c40d000d51310341004059960754070200b41c44140e000380c0310010b580081c003045182051160040c1a01540b04104039088540414010215105103141c0a8240002c14400d04c8080c904680e2180d86401c800002c81c04a01c014028190016000c4000b804250320b004c2c0c000d80b0702c1913940007007507203c3c5944a011080c03001e29001004003600c010241c0360b8a2401d07280199180076180124000c00b4070060005a4181c2c1034810700d401080460010f003000501e417801071703200300520b0104441c107680a008000002d000814807103c817121000d8a19142e40c1000d038001e2820400c40c0004000f1410041800354640303c0800701c41d410030303a528204040c1d5461b4001614004034400750780d903100500240c1a90720155603840680014401c0f030b1404c803116a240b20845191040b5054040c0c207654000381040301e41840c0e4040c2159400280c10000300c1122a210710300014103603441810b10300104d03070410040a90a1040c00c200e40d40480390142405 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 836475935 1250 836474685 836474687
    0x91c05180d0c0b0912011d151312030605030607032007030e0607081905090f0906090a051005120304080105010909050a0b0604090609050a170a12020708070507081608010507 76
    0x50a244600211400002910002d035100c940542c4d4a004a0300007d07c031810200d10b403103610a15414200ba0795008400c100400190700c0d1200500499940740680c0030110309840e0b010320110a082040305242e52080001000e07102480098810704040c1c40024a051520343c01546205e94000018a140020031041000a42041408441c80800d0790710349c4d00c3c0c0d4824540141c480c860f001100c2c050040e01b201c0107a20b564064010401c085d07003134640e081500240c1c1c0a1009181043e10a00d03440380784080040c0c8691110b603c010340c0108114221036003141c1d074502042c803a400d4010303000c01d00e03040058280300c65840cd028080c01084800401c07c40409192a1182c0329401110024044518038010501c1942d882e0400e08140307411501c10407010106285c02541c60b880c40b00111100341f580010070100d03407010010740c0d1940c5442d440b80e030301001c203520109000f5400100116100b00040c80140d010034020007069018141c03c0000303081c0c000d8030602d88030004034141c0c4090120381c10101084909 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 836477185 1250 836475935 836475953
    0x70807060c060b06130b040317030c030a050402031e07030b0610090308160b0f0402030d0201091509020604090c09080f0d050a05030c07170315010801030b01030b091c05180d 76
    0x1d40e400100009106180c0c100040b101e1144071100440d003c0071140118418010f00014000c5a03c505c0c2d00c44406072000c0400a0903000480341b81068100a2001503e402d049801c496800b41c8001c0a07150131481c040c0341d0011294811640c0101c0d80d000740024010002c2c2920155000041110341d81504081441c005009407006c0c007006003c4900071654503607441644c08815515584080030900928015404400307803c01203900f64464072800d080164198011320408049940022986140f0a40c85405001411404c00d049070010300821001695030300302d106404548495590310101070b494400104d2a050702c40302d4040e0b05421481d41c041c18903401800f1900d200c034890a01944a903210704600005d0f005200010b82040840d4040d1244600040015481041949071b041c122600100044601c03079424000113000f038110800600101d84844442d0703500c652000c00700c5814018000c600c01480461003401008203101080c4488029007910000304040c5040d10842c0101485444001071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 836478435 1250 836477185 836477207
    0x5040c03080f0408014b1a030604080403020a06020f1b060409020a02010b01020111040f0b0d180b040c09110a03241e12081b0102040e040b0907080706 66
    0x400720009a0b0390186105041550000d01c0c2d002c0080114041c4c401c00d045111101010802800d1034450306282c19252044100380c4080d0014080608000e07048403440041968801c5007070014106951410301d941d003000f000d889280319030320303c9888502d5403060000d1620b140d00910f0a42d040309070035042d030000014240158080d00800511562400c9001c25030a104980101030b9160000a030f03242916015000030003c000300ba4020003030360364485a280c41c0ca000702d00420081d8561a1800c10440f50000050b02c1c54041808c40010444c0c00785002d40c109103a000800c85410b0a034000b00000d010250950400500700da02c818041d05a101c15582441c0c881c1070401424140e8400c880c0c940030408000c1c2d620340711000c541c00c03441039480d03085c0c0601214041800d08461000910041031000003841c1c680011584181240d0401524162075081c41c0b5500808110641d400e000004500780d1000304d0fa4010b41c018948031000b0f0500c0a0701604020294104071156440044208403d40d4001020f1a03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 836479685 1250 836478435 836478443
    0x30a0302030a11040603051f1202040b1315080714010804020907111029031216050106060504030210030501240207150203090316030308040618020a03061b0305040c03 73
    0x180d69610b610051008050049a0b0315a40402180104040781c140e8000c03030040031280214990313150385c0c500b40109141e690140c0000d40005030191801800c080d04601d0388000014800411030580c03506250840c0c0c070707511046403501c0b5130600c2000b40020910030303040541070400f11000200c1d000b5002070104540600004c0c0038071214000036201900c02c9205640500085040d03400500c09000303e00064890701e8414101240e0742100d460301c0703c0030300007081d0303241ea005400780102441118000d5420b402038241c08559004040500c0000350083c8104000b0301450b80354161114218014001d00c80c3d014400507061514086c014440301d00c100c0d44d02c0f44e115040e1459a000c90010380c84c12420200140d0080305031545034040d01100c1ca0300807007c2c0c80f41e40810f400722000709a6003101c110b051504c81c4800b41c04154000081008a8800d4100740840b428502e40001c90069aa000c104c401b5880d6000f994200e5031400e00d0800700d20404500c1c1c40f540c0705440d081c020b0b81041c0c0c070390400d0b01c4030034071000b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 836480935 1250 836479685 836479687
    0xd0f06052b17092e021c050a05070f05071a03130204021e0d0c020d020601062a0f0b0106110a110904051c0206061f0f0f020106090207140c12030a0302 66
    0x81480c0030b41d41c2100d2124902403c00c1c221007119400c04000100c0100841c810141200c1c841042107100241101d444c04500040380c900e10044001958260701100003001003190802a090200d16a50321903000c081c8981c00805149281c4100000c01440b50800c152046504005101440d00c0860780b00300342c2078040f100140d6648030341510f000f0802403240d2510580c80046440d401c40b000e81d900c448501c4501e502a0b440003c2c6001080341c413007009003d080c0101e500d049407040c1030512a844040d10b0441c0d50050740080c00a07840d10711700180d458204942003e403680c01401002d0b07216504059928403513000707207400c20461f91400010441201d91034095040c1800040c10b001c020003207007048502e81800309900050f1403400035211710003114942c0c016103990180f201c04034031481c000c450f4840d481c0c1e00c00040107500641200c4428800e00540215900e83c8008600950f641c4010444584034444080705e0305800700100d0701b48625000a184107445021401204c46004400c80b17003031180340c2c5001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 836482185 1250 836480935 836480963
    0x50307080a200c041a040f0501170c0307062f1f0e0a0201081509090a0302010507180e07030f050705070c08011104031b0e0f04110306040305040b07080d0f06052b 71
    0x185c1c5c0b42048190b540b40e0300070704041c14040c610800d45d11a43c180c42d51400e5101e1009021500c0c0d95a0392452081180c0560000301e0400189100e00445e01c00710101c4954524500c014440c03101d0f40002940346c04a1540068280141d1141e0101400300d000c15011424401c2440e0141c02d191111850311000e41480b090200062184507030910f084c031080c0b0b00800214050401003e0b5a649001800080707015610f0400401c4170300703000e0710189480036900106d610301142445c880c01e5042001802d41c01c01c4c9501c81c00341c1d0000d10601e004036441011140d5610752030b011182080244040142c0c030024803a450720b0000800019444122002d80e90403400700e0a009100d80843c040c2c5600c260f10502c14454040d0912500e141c2c80c41c2018040c90082d810141400d0b403a80030952264020f46000300410001c10040000007003040242ca446401070b265281400b4801d001001070781c5584a446140f1303690380001b808545003100042d140b8200003040700466060280f05000c03401c0403001e001e003c07404e1030201 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 836483435 1250 836482185 836482211
    0x1e01180f0204090501050123090d1e1118010806010509090a06020301030309061707090e0a0e0f030c010615020c151c060305010609090b130c03050307080a200c04 71
    0x1110000400c108811541c1e260790300c620720000c18007030080c40e000603032104103407005440b20202da81d240c90006101c1d51130b00c40340000f04081c48005210450700017210344003000040800011660403503000e41201d481c03410702d110801410780b40080e901011000180014400d08030b0000c0c61606485090307940c040c3c81c0d2192881285861802d200041c441800000040f0070954008880f000715103a0b5150003182541da0341585500e11011201140000e4219100300240d290b9240081e4204408050014a02145100e41c0f420560044074104041e0700008400d60382c07450074820301c802025100b02100c01400700a5000b0740320b1007000e54440c42019801d601c0981000300c076045440041e400f4110303018440c88416a40c0203860a0b00c011b54071546407420004280e0840d0040c0c14445034030204410003551940039901030524581819100c05586810100c005041000204641e0307008907007807901c804100c0390061080908400b007102202c5104084249808001600400e041d0100d60101e0410400c0c18 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 836484685 1250 836483435 836483441
    0x90a05151002031b030705061501200a0f02041b020f2b082502010e0c1e0d05100c0203120907030f0221190b0604060509180c06030a060e1e0118 63
    0x6d00648a03000e014148240180c00254003c03500500f07882d81d45003228114086a4450840410141c035600408403103400180c00220180b4154402000010343c6c01340d0f4200040484144130b0070f030380581e20031580382c49902410440491440e9507140360300c2d01c10f01760304003401440319200d0103c8148642e040c00715103a8044d1906d03c00000e001d07100162030292003030720000d01800c0d134005201c1c407600410320b0610351418075180c0c90b0398107024030300c900344140b8840b001e0100c42e00c0608030a8410f40121000000124030a011741c4003040ea00ea0300640d1034494400d0700c645403460113041a85280c0c0446420000100c1c983d049000181d0101c81d03007030350b00003050008500344c00769001010503805103a0140c0500515003100843d41c900070032040c0309580d00c060074401220710b6800303225407203d4000f0004048607001001082c08006100540302c4500480b00410042c1c1c009913810400c00703442d44414407c0030180c4c20940d0b4007250b903c1c9800e13122006c01d94100140032041c0291038040d0b400d40500782320000560 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 836485935 1250 836484685 836484697
    0x609061217030a0207210f0306030b06010e030f150f090109020a15020a0c180e0721020105070b04061a04050f0f09070812070302160f14010e090a05151002031b03 71
    0x441a058000c8413121740c00300c007003119074408041440221f140c12820310901c5850240c9a05c2481641161075145c015612040c1c1e040540341d15208a00324021406001d0200107424904082d05d070089050003507024010800c01064000ca607890405901c015a03540184da20803134030801d51071881503240d03079005c0741895071151018010047e16500010b80e0146401a1515040f04003c10030800d403a01c0045070b02d6080900c07500e0300e642501410a5143e5441582c0c0e5604c50380705041081c54541a030b035461807048012a025148103690b08a491011185559959540c3ca4215030810241c0b816260300c003c0380340060314142092250300d0001c0c2035018100035900141180000310380401d05040740b401c100f68081c0504500500498000c0c0c0412440036842e02c0c00e41c1d85030b03041c90500360b05200c450300840c441c0c0401181000a4012007420755107496114038041d8404200201d19450701e29144884110403404d800d002d181103100b4540419070110642d0741007403181c03128010120007003000c3c0346503002e0a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 836487185 1250 836485935 836485943
    0x36010c060b1c031d012015150f2209020a0b0d0f0b01110d03020a020c0406060e01020d090515131502030d05010b092808030a030609061217030a0207 65
    0x381651540c880e402c0304100b50503910035035880081c4074040b441e00f040c030f05242d81c0351382c08240484114004048080f4030500d10070745903421150b20740814a42d6007121003090310b0700140c00c1078603d00b107005810402c8240c6007000050740c144491081c07060001c88088040c2e2109915155111006001c55039848a544010b025480c0c0e80c03501d230a80305810000401300f0498004900780707040318504c12540119240454010340c5009400f10745680c10040d000381d0710051803241180140104040e4640d07072441007002800050392032a40540101d0006454490091040c10910120703200130401560745926500620345000c000b01e48a02c0d0300c13108003903d03842c0f98219190718040010000081603000014004000c40218107019591303890490b000c80c1e00c61480c1c1690400600c807144000500e40094807404c0d13009081946903400c0d07480c1c024506581248512030300291319440100080701da580102d401610800068074403680c4660341c1c0003000c0608090001d82d00d500071001031100c1c041079041d5416076801c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 836488435 1250 836487185 836487199
    0x1050c0f0703031b120b04050603060c030703060e10081608030f0a02030903010903030b1807120c021c030e0c0307050a060c080f04090212160807030e0c030106030836010c060b 77
    0x808002610780c5c4440030000511500d041d40720b00c224a03050184a00648014000d807403e40c0f6040c955080c0c41d40700428010a15460780000100b803506480d415204417900c1080101150030030010b03e080501c0e500044107240c0c401c0d030041c07040010100032904980c51038841240d440c4117201041e411f5000314204141e00d9480c05a2050500d505030300324100502085509c210700350b003843c600c0d81c48030209407a80301c0000d18921008145061030b5121000221150044900310018440b000a2861030400307080300080d11002400c0c05080c1c03c0000503e04901200034161807420100400c0d051041803080d00c003080018801c00c402d025481c012650f030306079110081307a920780e01e0f005007202a500c00d240b80044a8003600015a031001c2c10619008020241c0d61418020349403407c080300600010020101c5600440900d000f459900340704500085209141d110340782d0b0f000752860280004440000c003482400800b40c0c080e01b40c0c007040d0b0020344004c2403c00702201d40c00d46c00d01c1c40c000d0050502d802e810010b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 836489685 1250 836488435 836488481
    0x903062701050a05180a05030301091509091506060224040303021204050c130b010c0609060204080f070f0e040f031202070818090c09030c01031d0a0c03050f01050c0f070303 76
    0x5402d0b04050312030301c401101c00602501c0341d01700d141d45210402014000717410500c0140f0000e4204e400803064134030038002c080022521000503004950f42000c0440384401c06020141021655006807001401c203400030300504816247c0c1200d240307000d070026590b200b060800280800d406a41501c2c41c0c98101c0307868049078940340c580255256900381d0400e00c108101c2840c00e000b800c0380d00503410b4018041c9e4502e00c02c421a580d54070040d01401c0d41c21030348980c00380000b00303c1d1101040415004926040244902132411303038100e400f4010b5800440c2c02000840030000420200c46030701754002c0e45403901038448068000c46030024000c081004240080000c1e00100c404152150851380038400c8582c1e020548032440fa40000388504101190560000c0a03001000c3d0f00070303480100ba280c02d1b0000c81000714070080d5858149554003c01b181c4030f140110062090001c2005000e8041c015500204542d0a00152038541800f80c41b12811a2420001d8040d0805200350040108482031444000ba102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 836490935 1250 836489685 836489701
    0x5090a140a1a060a0b0c0a0219261225030f0e1014090604170a170a08280903051c1802060304020a120308040215090306270105 56
    0xa004407030140c0b030060800002042080d0064240c40c0034000c02000d08109034540384800a8a8021030f01c5021079004000d41c000241c2c4400b010340380d0740032444100880080c1001003c009040541c0401c041404420060b000d81000000341080b000402c000515202c0380c1c900b20b4044d090f05a4011f120102e0f440010150405820540d9419080c50075201d2805440500c001e2114860300a2155000039401080e014540c4001c0300c02000b403c0c401030a881c1c9803640303c15081519071f1000555018546c0f0016154041c8207807240c2100ca0207100c1d1000901e007140151008002c0c0c0e10103004107060b400701e00040680d03a42d2109094412100b10300c1c080c09049103038100502540c0001c0031010725604d4541d10000d10103442c0c400c01861544204040301c104449400b8012035810040040340c0000c4042000710b8a500010003070308426101c1d964006103460300e84184030034800d0f41c440c04c140700c644c203000c896850f035004100180d00c10340e5804d00c403241498200181003407109048120a055180405001503a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 836492185 1250 836490935 836490943
    0x30c0f08071104051f0303050f13080c10050a05070b131506060206070e01120b0a081e1501030f02090405030d090b090c09160c020d080f09040b040203160305090a14 72
    0x10100b210204650345c4c40754103c42146812031607120040750080c20038000640104041d0142c0061a00400d06110500700354030182c003510740010289502040b880c4c0103a1414241c040c400510520b041c43c01d000d840b0b000940b260081c813600038403090340003000524884441030004030305900151001c0d81c10042c0a80c0340700400e058010302005003e030310001001240242e44210003c0c20681d0741e2845a03e80d011648010314400742c4182d4480c0416800003011a01000040224180a44040c0000c030030381052900d404006c2c99010201c0c424100100041141d00d03c200e2010754045e9440703500da541e1841c10504500c44c0c80d0301065440d1400e0015000c2c0040c0c0d40d61144200e02c00b000300c0c0d803007441300804c00407c028111780801c00c0807401031210401c0c1c4d206403c500d000c5032001c0c0403140110000c0e5102080780c2c10200c5004410b440100343c1d00e609190a018103c100300d4181c404510f9414444403100c090b038080c40c200710074113441c1c0c0081805814208624141503811054582c09130034048009911 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 836493435 1250 836492185 836492213
    0xc03080c0c03030405012f030301151e090b0d0b0a0803090315060306130f02030105190b0a0f0915030210090e070e100c030309060509100f05040807030c0f0807 70
    0x100d84501e41104909050010072101070301c0d016100c1030385034000c544c1c0c1c0d8031001c0070104242c2c0c00702101d076002801c000010000745002e01451a0500140c0da22250b0041024840303a00f00100305412140004040b500015034100f80d86801a22607640c1c0015003e54000d0700284800e00d801c40340c40e81002450761404005401007400c214241c4240e149003181d045034a442c180c0d03046a06401802c00314220040c400001c42225200b1112503505420703540001c0e084a03400c65160114552a41c40351041075910710503841e40070710807201c04070918109001408104098005c08501540c0c0d5045004030380307429800c600013981d00030901c40e086280c04c0802421a8880d01c900803110101130040785004e40600c0001d202c2c4107000d015803200303070b070300d11012181e01725000000e80600d1fa450b8910408a070541c003441d88580b690000038003282039000c00000446554404465080e441c103000c0c0800221402c0c200d80003241c05107014001031926041c030008000c0b42c000c006208000001c0c00720f0030072124000b9005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 836494685 1250 836493435 836493457
    0x204050c0c0d0f0909090c17070305011509050601020a03081503120c011a0607050303190f020d0905060a1a090a020417150a05011206050a0b0301090516080309031e0a0c0308 76
    0x1c1c00781d41d28800e9406407a0700980043c580c07c1654400e0126044069001544002c05011602816569292242110710443c2a221000c3c102e8405101102190042d2504550284001c08001e040307910024040c14028240302010707002d50542501c3c55601300f0a0500d0962240810b035511007841003240d00034050806a040180c20b4080460054540b5409481e10960080041d610395501c940707044107402081e452981645aa030f441b060b8411880d4800b900104e0320b03428000848000d141081458040c0c0101304040309404c0510010480901c0751849040e1201500c40c060300307494181c81c80010f4043c07600070203011103036200c072210200e600040303066554681ea5440e60b03440d10340c0c0c001002031f12800d000d000c40c501800a41e100000c0c0c2a5408903030312040c064000624a2034030000a400d40d64030041c180d480d90301c119a25058520784a0018005000e00c10040d0b04d403050107408070f80c495070729031000c1c0f101040c01034256040d0744088c03080c1070301e20750b0040081a500f07032070b49007018a5803c9103040364 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 836495935 1250 836494685 836494697
    0x6070c030207080d180506031009051e09240606041a1603021e0d0f05030613020a0e0102121315110d030e0d082811030f06031c050301030204050c0c0d0f 67
    0x486e8101141164001c00d1404030b650185030030311601e0f0b005044064021400064054034140000c402c400c0c03054002c4181c1c001a00680d11142d0b0b40a180701100b07011402420350708002e005582d92031100300d0302200d46400b000038820f9603442c0300c1106802458800c00b00b01360340ac424003041641c042818550444140f4400f028000c5001c0c4059507026044420800f28404554991201c0d0182d0051a44500018806180800684418000d036003105100c0408030b4400520320495603014001040980c5021030154105003254092040840c140c0c807035044d00748404568030040b81d1140c5140325020b642c2da01200c6003200704410080c000c1110744400d048500503d04007030f072020710506450b4002e5004820340c000d21102e02208118071215000070300342207035441d844002c1d65550031000e50701c03442c0021201c60740713850628189400c0000c10740018503141140580308031704941000660f81941c0d01981c0004984d6508120141d00b0710841c0071003c100d20940b242d88800a611500c0828688803aa0700c0d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 836497185 1250 836495935 836495939
    0x405100503010302220f0e010f06050409020d020f1c110f0102010203041a15120307111210110c19020406090e0307020d03030b060a05040f0e0906070c030207080d18 72
    0x4603000e00082c00025030000c2841c0307040c0e4400948800c0385060a0f011480013030454030f501d891350100c4455108188680c0d44454000395142c100e44210001480c2c01e40b024000220141d002034694284150001c1c400c0c00c0343d15010a00d600c0f4803c1040d8144142555154120740d581040e20300c0044041c0154403807a1080e036201e0700395106000b5280540d9010f640800d40064203c031689040034020424043e100d0100a00071030344c1d07213114680c4140111140996074074009403c094400007a061122030040c1c01500e480101d1039000149100340304a10100080c01203030900d184c034030a01c541c6903640305a00c03507069080d01001c25164000c1c246482298100310700c80c0c0d600307042c0c13042d10070800000c00e09800520001015007801c0c1800b58805100b8540001c901d1001400959241c0240c500000001c001260a001541c0310811010290003072043d81c032028034210820b80d585081c0107101700100704441c9092001c05000300503170f1014040081c20f07038070380c110a076400803e0745000110f00044010308980c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 836498435 1250 836497185 836497187
    0x70506060609060a03090516030b0108060a1b030c05160308150f24070602031303090b040b0702011107241d010905090910051503101401180b040c0203040510 69
    0x116240e81d600030f8001420100b10000a80c02406035450940f40c50240c50010002d00b20019844c0300950300c80c510300e000701d5040410061a0a50091001c148607203889481c49002c030b806242c0c946030325803130702e03004c90b50139a4179200f22780300d01907205e140079803900004a0b441096006079074503100b5406103950354510804401008203281d0342020450700000001e1403400d51251720380903030041c50f4034601040e2402d66155540c01c1240e108130b03180d60003603c044200e941010f45c4540148010015001b8250409080501c03520051140b901c0090501c1643e40308a07204403400d2051000134055500f2040c25061101c03581d486000320b2440307000029084500c3d10710034075544c4a503580584010f94030100442e040c2000d1122903075000d00031a4031485500c150302003040c458003c4501c21091140b41c0420111040c0c02c0c1403504800f40502c0208030b052851501c0440e06d0800b205045402c400124a01407039140c020704000c15400c00030542050800007900d4210307030008010310403910265042c100c0c0359202d1074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 836499685 1250 836498435 836498437
    0x1206050a0b0618031c020708071a0307030203040201030b09041506050a0e0114010c0b0709090c0f0806010509040f140603071203120b040605030d031d03161e02150705060606 76
    0x40115440841401004a5809011a0300c03030f843c1c102604441c0040c0b600c0061101407102644940c005074022101440034040910102c0e0082c11a01c001010807901304510f242507010013809103040690110010302960711a030009807030fa44000c3e00031011403c00b800c103080100481e264101c0341c80c1c100400043c46081c17100c0d004040358100d0003089516402c020441105126140a80d41005105100c2c0c030301203801051140d001d01e189495420b0414640908074060380c400401060070301c60340c642901926900103000c150f04c46000d180840d580d0000c0d000103002407498034000d5008600d071514220903855180990f5005000450841d00312640e01c00000c0e40c0e8041c8050b00400043e041c60700320100c00542d401c072130040500100045816902c82c0c01184c503118646c0c48440002e91100085105a25007988800c20398000c980a1031809001c1c68904564640307540c801050301c0282c04244000c8061108103141e0140d000b41000040001c8081c40c140580210000780d400780a0312001c0340051810310 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 836500935 1250 836499685 836499701
    0x5090303370207050414040201020a030804051c030b13181b030b0a020a0e0a14060f22140307120f0c050303031e150a180908041206050a 60
    0x1001145060710300111601154503000110000d09940301d104515240990801081100310754002c2c0b01c420f02c0d00c03080009691440c0144021035244105100150342e000c0b40c150409a018101820240c07a04c1c5449403502d0403101c48030100e007104044031568164950030001d0401d100b1a082540c0340c0e820003498080720030300354003140c0300b03111680c0000c001542205003054204071400109042d55403502c0710020b005e8200c0d1844d00c110750004041030501d1b040314518076038401c01e80b03003804081d00705810050541e0440745010300c16240800e5020119a400c0704982040c01d00f0010203491244201e080d6020078039500030340801858148401e0041d04000401e5022218254150000c80c601611441e0b0b0300c509000003924078600308907000c00d180c2c1b81000118003400702e00c0203801990748546052101c1f0700002c1c10340c2c02000040180502e0983d103c90000c0c042d10f80303c60340d00c6105a03102526900901818000a10003600800c000602240d40d020044106004131010300040d0388000d40003049034845 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 836502185 1250 836500935 836500939
    0x70f080304060f230a2a020604140a050a080a0308070807020a020f1201060308031504060302030c060306180f040c050102011b0f020a0602030f310b2205011b0509 71
    0x242485060a12440240c0c0103d0903425051142c0803280b0241591507000100680c003141d1b60f4180c050403007800c21058440c0c6c8600083c9801171401a600080c018812440b030f12842100c0305003500340c10340d01e443c48a001088000c0c10790602683d52524542c50342152030060700401c506400080113540100c1040b4071801c01c41d03010b4030003c07055908000c0e1014a8040c156084501041d060710580e5003481550080c6000c2c038611512854513000c0140c014003401545405070b070402100300300603140011000382980d4100d50540d242c0d6504070114000604000560100743c94080034402c9004904440764001c41c0105400358840343c03604011780c2603884609020120074040d201c10601c151084418081040c0d040c2b05407103160085850304020303a00103503191010314000d001441142400d1401c03030001044000702d01000a16403080d541140302203038a014003003020400009a080e200081c10f1844240c1d44412031000c0c04160134414002c10f1102d50000d00c2d001d10001d80c50516026100795090300c640 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 836503435 1250 836502185 836502197
    0x30309060106050d090b2e0b0403020405040203120a0c03120501120b04061b0e090601080c030103150b0d030807021209030d0e030a020a060507030e061c0c20070f08030406 75
    0x1e0031804440d00e078480311600441340e550f52011710025039581c040501480750001d001e01502c1200207681c0b6050740400c0404030100b01c1c24400c201221210050728100c0307804680025032540c850010a003000c0214201c000c0c85d00340001c0201c40315401514114440c0c0c002e9440c0490b201040c54800201d900038019681c1c0c0c1c681740c4500302d0000c0e030304040540d4044d200b0203001c6014100003590f0640070b40c01803038600100e0400b402c0c03980e10f401c00720086903002100f481d00c1d002608004500614520040c04080c114006809800705003d23041d81009404c3c0c1ba0160500f1340c0c000c49030500800050050314246e0041c01a00f40310300340b03030b4114003c3d00c01282c4014050701c00604942c00554407600202c0005400d80107181500c40503a5030203071640000d200d0b903140c0030795035011450010046100c0300c028500c00e510a008215224042100d042a090f030300f00400144030b11010b9003990b5000c420111a100290340c0c0303101013074000012030140308030780300307100301e9008280c50f4140700ea03e038001c50044200141c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 836504685 1250 836503435 836503439
    0xf080703020f0d0c0f0f05090a050c0304080d140a052502060c0a0311030a0e0609030a0e0607030309020409080414040902030322150905010e10022e0e010912020303090601 75
    0x41d00d03000d03042c0f0042c4a6001d010850382d94044131384202545074840340c0b03a4880c0703000c100410304010040c2c07540304001c62403c0000380340150343c040c01070002600240101a0220340180c40c3c1b60580e1110301d440020303560108140c80c294a0300030103000b089a2404c039014601c42c02103043c0d0b040d1444c001440074940c01418495854954060071078002801d00070406880d02d1300080e00102d0240250f000d0b20030600046000e08121041625005000d0070070010741c0e0007000480b0450b58440d00c0021142c0f000c5076115601e11042c10100c1c05480200006540302e442c0801c000102f02c5000c000340103c4003c1144440c21a0f1300f10100000c442031258040d4054100304124a0b266001807201c6075200c8011036659841c1b40c65810490900d410010940085030042005201a6820001d0407a164100300c9183d01c0e200d0541d00e0003174846035001c00c501184c0000e960000444e180320007628820100c3c0c1201006518028161540030b0541d850080d10341c60550b045224955102100322482202803000034800d40e4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 836505935 1250 836504685 836504689
    0x20f0411090a170d020703050a230610090b0a06050d0506060403050f010f0b15070b060a0510020309090c0c060f1306180c06031b080a02160c0f080703020f 68
    0x22030420802100c8000800804400c0d41d1541d5020020f4031064030044401c10000b44140e04c0d14400b18050003c1d98414a01040003880010f10340031026401144500c080c1c4445c0d190707c0254091140001076401403000308107104141100302001c455000c10180280e6030000103000f0070307408034003507280080c20800c0204100c0000d50401600020060109071900d0340c4ca0303c4d2a170074614580c1c2070480507511381c040d002455109005030880c0d42e1045850220786008041c04811510a00c28000c10500650000440b9641c41c089400010040a81007000010000e0402501d83e440182505d11480540c0081001408041c00341e8129170400c1300100010b450355104c004452000905620034011001464400108580070b070824160180c03984020070790f05c80c50090b84003901ea8010b0010149440d4203600300e007020503217442c00741c0401d00b0309850f6500d4030040d85019104081d1400308500d031030ba1140c4200011010b00600300c8501014210603151200101500c07100c040c80003135031005001c03000d61024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 836507185 1250 836505935 836505941
    0x60e0112151a031e01050906040906060e19110705150907090207060203010608070c021c140d231e0306011106010611010e01021204080901090905010909030e0607020f04 74
    0x200c001030789104003a59441c44042944121060400000c50002c001d002e2075184803101c41050b811000b0400c0d01035070410300440e0700d68000800207840790f03403507440c68001d006003940300300054840821102217074940000385084c000006008003038424681481600001240b00654481940c468040c01ca00030403100046001030b4042d00b00c02c00c50080e01b00000c0c600c501303071000301a442c3c070030840942c0745d6140c80d42c01f4110190007003410062016400c2003800585e02c21500030003c28009035520800c0046040c8100c200340c0140410300304d4070810304140011a0400d007850200503004062107010100f02610347c10307e0107540341d5032a141c400038060b5001100f00901031039000006140404d10701c1140a000c0b0310304042a4080f0010405500442d0507000c4280114a10380311404d00a600d0325030410740554044200801c0504001404030b03043c80a0ba06c94620b600082050030000e016550316034076820000d11080c8802c9001c10060030700038030f0509202094520082e0003d00c1d10602d00f603410180b0004d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 836508435 1250 836507185 836507201
    0x2105130816032909070608010501080402010806130f02030c04030b180a03050a05090d140706030e03090915030a0b0601022103060d172d070b0a0c02010216030e0a060e0112 75
    0x40314039090b004010f4641020144206120401850000c0c9092409400e81c101038120b1410031100004000151360020f001d6508a4400d0302d084c9141c1d040c0301c0020340242403007605800d07101d00000900c007149600f45d0140041d40e0103843c007211580c840760284007410a000100d00b000d40c0207a8802400310380100041c3c03410b01e444d414a24170b000c8103200011004c5100c0c8a00b210400690410400002420803100c0301801c1507040401000c0540d81312031781d0720f00400e80d441d4071407001080029105071040060404150b0054203d86800d2080e24101c28070040840e00c050040c401d0481c04070282025550b14036818036040c048074a07580f01c2030b09104c1418072501064410741341003201ca20300c030009200204800c011100004240c0d07103c8200007922040c4102c030480e680c4100344003c0703001c83c08181102e0381022014000081c5940c00e01d00980c0640100700a05011100884c1c154042c1900001030202441d8116040d00344c0e107440f45415035400d00c125206a0000762550b504408441c40d6074800e01c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 836509685 1250 836508435 836508473
    0x609100c02070b030a051611031209010b18220c062d020705010e031c0804111f0f030c08060d0203100f1d0c130504210513081603 57
    0x50b650f5221809420702c2c1d84103880000c5619074480c10011620f03003e20740815000500d18080205c0c050000182c0e03624010040b407010b03124014800315250070740940c0b10810041028110110802c1c1c0402003004400d4210f500440241c584034610724041340c107032242d0044503804200f040115040100c02c1fa4950743c1c000b10384044003d8001300301802801400704488003446a80200541402d02000400c50001841c0040c000e40c008905295011038565201d00714200b01d2600894569490401c810142c520f2254103401c00341c0102440b400c40c1e946040c42f0260250b540314410041c1e90b9440860449450b61902000140c4c1c80300400c8003490724440c41d41c1117600090445650505100080c000c84884000b222902940c84071000030341d0860110130500806440d014140e0b01030840d02142c1e624010101c5503038143ea076640003408022032400e0081c403682d640b00c0d8018090000c0301c0d0192480d03000e00c0ca20388001c03606100000e05d0b0303000095202a40300103441c0103581c84d444d56548040b81084c03403e80c80 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 836510791 1106 836509685 836509693
    0x31401170f010e060a0b03061b0309031608030a0c051303060c0c020316061403070f03090f0b07080403090807080705060706061707050109090e0a030c0212160302120609100c02 77
    0x42c0c234240a00b20304580c0e81c0e540320744050030751037406805400020254440810b0058400c0a0743c804c00e0644020040f104100c0ca05440901802c60b190701401c00344581880080c2e0140c00058a070242402c1c08111040d4560000e820001900903040c0c00860303000d0204891a40807034100c02070786032145801c0ca07504000b00018000c80c4501200c002b070544800b1040c08200c000d0152141164010000d02000c0c00c00004c0200300380d0b0300740c90a4000520743c483c081422000421845e0444240c0c030000d00b5058544070500c0b40640043c1425142c03a980e4800c0011403aa02c1500d08032042c0b2460003420004d0708000014080190396042040751618055025202c5040024000d00943d01402d0081c600c00103840062401420b40c030b52003a0b5801800300d03a00c11452185030500c00d507031003104c01c030300d589400c3c0b4401e90790746a040300c14411640c845115510754421a0740304419401c100d206903 = true := by decide +kernel

theorem cover : BRFrame.Cov 836330935 836510791 := by
  have h0 := BRFrame.cov_init 836330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 836330935 ≤ n) (h2 : n < 836510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
