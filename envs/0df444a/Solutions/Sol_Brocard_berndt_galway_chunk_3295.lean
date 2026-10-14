-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3295
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:14:15.936201+00:00
-- url     : https://prove2.me/submissions/691a90e7-e69c-4c40-84d3-e4741ced2565

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 592446043 ≤ n < 592625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 592447293 1250 592446043 592446061
    0x60403080c071109100801090b07020c0604050604050f120303010906080d2a0501110c16150807080915040f0b060109180f0209030d050c070f050d080306281a04030308 73
    0x1130281c000340c400b14407140e001505c0c0a00740a18031605204040440c6107013881000030346000407240c0c1161050b4410702050106444200507102101e00c215000040c40544001141d81d0320160154100c0300e020004c0041126250350b04008100d40f4207a00322001c15201c080304507041d032501c641c840c28840106400a502d05041c02d89104000d01500001984018040d08540581d104e905d402c0c00e660014071084600d203204000d42e50040c1b80d10242a0522044d501d0000d01d658030090000c4207012280d404a6000301e8100900d00d10380003003001e070341c460781094107100d410000152001c480402d000c1c4002440c1c0c1d441881c04104454140000039103041100c80c802c070103000395034040301c907580d82400071481c43e41d0100055a00961103403202d03559601490070040c00c10109800280c00d80010110410507900c40303042c000c00494005c06d41f103440741c031020005210101000760071003260000200c250132000110000808032104a040c40d0b00c2040a00501306450045100c00b9000c5502c950004880070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 592448543 1250 592447293 592447309
    0x6090105060d0c12150f090c09060804030306051c1e050705060a030b040c0810061716020109020405040c051206010e0606210c1b0a0c090f0b060c060403080c0711 71
    0x3c03015060400d00305412490f5901228030b48401e0b1491030400d580d041025425000405000e03001c960018002d06503d07000150100d840c030b2003004c08100e03101c4005030a06120341c3c0028080c04004042c420703001d4007881d00030444d0000c92030940700305056004160395502a18444081c0e1035004010303007620b80c544030030410309410045550302030507200c0400206590701c520441078691415100d40c00b040c104541c00c64070000a0f60030910174029000140895424814030040d41f00d08400c510100d1000340c0c80d4100e001d400e14501c000d400030b0410040c03004002081c61010143d80b01914400119041d4012450740e44d50288584107502c00400c000c10042e040038001415214205815003286480311300c2100c51001048458028030304001c1600c004401854811400902680e001840011456111040d8401c0c46100360700f51303550307920b800344441192900403c404c242c004044035250f1400088850b120a01214110300050443d0f00140d00400c0c140240d5034083d400909201c100080e2409010ba02c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 592449793 1250 592448543 592448561
    0x1518060103081803010f0e1c1d040912120f0c0c0807020307030b182b0c06180303090501050c120c030a06030f1406090d021203061c0507030b06090105060d 68
    0x10301001c0c20200c100c4d18240038046c01c0301c6415100203546d0030140201c038107040440d0b10f07050704c440c0282d84080c10150300c50030032150480c114550120f0342c2c0c188400a002480b80c0d060041075400341380042041140c0007900c503030f02d10b441d6842c18009180d400d400c14003240c0d0001624400704400321103a03c04a00d01c1c01c00342005901c09070031a0b0b2525100c0d02c80c7d25400d0f0b82225100c01d01c400d6048443d480040512512851400503000070b0f082d4025000344131400c1191103154020801d0f078480072000e01205401c100780e003110603030250580e80400c2c180100038210002007070345c0300c1d030030074020030000300907401204c880381d814541030769440c0c40e68035044000340c0c000703400f01c0c0740b00e600c3d1480031002c03455601411b809284500c0721060710310b0006500c035041500090452103076030851400c40030b40342e0700800d80340b9045601111441d0b03696112400100345109a88903400000c0c5c55148074000c101c400a6690184da006542d105500d80e2030b2010020070103401d024075034120200740300703010300711308290000070407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 592451043 1250 592449793 592449817
    0xf050c070905011e0506030c03131110090503060c13060f09090507111c1d030106030c0f0e0906090c06070201020c0d0b0115110703110111010e151806010308 69
    0x1203903680345950340a6500a822030380465007a90301454003140d550a0b510300801095410f07904500d40480d035090750740030040002e00780b0000b00701950100905000d210b41506001402c004680107900703801003011429000e402d029103d002c02080358040310700180d03064130180340ca40c0304100e400c1c800c084860018142001003800652280440e01e00454001ca501c100e03903682d600c1d4170303401a1810383c3c1c0c0f90103501341d410003026400300500c00b00541d000c115200304640c1c042078800703072081003408a030042050740d0016101000b40d07203000c690308010755450021200038a49801c0e054462000385038440344156110481e50b40860b07204400e505150003e002410f00500540d0741854210300404c074049403510b002c030b844800b0000140402c188091010a4010a6180c140c0c00d050312036070399a68920f00c80c00f01900c13994088604503542d84c800d140031030803111003c009110340ca4100c42c030690740b8182c00324048802c441c200000352030381103019295000302440f0001001c442c0d2861320340b030780e5503400350804001d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 592452293 1250 592451043 592451053
    0x219032f0c070e04020a06081504020306060d06080c01090f06080f0a0b090403020f010f020a0509190b0c2a01020d14090d0302060604110301030b04080319090f110108070f050c 77
    0xd140d880c20300075000140010b0f4442c40322854140f0410022205540003d000d01c007000042c02034039000301c181601a504107450042e5030340c03565400140c0300e004040401d0001402d007080400c0110005c1140325981d0003c4c4c0b12038010075181c2a41c000340c1b4080c0d01609001840100000301c9181244202c26000b01e406040007604031b0080e000b145044808540a03000350740400c1d442889204240704125007958001c4003107050408102c4d0060181c840c80f8601c5102d1850001c088243d40540000003000b80269451256109074516201d5111820102c6c2402100082c0d1402d585154284154000c4010140e014110000981000f650481c01c0303150a40c00500d018030841085840c0c08000316181402a0018040d520b0f1140c104000e031aa200040c0e400340d282400100002844481169045584001c0c10f64a030ba48a6080d0f010041b0402e4082c0c45143c2401070280c1480306005110103643d002d8444200301d00444401035407000c03015902000029035030141c03403800d1885507010382080904041994 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 592453543 1250 592452293 592452307
    0x312052203050a110d2c0a03150f0606080c1803190b160c020d0503130306020418140a110f031e070903152d0219032f 52
    0x300e148101030400c4022030800150614001d41008400c151441a01c00034901460744c004010190001c2803100d2500c100001303004078082000d94014030014001a0191700c02d1952420454581442e102450704d5592410110603802c5080e8007503881a601261100b0003540c1b1034003903406403039200c1940c002d040c0e0b0b44064243c100355400d0120001d240a0040d200030070300c513581010103000c036002d0050740a00d908030460b003031000d400070350320403415404a466414070512404c105007148550b032a0342c158a99038007008403c002c190360140050350b821030445031515800c030000d00c0855454241c05212250140d00040102226400840304030480403030050400140c0d4441c00565082940e41e04d50107280004920f40030015071928a40c01034851030706915103413542e00e45400c11550b640c40c400c00a62074480c0038950007000c1e240200304040d0110312404a024920b01c01c070083d0064140b441d011081280c1501819110f402402441c901c50200d00060b4040d1100c06036000b107901c0516140038000340825 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 592454793 1250 592453543 592453591
    0x2092d0d05010f14090a060e10060f09060e040209040618050a05100e0303040b0a0c0504150c0c050402040806010b03070c152003040b1305010b10030212060409031205 73
    0xd00c01a00c28400401da0703a1800c8200c0c0151079884080c0c0600c102c0c0d0104001d07030981c0000e00e43d810306d5000240080d1110891100da03080c001c000e0a880720302410468009403a504282e480400c40f1000d031401c20109884a2181c991a0400d840c00703903100c2481c0c004a00400c0e0380780e00120640704424a00080e8075003a503035050074525450020740d4550810401e1000e841128000c046914009030041c52551810355544c20300e180003c0d1000300640c0e80d40741c0c0082e8442c05101200e02030406200c0c4a1882e10102c11b0080070007403604000c030b03021010407100044030704260083d1429940b1800c0038000c2682040e0926030180c000801c0001040140d850741c401003103180d441003088052404011581c2c031030602c0328240081500403007451070f0104100308030100380c080c00c0380d5411080c2c044070000d12401c2410301c00d0142070050107403076114520001090803250103a000303011203011000e00000d903546207010003048440c40c0ca005008950400d441004244242c0c1c0415440200070910856002c44000c2d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 592456043 1250 592454793 592454809
    0x42906041104080d03090c05010c050607110c091914010807050f0d0602400302091306050a0c140403020105040315091506140f010906051b0d0c0309060302092d 70
    0x40c0e44c002c02d079101400424003d03580144400f6110a08001c60340c408107503200c6950b440000c114a0030444070001d08010050309004130883c54000400607942421300c546070160f6400062060b1848034584011a502399262007240e1b812520b0031030140030050f26000601c80c994002980340c6a2088182d640303171000a00d80d02c003904407582c0e02805402c00c020b205030b04090b880c104540e888000d50304c00c68600901801c529842e816240d050743c0e9107208c3d40750546211103510890030b00501081c100130401c154211603510210b0100401d64036881100c01c0c1d060b442a241c401c5000c080e00080003040180007083c5803030701e40c8400c00c0105100203000e070030070745960724144001c9904c0c080540d2a9081004a4207148202c100c40c82012100c25000ca8442d00000e0040c14042c130a15050101c0030564081010f415001450716a00398429105119001e11340100542ea00c3c25040b030124101260109440d4400c0c400e0b94410900a8042c511500030008641c464110000001402d449000a808115221000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 592457293 1250 592456043 592456063
    0x1b120e010b0607080705070816090b0111013303020d060b13020a030204050a1d010501231602120d051608070501151a070209040602210405030304290604110408 70
    0x1144c1500c6010a00c0c2190400e41940e020080940c0280c4070502c0c1c00620b0b011102c111540d01100003070b0030200070016940500300c032040389004d52070400388421000b5698a190032200c0c078604c06000008092030962101102c40c040a50006008141c1c0c0c4000b0b0300d568800f113030a4400900c0c2d860809203003800441a03038414541400060340214080049050041008011700440000860f031182c030905209101031051103018104281001280002c3c0e0380c044200c0d4282500700c107102e0782c6a101d07035604000300e0f81e4600704070701910254043e500c041c0c00c0410709800c0142642d40b198680840e8000300341d080b9100708400d8403590300811031600040d0091103845a0400c001c0d440009261504800b80c41e00300704800750301c52004040104000507601e02c0e0304182c1c081e034400740050701c07444041c10141d0b5104041002011b1a241c100511090200010242d8896071007441e5550300304050600c09450704807000281e00141104901080a914080c0c21543c0602c0400c289a400c0c2981c0c0d1404600e40322030b601d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 592458543 1250 592457293 592457303
    0x5330a1709011407020a0302010b0904080913020913050f06031614031f0c020705030f07060c080d05040b0a1116030c0201022811040b012705090106080a1b120e010b0607 74
    0x200c40e0071b04160f020701074041d581c0011584183e00d031506803070305103251090540c243d11a0078414090b004185d5154152039010301c0207042031480340d00b490258401041d06031030503100d000814001a226140002d05884c200b8058110042c001e460f08040800b540d1400359041c0c2d060040401c5600403a443d86100070905e0074291000c034041202c108043d04041c00d076003049000e41c100c107110003025a00090110201c445501d070000d1003195600705890a4007410b4081131146040c8002d010500c40070f455200e0003155050703810000307011804a229118890704441c1080d40244d4146031000c01d00a0f440054514018010354800310b01d12030782d002c048a43d012814040f011019806014441e1084907400809001c3c1d03400c100321b076868800031740540020300c1001c8012240050811000b901c440c42c4000512021303005040b2540c44040203082c42c001168941e0065142c4400f00c00115083c4c4107504103580103032a5201d04032803d40d5907401a0525200021056407a18078a1510380c99500051038514011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 592459793 1250 592458543 592458553
    0xa03021c08070f080711010c0c060f0207030f05030304020a1707051201020c0706081605280c0510060e090d1409010c1410060609180207060605330a170901140702 71
    0x15183c41b07580301c041034413060704001a12120100165035040480d09803440ca01b0300c62568810510103c1c030f082c10a41006054a1040c0d2114040000010286015901c00c940b0303190b04940351088902c0c00300c84000403c0c10782c2d0080d1420130042c20b00040b03040f114155a0005032412024242030351074010545d0041c0700082c01007003001814481030041035042003007403070224a815240412a415558007c0c000d08039411081c054014007801404c030700c004182d000741541c000300039016103800144450321802481041201c0000d01040f80030507041c645200700d4039035100070059262950955000709440070705112100c0d911401040a04500c02c0c9420310040007882c011088603146000c2e9041940a030040c848589001d214007130003091800d400448a5000607101c4495080181c042d00d26544903d80158040c1c070140c9144061a114181c0b114507138900301420707000500500124130070045038800040188a82d07114110186541da90030019100001c20400f8a500c103043e00054290b0703050703015900c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 592461043 1250 592459793 592459807
    0xc021e030606010509090f0601050c07030305030f0a020901050726131508071d0607080d0f1103010b04120c051011010e06010b1605070f17010b0a03021c08070f08 71
    0x30821180340c1c40002032a01900302080580861400c501c00746c85002d00000c800c00186180e445030007135500368940301040b50803096032414050030740e90090340c42c0c00c18940c0110000ea940d41d85402181c0c00fa880603581c0034039241d1a80c03603010b0048100704214114001d4442850403608040e405041440f100d1f03050f800e801d518004514502d540a490b03280c06000000040000b62038104a035122400d5402920041d120300a2001499501c2501e00042c99160041032454814603940d024490802d22000104010f4080c9035906440380000d201f805152042000140815606064103020f1a4481d210102256031070340001000a40c4418140d030004040c3c0c3c8003404400307070074000c0d070100076100701c0500710550501580061a114021103580b40f0a2946890410001d0401c0140010202041462941c5032104103141000000e2981c4402c0d0f5800d00b003c0880d240340c414004411a80d00508840f110007040501ca02080c0c080e120554440b081408040c1c0850102c9259140c600d02c11b07481c065403007076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 592462293 1250 592461043 592461049
    0xf0a060e130504050c060c010f0932060c07030903020a0b0a17040506011202060c0f06090708120d230c030f13020d03031a03030f0d05160f030504030c021e 68
    0x14544860001c41030500050001090700451450000001554810303036803510388200700d014150003020610300c186882a81428410103900340506149410007d00e254501400c0140000051682d8810b00350040390100300f012403a5001040790034420308110712006c0e581c0d00020078055540d489202c03880000604800c0c01a4030050300b2480d2200003134100c40302d0070651240c1c2d5071180e050080400f4111808540c030309542d1a5015100c10200398011124100d000d182c3c0551214009e1790740081030720441c203011524000c003142c4410740e007442d40e01d154108440c06a108010781345a8003d050142d03c101201d10042082820013440b815508960969a0a2590080b10211001000c001c1109055a00c11006030745031081032030300e16090319000c100d07104640b882860220198020aa00d0b100015088410700ca400000d048140c1c0d100c0000c00ca40c4d03907410444064000100d240c980094075046d40e40722164001d600c51a0014028a00340b040e2034150f034041030088a001c000c0b09048614800045264a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 592463543 1250 592462293 592462309
    0x10e10050a080318060a050d0f020405040e07061101020703080c0a091a0c0d0c0f03030f061203030f0615080103060504050705210d03020f0421062406051e090f0a060e 73
    0x1040c5d801a14296800740c0060481c0a072600d0384100075216001044005002e4040d940030302001401080441600490540c0e05c0c400c501c01c810206a0f91200d4208198044c42940c21140e09030700c44032515175810721201c0710b80e440180001e040c8080e210001c104421840301078416012841c1c9034641e42c01c404140e962500008a1743c400c00c000c0d0a0030b61800080d003101c96100420b13894200420021003034a0100060445a00800480c00100282000385545500b040c420b03030101c0d450030481c460302c810bd401152445011444003050f051b030010400168640d200d994098018400e540501d603d85000800c615400345000800c00404001e65000079018400241c014a4504046160915030220200030b4002c0d4801c83d5a46c0c0000c001c02e006107560000404400c9500c420100205060104008001e2001c5211282ca4504030b500109955000d102210718400501007005030006e03601150010035442031650a82001002c840118184c9a0b1031015024009588a4840003940c00090203400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 592464793 1250 592463543 592463587
    0x403120206060916050702030f0d0207240f08040501180305030a140601090b2b050f0f040213022a0d300c02030f070c090e01020c06010e10050a0803 65
    0x280e2995414080341c44101513a00c0941c0c51582409134480703080707000107802d05070070a015408500485143d0072082d940031404c5000d66508454a003800b80c03c03000c4c81e4450400895000c0082240d03190030711000b5010b4500346900c14814000071030300c0d1964440703100c45030201c081c044001c41e1011044c880d020404c0d00405215641c183c014022070310f8100300003000f4217861311840d1043c03500010180c4001070040c00300e4103400c001c580039401400e980c40704034000f4007048844403501c070b038004042298075030f829204a0040382c0060645598900b0341c500800294800c6503030781c158801c4040400804801195913400255000d0041c0414503514000980040905062100440143c41009000c00184e0481d00580440705900141a0110700d009900e540314a1403080281c0001142a05c10803514061000a40344c40101c10300408c1c9c008100c0c617090340154480506c4641106005200e454400072810750b0000c01f400c000041c80e60390b00e001c228003089640241e40c680d000041e20020400c94407102c0110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 592466043 1250 592464793 592464799
    0x230d0c0f05031312120518070f0609093209070503240403090503070f180522020102120d0f0e0d1211190302120105061806030a090602040312020606 65
    0x1a500e09050740d207601c0703009a00010004c00c2c40d95a959121446044d1160b518103e601c030412003820420443e02c14101c0e49442440a0320a155001c11003102851f02c07501198034503194903c2c01420110309401500b500408068807400181c40340001068070700708010803000071030411106050030460141003e100d50881030195104000c01200c5100c001796000c0218420890550a900c0c0c038602290200030a40c4210380c5482510000700d42e188075a00c02400700d540092103042ca0b50b10b02640d0344142d0340101c8030000c1e1071152a04c6005044580c0031060081031052059420035429410140e030361307801c080540d00405540f042100c1c41441c4500c66401c094a04c8402040d24180d107140080a040740c03600c0c59841e0680703a03000312031901a500145c4003001566138a2181c0c90f00c50800c000c000f90440d41869103806a52000000c090804208a40b9110b58501032944131016100c1840410340c0054142220307282c0e1004060f0115540380301800c007540c410380100341040701c80300000345420710242000344 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 592467293 1250 592466043 592466047
    0x2070206211008070b0c0708060c0301060807090627050405010906080111190516080703050a1d03030904090507090911130b09130f060e1e07120201230d0c0f05 70
    0xb0f15000203041d00455190310f146903901c141c4080e4543c1000180d0b4002080352240340c0a0005c50803441000d141680d8660740d80c0110340d9500c0104482085181c030031a80890000309102da812441c0358040d1800412545e076a40003039a4850108040352402d9000d5044a075440d0010302c91281d00307004281e1640b01d81da4031503003012050b482250a0072030141c030840034004009202e0a000d1213496403c078038550040301130341d00c51030305003405803003984000040030000b60001311250b132496043d102111500d00150046083c00801c0090200034000740009880e02c0c40303640e01c0058800780900551840307902c01c042d40d503800b1102c0307014480003154010850700043e0411248440e680c855141140c0d00c00110f4041d0f04201c80c160a14992040c40724102070007042c01d200305a071b0b000c480041e100f40368024440100040406017040152100618041d0280400b000380d0032001561041400c0100c0807590082c0f460002c1e64010b010182e030340326061804a2944a40040300c21070b410040700d10480b0110f060043c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 592468543 1250 592467293 592467299
    0x715020c1e0304170f030703030902042703050f0417070e1308071b05090718080f1b0a0b04060905030c0a081f0b03030406020c0a091104060f03020702062110 69
    0x80c2d241c2c00307180249510080c6124940d07050300010030030114068141415641e80c3c140300e01300100500f1100c00d00b80e0213203003020091403880d215440c4840e80030f003240b5000101c1c40000e540403078a580c00300d139030341c0c81420081c0800300300c49a00003640007248444000a1040e145841011034040c100146181a0103940d00c46910103d000030048a406550090000c81c841c0e01a502522900d4001d40007250040e46681c00c100c2ca207500158001510003500d80d404100c15074035a00340e552030400700ca0320307480b5420100d11502814500043c414041c0303402800e0360030460300c2d0425141d0681040d03101800090340058200f100e41020b209084450600f81d41c0340c000719041c100a0360313440140d0b4460148250040e8603003200c2e188203521800d103141006042c0d0b42d5407956840020b640704240800f603489000c8584000034103040c0d034400c00d039458225440b50b0b400e2601e4035406441102144440109040d005c1107001c006907a484010f118603590a10f0410342d90341c20b5880320031022401040c601c503d890705513041c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 592469793 1250 592468543 592468603
    0x40509010807150f121e0f0b0d110a15020601030309080105010515031e1303030612032f060a020d0c03060b22030602030c07050d0c0308040b04080715020c 68
    0xa001c0c030f00c0e542c1000700d40681c51600072201100490079039804a4500400c10401031240c64421100c0202c2e802c00348034205100300d0207400c450503031450300d03803140c014003490b000240c040080c080d4400c401401c0b00302d456030320328850114010020400d00140c000800500030550040880c3c5c0207007420900812840d0704007004504c4103501425054030109002c400103030090b4240d140d074802141e160710028440d0a1410080290700e641e01c4040b00400d08085000c190107611520302550250956520b0084140c00800b10a0040700b8000946003da044050780d0864030007000240c2c080c5080c00e5006030351310104118a821140303000004001c243c1010740c01c028034041c0c00140c8a05620684148172001c003500d08058803e50b50fa0303c01043c0c24004010007207002d0a0030f0292507000d014500385c8940004040d000c40361010b5036040240480c81102c0450301140c8460704403a07016202d1082107181c18cc0540300c07229080c1c512021584003540000304200d0b08607082c01501611a1400300089140c0c80800e00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 592471043 1250 592469793 592469819
    0x10e070c03080c19020705030c04180206070c03060c0207030317040209011703070c0e06100c050615041d011e0e071503060509070305010e0f0405060a0c0e0a060203040509010807 78
    0x1400b042901c4000c01d500c0041c3d04221000300e100c4040d00020700301c0300c1402a4403580b05200c5e0500c6030141100300b000e1b0b81020701841086150181c58451700301582c1d42005010b4000c4401504c02000d200408400a807c03813041c81c00c100110380007802c406145140003002c0724008001c030b09400217031100341700050b216903d005040d5030301c0d10b82d541c0703c0c5151851641c0c07560158031000351914030392032000a0090020320707400d03028000c1a6241040020078070825070344412048402130265202c0b00004036101b42000d03401c500e5140081c0045610900f05a140b02000480812200d950355149140034212880401100b9000318110f004c0c008502008040c94598506200e20301d41c0b04103640c8400207180c032a074800030140c1030060002c0d805041908004000b041c090180242c06000c031000b154904a200400c2c610403a84240140390344d40e1408403003009401c00318652030901104072020f015541d00d185042c8080d0116900031a103a41c540700800c0340c07602c4107030f0006446030450300081c40b0707040074056 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 592472293 1250 592471043 592471067
    0x40c05060a05090907140d050415022506020403170a030c020c0d0620041d060d120c060f050c091309330203270706120b0312030c0c06010e07 62
    0x118814117640b00c44041d100307030b0402c21074400b21560009032449504801d5003c280228020b20500403a061080314210881c841e900703000c82881d03074440d020703842c08400c112071040c96449000c0160426039a5a42c09880c25071006540200c1400817034620310880d4588200240382805100a0004001c0c41000c079801c25020000548440c0c1c540303121114500724170ac00c030300c88150340d024403582c0c4d01d54410b10300c040746400000591303d81e0900000301d0340901c0e0503005007880b2600310000c40b1524041050640380f506d49940c0446469841d150f40c4000042c2d50b1041601c030390b00e100c12055907007040e0700810200056840d84061028605030402c0e000c41ea0000101b04a40741c81d800105c030a440440061821a0901c1d03c60101c1c41d00010400668402002a16140120207440c0d518028100c07442c00d9103d841d54010b482c00640d0280d06044844016000304000c2200501590701d2190b50a6901c03005078021149840e02c8103001600c5449038100b04645401403c800c3c20160742400c05010080000000c05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 592473543 1250 592472293 592472299
    0x402090c0a030b0d0c05010212040b0f0313060e010506012003090f0118061d0301023f040b15030604080a0302030a02091c0c14130e0123040c05060a0509 67
    0x109406030707801d00a03801655440e000406912103007603d0b14021481c40b02a005460050003445404c00415184005a50030f4441034a0b8590500d440790000d844681c00082556410210052050300420f04521407a0401c42e10f800c0085904e2426030b00141041c030b1001c4201c81c4500381101c000f29040d6000c001e8131910b05007191020300021000b00100c07a00c2490030050100407000e0080000d034990040c0402c40c0080b51030200555014440781058200e01071440310022a200d58105c4162110003103644007203076030740c2d9120306141d80c0361442a0700342c240c0304940485200103020280005031381e0b0b820b4452600074044000301180d150650f10804e0500900360030740b003815004000300b03c480760710340c041c1c40b0014070140079907025882c1e007501914010031036102520760038007084010034405406060081045406010016400000c88183c001001c034105406d040d03568441c2141c80d0394002074007861003404100c145807000e0500b424101041c039095400300303204500030441811204d0b001800d13200300c00012 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 592474793 1250 592473543 592473547
    0x20409050a0b0c031009110d0902060c0703081206030f1b0a090c0509010305060102010b0109050904051203010f0906060215010303050903100c11071e03150209090112060f050402090c 80
    0x2031600070301e0800d1001000b052050030310b00300118407594101035403252410f03010000f05c00740d0f0754004000301d070400140040042000c00c420000c1d600c2d2500100b5500b803001d0101c07464402d42c80000741c00c00741550412550700307100040e59008600c02007140350b0005070480140c000d84081c44032150b56998451300350380188014180103140350b43c8140e41d040c000d141d0100c05100c0c2c1c5a160704001d040f42d01c4401803d001c245010301044040d40305104805220f281a1201840107007058200309070007100800c1105e440c4901c42807039402c065120040c0d4001c0a0400480303c0030750820350024140c43c21504030404541c00050992102540320f528070341140d030541042c540d14124640400d04101070186100c42c0542031014103941194400007402d1099120703000e94190a4403541c000c100503041c2c0b11850090455450184082848002441c0c82d407411801c0045c60109544040340b88013409912001200626950900c10300265008841c00078602c41001c12051803c1d60020b82c5004001d02400550000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 592476043 1250 592474793 592474811
    0x616030f0507020612010e0f01080d031119021612050303010611010902040c0923300d020606091e07110a02060f0d06050907020c091e070306030c1e030204 68
    0x141c81100d02d03880d00540b0340c0da038400070003151132203104003031043c0f20005401a0004080142914401e8140c1e10a000a00001e00c50140114050700100100d160031040c1000306070500744240c0025400100c4540141a0380220590903d200c21519400700324401d902c04d010100060300881240d06556050800c2c0419203114500240141050080250003516240f151002c064000030030f42d048034964139030207017800d059003156103818654000064210300300d40c101c8580417a900f4022080141307280100140e1040e207849051810f83d800c0c07845000341c1c21a80030b01160b0304101d1540d03076001d80d4140403a1380200b440803002c502c0701c0c0f000303004008021418092440381c0009001000b0800e80052446841e02d441c0c541e02991039001405500351546825400101805c101585501c101040d80147c82e08100c41e000303010710114010105111000c80b8410700500c00c07030303440755035000340c0c09a80c0018015003140303802021920a1b401c420049801244115140e00141c0f4101d000e036a03064902007a610390b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 592477293 1250 592476043 592476047
    0xc061503230717030301050d0809030a060227010c030f211a0102060f131b080c040e01060b0915090607081c05040215070c0302130c0e0616030f 63
    0x14154000615109110000c4041800044511001c400d00d48040e1054941c1d15681490030382c2c075061440c07040340c0040c03004020a180011100d40f000b80030350a494036100b03039080000c0c104040900d0480e04142e01007569100111440c500031581100050100b01900078600007a120f5030752079000500f044400702084224522950300401943d01f4181c0e07202c0090410310501e0b01070940480c1121028005010304a1958800275030140548415051440341d0340f10f9040c00901250b4201040d101406d13a04410b151406848003403100402c000c202421104c17000c09c0400c410388031a00c800c600e4603814501c0600c15140c000c404c5031004e00044461618081c4c201c8160602c81c0103900712035521a2012035810140140407000348040c512031a00c4060360302c0001d0b000d904a43c010f90b0041e40000c000d812160b00c04d0110340040039050b0054503402d04e0303246e499000074842c0141250f1001c40540303c641d40a401c0360400700c2802e20110071120309041010200f032904035412055800340800a07602c0b07400d04000c7c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 592478543 1250 592477293 592477331
    0xa0b0a110d020706020c03033c07030807030e0a0b180f0a1202060703050f0406110705060403050d0e0304083309031b01020903120306061216090e070c06 67
    0x400c80380d0948a50480709440a502d4281074071801016001d04501d0700130515000c004c4460041e0052000c0da280b01f5103000744a596008147c90303148141040340d01c18294a0241c002c1c01030240310b59200909031804c0300009094401101e1105165807100090364002881500c2c0181c0c4000c00c0301a0407003c24044000034030303108201e04144014010080c4180070310501c2118014154031a4007240d003540c0311b07004118102c1e01c0449403404841c45450101d00012015044071045000f41889a800c09055440345810300030f00f0f0320210045140003c50001e50740d80c9009030070712003203040c01444c201898128400d840742d216402112407002500c0740e5901c001160b404465035401801c02c090354a00e0310084a5a85c0c0e40403000f400118074030000d200d04440014000c440c5000c1000d0050140366020710354400f5240c00140c10319901803c2800120044014030080390b104038010aa40107c50181903030240c544003207900b07c1542c4d554074034100010a90005c20441b5001c0d8041c81c00110002241e4044081c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 592479793 1250 592478543 592478567
    0xe090a060b12010303030e06010807050f01030e1f0e01020702060d0f0905060a0504060f050108031204031b03030213050303040501230909180c031c05030604110a05190c020a0b0a 78
    0x41c801c0864803031444030503000040c0c141c038803a88040101440d80000280d40350824855001d40f81e121481c01d00060402d83c200119046040c1004642d480c5040c0707031103080000482d141ea8075429542002e4450150360700070a00c1c2c482d1100000c601c0c0071900c3d00483d50f1031190f1405085450f0300d81961903100d64080e400b03450100e13084025a0018102055898080d10054038266015821f0018a4604400ca8407550f41250210070085180410628000c0607010000300306605000d40310100d0300d0603201c040c8aa01c00300d0300c031b5079006984200355280e0341001c40e0039410840c040d900a20041c032150360450848044003401c41c407d8001284040f0090781c03188904910303190070010381d10038400c11810f12407941d000200032030292070959200c0e0f414541d4604410030782522000300800c20120301e901035001540c10031406080402e00481864500e152940516101d500080300081c1004241556550350001c2d04064540040945000c0e000103907400c59034090840701800001c1c10151003801054903c400c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 592481043 1250 592479793 592479809
    0xc05040e0606040e0c0a091413090c0306061d0c0c03090d060e07060908010507031415041508160b030103020f04020a21020a0f0507050d0809120315040b010f0e090a06 73
    0x86180107a440e005d15048000d1503c046048404045025001e140c0142c04050b0040d00c04060020088010300c040d044400b016030b0280300026010021a0450007040043c10303607041c2280c04581624502400454010610203203460107001c3d82c3c885c800f0210071500c524004864100c02d0f00c240b410458001c0543d640035071014811100300290441c0c000000b4400c4840840080240c0e5803810003d40584075202d0004000d184440002000c4003090107040300260009000001c480c80503103a018812000c580040d9110b40c0084804030984081140d008007a0507032000c0c090655145502040c560200340b421280700d42c1c2c012800540700d40c861140c201c2101d1180c3d204070302100000440320000c2d40514840c80000e01031084102510340981304444003990300100402c0f07100d60b20001102d16000107080490907020751a04ca00e0380c0e10b1107502850280104501715403003100001c3c108021541001980c5051010f081030f406955a08800301c00c4500d9400da580300810354550825000404454024001d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 592482293 1250 592481043 592481069
    0x10e150a181e0b0a140c010b06031503010b1903030f110a0c030501230105040f0605030f1c0f050a0e010e12030706140c0d020c030f12190c05040e060604 67
    0x10500600618039a003034401e258000020794a50488114034404c5020240200d1035050301810102d01c1d034401066032a00c4e0380000500c4000940001d0300729441541d01d064851800311440c40149001e10a00c1c0040c0c4040320000314026070703920404050810b03417001405105002203800c003520300841340344c1c102c1c03421007090329681803562030904201642400196115860480802110402c2030000140003407404100b060b43c1c3c3c03902c0c4c10040a41011803402c2c001503126080080c450700c041206100741401d001c0a00b0082242481410300d0390080440c0780100032005103130448080e0000b084850100080c42c00c4284850030800584100d011b2141058211144520009040d14040041d2007014070411007840031048208151580007003d407031003c8102c0c0c042011150f02e0380035a000340011208541920305050402403072240c0783d040307080008580c5000108110048491a0f0207002000120900b0056aa00d8500040480c0594020b41c10b1510740c000100380300c2e40c1d900080c3c0b4010080242201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 592483543 1250 592482293 592482299
    0x7081312050c010e0609100f0603061811010206010e0601050a17070203070515070519020c1305190e03030a150b0c0337030f0212090601060e010e150a18 67
    0xa0280d4840030211801c3c1d46052016000584042040d60081c003150006101030414040751000400c0821601c002c0c3c3d40d543e040001c000707601c0d07020310002c00a40d8540c24016400a007800e1941c1c642d5010241d0464120900500c4025039410000703402c12000c0c0382c0306454041c0d400050300c15402c0c05034048600b000c0d010401002990001c0104031551159007525230000f800c2e554406040c1d002d45540c00070500a0010319503030300302c82406411580803803048030b481406200209200f01e4104c40384200044d191420410b808040300c1006010824a80040010341e02304461140c0706d000203009601410b440e10b5290500300102c144000c09045500c1c16942c4d43d1010300c448a5603603221700143d007110780100301030005401070015003004010007203443c0550900d60350700c210018030f0502410305030741381e0a01031801400c11111032684200745070802061b1315418030001510317290f150305100c0d042009440c9a0019626171f02401ca100ca9101e90707113507448284480040d29120a030210000d40800041000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 592484793 1250 592483543 592483547
    0x813020d0602090a080a020303040519090504050714030a0c05100c0204020f070c050121110714060106122901020a0b07031a04091a06060d0c020a1401090b07081312 72
    0x42a00f000c0454112244541c0c0c0d94429441d40703100034020350306400600c0200306038240801c010600586403038401c0050f5440d926044101c1d0b40650301035600e07134032184d0144400648414450340d6001c0807002400c90310142d17501c1d58201c2141d40a014043e1082051001c4650f02034581c686d0850340c001c00c1952034042c42c0b08001041e40000805854038510504001243d5004012955051900c0b12003c0c1a81100c0c0300c3c00c001030007015400901c9400104841808a80403600e11801c00b20400c003d0302d15940341100040001c840c11401241c00341c60040f8a03c0d000c40d904c4040c0d400c0a43e1a111b000a961090005074200060702c0e0b0003509101075003003000780f100c3d8164000d8641e0781c00148040d8844050703100780710407180240300050180951004400d031200800c62314a61018000b45824508120b24810000313841010040c0405603211007005d400f0044440306004148042c0002040401d850b501c800035210301c05447c840038011807001068140e001070394602559508110340b20110b00c00d40e000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 592486043 1250 592484793 592484797
    0x10050904032307030809061b03070521130b101203030b031219020601060810050409020d0204061e1409071d0d08070201030b032a0121021e04150813020d0602 69
    0x3108645008400006104000c08d09150301080f000b821a2402c0da0ba40c55025a003d511000c4602500c40d1401c1090070142e00380d03252f5600c00c40075080c0e000c070030000740d00d0109076411024100241807110075070700380001e008501d80400c1098040c039000c209001c1d202d02003030034140120603441d2141e9000408203008074040c0304280005446508652040c2e070388800440d402101943d402e42020100d071400c02591606410200d900ca000411103200d40080c2d83c001001c407a100d602040ba010700035032406005060040407040100001d0308943c031559032039800281032013001480c032014071100180404482c007002c42c409040b0344000e010800218942c1c00c018615400900e0200e0000781070119859440c100483d5564801703030b4007102c3c925011010740026108a40030608a41001003002a010083ca560015100d07019032250703006a0700c2004035184202c007241d03c1a8903e461400308000c211031030000c1841c4625216514081c03001d07441d40051201c0700f4841d40006944040404691418130400d540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 592487293 1250 592486043 592486051
    0xc19050c0303100524040909030323010f050105191b05070305010609111219230114060307020304050d02040204090e1e0a021c06090212070e100509040323070308 71
    0x8043c14030f17005848030b403c0404080d01c5075034030b044004d12040110302815008450564428100441c240500c042e020307084002d002514020340c2d010f0001000f88000c0380f013051001d09003c0c07819a02e401101400322003c1b1a0500d5403800300510440d4071075064002d10203170303200a03a129081e1650183d4905082d03018003a0b9005011843d450030544581000c0c0910880e14421494545484599100c0c00350b08081c41160400000d52a1603c5035542d18403c030089420340340c80c0314500c5041c0395041030104c0324052500c06e440b9004160800902219980001c15a0b04035003085541d44c2c480311062000c07030701a008580c03107440c100d800c0c43e411000b55070f0041965216100c08441c00840b1100030201950369801800029402c00801e820203500301c6074840040c44114050303800481c0160b40b55011841c0807054008104490700400720601840107514034090b044214801d600301d00504050009036102c03400b034802000c3c00074244d41da282e4404421500307403905212500154031106e0718103000c2e0100f9400c135 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 592488543 1250 592487293 592487299
    0xa08061006020d03061415160f060501080102070302071a041203021c030b0d0f020a081e0d080f0601080402042d0f0509030a1b05030f0903010f050c19050c03031005 72
    0x410003040c28401c1c0700e0401120846c2d150800c5c2e102c100300600810800e8070b140500b1403074007080805000c003090b40e00700c07440900c903e05402058103142404000c403071040e0041c4000c0d9004000700004030754001850003e60325585d0a400641c501a5404121881036520051118041d0745113141495004251103545441000156102c89640d1404400315030310407c129601841c8142ca0001207042ca10a581c816440070b4244840f0750740300c040051070002c1c6502c4010010700d0140c0b02c000056402c0c0030300c0e50282c503507040060443c04d00e410241e0112200070300840c104150000081c01b9583c031a00152050301c090505130700d0340d40803100300341c440c0d509161103080300c42c1c1040300d8899803001d2807184520400b040806581000f5a5000413141001180307006c00104d00d400101c0404034600384000c00300005d44200c0c02d965402c01000f45401e4030580142c00c21074501c0c2004000d0318a10040c00c0710b40e4402103200002030300c003a400042e01d1901448030089400d11000c01008070300c0380da028140041e50411 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 592489793 1250 592488543 592488553
    0x7090311030609120a02071806050a1208030109050a0f09142a040c17090318031b06090409202407110616110f01030908030c090a0806100602 62
    0x102030654500050f01d6880e441ea2040301003a0300900040080c002103030311841036801c0070ba038450002c01403c1e10314400419080c1e80d038408103c02d252124200c00280715056000b0944002a1a1507a042c081446041c1312641c07228000380c070401d42a400400c1e001c0700703c441002029075505007040325809860b16042755200e50100700510000e01c01d0b0000c035810280c40f030074610101c1da0f810700001c1c0c04071103005014020f0b192155054203815940191142d40e801c8020b54482494080f26806410440900c0c0c2c080e4101022403003201d00c00008410b5001030540300030f40d03940f10040c041001027085a6014103040e000031810b03e0f8184a2b4000c00201110403110403400c1e110419114500d01d1040011302c103150401c00191002030b01c0c285ca5003c261f030004090310300f05061268586001d405581085400e02822401c82400e403030a40c1014009040038601040380c1c2c8010b5581da0414440909007028105000ca00d50310265078030000c1c0f10180c1000010f940717690400605120800d102c80c01342c100503003d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 592491043 1250 592489793 592489823
    0xa0806130e06071d06040504090f02031507020d0e0907390512270a03060509160b090f0607050708070602030307030b010327031101050c07020a0b040b032d070903 71
    0x301100d82c0c154400020202d1b40382520b4041000000c002c0c024089540a0b00d07018000050307074052103582c2d015800745002030040e1424100003401d080410901605001c8010342d00991034450130300050b4041c0050a00210000c43c0704400f017031040c540c016070f9000380c0c19039049030038a00c0b80030b05142860313200d4411580703003a8095401503451300883d136903040414000e90800d6840400c2028201e001c50010701840105c0d612600c80400340da4080342c06000c0c580c8101790340c02030441c0c485d45103001003100024031807c20340620700241100e8101d00903548100404502c1800f070100c28000f010040048004071002d65540316030113504c0340c00850300040401d1502d08005075550082c01041080d03924100046013440d05540211020865060306404020510603d000202400d210701405025480216911140c540c810403d10050303036081216444c000b800304001444041007035a8102080480c5140b031090003404c20440211030345004002c100e032410138001d0aa410640d07806c1581e000d42005000018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 592492293 1250 592491043 592491077
    0x1150c17070209011a091011100902090f010f06050f12011d011401020309122113060201140c0702030a120507110409020d0b0a0e03030a060806100602030a0806130e0607 74
    0x2070045c81d1450301a001c10440c0c00d1840c0890f841c010790510303414007001803070106c01c07010324203903c0c0c855a0044599403103101080d40340401c030700b81d03120407030b45900742c0c42d5030603c02d90038001c06c924030a840a01202003140d24a104402090340c4203461100c89141c3c0d00d40c3d4500c81500f05c014250880c0c003c8255007000400c881d01a100642e0700d070710040c0c00840ca041110300a00001e400d403040d40b02d205009030120070203040064080b13030034849011602c0035243c481d074580014560019a01803820340e890f0000544e9100941c1411650100602c1c10150f00c9803a240042400c00ca00340c40014411744104100075809038200b0301074180c1d80d0080000203048241c000502084400c085c00295010602c40c50f660b0009111141c1c06a00032210000070072004c41d80030100b0302c1c0d07810076242e1450f040d8482034144101d500400c1210760041c0500e624462052030414043d4032807103a8040a0200030a050000340692290303100c03008000c2c0002d10410014181412107a01c51106503800e400080f205145812110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 592493543 1250 592492293 592492319
    0x503120a050306060405060a0c1b050a15170f07090501030902010e0906040b0315190b0a09050a02090d050d0206070f090905090a050a080a02071203050301150c1707020901 75
    0x881412900345044003145068400d900300030581980004200004600d83d25084050130b03c2160382c0e22101c0b014103062030000c174181c145503041c51900c1d044410410003551060a01d000b03e9a8145140000740e0f500041201c00c0c00c007a801c00180448084c0030f00084140c81d1b904944280c400355510910706031100d0044055910400e0068002645040c2402c0d161500c82c0350903410440017003000407201c480030080f81c14542c888620a6411907440708104c80d103d00c54240c00380d00320300e511041114180e081c0000d811107445009904486a64071b0020314100b8040e81100e2900c4801099080b550240d85055952440c003a546c640041c000c01e00440c8040f03000d0b441281d10000a51103c070085800c09200c840102001452911603118003039214021940a200d40d5815a0240e02c080707a50f500c403008003902d0000140d002412449082c1140b0020a90090540e81514004a1440411020494203c0300c4001052001d41031000d450310041400006a006100031071007500c05505981e69865000109 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 592494793 1250 592493543 592493563
    0x602061b19050c100e030d06050d0c0b0f2502031e070504090c0b0f0909091513020d1a010f0e09190305040b04090501030b0603010b0f01110c060712090503 68
    0x1040040c440c10003070041024214043e030480c100d030920f400002441c4140c8100007012031494000280c034040c5ca0a40c0c4c000d03040075203015104080d60404c0b554a90412000714800d4000d00540814a0621b03c1021412508000c1d0801030f52041c4000c401460901d091003c40220310a10608072501080d002c1d550a48100345030400c05440c0041c50001807201600e9002011a40b1841d4448042a0181030402a00c21584000b6030346858100c00c0741841103020000c1c0003a40644c0c40b005900c0c00400c9850040e6501c1402014010360f029240c0c40441d191520b4003800819502c40d410340a500d06002d5000d50341201c03600603098a00c0c03035070307402e486055030410340306034046402094500c5040d1141102c120706046c843d2500074030b4141c0c0c4003c03c81c2150072a42041812a40701c900400c02d104480c06001e400840c100c00802c05070000d01d002800c0090324111443c148050130f0b45a280244c0107110280401034007500c881c0e668512490000900003a440d002008101820341c0403c0340c3c01d0000e60341d003907 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 592496043 1250 592494793 592494817
    0xd0e18060f030a15090219080604060b130c080603100903080105060f0f030a09050d0302090d02090a0609090f0209070f090b0c0a020d0501020c15100e0a0e06010602061b 74
    0x8180c03503880c203104100000403032054040c81030601c040002010200d40c2c5003c009003690000c0ca450680c4104a4020032210656500c0310070548103100c0007a000c40c0f040c0d0410b6000900150107551007000c45c51141482103100d00d00d5140036000814150409003551090b0000c07030a49600d000041c082000710b8911100160000d880d041c0140000e041c04801000390101c0d82180c035040030030751900440c1c0b69108903140d14400381c490300054200301c3d04010401000e610790405508200420010441d42120807074040c0c0b0911642012074803100c1550b00c820090280180300b0b00c68510380e428007003030802c0b640c181280200c1d5890006003819100b0039284200803903582c2c40c01c90182c0341240c080850740200d02c41c0700040c0900c1d021100180d0310760310302081c070390321950000d80c9500140b451a030809417280b180b00d07882c501210411508849601005066418408240d20b454941010100017003104241d080e845100340720000c0307451900000c0c258410300c0c2d620181020b042c0d00700411b0303085024031041030355 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 592497293 1250 592496043 592496089
    0xa090c090615080405030705010e100507022e060e13020f04061505131e06020d02060c0f0d0f0f1506110c010f0e1009050f0a15140c060103050d0e 64
    0xe0502c100c4001350040d02a07000c032410040f40743c44080c2102c4031104101500d17404143c0302c1e40c2c40003982c021294000c0722400900300200e18001c19002c2285100b00550039460340f40103210000031241c0c03001c0013810000c01c81900521f40358180000805041ca007d9200d80340c0d4812002c898502402a075081d2240304080790076980c4051829104d5400c26621460340b0181c0e90b0010441e030b84894410079641c5071513414075101c1f0380340c044d019080602180d80001150884401c04c00804080011141c40b075081e100055500d0740150340260003040c0601041c0c40d11401c1c0f40031515452003940024036005002d403c445106555440160307108002110340c600c680d0007050000c0d180358007604545081c6591814000c0100c0e80c1c2000140524034072094600c0819000c15003030107a800c1c440f101d221788400548040c0410350422600c0c102030400640c4690422030145c000b202001488002d855034409040203e0718030396107a11f031280c0c4505d004240d0b6800a014003091740d00c1850425080404070301700c450801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 592498543 1250 592497293 592497329
    0x40b0d050a08070512031f060c0201090b03190e01140f0f0c03040206091309030e030a0b220f14060c030402060304060b0118030606030b0f0f0705091302030a090c0906 73
    0x906690001d20090f14117015050000c4002e9407040000c510940c69000c40c04030888481c550303030425482c41e8010000f040001c00700c000040c3d802102d05005d403618100c41d0390300e99840ca254032118a14031f40d00c40d2051410310745400308001054004141035a0b24861030b0581c1e641d03252141a00b1441150084503145806000c00d50000918000311742190020b00014504410f000202e00004800000d00c84919960f9040030103040d48080c282110712030480141c81c20342e611342c503003001091000d864003420607400780142008404958100c04003a0307011450041a10362400d00902000b124102c07031415000b044001a85403070000202da109540c020105419a102c1d074503000c0040a031804110305100c2030348450a16003075802c15800055200d401d0201d5000e0a5141a20f00400040c0000c0c403194904c005110300c3d6200c21028a9102090740303090340d11345840c50000350101c0c0e5514440c683c1d0500c0082070054480c9280c03c001c1e03016018514612ba1507503540d10000c2120f0b40c61007011002032000b01c0e2705e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 592499793 1250 592498543 592498553
    0x1e0328060c2d0c0605040305031e011d090705030708100b030712140c04061401020c03010504020108070c15060e070305100602030409020f0d18030f02010506010915111b040b0d050a 79
    0x108564242e1440c02c6425004584e0300d807011200b003942c0c150301084002c4100702c0d06600765070000041c1d0103030704000640b5501d0075401c820000d207010701115810115030000746200000300182c030f00800c4001d00700c2d10310540d10305595440e24044140a68050b0405595034408e05000072080c007180c03651600e6101c24412901c50791078181d10001d038088140900305814903903560f40c0c0030b5103001d4145034541c1994601da510019107040500441a8081d90400301044090b03038001c04000da2100c8113040150781c201d4145050744002c2c14100b01c00c006c15103880c034041901d4256200c0c15204440f10b842c100180e0b1542c0358241201d1222344541c500503441040140480c900d04e40103884640d41d465102414100340d01c1d40c0000340d549031400c4500c02c1d80031074110402c1c10b41c086541404010b85000801040c105000001d20b4030340140640054003011061142c9032510401901190110003019070300e05900e200060000440c8401c6000d01c55400c01c00c2d680780340c0c5025050755007259480350082c102d1030720681d54 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 592501043 1250 592499793 592499867
    0x60216062c06070c03031508011b08060d060506030f0a060207020a060c150f0b1c020301060e090a061802031005060f040e1518150601090b04051e0328060c 68
    0x7181055121b021f080d04402c0f4400d001e5000d407800c0000032401440640381c500303c0300742010400d42004030100034440c06840d0240c0c00720741950008000300fa0703035036000c0c0428039000680070940320a11460800d441406442e50243c00941d02c2180c1a1000380c0c0c0c0d40702c04440d50b90320003030041d11300b4401a010503000c0c1483d602c80c0b0118100008040350000e00b68000551160b15101e60b18403202e403581c03401c41185001c0c85804058110300d901c07203140b401d01304000e99582601c040b00818055640440d015a0103d014116400070b038000c084940300c10040b4203c402038001611310354080c8410302c000203030714074181c050448111506401450b12100d01320226a400c07501504a00b5200001c5c40c080301c2d0441c2c28050300d11440440084502642028400107040d44d5003a0f001091070142448280080e54a801c03e6080100d030150307c40142910260010303007880070703810090400802500c0004203520780000c111001c1c2e07000702c60030000c4401d0303054160fa54032150004440101c030b40031440b045001001030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 592502293 1250 592501043 592501067
    0x60908030306040b030f0a06021207091215090f0602280c0f1401230105030106060918060b031003020f120715050403080a08240f040207060216062c0607 67
    0x3211204d45246d40414104482c01900355075603a0009614411261480e17111600500c3c1440d08161052600304003000d4141d2100d00141800742d0034190741c01c20741031904208915600140c410a06501a292a00080d4001400820f0100503d22140103d041e800c0290250030003640b00c01a1003202543d50060f03a041d903000440e402c2001e1186003d44040034030034440c09003000c40c0040b045012000407030421020507882148680c0c1003a40521035a5801140d0310219058580c8101608808020395006440c040d0052408410040104032884ea03082c2c1d03480003100e000b641c408544100071024883c0e074103580d402c0d034112a40202810480401c00b408402914030381450885c0c182620307981c0d801ca056011071070002c0018681000d1082c040d034102c140170045e500c7c49409450550400d0301107600108142c07005445141e01007880010700807603404a4240404445004e0410000e600d0b0400007000ea041484820800c804809503801d100c100c50041030a250070020601e540d10340d501159040c2c2612 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 592503543 1250 592502293 592502299
    0x20a0c0b070c0e0408030915011a0a0519120f050103020a030b0601050f070b1b0309060a0c0507020d0506041106040e040816020915130b130f1b08060307060908030306040b 75
    0x510000341031001d01c3c0085015a100d0101c1d59628188000460b140c52511005407a600324040c004101001c1d01071721110141003141d40340b64456030120020348090103940c1c0b242800c5003189a0401141c2d50002194047d940c1c200000c2040e00d00000002c42150303800d0000039004084ea810500118082ca21140d50043c01498801d250800b40049003a844c0c0100104076484000f100600c8089030614201039440040c482100f41149000c1d00010f560b0900a00400c2d155030b42c424590032018864000c88000903000703403903c50303140d090307140c01682e50170100c42c00c0e076194640019107030051600c08201c504a8840507000303102503d6688548000703a001c610140c1010701c91030000c40043e15420b08440c89420740307c0b8088800864002807040f400c502103142010645414801c0c003040c2d85401c1d0101c100609020001180c842000381a0010248143d001480c0e243d9524030101050b400a80c10344150b100303130103483c0e815540d42c10071b0320810900e008506da150814800925281080d501c1014085401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 592504793 1250 592503543 592503563
    0x5071403040b04030b01030b010e090c01030e07050a1d070e030a121b030e092a030c0c19060e031c0b0d0804080d2a08030411040c0f030b01020a0c0b07 66
    0xb0780c045035610b90143d48116900c880000040060001b4502360740d004141c20303c0c500d082460080306581d140c4951210060606540d05903018060404000c641c0152402811540180341c43d060400c0c420000d01d50b0a01480c80d01000052541e881071314817044400025004099441c11903032042070b0b100070000c90008028000c100740e0010944a0702d070810704e40c000e4980305140b401d03203401d00501400c010421860f01e240c030f60000c400f02600ea482e200b49195001c90164880e01d0700d528002440c4142e20030b1460511640e804c130810342c0514548280c00b64801c00c410020f8bc108813022945074040c2d008010201540545003403001103144d0401c0340c00d00350003065407001c552140d072401b0450304140c0000c129a4802c01801d0080e030707003014006090b80f845001c908080c040042204400d0f444100700106a004084082820403507079011411404500a009004524524600903d880d0541010100180c2005251241c03940080348041c105908031120000d900e080840303803c419441b40108803104c42d02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 592506043 1250 592504793 592504799
    0x60405180a090807290103080a0318050f0609060f0903030604020901051b010c090e360a0f03081f0b09010e0901260304080c040911030a300507140304 66
    0xc25002407013000e200d200003d04040c428201c0c100200340c40d8868585100901005202158200c2c00340e2300d400c030b05841e0100340206e900e0b203540e40b0264203036001807041c03054555808941d140450564414404603048030b255a41d20140800d298005883e26049038200708007203095030900790004d010300b02d0b06044c00c0c0d151690050b42070360303501c50b04112010907940d0703081c124400302c1d48000c40800401c29030040c40514100899141d06a46000c04000c4100d0f00305015000c000c0344203100290204902d500b0b4481c4045c0c5030415010084e030031031040300010301c2000020030b10705881c034141c48040b40003268025241c5c1440740e0355000c9e41c410803106d81886141541715040360364100c107032400380a010b0b13400c0b6940f61074003200c6c0705490707001441102d5a401c1030209200b402d00c00a828544000100c80c0840c0f221843e05006803000100c0030402e0b01030107000f2643c0d0600880c050342c3c010074092941904000311030850644000703051417541e01e002034001c029600200c1c0481195619602c000c10680b071601d99 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 592507293 1250 592506043 592506053
    0xc15070b100305030d0605030c040e1009020406083304030206040f0501020f1308151b07062c07061b0615080a0317070c0213020309010906020a120b060405180a09 71
    0x5c0c030344032002076031103202c280841c2c1801c4c00600304c40b04055500307000c0d0042401035507803240c641412103000c040d541c04079041955995003254009060003000c0e0340c1508102010b00714002203c80c5102405105100c07284901c1c110380d0142440780707425901411041c0c40e00d9030f4888070360f109141e040e00d4541d000e21030201c0c1c5100b401c00400381d0140c46142007013800c0c41e080c070031410070003562490340c128138406d010030509031201d40000107140007182d1002d6079240f00d880d04c0001043e200e400c0c2000b0800396010001c03100070b410042003410b403d8000311a91140e13601000c507064034462940a003402045400301000070880c1c3c20030b81981481029034255aa00c54070564130f0081020740030340c00188603800026a00000a5119800004603e811110081c0742c0d00801d5101c128003904d03400541c2d0010000340e140e4030a6000340080b03588150255a103004503040100052101da600030b42c207a00d0140e6203e603c0c982502104c08807900541203050003407030902e22103945c1400401007564039864080e4180090 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 592508543 1250 592507293 592507297
    0xc050a020603150f03072114011107020103051602030d020c0106084303030e0105070210031505010809060a020703170702010c030e010c1e050f130302030c15070b10030503 75
    0x3001d4203d4100d207070301c400001c024840e6005841c00d406500f0000c410301c000d01c41070071340c01d0300c120509440e43d0a64040740781510b81c4100703000c41c8103019440c0841211201003244006c119443c000d903002d1029032124030b00304a949036619034800145c2c2c0100001280c6901c1a00079059440715040001a9160b8404006040c0080c0e0304c20395011401040c17a1061221404407550400040011010410a60039409103580541d6010240502c00994a1007201d40e1044044850750340e4007901d40e0707180d2a14448050083c120302641c4854025002402040d41d500c2828514030558014008200c1506c40cbe51048000303602410040d001c0080300d08130a5586600710103010300800407039000051003441404024104c030410014204985d062010305001140c1c451030303484000b8445c1c0c59081c1c410b8200f00e4207607602d1060280291030782ea0081007001381c100742c803844081243c0c001d50690351034202580030040480c40c41c1c604800401c0d0140f0400020812405001b54085550195004655120f4179154030f1070b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 592509793 1250 592508543 592508551
    0xa090306180b0f04060518120904110a080403020f010b01121d1209030d11031c0f0f0608122104030327020a0b092805100801061b020906010c050a020603 67
    0x81d900c02c1041c0000c0181031b12900e0b510050b141813030b202801e040c000568450310003000820030880003280300100c80c1c0c0c0d20f912113000103019442c1140d40d484241c0014040b481c0c100c6d01500135008d90020071020b11011b002d030740b28201050350740c100b80e191414801c0c0000c200141d103110325518001045c643d49170301000f000c0030002c810f011154840415000301854581002c00402c100003401c44c1c68802128000255000d0103071507040300c0488400140c0b52401441c3e01c40110701c916051001c03c00c220314250b8040000e581070300003a1030142d41c003c0e41d1500584201407016044040c12801050070701c81480c019900f29200703285c0451004000c0400e070b07045018101021900002800c845011841c00400700030040ca100c01500e0300340120040080c0030001c5400e1510058622101021703035081040e03d03c10081d2800504031008210007030002072030200709010b88004901062034402584150701c0c10b041c0d4a40c0d00a01405165450100440d11440d415070b0450341c0d0b2203011072040042c0d40f0500910f2007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 592511043 1250 592509793 592509811
    0xf0b09040309170a0206090103020901030f150f150504050d0c0915082406011b1205030f09060c0403060926250c09050402030307060f0b10050a090306180b 68
    0x1c4541401005101020300c6810b28120354400340d03199006894a100b647d00c114030908006850f04000c0740164064003082c4907076110f1502d0908083c0041a002804105070780382d0910900301c268807030a8a4601840c40f14000010507010300c0204003034070b040c901050300c1c03900ca0f03035210587c2580c90f8100016107082030a11004038803000e100307110301074081002091000f415001010905011180c0c00003080026014a040247c5032140f6403045040030740450496078068803050440c4281e00b0010005c1d0410740300c40c0908110345c00400c8407100001149400b4600c4100d80728a010301d5996400000c040048080701c01c9014103200d12203459100203440c00f007042a5290554035103450f80c0701c0300380924000c003407400c59807030455007000300302c551042c7d4042d1002a00b00040303d03203844c00080d1460155490091619083c910b05040c059034031303002250f1403203003501d61540c0c032100003170240c405001b2041c00b00c00103401c1307100400c04501e10707030072110007d03140b190207800348406500c070311424003401c441000d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 592512293 1250 592511043 592511057
    0x180806070f0309020a0b0c0a0f14060601090e0c1b030d06171203060613051003020c01060b07030f1202091002010b0a0909020a141504150f030204060207090f0b090403 73
    0x10403690000c00c09956011030b03240030080107240740e0018401031940c0c01852482c85c008135a1a080400405c940d40005400c16104455404c2520700200c90141c890100e003050301031407000c101103500801d0f4150a6484980004800e90307203800c0c01c6a000d0f003000d21b40b4083d400040e040e08803002e2041c801000030381d502c02c90100d0020706005d04841014a00c1201207100d40c860b02292a504a54500392900158111141070f61a4031907507449500800c141c205980c46030400c91180b0105d50981d00030b081d9041c2d000000d0060079a40d6070f0484243c040c405010740401d0855a00144540c82161048807840c4c0b111801400c03c403030781c0042070824508202038000340c1e64801501c2882e03d00351014038010513001d0ba0600030040f942d030218500115900c9040c050a17200000814035940e950300410b010603031940950340f510f65500d04c0c1600b4000d51001e0a000c5500c81d1480040c03035100b80201d46c03d80b242d6800810701c00f0301d00801d05004001043c520100107640d0301040200d41c1c6c54a0301c540c006e40c02070352106 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 592513543 1250 592512293 592512301
    0xf0605030105010b1918290c030a0c0f06020301060c0605011a121e310c06053402040f09110d0302070504020708031602031206011d03010c0f0e090603150403180806 72
    0x80c2440c82403101b07d1151050038095900b0040c0000201ca0b0050f070245810703c1c00709801d1030b004c001170401e038000800c9a4004030020418642c80460112003a0040000303100c2c0780d0b03071152413080d4540c12007161315205404000c040d500c0c1f401400d100b5003019041c03003000c0002003052680c011070502918082029483d403c124082c6000300c4032000100c4040c0400743e24260b83d103a5464018002d81d1145006015000c40c40c03c01c6242810b0240700394580305040040580013020500404000c0483d0880c415840c0c001c1144004009210308038101e684480d842404070320136003c00c0110708085100302e00b103116070400400c041d100ca0000c0c02d10381d44100611034403400c0040c0034800504900540e14210751042c4a0750800c40d070008545900002d007801c02038200401e440240710344e80200d07440140c140d801c1c40010404c2903801001050004500d6850090307280f0700f00b040040296095422503072680c040130b01e002d01c0c5c0a4051901da001482030030042e09000114028108400386c0c1d5001c14500d811201c100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 592514793 1250 592513543 592513589
    0x8030a021e06010303200f010b01031107020d0b0604060b0f070606170a08031027060611280b04030804050705091e06220f0605030105010b1918 63
    0x100202081448552a00d94120100c982e9501c014032010381003000b00130fa442c0d081c510101c02c86820024413010f81e900c4601301c1a00070b001c0d01404e24540d0000e85841d007550764440380e10060b960030950003005401c0801c02512401242030f005042907a000307503200f10000c6c4284454005005010b010900305480d003a081c14a20111156544882c0d116495a000b5007a48000441c04074041740e84024119180d4070390b900b0041545690750801080560b446200d40030301e400780240c1c600381c002c10140a0040704e40fa080704a81407200703a040e1403a41d40c44103a0b5410341d03845480b5403901026180f110000c8016a42e150307103402e0031007901c00350040703114101407009021061000502400e025500001c031400d0540843d4640740907800414445500d0001049a030740d05c084120780031a075465a103002e92055682540c00900812070200340603460b00000203158103040c02051b04035040040c0c66400e141c07160040c030f013040307000054010800000c0c0041484110a4010304006080d600040f0001c4003100001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 592516043 1250 592514793 592514803
    0x140607120212161a060319030c0c080a12020c0f04110f130303230a0806011205100e060d082505030d0e010b090105031b0103142a070f03050c030904050108030a02 71
    0x60240b400d10400103240c40c000742100c0301c4501c0380700c00f041f4105503081c2107a080c0800040100441200c1d2000114027500256104085016042c4661300010300d00e010380e501c13070400d121290041020b40c2410031918007503218a100a0200c69241d10303000c0701c400900c1e5180d0120046000000d0034000610038503900850100d000c04003c142c8448800310440e2503403150148003006020401080c0002e202d59108003092007904040000074880c07401c100b0340d451200326850103551074501441c4002002c1c0d140c034161440105030041305261420301410051694020001c0302c640d1800d106403054800a07200300700902803459a000d000504506140d1003609690107008014401c4510740014071166601040190350300340e503191030145450818006a028044014400c003400169070b0400c546044000c03000b1541032a403240c210740360b242101150007031303026820015018004074101d40001900800003041c8101820b4110303403d00da00d80b8005400c0d66000d130851741c00d5410100d100c02190b501002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 592517293 1250 592516043 592516073
    0x1c0308010803040308030402060912151b0910081f030302010911062109010f0203090708061e0c03040809040515190e0a0c17090c010914060712021216 66
    0x2e94905403a44d242c09080c2e004c058000780c030a0400103004a070790b50315808025652030b050320503105130b01517590f80030b200400c0c2221081c81d421400c0c1d816408200e03407401114034a810080c0000c0c1308510101c1c04640c0014002e107881141d58800914110580c2e070521104c004501c40e03800030454402c2071401928004240d04a24064103003409040200c0c0b41000e002c04881d03115200560041d03640801c3d182c050800b526000b04524400418040040030204581c020381302d40800320741c00c40c0c8401090400103030b6015100890302d40140f02103441211302030002e40c1c0140c05991b486081141d600c0008045440a45078540c85103414462043d1a05040013180002c010500c1d08500d440d10348084800c4003400100b51810a55640e8415116580241e050107213440c08200c11240528090140c0b6648520790007103503002c1880341c0400990400982200d5001e0580603009070b0400c02e0a55950500c0b110b040c624005502030503442c61441c136148005030540402044034006003040b1824401d048506000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 592518543 1250 592517293 592517309
    0x19020411070b1006092105070b0c0c090c0c030706090309240f03021e1c020406050414041b050306150a0306030c050901050906132007050606040911041a1c030801 71
    0x81806c1000e07540d05561400041000200d4124001c0c0604c2c0c09800c0481c990084645804007040c23103004070000050030b0300c00d0031041c1e80c04609521a44240d0060340524484e40400303910800c03004002a60030303045010352910a00741325103829114040b0702084101c01c1d000c0f01c040e2000d400490400c13a031040200c41006950b0604600e07040c466040c54401280402c28950440c4000598030050303c182c11000c5011006440c00b1503c460300e408000308030b507116100e000402c20305014221614602486030121010803104468905500c0100a89860308000c0c003c1e40d0000c451300d05000103406040040c1000c0903d81c0d0006030311ba09520341010900c00a8028070b00130b10181c0011300c01602c464030203542145045510004607545801c5410243c80c40c2d184413011801d10300f078403808420000010b80905032145003074078070999801050004032008568060814045210940090705169124080c421000703182140040700480c08501c102d06000c1d00f02d0410744444a0003024994020078039805000e41c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 592519793 1250 592518543 592518557
    0x312021c2c030318030a080a020f0d090f140d050a05011b08040c05060f07050f0d1b05060406050a0e07030b011d0705040501031535010c0219020411070b1006 69
    0x3000483d40e00c2c05250240c0f0003c500c0c02a035603925650400c10310b101564040c148039a87c0301d00d5031009440c1c0c0101000b0813460702c2440b4202c075000e40112000c500750340c07002c1c0500c61560f140c10242d1070480c100c010113542008600030302c83c0102e072041c4102419280620004550100464047e080b28512100e0900402007480700b4000040e8403503003260103c490441c2c4098172409030340c4142d0518424680020458070484034001ca02c0c60002c100c03000050100c0d12010b03070121102240794000f020070306009150350080b800240c0001c1b01e0380d00403500418005000660038210b20039080ca00300c415003090f60381041201c01040010300340a4024034000000404600c2e40c01c102c0e4001d0601c1c002ca008440c14103894004c8030382550409407001008005e94007554603500c1142e4260141c00301c00d600704150160601d103010440180501501e00880341da03038010010f0b48845034507503015841c141d004a90003030311041e0182c030319036004014240080c050802110306040c0061055070040c00e591181c4180051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 592521043 1250 592519793 592519877
    0x20a0b12010515090d1109012102090c04080f010b12030c06040f020d060606030e01060510120509100c0203031e060109091a060a0509030705190312021c 67
    0x4180291811160151401d12003003410311a60300322805082803041d0005d141c00014400e106200c803d512200c2030603296150503076200d0324090031070340ca42500c4041040d12019108014100922410f5000170312420803800c183c0c86078075071420034161091092080c0e44410306012a85021001450401010300046240010b850011500c400340100003412000e00e030003032107056460300d1060b044203a50000e03003006050f0b01d8182c060001c1080c101810960361800002090900b04980c010b8001c00c041d45500ca49490b260440401900c0001c0c031072125030041e030003c010700002074000c5042280c8250091510303842c0c418158038408801c1181310301c1075102102401481c0e60415a12419118101404261803502e140004d1880070641c501503000003001a020000c00e61201c00361014881c1207090712038803035850301000300b0004181c2d408001e032415083c082002841c0001d07804034290146c010758500d81c040e2030500440480c0c101219000c00c0400c100000d4a0007800f16510f0710122803000603241200e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 592522293 1250 592521043 592521067
    0x801061d0f04030c050123060406180908093304120809010e0a17100209060f07020102070b1c0b0103093c050a1a070f03090602070f0c03020a0b 63
    0x10040c1c290404446440085010f06105960304040503400c0002400800421401000c0400c0712100840f503403038a0300041242c515090007610b080724401004110b4981c07420034001d00400070318000f11094a03040040d03203440e840e0b40400f51440940048984010070500301000c0015150600390410314000700808d11620344159148104590031003400758a0ba0301010041c3c901c1000b448520750f018446002c001186031081301508031014100095814080141e00040c0990241c0d64119030300020034054169444a584040c0180900503c11501503c0d983d008000881d0b000403501d140513802819807241200303041c000c102441e44207107400c000b00d41c2a610783c118140d142085840c218505504e01c07019a81c400492078048004400e0341482d99500b41c41c00680d0790341240b50482e0b071403480807000320cc4c1c40103600075648104915201c15000c162510030840c010040040100c410039402c1c0010303000b14098a080703060280c4600a1116014150700400800030703080c2e4800203010a0802103005015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 592523543 1250 592522293 592522349
    0x30606051f0c080901050f030a0e0d05040303090e09070b030108010c020c01050301030206030406110f0408060a0606090b0a030e07150c020f03210313020301020c060114062a0f030f04080106 83
    0xb40d00300304850740310049100120782d03520580c40d4241d800360300072040c004440351aa010391103410408007101c0b0703151812001540c19014a20004d804103410203070030008052025000c503804081d00007564030702500c840519000c0d4000780c1000f61a60b5445908040e203a80401c000d4640b92001d007011425907256a0004046100041c00149925121081003c1c001520001e0711111940c1e941055243e6860305101d82e80d65600701c0707583c0d903c02d080500c0012403902444100c825107104040042c5459140f00080e400707040d0a00c0011824820701800248079045000010440c1e04030383e0341c2d00c4846030140100a44180102001486500400b40c480460440d1080301760f4a405038400041d100d80d220581030b60310f844603140c0a50103500008a40c1c460303050201c5c5040c165000c103d07105091448010a01c0410700842c0090480c5405e07030300010300900c202142d40e14046501404440c0e122083c46005400c58215103400c0120100205041c410b402d000e006403409010180d00c511440c12441854800caa = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 592524793 1250 592523543 592523567
    0xd0501081b0910060c03030e2e020909070810030c3309170f010f0501035f0708070801090f06151d1e090d030e0a0c030606051f 56
    0x80300340031108404040c008d800240c800c03c041c03401c0c0c46c1c10101000d4060814500e1001c4101d58803050780301007920b04072501c2602c0060601501c1e00b04240c1c1c1c2d59105480f40003000d46181100d051800c13000001880302103411000e0403107164214030380c81103c0d021f514a90198555441c40945108803480e9041e0301410080c1241c880c0d110f24101d0b040054209820802c0035030941d010355080002c100c84402d520f401040c1200e01c100c210881a41c2c42040c800c603007103041041c0743c0040000c14030401381403201c6110760400c4180c44400214501904076881c54442c10281c0d12902608a41000c02041038103100c8500184110300092000034256590b00907061510b1f280249440d507602c40b10000c0550921542015041907481c1c080c05080743c202c0340d5903401c01280c81c0b50307125101008800c1d481c41c034200554041d51810004042e1100d41203020b4000e86010b208013a00c038440c1f90754010204200b005418010743c01403c00040440c182414003c1d2040d681c240710882c800140208803815610150580003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 592526043 1250 592524793 592524797
    0x1403070c0206210f01080d0203120f060a171005060d020d060e0f070906030c061b200d150e0309150d020706060b0c0c330d0501081b091006 61
    0x34508843d045000e05001040c2541e07420518001001005100b40074014140d45001c4102d0308990304040c01240d5a01c030f80c07030300c41d80d800400701e02141800d06550881c5402c400d0092001e484292140300e040c1c0e01e500d01c0d000c02100c81c0d008990b256903000080c4900c40d00701005803403550b031110003074000c1030003591104801018999501510580c140741400444424a002d80c2901c01d8540c1c0c41003160090700090001355402030030b0300c100207001d42c0212514422100780c16242234200c85141c41e1601c0246044504819241c8108800d10749583c906d100ca0020900c04c1c0b40210007062507016020403070762115440e060329802084002281da03030b002c05010300b01c4807491f00c5666611a01c4141070190150440081105043c0b40003c91030030314001c090240b000b2030f0000c56081014803000c00ca180b8840040b0ba04a60840c1c10214038504400e14244038000240300c0841d184c20344007c41d02c02118400d030f21810b015085200d032581030a07200b0304e0301008900b04440310401c030b0800d0040c0d044044000d22505e41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 592527293 1250 592526043 592526047
    0x61f060e01080c040e1008011103130f020f060d020c070e090c06070501150303031a0a0f120201031d030c101103160c0605040b0703060b0f191209121403070c0206 71
    0x41d540f80304408480141010500300c41c2c0f0b605104926003a141c005000e51507443d401c100c00358140e43c82da6401e5038841e5940b0100c0450240064480382c010200c04141640c0010300c03114040c2040c0c680e48002d00a030420740600507502d210a09999041c80c21682184580507907c00a000800c440061404090003084030401d41e280501d00c1c100340100401c40f901504c0c050300304000030505405038418841129840400c40031142c6080c200620309807180228401c0300c40c0640c00303100031494403c12155862040c100001e1400c0901401b0303400561540e0000c2c80e5078400501000c0a0505010680600e04203e40a20001e202c4443c500c0040c00000c102ca9554140c042c8008004c034030a59a205040703402100402040c1060304001d4a1032004a644401180c01c0c01e00000716007820324126031040c100c00281c0c034102000030680c0183e03902c0b00e0040100b0405807000020a0703045504c100240d8a10605a040c01c080d460000500354441d204100003102106104005185800a80328041c1070f81c100e545603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 592528543 1250 592527293 592527301
    0x180504052403070e070e011713033c11120702190315060e0105190b03100503070906061b0f0b04080f1210170304060f090e0405061f060e0108 62
    0x7494034100703600000c550507003013045c02241a04406050310900c005c0e0b13a54a9001d2600d0741100440000340e50740500071054040080c0420301c108007807505201c40c900041c2c00540716200712100421031188403071f00e5840302c80c082079005400140121002e1518006807415070546c202d502d11500400b84040c2c0202c0b245c80c1c000700e010305140040340240d544030040415055100d140d9600420490190901e501c81d160000300c0c2500d055400f0b49003900384403000b243c00300d041040380c1d0b02030340000c0c019075052109420049090b66092206101400c0110000601c080c070b07000005001c80c03000c940d0142d1105180c0d6040000c140302d1580f2048058102060180985031443d04007400d119070750080b5a91680465041e40d2043c00e03040d043e008943d0a000c8503a82911203407000300c510100b50444026a0041008211450055402030362688041c1483da07507569440060761850042114201c0b81d1b600054200b000d100702c420350700c440e0404c0540d400f001007400e160010340f80c800582100d9062024400004d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 592529793 1250 592528543 592528549
    0x30114070f23031f0906050607060905010b03030c16060e0604090528020703090801051e0411031c030c022125050c01021203060f100c0c061805040524 66
    0x4942c071081c000750141d920300e028030320b46204c0c2002c0c04541d00c411000c0400000c3c0d060b1035016003416030700002c1405207840d03210784d114402842c803070304211015500c0303020701c450598091001e27106c2740050340040c041c01005410704421403030740346e041a0144980106442d040380c0360001950103079013880354006101d840d080d40c0402c115804100c6480c41c1c500500810440d4640e035005802114401d44440d442e16460700152401d80e031046440c00780d0703c0b0002c0c0a041c030301060107003c0b036046402043c0d0100800840004241004a074a941c00c00e900c0d1944040c1280c6c80d03151084040c544140d00c050805410100e060786c1502007a000c2d0281c5158010802c16408030f046004001c082c0010703115201440203501c0c1140d01c400307024038814050b0103880c22486151001000f04d82c0715002c020500182e02c0308038010001d02c1c0031000800c0c810850f1080d40c120001d8079071507410015000584850301280c1181030f1420700007242da007001d4012401c12051042c4541e03000660303603040c0075031804545650081804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 592531043 1250 592529793 592529837
    0x40608061c031233140f09161101020c07050a0605030910020d0624080c040b031617040f0c0602070339060807030b041e0905010216030e030114070f 65
    0x28160320000320306401054440090308404c100c660103107400c40110b10001c01c00281008480780c05421800900021b0b0007800103c2842000400341c1c104031503207a04208c601d40c2281c2141c4403030541940f201c4014062481c107010964010001442d01502e1807918900700d030b45070301e820303440d488155401240b0210501107a400807800341a0710707407107007600d080241e4000e00d20f14164070b03822000c00c03024070201d40c000075043c0840c1c00340c0d00c01c03a408524588030416010b85459070058007a08100c14010010521030401000034002c41c00b4480380201c0b44801d00b0003d180b100f0070350020040d540074400c02c000080318031900640541c02d5420321002d4480f400440320900880c5071a40151292140e00410180e4000c40d5081c040d424075a01001000380102c18401124072080c1d181203050f00c060b003103c021504980040f81214843e000150400311400c6243c0040e040c0100124007159250f05d407046c0c0e6040074840c0800a40c10701a4013400340c11b0000e070181c960610015100c08010f42507001440c40d40480305 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 592532293 1250 592531043 592531091
    0x504020f030a03120606020102040602120c030f03163005090c040c110c0406051806040b04060807050108240603090f1009060c0806010212090f06040608061c0312 71
    0x820b5400d280c80a140007000d01c079001d21400c13440c502d03104001c100244140700362000d032034540e001003580b1594040068090b030083c1e80440142d01c0200005148c031001e1001660041c000d0010341d0301d402600080142215204854007048404102001d28038414102910081d081c80e0034400a155124100300a080010361500c0f15000350500442c1003999078025204d07100764000d0700035038820305001c0c2c041106807a01840b07081d5108203c645030500700b01d0110712061300070900600000701e246540c030214095694a034000101a084030004002950704100c0240d07004c0c5000d40380c2d01410280d1801c083c003030711402c1e000d40e00130740c07001c80044c080540400480d0040c9007080215803100c01c03242c0024024140500040390f1440c1801000c043c040e0003803040740e001d80e0058000c1e10300342555240702000754002048285e40304400c0c3c82810000d850707480080001d40310070781c0c602082d45091070911441405030b0642d8201801c001600e40b01284d131050095240d89445031010681101701e02c130485041d94181 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 592533543 1250 592532293 592532299
    0x70905131811030f060601050a08071107092c0703080906120108061b0c06062209060510050913030309081b0a02030f12180d050304060e0a0b0c030d0504020f 69
    0xe034401401000030702d1055182c800c80484841000c510011911244240c41c0a80416800e028102c6000e006028981d80321500d840c1400c65013480500c501d10b002c01903400941003a648003020f010410694401e81c0a080640b00d40c0010000c140010660307a03170f00b40c030001d446041c002c124024542d0b523000840707150300748031104a2000d503110080503444038009d40d003480f10f000402d228030401082d000c05440c6045a04e0024113050f41e180001d00c000a020071800a0591070700c14503154608060748140c2c9030a60013401c0001c0c00303103080c0c40c405104440b280c0040e4403d8001e50100058045254180c01d203182d8185400700c5d0920480c07078001e00078040c40c52270034a4100a0810101c04a09c00140303481840d000b00d0898000351a00c0d07049036110072110080c1035075040b0400c1040000a030381c55100e250400041c050050318010364690b0350a540007a0040d40000740c4400c0c440c861841c103c04804003804441081c40d2030840c82c600120340e44d10442110384460b03501c42d00014159a14851454030b100e20103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 592534793 1250 592533543 592533581
    0xe061f14041d03040f170c2e050301050f010c050d0e15040311030c01110c060325020303010617010e1906031e03020601080f03040308130b0406030608100507090513 72
    0x2c0800075240d40180c020000e401000c0d450000d00022040b42021098401d034010746940d03214402488103d0030040803584a100e803e04c0c00718080416884001d83c2a0003030307911241c681d418582000302419101d0f110604101303401c41d13410081900403441e003161040701c4c05e041002000f14030216485400b5100070050504012a0000900000b10320851000c48102d080d00c1041d8800c1005445e805c5a601103002180e110011148850824200441e00702d02502494103005040c42284401403a11220207001030300040010031420360080401c4c140c50681d200035030455030410100500c511030007230460300d02c24220896210700940aa01030800703140c10070243c0004100442544110b80c0c62000d04400602c20b210001501d81320100314240310409550142d80352500d1034032031864a4100030314207503541d80000400542c44816078000c000419039920302241707151604060f207080407100b080109000382801d003042101a030000c001001d540044410560944a0206101c007c0c00440c4140d40804a1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 592536043 1250 592534793 592534841
    0x307081005100c030f080c0301061d060307030e0f01111204030e040908090a0b0313030507020316060c060515010906120603150501030203060912092b060e061f1404 72
    0x10103d030303082049010380c0f20740c01c080800144c21100c070324040b100e10440440c10300050040500c9070f40d03084900341e0030701500710903407c0000014406a000741c41940100b0b640c2c06014190701828085a80001000c40003000401030100c0500080d00c41c030fa09502030007144100080415008510340d1401520282c4200085190380c40c281e0161342c480112584070300c03290600004c5e00728008003160b2052144803c10300046a060740d040d1040d4200d1003040364180991480c581c00c0040f00d24080005101e1076941c03441c02c1c0000d003413a00c02c40b40b01419140c820b000e0900081ca42d660000c00c050304442c16032030304c1000090f850103000c0c01011190001000b04054081d80360b65604a9003105060324005c500f41c40c2c081e110340510b260f4403142842480c00d011401e000c814080d18041841d0303035072101c041000c600841908120061480c0c05100204c40250303484811605801d81081026400150002140c1c64401c0411800702401494407450b420044400040440b40d12250004080b4030301d208c00380c280d0815 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 592537293 1250 592536043 592536047
    0x3060423040311100603022407140604031d100e130609091b050901030f0203030d050c0a0f0e0307031506050405070f021510030b0901110307050901081803030708100510 74
    0x60f2802070401a4030038040c0802d88680148103a2084960040c260504000040310041c000c000b900351240c424807040c040d5402040c408000c580503142d01d24041c02161400340b03400b821881d0003180011580021246589440c1c59603030191455902c02d003804204076202c01d00042c407820310301c40001c2d501810700e01d001907048030b0354024900d0284200107041e540581105980750310040c5129560b4808030600042020802c8101c03000308150002e000d0b0b92809180ac1d10007003d4400c00e840202001343c00052079114540c0c0103080a10201c0245030610060284400107552025140009440480743c4500d901215800d6401103000341406030051085d49440d40c406014041542800d00140c015403014101000c910610140b1814a101401031049e044d034503071407100741004100e0754456507542803070f002010000003e14413440c0b00e40d480c580e490400304001419020081d24501e0100300c4002c062000c00310110949074446124540100c0c1940e0702c00d2061105180b5a202540240440e000e400341c1517 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 592538543 1250 592537293 592537307
    0x301090902220905190804050d0503040b0f07140c0114090604080106060806010807020724020c0405010b030a0b041122150203030a0e1603030e010306180504030e0d0305030604230403 80
    0x64050002e840c0e03080303e8417880e000c1040200c00b0090812804100074800e0b45007085210803800d000c0e20803203081c0380d21400d1042d0341d54080010b2034a49440070407860b0800901c81001c071f500719500d1b4054200c04007604006000790038000050310101c1030102d0802101e0310340e08280e50042004400070311810707658100103400c01b40c2c00d030f42841c00142402d0001c3c42c0c2c03900010784001191942183d484040048000c0c06004640c080107001c2140202590484995640c0c02040c0c00303401d40c0740e80e09581703007000000e00c400c485082d01e02d940910b0828a01d9810703100803a040c1c0711641c50900408002000540c1100041d05071a0803a5150300b49a07020700140a5000016500c1003840c0c0c0801c020310808410607981d0743c2e0340d039130b0b041b000c1d00856038060000078890030300c00040400606002c1201c980b1000a0b10246a00d81c2500000550b90781c10001859403208038407031015001c1d03464811003c155100180705200c0185083e02807511245541210f003401011410030003241114902c0c02d003030615009140c0c3c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 592539793 1250 592538543 592538561
    0x40c27180c0608060d06020d1a12060c03071e0905040b010327020a08100e190521131716030f060e0c0603090312090c012304030203010e1c14030109090222 68
    0x240c003401664000c181010f8200c80003420088008bc1500d0780d070042c0305416980010700c0c0c10100040e0300700d0405c0d00c0403002c61040880c065600d81941d4107007080305200c1240c440801042c100350070007248034241030103000200a1b030503520031156803104640c00468030031a50344d48802d00c58429080e03d00c000d035802e5030184c0e200052600c1035503424540c02c01c9500e51106070400c090146e0f044108031810401544c8601d0401c000d02450b41d0b800c3c507600c0d14850058452236802003512076042c1c410203482200a000006500c03800b440541c1c98641191102c90700b40d10500e00041100341d03a0340c510443c8500c1000390300c20840c8010040340c0e89180900d41070380c580e0030281003000346140940210b000f2100106a0056585069565003005000b1401050180a0f805003c461a6604000c0480075032401e001d030705a100c82c514028101c02a000c0300040529080c03840b482c04021040c00d51606017008070045a04488401c180070580483e140002041c08115215003075810f5446440703000306000c84d400035200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 592541043 1250 592539793 592539821
    0x9020909030a1b0803060d0606050a060c0212010204060e060d06091d060a0c020303130f050a0503120f15040b030c09101502030f070b040c27180c0608060d06020d 71
    0xa41e083d010042c070292542030300800511091000a502d4102154003104981c01000c011a100c2d658802041407400c1517000640010020b4400b0400e40c288881480d2034414400001c41c50649041c030001c8c079101d001c16045100c0c440002d08510892002e400000241c100400104902558202c4e405039004030314039000707064040c000029840140a10401200304201e40207107213580c0d22000c0c0d00c1c0b08071031200021900503201d02440d07004100b0820180c043c5520800c01035641c0c5a40a00001c60000000c005000b030940301000c004241d04072442e06c2c0c10104080d1004258400c98400103801d0104509015400420020802005542300ea000c9011140d147d51007540329461180c040707132640304021044008180801c403201c0000d00c8500150391060080301c4807800d41e43c48040c1d402001840c25441e1490280c0070107103001018843c400c0907040340c6c0c0d411032801680440d644401c04080248904818812440001401c40e1113204118020070340c004811566501c2451107040200700580c00480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 592542293 1250 592541043 592541057
    0x2030901030e19060209060c0a060b03010b0a080a0f080f0304030306050a0b161202070314060702060f062d0a060914060c031801030f0c030b13020a1407020409020909030a 75
    0x8800480c3d02003103001c2405584103410100d03201d402c081d6208030b02154114070b080140b04040b1005000d6000824800c580102d0b1082e20f02c030030503095031462a4070710f100b40c081020401425000180083d00103500440c1c42c81203110b641044c01548c01140d000b12000320000040100f0140e00d42d2001c0c040c0d503011191075003020740360605640c86001300d00384840115051546003001c1491612800030329a1903104a840850726540c070a00c009005a442c1000da510142c2440308481d01840695403051034100e08141c585890030000303042e03426121012000020445c0e1510280400f1982441c50141c050000241a9644e1000401c24209407044071943c180380d00c84103403d441c0500c101e55950080800560901c1c45035a0b00208070880c1d89100b5050503690b0040e00d801000f0350094079142050741e200003400340ea180041c40a031860358208070240c80c1c4100450f072081600526030310f007000000c420b140c0e1945c0b141e02c0420020281c45201a40c09401d2780b04224a1007000402030643c2d65155903811 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 592543543 1250 592542293 592542311
    0x130b0106021605010e0409170712050a050f13030b160e0409030203040510020c090118050601020f10110d060e011a040e0c031e040309061701050a060e010909020a0203090103 76
    0xe0721000c0c46031100103040c200b00c800300111342c80b0700e108054804c0011700009414850ba074540844150040301d0b03012250010031380c00f050102041d5a051010901c0c10020301c0c040707144100800520032440d4401100c1000f00b43c0b0303680c00d0300c802c240c0406140c5c03000041c042c4c1e0400c0004040c0c0c204100040744005804101032482a040c280034540801d80c6c03603001942080e042030704111807104a42900008c40c4a4100d000c40b05560f03050300d03a8001c2001043c0090b8801204d030440e0162000200340c607046d54040803181d18480f8000078240c01c0145999000620301b08c0ea109042c1c01c40c40364030408500d10b030070f01401040f54a00010b12f24100c8695001c0c207401401c401076141018051351003620b0009628000081c0c0100303000c002541d000d290312401c1441031080590200a07407100355826400108452010f00016800141126a0004c8502c0400701da41c503001c00070391a8003540c06070f01c04121191070381003c0ca03402001039802401581b0400d5496412039900250760f504810501400242008084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 592544793 1250 592543543 592543547
    0x10e13122a0f030503091009080a110d0e09130f060c020114070909110c1b0a0b090f1e030604051506010306031101030e030c030a090e060406061b0f0b130b0106 70
    0x784a41c012200412400b07a80c9050b5102c1c0c0004014951070702411564840803d0a44950f0346858440e410040d142d40240c10b00824200c1c141825020b182e00103c100410181c00c240350030b600700d404540c0140039a54240100c0f5400111550040004000080708401c01030f42c0d402c60220300040d0f60081000c01c0c1001841c40c030050080d141000450f50445081c40b484c0c0c80c0f9000903c040b145191200e03e040020f02000b4500206084040f00040d00300c03104c40f030945420402c3c18010400d0038070345d50409050f00300045022110a8210340300300c0c0150301c00c14030344030030f18210030300440000d080c0c0e0440d03d46170800945404003085007281c1e4270001c10026610398003921512003a02e0704030720302c4546001080c0c0194014001c01000d907403644000d22080940d01c00401c0140b0010045542e00c52005140005d2004038510280c001440740d404c0c49002e02980790300c130100741070050100780801e15624090a0207581e1104802d009003006420500304108100c006000c095407e03c250049040b40c4e0703858400b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 592546043 1250 592544793 592544867
    0x130e0f040210030b0a0513050f09010203010602071215111c020a050d0e071e06080108011a060a05070c090b100806150705030c010e061b0c0303010e1312 67
    0xe500ca408109001c2d28030303109600c0300c00440d2000c1c04c40207840d512800046c082c1400d02408450580d11031007040400024081082c0d0400f082d44000d40c219414003002035210500c501419050b0501080c04400b400b0100201c5a000507808008205504030f01555039041d5001c00742c2440400513451701c0070104100352088030200e41c0030360b807a1424120101c8400d4080c1000b55920303042d500c00d4050104e00c4440712000c1401800d008500d01c1421450010094103000059103c0706060b4507003403c004138800150b41803030128070200d404943c0d1f142000800d0f60103000720240644521803140b0b0120b0807000c03540c44460000004c0b20b001a16580b00c0208031000401140c0307254111020700d2204c0301000903000030705005441441524204681d030341c103160071a000c03002c0030b070a241e10400c14401c40076909000300700e4001c030400a02d4600000480c0c042d980c0c0c8010300c2160b60b068603500c0040d4111115140b05000603600001d150500702c00814000c024125443c0101c4154045246003482400249a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 592547293 1250 592546043 592546051
    0x1a0705040302090603010f0c02070504180c0311060705010204060203120105270c0909090a020a0602030c19020d05010903030c03050a18020405040218180601061b17090402130e0f 78
    0x95514602400c550910001e29806800300e41c02d50f40300c184d0488004035500038a200030500b81e0007414802d18240404c010b035010400350981c0d8a40107200030000c201c442880c0001d803a008401000b01d41c254030049251445006409000d030352002c00d01250084d808001001c5607000c1e0041e508141c3d88a8041182d140d070b4405240c03510030421480b045690030043c11440e44040c1c0490a5070402e1110408035505a008881044868114100300c10443c0345c120000c2001d0a0316100550074001c100d0001983c42144080c5250048291010f141c119036401111311f00d0309900c1707002808601c00f03514010340603001c46503118000c01d003888001104442684102c501800100050414401c01602480010b003005030044e6044600c2c0fa456110711411130013164003908611104d207031841e001201860610130103070080420461001c500081500880000000c49a0400c00c940e00d140c081c031a0140c50307441809041c54125002041c7e07584244010a1801d0441e03154071045461956180c5010a242034229 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 592548543 1250 592547293 592547297
    0x510081b0c15060a0b0c010e07140102061305120d0c08090115091503020d050619150b031e090c040e06012702090607080712023d0c0207031a07 63
    0xb94400d5200c00300219642d4202002034a0f4045103a01ca8210550b0356101c1c08038684203a459400201c1c6803101000200b0040441c0080c8110081c0380d900002c0d04e81d07101501c40c0101940c070303001000602a050100c141600b9102aa0683d01c2e2045e044d0031019252064080e000b2465850010307160035810b008410580081b00c030038040c0581006958001042e4585110104510500300400141c0301d60f590005814000c4004000e1751030410600320741c2c1d2801d010062400c81c00d24408403002540950b501c001c0d91131410402c2d8403540c0301e9481030050558001012032001c90070040c010746050104d9020500881035130f00788001100c0c20241540c8520038462000780c03003c180070f69243c0d1002c0c8901e413500d601c1e00707841c0545070004d0f010000704260032500d000c0c0c0d0400000a40304040103204000e110b5980064006481110310311055100301c0e00c1d8020412611103551440200925904008905a0400a070040007078520603400296038079010b0108030790040000789900703a40003803482c100e40714408035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 592549793 1250 592548543 592548553
    0xb18010206101503020f071202161a0d09081c0e07060c2109030c1503231504060914070207061805010318050a030804021003060b19090510081b0c 64
    0x40300089000398801d1b04148171010b420320003100011445500034811880c1640107108401c031780c404010f004282c42c0d008bd06400f07c0c541b4200c80e03d04489042c4c2d8580b807046000040d10003a10f040008142c403030b18082c0c00309261a4106000c0304000c40c0d00540c100840c0c1c03811107007115242c0ca016034074070100d55400b41c800120314101007100044509250300e07690311880c01c3d03c42d07c0da0740e94903078200d000b154010040f20858942d002c8504c642c54446d044203941d58206010312881c90340c8900000701005001004110011001d01301d807a00c0da500700000401207200d0410042c81002840160301d9403c1d00c0460060180a1001800500c83d440850305001400944401c403450040154000c200c2d03640040c04101401c0100e4002c1ba9007400042020b60281d00d81014920b1f0520410000e540c0f071a41500c149450036106024034043c2c601034a200591098544444580b00802a0b0f1121056400554400075122100314401d80c018002c50107040d200403043c0718038212907403440b014003070500c0c600080c0d400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 592551043 1250 592549793 592549829
    0x4050f160c050601051002033007050a0503040b18150a0b0609151e030a020705070f0609031b121a09010c081603060506040609080f06061507030302040b1801020610 72
    0x101c0d1014146c48000c0c0100c034074000c000c60300801664280d14040b005d05c40124401440c143e605d0802c158007041c5440c00030718014a0071405401800090405040c0001c41c80c0001c07807a07501da140c00610007030f070a0219502240f03940140d01800c001294407185242c00c00d0b8520550781811003e488d41104010300c1c1c04855000c0043d10301d44c40d00a40c06070303240c07820010100b2142d10f0b0380c1030066000301040c400c09a0341d4105400c08a1822006a210482250400500f0000d50383d00480a50642c3d9100100c111491440313030394550000b000d40c121030100f0b13150700c0c1d0581c10040051060802e406040d29111010303a1002c0701c0b2400c130385103030b00364801040382a8000b5424403409503103000003080074180052803c0d2505c001c2880350704541c00041c0490440704c1c0038490050204440164100500d008000524007080030030346100c04030803060040c20004c80c8260030940250169400342070500e052a031a40481d0316080381c10f81e42c0c448400d0242c002d8101140140d41100940700603106810508140d80345 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 592552293 1250 592551043 592551049
    0x1401020a090509152b0c031b030b16020a02030709200310120204090501050c27030c0609060706050406060f080a03140c01090c470d06030204050f160c05060105 70
    0x145e040e50640c0c079841c1460803c000480e6410808000f1400b0307520340c840b15801d52812072000409070005039110203180b0400c00008041d031851603030021030a10b20369070392035140009074905031005900039414000d03000c01081090250b032140c00041e0451a0088200c59511803403c03c51000b550a103400702109a414440700030300e15482201c0910140000070403c2040d00c449007110019600b0562001001500c9200a0010781403840403200e0060900e00c03542c0000002961010401c090300d0040030040781c22015551981d06441c19aa0000c1d003d11951401d480c00c60001c0c059401003683d184041c16000c2428400002c0414203140c1c140c0f0b90041703600484640840540100c050912150f407903c0081c400999003243d030100034000d41d1815282d40040c00d4100c07004041e44400d001e6810900e840300700400050b00d0003140318402c5891442d584e06541d0f0800f1003e040d40f80c0010390414101414451400c145e1460b0343d02c2107460710040c2989200c0c80d4800c4400c54101c040c00b03480c0d68404001402145 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 592553543 1250 592552293 592552309
    0x9010201360804090c020a03030e03160b04031716022413020a08011e0c0201150b0f190507020909070f05040b131104030b01120b040b0a06031401020a09050915 70
    0x1e07000340c4000b403c055481c00c446090f1800e052038180140c100c0b003641801c241e0580180585203482c480610b003010b640100c0c1030303500701d805407000e4140d1401001040a140c0191103918104c2500d0114055502e8001d5001c2c44c001c106860b05001072040346000500000155428501d4610382081c030b103000d440c2c2940081119411520582c1c0c061904480058103520900c607900c82c140c02d0014080c4080f0440d0240d504544054900e00156414030703545803600501003010030706840ca01d80903d0b4654214a201e0230250160341c28404807034190400703412070181c00c00017402d100ca108031100741045e56040139a90310b07500244240c1d4000b24842c1e40901c0980303040c0d080000003910160031540c03031414004030340040d640c0d01d0601a40c01400003500b40144444004060b01604200c03103080042d41e02a40e90801065004002618040ca240c01160303180c02c03142c220700b000f190407804000b8514007408419000390b200154450210704043c1001483c0e080400880d4030420b15000380e081b882d044601400150 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 592554793 1250 592553543 592553651
    0x7060f090f0e06011d120106031b06020607053016030605010f030b0111010c050301080f010203060f040c1e020106080d1e0509061213020907080412260a0209010201 72
    0x4005010205c0a151104500c95406440c03810001c54031914504201c0640342d160540341c0100341d040081804040d80000d0f5040d0080100d10788169074030300c8482c1164038480c01c03000d8049809510007204c4409130040396420f0080c0c202c21181d110003080c9240c1901100d58510400c0d000c18a25001402028000d41c850003020303006050054000032032501e020308403915104410080740010006008c00307603041001490951155000310728600b4101c000950b10040180300307138420f40c3c54030442c00e1824401d80c80200302c3d04043c0b0b50200c0c2e100103058041e01a140034050350f08203205030501c80364070030f100c0d00180f150f815000d110365620800c5420210303259031005a003160091000c2103070f40c0420302c225606d184034916803c000050340c000c03403040106405002d805101080360810520000c01c2c41420740811401080c20315150303116051480703118407032180c511a2407020211080120002503a00285155142680200200720b03008618103901c00056510080c11200c00800d0300300502c1d0300300c601da52 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 592556043 1250 592554793 592554827
    0xf03050309120c030309070f12020f120d020604110427230c01020d030204140928021306080c07060209130f0c0e0618090c0c07060f090f0e0601 63
    0xa038690b8082403105511110031480a0360000082203140031050200c03001a20f40c01c9030b8100070034500104951018030b017410103486040e00e1060350b00c0c6959004c1305041c214402400ba96403441010901070f482c0d46e801c450a03a95545d042442000602e454031603486000000c2e1010500d5003110075148000908000044070b15041c420171101c040008510303140b042e004000d00810310001030340d00086c21300b007007040d40006040c0107000c18004900381001e011390b803201c1994401050350b10707452160306000c1000c0186c40001214481505110f200d81c00070400283c154281c09040e6a44d0001201e020b4030440c2e105034118000c1c401e40d000185140c000704219503006080781c2007031150b684401e00b266590740d515000d055032280001c04c210b41104d08000c40b80011181c240c1014043c0c840c000c507030340c40304d20180d100e450302400154400c03241c0000e03030304942180001c81e12220340340d100280c409000d20340c0b1413000c50036249001582441c80a0700350203541078081d00300c40c1034503240019a1502005080464 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 592557293 1250 592556043 592556053
    0x90706141201030c18051603020a14030a090c150e060a0e09010b0a08090111040b090105130e01080f010908181309080d11090637020105040201080a090f03050309 71
    0x621590a504250280d4010303841c8580d5203183c9031074654018072540441203031504281c10485007805115800703646047e5170601694500d081c0c4001ca48143d81b07402600d00380f540100600c041160b042c0d01101840b44035207410004503884180191800c00c6c0c4000410000c0d1114116040728100030001e040048518242031400b00100000a02220030903080440e210401140440050382c0c454032070368204104800070000074a00011014051141c1d0060801ca51000141060326921440455844031031455040305000d407980d0301e00900a0080c840c080f120301c1103404242c8500018854021007030b42c01f01d09140b44c043c240800c00c54400f1030800f0584d1003281989103110b40341c0640a0b030040b0030321810100b035440102c80c013440d044035920000c0700221882488546401c0d1100011a8941d00051200440b05002120005580f090740380c062038160689190820328a90150446070080340300341c854110701da44044820040761042e4002500084458404502103801403005540055035002130314 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 592558543 1250 592557293 592557307
    0x30213080a0b06091302010e060f16081b0303010605070f0309150306150207060818030c0a08040501030b04090506070e03030c0a1a010806160f020309180402090f09070614 75
    0x1078200114800140c032160405020803290f8036044039515406200031140e560141c0068000801e0002541c00c440e001d0440052140b54015040040c6c406540c03200b0702c107001030740c907625195425410640034031190b0700503080c00380c3c0c0c201c2012080d40c1c1a100f460341d410342000502c0c1c60710791381182d40c2401507041c080250408600700707001c40200a01c1d5040e6031804070720395242803640d0b44102c40e40e10a920441d08148028050150300100d1182c10000450500c90802c0b1609842811842094a5252140302e0f403c0c2d00e20400110786c000d0422a6000d0305c0c01c005680d4400c05200a40300445001042d40e04400d0004500782d0040300b11148604c405000c883c02d050800c602c00749803506081064912004801c0c1c2c02100542e545402e1340546110406001142400d071521201065440713000d1091082120f0707612420780c400c20558440d110010426944601d000f400001e80580c2501c05a000340b08200028180c4020002d40500a00d03061000b822154546034088400d464002030311510654100260 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 592559793 1250 592558543 592558559
    0x813050402041202030607140f090415080d020c0103060b0a0c0303110301090603061a032d0d0806040c09080c0f0109050a080322060c0b04060e0d030209031005010e07030213 76
    0x380002e032900c680f4002008050303004040c60124004c000c0802c001c0000d00c068490202c1e0020b1340d004c2d1204820b00c580340ca00640004c0c001e0100d41120a4000c2c11f1208006280700c1c00245a080c44400380d0290b8200c0f100c1a0b00440075141d0034050408144020445030038040e101c0c101110030341e4001d01d0000342c0488155040311480d03000780d024031740359030710356034240148000c5124500c505960318050480301c1e003100780131a44503480d441004031a40b10f00032810f0920800403140041100e508401d0ba000103018031000340241c842551880d0040e4502414940346074040c240c003a0035607030044010040d004080040164a4501c005914100500440f000810707449440102d000f03000900040c54852515000004181d0b00300100d4090403048071104011582d007004001c150325030840f555a6169407036040c02c0c00074244981070301103a40b195881800c459030307055010b03202e1144101d00356170449001c0282c480c00e07120203009640e07034a8069404240340d54029801050200709040110086960310002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 592561043 1250 592559793 592559797
    0x5160305070f121a0709030501181e020a090209010201021c02040e10150c080c06070e12011103060f0f03100501030c0e0c121f08070e0f0f040813050402 67
    0x10448181d4001282404403190302d40e801000b5224500440d1440c0708a80c548410030100c80f5045a811480c842c045903c182c070400c4014080c5400400030301249042d039a0b50264415464030a580c1160303a9102e900b040d21140b00501c103041e8004100203e002e081802610095108801e00745c103541d401c2041203d1241808050220304000140c010788481c81d0050a0780c26190044c84000c03481070307803101403054507a44210001c004400345000c0d41c1c040d049241c082894880c00c80d01c003400303202d06001c10025640c0402c840c10029015213138030228a41e10b403d030500341c60200e00c11044203141071000a0042c06c0095049609100003051118940340c1d45000c20304001240d50b03224201d0340c5540050050140c0d254070080148103007000d120061a2000013641180200c0761a003450701342800119400300340302c0e980a5003410120055800d020350703881026603a80101d00c40d00d00d00d828888006109100003010103441500180303601101540c40daa03030207155074013001c0040e0301c0a65070840400c0580f030750300c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 592562293 1250 592561043 592561049
    0x15060a0f08070305010b060306060d0203040c050d0b160206150f032113080a0309030321050702010204060315060f0f05040e100326300a090b09010b0a0b070516 70
    0x20701015811401c04c01d09407011154000e0040a0030000d00000c0d880320030031166050f426035001a102c1d1560301c5c5c840c60041d400c0c1c0c0120f51001185c683d00c1c05001942c2c0e00513005598100c40390403403142524040c0e031148411a041408507210660404c1e030740c01c00d500341001112005090302d10f100000350403118280a088030b54401480003259400e40041c182c2408009041103a004007800556503400130880c01c10350000a04000250039103460307215114407460f07110000c55609110b10b14210394000d00075041880b84000180c246030840c00b0304600311000c0415144155500803c800c0460410355841aa20703d400c41006000c000000b40d04408407030003800b601c10030f2a240044c41c5141400c15000c484503001c140da881c00b001420b29050940c101310352125007100541c1d56402c10305003c40741c030080300200304910444420100458107517258020503000d4403a50b44440e2685449441c00e003220b01c00701c0f081c0d1700802440c00510607403841d08080c6c02000e10601c100d50000e218140492f151501c9a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 592563543 1250 592562293 592562309
    0x3240e0c131d0f18070b0c010b040606030e10020c030409020f0c0a0f0312230612012f030106080105060f0408011418010b0d020d0c0b0a080907061115060a0f 69
    0x150500840041da8483c154114101c120301500d10300001403016240c003480e10a40e102c0b01c00001d1035005c0150290800403032014020000c000a6565210260280c40701a18031840c5001341404403400e525280f0030790742240c00d12002103051a082600c034600a5114507804807072440705100c16400203504112000e0068072030203840071043c101d0b203405050f100c5842c640103407960a000403050900c544032001096030001d200d51104c2500c841c00450881c2c0500400c00c0459400e08403401144003890900300c0d180d548038042c290140090010f001d5044c04203024500010310480010415840d003040a440c641d440d00c4249441c00c1c0e40e0f06486801c441608480400c412408420800750584180300003a40c6140c14009101d80e00180300040d50203051403100a2003000005541403d105100f14010080c3c01540b400580d120200003024000c2c210403a2107149600c00c0000129609114a02d00c526400c5440003c19440c45226410080800f00030041500201c102100094145104102200811802c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 592564793 1250 592563543 592563599
    0x4030c170a09060509090a0b01200708071e09020304060f06120203061f0303081905091c0e1003090627021806060702150f0a03240e0c13 60
    0xc40040c0000b51158855000d2001c280100d0859458142d00d02d40d10011011000440751955001a07420307519140d403081140d9410f505410949c1c03c001001015581060103c41030a643d8813502c8000c0520f40c2075002c40b1111041c0c0c10444000660003864109119240200d80000d10554410803201240e01035480340c1101e031106810340c2002c2c01450740054005000e4a03c0c0308104402c900d40d211144002803c0011020018100c54004a86141c00d284658014045070500e41d5070250754122001400310b102e120242c11144079400b5155081404001401c0c044206450360f4007540203203243c0320243c4285444140140500002c0d10740c43d201d1003111400e840c00001107006003c0c5410064160300c55101c240005d01242c0d640e00c2d42a10803043c2d0484001954503946100907089005580c180100424081802011075405030407a92011030b8195050b003002d88007040140420900f0b2192826004070400410740d200c1c0d01e6401089035847d040300c00491140d4400c20102c0407140e14420309070700c540b8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 592566043 1250 592564793 592564807
    0x605060f0a20120a12020703030b1503011a03041e030906090806040807020d1a010305060106110303071e03021c0e150f06010e0d05031204030305071d0904030c17 71
    0x1000c2842d400b1684201c1e400300240200d82c08541c0c82000b08090080d110000c104041c845108210190a0041454003507403120b125280180140c0714020b502ca21517030041640001e40d03100340701a41d0403615850343d00210fa0400341d001034070541c03028106039440c00c6056810398604034055003140c04680f00c0ea0780e0f080c11038501a001486103805410034403403500048240703c04980410155202c5980440d000c1c25507261620304601201c0b80b61000c005003040c004000420700c14003145040c12100d05864120b52145601001503c0307210803101d207008920b94010141d44000d03070f102c4408120a0b82c2c2001403400e1700c4241820080c00880c141c041040da1195010103004006102d00e40f00c0000303030129149117042c0b4220341c101192004000d0ba04000505d030140754555034940ca1645402c0d0000c042c1c0b96104041c01080c04041021a4250302007801c02001c40e50091003405040d652042d00958503100007240030401184441c060300c150104460208981d012489030b8084120802e940d0360800d44e2410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 592567293 1250 592566043 592566047
    0x315160903081342090302030d0f020606010804030c03140d021204060c020307230102070b0a0905210a05032a130605040501050301090e100e0309030601120c180605060f0a 75
    0x1950300c40303040d05038001c41e007a19407a5640f41044500194071041c0403480003540c94007141c180305c059201a5052040c0c004541d6800c1d04400580c103c0f403540e034248c0fa440e07a26a001034a0280003501c00500040e058003501020bc2d100d1112411100701c000ba102e40703800d40381c48140d400d90f001a0710a0500c0034640f02480f04000b1980316620145c51140007560900384035031160480c840440201c0507010102c0511400c40721000e40c1100d12440e070081901c0103c0c102032603054010a84184115518410b9064401c03808072840b0042c40141790940000d80352010901003182c0a82001c2e00c0e0041408482032901104040540c0c0b202c0142078030f0b10740d55160b5003020780080c04500c650340403006102c0100310500460340d2040c2200d0566804041c041424515440014541200c01a10440702880d100048403007a9002c001001c1c0e0b0034007101150700e03a90300c82d440c4071050008071000908420304a45c04101c5038000a11540082210303080004103550344002041c415800449070342d00c0c207840050801b04a036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 592568543 1250 592567293 592567319
    0xb040f080a030e1621081303081c0b03100b01031508061e07140a26010f170c0409264504020706020712080603151609030813 55
    0x3085144040e414170701c0d01142d410400000b0100001070350130ba0300c0e103609000501e01222002c4c1c950015114882d9907074140040e8642208103c2000025010703e0100c880070707240181d218608004025041c2c5503e911807180040018880c0d0905241e00d50f0111000c2c8500c000c4101c00522030700d405040f17549002600082c2101d0103203041d003000c0c0d02041c1400131060340704140c002e1450f030141f144c41e40c5400a54094801c0780c0d01c101900f0003644140b801850740c006950800d4120741100a40d0030000c1d894010400c050070b41c125004000b5804180320507150320300b40c1c006c44c0c1802e014110405885414002d0328070401c1d0008103030058402c00181e03001403120b40b43c012001134007400c6949610a103500959020b2083c00c85040c1c14100b9448840e41810b54441d8120f801e41980480b0856581e9030302c1c500720210141484541c8007023003605001501ca0704010814401c11141804120030580d00c1c030704407100208a200504041140808000c000949264000c00c41c1003044417140320418a40034149580c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 592569793 1250 592568543 592568563
    0x90b0102060c04060f0f140c0f010e01090203030702060706021303060c09360b030d020f07060203070827041109040608030a020304260106061101060902160b040f080a030e 75
    0xb82410401008031540c042e08407140c10840b03213003400b401c807051801269198800702040541c94000a00d8903503509000400101c58100d00700207000300c00f8808940350813112102d1700650150410400b180052600c0c81c010549207110700b40041c28884050820345440b840c0c1d81003140c1159407800e281d10303800d4000100d400184a12400015100c90b525503182255511180000740b0055141d031034542240c0c950001c1040d5100641100c0e065060f01000035520300701d2155040c200e00841d01c02054462021040714210b13130b08071a11619282113404049000340c03890f001c04480b003030070007204040d5954600800c884c0500400d10b9903103a6410000300411940d440e4002c0c801c1e0b900401c0b0003085180c000c81a501240c080c10902103aa10400b400c0720a0405007225604d2a5483c0c00400314401d03030441c10105003400044002c100ca41e071603070031120480c8100074100380e94103100312000c00021144510183d001d440340018690000096a5060058012003842c0c00800c0e1103040e0720701000d804000e11500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 592571043 1250 592569793 592569811
    0x60909100e0f061905061f0e011e02070306110a08070c050709060f1e0602121305060f032707092f041d04110f0a1e0f050f010206070e01110304090b010206 68
    0x13008803404902800a10000e10007410b02880860300d25089c0c0c0500c564109044c290000a074410005245c001c0d02c40380d090008135056858039503101c0b50141c5030016030710301c1450340c2c8460f0020b880d90f003425100950ac00008403030510a4080c0400c2c0741c8075901980d001080a0715801c0c02d4bc03420303c0014040390311340141d50700b864041b0740020004c140e8001440d810f82402040e001d640c078003000c1304620914169402c445c0c1c20401c00a07948c140d880c8000002c510a48200310441403820010705400034a109500b03440c42c643c0c2c0000414080034620b83d10511014103e044040208501e024036120b0465503451001c070440e1010404100b4104800325800c02c3c080642ca98118524041e950302901d050591a100d010b00020340782d1128584030881c901019009000b2003002032100302e074000c54000d03100e02a2507400d0380e4020f000a4035042813101218070b41d10580160a40d691004411100e07034078240038450400108003129542d60406100510140084402c00b0400300c1044c0000b81c0b402d18080c015002c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 592572293 1250 592571043 592571059
    0x63003041a13031e0b04051c020601030503090103050709050924013e1015050d031d01030f0603060213122001030b0a0603050f060909100e0f06190506 66
    0xc1c082c07094400c0c02003034035440b00410b400061582c1443e0051902001c0042c10407054000b8401071240c00200500c0085407402d5003400b24100c08412a111142840000c0c240c0d03105008c91400b0750b019400507075120840345818000ea690b14000114070860503a000c0c01c2058040c190700c9141d0340032180c42c0141c2402801d0003445408403124a00140d001c03908004034a4114070058950a802e54050502d0300ca400310444000000f841891001006005c850800158410000186034100041d020803a03e030140c440e1644054900b0f252154840c50010103810580c0d5084518100079540c4502c0c07001d103004200050300c9441e24501000a074507107801403078005659040840c002030b5101030000c100040600e2907503120b00c6900058014000c0740e80c110754818a0140040b4015038140c0c031280c0703d60941c1c800f0122540341c00d4240640c07150240c8088c0c0e82900700000c1200c098809800101c82d00803581c00719000340e02140304603401d10f001600c202c094814250500000c5001e907006064014804550080e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 592573543 1250 592572293 592572307
    0x311040e0d110a0b07080f0a0203090c01030e031207260411010c020d02120d021002040b04032904080a020c19170a02041d060702190303050a091505071101020301030209063003041a 79
    0x1381e86331251600c0c60304064503140b0031240007506000f40c40b614025441e60081ca82827283d8083c115800c413440f84508624450010780700327a440215114041c5801155404c101c00d100001111860b149103c03c2e604003aa40424200589a0703402446030700d420100a09000303d00c40000908185131420035104c114010700081c07024240c42c00441c1c085a81c4198565040040d80000f2840b8944030403894243c0c544120410090004060040c169042a98243c0c0c00b81d006240801040709101c11000003041c0c1c100320284078085034405042c40b0b00c401b0320f048501d15061580082c0c1640c00c00c860310130304481060780801410100300145034000a00b8000751030740c00401d8440744c0042c104041d0180416031600040303150810107900ca080c60031f410400f0a421651490302e208060b28042c1c4107031300050004251440001418829241030340e500030030805407501da880401019044064000c2c200c00392414844d0082440d820000c000801d80201568465103003445009085441a001c00d5a4800c204881 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 592574793 1250 592573543 592573561
    0xf030c04091401090c03020f0306240109030609150b060a1e1b0f11040b0306060603060f130615050c0c01030e0715090311040e0d110a0b07080f0a0203 66
    0x80055042a100007070400c0791410204401004041110300c075519040e4020140050050130a007528025100800038032074030803d0554131102182c141c155006540c01c800301c0b00c40d01c1c901041c0308002c140f500340e1410b07459890b242c04507150300303904a45030707090ba401034582c44200c0e0190790360b40c00f81160480d05241801d0005002401e040c40c152111000303102030b54072414083c20311075203201c15901118045001c41c0c80c1c0f03c488001c601c030054462552501988095150500500d0700c03452002e005040c80791a21014084142c101074407059010980084140c6076840b2064007d0001d0a1a030020800901d448840c080c505040c882d070300d08001080040c4c2c01562400280707851040c5083c80c000505080001d81c19080450340e4001d2075a2404a0680d15182503110440c0010b40380140964a103600d40d0508110445454120144007030304001161321500d8029604101c104600d1800d0710f484480a41c0e40185da0038048030303000c000c50171000a0040021140c002c2c079a21080e40c840451540c1490105 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 592576043 1250 592574793 592574803
    0x61c0c110607050c0a0c060314060613180902091303030c022407120501150801081504080d0b09180105070c031d030304081606022503080f09090a1a0f03 67
    0x2050140b00f80044c03068402039040040d46030707580d00001c01c001003503200c5c040200542110010110006070b20340100d0318502e891011501840343d034818000c80b403860b04080a00c10fa54a8080340307041e0741c0d28640400580ca603944c90520070a4a20f00c0b240b40055280303400303000c403400c218411045503c004041e891124000c0310003401e041a10082016954640004481600c044586010240c0c2440000240c1210400402c3c490100649980c452680c842d1a0240e03100c04c0f41070301d000c01c40208070105000c103c807840181100d992018000ca40e840b10f00003c00c0e5144002c0e10159103e271210011500c02000a2296941111041ca0038800c2141540ca00078588154441004002039144018449507601001120014080c100684104000c0c00700f606410640d50302c5500050f02454070850418002e0b070100503d482d10a020b40444981151034a6000703070410701c64500411030810400403160391703440c00181b02d40c030301d90700106045205000810705c0111268440e4081c0700d289102051035540450703 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 592577293 1250 592576043 592576051
    0xf03020319111c02102303040503040e1f080c0a090902180703140f180303040b0f040201051b0703021905030316110d080a03150b03160e061c0c1106 65
    0x1c1e00b103c0c0b0f00c4001c81074074404505110081d402184100d202e446075800c806103490310701d4048490310503c1e1b9281c0340031510b440304880050250300104000c5c0f00744d0256002d8960007030034000078141c40b608402c11040001045400c0900030f0380c4040070048007440d01c030280c240504502e4070148402005540466410000e007070110030203070203803c0003e840500c04c0e4030007500e0402110000f845c9080c010350800c403102d41964290408030048030b282c607145800104581c0034585c807200c3c22050303944004070001e6502003e0422410840d04100116004001201034103140307415001400e8a20714510402401081d0051100c0450a14080400c000d95003c0180e41d02039000f191010074001c084d00e05101e612040701c50035980481c8000c0510306001908d8050304c40b109003074030b08110380e18203c014040d02000d140301c0c0312035900c2c003000010700c0719500d01e0482d4a090b8140c101620b20002080025600b50060aa1180008414507800c545028039028100d424010703810803091250b4041002521110020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 592578543 1250 592577293 592577299
    0x91104050612040326060f0141071103010e0c150d0b04060303081608040c050f120d05072001080403180506030f04020306061509040c1101060f0302031911 68
    0x110010b42490b0064070802e0300385c40010341004071081c0140b6070724507540c000e965032401824a04480042035015000410100c19031000e0f214404250180c03104d040000700c000440c41c0024400c0400003a4074420140c20021320070711084100b6103088042c18211290602da454155100c09030700192601c8040c440342011304808406a030310b2100c0301c02c860190003009200350b0072030310300a000000d00da03009c541e00d4021503124850300e46140300d0138030807155600d0540e0041d19582040c1410003140c98a000e0400d0341d00000b500c20350fa00d8542c810414102025034032550003040000a105040164030082da03640b00c08205103e5482c0c40f2290f00092049500600003002e00618480d6030f2045400e410f030b10b01c0100401024a6604d140c510703410f103824941610203d02030302c80c0c84049040c03441d045100c1210b2005021105042c400150100409000100b2a074003e02081d1014011121b900f801084054403100c01c15030441c91941c4141031401c480401c000035601181003401000070381402c0c030b5134280c1d4011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 592579793 1250 592578543 592578577
    0xc010929040506040801061805090606010507051608010e0705030601030b0f040305070f110f1e0f010306050d35030103231632060a090f0f0911040506 66
    0x503848020481c441c80d00916400407010800280100d0150014030030b0300c184003410046480c4c0c3c0c00c0804103032001621400400d811110003d0b01951050000d01b0900d03014074100c52419401c0d84001424421131f4110034030903511800e1680d60880c04025200c004c0c0019401014107614540302c42114a01c058404006000060701190500d0304c500c2c00d07900010340000e80d404040e8030310f107000ba001c484070b00340d040d000d442c012a00c0c10103880d00e202003100000300c00c0140356051040d1b80411000c0340ea600180c50505075525004500e903241c1c0310070003840c1c0d4414502210500ca246038400e103144440700440b00203481030040c070158034000500392030450394000001003180300709842e1070300045001d141005c142c0c0314450b205018240d088410404881c10f642c5070125865603145c81001c0c016100800c070440408410b200c01d52810000c0050501e0456807130000030454442414880300011a40100c5881030741c6e80b001e10220150380315070400401c068030002e141c00d10f450b0106009001e107070820118a030031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 592581043 1250 592579793 592579859
    0x16111509030a02041d06010b0309060615030604090804080f030c12040515070302031c0b10090501020703080d0608012301080c012f06190608060106091701060803030c030103050c0109 80
    0x3c80c20310302d00e5605c1060300b035842560b19082010b020b50000c5400994170b2003020301158590420a9028492041480c001460341c0e071040c0611018042c1100101c980880400000079401c0c0c0500c01c0744039003400d80303002c0d5a482143c01e0140707140041c004100c810914041104000395584e012806040440041109496400340e050aa040d4041c42010340c2c0801d51180c14141d00500e150300c5050303440030495207008101c81c00c020032070b080700440c003c0602591010b030060011401c0c04010300f014031009000400c6032505c0724500384c02d480c2e009509411401010756500343c003101076001c05014000e0440105000318403600003c01052070301c142e015942d040301150061507113082000c0b06440141401302c1d0024101000e603503076014000219510b02d03070314040d8040340380a00854910304035209561080c00c00c0f42404005503540760740140000c003940d40c0f810001017040051006d14814880400076035103940c07650412a0420414440490401100040600000b003044481e001f641c1c0c601c200480c0d07500300d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 592582293 1250 592581043 592581071
    0x9070804060f1401030201120501080304170712062009010e0907020a021e1504050a17160e150d031e1809020a0327020607020616111509030a0204 64
    0x41c1c200d02003503a5400d10341ca4030540f10003e903800341202d10030f13a11282000e00f0400311900300c80f82801680d005e41c1040104102c0001031121041907820400b003982c1c03020f5a0342c002d4001a01170703020101c40658072403544505215410f820b0007000c00042200034a041d908400003444903540c410421b101e5043e40c004218941e100708021841c141d40a4261b0142e10b944030702924041c2814840b8034886c5003084c104404055410068404582c00a02014045030800c04480c4014109081c100d0040c03048030184c40750f034504180008000c054111000c1c1c540d08004100e151011402151113009401500d9818002680040f0303401c103240c00075820905071001003c0850303d043c100d0f54140300d980f07401100132415501b590700603d041c04107601d0412959002011030881301074000059084100d1400a0314054146040140107052000341858505944505640c4140715100c1c1c1c180c8402c4043da00d078603024148400b45500d09a00340c070905041c005140000780e529521010000c6c00384e501d421800d20024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 592583543 1250 592582293 592582301
    0x10e0d030b011d0411070b0f010e130f020603090a05030f04050f010c03020c040b06090307091b02150103292a030c1812010c1214011d060d05100c021b0907080406 71
    0x2a841094031019082088c980b0300f00b0b01c400c0c0940001c0b0180c8201049422550101e4041d0440c0c1c8004182c484d03c0040d000c108264100810103001d40c001c082580780002c1c0244001c10424841900c140d851b9805c21082c420907036600c400c000d0604c043c0035180000f29400040c8407210b0b2000302d40100f004108138022030043c2c052407007101d825100d0b40e2008144e014007500408502d0200501c00540c82c0007072841260784001000e940c1c4074800c2c6190040c00031800c800780c102d2000d4400b2030100d1041c3e00b162060318903035408688004210350300201c0b40d0007941245a04010785000411250700b0360038401c1921046100e0145403001f40e90005400e0040f580382c0d81510400da440c07480007000303c00c92011014000308170911038680a0352405080b07003114140b0032075187c103940c03030340840d92041029103804402c0b0080181ca49548540003099060000300300f0022030703504010002c0d01140440800101924000e00380c8185680c0300080308517a01551120591070f9130108413450041031540745d03401c0a800030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 592584793 1250 592583543 592583557
    0xe01061202071703040620070b0c1315030204030c060e030d030b06041403010b1504030b0a0603050606040504140607120f0911091f0803030f09010216060b12010e0d030b011d0411 78
    0x1260f480000c7c640d004020242882034003859650307185903540c0703407090100d02c0f5900381d40300100280c1ca02442010006215228800c070070b410b006180ca5101c2d05d4807028289143c0c400000500810003000581c241032140d862400401d0409114510300034000034958060ba008170311081041140504543c0d60940202441c030201802d941c1a506c0d5030740102e65070340d2041c00213440606d044804110880220710440c02202c1e0030001500e825180c8604002c09044041d00c2600c0c1d00084822414200c2410b00c1290b004a03081d40300d031800c4000c1d2000c000180c89900c415841000c1c5800780c0240031590403154501011000c40742038915588940c24000070200ca0340d040ca0031040c0c02107020440c1400000154003e078141100709000d40da52095060a0b44501c8541805a10045050000280144c2c00054207030500911012884403011404b608481130740030154010750100e40039801141e014450400d0220080ca4450002ca00d0b10411403c518036800c0aa0300032607030b549008a1207a03264003601d6003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 592586043 1250 592584793 592584821
    0x10e0901090c14030106120c050105090a030b0717130f140319030c020c0d02011d1c0503040f0b0a0f050a140a020d03050705030112030311130e010612020717030406 72
    0x50107440c0c00603d4002800c0d85001c0b0701940c41d02d8000b16071015440c2c5101c40325903000034442240c3d4101001110540c02c8a03d809820203000c410100c001180301204030f100303190741d03a05d0010010741050094242c40c40904801e0002e10b0a8007070002281924485020032500300300001480c014000c1114650701c0b64014000400c070345d074a20b00082d594590400400300c40311b0341c00c54118200d418100950b0743d010030b500a000c644452804215042d42007031440c0004d8000f0500c40c6a242c904c1540a00700301c0410741250b041e080060309020040b00c1a00600203400d00c0864513080003040a0050803102002c050441804030120301ca20800340300d00c8030750b0032100140c03a801d82ca800064002a45d03850b0744091200210341054001003d1520500949040702c1c2001140910f01205032000c1e0300902c0c0ca134407185c1411400f040070103801040010410000e116000034014250302d400c20042400304901c042d0401e00d8010400c900100b42c0f01004480a168040c412542e2603c0da450312500a1100c40c10f1184 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 592587293 1250 592586043 592586063
    0x408070203010e100f0b0a05120a081303140d081f0308120103110906030717010f11070302100c020a0605090f01050f011412060705090d0b09030a030c0512010e090109 73
    0x30b010341c0800d0000c000400c4c05403d11003c41e03510800d00956041c040703070f660403144da80c20030056032501101ca5040f405117001503628001c041d45900d40319600c1220a040100a203074020410011004442c03200d081910001d05411002d09400411034080034111800d0108040e1b84001c02080c1d10388902c0007164031005a65588100145a0240d004d007480207481e020198658500c0504043c04e4542c401c100003005010102c0c100340680c4445040c9200c03003905c41d0b681e0440080000b21a00c04c29641148420300c1c25201c009070329001785800a1040d0000680f820410ba03000c840e500010300103866580100b02088669074190b0161900d81d0f2070702c05480315800c00e820b00104145444086040e5441400c40f0307400c502842e400c1c840081030080e030400b0304d030307000c80c0c00148190320490251550490080203480400308603103a0700c01e0791809840c03a203a19080000c540d040c06805100d00c808250007424110b050540d8403003421070503141403084803010005000081c080031400c0d4010761500d0f030701c444094 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 592588543 1250 592587293 592587311
    0x7080408100b0108070e090601180b0c03040302030d0207241202030f150117040b1324050a060506120703020906220f151b02090106030c0e10090e040807020301 70
    0x140c200d08040343c0c00b240070400415040c5210f00700c0222480700c050440a007d07250407004491441908e01010400e04480c000030030804000c000804403009140001c5403502d05500401d402d1010805504065600040302003128581c88018040300c205030329010440301c04201d4056580c00c01e84808080954800020028079012501159010780e01204201116491a8005540d43c500c0001c0300388230b0521000020300043c0154210300e610483c80340301c41c121954199520183c940840c14131080c80d94854003070000f004000d00c1403c0c1d0011801200340007991034000407401d20b2090f6281c039206a00c0110004072658004d070122646410080c003070342e070f50b205035603400c8007075100c4443c40341805d41009400240007030740b141040301036850100c07008052500f1484144c3e00410996420300341804800b0003200943e8480d152140245000e4034003048603030200700c005201c05050380020348103e40403038901000d16440006481030794861700d0044000c2c0c440c0d05005d0307168084c000d070081d0b0540c01c1410300c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 592589793 1250 592588543 592588573
    0x3080a14030414060c041206050612030313062009011805130204090506090403020c0d150f020d15080c101101050c220302010f0c020d050f0303091603080d0207080408 73
    0x304540c0fa0743c2c9801d44060fa281c9160158051040c0c2c4246144001c840c90404082030b1590302c0140c1001c0700502201c1c03500b9000c0c084c642160803c85599451070003100c4100180100340c00782c0001d00d070340b290706001d8582d148403c421560007034512550404c00000400340c3c0e011080001324005c1c180085c4514400080d2a000b0400b0b98018040c500c1400c0c1010040303591030800c4807416000ba545600a413000740c45c041d090200110030003000b91510a20074030301d0310f401d0801d4498422000b00860300965200c0158100c00b0941d0320360b8010a501d04080c1c1400c014481c3d010612040c0000d0442c2c24140c41800c2e500c3c200e07216902100d036840b0300d519200601c0281e0806000600d103004070209191004a0045850381040c0c0003480060301051045015545680c8100a00450385100500b102500c50309a190a45040980b050814413907000205000444c00104106c24601003980c01000015055039140c029500409aa40e074049030045144c20030080c080d020340d0041c1c589075007200c02d292240303206 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 592591043 1250 592589793 592589813
    0xd0809010f06180c021902041e020d0203180307021f11030429190302030703090501020d0c230904020a02012a1403072f0a1109010605120103080a140304 67
    0x212050f03a0b403408072000601800030901000504a01d1100c5040003003d80030f10000d031807040c00c048060345e44109140141c800520280c913075400486030060322440c2400440040400d900000c203100c2d48107110045c0143c0c2c40d0a41d614460034560a220100903100c0310a441c0700e0a60424510180404074020400481080c1046c06850790300610780040200707545400a42c0c802e0f92480182201082c0018111030702079001140c0102d43c5160019032459951115822030b000b846400d1048c0303403150025110340d0343c801441000c40c3d06400c0c40d8010311440c001d6808880c8500b46886000702d402107000c0010a00070740c445442c0d04031000c80b42034a00d0a050409484150403002c05011030781c1242504417600b0b400c02581d101e1010380e03c401e4a002c145a004000c0e0194940c00c583c42c0004407802c0c1c90704900184900350105115403003001009001c4001c0041d2000d050300000100b001c2804107444240603c00800c0c11a6041105140d403541181c0040710414055010502601e400200b440700704009688 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 592592293 1250 592591043 592591079
    0x140c0604060221070f06050619030503070201030b090c0a0305130f15050a09080306190305070b2709071209300807051c090506070203030f0109050403020d0809010f06 73
    0x2c02c00c2002c040c400052070b0f6600a0201c003030120051001c0e400000b4100760700c45600890010641032031520b854041421400454004640d103400100c3c0c2c00b030465030035000b0008240012245002d0625012607001c40b00d0088002c20b50403d0348400110701300b5a01f443d41c0101c0c0355003040102c0c00c2c240030707414141c003100109555000014503010008020102c248101c01c40c090784903461a00c0c41d1185001c01c0740b02808212401d05a110401c07000000903020040113000b0269040c1343d40d15502001095a42d04c0020030a0504880711481c04200c16a40c1d00c4425621640d41d01300041c664803850468802040f0311030b001030800500c0c8515110b030f14408031a070640700c4e09020307503001804433100742222034030b005640d4a00801d0084c010443e04410101c0c0c8100090748401e00083c00d0f2649854152410805a0721800035810000038085001480701105014040d0407100740994203040e5002952080079003060801c1040c10000b041c5d00da1802c1d00f00b880b6540d1400014400c46450300d0344c050b5032411f082e0b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 592593543 1250 592592293 592592323
    0xc031501090b071b1d0103060f1d0c0f0103180807080f0304030315060203130b0c010f0219030e07080705040207320115051c02010c020901030b040c051c140c06040602 73
    0x7210004040c1300d5125801c031440e01c0c07040b17243c9007a440c50391013402400d214018140c026031900391205810300340004802e200a00070000b480e100c2400e1052001039000038190700d0401d420310540c501900c1c2d130046102803080d1700ca80d0156942d8442c1c14000c46601800c40b074003440c440008280410316074160040304445c5404c81c141c42c8803560390202642d49225030700b00300e107c1c01f00c0d10b00d00304038561480d0081c0408041d5200041210720220440700201d07800f22040d1044052103002408115602d80b14035180021b1600c001c1030320900740b52481e660340301144100c0e886582c001681c20304008030f0381c1811302440c1d40301c2608030b040e561030161042c104030481a4030702c4640c641203080d10310700e40e441071020460f407010700141400403002039901089006244280d05200c6903414550042c2ca40c4000a4000c40c05000c910006061514002c029000c00c3da01451050000843c984420140301c03180e12505079001d00300200710410002880d00b007440c440c00c0d85034010004240000c055401180c2502c59100307007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 592594793 1250 592593543 592593593
    0x60106031107020117040c090c080907060905090a0203100306020304050d020c1017090312010e04120512060904060906060803090109050a0f0506070501020921060a050c031501090b07 80
    0x101c0d1180d250360080c0c1c0c0d0301900240300c100d09031824520b024000c03a0400d0040081580c8503403110000350556040042c50000a85d00a08100d203424040c882d400c040d1040340381031641c080c0707803034000755544c3c402a21040000b507000000c5403581c0c400350728072001140d11060954480c505070030726070385648172265a6009806910204203e0749882c80003105070b00324079203d1404010418142030020040208046071501c006c02400e218a03030b8541003140203100d441e50010306440c251404c4044030917071441045c00d100c41404860502d0072400c0165a00010554450722183c0e140c0c1001d1011b40b41110b0040c003200c1c6001c0c00071407030140200080224007400e0f2103030710905d503442c018071580c6000352140a003601b0401000f40301516121004011381401030340094282046100040d10710802d071410840c4e5013040c0321080e81d0300c0c401444265402112000d082104c1d00d0f00880c0d20a042c84000c080e03031200d401020340640c80d41c1c01400c00c207000c0c3c01c1e042034071034403418140b60201c042e0f42000000d042403d10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 592596043 1250 592594793 592594811
    0x170d0603120813020a15030b121e0703110907021606121401140105030c040f0b03010302100f0804030f03090f230724031806050406050c0c0312070314010806010603 72
    0x140f42a081040c95029045030507181ca401482000c5810060800d42095125134088240b03958a2a0b0b899889003214081e00841d9481c9071100a10001c140001d549504101000c00218941c6e4802a44801d41510014119900d000c812800e021114200d4071403501d003c1300126149030300194a54215400410421a1606944e56403e680d2401d105130750b40c45081c80303070400c01940720380e006d5a001004400c1280c20145ca42071210305200780e5810000b00a031000c07004205503d00301e90b01c0f95150500e410120000c0340d8124009000841c020405814040c1e0b0b00301e070005051123684100c40140d004100e11300f400546141100c0c54410b070303210b001c04521600705103a030b29080104000003150f002070b0448034224050300d030072a044400c16004405050703541b030050036480c1540a4000580b8864100080c5901d41803070321307904840001d060702d03a10711004d0042c00d840b40d40020464002c003583c7d200305072503603403003032402c5000c2c0071541c04040030300d884032000240c845c100040740b038141c0d1502d480610007065 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 592597293 1250 592596043 592596061
    0x160f02030c070306110f18270633041a0a08011a040e0108010c0908010c200102040b220602060c0d0906141003020f03060105030604170d06031208 64
    0xa800c541c00d140d8110030b10800c0040e40c1503100d145110000c1515600b80185403c0c0c906454002048200012105480040e03e6180140322040540444e581941c0700200c445207a07243e180c401464a17000c4e02d14104001c81c1440441d01e05a101952601d2a80d411210001c401040c0e40141c894158594004074078035980c020a0419255056003558036040c82da031030416980041c1c0b045a04c10120a07008000214840c4041e001280c042c114280000c01c0207851211b008041001580c803000e066451b0111003002254002d4040c01080c00852134140008811380d0390900920851784140c90440000400c04800800061140000040c00034200310460740c5130800c2e61142c00403a1441221102013010725600031090740f001c0040c40c02000d000950b05010390072441e00b00d00035242032840e040551010802c6150045810411407001e401410031940343c240071039968140031300000c00c4000c0e2003640400030001c060640d100701510880500c001d035502c0c1040c0700700301200346d9108006005c480c0000d107051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 592598543 1250 592597293 592597297
    0xb01020a080a2f03191b030522030506010b0714060f07020f06070203030615090a180b060c19050f160905060f031b0a0302090408130e091903120203160f0203 69
    0x800f55001940c030300500c00c0400c440d40300c1048450740500c205d40e000c10304403a80200140868a07c80d459059a540c01c203005200807040c902c4401800301200e12013800007032004100300e0f0460302144c030a05d0703c4442500c1c016610030540383c01c40c0c0301072080000f04006c0381d100d01c440c0790080e80782d40c082e5881c0300342d00382206443e0380044405101603403041000c1007807030400112103080154800c1c0000c1c204480f4078001014040b10b41d2020003007a48804c2c29600c209034a00c112410214111120341c0b4100b0705078041501d84817042c005180c41b01d117020400d004d0010070301c0f0b4511560600410703030b003004c002502404624070309400381001651428001030003d04000404020a101c020001c200422440080c01c0010f442026480d4203c6581d0740d0010040e00d6140d410360182d071007a03041c1d6842d40d0010070440116039290f0b01c11480b81d605130301840191000400c43c165031151032409001a80703a05d003404d455900e042c3c000040464030000420101120100c08035050040301d5840e2034594191081c200d03964 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 592599793 1250 592598543 592598627
    0x80f0604030f0c050705010e0d060c200c012102041d090705180f22060b15070c03111804050a1b05060409150b0c070e06090c04090b01020a080a 63
    0x6170b0f210440500c81580600e2021111420052004059003199076a040a039042e610544c0082a005800c5000c0c0b01c0c4150108440d041408009101e501e9200c0c00082c4052040030818110a4180702c1801d49003425404550143c002c0c2e412848802036a030106841e013034030840b0401160701862034003054907d000705070b003441d003041e0200c040b03010f0b159813002d4108402c004d00000c1c04901040300c115030056422281c141180d0103060005201c5005205100c40410000c1200307141c010200170040014003007450510070380750400706a0b04800c2c844400318501d00c00c00d05030150400404010042080000070b020003050780700b112107050032403200820603544450740c010303650b125509210501207400c0c1640401c07811246d018004007000e584240c1da80d44c552005c180c510082d0030503a400c1c0005038483d030405810501c20340e11080d240c0b4001064141500650243c803d015450303543d0025039070310030401c200700c03240c0158446940715280c3c200078005c0d032040d6492144450340025844218030581c400f03c094 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 592601043 1250 592599793 592599803
    0x9051f050109060605042304111201080d09060c081c020309010c1d120a0f050a050d020712030c02040b09010f0603240e0613110306121603060213080f0604030f0c 71
    0x200303800c00060290000d9444030303980e884005401c1c001d070b943d65203000300d00f2001e0541c2d804030360725041040cad541d1890405800c445810b600080304034203d86c0d4001040c03012601c03079142424440c003d0740f40824541c4500c080d0602411421110f89660014a500a500810342030f80204041004840180d5246c041410307031009a903a0317400c212034642424080c0f07421507a141c4090b107081d592a69512506902114015078656125004100400c0420040070125140500040824526103030a515110303103400801020481d20383d102500b151180d0f042a80d50a038010301d854499038541404880221551280a0020f402c4c95022400000d5403154414100b070005082030843d0305005c89141070701000740c64140c01c55800f0780c0f504c09075000e521611344c0d0400103455807607417800d01108000114038078030320510803904410710b140c0403c449040050f0031664850300240c8c0b036502442c40b02c41e01403c00d601030952402111445895024049132040c0315511030340380c80d0070512682d141150010440440148 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 592602293 1250 592601043 592601047
    0x16030b07090810291011120f0c010c08010e04020d061806140c04051c0201091505071a010b270301112203020306131104021b060601030e030a1209051f050109060605 72
    0x1034080c4101b05042500351220200c507440b00c03c4140c00000b542c003111401111602c04101085070320020300400503c485646040501541081002c1c07901e02c03009880284181c1c00b100c2c41c0c808000b801d81109100a1142c41091068059030420001a081400c020f4020409102c0010b0400daa81c000390307015220040e02c0701000129150000c407654009000c02da061214080e00010481e90a121505c26401d055941c20340b52a0540b82480c0d541c0071412032100d03a0601c5400500240503c0c0c401d613402449100300c00e104200814404202a810f8140c0aa805509000714410a20100002030440c1c5510755910650441c0b40f1040141a018a00000b035041d040072010448000580503207040039806039480d9441c4a40c82000a0100d0344092001100f1100c500326042110300103002ca50b903c0542800c00f0700c10011120760b040c0c5c03a4841ca20032102071106150f05c4040d40c130010381c000c0c0502540300003140c610b0040c102800c2d00b12100c25108142040c10480041801340311405042304840003500c1c0c480c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 592603543 1250 592602293 592602319
    0x50114090a060902130c05041406120720030f1209030301030201050f0f04050409060e0c10091203051908010e1f0324060e09010c0216030b0709081029 66
    0xc80038000f0308105a03405220f095039140c240c5178603c01d2910040302c540310396507070710305c2e02640404c000d0041d0340541c8101d1080c00700301500340501080c95800400c3d1300d45148540000ca508030070007c201e02151b0301a1101080b82c40108804100424228114440c45503050780d178840328690717a1009000090009405011040000c940780000d081c8200c1b10f07a02c600d05164803040820100c80c03103100142d8680342c554041075002d4005000c5a07041d0310041d5101c42c0b014810400180500302c103885500a00400728040c801070500c9001a51031140d000556034120480b5088000d03e8000f0a0052100340003819002c43c030510300d0200c40d400e904507030000d5100038610356100d203050360802c503840c804849082c0140010640c100d100340005425410803000b480c2c01c1948880d800c546d51002e02c9002d560048130b400703a070060022140800c880d4400318042c03d0766240c1c1d504480c0e50090f5408103800e03101e8105050000d4003250441c0c040040700c0032244101c2c8030060409844140701c5400725801000c240b440e5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 592604793 1250 592603543 592603553
    0x3011503080a14040911120901051312050906030c031015210b0d050f0607091d092803143907030b0604050105060702100c110418050114090a 62
    0x55503404005601c3d950515558041e808183c2d4050f110061410304002080d070f030350011005a10b81c10200c00b000070030041c07801c8400d0300790400701c051001c0d00940d640c4540060300781c0324404031011920041d226580780d00b00300070350050035042512481a48241d1541c040b5001c05682402103819031550350301c905a00c619494074640c00141102e80c48015240e5551a00b203440302c0c1a0901c18511900c0189030a5a44418060601304090801403c21440e89000c010041900300c0d03940e10462040314502517a00c5a01c0c11a2030312101080100740f00e880b00c1c40798884610103000b0700700c885000c1e440751215030102d40a083c2261003016000042c03907e51071001d40302500000c03d041c116908070402458184583c003030322841c0440f560f00840e030301501740040043e0703401e00b402540d00500f000da51003824056a40d000803600700d05807007400200031007075100c6820700420500222220801074001c0280b1540b10550400000b01800c0580d250740c20445031800c807064814645100310f4014010745000385e515590 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 592606043 1250 592604793 592604807
    0xe0f0f0312030703180b07020607081306022217010b011e0e0a03060f0b03071d070507031202040b0d0b010809070b0a03090501020c0102040f0b0a020304050904050a060504080903011503080a 83
    0x40504150303035541a80c081c04005e40d0f0701580203000f00350100c2280b8200b400240f5120008103c00b003086010400c1c00b100e40c06116281c01000ea12101c00b40c2c0b5215061301c030343e42212010250ac1060120b440000460141c031802110030a120341c0000d216856820f0015589003c69040a0304200b5840c4200b925051042c403101005d00d10080c00ba202e03080d03907902d42000b03a417054010f5081186e540d1041a01501e0304002c0c0304014803245880502c2c031901ea882d01284200020068410b00800045100c10140b085582c4802640d14450442d110740d1241c4020710290002a101c1203407078a0704000485a40c00b034403180707104d002c1c2c500080a815041607480c25458001c00401401d041e15200315000150081c0060101140c4840005032603900c3d20300c011042603001c1c2d104407045403041161240c09940481150305039902521041d619450328a005031900c240264094000f61400c0248020080410300812003031104074004d001c001a06518120054484d2100604420040240480c950b000b698 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 592607293 1250 592606043 592606051
    0xa27060e150c16150906291e01050d06090903140c06041205300c040b0306010c02060405040905010c1e1b0f12080103020102060a020f0714030d0c0e0f0f031203 70
    0x71480568602c08280251180020111b501684410080301d1020b800c844680890214004c4070320750415000104507074040708820315103038040f00c080c0207429034002d108454503450050b00c20090669250a000b0042c0b4010100710700087c0706107240317280100d529050300c1c0c080c3d0708900a01910b407a141e448501c00401c03000c104c01484001d1040c040f140c1c201d03001ca490000000304a809000100f800031b40507040c4010074241d6038120178041809000f119038240e030b83c031410a09014100a0306800010362501942d4032159200f41001c01d004108403040d00480c505110076181c0e0898850010440d40207005141c1c090760000d030120411000c00b0150030b042190980c0035900710400741c4166201c0700484a4030080d600d005c2240c81c00100119603040011641c002c104072000c5092030000340000500e44150100546001c0e1381d2948154510810b0044510780c031a940303400c00c00380100440140800e001514458464510070200c02001d00b0320300c0408160300f42c010050142100c01e0018041e41c8c0e00b000d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 592608543 1250 592607293 592607303
    0x129060a030f0f09111f020d03050603071a09100e010203250209010608150f010801030201110111030a060302031002030c0307081003020901180c0207050105030a27060e150c16 77
    0x4006508001c900780b20710340c4e00300d001d04201d0540e44404010b00000c010542d10900d900900e50400740a100e90204450301d105020b860003081646800e0006880c2c0701564100e0045885a82c0300420885071a40091056020958010b00d081d0340d01e403001d5800c01c9d840940c0f50b015030010010155440203070a1484440c14146420903001c5001e50081756401800b40c00a03404510321405008a0f0a03202c000f051010313000b1251212a0f0403040c0c0001c2100a040c031000741400030101c0d0300350002100790040012210b40200c000d88034600216140040c040c1c911090b402030041c00080b20705c01105000310380c417412030202900c1c0b9585406808480c0c5800050225004021400b00480183e89520050f4000c101c02005458000b034940c0031074040b90810490311b0300350752000f2010841079801c0000c4d2030303000c3c561400006105001034090381440140260780d4610b6003a1000d45001c00c00d580c0d1001d5180c100003c2160f100b504123003803155550005a03820888802d050150b40342903845500306545c094030070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 592609793 1250 592608543 592608551
    0x15090c030607140d1506090519030503121e091609060803220e010603090605010e04030804020f0a05030703140f1219030e03070b0f0703090b0604020711120129060a030f 74
    0x21801702800154104200044201034100a01d141000c00020154203c41402c8400740c40e40d03492b00e907244901401e8017807807642c2c480020b594100800002104076048030f0200f0443c41c16070082c0341c40342c42d4060110759026045802242995940c451a001d85103000010b41c0351000d07810840700008004e04940318015920b0b07101040c40000c1c1c01890b8000c21464502180b440840e207007a00036101c0c142c0094511030f502100b0080440c1c6d02c141d03030580254041c0c4422b8880d5102d0320224503510242c0d0025030f018800d40400104120006ca41880c1c0f094956080c0d80c50700c80090b465948511800d02c808031807070030900104142e402c000103083c20034902801c0004a0310701448203a41590440c4505440c1640d02c00c3c1044112003000700740e0390b0301914619042081e50025610445c9075800a88454003559010941d18104420001c0003180b0700385c02054100050f440b10b100340e019010f6607661100101445580360040f1848031107c0c41900b070000c15031802c28444c1202100201802c1400076a0944c036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 592611043 1250 592609793 592609811
    0x705030d0e300304060305010612020705030d0c0e150403060e0a02030703030503090102131503060b04050109031103010e01240e010b040b1c241e120c030515090c030607140d 76
    0xb0800040000b84056100880d8a601d0708030301400c6280c40000400c50103004100c802c00054001c41120301804d074103e0000b5101c010b00c0f90445500c0102110315070800c000c0e40030040d9003880784001c0c0c004c8130b204510601284120f40c54160302c0341e80241000750954020389061000034001c801942d4440c40c65800107080c102076903520501d86285510110000c00a007000400403541402900040c00f00508140c1c43c0070302d080e0002f000384035144000b60103a5070307004402191703542c01e4001d0341b501c0f10308500910030326920444a444c2c0c8103907803d400d807015240e600b00042581548004d54101e0303000322005410185000b9484c002d46c0c0c0813100141c850701030801808d8482400d4030843d8651808450449040100b5070240804102c858110704050081c040310252044074469900040d60400b42440c03070329203894a060451040290001480707070284a030000c407a6888400e446101d1448a4101c2c0d0030142038006041c2c03a6403040d1490303400601c00d1101a00500c02c2c0340000d251100b2544000241071308 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 592612293 1250 592611043 592611139
    0x1030b0c09040203071d0a0b03070f020a05030f12090c0d0f050102070f11130b0f100512010902030a0c0c02030a06200d0608070602030408070509071b050705030d0e 72
    0x4000c0b40d541d170100e15165403401c400b141d81000308030390303a4040c7c4800040714207010902e071440c003008085c1001c1000101440c4025442032005441c2c040e03200040300d8964100c10300c1d856060704004031454003a0000b100041044800048103200d00101030001850280113440e506050301840d081038130659020008400056141800c481cac3c01030082c24420140745408003080403a404000c0c0f114122414100c00d51410703950949682c0485c8400c0b1110741910b40703481c03001e0b0395078060b503006038410310040000085d07216407076001140310b03c1c034060f4100b01c010034603441070380c4140511030040c0d059030102c069070740080d90a6110a241d1035550305a2580c402c420301c02c202079035103d02944d44440742c982c5001c2008000401281d405040c41d8005503081c42d0a001e001542e4444600c5114400d003000404140d13241d000c2c8004881844d1180080081c02e60a800c113940c0d200300e28032a085c043c1c45203800d1120401d20500003401450350081039910280d00410000111a080c46040c00725220006541c008400c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 592613543 1250 592612293 592612297
    0x30c09061211121003020906100e06070203011b030204080106091107110a09060803070b0f01050919060b04090b030c0a0b0d0906020c01140723041509180b0a12050601030b0c090402 79
    0x84003802460502c45c114030600c0000344028104d1401110701e5060129990380050506043da4000d651250300c6818038000207014003003040301e440c103030704541d0011003c15038560001d00a030380340e8200a0005c16590703900d401c04c031100b2440001070b5407000d0000900246242018034400c0000400d00c80800d925400c904e400c883c21903011140700e5100042510401a03280d00c0342e83d2141c02048000034a6141c00c020402c4070400614901e041c1c0481241d0088401d0b550b400a0090400c20b908035072a19211307114100104402d040c098420721419900d901d00d458070120a109613050400154180094a40d24a01030b080e0580c04a03003660302448a51007582c030034810100c0090425403000883e041580c4003800841c0344a04103241e184101d20030801000d600d13800c80d070032504948420003280340014411107140c0c1280d041407507070240c40299038682d410550042004a50129214000155108080d1601c010034102c010102c0d00543d0041003c02d990080701c42d446000f52544914142158000404903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 592614793 1250 592613543 592613551
    0x1501200d0306080303060d080703032702030f0d051c0b040f090b180319031401170f0c0a051216091401080a0c03200301110a030c0906121112 62
    0x1680100c88005105a150180d04020408540030758a90b0a21a0214042c0080d00b40050541c82000614000f014030aa01c02d00341801314001d8402c440e4074441c060441d40000004c107902c24410506d124600b407001141180c100d44442d1190303450081c20b14000c4612418044a403d80325903a040480c0003034445004280d10490427650000700d031985864403150350503018001c101b17205030359060260510000400c542c0940100d5184640d500c1c21098100c01805d84540ea00400080110001520410900d01440d2002c041d001ba1a0003030010031109a03070b24404030f0f9055000682480820440c140b28a13a05500d120344815034055500b111181c40c480c10071940640707010303562100040b00045400d0034113030142c4140c0010306011440364031a10112401800083d28541f003400e80c0e134000e01d1156941909238100540240102611080141c40a030401a4a90007003410902100f86007071203016074000343e500e183c4500180e815800301202c000c0c00c5811044024040411801c40c41010045d40d140c41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 592616043 1250 592614793 592614857
    0x11041d36011406040e070e24030a030c0c050f0f040905031e07030e0a0e0f1515041703040303080c0a0c02060d090606050f030312060315040b0108150c031501 69
    0x641001c6051104075000031014015030b40100609003c5150b01003091034000710000d08e665102c00602d41c107070654103034400020764144030742da40100c01c15402418198030580100120109036a031081401505007107035005591000c050024104907181c80d80c840d1403e03900440c2100d04116100909407080c440c0c00c2d180c81071100c0049100800c25a03c644540c2c200304050342d5582505181c01116111000042d000c00070007240440003c4000b090180b600001c014010100100d040c800d60841400707900034000c10700541c0300b00002280003d400412501107940c5a5541d0266954a0a180146800c10070000c01004840206240540e07507482c00f410000c504050002203a403624070308641124001c0d84024001c184c200000e131501c1e60044142c1e80d02401d070f000c00a010b50707900000281003582c3e00440c580358951210038401848103100c80d40d41070390790745001c840c1e41300142c900020307121404031000e02d00550f0401c0064001a50200520301d2038506042c03036841da14410810034500c2d150b0103083c0c81 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 592617293 1250 592616043 592616081
    0x1812030d0c0c060f18020f12010c0302040302030f012d061d07081303021024090b090112020604050d02030f070303030e160b0d0504080d11041d3601 65
    0x43c4152407141940f00100803404001e240340c03020b10408445400c2d04040e22440e08401ca1003403e4541c2c41c00441036a5243c0000c009843c000880600290402c2c00168046e01c6200c1c011f0402803014422110172604080340d085807140710010a41f0401c540c81e11a10220fa2a03130030020b08405902440154003480600e0a4130614002000422461008000840d082c0c66401d86601181e00800d054100e11002d07200800d06203121155507070f83c05400c5420301840b5070b08000c0022403015560202d004030f1012540030b61980d984100e000103031410b40da0f002e54802401c2004002e01c2c1b503c03c0c0346490f5188044e00707450740070440f42815814441e17540d0058000c241c80d01812114420140455400c20044441001c8a1810901c10303170b415000f8441140c030081d5444000c0780070b02c1030810a070b0f900c001c10050240021100e00c07000e103050350442d00c0b5000780c44a40c0c681500700c80520000301c520406040ca0b54140001405481c200c3c00c59042105500b11110441c04004414082c01001c40b900d820018500c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 592618543 1250 592617293 592617317
    0xb0402210a120206060d030f0e0d110f15220e15031e10020c2a1e0d0201080a0f1401031101080702071502151501080c1812030d0c 57
    0x60002c03040b01c0501d20840d0821810440070342e4070a14841480740d0185400c110084441d041030790109450103c29a0203040765045004120001d9010640180c056421651140566080c005075a4014a1a8040d914107000c448600100f0015081025a406605d80d2100e6a0764402284054043c0d505001140c2c221543c08802e05042003421481185900d0b120003034007119901c562a1b8840045e03840445800203407402d10154200140740107241d000e28064800c01805801d00c00380c1c0c0c9000e03200c03401912420840030780c1340c0002042149510b40604000341c082c905a0045800313140007011588010390310301225240181031310031b90b80416a80d000c2a100c070350640c2440c1c0300384402d40c840d103410889484208000542d001c0344a80450340c00001000b001d12142000340e08286202543e0010700705050100a08000030300c101c41d030303030050a03210b08019880300c0c4645942c510420020030380410074220343c01f80d1070410008a0040011100540381852800c00404080d2800d0b07541440008440c903a00c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 592619793 1250 592618543 592618553
    0x309110a06052a030a08090111161203061406070201030609060b04080c030a0804050d030e03011521031e031d480414100f0509130b0402210a 62
    0x1408500303000c03c5002d0f024842c02650f19038901c5138501c4002000520f8004c130701419025045400480c00d880c4038a0345548140112207102d004110041c0da91208220002e9807860107845400140c0e16200c3d00404045003420600c5082d510100c005ca04150b81d40700005802c03c0c0a1040318060314101c6042941c903441c01862902d02125041028441d40202c00e403d00003d10881c21202150015072346807003a4122400c050b81c3e540ca0311001d0a030194209100b001c03000c4810320038103040e102d610081e1180010141d04040000c2d1601d000100456180103c101c0492000d40030b90350050303841d280c04900d14031980107200c1e406603001c034114000c0c1d00400c416482010004903651510f00400c1000d00004200b203080312196203200d01070450401c003881e203510380381c4541d005407001900400307900156040030a01645905620b204100d200f4101c80310205640c074050f810103000782d484140e09000617090f81c40c0e5802c0c2c400041d20480e40502c402890041c0d1b0207410700d11400ca44400e0000d0702903c3c110b4100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 592621043 1250 592619793 592619827
    0xe0408091302090a0902031312120f0204030b0c070b0106030b03030d06090506010e011404060806060702060a1706010207060e04050603150103200a080a03080901020d0e0309040609050702030a0309110a0605 90
    0x40b00028018010403a8070304800744010440f80e0031008120303000860650603602d2140418081200ea80bc00c80c000c0c98000142c0c0080080b284181c07600d40c00d85c6d40f04030001555004082008108a08000c01000914403a402826480500074140d0389040c9903200c14108650840e03002c000966100d4041140640c0c00402c942d0502d0004e0030411006c004417240003995110314042c0c241405113003c00710f502d644800c019200c0c4140c1c050400d5a6034001880302501c03103420f444020b00054440c1700060195440410302d0301c12075946441c0c400021810b1002c010240400601858140c8513140c00000c0005800c66814021400348031075201010000a0394000007540755082800340080480800c03c03a200014103000b10382c1c2615100140e910790f1103401380603115603100c0080150604da410311140d4000f100400741d8031800c4072f003084101e5a5001000a580c03080f10341c0b1025800621851888500035003194081610414001c0d441114031000113005042a8011500050000c110309161040100c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 592622293 1250 592621043 592621049
    0x60a0506040b0d03031e021c05012c180d0f021c0f0e0f090a060e060d0c290301060807230a0e2101020a1e08010e0408091302090a 57
    0x1802c0c0300344011000442c0b41c060301031400400f01a95002c1d40d4903040c002d0002c14405c2e68200c182907654460501c400c2c40380010911b20702103100c0c81e00c030000030406048506d5810b0b81d1081d450742e21030007030349103102c408241006059103011501c015400e02c40e100b0500a21a60590f107488440802c106114024030304a50000181c0d034203048070b40c0c494041a008500d41c0f40100742c41c5010700e070100d08074001c1072000ca1074203642c54002004e0010300100710841d412480071b645c1c3d201d824500380e90364141000012500e0044c041e10610a611040c05400c24000c02201e0141c071030311085403442c000441010480d80241c1c00f40740020300180c01c0c000c00c1030340b054040072944207a0180c400c54010704e8601c8a41362181c03c22030402d014206842175103544400021060650303001701c40310103421000c16464082c1d40008502d100141140308207003c0161031515982090344182d84000f07490703003001c0070301640e414040c00a40da0107030244400c0a00b99203040d08500c0101d221003016071200c06140c04d2000142c01a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 592623543 1250 592622293 592622299
    0x60f070b0f09100b04020d060603021c14070509030f07030b18031813060302060403060b0111060405150705070b0709090c0504080316060e070b0403021302090108270d02060a0506 78
    0x2051102d01c03000012100d4003000c03040000544000c803d00020020300c0751000c80582d540c107005001508a4059026103020108030f04400074404c1e000e421030044650b103d0342520b103000302801044650340306074007922200002404682c00c118089189502c0c0c0303586030788221120782200041003400401c0d0b80c1c4280300c01412100440c100612408040601d00c1400c00ba140500181d00300810907420703a8000c0c83c001c603006001c0c0c035511512030400c0006040c614035820301081c10540b40d1074480301c00042952040342c0200103880c480c402900c0d052050702c40640480304020003400320002064410355110300500f13240d2a400078242c94042c0c09070a035030750f0701c940205101092004001804010003100c9010211180e51043c41040349071000040800100a12091081590105810f00034900800640340221601181c44145d50520740c02c3e8440c0310311040c0080d411501294603034650902e0001e20303103c00c1103030000076100c0c601c50718a0321010000c00300040c0d2188080c030490360454031030315401100503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 592624793 1250 592623543 592623571
    0xa090b0702130b1309050f06221b18050906070305100530343807020a0801060b04052103040b0a1107050a0911040302060f070b 56
    0x2030700082e03820034450070281501ca85035039000c405561180f00c2c0090710500400208000c4c140c60800c2541ca110082100c002071240801240c444d45d0181003808183d09022196048880550341d2104d20900740100030040041000010410341c10440100e10b1400718200c2c00600707854012038007494448007600000c10f0514000c02c3c030007000d01d8010b401c0113030791043d2007508800c1e8403600b6400e001c0070303042c03800c3c288541562100c0a074000081225895050007030800c611419164800c0060204d010700424420403281404111203540c045e0040016108085140400d04041d0f4040140000400003c51240000035200045150102564000e0501034008000131070030103505003041c2c4501e00880e441007072a50541045001102c0c0c1c01451862200b0640740c54a5451208104a03000100018042109021146441c05c030009c2e4500490782e00602c0304001a00d00380003040140000c03040c42c0c614900c00c02c00440943c44d200e00610310140c01c00c400695619560502071030396800985840780e00310740 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 592625899 1106 592624793 592624807
    0x150c060c021501080609060a1d0604121211030a02031008120d0608030a0f05090a05063405030a18050d0605010f12080d0e01060e0406020a090b 63
    0xd4641c00c80059803182d013643d444040c21210901c3c1a4004400035003810080c0d044908810b6442c5940f030002100c5290359410710804aa0503607040850a0703a2290326a4880200c0c0450048002c4c100030404802c108400248000b03004100310325004404102201e410181510040401d40c045035101d52054a41d44929044955035090041c80c22400150400c000b00840301c13404400d60b165801e04c03011074030a940603000324482c2d0750030010b040d40c04281a240c8400a104d01d104000204868030743c00c0402980c20b455015031482024010584100010400003d032103020b402400c4c000503002c100158020200b8503540520b0b84002001211800c0c04140c1e0322540c1a61007807104032141584400c818a01c2c90070000c0001c100c0081000118440211503010544848140c00081406503403000041311441040d54203503100c40e4001540d020720ba401111220060403060807250078810 = true := by decide +kernel

theorem cover : BRFrame.Cov 592446043 592625899 := by
  have h0 := BRFrame.cov_init 592446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 592446043 ≤ n) (h2 : n < 592625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
