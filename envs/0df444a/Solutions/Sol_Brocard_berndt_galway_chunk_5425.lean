-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5425
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:49:47.009302+00:00
-- url     : https://prove2.me/submissions/c15315b2-5e0f-493c-88b2-182a80a5a8d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 975539568 ≤ n < 975719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 975540818 1250 975539568 975539597
    0x110103020706020c0f1f0506010e01050904142418040201030c2706030c0201090218070309020909031209060f01060f3b01030e0604060507090e0a0f0b0604060f 70
    0x80c442c141442e03180b44114000c0c000311200014617000d90020b0805c00f01c001c106862106c209551055404602003000d0400244055120300054a2000302c020404501c01d042042c0040c541c1e403058402c8114543d40c809044040c0141854035020201d00307482c0380d4901030300d00850300010107000c2d000904054031040c0421038244981002c45070600c01c1a40311042c00042c41462035001b0a038410580071a080110703038125030f4011b2240410050300540810303494100f09421504501009042c141450795a00e80bc0380582c07500c640c102d10594002004590f500c00a28482241020050840fa402e504c400304005081e0599400306d41110543d08180e1507088070002c3c140c0b03241302510391102d03000d8a032050030420b41881c1600044241c0090504078015410311004405480f14902828041c1d0b000e03002040004503d580070651102e5980b800184a940360100760709010b10a0b18143c242a4540c42e0000b83c03802240700d80203210400b01e0780345141c2454240b000d41a01c03100350030503041c0100445102607 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 975542068 1250 975540818 975540821
    0x16050f04090b070e100318170c1906050a060308071104020d020706020d27230f061e10030f150f062111060c03070c0b031909110103020706 61
    0x140ca0b039000461a01614242d003008003409800c105040c401c40e08441c044100c180644561200e400007400e4540e000303c40c03500e4000203c41d40707015141c40d045080100e0010101e0602c02001036410405a104c100615400c0c1074041c0c81010313106401f940e150107020000980c20718111038055034000c143e01e4440c103103080003030003d000b0700540248041c00054000e04000c002d13401001010135a4004000c001c0240d40801e100310241d00780082c103a44004007400201d10402c040c50603405901da80761400d0001840d40e0342c1050304000d2124882ea0200003440700c003900100c040d403a401c0304040c10003e54501043d501504c00362911014010880e418240303024481e8002c1c900c1084102c03c00b06000082e03804010704000d005901c0303960100d041940a04401c41d0112000742d0000c2e402c51181501c401d0308a04001d000d034840c03101740c54a44800c01c10540000e8101e0848001031041c0c0880b55100e02c0c1c02c0181785000307040c0c2d00900742e00e0341c6000d03640b200290b0340982107151036000b80380c0181c80d410b1507c0c2660 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 975543318 1250 975542068 975542081
    0x90c21090209130614040215220303050a0815010914040f0501080c040b0f091f12030810120302060a0b0604080a0b0103060e0a051f020403080a0315050316050f04 71
    0x94200d0194410444103a0f807a40c80c2400c80c0303101d21000c20603150094020400200c01b510000d602c080d081a0f0000c58001e0a009080c00c0c42810b0302940002c1500ca44040d041e440b46d5104a003c0b5002050005c2c65941146005502021890342a40c1044824000034100704880c0602039100000903a40d80590f100c40e440f004003031580c00340401080d42c40322031140e92203d1501210740300d9410100141000e050088103401d1024001d8075910030f43d103520080300c038030402610350458005c03001d400014005a1005a5490882c06a00c88a1850910300c1303560030f000510350043d03010b106a14032440000fa900080705075210b800c400d00020030100e20300000c0c0c02803107194070400d414410f050250003400311540b002d5040b20710517a404c1001003480cad80b00684902d80480090129001100e0212001031188442c0101e048403005c01850720b9102c1e60b914000c0d4004041c043e0019944501c1500218400c004900c090704040300103009505141061011402c594001c1e070b80030720141c4a0808058540d0b07045036 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 975544568 1250 975543318 975543323
    0x906090602060112081213020415051c02031207080703090e0610031a10021005070e0a090c02010914060603070611191a0c07060b0402030c0315030c030d0e0406090c2109 74
    0x168100340100c8141100c0e0400b05030312451a004112007041c0d954001c2b4003c64502402c0b0104100e0700103c2107280e50210201a6014000c0a140c140c000c0c0d0700f50700400084e4421071a494850607941001403100d40140c01c1501d10003100000e10a0301e076030310785003003070000b20b039190209130001d103d4000d03542518204400c60308840824a00003c40b80c021580701079071024400b00300040d41d0b8090003100d520065604454004003040410310002c00a40c0020000714058000804c2c00e1509940c3d0302084840408480d10a03007101e0180202032500b030100200808092411074001019050800d4980b0060b48c0322000031401c0e40024810001c8540300940c40d00c0140503c21003d1030103205001d0168002c03801180e030305240c0300365041c447c0350500c2607078001c0040701c3c6d4180c255a6000803140c0b2100f0031a0f21541d05200b03200b201e500c0d80e0b134100314124560307240f940c907521014a0703c01400159426500aa4015030038447ca41e901143c1c0400c103d130111a05c814030040c0c0b540c0380900b41c0c00501541a01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 975545818 1250 975544568 975544597
    0x13140c060c030715090c0519180518120a0e13020406030b0a0b04030b040210050c013617210106050a1103120406110903071401090609060206011208 65
    0x185504032030702001808009020342d004051003440f018000003103903c480401416400c86000500090031310640740a40882840030b9051095243d00d4800c8903104c00080780403255072a501000040311002450440204400004005c9107852000100d014043d0008000070080782da0388001296444490a460b11446203000710351b034540300d030030040c05003821842d410f000d03030708442d00052103a0444040780d088035046583e02115403200d03801c110042d501c00c1300c0d880401c6170502540b8001ca4017846038130b0001b0a15402a002500f00345000400175441d88a0100a0280005150301250641030000c0103030821030000380d40c91141c08405150310034450140041500d1080020400541100c010684c20210b41c6030018002c40008070107549204901e0304065401440007c140011101e03008084480184445c06081002c2d200c042840c0883c0e0394000425494021140b103420358000700410090680d61400140b4030b404c4c891301a6481c4410311810781044440c2403c0400d00c00c219045d110303030032440d401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 975547068 1250 975545818 975545827
    0x170c0d0821040b0103060507020a0512031305030d09060b0103111b120a020a0b180c0103050405030c0d05031803070f080304261e03090a0f050304090603080319020313140c06 76
    0x52603c04030000340000c9403c18030784004940b82a0001440210980d4040010150400e18040c0112a500007400f00e1b10510a0071140a001450600152500c22036010000446040a04100007910038000e181030600d0314204103001c1d8028445c1c1102d000404601c0d80c001d25400c1520114030304135080045455114012540440941d40843ca0f210014001c250b41c003034a840e1250422003030540c00c050814240d000840034102b550194000c154000e015400f134034108546070b045a03040181c3c0c01004000030700300200b0402c00100a000142c20b99000000450130f0120707aa1742c241c08203003840000b501022001c0006000c0241001040901d11030035583d0303480100b810322209000d030b009002080c1d060412801b429030010310641c1030300c1c42202d000b001402c00e6901525a912032490340d55042d6018042004080782514050295000841c4290703011581d03403800c2480501c8034040440281d0b20b0600400611448810b5070078520f1550b60410542040c080300900d5803403500d080c4101c610380100c03000c038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 975548318 1250 975547068 975547073
    0x30106020a2424151205130b400206160c090615020d020613020102030f0c07060f02010c0c0b09011d060a0c0305010b0d021b0102070507170c0d082104 66
    0x8000e00b03140c0c5005080f2554907448400c0f2201001c2e1462400380040c04050b07008000ca541c1c1e420a603000512641016010780480d1140c04000c442150030800d1085002445640c1110040410100c10313141c0d003148040c84056001d410140015000282c4a904041140c0c5c009845505071b8a4006a001c4461003140381c0d21340d002c5d40508014440d050401250811b902082d40c00495605200040c95001e805a5511100343c2440702e6100312060f41144030502070901d0700b4520b140107102c0b00140c4002819203600d070050040c206100c0780031060469040526188034190410808810681c2c002c401403519564609a01e0044c089228500b401d4960f4042c0c00100c45e10102d411402106640c405104644140d0303804d40aa810a1140b2040c5041c200688074044007a680074118122101000082c03035441c0d00582c13401da82100d44107680b203401c290420040d5521003400328699001c9500600f508c56850000540d088a041340c000d0310a8200050740d24440d4000745d001c4032000541f4081047c0c030708090 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 975549568 1250 975548318 975548351
    0x60b0a0f030302100f0218040522050a140f031c0e1b0a090c02070e040c0806150405100608060409020111070b030f01080303060d031d210d0302030106020a24 69
    0x2020103111031380c0392920300a403e00245c02160106c55058421411115251003480300505000705442d490803000501c5000001c100c1c0e0042c0000c5002e00010408031040781003070f884030f800e03007001030300740381d1150000540e8441d002c015500882e50720180c42d2442c00502d0312003009010740001180050044c0000d9070112101e60301f0a9040110584482a80603156849103040b502e109004001682c040721040004403241011554064400c00c4c00e0508140d44501e5285010020341c0e01d800081d10950311216181401d200d0300d907011544c4c031041e104d440d18115000e85003010150045000c0d0b5180c08180082d0390103401d80715664441c050484030300b907030354948100c425003060780c841440924480c00094402c00c0002030720300a0300000c000d1000c01c0c6481d40c2c00c4c0d891900a0312419018004a28121010750300d0308030903d030040503912034504488407414014184880b45e696441454414001030100396400101c0700c81c85a80603030380215804417a51b0204400c00700a02c007859650a1031861030b03645500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 975550818 1250 975549568 975549583
    0x5061507141b060708031b03041514101203111c020708070503121e0f0345011401030804030516060c080a0c050a050c2803060b0a0f030302 61
    0x41c40107030303040c40c00c0200c42600001da41811050b840042801680c0c0401c01c0c81000b1600441c651905544000d0b007079122021503001110241c4109a92407883c0d40040c0d05402000390450910b01d00b5140351500000410401c001030092103941501d150413031041600804403040c045d140041103d4054260b0700040288a6440300c101d00140070722003002446060014940c800c0c0d0301d00802418101d10485d0600e1507640040c0c4203c2c2e4100304408410020786101402049a040d0305420190b6a1903c035550b1682414041601803200c1e440480d80b42402c1784146c001010b08a410140c21600d403615500180034003124104240b4145954000204014518000f0021a8420001d80d4510084c01c50507044100742c1e1310503100030500c0d08287c880001c0070305006042400260034004000c1c030391900c0300d80c60401c0100d01100c01360310a00c8503507000d1424a00d180081c440803151680b54200202d21300400e6101407000400d90358440548401654800481c5d81c06803400502a200496407420300a564516 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 975552068 1250 975550818 975550853
    0x10e100b1831140c0304081b0c0f100f0f020c21011508210d1509150311040c02010e060907031106040501170a06090908070c0506090d030305061507 65
    0x400685640001c2c034003a10b14128080030b4922039035661003840794165400200100c2c1c40ea442009003044143c544031403c1100d61042009000c041d2158090207401410511040e104036446524500540d0744010f40f0000c0120a01c1c007040030712325114040e1f1601101e880c9455004454001400003142c20a42c4555218070300f00088c48420103043c0c2c0394228540380c2c0a08000d0350403640c034210040c0c03110320341c1262411092640a141c00c0018030504100e6844452100c2e08113803810381000b04507030b00c0c0942c0300c8007100e45181c215220b00c1d45ea58035030240c4044441e14041d586880f8000b580b28000e511207a0242120070955501d4580340703a10715224292800200c545040c04e2120748041c1c1017000c00d5906441041e118143d47c1034070190803140d000b000030035000b40180c41d21400300da40d800714007592049500c1210341a4954074140b07130124411115404c203900660b810710001545d5038401806d140d5071a014203000a02d80c80d8000802c038880e4547c021040540310001e41c0f5030402110f00d00d440145807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 975553318 1250 975552068 975552139
    0x703020109062703050a12050c09040c1e08090a210801060e061b010f0204091514150f04050915030c1801140f03010c17010e100b18 58
    0x35482d1040f00c0f09852000f10380c0028503042100c1d100000e000310014042d02c0e00506040c814441403900000a40d40c040300c3c440e0f40030b0804162001031b820503000e40090100982003420100004a01d10845181c4103d000d20401c100f200115040780000d0040b400c2894120321408007a8807a00420300c50818021250800162180000600c29100d0000904040c800618003440c203116070146500c100303142481040300755680c60f84840f5408051000b40000c1071851008920b201d0010102050030740c641d07100c4c149032200303500c11521940d9001d4100c0c012020b0104001d0b1512560200d100c4680180d4204503007101183d400d000d00c840b9885800420941c00f2411121400c03255402d0019034121350444842d0a04054010700100d1205c103490910268041d07e405007080500e0002801d4601070204040410341c200c00356828040121422400f415000100740150300304400c0c2802c003c0d241e44214039100d034000ca1009201d0030503550441c82d4810060110700072210102d10703036000e403109484c2400080b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 975554568 1250 975553318 975553331
    0x7030501031b2301020f0715020d020106081024030b0f060f0f211e0d14040b031902070c0e090f0a1101020c030a1209050d020f0f1302070302010906 65
    0x3015040e442c1c0c020707030b240310749400c03c650320100701c084194080504450541c010751044003415201044036074000d2000348818845001c0c600006400c0c01c00001000045904044050091910000e5a1816003500290003e0006030841c50008100074810030101c02c050300210002c18002c044100c2800340d084161413800750303154181000100080c00761050b8102c40494800b040c6c628040a28044968440724000b2810043d226024185103005004410300c4010000701c80c094203040203184107100300c0d418901e1001c0f0118030f41200e00d005511076201c031003000000184925401d100c10f80c0c0e45207210007003591500400e140c5540850400d014400030750180200081d9901c0b40010240c01c1b440c52040a0002100141c49107240e41c940410286c1c1584a00100003c0545040041c016110b0180300b06400c0145851002032091303000d6448140f00c1d00b40061841d0160340c4400006081c0035046404507080c1900101068080704242440c03440141f002ca181414180c041d042a01c0b4a449007131b081152 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 975555818 1250 975554568 975554603
    0x703061202010c0f02041b0201051608040308010e040c05151c020306060912010902060a020601090c0c20040e010e0307110909030403120203070203061006120c05180d05060703050103 80
    0x40032440a4040d000950b0000c0e01c1c07001c03c8521061040d21030014001217800026a0020100e40b8052066080180e6440d020403010403201400c000c6480c06905e450401c5051030f0f103008003c1401070080c901e6455500c0003040802040810b082c00600024100311420300242403101e441c1d800c41407150b00c80c058081c014102c1d20301a03108803032042400400040c02c01c000107082c071040055012a00d041507580f003003c1c10141e42c810340900840201d5500a04156041c1980c2c9420382d0300b0003140d001032146070070200c000240320310025400b4070050b8403541082601000043c019207100225454a5480c1c001c84400d4003001100a120542c050742c50600480207134810300190b02001c4a000885810511080c0001007100c00030403105030132071049a003803202580000b4101102a0707940343c0794940c40302007004034039009118000007a4081c0c07810000c500c05501c001d445803280400003003100e5000f9056840c1a42d1300c80a081903140c01c0070071142280f41000300500100703001c0c00b0544088090701d410f00031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 975557068 1250 975555818 975555839
    0xf0613140706050a030c050409110304022b060221070305070f051321080d02070b07050a0f140c010e010c1107031502070c031e150e060103151b020303070306 69
    0xc550040c1c0d50301d880c0504c2c9090440041c5459011003040101c00c00c00080e1140441c0100200a01610103440d505e040c036104100143c411444030300d000440312010b5004c004106920b49d4501e47d0400380240c0da446850071414540c0501ca221030b0300c512241c000b40980103905602086c07141c6496120844410180f80e020b42d0140a0811078010320074042d401801041d10005080100c400042c40c900e0b0442c0441d592003905400442c600703940c031603001c1001c0090007201a5403680009407410600d141810218000301401075030a1103200b4490142840230b08441010104c5070550f0a8200802c082d88030307c1a000d004c1c040d03003a41100000c118440540725003a0128000d03007201d0703104031355841c11409040300c1c0b4040c0d0450b00c4141c07580244840004045016424081365201c20310610511035440c0e840c055a4003a0089002510b40d407404405800740c12000070704d07a06503a001901401b12048a88441028003150b480c4440c0c51003070340700c00d400b81a4000000d1400703510151011b10000c2d855010040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 975558318 1250 975557068 975557083
    0xd020c0d030f0b1c051f1a1c020906030705061b01201902120406390311160f0f050d08040501050703030f020301080c09100501080f090f061314 63
    0x81d0f100511a40c07035001c10554a0012030040d109009648107541c40000c04c6000b50000c440c07601b00c0c581c80d903112146180e10013408072502c0f04103c5513900e01a2030054071a5580e00c803c0402070040d05400301150003941d08100240051500030940bc2d60780303445820345d50020911003000e4240d0340c01d1000c4a003120815000c1101100d07075035140d02d4100700b2444c5a110288000d0400c100550140e43c1a041c0060704010081000d000942c950898450354054500440c2c058000b006a80b0309001e002c007001d08400c4070070b0b203060b039402d403800c000701d0360040381d400381800c1d0280786810308140031303410000d11240398600c050100e400d041c2010158550f503601384201418400c42c000c0202c42c1c1000140303c10360048001d0710101c0d01a04d00010f6044000303854a04030b034401e0700080c0b86544420142e10f05490650f0342c243c3e20290701e038140900a850400040c2001d080641a410740706040c0d000103c0201d0108241f59039100007200300d42c010304114401c1c00c140c04202c00140c030320a40c80d18121800c2d41d00041c120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 975559568 1250 975558318 975558341
    0x51e030a050706110406270302060a121103041a070216151e0518010e180c0f03010b0702100807022d16091805030409110d020c0d030f 59
    0x114a009154002200e282c0e00c0154116803041e5a01d0b090b00c0b5500b0298060009841c064840181240b18402d80c51070700040700494007050f0040b45c00030303c0107860303141c2510f2441d8028109044282c3c20441d6141c0a085003000d078842d242008010030003030281c0307820640d2003120030005180c031a442d132850898840124285065114400441c100000e100c2801e040d44c407403c6070f2401d61000da41ca50807007100000b0040d400d00016802084500e031552a403000560401c2c0242040030409103031034085680002601000656019400d0026100e04894011540c0303040251148130350303942c1c44803402001908040070990042c816000c030009641d0003244441e007c0c01d400d800070520000d1504404120b82e210402220b001d40503207e6aa090752000c00c40300c0500c0340201c14112019040c40c003104200c502080b100d0b1003981c400013054000ca0000300441c0d0585640041c01310351001c2207a456a59449048201d203910b5100045004403d41c01042620b02e14205550600c00f50500344141c03006d07600071030400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 975560818 1250 975559568 975559573
    0x103141002160b060d171b10090b060303040f300606060806030d200304031209090605010305091e0c03070305010b1003090c180b1c0312151403010f15060206160f05090a0b16051e 78
    0x14003205c0038092010c0e020708130000e2203002141070400c4036688828501011580c0c691504018001550001d120550060055005250f01e1a04040050a540040d50000c10804c0c00c0403d0f02980c000c203108440140d038000a034803090f105c0099000304842a03520417100518905000455558400d01640d405103807484000c10800040484e29240c1c00800c0c8200000751041c100240403948040c000e45000714082e0b000000e0b80c2d8190403c4c02186009400030302c04040c5054030400005922004003002c1d00c8400092601c0400d07900425001404160329541d407003184c4140a10178240d0100080d00f03041e100c0c1c0d450740440412601c01c00140c42000c0e009044900d4040300c00e10004030315803e89124487c000b800803a0b11030000c1c0d000c004440d624152018100c036039184c02d104040c2c04004040e0080c25140c00a9040c180c080740050030b500c0349545030000c2060018224010365a0b1586510103071082c40c007d9540c481c040352142c1d400b206120700454403030180103201d4008103e9805118001d0b00440d01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 975562068 1250 975560818 975560849
    0x905160e043908130308040311030906030412110c030c041e05010801020a022808160b09060709120b0103141002160b060d171b10090b06030304 63
    0x41001070115800d584541c1c00d441d91060109080c01030341c4003000c04240c12281465001e0403001095003c00902103028501e404040c000046e030701540003a8055003529103c040700c0ca1070031200707041d03100d0340d480f09070300160110500080c480d00041d032014228964440808407101c0b54400c1d502d41d0700000310154540c2091104844609054015200089892002c422800b00003c0e0450444400b80c1041c0001d03035012405da10415010001d0810051f030050140c0300d03200d1001d03000d8011644001c0010310030038010503d80c13403804849041d8071425038410840700702490030401c041c0d0b60f503000b1212600019041200001c4e003201c0c0488800950b900803c03a251560709646a040314030004c0c6c008500703117210718070b000c81e480b4407584003604d0910305080e5650724018180c1000680140040c0021344103c014910b124001041182c2d9599104490070003180c8404a04485841e03144e100140c288042c0101c500c0c00c4400e0440f544944503080c0704451203411a1a8001410355a000790300403220114002c80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 975563318 1250 975562068 975562097
    0x33170906040c1503020c010204030b04050d140703031112070215130c1e050604030609110907020312071e0e040f020901080a1e1a030c060c0a02060304020a17030301090516 75
    0x3c00342914443c0b0303040252a0603015101e542c01c81c1c0c895401901c10000c07a4003440308204c2c090041d442c084850b0710b0a1303000030390000792040141c0305010f0300031705155030340481003140007044040c0c41503515103d640c1c0e40b0340d14107500c01030b4a421421140300580b692503000030708844140109802015084072102c001d85091426503040701d4140c011906020540b03044c00280359403542c000b4006184201d202190b980d00300d10300541051680081c1c0c3d44508110b81c2002082a130020a0381c0610616212030101910703048026100c1c1003020341e20800c00c00e100c850b50440d4503004007201c40d5000e0280d8080181400030740c0300340c08a010b0608140d000a203101c0c08622003082c2c0f074200740340c803a2102c2d10241c81c4808500c084002c8070064841141c0c0c103000c804003400103140620141140d10703070030303604145007004043c840b548134520100001c0c446c420100c081010f548400d22818007910404880d020400034041415540750401d206000115007003000182c81c00d00201783c00d02c440c00032900e0302c6007114580c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 975564568 1250 975563318 975563339
    0xf06041802041d0f1605030c090a2408010c0e0402090a0302060a03060b13091805060c070c05042309010e0307020909161707060201060b0433170906040c 67
    0x481e480c840401056600405510044c00b111310000b400d40020107481040310f510035103640c0d42c1d91006100760030403001541141c1f140c0032001d5001d980107074001180c400a05103580d44201040003950f0034100070102003100401580a40d00c008081d498142180c10785004200a91147c2c01c183c64211890310310400c0117082400c0a4140f144160402145c09038807034040f010140c0006241c2c90b02040f020008009070f080901c14140740c07110348440842904c5440d26501c2c1e480f032000d0070700c1031104400280078003845410401c100c00f50200400074003c400d020180c460590440904007150403044d600865208407051146070190103d04c2d0180d03050030ba06808101c1e03040002803002c002030280307107040e40001044083c405c028114060085003480c0300c0ca40c2c603a10f80010b94002401b507a1406400303002154640041d02c007140c8841c61540700d011030550208800712101100066079084c1103440450312504102500a010741e2420750110030342d1407c0005a84550588002e010300482000c20301117685103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 975565818 1250 975564568 975564581
    0xd151806051309050f010f060e090a050615010314010b04260a0209070903060504030c0b01060527030a02060d060312090b0a0309060b0a03051513080a110a17030f0604180204 76
    0x5541515a190005e1041c03a003503515040c030265040d1f9a52406220324409550890740140107007004000c1910780f40c0e41c070313961030304003420001903d1101c08414505a200f030f0400007910b001403500d80ca155075034286841d51900030303004103000008038251219460100309080a291274034000246405842502801041600903002c48104a084180070000c00e1250107294041d034403a98804580101c6030511421104068011004100003040b42443c1054591806010003041c4618016040c10440004e0314090004c04003d401207400701e40300000250703580c800c6040340d0050700140741c48100c01404a80303003800c600524690071002c1c0304081801c4c5c07103079004881192141c440007801030b0003000000c40c01e01090b0300031507690b03005070f090001c4910f0356400c142d0002522103501c030000d0000c0e501d0784940d004a140764001c001300d2400d518080c220401240100c5070f00709005d44d0040d10f411b00007054035030040301ca2850f2003040350080741c540d040510542e00c0b540c001041e030f540101110b03403c202c043d000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 975567068 1250 975565818 975565823
    0x120a1e111c140304210816050c01021b0a05150f0411150d0b0118030203070e041707030507110f06030112030509041d0d0c15020f0d151806051309 64
    0x20b08054000051040001c50286004e0310000302180b00c12071014018030310b01400c0c3c204000403102800648425030103201550645820003644800d1240e54050080c0501f010030308541402e022551074851b0f0114008400710b01a0b4180c1c0c1848014030200c0e100e490050b00d5040940c031110000030085005007814141c1414001c001e400041100980a0880d4100400440b0010350b0303041d00c0260396800c030180d0701c1c0302c2c0d1042505801580c69600000d4a46071207214a0b107104019100050400960714a5010104185c084c0c49032690014200100f454100c0c4004545101c1001000351151910780075002c1114402090301d80b55070300341148105d146c62844411000e0090500141d08559514014160104481d101510b00c0701c000c440501c1c42c02e40a03040090510044409020101701005041074a51018250250360307400104904559441807071403607040b6520b88241c2c10321080c40020700f08200c40c0c451405c1410183d00782c01510440e0190f1050b15440059502440303e06240e64010045850 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 975568318 1250 975567068 975567077
    0x50127060f170a05010f0e0405070306020c030c0d170106020613020111030d050c070203070f0b160f020613030b010834170a050d03021614120a1e111c 66
    0x1403030849400342e2000f0b0b145904915102c10052080521889544008185900c8400c1c1d141c01d00c0e403520391b220380d200e0101600c0ca503000510b4205000c010400c80c0d80a90b042c504982c035440740d1070001400c1140c12850f800a4854000000520a1000031094002c41c000390002042521980c01034410080c83c456442840c002031180c060b554200c0d1194510640100c886141c1d244454810542040c205070001103041c1c2c403a120a22450000c1000d07602c001c50207200c0344694290b50304011141103007840000b544514001000001c0070754a2400c001200d00c910300b203491590720742440c0d544908003201c1c00c11040502c200d5591002c030309581c1096150401c50100c80109480da02d1700c0d10315146911b8401c0d40b5a0040f42c104041100402c024102100c240c5403c500f07201d90148601e040a000c0b201c081c01004102c0c050310701c211401d200d0100240710b492026550341d003043c00c0142407030001007000c5603140304d41c84400b4699401050701020b0100004054404a0b04058201600455000c0c5200400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 975569568 1250 975568318 975568337
    0x61b240f0718090c0203031006030c02030313020415091410060c032006090304060906020c0a172a1504050a17191a0a060b04060c020d0b040c050127060f 67
    0x340756604c034985400c1034507409142e032403401d550925031441c440d600c544105843d00c608085183d50220039207411900340a08045403440f1400024058020800b010450320030780f52002860007221740c03001c816410001c1c2021041e0303440e00b4040e40314862a20624000c1141c0304908000a0310401d422030f0288106451300401c01c103000a031030b02d49801101c4011607940000350034000c80b900010010010f0125100401d1001281404604030740b03602d104811044515444071007500d032041c025594070690084510101c02078400c055400c4135070401c81c3c54002c90003002d41004242601085605035000a000141d034580380a11980c1d4420b20810b5000341801042d900c40001c0000216841d5600e01074003092002c401070403005c0e9440c0340003a00300f1a40529010041100d03d42c0d60302614100c40181c102101682c03658000700740c03120840302004140102c130302c0c00c101c00c04c000714030a00c003510801c0e40d410403450b1110301c100030149011000145800013940041004e903105229608048003180f8040142 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 975570818 1250 975569568 975569579
    0x906070c0602030715020a21090f060b18040b040f03170c030f01050616020f0d06090605010609080303070c200d03030c02010e0a0c030f02061b240f0718 67
    0x99030415004800180c000040e45801e1241c1c41701c04841c0c00c000103604601d480186180680804400c2d5508000c0c81910300c81c07030355030084a500103a91b090704000b0500020070586441d500600001a58074440d01300c2e60110181400c1d192007c611440c1d004049181c5620342d2303241d1410b0340300300d490300724100020741d000c510021040002d003d0013038401c8140f0640341e06240a103290300c10380503004540078210501000707007954810000b0142c06034055500a00301d06803071000c40c0305403c441d08050030090400704003034100036071540541d040f69441d54992101c1521281400c3c0c0720f106c1640c40400260400c1d0341000844d1850710090305130000c140142d0800b810382d201054000000180c282d0110707556480f980079458086c000c65a00000a001a004440c81c5654031015213074140405090506050881000c54039018216040403038002c0143d102810003445407640c5180030704025200c1508921170740c440b4a0860760160007005141e0078903000e540c1e030003c2101c201105160b200610822501c00040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 975572068 1250 975570818 975570833
    0x30a02130608100e0f0610050d110706051005010c060c0905041a030606060307090e0a0f180c051e01081302040e01060617010e1303020c0411071b0602030a05090607 72
    0x51841da1940711240c903000a2031401c0246551110080e81c03040701c2002407034183da21100e81d1180742210207400404d40704204480c9806003007841e5034420700d44000321001821803c0a841c986209020a014983c2c41c000c3d003003100785041c45001e0200d20451012400641d844c1c100411040b400c0c54640c030450740d04c400041c1a141d0b989e01c4840e8010603001c081445060902c8101d50190303054070443e1540c1400c0d8001050034050f8814416003c0c2c511001c00c030a0390103500903603c4040b04800038400401541001c00a08014010440c0c041c500e900c0002080d040004111280c84000d28061031100c1d24100107442d01e8a00030500400a116840008011f03640c600c5403c005840302d2b0000149282081c001500400ca001070488900f5005801003008920103061507620404240150007406820b142c264a170485c00c01c00c0035400b0741000001c00c4a80d00c804042d0810501030045800d0410311650880402031050203008016041000340c920418001d00003481d0401c2e025200b1490042207440e40c14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 975573318 1250 975572068 975572107
    0x120c1b031c0e040203250908120d06033e010212030a090209090c010908030909040212151e01150e0f060702031914150103030831020118061202030a02 66
    0x82e0344010241c2002501c61000b06c4400c00d22805090004100f0f0038151215910030380c0c1e82000c3c0c02c943c0001a200c07440360f5960817503c002d540c400b07440d251303258024115503100c4207034911224401548018103074424604c0001a521100d040c0c000d011f03126004001c282c86c1d50310040064556940b91040000180c845e909480e2040303d0450147c00c1455840c0001040c4e07140d194003180042e0300c28021110b6607a5510300d0317160000e90413a080c01400d460112060300f00074400041c04089801c00041102c1e40c415050008800c01d0742c0c0c40b4400007a80c0351110f5410079400040e030600001d142d030710311801c2414059010104070328010b02844c01c0c030501741d00007860041c000c140040c0e11120360b8450010842010003499521444001a28801c441016014180c1c2d40520002d000c00140002040340c00207000e40c900c1c030940308140a00e03003090265440f11001c041490040f4000f4a42c10301103d003045c0c82d0f030482c20135034402e50307140325403040c0800c01c41010703400c05000c51000c85e42c200029000000c03200c0c21136 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 975574568 1250 975573318 975573331
    0x60316120b1e130b070e330f03040b1018050604020408070b04050901050414041727030d1e080c0d02070510050f060f0d060e120c1b031c0e040203 64
    0xe4204030300c40d2400500d010780282a9506115141d401c2048940c3d47d080c0c00c3c202e411807081404038880c40c10030402282103801110841c46800050410307104000200194492405840a07101a896551020051840c0c601c5286e200790318001c0401e10410498210301c0e0404c500070000350400381c5400240741060f002d81e110091100c00090100079901b0040d501038014001198200801e0610b4610030130301c2c40004100a052880076000e49820349804010381e6515805001c409100e80704001440c0d0100b01c18040301446440f428a001d144c01e803241003102c200c444106510103568580c41001e840209010303080314035004043c403003c2d10380107080c400307010310501a600411410220200036000c03a41c0141c01140d1200b81382d030420080c1d03100e0f00d450000c20032081d694003400300c0c034a0030400000d100082c0031648038011500000e0a1011b0f26002e03001040201c0700341c56441030002c40345c255180e4044d51003505600324080310400898003070303003038116900d0310f003040030081c90b00c840001e0480c0d01c105c540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 975575818 1250 975574568 975574591
    0x92301091503090309050a0b1605011e0b031507020c010c0201090317120a020a0509010f20012415080403180609240c11030304030602070605060316120b1e 68
    0xc3c8020304d40d002c82e600b1300800c415a04124080e0800c402210030b417054040750055042c41c11442000c0040c03d5211181c103224448480041d20891041d507005001078907041c0b4072a01c2681d03c0d000c024200c3c03c240324015000c540090041c004041e0054404024810003a8184a0b00003400004916031602c1c2c08031210a0140056030f41000e80d04402c111000070341054141031041c015000b100740c21004450100c0001d0800085031440703e1004c68509071600407c6012503114061140070940c150000c000306120400c0b040089188107403030703001e19074040c41510000304400c440440e0480c01a41842c1d002402868103010044c95281c141d1403d01c4941d1011700011700400c4c080043d042e00c00c5c2c4900150904901202025020910041003d030410102a00c03904180500c00c160341d41c02c100300c40c01168070030f40943d2201d50a00302840146000c64201d40a40a4000c0300c2d85511310741d40500080c1c80140780c0040020051341c1b100c01070303800014a50304450041c10480ba00d00d140c100036661058990050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 975577068 1250 975575818 975575831
    0x111010218030f030a0534060e0d18050405070c020306040309030b06060f1b030903100614030105190c0e121c02030a091a070803040312050106092301091503 69
    0xc1c546005562028010343ea0030901020420541c000103d80c0f00c55140d03080780c06260b01c1c01460000701c12050003002d04a52045c130003a400c0003103a410010701d440946041d42e5000309040016201c0c440c01c60314020103262420010f002926040d0b00864002503103103001c4499001903400b10385014070a89090300840c003007400c100304001000b1110f40d44900e060312480d04046400130400c030315005591280d000c03403014440302044507100300252440b100000701110100b80000703c2c03110042c813090151030760112140080142c00d050500030540100300a08071507884a507108070b6000145000c8010301c080100d100540801c41d9521034039902c80d8001007000d0061455440b06c3c51500e61040d2207004199002801a0f840003030300f045441040752003c000803400e000000c00d52201c070f0b03c41c40354002e21805020080c8401d00da03001d284008101c0800c03200f0422039807107003400d40d10079403c1d11034503007a0748228010750440c84520607030002d1140181003420b8078540b20b10010f121203004114440010ba900c15 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 975578318 1250 975577068 975577117
    0x270e040501290906120d030608010e071505070606030c140108060103060e15030f060a23040203192f040605041e0504080417070f0b161101110102 64
    0x11441c196051841d880b82c030300603a50100580141c64a03071801d4480c025810000d0b21507190307094041843c540310307010349024003004503000d0b00030856405541025031a05031017035900c0c0400104442a00c0c14142d040c0e0a03c1c3d9000d07001c40c0d07030b9881507000b00c0d003698940d600000000c0c00030490a001d440707070f8450449010151400144001c600920080c10541840000c10403110b2569840703400c110200c44100501c0c02100101e8074101501c00565107502c90301c020850303100b0107a4000a4604848295410b0380070703200f248038502c51010395003e94150040d5000d00d03103043c200140644818811201441d02981c0700700700c650050041400c904890000d10480c81c4240350511035800a44804c0394100045020b80540d031034214405d82c1180441d90740c0b10702150a1154100a0b140140310300d0362001c800001002c04562114180d2040341d44000310004003203480c0b10070906a42032001600c184a6141d5001e403110420341e8a15881c65061094060101c100c8003c00e00007050b910480d90508014502c880 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 975579568 1250 975578318 975578321
    0x708030105040b010305100605090607050703051507140d18050303040c031e0b010902130806010b0d14060d0f06020d0f0e070803190309051e0d02061005060406270e040501 75
    0x1c0f1050f410140303000304002c00c03040240f51000035628140b50054450401001143e160f119408001e0414403842e4000800c0000004880e2101803142803001c0c1561100f80c400c0e14882c10030250926020001e1005c1c0b640d942203603000541c50442d01c91312101c407030b08a40300c2c142107074001d5500f80c440120045090060095107207140004002c541400f00d080740494940d90010702060040303814064000505402c0411940c150002400480e820fa42aa5070f6511015016a0050000041490402441c84102000d510106100344030203482000c68908994a4840401c41c0c0d0b02d0480d2015420700144d10946641c0c4070303020000280c403000090444000c00e91a140082030340c04002d40d0b520820100021500061081003081c0c0c0c0d030704000c01c1e11003081c5440390804856040c90107404200c2440c150760004001001d00310544281c0175181d80383c480c0c288010034103013203008251300854100310800900703100f219a803c030714640c41d40142d10a40301c41180015814a6440072949503071610511003480020b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 975580818 1250 975579568 975579581
    0x170c0307060504060516020409050d0c0b24060d141f0801090809120118030c1505070818160902040f0609180c110609010c020d020f0303150a0308070803010504 70
    0x11802c01c182480d25060006085124112808548081c0300000400b1900d40341c012415040e884400d65480409204000b841c1c1102e002060b1407020282001c11300da9681080c0302400c0e100c044454203190001c07507092050305e9019107010f51550b5035074104401c000240e0740d60140110a5a840d500c108500e0704408880c2e41142e81154115074500803110001880320002c4486040c13050f2002691480034038041401840004070886102e9400c0c1d040508040c0d21100003803005214404a51103c1c41000c880403c031041290018007203100200410202c480889800900500b03440c110307688480e00d0214103510802962000e0381e03858000c101400103010b84400d09016012030319085858500e45080d03080506c060380042c9025507a11a52455078500c00d03241424000c6907201201e01c01c2c01d0034030141c1e008010307011014005019900b89240e40301d1010903130243c800c80560080d030a60b2a100c04030325840c080b445105510005510380000020451000351441600a001294803980f421081c03000b9642c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 975582068 1250 975580818 975580829
    0x140f010c0501291f110a0c0f0306050f09120f0706060f1d0c07060f11160c23091003050610060f03110a08070210060e060a15020322170c0307 62
    0x100c003407608400281400f001150f040d134500c0d03c0200600c0004600e801d0501c0d19802401c1c110440380d004c40c203840400040f50071a84240000c001c255540d491044440f0400d0b40d085070b090b088440128101d55090303000e80240b10f5070a022600c1c04080c1d41e0766400310b50f071992082e401c8840c410300401a054040820441c444251060180c440c0b17808070900855116816004014584e074150400ba0117103a98021315498040054980e941c80c0e606000d841c4030803000b0821540e480704d8407008642c5448101d10030020105913580040c3c0b4a441070700700610900c00504042c2d5607940d440c000000302da81000b02038050300800d15031078203017400c102e001000c0c807000b80d02020038136052040d07a1120420200c100c0310351105615120000791a2040d0482c1071140c45405c400000d07042900105d400e24600301c0741ca005000458070286419508e5800d1415140c2c00241034003d03800038000d01060b0001804c04040018070184400c29094a607140c0340c09070101c440040b5440d80c0b00c04427107240b6080c200030701c002521 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 975583318 1250 975582068 975582079
    0x1020601030c03241d0f03090d060207140607050703080709050108040609031106150f10080c0d060806040c060f0903052104091b090f140f010c050129 66
    0x41c11501e4403101003800d880010300c05868080c040014a02d22803111400c00381c180c4041c4a03199004d1100e10084940d1101c02d00ca6014010582d9035010300081100c8100c180908031001300c2c0b81d152104c10080d08500c2c0709032040d010b415130300d6481840c28006a88205120744449131036600c20304000301140c100130b100100740403135560184580d03a0441c41c55640a030b4042008680080700d441d0403101c03480a4070403a0800e10960342445012946040f501041100c190381001c4190110001c00110909018070140850301c040003280300000000c0c0240030741d6234421000301e007056850080c50300c1d1560858094134184002d4100f880f045038820f802002c4226075140c0940041d0541d15010f440710b540d449592006420300b035007002d4881120703080c1c0c1c005100108080162841d8258403528081c0400f408100003010110041a403014800440055441c4070307510980b0701880d84280071241a00300f025505009120b003510001902c01d010707400c1d84440e8015140040d070031003a030712114022042e4200b403159 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 975584568 1250 975583318 975583321
    0xa1e05070207031b0b030103080d1409030a020f0601350601030b04020f0d0b19090f050a030e0306041713170a050d11060a0908040e0a0501141507030e010302091c0b06010206 76
    0x740c0d840086d01d0540c3c0d00040e120359030705490101640181290711040c0e80840c11842006000c080200150802c9043c2e5002d07500c116081880c221385501e030034020301384c8210b2603040e070016a84100c1e440060919080f1a903200061100815924080c2c099008940441018041208500300012112032100080d03d003150000055610b048034104d0091408403860080b1189020000356600050f04503030700280381403828100342c203195483e51281070701980450441042141c481c01d0000e1f9047c40b8640104010f210101c00801010a5900c2a41008507030410301070003013100c100100c5030040640c540001048041d1080c17419038242040180c0400a01c05000b0780a0b0002401284079580410190800034001c0c0130b44c5840b00c0c00c8d0250360401c1c002c0d00c81007020458411050341c0240e040e00c1c0f40b02e0042840d001900d00b0449a40462143d1541c1307181f05211400009016030b04035220001e05042c003500f049866000f107844242c84110340001032180c2101d04d400c1c410203034241d81c0c11200038405040389 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 975585818 1250 975584568 975584579
    0xb0406030612150b1f02010504110a05090a110f04080d02060a15050402090a03060c05030f0906070f11010f15030213090809270106080609130b0a1e05070207031b 71
    0x40800c1c0c4983c1129940c58220001c010382e1075003042a00d80100c64090a954541c50074000e0003010101e80c1111101d25481c0c0d001c0300d500e40300d540403040380c10080074001566200d004e590090140600360380000401403160044401c3e0000c094800b9100400040682c28480308009241640c00340c00036a005250180b03e035280c404400c880c2c41624425200540d94a0082c0041081080e81d40d1020b840685410341a81406038080c0045000d25500103810490f925001481a15a681503402e20041902c424a00c0525030040750013444c0b14880c1c1c0000240754021400500554450a007255241c101e0750313100340118902000f055030304035140c5100700035818050381c80072058400c80c81446d01c524041455100c0c0381c001d003908070054501c000c401c80c845d540c0d100c40140c00345800780c800340d215854034000a24200415100030500f0350b00844102242d4403204c1d018002403042c035980000907058108000c80740002c50042030300460720742c1d00401c0302c54a9806e21049a1030545000a160101024104203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 975587068 1250 975585818 975585833
    0x30405180429010b0a0507050303011d0915190e0a08041d0c07030309230c090609070f111203100501030e0a1736132003041b0b0406030612 61
    0x190713903130003c0d40c69486041603c25038a074020032000410a200010010424220079846080340c03080644050015449840d410380e15040c9100c1c02030013604588000071100814881c0d04946001d001100244641a2024250400340002d2064030326040018041007a640c005081d0304600c0c0b80e00d01c54100c142803584400000c2c0c410401c0140c1015114050381007805a240482c40c0e00401103030045074111100710b0056228a09000300318031480603103002801e80e062509070300d48518041da84012110b91000f10540304480c512860185a120392a41c2852440b1140001c40c0100203804003224418a088001402d80d03840c0d254071081a00030410140010341c20300166842c00c2c0c3e480c01e4440d22001030420740240702c0c540f01000308604002c4810704207141141150604449006d55100114220f201c0341e072015a0b2500b0342038501ea03050041150b001c600c40101868000d0f1140885415203100e070750031100c150800f900041d0703140900090401c1026014800e69006188450011401c06480c3d200c3c0300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 975588318 1250 975587068 975587071
    0xa1505030726010e0601032103050f040f031e110d02070302030717100606050306030114060303070209040f0803180c0301061a160212070e01120206091002030405180429 74
    0xc808500240b0321803010354003904002d8840301c81108603155983e4034203101c400141a21404291021b44085e030b084418441d0090500c00c40000c00c0002590301e0300d03501c0302c14003c41600d094007007122240311104001d050700008a00e502d040d9170380c04c103050b06841c00c3e1400c0c1810340c4400b80070341d4081c402c1000140c40100781c580880300341c044041c60550303140d072046043c8042c030f4855290641c640341d13021031419007243c0070b03500420741a0002c00c4140c41740044102c0070501a0f888591652040c440754005140042ea0542d0203480307060351009144050786c4504580e002a0b5100d03419809100080204010070064040e0798042100240700c0b0303529010101d07100009a50140701c0325000000c08882111a020074030100540c054140c01c204c1000c440403d07140c0341980140d1680741e0392074000040a100c844801048036400a0186151440c62010040c251f0400003400d0194003040c480020281e0b9007140312180b90601c03091411907441d280c0f400145c221079003003400180300344070003860800300c0c103180805 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 975589568 1250 975588318 975588359
    0x1060510210b190e091f090305090d0c0611150a0b0d0215360603190c0201050604110a170901020d0e0106050a0b1602010503100b030a15050307 63
    0x1a0100c0d9800e40910181a0040380700750022482602445100342d104801c1e0f00321203000d850860142c5503443c0d000e8460490383d840d8844481a900010461070b0b0590101081b2482410034914040d80840450741641d4200400d641050009008001c0b1396005403181454a4800003c4d1094030103171401860003250182440d8541566898072140a0b12551841040c080e0008c15240d980c1052103e152070580c03024001209807040145102d007045003482420340000c1e03401c480c10080c4ea210005002c1c0d81e80008018420114040c1e00d0815a0320441c4603248203400c02e0360010410703203444828807081d551403d2211028840402121a441c2c0d40710700d034001501000d003071100c4151124143d940c068018102c0810984e4a80117a02400e02c6d015480041114001c3e91421400c65450388480700501692001100c0300001328035020056215400569105041e4006945080e444d400d003169250421134041c014242d844c080c1002c00a200300381c0c01c004000480c000c04d0381c00d0901c501d08120440c04100c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 975590818 1250 975589568 975589607
    0x3050106020d08160e030102070501050402010f02072301020c1203030108010c050301080318062203050d03020f0d09081e1206030303060a21300f050316021c1101060510 74
    0x484c188144543d05101c00740340700500030354036003c1d1803c00358000c1200303071012408120901e040c1443c0600203d07103607085485d0241981402c106203100060010341d0510300604501585e10100c601e665800030209aaa4446000b07540700d40c10640d005003107034060300044040c0304041c0010018600000100d4031640065180f000c410789141c8003244550088010b90003d41c1c8260401101111000381d005003164003400032901120845074081c2e04a206600c060001c81d9400c10948040000035002022100d101ea0700613840e04907101c0d00c100440c101140380098001c000503120303e41e45411000f0700d40200b011000703946542022070003e06490350610076694400508500d904d03142c02001c003154801a04000c0c040000110303d8400e42d6854000044907100e552541029003e03580300c1c02ca4003a182401c1d4580d50300d5600c48007503010348208100100411445281d40300103031820015003080190000e502c80441c0e0385c00300ba01850940350705401140c00f40d07c00f030840042c45070f40601ca400801503e03245 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 975592068 1250 975590818 975590851
    0x6071b091a10230c1506100c0f0b010902033723040302030c120403030207031e05011e0c020303061e0604030c12060b10080a050c040f0b040603050106020d08 69
    0x3501c4400c5881e100c083c0c100302d49108080145031100c0101381c140003a0b016039440056003078003143c8400064403003a80040d0201401c0014a0140c0070a40c4c001c0d00071100940300b10201e982e111140c4100340c100b040420b4000c400d001440481c40c07645441c030280d2000030611500c06802ca0500e020b00785c44001007054a40d9065801411040d00504880400c08051009480d050801035520b07070100c0008000f034070441e8006404008040f09403015079915a024001c82840d540f40d1031180c01d14080b505500c42401d2074520009a0309218107490041501092840c424020025104036111001d00b8015900b00300304104265030f4608000d0319811221190b13030300e01a080c5021581c2030081d904003c040401c241804102c41c28003101c0340b00c40500c9040b003408101107001c280002d0010061440c4081360000740031a02060664000355400f028000030303581801c2d5100a00716451030142c1c44440b0400c0001000e01c80c013130785809000d0142089000078130340800308000085c10070740020b140e641039100450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 975593318 1250 975592068 975592099
    0xc0b0c0d060b0408060c040305031602060d1b081617091e061b040501050d0c020319050705070617040602160c03150b030106050d02091506071b091a 65
    0x141a211914900039040001c80d40340d4049810302c1d8401e0155840e2441150005140d07509290205c03030559520102850a140340c900c1c1031085201500c000700d07448001409503011405040c45002d0360808807a8a01007410244007010b0040c00001e0520300c00100b1641001084a4100c2003004890141507543d1241c0e40c0e071003c000c3d0800d56184421007181c4e1980610090b04200042c13900e003c1c10000013040c5440a00d0318000b44907114911809001c20018003e00d070356100350358454035a142c00390040e40c4c41e100d0920505000d000c04000b1007800300d10081082c10030701c00c080080c1d90203030404d4181141d00c4030000c09070507040740000704010303d1180c00066204954021107002e81265138007480708400d203901d901d04038504115034006510040e15040c54520580313014000c403411584003401501100380a5002d1051940004003411103c032a404a9207926482d140000d004039070041440d41c190003c3c481721038402c08180e52103071312428102242c100c0f03c5000070a803c80250340448603200207010380c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 975594568 1250 975593318 975593341
    0xc01081801020a0203030108010b181306090b01150809030309070302061c0f0606030e1501090e070b1b07080601080726060403051c06260319170c0a0c0b 67
    0x340e0110032070350010880c44281c90b000000b840c1a00c1d80e1400030701c224403501c41841062008400c41f8442c21003a4400714050252010803001114010040403a00c940d50381c40d2340400440aa000700c40c65441c05800e00c1d0b019502c501c144e9000303003645010750700e9414550310166584000d400042d2141c0310000d1602d80000000b440b0060000c0480e505102c00140300c6009001400b8601c99480440d041004011202c100410080c0710088030700c1a8001e580d08024640c4014403035440034180600c507a000224040e4920809450780c10086502d071840c040203210300714100344195108070903540c00500180701d0200c0202e200c0090b5420300720b40e518030010005c5400c4041c49010340420242c0240300501c810700d03034400000d0001060000100d034190142c206003c040781c51300d210f2100348100380c4030482c1c004020000600312010b030003001c0ba4200129440d044403100d80c0c8032510303008600f43c0c5d414550b00845425105a215241e1544141003502d415400742200158040040030003010720f002800304104c6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 975595818 1250 975594568 975594601
    0x8030f0c03120112021c12140f0c01052a0a08060117041b0609260304330e0d0f03031e050406050622021608070503130e090c0108 57
    0x8541d045a5035101c9540d91303c00301c688003e03809580720506842c21491440458a41c41c0e81c000c840212504245004855020721140010403602c002c02908810b589184080c040401e01c0000009a60a0050348088440d80c841c202c000400c0c10310030101640403946007138640381079250400c208669115001213520503031950340001d4a618403000e00044c003120804403508110020422115191100810b903191402485100c513150020f41041011007047d40207001c1c0d280e0300d03a04032030030252941411143c0104104030458020b881030011210909815200d42404225003407200c4c54200660203d107510040c00740142c0000380c0b0f5401036040511903401520b95100b56102410003100e40c40780d66000c0d140c142d80c160b405a0420000c5992072501da42c1c40c40300c3c40da241032410781e45204a01c031030010350440c0f2503080c140745500301c032a0003041100000b4040903201e5400742d82d45461803142c0c030401d08000c1c1c10503520214804100b00e860381001401800c1d40000f400c1038071082e0f448403072100a80d0030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 975597068 1250 975595818 975595837
    0x30f090b0a0c030b060c25151d0105040513021b030309010c020715090608150406090902190311040e0118031815090b161703010515030108030f0c03 65
    0x560030100808800c9540c0b10040c0404141d40c14880c00b02000e04010031401420307802ca074290883c2841440e4820228600c50804258004403885a5668a107c0000c1740740406441c1c00b00b82c0342101010032030038032101d02035089024240385040a00300804601c021032044030035612a43c0c002265a00218854195004800c042e82102e0f47d17441c1c81c01c03000f0302a1006038041005441042c00100f0142a0703c8075030640340c440b42c0d0b51a50301500d040003c940601000d0500c8094104a004c0074060343c6036070041001601e0f440001103031040061040c08440c89182e4504820524551b100303000094407061862072514044501041c50b5103070040941c0146a100d03502d0722622400c211080801d508090f0059442c500081d00028040e643e50b581240108a0006600000d9500344140405a2008080d000f20b910080034044101c3c80b80d80c44003544a140d444806820f803020004010070324101c021f5802c048910303200c8a00b154504203825540307003c0c040103155010300121b501658404104181c890300c0b00d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 975598318 1250 975597068 975597083
    0xa09230c0d020619200606091315230c09092d2e1a0a0e03150a1b090909110607080c0d0509101d100215010f05060703030f09 55
    0x140c44c40c0c00586565600d268030720710b50309140c0b041045000b02086081c40707258050004183d680d242d40740076074468000b008c202d0b03a48188004103082c0119501c2216038007032441240781c150042d80201c109480d44014000c07003204000304140c407010b4440d074142d0390308042440790320b004051140904440e45072210b1400c80c804a14081000103880c056800c104008040814120708055080c8080254010724049d00c1c084010144609410040703900081c1158912032401c450341311510300001c0c0c01c1084103688283c40c80310b02014072002180c2441041008611000c95040d018800040686001a02c0c441d01914a0340c0f414503005121032940124041c4030010502c5559070020326040045400113240615148900c0031041e0b00140101c0455050290050402c8000e1940a50403505500301450003040d1220a40c030054054841842d02c00a0041d503030040d00c059480201e903800048016440615070700084081040181c407070404860307590742c06150100b85410b000c00078801400c40ba140003802c50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 975599568 1250 975598318 975598357
    0x5100303172703041505030103030504030f080706060e06040e0d0c080f040b0703090825030609030309170d0b190620030415030f0b0603011412060a09230c0d0206 71
    0x2c1c00c022005009942d00c0f0b52290203034143c428800c54090009000040108404120a20200b40d1082e220344110f4440c1500c1840c121083c2da0701016a582a40080514002e004c10b06c085407a00313001d5040000c0c5018003c2003080c5400c04010321100d8180700150032441c00142c402600301c0c01300c080314050f00e002c03011159511564a0700a1095206200c4d950312402030489642c2160000106821035200103c03410301c00d5811911040018a01d00344103c1c00c5c1541c1d000c040000a060505002180f2680a11079850302d0b502c0441005581400b013070540304000903d41051284603005018040d10b1441c540003048880c520b482405a41d41c65075456503d12020400017645480c011090220300c41d6554240306581511107400b082c0c40485121035400340050005000c030194002222181503070003030401c50f2400f83d150f0305504001c02074a1619040fa1500d03440360610150b0140d150705109100301030780c0c00c14a80c1415948034030f8114103c40c03060035406040e00070b45d65140300740d5505a03038100c6078441c003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 975600818 1250 975599568 975599641
    0x120e0a08091002060105100f020c03060a0b0307050105030c0706020309070305071517091b0f060f03040201091e030204050c0f030a06090b0a0b0708070c081507030510030317 76
    0x1140c01c08080244140400109814010f10201d61a03040394409410398101d20101d000c05d40c0c80307070041c40b1648214450a00e24a00913907003002103901030b01c00c0f6040016140c1e00d913000c0c0360810310300d03800250500000308180301d413001c8031004680c65640c00440068481d19103c06085c02d10760542e001a040348102b41010440c05c00410096448005035129010401d10244c54040c0185d4212080482a08003082d032940c18034642081c002d90000c007c2c40701c0450703089030001a016401c140100c100c81c20004c01040115600113030120084c00c40011460707101e40da0900007017081d0f980c034000240596255030110703d03401c1903481a286141100c0340f485459140c0012100c0042186224030803400d400d109000500d03043c10070b00c40098565100b401c500c1c1208070b88407030b191503005140440703020301303070150001d0040001d0054111060409c18240054100b11000a059036000303000c40011008022040002a82181c0f40043e04122680748400c0c0340da8141d40c0910403084081024418010b840d1901c55 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 975602068 1250 975600818 975600833
    0x30f16060912020d110409030306050315010f0b07030c120c0b0115140f0d0608150a05190906140a0e06010b0408190c03051501030b0a09050d120e0a 65
    0x428001490201000696508085803641110700c580401d20200301c0d0b000d4050f0a0a160001581e4020342a2440450035080840c045811017442a030000340d46070810711485c0b40c184110000c00d0084070b102512035041c41c1511a02403020306c50300801d210001800c0741050b0003a425a1000c0b48c000c2c0c00c18a003003956801c081c0c81c00a00780812035055096200200f0940300304000c90f481074040e40c1d110780340324010a1071030342542d118110361408420288000400704030903029410280c0050070144c039080400801124200782d021f042155228103040c100680c090038004001070340400e0403404529840c1c07a0401038002c1078802100c40000307800d40204a54034803150012030207400c0150864119a031b94180c410903901540c00b0750040d50300721a50006890460001626500d402005e05445180e501e03600c10307141c44004d185070240c0102d41d50042040c40070206440b540039018840612101c1c43d00e6950688400f42d886065080c03291000490340b810b5425480001c0e205c44030340840d140408542041d01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 975603318 1250 975602068 975602083
    0x403060b030d09060203190207050901090915020301231c0804060e03120901210203010321030b130f290f060a08010501050a1412060301060602010c02060402060304060b030f 76
    0x5000703200b00500750803079512541c0300f0307422584140d000d1030510320042d0034011940c2071f9013410411441504000b18440c1c1e50000c14500801003600b001514061902e40f52062099803110000ca040c814001000209001c0308241440c9481040c1c11485004030f00000c2d0744148024420103469968040340410002580020701c140e030141d85039854000c440030304144e541c4050415985186006001d0b03009954015900d85071154415020901203103d06940d1034201d0304241d03c20b4641002003280d0146600c55218091110308603483c00340301c614210804180b2a851180c0c20030200380d50341e8001c0c3d04151596001d2a9a00204407a441d070182500b10840d84c8040f200040a00c1003010b8150303042ea902c1d055085402c84140b036201e0040c1a8a020015580c5400960780801405420149440f150480344002d00c00c02c00c0303070400300b9098100314050608440c110342001c01968546123060307804a40001d8031301d070700c25411608143d40b6501d500e003100240210540480d01407040308a0a40e005001007602c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 975604568 1250 975603318 975603341
    0x81009020109140a18020417030a0818030a0f032403020f0108060a18090206070f03080a021809041103150a150e0a050411100203070c0e0f070f030b06040306 69
    0x21802610f4004480030b4440c0c1522865000001d000108150703030390780303103440541405200e0050805684101070002414240d10b01500c07030700700040070b516142c3c104078850780018514a04d606c25894aa50555032813252020302011f0041e40c403400384507940300750882e60003403030034080e840b032640c001540900c1140c1c09804103c0c42000309510810195100d0782c4c50b10f00c900340c0101081c010078904040000d0701000b440000409944840302070001d6200d2100400d0590320130001d0b2075401400d4180286040c00107090038403007d00400008030700505c9a401c0b10001002118030340301a454a00d000c01850005543c0213815020310444c0c003a10054038400c66209003111101405424032480e00d5503403c6070a4055005801d04000200385500403a6102d241c0c8284a00401c00e0301d101d80d100002c80d91103e80d00a100164000207404042150910035900100702041c038800ca1403d0002a00d400f0b01c000030108403c1040c8072182244aa100c1e404c881c0d00140040c3c0101d40e01d684a081180203030200a144 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 975605818 1250 975604568 975604577
    0x11010f0b130e0a15200c03040b0315091602060f0402010801140f0a0608010609081f3b010c0206150d020118090204140f0f1e0301060e1509130f08040810090201 70
    0x115405d81c20707404640b00b16241e04003551801d42041080700e0940c00240c1041c0c290402c01c00b1b040c65a0300c401405500461020003035000a803510b45000b880c220000701400c60041080081c000142d801140c0e240c151000c0c04115038410418a003c1403c0d520003101c41035110220050008119401000c3c0c103050f901c140d81d412060381c0d150031002e9640c0e0801da6100801d811600d088103042c05c03075603000b22034894a907440b0380d15000d9400c281410a002e0a110004900142c01c091380440d0001d108503414201d19002500c2280742047c03115104080c07003070303a07039004100c032500907011607101b9409e803181500075503241c1ea002929041818006c4d042402550491420320094071940e05d0100059040c4c908000c2401ca0140c80c1e003401d12180135400d90103000302030861200460650780130700980000e854803014200851810510980c042031500c0b2040d4016440101441003206100c00d5121101e50881d903c58040782e02880d000350944140d620404180c02406901074203014986c0006464034001d07a034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 975607068 1250 975605818 975605861
    0x6051503060c03191d060916081005060f10021f021207230c061b0a17060607060c08041a060f0d0615030311010f0b130e0a15 55
    0x18541d035404155080b1400400a100084405003058003005011318903c0700800c902c518004100c602d5500c201a61495801c400d0070028040020010700b88d10385261441410501d20380891152a0300c803418051000c241c80b500010080d0b240c80c030800d9041c482c0034020b841e01d0110010005c0d00c50300c184901010041c400a00c4841c0580503000b5500000e1914112110948400d0019503050071491102441580c4040d030031102404100b020700b0004411307801504040c41c225602d10a4042d00c4510410072030f40520040c000c195000c41005401610692006c039252a410300050007030060301e03802808a030400c0c041d898626030002e1003078042c5116044020740c02120b88508611008211150b90b04466020848600f80c40c207800c910000383e00070100020305d1000011106104c00d06a00240c0c04103070240c1100f040303880c0910960042c060018010404043c4810000f03083d500e030240c5641c031050700e481408040f20424003030201034030f600c00006010f0b5001c041d4201d010b050100030685004490700c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 975608318 1250 975607068 975607111
    0xd0807140f0f0d0e09091f0b04110c0303040f0f050604030909050a06081b061b07031e0b0f06060d0c120e06010b0403020d050f0f0717160b03060f0d0605 67
    0x1d42c00b900703e4543d203440c14011803003400d04c164400010000c00c1c0a20a902e1301c0000d00c24802d101710400070000c10b020a23000f0070342c0280019140224002141074004001f0b070721101c00e011080c0e031740082c1c1c4608060280201c9040c16138580c00c0c0f0800180c2075004800500040640106828046800484040c0700707659481c5010003c489040c843d8107529042070f150b28212030039162812866150043c1404c1c20f043e460f0244400341c40140040d004540c4c0601400d009200001d03183e14110504482400c14003103446d07884110044000c0d0501c15107414210210f0a82e03503030300017590318860900c10b0400c0200309440005100d0607811456481c12440c1408800c192040441e400707050b242c501d07860310303c0c1614560a104181c1c2c032800003603442d4040c061110503170722000c4c800112000011402041c1c010706144c4041c49800f1044100e5030340307504c020a120000c062280040c0c0441e00391048040c1c1b21341d60480803407400079103411503c0d802030010b0394910420204c0e80c041ca0003100c683c88800002d0702e400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 975609568 1250 975608318 975608323
    0x210110702030a020103020a021207050105180d0f0f1101021602090a0903020a0210030603141f02121305031e13120308040f02040b120d0f031a0d0807140f0f 69
    0x40e0806900b5401802c000005540241c0090104188070710450301c00005400c6480c0090700400360484d0165102c100307006c000d030622003032584907801480140c09003884040300600703501810111704040c00b41210603e41c00c18001e04006800c2c00a00000350764032513880b4044500101e41d4039040780f0849441010424985aa00c216040698940c005200e200313805d4081046149034015000200f5485490200000e0601c000b80700e050441d85004242409021910304510140017440403183e504c188221281110f09200150308080c0700480840165414241207045104080e42c0d10008003150b51800441071044c0010807000b10081d440e003030102c2c2c0b100d01c8007074801107241c0082c0c000b44c0b4040104022500c4208550740301807008100040c9003400c0c80100e580b000e140040c2c51800e4101d0800c0340d61080e00301211659072081468100701180100200100102c207200c2181c0c00b034100b09007407030f08210521085511254014203050190074041822603a1030f0004484403800b0b002e0b0b100311100901c1300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 975610818 1250 975609568 975609577
    0x105090106060f09090f0b150d11091c02030a0501110904060b0f0a080c04030f140d02060405071217070c0515040302010e060903100504030e011d1005030c07080a021011 74
    0x1513548491640c80c01001101034142e200c60031a15a40e1690175003030740e6543c0105184141d80e04060700340c44200300d00519049419001c081c4e100d402040008174902d0751204001401c01b036010082088440c03103800440c4c0b50510b8900c008010b5884c1880c1c0c16a40740c031030030203040540c070101c41c2808150740701c5801d42014010001c0c2100c04200500c8483c492038001c20b41c041d44082c1440001e400c00355651100500807a05003800d450241240041d12540d100602c5401c80404e014002072119041540c1c030f150343d81106220301403c10041d440c40d001041100610351520b10b068051058450341c00b404c15501e100070724402d09105180c11960103070307902003100a44d81200d4058444003040720503807050021552003000c140354140a40c000507120800d40f4400c150040340281d8030f49071001c00001c0007418507840320103a43d41c1c03510a41d400b8074903a42c1c1d800c10100c450140b8500300d07481c2c1c1c84d0f801200b4094010b8120042c9041d40214030032001540c0050f45040d0f031080782d0001e010075184d100802907580305 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 975612068 1250 975610818 975610847
    0x50a120b010611150703050a0b2e0306030209090304290f18100903060605060c030319090c06080406140915091612060f0b010504090e031b010509010606 67
    0x1180401006441e000340c2d0341c0400f030403180c4140c4d01006800c040c8400c88000464052002ca03680d02c05104143d185031041d000d11810030303108410100091401e04440c007000503c0c2030300c419040f036040301c00c0d240300740c001da0f0045502030300e04d070620704250b900c03591039801500071182288000c000e424801c164081c1a1250400380e034040500e0b0100c0c08089580c41e03400540c036200c1e030703981074402d17a519912a0340716102d2013949980c030829064294034080055681d982c3c400d03881400d091080658403400032089035000204504403080c036040b04503107038029009520001d411038034440c4c80051015040700e205403055210711400c00402c880d50b020603400ba101500c840d9020b602c0364003055002d80308410710940103c500011982451101c0e154200d40c010303d80c03c40342448402c0030020003049000d0161311852901c4030320500c51140c0381f0b030009125019601c1002005a00c8086c4030840d00e8042c02124584003c490b58200d0000c0c00d0b5051798080d10081e0b9810006600c0c061001550f6031042603020f802c4032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 975613318 1250 975612068 975612083
    0x4120f0b07031503080a03090b070e19060207120c0b0418050702120405132702030c0901030f020616080a09080f0a05061803040b0c0d080109110313141006050a12 71
    0x1804c5444481c0103401040760041415a2480a100483c4116507818032401d540c4c0d5601581c1c15020b000d2068034140c400003010550092582480600d40200d0000241c4100391414000c058003410080010040359003c49005000040c02081c030386d41850786812411050081400300f03031100b400032684e031144260b10100d0724205000a00092a000c01c1080ba4140409408980c16034039081c0c12002c10800303000c0100010300c4007801000c60405100340c040190701194079003415803460b100c04910f0f01e0342140080c4605000142042c007075001030b860740e241507000341c1c0c100d0b101c3d0f03590300000c0d00160107409803140d20b200300c020194840300c0008203166a1036004010340400e840e0140c04400701755407201040c000b400700340004110070400002410501300e00c04002c0100b054a1500034015090603009400d07407034242403560310010769210450b6002120003589044040040c1400b0b062400c0c41d42406178140149401c5481103641c5030090001c0d100100c600c1c0711507540c0c5020000c0e08464001c1d0081111 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 975614568 1250 975613318 975613361
    0x110609030901030b03010e12030a06140a062007120204060b07150506010c080f030a05180a020d0c05090f04060c02010e100902030a0b090d02010501120f060b0604120f0b0703 76
    0xd510a81240701844d501034008122240c20350f03009403c2110301ca4403000302c24000b204000c1c41c400c490166000500241151f2890b080c1030001103006c0ca1414010841071000c034003040d0520256200025426038a030100340c41c1401d4580c02014490509442d06910680c20300701e0206500d02c04a0031a0a40c950101c4848100c06a00a207030707024003802040d8906101d5000444004268408018007103001c48030115a038901c0d0010708501160f070301400008a12100c105100248940000d800c1c00d0183c04646000c444011342c64014081005a0040368003c6910400d00c03010320300300400c3e6400346102c0d41c001d010601c2c1c081c104134222800d40c803024245038011026244200d403258130880d03440c0d001500341c1d8020441074841c032026003c11360300c00b6030030b0303111100042c2d850368284159030140c0302200303480c140b80d2031035112104600e80720040501441c3d60fa18280a15954050856004040d8110550f03a40302940c24400d0001400c00d60544030400340c0000030701154401d201e4000300d90681d8031841c041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 975615818 1250 975614568 975614587
    0x15090303010302032e0f0b0a09050a0c09030206030a0e03040521010506030d17180a030203030a05010b491e0510060c030c020901030b090f15130302011e02040611060903 74
    0xb40541c00e15204d4081d80e02c080c00350700c0b03403180300ea4040a004021000f02b541c0c20250207d41c22110f0710b800340c130100207101c0801d00040c3d803248204c0ea005414010041b840c241283e8100d4194810340d407000c1d90001400d122540b00b5003410501d00251003003078000704030300e94420082c10b031501d401d030b070032000082c000d20051040c00481c1d102c1d2580010089205a00c1600c03201d600f9840d0510f5014150007503400030080000140e400c1c0039150140070304410190408210b010a1030b000c625104440001000c07112600303a2040c00c9951488200221108904103441442d002d08024008130400b10303010900d0071058a00e8200034000c40380240d5061040202d40b510b403a0b0212542d820080013101080301c100350140140c1e0f5803e0006010358090380702945507041c84c803000c504e0314010043c0f9660380e030407252500b04243c460f40366956001d02e00358401c00740c40502e40f400700c0c0100500c060342c0d65240000c0d40c60b819640595409802510002d448040d60a40030000c065902c9000316601280d0342c2c01002100d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 975617068 1250 975615818 975615821
    0x80c190903141f020c0106211b0608160e030d360b030c0d020c0105060a060e30010218010305071b11011e0e1507050c090915090303010302032e 63
    0x30107a0101c800047d407240c803501888003400900b543c2441c2d40c4075081c3c06c07105014403444609a1150844040000c441c9800809007494000400900890603004507100307000c0e000b85840e07100a0300003002d5031030081d11100081c10401188034031a0151088441c84038440410f1034240450481c051140c041840c03805844100c0c80d44001c1464039002c1060005400206031400a0480b4100f44800854903140c014184060841264020300400284c031200d4286512103116405d41c680404460718400d1042d8066035500492207912100036610000301202500070400b4240c110f09001d0b41e00b88500d44907418100d403051001c40038103043c0c0200e0648200010001111901c0101060400c01100c40a174000901d140c1c0c0c2907545d1101080f01c0d0f0300d58000624044140c2d40090301c0340d106450610729907880c1d0765030b100060005030340101c5032140420309005040003071010504841807019054903003450440d4681d0401e1204034080d1040c11480303410112601503004800950102c98400010080c1a100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 975618318 1250 975617068 975617077
    0x140109140a0c050c0a0f061104060e10030e12031506040806150d0804030b06010201060519030303050c07060c090f0e040b3402030a110c060a080c190903141f02 70
    0x60100401040c00f00340000c1c00003641a600400940034141000d003001000d07642e0300707603003288c0e2000100010310005821183d440c078107060551303040750f9040380f018094004006402c01081d0380c0c4a42c1c40740c0000d0a1010000b540301d50003400020551030072030010300c11140121700400000e6004000040c8200d81c691012803442c0500520090701c8801d04c3c2c8404007140d12a400984100342d1a50030404c25580900440d00208000e880e41f000400100e8103a4540f04510b00004041640b25804680c80d8810217069840d1a034000e5801c0113441c2c0c4502c400b9003a41820303c01c9410641c1d070000300080e8500c01d03070000d40c0325070740119010217103075202a01940081003c8840e024001e510400104840720880808030300150150002c6560f1410b044010782803001e509201200c580c05440d041c1056101c01d000d844510f5080d0602c0040c07038407600c074071103224000d0070001000d0041351080aa01c039503000d103010080328040e0076601004003c0c009803603128030b9651954410400da040112107007014690041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 975619568 1250 975618318 975618341
    0x60f0c0109020a0611061b1e0d02130e130c141201141f120605180f0307030e01020c22020c16050307050909071809021201140109140a 59
    0x1d60801c55400980101501d1304075000144141401d4400c1e0300c8100051504203000700791101101d0500441010300d1f22812099031202c81000469a414260b070100b503d207101e8401ca820f644880b80700e607441c04003007864407440702555510408075140d4100154948032441d0413035022450541405010070b0071040d5840059004580c1c40c00c154800102846950040c10b064045481c9500b405011024101c2142581d0240d40c080c41d80d08000c490340c402c07106580f0340c0d03001ca40402c199461080c0d140b0100742c16511704405006d042c1040d00503101c00300080051622940312070080138031801c01260703120341981e426504034171512640050303210b0b904500070400b0402100945444000203006043c200c4600c06900c1d0002003035002d01c805d14050206c10050300d030039518000305160031800d15a0360081840f88051507904031030181c1380e102041e00003000f51a0042c2401035040b8080c551503008041c0e489098900103081c00c004901c410407400b80c00126142103190094980f2a00b541c10020108440c60 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 975620818 1250 975619568 975619571
    0x308100b030a0209182403121c06030c0807050118031a06040b03010609090b16050d0506010201020d0218090f070e121e0a030f05040e01181e021314060f0c01 69
    0x640c0c1000000d1000601c5003409946c1d031001085441d2038203001040341e10116120740c101402625400d40d407a010360b22100c04400000300800d12414404009180307070742010388404080794021800d080009550f40403107000781c0c1c94410380c00082c20030350405600c41c0402800120520508107906000743da065402c0700c0010710002d4078030b10200000382141c4481e800008050349a0b0404400d000814095640c0031aa05003945142d46000100070040d01c100f104020007151759001041d134692007541a903012900c403150856131122880d508a0040c000c01100c144180e01030000940182800c0000d81d0040d10701d620b8030409100010304001c055055240d4045607446422843c10001d0340c1d005a5015803001c2c4405070032041070f10300b0010000b115481212003804410001040403821060540307044602a003a00104a1001581e242c041c10b0f69140e0407000400290456100060650003080704062811002100aaa520816180c0200c500c0003035400103080c800300010511400042051403100d100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 975622068 1250 975620818 975620839
    0x4410030b011421120c0d170601020c010f050d06090e010b040c0504262413050a080904020c0d0e0a0806060906010c0f060905150708040c0306020c030418090308100b030a0209 76
    0x2e0f071301c16904a074500311501d500070300821481310341090201e83c0d0500012100d441038900700c0d0000c1c3d55547c0c00100141000344081e00140000d200d102651484800010103000b00340d6108000005000b017034100801d29440c0500ca0314082c50188107680312580b42e900d5260a162a09180c120000310103c10410307500454550300d00840c2003406404500c9030b1206030400310201359101001000d1008019002e66500301103988003003100000d04205081d8084c01c41941d98004134003040103030103819010000d41c8130f40d21031106119040b81c42610840d5096540100003176541d50b42944da00800d40d00280c107c1300b00700110704c4035446440300583c5640200040f8101c00c0386907541c0c03011143d162100f6070f2030360059001c514555a21250468100080d8540136400f0f080644502c1c2d400b07445444010560342d8009400410803a05201341c138003c02c1101d1540c0035102402d00154080c180d0503008400240c00e00c0001500103c0318420b4800b40c506102e04a400c60b03603141440d5009500c0307204030560001110f130 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 975623318 1250 975622068 975622093
    0xb1f09060306180809091e0405060403020c03070b030c070206091201020a031407051b010b0a06111212010909020a1a0c07064410030b011421 62
    0x5144402000111400034149285080c444100c86400c030b00d0342070303203001c800000c40401d500c4400e1380e461035000c550011441d202d860403903c0110404884003022007000040200b4040c0105802c0d120b54000d800b994202c500c40c2c020152200d0316400303515042003050022a00b900020702c01b80c00014030150a441c40c0c202140d00181d03409082500b0f00915a40000d0340d511031680c50300a0800c8036109407800c221500704150b0107421805050310184400e44106181a0b4800c425081000556005818245c803161140c000501c24580601080c07a0791003951007031103240c582c0c4c0e822541c45002086030110300340d0920031124050402003e041e60f0003c0d8840d0007240e131403101d0518000080006905503592000d00c6040c40c1001107a60260b014010480740440302c0c6202019064444514940344a80c0280942105003a00901c9800c4c111201844001c0040b9211481c8004c02500d02501600c1001c1e031342d803030925082c0406c040303806801031000c0c3e058524801914a104005181004c1030f1890460140c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 975624568 1250 975623318 975623371
    0xe160c050a140f100b090a0203130b0c0406020c0a0806010e070c0c0b2d09120f0714190f05211f0608012c0703060504060213051801030b 60
    0x10841c91241d4210541049030324030b0401c4600301311640c03200284145414180094110350b40284000e01c2190000000707008000340c0310f01d0b90704d85540020524218105251a0b03034054006000300030144c855081289500d2420b803040c00304a8210300300401c1907a0a0083c0340121302c1020300700005008401c6000000504081c1d03d00020345102e07051141c48605076404555952000200c00350a10301c0100449003210744c8000325544600c1c1900c540042d00043c6d64154a092501c80c460080e07801080c80c0460303a0380c1000c82031312034001c048914008524240000e242581e01074440c0114080c03103000300300840d0a01c289041c00814400d03d404500ba06408110340c180010b1140c1d50b0b4003000342c584548200602e80c4245800341500c10002c10400c507040c054542030601a00c880b0307c1169004641b554807174000c100c2c52004e9940660140141d0800d864418041d40001c1c098421405541e4004515401d10700c00103044188941803030900d5920750b0300ca41c0d0389808060255034034060520040c0040c0c2151 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 975625818 1250 975624568 975624593
    0x1a1018090207030c211e122301091409060c04060315090516080a0b060f09150a03020c190f0b152101060803040f0e060a2d0e160c050a 59
    0x500714400c00e40180c100004086040b000da81e080d80d40d021603410322130640d003c480347c00c1c0820440d00c001084135503140c0502d40031005226207902070402200102e40044250400464002a46c0c8911340c2038a8800629071900c00c205c0e0805504e1400740710400c4000e100e50460070322941190032072480991104001c0c42a18000c851146840c06003001c11200d0030380c0030105650184040c0020407106158000180362440391001c2c5001c0000e002c030391400c0c140c0e5009a02200d50220809442c1e494817031100c0900030707400001c0400003038018039101e0700c0c83c440740c5410800555400180d8000320041340d5105100074501420350110f21600040e1400f6a45a0b520300c0d4039100104038480b800c201105805c942036a15607007042c9801c0e042800204511606684140250741c2404036151240d136991010500181e050b61041101c114911b50f1041100801c1403c0718150035070450810000392a0341c50541120020b80c0c42c1c2ca80da9504002464903584580da01200e918461003e50301c00f841c2980351815092007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 975627068 1250 975625818 975625853
    0x1c060b0403050a0b0f090c0904020a0b0301061215030c17010f110903010b040606081801110304080409050f04080412030c06020a02070f0f0315110c011a1018090207030c 74
    0x255424050100c4d143d051070f40540984c112014500d4401c4080d910b40907000d2a20340989000e0700403c7c1150f441c64004c034086c108152003a901ca607594000248102c4190304581881854441c0e201503020544400000f0707643c000c803d10352054901030340e02036408010706619a0b40e558070a41e01e000c0c2c5045025031fa50010b005c29449466481d00002c050860300c2d00c0b84424400c62800300704100a94000e40c1301c0b544150100040c404443c4510045c50140c5420618000300c0c11000023000b04100b1a83e001d0720070746003c00000c1090741c9c0c410700c40c4c1000c1074007aa009001603030144410010400488008000d0314031a01d08003c50440039600c41040e0780110580c4c1001d0f030402c0f942804900841d0039070340b000304401840444000c1ca0358881d04c02c14003092014a0ba000d884800701c030310000d2410304643c03045200c84020841c1407008480c8104945500250300d129005819401b0f0a5a104014861002405903040c041e0180740c0032910000358840601107050280d20340801d0041000319002207940c12 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 975628318 1250 975627068 975627073
    0x18040603061a0405010f09091506080703062403080c031c0e0d020312071b0813030b010603110f0703090f03050106080105010608090a230d02150c09061c060b040305 72
    0xe40702e02e40c18580d42888090903000301e1408004024180b000034064003207400b5240000780e44111818014941d145488072001058104007001a03200c0001801000b02e90045104003c1151441c600a61045900c14440003080c0456002d00201d01e000e4010451010110101c0340b4025809a0301c8030018907500c00c85154580d11543d81061203001d0002d0096411984003451a14603c040301c0e0418070700141006e401c010b1340090a0102d01080b00e01c031580140c0144420340c03590503000443c0a20b40c076a0100b21000030300c10000281041c068007441c54000b250120103420140c1340004c07030100e9003002a0540400c40c02c45400910003000b0400000918043c900200740141003010303850035540f044e0b00c240201f06520017001140702000c21030345420303644150a2031b1004500c0040004511030500c65504901440b43c0949079180c0009a403c0300c1e03214040071043c01d5580104508840c0a038589294005c40200403184142d1070b803011120204201050015501d5203032042c1c40d400e03800ca500101c40f41d9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 975629568 1250 975628318 975628331
    0x1e051b030d06080c1c1703090309040b030c030a0602210403170f0c0409020304020f19031e02032d1014061e040f020f030708060112020f030106051804060306 69
    0x1580306015103000f0b0a0a40d005180c01005007000c500320821204200c03c4a200c40c4a10108002d25a048901155000f814281d2130342451001c89840781e01002465120b05c1c81d2680b051010308022440400108008025102c1050707607441d0000607602111202e00d483c8043c107402c201da01c2440090b10300481c0640c3e81e0820b10390031040c42e0030720b000018141540301c11091302007101d0740c0c2088088a0640301c13030540268480e01da601c045826000448103140d4002a0100c01c210300702c2d40c4181c40d1003224050400a4070652074405010345607000b040029400d81c00580141300d002c040794840d2207581780c06018205603092501d9500742480d090400000c1003581781c8060140918007004031a81140381100c000d002984001c2c1d030480000502e52120303000710785651890f841c50455074152410180103072041230356842c0140d8000e09031502100c6142c040380e15200c030101055075610a4400c03e0340d9000b035162a59003000026140ca4004804848030600070240e0741219890314040c0100452041c40b012484 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 975630818 1250 975629568 975629587
    0x20f0f0105040305060403230414010c02010e090a0509370311030c031801050a270306060b0a091a16020a0503030d0c110109110d0206071b08060609071e051b03 70
    0x460b182151800b841e010b09c800d04c01c5106905e4584100030003400c00c3e040300c0303d1600c0181c600c900b94100080d17015182d40b0402c401c0840c10382080d441131290100b900d03003850403040396070340d074600d0b40025503003098411414116048103010003040003030090034060449c0c1c8440c5103480c074640c49901001e00c5500301181e505071418122004800c04031003401c2250078440001d0380100710036131440141d0248650101c0710101c4d50000c00c0c07040040c41c4c00502c14000305456403204c5102d54481c00c42e400009080c020006084012003002110b1810304140040c41d04100c800d01c44400e1a0b040026a448061110005007a507001c10040216044094000c00d24070500d19010305614600710f01018070764140138842c80042e404c84d02c120280d26044503003100400340750000c541b8600900344014950460307810302040405c2c3c82d642c040206c5030003004990566070340da0280022402c0995201c80800e03851703000d9403040c4d14844441803010006140c95410806d640d40f41100a83ca03a07500720f1160b400011f0001c21 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 975632068 1250 975630818 975630857
    0x609091914011404050a24050f03030f12040302150a1a100c0b0a0912020721081801020124050901080706020705060f070b07080a0b0409020f0f0105040305060403 71
    0x2001e01c0100c9403590358940b0300c1c140d01003142000050702c16540c51002071824515070707204441302510110415000d808025400c4400c0106000f49803243c0441401400035107800012240c0c20750b0b81030701aa0400c03203801c2c009001014043c1c000c0b802d500960800d40401903001034054031495610a012038400c4c02c0c1c008400804000001d42400345014825900103281c1000c00c3c0d01625900c80c001d8a800d03074407040103000620400e000104941d1091034413441d5568001011002e8500c0000485481c0c00106400c1ca00031011301002041c0d08014030141402c1074240c0c2011000b2130060002156a984e01e1241c0f1031250794021750080d102025080600290400c006041c0c09000c2c054020030b2014104407010356203070031901c100ca1040c440007411304240c0704200261044c1c2540b02c10800a182040d44002d07004010441d80c20092524020002a80745414090814907503006426061001c415a045c0603c000c0d80c2c8040e00d05110f4100400400500c0070405113115501a60f90048405c090341030a41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 975633318 1250 975632068 975632081
    0xe0c0315030606100c030e0303120412020604021503060118090c112413050a200402091810030b0a0b0906010f0e010e210f120a0207031106090919 64
    0x38069401081044520f8842c01c44c20603a081d007904081c010007015180c05c4840c40020300940390140404921015000d01c80d42c0c2090059124000e0300d0142d40c51a0400c80e640c401c2181c000e9880b1086024503a542c0e001d00004540026040c035140f2252210110151721004c0240c0c05214455a20440c0e503103015440031007202c0700c86460010703105421010038521690300c2c2c07195403843d035a4900700125140c035101c500e600000783d034808103440d4208690300304101c000707290714400440c000103c4070301821460144211402d9600003007030142442102e40c44240944030082c02c0007005a044100403020481d5a102540304010700500070450705011000c0c800802c0c40030300581c2c1806803030250300400c80d42210400c403d0300800e1038090107080d0160002214500c03210780d540c088003088003020040f0b138030124080002015004c200da00300d000100034140148903192a550068119400c188005140304295040d5114020704031418025981c0008a280405441003003006070b00108030580543c4a02030034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 975634568 1250 975633318 975633361
    0x21803010203420f0103180c050a06050c0a0b07110a051c03020708030c091c03110c0a0807050103020d061a0301030606080106030b0a15170304030b0f01060f0c05070e0c03 75
    0x1150f810300d02210901d002400d590441c8140803103902005542d101e98071581070081860054402c0e014141082c1d00000c2c1d040c021a4045c4410301c401180381400303281101d80d141100d20042030407280c1d0380c40e1143c611401030009030400003041d0f03001c50045410031003070000e1401400501a0300c0c4e544947e559200e6104980c08050500512001000c2041d0740280c03a8000203c0a4559450116038001000341c4262003040141c20940340b1000141603129071000140d503420008c07a004200d01c0c208104020742e07240300d8030700315511020b81413007254842c0d006041c150f01961000f242964032115920000c045800403c0100040400100180410b90280d84001e00c40c00008209407400d580300c2010007000100800791071603c1d220f101801803901c9030f02800504840d10714001000804240c40d032254442d210a640681e000d0005c102003150600b00b40e03040303810a80301c40d920340503170b83c9081e580d01141c0c0205540c20b0140c420001090f124a404c02d62003154164001544c1e1707d06000211003c07403c1c803044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 975635818 1250 975634568 975634651
    0x15050c07050f031504030216090501030b1b0307031503080417210703082a031e060f12073f020a050906030102040b0c0102070507060c15021803010203 66
    0x4600b40e4034045025001e0780a401880d4000359250705081e40b8241d50802c81500001401200241c800d540e50312450580784a003a00860301d0302c40e503414003440158038420785924002000403510180c060307407080d01180d121220014203250f582c4c44246554120354030408500c0d80030742012031004014040c0340c003003060710080390501c1e03042c1d500201880d0140e6800201446040740201c1d0030700007a03002000115804040c14410f48030182074544480d082907500e042041039185034481000302d03001546104480c0684000d0350115400100500a49000e103500c0d1a030141c031801141c0710b03d00400c01e020000325140b00d00c00c0c0004051090303400100c040c2080901c8a02405100010b9407048558012a0006c840d68102900c40c00002402071041354446c0f54a4040040c40108510b0190041c0041070300800c00d58103100e40e074a40984480c1400c1030000c00c200719042d80b100400b0f03c3c550181004500319004509149549400710342240d0040d20081c4054140403041d80440041402c50f401c0031141034039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 975637068 1250 975635818 975635839
    0x180b0c031e09160b1903020901030905011b02010507030b031506040b1008070e0103110d0c050c010e0c0f150a05030408070c17060108010c02100b060f030103030504030c230d0c15050c0705 82
    0x140302c801190700000c1700105900000e50041e01e0b8800d0b0020500103070048001c2108040000f280c00b22151601c0305840554204000144050301034400c07180400400340c05080d921402803001c180c01d1500030146548141d80b40c2074490a51645e6007180300880d01c580301c4441d2420050005003080e01c05560380750405041070f035030114107880306094a030152804440403400c0345002c5d40a4505001b5002083c00d10341c684490170b8074412000074510b20360710303041d144031401c01c1c0c8002c103010881c8261007455011180400c01084000d104a006540c02400f480300d2604150705980c0c0c0101030100c55100105506803a141c00820039020b1140038010300c0c482000300301c0500400303000f0b034072083c2c0b2645029150b9603401c54900652100c1f011549540303816121643d90390784034074000d4000d8216002c1030700c00e441d100b0030126034407004001d01e40c00e804101c58191003055441c010420b41420080d012240450050320000c2e00c10051030f0b502200c105591101d640302c03182d45010f10300e424003589c00b003803040300b4503007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 975638318 1250 975637068 975637087
    0x3090f060f040809040504020d0b071706040c090308160813091b1d0a0e0106080709080705011205130b040302100b03150c071703010315180b0c031e09160b 68
    0x10455140300401e407001b043c00d1b566400061000b0b102010082d1584c0c5d00c0e94100700b4890741c0f14a02c0c42d440302031a5501c6140761111001d0004490392000134101181c003c20051001c00c241d00080c148540ca1024056447c40450755031055503003104110090714580040c0c144401d8103540100d081d00104d8414076204107240f0b1000810a603005201c4d00300030b003118484070015480b5400f128000d4680300c0040301d06560b4601006058a90483d048400144884004112030801140c86021544141e43d0a07102c4020350505600400d0003515090008ca0401800000a4200c10080b4840c5009801604805264004200c142c401b20301c0624070a80003c004000041e120b24151500b2001c60360b201030300c581c0c0d10b01e40b03c4043e00c8185003900e42d10340301100010800804072462034110101c1802446451003660411150243e400700080041c0b411000280d4000504401346910640700c1c180d030000540e425104004200080e213841e0016004034480290092100085900a080c0302d0a054584072480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 975639568 1250 975638318 975638333
    0x30606031b0809120301080a030f0503040b010e280b19030c0306020a02030912060106120507020c0415150c060b010203310b030702300a081b03090f060f04 68
    0x741c441040c0412a07000c9040c280c002c108403520b074804258240d81d21b503100c8600030b584081950046000542c25020382c6102c0d84104107890046903c840c1c0c00a0707503401d01000792411200180100b1030701c600c5541c0ca5a40c518510440703040b00b18603120020b41c400c1c01f00705000e090800d1481e9011085c8a4010401c00140b40d1540d0f40c0c111b9400c4500181c407420182d8080b03007503100b07901c01c003030b403180d00115014000392000c00e400e030488403180c6442e8141c3c40d00000c80410786a0889940000d6005800910704600b816003204044568004040c400583c45402c401d03550b4542d1415240020a8580a001004144d100e16a07004800340011402c0416281c1200f040ca100402224803030b1028000c40c07141048401c040001801c2540450707910791070811402562022440d03200c1103c0c0e0030216440355110b0b0808056071421310308051191138a140440300303840c1c0b080007501c42032000c44000d0360002d030210008061401151000301500c40c5201c082051031801c10090404400314080406020000701074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 975640818 1250 975639568 975639611
    0x13080325031a0f060403020d150e01050f0408130b04081f06080a170d02070317180309210d0f180501080a0c110a1b081c0e0607080f04030303060603 65
    0x48030b480d9000400d00e4040340307039400382c1d41c0025000b0052381840000c1054050380705145038107460b0200101314001401ca400c0c2c0b03505444a440340d01c103500125002c40d0111000708800c520300350382c4001ca180e5070610101d45a110354043d8020b42c0004c0c125900c0e8003000c8240414007001240103100082c00c1c0601c85403241c40b5240002e183e900c004c509407114072408416a180136008940c04c6440b0b0200c1e04000e80400d0345107411072403a036444400034030744903c080d42001b560030b4404015400c20000c8418000280110f03070400b01c140c0103407031203603070b0b211020404007071030404c03950b94240190f0b080030010302400205070400c003200c15600006c1c072007030360301c4941180d00c241c44070b5001c211203214035400d5a0000410806030241e01502c20700200b841507403414503420500081000242580ea103c0300d5403107207503485100c48607500744001002d21601c10440c9807501d000040c10306151036916650105190700c0301d0840100c6040103d801c000b81905845174200500303160600744800000d900c40c0404a059 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 975642068 1250 975640818 975640871
    0x50301021c180c030c05010e0d051203071b080706050705030906070c020a0306051008100c0e13060b0a0216050103050903070f06060b0c01150b0a0906081308032503 72
    0x5803500c41c200409402c803088602e280c0c121141c440820386a0030b01440102c010300426002c0713900c2d800c640c03409082c41d581141a4641010282c908485883d4510750203a00c003505032b1042003072100c110a40c42c4820071b20400324510900ca915511606490140c0c20ba800003005441844400d0041000001d40411826400505840c0c00c003201070f05840040e100b00358541000c0e100c1032804041088010840408006072240c03041150000600c00c50b1480035640f08000010000e0841c05140c6128103090245094160502c440030845549400070041c0b190800d4000070016440000c40001211010703e20307801404080c64248003a1901840e89a900d200380c04000744001e10f1095404c0a010319640f014015182c000321459030f45d4203001c601406408440040c0c0001040200001901d8416008482000c1c1003034980c0c00416180c4402aa05e4040007005804142c881100360300000e80040c00131441009100d0110301c03200052a01e100b8007103013540d805e80c1810720341111071044844080c1052170780c5a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 975643318 1250 975642068 975642071
    0xe121c022b090b030f0613020c12090f0907121a0f010f0e0910030525031b0503010216050f2d0c030d030e061e060d0203031207020d09050301021c 64
    0x80440084031842c503aa07008811810300441480b01100364514050302a00702107a240010440004800040b481215102e03031a543c400c506036080070050a010707101d105c50003000d408102080340003280c2600c01c00c803000d000159103d20244070740a441d1007990700943c0056100f01100740301c0400300705404810b000090502440d90389040718184039041d0090840000341c41c0c1c618a092903043d41020444500044904d4041c1c90009104112094842c0007049020211011003c1c40c5848404202480b54403030640c40086c184003090301c2c0c8090004000b07591609000c0f90485d8450704000d41403411141ea000c40903040347c1080c2d001c0d0010030750822008800c25404500124940c00b0903840c01614200b0281c060003424024403074180c1645c030030825400220700740d03800c507030301ca282c0080c100741c0000401204400c0c00000c2000ad0401a00003905644040c0441385014030381d10024400681c1240e0800c01648000004000c41d9480710031500101001c2c1c00960801591090b880002c0801c4088045644e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 975644568 1250 975643318 975643393
    0x7060206060a0e040309230a0b19050f07020d020a2c060906030c040f090510150503060408041802120a15060c0506040b0606040f0b0c06011410030902010e121c02 71
    0x5208844115007c18018034020405965610341200da40142903e1034650681d0910b136034806029600300c8118150100b0f046240007080e6003000780800c48000c2c10fa8014604000100e4010a81e4420340340368150120840305145130302400c2c10402d100249024010300c1c080082c000c0719207001902d010f002d001100d000c5203003404e42d000d42000f4003200d440940140f10f001e1008503004883c4c0e000356040800740340c020701019281c0f014155110b07400d550041c941902000104103035450907805521451601c040903140c14441485008030300303020b43d5000440c0e0340d00d0300e0303091609600306003c1c0024899810440700d4100c05403129074881c2d40081c805042003900c140003e03544da6940301107802401030210042020b64440d45e1409454101c02e000d5441485028000300d60701102c0c0f21f0400d00500c0c02080364861503082130044014082c49e40f4124140201070301080ca140d07031011f040c1200420b08070005d00d565103046168502103810552040c066411442d9400b40e4210328503c0c000c0089d03030030010101603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 975645818 1250 975644568 975644609
    0x50408010c0504060c0b0603011e051501030615083d0503070501050403080904020903011e180c0605090109051201020a270509090a021c0209061207050d031107060206060a0e040309 79
    0x260060201600002038ac0301d80c0403080201c160703c0b541c00717400300c009610503210410005404846041c01494400e034484180b41404038451564194801d10300145e00c81c83c45d01c4862004aa4100803c0030151511961409078548030f144080d5030017004101e0080510524090002e09241300c0d40c0000741481710001030000440d102d41c1c04480103004050020841803040341d11100d06280c20302d95480d040350400c0380c800008021b4408070540030f900708106201c01464a030040d42d296001010860601c0494080013986a81366050340c821034008400146c0d48d90b00d0b61500902100f180c80b44865102054a0a240c1d00c4801c1841001510800d889030b0f12180c9502c50340c0d40c0383c00c03011a0020b520805400400010b41000107120304014426111020161201401c000f03801c0e00701941316425030b1006c4000c101d00e24140400100c843e02030f0510701c0924540c1c04070241000d003180c1220300940e20103000d00200d401d010524100815242060b522182000e50307009202200a00c505a0b4400000f55007406 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 975647068 1250 975645818 975645821
    0x270b2b0503070b19020903031801212c100c09120c030212060f0412140304110a0f0f05040207082109010f0c021203090a0c06050408010c0504060c0b060301 68
    0x6559044000c40303484103168a084070122101326028040030014203540d41040e1440e0081e40e841040c018095030912000000101081c014440c82504021004041d0a001300700b00c00006d0b6400c080950100b2100551000000150444100292000321071092002401c40c08078141c0f00c120010400402e01090400d03003251600000c0d000010b415201c0b44402c810404440c4141040f240300741c80c214940d0781840d458540300e20040322080f01250040000800091000c11490352445640c2080d2502002003402c8030050782080b201242d50000c0c005818041b842c09480c1c0c0c50040c90542400a9060700f070404420200400d4400c41c1d01a94002c1495801c02c680d100648034010303040900078030070710141c600c0780c601d002013551402c42951a2124000d40300d202c038015040780c50702d03a400400c40c9809079080c0074001e40c8014202c41d0107010f200400741c0024040800c242c0241a142d5078140c0304c5081c94142403c4452000c002414090200700c200712003a000000500126000950340c0410b5840354046070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 975648318 1250 975647068 975647149
    0x61c050a0b04110a060306090b0607080d110f0f12010b0301081f02160f020f09150d02041103010e07020c0a14240a0306090b0a0806060d030507020a270b 67
    0x61340714038007036400324a1a600d0382c8004219030b0389420a0000500d9034080c040340e0b00c10504041d11107181007008071210201078100e035151480c0980c4007460400c4420103800e203604000b50203501001e001510540e900c101d00d001e140036168080c44c091031549400070280d43c1e4581f429140c41c151100030b941030103917072055040c1c810180e041a00080c641c6010720306440080c174015001c82c0b04080100c1c0c010218280540c02c5885003c5079050000d90300b152400b00082c4c007030b0388502281d2007600d07018072811400041e0301860017050544400348a41c2001c03403000e0f044c0051610841d009041085003009146032600e00314014a40a03141e1908005225051800c110007070220700307140d8100029070340849645a44420b0841c0d088100800501c002c0ea020030903021268400e00400d6031192000c20040d1902045802c079041c842d050140c6000c8c16a0f010401e1903002c0d500441150300e080c1003000c100c0c0040030030600f4034818141d0400600540200041e07095400d003400c40c0d2845030702d086010b100f510400400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 975649568 1250 975648318 975648353
    0xc0b0414060a050108060a05070f030b0a120501020c0d0c0201090317070c0e1f0503030307180906091a04020915030a0609110a090e130b040f020402030a05061c050a0b04 74
    0x101d485151012040300680020310034900144074280028845a0081c4609405860300e540c9032880d072104000110050724040802c02d600504100c40050048101050200130710710170000540ca0f014800c01a40c24840f0400540b0240442d02c0d203e00d0043c1e03032110040b415250310904980e203c04d18051498128042c60740020f11032000d542c2c1c00b09030540380f200140d00c0f9000389013644540700f9a485040592905912426404d2761081c0007080446009a03004203a15009240c01308070260394a44540c1030340c50300c2c2d01c04020990380d80704480703060b400100043d1081740c00b03a900f07501e098031150100383d001c00580240c0901b024040085081e240082c0c02c488024041c05034140407007143c41500c03070019801440c65001042d4209000171b207030030a800f605440340303501d07040ca500c0a0680c0e03112040700c000020002c43d00900c0d41d04103140169190310185029610b81c02000489203003e0003840707100e100440c0d04007240000c0f12410300010341c00180520545a00584410b042d8a491074030300d4481c20840b041c07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 975650818 1250 975649568 975649573
    0x8070309080f100605310e0a03090906061b020120030a0e1f02070b1c0e031209070807092c033723040906051f0c0b0414 53
    0x5000a0310b00000381440a0300c1940020024a55520208a0400b20100319821050800303926055181e400100e84007207a81c40000100700d8075105201f141c14441c400104801140032000140915111881104c0103006503041c07612009034540c1c1070701240710b10040c000b41040690303000c40c1d041c0131000c4a10303000041a5400ca030307180c0d41c071808050700c2582d80400d040d005041c80b080c00c200c103003015046040c0300f440c16000b4208882c00e180d0122840e6000915400c0c0309210b04000d01038881c000d205025003181c0e182c01554942d0089802a04034400203850814954040101031180e01e00104588040f10400c100c00141c0c2002c81d1841d03680d149030100c1c03048020003070313942210412101100400c400120091406082c0c0c00e4144142030280c080200c0d071f03076900140380d51151a140a6111002c3c040340300303c04078000c6050781031120517541c8960441c42565071500c0c003c20040c00d203807000c084400d8103014006546210740c0401022105c5154010b052408420081000e005041010042e41c0d041c0340f05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 975652068 1250 975650818 975650833
    0xb040f030210020a061a122b140414030d0e030c1011030a170a0504122724020102070b1b0f0f1206030109050c040e0102160f0201110312040807030908 66
    0x6c00c0b1401000d071601c07034018800c00005d4000d41e140800d00440550701c407402d421000300500da040c0d03a000c400e01c030345000744441020301010714650705025200400b82d0305d0103040c191511380207150400000ba4840c1041c04034289064805035804180c180781c2c04010344010100c1c2c02079403000c94010030f405400c5012400002181000c2c0c991004c14ad20a030b00c0301c141410981d40314012020202d810032a0050180001000344d6101c0c10301c981011074809903508040c404035009a244003181415039400311110720780c4d1140e51403803035041000b4040c0345052800214107000b0980c4840e8141b00008002c4544e460a0100d91400350034071400f0741e144150384501c81900c805015515034440c0d4422603c0203c000403580c001034180c50140180682c440c2d212024090751003c960a20014284a0040e80b20030b54081c842e19080c0c4000c2c04188a4142c0641542c450f010114000500b5070040e401001e1025041041807421000c2e0104403243c100713a0101c01590780c1c000a050880c0d200c41c164002003130074041c504 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 975653318 1250 975652068 975652091
    0x3040b0f0702040b01080c0301231908190309120c030b0901150909261902060f100f140301180f05100b011d030a0c1508010b040f030210020a06 63
    0x107007490707610995003004034200c200e00569042034119a0b1000400701000144001f021602442080c0c424280b080c2c0c00a403100000141c50030f204d0442a2b0404440300c0c8104902c05041000c1c0c1964400303400c861000381c019031802403005030a401207100c05102c900d020740130400040c0e0b01c0030003580c02002a10311030030004403440c046c0024012440000035001404548070781584609060550300c045908078020012170003e02c0038940c0c0e0042412050305115500410001070002c20401c1080e5001d01041e10b023400b040c600e13074800070340101c1c4c0381d80d03811101740710702451a40e240099801e101b400d0800d14030400300084c050a40c1c104802004200c4441c100108a164002040305502c10400e485207002008a41c030200c1e1801c0d58402d0000e0202d04000d11400b010014000340d840c0082c00742c41c84e00700f1a841d2120944815071100d501400900b01d01030b0700d02e60111803607014244911105190600e0940c502000c00320038000a80b1410200c203402080d14003c04c01d9201c159407050082c0072040910 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 975654568 1250 975653318 975653347
    0x50405070503090d031401060e0111030a030b01080a0203011d0c04243b1504031406010e01050312030711010c050d180f0f03050708070503071a06010903031103040b 72
    0x64640c40d00f40d115a07460b58828074000d000c0d2006032201c5074081d81c0d140c3e290a0702207a1070400c80e84031606200302940e400b0100d00c01403005000d0504162008a911115100014007404000301a406560320600040c066551002420b48512403500c04d414a1a15944005290342c070603640190a40c1c091080c0c0c40880f40e00120b204903800d8001e80f07034000701039007c500c03540d03082119041c2c00f082c071041c44125000c4d42c41ca0522200e402240034190041d5440d1150243d00070350300c11781098680c451003000a80007802c003005124050081900314404952621001c40d039240c00707402828007413590100028003000d04c00c141c00c40c0b000060a000f40068600304801074040c0e40001c2c10031011605001c42595100f86965000a140d40e00104017402003219445810581e81200c00880410404008513000b052900d005080c481e40143c01440d0340e60740515120a980322240e2620034908100010040c090781c0181c101300840e074050a10701118a84080749a046d1f21503a0800c01892401003144404941075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 975655818 1250 975654568 975654571
    0x717120121050601150207080709150f060203070809010c0b04120f02030c060c1e070b060405060405070e0112150f150207081015030215030f0f070203160804050405070503 75
    0x10354031540360404070403003007480d000d003820024041d94042801004102480502c40080c0e61051058411540d12140340b6804c01c0c003254000408252105000c3c0c6075007000100c0300d4000d200e85109071a00c50300c1c00102a44034001c4000140102e100460698000e034000c1001281040d407104c010421480d2625002407000c51800c60300002815640d40394807a0f60000086450001d44c44008055640d552000d544c402c2e400042e841c0c0030203184226aa00c1000c03103a01a000044c81828910b1031440e10380203000c1281e0006086510030350400c418803c001d900310300c20307440c5902c081c68100c0c40c9441404000014200301300071a0040039810708001421120f556180069440540542d410310320f41c600202d948500d00d000322009500000b201c0700c40040c0c01da004c41030034101042200c003140d41d0b80e00016104403180ca9450818900041040083c003000c0082543c0f01e03015813105030082c248210002d42d2801200d1174105443c103016500c07030600800000b610000d0000805c00c1c4028a401c50000b040e5170030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 975657068 1250 975655818 975655829
    0xc06040302280219270e1506091003020a0603020d050609010e07080a0f020a0c1202011434030204061106010303020604060c051303050303060a050405060a0b07171201 73
    0x1452a42d424a099810032161440c0007900d114501842a03000c12001e10660310525800d81e4407030398000741c00d010b01d01d8240b500c00007003207094460400001c184000d6031032680c1641c056822640700b00805c82007400c41d03160404c0c402e84009d0306940d40c48481040d80e80594102031340c480c81e840780006080390300d90004c0100c00424901031049454032024031510550a0080d80304800c1c540700001c0c0d605104a020581c4130231000f00226800c05011028412a0300a00d8040d0000b40b041c806001408441442c034518006d031807000f0010100382e21a20615a900503140c0219201d5003400001d010035240e41d508891003000401030400a02c8040180080d4464822200850f14150100a075628045400343c12280c058015007041e079110381d5200001c04460200d0310138403c040c0402c187c50004040c11101030341c0308100840d5242442810405e000032598405441036090904000054032503401d520300302c480125449441e100c42d4a031a4010131002c10f13a4100740381c1d001c52003807240c14044005904951 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 975658318 1250 975657068 975657073
    0xb09130f050a0b19030b060a170309270c22091401080303070f0c060e0307030305040506060301021c09020a0522060b09010c020d0203030c0d02010501050907052d09060c06040302 78
    0x2c0303e180c1400101000c40c0c0f0540125810500204042100700703a41030381c441001040c038426103844800b0341c003407220380c0c0441c1c49d526440451a81020b05000b46002c54550011450200a6081d20910348050300c004285e103807a0000407422104203015610007500006141440d05101a21010714078020426030380c480e040d40c0c19001c0001154034004c42124021407207560380540100401c0000d03290707208069070440700c060b52070840030040b20781800640340c01c3c0d1190ba400301d054142400c1c010f00c0c0c01c101901041c4680d20402201003500d0a00e03100300380b804103465011031102c0d5103000289942310143c1c88030f0f0700044d103018006250307208070340801091707681b020b0100426a11280b880800e070103030b145050b01052000e1030020141ca4045249541c072440101200e2400d6800111541405220151100503039100d80040c02a450004002d96002c0e5a5281c800d04055141010405c03107406600802c40649000720b604d001800000110b4411604c0a8800c1e170ba04e007654000c603a52108120740070703801030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 975659568 1250 975658318 975658331
    0x1c02011211131d0411030a0212032d07020909010b03010527030310090b040e0115080f0c01021c09030f200f101b05010e070f0902030702070b09130f050a 67
    0x32440c01d44081080103110300c00d0f040655450345c40d000c44038420b451895042c800d01803070b0001661207210b0800303804140c8014548668002c041034080011b0254004e20341e0071170110006955050006558050760100c4480c0001d4544403d200c1c0100000c4881540650a00007001170445440f0008070000c00440d03000003075400900325541c1c490006840c40a403400d40b40308204441c1199400448180780028800030301082010360040c21180d07604c06809083c24113000810170440f040c0603d4050020303c01c0901444100500001d4848404555190685224070145207800c0d1240003d44061a404410f001180c2002e040c03c014810b1403903031010008024410320303007103410b00d149084400b10340a000701442c607a0640c000c2c0d4440100079000c1403840000d44d804c80c0820f0b000d000308082460500054080242080c0d001c00500e551500a01c00e41c500420501c0b03445940050f50300d085036030324184140c03181c02c0c1e400010140020a01d070211400c0c00d101407214541c980d540f0143c05445106e008000c2d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 975660818 1250 975659568 975659579
    0x504051e150c0c0d1109150f041b0f0c0f0c1a0c0a06020f121302010206180307060506131b09080c01020a0602031e092a1c0201121113 59
    0x588a1540b00c040b054110301c14002c001c4c1404818201954460414090340107440d0b00810885c00c01183e5046c0c031802d40303021900043c00c00c207802e4000c5031001c1d1824401d424407406540e12490f010320181c800c0003e048017985a40e440b4441c142c0e1202e5010000c0c40742c0d00e0480c2000e091206050140401c1c01544900e88218400000112180d0740004001f5100024103a200e440c000d41010140113003414042060450050121340302d1881141d0002e80504108082c1c0002403410100a1007408045075000d40d01803105000010340c1d58156112202203007590b100400b10701c10320009070381c07141d141d814050b0302d42d00c0d55805035080d404182169107901e0300581c4c07840b00940d202050880c5901681003e954100881e40640007558820703d10200e04490390141e02c52032890364021100701d0f0983d00040b540340e058104a201c9a03091000591095895103265000240d10030308503041c10000c003c081c841e004c1164000d0b0700d1005101014202000280c00040b140401c0c1e500c0b95400d80341c0b610344880049007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 975662068 1250 975660818 975660859
    0x1e07060f05090c1011010617120a080406051504020307320406031104030f0c03030e060306100e01020f07061d0301020c191115040512010605030309040207030504051e 73
    0xc80d600d04001031102a010700f050103111807081560303070100400035000290203102405018000c0154006e1900507500c010341d41424144004015402c55104111442605601032002d07078003d0740182001890740c44882100c07800300404006160418001310804c40202d0b000585004412000700ca080f442c1108000b0712141c00103803007288401c079201800b0500a480c4a680000141c030202003405282c96141d49170b1002407070319020125042d4001c8a0b05104040d80102601b15409054481c0303070441c10000c0004800144000c0e2403404c00400884100e050783c420800e212410021a09482e9903d032075600c000c3c60311220b06080b404071903100c500d40c00b00303003014421180c518803c203010b800001012085d000265005810558120851000c0c000c0603907654070304819810f41c1c0c80c036056511443c0c1000d00801e4013072007445145030b92400074204090745020040303804a8000b142d005a540b281450103681600443c1c01045e0080742d202c480d00c40300c100c4018180445a002c461110450204058460 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 975663318 1250 975662068 975662071
    0x3050c0901061d030703020a2c06010207050f040f0504151d0d080711071e27181407051906090509040f060203070906180b09090603031e07060f05 64
    0x40018000c240301200142010001d20155030004055500150ba60340010b0100109030300540c50142041c800003009e030b1100030072101001c0d0030034140007617468214000703511440c20b032040c140181c540000e810718503030f50340c0d00a421a81004070100304a04040c20401000030a8883c100c1010b8505680a04040c03c4014502c1d4042004402010b01410300e2204807400760f0081c2081e418481106070f5140b0821047c05a100a40000034a440c05401000c45401144400381e20071201f103611b440d80540c203d84110101c0c682d180710b0142c04510110490b42005401500c0140a480600a182060401c19010800c03200f1036100f12411511942d0b00441400751460030303c00d65011610900080000e0700307202c07a00c1a0b10174040d0443c00d000a2160b12002c0580e40f003110304000003048408244038154020358101d1034900d944003c421103a081004014282c4181d1100c1032003101404005a201d90b820412114039440d002c91100e100041d217090b032403a07038102442c108c41c06801c05520555042c43c83c460103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 975664568 1250 975663318 975663329
    0x11e060b0403081611060f0a0f090806070e0f03070801090209220b0405120c0c10030c0e0108131205180d08040504090c030c08032710050f040f09050103050c0901 71
    0x3c070f01d0700c00300801c2c0d0a40c2051015007140c900c01031035005ea17455590300f07001e84a8841c0c2c0000556465003100001815407161403e040103000490030148003600300001c400e41e010056040440720541c5200c0054000078a903001d0651500c1140000f00b60408103400502803d8420703541000207445880c0700e24164a81e489142142004450b4190042400e041c1d000c0d421500640039110302c003011010315146603110b101035105c1580700e803d00c0621400e0040c500a010422450100241000c00f000140340e0345240303900e141041000404105003110a054203058254000703413000081300100809409a0400c84d005200301529055861860038501031801c2c4099110b20110315041c00d04041000400710745a0540e020380c00320718003000164a540340c4801034820b6000864075080e42d0512003508030b0702c54409400100c0711b80b009030240c0e101e072008801101406c0c280f5588176503aa2200c12114069684106011030030464000b94103011640030700c1c1a43d010b1002c0e5050b200e50b045c02d21080042c28842c1c1c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 975665818 1250 975664568 975664583
    0x50a0e030f1507050708030c030403120e06070f0e0a0602060f09010c020c0411090d03081501031407050304080d05070c02120102030601080103030518130b0324060d060608011e060b0403 81
    0xd42030b0206111100341c1d1000c180d0a205080164988803404282c2080f80d00b0241694000144014150840c11010501c1c130039003428031021a10744541e913110b400140000040c03203d504040d5501a005541d10f045410b00a0031242e203071996000029030328142a45c8100c2800c0c0000081807041b00180076400c0103181e140c00910203c20b5000a00c0003c00062100000004c010b000b2050541d071a120900c203841e000ba82c1d803a2641c24584101e0140034805200c4905152420320041c0b100c0700c01080c076640c0002503043c00d58407640c4a007004083d030f03c10411440c105919010030000e01642103561419454021b42c0c80d00d22003e940d098207400c134881503905074086221040100000782c030880080542e8160303081800c0e140122440410700fa080440d0059080c82d0311428480006d0170b040100070b0705050b420704c00000400312040c00b417259041c040c013481e0086442ca0b01e0383c2c003800001d400c8200140440c800810090001154100b02c0c1106007429204140c104040040c0c800781450a96040c2e0740c10204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 975667068 1250 975665818 975665833
    0x3020a060c050a23030a031a0406080606060309010b030328050a1b02030304150302031b030105150702010c1e12031a2106070801030606060f0806040e07030c06050a0e030f 75
    0x8a0795520110a61089010100b0545001040b00e040c405070941190742e440100c0d0f240c941101c808c41011078404581d014900e000400c10406000240c10740c0c101c00140d0307030103950342c54801d40140902440c0401c50340502c40041d02c007144049040300d40c000758540d080320f4030090b8451001161588142482c0d100010013011b5841c1c0f04462847c500c1e021140300804491038107580d00d8030841c001c6000b2101c9000301e60701108108101e8034030f552864001d13200d010980d145d581008000341ca444c00390040c0b42071852020452000b1a4001c442205e0340503006015003284888031b500e0b4900d01e201d011000c0300c1d00f41c08075030700514040c00b1380140c8941c00c2c410f0b6180c1e0341701c2410100b401240c0c1f100116401550354524000c180005c01401102d000c4c070102c0e5a5280b0940c1141414010b0300c030242c0c0024200115074860184540d40020b055811200c21a0007140d00048040740034a000701d07642000c0c200742301c0d00c1b000081c1c2e250404028450215240c030b403503221891010800d9110150300400803481c0d0032a20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 975668318 1250 975667068 975667073
    0x302090a0905090c040f15080a0c030b0403170c091207150c0f12020d091a030105010309060f1b0f08040807060203190f0f0f0510142803020a060c050a 66
    0x400c203070b503c00d20071001c881071070720320200040c16580318518072202c80340d0f03602c03044030400c01e0390b40320b60701038081a00280380110341682c2303040210815100190400303071003034040303810103103d1304541c402d0814801b482082e03810b101003034942c1c07a409114003610034820048091a81d16000c50f10750b0490b83c61595080080c89131000c10b0b40d00c40e950a07011140801003c0340080081e0504200da803c20083e940200485a03507060302034040511504000c0300c01150a02114200d001c480440f41511001c0c42c02141c410340c0c2d0701e040ca018152801850308228180046a61100c1a04801e4240c0506550740d60300140003881c01074860510030740d009003500318208100d801041d265001140c000f04940c0703100c0b080344484082d4004450354031200310301d40d0f0f840b410b5400c1e469686004002e10300184030400c012504011342c804220440f144503406140b812040d4508287e520150030694041c003030410100440c1c00054402d403500c4070790000301c0c41003800c00400306a80b4440e00c08845400d80c070400800021003141c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 975669568 1250 975668318 975668321
    0x1b05030711010204030f05070b0f18010917010b090105040902090406090f0c08060106020715050a0c0c1802070b0901060308030708090115061d10050a050d15030f0506070302090a09 79
    0x10055424850348009900300705500f44000e10085006100718254100740d03142c29030500c1d00c10b03404140a28814003480c4c8100802c101210141c1c000010940111195907006a81c21002039010036440e010303402070703031025100640042c41440c1080383c030541503a0300d98041000f1102d18000183d0465501e20000e000903541d0380c4a45680c90040d42c0300d541500302c40c0d40e00181d00b00c00d80c0280c800d80d00000010440103404002c1c4401411501d00c1c901e001601204005145001d442221400c200200300043c0500c224074440ca03000c0d10140b0111890780c41c80c54121800f0303600c01c2504460855107080001c05240c4103200c0c4801b9650f210320b0051564440b4002100c0591010b0414000c1c0d5503119210352064803800c0c5210024000c540715010000c1051040e500540301012107240a40b8403200c080030056441030888e80480d0036030902540b01c4c16440300010041c80ca060720529011020710380402403001e00e008402c0b04c2c0748910100c81850755008012410b81c060700300701359040303000c101080c440352001b13 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 975670818 1250 975669568 975669571
    0xc01030f180302030711060412032f030c1e071e090203073b060703090f06110d0311040e090a023003041d07110a060501050109091b0503 60
    0xd0440880c40248001102050080c1d240c01200584d100045500800070380c451805418141180e0b91410241762082050500321184402410032031541008401d019200711410f04891103008000329920020440356500d034428403000c10684101e40510028080c803084483c05650345c840513103d414a400d0802c411503c4d50703212818040c2c000320780410102409d202070751007881d590b41c40d502d01c02000c5a010b48205009400305107200c00c03044113130390700400014150090790b0040e40d0703080d950700c0581000c0702c00d800d80c0e800c0344944030120304000407402c0c0d018120032515244802610f206402d40e400c147d04581c51900e01490509090000700b00c44840140881e0b8040c1260b01920800080765001440c000117488008100b030000306119103410b0310a81c4040b882c40c0f00c04000318a0107081544901400c10000990146110000b00082d825445000c1c0003900101380021a02d11451070320f0104060301c82409a14001103c00e0800104002103028800e0100c4006e81d10150b110104082143c0c142c2c070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 975672068 1250 975670818 975670841
    0x3021b030636030a08190c020715020a0209040c032a12021f080a0e0a03020c121212010e0a0606051603030209130e060108033f160206060a080c0103 65
    0x20030b00c1c40042c09000c144010422520a55145081850440b41d40401c0070b841e010994000c900d00510f00000703d40010361001562100c80840c20101040c00d4102d10b8034001d4000250004984428802001201404181946e1040701101c0d00d1100350b400044c4070580e200464003140006000402449031880c100c00c40650014002d02421402880d4140d2001c14003810100068604c4d0100080001584550b105d85002800900b0340c80c09142c0380250303074507078007018140b0038600c00c0440309403c9402c1007103280c1030b080360028030b0b1500e604001d0a040120248030700800c80405000040070148648140300686a854440030b003003001460782442185500c8100b102456401c11005a243e40d40c11030030780d41201900c4000c5010720904020600f440c4041e4049402e0768000e0000c0c6800c40034030b55042c01602400e50400701000000900400140c111014004600e0248018050002241c8404100a19940d000c80300242c69034000e000b5100541d12813039096400030b8508050940c8a40c12296045a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 975673318 1250 975672068 975672151
    0x70c03110118080a02010e0906030c130b100c050607080714030403110f0c0a0504020f0418090b0c1b06040c1509090f050105100905150d0905010903021b0306 69
    0x915140c528840184a402140040e800b01346000f0442da0302004011032148165480c52041c105100400d039640e50410385644104c01c0034010089204140d03100592000009051f14016000c858002c0c050001008060320140920f0002a1482c0d0043e6403a030f000c0e410a50b949042c9000400032880f0a40016004500300403149895400c7c030f01d41040701e10840e80600000d4020b5000c0c140400101c400f4650051780610300601102101886400c11f540c00c440c0004a07100c000700440b614400281907070b51005110f40241d1041c012191200c4014111104404010020030110700810598807801154014803520011106000301c01d419583c4c254551002d0074400f5509496100200c10303111007600d440c490341d54a038010032040c0307085041042d0303c90103820810310080c20140410000d07005030000821804000a040e021600320307902008605804c48000c010940311842c0080d203500c40c3e4114505201215041c045c0903141c0400c49034055801c1403d5440142955407400c28031250320103e191842 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 975674568 1250 975673318 975673337
    0xb03070507021f020f0d020606061b150408030105040c0e031b011b050307051e030403060b310f1a09150d03030b10110a0b040c05030109140111070c031101 68
    0x1942081e002c0900f02c182c0341c001e0301c0b004240f05007039880c04110f58201c204540c41321013801029202e400c121115800d6800007006106c02516103945044203101d1844200c10466007000103100f00000910f068440c00c440030b00c4580200c00080316808a075141880e07040d00036075020144d0b0540e410b03580e880e00b1418144028295503c0e0075001c100d6a1030007007520706030030020f456400c219060048408034400d01800c8080e000801600a075a4000e500000380790664451305080300b9910410444109100f441da203005855084840801580600000c2c1c123480342415841d0501d24030038001c2100c1514000d02c0c11a128441c013040009682001e040c00008003560700115036552101034020340c040b030194901240402c1c003001807000360388040a2040070406600c9200044031000300741080c0041c5c000c81d903a036054640f070500c0c0319035022550004e07034150300e040083c008104149842080c1c0b01302c1e2100801400700c1c003d55050075803107005d6004210350107006043c4000b414066019800907810b14148811 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 975675818 1250 975674568 975674599
    0x31a04052a0315101e050901230114070b04080717030906010f0b07150b1e0319022101020d020d061701060e0105040e0109021302070308010803040b0307050702 70
    0x8041240021030070310100c00c070440665007030030421401c0503901500001500e2520f2804141812980c1c010444200d07640441c1d10382030700c40c81400d5000707050014942c47c0507596030344403200c40314620801c9031440410036401240c0e0b90300a0050001c6603810202c01440c20030140e45082a0b000002c204031a11902485100c021130300c2e042c91085406080c3d02900c0d624240907814500c1d00805074099041c0f45013025040c0003e20118003900ca90960106641c0d124002a100a80140c28109a580e4014215101c140108040c08011502407101038041d102a98440001e0120300c0340340d03400207504403520381e0400e050740348100c560160b41404500010700b00040d02e10404142e80c0114030b01d41d4903036141c020900004044241405070004040020800345180034100b500c1080148115445103a545070b8021445d0700c02e40054800581c0141029501119071155034001d4104001c1a40050048000494214800400c0328107840000c1e9266003141c0e20420100c59a50028804036000710b00d82d1080c2e0b80 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 975677068 1250 975675818 975675853
    0x20304030309051c0c0807031b0b0a0614060a0813060e03030403080a050f15010905060301030c0e060102190204090f1e12050702012f0d0216060504031a0405 69
    0x554420703980401c60048504080f460106100040050110500e1265080c030b500041c19030b040d00e07402103440d1f888000d00c0c10203548501d51403407560307001204606074a00b00001e00740481c0c070400d14010104036464403044c41c0401c4070103801c181a04001d0800440607410700070032074550700800240400806040720740c1ca035002e41b031a04103031415642c00403060004058205401950001c40502c040140746032403d004481140050000742a682c40080f58000c00d134401c0e59080c01070040644481c0d80d0f0350307503894050704044941c81011000d443d4480400c000b0340c400300f41c12308152203100141c0080c80181d004c00c0000c0c032410200700d038990f80840608000401c06920407094442030045100f101000303050825440030780300c95800803c0010041100141e030450140c00c10740010030612001e207800710700c120f854170a5543c5405001d00c55102804910fa41c0021400b2881280180c2c802c0e0b6242d45200c245e0310341c061400014149801c001031000e20b1040b140004e03500030b0042e4201d41411104050403007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 975678318 1250 975677068 975677071
    0xe0606070c0b180a0518060f0328050f0307030215061306090e100b15031815220b010e100504020d0906050124050a0215150414060f100c05010203 64
    0x700038581c040c0f400744061400320001360050405961406460120340c3c2da180c0b621500405152040c40d081d02e120301c01b900c0801c41040c59025555800160245144541c800458081e074100d50504c5070450140041c040030090716003865250300281906001070001012541e401000b503604074007001c200100822260140e440204181032000070f41a0300388407894100f01058100000c0f00d0304186007422103864915031004050f04007680e2507201d032122080381030000794030030034520710344211110b04040d03440c001700d0030307020784210440f1012072080c070513404580040c440005090180c485004010b051402004d15504c001d0000e001a0700c0d41d1a2000a0100e8001120581803542d039900f02100704005441a10701524249048402e0440061149860042100d11040411801041c91355850303000b04900c100809544018082c54600014158003815504d280da80c031950030020b8004510a407410064024240904030040c2200180184003440d018000900100032044c0310b1071022400c20720145 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 975679568 1250 975678318 975678337
    0x8041113060312021b0d0302100e014811060f09070605090604210606140f06091011120c0601080c060a08070813050316060e070e0606070c0b 62
    0x18401d0035403c0500c0ba595903841c3d9003055600000c0030b5013403c0b204420752091450200c079003008117030306c0e441c00b24103000b980410744181c0c50030700305480d01201040d0841101101e881558010305a0141014035080c00004d507841018007060500e60498038400001590514003801c001b110319400780e018601c0c11a08507070403900494100144901d0b50028886080108403502d0034600b0b1030b83d1000011140d100da84622101045401d850a070b003e40c440340781c2c809840d000b0004102880c0e859100c0720010b560405068464081d4115960365443d1040070b4070802c0c5d101501680c000320018100b41c80d80b1149940c03440c1c9601c129070980303c6041486005022950301d80c00640029403500c68110301e00440c0f41a0380344034039820f10100c41d0503503020881990100c0a460440b6031610b56000f20304c001081c4100280c00d5000000e6414a0303181410116404144111020030100b100451926180c94940c0600c0004042d614045092440c1480103854000e01070840500c02030b58550310319400f0f0f07003d07042c0c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 975680818 1250 975679568 975679571
    0x90504140303150901060c02210f1c031512060b1201060801091103060405060a180605090a0c09020901050a260f0a05070f0f20030f0c07080c0306060108041113 70
    0x100383e0134510280b500404442c10200c000d182103034009003800031086040c0384224420303c01902c0b00c103010000030313840403610419111007070180071a8102e10403014600802003800d01c07840903920040f03100e102c0d044818602c141c2c000c0f0891991038a001d03010084140b81c0c84401d500c42403c4102d4203102d030500510345c0030b000140500303280c03a01c0f04190301211003491194101c02c0400c03010400c0030500c80c0d40158040c200051a0701c0003001d00d880328070000c6e400341406103003000300410000700013510240da6015200b02281243c2d1200048164801d00c0340c1c00d40054400c1c03021881c805e000300c60500034001c0c00300f4203c0841401c06c4a13801d030054100d800d9644160000140b101826003481516000b0403546444e4810300010a8080c01113200703520004c0400200c1c1c3c0f0414080441041c1504c4031560b4001681e0f919001c80c6862443c907000094a0041401240d100081ea030700c000130740b400404405000780a040c0c0c3c54400544070400c00900c1528002e96502d441072507692541151450452207550 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 975682068 1250 975680818 975680851
    0x60a050a031835032409061c1403040306020409051f05060711041505010f05040501020d0503061906030b040f150504270503270d120509092d010303050301090504140303 74
    0x10340700456170020500701d000d1032a1005001250701e90f600ea120210030070b004000200c0c4154604041c2510011500000c103000106002c030402503607800420485092a40500031516102c01c0045004204528131085803c0008100098101800034242071400b074203014041041c3c000c04603003610210b8081c04074003025083d0a206941c6c01101c2500b0400c190716002d81400d017000c0000c0e41e46e20603001a0310503c5000300000b811039a610904c5c040703c00101d034210b88400e56070403000e806400c506401901c00c2d41000000310200030507102e52103408280c5a1903a681500e0724003440005d0507006883d4001c3c604000d61242d55840741403030b41c50080d00c580000e41c0e03140138401d203440c880140844080307501c0000e048a56141d656070090000751a81204c9080070654919078180c07020300c81c1c0c14505030010300ca00100511500c90260101080b08907080303a021400c2c08145c00303a80c495003404000d02284040c030041c02003641a900c059845486011551048031104100034a550011100e50348030341d0003d017 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 975683318 1250 975682068 975682111
    0x30103030f1e03151a030a05011703041215180507060216140301060305061302010e0612150f030a03120e03030f0103080a0c0c0909050d140f090f060a050a03183503 72
    0x4030703641c01808400c8ae841c0030032203811143ca49910847c40741c100d4503411104030351305100b2149501d081c90090074100b0400981510540500b04006c03007010b45003802803100c0064020300100d02038000c04c00c0d052204861500b0040c84000141c0300b001025055981e5810210001e1020000d25000c0d10f444404004d14142c2c1343700040840c003011a0960184c041071000d03c0008440c04c646035080b24006088034480008880426828000340240356450310820072503c0078141c01102090801204903014449000c002d8211942d034441a02d1914041003c00300400100301010007038102040c0900c2c041511304c03d01e0316814450201500320362403040d6a210000100701d410040300e00c030ba1802d800d160100030400c407060400741c05900913602c0303c202e0006400f000741d07841d1600310030444801000d00345c03104404a0014081e4001c0080900803a10380407024080d10031131944000d05030b41c00003150140a6202421000919031040307801c000034542804a15070010000c05180300700000d00006180c200800d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 975684568 1250 975683318 975683321
    0x2190c080703032d0503010e060d0c06030c140a140714060106050901110c0f1c0c0e07200c040e0114090c0406090515040510031502030103030f1e03151a030a 69
    0x8180030310540c04c4000c640054035401100351b90440b0240840381c03042d07a4030700d070200d0030a00c82120000c1c6411071034000410b1542c0c05074000584201d4070380c2d8000c4644155916800c851080e400a0804520384050b4200e220101c40010820b40c4d20582c5120100c07440b40d82094548032003a0442d0b008550045004052543e1022901d00400d0300c000c01441e0540040c00441d2030819010b0300ea03401404408003641e042502042c0d001040c5500020341c00c110760f91000c0740e144603401900c6540c005850312000c480f060031100110285440c1c9075024109610f640001c100c0108968500d00b04a55210880800c2d8903402c080c00b6071098609501420a40354410204002c44900c0d8101c02881d6103480b040c0407104040c00382000040310b0903a400210350311010005c2c0c0911000e5440101000d100040c4100c4c800d8458002e0760480e4031076140d6290000c6141c000342c0c0d018006001a00400b04c44c202507104044c40780d0845108180c00405c203640c040e8540303220009044001982031920304000050241c4131005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 975685818 1250 975684568 975684617
    0x3030c0d03320105010f110601030c09140103120e010e04090308010f1703040504113604020708090f040b0a240201020c0a14030f12040b01060f02190c08070303 70
    0xa0071900c1400703169100c0b004012a8041c02128100071030f6100070b090b00c6000b070090301011001c003012500f496949243c1485681218002e200b001400e00e84001c0c0350400010082d4160381c2d010403a848940307020755007141e03105909a5180d04004140c00b0a1030140c03694480e100e03440f4002e6403186202c1d03060001902c140c00d0b05520142d610343c810041e0780170003007021094a0030398ac0c1c200c83c0402c1031034141c040002c150048204840c03042d40303580e868040c40b86021011000300010381d401d15408a071500b08100882c02568000781c00d41c0000c0200305030a2800d007c182e9800b0300e0040c0001a00070407a00403880c3d0354019000a0b080045040c41c000d070008038045400307080156407000758a030001c040985900c8090140380104000c0b030500d00e400c0c800030240203942c180c14110300d4041d100d04c03024082c000c8042c0300761010740308042041c00202e1100c3c808d41303a1b024000044d400401841840758080c0c0b055000c00350301540e13070541c081c001182c9180240002001580695621000c1c001080c61304140c0c50f04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 975687068 1250 975685818 975685871
    0xc0204061229070903080c01020d020408100e03070809010c050a05010e010c0e0a0b0a0503070905030a0303090311122a0a0501060303090e04021305131208011406180d0203030c0d03 79
    0x2038108001d01c180d84210b0344c8050b45c0d48403250f00d865040103122030303019004450701420301d640041408038206400003583e10504094042c10b00024440c429107a88a12544201030710b600c1d002c21942013070b540149090a08140f0400440d0403150380303620350500f1220844846412039444503d410081c503400b44400550000c00c4038089145846c0c111640c0241c840c5143e043c09000010000403001da0043c034504005207005400e540400b0041d20700140180030100040700403032003248056a00031400035102260f46100b03075006150405403030700951552003103502056500100e4a88151100c0c041c401c2150480c490800810b1507811841c01510b4100a9040a11418201001c02000d0399540c1c296140e00b51440d1800102512052012405840303185800307011741060409541c3c0c4980d110482604031030701150f07040c0410440b03a0801060344900c0800d5007011440c1142500b140c07610403190b0881e0351004040b6403405950003030050900840f52003050100713030b035010f5010260440d002c9100c1401c1c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 975688318 1250 975687068 975687143
    0x218040b0603060409021315050a150804031202070501061806060206090d050d060e04030215010506091503150a080c0f040506060a2f0c0f0604060c030c02040612 71
    0x84280c0104405020041c5814442c5440e10407080540d103815400070080260f0000620103440540e060801580251007460b0007420704d102c0024140c1c1c0d004449485540c81d40c3c2d00c072002d80c0c60f5500c00f11081c0080c070f0032210303440340d080000b540092401d10a030002030038000102560000308448003070480c0c900354043c0301590800001c1140985020401241c15440b608100380c07100300b500201c800070300507a0003410414014006000915400013410307925442d00001207100d41c1c2c0c80b902401200e0180000c01600302c0d1102e802d0032801481400610f07401140c925412081c4043c000008107014090790002210350803c0407000780c40d0030400d54035803007607805480500060606402240d020f110b08140e0b00204601401466004600e0101c844c1039030024075503861800118092540d15810f140d07290920401d2016003540319810600b056a048400380d48940e0207a15150300c0c152003090040c04c0890380142c2c7c451021441812902111217514044e22068036121080100d105021001c11501d0220b103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 975689568 1250 975688318 975688331
    0x122016030606050f1503221a090c0f1e09010b04030638010311190206010f030f08220b0301090f0b210109150506031009171b060a021804 60
    0x29107403001880c1d4415030300c44185d6680c0d0390380c000400c14090707403a10141012079641c14640c20f1142c0558008a402142c00c0b0000c82a21041c805660b540c007000062904036014011081e424940460242c503003880002c030340121007868900181d1005801d0700036094203c000308040c8140000c520074402002c12503918041504910b0515680c192691400f0740c0b0003500c000000c21141c1d1003a0004017183c007151890649464250460180d8900d401441d00014400c1c0400002e40035440714110003201d400c030420344e24030546500e400805074002203004460b4070740341c0c14403c0340c20038049824004040241c0301031348070350601c500031050303a07889070380410414103048180c0341c0740d40e540c64031006a843e000d50380d0740d51145a143c03036809019040070240c0f0660b03142c110181480f00380c0c0c02842c41150101c098075145070b081c0c08681c04850074042d020f4040a001007006c0d05a070814001000300d9050101c1c03506039100212000b616004084400340d42240c1c02240100c10b0780840165000d40043c125010b010ad07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 975690818 1250 975689568 975689599
    0xd020c01081b07060f0f0e060c03040f030903080415030f020c071401090315060e0606071e140109120e01030b011403151f080601050712201603060605 66
    0x200307030000d800091000c98400c49211282d00c6202114203207a0b0200041c0190b0b0824240100100340000900d0b910034100000ca401048002c6003603403062160040c510304549450321454820901c0e408c0890500030445400310205000c2405030004211a01c0c00c08406034201c28000e060b00e03110a00410114018042260300740c0010440e40151080c045842400400400040310810344641c0060151004c080c80400d241404d0307081042614020a82d076481c81d2221003d100041c407e084c0e015000c542d4200c868100d480341d004440070786e14092031556007400150a82a402c60784416000c403400d83e951401801e01d982c1100580511034000d00301000b8080007400080c000f401440500c40c0443c80000000320181000d40075040406070103017042c84c0119098504c2c4138207460f00c94000006c10403c00025655601c0345c1c2c21101b503158420940c2031544800002a01c2103a104841c3c2a50078400361075401e540f0800700503088040d6218000c0b14480c0d89107040002c1203480c5a0001070003581d805e20403819 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 975692068 1250 975690818 975690827
    0x1c02190b1c061d0a330e06060d020d020906030a090c06110714040f0204060809011821140d15090504050331030f061508070b0a0912140d020c01 63
    0xc410001040a01c4241c1d075010641c401045c10760104800b03403000016a4154148262100101e04024003400306000e40313070348005041050407211144d1042040054800c041c400c1e0b000703088c0b042990301c000350420207000300081c030503002198003001c10759903a02203105003c8031b10112801490b5505114403181500c604140d1070310518040e00020400000a031111a01da0303900800000d05044811511641c40b1440100402c1098030301703095960a007505070030008034034910321040561004021980340403034200d06460318000140c41040c004242c0304250f03201c5c8039078010030441c0328001000950000c90f00c031007054060950000340c0b40910b01410040054400070032944041c0c4044614120121040369200b000303520741091480c5410189030010402041c094401502c030f20880c81400085446102840640319900c82d803105a40111030030800c062120740240350820b22494040f20103a124a1094034000300d070342e0b08035030581d0034040341035203c4410300207aa507144051010789154a41c10000030f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 975693318 1250 975692068 975692099
    0x307030e070b07030504081522080904060906080106060c020a03060b130e070e0112030e0114070c03050d030c0c201f0801140a03021c02190b1c06 64
    0x9140d6104032150300040c04118920080c6015095180c2d0b5116a00d0010043d030041c0c0b043d400f6a114001174409160500c168046c89494840244c4038000407600c5900ca01d840031003016240900f00308154942602e4074001d4030090080410302007101841c151203282103031002d5204508000b114941c1c42c005903203aa55100c01c680d00414040345000902c07001480d9408010b10003580ac600d088103960240d90081402003c45a9003100f105080e81d0310340c104400d039402048010001140008104031035070041c80300300c0c01030790721010507814659907542d100506031180c0c000b40d91962050700c240600a905001d280920050f9251445d10468659151003141840001511020000400e0b001080c0c885545104054000c40161045071140c001c000e400aa401c5c007e400c801e1548605818403070403c01c003440100d0703901178068141400720280e0b0407900e00e8180703c101d17480321281c1611441c48405282d014054010903001039902e2402d07024203c001d800e031107100356510381850802c2003020900398040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 975694568 1250 975693318 975693331
    0x20304032307150c030608060702070f05010e210c0301230109090b0103080d32010608190905010f09081b2a010201060305010c050714030f0a180b0301060804020405160503 75
    0x1149480c00501c4c260098032440c0c2004090b48200002c018045e540002c8120440f02c40300105088030f52500011a00c0a04000190b03820006213514503901d01d5180300c0c038155000c000815120b004104400081c2900c40003104400004190301059a00c1c0d03031680c45040c0144946c1c0c80810541c020f6540c0d490601c401480f000c2e11428011891000d042020741246d5580041d407d0035001c800039201d504603000d1801b400d042404140704002054182c081d60b58070340185105401c48500103040648a00035140c40c07a001c489a548908000c000040b86001c5d04080601c640500b90b140e084041e0f150b103507810140039483c0c05600880b03008001841040019049803400c4500d11000100c440c0180d001d0403047d40024000c0d032030084000d1109a20030040d059842c402c0250030704900c14400c0c01956809006100c00400d5400c1120203140c0d80600b004501a40d001400034000c15500c00700e8991a800980c004d038045010402000110300d41441429408907690704500da00c00b207000307030060443c003009005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 975695818 1250 975694568 975694571
    0xf01050706021213030e01021204090b031c030c0f03090803070e04091403030105030c060c06010e091005070206250903082203060c0e1e041a0402030403230715 70
    0x4042804001c0d0125100260100c3e8008001c1c1007000003035200d03000304002980069400d02c0042c12a610104103101c000540f485040d0400c0c1c00c005072000201905a980c1354944248140e1507152107103038405204241c47c85d14005040030b44070701c0280040d49080622030415180818a00015a854064a40040261902c1001c200404c00450004c0a4a000207411803030320001007180e1030320010007941a10000c2d400e45150b503161400f070002501440103020030350b40103800148078400c1603400840e0310038403180c110303481c0040841081c4200c0d00c0545070100140c00810070001c44050655103660700c80000b04594903848261700d801000b03007502d400000c1c0030007400202281e0311120952112003806000860000441d600d25204e001407065a2903400415100d0000704454504050768003081c1c080b416043d8141f100c00001c002c0107004841813184040c2c030040c0c1c1c44040b03480c3c6101651140d4400c0d113518402000882c81c80c1e82028020049002c071070380800058001a021110011203d04038460 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 975697068 1250 975695818 975695827
    0x118110a0614071e140c150c0705040506190905010f27110c120315060a0c15022107170709170f01290901031e020d0c0f030308090a020f0105 62
    0x461400c2d02c00c1c8041e02508101c51750049404810010421043e14842103601d25001685540c500c070700f83c09035055420301078000ca0301c20030481c10581c001550120340240100c42006c80d0041c60301ea06210340d081554407a588070010f0000da841800980060112080d0780b0000215140701c00c00130080c0b402418003540c1d01c522520260002001c03d41c0d00c032034441c034140d907542000c034038690003160401c5441407000c0350302e075031081110306000040fa030165100740d480341450b0710302d6102c140318440c0010075401500d600b0000300c0d117504001085422040c2c0030100000140c20040c50042c80c4c0840b542c4881000aa46824090601d40001660003211850f07145141e00024050180d414401544100d00c2107508060b45a2004907000070702c4200a108000f240308012015001d2000710340007400300811510381440d08840d2134101c1e1004039001d501c02842880300c290599640c0e9929905030b44013600c401c0b0103d0017441056000201181c4c031525020003440c200c103094001503803c0984501c282e042c40350024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 975698318 1250 975697068 975697103
    0xa0f0b060d1805010c1d0f0303042117040602010c032d0204080708010b0a080d0e061813051009090503031f150c02012705060901020118110a061407 65
    0x100041c041a40142c005c0001c1000f41501603c01100c0c031090000e040c440210800181c6010301070113242010103001141018100140918051031024004206540b1501d0034400944258044110759070581c5000d41c03140d2908401900b07480c40841420141810f0100401c00b01e20703006078101000c0c1d21041c9105d298205110703544000e1099800071001230140482c003140c02c5105411200000381c0035600c1d00b10310b50303681704140d480c0e4501c0c1c01e01500003421100c006071a032808402503e000c40e446081c00d03406000e038500141e400412526a40075a586410420039030882c5180ca10005044912042c001071406a80e071a842e40302c000c050b09088011f015103c038404460984402c0500403c1c0080c003503458004d84041c1046115200490001d4a061000722050600980081c00181d08902e50031085060504110a40c0c10401d0024110742d81c6902903581811414130a8294138042c07041041c1e100c000c0f005002c450005600a80113000e00017802d04d801c0300443c41241c0840d50002e100c54000714914 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 975699568 1250 975698318 975698351
    0x3090c011d040e1506010c0308070305060418030909051806061201020c070f0e07090503030d0b030f070f0e0703060b220510080f0106020f150a0906140a0f0b060d 71
    0x245145402c40d2400b0600305900d0360000b0000403404154000c80c88603910b0710300446820071318000090014039040c0c00b0903002070098215a8009400410110383c202104030340342d01300480208140c000909040003001490150305c00c0301c3d0000700c1c02d025110002d40d01c110040e5a100d0161001780030b003803040d10040c0344c0d040a5058400421600054a1506030390302d0b03100c0b164441da401000c0042982c040807035076490050b10441c0403620040e01031401c2c01e0b540315034100180012140c444c0c1500500c495072142c040c0500c40b10780507000c0800741e0072400d0300b007080d613070041c22000b4106402c0c50f1801ca03090101c81070301c1d4169904880b040b080d280c1c540da1000160f0310740d6461036100e0b039000b1450004d1641d000d40c1003a1014465440001e2103969a81d03201012644c40a800c0c000e110142c200c00507200070311100036485680849040c101088084031550b030304080310a00080d040c0c81c0c4141109209443e00300b8014040d440030041c0e01808030070b4030707100040c0c4144502c021100d111551401e400303d00c48c000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 975700818 1250 975699568 975699617
    0x60a0302040513060f0228022b0e0f0d14070b03070c1505071413261213050f031c120e0303010e01030b0c04030804082103090c01 57
    0x10703005001504101103d0494414421411902c01e030a080514a600c4e101d8401d45941840c140c4945440c500d03030764082c40450290f1403c50046000701d0704800c840c44194100780721900c1c0201d080c0c1664400325132008015401c1b14a441c6d01c00c800707510780121982d44001c00c14901c20f4010103540c10742d680041009107480202c0e400705405040100411100581100d0308441d89809200a040e00c2c04075103040380c0407039000311260307400b06000ea80003048540c942c10180081000c0c03011000a5551214407545200918005401045180389014103401e04d09100300b4440c0400f81500b44c1c10242d04490f03200e0000d245000d0940070396940c04480e5110350b420004411044c1155402202541031058010008180c003800c00c11941d041110308000c62000004603812603440158510b116406c59480500100d00900044081b0405200100105010030700030300080410074010442e1000030003079400e2810600074800015082071081100c071590209500c040c42e2001d00c1c201d041110144614841402d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 975702068 1250 975700818 975700823
    0x40506090111070e180c0112051005220608030a1e0306030609110f0d0f060b0a0810060e22030320040b0301090f050402010f08070c021017070203040f0e060a03 70
    0x108840080c59201c035110807400703031010203044005c100b8200302c0e031991b83d804c1e04810b900040765807403112840110742d031000350000e8809600b07000c40d0f80c1d02c000245426007480b1050320242008142900f0a00d403a214040040500c08003030360405100c0c110241041e019000c1c4540000d036801000344c0102d2081c4e000380c000d1940010100104816801e2610301e072500340f224180150f40c103400744001442c00d0445024100d500014821102441d90303038440140c4007034652290001544103020403040700511141714103814a8100103181c9250498180d22604080d051004a61b002106140080d0365007030074040032501410301144840b11800f02041180d13800600b00300004001c80c0c04100c040c80b00d80114100d03103031020180000302a200b003030000c94100351030081c0490540c0408880349405800724540c083c2050a14503e880a41c2e0040b40e2003803d030300e01400001c0c4103554140d251803600d01c01c403030304241070340b005500305410b05144801b00c06040c0038000900c400440098081e58034980030034007555 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 975703318 1250 975702068 975702073
    0xf0503071e030203100501021b010c02120106031a070f0507061a09070c03020f010b01050316120f02040815101a040f0b041a0f0405060304030318030206010f1a040506090111 76
    0x1c44054000b4001c0d00f06684008800820202c0080c103507200161031400c6000300040b9841c000508401516040d605043c12a0004149003030641855004e1285400a500418481c0c95122040c0c0044c8404a001419682409203105840c0d01d17003a408015540d202d5801040010f411803807d85204903c5248072146038010b080c030041107102c1c1d42c003e0142d100180710340c007140c420f4404003108038261011011410b000890510005040103c02681e0704070487c90f5003004000e040d920300700d26080e90001d070706044515400040820024104000304a4110454044c07502142012b1091140602c0d05101d1880d50909070300b030340034850352074908460003070907002d2000d8551a9a88601c00907508644504031591070783c0030f00a60900004000c0703070b2580c01c10742003091506040c1003c000483d00040c2083c0c0030035986400d0840116400c0041441c03460003a0004d01c029803510a01ca0030300041c5400c00761100510202c4106030003115016038050b41c1007251496180c10b6241c00481e4180807081c0003001d5403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 975704568 1250 975703318 975703367
    0xc080115060e01031407050c010e0309090a0207080c01051f0902030601080406020315030a0f030f080903040302010305070302160b041e03021e030909010b03091b0306190e030d02030105040b0904030f050307 90
    0x31b980200080c08409001c2c00284551070003011b04031f4a034000c3c0d03d00c258101072901d0000e10101015402008040d10600c07400e4201148081403908468084540d001d403840041c0c6203407501c0c2c0c41100000004c164800040d803441c07410f000020301c00340e0702420040c005900070000c68003003111251030390f034080000750854503c0d0703c441c00c007010b010319001c01c2600031407498240f42c50028480c1c0080c5201d00c0030a4010351510b03103541e00440040000401706403c00da402e01000c45400345a04401d4076160042c078810107642881e081030201a520101d40c03a6401d02d4101f0701e240001d4000c20f4206071020003e44603111407800a014605600c40d075401aa400f0384444000702d80d40b0780344d0024501410b00e1104071403041c0c003041d01d25202e02c050b8215003641035000b01e002038001c0941e4051619103003841d420102c0c05109082605107560081a01c4803101c540110050125003010700c00d421021004958681441c242a18080c1c080402082c40004100c0000000b4001b03e0081407003c80b036183d00c1d048480351 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 975705818 1250 975704568 975704581
    0x90204020d0c052104241503030c05070f061d12030a02030309120403030504150e0307121e1e030c0209012d060504060c1103070b04030c080115060e010314 68
    0x3d0361029151444c2c0814004c05902c20b994040501489280d20070344882a94029940043c20b00c1e440045403070945448045003032034030f440b241c8004011440717a165426101e00a10340307181409440d070441104142c49030020001242e00844041648404e4005240c0b18051180440c44031200300f00c03180c001d0b100004118070740507800002148a0640c00040e2071012024001140b183c0c17042d0b202c0070f000194240301c00d00004c0000c204000c62529282400300100a0241c0401d00b802c125600001036114002c125a003480420709a20100c2c81031805900c051460f29628141d000807800507500d81000d080e8601002c160080003503e00c803c4d00140141c460b5a598081040c3c06480c0310003007101c00303121300101c40000140c004170750b055400d19140c00c3e05041c00c1082c1100c85000d254410b41e00c06091143c515070f1610240403080140020700c455560302c0e421401c110814903103540c005203c0380c1c9440003480501a50050301d2041d119507142130b5080b0f8218500480142412080100da4450b001e028040d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 975707068 1250 975705818 975705827
    0x160c03021011121312050903011b030501140406080d1404180f1b02070608060307050402070503030619060f081801050f09060a1404020d02040e03040609030203010f021606090204020d0c 81
    0x102c0084118102d0104c0c0c0d15209801100441004010001d6222254419640d400761001d441e02d07031005400041c00032008a04003051010000c02d04000c00c0e920030052008041c3c1e41841c00813110140da0a00403e0320304144150b0780c0740c45040140070009688000702800c0b844000307d600030400b2841c01030351014484040300040c00c1094030b4040c500d203455801104401459100a9108119006004c4140c42c0c00426251008018165640750280c0d0b48003048075640d9102500d001c50103a4015600ca190050074009510285820080313a020401d80420000743d000c42c940840c00d90510b842c3c0c08036110b0348036822560300f004000340c500354201030811405103a004140762290010404544c9141c48102004044800e40b0111204d6525550001409418202c150501561000d04001002c40c4c000b0091030840d0015000100002d005a20400c154582401a51082450084110b29203012001d5001c070500c605440280700d05d48501000e425561380b80c0c192882042005401d00420102c03540041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 975708318 1250 975707068 975707077
    0xa171c1706090105010507060f1e02130e010312030b0d12050a0f08010f060c0f081615110a0e030a0b07050a03060806071b0641160c03021011 62
    0x14040040d00300080007407030720101441c101d96040c0c590030f2070a0140e481c0e144c0070b0b01d114445000101d0700c44d2100b64008480030006c0100c01e401200050b281d1055580c401c0100503e41e211070f0208100d800140040356880050000a417000d09000644000b10300115059410310034011b422018141d5803081c1d2030b41c1281c0141102c0b0724554070b4012100c03118400340c034000f0003806280c1202140c5031003408120b02641d00c50742440d000b440810b080b0486a642d410060748a1180546807400172800c2030200b04074200c0781c41d00c01410007028400040c0c1003521a6090189502ea4410000a641600324544003840381c9100d00d90014140e8200d0715007504040e0499101030300c1180003d1400b4000114146c02080c02c6010b84416513034545240d02203950640c61404c001416140301d9a124510f0711461720321040c00409145028060348401c041240d00b048120420080300315152882c0b00300012068592a17404403400b4900b00105107500720b0504a1900c05610b806084003860058a560315902c0440501b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 975709568 1250 975708318 975708347
    0x27050f0d03091a07151e09050a0206031501021b0913030e040e0d0f0302090a0b0702060c1b1c030e0919060f320108040f020d0f030806030106050a171c 66
    0x10780303544a019000811190300320130191404030240340106c0b20040750740010386c5203030040d0b04542802050380c00007081c5500c01e60b40400816102c88100d01156014040c4a139171007071282c1410102042c51010580000009040c0752844a440c00c2a00415024416408a0030700140c0108a40b00941c2442ca944414440c0740c2c00c0400d82040950340100c2c440c1c000c580c445003025281c0410503141195000464100c5601264003080a0002c15a01c610401500310710240e90110260384400700f800344440040310212100580204205007004281c11a10f50404000305541034507495560083c00e01008015141c00c00c60b0600f48500003494100c7c000e0180b00391442c9070111504e003190803280071100e0720480414201042071283d841d450790f0180880c01d5226000340010ba180c91413a40c00240e220082c843c04448110201d825401456881401c041e8031807402c1d0020082d043c00c1c4800190a420b0310b10030003241510403040e01588200c240000810940c00d07500c448004640400068030041e0172901c2c0c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 975710818 1250 975709568 975709583
    0x40302062104060c082a0a032706050c03040b07110c10090512010c0206070c1e05060a2409110d1409210301050f030106031227050f0d03091a07 63
    0x45840807440710419002003600c10f0340600364017140149180c643d00a00140d40508d992030100303111054000681410000d82c01e00d00003148000e80c5000000c03120050030300c0402c00c0e024003c00c00060001900c0b84e82010440c1800c01c002000c9003241c500d0700f140400981d8100c945d082000c0c0009801c49050710503074404640641502c240001264229440c07009005c3c01640850b01080b0f40f18080d1000c5540c0071301480f015105d19400c901404400c40580104580381d500650420200b200743d8070a21087c03800c00c104c80403014100e140700154200281c041c5540710b0740c0c2d440c0c6d0245c092030800120380c04403050040900490b00342c8401c2850760841183d105a55006900c400e030110410459000000d0800c2081d49040d64240018005100000c035031040d055965100b0100209000484c40d143c9901c20b40d1f03d007484c1c510b1000761086081080001480740309864441403000b942d0b03103d2034032400e00003600d4407005942d4070308080303482c1101070340001e02c103100d1816007070700e40e44e240c0f001817039441d008100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 975712068 1250 975710818 975710821
    0x307060b03060403050304121103040f0905060d030e040c0309020d0812150915010c0c090e010e011e0e1e0607030605010c0c0312030b030321100605040302062104060c08 74
    0x240350321070b001150000d0004504000140004400404080102c0d416140214040c2054012146540c0c001d13080200e542d04000005c122a04440c05603640c00b03001941c00b84a004081d95000d00400d61400906204580702d1401040c0203200e030748515003c0d60018001c00ca40016030414041ca60700c0703510a85841c81404001583c1d03504195828401d00750081c202070b03034550f0740500100411042d0345d01c0030304105650442e0404a005640c450000c0e00400e040000c048107000145421a8003401403003440380d0401c0b4646942d001c04a4070b8410300d00000d40e01240083c2203040c01414038070048441c108601c01041c40b861400c0303001844512034921a20100981ca03103850055130b00c00c44c4810010f008010225040c40040c48000c82c4011404050801007440c02640300002c0c02d540091000102041031080c51800607406012039a410084c909056500281482d8008140e40f00d0341c0000f90064900250780c403480841c0c17806d00c10449141c0740c010480d40c2000c0c03a240b405040713918500c4000500010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 975713318 1250 975712068 975712091
    0x30b0709170309060d140403030e061602060c090f0306010e0a150b0703120e0109050307020310020c030315060412061506050f12040618050319020303060114090a0b0c030706 76
    0x41010380d0455018000c2d41029403002c2008210342c000a01540c07002d49800300d130482a1a85081c09010340e20a8074045047c0c0321662003180f5040d001007548503003029001400c540306402207009600404a02c041a503101d1b03240010401c4617a00d0514990140304040000401146402d40e9074021a40c2144c03d000d4545000822aa803a00324015250081d00c20081200003e00a01498483c80e6581c0300c04102501c0407020705007107805424040d282d81e00001510002c625007407141c2d10002c080101c003182070021000c251680c82c04010b00340f00c050740100380180c62030703603a0406407401001c243e0304807105801c1c545000d0001e0b0810b014441d001021500d804103041c1d0189040d501c8000c8d80500c5c290403c0703020400c5a1600d08080c000707503401030b52001d044000a4140c960361500c28062402140d03a1840f64480112414032140c050045420501c03d104e1a41c0e8011221070a0f50054030020381c584101c000000c104400039402881c001c040002c0901500b0000300c040d040712800f079001000700c081001d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 975714568 1250 975713318 975713339
    0x602061605040504020306010908060705070212060112030809150c09010e09010510050f0d0c082707092403060b030f0a020f060c0712080304200a060f18030b0709 71
    0x50080800300710144400e00040c1065405140c0c4100c0524100c2d031019620100e4600780381096500750300040000511206504120001b010b25241d804010f0150790700d8001024200c49001c140107040100160124549a80411176680c0c90030a11071056074605102c4009a1254020354032107000c244107811050144ca0301e134005904035a40a00008109042040c00b21202d6025207804c140b0800b00344104c1402c0c0e0b4071032151004051440e21012128107006440c0b1000003400700c0100d90840c032038120890039001c04901a0100c4080c1070b00032070100d10341080046a00031900348000c003e40200f0002043c4407047e00000c0c0138070310a806550742501c50345031094840100c40380c041e4009008007000b07000c509107040245000740c4580140c84040e521240c0a1508a55904003503600901c04801d0106011030b814200101080180c05108510411030100c0c0149000d441500280040154103a0189000c0d0003800b119480886044862030b4582c50016441001640c407007001072000708000c503140403403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 975715818 1250 975714568 975714601
    0xd080708190801060507210302043b0408090118050306071e02070506070f08120411030111030919390b0405010203070803091e06040204050703020a090e041713060206 73
    0x3c0000902c0014201f0055181480380b8411202095400c100c00220300c542c1007080c145940d00109802d103039885000c01881d03a901190a0408800b540c6414080003485443c101c0710780711030078201039801c1ca00d0600346540c900c455030310241e0580500e40400408940c055000200b0301c44c45e80500803100380210b0100e0751105140a52342d04840b0410040300824902c0f60020691441800e05601d0081a64450500040180d43c201c92103e2a6118203005103400c0c040c40070b50b012801d03500750462603d6021965502211030106c0c2103039108486000520280c2008070090721a944008480010450706281c59000805503031501c249400801144d090040801c0700c081322416402913040c0081511500c200c3e610141014410740300300c3d0380020035034841c0d00407404200c51a001800c410302d000d005000664074001c2844041500c104140d83c0740a400414000a13a6454110880c01d50344525001810fa140b203a02406858404503a042900c504100d420007520040e0b400d8078020348a94040c48401c0740c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 975717068 1250 975715818 975715823
    0x30a260712031a01140912070b0301180b010509040504170f130906060906112109011d09180f0303090d0f020601120803060f0406090b010207060507050c0d080708190801060507 77
    0x42000c8030f03170106940c150181503000c1004020401101951030b55a04d0180300e5800b650002101000400c0314203405400c541e010058144280000030004c2e0000b0314030310507207545a1243d5594004601800301d40300c0381364040860301d0507041d600c0c0b2204641800641144d1b071000845940340ca400b0400001c140110000c48805889a0b100c1c030b030030404c1c15220424404a522203612584914687e13141c00041c5000c0300d144112461903640d11048001450702000180701c1c0c0c07400d40d5851010f002c4d615200c25490784031f42c4000a221b0312582501145040c4401405031032442d1001205002005501240b4081e80b90215140c1c015016951002640c03501c00034450b0600811810b0107600101d101d890003958040001000a21981c0012002500b1241560048610142d885d03c04100c5541c0400c01900070b040282041d6041628550b219179541c411940036601136141888a442000400000d507241c03103511210590300c03152005650142c04074551030600004910900006003a401081102c0700e068 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 975718318 1250 975717068 975717077
    0xb0a0c1b052704020630010f09020313020f030f16090b030601060c021c08071202010e191202031c090203060a020f03040f1b0e0a05090309030a260712031a01 69
    0x80d9030313400f080082d820001a10b5003100460250400c1601130f441c03549440a40c2641d10300081d4145003450031038070055000000c5141c41002402a07104542801449207907044840b440c2d844011000300781001a1151900300302c2c811000d80900046032442035005803085010704200d0800003c042660300d43c42881a4030204440032800005070078060307190112032118852045080c541551000407950000380c2c1920b01940e070f102c5040101e80e0a001d01c94000c4c1031a0b009051802200e50803042442e0502001050300c0da04a0b15444014003d00503105d00f8207220741425005c01c0c68107010009008082e600f244640503520000c0d00701d6003d8801c0d2111602989811411680c4a5559003240030a07010141d4020400c0303025444070050483e0010301a0480c04a100c025003001050403043c0c0e500544109040e800500c801c10540d01d00240d0308000903006405840030600119008002e0040144d01c0303146080700040c04000d10040c103220400894aa030342c10001c00d091b0301d188201c483c0030b5241490004c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 975719424 1106 975718318 975718321
    0x3040c0e15030601170c010c050c040504050a06180c17010603050115090e030c0312100503010903170a0504051e0309190f08070b03010b0a0c1b0527 65
    0x41180c01100075900058580071074940380710308106da04201006031003500748036081029480c000d40c06402082241440d0411603101d001c00001a6030040c100482040b100c0e081510351020240c0205a40c50054100281c2151203a5800d5036140ca56403507881c00700100c0e0081c420180d038842c1701d050b900c5041d4589003202d010f8130864010740f01c0710f41043c400c1840b400d8000c030880303000210103032130209244e032240c00441d07004015802040d019841c000c0d90604058021605110200200100035070130754498041c81c017a10340c2110010600d4000701d003c40202e444050700c400403010008140d0307007040f81400108001116040a0007441c400211041012411100e56840038080e00c4010b45806420303c030300c0b412a44818407958030203060006200318018880c41904403019844900e0001c10510030010103081c98160027128410541441c10103801541501400220900c008804040307 = true := by decide +kernel

theorem cover : BRFrame.Cov 975539568 975719424 := by
  have h0 := BRFrame.cov_init 975539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 975539568 ≤ n) (h2 : n < 975719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
