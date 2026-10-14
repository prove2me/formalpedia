-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3076
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:35:06.576983+00:00
-- url     : https://prove2.me/submissions/d275decf-792f-4dde-b481-496e970008a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 553057553 ≤ n < 553237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 553058803 1250 553057553 553057559
    0x614151605031c02030718060e040902060904050c07050f06100e0916140a0b0301140108181c020d020f0613140604050a0b0705030402010c141c0e030705030331 70
    0x101043c11141c5580d810b00981d9030720785001c0003000310f1820b0440b10100d04a1040500c9170680c003000d010030920099500003000c607061300018480d80211208076a11074104810440c01c6807220003e003916501c41c504907040c0c80c0414a4498541c0c4044500d9512000040810003030500d83e440b41c0c940103490b00064544224100303a480a0821b12074000118480c1100b030108a181440c5000200601300f4248aa00710350525070a4248840ca2110942c100845132020800d015180350030328021403402c008a4140c10b03804042e00d030511704003e80490150051181d010364803800800c004880d000e085014010750740d240d00300141441140304040d1101d100041440340044400c002030b50159004000400d14040d42d40760001f980c100062516042003000e105100050340c00550b0000700c10340c454041e08c0c200506e0400d2a10f800d203540c00d0605902c00c1102c03000c501070380028124034084025810342d1b160304e4442d0203050b924030802504002000c10245411a1208075085c0c012a03000143c101d00c00282c1c0e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 553060053 1250 553058803 553058827
    0xa171009082107020717100903020304081c1b0c0302010f201c0f0f03110c16050a05041a0d0f150c080106081e040303110706061415160503 61
    0x400700b8240c0105841e40c2c02c1c0046250100a0a0002d1184106d00341110110b0074010780c80f1980031054800980d216011001014000e10541d40030b401c00340121400f02a280d51010258601400c440011032900080c024290449481404060f078015013000045841c45d4011211445080c98140c20881c0c041d03940850140f42c203103040186d0500100414004200c24910310317003012060688020301842824246080b60840c41d912180400c5050009640c8204140c200c5030344160402c0d44294050852020030f83d901481c21142900d030103540021059171100c0c1030104a030400ca10996070924210011156403510b00c0c062a0304d54856040201c1c5c0c0320300c1e42d0f1307002807a240811005035031a4a4054540d441e03540550728600501c2186400000d90070314490b504900703110136500240c050b40010015081c98042d41080032102a00c0c20280e685907101e0a240e00284114015022070b4440014248180c0c50000a1070f6050b01200180b1480c00c9034010a840405000c50b8046400f408127100060040d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 553061303 1250 553060053 553060087
    0x1b020d15061223070b0c120a020609070501020105240a03081204060c03060608040b090c06220b04062709020f0a0f080f0a1e020d02090a17100908 64
    0x30001102000c2005031800386034080031114003495001c2003000c3c1c0c81990500189000850b124a0001c507074450b400e0500b03e00b024030702c104e0070315038401c0003030001e10007640080e1191182e40f40d201510309441d1a0001242629819904110a00a11040d0f00a1902000c001d0f5124240007071040c1903c90317403640c6010840c0c1007001402e0004030504e0403c8248100380c080d400c0d66488a1608000c81c07401d166001e0104200584042d05012903000003a0700b203401001081080b0000403c02c40c2c80d446051160849d07658050303005001d0346211074001464280c480280c905a544d603803108840c980c403006031154942105003411031480000140011550311520090080309c410b294902d035144d038509805005045890742903002c204103482084813207a1583e10254009145030404107088046500202000e03e03900c4280d03150501c0045d211041c0c003641d0307000741031804007607500c11b0b1416074507811003031a0001c0d107180290035000041615081c404c02e601c080d80721440f40045030704126582c0390340150b003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 553062553 1250 553061303 553061309
    0xb0102010207120206061f05180d050601030809031501080c100915031d06040b0415090503190809120909040201051b0c210c040902011b03020c010f1b020d1506 70
    0x25805c404140582400c180d072112880c0001102030284006601070000c040e4407402c1c01c1c840000c3c900176001003840d80c4040c2030000035038001e130440e400f55840c1d040480c4c04d03510013910039111b0b100340910050b910f2030324000d46040b60111409050503924030b2050203800154941c840d400c101c04020b0108080c45003100030130300007900350780010303680300b500c600302c1004125203c441860380e01107001c000000300d004c0112035100d5405a000c0c0c12625070b80316140090000604002c00c0c5004c0460301380390740c80c5036901680000c03070b032655840b0568581c6c14500b43c50f90483c0c1c1da91115598100130060705410820b080d590050f10624000340341c804881c0502d210400580403101c40da820089404c05540b610142041d043d0580a07081500b014140741c141b079031461090300d00ea010390313214490303042568003842580d8600d00c45103540005107010351400a460310185000c1601040c8510300d08040c061081c020a00385c540c0d600d021103460b01c55902003004190342d10300304480c01c903269080d51905540c503001e05c07002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 553063803 1250 553062553 553062557
    0x905031b060714010b1302030103021c0507090606020f0709110f0c161401030501050102012f0c0303070206040b090c01080f1b0f070501050604090206040509040f0804060e01080702011e0b010201020712 88
    0xe29400c40342040603005042c6c40072203400e4014001400541d44030b440c4800110703580000d07601034a0300303031410302d04007002c07503010301c00303007071400c0c400003901034000c900b1007085071400007900c13041070701d401c910822551405480c1031018000d02a080d0300b000c5003001000c900401800b210246400084001011001c0b13811032965168903013801401543c050103114058007090009004001312100d81054910510004400641d40308011079803942040c01103a0b0f0403182d0034143c1f9641c0c03820300006592900195001ca0301c0001d10306c0080c1c60800b02040d60140d8803016542e03504035440c0c951706820482d4000d41418080c070a0140400b51418030030700100811510b05107a2500c0f602103003000c6017181e0008058a00407404d284e8817030010f9030b07042d04480a81e9002c84050090b6212410180001794014400401c10000083c000c25402d42260010742c034048240d8441800f559060f50817426110355503140701070074801d202c241c0d40b09910380d08180a0302c4c1042c8001802c0c00103540390f9072015056141e510b00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 553065053 1250 553063803 553063811
    0x20a0b0c04120f080c0a030f1e021002090d02040f060e010b0a0f0305180703030f0210062402150c040f06051204030305180a060e010608030f0906180d060b0f010905031b06071401 78
    0x688c01d5080348060030380094030004506401c00403030300a1f440e0101031a21200e03a90b40040c0c1840217503550b880014805030064410082d400e003c490101c0200180c1c041d0100b00309002000050007455182110074000b40e6a48000010440150503405000301618039005441080703012200035508000303182c020b40c001c0c0da0f001c000b4010040044c3c204048030208401c0103041400c14006001701c207002c6a007a144019080203d0703e10104200e0410410801700c190096509042c010200d440c1c002400580b8100031210b034070b00303988100580c0d55118480507400c1c5268030000080100740a5031040c0c0c0d1080d280207082080905004086041c100480811035460b542c5005014005101340300d030303802030303d1101c3c0118035100ea91545a01103011b4041014407400c40010510b44100c44500c944510080103000d50423942401d01e001c401418100d507455014640c0080c4864181d882016450101d90000d03000d03008040c4040c1d50508460304020016030003a00030041900050f2212564608202007031000107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 553066303 1250 553065053 553065077
    0x60503011a100f140a030b0306131101050a08040b060a0b0d020304060c0807051b070b07051015050a0b0c0114090a0c050901030b06040b1906020a0b0c04120f080c0a03 73
    0x841141145040ba404106032201801243d54224401c0c03820001c00840d25601d586550100301c0240c0003c2d062141c15000d10400d00121200780c19038402c070030b4481c03918039040c01c0c41e0b4001180c050096000d4840024044008100402c400c0b5080f44d401440260156011984412112000350300c200c080d2940198000100014854940315401101016151103940350a100000030b0203030040801c0b0101803064210b16006010040080e007008024032400340c2e440b401c8500f006515003403082c038070110301c0d07040c1058801c0703030400c004440040d02c100910a00d400c4c0d007092034400c21a0884003c48546668980c95140341c00f64400700944a48039105c01040c00811510f4580800c82d07482c1e1140780240703000001880001c0111050b542c2c00f500c1550006440d21011000034803040302c641d160300c102c002d00000412120381c0414114801400340d05003400d81c0e2540010a2460304c25071183c56130300c0e0000f1a5034000a181240c5441081740504030060078058203008040c1040001301c012404160212008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 553067553 1250 553066303 553066309
    0xe06071106090c220e07170c0d150c0225060f08061f051b06011e1503090c0906092903060f0604140a060501020f0307081606060503011a 60
    0x5103600c8840c0c0c40183c000004410003154800b0b80c0d00d10f1105030140703140c0060800e02e00942c480c0c0c003552054021107490640da80380010a0042061003032690780650500702090341080100e01c10980d0740f156006010700e8560b1a981c004140201410045005103070304000008104508440c4503450118a142810701e805006450800b405c8500010b02c50020104561030f91800c01c54900302c8442001a4481c401d0090115030a21800c0a4071420134404a5a02c8501d540010fa01d03040c0ca12091450250003100710000640c0740242c031071403900c184100816a081d911070f0b002012880c2c420022601c60503164403c9000fa16215040003101c3c503a1000d01440059580c40750000e081807941d440744c501510000405c0e101c0c60014500502c96030120b0105d03ca580740d60380105c24003030311030300490076900380031540704050440c51280342e0040c400d02a9281e1180004002c0396801a408104030b4a040c1416200002191070b0640c1034914658658000a51b62403e0041001840e1302200d6150485500020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 553068803 1250 553067553 553067563
    0x307180b0d0c1b1209050d030201050a0e120403060b0a1502010507020106060c0b040210050c0a0b1611190f0b0a020904060f0807090e0309030f0303100e070816030e060711 75
    0x2242c01000843c0d000ba000c4805107a040748041d40d00056403003c042c507000c40035144803011b68069a0864412150f0b4818160706621450140b5008001400010390031488555590234800c4408a2501c08000400000368123900c021046440035002c613611a0703860300d05602000e0074010b40000760351948100203000781d0a10a0201030600c906103990f4503001526801028180244001e00401081035045a41c1c7d009a06481100ca120b0045850401e80c500e0a0310300904180c0d0070001e941d0f42840071315a1030b8006c805030000360b0981c40003000c031401079400d07110348200303032020944026071904d1000010901c0300342424030681c0e00f90005070b9140c520301d09010444240e54441a40c0001d000000d114080c00440c441f02191031a000c0401d0800c00441c0c000e0030342c40361015060f13141c4246055030b04005c1c4044003a42c425450312802203107259640080308100342c0111068030020391202c00140d4a5021410401075003545890000390fa03140b8043d45515003a02501c1e000f0119442c860a001c1e00001082 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 553070053 1250 553068803 553068821
    0x50603090d122a020109021203040311120a1b030f240e0709020a090504020a111b033307080a0b0109031707080c010204090b0a09050f0a020307180b0d 66
    0x1c20883d50b19260720458040c503034001050303a149441d40f0500040ca1003504000c8800d0740040042c80f2080300c40070b03560740e42c0c2c0c418030044818000169141d0304c40d1808569880f200c070190801380200c42c500d961841072a15164402100980c2050004408a51081d0031284442d10601c0e16040c1c010302d402c039a40e0151a00407074059481d0400c9802c00d000d48000c2059002c8810059001d41c803008541010f580c0c440864002070703002480824039452640e4000c03590441034140c2404d4500d10140200000700c514007183c90903400d54840ca40c20345880c8444d0285061450000b41600140281800320790307104903041d00c8400002c2c20000c03d105003042c240c40b034903021103424204050101e141d40d0b1240040c0d1111001640c0818002c900e6906000020040b0703288012000021591641c403408080c00a03d01d1042da2801003e03810b1010a042605100d01405040d160040300c05a41d03400c0040300c0a0341c03006000508101c403609c6146912520003491902030800010038940303e004064001085900b509 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 553071303 1250 553070053 553070087
    0x61204080915030a1418150622091109010803030402060f1c0509120717030c04170604060f0c0c14160803030613140c070302010b1804051605060901030e07050603090d 73
    0x20000f0344419000504112500c1c0c1d0541c403810300d03a11304000a802c183d40b0241c078003081c5000d01545489427815480903c03140d218100054508441e4014499070520034000e052056004001142c0545009030140c106581d10ba00500e2500d00f64103070b40305105440d01020a21030781c0310005d02c01c41c4030041c803201110301d2400b0302c0181007410035295000c1130b094008004000c0c400c00804951411030076001c03503004e021403921007240030301c130007070400d654500c06c89095985900d0808c03540c010342d40b140994900c081c1c56a4075049100c0390b584030f02e0541054010200d20511a841d600740102c40205006801412414007860300c0380b6204c000c1c45411008001d0180310301e0301c0d04d09c2080080046940ea103801c0032841c09440c3d01c8008625007030703006046100c2d0f52036118007120740071004018098500da104900c2141640d41c002c002c0114000001d115014503541300c0d200380001d0801e54800c0c1d1003545c0e103018807011110b002d5614008905a58030584501e200d40c0c000c1c201c4071592540003058520013000003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 553072553 1250 553071303 553071331
    0x71e020306330f0a08100f02130608060f040606200c03070605130308040f080d020106030308071206090c110714090402010f0201150602030c0c061204080915030a14 72
    0x21410140d600a6144030441e0754600d0a0510440d5150043c243d50a920041c00307401040780c80d52000341d582d09003c0e00c82031805003894450800100300b402642c0010301e1084c0c00c410168100307c41501c05000c014007442d00304041c01d9401c0030360303134440c040c0b4402001c45466114248880e000c415035020005000325000e80e1000054900e15200010343c0001c031105454819194418410460707142441c42e0b001070881030380800c1c086030041d031f5600030700c0458810004555030848010070030ba0981d2503d22000d8041850040011401802403407449043e000c101c7d03000a00940f40d04001c8216912003107054000303456200c20029610080201001500e00c41058009d441032000c0060103144008000904221081c904100c2550003500014564000b5048120034281c9458000390349400001c2e6014003842560800c20301418504200c4030740c0c080345526020203541c0d0342c503801c03165408009140d420041c0d02c0d4001e03503298902000303140141040a0f0114030342d00c038450010004a00580389041049107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 553073803 1250 553072553 553072591
    0x20a061e050702060405210d0201050709051906050a171306060b030906070e0135010b0a0504150c02030d050306090a180605040632100315090503071e020306 69
    0x1802044e9401c5031400c51f00e400404400d003110444000c445404d0106a21a540800c48100d0301174100b14400c983c5940c8043d20790765140c081196450700080451b42c021464101889214411030042540042e01d05014101810103100c1d400c041100700e4644000038049540003040040d9405540010100044c01900b1070400000150700c1781400380440f800d20102200c0b0700171590013032105205903030b5001c01c0d0b03004482c40e41c40400c42c416600302d04641100100340010030b040a0744c0080e21404900c07130340c3c4c00b41440d00b00742e201ea424080000f00e4606104d1881b10801c0181d40402103000b0040320740d0742c0c01d0784a0410380c040c0501c42101400d080c1301b450408205484860000c140c2c40c40280e0032000205050301c440c00c1c500010308a00280800c02c0817201201128052141101d20140c00741030030700556a0340c0c0740084600c41c0340c10b0000400710f0404c002992000300c40d58018089190045098070f140c0100e070381d01d128030902010000b00340301b00640202410f42c6001d100580d80080205200035181308 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 553075053 1250 553073803 553073809
    0x309090518070e040c180507020d1e0e030a050330060d0206030a0b04062d080d0507061103150414060f041a09090105160905010206010b090d020a061e050702 69
    0x10b12400b428485510081c0010300b4001030441080040103507202c810480d03001041c526020303280840d034a402603c202d07840380f03003448c1c0304034000602d12140c100006524000e0311021100441c9200c44507605100351003011020034024001440a000d0200c03407801d4a085100c0112480c2c1c10075071001081140d0701e800c215180c2c4139a80f0030102c165044400e541d881e0341b16180000101103805090350400e2401e103000c240b18004129034058a120601011201d000305040b40d00440c2c401e0250511981101500d10340c09030045029104451080c140458820039500e6654601d40040301c0c4a078460402000b064418200b610031045481041c1c40c0322982803034501c002c980c55801824030103001d00c1e51038031201c29040300110884607501c0001e020940e43d061868040d03000c0c280c02d82d801200043d0150048401074005c1c0d18081c129001038020307140700c2e032070305540f0031090700b01507041c507000f8114410305001a541da501d40805450140c031406008d140c3c45c07101040304050008008140030081101c0d402690b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 553076303 1250 553075053 553075063
    0x1807021504080c06100f0911040303081306091109241c0b0a0504172506090f0303052505040902030603070b070809091b0702040b030313030309090518 66
    0x100d0340344198a203501d0300d01d040d001521403a003ca20541c080d081c240800c1c113a01070540c0080300c00741004c1102c002c0d140c081c06002c660010310b42405a0008000c00c0001074010340c142a400440841d0082c60b040c000d0301c9010076504090800c407415402c581c14800180340030b5141517000610b8040200000c0b9440c0d0000303200d000c591181d20b1280c0188030007124000c4400092800a80e0b01600003203a50070302020900190030140ca08503003084000401c00312107030140c0d0540d140c010440590241207480020f81ca11485371141082d10002c1c4c90b1400140030071060070b14522114803a40e800501c0346000011002c1c03248440d0040c1082420000c2c0070b600c82daa10101b581c080d104c50b80d20040e6070361140ca000925046669003c01c2e0402e50208d86c40301800050710252000e40000c1e54068180e96a04d245d400c811f5002204480060b0403d01800015081c540c0c400b042c0c071107000c0d08481c07804150710282c9001c1d00e010b03401100000c0ba82d8006211820982c0075080c1c00c040801c003850600811034200988038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 553077553 1250 553076303 553076323
    0x91b0306062106080f100b060a08011a0f03150f01020f030d0e100c02070602010506090601080103080703111c02010e0a020604061803020d030f031a03070504020d110a0905180702 78
    0x90300202ca0890300100b0b5100800510900d001c5982180c01d120320340392507211100703500c5080b62a10075610300030b0074180103d404070b05050341c400150b40c0c2080c080c00f0500d02710700d0394405204800d002c00010201c000000750b00650704000f16803185050b40c8108000c08800311203040c1150096217480025000010666002c988420300108031040c2d15460107242c0403209011826250134082110423298000c0341030f170141c03070300d43e802445070303503a1712050040d003200913a0240c0c0010303c400010404030712520007410b0050b1007880c5c200d007500360103d030581c034041c81110b0000b01c0b804004408208250240300ba44c2d40d020201c0040c01c064681c0303400142c034900862041d40d0a2003205001c00d145c072401d8580398006160300801107009a0b540e4100185109024010071001c00d180c4550348103c182c0c558080e69400c403008001b000c4650805003404089d41082214a840715150401100c0950740d08000d806007000740c1e503420010a2410040100d10404602d01c0301e24090900d00340015686e01140507506 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 553078803 1250 553077553 553077587
    0x915060e01121a10050306010603050f07050c0c041104050310060806041b08030301090203041203020313060b0a120f0303111201120320060907060906020c0d0615091b030606 76
    0x42d0b81141880c1e40310030361901201d618040400104000c1010480d6120140c0c2d405500322807060307032030b03040550480f80161420307a40c201000000031906c6128800809100310414155882200f201c000308066031507240d19200c510a010a091240742810400411180b0407002c007401560300e022152511150064406000580342084248035009083e071038070018445101101d43d00d69560820300000d400039035080318500030506142c0c0f65a44240256800389462168006075908603a680b80c009180c803258654020011720000100070f0301804071300c1c4500d4054030101c11461034905e401421a90700343c045401d000d01c1405034443e40810380103400d0550b900c0303182d102600502800c00340c602d0b0369450f404500100703403801044101500440c1c0507000701764007000c03160761a403252030030340b0045543c0c051600160705c0603412510601c3c1011070300d01c01134000c04000170000703c01c04910444002a820100071603440c0c0780c111240c61a034501004c42c0b0740882c54100a503d003888001030400e07105040c5100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 553080053 1250 553078803 553078829
    0x111031312020a0810050906060111100c030b0409060228140c030d0c0c030e10021506120a03260c09042003090c090108120a11010e030d0915060e01 65
    0x104640f5000e42e004003034000c06040300d00703030340d00b013250760300540710807141030310310740030746d501090305540510462140480b90701c025103400070060b000c3c1c0d402020303221a6a410940c031062520041d480320b1180381c0b200b03401520f002d41d6400310120008184920b80e0400700d044070b0750258400780d40d6440500c0c0c0e04070080242a840c2c1d07440c401240a85503014414000314581e00c0c0c4100c00003016081a107030b0118600c03c2d01da0f41d481c40d40400410100321a008448800740e00031740140c1010702e0b18084041d82c0044005d0000c050401c1a0058610384846070b2001c80c003090b20420f2500c1a00c50b400c0303260b0b02481c504040616217282c0404072007824042d00b4240c1d0302550702c2d00c1d10541248541b0303a825070103000250100e81c42e07203407801104e5521904c0311389040c000d003680000441c0c82200816004d880080c0c030890f16141c04c20303182c8110b9003501c91244651071950703100038010341c00005000901c100145280c0214103402503003401280450112001001c40b40741c200700b00001441440003e0442c0c0e6207015200c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 553081303 1250 553080053 553080089
    0x30c09010c050a051501030b0f0108033108011409010e1005090307240e03070c03030c050a140d0306080f070b090402040b070c032312030402040204150c0201110313 72
    0x1840c205001500401344d000e800d40c10030002d000d240c001d9040b01d00030301140400340c503807082940900e1000c0c020141c2c960410010501d500114000d11040030781c216441e1642da482c1c0c0c0000c1400c6c40d02c50b400240445e510703400d0032860400000242a0801095030007003061852071003a0740d030380c3d000d81452081c07501c1d101c40000d0000e400a00a80e03042507004000140e4021000c2e51268205003864440765074185080003000480c2e1000090390b400c0c56101914641c82c50850b2000e07105c1c1e2075100c0c0c04440501c10702ea10039001800800300c5c505500e02c100c00402d00503402640142c10f85009801c0030059500058030f8840c50b000c0091000d040b29522420b1f150b80e50424004540a03210f0740c3c21101c0b902c000000d080c8100909942c458007124081c3c3e0a032004c0e500c003010a4888603841700c048070403d134000d15050031030228040086401c10b00c010001032070566112440d0882c000c2d2248684c01007100511210195600a80e5000081a0304170103146403c150900a455500d01d5001e030b084009110b101039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 553082553 1250 553081303 553081313
    0x60806240c070302030d0201111803070b3402010c031116240306050901060809010b1f0206010602060907140d060e061801020909010e1003060e0d0212030c09010c 71
    0x2408880802032040d5580d0944403080340d480500f4803080780a881240c50010300d03288188100982400d014252514000c0c62203c12444240440001585400b45440004204004078001c01d0b1200c6c0c2d45c418804504a06001407021a4484845c1d11904d07461002e02c0300141c0e80450f00d01e80b4150b00d0305010744c071803403800703119440e002181d40780c2e81c02c3ca07280c641d02064070200b070341c0c210010644009401135030b8031400c4c200f203041e0340046c070130290011100360043c069a4010415654003c002200024080c0721880014146103039128032545400c60032407043c4200c0e64140040c0b40500180c1c001401c003810807640c0150745542c148610f4400307101c01e04155400e55581840040a603402c8242800542090041143c0345c44040d113009040c11185400f030803601c0810300036030f00c400200501540c0307182c0c60040603200380c100c01001c00c20409014480400010141e124040c24580f04000070841c1c0c01c40d444010307240c038003009458044200d0a00810010907000741c00c0301c04c1101c0038030701408070034410320380 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 553083803 1250 553082553 553082599
    0x50d020d0e040f140a0906060f060c0b04060f05010b07030e010c030912050a0204050c1201080d050405010309031107090b100c11012607121103040203100b0d0605011716060806 77
    0xd01c1051340c00d802408a251066000301a40034050f00042001a640d212046181e030194403c07000420100740f113020105403403010b060381c894060704001c6080d040c804040b4040382c00036080a420940007003618800d156200043c10342c001420300f4000b20260031500c2c080c04032980340c401c01c600c48006803401c00c100308052089400c102e42c098030a200398140095480b4080d008112040c0515101600000d484040000d01d0510380c0400d44a0301d180c00c2c1420700440241000050a90900c000308942d8030402c08100040401042e990b5000140d1800f01e10800a180300e0510705c240070045840e44030804505050702c81000c082c801d080c4010750719440303c8d01200034020b40340419209004181041070f41a0003440c140c03021264050100052130207800051524002910042c0d050383c0b005010702a03070740c41d43d80030507665440140b88404200440d6142d405481c0c09801004640c41042c407030050402003042441d400158047c07800b0382c8141010001001d6050082180e84680d0448004442c400402c002c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 553085053 1250 553083803 553083821
    0x80a110705120406020d080106080420131407050f0409020901270e130305192003070b06030303040b07030203040606030609050d080c190302070204111303050d020d0e040f 75
    0x203544800080b5000c15a1a422510512016015240640c2d003058420b0310308505890b455203901e20795442d6621040140c0100c202c0c0201c01c05140314024101d6a15442061040c8140382c4001c07a014405520b0f042c0854400f038040c0051101c180300c07042102c1a61002e50b0252001c00c600140c072081e0500040318200319004407511072310a00c401d88a08403108840700b8059074241c0d082f41900791110b0f206110301c1f2008210244c0041d005000900c508601417000c0860907416203410001450700440010b514180b80300481c902d980300140b00420400c00700407195001804802443c1585410b854014500070003c000c0700426600000041c1007101592090014540000d8100009403052424590f1000c64050b84004601c5c00c10002d0240300103c07007250181c610b0851340c3d441c51080c0b81e0095010703410400c402c90b44143c0741c020b5002c0c40e89941c3c0141140e5003607002807501c5a895414090704100350a0030000841d044085014010b40d005408004406d605580001c0d4880e0102038460040c00256 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 553086303 1250 553085053 553085063
    0x90f090408120106020c011e0c1209051f020d140c0105070c061d070618082e06060c140a0f060203070f08060a0302060a09170d0e09040201080a1107 65
    0xc0c00180400c440142000080300b984540385a43c032040c0690755862624101070000b00911400460000c403c0454a810701403401c05c50300000d42503613841c441405200741c6800003078440b0020405894812200c119605076030440f210b07481030300ca60080d1140014024041800100e4804071040b00d076000c100c540f883c404000030020350404080c01405807661080c01c0e41d0003801d0412406154041010404076020854000c00d0f1044c0303089e1003039481c9512184950100010300710300140c0315500b48848020501c0c2d6040b0090b9880d1044071b0350344498200407801c00c0d100d00c1d22034207000c1d4940040066000c1c2c0d8020b8400400c207d9608126442c0184d43d000041400000152510400502c3c3c0c010394002c500741c0c1c81d49000000c010804a4044e041128000c0c0c0c0056589401c1000d0b092840060010500d03d00d4103920264498800d0754140c204841042c0495118109540043d5840034091041200840b451942414aa00020304030a0041c0c002d072400d613501da400d0710420104c9401c91705965880 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 553087553 1250 553086303 553086319
    0xe1318080d0506011409130e0c09040c030b090f073f06060b0c0604080f22030302061012031409030706090e0f01030515040f0c03080a03240b090f 64
    0x3481c1d20300e01030841555214042501c0800c500d00d056121019a8502000a807079603240240706070441018100c0300c07505000d180500c600c00c1940c1d441d6043e40c14400d9004020220300c0b1465072520440c0c001d00140741c0c00158000c160b04011503c0041160021036415001c80303644000301d1000c10b64141d00d49181c035080e0090a07891045440c1115405601c200d004220070820301d60b03140340d060a1445003103070040c101c0d0403940024000504e140c3c0034080f41102000e01070309060390300003034079000b07008180250710160032082d0400c03c050b410407003580d00410519061b010145016135031419110000f40007400d001804000a0b003144407501910b00458005003290041035840b40301800c82c914601640c46d400b100d1000140c1c2880640101604880e40b0200130485c03861007400c21701000101800481b90801c00400d001d0200d40380c5400000518000d503140c80d03445006207006421035070200c01d0022100380c07860124041e10100c412181c12034801403006c603503900801c4c00040041c159089159840220 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 553088803 1250 553087553 553087567
    0x91202060d0504060b010e030c060a0c0f0203060f01090e01090b15130f0b041409030717090402030a050f0f0f0a0903020102090306151002030f0306040b1309060c0f0e131808 76
    0x1145c0c120240d0354801f0303203419062582e0b000526440c4c000b42c1c001640c000c60700300184600c4a204540298a80e0702035115100420410760001e4246238058074a441d4031400ea200501c08440c01d44119183c9481002c005c12400b20103070b80c0c06003007480080669041d41561200c141098407440100603840403001800c1049003200c2010100902c284a0a0b50245c6d29000c0c0302c17880702400b03d83e09802a41141c00950901c0aa6a0b80b0f002084001c0241ca0682d80c06019082441d02c5a0014500651031400b002c0b6031490606a0607104501c01003003510f050641500388050450301c0e0090036003100b45d014010852a005050a90283c440e85000784d805100d420100310300d031544d030510380d0310b2040c0031100c0908107580240b00302d03581c0c0038400210301060010004140285080d900c42c02d0f92620140103c15440b03e6180c1c0582210001042514070640700c1d0740746100c5507402004c4035402d1000d402d08200c0b2201100c089178046403517074641e07402142d9450f04083c80f00c0118900c44510b40d880480d599569007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 553090053 1250 553088803 553088813
    0x50403030515060c03160c1809141b10021509070602071a190e09070e030d0c08030a020d06080d020f0d0306030503071b0b0708030906010510091202060d0504 69
    0x1d088588039070380d82c050601d02a103498030400700c03070700001c00800550400069005400100101ca5011201480c2440307000036018240c00c19044414125040050f080c1010708040070242c80c0c908416400341c00001c20721000c0d8000d08000480c0c080d003601c1502d42c00402c144140d19010aa041d5140008043c00801580c1c0500181440c03d81d040ca600341e40c04956074038004014288194a040c52409040c0030843c0c015008101c8102100341e41d2412501904490002c1a1142000d9900c000000c00c814061841c6040230400040ba908403481c08241c20760443c1c03940c1d0103900002d852440c2c5c503500020304c100321000b075070041030183ca0301ca020b5446220802001a42d900d0a000000100e401410380c0400c44900034414082126001409149002c415948600e20714880003901560700301103240200d451180d1071b020308800340c0308084d002c0e503c1c20800b5003d407500c00164040c0d8411109800410036090b80b02700789800312911504008a012294800200103018081e200c2c1e02c400d15085c00c02040c44 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 553091303 1250 553090053 553090061
    0x607270b07021f020a0b090a0b09101a0109090510051c0c140d02010f1112070309290c0c04090309031e0c0b0d0e070603140a050405100203150405040303 67
    0x50b108441000140306801c107400326110b03070451401d0143c1c11038111311012825030018a9805084202666480210380d5100c0449603c140c0d080c02203540400c45c4000403040c140324004011080401030000e2103006d100092201c05180610505613440784041500310840b0740031800605401007501146a00d5680003505040d0035603001e45283e204400d0018810000e10a005036210002d444801525807030303001940d0020a840c100c0d8100810200180c140b048203001149414074030000e116500c00e00e50800410304069504814440c01141e42403803c04400001c6154103d0001482c0700d4881c07a11001c16800c3c4000c01c200180c005081404601c10907a0100f41c48080d00e21801003000013106850381d0031204041240001d068004c2c030f500900808020070702802103c1070b140303400300f1200d040d4071005041100640c005000b20380c440908544807a134440e01036074001c5280300c040080d46099120380e55208002c6101e95440c43d40080415008907445100d820000380151080c0103d05003803400034018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 553092553 1250 553091303 553091317
    0x90f1202130b01080402041a100f031a03030a0311070c1410020c030a1b05060c1c051e070812090f0118020603010e1302090705041806080607270b 64
    0x1500c41c00d115403901100d680326a407100201039441d400d540c0c0d500d6080c4401815100003501c802e0b241c0c803000c0030580d0740300c0302c2c0585d01200c156100302c054183c401c40034080c0c40351003c085054a0500c80810b005807000015594600071b9454003040961180003081c01c1403040e5000039196401001011071041580843c00708102c5050b9614042c0900d19041240c584203081800d55040e00031070032103400310306601c80310110401e503102c10034840c0d940d60002590307c2c1d20012100c01e464000c2d0050160302e0803040800100e030300781420220704e03003000303851071015000301c20104048903480070400c0021701c20500165444082c40840d4100503040075124a40da680a03034191724569800c1506484180704040d062151455001e440c0504503402c1c90241c0350340480c01880081d178030220201d480c001d640c0e04580e440c050f44d91a25043d030f0380d90030018540981c0211040404505040400400c40d4000c00100a980480c003450715034620a52171741008020482003296000c010314000e80440c6000d8503400401078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 553093803 1250 553092553 553092559
    0x3051002030709060f020c01030e0309122a01021002070c0504020304210302091818190b01080c090a0f090c08100f0605030d1b0602040306050702190b01060f090f1202 73
    0xb0313a69160111541d140142c0500e0060704140030458895000b0f40009031400c00003010703681401d21290200390b03d0114071402c2d030500c3d0300004000c03c519151040c01c2d0082440056400d404092910001c1c1d80c803403004d0b02c50303640700764000f404005000c010700c008406030100a1040d1740c2e07801c00d0700700525900903541702040340c074104290140002d4004d20071107580880c06040e2009411210841c1051203000400307080103102c00944000b82c1d00400d10146164010320302002101141d41c1c00d022500200580060f10190b101858912a66030f131080002e503c0102840b0200e4605410701070340380500001e480081032000040c0d40819102c0000c501c0b941a4105191700b00251b05c2d2034281c800c203491440c07040d103030181c005000c444013203882001ca0500c40348541c244007240c0c4285035500c0c012a4450750094400541e81c8081c00b249030b6044c0140c01502c15941d4a00302d41000340d40700c08a802c40c0601c03421003400300c8002400190790041d04241e005203107506101d12859078440ca2103a103000100c100f284 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 553095053 1250 553093803 553093817
    0x307180209030118020415050a06050f1218101e0902040e0d080a0b0312070303240e040c050102010e0706081b0408150c2107210c121a0d0804030510020307 68
    0x1f075151103000d2403030201c43d0010f104e44d0004e4a40360342691240e1246104540d6001c0c10040313800d07000000004140116003460705070017400910781d1964146030840325580c0e4098101035104030381b040b83c14080740140f00c100c1c400260032044e920004004109200c8203217000d014175091a4402c40d00034031464400c00d10a502031148040007020141c4481c0b0a48802c0c2e8000e40c0bc2c0712500100e440303540b140038004810030482010345500000701109201b41d52200707440b08a02c404200400000d2014a0b00071304080c0020710203500030004880c2c40350700c00c1c081c07078040003145400244400c0748860450010b1004d141f80540d200e445403a1300740c0341c0407a0041ca2600740241d00109448541020440e900025502406103040c07900c080420341c8984054001c80070056182c2100c40070b6424103d51050040940f41c00150740818079401a1041450150ba40d901c1c41c54100d600c1c1c1400d01c3e942c554820604225204105403a107071500e510a4043c80c0c20181c524071816100001202e503560003140034015980b2041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 553096303 1250 553095053 553095071
    0x1030c0c03090b071406090a020319020d0b0606091309060615020303010e07181403010b06041202061e071a160e0103090212011104030c0b070203071802090301180204 73
    0xc0c86500440303000500185811004102c1c062002c030140a030382c2c0c811424070b200c00c284241c4851901e10b055682143c6500207040c20701c00c5180030000c503000103050005161003002c0325000204007802010300640041581d2000a9003030366400700f00ca041c6e01e0010582d01d80c001d0002080001000300100480d42240307003510208031446480000b0103500070f168011459070303080420342d540d02c00e03004c1c0188090041448102041411015003117019042410214041072590403c05007540d8064440d9800b0f41d000b00801c3c03120f25031309090301c41c0303464054070481e40d42c2c10200d12010f00034800f00d13400680c1e034030301080c03100402c0340c2150088030788412080628180d884440c100ea2005442459070004140514000c02d0f140d400794002d4003095000426010004444030740b140d003076901c003c810110045002400744101303c60040b0041c007800300b049065052640743c2c2c3c0801d070b0704c051a015860750541100740000d6007003400c0c0c0484070a030701d000c0c001380301d05090180240005008144100d05c101d00b0041c0103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 553097553 1250 553096303 553096307
    0x70507090614121f05090d0c05030f0a180305070303020607050306030741011209020a05042706050105090a14010308032d0405070e0c03011e090e060601030c 69
    0x201d003610918100e100e40340c0c00700c03010406a0f0b621515400040d004074441e807110b2088640164914403102407002c5030a241c80a00c59090181e00c0c02c44100b444169511368000c186d0000549200503440c0c0d0b02c0c640d854490604c1601d01c40b0b6100700c10100f0340403c400210412402082c00000c40788a0707002c80d40181c0300c46005841da808200c2d5000d40540c841501080304800700f40c00d07080b80e0003014551440030401e41a40c0481c1b468200700500188980c0c4843c1d1000f547d2103004181d000d41c8500c2c0c00c2101e8501a1b0000700d0352450741c03050520643d2607402d14a0b41b07081c800030098240c0c08003aa0139a0000c618a41000030303180034800c0f41c0c41003950b40e000030f030400d4031030080d80b81c400040c907032424090f821513580350503903000034000d144207010614402940d0b02200c1162014000042c0110031245402c0c80d003070345010b04541029050740c2c100da0900a010309100c00383d03410344d8260711705030003240790802601e01420410740c0240005030500f150406a03403800724106015040c20703a0140140600030b001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 553098803 1250 553097553 553097561
    0x1801060e0f060405060a030803070206070801080a0512030a02090a08010c0e0411122517090a0c090b030a020a2309060d14070f030311070e01150302070201031b0507050709 75
    0xd042141c004540041c4030343c50141d001c1d070f6100e94000c10004c0e082d41c4a4881d800380d9041102c01b503000d42d002505116006802042e61030041665000404040018ae0b0f00c2c175854070b24660f540300c0e0780384d40400426030051a64054074003451003d440c551005a650307942c0c3c0c2c060700240148002144007982000c00c0ca040074094031281c0038488004901d8000d07000307a07120322090020446c0c0817038000c00000c054088004401c68440c0076065440c4c02d00845a002c485030115800350220b04140c2c0103060310790014200b9021030301241c44060340000e01c1565603000c0307400e24074000c1009600ca62820408a80ba005600c1912042680e0b01c0f985d0441c5401c00c0244400d0001c2610402d81c807a942c0e11002d0000b0300c82d000ca45034800c10600c29203134016540c10802014100c207400441c0440d180902d107078013005080040800030002d900c00c1310f200b03501d0b0408112080080101e540308064001030f5043c2564002d0f00102c41000460702d0b02c203060307441074a00908035003060f4030480d024000c0040001e007405a5000b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 553100053 1250 553098803 553098811
    0x4031a04030c110409020406090c110c090105010c0309080703230106050108160905030a08030103120804020a05060c03072f010e030c0103051801090503070212011806021b03031801060e 81
    0x94002c1e844000307403030780060400c58006440c1d2183c1c44061103401038860707020350b00040003001000314240c04000800740c215142190359211a500c514800f250503600d07220000e04640f008c0c04c1c8000c1100c818101110022110b4100d0542c52040640c0001042940d170204c80d2905c00011201d020350446400d01c500341c0c1e400d441050700040450000c6580c914050303240c400410301c2414050030082da18030100381040c000d01410f0f5036a4001000400a1045000000e44000c10386e103807040492600fa4002032a15909010700c5000340d41c08501168110340800482e1082d5800905500c0000040c5800c10702942440814118401100c0e205800300c1d4090100010840300c010090040c1c4080301c401100184001041c014420300c00d100040d00c105020300c10310f004a4050406196500490300501240308058400d0400f141c3c50200c040100c500410168803d039a403044015a85080300e1414503400c580c08010205580800814800d0356814103a0341075102d201d090082c004541c0d140303e00c440401d800c90b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 553101303 1250 553100053 553100057
    0x60e0102070b0f07290615160f02120607090f03030210150302150d0b0609030607110709140603070f050a060f140403060218150d0911100504031a0403 66
    0x2060030300c020300c00e19000e0001a402d00204074102022030f1640a0010751000d0314a085e1540c1e04d54004802d07078600c03901c1d98803407010b03100b0100303501a044440d600d034401c3c0800c4504030324140c0000e03010881e0442c201e60312181c008041c0b11103102c040c020340341c40e40740686071840407075404800040d00801140110003160b4242e0080d0000c02003480d4010301501000304140900b003500741020006070b85003441c80c025001c0703000e04c06488003031040f5070b80101c5900d80d80031032082c8000d1140500d40d03940059000d902c4405460a40360a02d030a180c0540340c1120358201124881c180011840d0900042a00620915080303046415072aa00c84013980588a40d002c0c0341d80000d00c2c408140440c60281c1084103000e174242c0340041a841d04004942c04a4006800072203d0300e80019003000c2c1048102244400f0241c126004c20b011201d4803045a05c510601d50116040303901e9069460902500d840702c1c24551801921300360418145010052aa6019001c100d6408851400710415080b004d81c80078071a80d85a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 553102553 1250 553101303 553101313
    0x1e0d0b090601020c1905150a1103040b04050d02041b1101051f0501080c22090e0721020301020c030a0f020f060610050d180606050301060b090d141509030a09060e0102 73
    0x300c0144940352240004400f9504010100001ca80e100c01c0041d03d4000318410003140c448e1005040204898400c1418041c1903105000a0080c02c012400b120102c8200319500141a100d604c0410090003080705075080044c48010715035405a001400006501240303002001590f655500904000601c88840401082800c500740505d5014002140c1c0200785201581d00b090b4000c2c9200d20b002411400711981103400000402000c03025004520405610001500c2424280501c046c01c0c40340b240016908011054000400c0d91400c0d0304a44054640606a9594124454001e054013588000500040c4643c106610703040d00081521801450000d0446d4050502024211859004250507030740741a42d0354281c1d1402c0c01214010105144142800329495113010100340c211038060b4000546c90004108891265450660760000c06030b0004000101c0342c01d0301500d80c50501131107454182d194020003440b6203d8000405003d02e059159118000940c80311811a40a2000d00e9460302591003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 553103803 1250 553102553 553102573
    0xf12110405061329090412031104180b01080108060f042904140601080706091a07080a03060f1421010e030f0304050d081314031e0d0b09060102 63
    0x42500041e4116100070040c1074205031101d0580125160b0b03003441c10383d00c0090310307000707041030015900c0504422040b01c6401d400e20341529910400f40381d2011000c101992405041e802d083e9010590f40035068102080c0c2f000c00c40c2d03040e03190040440303c003040d01040000e0000148040d000847c3c0d4403a040070907504450391950f6456003444103025525401c5170603800040450b0385d8890f89200e1086004003c0752002420f212041c40c203000061700080350035004040244a15600710b6264001c580070200c00348402e450200514904e80501ea100600312040000d64426503581604000c0644d0b01c0050300d080340d559500103400380f9040c407402694010ba55000c1d944559200415540c0c8120f92042c008a07a44015445e01c3c0e08690240104518a072000700c140000d00c1070400241001a2050500c445603060180c550051625219802004d1140c410000114120180240c2d212500e141c00d003039004821205010855030016803407103028514007400f03010285001407295001d076006030084c0c02d14444e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 553105053 1250 553103803 553103809
    0x608070b0a051605030a0f0f090b030c12160e0307030c061b0204020408030c0c030f0309060a05190903030f2109081605060117030a14091314010f1211 66
    0x403102840b805004500a00ca52100c1c0c9124151050018507a10703d0403a0001d019030b11207070584010080032050143c449500145801e058950180310706e030722580c030f05a1f8000c0a04c00c100941c0d07600b01d000c4092110000b80c000001c2d0b078000958850120414480b018540e46403003a1002412958076220301300000380c0aa00c2540c9010104c5c02c19880076400303900814142d80c010340c0108001e40c400242c442415809220082001804501901c86520084a91070b0f684c040d6410f6a031081e80c0000d00819414020800c5900b2458209150090740d080408081c042034024481540400d55150b4120b1602d48141d42111110b503807401684624000e1030b80c000001d282c2600308071070101080003200c2d401d00c040c1c400002200d1260000701010340c100107440941d11180345140000380e20501c03030140300c1b40d0000b0b2420340d0050044600c4c0c0c1c55058400005284080d1084a800d4280c030f00078000328410258201d031410382c2d00203420000d8041da00c0c160460804416580949034100001d6415080c0c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 553106303 1250 553105053 553105057
    0xf020a0801090b06090c0904060b0d110702030304090b010c0b0910050702150103030e0102150f041205030c090108070903020d03111b030703060e240402010824040504050f03040e09100608070b 84
    0x30712800ea047e003010002c81c085005c0748d40c580c100d00020f99021a4009901900c1c1c014040305c0c811010726036042255a03400321385c0e81c0c005ca015140c42c15880d40000142e03a48108050740301c070780d08041d000c000d50520120650b1607040c80a44128483e041c000000c00040c00001d068070805140c0c00e698140e030f8a113440444d05a2a4024454114016075103140102201c9086140c00350000c40c0e00e4444a040900d4800e03c0d440d400c0e0072250a0200070300c200451946408241c800750350082c2000399180d074401400703c400d02d0f903940001358070941ca07007500d605140c0d0001c0e100b18941d008904861410f1501c034400410110340c940780950540c4501002c0c40011415080341100b117141c902120004926401e60b052260840507140303543d5620a400c0006569004141c1d5420000020a4001100c0e90340b055501004801903094000c50f19100801c041180c20030100100101080039241c03180d40752503060304081416034160101c0e01c03500800c64000707042c601c1400100c8130070700000d00401e880c0441020303441d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 553107553 1250 553106303 553106311
    0x2180f010f0809100e010e0c040608030307030f020405061602041406060d0e010b04090305210c0702271305070b04050d0b0a09230d03060806190f090f020a0801090b0609 74
    0x2405600c501c5400c601645c003981ca0f0441e0b000d000481c1c513141d020215440c1010f00e400c0588542c1c00c10030100328481d4007104607900082d072490041141122414040081e200380d0b840b00703402400006d5038141d040d00900c001c0c070006200b150144035524000310340032108031094443e00c1e40410100000f012008081e4040300041c0d40644c004909103c0400000e01101da4010741a40440c90000d6440501303144d030450603140c1c002030710403e841824030800c0c482c5640a0b82c0b5009008044e803038600740c030a80c45025020109602808617100501e020440d40c0c040d0756007201c04483e5445031440c045480401e4000381c2c0c00351a0b01810072110f1a03051707114a90745400182514000940da0a0010f0100f48100e203081c02d00da41c0c050100e01c4811301c140b0500e02d00400c2c0c8096104040c540f10041c4040003001c1211a001203100c00400342c2011034103070140042c80c01011140c00030340b8201004003001664018039245c01d0007142d00c051910390b41d50342c1d5030036105905001801c2204903800100145445803000c0c0d04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 553108803 1250 553107553 553107571
    0xa0b16090914010305160609060509010e0d0c0503010b030a020d0f140a05151f03030e04020f04030506010306230406050c04180b03010f090b010e06040209100302180f010f08 76
    0x1140d40780350355012506811244501820a80010f000307003c8100604c10340c1d08404400100c441d45000c00007000303e00319000c1c550800500086a0074943e100750184808a04000c12010341d03016580740000c10b40360688100350180d42450640d603102e180100b61034415a4028200b42c40b1003141d5528282010b5141c041164000c0426244002d0510100001201c1c0d40c0304400a0800081d101180e40140b00c005001e030720280c1c8503400740b28940e107101c580801200da02d8102000e84460060000e03000c2c1c05040902009030f140410008103100300042c40904a070b004440802c0a040306110541064450519071411401102d01290001386207500465215046519090800380c86481c040b07080c1280500f0b440c40241c80340261201d0b85001e01c101003100e156100c041004001c1980c60308048030301480b0785035080031301d800016038a891700d804980c505031004203048440c1d0042d84001c1d0094100718070340503071405040750141e02c90911002c1c2040410050319070015020455400700d032402002031100792 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 553110053 1250 553108803 553108817
    0x801081204080c2b030c0501050f0c09090702010b06161407061d0301020d1407021c0f231306031503210c080310031104020f031812070b0708090a0b16 66
    0x1308000381c4204c0c120918426900c0240310300d11400c0a80c25248068143c6c8042d80041d4140039002c51a0022200c000005842c443c00355555080c05900400c80c1800e599084200002c0c1e12000200f076540800300c0511842c7d60b040c9441944e11030550720a000c0c010580401d545030455410000c1100e601c00701c0000c018005860700040e9400c117003d54008a0307007048104094806d1004041c3c040c050070312010740c40c1103550070000304401d0040c8542020343c0b400b010f1042c40e503282084071040281e2000b80708000ba0384a5500c0c5880e000303004041e000e1744201800a03280c0486503640300310103100d0794201c80c0c104030b04403d2454180320701c22000901109480600100a540c070000070b042c100910b210b0086d0710058203205285013010740c40f0502943c0080e114920421424000d02c1c1d44a055a41181e040042c0b4200784400e21030207441c3c215108100c01c0b040d01c01090607005c000c0300002d483e204206603039645071151902c8401964401909100030109000329000403c0300b0354554002621000c0c0e0700c1c0c00e40c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 553111303 1250 553110053 553110109
    0x30f08040902070804090506040e1b0409050703030513060201060b0901050c01090b10183b03040905061c2d1505040302060606030f04020607030c060c0801081204080c 73
    0x781260f004a10451390140c010500b00800219841000d45c8448165020b2010007001c50380300e51184205401204d5000010b01098003584843e4000c4540c1c42d0b000040310082516410054010340002021400b2146000c03000309000d80306004035000c41c0c4040000508040100b801542d881d040b001030003030150f503111031800101e03d00900c40c0e401004088490014581004821100d00d843d81c0394110015051080705840c64031405c076550150100b941845441d179103005560900143c050303001c80d41a21021401081030606640000e0082c0d40481d502c0400c40c082d81c11001c01c852115001034660070b141301c01071411040f035100541e404184801403060340401c0350313142000c2c070341710002c150000d40d42c0c0c2040008040d0100700c0c090704803c048840f24114600164050700481c03004100a0048201103800c604040c0136200098565030b203e0b6052002c0c0e41c08070401444a0400d1055a65620890140d52800d03800d01c4201c1d0240c4646401600c1c2580d41c803000d0200b00300b00d8402c026101d440c004102 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 553112553 1250 553111303 553111319
    0x711120a051c0f0608010212060d14030d0b091501050a030c030f0606020a020a0b12010b07051501090c02070b0f0405010e03030d1103041103070b030f0402010903061a1302030709030f0804 82
    0x600b8406000100005418140c4001c0c481151140e410440c002e03032042020041e02e0018041a690251080741e0b240d40c09205880d0100017101c4190a50402d4032011030422035000a6412903203204000343e41d05040d41d03403120052881d035001d0341c22071380c00f1800800000240d281f00b40c1090810701c80c1400c0102d800c004640401f8115940c82d400b00703006801000e5003008615201c40da0000901c514413146d810109850644294101d0602c141807100c000010820b08020f024423082c1540c400a41e01810a980c1d690306000c040d1085241640c010b02440c4008a2100040000d45180b00300c1186120709050505005690705000244480d178940301c1400741c3c46420074140580c2002000040e545512800d00385040860070240e41a03241c842c1c1c00083c0107000004032002039035844030701c80d0281882a01c5500050b20b075118182c0002d0070b45800e040c0268000ea540f0f00c0324121ba1901a06c2c4040d090b00245054070890005803024400140780143c10404184d1510321103030403501582015107069034403452 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 553113803 1250 553112553 553112587
    0x6010306060e090421030e010e03031b030a15030c0810110a03150e0a1e0b010203070f1b0807080d08130b0c0d0c081005030c0d0b0c13031103060711120a05 68
    0x11003000282c68a6031f03424003000c280a00022041018025800c504140301e2280902201c45d9401003001c0010001a41e080c000d41c021801d10342411204020980d100d0802c200011214018841207209030070391081c122105200d040340398803030345160b41d00b8600054011405408141ca040c54218a864400f00e034044095912901402817402d000070700344102c40a526a104604e080012130700d2608080c2103159030048103e4001d1948100d444880500134941105c00e0000c041000d00034581d46800811030042c0080c241094400c01c508507020724406010803110100101c60200007160304210000c0000d076001840303508250244151410003410218040031200c0c0750700c030100002c01d50710a000303d21071070104400c040c0a00364080c000880142c0086005006522002003100d4203600000c0d04903000c1c041039032410555419540f003460b659040150840c0d49609081d40319001d0440030a40050141104901304038241000e09542075103215016903e42000e0410000e00031300f0000c000e0148940c80f4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 553115053 1250 553113803 553113863
    0x60a17070521070305070503010b0d0f06120c0501030f090215030702010207150b0f010c08190e040c030501030605100f0e07031b02030d051006140c070e0106080f06010306060e0904 79
    0xc81c610b0078500a140102620006401c040c14080c0c100010700c06001c0200c04c8510301d041d42071b40400c00f54101320f1880020181e9511034801103601210040800c4070315514981200c000b680d05004005144048004842c3c0c0c040300254030031080390302d0000c0706015601031580205640001420b0203141d44800c0c84c4014541040d80280d96502d086a000d8600082c1360710f5038803006c0ca0407100f00c004a81d0340180314070400c0d2403400c00c15400030407401094840c084002c240c49020380244aa4250090301401401003030104803041401c103c0004d6040394000c2c16581116101c42c49003c65034030302505040c803410041c1c4200109074030355001c8114200c0300034002440d0052940115a1040400e804800300c440241000040e00c0480104100643e80000b80d8141c445119868950300d288421100e0301d881480e0703014100c48403c100000403141c1d08055110301c0703440140d90070155507a031200114116941d80c002c00000c44c00c81d00041c030303250030403030311344e80d80648030b000140e4130701104190020b02545081 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 553116303 1250 553115053 553115107
    0xf0606031014040b12160806070804030c020d080c0f070b0703020c0108070c060510031b05010e01111006120c0b070b04080c01020c0a060b010912020a0e09100e1605060a170705 77
    0x46c01103030701040701e03c8150005280110240005060180d0020701c0500050405030810a0410f104403d642d19500800300c0c0c981d018800035078803e502ca44180d211841440d00000f03d000d005030000340c4805c070004403a20300740d145d405042030b1b8035080d0042d03480e158041c05c100100850004907200040c160f21440e07010310040b02042c1940346c55440c3c1b0b02543c00d6440e16201d61039010040c1042aa40c00141a0280c0013090270486041d08140500394903120590118541044c10030300d001842c5240c0c0c0c082c1407000c070b004540d41c142160321070084900a11030308400800039421a4001004156040090000340340081d0001d807618000c50b009918000d0300c510140c400320341d94040c0c03950968000c1c031400000c00d0925201d07445114981c0000704107011902c101c1001c400700000140220b80f060141c10058000c41c0802c00c64422807040d0b207544ca0346040741e00c03411114400c078080f40c00e00c0d095060324544507007591451542e01070282d0b490300b041009070442043c01801d100c4004004075506000c28022920 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 553117553 1250 553116303 553116313
    0x121b0d050702042706020a030b0402070b04050d050f0906071a040c0f0f060c0807030522260a030c060e0718140103020603070f02150f0f0606031014040b12 68
    0x40d00403c001c032800200200c407254916848215080350012030301d00a1500460016214900780500741c1c05000720282159103e440020300e04100100100d04901650081c01194025269020b09a4041c464051401a0080300b8401041103140040041c64030910486540180d44500b01c2c0b10b1105030800d9500b254200d01d642c1e028402c1c80c40926201b401042c0000c080303803103a440d0200181c0180401400a000c03203070001501350606000c1c0088880c0e10210b00c480b9200c80792440c40c6108011054007a85130701c0b0343c12401201019640c2c4d03421403c100f180c80702a01030840180d13400d403210004410210345007910380d4a00030a0183c103000e100000c01c41500c9a5203818580510a011100300104041844585030010300160300d510703040e2a0701c44e1140c00c001c80003841003181a07260100075035002a08564001c05c022424550000e00c83c0205441424800c294903007030104012804119805e40c145801d0300c0b010005450701401d40b0810394000340001540c581500c001c5890658590460100c90b484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 553118803 1250 553117553 553117567
    0x3120f02010b0105191b17040e090c0f0603091f020a0908010606020a0b0a091203021c0b060f0d0e01050a0b091e060d2108100f0305121b0d05 62
    0x20301454202e4402481d1961030940905080f80c142c0c0c0b11959400e0070400b103244c2213041080c0c0c5030f020701744c61500000c075480d10101c01041d414007030f4414010030400c40c2031080410a80440081c030002418802420a08518064010b100080c0c04c024990507061041c00d03548000d20501541c00307109030b002010301581e00c00303803890044e203008000e9000400c542e1410408211956002c04d4182e0701d10760004030103a064a4081610000d8200640090200d8030401e00d074490b4035403d5401044081510350388000500d6810700d0250445000280d1581c21010070031040c00b0000182d001001c41702c082840000d105208082c055086803021a00035000325580d081481051408501d801e501c00c0d1161001e0070171107101c8810342c00812002d80101e00814070039209c4820043c0741d64a080324002c0e403490270340000f101824020b21121054078040c4000d000600c011503417102c0d00410400b40c9812500a04051840d0000c0c1e0f00154030a0240d607130340c000e50b00100030841200b840444040c050f02ea480f16143c501e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 553120053 1250 553118803 553118807
    0x20103092909150108070608041a0915010b0a2312010e06011e09032004050f040b01080c150309070e040c140618090406021e0d060504151e03120f 64
    0xc0c080111800d0f502d441c000402c8514400102071064404c01d10b440e04003915185027800b0700400e4aa403e0740301c3d16022007040000b090001d19081400c548205648081e40c0c1c0e0603070358106105c3c0e1902e050020b502c1d00d0359000d240d00d0703503022800100c0e6441065481e00031000c00c001c1019100786c02071500303200444184a003a40c0d02c01303500e90394024410b00301c40315010350384000741104070107201c0100b1007807010003040d1300c440d110310b01c0c10031407240a0002e01181c0382644869904a2702154110f814600e003600206e418100011019991030b005040c07407000b120945021002078000418804503481000c030080384507400c5a40180c001c03846076208102c4141054004000043e9144440703000d020107000b03461901101c04078812194400f600c2d54041c58880e0f040c1900607109c3c4111451690242000e1803480c6000380e0018541c080d07443c2400c20005880b0740c2000161100000302e140391506605040c00608880210581c2c09142c01a60100080e540c0d0b80c2c0c40314050f01c80003024040f8481c414862a015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 553121303 1250 553120053 553120063
    0x5280e060c011e0501260a0c08030d0c0509180a020d0e16120308060909100c0507030e04020909040803090f0a0c0e0906010e011404112b0e0a020103092909 68
    0x11035442401e02203503042060f4403003003100806d51a01200c6000d000e600222000b8000c840303000f0780100901280d99103d5200c1540d075801440404e500900d081c4030090f02c0c07417090381546d0b0b01c050010101880c1c2040c580d41401d540c00045c02580605908101102c06089580300c0d01e0803c40c2c2c010003900c4450085604c0c40c440003015400507045102100312040000d6102c0c0c450b503803041c4211241c24ad10b444411503285071401c0c030706d5851000c0345007071629405950400090a003c52099407445a13640114090100361700420070100d800c86202404500010781000142da8008005000c9804080885c403580d4500700e9055025640c20a40c440c0601541251141c55940001400010240340d450900178402d90401445401c444c41b081c0b100d0b01202eaa5560051003150202c07865030b54135527114010988000402e100c0b2032a40f1480d010014441041c40d01880c020444c14170081c0c540585590015000307042100c03000c40c4e1000300301d2038541910301d105400d051031074121500d42d411840c042c130f0780918003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 553122553 1250 553121303 553121351
    0x30c010213180c0e1c0f05030301180e060117030c4603030203060411040f090b011e080705040b0c060114010e03030304060b0d0c03050c030c0105280e060c01 69
    0xa2401e00c0fa20740c0d040754000f5101041c04205403200400c8031500c08101c0c1c04180c038110001c04e04182142c50700140030700000658142e80c44c6030007000700801e910701c0400c121400c050b01c4210680105004111040c4440e40d01101c00c0d4456054920b0f08481031411800c0880300d6102c028900d891b10000d4501001c0c007000c42d050401100440401d01200600b1141503c0111030028100358001000542070745498102c0c0180200042210b51100d0300c0304002d03000c00405000d082c280c0f40c40e018495185611884078059606202c03408504000070422040354408402420181441410440003070a801c0c03140c0200000d43d24a40582520750620350f0005890840e04c0c0d0781c60400101c0781d01c0300d08654000c4101c0b0340141d405200080c2c40c012000228403604001c0c031001d0502031804a00000340540820b0051200e2030480c10b88140c00840c10044d12923008000e41360741c910b032244c43c1c0580c030340c225070103018110300040c21700a000d01d0701c1400158103580b101d070569034a0b944481c4658074040502d0048585 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 553123803 1250 553122553 553122599
    0x506010e0405120a0e0d02031011030603010b04140106080705042411060c18030a05060403020a0b07210b01030915060504050609090c01080a02091806013e030c010213 73
    0xd41404e45800424140b4000c3d00244551545600c00c1c00b11340c0e00f0440612802644842800f001150b02c514581641003120300a01030350821188500318541407190310526070a00c2c00305001039080103001c0703d540d9402410b600c1030100c100000300d05002e114001000700000d200c010742103900030300c0c401000f0068155965500754000818011108000d000f40c4800003c062003100c124000c2c0c3c00000d182050080c07000e0924002d65003403200b030550200740580361602400815803240c985080c1106c003c0100840340e82c2d0042c0c842061010041c0c00e420068070044c0526002c610401544c988640c41c42d40364424502042c0d44d01d50030005400c0500505602510451741e121641c50920b004d540c0319480081c210b81008981c5001882c0804250306403040154041c21000c14950324000f0021080c00566080380403c944a6030034941d00c10810080340075449024100d035540103941d203460584100320a5003095804188040d0382d220300248068094007102c2d6416980051500c1c0007610050049501900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 553125053 1250 553123803 553123807
    0xc05211c0b0604050409020301150e1e04020d080c0a240c020106051311040b0415122a23181503041209030b1006122009030a0506010e040512 62
    0x1071a95511029981140c00503038000c1160031032031000a0040070003540324503031003005490120301065654101172181c1072103920345110107180209504800700c215002035004581c0070210000802c5100a40b109100500450380e411900340c3e1a00700c0d0540c0c55000720340780c511307120203040742030b00600451009240c0c500007004040c0c1045c2c0070900e8110300e1400040d481d5100e0400095402800341202c0003415841c6415407102d45941006075800d0802c440700000408001f2035416038140791140c80c11030400140d000b501a15100c60109001403450441401d10000c0c18140f4050038141d5266407102c155200341c0e41d901c2c0c840c860f030300100308040c5000c0e034016500d9414081030030451408494000390010004818100d000c40110342183c2107400c003c100780c0e00d0b9800d2008403641110b08170142d60290b00d9404079280d901c480c510880f0a402580001403801104482d0302c0d011200050a40080181c156000c080d03840c3c0380c0301e00e0800207070710542c000d00e421002c01c001e0090a0000a20114074016228 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 553126303 1250 553125053 553125071
    0x603090a050d0c0302060c07080c03030c0409050c030106390501060305010c0c03020703110a090e0a030305060126131b060905061201092f04050f0a03030801060c05211c 74
    0x70341e06c0b00020500c03010700100050034000c0c0f02240e0240c071005491581125580d01c0c00b4810760105400500c289203020303041c000458140d10144e01560305030b40c0c840c0c1d12700c5403a0140d503081c9281d040145880404410042c1400a0109a001f01042155001d040080b51740e03486c51500f1800c440c480030002003048008500040020781c04142c18003200d0300004641c6810790000006a6a80c846030b02c0740e64100d1400c40e0211095501241c1c1c1d4102ea07020343c50070801541c03908010f441c000d5103802004c404840c0615155601100910810f0308020182054040810f869454942064540750040d011110250040100650140f100c0024080c10303980036040c0b02e410b2203800d040201c10b02406a0443d104c0212000720210700d142c8030303910161484002c00d45d000b0071070415081d07809802400d0140350380c0b08000500d4240324502c84110f0354980c0e13034060241e1030031408031980d05d41008211498024403541500c503e05100d0075450b00348015803403940e1101900654040d550b44051600401810310103c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 553127553 1250 553126303 553126307
    0x90b1311030606091602010e060a05040506090c0109120510050406020915070f14161e0602010209060415140a0201060905091c0807020106081e07061103090409110603090a050d0c03 79
    0x103103421500a0541c002e1545d80e940041c0d001d001001d0415035540705010401c19000c0c216000180111b02400940d50140c03128880a070302c0381d00391a02c850205c0c140c1c40c030800c814090503660006041c025025940c512104404d120107581081e901581c41c0c503000b00b0030100703514101c4c2e54241c2401940d140d4518085850351040040040c8050181120100115451152105000c03848802c2c4103004400c0255440300b0f440c1410500c003d020039070f01c41007510041400c500501c22100d660000a00b86800d10340ba10703040762000b600308151001002500000c20032a5108a0044c1002d0681900042502828520319204542c2c000b40114055444500642d6034860501c4080c00e4104940c40d000d44507076070b20a0143c0c050045503100c00070358400c1c8204003507030f81188520000e40404030000d444195540394011510610762040708001c0750400c1040d02d00524080d031101e07203da48a400d5501610300840d00107411504125400d40301c50300030f40301e603030308020742448200d811000e542841510740c1025100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 553128803 1250 553127553 553127569
    0x9230717150f01031a060a03050303180c120307121806020309011205041e21020a21080a0c030605100503100e150111030903071805070f050901030906090b1311030606 73
    0x180c03074010400c0f175000c545a51035040702c4030051904807003180e540381800d0442070000c03201111800014001c4a18229061425540c5d12404504440041d410600c0030748070100856040070040042c884a09070381c2e00003208031903604000300020b4029588038900600090056000704a0b00214140740008220010b0407400e410260070314000301c034441001140c9481c040f00c0f403045000848800c010800f81b41c40a500280800b0568852040b400d901d17040004034078000781d030114652020410b940001003042d5002d60100140d55814503000c500c6a0751080410b00140021030f1002c00a50300104222000088111510081c484007100c0d413401e01e0441031000c0000c8440c105241040541c12224003000420410b840d141407004042da9505540d400400c000b611000a00c03504103810080000c8400f03008001451400e00e49858641c5844240c03001100208081c0008850607956a41c415010900340c40445204046035480d180b0195058100303003072a00c542e450460b03c240d0009007042007686410300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 553130053 1250 553128803 553128833
    0x1b0b0f04051002071a19150501021509070510120903080f090c06040b0d11130302100f092c07020309040b0a14060309030712020c011209230717150f0103 67
    0x152810035261003c20407046c0840c113000d43c2050707003003040d9500310700007060ba0702c0304603036098085494000ca070b11101ea010440444a01186800c003030401c0041e4140451400c240010624014162440c0d424090040701e9850b4001e40c00217842400b0059000c02c801c008503004071000c40100141681c2000251162045000380c10540307802064010150a107500329070741654003005102c0d210f200b40151061b0700c10281c4070980c81415100c40e02c10b049800380c48010920041d594400b0308050605608607144244e22500b07001103000302e207187c0350030012525040d002d541e09038040d5944101660820090fa00086038103481005c561074104106210000036041505054450035141c0c2e448101d414154001e495014211414810a080c100741d8082035031480741c07030300740c0312900380b03544401f103420403103503811001413945d9402161112036904c100070100e40b501c0600700b00c03101292611608041130001c03082101140d070010700c4145c071a006228449501145c0f80e0095110380d0b1641d1500024008086 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 553131303 1250 553130053 553130093
    0x402090c0903030702120309010e060403050d0c080712020106030b09030a0813031b0308010906090501050609040905030d06060c061b020604062a0c0b060301020a0c02011b0b0f0405100207 82
    0x284035142500c0900031384148940081041c288028100000b907184c2e03000343e6805d80000c034040348070022407a01e4819030702581d40240090500d0914440c0c2903415444c04c0500b5140c406050141c500011f1144032a020140e001d0390000ca40d680c5545445c02c07012038041c028001c5038206100d100711203a40581c0c502c0c2d210160952465800040e800c0948288541c0029141c001038075800342002d0603045a0498101c0700c5451381042503d90711400103044681c2809443e5100904100b500302601d0280c000d4030391140100d0540c2d18082100140404681c520760190000c10b041184650074451070b48101901d480d201d2032078480324410042e0094603440000c00c001c021a555004241e005485c00381c1d0f00b0500740c5291303003022001c4111140902540c4140404445080f034000c001492410107000ba41c1e0f01d2846511025242001c0d0780c01500d11209003000f03891a030315262181408202c4400c0300901800440c0702030071003801d040c00c12609240401d1001d02046004201c0600001c07917482c9200720f00c40a071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 553132553 1250 553131303 553131307
    0xf1c030b13020f04080606100903030e121618020705060c0304170307031e094d09011d01180b150901020c0a0302091305031e031506030402090c 63
    0xc0001014000c49028003010a840070460808600541d4001c00503100c032001201c1d0b041c0c1d034200811600300c42004814000402c40801000024040c0203a6031100e08028070508100702c20501c1a40b8005c000c0f4000390025294840c10080c640402e100700401e0698a0307030940c5081503903241c0590b6804058454907400000000060502400301549400c5406180c410fa690b41410f80c001409001190040d0203004c1501c03641d05441d41c65841a120400c0d031003148a0134240104100184801c46e02d1405e6910700f44071041036584c40c1400d03c0c415032060542d40401070248050003803011040c0c05030013421243c0c081e10900f45903192a0411541141c1e440428221104802000302c40504031400b002034100108190030034400480402070b05e0b55141c2a401c0f560001684d0003009042d9525100c007a400c00c1480d00030952014540300001440c50180085a10b850b04044809050f0324001000c2402407001209000301101140560001c03071074116512030841c105500024091040501040c00345680 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 553133803 1250 553132553 553132571
    0x5071211090d0f0813032120010b120a0c1e0306051302121f0606140906040f0f050906060c060f041b0f08010e061308091504090b030f1c03 61
    0x240ca0460102580c0c000500e0717441c2d40d48404c1e01c0b8004141c40c007040300c2004001070f007903c190754840c0d020b90031503150b55202d0100c80110b1002c4150480d030410013001a548619441c540c54846c03040c15440001a40000c090212490510345041e0760704d500045101d01003102301c11550b00007a01c000c01529003120000999448545440c0c15600d00c5050080d084130b80e15413414400440070a210b040e207500018030140003407070384030b00c0001c42d09030703024090210303c4894042c242d20011101070051801c0141400b0b02d0141c0340c00410100380510350207541c42d21540d1100f8402c60030304101d80c0e40c10000664000341010700883c690f507100c480c01032010300c0354490301c400a41030040c0c0202809901d21360008900d2415180c0010290803481d50140e41169800c0c41e4100d330500100141c414400c21003222160000f140d1540d0381c010f1a80410741550348034a01c3c1c450410300001e0030700140000d00070404c002405405450078581400c07100314080360f49400802c282d0540280c0300b54418100360040c030b000920340e04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 553135053 1250 553133803 553133813
    0x30d050a120b1c11060307140708072406050603040807020105180402310e0f040305042103080f01350607110f031306050a02011803020105071211090d 66
    0x504402d403942d2204180660008403021403007450701e114056040c244082e1039101c18041184400e540f4880060308401c202030380103d0f0713000075252091003180040d282a40320380300d80c00c00960301e1407070400c2d620343c00d00c1868402900d0320400c0c0c01400305407803880c1903142c030741c072030329020301a080c400307030501c04001b40a0146207094444003401080080045480782d55007507003000c10b016180450007041c0036410100c0d03100c3c9400c0705090111030000d048060280e0f01c0400040d0b00700c0000d0011001e0150500020401e40306c080810f400703020001d00748102500030b6050003407400601401c504500140d0b07031300600c00720081d090000709143d40010f802d00103021154034150740c40d0964201c40200e001ea02c05011205510a82c840e00300511030302100c9404140440c03081e2240f180030446013038210301d42c100300800c60003040905403a04c1c1e14000010045598000c40004640e4424110011b0b55160304000308990070035680c086e4055035103010088201a21412400d42c8101003400d0b01c105074070070310081004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 553136303 1250 553135053 553135061
    0x6140925030f0f050f070e04020c100216050a0b0717060a03120908070b0c010606050a080a1d0d030f050a090c120f0c08010506010207090504050a0b04020f101d030d050a12 75
    0x4809804022600c1c0c801e1800303040d5517042d59030384005007100e00460032900d82070094038034090407000030701802c4403117100c00c2000b5030100752404280d41c4020000004a802417021309410b0703014403c601e1252401d100020200b003c482000ca1021000310305110750340d201c0700300304010b8950004003001001d150000a440a00c0c0c65481050380b88039442010880aa80401600c41c07090303410000c1c41515141c0e42d0070380b00ca024420060700051000e40014400240d0341d0044150480c04a02c400d4498942d101040d00700342980403148003003a20354a00e041c1c9491345101d60745d40079240304010045441e03588d840b04a0350800388282d88000b13011500a01c11b00c8011380c0c0085c0c0c010b0f4454911049180d03280e1503d406800308403070312400f60045210003e00c4c40d00c0d90080500c65548480900a00d584a695000310b00300094000c0e41c1002e42c0f10040d5056499a030041d401c5611141c60710510300c440f00c0029480c2e0091204a58082c0d08007480840c940c7d50807905030380300c84155042450f002c10303030558200014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 553137553 1250 553136303 553136321
    0x6150102030f0a1206050f060f1602040c0806100801050f0904150203090a06110721020a02130f05061c080a02030c1b0f04110414010e0406140925030f 66
    0xb490000c1c40a81154214411990f18103c2440900645540e50100030300c1c20300540b0300d190007c0707040201c60781c03411440c3d0042200c861158819004a500c40e004501100c0010346004003140300b580911200f03140000a0040c055010f1405542c50360400e00424100e90115804900403c0c400000c038007048000104105034181421007192079141011150b65103240081042d17070307030514100d40020b000f102d1400b10b8120075080190700702d0707108004a4094034256180c0803001140148080c2000507607949400000c1090031003c0421411000100c0500b1100068105845090002802e48078240c2c0500180100c40d004240180c0b51903401c14141c3c1548a403c01c180f03414002c503c858048405280c03182166400b042d03402e000326503000d000303020803150540d00601e05c010040c0700400c0300c5507510b0409a04d442040c90030481580d186400708040c3c0c1c409400601011480700c1c5d00c0051420411000c0da40407241200b04414a0308100340e20b1504404144c0401c201510303131600031684e8102da0440b2100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 553138803 1250 553137553 553137577
    0x809011a1903050f0705102d030e01143103030903090b0d020d0b03030310050609060912011a06031303031508060f180c150a03090503030c1e03090615010203 69
    0x5091341613900580c881a480c00b565200706261b02c0724461070340c410001c4224070040803c034903420705440581414582c10180c030000030192200d0f103c00d403142c0c0a01230b50780000a0000e00c01c4050401c200d00d01c070304000340340851044000001c1c00340700120140210560003030b05400c0000d44000c030384c11304462950f55a0000d803003a19001641062014050380180f0b00300d100310808100e44c1d9111404c00d0303101d10081d140280003141c3c28030148a60f2500d68001d2224600040030145404c101d00003090f401c4080d0512581140d540b0890001c14201c03d01c03a4240c62102280c05c2e61862600082803460280400300c003a00700365454400141e00100740110402a010780002c80b12030b40740020b80013070300103000c90780c250031342ca0401c40080000c24001103141d407116008211215110301501e4500080d00585400030405480e0000400802e40500084d40903009180c15566a8221022108405081d000090400a8081040085600300414010381016480900c0c03005050302c880101d283d4042c40d950501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 553140053 1250 553138803 553138813
    0x20a0801053d0f110303060405100f08070e06030c0a0905060307180203060111070b07080f0403140f070e04080301030f1110030605031501060f08090f0106030f02010809011a190305 79
    0x1840608451207103950040b42d901c4100700c1c2c8022804465070301e42160601e2580d801840410481c1c600303070304010b0303120b1240751030030361940d41e960898824085141e010000304d030048031080c000032250394845d03540418180c0061802180c4440843c500207514882d0160440e0380c1c80100d0b074150707000c0c0000b800a00400b151030074440d40c1e140303560009510a41d10a0b0121b030200800c03201582011880d0801c403480c0100742400d140b00d5848013040c80d8800c0c07005050f50001000003100144030782c0706198100715404020140080ca0200b22403800c407154000070901c0e40390104200000d01e448049906482e8005d4000d8194aa82e103044e049503510b810050b0b500c1040c90302c0103030002d981a80040700b00c0700101c04441c4443c90210020000441c02c7c0030342d07800504000e20a01010b80102c00160300104c103c401c07155a01b18061440e07017140c2d400c0d00100c1d18a841490301c4010f540e40001c640d90049041002002803c5058010b44800c5000c169102d004010701342c100e0108845e50341c5100000c1d600481030710 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 553141303 1250 553140053 553140139
    0x60c070b0304080405040c0e090a020d1404050f0d021f0c030906060b09030c010309050a14030c07031b0611060a18050312010603053129041401020a080105 68
    0x3d54540150140394082c85c40c10f8034007208184a48141c090580f005882d070140303a00d40d1a510400b03584088010000b05450301c0703030904c2d0313440300c0555280f082d4020406080304100d22810141415104802c9100b1540002c08401084441030020030003200d40c0b04000070b80f409081800d43c090300c010f100180c0000d1a00700700180c00c40b00d40000341441e00c8105c0941e61100085001034007200c0d40c03080003800e903600040350000011600302c1c64824000b0b5180881713041c210264001031400c4040e40080b2022091003801c2c0712015405070200300900254108a43c1d2043c40540c0e8036030b91100201103400964544034202c2d51100c030305c03207488281d5801005036642e4111507441d40c20045c0080c42880000b901d0080013130400ca06902d141c0703044808542c180810a4410110143c00742c001100039035070041e0100c0c21308404d0b030007055846a16076000b0803264940c9010700b81213203100c6101c440f00388142d004002c5224400e030320100c0e441c10740e2021a401d00c2110030032551500300d00b0304c1030680d00091100c02000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 553142553 1250 553141303 553141313
    0x62a140118030905011b1214031003020a06081608100506040b070c0504020708120901021c09031707090504021612170c090f0d0501141006021e03030105060c070b0304 73
    0xa000307050103034a540032001c0c0d4480045941c0b091600d02d0076203503500840c2440002d035102c01400603042580c5003a060124105800400650040c0d90790394130703500804820021130800c03221603c010907003401c205030300d840e000da542444801002c40c10710800c01c03a240050003544030402c0c0000a802c000e8420781c1c0f1141c4442c09180700354000d1720107550342400c2c0400003d682c130f8180201c2c6c03a80c03540210010700384032038601010b0035050058119541035400b0b00000594075460745a000c0e003003003169008a090341d26400d02912104042c40d006201004100070400d080703801c04c608034202e9109880050340e410072552181c04e6584408001000f0000140c95004180c0c3e001705000441c010901d00c40501d9100c04002041500c201001107400c029441c0c0706038403a2a010080d011240d0052002080c948100f544007021b802e0308031148144104a10700c20720113070b9810801004000f50340e0845103520100610307200c0d545c4c00705104552290200044030300c5000c4d8188411401081402c1c0581c0d00c905140c036003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 553143803 1250 553142553 553142591
    0xc03040303080907080312040c091a040e060f280c0302090a060e0906151902010c120506031509100524060711040e010623040501062a1401 61
    0x1540000e9803100401c0ca818000702c0c2000450b42817100031480d005105108000c4c41d000100161a00d90141a00040c662960700820b900b00d17100b40d0001c814420454100800c840390303c042030b211688900b040001c0800b1904600f13401031542d480004c030310180350700200c0030414040840c0f8500c906140030601501d8040d00a00201d160032541d14182ca40c0303d60381203d990300551021ba07445400f0102103502d5090200328460427080890b5240e290100c20f50581803000d00070401d407001030b03540341681c10402c3d0f8010410b0360355603040c100900190030000002582c1d9019203002d950726090a80202e20021000c02c07004c0c0b80d854501e0414032051410740c2c1c8010344084441c556a030b10300c002014904103403601c0c0c0101e800700390740038a055503414071210a1100a000c250129456903503500000b2517202c1c003101071401030440791191480740125090602080d01c5c0180e201c47c051106013120251140c66030811880344041401e0190b040b6116820308044440441c480440d19519200350940c8065400301 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 553145053 1250 553143803 553143809
    0xb01260109051501061803110109150905190e04060f02090a120b0601030507050d05060a0801062304091511120c070b0702191502120711060f06010e0105130b0c0304 72
    0x5415490380e0b1030b41d0989980c0046d010100d0300340104482840000d200e4114901c0d00d6a06241c003559498440c024410b00d5003044c08c2007000f18881c1703901041217260402d010310480d01120400c0001c0d51400302a1190400003400082406447d4140e00080c420030f981610842c0070700801c1c400c007007130380c50710406d95500365000181c500b800700400052842d40a4010240510701d2907540a182101c0c404d501c000a04001c0d1032140c3c491451400000c01d04804d011740e2014100d40800441d00c00c280c0a54442d52000b4910400d000303504000c0c41c0c2c404954043c21808443d540200301048011442248808030301c80c1903d03040130a100312040c8070514030182d0280007198819174000c6026244d00d6400d0765507041c1c07503859410760a00003e00a0008428011109909540d81030250826400756001c0e00b11030350454014000911b02c0c44081c440307a208000150300212052407258582c01d06c1c42c0000c080740ca0074103049042c0314000402506000c0100c5020b001042046da0003501c0d0280100056181c1d030240c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 553146303 1250 553145053 553145083
    0x109061211030c2214070507030f090302030f030d0e0f1213030c030c051306030b1609030c08161202010c080f07060501150f020c0a03020d14160617040b0126010905 72
    0x3001105c0f13800421030603400ba800355111142084007954044030b0b00d1a20300004800c012880c0800401620b04101072820340780d8a4010b1500d80c0034040302003003100c050781e41d075030540d610944d2410f0780c010010810025048071010700c140e80e10b03d051a070141c140510780c001024080205000400c2c4143c80d84184140e400854114a41080340c0101101f914200e01028000d0481107000c07650718a1200902500f0b0601400e020816a0396a250741040300080e500094041d0442d409402c0c17407905034070045001e000d030101c8500104c2d51b00e8000804944245500616000000608000000700c602c1034911301c0368840e005000c1507845034112207420320030f0480500403d44841180500b14004514281c6050018003d001401d1454080050040340140151068074007840d66042e280c50a2010742c8010701c0c2c4501c440107851030003100a00e0089940401c021a104004c1031200240c440d0217403504507041c1403080b50b2880b2030214803031041d0104c1891303012103600c0d04c10080100040401e02c0300c0301d0910f40c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 553147553 1250 553146303 553146311
    0x703050a03080f160320040815070504140f0609031603030e0f09060906180405060106140f07060f06080a06060509130b0a0c0c1a0f0109061211030c22 66
    0x8040000e202e07810584e502040a5036921515100e01d2081d80441401560003034000407040c010310b01482141c3c0036404c91031341a004031902e142c524220503c15508640d20340b500b90324084c40e10f81506032454503002c1c410701c01c28420120804581d140390645085c000018203075015070240465042803143c03148001c60205261181603101c1d8904a644c440748000082d001c28519036580b010001d500500038455944000210030748501940035000b540d101d644030300c0c0144080d5042c01006002004404113841c06401c003044154284803503001510740d00c980c80840403400000700034002015103800d82044110344a160522020300c40300350844400c8503016a18030301c2580700d10b4040c0c0d802c80c10000f401740900801c07030049070303101801c2d0740105000005481c025841c0155a618080c41c0f030701c10805117008042d41800d100030183c0c180403c1d40101192035007000000d18011000c0c0d07602489174005000051000840700042d14203101342c03440e003031009207880c031461318100400c0300100c0ca8448602442c2d00d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 553148803 1250 553147553 553147561
    0xc151d010201060807060311040902070f300e13050907090f050601020706050705030903060403031b03090330110703081b04090b01031d0309040c0e130c110703050a0308 74
    0x107110f15001e49840c44098080c15003001d900750050400107070341174103035203082000190915107032015101c020320406c1d110352002d1441c10001191150480041e19000c2d0450240c1000b05809080341d10701082070510000400940000440c0e0034014502d61282c10f003450104406140041540303415103444580400c01ea98000c1000005c0f07800c1141d107240942d001c80801e1190900a1000c0e001c0103200700100d80c60038080d200400e04000d01502d003200402d0b26110005035034800d5051413010800c0030b00d0b040100c0031058134014642e003013448446003613558080600e0003002d10640c400b000308180c4002809682c41c00407030141681e01c5014180e0000c0d0100380400e509840e00b541890404000008960401d4140b09180c00189068484907040c10358445a1440404012601058015182d00503545520b029000d01003620100b81c0003004000700126900c409640398000341e80b01e0440c0f5070b000140244203100940d0600726860f1000e4251180311000420040300181807415280300e80e0b290300660300c4d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 553150053 1250 553148803 553148807
    0x403082724011505160c080106090f0c0207060809010b040e06070201060b030705091003060e07080402130c1713020306090703110406121205210a110705030d090c151d01 74
    0x200380108041c00709541080c0040500c04c402418071560302c01c00c440e10310402642c4004c0d149095502402942c0d4498808010705200352060b844404e007100800e01c0b5450343e00c0740007511206230380180030611404001003162400254001c3c0e0031600e020300b0421005100c109a987c0c3c64600f220000010360900030049078504001058a00400c900d8642d24144481181017260a0510360031000416988010024950505101150040000340c40e01c540c00d0130180144910040c0700b2200b42c00103401c0c44800f0305165889000c0026000b0240c0b50642c0589425082c01c180742155a80a2340c544109024407845d0360b008914442243d12a50b041c040b903d000d0810720040c0d036000d20800e800340c00040000e001141401c0f00700c0010340c0c403d240503440c00f1080780e110000900c06103084a1400b0f442020400e84011621500d40c14440f80c154460602c4801d0b034400396288a40c240880b14a40c4480c4100204184190000003410004416a000b046000c600070001039890b80e6a00c0c4c10b801292030450b20754 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 553151303 1250 553150053 553150123
    0x209060a0608010b03040204021306120b090c0a03051b0403050313050d4202040305160e04140106031a04020420181c060903170f04030827 61
    0x10700661107404040e0320f4250458001c2d00020402e0744c0152302044180c0d6515854a1444040c0146485080310b1013080c0003050200c0704018040ba0184804e0350500141052a03400d0320b40c4520310340780104469031990ba28030f20481c10500c81000a400100d0088100000800548403140d21340c06004841c507a500200700419002d214080c0640744004158080c001c100e840107074020b071a00c8100114214034034440361036110036a1000020580c003150500820209103c40d161b0f0506110082d10041d041844c2c01101d40800380006001801040c44029024030a400c0000196040344586002e1071000d040420360b01401c450480c80b507071421035961203221002190f1180c007512010f00d070381458030f03c1c00c06403c2d030119401d820354410b8015040c0010b5001620781010b8062007003202291044a510300a00740350524405c54106448000800203247c4070144000d9100b42c00d03142c280043d071180c0007403c0d519000740701d21507110801c6884c0c1404000c03001401800d5854800d640c5861900607602815400e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 553152553 1250 553151303 553151309
    0x1503040b0f131e1a0c04080708070b09040c170705120a0207050604030302031b0712080c04062c180601080a020a08240d1208100b070b0c091305040209060a 68
    0x20710040d00035070f1504100900203c848031300c1014090500404c500700300b00701d000122014001d0340800a070901100c2000c2c000c82e401080440d0050004900f42811695903008000c000c07070040b55a0790302c005a0900c50755031214410010201d0884a0400c00001400c0754803000903000d54442032408100702c411548201e40407190010702500c99925103030b80032800ba5001825020500c6030700d400c034000058010b4000c0c40c02c24410700c0c991911440b184805454840000d03c42c40070300c2001d0104000c0580c12002095101f001e104500c0c02c100101c4051f810b140120320002508120781e8181c0e070000d1406a8107441c05280240c86007445a0744001072401640710f5000001c001170209004900b9900c8000c84014101070342004442039881044042169440070190541c0c0641c03119624400058000601940000c0400e04034164103040140760b5000e4420540c004203030b81c0c800e20001d0b0000b0324a405a0310912401000c10300e100c980d140480c00078203020b071005ea101e000e249001c42d401d4a460441c003411 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 553153803 1250 553152553 553152563
    0x403050703110102090310051e040312020f120c22210f0624140105030c0a1413080106120203060612010e010204060f0e0a03030e0f1503040b0f13 64
    0x64210595002c03555080321030000c090540d000d00c40120381c1c2d502071008504041111900180604c0d04001c511640040e010b150381078a5001d0081c0408281c0c009030f140ea890303c50000241e62064514060001481142c1000054810b60700c1401209061480201030901c4c051485241c210044203c841d588880382c81408052120710403044007c030740f1100005046400b448030980c6144441d200c0c48151002044041202555518100c580c141c0790f184000280000711000c2c2c00302200c41300080c040340700c0074010004285002c00e80c41c00c5144540300d0440700c80e107000c00a640321140d958070f40105c60b545010300031484d420450041031084003aa01c01050940050003040700c0c3d00e403401405014192250240b0107952944d40341012040c0c2400104001c04c00c540d01c10400d160540e40013410303140341c1141f03030b44601c034100001c00109a11002c201903056007128042d0080b6040780000d4900318402075006e07802140403040000303209000d03400e80c0c8034001079042000c0581c0ca01f40503000740803d041300204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 553155053 1250 553153803 553153807
    0x1b06110105180712141203011a090d020d110d080a0e0f0f010f022e0e0105070e010e010203071a1b0f030c071e0b010311030f0a0210140a0e030d08040305 67
    0x807260004034100a080c5005283c1d43c42e01c410301702c408500b0308030700070b580d040401d400100400c055468080a40d11074928000261308005071840040d001060903140640f040c11410b04072418007071860103403603259038014070101008000b86042403868100c0d48482c6c01145032101140c409040030850303501903c500400144464850740e0056460100b551001003c6210b01c19108000c907040c0301010135075541c40e4a61050350343c260042402600c1c01030f510340146034140002d01894903000680c6042102c000d0a141b44030004520040f40303580a00c0d0406080a00104a000520304081c19614002e0350100300004245440d005407040e14454203a104a0300501000004c1c1d24594201c09004040d00c1030b25003d28076440d540b0a00c83c8204940b90540340e1b00c1c1c016004104105420403030200304182500a001254852140d151b05d40d6200b0f000030380181c0c92034030503141e0390f4403030752050600b006c0c160442515034403a01e00044c600d207452043e0302d000384a4815401f851500071070005120340d5155031424 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 553156303 1250 553155053 553155059
    0x30c0f0d02120c0a03110a050402090603060f01140a0314090a02090406181703060910080d030b0d02040504210201020301150309050f0d030b01080c031605071b061101051807 76
    0x80224201d18864002c0c0d40551401480300d541d4410308200154011a503803204e00b9500000c00c25451556070000d4440c1d481002011466101c00d01640d6001c40c046404020f004035a0b001030310352445019500480c00000625040400e42641c4180c0101825040801d40d5a90f4081490340d02c07240240040d62100c0b01b2400500000c2c013540141200b15007085940d458890706685203d0101400c10128044130008000c21070343d0b0a05400d8198440c007402c000071822031030060082d89442e02403004404054442610300c038144c03680c80782c2c0544d81c0c1d4080e200700403d142900340580664503e0449007101c02c1c600740c6c1000c03414414029079069669031400d0341e49800162000b54000e014650b4120790078043c84c81c0407a8200001d104440b40340c00a0f490106800d00010001007010100130034981e00004248103110302e040c08000e10f01c41c14419810701c103542e40030070700b40098050441480c42d02c841606120115805a000048944038a00714000f402640c868103550002281280c041e16556400302c1020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 553157553 1250 553156303 553156309
    0x90d0e060309120d09050d030c090b090103090206130509010608040503160f050111030106180e010e06120d031b020120030a0906050a0b01090602031c09110409050a02030c0f0d02 78
    0x554010030b80c2011a0800a01c40100a0301600720b407852000e01545c4212010a000b02400140c441074083d107420414845100005880300c80305004040e0284004101c1c1c1d611b83c1d00075400301c4400c030380040000d900d41102d120100c8641d445409103601800c0d806000082c2030f400f0348506402694024003a60400b041007900181203c0b04440c20340d480c619034401074010800030b00c684a01c40005920f4142d60307606158018009042e010b468207812840c0f0403040190540c000b40d00c0d4192890800030f9403007904c501d000100a01c1d4402c030f070500d00303000c3c0c03c06102d071a5801d0b903c104420001c0e2681c4003e0050049410703401c84040c00c0c0074510317900d51151a07020f0b414641c401941d20901080d400140000103403515030482e00c1c111450722380c2c559111003d03181c942e08032600b4001020240b005601d00003404c029aa0b451140e4a00c1c00350090311040e09108221881032002c94421024100304000340107401e1040d03070b0300e0303810324160b01a005626901281d42061741020001c13000142616143d88069428 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 553158803 1250 553157553 553157557
    0xe1b060304060603120f020610180b061b0a060501470a020a050f0601062001090204020a0c0b0108010203090c01110c0a061e170601122012090d0e06 65
    0x7040b00e045540780000f0000030036410704007025070116a1040b88100e00d07008083d1a241001c0d189280c4500d1245040140440c11002540c2e901c5d410203002c0780c4041a4070101d6401d0040304d00c4401d035150503200e8443d4111001950070311090103182d090100340d030303a440804900340390989103101c140340c00301c0e100d07016018441e0714182102c1e591042c070005480c80c0706000d180740c00440003000141c0003014528140081080403030800c10807100540580c1d490a040945034008095481102c031002d2110980507c10a601600340250081c005560301d0601201c000c1c140c3d031145130308480d881244000032030904014400d4034441c1494000502400c1000d10065a4601e000c403c0d107022803007000c0c3e07100c2040c1c41e5407003a10010045ca40b22100f200030b05034041d2402344000f100e80020441c0c00224400050300c903c019030f4011000382090415032240849910160a100310369200301c1c0d50160b52800300410500c001c1500d1909840110000d80750030300750307985840c921000b40001912a5208004524206d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 553160053 1250 553158803 553158811
    0x1512070e100f0338090c0a1b080904021206010f0201060b16020d1a07120b010f0c081b06061003061503020f070b0702011a03060f0a0c03020c16090e1b0603 68
    0x1898050840f03440429800d11116882042c08110384d2441c2d80e829082c9106003030307008016208800e00700603140000402d180300c5005182c1d1015040c1e80700600b44200d20f41200e26125000e00103558410701c40000220b0008240c0d800341c001580106003906c21807040c866641a200001411032401c031920450401c042c12082042c1c0c0c0c030610355a0a40001604002015014a40e035601003e0340c4c580010003420358030900200520396414803e181c0140da82c4034120307040149060a113607103040d205042550a07030090400920580c89681c40806580b0400203400703105000403501568240c100600880c141c03400341c0f10fa40c009034100d42e00002d007a4043e40180804d110403549003401c009143d144c04003205000c0c0c03030700400360355140707a45407401190700280044402e0a03030080c1744605000d0810b541000e8000d0403000701c250380d02141c0851038401d404949203e4925001c0b150980c0c404928403080c0d005138401c1d01750031403501030644c4407440c011a80c2840c0003072054981185e018180240041c56000034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 553161303 1250 553160053 553160081
    0x30501031101230d0b1e010905010c0b01090507031113050307090c140c0f03070803190e0d080705091801090c080603030a0f12050f04060b03010b060f091512070e100f03 74
    0x40c01d040d9641c485a840f035510000d229841b901c81039001e40050705100841d002141041180c485074408503280d00d0380a811152880740018003652441030480080030001c00c0c1d10112000004c2c542408100e450003031040d1032044080c0c402240c0d4500100c01180c00c20310b28400400c0705e0b400001c80b800b401c0f4003d898905010025210000c0444103800e0542c0e003c180704030382c000070120a00108181c10b102d170a01c02c030f0a20204220044112150315a582c0c1e4480e00f0004018140c40040c0310b80d0310641c165200904007826080e86900d0300340341e0480500007400b1b402c401d0362825004100c854031841c00786005560243c05145040c5203000100e408209c4801c11501b448044182040c0c880190b00c15a40701e5820f8215080a506041c50f054040c1c4140003d081c0c801d038100082e00f08544e6030001110b0340c60204065040c0d031a200742c0c01056510ac00174100302c1d901c240118000002820042c82544a821690344100f5010404030802c080d8400368001c000c00205000e25041c061070095015090b100094 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 553162553 1250 553161303 553161311
    0xe09060a0306050c190f1209020607111306090608061f05330414030c030706031e020a200d0509010804080c0a140d090e040b060a080a03030501031101230d 68
    0x42404400d242c1180c02017080011450f200003445103500682d003901d250010030050190403140d80020b03083d4011000094800c18842906070310b0717070752000e020b191010f08100741809043d07a40c41c440c00040c0703001e2080c00c516001e0fa00004405007199441da59901702601130542c071860610040c01a0003490080991580040e5600103120301401c10245800c81c6090764004e076680d003081d034200700c07410889200c103000b0391040c9502d01041d40c1c00328030718080c0e5655141c0000d4400c0c91810003401250344e0841c040c03404e031000031040c22850b4410348605680f244610740300c01d4101034885103a0307214000c1449000007030702800102007035071265070700741d8105000d102000e00f400107101017241070100020341210241d802c02c090320b4004005020180d134031015403c10804140c54040464090b090040c40180007441c0007000030459590941c842c0c018102000c21104500540e01e000b80003844280000e403016200402500c48661207102d9461f100242040604036002c0804d0380f030451030b0050090301c6a40784e25 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 553163803 1250 553162553 553162567
    0x1507021203030a090c06022d0102090d081803030a0f03090201091707062703480b0708160201021908130e01080d050c070e010b07030e09060a0306050c 66
    0xc10806140140f004041c0043c02d15014906070080c88115032003042950440100e036614006440308211581c0c200c41e2200e5000c1d88428036071402032090035070340c0303510100040e0364000703211280c0040d003200d400481104460051000401da501c1c0105921500001c0300e440c0160243c0c1c2c840c0d080603105c1403041c10520420768403076581c0049200300c4213030340f000e0303074820841003065590040c45014041e11245050310710754008015000c20391024000501260122506501044e1100d80c2c4050803800c00c2c41d004040050301c94105a803044045051800714280c1d10011070b8000321001100e00e0264440750861606240c031012207420000c050059040d8000d110045807001420740510850f9840344030901d69542070b01c03205034030300516070b000f10700c102005c0740040c0036240d000250060415124100070f078441000490030f901d008070940140d5425004240000349034105640a8001e891003920740e654450008018085202d030203c400d682d026142543c1080456080ea00450308181130250b41840c00707113 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 553165053 1250 553163803 553163839
    0x912050a05120c03040b060618090615131e050f040509070e0a14011223070f03030905090f040b0c0c030405150301170a210e042414150702 61
    0x401c031843d24022100004110070040c0c101120f6920417400c60b1603900b8862007031601840c04105207002c80c0100d20703c401051319503489100b00c094248644d20400c0d9524560300500c064031445118103c20070050000c1c00f05807910140e0400c040d103070060114600300c115042004040d10b0042d04c03845160044180200e1090b042d84151071090210b042d0115451048003030300d8001500503841a603001d501c18500400207100c0040c42d00902403106018090340f84108030b054103010140c1d200103410b10712807000000301500848440d044440450b1500801d0b81e515001c0707041c10b00212002005803600f00300049500d41114003805004031010110b86c2020788a9000c00c90440c08011883d80d01e482c040010040031899003000740c3c5080605010f08103800d015600d041c109800c20f042842c41100d544040d4000c0d5203d0010130b660440000c000b4010050184007201d02d070707030380c140da101c4c00020314407408921641d903078045640b03800700070f405c80b10f1403820303880d03841c40b560015542240c0c408040120781594007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 553166303 1250 553165053 553165087
    0x7080108191505010f050a0911030c090a08300307020d030c02010608031b010b101b17130608060a03022b0c08060915070e01080402011b150f0912050a05 67
    0x40300c00171164494a00740000c102c44010603921940420b0705080d90810b01028910550782c20403244146607844071840800140d585030710f034004950034030a451214a144444018105144810b8240060000302074511090b0342c0c0700441c0c151026a100703140b075207040c52203940b04411050700c0c2d02c000180aa00d481c0c0c10340c01d50f4890400c030130100984440f0303032045890a01c80c001c0c0c02d000c1220041170601c0741600203071102140303034400d0800c0300d01704244d0303014401e03500c10070b0f00081c0e5141a0207944140a03407003001c000146006003000125081c000409500b8880049000c2c1c2c1d4000b4007200c035040c8801c03005031880e030564070107001c4047c0d0402048001040046d48101a0051001030105840c2c850501481c03c0d5102031102c0060310142c003802200d5810000c40e10070080213207441300d2107941c2d40c00160f490f04103000f1103001498080001000f07110f0703000d0500384110346c5120b0a2000512205410055848014000c2c10f100701483c0044a55800f81001700224561420454246040c81219000740 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 553167553 1250 553166303 553166309
    0xb3706020a110103050402092e09050411010e0303040e0a0f0203010b180301092111190308010b0901092904170d0306080c040e0f1e060708010819150501 67
    0x907034860701c007010030402c62a0321208601000e1a0400c400e1034250001802c6000280c0380751410ba102001c1c0744d041c003d004010700d0310061004441d00b181d69a4030b8505009110803203050320084840b40701c4114941c8911141255440020011410b260a1402c80e80030070034003a102c00240c030b40d112007500309203109e03001540c02407140c1e0052589404000102c0ba03003282c40072064a219034034000913140041c0c0080d0008103210241c2c6041d0600c83c4914109440e0000528050900d0740300303500b0f00305102c107010700d2580740807807007641c0384449a40d894100d5400c60244240f143e020405100d028401c0009107208114000e4248108401040c00941d10303443c0381c1d11030341150011803001d11a0403403e2038200584174411b06a0304d020021a450304014685611501c1d050901c10b40d02d40c0602603690300c00b00201090b11100b00d042e100c3d01980720740c0c1c1c60324209074282d0740c8600740659000034203990300503c05203048810715006040340e4580030449042464644200329900801c0d240d14a5035035125108450207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 553168803 1250 553167553 553167557
    0x30504090b010909110910021c030c05070501090c08101e0e150c0414060a090902090a0b03151807081b0c030703020106180213180902060d060501120b3706 68
    0x9071b40c003401d06021910710302400400a6502041d000c012003a800d40c1c0c49442006240380006905071800e0044800707214616020f0302540c2031014510a0050350750a00c4220303106001240d0304030000e00c000c130003030300e507406840d00b00081d07090103030701032002290080b03400002040203030340030319000402c005070f07881c0281c6a05446240c0401e0034010100f0b202c1454101800841e9014202804003030000d10301034081c000d0703841380741c0c000c200205551980c1c51a00c01505004030700300e03200e103441e9024203115085903c180b8480ca1964812214400300646a030340103000701d80d0b41415503520b0032402d00c80d2559540d10103001410801000c200b04100788050b000c013a100ea4004100e0502d0306070200ca40c05447e01d04001080c3c41041142e44811010b1000d40c2290010a0421044012101d105008052110010b0b40001001982c0704440300946c0c810010340b107090303c844440305614010102140d03600040180c01c60020809803400e0700b140d101000084920006c1051064070030540044031103400d0703100c040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 553170053 1250 553168803 553168807
    0x305070507050901031122020403050c031b06070803060604150305040507060e13050606040503030a05190e0d0b0405010b10020c010912050606220501030803061903030504090b01090911 81
    0x1081014401e1100505049030060160f5055032074100310b00c1105902180b294921074205540e4218014038450403549400d002c41d07c0b0ba98078148140c031980c181c4c0103d4864003545d01982c207030504681c560010010060701072030a0007540e95a01e40395038800703008540d100c0f01c04c2c40002800082c06000209108180e81d0203e520305145c9092450020a600302c41d0034868602c101750001c0d152411400d400f02007030400840d06403a10030200340c0a00c0f07a40c00440d0580400114044070f55007010050025240e50000e9580c1010384441c01c4515151031a1002e0348840303946052804078003020342030341d0464003a5000183c00843d5a002a11b03003541f096542000d600041084201c568000e2035070300081010040c41040d03816165181921040001c01309031245049848890000005036290407400700680b500700328030750312030800000541007114002c0c46071001c0c074900c54000c0c81d1091010100c1c0e500d500c8503030501d400c085540c0054811001041d0401c00650b01c0014840610b00602000116405403d9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 553171303 1250 553170053 553170067
    0x18050409240b060306010e0d02060f0714060915041a10091d071203170903030a050603010e060a020d0209030114060907170613020d0e010501060f02150414030906070305 74
    0x6003840854aa03001c1c01d05160854030001921030400301c0380e00820034030307181a1500b18100003451140490740302079005400440c22841052914004100640c01011004000500490354a944d00b008561940607070b080020919045010f40309001d40080c41500c05840e100c1c84400040012202110003003800355a1b00800c01c03120b0210320a101c01c0f050130450160071481000310055840b407080c4034440328603940303401500a042c40707030594035400445d98401e01c0e09401e00855061381d9403c2940c0c90102d240c40c160100700c7d50704e814810242030014240280407960354030760302d000c000d4024214001c14035408001c0070406a40038442c050131015222980551030802005010841307034014220b1040c80350b0b64001e2800c08049400d100d610800c2140c008003034609a0020300040c1c054a59814009824446100301d0103006400c4141a2000c965a2090003403900c2c1040341d44210044200211071800c10209000c1640c5280920710941035108892410142c00041459940800c00c02e03030010320701203400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 553172553 1250 553171303 553171343
    0x50714160e060a0b16030903050f0c03011506020a060e070906170d030203090a1502070b130302060703061802030c0c060112030e03070f06050c010e06011403060a020a0504050118050409 81
    0x2003074004000b55080303038071503082034410f030301d20710804060072034485aa50041d0109881f40c04c64a02550340601030b10840840340c0042d40d9128100c6840c14401d508140b0841124904200601c0441c0c51550003042900032a40342c0c00300405900c04441d11034000d02c0d0010801c03090a0040c17030000d0804444107107505015040490400f2051540d41c4201401001484914800000c045c10803a4012250765038510340c480c034206c000e1082c110024002c0c212041004030346e40c0c44416804c1c0884c02602542e40c03580d9001c604400702c450a00440310101400410b82201c04000e6000d994800c80a8101714540307500c036044146000002d1384601c17100e40ca00380001d0308041d1300a07201c20345400180d00030480700b410000490b01c10020350090004200010400c0304c0c0114094101c907984110349020345240c0c1d40c40740780451040ca8070b0380105000388900000700314541d08610031a0340601180d95207600f454140381c0119081d64102c2c5910701c1c0f0750000c180101e1607540c1c0707110f80c1d10510f100d0000391041d8410713585c413 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 553173803 1250 553172553 553172579
    0x7081608120306010903030f050904050f040317090615010207030209010902040f17150403030b0d121b0b06060a050f0406050d0606020d1d1309050303070801050a030f0305071416 78
    0x401c1d01c0901030082c000c0d0340c1d81000241e4107403a0306040042e901d850100342110305000c0c1d04d0a86a00604000910441010340f5500f9401940280d0301c050001d1000241b15410100a941e400f9040c1c0c0907200040c000c420444c1d01d006111340c1441918201a90794000828500c800c0c2c100040c0d0603030008081012740e1710354851400a01362111240b20b0120a00c005603241d21101c0c1c2c1d0110003002040008c0c0c201032007544a98801c41c0e00400c8060b079812641060090943d0701c43d84000816032490545210300801c0348001d450b40d511248180030756a680060007850b030814140702c0e05004040c8071070f0812904003001340028000130347c0d6003a1100b081020450a44023543e2000c07055410007020441303600c0e840b02803084034600076403424007210320a802041aa10100c4c00000500340fa1054010030800f011000314003c04081c0c3d02e00350541d80f640b007000720b02180b40c80700503d060244541080028000c002924000b400307030000d1140074544400450030040d101040300c0c80211207100510650000c100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 553175053 1250 553173803 553173823
    0x30a02040e0106080c0403170d0c020d0306090908070818100228081812100902040609230c070f080c120c0a0f06020918160c0f030e010207081608 64
    0x5850a09421710030301041141c403c0b4000070b03001c1c0286410040d02409508101c6540c00d02c0e0100401600d292404025283d00c1c80d1b240c9180020f050800014003180d4a00400100340e40014185190207030f160795510250703200311000c2c004448545a0031040d1b07503d8600c415a1300090750080e2104000b0244108903400850741c00b24a561441c0303e504c0301141d03415041c0c1300300c2a50307680300c0544440030000090b80a00e22000794441403288161303107003004c0c0268019540c3e0350f1003a14184038440e1074160b0001620b100600d000c804681038401950b09440b54818140c104540114461403c030041d19001090f141c0c040041e140300e4030010b000780c814030b03040040c22401f0b08003c140a00b08101b9101103a240c071b034200300c06410070a08a00c9041071003402d50490707a1044000700b10506802101001400c450001c0b0380d6981040713003900060503468012100c3e0034145034840041034141c1650754003981c99115141e03600781148950100402d21140801c10740c50260f4111094160880c0380c01d608510700403402d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 553176303 1250 553175053 553175057
    0x8030901050121240c020f0c03010207030e01082e08060f010f260f07050102190302030d090807020a03050c13090b04030540120b1902070206030a02040e0106 69
    0x1400040e114440c52400035100c1c4e000e080180041c5084085820b840c080c1200c40c4c4401d8a4409a025a5030300002e80000252401060700c6400ca00d110415080f40078408001c0e01281c000840301d90503621540c1074941c03080400c0340f41b582c2e0080c0700300140720441002566166540c130401e03043c4607010042050551202c00c91034500e03080d6050032441c201c1040c20340302d24100d4201d503508807152440d0a500e10117141440c881110800940c110115643e06900e03c80c00c0d003d4000d46d4444183c00440703032801d910694058000310714007040701d4982401440003040c2601c3c03410082c0041d0005a40d544600b000a60050009180c402c100c10200210ba4111551702e5074650310780411200001c41c0c0790103190b07005030141461a111405030306064070104500c00443c0d018128290924801400b014518485c5403412b00c92030407543c1c031108408000300b620800984140d130700c40006080184c0c000c8106420102c3d20002500340b022580c081101c070742081d074006910a070003142c04c7c003501d4030700c6003528010304181c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 553177553 1250 553176303 553176329
    0x70c140618040b0f090a091a1021050f070302091003050601030605041e03020d0f030513110f0a0e09011103190c0c0804150801092007051504080309010501 68
    0x8910011400020307054030300664440b00c10541954070503040040290340503288200c03e11340f0440001c000c0c0700084c0200c2e6014200c5010310a85800040d410f44102507150010051504160b08601070b503e403410403a00801d6030700c04d40c0c0c0000c0d805018120500e84094010000642184100090504003e0011001707119180081010510020365107044907000380700002c10b51100d09182e1000801c10180c0703000da040c205409810107a000500c0012104c0960b200e24215000b40070440590300c0c1500d00030504600030800c9000b01d0075800701d4a60498000301821010481c3c1c5011504441c056440446e2100b280780401010150038003940c03044c50524100c06180d0b14007103404001c1444902da01103206d82d07842c20322420841c0519813403442c26030407180d12501d035079840c801c80440c0c8031060341c9a00069030440001402505c3c60240c003456041090000c01e140112071405045a0424041038480e44103c00a0222511254003194010340c040c80b001640d07840e0103102c450a5940603440859201c1403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 553178803 1250 553177553 553177567
    0x60305010b0f03191b050303070b09061311120f0105090705010314070f180513050402010e0d11100e0603070309021207030c090e010209032d0304030503220308070c1406 74
    0xb000d022039400d1782d00c41031031214603041021041303400c4d0240d040b050305880001510b405000c803e9481c03900c15060401114510f94810421440d000462400203024580702d1448082c1413030110100040c2e0b00c05d0b1700480b0181071038181c1e118292001907403a139906400628043c841c6581c180240310341e80881308020701e107500303214500804100c0c0d91310b000001c1080d48107040364003081c1c03448100000d02c4014604500429544014001840d0954040340400c003801d64100300c504088450300304443d08050000b06066151092001d03070108109180104441142150035541d106000742d07024954076980000c80e8a2548107104110208290450321503002c0c3c1c10420000b48001c51003425034045500c0130400710f0300308103424064000d088040e9410700840410b10114007403195145010340c0705a600c0c200d02c1d03030a00b00f0180c40b4400c2e40400350440e0001c014030311911100c80e43d0020740b1820b1106501c00e10f566502c4415181d0000300c0200d40ba4240741a08104230341c04050066044071741121514a0105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 553180053 1250 553178803 553178833
    0x15030e0d03110f030702010b0117040507210204050906012d060f05041511060a09080708070f050709020307170106020a03120605130b09010803070507031113060305010b0f03 76
    0x10300c945410304250322141004568030072601511603c03040c0c50314241c0c513820400c0004e40070380041424140050009551103020303201108441d80581e82101c017801c2c019003000f074909090743ca0080308101070f82e582502840140c403540300300c40c4542d00c50406081d465041ca00c5220500c0f5230714402c404034000c0151009010071140c183e08003114a50305140070f9000c2c1d41a0150b40e03d00a5912200d656020001303100613094001000c1020007951500365001c030ba0b5103100440440d503946401507e400743c180b00300d00c0000c0540000700001d50149480d602044003507a10640b40c008140c015505481d004428018490341040c8c803c42640c011504411884d03041400003956042195070143c1000044d1101c070405040700d41c041e0010b8540507000c2000303910540854000b13404100440c90141d2041d400001d400740000c010b0f070300100d40c400003030b1900c645180c03107240c5245004c1da1681d03030003500200403c1c15214580300d220010b40c450000860140710100804c581c2c10030f03010541d800303500310704018007540f8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 553181303 1250 553180053 553180063
    0x30307021504020a0e0a091106040b1c021b100f0c080406050a0e0f0f0c040b0f120708060a0b01031505102706030504021e0a060c020118060915030e 65
    0x80c0042500c0d5107968403400000c070b071502503511085500c03d809080c81604105134104209160160750944030384844481401858400e512900d02500400c2c4141840242c6501c42e018082d4001d000241c00e1041c1d0f0898441e0000707074003e10034843d0303102d488800c080724000d02400100b0581d508041000e008a02e5018102c040e0040c8004c01c46513684002030454000c0d13901c48030f0b4000c0094100d44030051083c1c521a80c0b281c2c040c0322018148206880d0607941e1526000c0c04400c40009040462802c10780c00a00000310f101d5554401240214000803424a1003003215901c03e01c5030000216081c069040003400f01c404889045a5403240200b043c07107a07032a145403c2c8010146842d001030181002c0d409007660f0b40030f4901001c0740080c0c8580004070750394982c110720702450007221f40710400b40c03c0c4654030b41d00d191070101e010740112462000700b240360b0080819601041c01030414a040201510311130034201c1103504220007103180fa0400b8822000c01100c40c2400c2003403030400300100704610703000715510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 553182553 1250 553181303 553181323
    0x303061203040b090603130605090c0a270b030a080a080f06040c1d03070e09070f061d01050307090e090a12020c0f0f060c0f0d0f05070317040c0b0a11010e03030702 72
    0xb1741001000c14140081101107440b500c3d0080c0e000c0000d428003e60481d00d030601d482c00d5502c54440c19401142801c0013001c805180b0817110a010250032901c08444050101e0465560341401001620008a0390304401083c12155503a61003800e41307080c0c2019900303c18003804c9540907a1811116035012504a420348040b9100200200252585580000e1504c8a56040071603084055028010b400000045690031365154060944606403662401c903100e03108a102400c0313040b0700c4522219294050002182c010702c080c039040aa498850540488140c81a1100800c980c004181071092051580a84089441c0c80c409402c5a0404c0d0001550f81c4805021662050b4a4822004c0c2c590740c0304c0084502c000c07001026200d868941040c52900c1d0080440e400010031510041c4175a0144100c0841d00c00c568141c5801a11413a0240c4c4100c40600c0104101c80f129602c1d40007180b440d2500d800f42040301030550383c00301d48c0c01510661a003980d0350482c25850702d500600c103000780340d03802090080070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 553183803 1250 553182553 553182559
    0x150a0f0e190b19020a0206120705090a080d020615010e0402160210020604030215010f1403010b19140a120b0c07061416021c11010603140303061203040b09 68
    0xd011003a20001e9514040300000d910140403002001844007142000b4003000d841640310002c807452082020b81e144d1100306002588a40104000188500b4507808660001303060325180742048100c10224644407055040f64141e94000790000c0c007025410000c1d507502c113486848200540140c080040c1004a414485a01c1a81c01103800002d804070801e02c1a00103030001d15a4044240c0e022010792501000d980544c010b0050704400190400200003007412a0f5008441101d5540b5000d01500481906c60fa01541552511400021991490b110391244020034a06200451922400344100545e40e41441d000f940070090410000a50001c2840d6150b004641c4000350381d10a0303004c40f00341c410300030020510b515004645220802045c4160f103d5111072144a4906038103080581e503d00c0e0a04101c009036240c68000b0207001c0c41024104541034506002007961501c0e44e071031610344010100b60f45802c0c0d001104011003480c2c80c1c1c0030600c83d401d000c0041d600d0141415a0001c00d4810f508880380 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 553185053 1250 553183803 553183817
    0x9070c0f08070c08060c1804050601210c1b0f0611040306050a02040f0501111b0a05060304060f150b04060e0a050d05010606080601171609030b15150a0f 67
    0x28032080d000106a100d5105030a1642c8039014034002c000103105010300f0b4424030942002a02d0246448200c401c49210200301040d000240710802000d088005c088504005091901c004203410808401051210302100490411182000102041500302c901e00700c841010b1540c401049451500c035000342e030401b0000c50035007603800540480c0d2007242d2004000314a484104501120303240e015105807400c1c150140707196640c6d9001101c00010781c141250f030075009100328065209200700c1200503100098800801559038100103115600300f224103450250715600281150000d40c800e204042140c042007183c05410600b04918900072400780c0c100388100d0b01201d4403241d907405400402058020101c1d8400012480c01c2c1d03000e0b028078030a07100441c250703401103006503028030110301e80319205450450040da5040700600808510400c142d043c001c04250110209a40b014001c1c41010f1417500b124200b8055018004100724a0100282110040c80005481c0c1d500030440c41c074001561038150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 553186303 1250 553185053 553185077
    0x8030411060301031401050a020703050306090a1e0501170f03040e0c04030f110f040b060a05032d100b0f040b03071418010e090c1611032e0b0907 64
    0x2040880200a21907072080e0084000810401620215403643d80310300001d00c03990310341e07505c1401a4050840010082401440020044c0c10030709401a40280100c01c0800d6040451407414144e540c40c015036030020361140d0040c05007600d800c4884c0510034094008184040c20031032050f441b0f008034000e1424040301c450116018050404c01d0790b002d9a00441d804415080b5407030020748011380a03900301c0c048c416000d44004a4503062290602c13040c00504098034107107114a0440d5140e0005051425003881041030650a45500303d0011202d00040a51503090a0260303410701c0c40d09441d440140560401c00803a00b00380540d2040d18111854440360035140d44821f0025140107802050710381c80c0090101d03c0c080b81d4074494040750081030302078076a2040d4540c89005d002980600311848900600100540f010049500440c1840d641c00f0b0040c510900071580c00207420500344000e240c1390900036284e80360301c24111000c800c83c0c0816040c801c0001d803150030003081005030014a00410710140080705 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 553187553 1250 553186303 553186313
    0x10f0e0f04030c050601150e0f0a09230c0702090f090c04050405030c16090b011e0c030c050d0e120a020d02060d020c15010312020303040803040f1a07020f06060a060c080304 76
    0x100b01103901c00c0546003a0360715051420000100d16411400145403030210303081c0d032704095410b15070081000e00104110350908503008050800030300015911a104e08106c420610b88654003400f420780e50700c60796660b0701180100644440701801c009500c51520051207442180041c4841d107106c8191000705455580341445401c40c091080d22002c01d002d404906aa40c5030355400306d5003501d013100e108100c0d003062000115210741d080c0200c006410121a140c6c00d8080c096841e4408a03440791802c42d040b0b070001c0e40d41d01d0600480840f00c1000c1001c0a107107801c41d291104607800400d02c0b610007440f503005603800281ea400306007407010b402800005030012244d0358039011a0580310f1100c0480d980e101d0b2540c00690400007d100985042d041d802c0d840b046540b0110469009a42059074181144c4a41d150b914004031000303422201c10805060030080007a46c042480e1142000e500644440c40c9101e49140c20075000074110307445104004001c0c014990003000c003407a05904040c0c056100c4e82c91b40380c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 553188803 1250 553187553 553187567
    0x160e06010309020301020703021e300f0703080f01050906030d2a05070302090105031606051c110a0305010e060307031b05040e030a091a030406021e041d010f0e0f0403 73
    0xb019400d5400094103200b4940c000920360748550900046914121324407d689450314282c8030005403c0c5480d503013001494410741641c905035501400c140b0714000011b1107410040d48000740c114040781e419410400c401015680c800e0042000780d41e00e00492902c0000280c954406041000034091801791210710041403007141341441780d111f414040104100e05041c0d944106902c41240301b40d40c020000300b040c0c2004130f550a09280c0c8807a4a21445040c00019521500700942d400300c0c0c01034005604140d46090300070702c0400085010210359072a116031000301030f20416040003082200b64024000366441c002041c1c4103da8201d0041e030301c0d0054200c08480805507960107280e005007402c5540c02031441c044000d1010300e18546803a10b030240d8825031228803800c0c4c14140380404005100140201c2d5103600140345204108000c0b11000b003d4542c02e080c1a085a08442d0101c003442014141948015030404e0240c00d0044440981a140100c01f07900940e004085500c64031565020408160040340c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 553190053 1250 553188803 553188821
    0x201060b041e0e0a021c02070809090c1c0506040f090305042115020c0f0c0904020f0d0605190b090609041b09110d06170c01230309031308160e060103 66
    0x10543d002d080000030800031790002024020105180100d03501e00b1940c5108907000c1a82c007000a904003860f08040002d0560000e154521400003005000c1d02000300e00100c0c0469a403810340000c0301d042c64000c1c0401c17114410b0510120514000c0007102081d000000e48084444500c50301117440550384501940c0c40720100014550b0200c088048000c0340c40d43c001e408001841c0040710390591a1000655a0384080740c18550400d1200c00880d0150504514070715040340040c0540b00b1545e81a0349080803600100e500496103580c0690301d000315066400b8a4071081070868a001140c1050800a000300c480680001e25088403200c40509910094001c000104802182044040017030310f80c481c1e059016511100066103002c402080e03010728541c81003c4201c150b0020301c0e0401c210750040d10b00a000c11002258004005100a65403401c00000c0d4415425200555154007510700f180b1401c0c0340d00e4001741056000368521441d041202c2d16240c007100c3e1541102e031826100e050041c3c0c01000084 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 553191303 1250 553190053 553190069
    0x80901021e0102220f0608040f02030a140c0d15052a0d0f020403150c020f0f030705070f21060209090c0c0c030c01050711042304060501060201060b041e 67
    0x4400c40200110641c00b80a50350814400008040c08104100d008541c503170181581080e2030748002c0c01441d00c00e09034140e1182c890342d00c03051241c60a80000e858002d401004a5802c07000b29003050f00941c0c00d00081c140070b6001c2d900c40030200556a1107072125090301640240303041c3c2c0c40001611b00329120700469100c0d0700c510b114a0305071551485400e5198000d40d40303400c0d200c0c02c0000f0a6050a0701d40b0880e030403a50011508e89007038034441c400401034011910104114880c1c1c501840c80300005000040c2d020442000440d581c400034946541404070300d5100381400741102c02c0404c00b4245401c00c1000c00303400411802003040e550718200000f801640b0001e40c0007180642048101280c0320f004040d442c40c50740840350340b0780d284810103075600c40c600013050010300288201000114444400e000c0e43d10024404030303000348410301c0d1210210103d031880c0000f1000c14188000d001e058801c96003d400c151000388400f5080050b080c18602c0341b80b05840388040c4007000d00600703101800030207014100035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 553192553 1250 553191303 553191343
    0xc0f0e0a15050d05012705060f0303040b0a11070509060d080f031005030f0a030f05090406030515190b0102030415231305030a0c26010504060c09050303031308090102 73
    0x803450040c00c94100040f00072406207004c0000c2100003030040c00f14108000e001d08070301100c0d202d04401c0090a4041d00594000f0f4540034600250360342880640003800c0398030002600c03440c0c0594003c1020307000300c0b100320300c0350002c400038011030701c0c1c5c240c2d035603407009040d00c0c8103540d2920b504d00b01d0610302c140b401d10041d41d44007109120300f0715030541d2054100c5208030f0841c2c90401d5025000c9441d140d190130b000340400c420082140003517000300d0240184000041c000200181d480d00c40900b0050303000154600c2444810030800c41e03035a030b224006001d103403451080205000703400010f55070344924000d042c3c03a10960001d000c0031520070340046044010b0080c540000380e428640d52405030300b001d1800900020600c0001c00c40c1d0400086281c070790b03070b0002c0690703030078500d09080b41c50b14410403041825a14807070307100f68541d0542405105d014130f01c944c2000810907075805008020b1417150300322038420b41040050000c107408030b4481c403080d40c0e0003a554a66560301400140d00e032020b540481c4c1380c56840 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 553193803 1250 553192553 553192589
    0x302120a0602210c270d0b010909061503030e0108040c120311010f0e0a30050301030b0f060d030e030f0d020f1e0709050604150801050612010c0f0e0a 66
    0x7401d881109a002c00d03c903c105948610205011902944003000080c0003021100c42480c0b04c141d400064044e4068070311455400c86131036248091b00b0982007075844d6500c92032907e080184c1361041c0c021a5110f140303c0381c030b09401e5030f5004000c046410300c0d8a04201e0f40c000450140074402130f0b680028010f030b0528a1350714442e4035018000851480342400319520380801c40c901400359001d902c0d08203403164068000c11106070b07a00600c0d0241c484030a45014a8900b21081102d80d10308400c41c0f0880fa0380342c045c1c80358511702d00303404003010081036010403407902408c2c400203443d444e00309102c969050400303409950300c55022902d400314041040790184108052983e6580c5c01040e101900b005032015500821000705109603910403500455881343e0100d070041000c1c107140c1e806181c0001e0001e1004c505040c1e036001c000c03080900340e08a42c98695403682801020b142c2081410b4011a42c003000780905041301da00902900c00c0c005016041c07040315201c0d000e0307030b03560f507050540074212140d0700036140b0345 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 553195053 1250 553193803 553193827
    0x31518060c080f1e0a1506020304090b1c060f0912030902041409031e09040218010e0306042f04050901020c16080604030e1914150f040302120a0602 65
    0xe034804407007020840181c00303d00000d03245003166100e15000108074200c4400d10701d021400c02d00080c9081c400f1a034845000d81c80c2580e01e00490b0062a140e801103803504d0501025104a40010490902c640040f15889041c156407840f41900c3c0d5802c10400940000b001c044000646100503000b8081403d071390300042590342590250f0700c0f0a00035141002b900c0b451404511040400303035201d0610360320920076030a50120b440364180b80f0001c06145903040000304d00119013683c01c004081e0b40c480c07801c0d0355603039420350340700e1000340700d4080c210000c04541c2425160405030002c802d6542403150303099942c8080842c90040c40c0380005002071700c100f2082c5080c0f620075000750000c44181601c0e01400c0c3c0d03504401d05405038120161000314001d04404c2e1940d03030f02a650070000d551030640105401158120600c1c0c80c86156004207000203211240705842000c20060807076002d40d40d004d00e0b0090003000e00140d42503040c3c8042c0c0768103441c00211011006501440d007601824020141800003402e403820390 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 553196303 1250 553195053 553195061
    0x40201050c060c03011e05090c090a0e09030a030e030a230405190305160e0f150916030e010915090503120a0b09010b160f0c0803040b121003020a03151806 68
    0x1900204031442c82001b000d9420450064603c9443d50081c1e100c000304040641400c0200110040100814a559a10b0000100c1280115040980340d00041009100140c02d4000c40180581d82c0000d07626040d00004081c08112000a00c08180c03284130598010113003441086401506009000c5507601c1c02d4030b500000c02c818140004c4900380149030311a0400d01c60004000240d650a200e2803045546110010051000007410320780c0f82400f042c01ca5540d40c60713100d80c05000c6c03060180b010301d20f08600000603058a0000c203844006a260015400215510000c002c50954480748041078410441c206645103018160040282104040500c440101941d0040d0500c520907203500c1c00c241c1e44c40301c0200450084215600b8030300c00f5840c4200000c0d155030504c5d16524403900c05d130042c4940351001e0b20316581013500074904044000510606440204007010790101d00b01d1810300e03456056901045002203d440020400d6a040f9400307587d200c92904408400ca98a6010b5040c54490307003070800c064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 553197553 1250 553196303 553196309
    0x305010608060c040e04150f14010f081203130807120f0e01110c010c0c0e130308060a0b040905040507091508061602120a0309060c0915031a0d0503070c0306051902041a03040201050c060c0301 84
    0xa903078bc0140004c0ea01404501d0340b00c000130303c2400f1419a5103e01480c3c80100b5214412520203108000050000d945604440a00c070b10941e6410003503140d40c1c80c054180c400d104080c41c10300104100c1101203d10002e103050b09008207291401c0011094580389400520540040d911241250100082581140ca641d18518042d9031b42100300e890711002d200700040c0a000d4588800801c100c14030a8110f940c0040360058407400403540241c0e43c0e9031400044810003626980c000c5200e0030704002c807150401c42e050b0003a185207107030213114088403c080d42d919220140d0801c1f043c400700e100d5107814013990040c941240c0000007031009e16034003100205602120f00808099090300c03410842c0d001e01c41d204811000038140e1308004041c0c42d80d010400700c03040a510455a070302c002c120700f100049202004000861245902140c83c0c00e0554000c203882980051044106e132062004000701642210312007551074408003032035500c2d222070004031124811004a10351070b21659003840300a0344d45400650407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 553198803 1250 553197553 553197569
    0x40b010e09010605120703020901050a0c0305092805040203060d0f02010c14150a0506210c1f0201060512190c08011a040c05090d080d02090a0305010608060c040e04150f1401 76
    0x203151b4821800b54128001c460303c290004d081444031041c094000e07040119064080c1c140581860079a5000030a407c0520000700c03040300412080e1212841c2c140d00650150808680c298154034144012508181c120704000d462203144103403400c15a401005660182c680180c1c13034840c2c000110701d049680385024a01400c0c041c9002c400510400c0303107807180501600000f0b01880c3c8484880e1492151080c00c200001800d0048164841a0b03548003014040400e0b040b002440c12410034442c0a400c581c4694070440c0a60115855044519400310340d402041f20162071410042500782040504d104044d04510420340c0303021001d0b42c0c89014945a01c0030080112003d0146101c91132007200d1500038591010f0b04410401d0503003000130140390280c00300486149006081c410070f0f60000b40d0301c0200758000c4e25a6555a50140464401800361a92210b4265100d03454035290201c0044100c0c0000c0010780000d8be11040800308202c0c070780000080000d51502403010984000c0c0c2c90702401d0081c811001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 553200053 1250 553198803 553198837
    0x9030a050109020f040e10050441060112150f0203040506060306100609300308041106030411120c1009050f042003090a050106030c051c0c05040b010e09010605 70
    0x120713500d003070b001c0c0fa0740070300112019015500c0c88445e45005803501400485000b20840d003031a0b8181034100342d15078003d0800c0350310200441403103048100003205003860941034019000502190f101c4042c10310b00c65a2280000320660040c8a0004c014100c2c0020042200d0000040c401400400650140548401c0b0300303440301521071407002c6120b0f034410300c41c074404900c008a0400540c284007109403040c00d030900c0043c078651044004640103603c084801c0b00171400000a0000340301c484880b1800346d401c00d40b185451410a511070062221070002000c0c03081c1000042c0e914800c03824131844aa6620190246e0350790029000d0240410311140111805400740f055005511300c0d05000301c512061a00c6c041002d540417650920b03565510080100e400340c8510340700d00001940034442e00c2e004500903550b03484400d05110030002620340e4080c801c1e0300080c0600d00c1e900400c0c04165003004451040f1000185034030701c0b50041e1189101c0c0862150b01449040000510345e030003d0090a40d0001d480340d9003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 553201303 1250 553200053 553200079
    0x8010311010e0f010309020d020d050303040c1211040c0201020d06260303040809090c04170d120b18100e0c0702120312070813060f0c1b03080a0b0609030a05010902 72
    0x450208401410550116032070f6010f220039400b981c0721042181c00503111290380c880c2900854560802c00784101c5d03043d40300104200c184080103000401800410203603084004050300c0c4d00001041c1d980c0b466110301e907142c0140c00901d000354111040304449000038003409a640906e00e400b440800030305981003102981c03203c24500048112489940e0016855040c6100312081c460001801000b07210803000c1044040384c031a00210b80132a451044c1c00080c090b0280c43e2030010000e0350040440640707a82041c0340c3e405c1950701d003580500925010500920b0503a00c02081c40f00e00350f00d40d4850400b041c07900e0305000c44003150300c005001260003510342050341c1520101032540ca118090711100040e5a12000c11840391041c1d0084d40c10074001c0c40c0d01c0c0d4802002e5100c41084030f5140d0203181c100b50b0b480004c007603003541005c038000f101041e5160210303590045440251020200915640741c896503441030f17100aa44803016034910b103d01034126182d046131881c102c0d00901d00ea100a81c45600490501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 553202553 1250 553201303 553201307
    0x1b1413120c140609060f07020d020303030a0203091b030a03110111121e13030507060f05130c060906051b1501030308011802031003080d09060c0906080f130f051203070801031101 78
    0x4400c031400c0a44046d01e4000d80c20a2030b9200d40103800220b9108400316450320140c0d808102441c0161045500166241403c60600e86006c2020500c04410030720350120014a0b500031540249103909418800030400529403c50300419942000c00c0c03a142e004a1036051251010103120312800d01107e00180c0d00b21001c4c0d0210f10544102d54404035000320040c4ad00c002803003000680b819034859400842c01004007609401030b2042100c03421900d001da20100030501c200c403440c48000f03040a040031502c1b5802c10340f0080562199014203000300722500c10740d130107100082141e40baa030300d050340041450b540c407407030001e01c020070030311558440701500b0700c000c0b4610316a031003101e000e04541e01c182d0461b149140d81d1110a40c0000740150b0034a603031100400c020030304030302400408074072565690310323484c1c02c003400500301c42d0010707145610702c442403020410303101340005407004200d07000080400310641c3c51411901c3c2c0000c0704000c118000c03011040c03056440c0c00c040901d06907885078580d070300c4918201c401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 553203803 1250 553202553 553202557
    0x180312110609010b031905030f160620042102130203062404030b04110a06030b10020106032a0b19090902030402180c0c060c0a031b1413120c1406 64
    0x416811780001c0e0b0035800c40f90801d610086c4240c824415241000c0905460f812150007140305103a0311580c40c08400c00300400380c496148403001e18207a07048060f030105401d4a0602460080c140c003441c408441c080315019200045041e641c1c020440302111000076203c00c00b80d00150760003801400035460040c90449408580114418503d11715818103180d42c51b01000301c44060300a46210801d07400241140c0c0b0b80c01d800313801420658801240380c440c05030521024800b500d030035030700b1645001000d10000351103821a520305034080c1c803810044040c00c0807d6110390101e07031100b40500000116904100c82c05a601c8407004c05035210038010741d95900d0703a03170164401184d00a43c04242c0ca850b0125441b00380000c0ba410500c0c040000d400c00702025038480c5420003c5d907030b61101c3c070360205018200c2507060041c1c0d01c1c804440c41d004500c2c090400d1000c0c000e0f03201d0718103013144042c0c08030381e240c50582c0342100a002000500b890449808050604140c0002203000b598000640c90310740468905000f01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 553205053 1250 553203803 553203821
    0x60e0105010b0c0d0810120c050316030c0e0c1317071203120c050903010f0b120a0c090225080a1121071106040e0108011a1018031211060901 62
    0xd0f2402050f44c0c0e504942802c402880114280300100002c2108850368003440401e0b4403d64103609200c1c109001c0524040c40003d22103048850540c00b400012022003440040305d00d41c802580f031944070151800c01c82d000c0c4640c0c0e603206400d01000040c090144c90f070f030036140002d03d0307060703a0f40c068580140c00d2100c00a107801802180124401e080c2c1841540e00c00c9241c1111841c0a9040401110009013075460a001400c10580c46e02101c1115180c06186a0002981e0300f00600c00560700d43d4802000c5082841240b00d55030707011a50000c008048140488041100011125911f000b0f1900013500d40140f00c0140c0080d66441c19101c0d60710340081d0001e0f5a007203015807100700c541c0e80300c0c903c1e01e10303441140111181c104501070130b00951506001b030030240a100592040940c14000d450f8211303004840c42141c5c00212010700f850503201c014405661952526001601824001000303801081c540d01c01400c4440002012484507030003041070200c42c00903020303a5413680368040c2d01804d84070555 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 553206303 1250 553205053 553205077
    0x504022a0331060212191709031206040903080112060603020315040614070e100c050f0618060c12091507120c0206100b2115280510020a0b04060e0105010b 68
    0x401044120307104020714081a641d45414181107881307e0310b1440c03c200941d41408075a0002c520110b52a2000c2e1042d503005005640410405c039860300c00514164040c030401c214103c01c16a80c60a010060f00980c002e16005800c03541d200461006140070144122020b0700d5482c0b900d5261101007030b00c5003a803802015250b032000e03801e110030000c01404100d641c1c00d401c1486050302000c40090009e2001c01a40700b507410282200b4909101c6014103030b0070088080303a40303070042000c12032803208000998030b01201031802660a40c2d190b030001c0b440c007045c0015040d05010703080304010381c45501c068000019a454030041c400600a2001642c1c0c0c2d0906440e039046131712503084c0511060806001800b1000064055078050002071403100360703241425101d80d042010081490701322410070002c1040d0030f4604413440c1c1505d02204107802c104107002c1c0100b610a0325041e0348020154420001c800c103054202204441c0c80c181468914000e080f00e10454103a9400c04000040c0500300b4000c0e00c803800006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 553207553 1250 553206303 553206307
    0x703031802150a171e0708011805100308072004020a091403190c08060106080f06010c05010e0d05070b06120a06051012060c090504022a0331060212 65
    0x720b01c0d09102d600030456540400130040400c038007407980d0a5030503004a40d084481d10841c3d40c0801da8051612004000741d06000b018001000203c41c0c40030320320a210143d5400080503107800110710240905944050042e107400b299480c2070202000e803000799503145180506881c4108402e01050b802041c040401040104104002800781d8100550401d403004040d0743c2c19260038411641d5085000300140c0700065900010301c402e24040001074050300050424500c945031441005c0800d0b40020045070420035002203400030000c0c25080158100032100a54408a02002c0000c10382c1c2c00c05801642d42c00b120001003402418507040e214081b22541024100700c074801d49508000d80400f800c102c0010142c4000001c2e01c040500d00f007102e0034030514011036511842039005107402e80e540c200034030551040045058200302031b0009045204440c000c0d03100940780911042c00c1d4003451030408201c40d6804140400f034400c11440344da100049154840c031640e26250202d139288030500d0950800303101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 553208803 1250 553207553 553207579
    0xf060d0f140606100c0b0c0c0307241a01050d060806070e031506030607081f03060902040b04050f061e0a09021e360d03090815090703060e071a0703031802 68
    0x6c1c85070356075404200f00902c14602030052028520b154815602612002c0f0b0640c410040b03900550a11007151120700350a01c510701184640b0b0212029503070482c1e05000c030001c1c400644042e40d400010007000a141600d03001d1410346006800d0354180400188a80100200e01140b50002d40c406402020080c00916596a8605044d2031117a0701a02d0400c0c221307480c4100700c5500031055440000b5600c00c0001241d000007900c140010f44000e616130768450b6082c501013001c51001100640c3c1c2c000800c03100700586070f03e88420307165a10180180c0581000a8043c00b1851030760030780080186440000302c031b1040c00d0646107401d000b4011503408050050a1b000c0705202c5041c003d101600c591100001d005d013945c041d00026a010707803008400c8011a603004001c004180017400440c200c500c00172042e02207031600d00015034a034551404000c0c1001e1341d070380d0302c0710440c1c0040140e02d007d410b08a62204148031125a200741c9a080700408500285c10241200b2440c050765008613001580505224034800c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 553210053 1250 553208803 553208813
    0xc0105070c0b0715020f070605010b0915180901350a03050a0e030d1206050604050607060c0e12011a0609060a0305060f060706141605030f060d0f140606100c 69
    0x100925082e212084d03405404a50051944014201d000a0304025584c6540c0d07807078480c0607184140d01201c240b090510414607181c0340c10740e00d031111009400e075041d6100d041c00d80c0502000a080f503501d4205881c0c100124000007040c9442c0764a049a20800c8500b08521004120809040c2d44c400203039000503a6800020f4000d401414603800c280c20211035584502c00400e2401c098000000b0000e5515003a4240e140300e1031003500017038030041d030b1040e24003030604002c980540b0440708014a6907503a00b01140c1c109104442c0500c3c140402030031402c1740100002458040d2031050329011360301c000c0d075002604c140f030905d04564000401520140c1415101c0c64250b006180041c54203801c0310100c81406400d40c0c480e0010015148240f0700021258075000d0300040c04031000384070303007507008040c079500d40e4084d000002d6030b034403400d01d2403a01e080e1b586040106e030342c0c4814110010402003140c44610b0405c4403040507000b200748103004460b1141c5e189400c00c400400d031003003010b0215201d004080003040b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 553211303 1250 553210053 553210057
    0x1303080402061215130612032001110703020607090f060c03031401090204031a040c150e10090510090b032202030d0f170408030a022109010c020c0105070c0b 69
    0x6000074091420f1078001402d007000d1607011100301c0c10344420540910594509001c0740944c91820f50020000c1608000c070281c03501801040180c1405100c102c84521009001c4141031100c412000a11407450741d8082840140c100322011805400340f000003d0f4030034841c040c0303282140d0441884541c124500340c4241c1e40d0200450081e800c054844e01e14111000038041c41c035000784810500180d80364550300340065010a1181d40352011042c0c0d1b0140703c04600441c0031030040c0e40a0105c1c511100300700d42c800380c400707189218280d90083c248100300c10720150080b000e101100d00c19640000505c42403032085401d10b0081c000c1555000c0280702141c0c1c080626103003030400740e6404501580307100558001078034117140300300b800c0d00080821801c2c10000381e214042c020f449000b035402e003000b4142035441c6980d9001c01000d01ca50181e003c51441d050590030304940b0418885698151124208a00014060081c0c207400b100588240c6403034038003030b500c25412100c10070340141c00407207080d007070040c0a4029 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 553212553 1250 553211303 553211311
    0x2101080c090f06010c020306040b0109060b09060d0b13050103060902090606030402030d030f0605060412060608030307020a0803060114030a1d03070804050d050304050604090f050109020a080619091103090114130308 94
    0x5c0e00c00551801a202000198004c1d0b001e400400520742c580106042950b40a40001c10442414400c886854641d001030364085800c1c910049801d118010108220f13421200c004840581014000401e002c1c9079803222440a0080c0c2c0c0b0036202e541c07100103000d0503100035a8025096030242803182c9926219500151841060541c08030318036544000142140d0015044100c01e1500c0d4039420003040f40e14445c5030010009000a54290314011750003940b0740c1c540c24400382540100200051840e84190210002100600081c80d22030511844c80d1000b002051381c048040620380c4417081c64428004160f90f4a503a1209883d460f140c100740078010303180c0160404070348501c401d0101180e5030ba68040504007800c01104000f51020724a088081503e030103070300803043e1620410030f060545a02c2001d540d80245c0c29a074010344001991072071000b051543d03100880071071407c0500d41d02ca0820340015030282c60050001d0149000d100d071000d030701010030b4480580b6400405000c50020740900354260740 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 553213803 1250 553212553 553212557
    0xd0809031c020409062c0103031b0c09020c0d020c011d5a0105071b030501020f0409050612060402130207050a0c082104050d0c0302062101080c090f0601 67
    0x30f142d525400c2c401920140d030850022540441403000c8143e81407802e01c2103800764034038540c03100e51641d18003400752a603440d941c2950080c04130005050000c0e021202e03000740100030781103541d0f442900200f078495051100050040c00742d1902c4504561140c03600034541d0414010440040351064100540e0011b0714013150300d4244614030080c018001501c0c4c28204051a40b1180301402403509440c0750385d409072590490465511074000c5035a40d006080d18480c84e888042541910040240c0070b107420000d0b48000e00a6000143c41e04c90b01801ea00500111a84014203000d81d8403024200071801c06550084201d652042c40014058070340541461400403c8000041c5002c3c6a5245c00e401c058011406640000c1c81500800c4000010403514800b83c0352816400351044661942c0022885580300d058403956952030400d09004a01911100641e4014070456451040c8195003000081903a4004000c0b4103000c00080c0d0700c800844c102880c1c00c4d006224180643e1081c0c2c5503100c00601402c1c3c281 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 553215053 1250 553213803 553213807
    0x816141c060603032f0a030c23031c110a1407080c0102070c09051003120215010f0905130302061b0409020d0e010c18050d020118090b030d0809031c02 66
    0x114065100b0707440918080e555000c100600005166940079500c8209801640d90031a8080850000304855440325818540440074907641e040400018401d42021a0181c1121003007204801d0000010000ca2000703004090842c5600040e03c012900002000076044500300305407c42d0368800d10b00120031568520780715040015645400c1225003040030030810980d400174410782400144d0350040000c000c1c02d1014000c5241c2000b08501e45203042c80004d09001c1c07202c1c0d5070001ea5009201c40004d110b100e110031a07080d030b034891390301c0800d000314821000780510b05070119216100c545101c4201e00e41540040c4001c1e200c2c0005521b07a241ca80c610006401f606000209104c00719000424241956503000b0802c40c55501149003101c3d078105101c0180000da10490380841a03a00e841c1c0e08991048410409030178540c0016214041a0203c400b119442142c000c18900400c2e03000031201c0205800b21928014010803d0f6003034902622210503590051180300310948005140d0300310240d1001e0054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 553216303 1250 553215053 553215109
    0xd090f09090c0e04060b03070b090d170417010b0a0b07020a0312090f0b0310091803080901020c060f160f140a110d0f03050f0402281a04081614 63
    0x300e5142019141162510744441e46e801d03503407404024000c0645544100589031086000c00a400d204c5038860041246c20012038030001682c5041c2524024281c82c01c84600082c07440f8002030003011f0400b0220b206410072000412201c1c81c0c102550201c60740981000c850500719190004d9072000207812204006a0784030101e0785003a980c98800003030640546454803810401001d01808080f5080183c0300b46c9803400c0d1000701c24a90bc43c3d01e19079501420054100c6d102c0800309401791081c0c03d03042015118a600740070f40000560f600343d11488000400b4483c011500c1c001f160b006070b55459643c0000c511080b101e42022019005010488a070b0800ca010b03456400c88050038000c101d2040000300700c0742940c000c2200d816005080d0710440601e4001035501d420742c001080f18940340c0400c07810202e1450070320300541211003500007404210a5804815a54000e0401030340d0040c0a10b607000e000702c050a00f0003010340385555044c2da81040300c0b80302d118a4082800804401c070041d80000c01c81c40c40e484 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 553217553 1250 553216303 553216319
    0x6060913020a090203070807020c0f0402091c140708061005040c0c02030a0b0907090207170a0504030c03150e0c01140a020109080f032d0a050a0e031204050d090f09090c 74
    0x450001c000583d0050b8480c40e0800c00500300c1a001410390b01550800500715a290355501d903d040c1801003200d005840c0e0800700007042c0120201c40700d01c450444444907800500813111000c1c01c8119031002250402d40d103801016881f40f5040c0c0f643d0000c000e1650003480303186815000907030007034500d103401a01c0c50718a400003403800e110b0550a0381c0458407038052000c400001e0022001030410b40310b056244c403071159609001d1b0300302809491000003001c51400c8200e440780c0102c90055800507a01c4401c4e6890781040c8a0f80e80d03a481c48148482d180190040c605c40c00800e81d0031251205031107041b464900310354103c1c0258807280005085541e5096820300140708070700941800464819280d03164030b01010f8906004241d4107042e14508a1a40c0101c1c81180b4003c18aa019846c06004a0305881300c1c8131020150184110109a5010101d1103074044440d80c010f00e44a02c0c01681291644040c19400340c032010034600a0b000d44c4002884107208242d00c0741c000224081c815480c1c4880c07a55a04c0c41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 553218803 1250 553217553 553217569
    0x6060d0305040524180f06040e041403040f1404180203100e01020910080f0901060e15010302070c03030c0b0a0e0c0915040915050c030705041e090203011404050c0304050606091302 79
    0x10b0341c0c105d011065004001030600c10644010031000f51981440c207821302c10100703041d110003000100541783c030344001c0425a500b44180c500804540c3c4181c8a1141c4800ca5008129041d2110314015480d100c1c85030701042102183c1da1925030003401800440601d8110b500140c106e0360007044e103541d0200070051312600c9500180c07040d0b011a50303d803904c5040c00b0501050941d005422440d003a810403d0034803200302483c203070366080588468000500c881080060f4082c0c00703494030280250a60040000038190007031645443c8512070114500c680d0b603525007101c11181a8010394008d507005041c1c00d0b00034140568a2171b0081c203042072903030002080b800000e0035104491740032140420b0141041c01c0c0001035010b4560011901da409504629024400a20902507446010380f42d070b071040003981030f96000c1103000001e0411184159640d603102d40100c03224107014502a4061407034500004e01e80c0089000381d900469000b40540103e41b01c503030401009480c0904440d0003049000b03141001661142c0f4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 553220053 1250 553218803 553218817
    0x60f021509030a11010209060301120c330216090908040302030a050706080a0c02060c0d150b0c07060507080703140f03070e09130b0f1e040c03020306060d0305040524 73
    0x100550760f586219900078481003c1c9204018540e0040c0030714181c5a6801007502c1c150703409840c201250600f11b0500c80c24010b19513000880208505544004100941c1c042034500041000c0510440340702d030350200e903a01400c107650360b84c8221151043c05007110303a42003188220301401c51350b800c0c540c036600000d08100e483c03641260507a0081504010307241c2c208844640c0910b580d24100624204c48402079200c1c60002c000d4075034520000ba90000c1d04580b81e00c508407040000c004116099155100a0044d0b800284e44030098441c500001828a20400440342c0e916030140020b4108a9281d0b0240c510424003608000c400c1024070405203244803481c0994424081c5a58201c0d0044840341031100c03025002c0c0c00c25001c081d943c04d07040081924001d01c9500080c201c00450055900c5003059480016086c00e2100100351002c10711050103290b13244001035070b00803420344402e0f0f1201c00c100300380490854801400700760248804c010b549014194410700d03525040c1111031800b0300300126007041d84142 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 553221303 1250 553220053 553220071
    0x31e0615190201060f0807050904020d06020c06092a040f061a0a0e101b06020c0d0203040810060806070c031407061406090912070507050612041e0c060f0215 69
    0x4070603586200c0c2d0902030070000700166031401e4507150070246069281d400a003e0303580100f10b0040030a0841d160414130b0310b88142c000c001151200040311399a9180d6906656400c03051152000900520804c08094850302503240340d044014011041440041c0000c16940000c03996125000100400040c1c0480d250001a42e152641c820200703401a201200180010317000d061514111440d0310741010b001401051140c4500008104030314003407000c3d10688082032014015600350030545078000000d08143d403100d200765000c044000c04400200d923864401d01c403140e1701c26030216540138007580d2901c40e014003904e00f40003003201d80503000703040741d108503012105c1c0c030f9030b030300042030144240d5502c0c98020384200c40300411810208002551020400d05035500f4500c00520701080100400010004050151034a61644030b1201070369400039040310161142540c2c42490400703200c01003441c40315a07500c0070494801a0400e072040340c00c2d10350120420154410700055240001201444600c200920 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 553222553 1250 553221303 553221337
    0xd0c0b1302060708130906030f02010c111309210f0c03120501060905040c0c080f0f1908040c080a0201020a030809031215010e010219020402030402060d020a020a060c05031e0615 78
    0x9120000b58861a86c001c40d0b11519100b0148001250780e142d0ba105e040c0c0902e080b46168030281032107170014001e0107460398003010458007031801207810340003a000395000c0c0c002100c440b40da61000040f00a03200d14200300180e501210140010300400d48200f85600900d0990801c0c100c0070320300c2c0200c3d003003030704980c0104480300c1c4100154a0b1600903510803038410300c0c06c1c82008020b6502c00480c2e025260024800c11800309001d0911003c043c01c2e00d64010001002e05e007000c86154016182d81000d40301039030310031038820011542e488002059490942c1c1a030040608007040d44003201c21b882c2c05041d860060008020440c0c10b140301c161000d0141c0b200c220210080720305100050088058108128190340180300e0b9001000804090540c2d0507406940150b900d60301d5200103801c5200d281d1000610780e10200f0320000c807e60024140180901c1450300300720a507890760040e5400c2c081100c400c402c40070344d0301d035a50b941c1c00c0c445030161f0402805000342203140d03807120100555030010f544c0c00064400c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 553223803 1250 553222553 553222567
    0x3050123060d080a1116030b0702010c0801051c020301110919030b0a021b1b0112151823040c0608040b06040f0e0a030c0605060f06122206050703050105030d0c0b1302060708 76
    0x40072311440d000742d0540000c00070310141960140101c03405100311481008050f40c603060340e082c400d954900e07c9038010003c00082c0d01c000e40c0c8007415007041801da40a582070342c0f0290007280c01492000c0540f03400180040d601e42e1244d0350100a940040e20036050844244001b21383c0324010812400c0742c40755908501c6500e1960400100207403106080b81c40000d08043c00c1501846c00040c0d0305055640c00740b601a4422003451f03128014083d03228820400e0134075104d0011b218044652441d004500c40c20000c54620b80d24081102c4224040c5d501800c10f400d600007080041c41c00381c0c0b1454025050240100b00c20113482c020b6401c2c4840c811082c0c0c0850015815281000424403a9a50040c02250a81d5034001d154010a50364003071882c030300c0903003d105804215040c11010060030301100e9646041c0084d03e6034641900641001c3d12008086424500041518500811044445502951086005052500d402c0071026000e009410503102e546050400b41e1249001006c11034041d002c00c50782c1e115 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 553225053 1250 553223803 553223813
    0x15040906020f09031b180603031b030a11030301031a04060605040e2401082e060f06030f0506060d09030509061b060c03040b0711011503050123060d080a111603 70
    0x3107555600c28011500c60011790b03590750074080341d40307468074600400c0a0b500d201c0480e02c1c5106a0352a5030803000343c0f441e41007010700c00000034250002d2030368450106c9100d055a880c3d6a000030301004214013402c1d8401405041000ca2580d4494092031021800c1c5554402140403941d0074010140a50001920300c0910520301003255084c0060001d4001650325043c0c1280d00c0300b5040001e2401d41c40903080c9100005d0344000001081001c03031100b001070503990080040c41c0804d03442000c0100f402c2060b2503000641910401e4854000a030100b450090200c0900700184000c070400c9051160500028800d521618041c2400c4000315015103445410207900c145003107801400804902c00c00c100f080000b0759840700e11390300300030702d41094002c0c0d00002d29501e000d0301005100e580100501b4100005009054010b04110b0580700030103c11131001564500114200321000ca07046080d48000400041000d4014400f501d0300380307403203001004054156030500c1d0b4031460403000f00e41e031500240103000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 553226303 1250 553225053 553225063
    0x3140c0d0c02130507020c040b090f06090c2101050103050f1003030e0307080a08070b010503030712181212122d020f0d02070b0112030c1211030c012a050315040906020f0903 76
    0xd00848400d1524a00411850b05d10343e2f005000354001d07030780e030070100b03a29031025410394902200c8100c9201a1013200422600c030b8110910645000034101004200140540b42c0e1443c0212071031000d00070310b1070440d101035444d80303a1000d18a4141c4511140003030010f41c140078a00d115849608041d60f940890709020f1604101030704070301e100350410400d90f00003c0050740c2401c648802800d040010b50f98402c0242640189584044440781c80b02408404100c8000d80085407808903481d20443c100245081d0303011240030f03452091034503245408102c402045840d00450480103190301620b800c1e4000c000f051981c00500d212208583c000c1240c004000e140801703039000d040c08540c2244204001e490050a08403000c0001c1e001c641e41c2695040843e108998080400003010112542d9841c02c94400c2d009058010804d60345180c0f0040c6507031402030300c0035030a0a002d5544e851500b5621041100240c000c900b100180c4d0007603680383c15100159071400a000a02031071042940c48641e40800d2500b04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 553227553 1250 553226303 553226321
    0x322210312060909110a180e0a0b010b0a1701050a05040905010e0a05070312051e090a0e100e060927010e0a0b0402130905030f0706180f03140c0d0c02130507020c04 72
    0x6c5e421401091040d9104101209a10126588040749100d0003044080c181042c507180a407214541c40001b060300030610300101900180ca5036144100400d85050003d074440038001d1a0f804500624204401e25042d00701e0800749002da0000140b5842d0600901c0c500300c01c0040403583d9811403242041032040001e4060004501c5041003458840b1043e0603407009484120100040000802c100768546c8607203001d040501b81102c00d02015003401d0b4805608038900d841100d0102085c1c030006042030031314140150042c52000200c111038540906880f681268020090312030b9942e0b001d0080800c2070800c40902414024000c07071035141420300510503529440840740211300e0400c08460001400003044401e41c8045245003a00d440346441d00300050149240694006084414000c060040e620f220a460903c207880d0a080c0310f442c2c00c00380714680984a030401040d0443c0740703140d44040c0984007689003a840142009a0706c0c644d8101001115003e580110050344825603c101c1c074100707441141c0710 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 553228803 1250 553227553 553227559
    0x10e0f010506030c0a030f09030519030b0906040e0f060f16022d0709050a0b010e090408191101090320030c0309100908030408032221031206090911 65
    0x10940c10000801d0b50b51202610404103210009100c1d082c0c07a1195202da40c0d441c0561000740b0154981e03090060007034000b1840001ca400c1c65062030404a4003c2c40740d03001d14403028010000b075035a07100800000b0005c82291082038012100c3c0500066028040c1910428001c4001140c41c2400741407100002404e414540642d441916480710031708004070300769060340c680140c0680359a038101d085414032109c0d074450701089040078144806010315803c4409500804e9070780c0312003021183d040007100001a81c0160441c1d4080022001d0b0808001d0003101200990420b04001c1c41d62205840c00c4684062090300040d10f501c0c80a40c003c1209084484051038040c004c42c102181e04625507240c1c802e82810911520b40540b404d81814000c0b0120b90080080d013045e070740c880f41e03a820000d0712035005201d045002c003020900c020100c3ca01550800650f0951207520040d482690702210300301c00700d008d040d82400100b00e08401d5a030302501440014008607000803685035100d1501c0981c101181c50701c648 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 553230053 1250 553228803 553228831
    0x30807020d0f02032b0c050c0d02030a090b090402070b0711010b091612090203011b03050106051804090f050105090d020c03030406050a080a11030703090b060d030801090b040f0e06010e 81
    0x11941d40c1c0081601d2602e42084400d01c400d08203e80c94101d62900026540b40c130904040f0105c80c6c564000c1c0203000860071781026648045950b0a0482c6c03248075024032080400e04552040c01880c503d03102801d4200e1016000600d41401ca0b214400c00400485424000564120b20503485103030a00030700e0400f050540d4500700e43d0a0a0b00c4c00600007214142c00340400600050050b600c0350207402965103030f90098002c0200f51041031080001103520042c03000881c0c01c0200001d070f020300c10003ca900c40d0740001c02d000300d1850300000300009810081c4056070080308100c55100030030b100f03204440c003640b0024000e00100ca8101e10290601c4c9081c2201c40c0b0a0b00140010484240c00008640002c0e00e20701d0000c40c2942d135036044500603c00c0d403407120500100441000719a80d00340c1d100004450081c0300e805011369482040060400041600400195138180100206081500f0202241500a1000c81c04003090550030f070031580300340412512580410010045d520304412081d8200b088401541 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 553231303 1250 553230053 553230077
    0x41109010b0f0c010908070605100b07020a1205031e1c09020901090e0a150506090a1802060a030608030304110f060c0712020619030501090c020d0e040506030a0f030807020d 76
    0x500c0c5002e280901400d0000c009940441610700798003981086900001071520f8103001d040c07140051504441106000101e03650103c1d01031490001d0b182e1b240c0d402016801c4450400030308071951100702c0c0b41200d0510051180411b00307110101181c02400d05400340e161505072510f00c41d050790040c041e245280074601340451016855103444907041d960004004500c0d001200e49640c0351542a680c05032085074036103404013006245400c4507000b500120f41d20429511641404401c5a01030007400d00c518036040503003801070a255014001c441001e090008460b035880e24800e046510440d011105210401110a02460310390b1b00030a24003407c1d1078450030407210754442960b403000343c010040356400c00c0b507802c011592004c08541d9512a0000351708040f00302040b02038080c2c01c0070701803910514100466021042d01c00244031002000c19500d40b940703040032505000c02000044c5c2416054020312101d04040303010b80030091001d610942d10200e0754542840000c0c14145000f40040401995110340c5e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 553232553 1250 553231303 553231319
    0x3020a0909020903071d01140f091b19020303010504061d040314090a09050f0a0509190615030b04200105040533070c3302030c06040b04110901 63
    0x40d0140da150980043e80c8151910002c0c0c904107107039208010461920710051803a0328040c004604a0b00c407402684910180786040044207000c2c004503070f8001d0f14140001340d1000310403980c140c10f4048107100d0b510780907007030100320381c1e043d51070032001c02603480000104410f0505106480050440b50106d01a0103180d4808901341c52000c0c1021701005110030390020801140000c0701d0103800000c6c00d0030151980e810090002c1c00c0200d0304003001202c0c0c04002030081300140180791040260300090a070340030040071030700704d410301000013130380d00301d40d603800c3c03d0f02c4942600f03085400344d13005c0c240f001c07600d1400c1d19202030b000c0301100540220324100a500c0038103903004000d43c0c06541d401c8565103c0000702c1d80c1d5070403c040d18945021190584189100406031000004040e498010249074100907101e41940c41420020203901030100102d286200c810340090075010000702d01441904e02c1c140d050418a40f501c0d03010350341660145407003024001008140300800140c21b4082d28100742a42c0741200d2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 553233803 1250 553232553 553232567
    0x30403020123070f0201030c08101a09090f1b0a02060604090f0c090b0325030206070c170127050c0603060d0f11040b09040503030103021e121c03020a 66
    0x1009041c0825895541d24200b0080440d0001025a01d11280c4680c980e040c00c0581c50035180c000d901003440d114004028903c0750005912074130b80403465040b100e103800d000c0c5103002101000300b0000c440600c459002580c03100b0b1054052504504203040340d0030080c0c00c1895102c40081601d070b01800410511701e0b16074000c21440d90041c802c030b80008400b5050b04000b8003115000740010302040c00c00002081400c0700e0b41c818210b900d0150101d801c01304a0200b02da40403a03100b4214610b4480c20041040145003080c01000b1280c0700e02141da114a80d20075075484032002c00a4005103503511003000c1e2012192150f041d10502c0007298455102d080300d0784036583c582241468140c0140c10000c0003a2485c0c48010707070591155800700703460140c06031504191075451010021644030340d041c000208440c2c0b50100c005405190408089c1d4503603440c5174200402c60002c40d0380c125005550011400c0f5644da581c1c070b03080346202c00b000038040b45d03240310340c08900b003400c001000402c0c9031050004045c5a030784001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 553235053 1250 553233803 553233809
    0x90216170403060f2a121505030115090612110904030c05030d060501140f16080912011a030111030f060a031e021201050c0a050c01020706020406051801030c14130819051e0304 77
    0x1400007007c5503140d0352589014030301e4014a4140d8202403008082a400745050740840707a0b100c10420903151600104056060345070006480c1e104014100b44991800d01c60303440c2c002d4441c0c240000c0c05c1d04195212421078000840915440303941c1c04c002c028a5030850601038040d5021410b4515011a61420007100e00841c42880c0104202e407004d10100039500049462800c0c0040044203c415281e900314042c1a0008246281c9410308802e503085080501620070501e1002c0c403102d04580c3d50505807812284001c2402d42d119900100000200d800740040c17008a4045050810708000c1d140140450b41e408209044002c2c1c2c9494200025501e104040e1440940245400da40d105c105400c02406030140410141c011840002e00180160304000185444c9500812843c1d55002c0340c0c00541c200c44241140c807003c11200b4610007081b0527002c0040018100d480348020186440741c0c1c03076500d8044089030301d200c040304c000b5160b014084108040d110044c00d9001d03407003640404800c0c254490143d44 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 553236303 1250 553235053 553235087
    0x380307020d141605160906060908030903031903060b030c0403050c10020d05091305011e0605090901030311030c0a050d030e010615050703200d09090216170403060f2a 73
    0x103c02404004062110b40907801c240d150f041240c0ba1688501002000c00d403040700c1c041400d40700700044039000803054803d04d40c402005142021583c030402c0000c001c2c20200c8500f0995140300124a80c180c0902840c051806501e28540f1a0700b0f51410618142c98500f07090312070070900344100f00ca2680028141041c2000349889500c0d850480046403002c0e2900b40080400c43c2007000125804648208445410b0b070007446202039036603100401d84807072086076040d54006a85070018170120380500d03c0540720710a52030840b0300d4450381d810480d0520510348000c0b40c0136000850740e4086954540202c1c4010740b10b810003080020301d089104407020140700300d840107000001c101d090501d40100308410861442400e07540744a118400301944841802c2c00707034008989401c1c000304500a59100362120700d00d090403022031102003901c846620984661151001000401022001515501401600c2c00480c030001c40d4844a03a8100c8020b4102400d2100803100303c2c040482d00c25030b010705c1d04030850100f4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 553237410 1107 553236303 553236337
    0x516050c060703090201120f06050406090b060412030207120b04030f08070f0e0613141521060406050a08030c070519380307020d14 58
    0x41000410850780200002019540280e00042d005801410540040040d00b80143c058900e103550608000d82c81c1c000803c1a0b00b01401010081d00d200c00382070040c400804080382d400d010358030914074001c0d243e41c003d006260080c8655005041110044501d0054500300070542c00400d071f80803800985501c0b081418203104d44641c501074645640c4103500d18110810450300b0500c0c1001d01c99104400700f00302107000020606440090003100d101000c0b88140710201700b190305c1004603e15110200b08440b44200c2c141d200c600d40540000014000725450710303004a0003c01e601c0d00455044400c042c40407401600c00005403408681040c03c4030f1216407a00c05000c0f80740c5070b0054041802c980d281c4244150000d903a40c070703181460b540d001103070f590300c01d80d100071100d110020818a0081000040c440601e5043c4a601c2013040f09017058400031300301104115040c8500384142c03581e2002 = true := by decide +kernel

theorem cover : BRFrame.Cov 553057553 553237410 := by
  have h0 := BRFrame.cov_init 553057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 553057553 ≤ n) (h2 : n < 553237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
