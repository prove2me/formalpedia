-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3042
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:29:50.753835+00:00
-- url     : https://prove2.me/submissions/0568e978-fc2e-441f-81c9-cc7f15b2ff74

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 546942446 ≤ n < 547122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 546943696 1250 546942446 546942481
    0x211d0f010213030f08040b0a0f1e02030a0c020a120b011a0717070303150b090103060609030209070e060c0714120a0b0109021308010905010b04060803030f01030f030e1306030605 78
    0x800618070002d103182c8680344221a26402560340840401006c58204030f004000d01d41a00300e80c0302d0b04280140c444c1c00404203040300e842e960071200f010326441182b41d40407044446140141c0343c070003810000c0c0c0c00015110741e40d41c0d00400b50010105c00200c10801f124140c0c5040780c5489220546660441c008091030741701d20440240040c8413035200c2c09031901040041c1c08031902034940000c800b101d0049010310304405030461300703004a0120b842155176a25021f802c018011900c0c3c00844180b443d804940a050701038005428440d80404020807620703000291055040098211420a41e0725281c0d44070200b248084a40110002d0b00c5030544490000303100b00390258001e1107500380d0381c1380c041d24a000303401100c0c1d030400c4502200c800141c100c2d02405050040360250000096003003500f410441181c00382c1c1c0c46800e098209008100380320100c108098116604081804115480c0e46011508440400011507000400000780c14441e00d00703602880540f441003070104101d44905041e1715014080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 546944946 1250 546943696 546943717
    0x50c03030f0403030f0e010608100618050a140114130204062003090301060b0405090106090f090902010309081b0f06060607030309050a050a050f1002030115211d0f0102 74
    0x82000c0703802019003480e0240d110b8020310340054003040550149054814080820304075a448080c01e00101d00103100e0701c2100200c041c020880c040c5000003030900d01c88007103504402150fa43d00011410400c80e00311000a90522001544039a119401c403241003900c102d0050044d2080d17004000308018034401c40e400c6e200035445444182002158609001401c0e514200701400184402c10b8140c40034055070028060b400f1100b034482c0d0602e41840100130050b8071405c1000840c1034100640131450304504185e400050b0b0201e004585d500069001d80861103000b89001e00014000f551021170342c400060703a882001c203940002038030742e0b500c90341d501c0f05880f05a07014008011035070009000f0f5110913034441c400c13016501c440005445903400e1810f402c50648040c0c11101e07403900d4500b414042d8100c0800780305401c5040d0f5043c50000070322140f040f101d031800e0060900802c0b000000c106008115076443c400c0a00c0440c0e0460200404c07000340d48100c08003031040308140c045010041c020b6440b51000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 546946196 1250 546944946 546944953
    0x6030506030a320118050f0726010204030818100906020309061e04030f02190b0405121009031d0105030103020d1b03140304150804031d04110d0b03010606050c 70
    0x40c01d006100307a40f816040b06000f4101c9441c2010b95650081c0074002040c696140c2116202040f8107002d8104845030300424030340e4000c480c080c000050340440c003221300b0500ca2135154076400200c0c07550340284202d0700302406038100031510405882d0720300d0b401651200c0c10b80e80d91071481132813201580c14140a000380c10140c0c0007130080140a0901401810010386c40302020000e1034a6080d120b000c40d8050f410a0350301c81703210404d00081d42420106944910202d600f03410015140c441401414001d1740a145e129000c2483c40840220040100c40385c0e40f242d2000400c41031110780340142c40e0b14990382c4400d80d81d500c0d01014401d598010401c1d40d0403a6000b500390550304c141641d03284080c1d0322160400040c2407104201001041041c5403982880060b04011a0b46a0404044036040c0d007041a40c4020800e40d0010070000a03030200140728040f141103170121041481f1400203015048a10000520f4800800c2c103c50300422500510100d0b081500200031003501c40e4000c65141c0716010b058605540b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 546947446 1250 546946196 546946223
    0x606010315050405011401091d01230319020907030b0901030f0204060b03010b030906010e0115030911060c0109110f031e01091703061302090d0209040507170706030506030a 76
    0x5009811070340340d103142018680c0266480304002002c980d802c0c0c002000d010301c00c0030035580550b040034920003d0582c4e40510070301031041c0403840804030300c1400f030802c220414040e41864402c00c5c0c3e40b0055440c000900380ea42e220846620904c02c51380700b12003a4401c030427010220303800a0281c860100c06510252980b401c030381c215250180061168981282c00079500c5000044070708000300514040d00d04c1c0b01e942075070780c10f181420034a4540d040c3c02a12501802c080108181165080c003080603098606000c0b4404030141000190014140e03503664002d00001002882a10107600078a0018801e01c01c0308680d01d02030041c0500d48a00400003900356000511180b10040038111103066903113034100120307103c0c200d42d44401030520061f0420903040030100c288080f501d0040d02c0600388038001041103080500c0c0c07078009030703440010030800b0b8050161100800d041c03010602c56207018214240b01c1c000400c8905008030303910401d500c98070001034940f002080c42480c02048031005250003129000340c08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 546948696 1250 546947446 546947449
    0x212011202010905041d060705130519031205030a0c02070e0a180804090c0915080105061b031306020c03010c1d1203160201110d050316020f2e09020303160807050f070303120e0606 79
    0x44cc984418514001c42d141c1c0700000041d02c4c9010090008055a5201c0e164100007040e5030a0342c01040d840c0043d5003109605014224408090340d0303100000000200d1041c0c00f03001000081c0c4190880904500f000040128101c10030341c0000c00e6581490355083c3da0296103848050501c1458400c04c0b0024010400400a500e400700c041c0c008104030f46031099603002d800524520b1b40c0d01c00d035060710402500c40703802c004458051103146840141a00203000012130340300020561013186622290103000034403075007041d0f1903210307450b4117181a0030b007140c8d501c03440c00420070095500d0f120101d0004070801c0c40e40220200100d01424101000c5d04c5150654803011507400054010805110861140c191001c00c940000c12221940d103510806102d850307440d04600340301c011121021315500b1401d03c030040006803800012100000c8072000300031420642423514203568410750801501d0303480b4004180320030304004561002100c0c86900c0700c149140381c418217881604c40c1e508400c41d00342c0041c1d0015206 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 546949946 1250 546948696 546948709
    0xa020609100504210c0602010203071e0e03012c0a05030a05030a0b060d0c0f030b0f06030c1e0301060e010e010f080705040f030b10090212011202010905041d0607051305 74
    0x8120540c20058140364813001030203581c00a039044021a04114400301c0306110113002c400002e451507100951540c545880040e1040280110880e118469081c00c040214813903d00d012019200a000b13104c0700d5040130000003200d80181d8666403020521b60050045640011a606807591080203142410343c0c898080e1450341009010802d0241c035000207414a690300d00050201c031080040000c2c01007441d090080c406000e0750304d40018503203003c01d4404242d03655805141c0c4100c0c00ca4602d039032691004201507907402041c022140400c4000080451150500083c5060390b26940d81d2102102e03032800110355807040c500b24136010441168051410901c50b10301c155002e94141005451700d692510354043c0758941d64020340740218041c09000c180d10390001c221008005044096060226215580e00350120621640b4080a4004500707411640603080d42c8004040c01002000104243c0d0000b15101d2048810010076000e19000590800c0c059810307941100361240c01c0a034620301780420b0018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 546951196 1250 546949946 546949969
    0x1002060f040230010c08130206030a020408061e09030313060f090b090114060603060619020109050d120c031a010507080c070303022508120a030e010c0e0f030a020609 73
    0x200b0114400680c0010f03040da0070700100d4007094070381e9101602c0110f81482d084919402602c003c0200c04021700070700302521003a039209983c0444000b0b44c2c0c0d403291070340c1b040203100e990701181050180320108030801c0224410818005a109004640c0d0740c3e070030b069642c40c1c2c4011150014510000204031003c14115889a0141e0882d10400200740a80313032141c940c28003080301c0242c00d5031346621511000902c0003036a150003c1e4140c440f181141481d00005040f8050350031444014405040c0c1c0e1500a807017500020b5030960094203540304280010402081800f500541c800c80604124011101c24440e1056007a001500541d10070460150340c01110290322801040d070308964280b20100c400042406030100840c400d8004002c206903a00c40e0707095620700200c0201d4038141085040204400c080f8070030008000c000b48c580c2d80c9040000080d00107181d4400d518180307601e41441868000d400400d8220850000c481c201d6019850804050ba900741401c002908001e09100020a50400807030046 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 546952446 1250 546951196 546951199
    0x10090605090c09010203131403070828020109030b0a050f151e010509040509010e0f0604050c010f12050906010f05120319090b070f0b0705250302120408010603050c1002060f0402 78
    0x303207007455602c001c207d00c1c40d90782c12201c4002c0c0000b41d11500d91030704105d200020a060405007091655180001c070003045403100000742c0c021510990001c580c81069810040c5074486102c0d81c43d03041c90216580140000c4400d9035421400402003800d08181200b5044003000007800f0081d5152401c2202400200701504c840c148942400003031942c0c0d5650081920401c00200001fa410300488866480c0c40310340c1c022100f50740c22403000c1c08003245010400803a2034a080c200369a4900c0d9603c012501c51288040c6803000c0c84c03a10040c003e02c07800c0450304504036020342c0d0020165540340c02c1040714034106414102001e50040250401e941c2001b200c0011180442c14a10700c071554413811400940d10a40c8105c0e192180c9400100400401c642c0a68002c01d26181150414403804000710000304100000c5282c5007461041d503003054800c0028050b01c4840381d000c15111a80c600241d406040540811141c0380101c0050100c01e051520b42c4a500e0100c03640180480c0d15501000d4416a1024000340d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 546953696 1250 546952446 546952453
    0xc091401140d09031d040b210c1206090f06070207090b0d050d0207030308070c0f030503090109081b070914010b03130f03260601080106120f0501030b10090605090c090102 75
    0x2d0b80514814442e0010303150080c0c580202c005400c00024142c644107051082c0b2035480c029522449441d59030b00940070511101100d10941d1101c030106242c8030020b01c0700d56016102c02541e00240e88081107480c002d4189400310f41c1c03228500d0384002d4803500111685001a88841742c208804a0700343c005003510a4090103503414000700d503e074281044070410344000075a0002100b0403c0551080383c80b0342c0300402d440d0007180800c080ea1810030030021510702030204103010001ca1640c00003940300f025400c1c0d20012580d0b07601e40c8104100300e4200744200c01107107800780f280001040c04150044030107184000200509903824000c200a294001802c44088015114100e000044031120140203450081d00e5a005840c6030304003500305080d0b0341050056036143d100901000e130f40c00c500054156603450070161040000b8203490f600620781c041c900000a0705000c0004240515242a1406145100e1621240c1134403824000150b4140d41304a83d0444c08100025041a000c2c0d0090405010144140c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 546954946 1250 546953696 546953707
    0x604090c08060c03011514070b151e030c0306040b0f13050303071806030b0a060f0324052e0f050c0d080106091a09060d27060c09140114 60
    0x7400e1400700200d510003070107103001005105603e070180c044601e000380740c6407054003203031041c1201400b4000e00d4401004140c800d40071452075072550070000099000a80700c21100c1d4804940c0035020020300e40068081d0040d50614081800c01190300c0c0d1040d0740000c0307a0307541c544550101045001004203e490a0940f180e95031000410600045000c1c0c0007513601d80e041000390080811000c10b26070b100b1300c1490319014080c02d003a03d80e04c1060307040f2035036400d20550346515603c0540180c00d10404401d681013181920703001591500780110207840741510000e2000507412008400c0301280259003c1170760110703100104140c420501f80700652042c2c900355050845101004d49851071f0a40e5050102d0700c2140144185030b803001d02c01c001001499888541503041004003410b40c0b1600388a0b80c043c040028540701050b4154202c020b240002180c51004010480000d5101c0d00c0e0780e6004498141c00c00e0500d06c0380902c6814250140c0700c02c0c1940d02d1580034118015241d1501902160f00311013400e000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 546956196 1250 546954946 546954959
    0x80a020a0e0c1c0b030114040f060b0310020c01020c1204050913061401030501051905071d1504080607030609060f09021b160602010e0102040608180106030203120909070e090604090c 80
    0x143c090001c02084000c01c4541c1c4007820142955041c8850040e100028000c10000caa641040f04076030542220300007071114001d1011038203040164402880c03240c00058405040c0d081540102a801c000ca41035484081091150782e03040c0c41140314296100c0f400c030b23022602c0840300a58140040e8271840d00002c0000b1660b2443c4681c0d45c0c240d0045c0e403c0c2c0d650704100100d0f40680c800d08190a00e0003a800c0200d4601040054052186060414009501107440f43c00984540c1021020b0140e24080241c45981e1001210b59404044441600203400d01c0781c0090074801e40d00501040c0c600100b502d21825003030212200081d000040512a21806161210030524003800968a03456042420990301b904291019080d1200824288401e80c8100000c01107254418003842d000f0104801081c0c856080780c5085001d8806600040d42c540624144420340e2922400144480f8030b040e1500c02e881d6603a400c00342d508140e000c1d0801c2e0402119000640149005e0740820482482600004c8403943c4481 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 546957446 1250 546956196 546956227
    0x20114040c05010314240105070203070b0c0f1203070e060d06060906170124020a06050a0209040b090f19140c0306010e1c24020a0f0801080a020a0e0c 66
    0xc60540e00030911080c00e00c070b5540c2c10300071011000c01c0485c8020b05800d042106c840c440c02d003112a4030184117240d0000629a110700111b81c41550000c0850b05e525403542d013480c03116404008024500d104140d100048400081038120b80034681c11441400c4d66516030040c2c6a000c00c0d01d05c0964002c20401458a510300103202c0d85000d01026070300c08040b141410300282c0018602168402c0c40c5050b04010014007070400f112211102c3d5a007107807200710341506c1041c3e241418440c001007045007410704003c030304c7d00c0c80d50113000408400c5a05018886524003480f092900903241090480c2c0e0f00c8000410303042801800c041f01941007000050501038001400960441c25600c0d140504030000a200d05907910200703400c84070750304030b854616030340ca041c490360721400c0c000c1f800602d010400300340034016000c54041000e2150b607031032041d5514031011030018042c05000e05184045100c5000103c0c2c0c401c07001502c800b8065025002c3c007402801c103070b808281c180c00101485400402009005050040742 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 546958696 1250 546957446 546957451
    0x1e0c030d0902040605060403080d0902010c02090a1515120903110a03170a05010b040611030405041112070f2c0a06090e130803041b050616150b0619020114 68
    0x303400090400003610410060711042e0703214501c11a400d020034400704908604541f40807544c0c910000c0c080c000d07407006903840442070300301039030040245080103150319158021040046009064040d410744684e9100011184094214006070603005030100290030350744902c6800d4001c1c2840c0d206c2c1210852030a1400e02c008404800150041141c01080038101083c9a00315410b184140119814800c80f10854082c5224500c20071150034201c03c04c00d80c0610446000e0017002e4824094089a0304517107495600201e60941c04802080c0011a214410000544080c003da50b03441d43c0c030b000295a5040b60007406d6414040110224842111607540c4862a0020300203030321080000e604d80110013440c2d1000903c01d000c142c20b000d04610000f041102160740c072a43c07100a44e44603014020101c850300c0c0d040d400c219040a000145907a641d240e9407289100b40303110f509144c0078800498030344003e503039200f4182e07a0461028405203c402c2401d0b00d03151540c555074400042e0700c2244100210150009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 546959946 1250 546958696 546958717
    0x120f090f080114060406140607080c0123061f0f050c07060e120c01200c03060408090a060903020a270513020411071104050705090301140f0105030609031e0c03 70
    0x182c6000d4003140311040020f41d03020b141100c0c20040180307082c1ca50300e0720802d41b607030f0300b44140000180b44041000c0d81055443d145c2d0140001c0202041b40720b00940035151000f058002c0703104010001e03c25280202450030054a80f00600e200d950381108251086800a10b00c403080c44400d0046515011080125000030035591756020005200d07507083c032065014203680205180c21400c1e1404039641c001340c49201a0412101c1c17010090b04400c072050801202d61660750741400f4810a000c1885a403d015020083c8102c8444e81d14584e500001d5980c1c6410340300080d001402c200c010031070809054100240170b1028249111000c01c000d0b000e00440f0340407252021100d030081d000e80c0941c100761044200c407141d88200e00b45400042c5d100c3e6808203003105480746c41151210001002e6900c124141c4003d500050028401520741f03810b2910048400c581c0865070703c2110000144515001540a00445900c03000d5460032a41e9510783d00101d0074511401c0c0a5442040f400240c1034041005201807800b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 546961196 1250 546959946 546959951
    0x1c031a10050c0a020d0b330603060f0409060504030914010c0b1e16140424090801020f0403120201020f030f04030e1503071107060e010302090a12121209120f090f0801 73
    0x101f103844c808402d62042041c100c500610790010444050b124800610500202c6443e03803070343c1e070754000188910700300d40104e5080340c103020340101008074540055008034469181c0120140d00c940000001d844d0110b44d850004001031413200100d071754090740b60707009210a0748004900c0000c0c80d01c1e8444807016036000c02810181701122940700da10402ca0340d000300c1e180d0400d40c5050310300321080341d00e0014a400b804010311481c0030740131103901400381072000f001c02c0d070700070741d2150301176444005960040d00c4259007082d03001c002d41120318418801c41c0c4000700e20710402410340e1208041141c607407030000c0c000c409001c0040080d1121f691000c0000d103442a40b41e0040d035407071410020082517400c40e000c0d2008207500c0341105100007508240003443d90202840c0040c0c40303104640c00948808240c1c1c4c400c8031921688040d200901000036864a10400035071100580084001081400c40b8507208000c0c00070382c050020905054071401080386002c0082c078040b00103076203e440006e41c002140d406800c290b175 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 546962446 1250 546961196 546961201
    0xf0905070b04090e03040303140c071e1805010e04031b02181503010c1b051c030638031905180d1b030f0207081c031a10050c0a020d0b 59
    0x8030f03400f030b14421403065000341d81840e02d180da000e0503100d081c28210404030400b00703010800030000c001d1480140380c5000c03150a00300310f0300242104082c00c1d000320360350018141c08004003101140251030496440f1040d001d0303240e68a0b2030032180d043c04080c407030821100300702c1c40c0c10260b506d078034813043c1e40b08a2285e149170604042c01d4003088040300c0c3c110207009905109480600e00e8000c1d008006601000854400002051900d1800c00035a0114800c070f0b001d080c460251140c0c2c3c181d00c100c044d40c1e40040002d541e211508076031503843c102da0114800b140810407840710103000390000b9541004841220480e014003c01854064410459000c042c003d411310140100708030800010b80c2c4c401450030128a407034103685000c80b9201201f60041c1c280104501c10040c3d89108100c0d28004010000540c1c8000d420441c1a181c480180c0f900d00c00003d08001c0303484d60304880c0d02640514200c00030001c4058682d03283d0113684942200003400100d010340c4200401580301d000c0c001e08032a00c04c108050b003a2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 546963696 1250 546962446 546962459
    0x120203070b0705100e010c12020901110a08030105010917030304150207050a0f060b042306122e060b0a0e0102010b0d082104051908090a030303020a140903030d0f0905070b04 76
    0x11024200082856810300b0607d40310590051020f4246480b100c00240e584c021140c0140c0e814590709604090754400c005100c4140b003200c2c000ba45c1a11000d03a103c29860381c1c0d810254100c1e5404014406980e0010000302e40000c1c080c0103201200003041c08050308143c4c403901ca0500f0300c0003017901581e003564000580020000a80b0402c6000041201c04200d03850707803024000560b860540b03000b5a002503041c0440d02e180c5c5c4981e4010209400801101d84a07501a4001603141100002d281088412030600700054181030042c001502e1848081906102408408070748440007607000b10b065550381d600001c115180c840700c0f810f5031802000550350b6030680e50004802c507421081400c08801c0880207200c00140003150031981804000d644410f440030310f003007a00303a520402400310341c060b600000002c1055011b030041c2c0809000d545414400a6900252400300d21a107080d40342d0607003080058240303c01031a4810f0503140301103000041e14402595802d80380000e1500901d030103404c007140c200400c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 546964946 1250 546963696 546963701
    0x412030905030d0903060209030f1207030207060309020f04420807030c290703031a09040c1802070204110301030b0117210c071511031201120203070b070510 69
    0x4081c190300070039001480318002841440540002071825400050100080e50200403210420402c041038440010351034a40301407070351003170394120003602903048001941d5000c2d2081e41656070b00a040c14410070142000c1000802c48000c1d40e1000702165500744207080303d00e4402a41130454441803540700419001d1840b1680c06c3c0764407106480d4005141800099554083c52048424000c8a02e00c0880302420200e050030031603c132114600c00200d0704c1024160b2503044008440440b220248524821405004420104490242040442d1001000318a8203032000640400014000505001703c90780020182d50b0304401030341103030002000520510032602610f0f401000001c45054260f128030710a03603140c0200440108040181c49880c000d64042c41084824650b02441610355458030b40c2901a0130303d100e013500d04006001d41b4402a1008800070413500b2142884007580315981c41d042505488c0404c1d1103080340c0500580000103801d0640001400c00b00d40303c0c00140c024101c420204408 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 546966196 1250 546964946 546964949
    0xf16050d0e040f0b03190c081504022d0108130b040c2d060c0309030b18010b060a200a020621071b02210316110910120201021204120309 60
    0x2056454020410915070b4001101055140c80e550380031110001810722604241f02c83e132128a0900842401031414401007034850300ca280300b1569003580c070f400034510204800f80010b8481c01c3c20600c500c1d41703520f9030151004c08c1e48004100c1d19602c0d00141640d80041106d41a0b800f110f403030070140010710450400300c08500d4210a14040504451030f200500750000e001d601c614428000780e10048010b042c17180e8141000741da080610420541400d4004144141c001410740c80e16510302681102249000011074a4030012559040321340400a1007417940715010580048140c0b00d032000110051300c802028004034a407002030520741100101c0c2c02d81802030700402a50411800d4040d0348540d02260303103164007498040e64954071403124200094503528101e281e401e039510020910912500f8010004000079100b030840c4a40c1e40c2074013080c807105000a48160780199031280092180c1e65480d03420400307884c014411220040c19000340a84140e00580048440d4454a40e401d014160018420710 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 546967446 1250 546966196 546966221
    0xa08030603210a0503190e160b090a0b031012030507030e01080408030a1d01150302030c0d080405122b021606092c010b030708130201050f16050d0e04 66
    0x3507019a18840ba42c4240706100046050007404404603000d003c121601860820038108208100569052195520380170900c0325501c440d02000f010501300502c00940340c41140282540d69840e050840292254000820101240c0040400010350078501400d00d41041d00944500d641c2e0405818014800148041d04605011500b001c0c0400a036482049903844007010000140b100900240b50885546800d0000800c0d03003440750140724030051101420031a48224101d90702c41204000b803007460f1802c80000741020710705010400c1a070600c0c403200c0003030440c10740981e08440e12000000c0c1510044416240042801c500d8019410f81c0402a10780e45040190300748126500e881c5e0001d0111b42e10380a4001c0500c075a820180703400458402410303440300d602e40c081865686a54000241e0f070000c0340c10000199003c00441e81302c0e0b01c000443c44000d070701a9a103904c0d041c00c0c40c40305102e40c1c3c003103015000c12038421116900460400e0040318a8146995100d40c0f82c00c03001001c00c420f8403007070b00a50 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 546968696 1250 546967446 546967483
    0xe090c091503070203030c160b040b1005190306020a0c0609060605122a180c0a030c0908070306050712020304060902130605011e0917061603020304151d0a08030603 72
    0x80003c6070000140d0307601008a4000715955a284003041d80d1100d403240004280c2e11180091008000c4036140040c803610a4070782c2c50010030303600c00030021049150113042020460381007080c800720b9026002805e01440b9401c2c2154140320542d5140d0840b13520180681e010780d600d00007441503103407502012025040080042840a942e504810f010f01400e006218816078203d80d0300307055488580c004800c103044102c110740d50780b90060310704030b060f070000540c800068903004008540900540ca404240d41e00302c40140b01180c11075952200800001d407566040c4400c10001e00504c1c00e01d4001103115070320031940420511140d1044c40f44001080000e500d44d47d003040705c14052a6809820000718000c03e407590032040700c1e40e00d0700f82c80010464000204c2c92040502140010074000780c0c1d140609600403071043c2c05801c0b504118102c3c0019107000300107034510140c0058a8a0540010f29041100e481241038507100079015442c200112808a900c41d1005c81000b0a51805001c001d02407500f900c00e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 546969946 1250 546968696 546968701
    0x6041e0e010b09310207021005040305060115092606060909150606070506040b041403040f0504020d0b030f01240605030105120114040c030203010c020f070b0702010e090c091503 78
    0x40d0b009a01800c02080c0c000d00036604880d8501c42c900440503224420300d02000d0202d551844000c01079030286005034060340c0b945400d401617521540488003180d03000740140070783d6420648241c03048000c1d14410300400c15801c0c408030344190307243e40030044902e0300c40f02d24869456030b2000d44d0400c071005011510038000030040080c0b10001141001d0140350000040070607035203000c0011200d00829001504600c00c001c01c010401c22100c0b0094051402003808a8890711200303105039032489140540c0e1b842c8200b2080411440c1880d4000d0030340c07002c046070040740a4141d00e011919045000c103030811242c1d100c46518080c180b254500300c808003081400c4464050600c00d01902a21041c8a003501645500d1012007039400c00398824000c00340380050040d150b0400e410714408550503804281e119510305040c1c184018000107240c6000d10516000d054218079003429010b00e03801158080c0e05000094180414030340d141c41a861003900c1001d20651030311591400d0100c440074101121840310810400d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 546971196 1250 546969946 546969959
    0x303020d030903020718090308091c082802030712020c0d140c0106080102091c0c03260d090c050d2a0302060705010e010c0e090105100e06041e0e01 65
    0xa012040c5009401c0204a100e000d1030103c1c64821940d01c064207030190345040a51408050f00030291890191b600c420403500c400c0271481c0c50302e180504441c2c6014034032605400c5c0354014448035911514404080d1180d520b00e840c016081c0e0301d54030081241c035500204001c0500c1c1c21414414001088020071400d110f03001131003a60311500c0420740703418083c001403118598440202141c1e1010703203040007031003003543d5242614040c5d00031040381803151190103075022003c00c014001140300c1da004119100d04610b5a2144004043d0300782000d40c0d007113904500c04020301002401031010480c504000240c4e0141801c1c201c40e00d1425401c00c1e0300c101c04031814417011030f045040c07842c6002e009507420119855174440e0b8040c2184294002500f00901140d0041400419488018900c0145009124007107500308200c580800300703080766038044501d20050100c0d00780341910052200b40ea0505601c1e4907080d00000d03540d80c01c2039000059518118a1411410405024a10041282040e0350129504045 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 546972446 1250 546971196 546971203
    0x3040f171603030f02010506012f0111131404050403021213030204050c09012003160203100504080d060b16030302070f0204020f04050312160201082a18010306030302 73
    0x11425110150104000d55014801d200150700038040101d0064125607900e0040c00c408481c0c030000c8055460700c000074034554064050131a4420004108440c4944440300271030917400c0d9144500710545d81c1e080101002c4000c0f00041c9803003800f011740c3c0640310b880c101e007503404208146003d40c0074600b030070184000039400143c082003109443c41003a4560802c1c40301c0c008460f2642d0300281d4000d04220030700c094450540000c00f088842a6603150300c004204204484262074519013080381d07413081090495944010041d20802c0e84000d00b91030201307004000c4030080e40d0061720207503000040083d107004090700341e20980008280e400f85e294102102038014844001c828032014043c103400081304800c00810700440c6807001d90091086455201c00481d525181e0003e01449001c0d215030000074941c1c0d01198161201c1c0701c0e45103400c0042000035401102c0a10014018580740518925000003071207225100800051044a500c4d80711003030088405a20100da003070382c50500d40703004814404030341d011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 546973696 1250 546972446 546972449
    0x10e060c0c0606101b0311060601021219090e15190501140714070608160806280e0c0a030b01180b0a090e0a020406030c05040f031104020d090f02040c0203040f 70
    0x469964115031021a0141d80070f90106820785e00751100b005002c0b081540003000110301d0941d5604890203a0707035041c01603035070b81c1400a5408941c0010710451400d14440e68542452401c1490419003181d40c0c1c62001401200581e003a10141c091680c401c811828048040c0d43c2e035580302e52404070341501d0400040c03d2031184500c03003500d00304005140400d1024007041d804800070403404407001d4a9899100414501c41900c041d0426000d091410b005188901d15103401507400410010b42c2e0146100c07802e0082e40c80405805c544444e409d0002203003140d45840e6445880c84410550361980c204100508960003183d0701d0341440001452845c08140b00c810000170755449903003ea644612804041d9000d0301c4c594440000a201c00081101e00c0c810303a0080c108491181d1070500c0502003142094581d4001c500409200010718901040843c0c207941e28411910f20144c001843d203e81280c850703042d0b0301c184c0d406488003102c4507411300450429202d0104070480328406107051500342034482c100c01c00f49 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 546974946 1250 546973696 546973699
    0x40e100b0d12052802060106020607050a121a0a0609050103050c07240b040908041e0b071b1d04020a090e0a0204020310080601080a05010b01030603110603071808010e060c0c0606 78
    0x402c0c1c0f450000b007941c25561307013681c603104594020010124002e6648070240100001400380c680850002d9016a003901c00d4461581c0310f00180c22003621100008185c44081d5600402031056180007a45420500f10040d01e141e594110006d4104030000d01038510150100300308010800c5201d0100d0300e03020070b000444130380c081c40c010000303030952261014142c01d00980ba03200e8a8600458200036401c0b0044c011262051703150103810108104c0e80c2408040f92042c00c00d01102041140d000441c6410303010380100101603000000c5446000e6200c010303400144161780c0c640001d041c4025071070918012030082a240d0014010038285440302521030849500086c00741d500840070521040032410300740041c001e11411204650782d00c81823543c0d03a40c0e01c0a0142c560b5484d1400105081d4400c0c011881680d40202020014072604001e2042c5644000d0801007008920b20045a0341925005c90704002c1c8648070011a01401c401c04a500301a40501088011042041082144000413546640c424070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 546976196 1250 546974946 546974957
    0x16020a1e060e030a0c0201110601030b0126010c0f230a2a11090106020c10082208040504110414060a140d0204030606360b040e100b0d12 60
    0x40c0c0c0c64044090701200403100300600000c1802052964070661020055000366603020701c0c24210b251241d200e050038000605003545100042c0040c00e0411701415a410b03c0c280804071b4401e01402c00d0b400c4802d80319019001440340b85c01c61143c9944100e01a299040030707111420700c107103001ca102c203861003282045010711810340f41f22800d0529001a15114644201342c402401c056850421400488904402e01c103110b82400070400520005080380310440141c02c006a0300210030043d5a1079000a009603c0e03051030b840341d01800c0002807281107106119210585d2210304103c00c01040c0ea6251032094a0450288020890081038644007101100e09441c182e03a00c1d252404119003c08203003071a12528a4001117800c0100502da005004690086070200200ba0310b9403010801803481200d150421894065801055882644000704000701182c00046202c03503880400c09440c4c80786800652500030003401415400b0602692102c0034003110400400007141c0e60390180480e003803c502d4200403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 546977446 1250 546976196 546976253
    0x2307021c0311210f01030309030809040f14040309150509060901050f0414040b120c041a1002100b010c08070b06040908270618040b03070b0c0616020a 66
    0x24041d0348400500308115000941c1c440500041c4220301e981c9546100e03103e1110400a9070b5141c898000f00d060369456690310f084c492443d103d00342070740c110f580290f134480c0d80d0b0b498038001400180301d00c2202200301420182280b0b081d08025202e020030f5803089800c030100b0110a004281d00000702d64500c48103c590700e07168003411004035500e005140142504000c00030700820900d04100e40541500801c1718140300040030319052000508040413050f40743d40c000103054100745080e40000f81045480c001071000061400300150003800e280c0030000c05038028104404881c10180100400350000b82080c080d41c2c20180d81e480e02510580c3d20140003e107a00010407071554403500304144c2190485881522000c01515108000903961007114804403100e00d104102d04000041e00c403082c0c076a00408660700c0c1d068090201801d810b0840c036a050150b8030b4007040f400350a0024041030a40d800c0100014070b40103001c00ca2010300384c4c070f002041d540503501c1000007a107012000307103a09440c100c80c403180c00b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 546978696 1250 546977446 546977503
    0xc0b060a0e01120506160c14030c3403081c0e0304090209040e010606050909090c0a06090e060307030b010b0d060b030a0b1e060f2203030509011b0b04080703140d230702 74
    0x5000311914200c036805004000106030380c0101ca144251180300442081041c5600b40360840000700b84001031068206218544010801c51003b000c20b001c4d1070b5003c0340700301706a1440360642d4402d0b00314004456001c00e00c1c5655007010b1085c60b0010160200821589080001c054294014018090310603040c0f2400a03039424001c1c04040c00010b80078110355451900c5a1000e801c066803400799103592102000000c00e54500050300d002200d4100c0311500c22a400d00c80e003007600d98401c42a2503a0651110000985510010300442c49007440718070001d100300d00f0508100c01c0680d5981e84d080e0001d001000c25050355a00300807125070040f9007241c1650307003c543e40c08410080c0c0241c035800c0c0180030140000281030300200240305100007640d03002e030076a210b011100056500d24802034848201e0400080c00125690018880c4c24002e051010307410715054505012a80f115201c15051612144000c4201d14a00141400800140101c50192038001c600944d03c1e11032010074150a07180c0306001062 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 546979946 1250 546978696 546978703
    0x1e0504020c2e05070c0b220210020304180f0606020f0c01030f1e0c0207090606050d050405030708040906050405060f030d0e0a0f06030e07060207060c0b060a0e01120506160c14 77
    0x102c1c1c0c0244001d00007460000c2c00074010100c5000265460007108000450900320389002800b0394400510060015000e03070203000fa481d0a03403007004207502c41004041017803d054542c0444003d54180042020015a03480d441951066402f181c00c0d03601c008000d240e10540814410341d0f440007882d0005140003420f400c00050070116109101e5810490140480300c0314540120ba40760301107808458070340b1f90329400103088a900b403062070002130040c03182c007902071529082a038225000d441201d003014a6a00c034600f10790f100341e00c20328904c0c0c0d480d0380400050400d8000c4e130394081c0d030890b883c082d500d19080c00700f91035046142880c0e041100d07864401345540e0b01e41207404040c0c03030b04040550705280c48202c00780040005220015081c0711781e4070300080262002554000781c41a503540c244050809a4070170104003005040240e03c240d800c200441c0c030045044a090090000390080049440141082c0c0c0c00c21201426503d124078815489440317158120707503602610745e07008490100d43c480c800b500908 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 546981196 1250 546979946 546980023
    0x3030a11150103030314060906010905090a020d150911090a0b030402150a0203130b09030a170415091809020306162f1204030510020705010e01061e0504020c 69
    0x20310401c0500100625030b05900c281907000d14605a14903e843c2c09040101c00300c41100e030b641c00201c890342c0902c1107042c64541c5640100301414054104248420003605540300c015070000308550a44081206a80741e0040c140210103060f0708901e0001d40300080360420400e401404890314000010900f1526000480c40d1a0707444602003684841031010000e4480e800840381c1145500414000b14031003881c4002c4031207007038009005000007049075407144074118581424041c0c440c03045c4000203070024035104162556174699030b0b1001c081d042c04025540910403c00c0345c071515150103030250050701c3c00151290401c690424101e80001d502004a038503144c0000c0b001a41002c1d88100310100c0348001d110001d4080e040b054400e82520b0b15110016030085120140c04c6e584002a0310b1540c03042507000b030410f180900008a8010b1450400600f92031440c0c0c0310251a80da0001e0040d00ca82e44141054003910b012102036250040c0500c60070342d84c20b180b21a40046100c4644501d00101140d01c4585 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 546982446 1250 546981196 546981223
    0x10091a0310020301050406080601050f0108040314130f0e10180207060f0203100e041e11040c081602030a0c1106120709180606210221061003060503030a11 68
    0xc40712480045020701a400c01e21445008034240400411800000700303c0f5416200081c1c00c8a1207095020011601180b020b031098081c01003007210061103000100040000c00010085019a10319207050b19100c80c00580c012512080d4480038030107a030703883e00001001c6880214280d6104492451007500034404c099004120510305040da03035013050181c01840c4920080a0070710f0140e565002c401c00241000c6030000c104440842c08032601030740c10010b01003854024500c1121119001002c5002c0b20303500000700000c119a141040140200750224103800c1d185e520245040c207803400801f43c9901c0c1c042600821a030b81d83c514107440c9407a02c5080c2d440ca01c0540103c03544900b01000003500703050650150b049420401c0c504608400c0d0710740144070803100240d803024218240300030200e000780c11041c002c284185c0c00b003201d1031004c200e110f44912540c030741030203a40c03d07400d03c4400c00048a4098482c0c001b850b060100401c2555004000d0b40e00205607400e04000000b480002d1505120111800e00b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 546983696 1250 546982446 546982453
    0x5010605030115050a09050f1605040b12040506070e0a0927081207030b10050a17070e13110a080a02070803010f0e0603010e061306061203170c0310091a03 68
    0x112030100144030f01074116881562000740300c40c1c8906018003138500465590841071183d50204021028003801e032611501a8645942010345407040d04a0580c011030b041204043c42a060000744882800a02d4000080e400d1050030842580007007070303400c52a481041c2a50f036844090141071101402400318400403944140d20040507850580720302d0f0010103054441e00c9030240001d01c0740f400b030f00c00c882c602ca03401010003d00c400305401c01c81c3d075907101e66a0032081008aa6080c0381e0006031401d064018119902d0b40b0506400722000d020000729030500541182c0d05040c0b81e442e80000800407121424000d00d41810503a4800b41c820010780b09031240200012000000000c1c241c1c542c1c1042c000341c508040081a4a4603a581014240c030250705260038590080004240314102c071015220744917100e09030104040350741d003102031164125100241c1c04541015944003d00c20750a4810f54081500600300c0e0a50500c1008050524910301a10300341039540c00003101c1038104886403a09035074008046 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 546984946 1250 546983696 546983711
    0x61918020c0d0206060312160219090b190e0403091203170a0b010e0f1903110108090a0302060c0702040603150b0a090c0212030c19050c0601090903020a030c050106050301 75
    0x20400258804803020300e8a008445500400700e2011643c2c60050342e00170020309a090704204ca000550707122006040c0081104d50040700140c079003c0b20780300a80c81024071070360841e10345913100007550318200a0038403541d048090b20102d8280b030400380302034942120203d802c503038651405403084200c0c0c0d0041940810b01c11140401c0540c8000044640b0024030001c40e1580c40340131011080d00c0241400300d012800004e452403079030034900308040f03035010002c140c00c1c003017401200800c3c40244550000d60302000420420b41c22960465100fa801ca007009000385219403540d1802511002c0150400003003400000750340084d5551600030101650b002090345070800040034010000b0003003000060300a171045035002449000c5403094510301a0640c015210351056040e0000031a40000d107440e580100500081e084401255140448200c403501c030581d0769400d04481c40c2c03401405a000c0b203040c0381400704000000350702090b90080254103042c540340c13102c0030b441c14a0150000d034004a40661801c1107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 546986196 1250 546984946 546984989
    0x308160b100311010c021011070504020a020307020a0e0402100f140d0506090c1306050f0706090503120a0c0e040b0f09091510050303030705160606030c0314150619 72
    0x16082181c3c400d5510806550694006450300c192011000e584820810981c440840c00b5485602c4422420305c107450350580c507540001c003280c001201000041c1c1c030204600c1c0131410710340034041c0600004600c0320030520b0b10354002203015441d1000c4a00b00500001e0540c00980603444400800105036400c40e02c4004824681e401810300321241c41c8604103400115004032035071030803905101504d0041058003420701c1c0c41601ea035440140b0490289108104c480085055881100346072449030020303655800142b14a00b03d15000500754000c1145448200880d5540142c800b09409905803070114080c0840e900180508074064071359900204a8001c22180e40008560302c82a440d0f841100000340d110788412400102d91b43c022560140d1040012411042c05030000c0c1c000f06002090014129900350b845000b03498050b4030071140e404c08440180104040700310011140c0390700c00300419001f0940d03012400d10b030801420702801101c00351082c0c0341c0c210030b2700b00c51009000c0c070901c80300529227540c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 546987446 1250 546986196 546986221
    0x19080904050f06041d100e030f03090705011e0905102105070327030c0222020403150b090a02090402040f1e05010206010b03010306050a02091309060c0512010308160b 73
    0xa8440b441140380c10062400c3c981c142c84000c901e07a0311080101030406c400e0021100611038a07000070034511082c0700a04100d4940d400451040b0403401c0a442068a090000340038500c442502d401900401c000008a00e41d114026201b1120115102803075070411450075204000c104039a1548034030f2090000c0d1858100d5000140629180c0c2d4042200301c1c500030351800600490224500e81441c24098000441d2084040d01c481c0c50005200c40800070145040b1003081c40700444000702990041810014003a401d6130144821101d540280103140e5143e0000c0c110a20060111040903070100700100c041e25964156006002c01150491032113403a0030044600c40422038206295003880b05012032154404100e4074100c9901a81a9080d41d00390365130900540030003410481000e034213200e800d2346559002c0c0303444074001003001c0006d010141c904200050701c030304510a4052083c10040740c0d90262094185030f0450b03400200b580e4a500e040440000080c8103600c01031b002400384001e00c40b103100c004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 546988696 1250 546987446 546987451
    0x3371412151918090f022106310b060904080415080f010909020a03030c150911040f0204051e0d121214040b0606071703011811070519080904050f 64
    0x103e1180d00740b022440c400b0082e5000344400410030307035405411a005041c1750b11501c2880742c0118104040c80001e510044c41c00c00d0840b2204210b0f156036000b10a840076201c3e065184500c0404510759a40f02a00c8050000201130304c11402404038070001000c0c4406082641c018000e200e0806000d0004241d0003000c41c0d00c10303215183d6118a00000140d8102071f4440c2d498210750280c2a694000d107180c8095603428903002c410f0b114224918601c100303204113845222a80e9219889000240a0341400c1c4030850b91400d100e0390507075104100502c8941e4841c0c40c981a080383c14a42c9800b40200031010400b81d03030070000024014426040d00019282e041010b50407a11016142044001701204190f5100e0700151000380100c402c0b10007140035814008010b140d8140280c1c051200380024210740c4e103243e0301c00d0703020b46c440900105884c0081c1405014140701514050403403428040d464403015100d400703980c1a4295010700d80c020504000320201039421081300140700700400d00e004c07002e003007203002c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 546989946 1250 546988696 546988709
    0x803070e09060420130312030f0518071a0c010c050c0d09030c21050a0302330703021312050a030e031f0b03033714121519 54
    0x5410001c0c1d240d06091148003200d14158018406500200b40440c14582c00460f0310000c07500c00c0100840403540344487d80941010a50f000181e2260083e800b200312030001d081480a00f41c40704000c8422000003418000b0f8a00c1c805100e403c42d01d10346540c00180c07141c02100c00441d400e10780b60350449600017005e080c4540400c01138032020344200c1c90450301d01d4010b0000522078041034001788907640f600031040f078405103500300201c500030107034a41e640707001c0100308201c0042c0c0c0601451076403900c1e07070782042c01d800484000d0314200d1a481d0491a00b001030090505040590110f0b025510074809102280180142c2d01c2400c23060400e401d02645901ca003243c01c3c0d020501c0e900300814281000991500e207401d80d899101480ca00c0c009a0101030401d481c0381984c075210510584e014210101030305180c602041d8060001000071403c401c225409008405060001065050010354000d400300c513018103030180441e8050351455100381403c950301d0619900101c40d04006001440c409100c01c05603030701c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 546991196 1250 546989946 546989959
    0x31905070b0c060a0c2c0f03070b030604020921060f0708070219170a030e06070915030507140304030c03080a050115080901021e0d060504020906190c0803070e 70
    0x464020706000380c40348081c207804691103940002d50b1003095078810444480140f40150305120210790203210f910f2011b0780b600400100100d03561803850540901c81072020280c019001803454031402a1842c000200221701580e00015285c00076550b03001401b40d0f00c40c1c0c101038500d0b4074900d0f00a5981d1070b030301240c407030a661500030040303030065010302e4156200c2c502c0b55006140c40700f0510104030300d1301e5030000c040359480c2c004c0c50343c00a030b030306502d000d40604482507600058010902d034443e4581480a883c04003400f4084d142401010301401c45a801840c080c2404a207079100d10808555454100888013501e01c00031003070204050b0b2040102c16403e004e80c0d60180d6070740381c8507074034404c07180d003845440402403c000130b48003428007906a072a400303010702c0001403c0150080d0711004001100116043c910070000301140503035030a11448001d01001d4404501300400d00300440c02070300c01d0249165460680b00203192503284524464000c10380c0c043c24a41d12410b14601c0078100d0450003010074130809 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 546992446 1250 546991196 546991199
    0x3080702100b0a03020f0a090f0e16030f140a0804030614070e0619020309040603050f160501080402040e03090d0809010f1412130501060b0d1d07150e03190507 70
    0x2031060182d2002c14400801044000c0d03d56400c00244840c44490280c001d100c0000004040d2107910440c4401c0c0720404005c40c1e0700584091090403c8003421288641070290347c000d001044c1071202443c0c40641c0054130860308482c40103050300c2c00d503465000a111100015000c800c0000d10b801000340080c00090045880d2140c250558080c400c0b03000051b000f034001d122080e450301881c490030064402e180150791500c28484041402d40c3c074960810340f03080c0c1c09003c0341d1030072a6042100d60b0040c1101404150110704100000b003600d0b40103000a0302c543d494842d08070303040000348203c60040c58010580b41c040359252415400d1504079916090118031164040c0510074000d00c000c543c00180c101200d0301c0c00c283c94411500ba90000b402e0620141c5040c0401c0000030406d2258202810711082c00c1c68441500c10584019101c0801c0100d14480d0300490316a418800040c0b42d1050f1000140f602d41d41100c1010700300c60f2f0b0480300e10025414494043c400031403600d070758443d84100e4000d006a41009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 546993696 1250 546992446 546992473
    0xa060e01020a0c120c0c08061033050c0102030411030c060705030d0e0c090406060311421818061c0201200309090a15140a1203080702 59
    0x34040c400000d800300d07004034035510004d0300d0203c035100d0070052420b000603640015280d2189038100b41e002035006901140c02d222502401c001c4820082408814100f03100090128511200105140c045d41041410790200500c50260f419110340700c101200841d124503003800e04c041c40300800002103000e4064003a00884034140349084034101900000150b25103e00940c0500c01442040703c0c9091034047c0200703124442d5101c904090007140651008940b060450500d850140c804070000c5108120300b1032000d8001c1c44041c21141029900c030128046c2181d001c000202c00782c000d002141440e0f00003c0d8403900a01506248890040e0540e00b01d038590401d40c0403207401400658901e90f00c001d110317102e0003d6100710b09800140c2403061400b92060b807551800030904103010340d81c00700e007600040b40c090006d00301149840e030701c00c01043c1c0510040941540a40c21100180181541c0b030a00d03c40890351034a511410500400c07411b814000300205908000b482400160b8212006006903000741c1010b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 546994946 1250 546993696 546993701
    0x10f0503012702040807081c02150109050901110412031704030c14011e020a031a0109061407051002120c030103050c010c1a100501090503060108060a0c02120c0a060e01 74
    0x694203694400c10002d0b1800c82810354400d48200702e0220280c003044040742000e014002107006107000e00c01001c503d200043c007480e030282d58101c40c4007198840b1740ea40d11010450b46031541154910310700080c0e00d2b184d103507000e8058061a03885074000d140008000812000d210b101610650180c1c2d604411500d401300b02e00b40b110003e1f20b020b80000c0700210303114003040100002d0191100410000a18110000c10742e40b20f400708015142009540402c0c3c103040caa4148c0913032000e4a2809a0103c11002c41400181882c00d560040320108100c1c540540f02c0039600d40c086950755070300442100c111010851714200079600407d804401f08056001041d84402c00000b40d905032540b10002d03050f030103e000300464040005610580c0c0000306070b80c0c0651521041d403211401035034200040301105040c2000540240040d900040c021b60015004110411011407a10740083c3c070520007140d0160041822442c0400c844890320079908002100300400710300003040c1c9910392262a06101d01401d10f11001d08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 546996196 1250 546994946 546994949
    0x51b010212010b0f07061125020904030302130b070c0305010b100f0320360105030f0601090b1308010c030209100e01030e030403060501092a0e0a090e0606010f050301 73
    0x100321400400500140d000d2502405007048407041140c1050b0170b6031104815101c0f00c20b140c5a000c41e002034094041c3c078100315100c0140c0241010012508202d6020800890b4001e0010b01003650100c1c24008150000d62030000620010720010303291101d0381440002002e20b0701c07045501d5880d1000102c40c1c0d0400003003c1e0a90042625155860884203800350003a018200126040300000381d1003103103048010000d002021802540704a0000010b1482c40720403401583c42c1e2061180306035032141a03030388101220f611412080000300b00c0d494413001038841402c00c1d0080d4400d0040424800c0f501c0c40303031241410859030454001e00590b07150b05415001c0744251080303a500f0151490301c4145950140f0300351280c20300306260001da40c4c17920b0403106003503401a82003250401e44900040000040d140140e0f16241460b941c6494404c3c0c1648022940d140e0180a42081c08101e041c2014507681d51901c080051680074020700038400c6a2202d0744c0c072a981200c84034041400c90702c459020354403500a030fa0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 546997446 1250 546996196 546996217
    0x50310080a0c0303050a1e030e0f0105100314030f0a080f010b0306010c030806031612020103140c0901081e100312080f0105010c1e0c051311040e0421051b0102 70
    0x40c0ca4500f15101100c4560103811200706100010320a02000c1c100d030401d007040407145903000510b50382d480c9401414a1362100340740e502c5038140001d10125218070250082141d03400405050740128030f5082070700f1170194003402c10390b541b004161403609a4001c00154801c12036600f107c4600e81c4c880c00d40c4c7c0e030a4042035891300d00083c0c02d085a600000e024004040d08005c0c010115101c0e280d0380d0354890b400b0311868008448408480070ad85046503014003824101440c80038041d00360b4030b0010000714490094440c07080c100314107040411610f04002a046424550703402d5440a146015800004ca1650318442140d1144400700c0c4128410b20441d0214000c151584441405918100c011500185801c41c19107200005681c08009549451400c80c4218420f94004000501e40010055000203165002003103c2c24040b8020b4815841801c442c241c030541c1c07500150540329400c00d000c03200707650500d41c0b5101a450401d0300b01560030001401201207150886c9052075581c1d0700141c240e015203c0c0c1030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 546998696 1250 546997446 546997463
    0x3160c0f081602030609030d0c0c020d0210050d1401060908010e06011e050612220f0318030209090705040c03290303071a090c1f0804061b050310080a 66
    0x40c00021078000c0104210344a8040030707440202143c0001e800c010341a80d0300c94496200180540c40700318079002c4c584e80c0003a04c1c00e02c401366007195000310380f005a00241c0248180070038118404441e00420507503441003400e81041100341124518401c0c50b11083c001d003000306004410014400340140035001f00e4248940190520b81d1910441c000c0032000800ba41d035000d016014085556200d400181101c2c0c20f08500e201c6280c28680e1480174664081c00b046031501100c008000041100191501d92169040c902003452440b040d44514401815420003984400401c0500c48450800180e000503901c0440e82048100c0d40384600760120b0761f5040714040388003180b4408011000b61485038038280c983c0542034901c0c000305030780d4454000d42880c240c0e1401c0048e040c24007e0000d010031959000090a070391031524031101c00d0060340380b4810b1040c401d08004107000002c1c2080741da60020954803080300c10040c020810400c014015070000c69451130761640b214000100158001520b443c0540c0100340c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 546999946 1250 546998696 546998723
    0x6140105070f0503160606090506030307080f22060309050c040b0d02150712091703040303080114030a0b0a06030b1e06130e0a080705160e07030b0114030c03160c 71
    0x10340300480b40b1000159030900042c441d00400104082100345000d2180d0070000e07800b4101018181114000f60810b03000e41c1c028485200002c0c2c2c8642215100807002000c19110000c0c1000303100c07145080d0490703804034078001d000010041c2e010741200a48511450564015a1241050000311003011800a90100d040c006540150501052041a08480c0701301c07146407e5075074448105041c014002140061000030080000c030403501d5a81101000920140d860549191401051800d040c0520001e1601c0042d5032221903804215442801d03a201180c01e010b071600c500c80d10024610703403105942002550b00090a0343c85c43e10000f0809160110400007503440b40c4060041a030107403001c1116095541460100301281002010880d80c0300e052560b584545c1494607a09140401010351000810391000b440290300014290764000300e07501c2c0002d04e103095040101c500114590240c105941d00005000e0784000034002544201280030104040b0340250000b01d406010b0b00741d02604100c880c014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 547001196 1250 546999946 546999953
    0x4120f052104170c030304030813170a021002041a0921011e1401030201050d020d0615030c0203031003062d0b030f070e060d0519080d0614010507 64
    0x804a014980a19045040585411114101403090301c090400700c84000300304020000240d10b101d2020307070310f0f4900e58240700019803060f50740d000c0504003e040c0030040300000d6045100b0311503846050340200451011801c1d0082039801ca07440400600c0040c052440090001c2145000b16000c44c1d10400c0e142c0c0590903142c14458643c2c000701d90303142d131100c0e9003a1480022501c50415403003101ca8030000052500c1c80149195111040b015581c1ca014180f10300f10501010424015045030740a0900035910800043c10178000d21913500d00703410007450310602141a9140310b400c04100f00082c1ca00700004a18110181c2c1e40340411250054010812401403001607500d812580d2000400941c14101d0000c50f40d001d00303000f0408841c1d1030081ea60387d2845c00e5900e0b04002205125000002404145003000c1c0c84032a840401000e0500400c00088540c040040400040745101d185507503c4007006580e00d400a125030240c0050b1707115a00303002c4003045209038540d0b0040f00d080144c5486183c4101a039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 547002446 1250 547001196 547001207
    0xb0f090406050a110f12010608060f0d030e1c0203071707120201050f030c0327100911090c03070216061e02010f060f0905010e040809130b0310060e09060412 69
    0x80c03503da99035464180b0880402180c101605041040c041c25644488424905040e81c4d0300c1603000b441002804028084140c65445075200704072006c1c0c0342c4c1c00c121300c22030a0540f03c0180942c2c0d8580c103d01c0000c25284203140c900e0b160030703203130748220240d5544540d2040740840d42108420300c51055080741400300440310200c45041c40c0c0c1807060600781d040c100400b02ca444541c1080b14440b25040000040090142001d0070381d0070445414513004041094108105545c4d54240602910040d9949001c1d03090000c00480c1080c2140010241941498240000c0f0040e420a85403080584117100700e00703188825681c0c0d840142e4556540304000080032050404120102030030450030b5558401000d0352441d214000c4101501194100c1d034202072502d100303282246c80503801940ca510301c20080c000010a61812109281d10494031661000074100c4010008c1c02d07000a665032622500600d440c7e000060342062085030078810504405075030340381086458600840d8010403854078070020410090080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 547003696 1250 547002446 547002451
    0xa05011115070503070e1f030c0e0d0f05100204080a1e0b09010e0c06040806181603050c09060f10140408030c01020c060601021f0f18030903060b0f09040605 69
    0x180407540d540400d6005007060820590b0a20005080007040162460b040148032400c00b82c203940c1806041940701705514598170311015001016103131200c600c88070b8030406003000d03200700082079640028201c1c80d1581300b1242210301102d043c0100e9000c41c10084041c805d540440d181d98015040305916551034503502c0c02907403d01d0051080e2010803e0218006c80c50492203111030000004946131103903509454001551041e0703105500801040c0480600400d1507900f11403085d0021386030b6000078403080d08110581c0721029001d052194000240040040c030690706000c1078540081a807190014000400c908034006600720154002c40c55501748180350081102c2c0708240c000d420a600c0b011820b055a112090710501c0d1303900841c010390242414007460307800c040240014103281806c00481443c12041c070008810319a910713080710704070311881e400600e15400300d984241076440407032030b020b0058000d6010a6580c00c4c03800c1054459420100c3c850880313040004c0401c001e994444e036406001c0d1100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 547004946 1250 547003696 547003727
    0xb070201120524030123060409021003061a040305190201021c0207050301060b09030a080c0106030f14010509010b0d0f1e0f03080c07080d090c0b0309150105030c0a0501 74
    0x1010500c1880c210244609401800c2c0f4540c181000c000c5903450100344800c02c0701c481e1184c0d1401135841041c0c0303a0081581000d40c12046011b90320b5848400140007800d00c0301005e5080940c0c0c85004602d1a0b041d030046007624140c44817911184072401d0044007070f0240c0d00008041d981301e001066040380c08a1140c00345184144100c030201100c0850309081403070100300b91405680018801e00c450714080c090035020340140c155003804c2400c0000002d984000c1c0141c080c081d0000082c002a1040c4203401c80e030301641d00807903015540f000c14a04000340060ba602d00c0e02d221f528007004a0721003a018020f0010780e030030040c0803107075241d41e50311500c2040306500b400b1600143d04140009050224400c1e5401490141a1240540c403542c00e015150030002007010501510401070500000c204c9026101d003014405030000d21707550075140080030b03031019400102403000080200140703c000041c041000c0c259078613841d007040c0da854041c5580c2e001c0c100d030081e90290104005103c55449000c10729a16801d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 547006196 1250 547004946 547004957
    0x21b01031505060d021e0c07030f050307170c0f060705031f09050a15061119060f09140d0528050d1406040e03030708040b06040f020d02180604030803010b070201 71
    0x5030344002a24a9008041c4141c1c1d454000c40c080c86c46980b941080401148203000803442d182865010540b503514501008000011408030f03902400341c1041519034483c0d00c005003c000d030031400c000c0c800740d40190611032514812444400402d85001c41d072680181025200c142c2162280101180e1181d200c03558610605e03103030100042d0000107400341e640190070300c40001900785418042007988440300e400c09c20030302a0039044414808400203111003d840c50340c81d494100001031a002002d8076600b10040035590a007000b80d01489201c41e10700c81d901c222081203030403030014050103a9682c0141c182c0b207110800c0400700e920281502200304051a91103140552800100c40d824400712900d0140188a000e000001c1180c3da051512404a038012007100030360942c0b0b4480c4c0b00920010009000818641080d00402c01c0c50700d40313412051851280c800e09640f1241036010700d6000390421102080c80a001a40190003801d0001c11201070301e4001c2e508919503030a05554800546c050f810881c10800c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 547007446 1250 547006196 547006199
    0x20c010f03110d091a04030c08070f020909071e0b0904090302010e0a061401050405010e061207080f030309100b1309020609040501080319030b060406081306020f19021b010315 77
    0x10b101c00010b01c66a42400c000003840703200ca05242c10109040300040c041301078207006110101307400ca462540500e51181e0b81d03d80d150154a0f01c402409441c40f00250800900700c00c1c08544a40840c02d1815510050f8144511307950000103112140d08610039100f10b154100300c210610b05198000a41090180c0004960080c484150f03610f40b1807004c200b0b840403130b80e0740f071525210742c05054054014902202c0c180702c103505181803003c010740017a20b403d1251148003401444c0d00428000785d80241005016202190010b48038191070340d00c1158800360038020004e403003100b051907210b1068019400303451812021050b01c07d840080040402c1a64447d1040c003040d50540c0c0c0d28042d49020305280f0380a10344903c101e142c11700f0f5803c2d540d0016803e05050070480c0d0302035103c082c203480880700f1a140402e01500c2d05150002d20461005000d0402c5000041001014058000070181c02c0685583c2c01c0000c109000700301e8964941c82044100d440704481c00d141c140d8426001050440d4120600a1156 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 547008696 1250 547007446 547007471
    0x90402150c1b0103060605035104110912012a0f030911041802060d09050d1b060203180703051605060c0303070c0516030b040c050d03020c010f03 64
    0x350032048104940b5440644560800c0d201220031034507584080c00d0510840d410f107100a440f40c00010030203410fa9503008200038005840b250030300403000c0c9041c2030800300c3d01c148403454106001e485409002660482801400c0c1c01c05200d0102c0454002d0388031410400340300208007541d500340898043d69902d40314441c1c03c4e0084405500085140c460300080d03038401c000006884112a00d40c240181883c02450f08042115252001c00300b110803074000550103204600303825607000c00c440203500b049010030380303c4050506510064040707000c0c10488040020010045401080d003181d040900043e145209000800320303005960010101040e952030301440c480304034070b003c2e03296101791110381c440d0341072100954012111002a000030384106142100c01c030107a83e680d200c068980700811065020100c2481418401c5e0301c0070966507502000342039601d061410030404291030903900e43d00d200c500020186009a09110150340c50340141407410301103001582e082021030142c0e014103845201501e03c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 547009946 1250 547008696 547008739
    0x1a0f040504050627041514070e0d0807080306041104121e05030d060f0f03030c0209270d020616080a0b0a0801020703051b07030201050f16080315191202090402 70
    0x2200b00c848013599a0781307424105102c00b9040307520096102490700d03000040d098114228039901c14642c1c00d0051450b005080030415001a03180044d01084010801c0c03010404404d000b90b00840c42294103005929003948a0541c034802c501c1a5004c680c48105c21800142040c068074a8040342c01040c0d103500303800d944540341150711561450203d955103600a11040c00c80c112800c000e4040600611896800c0d954050103c00d44003802900c9420303c8000075a6900c460b080300d481112320b80d501c0310f0940700400c2420350348800b40c031070b4100540940302c001402c19070088042c00719000340e40c0c2c80c00b005403038026400009040c50714500390412001540483d00300400d0009001c074901c0b0759521030362162800880b9600340840710b8040c0380303031b00b0805040000d07030703030200c03d5480c0c020109020a81e00e28001064000340040880e00800014010040200030302c007030034068094100940f180d60000c40307100b2000440341c05c180900e0505403079519a200141c1410300c2c1a941c440e1014001080f44001d070700c4984107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 547011196 1250 547009946 547009999
    0xb0d020a0b03061e03031e09220b0108070c0f0302010b0301151406040501050403150605040903090e1b03070e180a0605011206030c090207061b08011a0f0405040506 72
    0x1840301c400020303c04142880f1103405041103074100801c12100d0000300080c3c5900c00e01103c10703841c1d11000b034426107400170f00c0b003201c4041c40024903021a5a44580728802c03211803000311086c05600e01134022046500039011588245074a90b9402000000ca5a6038407807030000700030030340c110340d40ca000300c0f4142e441c00d1142429103a48100400d025500d0046000b0450310410021400f0b00c01c203100030405170b40c100c400d54003901e0f84062908041504625064000d02c10383c1e01030707540941070180c07503018103420035040d80c141d903210405107480d6035404d18078120034410001c500c0140c3d8401c03c005094a80b03d114400007242004115030110100504076880402e810341c2d84030412540e6800421846d03800c00981c1c403c071201518180092451515691190b803070074421003041a40001d603840400c0403075401515804106092110520b90221004045020034050303000c1c10b040c0c54a0142e5070f5040e03a0213603409001c08c10003152405084c03100f440040c1c40007a20f107682040c400c0740d442c1c0c0c5440002d800280c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 547012446 1250 547011196 547011209
    0x60c03070501090c051203040e060f270703061712130b03010b131212140f0c012007170d021318110325090f0618060212030a0b0d020a 59
    0x14811307410300042004c04015468280d15541c81088104001d5407000103031580800100c810000818004020550400d41258401d810800510700c4582050100180034040e0641d980d0070030030181c0381e4856030f10301c3c0000041c0640d01d40c04003a50711480d500000042160340310520810722416980c910400d036a40003a080041074460128010041c82c0540300144018409502c401e03049041c0c544440c0381c0781c0003810101c003c001c501240002c40a200400b00c1d041c1d01d4401d94026955001d08111174004d00c6c0269085264030011081e6800c0d09810405030b800c0690062a164078000118034010580da1010084007411a001d2280e903120a030180c51400007461001c00c10b280a0b40f501d9445011198090842013070900c1c00d00a000400c410f5101500406000742083d82a4503162803003039a00c51841d074088810300e65540b40100d0015884206041181610b041e02080a9111b82d0160380345c0c3c51240e40d8000c01802800040d01c0d40034a0740040501d80d002809007045d840013500071601c01601c641102 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 547013696 1250 547012446 547012463
    0x903130f0e060d0308011e0314010b10090b0a0e0d0807050708060703020301141c0804083910180b07140624040f09050d090b03090309060c0307050109 66
    0x1c00c11039881950381e99218038110307000c0b100700c1415900509850418040d140540324a050386495814004900c04003550308403401c840e122a281a0107806083d50656050248140300d0038603c03a07600445c2035005403000c802186083c1010190222800b10050104661041e68540300301c0100f842c49004110303507406007014040d000d0800d8402860001c000c0c0200042501c1000104071080a1307040d41d00d07814004035a605842c884280c5a0050351561001c080d000440000d4002000140050300d1007030980c4501c1d950f0007012100903220300c1c20036202e4a084030343c4811499640c2d80d2400d6a00803580c100c0e503040011880c107180001c0d245080c40ba13042000c0704003002400344140141d14244080c04101507004102030328106c240d81a80e0117003e100320b50205e02103045402c48e13584d82e4204804183c03a114080207544a1410f01b80da40d00101c41c8101c000c0758807000301042c003001c1007007120f114102c01c0b40110301c1c1c901d00ea000e1002c158829842c00c002e60000340710b0000018020b0040c90b00d09c50003070000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 547014946 1250 547013696 547013699
    0x61d0109030219030e01030b01023a0206040503040509270709060b090102072105010207050a02151603050d0905031308010b0409051509240f060901030302030d050903130f 75
    0x1902e041c600310f0488454024084060740000c1d8400c94241800d8800e1a01080c0da80b02d520040c1d00c0c0036041c0114100d80312481c000c41e00510207800e0105180c0d42e10150003e85400702000607030710ba5400352070240158008100500c840c1c2420015980c025100c7c041003200d400d80c01180150241c0381034041d400c244c014600401403604540a80c1d400b40c400c4011161900e504400041d588942600c2000c00200b464010049004002c90121448a40040c020f555441251900545172411202d08a2186c540b00c114061a05c0d810f805442c4895254508441e0a610640303042d600c40e001101042c0c00c00340c55403c2d00b40000c8091020340002103800b00b03800029810f0000e16070035901c650072030758001d501c1c00c0a040040b580002d014038020200785000711580c0c8500707400074100014a102c41c00d1583c605a0b803410301801c407401e4903108050040d841481030700ca0b030003040140c603028840030340140d10911050302c2c04001a0710664000d5040c1045a2a200d607112101280e11280d034440011410b0b032610 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 547016196 1250 547014946 547014953
    0x90405132a150f0f0e06040b0d0c0306080303040303020c0c131d060c04050d021f0801090b09040b060f0d050105090c040f02040509040f0305070b190b0a05010516061d0109 75
    0x1400d000360060071100b403040c01480c80000c1001d20f0380da541d10104840001020b500d5405001501543c0401070075066582c0c3c1c0f220b40589070350340441e041c103004038a0001642c0d0440d00c80c0c450301040c0d41d0914040c6203552502d4034201c0194002000081d09070091a10008035540c400301c0591b2034241c0f03e04003240d03c0c011101c1c036602601c03070001b000c88035804c90020440d0042000c01200d094840440305030800071000e0000c10b401b8940b400d12003070807041034010704c0c1c41c2c00d8001c84007c0c101c0d4000c400c244802440c0c1010700400541c02d4400a20094808000c00c80307500e4660608038000b0f201400410004031640c075410309492040d1446a015081403103031032900c1c14913004446a1295401041d0728040c582004189480d0000308094080c5510081510400d8070030400c4440c49034011256651505080210095400d9a80042e070416803905c030b249402c90a1450000c012104141c5602d0b0400021541c10007401000304401c581c0190350349a0352004a90301940041d140b400ca100009249150f0314 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 547017446 1250 547016196 547016273
    0x207120f02090a330b03090601080f030a020a030f03090b04030306080f210901020f03030901051e100902090f040e0d171003030c0611160516030809040513 68
    0x2030480b00350504000141c0e00c4821801558102a030840c01c010703816a079040300c03080c62100b517500500b1070002d000081c080e2249000038003e0582e2001700960b040c40c8007140081d0f0360b0b403190030000c0000d0307004002060042130182a040c0d2400030307681004541c0f101c956503142e0030070a040b20100c000c6540c0701d01c1480302e158208403003102481032000030200d80e07502c1c80b10303089412904260400c500030005640f1046074401e00849240c01072000460307840c0c0c1440c030356507400380108035600f034103c0e44103103100c036400d0080c0b01819020f80840e40d1607142242c10440110040c1d0b02c0003591540040c50072901c8011a2124400c0d0f00c24503005001400d4070302008800184803105800c8c2ca10f042c4984a824405100b08190a80040380d516040a0b03000401da0702c5c1c144003418181c50b408104090218110704015014035410301c006202d03100f960706c0c800c0c0c082c0c2280c003014224013011b821200c040c40041041c0c02c103507010341c1d000014400c024080500c0da0741c0f07260341c606050000403070030003880c859078614000d184c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 547018696 1250 547017446 547017451
    0x270402041e032306040b090c03030705010c080a110a030506030c0a0e0103020f09010317070507050a0803030402040c21020f0c03130e09060103030507060203060d02060d0c09080a0f030f0207120f0209 87
    0x209000080b0804984011350390540648084d10900284010500c01d0004000041e249640a4242da80f50b00f42402d003a8000c6c14408901d00c042035400c000158011030701d100d400887c880b50100e0350b0810901c0d1a045004140051089030144150502d0480741c1d81d030741154030000e1020f031459803c0d079170441c4140111480c3d003100030fa000304220001800002c1940d1004068000d140811b075484050a0400a1078008035070701c29500103010100208054002000030341c030481c005d903014000c180284030204c8500b60761022507000c0d0102010b00400c80c400c1a0010011481280c003044c1c10f00503015071803401c6d940075078011030000584d090108031501d0340e0602d00358041c0085000e003540e50f246441c0a00180314010008202c1980000025090b55407211000022500a00465107503040320600c100100040c91498000c01e19032a00001c04a07000144038030855400000b840701c0e0a040c2d0b4094800a0122100d241940182507010640c0610b6130340c0002d62600945880070643c0ba103005106128402 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 547019946 1250 547018696 547018733
    0x50105010b0a1d0105070b041b060c031b02091906170d02070b0f09040504021c08030703140108211b0a1713140609040504080903070b270402041e03 65
    0x3c1401c0d451541c1c0c3c201c0d042d100384036040220600b540d5900e150030a020440d01507030791030645e074000e070208001c5c1d07110350300c010514400e403200c04288035040c120343e084401050000394407458020001d248600c0d5083d29560b80703083c0d0707400401c3e0203845500071f0040c286407800c00c24243d4801e9415640c0c8035070401c50300c001030400c00340c0145899542e081e07041c03071031080c03c000701c0c003954803480460119100c803420540d10780d03a500d40109e140c035441d00c2d0460659105840d1040000e09000012401e40048100e1b94101c2d0340362401050f03404007205240c030000c1889100440385138800d06c84070052114840a207a60095658060401b2281d6841e055229a00b110280c85109038180720741080c0d42034040c0c401d403ea60302d180b55032201807038000014103907108541005070801d08150600c010440e01c0c10281801e49030880a0b034402c683c0b2201000306901074900c04a5a440b40134040c684000c1016080c68560400a003000d40790588428104541c0740c0c800c8100140041c00b190200305200d0f044540900000340e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 547021196 1250 547019946 547019987
    0xf05040302160f06050318010e151005030601031527060606050a050a0e0a0b1206030613030f050a0323091c0c080f09040e030406090602010c08010608040f050105010b0a 74
    0x1400e1484503081004d0160000307100c40080407420108203e4400b06140304660001e2020220b0519420b80b40c13084200c08006400420001c01d6a904015040006540c0050000c043c0e0b0703032854881880114801071100641580c5004103e1108004611280b01951200c1e00b555000054902042250415440301d410401c05210700c3d07101d95401000c40e0720390b4016140042400c0a070500041800e04a5401a80300c09800506800c542c0170f88810241320b02003c44c26a65666240b50b007d04550341000d000030002458100b10313203074079400783c400b601a1144510b400076074022480c0340080380303000810402580c02203107800c002c000441000650019400f560007120745070249100030304070b81c024020041c8030320341c0480c1e03680c00869040244e07108a5402001401210303014454181c4075032090064500103541e211021a0190050041d03900c0c0e50002d56525065070f1070204100c90024024200f200ca0300d40a801c1c020118000f401480c0c0640b899041041ea01c415044015181c01a030400201c80701c00e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 547022446 1250 547021196 547021199
    0x20d170712031803230a030b0a090e03041a27030f0c0604120303110301060c20131a040c050306120604320706050304060605040b0a0302010f0c02040f0504030216 71
    0x842801c0d83d2506198117080044440121030703880e0300406012840c0c00c00280c0049161407045a0503003044000301c90039550440419181c0450200b99205115080210741c0100030070086d021005015698214400d0800d6051141710810011442000b4058005012910862035864031b4184082c40c10101c0d6440200502d00c10301c00070904501540c031a0116903103081b92450181070103500f025003030302c1c0090040307903580d03131101005072004a07844403c2d100640070074200600d02003c451b4086c40800700400c01040042181c1c15080600f04000f07400e0280f404100b003416950b1984d003d5030440180b00d4454503160301d804002c2c015000006401080268001000d002c0851002c041c145001c5404000b803840c00c90210400b441c2c92000b401084200f40705036003000410551240c051405a0b10681c02808825a030704100015185014202a808900c04030200010360183d40042c010100301c1c24103490010303994000404860100c8400320925842d0700c00c2104155040c08822020b00340d4285810205 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 547023696 1250 547022446 547022471
    0xf020304020108070e211516080604020a12050708220201120905010b031507120c171021120201091509150608011b0504050d0f020d17071203 62
    0xf10340103403140092140458480c40142c0740c00c07500031091131403445518240e8158252003551421038910030220f0115a50229240f1755004200601100c190340c3d031100c0369180c440c10030000758010300c1e60009120000d00d0110702c0f20001e00605111700314540381e0702e005203070080024111008020b25071101d00c0f111250b40f030060383c0102d00307258034000c03034440050b45007030600d011401440d00311501030341881952100c003000c2e074503215101c1c42044607503100240001045040d1003503c004080a00c0403882880081658a2081c581264804d8060198029050b81c50340121170300d5201c4c0c1307011280b0007036103030200050141d41303103401208030802d100030004c90200c0d49aa951101403062581941c6807220401001e1003185400076013018170004041082c41d5950301d4050090159903202518010380005090340305004009640c201d600250450714034801c50b030f0300e250601d4240c0808981c00070061a214001c01c0f6101b9081241030159055070307564007950305181400c0d03003404e40c20300101070800a4003c5030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 547024946 1250 547023696 547023707
    0x1b061127060406050d060504020f0706140f01030602031005041508010b0901050d29070504060e01020a08030c09011e0521090c0603090a12092d0b070311030c0106090f0203040201 78
    0x201c82480c038005440710301e0885c000700a0f06041d0301844c1d006001192000b082c00001008002062007224104202003441054910565088417a005480308800040000c00c40e1a001550f210300d44181d84081c1e20f495034006030448890003000c410480b03010b0720500a00e00c0c01d04c5141c0050b0760485515089600d0140080d0500080700401001c0c82103c02100b205105217072402c80101c010011108143e00d80840300130a81e8200e84035000011b54016003080d865400403410141c11500306100f50b00c3e56440c1c00c040080e60744004031050400c103e6140c0035410042402c8244103410256454540e81c541d6041511150282c00520342140040b54003402811840040c20104020b0f00359500789d1a5994490b4050400f80c030008041c2070001141c054140c2183d02072858015180501296286c00545c07400d407005e03407002d07590310420a6540304814030500d02a1806082c085210f0701d000844880040a0b09007150000184243c2603034640701e003480f00d2845409081c540300c8140d03e0450a624054000824 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 547026196 1250 547024946 547024949
    0xc06070206070311310b03190f0207050d030e0f0303011d01050907122c0a170705060f0402030f16080606060a02030702091503010903020708121201061b0611270604 72
    0x5c0c010321416055038400610308500300400078824115100d18040c20340e460240c85000340350840d80e2504d05214501e010600c25140070340c0d0080005c007003d4014a000341d00400248000041600c6a00c03c0b1442103101000110302a040842c0b02c0812404d0b8800840405071040e04600c1c41101e0110400c4603455100b248070b4800f074096000452051002a0030303a086842c20408045040e00e5403400010003007000616402c11889803941c01900c0e0342c1c59030740031528002c00c10001c1081d0800e10118900301407120200c1d8210340002c00b03981c101c55244152910305003585107510780c0010381020800c040c0a00788000b47e071084099407a54509606620300a403644111400244108048004505003c1e4040505008010058020000c5a80b641000303940c440252142c001e90f48200c0c4904101c085120064a140f1011884000703940c0e403d140042e81e07054092130344c1104089080010802088141c0140f091110104d03007440c0e0707079000d145030804040d1b0b506600841041c0106140d10341989815040381e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 547027446 1250 547026196 547026247
    0x14130203150402070303020a0f0201020f1218061e061503160306030c0612110403080406080a090b04030e0f01021c230f040501080a05040f03030c03020c06070206070311 74
    0x140d980e41e80003501d1401c407908850309a0418800b003625000c258066008061288140d05c441c500710442000403400d1340701d41010340c0300d9510140020154011001f5034240c20040950a584510a00d0403405e0310708601150203001d508100f041003081d40081c2001b2f59040b800c01d40d025080b580c5185a0708405110203032045400045640003020114401e60203880515032082d8401e030042d60383c4000512030107200700c0e01c21900e49849040b0000442200c11941100d0380614501c2c20145002e03820348102d00010043c3c5205078450b14010009100e06013084c1c8941d11a494109109070b100c0184205a4600f81556042d0b500c041c0c2d4840b4850b07103a0321001e03005405480c1c03614204c2d42c0c0c1200c101154200d1441c882d0070b0b2380d000ca90320414860080290094807001e90700d000d590340c0d13416034802c103480080d940601501c1502e40a500428480d810142c041207040c10050300e0b080201d04514030300413040f9070303a1005070070080c2805041940b40c069140c907000c50070082410000c42401800248048481d01c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 547028696 1250 547027446 547027451
    0x306030c01080402180f07030605060315010c0305070c0b040f060c050a0b270c040506220504060912030902040507020d090b030603161e0f03050a02040f0609060617011413 75
    0xf800c40d592901c0080134600c1c110031801c50741c00d00b000c10f03103a0010140d030414007003030900c1000f0401e0300303000c0d0075280314442840e0841c8007140f0301c50064808072900781c800d0b02040030400c901808201c04e0b0002c0b000070504050f855949a141a0b00035420551a801c46000c1224021600010072800a2400000c1d0b40140d030010003621400580070201100c0c143c0c0b910801d1a1030030981080d1400f00e40c055400200342c45c180001d07926070041000e580c1210626203114201316580c8150401d075940042d500034407500c0d0001e58000152280341500d48100c11040000e03071034501e0507086050500407160803003014001488503200d075400c040d101100764000c4041c1c00c0307001302c00241c0360b036010403240d600150381543c9840450740750031203940300701c0c007406060450000308400080c96840b01c640d0101104c4d00701000c1c006051840d070070080501988000455459110038000c141030303a092003107a0007450706c1c0d1900e40882c6412a907501c000d030b1050340a40340303a40058100d51925220b0705503101e98040d500800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 547029946 1250 547028696 547028701
    0xc150f07060e1018050601060206040b041101030207060e0c041d030708090f06041e0e01150302030901060320091302011b0305040305390109060e060f0a0e12030306030c0108 76
    0xb075403074030b0303180301864207203504055050107498041e1004900320384c050019100300b40e803101c1017641e40d11410340c1c00800d0400150f00007004a05400c08410032030341c0501d8054a0b004e09501d0f0801a80c410146404454014031038100700c81c90180714800440d500c0300c2c00b07001d003440003d4500f40c99000d46031002d40400030001d034044003aa40c1c2c1c0030120103503400501682d1141d88511422141100301e81440c1c540a20150020031031b5400c103070840c3d0480318940d840c0103021800031000c0707010303420207480741649648500d00480015102ca50707100070f014400450900402c0e1072802c000307807403a0140814211005c0400c03640c01507640448003040480c0012480741c0105400d140031201c52040e58009411400b841000d00341905018800e90b1b03445109201d03213801c0050404070485016180d46100d80421648082000558002c5640e030500d40402482e090501740c40c02c0500081d6444010282c00140c3c0d407101550081ca02420f0400c100d0041d500118103500d00b140c0400d41d12841c0e40a45414071115100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 547031196 1250 547029946 547029971
    0x51f0b0a0302071a040c03020913080a03110c0604211b081303050129040c021f090b1008010e0304060509151603080a05090f060a05070314090c150f0706 67
    0x14030f18000c2c040e007400030b1445ca0141005580103074180030880c4908036400c00302e0b078000c1088128140d03143e0841449864815000000d038007c1c0007520341038a1071746c82400032502080040c8840c501c12070090412503100c0400340b06032940030b40b24640000c18003800942503c0d03c0030441610410a95000081d02d94600b0380c06c1017075a000c455640000c1c403035803c008869464200454000003035a040c040c0102042c900007081000350b810203ca1100160300405440444031404011a90b001c10010f100249040b1142c41e03540184400321005d01e01d00b924003100f00040c035030911590210400801c05075060508000c0018010f204583e40c50b841519034410962a1101940c12103607402c0d110780c403941180043e4900540b00d03003001c0392444c2c411850309c1c00140700000d000c2800001000041c0142015a841c1c40c1040001c04026100c603080640e500242a0b03d01c80d4007030079034024502c040003404441183c204109000201c0d0b04c1c202ca81240611030340001e80d42071000d41c3c0c41a0b0380b021001c22001c14116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 547032446 1250 547031196 547031213
    0x1303081308030a050d0b09010503060f06040f091a01090501030c06030506190920030112060e0309040e0703061506211e1e2a0903080409051f0b0a030207 67
    0x40001c0d074980000142200f0041c2c01000600c10303030507075140c02d0040740340c1c2ca4200800c40d4400d00c40e00307070941c020304002240000240071a66111030001c10004008100001c0b410864051a9044400060f1910710360031010081c04a28010301d090b1000344201e40c116507520001820f00d1007500145911400031030000e81d507000c040b03000e405400d5100c50350250742c2c0321614041c0c4241c04903580380070850039105c070200310a602224140c50301510b4680c50101d241d030303030f040040c2954402d1071b23103a000a00c42c044d0260303a03a02805800d1609140100300260642c100741085401c039070386142e00050503040c20050b454000d0110401c81d403048122a02c43c5805800ea44081c0628091412070445441c045a0260010354402d4480b19030000d0310480e41e4109c054841c084502400400380c454010b00400c8103401d8001e10340b00041d240c58a407207a60a41c0d80da450416079049900311f043c1d4251160700708890074210f2900119000c1070b4201400c12546011058030061107500f0310481090307000940d8105028282 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 547033696 1250 547032446 547032449
    0x807021c0b040b0105040f1505190801111903020c07150203390606151b0a0807111c080c0f060a0603050f1b190306021303020f0613030813 61
    0x214103401c9500e8146000046400300f4010341e8421490304a0807070001c4514400d101000700c82c11507200c4002d0408081049981ca08085403043c18041c2e000410038100a00458203064030100d06a600c445220202070407402e01040601c08051050150300d403801e400040280407941c10400745070b42c484050360304900758811710781072810711004842c41103c00d64444070300082d2101103c1106003c544180f45581d1540700135a4010791058070000c01d01072000100f40107040301801d0014950a00ea440c2084e00d007001100003082d5021030010405038244a001c40002e000d04004640d400c044040c80242c005080340f41c040060900007021444015a010801c03440244440b0300c0c003102c040f4600404840050125400212480d001c0d885001521b0200019510f41800c402420701c1d510424040c03e10240350b5141c43c0b1a00b1501000c2c60000120b62503200030140d4000c03a100c0ca0382e4190650060008111040e034000d0f0080d0070810081908000074040c03501504d41c0000304565482c030506124581d520617 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 547034946 1250 547033696 547033703
    0x1207120f090516050103062d030b0c1c09082208010e10110406020718180620090112050a0e030a05030103030207080115121713170105040807021c 64
    0x8000300300042c0000050b0b0503102030b01442d0784005584d140e00044040e613609100d8440c000c250300d004a1105006a1188003030041d050012044650766611075400d50507090703ca01000b010002600c2e641c4200c3d02454135110a1500c0083c80a07240c2135444604c00e10030040540000035114021040110902280800800d07581c4000e00000c03080317480300e940f40e425100d0f00c0103070701c1d180412610140440b08141c4013181d40c40c2d0081e1040f60f107840d8080700a0600da82225211503078600b00007002c0101821450301160055200007044c24843e001c3ca01480c4042c4040e4484203018800150a03a07806040242d25458106c400b06164440e000312101400d68241c401200c0d02000c2001c803c0964005d018504a030302950894250702ea48000082c2210340306c04412032501c1c0e0354081032120503003410944c044284540c08030760a4a60201c2e0403692500001d5400c04c4500c0e0b814800c110003420201001c20010a00000f08207900701662860454852800000c0c081c036010500c2d2003484140280c0a00340c940c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 547036196 1250 547034946 547034951
    0x3080a0e12040918151e090c05101103030a020406030e0a0506011202030a02040e0a05070e010f1208090a060203040906210f0213050406060501080708160302090604170102040602121207120f 83
    0x11100d0001030324090030322a80070386d00382e4006080c031182400f1341d1400780d0304a05008d45440c10001449140c0101104440034480780703074030f5001d41e145c0800084d172184200c020010b0b100c504110008041e54035008251142d03900000800c00403d0303001c00c4450440300d516203012a01191071000c2400c1c05815a0040d40c4545400c0703c09a40340004166001483d01c504d0546110300d49482250b800080b0a00607280b0b2100842001d121101c05090f440181900442440742041262000604e00c0e0840e600102c005030030204041189100c9406400060721395440403080400d941c000c0c14603d80030760700d00a809118210008020b54882260511804d02c0f1720800380164681410100082d0060740b0501d030001d000d0100045842d441900b04d00c1c0501c14010021040025140023200650060010191701507810080020300480040400401c55403000015842d18a020b4029051a0600107012020360041145000c0b503140181500c1c3d010303000341854a6030f894902c0d8058000c00c00700f00010032662 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 547037446 1250 547036196 547036223
    0x1210501060308071e08091005040e1501030c030b031c0905030709090c0b09011e1e0207030512040b2d0c030c0606011404060e1203040303080a0e12040918 68
    0x5090005001c003a002d4100e0b1105003032505003505c04074040040c080c1000201340300c000d005280004a64030002442d1030700f5030510703454010070103200d06c098800b404003015602d2000c50658260040010f0000c160604014424038840803945440010380089801c00c4204801d4000901440c1c1007006000302808883da07031915040000020200088283c40c005280c0500040300240d035400c40f10001c00607500e0304403a0b607140d1801c0d002e03003554140007018080d8181d107085c143c5007400700c0350410b00402c0d030081c0545851410f006060042c83c103154400100e04100900c0f0700d4041b5011104e03a01054604082e10840381011355058444580a255000340c001420800c3c9500000103010710041c92016218240c840d03a0040d520a0040703c10010440e00c180000c001c6c2c81e00135000f013809900042e01800c02101c60b081c02506660168000f1004075071080300340140c0c4c585511074841034100c0e200c010b207115590342e25a410a07003d10700c1910941525812040300c0e00089112138204a0f5014803200d6088 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 547038696 1250 547037446 547037453
    0x1715010c060f1401171c18091802121513030509030714090a06030b061512070503093309010e010f0509010b04060b0f031e071d0108040b012105010603 66
    0xc040031300c90841c940c402003485d41c205041c0480c521030003038504001e0182d004c41d04101554000c0c6008140b0820782d0761843e000034800068010000c034981d9040380b00c0c00d00d030071f00e104102148480c000106400c2e40405801c11690000c0e48215800103000b008c1681c010705203180440b80c80c4a0503c5a0b501401140300c00100d09044099100c040d05046075101c42c540d803200e01d007100316102c3d40700c0500040c0305440425494101003506061a1100308540c82c034028102603100e010030001e031f0742d800005000104005007c9414480c2d4010070b076090f5004100244c80da5651002c921103200400508001080480c980702d40943c40405000e01590084c030034184148408002800c0c1111402d00741d50905542200515152107900c1c00d03030b100105554100720340c1e85c0301403c0340e800040400348118242100d010186100d00c591510401c03250352111a5929511120310b030b4610f2404850713060000e56414040001d44601c0304905668068101514007907c104007460580110070014000394a85480441407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 547039946 1250 547038696 547038731
    0xa09090212150423070b0f13030b090606032b0e182202010212030406090209090a0326130326010509010f0605030109020f090901080c011715010c060f 66
    0x254000d100c0f68084c880c003940e950344c0710100c02401140f0354000610500c04490860b028100c81d0328050901404c1450006502d22071681c0c980041d501300703411504005100070200070b2507a000c54142d01620074001803144d0124a00031030700740a60080349078217112400034400c00038018070100040201c1113500020740c1d020042413003900c0c5504018402000c40500109892124205d254180c1c01000414400308840c2025000600702311051a1110900380240c0d0700e41c051640617404101c05024406194607014110300c2c0d00001760110a512240c04291581e585150154407200003401d044203950a807608070b507105142201c0ca0900d0a00700007000820b060400c01a041c0e400a23500080141d0300d400c03500a66412074450301700091310402c01480600525005020944040b400c0c6c50b00780094900000c0585001b60402d42c843d07071095218641d1340d80c4c0451f440688000032140000e06060508030000403032401d804039418403002e00100c0080000560050030b200025800421911940005c0100e8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 547041196 1250 547039946 547039951
    0x20102210a0f02030414010f1104090504060204081c080610051204030c06020c0a02010905120d050c010e01140a24170f0f1f02040b0d0c030f09060c031a0a0909021215 73
    0xc10b9803030000d02510b07180322341c4100305181011a100c0d130304041c9001078281c042c000c01041200c0d00b940920002132003210410070441e80d8034007001c449a407925a40e40051078400000d04442c4036600c8194060000c5070400d080755a8031201c1d540d030f6a01580c07035060540b00302e03081102c0100181e00c0010030043c03512000c2a883c20300b51003680c4070400e0f190741d2810031100003140403207103083d50044494980201d0013100109941c0d4520400454010904840d25085603189090300d8500c48007013003084007000d001d200da6080f040f00385442c10f0b2952520322600710050480d0203040c000840e20901982040d40c20495000741e610400308888200c282000300139184d288841900d000c0c0b2001112040a1130f2850080c0c2c2e040c0c45154210728202a906240d5001030202e05d443c00003496500c5842c12421803080c0515104035009010104287d9070112000b4101c8a092810030008075001c0c1d2656a20760340c01010408440c100b29001c116036220f4000100c1c800e0307820324103880701c2c45210507140024070420516407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 547042446 1250 547041196 547041233
    0x1507050c0111040819170d0c0e04020c0703171b0c0307210201030506011707021501120206030604020708040e0108010e121216260603010b01020102210a0f020304 71
    0x112005104002d95540550300400c5190b80005581d00d405064894800304a54050a1090100308540300d040c255644041030401941c0d03100d02500301c606800c002d41c0c64030b400c0c09407400c604d0a41c2109196844881c1d0340030040c40308000d50420510244034409966071030100103083c68407880e0764444150340d036420084541c001e014648000031400d5181004c10302c0b091281d44c131100c0082007a4011802040020800ca05200010070300c0c88120200100e024880d0b4980c0d001009550014100101c1c0c00405910144462510004440c0180c82e40e60540f03030031071000e45c0c000d07854031480d1500700360a00842c2c111400e140043c90002500307040540000b00e01202c0402a21840a024036807102036100d10b0100300c02e8075485a02168100c046226800c42190203890540d604007041c03828000102100200800e0b410369078824041d840c40e00f07110340300c01e11509000840c03a03c0344162005013031810000342405002c91804c0080c44000316a0010401c562604008543c4da00d0103207013030081d014807000181d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 547043696 1250 547042446 547042451
    0x50907081b12191401060e070206070206010e06060406030b0d0512031e0411010f02120409060501020f1605121c0507140c06090d060e1207050d0206010609171507050c01 74
    0xb81c1d00c200000c183c5120507002c50080d03440150b01d44c1c88032101400b004441451540da101c400003110184c2015036401a0035540c09400c903400c5c4000c009140031410303040b03c019541600d0900001d0795402044500702c07003040c180441d80c82e11034000500000c40c00c000103411401081c400c030704000c0a1000540c800d5404031128403003400c0c01c0580c5031801c0c404850040c4484050003107803441c0c0d0f02480011400100c18811140201d04280e2842c4a641181d0f010403040c0e621b98078240155a01440b50421254801c80202000740b1007a031402e0703c07204603208450150400d03140424100109108004101c0405920548400606000100141e0001e0000d0383d140c5600c1a101036140404a4003440740c01e001400340342041d00b01c0080150001c4000c50803030b400c9566904800e0b040000740800301700725680c00f4406480341d05500f0010b0800c00702e112034000b190040700c014441750b07800803100408d442d01d1101143c2c00c12000c100d0540343c501000301d0740140b0b0500f042000309065001c00140751000f0210000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 547044946 1250 547043696 547043719
    0x50307260307021009150608100c080c1b070801020f030f07030207050a020609180c0301030b070c0308150d060e010e0c03010212150f100507060501060c0b0703050907081b 75
    0x3000603902054900c0001a0000107000c11300c00415001009118001d04014850843e50b02e9a4002c84005512074400341d0841140700086078214070400f11000c01c0e80c1008030492a014507825024070038040c00890040e40c0d001c0c0c080c141d0750100a407801070a4240000c564a445d180c60410554004603030350030316104c880c00007501d05031182c001d03954030300c1d4404010724826040b6800c02269402c00a10300703400c4410668800107050414000324058103444001a0b038035415030600d44104003005200005121041448100090303000d01d0003640000a1610201e0903203008000402c112032004026084c10b050a0541c0c01101307040d800040700340401011500ca04260300c3c245402d0b4015040194502219840011034500c4c205400100e180401040c0c0031551000c44000b1f00034103201d4045000180d804100c03001045401e209645c098440740c24070ba03114209944da40b503c20303071008021008064495002c602c00080c204500d0740644010401da03582c203605d07a80303210f44199a042d0501c1c0320341507a404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 547046196 1250 547044946 547045013
    0x5060403050a0b0c0c1203041e17030c12090f0705030d300e15090106150f02070503010608030c060f1005010518030604062405030c0f0a03050307 64
    0x12101280d5004010708070031000e41c0c03201040c076040108186015901002030505140052000f000d601d00619005034881c10301e803d180402a051607020000c41101c03145110105d0742d010706201180e018501d5980c0c0e80d946070030b441c074524002c0c0c2000501c4401c1120600403041c2005c1012504d880e00c06044904c916a00c1007055500c001d003600303181c003141c112803440c2000e850184454010030801e11052052484003506c0307504640102e128101250886d500000543c000301e10000d4100191100134402c950a0103640622804008080818851104103142a0368001e0103003000030107008000708140d82c1d540301c2c00790310703540303c009168801e0290000184908403100301440c02402c10000d520646030401c0019119039000c0d000d43d0a01c26034041310518907039000c0004a1181d48160030106c4c0310400288404000a6280b000c01408400440103110a4500141030200108221401003000c81c51a01144901c1419003010f4818000050060140034240301742e81061809401c20308040c080610 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 547047446 1250 547046196 547046209
    0x60203071b11010c08090d05030901020f0d080703181b15020f1507050421020f01230f0d050f0403020d170402062506090209090703080702040c030b18010f05 69
    0x10020080d4004400d151090f501c2651140c0050384600314407840d1468000009884088103441102d0540c0700041c80609541e0512040c002450300c10010b00b085070560501074030800c00200500101a559900381c2c0c001c140c1c29500d444c8458014021b10801111698a2103403117100e4007410100041c8084400c0c01148001261480d802d40a0f014107081240702654001044004d0007210800406100100300c03910803803400080026210350b10300b010620351040c004e0114401c500241400b803220115075208a240001c0d0b000c0c0300c440801160780c0c40001010034054003c045450700403a285c0010001411050760b6410300940c041e400701e4071500314a40003110040300800d280c80001068401290041c2031039809071544255080f46040e070404081d1842d980c800c0381c00020ba507042d844907440019402d0014195820450407006003441900b5620703000d2441c4200900240111b907103045070821a03200c0d41c002d12541000802a0001200d22554400039100a000710004014403220004d814034040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 547048696 1250 547047446 547047497
    0x1110906070f050a08030901150f061b020a1a0d0f0203040302030d0504111f03050a1a01051b060126010603021e010e06211302061c0f0906020307 64
    0x2421145810010303503031500901000d42e011121845442e84003000200101c02861007800705030300010b0301500c00003040d8444100c9a0042040400e85a810301030a070740000380c0a250113121341d1814000b2058404a2110700082e44504e40d22000d920112058500d40002000c010006042c14890039060440b810120321003950018056881000000207085058200a41c000e0143c82184410b80f20701d00465442d800ea2441c007040903944a44003501c4c19018032407140c1010032541c0800c81c0100c2d20882c00742d41e100300540703141400b5021a1001c02015540f44082e1003140c1d2805864095a507041c03245c564051307601c0075200030300382c9210800c07801005100c1e80b422282c0003880d8003861000f204c840100d150000807400e04000b0000442e82003520f843d00103000c00242c20501c0321007a1101c842c4040c181c03c010341120200041c5240d2540565115030a50382003540e48190f441ca1296400071800080c5980c520344003015044c05519003d004584d03000d14400c0c0030a4555559041e40c0354600740301109403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 547049946 1250 547048696 547048699
    0x60d0c18150c08040503010f050415050114010c0203030418020403021017010e13020d08030901270212030c01050907060806010320090a051809120f0711040b130c02011109 75
    0x9442141c004610521903021854041e005842c0741c40d444401081c00c0d507505080c40110300d40c98200f0b001c00c10500c0c0341940c550b42c13105942005154141240030808146100203a8100150b5142d4241075560500450b070080c50401d52a0030745882c0d0072a0070340a5005480160300c600c8034240c4c004600303401448011b6041d10b02c0c1480a43c16800c11002104214002d0200705804000104500060704c6800f4003500f51801107003516202d00e0044881400e40b10403110305800c0b81d1b001240790ba15108174800c1c140d11b003541107503204000f442403c0d14501d54060701819240c00e609040601031107000110b0700500303640c029070380c02c661540e5100064050381e140b5005044801c1961381c0c46107060010300c0c0030700034041000340080141d0340e0703810010340d900c00c91916074030020000d00140900a1000c0001ba40c2c422441e060080c1440510f0440c4615406541c001038440100b040c03245810b0f0f030303c0d5841103203a101c000b0b001c1c2c41480e00c6100f801e0002d1072600700d0a00503602e0308180654206001050310000c030700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 547051196 1250 547049946 547049969
    0x3061608010602122514100b0303070506190207021011010507030209010813110604061d04140703090f0b0403111501140d080d060e071409130507020c060d0c18 70
    0x9000403000d0305c5084061604200072404142a40026400300320048180034010040007400d59a0090b14101e030480f10038244a0b510400c1054005000802c03410f0b4000c2c08a02d50a174050b203400c140c03e01900c212100254088501c030490820700350001b28014640340e0410080000d40d44003c0e050302280f01e954000f0b40802c10f80c00001d0402c6211125140065100d0031803030420098000200740700790460740200300483c0440213030080e2131810305800552280115010b02080001202d0310041c0c140c090014010140c0b108142c00500c88110f44132403107560300c60006402ca00c0d00d8200107200c00890704281c1214000c00c0251445030005140c460f0607141290741664403800c40c5001c00c40413030034004084910020a0050301e03400001d42c800e45008005580e1460707160326104030700510551400088020391002408400f070107407a41d2000e200c061800d8580041daa07202c00707000703034030f402c0030300c60055170000000540c0303041903031250000d02c802d5040d503c907000300c0c81003210801c4010b401405a00c82d0f462 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 547052446 1250 547051196 547051207
    0x20403030e0d0309081605120606010c0b1510111b0a0504020703090e0408070201180b030f0403170403120b060301150f090f03060203010f06080609011401030b0306160801060212 78
    0x107450038445100074440e040003041c080e9911101d0b400d2448120311115010903500c5c0c101f0940c1042d80200e80c5d4912200081c0c09035150400000c0c00c3c180b68200d000d0311484200300002c0d040b40d05d2228400c00743c030004041c21000f480400c0c1c010040748600c1c0c101245401544140d0340d444407075000858006078000d004001071b030300f42801c2c44000d40107000150200045003000103426002340e01c08501403400794030629070354007a5000240450310040d610213092052071004200c4101001e01341c2c2d1700500c40c400d04001399240c600301103502e03140300409080210740200c1808101504403e2a40342d508262406001d02403501c4100540390000f440342400055204440100b418440e1440884060190404580303282e181d203407040c40b0550796042155500d43c0000180700b8480c4015040b0010070062505004902d02180440c0a00a0611400e502c0c1c0c043d9203801c5085a0181d0480e0901c160302804899161410003041405011030b0565100855113400021171f0061000c80d2926609100401a62422 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 547053696 1250 547052446 547052449
    0xc010f03050c0d0608060108060138190305060a0602010c120203060a0f06090e0c07020609010e0f1206011401260c070f050d0e0103061d130f140c04020403030e 70
    0x3004010551014042e0400c1000d806003c50312504002c0c0211600514056050252507071400ca01078024118102141c0400000015a82c1654a90b400560039015901401c05030100450081404c030691049076018011002549540814030500701124038075131a507520001a8201c4207840c080c14002024021810700700c0503103130002d40d08640040d16540c080350780c640b084503d02065800140004180c510204520400b022507290030044040905282224130307800a040c43c40b4811000c0d05012003001e07102415035407502d6004140c00042d24a42d80d400304c000560352105402d0003100240b84410850005a5128840000300509038a01e01440b034600c844e014100b8030001020b80d540540200440400248040318010b02036200d240100960866517002800044421903c1410989802d8007005454580f900300c40084400e03c00103010368461206510390940b1540c000340c0902d100d2001e50081002c02c1d9040d40c080520401500c1e13002100c5020802644954840600083d01d0300100d605103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 547054946 1250 547053696 547053701
    0x90411090f04022208030705060609060a030318080102031e0a02120c070807051603023c040e070f060f0503041a0c190f09050409080d051b040b0405010306080c010f03 73
    0x40b800214100010426107078213011020a050308244602d40022582d501000350420410303400c200101c55020042ca414070104004184511020b410028030800310806000980402005004804001c0d9605d1410081d0524450b4140082000e042803080004400804178420360340c0c0c3c0801d2581c1c0780394640f502d203201512508040c0c030a4440840400c001c00000d0001c1101405003407040900c40001032860041080e03a80e150a40d4042800d02c0a500c03140d4408410464240d841e40c10035241c4815440a0118004007a0442c0f070280b1807180e2440440d003c007420f00d00408603182035843c0101044110300440f0725000a80303009004001d03192420a180c4d0b00030841d41d51003500d040c18281810300041c55042000d21105403500481c1e54120b075402d80951260900c0003804094800740050000d95490750b40e10b00c02d811302010940e6440c0041610003000e060f02001030352a400c8040e4540e070301d540d8410205e078804e10440e800300b4504100010a4132001c00d409101c00d005071500300c0e0080c141902a8003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 547056196 1250 547054946 547054957
    0x1e010b0609040c1202040e1e040b0708070e130203090d0203070507140d0609110913030905041505030715020d031b08041b03050f2b0e24090411090f0402 67
    0x1802401c004c0c9078010f9200f84040d000501440c4041c0c4150300f00392220400c0e42141c074948250794000034003000089864840581e03000104d17407505680640d2400821100e41e5451154654881d01c054840c80c0c0701c2950b43c0185000721030750030980c0c5140ca038081c0c0503030362071255041c01032080d04222404c10103803042e0000d0308038492024000903a407030b285070f44100407540080c90864203001081d03a212610706250071800d501c903030010010031551445072005800c0000c0b83c8651441107480e911841d03041c1040d610030000030040501160340355900d0301c0301600c402030b8091a680c0140b08200a89210600ca80920954a610303210b42000e5004100822030300304030018070541e030309030036080032a202d0020354085000450180f4040c14000e10610481d80c14468000010020501d1146e662609190304070710011507a6254200400c04140080c0420401880701c074098104030000f0102e1095070913028010101604215001c11040c03044112039201805003441064119002913080d20a41c103040d0700604 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 547057446 1250 547056196 547056221
    0xf060b060409021201060f091412030c0604140307170901090302060406030606031d0606121606030c0e0a060e131b0207030b010b0a020303041509060e1e010b060904 72
    0x400189110100300240e0060748024101c1e070740000e00361a80c401a0681030702616032032408410080c07400f40d005082181e54000c0d50031142c4001c40c40c1142d40c1d258900110320315a41c1c0262038588107821030164507004101d03800d40e40c00d031007410840d500e81d20100481c1e030030329400450000c0d240e54940841040e40c003c00901814000d200401001580d50100030b440182465070b008034000382407603001400d58018140640c42c06000b01e9000c004940e02250b2580c0c400c0d4252001c1d046c865030382e0f646a01d80500c20f0101100d11182441c0400c2075035060f080a20001241c3d00c0701207941e00c801081c40b0504145d03101e0f550000d907441254000c1c0e4604145603c2070030301c4807500818840c140304803490554491551910159005110410800009400b40b40c01440308042890411007502c1c4080d40b030b440000d1005120440c000e4203000c29030555401401b195401c08000c02c02216091452650354841608002292581440012003068140507401d03100c0405420700703083c800c0e8103003400003406250b1440b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 547058696 1250 547057446 547057451
    0x5100509010e09041b06020118030e15031e06060316030b060c0102030a0531170f0a030902190f1502071509140d0323040f0923070c0f06 60
    0x5403a983e4491090718021409145140302804403610008510099039001c1c0055905000c0c1c0c1d070b81600c89009650304181d801d400e0211400200c02d00143e00b059000c045a4202040801481400c100020a91401454104171221103854403030421101e40021214080704008079492038004902c01d07013103c100c3d81005065941401d000d0271703406007aa0422142954100c1e0b0302c10070070141ea28000800210b130384540012280304850300000552071720174032101401001403180d801451030304410440e00c0300e80e45268503644401d100c3c0801409421302c0c0030260710510b401c1c8049084108014000800c40701090903610040d0704d00074000359501d0b80b46400c0415402521800521503d12801c0742c20307a070416544005070682401500c3c1c2040c8004460140035640e445110030009402400314107140309040903840180407d468886803d2046030170072100300fa603844002a41c0005070300201990400300d6880e0052411204003e030003000101d032600d00168109083c2c0c07000c540d1040d01002828080c1d0400f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 547059946 1250 547058696 547058717
    0x1409040215160308101401020607032d140a0e0304050f0411131a0708090d06110c0114090307030804021e0901030f150b030c100207050a030308041b0510050901 70
    0x40148140c2002d00a50228074107108001103d0b501c1002e0001030310300084402d400c001d0100000f17655000c02031940c001d00d541c442c202145828145551481c443c4901c4c500d1803800c500740398640107800300084400441c00c07034801054050b0114010320030103210810003181428034003000c00107420b0000c2c03205900941e070350b0610241d1016000082c0030065040014a80c0c152800315200119440700d0201c00c0500790a01141000441c41b0742200c0c80000700703c0329048581c00c01e003001c0c3c000f016403500c81174a9101c0050792040c59801034116502e0303440b0f01617008010f41e58025260382c4070721070b40c08024000b40c108000540180340072401c0b50990f0169602000030200488045040c80d042a017040d940002e1500e0701500f0440d00c0b08003070b0040c0b14150780c244003940b64072010035562070442c003400d403203000e08103100e40d05d451003007044100030000146405000e5940c0c2c28045c00c0e115059409072240c112806044680002800c180c1044480c06030400c42d00030a1040200c5080d00805006410041c80212 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 547061196 1250 547059946 547059967
    0x120b060405180f070216030b060102160603150803041410120c080411100903020108070c0512070203010b060309032b0504150b01090806010504050a06180f061409040215 74
    0x10642c95142c4850700b29035050500a840d00c02c2c500819180031540b00c1101c20380d10600310b0304c0080880783e2000000d02c0319100c500c0141d09081c0303201c0d140032507466240000249241d0603041286070400b002c41aa40c402c1e00c80400945910550280d46044041500c01c10024100380180d1000b118040c500140d004100c2d82041301502c81400c07400d80020381300014442802458903610600140440d2100c02c2c0000d070f000007070208501d910000c1d043c080004001f6030401e00072007183c0d2000303a0102c01d90b090403c500091414940041d10140c2c040d6107002d4400080d81004421680941c10400045040040c800c980f403c00064095041d00040a1032171561451251800356500880c807400c041284030100b54204021250342100d018100403002004000c1c0c00c101261a80c1559070540f0081115511134100b100540700d141d200c00840710084854184107604c991105408409180042c0302c403541e0355010388403400301000c000354007105203400301c1c00601d0940400d04040f10a00000d80c2850076106 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 547062446 1250 547061196 547061209
    0x5010918091e050d05090d02010e0102030c01090507030b01080d02060c0d0615030203070e04050c09040e21071a0f060d0201030f0f060305011401080d12110d0617010507120b060405 79
    0x40707400d40c503114500e02e1000c210040c8540200d0600300d15185013071081901c00103491a0010a001c0d0501164001c80c01e2580d2080c4201d81201101034000c3c8000c04040c42c1444da649070034841500c8032240d6400100302c184000c21019103a2000394020b100c0e58a0384041520b085e0301056050764041e60760080000e40302e8600803102109030f11a01e0045e168602600040d14583e24064000e104070324200421110042c07010540e510710a00717603000140052104481440c0032120714440c002010110800c02030140c9100007021182d11800540246804d0406211904c11040e201090786184002c00281141810004211200d0051402040c0701030f800c3da4203821a44807454092030a511010180280710f0700b4001d8443c1101a648400d259600d40042c0c0758071030602c0c1d18800c0800074030120400c1c040727074241c112030828662008090756503010001303080010100c51007644080e080c00f0706404884d04062150a11817078098440429148602a00c03000910712203c0320b55105005003c0411035803102d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 547063696 1250 547062446 547062473
    0xc0b0c04260105060a03020a1514040e010611010509120306061201061e05040b1206180108060f0702011416031d0309040506370306020705160f0501091809 68
    0x78080181140c410000d0796003035560041c1001c2c080c04c201d8408100585507010000700308d4034214601104c034440b40c072003146c0f60b01507159160740ba058041804100384001c200780504a4840d42c85882c0c5030102d2030039050a07074408a4001600760082c00013181c0200e48a0010340d8040002000e5070702c3c0c071002018440040c0d2003030300070300006070101414400883c3c01301440745050905050003420546801030003c0c0c680310b600b510b070b00b00050040104025480311030701803680f240c10341201100c540c0c68016840d03840d281201d100a441c0044008900c0681c01842211a0f411620701d0350303111591228003c0310f260741c03c1c481039000c0644d10350200c201e60b0040440e0504101d0258003943e511209181080242d035000b901c3c040c4100c0c15142c0711320210036240001c00c40c2c6420300549050b80b03d41d0401c3c0509000741584064000c90002501008100c0701160390303030884105003449080340ea00c030307020220f1615041c09000d01090142c841802282c61a80c6150240201d00070085030310001550b031810790300400b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 547064946 1250 547063696 547063739
    0x20610150c23010e07080a0803060d050102120705070606050609100c0302190b010503070605120103060b010c0b01060e090109110d05041e050609010e011b050c071a04030311030a0c0b0c04 82
    0x4035045080504d6051141c0e10092941030014000000961101103940c0700c0600f080b44265080c0d03810100300202901a50810f01c0c04407100401844c0140000d080c0d644040812680ca40c6403000c0492185054025200d9070f48024114800c40400c5501c10f03a210b140c004c000343c00303610440410b124031400345030098640718442c40341540194500002d06250135120f410640510009103d070003190032948210b103044a800c180d0214075030700010b005130340c0e01814040c09084c00f0007417400031943d01d40151060501d4030095034082c48681c1c0c1c500c0e85070220769504140b082d11000411801904c20341c0e580001b5049800303000600301c60000a80c04c9408807d0b408409c035440c0d0050410480410000e101c1d80c9003600009000380209101d2409640c504044540403c05000010442c031030040c038204007140140c0070b200d28090302e440f0443c0008000e504540300413000201c0404101e00034070000f00545000320000e0b00c91034880300036940c800b41c8855000703001c84810401880001009201c40c1c181e56a444503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 547066196 1250 547064946 547064951
    0xb040e0f0a140703120f050c070b030103031101050103050d03150e01151101090b07030c02030d1d071d0f06030f15010906320109030c080d020610150c2301 68
    0x800b854141080c4202e03019940039500311000800114803244c500c4844402d20b4900042c824030201c40a807403501450510f41d4144c0310b0140081400c81c25a8000c0d81620301035122680c04d00c50b80803030607081c0e8600740002005074110040e0241c940f8001c3d041000c00c1707420310803001e000079124540150600000d9101c00b000c1d6009411042400d9001920417031455039180003440154a030391180b600000016000c04101036541d42050003d07403080c41030300c500079480601400f10030798800c880c200c0d262900000302000c0c02303208000100b615010100d8603580c0008903d86040d981c840e207070445040c00c010880d503058000c039032441c0d080100601c40b810000e0550003503421503504105940c403c8401039040300060300d0340c0ca0100c1c50151401d62035040712040e00041d01c004002001c00481d03a0100550006200104440d030118240b440400c8880031301e8003079800c5682550364000c101c0c144488501c1159400303d0340c1c050248505220390301180ea01802903003410380e591803442d0404580d0680840002483e503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 547067446 1250 547066196 547066213
    0x60409050a02030417030903120a180c17030a0804022403040b0907060903051c200102180d170a050405120303070207060e030c09041a041a06220b040e0f 67
    0xd0703100400b8400e0040662421440c2c440d030305030f907684683c2701d4044040410800151500e103042d008140006a47c0d1b02c119030800c52442c100328610241c1c0a007464100031003028164041c4000140e45901d02c00345d44030300b0b15845540a01c40c524003041c44140c00404c106500352007a21600e002580264410f4003003151034030300250b616003055800d130058010021402c9081010550005170380300006000084510b6000d00c0e16000c0c6c50960940c002005d030750783c06440200c210201035024000701e69180032040307000307160781041007004150030a000703010b82c03080315940011404144c00b428000070b460030910314050315100080c0031107184d0481086642d00001c01c00c151541c2c148640c0c00201460f040c0f0495400c3c0c40320010762030700700c2c0031a000c0c01500090000b4060202c000c0c542050450b0100e540c00c11801c1c5810702d420390942100e0b400e419051a00b010400c1c50034410500c001d103507504070013100405e102c8070059010344002c50205501989403034420303005003030074004030f0300c4800400010324845 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 547068696 1250 547067446 547067453
    0x30c04030c06090501120b040b030f16090c02030714070909080712230904020d0c0207080607050c100f15063501060c03140c060f160e040209060409050a020304 70
    0x12203582061041003a40c2a013001076981088071803c02410090000ca481e50055011030f0040c2030803002194944162000c1e01c0300d000c40032134480100413000800c4003d10707031565056001d4444035110400142e000b00310744404120303d48170003600c03e0511415200c0f00b0740e0311406282610f40300031094902100c0040c01c4005c05c0391820071030740d0f10595414541001e43c0300310010510003000c10383c07902d070711000090910060f03984c5a0407030b4004941940c0402003190a100d00a595642600880a0340d2142c9004500a64040e000f5110100c0f0350788010200c1c18844d120070030242c202090b02d1a07078031b500d0341035030347c0d1500002800c00083c0c529076803006002065200b0000d1180c55041302c035016181e0060b121481e9034030903641141518010304145070302c0d8a5a1608945a26100c2c00c00c1e041d00c400072880d800f1011020a41a0155161824055054a8018a0b107400180341c078820801b02e0801c074020403c2d8100794004c2d0264500090480e404c10395584100740546008560214100d54008100000c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 547069946 1250 547068696 547068713
    0x1c02030a0f030b030a0816020a090f0b010206010315090c150c03031b14030417030a0207150203190b01020c130501080f0a030807030b040b120102030a0b0105090a050609031002030c0403 81
    0x10705081c0c80c040c041040401c02194590a000c6409401040c0005481c125110903030180a00154054081c00c986a0394440700c800400641410300d281c0c605003d207800725988001181c40c16250840220450003100206043c000c202940c2c1c100d5070034080070030001d40c040e241c0700000c101005540f10411704004500d00103045822000c0c41c0c007900741c5a80c3d141c001c801d038170100318000024600c00c079035900d440301d003881e01b003007210148030b61141c010000803c640c940b010b8020f082560300c1030140703c41c0041035050000c240d010488040d1181030b00301804a000e181e035604034460408060056410242e02b039408526070400c403441780c5c00010f44a800400603030a0030000d07244101d0034400544202041550700801c1080040d0172202015200d82c0020090380c4c03682d0088a080500404082055000b243e00c6c5c1d010390000c492030703e0800e25000c002d281550141d401c40da4860001000031900c43d08007010000c2c590096a03000b0b4140c4511080303440303800007038401140030344c50015030503450f00c0ca0740c41d0880b003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 547071196 1250 547069946 547069967
    0x30c03050c07020415050324061512060d062f041a0c0304080a03030b090f09031b0a0501021b0d0c03020303011401020f0105010905060a0906050901060804051c02030a 73
    0x80529040030480c6141d4140d05030340e00941d044401151500307804204a04401094108680c58080e000c402c0e0800d600e4101c03804402c5620340c02c42c24140e52044100800201189501c900100081082000d1581c0307410201e036010704000c0500451072003d881b03140c1160084c0c1811582488000c4000d11000700154428140c0d03c83d00035801d2401d410282d62000c00801a4600301c15a080850103002c0b0540610982e40900034001c22104541c00030300f00140540032580800d0300516614000c6072071341910440281c03141003054000c1d4074000380a599900c8200020b00c0300703d900d029403000d00c0d0000350280002d00c0002d1051421419180c4104021810085403000000920802c0d20b01000001e402000343c03811a100e20605681c8074500000507400c020011410305c2c025440d220000c1046034083d40414003642c000e60f15076190a0303c030070042d81114428028a548070254000400ca4a4464044030b64014400c0c8140c60341d14400114030050064220008005030300041910021540e00012011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 547072446 1250 547071196 547071221
    0x30f0a03121415040b210709060603020c120a0903020a031208010b03190c0c050307061a040902010c1101170f04021c21051b010911030604020109060509040b0a060f03 73
    0x103042d82004070241d01070000e8100028095500c50b540d4115030ba4411a01034060184103803500c002061000015861342058003036003c0d130b0f9240400100e0701d01d10070b100b51010081000300500562101c482007800b584c1103034002d0403c00001e4000440180c80e500c102c000154800d0411182c84080070901824030201600318400103c028030421141044900c101001a101041d0000d60045190710484000b051405e0141031032000207805001c1014940c041083d0541d4544861425016101048191007200c10040c0c0015810074050300810001d20818040e000e05041181c0340103081c40d5007009607a011a003524203d1107480030402581810f480501e0244010000e500380700445076210541800340c43d009100c0c000203000c4214070640900c045640e906098000e1513280c1071031420340c5001c0c0a0543d0203c5a9482201e1002018100040d80e80d0149038142c540d014a00e090000441d16038204840c550760281c3c49252071480340e2503403e10035024125550383c0c2d4000c290a000094103899204235000f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 547073696 1250 547072446 547072481
    0x10b0d0f0f1e050714160302070905040b090c0303030127091403070c0b09060406050a020c03010e21040303020c06030a0603150f050618010b070c03050706022d0307060b030f0a0312 79
    0x1c801101459041b90380d803901801100c1c480c031a00341812450500c50390010100b6501d40b5060209203d50204494030940c040802c0345c410800d9041459141c0c0028450020010341641c540c0d44451010481c0c1c07000c50f4035080d000544081140c84850001810103103410003070b00005000401e01820720080d00203008800101442d10b040d042c007145407445140700d900304001021401e02039580c402d01026200d500000c0c0240550040031144a40320005500714003030001c40101d0211903812002c05079000c4a801d600038010345000d45040c400c1c6548010300074054143c0d60390700400010b44107012030506c108080c01c0020f050703184444440c00c81d240582514445c3c4281e59582a00c440302c0c5038214151452900442c0e2540014a07041038502c1c2107410042407405040c0c8045000342c2d00283c82400c40090500003034050840c455a1078440b150702441c90420341040000d0404070f0001d400c0382e41d8108002d0210b480183c01071800e2400c00b0469441240045e0168008134142c2c0c215001d00100c400c6691241b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 547074946 1250 547073696 547073717
    0x10b070309060c0609140f010b180f0403020a050109061407020f06041104020d050a0c1b030c12260103030905270a110c0c0315010b0d0f0f1e0507 64
    0x98040380451282ea000c000840090204021003034124805e16940045102e2000c1c1c080110180c1710003904150340c40703075885c0001022075031170248050346408410040000182c7c440d40240103003580000d00a0342503104003540302e000035400344265804680501d600040d4058524061440c084024000600310351054011040181e0041105a0030540c0000428088010310307011602902658040105180c504400c21400c00ca43c2e8100e0100c00c00c890b560ba0f980083c2165030841040c3c83c860024002400103c1d0a4000820007124040c001c1d0f0103080c1441c1c41c482e58010004800c070881c9420705948500001001011742001b111000707003108440d00c500b40c00ca600c0c11100c031140040c400b42d079941d0048001c540c1000c01540111174032944125010f945018241e0110780e18501d03050594028400c81007101884482c00800c1416200410041440e01c500c80017180003900f8948043c00c40e80342e4561802c0128000342c46502405003800d1050000c01c102e40e0100030480e54010315141c180310b1581e48 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 547076196 1250 547074946 547074953
    0x71406090d1427030f011428020a020c04180201020c1023040e0106021b0612071107090507090501030501090c02030901140408101b020a0506150f090a020c06010b07 72
    0x6680070f070300c80c0d243c030140b841812500c2e903041100c0012046415006038103042462540640001c0d804440f003045240c65500c400400d105e84010103280c1d0406031000e100c6506a11200390001c011496aa1046034003001e00e00b80014100e803003031500d0080050804141c4002c5580500000105030030441d00703800303800c003202000f52000201d18861640800c001e4005a405038001060300c002d0f001517480d0800941e12107102958072510300d065560960a08403560078140350a0044801440080002c00c4040c0c4443c0c1702911112203103a101c0c0d90758040c1200c0404c51101038032921f44600183e50320030882c4d500e060005000c4038030680082c100d080c10095070619107500003040702e0081c803081c03074030401000c40606e41c0a5140160742000c1d00e203015003228013115030159044116641e052284120760041140d0041e0b907109007008004100760411000210154024120b40030b940d1005080d20344044900c10015601c0c1000321030701101a5408030780100d4240c0104502d03400350801619041c41d080c6280c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 547077446 1250 547076196 547076237
    0x601080c0a0c08130b040807080304030203030909150d0b0a0e030301050a03081605030c0115120302100f020705070308070c15080406020310091a04051f050f0105071406090d 76
    0x14030401400481a22482008440811101c40109004603018a10f4440f8002805d6910070703c6025031070702c20508007107101c0d00084200c4040300d9000f0029031130984040c1c240305202c28005c00c000c0201031044240030054580714041c01030b040c400d607211488c80c0b5006815204840060000012070b0340240010f008640b5420b035036806032a08900303515220315100b540c1222091591000500780c0c01b0200385c43c04654070540114040a05a00c04603020580780c258000f9200340a21014005030b010300343c001003140e09507221070304940054070058503087c001d0302d606192500315401102c00000002d40300041c018100e100d24064124103101440b080440c0d44007c1c206040030300040d000340c1d80000401c100c0c0e603617020f000005041c0f03100140072081000a0002103030300825011800390307040000040c070200507020061046203c0e640648901410482407003414034136104d406060001c204003290205805503100203004455000130411898000c81072810440114111400d2100b801c642688030300161 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 547078696 1250 547077446 547077457
    0x60c0702090a2c0f0c06030c090d1e0f02040b03010203160f0c0c0303020a0b090705010207091802061c062301031515020a03020f070b07150908040f0302090601080c 72
    0x7200089205441c0c16080c83c6030120282c10708001c86007540146441c0400401e440100c00078810682e20a80549000d01040340b00848541c0401d5074100b0813480c1030300d050030b0b034902110300039850040042080035060600020000d400e030380002600c44620304503c2c0a004202081109400950071820442004d80314807507240081d40c2848020605003000074802c0f09035244c265005485040d40035503a0138060f4807040c8440068800d403221200080c84541c0002d6407004031407060b8014030300d1501e0660418020041c203900c205003006500d100b14007507a60308028010702501103600500080001d204c2e40c1c01c03101e555010301170a6101c0680368600958003924000c0d540000e08000c241e0044482c1088103030130303c603085a4440c281a448050810b9400036142d01800c8c405d40844c3c054005000405545110034410110425010443c40d00081c0b01e0a5401c0141c545104020030b15202940c1c1d00301c815001600304410072404940c2c00c2080d403808a5020380c00c03400a081c614001d00740f045010004e0300c42c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 547079946 1250 547078696 547078711
    0x3030e01140c030d14180d0e220203010503070f050d0206070213060b09010f080c0403260301030302010902010f081014031009080306030d020d0f080709051809060c070209 75
    0x46121614244004084800c40c0c1d10110039203503504d007076026020080640c0c4006900103c18180090820b000f020740e072002e00b48403900244180140500d044071a180500341454208180742481280200a00c1e12864648114000981c40b1760419007810716120f80c0340d02c509042907a0601c1041507403941d50a0040894058650a075518070034000708200748a02024071b07180608c1c0220001d96420ba81015011820090380c50704e40380d038010041260503202c2918103202c0600d0821003000090700d107580c4080700b046480869601020030035a0000550802d034419400b6075102d2100c0011907031b1049014894050900745581d00f07081551002034150b036180146146101500101200742da07080240e15030000e10f000742441440040e1801d00c400350420b5940c0360181c4120b5003208a41400451002c018100913514000d445411080031030b124000a8210790a00400c071001103050b441c1c140d92003c445401044070305207070415100c04c5141c03850040c440c010246050051600583d62040c81c0e5410109 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 547081196 1250 547079946 547079957
    0x10f140d080f09040e0a030305150f010905060703020c0910090516021b12300c030f030a090f060e1005090c0402030a14250503060f040c0908070803130504020403030e01 74
    0xf103400864001c04802040d5240c46c45450000c07420160b01d900a80e10680602410199039040702040c0094040c82c400b0700c50201d615403a00b4082402c020001d8444c0c24080c1c812a44002c9052000c41e00c03200060300c40d0388202c41c9a0f0b0050000c03036906d0150343c1d0003074940b052001904407a0300009403140b600196810000001e16100d00056035200c0041c00d101c80c0c0d14054811075403154441c440f21020840407810003810341180d00b5140e81c075403015203030502c2520005d94542601e496544030703654401805082072682d500c0c112004074035102c0341c070450b082c420b00c000107008034000c60b07151070852600c05030080d01d81000c04001e4601c401084548840c4002c3d034015850b40c5030382c01d842c0060640260641820307203269041208221410089040c281815810300100000c190300403070700c03441308a540a0b0090700c40420300420b81440d03801000901258500001a01d80310483c0d10304200e21030b40200a1355001040105000006a58110041100310f50440c5040c3c59960050400c216031400e0720305110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 547082446 1250 547081196 547081207
    0x306030106090606020c03070503070608071b0609060207021e100f021f0b0108073b09070f0e01080103150b03070f0305010207060f090c1814010f140d080f 68
    0x1242508a074001d44081d40d0284042911110000e50700d041d2600c4040c840d1280900001d0a0704012400c0000c1d991156a402110390307400c04240d0b540f1a20650380d41020003002043d0001c540c461050515084c4a68005640e5a046004000080401c01010780d4502c0250b4180b4980303075181c61380000d2140755402e1200841c1030005050f400d1602400c402c600007072030130248203031800c55544241d915038401d89039003200303403134952080310100b2415120700c42445003030b40000421401e1455404404e0a0035a0104e42c0c00d0f8120080340380c002090740c41070045500c0c00e000c010801d801c82e5414401c90820b10340b0100303944c910344a030f00b1040740d4a50420009540ca070001c907800d49050001c0000b80c06544008540300c3d6491520310f000358007c2000380c2c0d616180400d1107030018180e0090b10141a005002c801020341010660584450101c0700748102c0c0e40c1d80d2400d80088000d0641842c002c0c001d0380d0350000041d00c0c1c0f605540a1440a80b1214030542c0000d0100c0700062040f8113a0b00701203e6890710a4aa1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 547083696 1250 547082446 547082449
    0x804060b042a020f0106031b0e070203090d38090c03100c0905030d11010507051606050619140301051503071a040f0e060a090b060a03021c02040f06020c0603060a0b0306 74
    0x352030301340c6900d500b024004170601548410090095002a071200482d5540c1c6a1466031914165202c20050700108101600c600e40a02c3d0b82a5007402076083d100c0c1e00218070b0140c0603131401c5480d5000c072401d8007040c4000c40980809038683c014605009002400d051000080c2c840c2d02d41303110030300300d80e603101e6459540038440d85918014120140442d08170040311740005c1e0501801c115456402d608100004080520440c299105910a044114960759141e07075031380041d040080005400401030000c219000c5440550300f801450081400b804000c0360764145070940e80b004140d1041c10130400e00d2030809480003d0200121100610001000300d10032040301050322030f6911200e0031a40c90280440c08201c4030312054000e00301250170110441c2d075030142005441d8002242039000a052040c211154065001011802c101c00009009142058a40070881c0c01c07036000942c2002c9503207014040f00760108030150407200211a860704500c1d240d000280c401c1c0e00b5001d0802013210101c0401c0c01ca = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 547084946 1250 547083696 547083703
    0x6171b041a040203090f03040803070b01060c030f0507150c0e031b060304150b0904060b04051008070b0a090f030503070c0e01030f0f0201030902040c0f090e043804030804060b042a02 80
    0x21b01c4c40300c4140d0303a817683d0380c100c84d0b40c2e03d0300444015262008504000901603000340b0642640e01d60503180d038559258406400c1d01d40f0341140344144c40c003050140752003400d00181d20401c00481c080f51101d140c40d10030345041c18504003c03034401846c0303408040d0b0b0204595450310162a801540254100111141c1080303603c040d2940180031030300080740006110030405030f070700718400104d4140e130200034542e9420102c4100124621401400340c000c03803014044c003039030f01c802840610392504142c0d40e51595115080c001102540c0b040c3c1d80d540000c100b02007000550081480248039a012581d2a54150b807505078043c501008001c050a10105901c0300310b901940104404640040c070401103403050520260076910011300b0003002900b03c0d10041544c594034800c090082e070b00184a110151401050005180000c1c41000d840d03603040c4800111883c0c0140503140305030300c242d560003414181858240161454021520701c241e0501d200100e4800b04d840451001a4501ea0005004001c5650903400c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 547086196 1250 547084946 547084963
    0x30c071106130909200112020d0b060705060708010611120d110d060f090c080a0506010e0a0603021207030c0507030e1c050c09180d1206171b041a04020309 68
    0x200302d18800c100045548080d0700c034581d41409034410f80101d6184035402000c0c581440203042c081030071007504d000380c3d100c141e000e049034040b000d02c00600b60445000003001c0741c02000048509511500410407a030b54000d0300f260041149086c641e041c40ea0480c0001d8407040584150740850101081840408909800410310040c81c5003c040e07583c0130202c82c140180860b80220000a6203900000503480000d100b04a0444425940d03000e40e0348401816402a002c050400e03070421042500340020b45d5298030072900100000c3d1401603403100c0c00d0202401180004042c5428075243c5245400110741000454003400d40c5407038806040d01d20306000031810020038403180c1a801410f964442002800240362006200841c1c3c56041d0f96a00031821100071a072100090480c2c005c40710591405004514044000206210100e030440d203d80007111212603075040010158070010300c91190b00440f0301d50102054040d1018040003100b031201a02c48100100300780d000b42e038000001002000305204030034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 547087446 1250 547086196 547086217
    0x2030d090614090d030c050f0d02070c05120304170712140f010216060b060c0718180317090111041503020702060705010b0a2106050901090b010807090c05030c071106 73
    0x7114100443e089964200c2e032003201012915081001c010640141c050700c0c158400008a1854000c00c25940e41c041d41250904651900c40392034045095555260035014050250000315240c82c90b00114030305a0000b840d41108607040f1040c240440006160f0610380c40b504a120080c603440d401460300c2c60200302100103d4554404940f1600041c04900c85491003070080205008128030001004094460b81107080c8950344210803c0242104000e445800207654000c0080d0007183c1c280742004150300020214001100c0b011440320001210b2076107034019143c4402008240155204070005200d503008210404862000341c030600da20940480300d200394003a00451320303041c091034042c3c040c1c154045040c0c4600003510000c50344644070030250300b407040b179590016420661078030b03110b00030300018085000c19502c8050000104003540000c60003401c08500510956117040c90150032202841101810030804009009002511606030303032110381c001600000310b030340003000a05180706110b0038a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 547088696 1250 547087446 547087481
    0x10822060e0709020903070509070c06050a0605130b0307050f060706021305040b1c020402090f04090302070602010c0c03020606090a14010b030403090501080c0313020f06162102030d0906 82
    0xa400c000440d004a4400e861407000c9442640d243c240643c203a01802c00703100e8056200b50b00812062600740380c00e503006001d0303041c0741c6004450360320380d4015160304440301c01d8010b4460710200040c1c00d080446d14a078407100e1008000c000c85487c0026100c0d031091080307074412220100c43c400382e5505d482c1110f5502b44e11001c00c55541c2c042d1159100c0a000d24410b144c8101e2405400c2ca080d41410800986580c0340e0700555503d008913942000025040311142a40051901d900d15000c0d450302c3c411015082d01a400801006140c808000e094508e081c1c40300c4108010000007a002903000a490b035040841100c0310059940c80c581004010410148003010000340e44000042c001403040045004a000e0303981c1c01541500d5600548020300196001140034004000082181c182940c0c05441648001c2c840c120040004000076800e420920b00b40041d030341418407940811819900c545518005400d0044980c0000c00e00a03440e03004017440041603980300e0300c640f4100b25607a4010303a0ba00d680c0d00c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 547089946 1250 547088696 547088761
    0x3030a030902030c0d08030a0f110a0810051c0201050702031603140d23031509010602011d010603080a0f1b030f121b14070605042a06020307020108 65
    0x10041c20345108168000e0140c86060007080c10100e07092040143c0100d150b074596111010300c0c1004008035032144d07480f1680d4a00c0b4201a8030000010501000300781d4648515041c060407816a90702c10394416032044400201e0140b10050307500790420f04940900702240c940c3c41c1400440e085c031124a880d12080442c0040100c1003101c0b00940340c0074000c0420071101d55204100e81a94005403812240302805203644c003030001504036400443d440803807010b81200c2045c9250100b08404800e82240c0c0150b5100c48041d008071080c1f2124810b6207480000a10520b841d54076030600300e11820240d442044410b4106038102401100300c003c4801c0a036141004440003030500420b0b01041c1c110741030028120721740b080000090743c010078030001c5c00d0f80032a6800c9100620b080d120300c1c6108428000b43d0b01700b03021682c089000361003441c1c41140101d04001d40c000140c003480d401c0c01901c00384e40f0003180b01c160080c06043d80c00019214000c1d0b0a003859075803034480d000f0394456a4440c80d00007850001341e038803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 547091196 1250 547089946 547089967
    0x130b0d080412051002070b0f0702031b1b06070803071b0b0c1b0a02280305070b040311090106020307170d091101031a0d060f1b0215010605031312030b0303 68
    0xc50aa90107441950b40c0da283e204c01d0103099100d0440080d0500c1d401781c02280300c0c0503030342e8151030304070040b80100ea141208188940c1000b240f1b8240d0b10007290040b225003590f52140d480d20b000704200440f41549402c0b070b80d82e60b840386404040c00c801c00300400b08200f009011005024034240d107411015500c01c2d0b240190035842d490348100c8074800d42440070382c0f420182500000d901107a05500401c032030780401804500d0400ca920341d5054405260840c030300000810740500c00b00c006401d58079006d40d03849003103040510b0690003802c8171034000ca88120041007020760200c01c2c7c43c1700950002901c1c2e842c2d10040c4595442d40100b4494024480c60039034248200000602e0040c15071200307880a210711400c0c0412003800c100e9000d801d0b0b0b08610100c14110009005030300a1441c200d2004001880700000b91f00c0c500003210035410fd501507400b000000220f52a140f080354010003503071070020310b5443d00380c240c81d03240c1480f16001000038000c1142074003490f001c2d0b04641c58041014045030f0302c540701640c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 547092446 1250 547091196 547091219
    0x60109050316050f010c020d02150d020403030207080727050606040b0c060f150a0314030c150901050a060f03030c0f171209030301080607050c070b032d0402130b0d0804 74
    0x803c09100d00400740c0110400c1d40904080034500340c0051013082c10089540910000000d03070403d01031008010440c0c4890b100051018002031400795004000c03060034000d00b5480e25038142c005121821565010880b002801e42c82c84e81c1d1103162840c0072945032151170104803d0b0295070800e4140920124004070080760004180f4424a0b07100b01d01d0300b03181c6072010902c48890364010b41d9904102008001e0003c5030110039902030910300c0804580c0382c8140c40c00003504110b054441c080300078641400b40012107800340241c2d90041c0c904007081240d2854882210801421888024240315215990005000d49641e14200d09604040820820b00d9101c2824004c1d90000004d500040380032400300e645080c0001c140d0b81613030b080b18020b02d025183e002b4140e41640240e03c45681e28800c0d8030001c1000e881c0400598091150125866400104040340d000b605619041c901f42891280c0d0407c409a40e44004001d0714134400d4100007100c0c44400007091020410030b0b00a40b4044000a00207400424417 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 547093696 1250 547092446 547092449
    0x6060603020903011523011e1e08090c010c02040f0501140418020a061116030b070314060d080307031805070f05100504030b180a030216080f03070803060109050316 72
    0x120001c000060244100460380c49042c0070b809240044e0b0700c0d06c159022110111080c04135814100081d0518210315180a030b10001018a400501c1d034004040e101d1000300585002e031081c9003082074842c40c20050340341e516003c0d1300100c1d0400c1110440131095458982c010001900c52000a1000b076840e140758010b450541c080d100e009926054441074003034080c03c40070099581c001c0a120300d42c1c1c40e1803421202507840c4100c1c156140030301c05d500c042c0043c0340c00501005510401c003045851401c9a0b014040341d03201d5481c0072602e080001040551f9803040461100c0c0d0b40d000480d1500ca4407510b130100c00801d528484000840c085040d8042846030010712102120b003900700c0c02601c141c5410604c500180003103400000704200f80400c1c0001100d00403115400901884160034001d061040d85280041c403070340036000360b004030b40721103620002030312000701610b00300d0300803e049040746001c40d41c1d070710503448050115040400403c02a80c4100c00704401021700404845c0c0101c280c074150760580c0ca15 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 547094946 1250 547093696 547093699
    0x30206060103151a0c100c17010b0d052208090306091216110d0f0b070509010507020f0f0604180b040c0c0b070c081602090c090a03031407060606030209 67
    0x4400000e58a5031182c040d0300b180c44034084840251601d8003c40381c0704020514408100a2014050f45210309003c0240000c001d00759040414180508074000d07140360301c0444518016520000188240b01e01c01e0120740a01c0103200000485a070764171112640c05102c0c030340840c04807508240110a014074007015068001c0110240c4105846801d11b280e0b8a001e1055400c10f51a420b1141e400c2040b0005000d510301402020038111501c41c0c0d0b00002d0100b00c002c0012191001c003d038540d000e1183c0e103002280c0c090142d041140c40c150184c0d001074954011920028402c240301c0915040c05e407100003094020b80000784c203103034036103803280c0c0c003100c4050f580108426814504801d02c0d445140c10300071203101e100f142d21105801c1c059a25200c0305100001e1580040c401f110281c5000a1180070051000710381002c010500b209642c8108003003104040c100c10070045013407007101c90650f11038800600300c035854141403a4030301203603803c0c80c1c0c030307009000019108500d000c40000342030340c25030000e160b140b00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 547096196 1250 547094946 547094953
    0xc0501150509060607170313150e0c030a1e02060d0c2c010c03081f09060602100b0901120309081b15120a050a09170c06071706010e010e0603090a0302 66
    0x903000f052224074040c4580252103102481784402541c4503420046810141c21400c100780d42c0d00d1903d0382214152011240304403550747d0080ca800d4100f06000354101c455080b07000d000000d1160b22500d8414405070074641030004c142d101e1108650300c0c10102c40c1c1c50720b800103040c400044881d9000d00441c010b5a5840351340c4001418042540f042d4105881c0d03050f9050b124045040f0607901d0071242d850780185060300a5015201c1c039080342c081035041c1c0c1c0013400300c0340d400319001e0304148000b07003081103114254010700d00b4040143c001e540e600c3e8a09066584540c0206038081407420100c030f1100d000d80c0000c00d00c0c064000310701000304c140c0403200709030391054809a1240074400704440c01c601c61410742001076001880420030b165403d0f00100e41107011000081503100700c681f2008410100c043c2e40785000d140004060300c1030002401110751020715420041044064200c0c442080c40c401801d00f41007104503034400782c480c2c4c01554401c1c44440090003a0f6101d1400744d00c0c0311350300d02e10003200b6030240c071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 547097446 1250 547096196 547096201
    0x40c05010908060903030f0a09062a1407110a05060d0e0d050c03120405010b03070612060602030901140c100501030f170a0c020d020f030f100b040c050a0c030c0501150509 75
    0x104000f030040d0158007141c00662955444002101600d58023a0680c0c0c2503e0703c8041ca80041050b5020309501c0181c010401140d1841c00c1180421203214400117805202514000000d621491420740304000e800901039810110254000f0b900e003141070300040c0d8020760104040480880c65403283c0c0750101503d080b035042040b54034003540c0c14003401020420681c0104040034035500c54aa00343d40140c461000410b000042c080001c3c01c000040d0065000a198500b40c8000030100d03008900c01401140041c510344506000001c05106455020300d484110001da0b00446000130000c25800012602c41008596102d14005507001c100b00b2040c1d6100010184070748034105610b08407080c00340341d500c86460480700350782070004600b8041c100b030f64043c3d18080d10340344940f8184040086810101c002d00603c141d4041d4050403208149051805646805120000107802004650702e85600e802c24100d0080503140444000880d00c0c00180503508112019a605071248448020f5501c121034040d0302d82d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 547098696 1250 547097446 547097459
    0x25170d030e150c1c0f0902130504030c0b040c0503033c030612010207140303010f0b040509070311160c050a05060309070603020705031b06010303091203120f0b09040c050109 76
    0x60300c15514010b08040441c003c00c51036500c07080189581c5040064404500c0d1800c22010110b0708001301c540b001a4440440c41c0c11482c282c087c80c002ca491004041015003481c2e10020021208600001d00103070103603020600340300440c0310f007000034400141104d940e9226500480303448007038519041342d040c42003800c80000380800d10880c17010f010100b80040c250794401d01008010b20b40d6101c00c61555600300310b024081101c8807040d58540b0042001151750b5403401d2030f0a90150001d13400040b070428280301c24000303651041040c5410009504c0c0c0412600c1c0079803220b117000d2140b84040c4542c2807120520908001344400300300704a0340304494001d0f1450796002030180521003100c01041c1030f08078040a0107017030300a501812515000e14120b81c1010205c050002100c83da614141071140e000c0e8004208140d031000d528000340540c03503400e000e03601ca103a038050320041845203403000c3c00d07440d0203012903100c01950050308400c0c00109041060304050911a100118034090701d80010906a00816003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 547099946 1250 547098696 547098703
    0xd0c180509011803051b010204240203040312080402120d030e01050c07050a02060d020f040801140105060a080f070513060503010f1205030301030b0411060301080615040c0225170d030e 81
    0x100035243d40c200c4800725059408840783e620100340d40075042c4601c0030901003118240b002d000544640912032508100c11249403280f075040800712030455100300001d00026600c0e056000b000715150070620865201d40c400140f11208502d03a00d00d6901c100340024495540c160040c540380e50450000300002e4881c801c1d952228820041c0203861984060741e0381c80107051210060040050300f803001414204610801d2005911a60000000f6034554a480300c8034540413181c1d0b80140300c11186241751100442c8050481a001840820a00403c3c0e000411040c080c000300c51b0595680101e030000300742c69010142c803580081c0543c484180e1040c2c070104601c01c04000c07450b151504000110300b140c0c40d59981030446d01d802001120f80f2061050106400e03258035001e075000e00444d00c042d00d501c1c5012050140c1040708100c080b4400d906021f940e80e049500032480321401d0111024004411000840c3c1f0020b03824990700081c6030645050a560280c50b010600080c44903480d60309105142141e245581d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 547101196 1250 547099946 547099961
    0x3020a171b0a0c050a050a031704050603090a030e0103063005160f050f01022104030c0603060503012f070303091b0501020d05031005090601021005010303020610081603060b0d0c18050901 82
    0x400c03240d0b11601340003068002711b40b803102c89041c414180c0382c03681344c0d00442c1d05a0010b980121556002d010342e8001c01d070700013611145000e030a00c0c0800600d803a008401c0c803443d4107580d114094000010448090844403120010440e0300602180d509034911000c2811401c0507109040e50700004580104480c9400000300b40e120030142d00402d07036940c00c900003054a00c5880040b890441e41000004001042d240d00800103205035140029094644020302d42911296401c0a80ea00d03009401804402c5c3c8003103041210400327261500361200150301d800d6008100354540a0300fa0301020510b1034400014991b600d003918400c0c0d0a2f41d480200c02001514140400d03038030110080803808052000342020b0b40840d0b40300344144115529001d100e03481d04200c84003a001900141c001e10100030050304021840c400520701721005081c0102d040b18a128a00ca060100a01250700d4044142d41603848120441c1165040740451001c0c44da901c1b2142c4035450301e000b001c100d4604180005042c008188103941307 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 547102446 1250 547101196 547101199
    0xd0905190308180a1205030a030c02030306011d030a020603150a0501080c070204090f0f0506090c190510140a0c0201024c0204090b04140403020a171b0a0c050a05 71
    0x242410203aa2810034520105900e40360000013030007000951004207010004181e000d0005541d0781e540046005050700e0304120140155401001442030b90703688048252100c80d400c524203018200014002410081d501001035844000401404114446e24881c0d418980085a031100d090342d55000540e2408022a440701262006102aa0140c00e0135084425528070400e007902c045082540c911203038011107882a5440d0380a50b04029020b078042107040c1404d18201c52140700003a1101c022400e04441303009250185034203c4103162000d000302e0300e0582c00c5504844064403035080c1140140181d500190aa006100d4000407181c4001000c90280e00c6804407940b200445c04040e907080d48901c1c1c0c207000059484100452604124118405080903101e80304021503040744241c10030042c2c0d16907080c16100004440d05000000390006140041036a10070750b85840d10b07004000e0013809008441600d01e5611050040c6000b401e000b1030b009803030300e1003604c01c03100c3c8a4030341051000c054501c1c041c49 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 547103696 1250 547102446 547102463
    0xb0c160e01140d02040c0503041403090a061409040c1106061507030302031e070e1518120a06050c27060d020c16030b0906011a040b0711030d09051903 66
    0x601981100240252440102038140f00000b5034070b50108084030400a0380d00000f8001005000c10400407444121300700d0b419000540c180300003900000c4141000740f0800701031010307499103800c52005602c1503980b0014010400c2107801c10000014080c40b20f00c80b00c07044d1034002c0c000011080d01c4c1c0b0106107002d40401144641c10103886550580080d40046c100d800f107080d83c0102914041210f030074052088100c0d54402445009004c1408500018800d80c200c0c5407030288005226442d00c0000d00c4c40004085488500001c00c000480f400c0c0030300c0c081c020304054240300420550490322402040311560380320801501b90b0680c0d840e005c0700800403101c00d910010402c00c0000b000c403184c0161411003c410305035100d41d242c404115201a101c0d90040b20071110544c01c01075450f8082c08241e00400603400c00710103020403061049424450740c05412041e1402142d92300c1441240380140c80850030242c11108034501c8040c001e81000302c288201e5100b010180e015500505014040104680d4000e088 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 547104946 1250 547103696 547103699
    0xf0d080901110406051602041104080705011d09070c050303150a080f0706030f060506130602120412030c0c08030c072409090207080f1b1006030317090c0402040b0c160e01 75
    0x312490f601185482c030344102a40100005230f0345612694a4010b514003001c2d55440c6402045420440c40d548260b0500a06005031011900e00300200c5890000c1107900c0c4034030750303100c0005130f403218491640500103200100c100311102d11000c1250b01d03c20001c4801510140c0d807000b000f595190351041c00207254202305400c000082c02500400390b203000c4200c0108905446e203021440310b402c40810b083d001d4020310001c005803601408003003d10850070203554034041c01c10300403c00c2a000740000a04100110041c00203204020f600070014150704416aa035411030b81c0010f65944410303000f20b294280c0b0707540d41940015000c0304003400169864072003c0d4850302c4c008000703000390403220703064811107020081111103500400003001440c96a8024030300401485802d14038010941061404203840e204d42800030a8110040c580e2062200100c010a60780d01144e8500b810108803106401c9400802c02055805941028000c2540d001c0304540c6130b0080040102032100d8188116411142d54000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 547106196 1250 547104946 547104959
    0x1806010c061109150306040c090b160503071505070906020319051803010e0307060f0902150a03200a140a0f0f0e0d03090503010b01080712021303050f0d0809011104 72
    0x882d0300d103101c441c1c076642403100e01400300381e880c602c120502989400000400800340380c1417090141510075490940d45107410400c8445c41480740c0305100345800038159401e010408100308490425520803c1c5500baa10034942c00c0c800783c441550001c0c041125050081801d81c400030603507a02049103c070111900710502026212503001405802c855410311908400d507440901071080c5103411750000719030324016401c0c50740403907e001d03504010b001d0034242058050390f103910740315403100c0c120400c4551301e0822150940c02080b040c81e030003c503e00084411205800c4080181c1110310094454010b800600382d1880b140d4031071900c980d000b01c4c10041c40c003d4140d10401001c2c90080050074004030101500d400600018511601140081d03141d41d41484141401e010b807400400342800d0490060038030100c040d2800041d16240e10070180e001c174802a5051110490800840e04981074403a2611301480c81600c4680781d07441c14010603880408202002014411520080503120328607040a09101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 547107446 1250 547106196 547106201
    0x506030d0530010303020d02191106090118091e090f1103031e181e0405060d061805010b010801121506350102040605040e0a1d0c1806010c06 62
    0x4601c01e050802c082000c9004084450005001c0c5010760001c4c10034a1039544024a44001e15400c0b02c180d02d400b211001c001000080154550300c800c0b1091600e85000c540121519030312032000007a108046000000c0d41480e80c0d202c04022208181d6045480544003155000c1d0b03070722010b0040034410020204000b00307080c5c90b42a02c1c0d5140c000c05807807410b814000c06075000136900010441700280050003c0340ca030684801c2d203003618006e13a480c02c150120b1500d9540c40400c00070708140201d40f51000108103503540b205240300300da80304c10108100f000000e904402c00d45e028004507501d619000081000e58050003680307049490500340319002406039602d100007400401c200310000754031160301148452109031100301c9108611445401c110458950100b04035030038500e003580b17034070420061000c41c1d4884112015140c09520014141e216410220020b1404000648081080c64820000b4041c04a142c244c903003c210344100e00b054a0400e81240404151181c41c08102003c40c01c00010311031340c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 547108696 1250 547107446 547107487
    0x9030616050708130f090c051602030c10081e06030a060b03280213020c07050d0215130e0a060e0411010201141305011404050706050309070f090203010305010506030d05 74
    0x9182040c2002c09035a248801c5400c454581c010320414824180200e0f0002440d0000403c0b038541d043c000b84210020251880c411105070508540d5040d403d4810364400b00607500124001038886445d01100b40002080700b0b5041d60010b050b09609040750205d080c2854055009a2006028090314001944c40344000e000e080301541d054040d1013682e81d01050210501c03100c003800032622850402c10751040103010014081d0901c0b0540c03040c8086002c40344002001c4e41a2203083c1c5070040408003900000d0601c01c40c1c4244040c80010000303d02c4100001c1501c00d801b00c9250500200203030303e50351043c005449844c051403159208602c0000c0103d001c020200c455202d040c000043c046805c0045034041007400c5a8200f90303003440c40000b004025092281340c003040b0952940d86001e0070310f03580700c0b074841c1100d228180c10440044041100303900c2c14800c09000b17250303400003074402d0341c0d031a50004041d41003440207a80b15440e010001c1d2441c00c0200303000c0f0b40c2030000e0399180c1ca010152601280c00304000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 547109946 1250 547108696 547108741
    0x60a050109062a12080f01030b0c0702010c12050c160b070602030406021b0618010501031a19060602011515090302043602212107062f090306 62
    0x4580030840d6809607183c21040b00e409950800c1c0c046203d00700c00307040d640005e40700250800c06800100b002c03640c14000d483d003000345220307041e0356504503000480709021031440160103c00b41034080c12940782c2280081222101c1401640c1c0c240101458041c0d070f14815106040341000c080120701d0000d007455004540c06882403030018100300012080d852100c94813809456158041e0061108a1840c8806840c3d07110b005002440203604503078500d80c18040201505600b04655004103102801115030844400001d000404c402e69848100034042c0070840c4203e0610450104041840101c60342410f905205a0b115096120b10b10307400c0c0001003490648041c81e1403a580b01000340d4900322054651082c140c145040d040103160300401125544110005411009100b1092048200891480502a00348541c6c4c1821301440041909a20450000030030883c0350401e2100741c8811641e52098031031010442c3c0b16580c0e002e405e044010f10980b0300035585507019500081221107942c441d101451003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 547111196 1250 547109946 547109987
    0xf051309050f0406050a180204052a070201031a1e011b03050304050708031c200f03090709061a03040c09051003050d080f0708090c0a0b0405010305060a05010906 71
    0x1038558100c41240c00982d804010700300741e28207000070700c0941c2c007505800c460389500030880c1140080e03d12030024080d0f01e00a000c1d98a07400001d00502207042054010429910282464111091410303916032024408a020a1800c40303100302c1c11130a603075501c01401014154440380c5480c8010880c58103186032455041087d2818030001c3c080c0219010111144291903181e03c80c03d240c60441e0400902d9048603596a00a01000c03840e542014030000340d9480304d0320000307070107044c0b214064560a41c50b031070349004100004400e44428aa04015807007400c0800c1650940c1d6240e00380e040a8410030701c21641c64131180128001902c6c20b5800442c3c000717105100031101c1030307642c5400c001a203504580c400700c5510032042c00c00901006200444c6040c0c441c0c501030b03440b4070306640048110100509200704200d51070000441c418000c01248949010081030415050340d0340003642e04a40c0107000e000d001034103060110b5440c0c01c0040d034110507648140c41c0c4012150800303004452180c1d07500450b503031111 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 547112446 1250 547111196 547111199
    0x31602010209310c09050f04050417130b03012c0103052a03010606021f05071b15050f0a0e0c06040324020d0b010e120a060b0111030309060f010e070f0513 68
    0x14803a03c10181341c400c40d038991107102841d0108101c1180c45251a0901031400e0008000020f0034065480101541c0308a0701c41e110006030350f200119030082d40100300303030050001c0081000030000c08040085c211840610319502241128103401c0c050a1100501d50780c003820810762812191006104c603003499099200b00700e140240000d0035180158003540158000111807140178480100702c0c080840100c0c03051080e800d000310014400c2c1c1c141c04052188000c0741d1311442c00c10a4603000030703020b01d0200c1c0d010712860800701e01507103040307809866512940e40f900004642120000c5000c80c08000028800b03801c107407030342e1a42c06040d00310400b030a0501000c0641c44440c00224405800021036035000000e0800040e030025100280c074000e010300c60400c40d1803035407283c140000d41741011031b4050804119400b0b41e100503504100b540d44624440d00000c42003180d001c1000400c2c9200e201c90046405041e42d03a034250b082030003000c0c0c4422000403003402c58610b230f290280005050948500c0400000705 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 547113696 1250 547112446 547112539
    0xb090102071a270604020114120a0b10172703040608040b0c0405030d0e010216170607080f01030b130c06020d020105070e0307180603080a0203031602010209 69
    0x100031105003640c5607034420140001d10641c0d9811410000400c2c3c900c00c60f0b800841001c2c0c3c1d880d03400400090401a2000c00703941c611407002d040da900c881a0801c040c4040c20851600d5000d040c150008500131350903032110800403403007107806202c0078441010f0b0700c80702d46a40409400e80f84034044c09d4180f650700e00314400c03200c0074200010001001c107643c4017092424645000d030340d80ca50103000901d001c101071005004c0f43d6400305800c074014015091400036101c1c80390041c0d0400207900c0003812941c445400008501983c0d0030710078604200c540640305c00c0d40e01c0500c25503010009a410b10380c0700708088018130008041d036480c40c0d0004413011038200c02401540d1341c50a050f44c10340000c001038100391440c9100c150240219a00072413181086942500010701203030391065944074460401d03402da410154421000c2c0d10100113181c0100b41c40f5941e03406c10f40702039525807082d907403407100400030510066602d1043c0300350b40042c10010000c8941040390b41040b8107103411031744210400a007250b642c2041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 547114946 1250 547113696 547113713
    0x4020a0302120d0210110418060e07170a020403030c0b0702010605030d1106100e07031d012f030c03060f01030e0f2503050c010c0507030c1215090f0b09010207 70
    0x40c6040800a04440c3c030700d1480242450a8640d00040560901c402d030881c0d540400140c130203481c0108048100c1000d0186403030301800c0280c4c0001c072503503000000c0c0001c03540e2100d00c103010403c014540c0340c6240c680c0c3d14094102d1146c2d00c40030f00080d02a81241f0300007916020b0064001086200108865885100003414030403501c0c500c202244080c1c641001200e8244a411b6000d16440d86809441e861300c0030f8601c410304010141001c26a64000c0403611a01c1d0b41448094904071070002c01c503c1800b05050088840c0d0b030a51880490341d04001010586044000c5030f00c40d491414840341035440c1d8030284003080280256040c103054848900005d890130400c4100000e40b803d0f030007003404d11050303400704050800c1c05041c0045183c5c120428404140300183c5411100000e280001d007012aa04045003400c030707503400c010061a541c000004441100484561009000c0da201000c1d003145c00c00d6400c2260302c1e0580040c0801c10003818000070a12081c4280ea0000102d4005454106203603140c118 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 547116196 1250 547114946 547114969
    0xa050d021602041803120509011508070602011b27050616030305011d0126030a0302030939060d1104090e012016062a09050d0b04020a0302 61
    0x100d03074a9006a4000d40c0381c03e00911044803540504850702000e1a01c00801a403030b0f203e111004552110041951240d0940c840251018074004000b860b41d140c650040d1280c0c13441c41048019070814284a0f560b503c0700200482c881016210001142040b45110841842c00c190344c507055a944980001c0310740344c0d4001070400c0032400500c0c4501250358503000c0c0858006070451030ba882e00c40e194641442d0302d03044809064415099402c0c400700b14880c0d0740c2002e400c0e15081a21a400041009610f003901600510302802030380341900d80540042d02102181c13010700594a4403144680100300c03840740c004c0620403d0035409414186092244201c0d9029581c2c900d0150300c400600243c1007002203450321600445a00040081c00401c00451200c2010000e662100c48560400100c1600303950307200d14003440c1554032100c2405010f151003800403440150369194046242505400d9800a10450400e010745030010400805900f49071600101c0c1500240b0881e0001890100440580e54110b031128 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 547117446 1250 547116196 547116217
    0x60215040c0e0106022b090e0c041d042604090c020f01020406020c0126071d0a0e0103050c01091811040801020706020306190b16020409170a2c060a050d02 68
    0x1041000c2a409a80001c401070310807603500c008021425901b039400042d01c2e04460742c10103422006c3c1c4511100c03007414031a03030b401104440340d15003e41003a00842c0c0c0380e09100340e000720004250210114160414580448000c0d400c1e0300c020001404408600d5000200b0001c40d44100c40c550301090a00d10308a902c00d402850141e4081d50901d55079603440704036080080310324807148440c04851085084422000b41c120014080724000a111903401c141020304112001000550f14030798502022203451020f00042d0f0381801400d42c3c0c59034a5000b941e8803000c4400c3c00c01020403402106503880d0083c0110019810241010000000c101a090000e0444140110b01c0160341e410141d0402c183c01e59030000d10491250290010402c21580790184e462518103103002d01081c0c80780d4800940200002000240794203030803010b0031501402c900280c000004e190b110300c4c1501c5940e003030345c1c0114064a40903c0c0f00d00950121681d4604054010340940303402030801c10b00b0810b1550500c0181e8101c2c1100c403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 547118696 1250 547117446 547117453
    0xe060c0c0d0302040b040306050705071a0601090e131709031c0905030f070302090a180309050108062e11120306030111070b0601140d1a03070807060215040c0e010602 73
    0x800440c03007441071040c2001030307003000c5152514001c030b00b00403801540300c0030303210945d5103000524541c014422141c0d040d6200c1c43d85660605001d65140e1141004d80e0540d0011310708120100c0d1ba40f4140b50f009024007125010401590700355507070a2041800c04505e0400d089040c080c0228546080001600b252001c2c3c402551840c100074000b4000403060303105510035809031400824005011400c102502d0701601c0c41052a03541038000d1010789408102c5008028002c0040b206160b031082000d015501c00740d851807880c0c1ca0b03050400c10606e106130f22040044c2d00503a5044110090700301a09410201e41c00d1400c0c1507611038000a080c40740da068a0380340404000200601440c0a100c2c0c10350b0700c10615a924100300c450340355801000b000404550505c074011b4484010100104242d902c0304d42e140b4030503c62502c0302d13205035945200c0c800b00b25000e40325a1a0104080390080340b40c40940340a80e0041c0740c0d09003101c1c41003814a501a20030b0b038500c18100000300d080050185480c1c0a006640c008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 547119946 1250 547118696 547118707
    0x9090c0d0503250c1802090d0303050930031b0307210c0e01051b0303091005010815040f0c03021f020f0106141210090f050609070506090111010e060c 66
    0x300c540c03c0c840040501c00009201030346a0000c2c44190380d40003030b11003801c0040c400e1485103490344000c1c42141d45280c0d1020800706400308155158006078420348503e400c0c2d903000c640441d1607014034509410348169060034800549002d00c0000040c5038480032a0a5040003840035001c02d210550050b14080009100300c0190507650041150741c410840d042002000000400c040061240c081248402d0400c407000a000039000310b42c0720010508460001500c0e9a82807012010340d0311130038100100c203e242400c0c00069054000725828080c03c20074a20a0f01c140e480c1da50385280011040e800f100c44500649000c0013580780e2070f0740041400d10041d103d0788600c9502202929104004081a000713a060400038001c0308600d40c22540030801c2a241824040110504241015403080010030204c1c07505007110240700b0100720206846010754140c0d000c80e00e69510321381c1c8034485809400d80140b8208510388130b0394420055851345e8113554000040f56039100d03a415090010507a4115024038001c1003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 547121196 1250 547119946 547119967
    0x10207120503040305070623010806011502030708030601030902240d0506030f071806080313060905090c04030305070c080d110c010e0109030f031106041a0c1809090c0d0503 76
    0x540c104010300381c240300e415450241c2d0010802d00c100d0340001c2840741c903604015031028400071070354050003840d1020842d56850f05410796591a0074441d0242c102c00114000c0d40d45030012003120b0503940c125856918603907039680103501500c0d81a001302d030890058031001001110311b0030450344000402ca0070956586100500c2c000b601c4010782001d10a803c00c82c00f4441c54100051810119403c02d564030105988244034035004003500e50141c3c080f07000c0040c90107403500f552031110341669001e80f01c1e510103e0702e40c2c040c40a84002161202803800341003100740040f034000c80107801035a1141c0801c0d22001c1e1500d03c02030901881088200114503400b0300008021020311003d0240002032800c41e0789144002e0000704a0b80141c400501220081c058680500d0b100303543c00503264806400701c81c40c90501c1e00e40b21050909003c0b509605520950100d4144183d10303084a0880704804048a81201d48808020000e41d000e004600c0600c10718015190a4a074880c4d505000f5008101468070f5a03482c40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 547122302 1106 547121196 547121213
    0x141503010f0627051009091704030302060708090d0e0103021305090c0a090b1c020a0207090c05040306060e07020a1e0c3011011202070212010207 64
    0x80116000c2100350314401191070f0500d1a20400004200500441c0e0081e64110514603003214200603005064100c10700e1390303000d0380140082c01c48510302c0614591143e03004802513000001005482e5410085c8076502c4440314001e001d800300b02c04401891a110b007500d02d8103155010035401c2403241032401e640d018202c06440f168890800609010103a0014400303880014118280465419a40001c1c0c8500ca0303c0304d00740082c0104000b07140030294016030002011440340c002c00003a006824015a121011350380c455903540c60440c10287c00365405500240118054001400b51003540010041c5507603411000d07195841a240c20003800c516583c0c40058054041e1240c00b00b41410034040ca011030800d0344403440107e00da0120030340050307401c126024202c64014240301c003040d40510804480044011001890020164001003165881e540071442580d80866444100603260 = true := by decide +kernel

theorem cover : BRFrame.Cov 546942446 547122302 := by
  have h0 := BRFrame.cov_init 546942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 546942446 ≤ n) (h2 : n < 547122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
