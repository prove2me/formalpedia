-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5452
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:54:46.926533+00:00
-- url     : https://prove2.me/submissions/fc2f8353-3b5e-42c0-b0ea-0fcb803c76a6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 980395683 ≤ n < 980575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 980396933 1250 980395683 980395699
    0x100b1b07060c0c0b130302270903070218090c09250e0307210204020310080f030702030c0108070201020c0d08060a060503010e0c25050604020f1c02010f090b1611 71
    0xf154400010b00b5038007000000390b210303000310000180c41c085940c00a5804000e66000c4480c8500705c0f0302083d89a89081e004d03450b1540c807020b00301c1d41c900c60000001e41180402165124407058000303003d42103501e142c10f0343c50f00c0303d4000006000349020744883c0741400349070b441d0250a00e0400d00d40c009a180f80e0520001940d075020001c0d446958038403410000d000c0707420031140c008448d60b2402072200d038010021526410503840107000702d03905014456252152a4403686079041c00025642d00da54002d00030120031030410300442c0c40000c0604164155902413101d204ac100082c04840c01180301d65035000503030729020b020407410641907448801400802c20060114003110800d055008400010050341e4591000c2520340180400d8540c5408010340350020042003030203e00d150040d8001c40700c0d200100c20710340070810101206602e0468401802000b00010350103081c0780711104445c1c0c100302c540295180c912803070a50096a0b481c2c000e0b8148405c00c2d041201755807150004400944540c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 980398183 1250 980396933 980396957
    0x608010e04020306040803060103020f0408160f15030b0f1e0118180e03070c0305030706050f06030c120c0a0303090e180709240b0c15090c010503100b1b0706 69
    0x3620313038001520141000d5800400250366900980486000108100e05165035a41d1500c40907151122030040207080b00a4160002c1d540c801c9050060580e250200307129008008901c01b940109141e102154100070b20f241c1c050401d80c0e17000d05090000c19528040343c0382409070740004000700d4004622489800d604c50040c060b15014140d01464600304400004440d00c3e01c5882500d14002ca0000038100304510070003200304480440582149032151800703000ea0780b03030180c022f4403030b0608550310b6402d43d003c2040483c1520b000700040201e001a601522503c143c84000306000340c01c245c1058020450106003041040381132001240d01000c1d00c8480c1c1002304015138026114285031241e04802511007000048003104662a180481c83c1d080c50b03448500e03991214560300341c012400e101c0e00790240c1c400141c11402c40c000c85511901000c00580700007047d07000156400d80010342881b030461600c080100b25041c0c017070005c052040042100201b010242c4161914101854000d10104001141d0301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 980399433 1250 980398183 980398189
    0xa0201030b151b0726071406091918061706100506030c2206180e01120807050604030e030d020c13020319050a02040911070c05090c0d0203100608010e0402 68
    0x50f4465514104040800c42c05034030394185003400503044117450700030398030140303100721074401606145160480035100c03503e555103a1a002614144c2c85503070844020003c2105515140391810007049007404602d00032629008a0861074050740300180c0798540d03910702888038070700c1640070300802c0c1c1020000340007510741003015003580754680c42403a00030000400455045036082d400c5d00c0d40c0081c00c10000c11044061080004c0481103072003000b0105210503000c50302000400c21040a42c1c10405407002140d19008801000500c100c030300356502d0ac0180001000280103100c6140501d010350394440306c10f44c90208050a04039502c1c800c5055503c1103c0c040c9441d22400718420004481030001a201d5860714580540624150b44071483c680c509030400581c00490344c0a0310503100801401c001c960b88604092121388554107000e04948000c3d0401c00580c6420702c54160301034255282d06007403d005079003507426604141d41c40d40c4100c04620080c07005961003c03180740141200c808420090401743c002c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 980400683 1250 980399433 980399437
    0x20d14190234170a1406040c06030515010518060d020d06170703030e181905101a0d0207050303010902090321031306060503071d06031f09030210020c0a0201030b15 72
    0x2d42005200034a2962003501c0d0a00008440d15000001c5c010130b44c1c000310700a030b05d640c800c6908841d041002c00c000308907144a84515440380c0d1550ba041413031140803200541d1140c015181d800702c0c500d022111200300383c41c0c1401138001d000c4900c0340940c03542e0301c3e00c0c0b0b410151809a000003d0421128061000700341002a49004407a01070400701310311061200070a007542c640c0310a0856522045080c0b14900402e1800c5048010524100300404d4580ca5001148a80f292066110b81f0103008500710182022071700400c000d882d442001840d207011503940070f0030350b042640003072075442d40822400f105060030300c0400180b45111071140e001f00c031050a039441a00010b007009960b642400386076030800c0744a42c01a40942002030858920030359902100690f000711200e44801c0029210110300c0341d090000360403000c160040040010000204000d00c028a00b040d400e400714410301711500c210814510090500c0034124010303080c0007020f40000740c01d903075142c40c10324004e203402c41021101d41d540c6d9003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 980401933 1250 980400683 980400689
    0x1b10080601030f060b0a0f02073b090f07151b11130207020103060806040305090d08041509030317061302090d080316091203020d14190234 61
    0x1080105a103802004030010b094034582103020600e000c030041481002c01c00506900e002035910480e05a001c00c10498440d1210f208905809c0b5000311118152a201590080d2044a00080201c041d4500d0418245a441a00c80d00c5043d00808200c1590003800d201ca00d020b000b0804036005541403000c00100010380c10f0f0424170507000088181c400300409107000d03a0b80e90100078400242074031041c1c0410001c3d4000300c0120301184c5032400014003030030b020910360310680e015110b107822310201300e007406213070400b000088412010400c008110002e4a131030404504089568400c0918218a400780510407190008200015600208802c0355185010681c51400d40d92002d40c46e0350380080400c10002c0c081d103000301010300110806c1099040480c2c500001c40d8150307180c0710b5081d0703120300384240616007003009001600000c101c40b055a0040641c4144e080845151038540303580b5004000c02c039041c2002078801038010b80c65407000200b041c810140000149801c4d1a41440c01200c5180c1109242c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 980403183 1250 980401933 980401937
    0x80612011a0114070b0108010c031416050c0f06010f03120518131811041d060619080f0a060606050a17070c0807050a0201030f0c02190c08070b0306031b10 68
    0x3403810f85582d40080d041d42c10f0382e0761244050685586400c4000d02a00e503407200c03040001e11700350384c1c882000540b002a900600c00c80c5101d480e5402d00c06000c0302da0b6400110800700c9807040d00c01080703000c40d080000b94001c08041800c1d00d002411031a02400794007040f038007441008030504c48107501984441c0b204046a00403180340c0d0061000c0100c0b84054180c0400d110b07140306500740391000780071503008800d10b0030000301c0c0e080155000e01100f171410404c41c0204840d1076840f5900103011400c0a9940006881e0320445114000e662609014078069404034200e84a8000f00c10060070804140120030281440b42085800d01c03440d40e50042c03216600c969042c00808120010030482c9000320441d0070461703080510599070f45014213046940f2181158200d00203071030614502094550b034419070b060405180d01502d01d130b080c401004890103020040c00e43d2006112400010145410080d60700201040c800c440d032a071074041e00300340c01d200e440f07420040c01300c0b03801d40402682e60329000d00034020342181c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 980404433 1250 980403183 980403197
    0x306050420030c190b0d0b03070503060103030c0b061c0326011401080a0605090c0a0807020109020f06071a18010e070b120a18110f0a0e1902070204050403080612011a01 74
    0x2424130804048296803048041100002c2c00e004940c6e000d80101c416124140c0c103c8448503603030f005055480b6024800a0001800043c8400001e11a90680da4000e00014050340ca010308080d000c0403554851042203005c00d20440d1002c0111481c060022800700040c81421040e6141502c0c1424054001001904000c0801c000600c040003c0c1c0c058009032030090041d00a6103841c1403595130070340c0102c580c00045000c0300000396015205015004d5034550180410391814425814040d49412220b802c46400d802c00c2540c0040d110641905c0384a001c080c0000345580c071400310114211604052030409035040111b040c4036249200f01103841c040e030010388004160341c2c0d0440b08030082480058014511703020290301e1046c0140c0c00390a242d0031800310303074003112003000360204180304000e0712600750000c0c2c803c0c0014810006000742000d5040c07451001624000c040d90004040328000c403400c4000c60102424040503041c04490107400307804480c000c015910410016080307096541441c80c1c100031803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 980405683 1250 980404433 980404459
    0x40c230403060507050913050c0715021225020613030c260406140304120809190f05010c14040e071205070f0216061209110603010306050420030c 64
    0x440400c580080d500424100824284404010800c2e800240e4440c403660b030f801d00440310003901c1d124079800b50702601d040c6440c0c1115a034500384885032150003180495801c3c85141d40c1000c91404103441036110402001c210286c014000d00708000307845542046503c000d007084140c00c800c00c5d0b4010309541508010403081014501a4564142d80f042c42c14229003102c191494114000058425241c040d120309504180b0124020082c0c0021503000d460384078080c801c0400e042c003e51080d50400c00000a80c1c00542c03008402c051140c480c08400c0b00d4000f448868541405400e2240141c103909900e801da0070302c04011340245050050380920007810100d0303000b049940b409001c0f482d42e00030b01c4040a00c814980080f01416014200c1100005401041a240f5a04031200640c001340c0c1c80584520703069070071900a0200410000c0021214508100c01506a5584090285000310700c2039101083c41e18143c5170486200d20503540000c80300020008000d016940890340c0d4400001c20707034072000c003900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 980406933 1250 980405683 980405747
    0x305121201092f120609280b0a08070911031003080c0a060e010e0c12030406080603010e011404050c0607020f090703090204020a0906020606100807080405032107030506040c 76
    0x1400d0045801200e0700c040342001d410088a000d8004e81901e41c03040c1c21540e4a01e024001c55110480f002d503840040481444400d00d04201ba101107004080400188101130b180400c806100c241c2080b942940480002c0050b003065004000c0e400303070f88000036400e500b0f0504018000e0f40b0749000090800700041031349407941030208000e024a5030480c40c24800984003d004d14001e1100000c450b0040c080c42000b03001c40d0034401104005842d112000b54641403801108594104000d03018070341c15500c5034249a40a0401d00886c000c545070b2014095007414141b814519242020203000e0240d4418003490b40540e50b0f20b05032483c5104103480e200039a594103407088004102c00040250f00c24400728103489182d5000001d030080c1d40f9103401f140d6181d15000704010610740c0d0464501c00080307505001a55440c03207911120b41040c4204222401c00314030342101d9500e14081e02c0408002c0070300d40e00f000040780d40f42c0265908640700380d4080115501951004042121030080708500c800701c003281c0140300c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 980408183 1250 980406933 980406971
    0x605010c031b060203010e0f090109020f0111010608160f0801051e06010c06050f0a2009040e0304090507020c01030615020a0206090d0609080702030607020613110409050313030512120109 82
    0x143e03c0720741155a0341e11982d03180c4a213042a540b40410030080300008807001c50510958191980040c41c521440018a00445101d611240d004071655245e0708000b4121000700030a10742d100c41d40568203512070414000310210600c81d401003400340c1c14030061002d444004000e09002120005030824140c0d40c0b100113864006661304002c2c8107502d8070b07081042c09220a001c1e030b401004028800e01c100d480c5505841c8404001c0b01c1031200050082100118500e4683e04c0640b0071019001500d0500d43c0c1c030404142219401c40c2c4c00c0016800c80540b8000b65039040c4900c2000d00383c2411122109110100001d42c0c810130110300a0141600060212103503850a46020140394007a0341801030070312615281001d504504401ca01901c24030700414115400468400d00c1100c0540b950741c10a0155220282402d0510001a4215a032034180101160707041c4004e05030403000c0600d24941914502d003480c503f06552030a6104000180500400b10142509180c1121000600440c00034054100b6100c01e0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 980409433 1250 980408183 980408237
    0x509070609230607050a030906030b3312090712031e020717010608070506190f0e0405070e090f15090604020d0c0c151b0503090c031902040f0605010c03 67
    0xc030004c00c0541c200b000000c3d607100114801d0f0340344840a03940740020f6065588054409a01001c5000103a04e0202005040d4101400b109044414a271040a07180540d9100500c1110429141000c01a0040080040800a2100004909145c2d1403910018506c407901c01c205c070741400c0c41d00b00903056103208100752809800f280c1c2e904940c0c111481d4100b4020102031003043c030f0074002c44200280f14a00803040d905500030340c01d4404c10906c00c400307040710b0610584c1c43c0c1d0402d100b10300d02c5040840d195882014850506519608408401c070802c101100c1c3c0c00601e4a04521030a00030850070380084180f01e04040b03400d40340c18a00e9190800040c2c0030b4094940420551842c00051107802d690194000c1c0342d41e070080d44041c044d01010b044a034161514401907480241401c0c00710080305208000071036022203c00300b500c00c0d4491140010f0300f0080c0400e51640018028030100c829464180300360140d034805064100f10103454000080c041c00c0140c4405010300c0101c800060b54450300c0841c1e0300c48 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 980410683 1250 980409433 980409439
    0xd0f0c0f09020d0b030303060105040b1c110301050405060409022b0f051c02010608031c0209032b0302181011010c030507030606020f1203060a030b0a0f050907060923 73
    0x205840c0c225910003900990283c3c55107074202424803031541008021a0300400c01a0340c4e02e0700c2c107414080c04192036408960f200105420600c248012000d00d8441c1e110301c841c1074100c40c3d030b4a500d04020401a140041c1c006445a07103040034040043c1d0301d40c43c040319042c1e04091040b08007005448405c500038a0b0000152082a002c4251000c0250204589441c0d18100300c0350301c100486800128201c0f0790b01d00070500b440c1e000308600c15240b5804039000074130840c000c40243c42c00b44900040707420490340c100b404c4801034511020b940902c07441805010701c1491454218246004000c0b56504421044406805884d040c568007416522841c400c0421683e40c80090102203060103005000b0101203c41c000000e04d401c401140c100d202060140540130241e00030051a000301c0b4044406920180c01c1c1d40e480030740c0300c400000041d200c22095101e9680030b100016030504c00700450b0309452005120341c0c45900804014414160401c60704420f0390404070a107503440010f0742e0b15003414440003001d158 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 980411933 1250 980410683 980410709
    0x1a1905100503060c0c060c0301121b03140604152c19050606031606020303180106050d11041116080c0a0b012c090309130b06030708040507140d0f0c 65
    0x64081540c002041740c0d000c800201c60883e0340d28480100700d4082070092015040d102d09030300000c50010310a88079074810701c000e00c2d050603a0307070b035284000a042c3c10900c41c00c0340c201c10100002d00074070a024141000c29800180100c402d0000c0700c60455244990f017102030f4807041f683e00d80c0344104000c400c2d40b00701907800040c0c804219003403090351107500b190843c0c8030744039850940d10440e031110201c100312500f9400560035500d8648241e035480703520564101441d0b50741c40c00020b65580d0604014503482c020502d54131112000401c1c4026a440c01c030842c03049440030841c42c3d03a81c014156104950f90342014133030380c8420030205c000d405c003010b00002406601720440003140307400d620368070f1106962882c44080a04a5142100c1d40e1815048a5201e00740c2c105112403602c50400c1c011101883d0042500001c03003005403000070305181c005654035000140c1d035004004c2000010880c2d40c0207080282207400d1840130320780010b80e01d0026890700034801031400c0d4100e030401c40454a41c101408a02803988 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 980413183 1250 980411933 980411941
    0x18030810050d05030705010c050a0f030504140619050c120c0703030b03060106030c17070f0e030f1002040512060402030703030e030c03010509030a090f0b0405101206030f1a190510050306 82
    0x213070362500310300d50541d259423038400d00f50035040c01002118071740030040d00c07040c090031041d030f00036001080300030f1003903401e80368402c0203c20000007030190921504a580310b040707080e20b038410100c0c212080149040c105420801c07500402800302d082c51640080c00f143c200c0c1d500c2c601ca00c0e085004e004c100320b14603014800c0e10004581c481d0540c001d0b252580ba0390740c600c3d407124a440801400403030160381c101c0c00b01c2c2141c064034099512070300c02070710100d03000b8040710020100600070a191903030909100f038044e0343c0401c0601081c0f500d0403887e0358801d0110b00802c094145034000a0300d841d16884024140b00d03190035480d040384c9080c41021070317a45000b03008110714070f4807100d4162660310800a0b180024400d420215205460005203001d940c803502d50f0f103082c40c2c18603041c41070b040c0c1c15038200303402d0101103e01600000b4990150030051071207074450103884846450202c00180042a1007580c00b440441001f020900348a240c0c01404040c00000c22540c851448180000c182034000b0350701801500c0c108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 980414433 1250 980413183 980413193
    0x70b03090a060f0227150307050f03130201020c092e03060c020d110106140d0203160f03230d030c09050303040e041106040501050720060a08071218030810050d 70
    0x26010b81117011703e6480340400101424060550004410342c2d02514048030b01802114060155500c00118205a89059001080a11039400c215032580340140145500d50465078180305404e04081e050307132200410308101441c240c480c0d101484105203441000e040502c40201481c61030020364000380100104008610000e4a0724040760300354002c00e841b078003404102c3c0310502c01c103411540003654202d40102e8440070003988200b20213059070705100e6030500400e52210541c9030401044241e10142c1c10300d1441c07034404020031a040001503103441803002920f01c5403021905030f0322080140b0340010000c54144080e900c84c4140d8110940520011502107600d6500c180ca0354022401514400082c0d2040310801c0b000c1d02c243d00485c5e00085080c46001e00041c8451102400e060444203001c217400c0d080004a426a004203420100081c807a50600c001d15800162400055141d84010b001c130241214150868042040f001010401070708002070700403010080480c0078200040500c0070311000341c01c3c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 980415683 1250 980414433 980414437
    0xe0610092409140702191b03061e050a0501030309050906031608010b0a15051c09060c030504110d0c15090b2d12010b0903030d051611060108070b03090a060f02 70
    0x82100d0158408680d1300d40c00090402c05071b00d80548015205003031a034640386101102180003460404013400400001e40c940501c03010b8182c101a041101c0007606501e10030f03031b4000752680d0724007841c0c0401480440e5120042d182669800d0f14194119151100441e00e4104003124000040b03e403110041018501034004102002c400c481012031151100060440bd008030314a80d404602e0401c040949a400e90203040c8242041400008001c0398607220314013035030040d64401c80000d684408002c10070841c2d08603c0b03400309094031310a007001c01642d40d0464042050050381d0320203160030801c1c0c5c0c01d1442000100082c0040c40803958035544000321b04107480346c060b920301c481090b042000314030105a0806032440c0c1030807425018131342d034600500000e041e84128a43c03a00f5010400000461100d1070040781d0040881c614851031489140c0700040000070a050a01800e8024000420650300c002410005a40100d001c00d540d9468120005281143c0200020030781d500300304c803101700c0e41020f0f40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 980416933 1250 980415683 980415701
    0x715051503030f0d0908271215070503092b0215070912020a0b13080c0a060c02101106010605031e041e1b0b0c010e0610092409 56
    0x1040c4100caa4160400d0345038001d000a603203192805010140141040d600f2126440e0b0258442e1031038242c0384120740015585149402c80282c00c030b03082d610181c3c00c100c1a15182848044090f000d0410641755401c0713401c038041d01c1c0908100022000c606150410b000724070b240b000e5102c8110001c101c2030290410704804528a0026008100c08100980348000c8940d104241c00d80d1065402c505101c2c54001034401e07880c050303130094941c0001183c0c8c815248002c080e0304080c81008441d00746402e800e50b103403034801019a8065986c40200300f00740c0350030103a0304500a90445801c1e0b0f1200750101e0482d141810a800340c0e02511585000042c03842c3c000340194004d8600081c0712518035400700d1601d0380400180c3d0024550700b60152000c041030002d1a8540c0740038403824400c01010507038500090b40c0009500030303244001c2c0008403140e6030b0900f441200403440881c000b44c07507245000c1d1840d0444440903c6401081070322440b070140c0803080d408910402601400076410020b80b1a401400107043c405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 980418183 1250 980416933 980416951
    0x111030705210301051f21020306030106060302130e060607080316021005071403072c040f06030f1511070605070807080613022b0e12130302010e010203071505 70
    0x1ca141c01041c002c1002c0f039040c0c80b00036101e28004110031141241e400c400f482d001d0204983c0344a59040d00c400c50390303401d1031005840b4000d0f03140d0401c0c60400d8219842d591006051510401c01224002c0800f41c00300c0480d101810039200c02d580340c1c1c0c0420300920640f1002007106100004201c200001c410080b004114617508580c501509620000100d070700c191088800314489521811090342c12900455000d440703450898140708410320429502035241000d008a103001c0002c1c966103060510550b211400b90300014800e09203551241c2000b0700941c40041c0c41e900140c0302242c0c02000c1a004114148800c640150740c03031035030381420380003014103544480c001601c20b00415a014130540d1110f0040c10010041021028041c0e00c402c02540040078844030458014102e950507450040aa2101c400149002c911142d03440001070401000003451040703d1000d1000d0600000100050300580740d0a00f4041407101135000141d145008010000340a00d952030400240018603401c0f4602542c950 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 980419433 1250 980418183 980418223
    0xb070308010b03100302512d040f03030e2e030e240405010606020d0c02100512041b060e010e091317030907050607020306060d020111030705 62
    0x50b01c03400c44244002c0c2d406003881c8034807500c180094074148098101c11020106414409807107008120007204850650400c180709122240e142600740311101554240a02c010b14500340400648542210a510068007507203c0103105c010400b2501088501a00c00b121643da4030355520310b0001d007244440c2c402a800780c550450300302451034200d0417040d2044546e104001d0b4100d2103040881c010400c140802805100d140d01480340030021072100305601b860750b441c10445181c2402c285081d00c51503809101103500c08110391484940c40007c0310722003030f8111141031042500500071601c0e8020300c03218041208107001808208900d0003c5200f516a0209424480c00d941d0a000d5540c2c80c2c0b02c400d0304d404500b4414183c8240d16150508aa01402c1e4640c8008900c030241c6030381030031b01e07a86042202c0c400320010a2118841c030070021000100401c407500e610701100c1d45c0c046501d54501600d514003400521070302c10b017161b01405000100800002c1183d88400043c00c1948c2d40b81104c503c0c4103021040313 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 980420683 1250 980419433 980419439
    0x7080c1f0605011b020427030201020c0705030708030a050c03041701020901020c04050c2a0303041a060d0c090c030603020616020414010f050d0611040f0501021606080c090402070206040b07030801 86
    0x9901340900341c2006241c12800c1c81056000c0c00040d1031010b080b605803501040d90104100494607482800601036400161a0301c405c1140e01d140c203000c1e40110b40720340d11407041040a5100001180c1042010340340c450344071031b0071031031040c510700854000c01c01c8001647c1c19034000361415400742c41303000c10980c204c80d01c0401d078a003800119041561b680b1425141080801c440c0b5102407103a00e402c10500b022415040b0500081301c1c03c5400c1070b58100d0b035511020108203403d041084402d07800c000d0490b0594842c80c05943c504005801602c14403041030346420304020b1081c044d0388100c00540d0050400c681c0d51203500120b280c000e17030b8058200c0c07040e8940741c01d00300400d061000580c1620381c10382912403d94106010044101c1d0040e01c1125029180d401c03e06130580011b010300f00808441001c000c0450a00303001909003190f510101000b580d036400c0800003203503c40482a08241c10850aa90b69079000c404507010b03104100002e504510001b400207007140c3c7d0a0000e1941078002d40d43c040a40c0d81b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 980421933 1250 980420683 980420687
    0x20a021005121807090917030106031d1c1b0c06030507090f0b1e1e040303090b070b22050f0309010f091805150409120f0e01080c07080c1f060501 64
    0x180b09000003d40c1c0c4812420710a049859000300d040707034080c040c5182140c040d000a45407580c400d8009000003a111030080d0610010096281c41c0c1e80071b444050301c840d28080c441024417151400d440390811407070021550303549841c481440c04680d00311003141d13a038a4032600094043c080c25202c00340060744140f8009040c1240340f9103801914590008a46855010a0b0b00c2c03042c40c800ea005112132460400c0803905030b108031039049041000300355032070752101e00e10700780582a42020b80c081c00040c0d9040200b0000280003a2040345d0200300b20750401410307000c2c090b604000542200d4001c0052068080782c0340303400310002c05050321a2007640c8400e960484c84400300c403e607803684100120703d001440c072120f0720041c50300425406007241d4030f0701140c0f650081c000340c19641c0d140403c2d5046511043c000101d10303800b03d188442c0d080b9904281c2d200f0424400000c0503503600800e1411100b1000c9104000c06c50a1350032510060f0900c0c046400740301804d1003d94030700460f01000e00c401d030729020000882d54 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 980423183 1250 980421933 980421961
    0x1809070908070312030b120a02011b020f120c13020c0c030d12020306190e150f03031605100203071806170c0d06090219080f060a030210020a02100512 66
    0x150820002d04000c0386503a64140780d50714284d40b800c052645800380d821903a01d918030703804d4072100204000c0440500500015041c0082d0014000c0101042e011040c00350b10f403050f10101c4208241c1d0b030254048d515000c0e141c03c04a88480c0f01d0380c801c07400944100c640500d5000b4100c045e805c0000d58501515903000c06582d600c40c0018900880c200d8640c490b41d4151650165600800292200b80008401551194042d500d6040a9072040c100010b0000c402c1085848025141054408124203400040043d0f03484c0580303987c005500d0010710004042002c140b0282c0d041004400e41035499082c004009445d191448c0351441160707048200c0010302c40d10650041010072001196030f19207860b407140250b100d41c4004030b0001c142e92036038000074014460340b00501d00710f070480c40d055808801188008104840142214422480f03e00c2400384503a45e0f41c00344011a6411030700810307159582502642001c080d1000a544003034030742c1300b0300c1816821000511201000041c904405d580d0189171403200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 980424433 1250 980423183 980423189
    0xb040f090608061f030b0c1b01050603030d09050c041b080a15030f030c02100905040c0e03100b1f02060a0f09030e0108090a06020d020c010b0607050d050f0f18090709 73
    0x543c442000300b80e542c814801c1c0020360140c0c5055100c4c5040e202d855190304103105480c406501e802c0021050340c448461601b401001a105000744294103040000950b43c0c061890105c0d85907030389042203c10000d04002e4480c59080181c424042248200c4601c0c59880c0c01000b0303600840d50302170000701c03245200d20a40303001c0324403035906400a60644e1640208140840401c46c02c2c00002000d4001582e40c007060241c401d54555503414515041130f003400103407600c0320a080240b207271400c3c8036842d507600400c14508081d0300e000005135446c03c18001601c91f0450125210190f803038403075180160b03a4041021803140d0150f6909201d240c04a203103000c211800c002016001501101450420b50712412007582c1290104044420691180c0c540b030080748d0000303500c5a0307295400a00608000d00038040c0d42c4101c5002c8030824180700325501c41c04e4a03689c1c04401c02041150004016000c980010b050741e124103a0302c0c3c40aa02c03074070b21000c0720f2404400801d4031445107101c000085c25031403098803e001031b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 980425683 1250 980424433 980424449
    0x7171305070f030b150a03060f200715150b0f0a03140c0306010e2227170306131a041a01230c06040305130e0c0a1b0b010b040f0906 58
    0x303295100003118110700503030304170a5485920035000102259281c000c0508038003020347c00181040310440c201c040d4040c4c80c07207c00034881b002e200c032201240d104000c2c400500c1400c0f102050124001000200541040d00300a08022010a404014142d50f40151010041c01c0d1070800101c2000203013021740a0044a440152a41c00c000050080d4801e2000c03c0551001a0040c0101140383c00c0500b0495166503d504005942c0d070400ca103864001c071a40c5440802200c0c2c01104105161030301025512200138100003036400101164240d1190043e20020b409803440070019140200c8014140445450801d0300c950300f0708143c5034042050600c2030380007660584408028002c20768101480c02c01c0a542d40a0b10f0070180500900e4034014000c542c0714034402e1b40c03190364900240030a008040090340100b0f0300e1034243e400f00443c42c070207001144c04c403c85a04114200006003440000031540c6442c0041803500400c1c00000d0502d83c0e04064001d85200200581c0c419464914001c1213401512400304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 980426933 1250 980425683 980425703
    0x4060308070222021b150702060115120518101103060d02040603021021020a020c210106060801051804080708160c0305060a0f2307171305070f03 64
    0x43ca03052000305070780060940c202d5052000320046004a07040450f200d0700070003c4000c810148042480741150168402d0070403610340c20b000c24000e40c0d620b014082c6180f01d1303107100e990810b081e018181d041510784801c0f0041c8894a00800c901e591040f03041c000c4401481951a80140d02885006810103085040310300713030441c0d0322041000381034501284142c0e0065070b80c04010015850b4503600c4141c0c843d5684980c1c0c1e08001410001d56940da52548e042141403040c8200054254085009021850112800740b0503400610200d500404e507a00080c2d20340d0705e400b100140041c0c01210260488000310f90417510350482c281d0b2903a110008075002000180108040d000154410002c0d0408401c40c40c9007030140ca0303655681e801044100e800940307850780b00204200040150740030354401d18000c91420321202904810004181110f01c000c0350100c90b0600000384094031070034440301100361004000f01a41810304070703000f0036541034030141c0300c5014640303012403c441105080c00469a0002d00e000e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 980428183 1250 980426933 980426947
    0x5060603091b0d05251208030106030f1d010903110a080405150c06070203040e061f031a042a170412020102040b0301141e1806030109020901032004060308 68
    0x9001c014403420b0039074440c02240c00080070400c100404103111800d04104141e44419038000303a2410000d40c0984e101c4c901c001c00710340c0020700c0722007503a04442d42030030007040f040c0602e21040042c0c007110300c5405500307042030102840b240054201401d03090280e02d4035038000a07a001c020742c480303901c07080150000204002c200524100204442035056404402600300a45134030000c4c10000144c5625006900c0400c0c140410b01540c0c40040e0400d404070b0f481111031440c13129451440381480c204005259540990000b20018551440041000203000300940b54401c20314004007004000d201c4a5580e12502d1006200e00811018000d600c4004580105e83d4071640c808071102c14109004046540030b000003e03a041c1420302444c060550040266401420f070301c04d0100c80100f640e402ca8549065102003640b0b03444056550700c0e40600400348140a940301008a4050080c00364000e4014084000002c10b0080a4000000c0c010200d0b19056403041d07004104401c1d1112808040d01500c1d0800103c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 980429433 1250 980428183 980428213
    0x60509030c210c0312010e011e03030c02011205090f06100602060613090510061811040b34020a0f061b060e0d09050f0105031005210616030506060309 66
    0xd80b5000c0e0010032002c0c90b00c4500300d00a403c54101107642e0003802d49940040c4050341c40c82e41c40714050400341010448070340001c500c0c4562001c032480b001d4180090000c0e03031b01c10341e4812410068132011480342408a0300340b00f190a81c1e522403203034010310140519408104618070345450f6104444071039008105a480341d00401040301c401000c07081e140e65980c1c503803400080707003800040c043c1510a44001001868102c6c0c0340105040101d604041f1440e004002e4801144042510152a400d03480551100c03a0342524200c0c10440d4883c5040c40c804071031602801d030710700385820303000c0c5842a42c2c10a0000c3c0e840d20000c40c2e4140da0b020300c13404960000103101c00f11451035201c5090324091030000c940440610900e6040030707649011007000502008062056003001501c00000c0c05d42864070a24528040d1080b25445105010355440323013011100c6024500ca806004101d81e40011003900d89500b0b08a0803003a5104010401c0070109042000107901450240141d03031182d45000017500c48902c0130281 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 980430683 1250 980429433 980429473
    0xa0f1d09031801021006140109050613180608010513021512070e1f090504051b07020f040e2a0d030f1116171c0219050c1c060509030c 59
    0x44504501c21083c2800e50305c070741409008001d0112003000121001d00d41c0c001400c00c20590031460003000d00f00050f030300d40d4200d038514800700c9050104910700d90300300141c42d4024043d41e6000c81c01540c01e010503c04208454201c0d454454800c8814010406440a01e0300d0180140c1d03c0c0c00e103511050a0000794058010880a45916002440b001960101d4035110203030400c4c20701221f001800d109014801401e103849000c0d0899042c0011102c2c00d031900100036064421194000e0040d0000d150700e01203038580c1d8204401d001c0f280b0781500d4100c11030311501c080c00701d613411030190f50301c50001140207103052076150135203026055600c0b202502c1242c0c1d411741e43d1140d00244441c180c850581c1107c461405000004041c04c102015119aa5101522903250030311120030010350160a41101c64a15000140491040441004280c5c026214102503090100307042c640d54000f07000e40741c9040e1a069041842051a100348820019504c0b000c801541d0390083d00c43d402c9040d4000000e0154081c03110700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 980431933 1250 980430683 980430727
    0x315090911060406080601020f06130201050c010e2e0902060904150302040c020f06061207060f020f010906140721110f131d0601200109020a0f1d0903 66
    0x1100034012894a0224242e80e1041e0b12000004e01c140c2d0900c002c66a05100380f080141d040702c02881c10303081c000da41c2e0424000d4500024180400000c44641801080d0096144010b100c0d09542d40c840440d1500101c5041c44c41c4441400e14041c5010b040070b4a0912603c04080d0700540042c0c02c0100d41000c0c0b000406201107001000c041e00b0728008016611030045912054041e4083c08800d8034450340c00345032036009020107220b00044c081d00d40740218001f403044212000c07407400454014505000303038140101c10b81201031a50a000d040e4040c00820380003510b00403107101002c00595214802142d0343c0d01c94245501284001d540c031860300c0f40058000d084040304c0d8441103442c1101440713000010307901a244600300f1090200c2c04101900394844601884e500d5848070502030302e00440001c0c6102d008a2140200000781a1000f1142c0d000350312171504c259014100301072081d16121f00c0480d20500784a400c4403500c0100144540380b840c050074501466500d0019420890303400b142c17001521483c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 980433183 1250 980431933 980431943
    0x120203091005060f040533062a0a0f0c080c03060109020901090906090e0606060a050d0207140313231804170d09020901270c050d0e011b03150909 64
    0x1409906240d50714446c9038010400340300038404140303406100301080440c11b11400400d51b00301145c40004c1c3c841504481c0403011064400100f890341e0581100355001400c1c02c1030181c40b605400c401080400e42d088207005010388502607a807035954600030355904a41041c42d03010381280707004001440090300606030141c414101001c42e961151180e004942d102c2e4400c00302c090700c1d80d00e000814041408141d030003480689040c2d20745882c0c900060520b104050014002942c0080c8840c1400710800d245584041d21200382d0355140348054001d1841c022500558000c81100c0a540c2c4c00c5000d03000140e403101c0b001910091100002d0380c01ca002120005005071901403540d08078020025408006020944000500003581100350042c844c1054058000720041818000800007006180140c511514000c0e580031400c0308460f102120b0700d01404408209480c00c011996100c110306400982c00344d00800c18071003240084400441c2683d000b00304480f03481455210510841c940c0e0342107981c640d8014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 980434433 1250 980433183 980433199
    0x513091e180b06221a01050901141303080a0e0102060601020712020904051204060f09080601050d060b040f180b06300a080406032705030430060b0112020309100506 72
    0x15060014590088140c003a0207150303501d00d815620301301d50145d0540ca4100307180640c1461a40c800180c0003803030700b182c00800c12401081d48104103a00104520246500410007512540c420710040d145940842e0098054001e51002507000c0d480003c803201140c0c4010254110a1025028044042c3c1c0142059649005501b00252070540c1340c40180000c04e190345d0351150a005002c070060440c1d00541110701580c0080c4010441035407900800704805801401c0001d0980c09000020000c004800300c104400b401d01c0c60b900f509508490b44140c00b1806071802d03251036030303803241001003508440410f060304034029074030961410814480d40b079000c1010022200040700644a04215800070341c0803100003503c848040010203010108065041c000e25580544e81a6960300c203516401540605500402c0c0304004103101100c2d1030384801c02011246600d213044000e410f00401a0404969090100c1c81882c04207400704598070803607214007403003c068110404c510201102900c0d02608066202c844 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 980435683 1250 980434433 980434459
    0x70b04060e0f030301152a12020606030c120a0c0b0d0629031b03040803160507050d050c0304030204060806040b09030a020a030807050403082d07020a030f030513091e180b06 76
    0x10400c541c11090340d507204107c400c2c0705460f00300070248901080300c0854000600380282d44c2c800082e000c41c1c010044070303a54100796820365544d00d00181c003240909000e13003c8400066281e1860010104103600e08028010903881d090400c089040380820240010901c00070301b03c0c4001c000340a0b517040380c0c100a0b00c54040781280d061114030303041a6400c1c0d4038054000148080250700314201c00680005c2c0c140141480c1e4151030381a103c840c043c0219051020000c1c440703c0100c3d050044034091135009104002c40750700c40c801c1c26524401100c0c01c0714117080440208184140000950303021847d1030b80100540e030f0b440c1d5011912000c014045800340030013030101100158552000e00702040d06a060342001104651440b401280d2104400b11620710400602015841e42e660b07603400e49400001c1c500310100c19180450f820301c6640350303124000100540102d1584440d40040d80840940c20200c40328901105c049021511854100c00c140f4440c040d0807030000c1c1c01c40c0e103240d6200400608e07491517544 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 980436933 1250 980435683 980435717
    0xc1b10140301172b0e0f0303031b043507030b01090216140303071806090303140405121b01030b090103020907030920150c0718060803070b04060e0f03030115 69
    0x8200c08444d500c1003484c10f41880c481c0e40b1100c01080c0390022030790310600d0504500443e0300d03840b020f800c0b0300408403000d006029406004048030020080f1182c40c91850311620300f244140007178400050806081444645100c07a00080c84c04181c2e074000303c9800c49a442c228913040258404170f49100da806000e007142000c00c00011071041c03140007400c050f503524a01a18020416803c0080007d0305900b5002d040c42500d502c140703800d042e690725080c20707451031000d040c814072135000307a03442164002d800c8031031940b500b4008114a8101c0c0142040b4918802e15000150300b0313038003152031854010003007400401c05460040c01c0c0c0303a0025040d0400041c2080070703440c1c24411801000301c03440d1040c5185c610030703c10f0410f00c9061121404038407041341080850860350391108500e11420300074000110302480003007840e612000c000c000040403680e0f114000d14140c40e142604440c1950101c0c81c00303016503200b25001c01d03242c95045040000d146035030b00b0142c143d52145c480045600411a40191080504d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 980438183 1250 980436933 980436973
    0x40b0d092306090d02100903030e0706170a1a010e0f0a0e070905010201020f040923010303020c0a0803090906130e061302091303090b0a03020c1b1014030117 69
    0x100d554444040c0d50030141c55498034040b0080c0201509502000280f41c0440c3d02103400e0302c0490311000045446243c5040c200d000d81240e41650010340503403c17000404c2500447c68500d02032854641e58a1542d80203446000c8889901c11110384608080780141c540d03110b040c0303283d4118401001c07200741c3c90341000840c041403440d400046003c0180000d008405030011151401031000741300030761030802141c2030400309029502c28021015107a040c600038551940210301080300c0e0f200c0000c5403641e503e04000750b5403400c0340740440c0240118800403a03641c401104a540507200a808041a45c03900320070320840341609080440040d40d210030301c4840318424000305005444a000c440d450400500410845c800003800b50b5604610030308a4400003034002101600312030800c1250b54031028002d9080d0041d20030b06283c50313131030b00514451190f18010844001d507089030968921000c5401601d060390010300b8202c646681410a0004108114110001e840c003525207030144c90344d1881c0c50b44070001503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 980439433 1250 980438183 980438213
    0xc09020304051005100f0b03042108150a03030203490b1f050a030f0203010909030e240c0a0507081e01020306060a0e03070509070c0521040b0d09 64
    0x6401440481261020f90302855401507444254400054a002d1a180c071443c0b4500c0781c0c8000d80e00c04800602800900b44081c44200404d141c0404103658492009040850803166813078001032070321040300907040050f020300907240c2c103400940c50003000e0781818000600c0507510007900e280c8141c0c424145042c00801d85007000d4002c04034510071010f1040c03c0c0a9803600d50384180030b50340100300c102135401343d89400c1c6000f0b40700e030601c6542c4203900c0c1c2c0f040780a001800344418200d4000070002426105c02d5006c81c801502030340e10090340000042c01c100540442559101e030765041d41600301c0b20081254000c01c124080d40b41200d20304807642c1d40320750802e48185d0052400c0c0e040182008101b4050075071042200c2c00c42c1c8003c52552030904001440da000b4401040b0070480b0781c000c940c44503141045051b001c0c01c0e0003021240c042c500040d00601800300224101c41601910604940c0e5100c1141c0ca045402c0c0b044030704605260a20701d82520603040402c00d007101070307120201280460300c00030418400d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 980440683 1250 980439433 980439443
    0x1091518150207060615050a05030405030403061407020c0102060411011b0204060303050a020d1e08130b010905013813030b010602010501031e020a06030509010b0916110d1b0c09020304 81
    0x1036602c14202801124002d506c02a0700e0014881c0c6000c09540c014119100300c9018204241c89444a0074085c0c42c50003641c1004182c00e140c801087d068409446955205451550031201085203500049071190401e880042c2040448030400103a980140d1281062000581c40d00396007240a40002d400d0b5100b83d17000782d01003040041c004803147d605112030400c0039118207000c590074802c0408201c50024283c40300c02005032450100750f0b40024042c02c00300395600046c0c85507455031101d91041c000c04003071103a810700e481004014241c1c804601e00b90205c4a0041941c0749842001d0510841d43da03204031020064054801000b20008240c101080d01808050380001481c1d8190301c0c1010101844564800740c806c40812400d0050f9150140441601c0c6507280c042165102c0d46070b8640034206da00c496540c403820200401210300c6104040c455038240390340d01e1044410008038250340700c1096841c0d640000f06164040101c4000707102c10340940c0c52044c1c3c41e268071a035442402d00d089030815507080324 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 980441933 1250 980440683 980440687
    0x40f080129030c06221712090d150606021b0a030f14060708060a0e09031903020c03121030021314040b07020601080a17070602041214010915181502 65
    0x85400916a04200540110680b1b800148018a0020380d038000004401c80d501200040ca90015122010a540303240c0c4e104150140106500c18140c024064a0084c01d005224414a030144520348040300203490741c018065038030140c01e5480d180e44400d2404019507108040031103103842032204000b01d42c03041700302c0d9450703505030308000c1d00f042400000c0c4d5200c08110200d44080c007403d80c5000c011918800d810210110081c0c020714000da020380200f44861815000c0441c88031481007003440d8407486880c00c01004188282c50303810150900303290f8100051903140c80f105014400caa01c04c0c80b0740890780000d0000042c1c1d2700603a00501542c042031041c881150200c8280030401c2120090550051020b0010380003943c100502260b5640c98400d0180460305050b03045058040342070304484ac8250400003e642d1280c894143c00c40f00c1419801c201d44c40540800400e50325501842005401984a098503080303140b80c5d8600005049188402c0030140c0c1d00c500514005010007500c1c0c0301c0da14000700090707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 980443183 1250 980441933 980441977
    0xa021206090111072315070e0f0604241106042a05100f030204030c081f0c02060c1b011a0a0f03080d0c05040b0c03040f080129030c06 59
    0x1e400c1d904102d591804404080c030042e00040c1801c4603240e00002c06142c3d00300c81590701c41006140c062001c04820008070b5050900c05000c0e40b080d0f0f42521308400343d800340b61200e452014450742d44a50300c0b541c0910703a80f080d1030140d007013100304903200128801d00d844013501c3e03800c21105040005c01e80742115156a100542c214949002c808801c444500320b002c0c010711468030022a5048002c60700160804c0038081106054a02a5040d2006150400e405000b01d030b8982444541e0b034840c03ca00c0c51140e15410070200503554850040802c1000180e01030031842e140c20002c1300164214140c041000a042400a06603c8007442007000d40880f02602c04850000d000904c08a95800d400074651035168007000d1002c207078807100b21100c6001880700080c1e00310f14804211741900540c0c00c240020080040d8602c00d8a6000010300184c036400f100000d8044da44171150f500320b400c200a00c0c07040701912112020f43c100c1002c40d4170040d850103401c0d0ba075038103041000103003903900c4801c6004500b44484584 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 980444433 1250 980443183 980443201
    0x32406140a0902031003060b0d150606081f05010807050c0a121b020906060313021203030a0c050903060a0c1e03050f130203060406090606030209040f1101050f04060c050a021206 78
    0xc1c002420750308002c40c590f090a0300c07464620859800701600103034548250750313410b842c1d60b0a143c02c9075400034658281c8200740ca01a1000e0195840381400195060003c50200a450801403499021080c44039204d94940401995040c50050402040c04828015400c10b10814008106482e1080e1101c81c0e000c2c00c98900900200b00c0036145040f28004c0039116001030311060a0340d500550110398098070f943d940c18410103c400a1000290801131a44811005100000245009000a20090041c003032547d604907014041c040005034190b10510100d0901607190340300910706200c501c2d11441449004d149060b20b840910b40d040006a952002c200d8040205045250409205481c590340b020403a00003a545580103000503044c1c0380e0310400402003080941c06000119400340c030400303607480c160802c48903440340c07150191400008050200e005612500440354420704c45c0c95003034141030038410704880c1c02d03012610844003840f59070101409640c54030302c03202004640e5802040307a403400550f0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 980445683 1250 980444433 980444449
    0xb120901020c07210f0f1707020a12050f030a020f1203090d1d0319060f05040209071409030118020118031505191415061303240614 58
    0x42400a6403050007841c110301c40c082408811242403440e00f10780c1d03c021080d5140c4445100d80300404203520390a50408020070400122601400744050502c0c40d0400c482c100900e10941000a43c0300001c1142800060210030340350032414000e00860f034416000540c0079180d50b00841d60200907a110001701c425400b01004204110722882240f142982007130301c01c4030764400849101e47d007070080211030545000c610a20682461304014200c88245e40d42c250f45450144119009032181401c1c1041a03d19695601401e0302032640039040c20241d0355081000c54400d02a203100200d122010881642d981d60240100420f003082c0c0545805120380c140f00240900a603400c03254840140300074104040750100d04411110303c120400880c2d25940c040280e100d5806110038003007228940240070a03c0c1d122406020310945418040a0344441d90360704104880c00f58082e2041c94400460080c00095182c80c011b081d518856510b50001d414107070249001c0e07132131580100d086d00090016103102850a010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 980446933 1250 980445683 980445691
    0x17100311012a21050f0d0504030212040b1b0c0904020108070c050a050606030f0601060c12091e031511030604020a020f0d0c0b011401020307020f0a1802030109060e100911130b12 78
    0x401310728020300790442540500660300004641a40c52002805150082c030030704940c03030b4129080c0c40e56a610382c191004250891030148a9828481c0c1f801018010b001900c0d08028000400e43d000503501c5900444940100034503c0d020440151003880c00035008000410840b0311a00140c0b2180c0b42c900d00f03252520174030788080740c0c89070b00c03d100400a007138202c681c0da8071660300240303000701d03061007004190317490075469000000c80005001d521a43d01c1c25080e804d405e4034821214007100800102d0300000791103403290040b41c4a91b080000c40d4080c5000d42c0101003200319070040da040561181041800c00071800c2043d000b05448403020310030807195040311405406001030310362454445400003903407030013140c100901861000001c481e00da9203401015005002c0541500e03468200c2410280294000307200c4c64186034107090000c20340c100a80103840c884c1140450400d0428a00100100600004200c0e1004a0020012144140180c000c080054006482d1043d521030918a4400b80b03000010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 980448183 1250 980446933 980446937
    0x2130312090e0f132a09050c040611010b06071a0615040e18010f06080c040b180a09120e030c0d1220070617100311012a21 54
    0x1203080c00720341142d5410980200603071114548503600c600c0700b0360040b007150f1000740c42074100c0800b100781031410103821195890740403858000c843e81c80c4d0340d8406030f41e42030313603008890b5006000c103000f454410159400c002408200100300000344401140c065032020b50705503480600013903c182c0d100030f0030ba4050b0700110140c5071100300e4050840320801c903004a0017640031007003050000c01c00c10f007002c1c10041103180701c50001308000525181345900420203440385051500403da0f51b945a8074040c030a26000d40341c05440c001c00d41c03006152101148500400300c00e44183c0d00c11482011400340421010303d0551a21009034500c00c42c802c15140c00b002c803213414403841d403007841003001070600301030f0342040c5d800d504200000c1644440305210900600c20040105c1c807900c040001c10582c8003500a40411294035410155101d8214654424809000c040c0c01e5a25811140e410b651041d1340780d803100200d00011441d0074807001d522010042511205850a4140300700d41c080c4218a4841030034024028 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 980449433 1250 980448183 980448197
    0x20306090c0f09060a050c1203160201050606032d0a020d0e03340b09010f1d330f0a050109140f070507020901241b0b1902130312 57
    0x81e4410b00c1481c420540d01e075004010100b541982c441c00340090f5140c400e80c0360300355030002c02078100c4890160411140f1010940c410500c04014900610400e8050100a8201403a6030b03250000504401c4101410000c804400404520f01c41e945d5849103000d11400e42000d80c4e1f0380e50450b6158240e03605000c441503550000c01038403844000c6208118001d00f04202031210400c8034401c0703406e054505a502a1611400d40100a2000010342c046003400d199658204004100e004800b1007100b03c00300010ba043c0d000f03480b806204100d8181201742c0d000300c1845427203504109240c499030302030159641d03050212000e040c0444081c0600415001d004d01310390411561045243c1d0b00d03039071940900745aa41201e160045414948140c040760003035074024000c0512540c0d1124562018684a0390615418000101c910159403003140c04013808568050300105500b02038880714401540505000011031848090f139a9108050014020300d0201030854559186035081803811086000d111800b0007000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 980450683 1250 980449433 980449447
    0x7090815250e0d150c020307051507050d0e1f0c03050a0515130e01020f030a0b0306010608010b09040603051006080c090f010b031308121f060807030903020a021201020306090c 77
    0x10080c00c990326000b0456074240305050f2030a04244040100909050a5040c0040c0c54001ea80000041107240c0c480c40407658040301c510b806140003030301910000b0005000700955880c00c2d5803a0084510795516030252101140c220111060b1301c0c1000c1280300c8403e0325111300349503040c0c05200d041c1d0b00c1b03117000800340084d180c40003d441c2c1c0c40e00c640340828450b86106001c961041d4607a800901440f000500071907887d01c20031914141500101e40610b03a0b5400d1012005d064200403a000f4100c40c5584c44000b5543d00345500c064050f049500c5803070f001b503038600c400004100304020b8080110240c0c40300144079810141c1840c10319410402460240c1e80072800d1000451019003072904544400c1e039a95100e840b800d070120803610301410042c1c203078034011034064042e0207100300c0c0902602090300a404018682040c544900c0d0880c0300380408a000c3d400055250f500941111240500c42d1040e07500c3e034201540062418842a900d00110344e41c048100b204a040180e80d540d040708400c0301040c24110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 980451933 1250 980450683 980450687
    0x1501021905010612030e090106020309090a0c022d07051c031103040b071b0608091b01090305010e060130031b060e0a0210030c020a0b0709081525 64
    0x8642001a224401500c004018440d00303510001c0a40304001c0340d0403100115050040600c20020b11142c41138069000000d42c0500000499803c4d00000e006020303540d84581350000103041200000d019030240d8240001240c0d81c2e40004502e0211010070480c200702407040c99403510303643e030300110b0090603954040302060046440000c0600d40c1841e003101c80c81051486c0c42c1c02c40c000c580c00091420790104005040145080d00005026101480d254106d0b5668074100c0714103009483e50074590300420b02e495032032207011603250803201c011b05140c003405039030340e50362401c44001000c0d0352099000440140052004600e18280070b011a0100c8440c8040584c3c0d4003200c01c5c1806002018440d4940b904100e6800c0d182c541c80115410403c01c106c90b03a400f400b91a103502d8500004c1f80704502107401d000450340203100d8888512040e0303006080703260803540e42900c0390a001d000681404120040001c810b0fa003005039002d02410300c0300c0d0b0040ca092100c903040c0390544122016600340a4035500f002055 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 980453183 1250 980451933 980451943
    0x609110f0304080c12070201031107030e0d24050f0907050918071505070b06091303030f1404050a030206250e0414011d010b03040c0e0405010f15030605150102 70
    0x300000380019a03a0319185070401e460300c80c029400c03400c0e01480c400d070504200804060303c01c3c54001c3e01c092281f0a007031500c818841c4520480200801d40802e4000d8071810060440200d180c4200207402c0c01102e241024001007081500225440e80c84804100a00c1c45074002340d82c1203500900205440303800c14001034181c43d40180f40e40c8060003080d2009801360010848040100081ea404004c4160f408400a00662005406460703035020f03007001c10158140401c04501c11595541c08100992040c0c2e41140900b000a01200d40d440d1140c8280c1000014500c456000d1031140f00105090f814616010307007401001840e40074400c0780444403080580c0480300d00180ba000500c1c10400240401c1c0029005000d0000745074105024240040b804070600d2203040c0c509030320202c644500340e80c0c4184401907840202ea0040c080144114200280421420810b412a1040c0004510000c2c04003900307045030b40591032881c8949600750304109001440c419030750011103140c010080f01c641da10002c3d540e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 980454433 1250 980453183 980453197
    0x40b0f03120d090f060c0e12070902090303040f080708060a0903081506070f0c0501110318092203030506010e1009030b0601050705030d0903030e0a240b0d03020a0303060911 76
    0x510000105442032104582c03000244641c09140303100101450b040c00c8000b0a61a040c503004030350407035003d91f02c500c0d0a5480300c03009110b05006100306070505210402035008801c5154040c4170510002c9000d24040b50341c03034081c01507003006140c506e282090043c82c101d400303012445464501340c1001d000c01d238401042c0d079201065552884000d0340c03030408152544144080501494440c1e940c1e042040311680782c000444000344d8a4440800c204549640c503031142c082c802e1031456a04000c80c0381c40c140703a00c605901180343d03030081c0040f400645001d206000c0802044002950340c0302002225a0803103500032121200f075900000341d500440000d401e1442c0b41c00090030803400070740044c1c034582c8610102d80f02e281e413003025070b900d90800490340000382000701001c5010904011440c5482c110004025031041d0700301480842c881801c841e614900450041e002c07c80b00c3d00e80000340341c60b0321803180c0320344017512030340c000c0444a03038604000301142d2094100c080c0e03443c24044068074a40f144000d8601e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 980455683 1250 980454433 980454463
    0x3040c050907051903090b0105270601021e030702030d090806190b04230a05040c14190305060a050f0c07030311090306071728151a0405040b0f03 64
    0x41d510782000c1580d05000d0310b05141c4510500d9410184e0b045d0f8540c010440380351260998480c180d8a900810107100458103624122220800640c0724030b6100385800c6402400600641340c14916644010078035080da600084040e50001450508500b400c100e0018001903518200d03104606007000c5075140c260241404080d40300c12010013103001c60981c00710a03400340081040000500c0c80d2541d2942c0916850001c5501c440800001c1a10310f1601460348144e500c00190b11101d0b082c80100880d4100150049800500c0040d513040110684521403014500510003030034185003a00a41c2d00340c0300d0007441c61001384404400e201c0c40b1101d0005035228107a050030041403451170141070020318042c074991294180325050500880729008481100315030850540c03004d0542e40d0b5104e00c801c01000140c0729070b8035040911000d406640e41c1e4081c007042c5240700e0201521650301d5000c0b40020710088841080f2041c0094108950301d480d10808100307540a9609070481c02e005c000203900c0329942c0b005011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 980456933 1250 980455683 980455699
    0x301180e120c100612051504051011030f100b03011404020c03031008250311040e0115050f0103050f0f0606161203060603202b0902040c0503040c05 65
    0x50541428440710003460456442240c850000302005540d032100084115515483c00601064034807808600e2926540c004004099075040031490007441100100b0903285800b6200a111501c4003902604002c017601600300354036418090011003802c0310203030980521082100c82003100382c01c0007081c0c034115103209806800c030305d002c40e000c180603106028a00643d4000081081542e810944091003a146a64215402502c100883e0040000544c1c0a03005072105548100000341d2034904e10a0903250241011540011b00c0e0344090a40345a03079000c4161200c081014416070404641d8140000401d107000d1105007001844041c100201501e481c401c844c01d800080d4040c1c64400481e4510300034145009400041c0b82022201c2d00d0920b002000003900f03041000642c284a130003400f01c000000b803400301d0260352420548107141d000d00c07440780e43e07441c041e42c6000400c6010789021070420400000803600500c1c0b88100821036030040031039014000c09100707000102c0d8425482c041601c1050301d41003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 980458183 1250 980456933 980456951
    0x717030405060f061306080d03050c0705060c160f05150a1509020d020c0a030804020a0e04021f090503010608070503060f011212030609050109020705060106110a0204050604090b01080d110102030118 87
    0x2c1c007517100d010a8041c040307051940c0010385500000d80702008170b0307403950300b0480d03034455800850407845920000f8089501c07410100b01c8800702c000c020418a00c20507002c8480c01d00c607680b0500003040c8000c081c0c8840e04034801e010b40045001e01d159a00ca101c400d0104180e5038040644a0002d5490003126066540455a00418100c0707904903440c00680c401100c44200d02450700600404044804901800d00140c2c001840241c0c042001d02a039030081c450b4001000c00c4240000000304a0400e000700011804001000e48080c8a014003400b0b54801410030300c2d0a000030302d49081e402030706194041000e900100841014000d603280c84d250301046050b80c0c0680d16804501502071904075910442c901000003445007071a9000b0410148600240c4035140ea82d4282a12110960105030703080e074103c1d0f2a80401498594459940f05000500c0040c58100c00d8071081e0340420260480c10a0750700c03518425400540002c2c030540d42c503003400300a42c035641c1003c52242050000aa03031400d265258000741d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 980459433 1250 980458183 980458189
    0x90b030a06050c041212121104031e06020f0c011a010903080a02151501020c011701050112020c0d020d02061b091e03120a0e01081e040f1203020717030405060f06 71
    0xc8006082c2c011070140c42c40c82c0c609010940f0302c1441b50250104034003c00c5c5422203142405080c59402c0aa40c005040501e1511520310680740300008991f80d0b68095000c00001d019032003d4107000d81d06a1100f0744442c4594403040c2182d20003010300c450a401c02c0e00c1a07800e0f0303a20102c0700042d00c0d403243c4d055884a0715007000f40d2401e444545158654824642006000c103040510401056000d80c00c646e16445064019a9614410714096802400000c0107000d1075025400d54118164280c00c018985099294800d0138407a00300052001a0084928101860341c1003040e40d402a03441b1542c0c1120402c0f542c0d01d26554400d0789d81481c061007203014810020b50f208540e0544c039200240070340c3c14004c03010084ca0b4496114030002700c08501c103a0040d0040b54030502d4603505c281070a000c011030409402d03404480d0720500510480f11224607801120001c0d109000c1c58121104a80b405620388009203000c0090101056142b40c03010414000c01c404108000b072450781001649541c3c04540c1c80358404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 980460683 1250 980459433 980459437
    0x40b040e0622060f0c09051906050a05040e131b0e06041d1603060e01110412170424050309060708040c1a2113110a0509090d0801090b030a06050c 64
    0x340a2038544490151340f00030035040071400040301d40e190002280c590080004000141c200c0070746214465005104003030190008003201c00503420203e0070b141d500c00c4400000138040301d402d40c0141190307054030304000d45040340d00700c2c02070111100d14150381044120f410800004240d5071041c1c1e1aa0400c800e5030541340c0544499540d00070548084d1020783d480f0348074a10b901e2000b144d040c1d03c4c24400c0c004464040c4a1015060520703000f441c507103407420100018039085690207442e01185144070754861120100100010032800d5040c0e9400100480b0220b5039802020381d500c18004104208503008101003085070744405a420035004a40300da003441c40712955103402184e48041c200500d10405d0f1a070303602800003400d1340d00310700200342040f8030060b402d14004ea544d094580d4a80402e0000503400d0500014440c10150034540c80d10f40e42d4001500706082a22030840b80e0f0840f100c00e10245510004060141c80d4203402400302c00d2201c00481e0340d80c0c0c181880586001d0769135001c40d01c41500780341 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 980461933 1250 980460683 980460751
    0xf072d0306060e06030d050a1b1b121118010b2209020c19080403020d080c030406050d2301180612030201020c0d1103040303210e0309040b040e06 64
    0x2100b00060750b1541c00e01c082e4003c0039949244240301e080c041c108268468002c460120140d80c0d200e00c00221454a8100340900d0880201d0704030794140120f00a5040c0c5c00551001000301200c0402030f103400d406d0041c2000d81140700180602d101084d085402c9007411071060445481c10042d40d550181502c50945e91031000e03903540003a0803041c000084425840d00a0140790124506503401d080c4030207019140450741c41d80c0241600018002000035103041c2e02e4082d8036a02442d0b1003407801e240d400743d076802d6603c40d40004010a101103003041d1584031a11030071240d8445500c1c4028401e01c00000726500d150705109a0b0b0740201c1e9000850440212070304140002d101c0c1d0100070240c00000d1502038040d40122a41a207548500380b18078210728440c503c81205d81e500e0b90055481c00707040d40c60840c2c000f00c1d146e6603444003a461840c02d00d020f4000d4440c850210f00040c0c0910340711118801044140c03050020f0f420711607810042e044202e64004034181d42c02c00c02e06040d41200c400010700401c1102c1d4960 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 980463183 1250 980461933 980461943
    0x302280201090212010209040605030102030105100e0d05070e01091b0207031128140102070b16030318051c0f0e060c011410050a091b030509120c0304080f072d03 71
    0x41c01da81052813054018001c064812102071200b1030b01c0d00241403c07800248079865004a084820300281c6002d078403904465580134004843c08000c5440b90351404446900144451a1003001001400d003140b00d50003040020004910030981c00840007507840846000142c070f0075004a80803441603440350641400b5120b99115500041c030321401d1801c2110b054800d160fa604d4048100704010f41c804030740c40d015203000c0401203040c0074411500810002808200720245680c0d6181e003090540707880317503010038030780719400a00c030a0550301c10b90800081e20b52205400d20001c41d0702661310700d4002810071011002900d060340c81d0103000d21014050420500c000e03095602e00f03010703c080345000040340c5007940c2041da10100800e80e41c546441c1100d0410628000d00e009190018908070701c80d8120b25003124080d0100e0f4028406003914001a034441c078004c1080b03920000e0100402807042c880d140000c031614010b031040610b02074031180401c145800340c007101540b210941e0203041403e40c190001e10307000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 980464433 1250 980463183 980463199
    0x209270f03031009060807180612050a02100212040603050a020d2c190210090b16140304030c06050d2a120603050d0e010c0204021908010603022802010902 68
    0x4814050701c81e8801d0b1800c905051009001050324040c50040320200c6009100030101c1c00d2600a4403a92080c100c48a100a11f031101800030720030450105005506001c3c1d0098030344a0038903c10032405801c00040c41041d500042005940e10394020103071001c0300c50505000c500c40d42e0701c54028000b4403542003401c0403030785090340402a4005175134180c444031185680c0d40074942152858180e65600d1034144074098850401c1c8240103040091415101c00f81c1400c069242d40e445001b03800158001030052500c08000801110a102a4800b05030800e2074010155141c42e007580c03580703130b050b0110b40a080c0a110001134800c481481c0c0c1c0e481401942c6540001400b1040300100108590140a600c03c001031034038803003044030000790300ca05400c884e40a0010a00480d0b0030314241d69442003113905906001c1a4100e6001503101ca0001f401d80b99030388108608001e8a05201505200c5c040e00440201441401440145000080312083d80c05070840b40514501564008038090301072814001d400c0014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 980465683 1250 980464433 980464453
    0x9051c0c030f02010216260c041d10020306090601050705070e0f040b0a0e0703060b15030a090308071106040308100b1201051509031504060e0d02030a120504020927 72
    0x1181c1d800040c03543c402d0b4260f408003d481c0d122035002c81c9071030164520390000c4c00351050017900c005036040303007410a11080c1c0301523002001c0010100d4413096100f03503124500c0c840c034102c00d480600c13000384882600c55046056047c548045401203400401003030500800096220611030300300119401441594200d00d0146051444c84104442c25203045842c4180320300030641d4000c0a0080110b03504048000f0900c01d032450312500003a000941c0c489402005064912403481018070046204508105003c520600b8901d07008141500003403000d03041000d00340da03003280440080b99081c0c1280c0c062800302c80c1502c0303140710300c0d0041c4140e03408418048400036810001c1c48e03d40184d41c0c100c900403503101c1c110040b0320010109500c100d4100ca903268001c0d00703264034584038440203150014000e01c000941e1340414024185000381050115000da070000c03400016059108101020000e140b042c20b1004d400d00b580422142c030005000001c41c10b401404803110180610010748000003c00100c800e0541 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 980466933 1250 980465683 980465693
    0x18031e0b090a0614040b1314030d061e060c060e0705060a02060411060a050d270309090606050f040506030417031509010e010e190b060f03071d0109051c0c03 69
    0x446901260201d060104c5600390250492540b407003160013084840c2c1a40d660b0001000e81c0030708801c126003120a03091b803104060003c101811f1680c41c102d00000300c00342130242c005005404942082c43c0300380c600c68184600c0b60b109880004c5103910900c08121614215802401c1140e5a00301c260051004642c034402c1c81d074000351082c001d81c0203800c400d04a10402040c84038900c90301441c080440c104000c00d040352810342d80305405450314140703c014094000c2c00051000ca2102106600042e2503100a1002e1251071003208014103135402e241d86004410441c0380846e015502c10107204210200000341880140c04400390703402401d00c5529581d2504120950410001192043c0a00403040000c501c0c01102400a416035020394541c0c54203030740b00c103041d400070042558018162034885a601ca202c0d21400041d040c0d007c14403401079101c0c60b1200b40106a84064042c1e07100710b0784144400003070343e60090880d4096800990b0450907080d84104141d03c3c1c41003102000f02112590741000003808 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 980468183 1250 980466933 980466943
    0x409030e0415030b06010c03030b030609010c0f0e0f040911090c0d060e040b16020f0609030901112e11040b09120a172b0f0c18031e0b09 60
    0x3a00300c50400642800b80003103007110201d40001042d030741030a404035200b9802140c13131140a41c464038000c0b41351140800868241a0181e40d641074583d1581c0c107001030346070020001c2e0107800584c5480342c02282ea00740010100e40382d00d14260b00441e41d50303518006001d03203801c0a01c00520080e0489031a0308100c5500c00f115407021404003101480c080380450b0000c00310010314041c1e90041c003419500c0d10341400203498540080140c5095200c1c0c2000009902011312140e846500d5020142d901c80c0d54040001d4020000c403188401315400c29072010300388a20411010f410302c001008440f03021224560315070000d01c20564400c80c94200800c002a64181c180014000028192540c4024102c01858181c0e01e5461a07401040e0880701c81201c400000c441c0b01521201054046170032981210410f40703581050003140c561403403916410528005243c0380114101c2007410320300b80042400d001da0f030306001c3d005800000c013490350b540903103500b003e0150b1a81000d160004080a00382c01d0500301142d80b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 980469433 1250 980468183 980468207
    0x90916030522061d0a060c030b090408031b16140d09030203030301032418030e03160b0306030f1213080a0b1501023d0612080c0705040903 61
    0x2400c0000056050200244620b40340c0e0311402c002103035460641da00c0700904008410510689003c4003081035050f4100042d010b00350003400001400160400300400b91000d401019000f61108010b200c000307150101180e0348150340030b03c450b0600d0001071840c8143d10902c0000c2c0000904003694806021702c0c1404520080907c6c011984040d030082030a41d40d0302102d201c003940c190010302c010404501c001a1914600714400c1104080300301405072201204c07410000340b20084090a44d840405802107e07001d14500101c0c0203140c002c02c464104002d041042c0a0a0302481020001c07580c183c074100013003030480802005071440000c24860780b254903000196104c180e80514000001c08000128410304129000903040c0c030382d595098034200328180200f007000d046100d07415500c039801c2c040b0484510410180031661030b00f1007401c0d1000c801d5560400c01d00151500e003140030440d06103c1c004600321146e000170000e40300e82c5610300050414440f03a011640080c01c0c15082e07001c25601046500d4a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 980470683 1250 980469433 980469437
    0x140a0302040e0f0c070f030c0206072118051e0d03050c070b130b1b06010807050f0906030618030c01020409051b0306011d032b03060510020607030203040305090916 72
    0x2e039540f000c012520402040d1455241007004200c010f0124103100222036440380a414211305000300c1383e011402c5507001060548020b401b824240900003200f4840f1b0244104c10326151242c5c10352464940c00e1034000384180c51103800300085a00340300040e0b46600505600090400c0f50301d4046040140582d8060310130500d59010b591008591144003605491072101241c01c0c000d001c50508240c900164085400c034040070661002c000105041041300030301906d5008003034030940d4509003e100701441100c60462107510040200001500c001030038687c891404450070704510701054004d8107500c24156a980c495000003004601c214003900701500603041010140d4402d800400c02a803980001d85101c0e002640211303a0008907802480c4c50008818014207442d00e130048403d040521410060b0000c0c1505206110701403629018410381c03004200907141c102400c8980d01c2c0007515200014102810f05a010002c00d05061217602980e0f10844050880900d80c14100700c11144407601845400c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 980471933 1250 980470683 980470709
    0xc020c0409051b090c12070e062b14130f080408060f100e0f0c16030c0606122105040f0314120906071712040f12030209010c0f0201140a030204 63
    0x7031500f0302048640c445c9840703003009820901022510030308000081c100c1c02c10821005010400b50342c6041c01041038511038449000c0d59210301000b1145001c0e1027080d081ca561074500711124401d04044402d501c502080710312038404146182001c0381288291004d4403003180410041101c8000043c8140034254aa40a140700e954200c41c1c24408a094084c03100c1c2c0180d510049a0510801030105800140104600d030921910840c0381c0e142001542e0147c00180e1000c00f000d045c060349100d00000b6000150003403104d1203540e2103c003002c80c4450038000c0200b24247d5006521482402954090004094641d00030f5540b030070601e00700c220f0100078000c14050304981d00c28a400c504121011288003500840c03e00004d6240c034900440c0300b03a00601d25220410280c5942c0d0000300c0030510a40c89031140d110719405a05000c02c2014140f605201818030401014146a030401c0314205041e611030076a6500400910040b81d0114030b981800103040c1000c10140000d64140d000b91090300d147c150080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 980473183 1250 980471933 980471983
    0x3040b150d03031e050a1d033108030403080408010f06060915021f0c18030b040b04050313060f1107030803043f1106190c020c040905 59
    0x8114950348a8031a4081034660420000a0283e0000a94801012040b0b01800c2900c9140c00990300100d515482180d55440710302401041c0720b000c080c0c1d49500000940c141003440d40996030080011103020a0400100340e10b4000383c040b075810320b000c0e007040801d0340e407603554070315040301544c0180c0106011342d420324012921680d05442003400300c0c5c8856503041c410f207240c50400000010f0001c6004c045010768500031000300300807007400340240da441034006209410501c00401e05110705039070b03180204019100f00041690056400d070015040803031102645c5441c9000c81ca103201c0d14132900c092000040000501e950806064189042039031102ea114142c2d01c00d01507150802d42c040188000014408600454041852000c82562400d144072060215810b0b42c03100380c3e0920b42d06080b040c04504d000e9001da920481c0340f06541384030030052000342814400c4200c0381d51400f08a0000c0b55417107621101c0385100300041041d103003002d48204241241810550b072a1301d08005c1c0d6a40ca00c514168030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 980474433 1250 980473183 980473201
    0x6060306060b030910020a0c061b0906080c09040c1106040c0515091309140717070609150c02010203210108060f0c0f16080a030c080604180303022d03040b 68
    0x3c030300c20709801026004808a0105207002504496030800812440108600014686110310219130300395802d070715a0308610f0071001b001c000540d008074080010f45e5084c08003184d0200261600003400721030101d1132910803201140c400da001007040406104200c140030903c11342c501c078a030550360244c0b143e00c103011a40c50030b07542a10600032055004202407140c0000d4516079030100941d40e10400d44001c60350101070f01c1c1c80c41c1c0780c2c0c0358105065803030800442003040c15080100c80010085400c14061541c94000180032900001602c1c4040c09030060301502160700c00e2044440145000404800c00f400d58810f040040100340204803480c481d203404659050000d4010510403d0390302c10765443c147d1102c55040183c0c1015501c0301d043c525014030b940005280c1000f07001c5400c1259400100c54080c40001008800d0140165015620706042c40100ba410310340c14096007070301400d0260361500c01e10541403411041d410380c511104141024000d00e4072004004500460181100725550b40307c0c5840 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 980475683 1250 980474433 980474437
    0x509210a121a0103091103011104140406060c121701091d07031101050c0c0901060c05010506040510150e030d020703050d050a200c0411030a060602070b1b120706060306060b 76
    0x31031540b82d4414007040c0c100c0d42c8a5007090003164454101031007990003800220b82074400c50400c001d550000881c0604c02c51001c40112005004200c4091001074076000016190401d00c0340081c0901102c071130310622050042050098803202407406d460365680d10a26040240038002c55078561045540c0d01c590032030030014280c1c0a0701d8100c80340800561035400152003d6102d030382402060300500e5a240c3c101d54a00306824000e105135210020680c10380e00e043d40c219038000300040d11580c5070a05010f80c0022103900302d004c0d96540c0317119004280494405417005400e210300c85d81e05110b101e0341e40b07851650204c1d501c001c80b0310400494500071554072040d40e00d4002d00902e64000f69041c00c2103641c590504c200d42c001d880544050380c2340c40310647c0101d01541c0c61820401c0e280c1d80c0c00001d000c0358400b54402d00c030052055101501035103060910f0751803503124043c484021001e40c09041220240c06110724041124002c68081c0e42c1c1c1460320307281001d083c06100503101d44d0326213000040c2c03071108841 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 980476933 1250 980475683 980475701
    0x304060e0d0905011106090706030507090e09070302120f1c030905121b19031209020d030e092406091801060906030506011416150e070509070c150509210a12 69
    0x1f000c0c14040d4140003049000f02070003822003081002c0d0580018503103a804003800e01030149400038246203411801807046501c2c00c0c04501440341d010722000c202c20074011404038240700c1130380803c90030607200c058101c01400c0040805815030051450b988460740307160f0002c041e03045801030107071441c00840e01219110800c4520741560200c00031192070000c0d00c52100c044103440200b80016034035802e03030041070a84103807920441c041520321000f090036103032041020350310030501e810b0400000d81961034014405007002006015200100e0600070325502e408500c5000c01110420500035179580784001c0c83e046a52103444086032614020400f076511900b00307003146420301c16401d40341405120134003c100f4034009003590a9020f11081c0009914980034452400340c2d200300a226403403c0601b0081c0340d08000e8a4201404a0700407100c00003a004503600400b40f03400c840024595490551403400c144095084c41050f8803000303102144243d1142c00340680d1486543c0d0100c9043c142001c2a0442d40065 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 980478183 1250 980476933 980476951
    0x807350f0f041b09020c10060b0c0a080c10020a020615010e01080126060a020403051b18090a02030d090e1b030c0a091203030501030b0f1302060304060e0d0905011106 73
    0xc40001c010a9490b42c0045010f00c0b441c610000c19136840142a040380c11000c00d5118a070050f450505054000740540400751a4940440785041500906146c0e1102c60700b4000301000740c042888110190300344501d901d0144850700c199a01c51404100941301c9204079010811a030341d40142c0c0c0d445d075210b203000761141039060b16602c000c0d0742441e00007072800c0700b0405415950410329a0348010300c14148000303401082600f07000340e100c600b946840b034244070aa500080b95584509052003151f40d425a05030311090380740b6040281600c43c070796080e003400e03050701d8040c1d010b1084103100c14481c1c1c2e02c40c4d150012078222014058060300c4061803040c441c0402e1205400744c1000f4004650340c103601c0380003025a041070f410a0801d6035a500d01200c0142c604503010f4010030350780c0d001001130003030b070f1400036038000030003202110107141c0b8002e51107081c0513110b00a4015400400003c1c1005041d9000c4259205040101c6840b2651424018100d0f4001d000b194000355191103c04c60324480080c602d0300540c200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 980479433 1250 980478183 980478211
    0x2090705220302010c0314160c050315100312050d050705120a0b1f0c020d0c06182115020d050405010b03030f0403020d170d0c0e150a0807350f 63
    0x5921b0450300713840c081400c940640002c00040511a12006184c442648a101c1c0346000710b01d40300130181400d2554412407800c000d0705041180e084000042d020641e41d0107064503119522003117046403a4000c00c1c9282c0a9a0f00d0f010604c1101c58101c0094400d06429180a000e6a036940300042c003a0341c405482c0b06e4019a12011a0707070400b0008040410264640c545400a10080c1d000104a0701541a081e03c2d000050203041c0a0640c3c0070401609103125901c0000c1001d29200d0b07141444040368144280c514902c030b9101081000444041541e01e040c0a015521007805910013001041c05039401c54a641c43c0c13041302d00d00303800c0100076918010304400d00d10b824245143c00380f0103020002101100c1d00021180d510310703080304401c05040502401100010402140d18002c1c01702800e1065451041c0840c021450302c83c0303940c000700d550100c101d00e008400c980b544a000c0d90f0b40d081c100d920041c10728450306240c010360050811445c2c03c80c2256074080700d5884440c44942d503000d041d104d8846141c14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 980480683 1250 980479433 980479457
    0x1051e030607111009030804141f05100b04060f0f0806130e0c030d050d0b060306130f0b0402040803130e04080703112d0607110c120a0209070522030201 67
    0xb080411040c0d0583c1d030540c1d18911081010300100d07485100c0407400710303500205210500290040d101074a24044001703080325140407100c070f5185a4120720184005072510000303120005500355100003400b41c028016200c5d519244060104207a12030300c08001220b40c00f005194030301c00ca1003035001e06000384c1040c04091f01b1040b0f1801505012800600900c2804603995898030108404445000c3e5540c8940c0c482c881504624183c61a80840300c3c40341c0014018032000703546d615015002c8080c0d4400c0040c001480c60041405040001b402562040c80402c002032141000300c0242810f0051940d0014550385034601071811845c1560043c0c500c00082c8042030020f401484814034600300e4104031020b140c442810750031800008500070081e24284248602c54003000c01c081c0303402c4101d0342013102c02070300c007102682e13643e44a00c1000c52299030510b05090802800380442d001d07a0360060400352107481c0c0094003a046038401454107c1024503820103440c4816403540b40f000750b9034141d4940c00023281d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 980481933 1250 980480683 980480687
    0x801050a0b16020a0308130b120c030a0b0a0e160306030c090b030a060204080102040905060402070308060f0105090301090606060e150a0c080d0e0a050f2d012301051e030607 76
    0x45000500949944070740b0700d0141c0d40d0041000d009621070440940d036800038003240c101001d03083c1c0c0f001c2c000800c1071190507009540303240e440382c0c040d48501e40cae40d8503940c49007906000f400540c100180c2107010400049141181c4c1001e4507c240014007209070f101d003001c1412400c4500794400540740c1c24140c40e05000c0034901350800403a0702c000904581d04940c04d91100402c90717104d50310124450303500140402c00f048003800303040d40c003000c00ca07421400e03c810754a000c0c11000004110900c24004a0302d540083c1c1e01a00507207d00c40c078090000c01140c00e0300d04c2c0c00c0c4000d000e039005500204151030103108091400c03c8410401d1018141c020342401d200c0401618140c0078810100e40c008818400340c03004407014403d00c601d00f12003038001c16604905062507420300240c00c0314010709400c200510b04040040d0202c4207403868050200b2100c2e000044c07040317801010b02210100b0400402c1c108201c500030320f0070405040e102c0441c0d00d2801a000340c402d44594982010807035400d03410490005824178 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 980483183 1250 980481933 980481937
    0xc1e0c0b040501021207030b03121602090613020711181b090307180f0b06041a0705010b030114090709151202010c02120a03170601020319031401060806100801050a0b 73
    0x1602c12000907041040040401e000d8000c01c850900000c0d681d204001c004c0c1c07a081020044649541002c540b5101c2400d250712200740d507521000c0c0c040c1d0501408280760703445910b1211742004441000b1074882010b03141284540100750507152007406034202d50f03003004d00c43d40c151900696400c1c450a440c2106903660000c1900a000340c65810300550300d002480002c500040e401101e1505000180c455000000c4000ca81920300b51070301800d0b05100600640100310301e00c43d24052100f2605443c0c20944ca030003030150001c452074076055400c01310030b44100035a4414940c080d810300030070780f00d20300e455001150455103800c7d40e0781402d20400720200a00b8002144002c11180185040c440e4203000c6e0300400d00c00c42a02e005500160301c0028817000745680031081144445070761441c41914102600000e659025502ca4603c101480340b1080300918045c3d44102c146100308110440e1640e500c41000e82002c508a42042c0205000d143d907c030124841c190b02d5042c0c0340000c04130f928141c142102c40d1016 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 980484433 1250 980483183 980483191
    0x8012904141812070303090b070e0604061d04060b04050307060305060105120613380306071413060c0b06091303050f04032001020f0a1e150509010c1e0c0b 68
    0x9806031814654024107403c00030442036029450100d070494180c90032082405000703001d14100010007254001d60b03580c680445045511300d150201e040d00d034036042001c440048041d400e902c1450410001042540e00029000712001241a2860305a45c3d80040c0c041e507400301d61590010303d00b0044038082e110368102180c1c1003e009018000c80d036902c4031542040300c2180420303100d403121056025158100b2401c44507000140418000c00402210700420740d9a035000d8041c1050101030021800541060810740c4d040d603901070008008641d035441c001c0c1007010f100c2d000f80c8038005500001401400c00020607030090480705240d60a440701a11b0031038542e002800303903d40c2990100b00000100b00c0700000184c0c0001c0c034411440005080e000003914212200901401c15003281c011880443c00184001865001a520301c420748840c80c58a407500340e00b0102420409032510050100e40201503100c10818074140d102e100c804600c2c1402e0200c0d00c0c898030020000512080b2100e40002d541c21982c3d900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 980485683 1250 980484433 980484481
    0x5070221160f150b0f01201c0c020102060a110a1d0316170d050409020d090204020a080f090601150c02030f011815110301090e070801290414 62
    0x50314219600e458004028840940b8440408003506484843c41d114100030760b00111140d0800b0515080080c00d01402480d1a44820010007107402d460390080c00207222030544140340500c0d209080c4000fa000c000c084c1d900b0703401441203a0001d01040e001c0c3c890050382c0d01120800b141850100d01c0222002c00454064802c000a06124a802c0762410441140c045559105003120306050a15882056168020380c0c00c00d170f444259941d40050300102103900783d400c01200540d98240700003c2201400d0103090080d04180f000a84480e155031049070305d4007a034400d4801c00700d42c0e2101458140d55220038050310308800c01408500e1060b5011b07400c424503151014003540c00064100312000d007152006407505419800780d500d11020030040100c0d2916140c0c500308100400b4002c0381300000180414001c0320242603481e940c2e140d042d00c02300030140c02441c05800a100d20812407440c515140302581e803400c030000b5258800d11140c40c00340a08882e4110a01408604d40d4990054540001905180c2e0309 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 980486933 1250 980485683 980485717
    0x301120b06030c1e040f09030e2701090203070230090109080d030504141504020f0120250302030a030e0a0e070e1f080f271005070221 59
    0x1044d450304811040004d1840c2500945812a8001d020650b2118140c210303034149042d9200000a07003166800825030416140302403114039401011803020100c14000e050b00103004000100c02200e42c005502c204910350036101c03c4404018185920540b115103640c004408550000c0d803005030001400c4540014902401215075801002d03003440c2c9400001000640c5450800c02407103c0c008100a030a0031030801860381c0321a200e64901140c1014100a1107200030341026400c45c0c2c404c00c1101c0c40059290641400c06118200740c030750303a010340a2207640d042605d4407468500e02e10b140f00ca004807a0003402800700400e06a90407a03000802d045840da12461558001c65a1060030341010b01c10030441d226071160007464400c001400316140f000c4248295400301001e80b80380d01144190f00021100b03840d9400380c56a00058401140b003249901690341040500003c10030000750030800346802800801840c0c558220884e218500626485da1500780125414194400342d8000d009041150030041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 980488183 1250 980486933 980486953
    0x10f0c0c030602090609060d020901080c030f16030219020a030e060a08061203071a010e010b091e36010807080a080a0c0606120b060306011508060a0807080304140102030301120b0603 80
    0x9a880d801841002c4940c0327502184404055802c0060b180e00301d0025040203096144c14000e02d0000304005055004221840c4000318645000750155000308611084480402022010007555011840b00030740c005140f42c501400389091080454032003d03145d0791240c40395602c0308103000c000a142d8441420703034401000810042000501c0045802608140600c099403401c0507131644510180c11030417074821f0400c5048070558402158500500807080c1d9103065481d200700040c251880303c52159110140c3c0740a4542c12090300b89050305065541c04d80b201d46d40d0721007402a565001038080c03007019038040c0c0f41c2400465010405006020101d01d4805c0c043c0c1003656407201598040c1c0d02911503000c11480340e00401c4a10b5a001c0c4d482a01a00281102d61403c00070348000d14004030080b0038000b04c0302c04248940c44500442e0040c090380d10898446590b18083c09544c2c2e403040c13103011960040c0d100d50085030761000c001ca07030480d80c0d054145d02d0a08059100c1448966000e00b0380303039061260664071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 980489433 1250 980488183 980488189
    0xe06030f06010816091512020103060e0108010902181608040c0b0414041b0e15090d050a140c010905041e0618060617011502031b060105010f0c0c030602090609 70
    0x1d81d020b480c1c0e04000c2c003a0309a15212081964070f0340d41100f1805400c04401003d11500b000038401101e6070003000c100551600d0006800901c3d05410402d0303135440c040004a00e4072415040980e10074826650310000301c0c00c407000d40748000350551f40842040d107244440700d0340364030441140381c2090003810820ba815688440f0022075500c254060380d4008180b0354400004c1c87c2501c01c848625a8800941c04007042804000740314480b10b600c15071060018842e80c0781c80060044c02d560404070050700c0304904c0c0025007800d5948403401e02d000c5070800c0d00c9003040c01e544000803540e02c0070f4030f03810384849041500b40b4003088080c085003441c0410000c1c400500c480303501a01d004007002469100c032100708880c094002c00c015039032123400c44001d202c0e03000c3c842400c04420701411030458001030030000c141210703014120b085125070f070000035030404c0d80208074103e54408122103040710000d03222410021a1900107480f0222010805030140440120400201d41c1580041030030103c024000c40c6405910000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 980490683 1250 980489433 980489443
    0x9060d0213170f0c0118030b01080105040204290108360d050c03090f04020c0714090a060b031602010605180901150807121a010b0901080a02030705040e06030f 70
    0x18070075100700c4403010818041030903280c003100c10090002d000700030018040c0704c1e520b500440d0220704000035001c00322414000101001c024643c00441151956511001d02e40603100640301a84518542042c2da1001c088d23080e00c04004c842651540508034a4101c01584e20107001408004c44040c0c06413007100030301030300c081340b0300e04800c0701318003096040c44000c0c032442e09002c2c03080791040c0300c02044540e8090720004152020607104032038000d8401e52003408140a80615520401e040c4201c0801113848884440490345001003920040165603a000d40c80c02500d2041c0300c0c03072804040420100b485080303a0340b046010b5408500012400580d00e6000c5001d0000c102c95080c0104282d1060042c1d06a0a00929810b0201c040c0344201250400803003907110081446000007443d41c0441c40001c1101c041094101081030030883c0c0659a91050b200e20241e10640703a603030015030018002081c0c1134092090b00d009410aa0b41c0301e0070b181c00c04000d00f000e18405030609915201e0003212103210401009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 980491933 1250 980490683 980490697
    0x50307060c17211b0309070b16080c0304080f06100b1602100c2009062701060309050c030d052b0f0e07060504060c03120e011407180e0a0209060d02 65
    0x8070f04500391520f11050f41d00280d0f2130464400d520004c100740b0405d1b58000406009403082900082d680d41c42d0343d02400b40610312001c0042c8010404030743c820081001001810031540307101c040c0c4024003500c0500c15100c4000703d0385000c1d1151808018009070712540040d29011880025241c0701245680024040094000c03074400050720003840c0c80200001800011707400c0c4010f040880240c00703004001950302c6130040c8883d020321001c01103000ea400780301840b07803c8a6603003040281d0950311040001c0c0035060060f0162560300c251003903184603082c0003405007450003c50760703141c4c2008070314010080a80b014064011151041101c102c100410310b110301c04145000b80c00010f8502c441c0641c035401c0034420361000e014002c1c20b2108120703103500305c1d0606050036032501d0161603183c07038584540010442c0d00c0c225070941d0f00c1c1c080c0b04192203550601c054000d0209072902c1c003000b14221128561f803212801881d540008840100e0503455050b000382c19105002814a410020034a0303e1f2022604410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 980493183 1250 980491933 980491987
    0x213020f030a2d02250b01030803060a030b011e061704110f1309120c050d030203132102010609020a0c12030605090c040e0c030c03131401021c06050307060c17 70
    0x1078008401e400f05c0c41d0500720b0100041c006607580c0294071510070702c05c01440090190080080001e50580d00c440540000c2c5038020070b105c02958607440c0c45514a0941039081d420f00c8852580416082d00410480020a07042405281c0c1695599100e160920346000502d80140004100800b0b0f07654180000752030301144040054050809c0c10542501e0b03a10021440138000d140048002056000c05e9400501510342809680d80e282c0074800380c800d03150303010082c2000000a102039000a0241903480c111401503000780a00c80d21450701804900c690501d550200d5000d0741500f00042070345410700c12001d901c2c2000102c541c0d441020070400b000881d503004d40d00d00000790911a07504020a900d822240001e142c41c110326005c04003201c01e1001602c042d504001c4442c00300d04000180c0e1510400440b100025512014040c07600e079038440078501e00541c401d0500d54081900c2c100065a641250003d9a0364021030265840701594052100c245e208445803c101c5a08520031044028008070505 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 980494433 1250 980493183 980493187
    0x20d0c02060a1b0c0303020c070506070503090a060906020c1203120c12130c0e0613110d06080c100f120c1d0406180209031009030305040213020f030a2d02 68
    0x30030400c40441d5121810307007004403c5901c1071204a035010f0040404158907060043ea030f1060003c000d1303e001040e600555000000003018000c100020016248031401a00d40b070040341c1e12500d00b40c608034800c1c0203103401a802140c10604600e45040038400c1d0302515402e592400e1201128404143d07006c07220b042d07042c000025142c1a1611000c031960b40840202c00c2d0031282c0c803243c0d0f250b0482c03e00c00d100e8408842c01c0b04000c600d4035541d0322a04405e90f00710400810410403200c10451160b00304d07040384070440d8504000007410b90740110700e4007888500141070100d030821070342c41515601140c0c90440100440d10341d4125194180d44908040c00486449280414005007002943c1021502032280524108071003040840d151010403000903c008401607261928000801d00e05160021340001d12810482c1490a15806901450003103009030342d540b240007510070352a01270f442000c18403000f2410070000034039442d036154000c0c4a854260f04200c07446400201e01040c10281d4003c00070001680 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 980495683 1250 980494433 980494441
    0x90c0509160908060609040f15051503010c110a0b040f141b040e070b0a02191b060216050114070b041505060307051c08090907030e060f0402030d1101020d0c0206 71
    0xb100740c2c40b00400038940142201d29103100807900744603002e44001e21301c802e4032040f00100b081061074641140e02c0204204032030b140840049508001c00c484184c060351a0881030070b05103125012031b06040c4600c00061960710a0341c2c1e02d074003000000401c02c0c0e0310726620040400c00070b880044102c400302180030042529508140085050000c1c00001a120b81e203410310b403800982c0042958021113107500714064840c80011000c0e402c00022525024141040504010402c0512035403018007100c4c14001444181d218041a40d844200080d007128004072894204241d41c400c07441000b0030307480b41c0c44d80e41c14034400c3c2e507a81c00417103130544048901664603059144640c0440c841e140c1e000e030b821801441003e26081c0850b140c809812007400c0d440003c5000c40ac2406518011288400f001804d501c0080c40c01e00c078001c00500c0d4004215055026a0000c01c03e0106008840d5000d290010050a00b01d0050324040c1c907040941d04082005540901c601e0428042380e11407029054a40c4c0c014091a10b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 980496933 1250 980495683 980495687
    0xd060209031009021008041b090f05010b041a03100512030a0f05040b2205030a0f030e0a0f0b1602101106010801090b16020c0402031303080f0603060604090c050916 72
    0x300c24240c2c00040c2c0c82c2100301000360703440c444051403005003418024000c0c1c0f110300f0210000e200411021f49071108102c03000810303103110380c4a04d50a6030640750401150b40c032041c0c0e29959100d00e00c01c015100b00c45400c104545102c0070300131178101040c101c0b15034480e036071007001c01c0c0254580420b00326503070004a801c03c80241c206c80580d503403400629280307150906108010301d950146c000b00c1e82c10011800070715400720302c100c410308003d8040203040340c0b50b607942c5140003100740c00649800c40009500350341d4a4284d0400d11140c40947d0141100b460340f2070f0410485200320b0b007020001c1c6009950201401000d61075290310401c06d6030b1307d582c402d00c241180250451a006c0103901c4840c60b40c4c503000d40f54002c6074a0824142e0007204903001c0085c0d04922180803840c0440f1440660761091000041c01458404200c1c2800f06520a4440891135514840250a08441241c0301600758005100162143c5050b0707009001d43c6100308800c004181c1c0b0b450126500799002c071203001511085802c0105070135 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 980498183 1250 980496933 980496943
    0x15010f09080a03051206180a0b0409050f060103150b1507030302090a1509050612040308091c09050f010c0308071817010204051f0c11120d0306050f040c05160c03020d06020903 77
    0x400507200101c181681c87ca0f0307a451014014030b202d01c45699203034060481d903120b80228140365002811034203002c00c000309140d00c0304400c0c4411211200715210b0402455242d0080c10201d002c01009078104259401c0b1406040c2e010300d03c12010140e00300302c0a50180d4406080d1005070110340301f206014100f44c0740152100340305c0d8009a21881c010f00c0041345a607445d00780301398403036423601c5c1900e4152910181c5070310f0900350050341c1211100024180e5440c6610425150171240d044130401840c0ba01c290042d1400000003030090001510107000a80c140c1c050701e40c4940c1010b20b0480c1a20f1181d4801d4107051040e030265140b03031283d400080070031252502405c01481480c00032034000820790385000c0a040e40450f810003c0c188144210300420a50b20070017824100c3d14048142c5e41200d40f03030000140101030340d000e040c1c03041300300c9040d034145400c10f44500500402c80e40c4400c0d203800d1500e0162002910107040881e0081c0089001200684800240780720440c800c05005d0784941419081508003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 980499433 1250 980498183 980498191
    0x5010903081608040e09031207080106050a0e120a0602070203011d0a11031006080f0d0801081203180307031701080316120207092c0615010f09080a030512 68
    0x494501014404540d0001c11240d4079840d00d0040301064060f4a00311089000e00d80c0a50200d00c20002009410f01010008104800c10020300c1503242e03036261820303105c009081c01090000342c000e2103030300501406400c0c51089001d0007000c40d1581a100c2c0043d6181c910510401c40303800d600810351008506090083d80b2078040d40070f4910001c5560001c1c410380d542c0159102030081c42030740029000f151001d124640c5081c25512041c004141c60b29540c6070303504040caa43c1c420512480314032091080c0b1840a840c140d91103440070b01080e8010b904080c1e480e41014000800c01480800040c00c036001c10401480a503120380c854003840034240c0d40c045011801640140f03020740081020900080110840d2040258800314010030840e0011040f858428990001031080b4035205814000344011005060601c1e0303c100c3c1c400c0c00103000c140d03582e00c1d00010f03619140b44042914501c221507000345d4401d118003521b4513000e41c00319903604090b803610007040c0d001e6000c5030b00003230001d0ba22a00e038403181d540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 980500683 1250 980499433 980499437
    0xb040b060a08100e2b0c080d050408070515060f04090c0e1501092405031e04050c042405091815100501030b01020d0305100b1206010201050108150c0d0f0e010b09010501 74
    0x12200e48050001660700717810340803d04110705503078110704201400301964003064403d0002c00c003501c0c1c586081d41c1c81c2e610800041d280c504c603514100c0107984189022074403507a0058508050603d071207041c0005811284001c0750340851101c03000c9282a64182c10342e12030300c1d44140e0412141c070b01c10000760100c001c64100200800c2400300c0407485003030742c040c14000c14101e45420356490f80d40300e1501c10075078210494010560200707428413003031210005490443c0b1070200c80c100700d0f4860024024034840f500614a5690450304482086140f91030400d86034806540c6000c031102c030003010859828154170000f00d4550311041d200784500b0704004400c20001e0301080c00c0c1002070361720600000c0d541c0c24000200d141015100d60010f0003074146000000018449050241d4441540c6114485030b4030302180c9080c0150b28010000554410010b40803030084010100d800403034a440c80142c50541c4111007050038580c136440c0c090203014603842440980381181c800042c2400103402001010380c0c0680c03003941 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 980501933 1250 980500683 980500723
    0x7080408070b181c02190506011203020f06100f0b03071b1104060902030612010c120b010e0a06020309041a0a0603240605030a0e0a0b040b060a08100e 66
    0x29440c6040398052500a15410303030903510306601065400011070810481e019488000600c00808a0812040340e020b800340c5100810880000381c034804002400b8041394841c034010410418a80170706020079000f441038404501c4c481c0c056525105c1c041e01c0219020220350000c0044110b08040d82d405008422845403840c104404014625840c030100c42aa4101c45030000e400c0100100003100f040341d01070406c2c00021341c0d907d603200081d013040f03808601030750814910b0340203054184503102041d852a240c4035003841800030030a00601c94140400d062240c02c054118480c1c3d03c5485641c01080315600a5030385d03007200030603c0180d90410084000d0302048110244466a442c4d40e22415907040b4035000510400009502c4030400040c2c0f8418240040d103400494a1503000c0002d40c07007810291824084129508512f981c1c65851070f82c0544810324240110f400928000b55460300060024042e083c0a900c48403c00e04140580741c400000365a19905c0d000c4580046c0800440b40c00b00c054016 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 980503183 1250 980501933 980501941
    0x309030f0c1f14061c02041e1b052706031003150501030c14010c080f0705070e010b0921011b0f0305010f0e100e1504050a090321060b12060103050708 66
    0x281295402038105481000c1780040350b9440038141d0084116284c00800078002807454203000000d81c00c070307030000c409042e042c040c500000c260b10740c1d01e491036980c80d6900d1510300f652445400c81c0f096840c0d045130000c170328071070314180311a40c0e0303600038502820000206044880c61031030b00300401c044100710954403074101001080403070718040300c000c00c840b0000c0b1001e01b04030300400102d170b29585001d8010300310b01c00480d40c1c500e482418409002c00901c50f20407185583d0301c1d0318014104000034807400211203000c20000b081401d02400400c800d041001112448409254a190030341d140001040d0090694030150320900340d00143c40c842d03820050904004950501000d11400c1031940241060718400e000820302c40c41d0006404002407030340284e0072150742003500441514204034003440384214100004510704204030302c18030b801c0f11b51549074610307a103017541d0740c0700410101d940c01100030f5540c0380c03400110f050002c00207141c50310003001e06401e0b40c6070074070015045906c054002000c00c11018204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 980504433 1250 980503183 980503211
    0x7031502090424090509100504051606080906010501031107080307031a0f1f050910020c0114041202011107050a0b1309050c0f07020406180c11060613020309030f0c1f 73
    0x1d0f09407246484045000e517a4501701c0c0d854034081d5032515240c41c0c503280c100000e00c580403900303403024118540700622071581c4210482e4419010f030780410b15900244010012980a1790110140001240005040038019160882a41c00444041c0d000c280c448049a44010380320b1600801c4600c210b5440b8110b07440305010614443ca150014152040d112214003111400340094072030225000340120a81050450029141e442c00820280890444114030440410312000d60782641d10544015998818980044410280f81a0841040e004540b004669500c4580010018006d0221416910241d074a0a80001909503100e041c9031072408040c01400511701c822a0a24070101c4201510303140180000340040800303a0003a9020f0b00d421035240070a0985402c0401d4403040798481c0c0705a00c1604000c00d4403007508035006a0300c404003a070501500d41d84c1c2e80c00b03107030000090402c59083c0703144903108902c1e50740810503d94440c0e10001000c0b00c07002d29608000c505084111080c042e8544007640 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 980505683 1250 980504433 980504501
    0x60102010522020d02040b061306172215020c071410300615020124061d060406031e021620041109040c0e0a09020c070315020904 57
    0x20322034905134610b00d0955890350080312031030500500c665650f0440a51030340c4102d00e1340c40fa981c082803d008c02c004030f440081c2c00403440341c0d00d065a000c4005200c000d060b200e0316210101201c00c1c400c030900c00c140c580140d2020308840301201c0d004002542c10100480c05010428504c06e110320290155401a191301c6400f070402d100003a0003801c01d83c804072820700c00b0b0020001c04610428600140000d500b001c4202c520908409030f0000c0207081040c1d50590306080d1410003080d854030100d08200302c0c0783d21130b40d070f028940346089458203d82403074100069807942c000c1e400800001d85844103c0380d039032000285503078101d070880d908501d80255a0301c02860300904940140840440c41e05095005586440351140310000502c100f101141e1603a40740c1003508140d4200b40250311781180041000e00442c8c54544900000301111140e900d02a00308000e035010b001c0882d214045c8402c0080015030b100000346440d000c180c005070700c950401c414001101d106065510010901c402803c0c0506041c8007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 980506933 1250 980505683 980505751
    0x120245090d140d090b0601111b06030a090c12030314160e0a050612041103030c06240306240d150c02280b010602121b0c0d0302060601020105 62
    0x40596a0361140211080d02e0f00445080149a0341002c44000820400c8092184100e500340c81c0d021442154108881c0d9411604a00c0013468900071100502e5140800c0a590b100600380000b02e0224040d90340e000114069602140104081c4c044070010150507000d504407038412803c580c00249081503402d4040c0c0120a211005e0240d0400610721917140e40168401806000e0702d1544d4480c5440510786603500e085400b640d860600303042a0001d0326000c811201424088401000b40791104100860b00c404451261344560100d00d02050f1140c400b032098601c50b181300304c3d213689401c0414040701d031140c01c0841d28a205040c248100720005407045c948212262101e000002c03034190041c0241e01d043d80340c4031542060600d40700c2000c200080c0001d06000d03d0f01c031750100c41c00b03a40d0b80c0c8001c2c0da0b41d031300b1500e2203080d143c01070051218421028030055030100107181110012402000460542200250240c00582162082000558090145940040213410b41c042d601414496160748585054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 980508183 1250 980506933 980506937
    0x130201080f0613110a021b0d0605090f0712030912211103130801060e0f0f07020304030b0a0501081b0102031902210a0807030e07120245090d 62
    0x101c08151281c80316081190301c0c040c0f03d071041000340800540240145c00c194200e4005100f100d11007100c049032409504662034014042d0802905c1c0390303035810068440202111481d21030000d440e01058820481c0c0001007255440a90a100b0305060003400b400d4550020548000450100c81c0020616400900c2c8030008c411140c0038034a003080d0855081107066008441d81c407001c50241800e481101c0100101c680e540e00803c0380c0e5075286419000b500003122401d220502080007e295000700041e19640241c7c6441075901d460f840b9903038903550201c16249000c2c010782d1840140b0101104105142c1d01d6150361441c81800158040000d40c1c9124011614154662006103103440074000c015019060801d501c50604858112003110030980011030070070b0000c3e03800c1012a203010700920648442106140c05800c08906062143c840450305400803600640c502c010a40d48617a00c82d060901380c800e0340d0038a100811000b0b6400e10b00e12000380d0900c102180c440138450180800507840311260898 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 980509433 1250 980508183 980508211
    0x20010e0307062a020c0103061403032a0a030c0c06020307020f0f0a0b04080f071502072c040b0105040506060906040e04050c0a08010b1f0e0415121a13020108 69
    0x102043e094036032120031105040ca0602c14440c26410f4012078602010b2400f030740c0c03c014403582c941c01c618150b05020321142c2c040c0c200b08075100745800b02740210942c890300c040d11405030102055101d89090300f03504041d00054848ac643d4000c10518496120040c821880207504044076600011034000d060340007e41b041c4902c241403601c54544c82c0f00000280705540149840c0e0342d4855516843da44001146402c5004d0000d0128002c001199a0341140f04564014040729040500080c1c2040c40c22a000803c1c45940e0031582070b9648044100c3c3c0700e64820526441c03554982012311080d02c8014019512448081c000c0d41c1603611840103071070840c1c071450181da248bc0c50724100241401d40614031140c000e240c8a4011235103a00541081c03501c0d00040e1800d0f0484c200780d51215011500d0900a40b00107404160000c1c100d1500740c208080e03d107900da8031110132590311820220300812220044907410228140c2e4102c0c2c1c480114010b46c09450703050b001a5210860340000d10246c4000c01100109840e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 980510683 1250 980509433 980509451
    0x504050c040f0b1c0c1e0e1f060203070c08030a0c02370311010f050a051c0606020a061a031f0207150b100903150b0111010c20010e030706 61
    0xb5503007000c0d03100500901844184020280d40c2c21810aa6060940f800c460b5114009406081c0302d41d95001c410003400000031300b038203203546903030f4005e009010854098848040506003005c980000001032845400039541c491881c502401070120079441898076420520100c10025005201d0b4043c1c0c070360446000c4102003400510061104460b80f54080745d10a0b0584905818240e40740101070700d0041c0040c030540020500110342590200d0070200c00a0820b0104c041c1e198010340c0641b0829101c1c4070103220105030b40c04007004590044e444480140e11451240003800554418403000d8505100c20100811400340030a60f40c42030003030400c1d840e000031801c000c6025080c0e4146c0d0320503940007450300761000318103c01601400e4442d100314400e03a001903e00d06894056121501140e0f880703221441c90b8001c03501c1140c001d040d15040941840407040102c02448028803034006072907490b4a031490328131a00b00da81d60031141d6104c6510910b0b8506130010b1107444d0008151a4220303440800403403400d40b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 980511933 1250 980510683 980510711
    0x16080325050109030903021201020301120311010b19290405090601051c020406120b100e01021504060e0d090305070b07020604090203090c1504060c1506081b040b040504050c04 77
    0x240c4804040c095501e04400582050b61207058101160700881c2d25525001000d08801e00300d1000b84903038200b8940d41c40010001078000d07118004141c0408000040040c5106d021480e0180b000d02611029403969409201d0032211119030307110b110f603415103400d04168182444072148a2030140f81e02ca5518600000c440c1e0f803040044844a0240f1146081c040d600818150080d400a02403a400f00e80c0c840c04954902c01c1a10034108800d1b0010020001100d00d82410f4070b01e1824151001d04501405021103500718070080c82c0d6006900c2402d0005038040103042c2c00d81080800e001403010092074150400c08a0000500d01c000d54042000c199568542032001940520035a40702404031400030080000c2c40300003040100e220081502d0130451040e40804203003041c071540c010000858140b104140100703540d00340e40c0e9044205240c0004001d0f842c0c07402d8900d09100895082001145d0018039500350506000e080c0d2a928140c505000f42c0c00c19a41d102c4c1c55038001d005d164017484e03603030341c3c2032500b04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 980513183 1250 980511933 980511997
    0x20f0f120c0718020406090902035b0803090603010605180a0e090705120d110c040e1e0304031101030203041511090f0d02010c021c050d0f02160803 65
    0xc8142d8414010f5400900b20440280d046481200041303510880001002c12050003200c3c07082c883c140340e018181d500b030303d0300000744a940c060004014408042840100c1c02c0210354009260390002480501c0114001105c01c1450641203c8030b00c2d0024011216551682e005580c103484113802c06035101c890400e003c005030111035440c42d13405102600001400b40301a42100e0152408030255031255407207806011000303403414195800c0b64807480d070b87d03a141c600c5440c1d00400c40d40b680080e1542e0381c040030000380680d90b0964000c00603401c917001d08002004022113500030307003126801075402c5c545903440e004000c4602c00640d0f410b240e000800601040316258000c041201000003c21100024540d031482907003000400394051501441c407440946041560f10a1080d416500e8403050b07100750b402d021420601c1861180a0709081083c071001034000e0003c0320b107088081c1d89803a030101c12200001c0c41d152400040601c000481d21081c410808040110340d9100e000034044a54a1080c0903c2c4900c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 980514433 1250 980513183 980513189
    0x31101090b01091b0311040506090a1e060906181a0c0105010b1804020702150a110a050303160809071a04030515011406040b1815031303020f0f120c07 66
    0x1901080300126a106299000c804e5950002e208450304c0300f03401c071054003101c0008201616000d418002000b061400400034820040007410525009030350351382002910700c035680c0c1c540c8103a6407803009100080e4404c06290040890f4940040718111070545000b111189004e5024601c28078124201c42012401c12134617826202d0008011300e6a690808030a00e400600d003180607150620341581b02480c25000361814550018890680307014490004481d40e84104891028860180141202182c2c14800c080700c25025102442d641d00e00303100303c0d0020440160003281841000c6007802411040081c00740103550004402e6042081800d800c50700d24001c540c4014254800c083d0410740703200090000e14103c8001010740d080400301d2804011103405a8000c000403848203101000e1200000040d815541c580a01b40020132080d89841001560045404d01d81342a148140320040541c104a0051885030f110050b06911401c848100d842d200f903032034000602c00008c1103011143c08140102001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 980515683 1250 980514433 980514443
    0x1407230715060303080c0708030c0a180b0d050a1a0f04110a021606030903020318010c060e0618010509070b18100207091401050604060f0c24050c040501080403110109 73
    0x41e00c55100500010701520b001c03c60010703c5520128511400784420399000c40d43c00081c0b030381541c1c0e03a20040151904052103450800043c908400208800140e01c4000751240c02900b41d680c40c4c0034040c07107058031006050782c1e00b11842d050000221820b4031001f00c15003a811518003140201120000380900880d601e00034039608009050484103400040304400203440c4068a180e480d5600b00550807030b44449809009038008019210f498542c208880455000c141446840b4407540e842c2c88007201d4801c862030b0955031145003800704403050384403001107000d02c80000340b05901d44a008540c540200d0b1203601c08059001c90700d4001c17410502061070311007901904140740541e81a00007035840f10140f082083d000e01e09040c05400550440505045e2880908103d20702403070001c04541e4034880c12400401c10002c2485400040d507500c1c001c1d81d15070003600fa44640143c034011010100d810240168507031080420080140e030341c110040301e921540509021017500b45402003075016207050000145 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 980516933 1250 980515683 980515703
    0x618010f09051c0515130f0311010603061416050d02090a15021c0f0e09070302070b070302031005060414040203041506030f1202060603060a270c030614072307 70
    0x54020403003090080140107100311040401e0081d00c1c402485ca041e24a401c0b0004006c03164004560b00e0005900c1c2148245071041c04040702140440c2120081e400071503d40c2c0d241c1c4503c0d80b40c6070004d4941c6402c030441d41c3c98910500300a143c080c11600c1040802e103c0d031034010400300c0080d641e0010b400b00402841e01c0c0101c07074598001c0001e444a0386500014401011038448203181407043ca0702d600011041c0e01c2d1001001e4103241000500f0000800300401c00d034007000f81c0c10001e12078048850103a0000d49001d038076418400044404411140c02003402103000780805c00c50300703e4888086e9500b88040e20010703a42d484500700304241151a415a00540e0b062050000400c810550740611084c054100381c44c500c0080b030001c90301d4280c2550030036810b91103c1c0200341440f8444c1d12108000c01d8480403080d04c1074103502169510403035254183d45214004c1e0041007406400e0007148503030b11080c2d00707158952402d107002420040066480b04101144014000c64848464045614150300000280 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 980518183 1250 980516933 980516959
    0x9210c060a0e0c030115080601120b07080604180308070905060a020309060a03090218190207150c050910050316030203061c15020409091a1605090a15020a05010b0618010f0905 77
    0x1b1013540307128032403462580304d6000002038400980151444440d17106048003045d49504d8412100198060705050744155501054010142401130444200c0e102c0d4603a12018680041c01a01c01071080c2d1016004000c10424038400759030200840b0665a8100d6603562100d10302c1c00120010850f124000f5000000001c12200a51040c6900da1040e81401c46545200d00c001480c0c80030fa020311100100007003283c00161140b01040e40207051050307098500b85041106003000187c10048050140c0042040001800b103c552610000c8481000d142410340c03541c02c20001050030300b907038003034028805800060003004000386161b0141d42c10111000564845840780a42c0000f41603243c0120341510b4011560f81d4503c003034054480c418014050182c80340400100d00381e4041d840844401d46c0080140700c0840c541d00e020f006000c01324405c0e4020141d03980306149c4a0f08407009011424801d010900100900528010741c07071100000a1804950032007900e0f00075078080907150010b66021065410f09 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 980519433 1250 980518183 980518211
    0xe032e020a051804090b0601050721170f09060c0c03040f090b130501030c0528032f09041202010f05010b0a0215060d24020309210c060a0e0c0301 64
    0x10f0a050031a03500d85034102c0050340100011211110401014a05030f280001c40300d601400242000501071030b4030207040c05186d21410400130010764420b010420f18400300d1219810941b40395803104259a103030400e81410744c00d45907507040c010603030700f0340d01c000280f50261024140161001420710079240c80c41c85803100388180113441040880e41c01100b03141d0950b59a5003081c040e032070480f0781010114040ca0b0070301c01440b00302ca039503204c805000c0b402c01c4c5075101081c0a4044a10040d80035098070030b254803181d004003030405034902140c20007aa4160464260303513680c003103d513081944484c04d409104003040b4168050891013003085507640c41e10000250140c207103001484c112450b64240c850114403050051203008040c3c840540108054038000009078007518a1100c0c01900f10070382c16040081490a803e9030310440d101140d81d00080304d889440c0541200c0303010004840d0003550300f0b06c26848407507030350741d080109640b05507a04d90102800d01038090000400c408406802841400d0f82c0c501a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 980520683 1250 980519433 980519437
    0x50f0f07060f05070c05040b030712050109031103040b09010806040b04051303020d0216170304150309170306091512030f130e0601090b070303020417010f0c0e032e020a05 75
    0x1d0000400c090549449109200384100d464040c0e10070800c0c0300b803504003007d0100620b09101c8164242c4211480410b820000d500d1425180c0d00c2880041040075880c5402448043d8111620380720340e000307020034800c0005500658111010a10b048165a0741d01800100038100d06804603400c0b615020030701c00c0709100e80e070507403803080d0084e02222900d485c10130040703940b00810144000c501c007003800c0620180548103016101c06444108407800c198498800d128a41c148005e4031000c266690800403c10001100c00000d80c0e010052807815450700a0206440020050002c00a0048081031206c951782d0019130080080e4003504480d00d64040101441e800c0d800b80c039034018001044980080c0e403916419880e4400c1106a407410402c501d8552001c685400911080341415004c2c080456140748600640d0300c5030140da00003190111290860000701e41d4018104810400007090104082c0c40000351103101d030601180031000b406a55408040c54440703858210000f070b0002600c1d0046640c4540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 980521933 1250 980520683 980520689
    0x315060806030607050a170c0d0c090f21140a0c0617010504090201091203050d0903030956180f03030402030a03050a0302070212060a0c0305040816050f0f07 69
    0x41110342c10b84803c40145c1e0640200c8100a0004201c2042405000c01520035950401012210039081201c0300580301c00b0380c0c002c40ca022002071100f000400075840c00320024002071102944040100c900c2e885052444d848916010301403805e078080382c0c841d001d0104a01030545030400074449072244c81e188010a400c00d0a1925103800390994008140d0b85440e1040b0409568144c5032810180e14140040158840d1202c050f800d2100c02d2040306101c40341070203030352119131207030f5000126480301c0e2801104581c142c011041151144d03c0c103145401c5441d041a07005000b10781d0f0050410525000d0340c0042c1540d100381da1414030801c0040c0030105e8143e0001110742c41741c48041e0340c1c43d10318a040d000da90740011540a50316501c03035004280030a0041004024201c80b525001d031501c03500380c01190300c0500c00c5615a442d035015504020f6405054801c40310500490700d403c0c807080c100358031500c0543c0038110400340c08030703150825041003240800c0300034820382c0454140c3e081c144012140c1c1e622444030b44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 980523183 1250 980521933 980521939
    0x2011e020d0e09090a0f150606020c040509010b1003020903010e0a060506090714070f140a0c090b272701020d0f02160605091009060e07090c080c09010315060806 71
    0x34407242c500b40382c0060f0492003500c07410024010100c0c10380b41c590000c000d80c0e805480f20001c1d165074020b8141d69000c0c00001c2c195680081c00540c00030000d00c812030720010011440340e4504101086940d450540142c41c2a84074076015845d00072010021f801004880f0800c0c910b4424200d00790200680da400891143d00f085445400594030700c007054a07080c402c00907800c0300342c0c000c00c84440010300500c08821000d026032405001c046041d10703c20318090245e1420f0f62003a06110041140702c89034000c0d820400429a2036256004025403083c0000d107582160110300f0018100003001e00e45075804030461605c0005403610000203a22640d03000b54008110307100e00c0350800b078079005851014001c440e4a0700d84003103002c00d411000c1d02c80d0fa000b844080d19070065801106000d42c014510742c040d9118090040c180094024005007402e440c1c402e00340d22520f032003030424000c0401103030402c205a500c012080184c640d5080304d0700040b0024854401089400e41c58042c0100e2107680c0522603074030800d010703 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 980524433 1250 980523183 980523197
    0x7200c1302040612090501061703070c05150a120f09030504030506010608012303010b0603100509090f03071b1509031203111c0e010204140a0e0c0901050702011e020d 73
    0x40225205910490183c100810480d200c20052001070742d12661090340100d000164040c0c50b8505040300c941821411141640f0100d03010f404e024a03201d4803001008221821440c41c07c071209421070500411496809000902c45804404401c940294003003841600c4200001149858040e20036000340c00256114400e10001140050080c00d41c9410703500203548041009601c00b0840040607440c500680d0995251030681420741c51341c00c003660242d516015501d0754903081400344465074000500110890b0301c94038803ca040d1030040704540e15a50415451182c0003c1d017800c55640c103075280d000128201200c020129250b07840810b9001380da114040c0382c036910140c84030440c19605405403082040008024101900c006048105914140d4941c04110340741c000002d60b08980040c0c2c010315607000c21128000395031420b62140e030081c1c604806804814101002d10a0b900d00811944506024000440c84190380c014a1100c10b1001ca0300c0c09403000b00e44001000b52500030304100907001c0b901d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 980525683 1250 980524433 980524459
    0xc1e06070f0206010503210702090a0f0b010804150504050a050304080706120903091e09021c0c1103160c0306021b0d030b090c0a1b080c100b0108060907200c 69
    0x1c0815464105c8400030300605845400d4005113400114582c40c002129004219040c0143c540710440c1e442350b02d02d40000a5a003a20781d4004095449581e82d450400030a4800c000000c1c0106d00c00401e14150050300203210b54851034905d2038004504406800e61101007400541c0c0640099000140c03401d55990401444250f1003400c25901d01d9003000300070072821036003400b40c403c00d10085d1780c40410714102c580c1d80742e64079076070b09040341d001a40800343d41600600e80361200c141c40c01011802c40d05490a040c075071042ca0526516400380060321248200c04070a040140561801250081d41d0008011555943c0418120500e054801503125080c0610741840c40707618028401ca044c031410150500c210303541c8000491025030300a05204007448002c6100800c031400c110941c000300c41c4680e001c140e07207442c6664090314060181010b80b40d2503041a40078645c41c5d03442003549810080903035541e43c0588402c0c00a036242aa000342c00c0b000c98685182c400704080c000200f10080142c243c0b408006401c0e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 980526933 1250 980525683 980525687
    0xd0504110f030c1203090402040807030219030b0c0708070204050a33030b0c0f0f041d0c070b1e16231e0d06150315050a0b0c1e06070f 59
    0x480300070081c0c2c1600060303191001801c00e8941c596404c840101a0ba1400c0e404000040032078005422003e0b0540c04544144210b0500d504070311a00d00b0140c1203042c1491031503407000d041c2640105079401180010454004103d040401e40308919030041040c0414500000380c0002481080706825011400e007101e130b00140441c42c2c0340f800d1780d192841020b0210703017191140c071000400075100240503079041024000c1c074041500549240345100000c907079514070f05400310f007444041c0000c00300800303502414070041221a5013110988c07a80071187d81404c0d6220440c0c1007500704185012429401c1050401040c0040341d00b00c1c100d559a01d48450300a03030050000510200c11440140144038420004a00060011400088000342071a441442c10302c00b6a400d0381510b0881d407100368034081840340e03082d046406004440509220041d0072100601e41800200900464858120104800600380308400070038410a8080d10301c2d034510b40d145441081c5595a10a0110303040400100080180c41c8564 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 980528183 1250 980526933 980526949
    0x111008060112022110030311070f0324060f061b0b01170a050f03040e0903070c030201030510031e050c01082520010c02121e030901110d050411 63
    0x10380c060307481a00340900c402020000758000d402603604000aa0b03100b410403040281d4091280c52103151440d5010700e0341c0380151007400000c0b501401c4c1d8100f00b1052041c4103030810700f4400c890f0401c0c0810503d0a000c81500a0640c88000e014030340ba0400c43c0125400318842d04460840349181d881d002d03050114074030700103148051003000301400707200c0b001000025100c0d4150803440100c54169044c40d40f070303940d8140c81c003c80c03071b4003011040c0c01c0071a04100300d0010751101544000781034065072600f081a9101c003001045800001e041c0b50b41d65000c10518011080030303078050b592058100c807500404020b800d04803003000108a80510501d42101e64951140d255140180700103180100090310142444009031110031710343e0100511281800c0c0e031076500c000700300e1022441200003d41d010028a000741400403031607d4280054041228405000c080d031201d408030f0a031001440d0322901c402e03c665000d0001c890059010400119100400e010075034486070190b8480c2d00b081a001501009001000b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 980529433 1250 980528183 980528191
    0x6021015151416051603150c0504120308010812121311042c0715051e0705100b0a031502090f0411090112060b030c07030c0b04111008 59
    0x1010168401c00c101c10110000038144501420000c2c89108403040c0340480740c020841816900110003403c0d410b128050020700f4442902c105030f405481d0079504d50720b81d044521002c20365041e9940c1600081c2078440c1003a90b024050b05140c020420b001424000c010590078080c40700e050041c080408411140c0104440d100344a48030000c51598a020344014007000840096502004401c10300301503668901c504880160180d80164650003415000b2044004500300201c80760300c011010f01c80d51071421a00540c804427481d2282d9201c82200d18681d0f40b201018000ca806880031811002300b14000c00c03000154884104100003001001c0104003c0025900c001380001d00481080c0303615903591b400805071002c0151820b0703014200900442e04940154080d40c2e15460085001c03005980e006c4440c00b4a45640c0409005003820080c11322810300c00031301181c054550016859003054003c10b90a44105e03044043c0607000d280908000c02c0400c060b1105904c2078458003101410315024407031445c09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 980530683 1250 980529433 980529461
    0x40c15020118150603080a11060c1806070c030f0803040317060303090d030e04020c01020301150906090e060f1305090c0a031122021201090606050a0e28230d0b0415020409090c060210 80
    0x500c0f0982050128a0b0310403102551408ec2c121804004551401510490244151199035481c54103003802810b0744e4013040101c001010207018401155000001d541c08a40202e840391026605854142d9035000c1060703625401134008180c203a010b20041d406103048039220000328016070b1102600302c402854900504000c2456a1004d01400fa141d40b801540a14041c1c139443c1c0411200c00018802071043c40c1902c01d2940324020480c1407441804180601c100030385428025070f0440d911070940c14107003a10a0b0003007070082182e20081000c14040300d4005401441150744040458123801d00c074409000d800c0c034007818a0740005600e84a001101c401854030754612400e1075101c03003040541d075540f2801c03000b00407481aa25a03002000da2102004102a21032958001928150701d800403000d01d10305031161104102507800b244c2d492100d40e61140c2d001c000d1240106129903200000e000ba60002c08030a40740000d41d204001455006000f526040d800f00c4100901030351031072080c0d41e8040402d0f08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 980531933 1250 980530683 980530717
    0x10b150a03110904150501120608030f03150d060603020f090f130203071512060e0c1606090f0f02280b0c03040b03040c15020118150603080a11060c 65
    0x42081c800e41c041e80e6844100d001103841c01d035402002a080d00c500d1858210403e4003400208031560304400d5200380f0100004040c0441440c1c0b80802d502d900400104c0c40a5500000c0050f00300841c0c0306030b0010300c0c500180f40d00605030380307400c0410040032180400c9004010030f00c0d030300707e0b80e10300540454414104424041d00b96038684001002c25076943e80700301d800d441080381c082110300c2959940c000c246150358035041500c40660780e29058410300d074010718207407004c1c1080c4a003041207081118103400d1400600341140c03c0d6483c00c080208841640946082e031003031900c5041142c001d24500b0528002c46840c04030a1102810311440f036003100c0300340340c1011088420800300401c44050304d540c0840030207403800d060b900d410742d800643c070454040316a0b4038440c0050004100010303012040b0110b6100170001c40311540102e20324200c1032003000c0c00081000002c110b0b059803c0c0c111300701660b4400e0f04144c5030081c160b00942108200245410f80780603180001c2c120f10500b8042c2c0d00000d03800e14030b00f6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 980533183 1250 980531933 980531947
    0x4140120180a24020601090b03070e0c070b0a0204081501050108060d050a0b0f041b0303080c0304020613031103071a22210b06040203040c031b080f0708010b15 70
    0x103503500740c03034511940108124400040d0440030200401d95110741c1003000741880b24a100080c1000c030f0503004000b28030b1038143d0004007600d002440380199041c8200380300168440880070000c0d800b446400400f20f42402c5d040004c40f2000303801400450310100100d40c00300b16213841121407502e09000340d80c0040c03802c1001403c2c1d40b80000740900154000d0041e1210b490040e101d4011400c0101c421945226844051004100825a4003285180300128808200382135540c0140344100142c0800d5440710302002140541d92144112001080c1c0c500c40e01034640c1e030300d240c100c2c0d420020281d0b0b20f04c41d01440000282514011703045199048034200c0c3c40789000202c10f035070a01200c079108940c00b800c1413280301040c0340c40d0300c1c064040040c8502520070740c01070711498200e0b6191002400c4900442c014028400080c50380c8a800c4c1c03e80340c1c005410000c0f81d26a0030054400d056070340c04110207200f44124054003040110307011082c1d0b20110001e010b42c59030001400020480c1419080c2c032440200115 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 980534433 1250 980533183 980533207
    0x5090d060209121606110f0606040f0f090605060f0f0105121e01030f050616081302120a03080a050108060640020a030f06080d0309020303090904140120 67
    0x307001e102c1004000c07010307882018201e145030600880c0e840c000f0080e0340c10148821303504006640ca070190a20010541007118240070741d21414058034881c09251030f0380e01040401c400c1c2d0450303402180d0108003000b034002141040c601509040e98041e0003242001142c00c0303c0e00f04240c51214031001a1596860b05180030003500ea50000104043c1c510412443c01b50040301204510758001c500a0300c070b8074401140d40c240745040c820080c05000494843c00000e48086070403649040c2e0085c600d0b036501103c0705990007c900c80c00a4822038080500840d1811010550021202800b521030640100520b030388440f03c2c641e07680c40589810750b12160003064070300412101d00502c01820344091908020180500240700d10101c8a060816915004188800c00c0c50b8548600c501c9041400d10078402545008600d90320b80c050803540310100758075020b042044d03440802c1100d86810000e0b01d4107055150509084800c07100320844134085500b030440c10300441c01c5901140d0045046601990f01c0c003003503a001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 980535683 1250 980534433 980534437
    0x328050702060d090813030512091020010222140607080705030702042c070e010501050a030b060a090e010e0c120a0b0d06051602060108030708030903070501061206060605090d0602 79
    0x3d501c46251295a054002008140036060b200043d500c021030040c294034045040c05d070000c0f20b850713100a0900c510a00c1d651140c20b40044224070381011414008462582d420039480016001d202c0d40c0001a1800b00580d5145406040c0034107010003c801c9440302800c5090800c40521684d00100074040741c0003040720040102070f00b0b44078400700c9180c42c00c0380d0701003020344104006903804105400035160802d2020b600381000c10349000060401c9a06000940300f400c1c0c13041c00f6281c1080000b055004201e0f00903030007140c1120300180001d4951914020040c078240680c02031f940310440b03120001405170202d10f1058050620448464181200180d048000e100010504a056500c0e10500c3c070194441c180c0c005a407600500d4042403e1614440180c102c401c98040700d0115030000c0f00400c06003202109a802c0d40b5804944280e994565050302807450280c400050a594606100014001180b80241c40d00e1072207914184469a503644090303e4a0252288880d0444070300c3c44588002105940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 980536933 1250 980535683 980535697
    0x3020609071d07051b0a05030909280e0102040504050906061906020303010614041815150c06020306030703050d1d0f030a170d1508120324011202070302032805070206 73
    0x1694007090740d03041780130310301e45105420f040e55603410014490009081104d034081e8090340403500440e003684060030340c08204070605080e04c01c8683d201c4201400140070340460b0006c00f0014000e011a0800c004c0903603c0c3c20b001e842c0d0764802e44000c001d1207a40c11210341c4400898010303030081c41c00e51f0328003202520041c141040c0181202d01c00c02c0041064074a0740b180c2c1c508440700400003d59140c24250044075078490b6000492140f02985034401010b5112034440c3c4c2065100c41c01580f00e0b102c1c0d0021902c3c09445c1e810003016405001c0c00800c10f650700001100042e00c0300044404221404014050600b01c03502140f509600a40150404a40e22840d80030201c40021641c45c90401055041022203135111690f02038114080b50402002074204039085e4599100b059803440c60412510f11514500101801c1440c170035001c0a40005038011440401900b0303042d01c2c155520322691030020740b25440f908103d611030401c9403041029115202d601c00780c140b000d41301c03107103403501c2d0350200032084d00212 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 980538183 1250 980536933 980536957
    0xf0e0403032007050106090204081b04021315080718030602031504110a18060c020904030e0603070309021c02131d03040b0301050901090506060f1b0a03020609071d0705 74
    0x9903401d480d0381001191580408010f449496610b442d42c00e6403150741c80405610f0043c070040c821400301040c101c0c6100e980c0e00540400c0e10341030000c103001e03006440f200135001d40c2400300090f80200d0075012200741740c1180e072110300aa441030700680340340e40034072042010035205070300c20320000390503500550300051141515100d0a240754005810748903c0f05020769607c0d00810f4100f041500482e59040b103807804503c41c0041428030200400c50f072103107500a8400c5841c140800d042c10b00071b12400140e250068181c590b40d180404018000d045499000c80c05021203250240d140301001d805a83d94070b900401e00250780144150482c00f0b401e8000d1032652440c0c80403c2e1048080c4d0400c000c100400e044080c41d41c8a43c904001c1200b940d105038030401c0031509250410040b41d50302c078101e4440d8200d801c40d280e100d050342e203840c1040000c030404c004214412001c094003419000120315118009804c00c40702c10039220341c0481d08580801d2041440d221035840840c130017900038000b07820807030084 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 980539433 1250 980538183 980538191
    0x60102010e010c0e01030c08060306040f0c09060b090f06032701140103150b031b1504030b0f0a110f0315010c08130f060e010e01080c191d0a0f0e040303 67
    0x203071000e00310b440080703081d80441c104030040c0c1d40550705401501600203050030a0a01d5181c6100441e881d0000144020a416440148001041011107080025240e0030004101050716030f0040712a03035110054052140c042c48444c2c83c0c0710325011003142c1c881d28a101c101c1444692a918002c0441d425141c10009952107260444810900d03048090085020303540080c400801c031481c900c100c41c9001d55050080e00030301c1c603607100246002180000600c06807443c00406004011404507406981c000814000b42d240034400c4010960302480e003e1002c4010401143d030b1902840b01180c42500040d8120500610004542e00e40400150300100018104030300fa0780c20a41d01c03081c090307220340200c810b00d201d07004044c80310040c60040345000d0076050401001c03400c0d400c00080d1140450b118258100801e079000521440364032030680d60036a1040d500c1d4948880381e1103028028140e1002581004203078201103034428078213000c41c0d008550751030030076641180c00d0150055007008000d109600740760315 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 980540683 1250 980539433 980539451
    0x2a0904052d06040c02070807060c080d0e341a090909060403110c0d080d24031514070f050705030d05011d0705030a0e010e0f031c020c0604030806010201 67
    0x181d003410050007035840c0054209240940c108000c031400f8088035411940a000140010080002c0340300a0701c00781e00307103840600d8a91030212598811f41c02481e0645041c0001154002d400007482c80e0955803840066040b042c441500d880c2c4190744490704440815034002c10480001645030304000d21100c4801149003c0b1801c000c03c501e103000382c40101e030b2a03100310200001c3c5640700c2c41c02e2001d0404a0083e103413030010344000403000001a440a0404540015401c2034003560b6413110901c0c001001400580108100200b0860813451000380c42803084000c030355082c80e1042c40b40c8100420b21013805100c07a01ca40b40c080390024491310f0300c9018000200612400b00f04100003500200304100c0d404103096040500c0450141c2d1440500540034032903400b0301051a4001d02640c0d804006d400c000103c001100400901503c41d005da841810300801340010103601000c00140f031026259421040303020070000c0c00c0717030480c410346072208070340e8202d90003280c00207120744c5a00e900b00e01e0510000c14495a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 980541933 1250 980540683 980540731
    0xc100b0321120c0408070e011202091513020a030e0c10030203060a2411061905070c1a011707060207140f040f05090105090a030c0b04030507080409052a090405 70
    0x20b040d02d440981d0240844c08100c0b00f0010030004010f4906e00ba6110141e500d420394000d9201942d080c000e1140c0c0c0795030009140117070150070710203170348400500303021071904280001e500031352092072514000b07414003800c4401e9503400600c920a180001c0c18101e100c240c1c1e45021002900060035642e4815038010000480020074824010305d003842000c084040c80303002703c000e0103000c1440440300043d0020020080d4078950001002e4840000d51004605a0350b0031070116111110040d0090050301d00752030811050035190f9100b410f84a641206540402140b203100340e850040c0d00c04e0000507881900103206d0800d0003000c1c420b2203940940001d8450b0140f40004098804070943c84a10300c0d600c03010000c1c521000d0040c81c0c3c20102020203400d030b444454600800704400003002070041703090f113408502050700c0340040754100303a04108020341b03481e01c40c082240501005d0782c4402426000401070751409540c180c3c4402c9040fa40a002031074480d286003440054074004140e85801a07070000c0d0206804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 980543183 1250 980541933 980541967
    0xb2202180607140601090c05090d0c150e040c0503061f0c0609050a050c0402092b0b040f0b010b04061205070207350102030f1f1a0c100b0321 62
    0xb500c20940110000f144040aa01d03102e01680030241503804c20341c804100f07a4102d4100d0760054010b0725a003040f41c1550410f019843d200350301c00002c02d9080c11011a006a0040f1202e8080d502168103000c2d1415849046545002c103640082c3d21251400f00120007107c00b4182290b89401c5d801c02007849002601c8400441e44c40303d0059134203401907043c140400070f051200c0c01d42000111421801d00b803c00b4041030500d95500b1040100c15011031903a103142c2403400030030304c0c50b69100001600070701c1c1501d8141c0ba000164141160b80d80d82100000c82e40c1c1907510305947c02d840b06a41c17402d640b800c0c518031900203001c010344000f00798001d40c280030511181203406802304185c031311071448071211885009500c01704804000440345c1d20500600c900542c0039501a500300003150b0305450841d41c40900b800c4121040d41c809407035900d003070400d200c072120740304003501c0c1d5040e0f80000c0d04e07051942010700e4019906802402c0b68107400560658184440240707011804a400e408502e00309004601805010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 980544433 1250 980543183 980543197
    0x50703080a08090d0909020c01020d020c0d08090d020d03051e07200a08040501081e0a0504020913020a03080d060e0a02032e09050c0d1802040b22021806 67
    0x481800200d456034190400b010a030000c03120340c0106141036200f4002020340c0388a0042e0000700b030300045c42d6401003400350140c80384022084000c41d0344075100c05013560b0f50f01181030420003141852000501010707000c03400842c1c009441e000307032100ba003081c5411001040300400100915400c500b00b2480150b180c80020312072481500c40003003607801c000c811402440c2c140c0c50035450740d10141d1044009682c0800b40e40440b07100b0708000801303031a40040011562000c001e8000e26461184c10020b002810740c2100d40100d009440007845519182410202041a03601c00383d005000c4c0c800030000180031900034002040c00303550009003207031a501101d840c644140d85070000250044140103d000402840107100801802210501218008050b003c0d07041486030850066840c400074105014a10899401034071540e0104907089044015400d040308500d0240c1c0594a06045610b55007040d00c017400c582501851000e4141a2002541c80a0351040700c000026442804c6140015160f00d8064051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 980545683 1250 980544433 980544443
    0x7050d0306060318020d1e02100e0901062c0310060f080601081c0507030201060f030b07080a0c0e0415080604030809060a0c090302011101060b1314120c011b050703 72
    0x10510b8104000c1c20f607036991641e40402d0003a0400000140c0ea50425000c03400d9021441c1020a200c544400c1051945c4100c040d422002151004041c01c1d44100ca10030144000c0704c04034035a98032003204581841d90199410f0107a0a2035504001c06444101c088401c02001000c450b5060461205101500c1c569445489050403400c000d100841041c0000b602600f8071100034401e0143d0100654051008401c5841c02d00000041002c00c3c903100790454009020000244541c499503480c00b455082c0e41141c0100015000c1c00100b04401010300540800c40d9581d658200c51100c44c0c410080140920108a6041c600e00c81c0002440c0d1401d11185114030f0081e1500119860040005400d0641c010100030f103403880d2010908500b0f400000301c6003982e0702841c0154641501c20030442c010259a000101d021201060720603107100c18001c003030152003000024003900c407a00781c103000d09100003d16017101b541000a0400c6d40e0352046503020308045815000c858001c8850b01d072903003041c0641d081610 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 980546933 1250 980545683 980545691
    0xe1003150b030622020111070803180418051f14071709070821070501110a110102030c040501081009020c03072d08130902180a050618060f07050d03 65
    0x3241d460b042c00b20036448120210070320800ca1401d000c25414150048009040c00700341800d80c103803100c08000c42c0300640440d4040301ea5070b14030000d920122200080c00d1381d106a00345044a6046403204001c010303003a60110080c986c20640034820311568000c0c1d900d01c1d01d401d694524189403448030740000b6024840d03d0315400c004200c50b1503030541040c80108880f03040d0b8400e840030408650f00081c203007002c0e0004140c0c0c9218103000446d2942c81c0c41503640c0030f0119802c00f015201d504882d0313801001804140e449002003100d0042d600342c02e0380801c54904408020a110030002075028185003940329210140041d00c8a40710f14018040b600031010101203544081017003003c000103460550425021361010071040e204580c40c0f41d250350b01c072050040c28000003160680d1000d24440072480505030008080d501c4040e03071500051071081202d00c091144440940c009000d09000c01200c0c41140002d0580c00000c0c0c21070207100c40c5500600c00c01c2d0020404100d20400300c1c00610402e8411100d56401103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 980548183 1250 980546933 980546951
    0xb01030e011107170313060b0f0d03020c0a080111121308070b01030204050f010810090c0f080a1b05030a0305090d2f01091d0a09080408060f0708010308040e100315 72
    0x200031204c3d030610034004c20030100140200142c2d001210500c0b1540000301140d000222404980c3c598407000b005504215116030030000c05402144a4408140507140c00c1080365a40318000e0a80c1d01c031580080d02d00900b00205801c00a02020a0341c9c00b1486200300c81c1c0b410a41d07650741e40164007400d020b6440d994200010700031842e00d40941078100c01c3d080d410f18801d5041c01c0c1d2032138952038440c071480201076940e0640e0040011507003c2c0802081c84900c06600a50b68901040d241c0034071803000c4801c052030b1540d14202e0b02000e480042a00c80280040c001d001e03031a40e059400350b00044515501c0317241c180c0e03000d00054282c3d08104011200e000d00280103034100801c90350700d0ba840d041c110f040c410b140d1801d201c0c40300102171b8104203500c00d140189180d1600d2401d10014548084041e007110300000700403c4030301c000603c4cd8020b4070080c50b51420b660320ba4000b1684450280030060029400f040f04021100000595a802c4848a001600050381d81e951307007240440d210741c200f2a0180c07603003061 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 980549433 1250 980548183 980548193
    0x1e06280e01020109031b02010e03031605010b04050f060d0302120d090203010b042f04082b0305010602070603020a05090d05071517160504030506070c020a080c0d060b01030e011107 79
    0x10001000c000c0c0001e00c01c00300c0b25513000c0c0c1a440e00c1150020a0703001d0078420000c0da0b02c6582600c0c042d60024040c0c4e03078aca100fa40002e40c4807210000007034581d9030800704410018105403188a116103c00344800b0159210791082100e01250303e00282c2c21841500800d40800a120000b0102e07101d08140008410801f0f10606003540c01d2080090305c140e18050302000005444600c0c441c080c04045170602c02070044414030043d50103241c00c04840c902c2103218040060040c50304001c442c400c94081ca440740c0005132402c40686000b4080c0c040180c0004804214540c0250050100300150f81011030918040340c0100d80303002041038042c0c42079409000204400000d01d104580d02600c9890481141c1e00c00340c0340009822405003081d00418200e5040b94901407188080e100510b9000342030746d800341001100140943d050340d20a034032941c190710000600341400624041580c6010300f1580d0b00b03441689031100140105c04495051640b01c00343c48000781420720854410108190760103460b0b00c034034182 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 980550683 1250 980549433 980549447
    0x2415160501050901060531050712091a010e13080310270e071a0d060e070309170301030f02040506041d03130e2208090604030803070f08061e0628 64
    0x4811902841c003411600a0700c90110141e1f150715000e00205894880810403034019450840e04001585000090b904012200c41440945142ca01200302c0c16600d541c0404203241d403e8800042c1c609070029081c0010746014007450f40200d20f005c1282c0c0f03240d038074120304004d80081c03c4801c1c0c89200c8c034903e500e0603000c1446014a004800d00003840130905003042d581112491410500340310034003080840c1da9000541000d0090000d80d240700a103404e20400203800340058400c00c84919085801c00e204241c88041528102d9420910b0b60740c0148079502448000d01c4050661600140c48820010190f070040510000c904580001584c0c1c90320ba01d9110380500d003140c1c010000d040306034000c0c0a0724460000d520b1464042c000740141741c5000900c0c10700c10501c9031000c815081400460000140017819029621034400c036214402c0c5456080320880c0c1c070840440d002640310041801c0807e000201101d0003003180c0e4042d001e03e1820715420b843c10504003140a15074107000000f42e59140d143e90002c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 980551933 1250 980550683 980550709
    0xe011202030603150402120d0206011403160e0414060718050306040b16020304051e01030e012007050717010203061215071202070f03050324151605010509010605 71
    0x541103040d4105000080d40f58284041c4101d5154018401701c1c084d503680c0d414800c0c1c41c0e90f03110121a5450b0074100b029440c2c0c0024440d0070702c134851181c07040c100c5003004610165a0541c088403040d83c01d043c00c9613509940c0000e08242e455000d40380c500d00440c0c00c1006854000c003c00c2c0ca03041e040080300490b41c00e00d00b140781c20290181d003115048c040020300c0d00380c203140c0010300350341e0050b400091100202e155020381e070700c101e600000100e444007103000076070001e61140c1400e80e801c5c442c246a91000714280c9608903204044080001c0300c51307152408060203400818418019214065582c244c506c40d040c2c801c4019202e0350358000309000040c507008480070041c0d50080054100401d15101c0c821803980028002e1080c0b011001c3c0c0c01c0035800141c2d0484807030076400300d0074900418680c10024420b401c21655080308415189032148140e0001185050400b0000d00058000d01d0b1000b02195030b4002160310501000c3c0c0c10100303000a5400e00415208054a40c0000b40c034a180c4420042901240c00c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 980553183 1250 980551933 980551967
    0x504140d050d0e1903050714011406040c1805010e1306090e071a030604051b0c07080d0203040b0d020702030721050c060a050a031a030a05010510080f030307140d0203070e01 76
    0x540490400003130b540092007894043c10070070b032240d001d401c00a8034401100070b2811254a03116107a2560840140403e000f68001d032001c000341100140300381d5460b1402805890401d00248007041250311500401c440a880034009504c40000080445d0540e4510b4100c08505030f10f070320030300d000c135401080118002c0c00c3c44640725682c615440408011071101504842c0103603100d130000795080b5800c800d481452618071074000e1361080144105515408103020b0f03800e950040b4008028410300c0002603d081c0e40100801c1460600c0703d00c4d002000b0b6106400480e01401005000181e0541142c210b5000090005049603407040c54505642410b02c04011326219010610178403080d03c0d4840141c801444c02414005506010141486510240c2ca550a90701d4443e8400d54020000103400040c041d0300c4810034810b0301a100c1c8601c6072074484003040d194055000740f0009060510440d680914000b040c0c1c6910300d001c0011007000d040e81d000f22000c0300820032050080c0724550307220392043c844074506 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 980554433 1250 980553183 980553193
    0x70f1206180807080f04031e0c0e09101d010c090e060d0c0504090302010e0f0c011b08071b1a030601080a14010b0706020c010204090603020a08030a020607030504140d050d0e 76
    0xd030b4070403a583c018520301400205000c44c00303114a551003402c9402960300701541421002c506901c01d28284001082140c0c2d0a220b01c6002800e40c814041c1c0361300861080b80903011482c0e4071a02d00c0700900c1d421101c4020f440c40d16928603e110001c6c0700b41e10500741d5070b50760400750a0030010300c41030140c409420140074514098420001c00c480c6419041a100221400304000c2c5180c1005c80c0984040b869201c2c0d140603d81c03040480c1c1e40005007100503804280c89a169884500401012040a099001d015400300708251000604803001881c103000e00c2a1000000507159400008160300c1d10218519804000062001c04e41e00070f00a00d9000401d0032003801002000300203803400e0401845082c03d24a000708a51040103042e80650303504a404600840d2910b5980801c4000b80480b80f2099000f51000040481d40c40c00100444402d8980c40e001004243c452400817070040c000144143c4003010501002110140284000d80104181e43d603150303114421228bd0404995a90164071042c0d804 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 980555683 1250 980554433 980554481
    0x109150206010603020d0b0310020c0c0307080d050703091d01140f01120c0e150301031703130f03140c06061c210509030a03030906112a070f1206 64
    0x20020740d6070305641d1a03150241e110841e5510b8040600070030310580760326001d0342c115000c4080240d4060200b1808507000c07643e6126000040c591107503440e0040300300c3e5400100f00340311034900a40042c5000341c802d2408204440c0c1d10b42c0c211207030704041485848500300c00801042800c4101030300241080c4c003203941407040409007002900c00340701d00b2509030b01035403908040300035203020310540d4000200103825100e407810801e402d020300b80e02c2408121000098170494112100100050368480d2120403802600c1e0752480e02d41c031076a001950421420400b60b00f10a04c0101e0850002d0819400c0810042505082c04010003081c1756000d9000c141d10011005200c1c04559020a001040d20034990911714000310307404c0454242c40340011141d00b504c940c40b101070030035505612540456005007010801c007204490f8500561090320320300c0304c465105d1000102010400501884812080400c4440156441503ca8100842a0300107040900701c90070100511800e03024452603030710b450340315500d0901 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 980556933 1250 980555683 980555687
    0x412020714180403110d0e04051005010516050a0f121103090a140415120605010b030f34020a0218040c0b03150438030303150d0b15010915 61
    0xc00442c4040c20b2608100204052500441e01c044503941200300365101416650f0006d041000c2c0800300030b024900e030900007070003c1940020712050340c505a542d20b24160340216162103081c40950103817160b000c0c0702c840b1000500541103120406114140c07042c82e8510304003011b021010700810141198204003c0c40301e0517070b0340d0080c990075100e43d001c607203038804680da002c54001c1451000043c100c04451101080001030f0060740800c40348a050140010b0380c0711281e451050105888281244400401003085036035a0061548120128a0b202c804904600700d0744130307041c002e03071101000360308008051825030501220381c0441d10a503080d554203d0401c0c1c1e444034101c10140c829180802004008104458289942907407107440c01841400304440b49208150410501002001d084000c01404503960124465649030002c0c0100994159500c002c00000813402140c900c99100c503aa04401000038880744041e0700400c506080c48040013040340c005443d00c4401c1d0011240e5044200503008496 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 980558183 1250 980556933 980556949
    0x305011401060f031512030201051b0f0904023015010201050c040905040c03080703031b0e090f190501030b060120300a080a06170c0420030412020714 66
    0x243c040c070340011542c01c100910308201440c0e4100f0f5100303103541e0140b07600741641500b000d030140c41d54200c548000010400e2030070b1184616809900303c102c0610801c9050f203450340c0500910b83d095a02d000c0d03038000042d0300001c00784a1030301440d09941601c0600907540e02e0f00d16a00e1020b042800204040d0504001c9048240214803600d04030580b1400060b04101e00c034461440210380c01f080c5103032508010319000d4094111038658100d40a03582c006840c09078841c01c0400002c5002900701c0d20710742c072003c0c142c40c40150000e0424036054003045003040010928411603008602824008a0904181c1d00040c8803000400d00ca00304140c0250070b040a01001081a811500c0e05180c8103440d00d602030044c00e601c1ca400320360f02490305c1c0007245d09d48083c0c0c0c028054130f100703031050300c0204000c0c1e44803483d0208051860b07104900c207a0040c00d406100e402d1551040c0c00380d05107981c241c1c40b0003140f80003040940c1e0080f501120200b901203110f45610b501000280c01070003020440452004c0b040011031010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 980559433 1250 980558183 980558207
    0x703030f063f02031005060f1005030a1104052e261906060c02030609030a020c0402090409211101060302060f03132909030f03130c0806070801030501140106 69
    0x207000200309590200002c0d1854000c0641e014050354004204079140341d005013401ca840a0051210703803021200b0307241c140c8040000d600c00383c9501b810742c1c5510901c0d1004040e134824108030707004204000705040d540d400c01c401c01401780c20100724400c400c0903840030400486d1401c2c8024400f054201e441058000c2080308040d80100e0300302c0c589940c8038640444450f00f8103d20303002d018a000750106440d0350105910340780034001d4044980342d44035021003590343d01c07030b91100c0760058008241080e130300d03d41a0001e02d00000020404108504140c80311062086908944580040c81704001c0d1440368220340714100d005541802001030600d150003203404d07031043c1c500414916000100180c009440c3d000e94091240d0460b501030440c1a0410701d400f02c23546540e00710f000000c0030304001982d521000088600550f841d15403030303055441e0035403078800304500044126514442501d003c1b6400c1c2c0100051403080d90b80e55030700200c0b0b501d541011800c50700b0025158488030790210040c8505a0004a00108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 980560683 1250 980559433 980559509
    0x1020a02060d0b0a0e04050123061005190206090607030c120903200c011101051b07150e0106061706030c130b06030411091e040605040311030703030f06 67
    0x1e168014810b0a004100c01010b056004e403003848041000401d02011521983c41203000704507100c5040042035010300300848030448034152800081c3d40341844420540700342e0490822504180c070f100803040c8080300044018005038001c0c03040201c1403404000c5181c0010745400c003004dc490b0f50100003011035914280b15542c1c40c2d121040c41041501c42c102034016800700c1d0b00981e190850004841d51174141c0d03a646d52703000906040d000d410024040c4038940c040c00c54800d4225190808281029040d002044203450111030132004528049203809284150b50060000151032030901030b001e020340e803ca0661015840440f030800c800e40d1800680844441d00440c0c86a461703821611070700c000713041501850f5400002c04410302080100a401c200d58046c4203c42c10301c1695210303414400118500c21071050303040642000f180100e4400d9010700e8000b40240392200141c1840e01c03c9519507481011700701d002980e14401042e83e600c652240d1406090300611910304080f00c10030301250881031295800c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 980561933 1250 980560683 980560687
    0x1090b10030b22120905190b0909060f060406020c0a0603020c0d12150e15040c1b0206090901120c0902161104021e0408013204060b0901090f0609050601020a0206 71
    0x2c0034440d5000100c11070382c0c8040504107003803a01d0303c010301500b00c40c446d09000d100e51b035810b6070110085158a106503402d550307006041a81400c10800004d6001d81004d4114401000780c90300c0e500c0e00300091014140580040c003070058000184585142075a000408051041c04248010000855001644141d0b480c200c2004c0c1c2c09200302a0041200444ca00301c01d041d2404000b5100c2c00400c0c1d40342c420140c0c240d0a490301c0240314207001c01e80d84a0341707a03040041c000076030411103480001d000521301070003d80250b0804586030085422000280c012104980715810304e00100181c00c440d00001d001515810341c10903550a0449039074040b50a0005e1510240c01c1a0600d0780e125541550020081020b407810403074502c4050205039400f03801902d9295003044070038882200400c28200e4060b03098920300151130301c24250103080300da0242049641d41d4031060800c17110f40d116101d041c040c00d03c4110003c0c0c0d0720b015155040440b05a50b0000810a003881c00304085030303802240400200c3e07015240b641e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 980563183 1250 980561933 980561971
    0x1f05180a0c1707030f0518030f0307050c0d120c1e20010501090b19030215030c0d05040b1e0609180f01020c031803010513120306090e01090b10030b 65
    0x1d9400d4045105075440b420350481040300103a40b58000034410ba44507402040940c85002880407002c0100c41044031640c0204906004c0c0240c820046621802c0761400a0070034010b91180d41c28048031156000c0001d00300d031610b952400326889900c7c1c0010084c1003803019000c0c0324407424100c0c01904500e50500c01100c400d0600645800d1103650710014001c001c22a540e1110070321001400701b1041c0c40e01440e030100da02e501c428103101054050321740003841c41e11001442202624180d00003000304650140030311003184803c0f598003c880c001c520521440700b0a241019551101c0703510700c0720f0502d040d01c01c0c0f4103009041d100c4407084ca40103980402d50034002c943c042069880c1c0f07264486004840d600c0010290000600480036100500384002048144800034040600b41c0d001a0345000784a200400360000042d81c000c2080300c3d0801e542004500d2580d90002c0d90129280d0074450000c0ea5103030003801d000c2001040f4404d921400c2c060050510600b581c4400036070401c01401c00c038510020200c1c2e0303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 980564433 1250 980563183 980563187
    0x7090b091518030601081b1008150103110307080711150f09012903012306010309030e0d0c030c0e160f030605060d020a200307150f051f05180a0c 64
    0x8020a14040c08803080c81d651140c40c01e0b61108102090446c00041210b410094600380c1566400708c0110351b207000080d201d1010000b040810003900d10b062580d900340843c20701d0407403805184a0100b0b511080d846140240c0041c001c21042411405075800007810000d040040c1039543e80c0050280c1000c068564172044000d004200350144134007009502d0300d40800070091041c00200445040e0024803500d04402c0c1d10400203000d4244540341402d9640c00a10607502c2540180403660007403030940c0c0245007502c00710340103030f808c01c20039654504200e1050040c41178006140c40280168141c1200364600060085089000b44542c03030100180c01044c00340240c8a50840d902408004161507608c10048155400951000f007032540804d80c0f02e01001c1407452840354003102c02030301782d028524111460b03441452032254202e145c0802070b03a80588209000c05c51044501c00c50500c120310080107213a59400307a80104941c042449a5458000c07610280c2c82946600d03000000303c103003c130f9075112030901 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 980565683 1250 980564433 980564467
    0x20a0305070f080c0102061012020d0c06032003010602060112050c04060b12101503110d0606050c060108010c05041202010c02130605042301030803070c0501060e07090b0915 76
    0x54958850a6400300c1c00894403030064080f2a5000300729030b1411003d82c0160b844e0700c0300b02c84000d1303040c50446080110300390300522422040c0c401041030401441903590340f500540c1507004800000e0f50b03110305000f03105200810800442c01d00541c18215890310300d009541c0d050500406076085210f2445108020301041400c002b5403000304180101a15241c0d8500315070404070781006140340c800041200c00606038a03240503101740c0704a16080ca051030078190042d2130240d07a41070150b04100156242c41481c2e1107210043c090300e90f1101e03030300e20100640518102c0c06070810b42203a454001c00781e560940000844d0b04035403c0446170030400e8154001a966603d0014000e500aa170100c140015090140d001400351b0f04112010045407407122402013203c0c0003a1401e02c800030008c0e0051002c0742e583c4010399031010301460210306007801517503200d00392541540461032601000082c440810380001002020300168503c079820b040040b000205265007000038001070340c1d8001030000a6000c1441 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 980566933 1250 980565683 980565689
    0x80306010c0c0902071a0c03060a031b091e1d0a0f0c050d0c090617190203240106020705061903270c050915010210050c1e09090901021c09020a 63
    0x4011901c9445c01c0c10250b90400c040b0045c00041502e200c000b8054540e10015280510382c058003044265003155a031000c00000e405450050b445462400603d88019001e1603400142100c03850a15824210554090318008900c81900c080701e49151400b50034009521030f06c1e2504100b10341e01c3e0300524100070242c0300c100d4200c0c40d00310080400c50803e01490041110482d0f050000030002c1d00d40d5040100e48641c000d00240d24560001c1c00013aa03c140020300340c41c0824002006d443ca080c0d4141c2042003960000004410400e518a00401c01c1030303010311613007005100c01d4550501e0403040d402c0c19800c50030280c01401c10305548001d1486001c13a02e0200149009041d001003540c0a20b9040c09046550984a0030b40308400c000d0000300740c1c502201c0150341c100010f8008141203100f0350703080009001c0050101c3d070800c00034080e10307901030648042004c090f021035850342c1c1d58482a500b4860f40300d00050021129a00410240244410201c403800070394000c400001243c0b80a0f100080040406034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 980568183 1250 980566933 980566949
    0x2011e0915020c0a090b010203120a18051c03060308071515141c0c05090a18030f02060f0603030d200d150609050d02120c100207180207080306010c0c 66
    0x120030700050580001e0141d20241084039404861580e8100c0041501d9080c43c22500580040c400a180120ad80d02403e4004c0030320340c00819404014841d4007290200b071101520302d40d205100d075a24210300e185504c0c90b1100c8900d4240800c5096450f070440c1846015401483d0040c1840d4610601c448e41e489254862040324106004540e1130380c110588240300002a40725640072036400500003d0350704400c401d1030344540c6c038110311403415040205040c0000c205940e41510742103c860901000314401e1001d82c800d03101d43d40c890f10035000091a00400408941d01585000148515503800006440031805080c01c041000d031030122904058140d040316420000001241d800d9280030640c001c01c0a480720202140c229960318074040380c07038034003070701c2160340240380c410f002009030612880008944a00c04121043d80d07440c540410b21015417103904c640103801c0a2024080e0201118800084c1c0c03032084420743c200a81030312400040d00c805440e6a0601049030840720400050342c2c1d040006203550 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 980569433 1250 980568183 980568209
    0x906010608071b122a0f0804030c0b070b0a020a0c121803050706021c122318010608030a02030316140301090b1f021b060d0f0b0f0402040302011e09 65
    0x1c0c44d150241800c480e00d2400451820002d04144600c80c0c5200081020178180c4841455001c0e2152054500300c5a415070f01d045041201101044441000344014018490520740d203000d6820101c54000c1c0241460030401d004008003604180c5c40a50489810f802c040010f28101015a040d191141d0381410017561000c51b0300000b0510102003522804c42e103103a002da410aa035052910594066007049070000b041420219042c0c0907155400110150001e189800307029090070b4945154071000c4030710101c2e0011110f6100303101d907001e01800000380700c0b500045080c502006006501d81c0401442e010742c982e102e00032811007030700c50ba811030b100c1780394540e00607030b0795031034001c094003800c070910625008103013110711101d1500c3c0040e118040c100c010360107030801540088001c119120041c3c60390313600c4503040c403000c5401142c03403107980140e03000608000360460380103081c0044444142822482648107000800242c3d0b040030906002d900c030b030306400944c010b58040a8401807901c2d04998101580b03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 980570683 1250 980569433 980569487
    0x510091202010e2704110108040201120c0311030c0d11040b1c141801060509070801090f240602070b130302210303070c1a04200609130b011106090601060807 69
    0x401340b842d40601c1c080d00000f0002c901c00d00040d20524410b42d0020f0005079444c1381010300c0d143d02d074813015800c400c0341b5001c220011340c20002402900183c030800788698000034440d0800380c0ba441440c040910700c2c0801030916246c15014080390003845a00d0f000850004500f60744009142e00281c4445402c010459140c104030034003a00c014101007000c1f1282d8039202011940b481d0405820b8424000c0360390700b9103c0e030b00304010400a40f042c0b40060201c40d4955a16201c200040070108054010201503480710b6490300c0d000900c3c04c5815449441d20740010002408242d4501d20b00f00b0941c0e8043e80c1165a8042ca1401c40b60f1604044188080900022090120f01070b404850082500d01402d902ca900074403111840f0828103098900421030284d030080070014a035a201e1045a400c0d00401c407500f824a4240803c004040c1c03042c1802080e03664055019a03582c01c10641d6420350708042c01010381e0302d028840c840e0340706018015141403000c0000082c0002c2d04c0360301001c42c0000003403051352980798 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 980571933 1250 980570683 980570749
    0xc0105010906080601060903050d030c020a02151908150603040302150c070606060825140c0f0d0903080f03100b1303060e030a080c160b09070510091202010e 69
    0x2c0c0380d0140507064000c00000090301845030180b50b090b2a0030001821451400d94015001060329112400640c025100c00307402603039622254148001558946644e02d03414002500c41d1100c041d566002401042410310400424403240d961320503909035280d0b9640e464608040e490100904031607240c0605070400c2280c612200720240592030700c20b400a0200503241c0300d080d22944000c56103c400c00c0034454200240070a1503001f0290b2002500381503164840c0c2e544101155403021140c00007070b6104607651101c0a508200c142c00d000600d15054040a01755030744c50500b4410001e40e0002140d010020812034120418941c00426400c550942d465501c1001005014000d01c025a45a881c1004681e141c03c40032046a28400c000c1e0b075038450507074452031944495081240803028842c03440c030000d0300103228501480e005540f00310003400e440303180004100c0c03501100c07010b44007000501a020400300260002083e049a82400c040c0000032003440800d42d04113142d00d0500000003942500d1007085 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 980573183 1250 980571933 980571941
    0xa0803040617070c150b040e150f04020d03050f16030804030327030305180106030f050f16060c050c090705070c1211060d060e04080c061b041202060c01050109 70
    0x240032925210b2211000414010103424110781c142c0102c0c8483c0f0300f40d00000c0d40c0d24148810310382141e80000d00c24840e0300104088a442c0401b000f0650700204440030701c0c110b50f00111781d000005085d00c0e4182c0c5443e5020410030301c00000c000b028424042800c0c60b80b9160715040c0c4850780f80c5507180d2008541c050500a00000040c0d600750040303468202d110304141111320a8250303a40f240850825040b000d550100c0060400400c50070010b0042080c4401424080c090440113500940e098000441c40742851814110018507110700790f444807819010045d020502141121003c0c00c10342c010f4106814031a0400300320000c1c141d44030000c10104880150420054542c9600808501d0140f83d01d42106460840360008042d00b07509611800450fa45031180080900311107810f170115040e5660140305a9040e0296421240f581d00450741c640f00802c10414a50f0080000413044041800d010304c80c85644141d004458203808001c0f40442503440342000ca032540e01e0794034002c000960b90b48604d04c00130 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 980574433 1250 980573183 980573189
    0x131b03140c100c02040f0f0507021c0e120c030604050601150e0a0e040c080a03170f1b0c070f080120180609040609021c0c09060225050a080304 63
    0x90014442020101500054110654502030b12002c00301800039402e841840260300102c4c0e0064495165140b81d41c0705000d07071400650104400304003410500c0000c1d050a01d180c6a540c00480000040c8900c5588144040828442912070b1580e038903400083c541070800304014150180305003000e000030010700203000c41c1242c103885010000700100d890100c4580811003206030b0301070250b1200780b008101e041a0a0b070020700c21180c42d030074550f46401c5581401441d40c81034001c90340c3c41c05080c1030800c1c9a1441684621544040c00d62480c010768a8072545c1a180d5040e45005d1010441030b0040341d082007214082d14501c0c0307202d00196510302c480d03030180c00c7d00128119074244800103807030244e00050541e4401c21008030490341c09848403042c4262600241c6246600980351480002c01d01c81a100800e03420040d030620f00c00340d1824400400030741f4110000782c42040f04c00384003006455808140021415100f00098142088040c2070501d102d40ca90002071303000c50503410000306890000002d00071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 980575539 1106 980574433 980574443
    0x90717181f0203060a0504050432010204090e07060c05190203120c1b0603070504052e0908070f05010e130f2d020a0f08131b03 56
    0x2034400c1031850380381182d0000900199085c4044030f0700142009507424001400c2030340d9030041d4101c2c1203054440303002c0c00b410304000c0c00c0401c0b559030300020041e00096441300d4455060340014004107101c1c0c0014032441a00040c1a4001c60100c0b240a03080005092808540520100c402015420482e4107014043c2214507504184020740920300301038000307203645000c66801c103038408800165907101e544180208181564490222400d454007500c555000510101e0307240c06850340088980740800018040201240d030101190381203485250844a22a9450070b048103015403a010311800a05001100030080c14850100156200e200300300003030b60840c407050781d41203d80e0380707403840311081c001c0040c01a44104078511000000e10b0510445c5070542c502c0d40038101c2140e44405070117000140b80021588040c4444074804d640c0c003c0043e030911589c40010030a160076500080b16 = true := by decide +kernel

theorem cover : BRFrame.Cov 980395683 980575539 := by
  have h0 := BRFrame.cov_init 980395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 980395683 ≤ n) (h2 : n < 980575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
