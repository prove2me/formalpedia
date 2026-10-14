-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0092
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:47:36.556973+00:00
-- url     : https://prove2.me/submissions/94add03d-4772-4f0d-9c49-1aeb6ce686d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 16366913 ≤ n < 16546769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 16368163 1250 16366913 16366921
    0x30b0a05190302030a080d06080316060b060c0d020615010e01141608030106080108010b0d030509012a050109020a06020601050d12020c04051303030b010206060105071509061811030a0b 81
    0x207005442010100c0d8444000e6161250007181c10009061802e503500940040c0d84203c51520384071726030003044c014014604040c440d00030000c2c05585c1c07440140019459810643c81580c0d1081290b95a510b2041211130043c0510b8019441d0345088403171410000b42803050300e5603540a62000d00c201401691001c00d28001c0d202d1148207500310311f40c00910f0202c00490440000e001c3c0b00114082c060a8985031101d62406202d1070075502003210441c01034101000c10740c00281c000741078a254041c2400d04c400c011510342584c1640d81d90084c840804054810702d07001c20f005042d440404070900980b000c205c0146c803a40145da80755820320404c0c0d0888016030507200031482c0c0c141c820300385080380d2068072250818a0009006d60f5403c0da0380004604c13541c45140105600b40c403829109100a0014050901e00080041c100d402070040c003504802203040d6046c40b10341076610141c03c056014171b080003010781407032400e2400c0ca1403074011030740d00c5d020f20015059481d00140703940d41280d0240300001c06a41d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 16369413 1250 16368163 16368169
    0x70b03100b07060e030a0c050d050f03060405060d060618050901060302210703060c050901021b0a0614040807091401140904200d0501020d20091c0c031b06030b0a05 72
    0x4441d8409481141d134545181010300410320050a100f402e40d43c0b500305804282c00d10ba4140103d088082d410310104010f41c10400f142c0c141503a0b4824400c03140000c45540c0c400c080344040c0d010310741c010002841c003c0003103100c0140700c41039044402c24090400c80e0b5a100d003409801c807019404003030340c03200c80495489900302d41c2d40e0b01c0d641c00b680c0300c405a913442560707955140d050b600811900c601040010449d480310356810019021070041598120400c1a8200045040b00d040c0b80100f00410021212a190000c03190044400407c104012030710300c03941d0386050000915000f00c05982c10380c400320000541c0b91307054140030003011009182e08502d80ba20f5441d6070f04100101295030440550a4020390184e0b15100c1000190f0701500026954080b507190ba0000c13124100c45400f04000e0303100d4001c50070203014050728070860082c0d4034040c000b9011302020007440355164000380020045140441040340700c1010051b968481d1400ca130006454260170b40c240d400580701d80c0d230401c04100d0100642e00d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 16370663 1250 16369413 16369417
    0x309010f1a0d030c06050a0507080c12010605030a02220503160e0a0f0b130b040507020a050a0204020a090b0a0c060c0302040302010c1106090409030206040b10060f030e0c040204031202070b03100b 86
    0x6101341003000d4410465910001070710030403542100322a0b039603000c01c105207410062291340b02c10b075081d8562030a00d641001c42c0c0d802c0f0042c0100300c2040404000100b14010b2541103e5401141d01c8001d80741500342c00200040c44854081c1500034090404100482c00c0e280d02c82c84290b80c0c104841c2501a6103403030000340101041c034030082c141d94032100c1d4030b41291112402002d815680d01c6003c035000c4010300c1031000381d4002034603910440d0f00070600c0302c01003200403070f1045c9080c1d8100c801580d2400a400d00319250001078014035543c0c10000340400c0181d400280d202440d40c1b04400504c60404902c20580c200c0c01355200c0640403840b50b004100c0080c030210b07000345045600503c0c9606116020002c281210010501280036034000020b000c1400b030b1010089500c04d4100f102010b401e810140001c00d0032800c1c154000a140e198004c2c031120010a2080184207400a481151240d03035901305009184040e0300c0c15002342c0100d07800420690000000c8038480c0e031400c84c000900520b0118007407100d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 16371913 1250 16370663 16370689
    0xc0804090c02070510050a0815031504020d020901080d0206010803040b07020f180106090503010e0606060909071103070b01030317010b0f07020316030b010f0602061306090201020f120309010f1a 85
    0x103004051004c0780643e43c240c11004070070754564401c1d890b0801c000003d002984041c12040c1483e801030350b40c0040c0e9400044200012600c0458418103495510104004e04c00d654402540842240f0001c103200c0d00c000f60301d20413220700390700300c88181c2d0740c2c1e0308115247d00c194010a902548100212800750900880403c1011006060100d1f22220042401c00395030780bc0e000100004c5449400f0850b900c1e09010300703005449400080d00b40d6062882c00212203120380340c9814003030150000083c1016009111803004d1b60030070b1099956a080c603262040d00c2a900f40400c80128010404200503030003042c0019058a509a403514030b4810b10240c3e029042d00160f8089038184200440100b100c1091101e0f40003d40c4541521001075050140c10b4014045541002c1e0840d4090300800c040000c1c503030a02030703886402240c00502d000b400c0c00103c0c00c000903040780c104036201d5515408840241900214441c0c4d20850081015540345c007401d005075a4404481c003544c0c0e00501c60b02e6244c0c40c040c0040841 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 16373163 1250 16371913 16371917
    0x83105010c081b030405010210020f03070c050a05010e0102090a080105040b010303110705040905010207031b08090906040902060a020709060602070e04060e0a0507090510050a050306070305041e05060103050c010c0804090c 97
    0x20000f42081c810344881c40000d420015130000328040016580402c441d400003400c0010650400b000c40c03110910900004044804010750b44071400d06004d01030143e503541c0e64000b00280303c030144150901d03020354001030489000c0d0382c040500244100043c401c940c002c95026040f60700692860302c040720701c0d40004503003110747c0c0560380000a01c0ea0722071103006501e612a0002685809680c00c02401c2c80c240e6400e04076207031507110031440010f001d4070101c843c02c004c00c0b580300d80c00740c4490f00850010305c007128000f9044000000e0f01078440d50002a03e80c22a50013001c10300c546602c81c04200c1c5c0b03510851141c80e2641c65041d000c035000a0107504804144115501259900303907988c0c079200d01e03200450340003101c007590380c40c10312851803103080c0e6074809040c090380e00740c0c0c003185880c0c0802e645038070041058082540c3c80000c00c0822881e101150034034041c04c03021000c040b02504025031175030b10a20040341d161049448400f1039501807103442d4000c54010304002d003054a4123a10070040c1c0102094081 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 16374413 1250 16373163 16373167
    0x402010e120102040f0806092515050405130e0c1212160803040305070506060901060f180512010c02010b09040b01061d060307090501030c0c051213050303030103083105010c08 77
    0x50a407800c440e41c20001c001b00130042009042203221117080101000900c241041d0450050018050076100702c005c80d144103c0308181030b41c802c40c044460f806a504095401114680c1030294810903410141045040d0016921100301c19000c0190740c2101a4010400d50401d54042598011441c003801c041940314103031600818060341c4074185c41d40700700e508802140000c82c0741c03004d110b0100200ca40c00308080d1400000b81d414070300090b1002958041b42c604012211600340da17207550f064940e20040c14068012809200061191400390a4990802c4010342c80c104103800c41e444c00c00c400754050781d0003641c094480c1e400c0c108201c8020910117240381e10b10348006000519900e07041d00440c442d495680d42c540d01d03942040c1c0010180d414007039280d0104110f04814801140c00480c210310b0007500790007107036903a03010b203200050200300c298006a45400301100003c140700ba2030000308030011500f43c1ca281c008440c113010290081c44100c00c40034182c4804c0041c0010750086400c41c81d102d00506210b8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 16375663 1250 16374413 16374419
    0x20d0309110a03140706110613030315091b02011a0603101701090201080601111213080a0803090d0816030203070e030604110a0501090b03060405060f0306040b19050402010e12010204 80
    0x504400c070b15500895042c0114401081010410f100480c0913240c1850b0907440da1071080760140d030700c86002d40421001080c1005100416000307502c200039084002d46000103551780c4020301c81c002e049001c104000403200d960301075411481071040703076010841a41c003001e031050b10300d0034444603400003400409604081c02c070100d45808041e90f0070341c26414450001c50b03102c0c0c80b840010700303007580648001e0501030f1041440c610940003164460346041d1890300c4585803000b403890504540620761000c003090203200314440500400c07000451180940d0400c540303215081b02c2e022524294115081e0800c0b00890308410210b0f071080e001560402c29503c0c040010401e0003002030300380101520211034240000042e4852400c0c43d44450000b8007007400e080c4da0b80b9140c007407060560b02c001000144616a0f60001516640e211501d000202c4000380449440b0300c2c10b40b070140c1010b807064402408441201030000341002443c040c4030320555040c3e40d030a002c4440c2505005004558200d0190300303540911001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 16376913 1250 16375663 16375669
    0xc02010b090a0b0406050117040605060f1011070b09010c0b041b0b09090109020c07050d0807050f060a0b0402040303050d02070614090307031404030f080f04030516140d0201020d030911 81
    0x5a0050340c040314006501c3d03400d0f03000c01c003c454030ba1748480d06000250790150409030300f0002c0c89a00a400c5075010845d60f0350140001e0380f8640301c2046030303804050b40c0b0035a5111540709005420225152049540d80d54690803541150b00402c079606000a511201560000c1d080c0d514843d08180b05880e04ca00e500c44d1808a004031180c6500a804d41d01e030f001c10b54a240d460542c030054010170b003644046240044803035402d40c4420041c0102c2c2e00850640100e1360400011404072000d0700d800000b0341c1c000d90f105a50250300c8100986d017000440e801d20004e011286000c2c4222401c5980c180c0381c80385082c04900d171003006508180b10649000780c0d10805542c0050380f507014107116038a00d2000d903940d1351140ca8054100c2c0100c80c10420340803014007060000603070809100112a8000d00ea190319031081c0300060304a41308641004209000301d42c000d41c2000c4090080c0001ea4110740301a00c54032495009001c101340301020080d0040c1e100c0104061503e00961019807618001c44841b24004412004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 16378163 1250 16376913 16376929
    0x5030702061804020d14060103050f060f0303090402030a020a14090603040b22060b040f05010302090105010507022b030e04020c1b010c0c0e01030308130803010e070c020301050f010f0906050102100c02010b 90
    0x110b03e442584414024145148500001d46e00101c2400d04100c3c40c20502d41412312f05500905480c080c20f00c1e201c0c2da07013096a04009a94010300f006009669a10300184000d000c1d4011844460105000a01100380c0703507282c80039070700068801351100d419643c558881710031641b8007a048451010000c1141005503415048040c0c64038082c1c1004545103a010090204440d0a20100c07903e00385000c00600069840e6098141110400d00e40240c50320b0081c000104000004080410000c100a2415044201400e840c841103806071300d480020021030010300c41640300781072a00740e041e08491041d110300603900c103040000d0304040c03612800c1c900c442d650b0030b8000401504001e0900100310010420150301c552910f40c030003801707007601d000181c1e01d541d8078541c1c0c0010b014000c50203c1410020310494480c204a162903500240203000e80e003041241c1590000c030a00640c40781441027600031070644964092030381181c1c0c042e80104052003414a501004100c81c1000d101155210002c480940d914080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 16379413 1250 16378163 16378177
    0x6120c0f01111504050d02010902011205070201020f0301141e06030a0c1412010806090a030203030f0402150d050412020304080a1e14030c0c0405060603010909060f0c0203070309120503070206180402 87
    0x2010103c2828903040442c50042c1881c80d080441e8100140390700180d0b403101d4411790050544002103042d0700c0d4160180c2c00ba009615461011800200001940300a00d40c0185d00181066480090340010351506021051101d60101d802c283c0c00c0022901408040c0d00c80c510800755481d00003002c003c140711100e2168400915411310f100d02000500c90858180400c079084200f00d0010a98180e90380d1f0061b450740401070043e1050001100014159141c0c040138422043d14048025600c444004a1800404c3c0c15501548e10840540e840031807207000208540a80300c014008008942241da68060004010001d0318003459050011070300040300d40807061000d08914010315116010012510f1401d0340c2e00f00c030a0301c07c0d400e12051101a884103411641510341c418004101c0d81102e04100c0041c0c926000500c40d55484c01c42050a0030354040050421036102e0343d125083c881c0d80d0402000300c281220000b60135a0410410720b40103103440310040c01444811203002c1229286480004e00b01c0c0c111030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 16380663 1250 16379413 16379443
    0x204060503030f0405010e09060a06080a02040504060306020a1b050c10020c030a03021f050103030905100309050f06010f050d0506060103020a09170601060f020d080415020706090c0503010506120c0f0111 89
    0x100b0107000560304110340d091050020388a101d0145272010000c1c04001880c880c076401d10001c1801301d224403005404440103084060410b1011981e0780c54400000e41c03000c8000000500070900c25541e8080045d044115035030404024102c03910b0140411a0707a8500e4220724055118000700a8840d031400d2001c80c218a001e134000c0c0c07180380c5c041580f08000d043e04c82c084403000d0b0b10f000010300001780c00003c100c00f9954141c03112020b480034900d0907001807410820140091140c11100c0800c40700c0040d4480c10b907146040c0b800c009690307a5040c4401c8400c00000200650070410008070503500c20380c05000440d005280c03c41c0815030354950310302c8070280e80018a1a0f90058030050040315004411110300b4169031004128402815000500960014100418060801c3e025440061054041d40c818a41200003001100454680190f000d40d0313511445009500306000504a0729000d680700c4440704c00354021707010300300c00001002820081032101c01c3c18852406410340c0d80038010040c00f41070221071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 16381913 1250 16380663 16380667
    0x160c1214040923070c031710090218040f0204080604060207020120150c1908190c0302091003050c070b04020307030b040501020a02010e0d021005090705091609140603040f0204060503030f 82
    0xf030740480d154180c00030000780500580c51940e000281c0d00c035000c18504201c0c1c4c890615107460704081000200d10680c0403c0c1318a0003c02c4040b62825440301c1084100307400c480400c8001071558500c420b9000d18407444203640c1103072000401290440d00200f540c41d10500d0000303991140c1c0000111064010559800d00d0381c80440740c1c1c040310001d01c0026411401c1c0d0340d41d0310b0400300004481c00400b400c003400b00c01006502c9010038007030a40d8a801400441000c0c0d414084030030b080100030000c0d00030101c820310074421286120f40170350280c811240540c0384041800e2030809961103c4401e054003600482e01845003000000105142c2e502d20360103203114400169440ca80e0300c900a0940d41d1003154500f0540120401e490059000a000c510421141e40045041c0c0e07203222160f418810a9800340d5017180b404810800f00d07403500e0188030360108079501c0c0d03415240d446040300402c1d104010300140e0028420804100414800c40040ca0090300c010400304541c2d0311400803900b1504134508844a02c480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 16383163 1250 16381913 16381961
    0x11802090409022706010c0c290a03091b0b030606070507030602032415180a030210020601150306080d050c0a06140a0c0203030c090609120706020303160c12140409 72
    0x110340740c04d0707085402440c06d014802129103a640c0c290050303200384000c40150301702e6040381038603036034811640d200c01054050f00c0d1180600d01402078600c401085075410109660142440505c4030100b003a04d054011190650b5140706c24465690311070103007550f0134802c202e000400980c003030008521843c00c628111410061041c0d803002d1086409040622452a0b07110b041200c140300000d54441b000c18802c2280020084c1012540c601041c3c2c0019411120719817420320526000500c56048035800d400c60080d1070703100182201100c0e03450158113030307680021138603068052184000d4491040d9920503034040703098540d101012681c1d0182140c1d594201d03802001000d6403e072103405500c007c2c43c0040c0d07145141c03480d104c403000d10402170402e01c162800f01e502040c5440311a013510160559004542c00da903113400c000383d0b698004843d40c000005003c003012030380c2ca114401030306c0d030346502c8a0304200f030616aa0041d0352a543c804603013000c50783d043c00700040c46d42413401880801c050242003400c0c00380d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 16384413 1250 16383163 16383229
    0x110103060819110118030803041205070c05010c0309080d11010c020c0904060e0313060201090b10050105030610030b0a09020408010c020105010f0308031005040e06090105090601180209040902 84
    0x4801d60104500b40c0000e642000d400210b841151009070303101c04501d40320b01118005903400400c2d080c501d406003107000008010000707000c00450045000c1d603890841b00440f41d0b02143d162090310002031001030303d24410440c1e540643c40200586200e82000340103a911000c0c03551034101c2545c0400000307584207201800b001300c00c5c891a240f131a030500c0a00b8008510b90080341c1e4411010300018030a036a1803031064550380c010f109442113016254800c400d61544d601009010700004801500c2041405000c117031380c016800c20a200306c0341c06031550350440d07035a101000300107007401c075400c0d041c151a032040701115960141e242c80a04610580181c5072800c00c000700d070854221810301015a2b01d07240050003461521007964007160750089003555241d40342c01d0100c003d034605520030b03034009051480b4209880004245141700b00d15090082007039654001c501070742d488080c8a05220119100180c0c0c90b1021030343c006140f14039014002003125292603000c00c3c0b000d50040c040820480030000d4080b4400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 16385663 1250 16384413 16384421
    0xb04061e020f090d08120103050303010303110102070209060f0d140312090606061c0f05010b0309061006050307030b01020705090906070f020303010f05010e01020a02041a0a05011806030e0703050a110103 89
    0x210002141090b03508a5140124412090958031a4494403107800410100300b045076410b4a00914001e01941d681ca0003a40e00d8001b80001c03808240b1000840301e00200510942e8020340e00102952100d031180e07802d0ac1142851f60942d07a03041400c48505401069030b0300c0300303041b4241c400c200440c1c2d20404c0c51b1840141039401b60001000342c102d003090004542d507520503191911085240d507010004c80c0d08850004010584107040d03040d0a0100010304038010201035403051010f10140c844070b83c0c4043c9240b80032941400342d0300118009202041d0f0039407085c0d201403440d07501801110401900c0ea0f0008081c000125403060170342e4820740403c6070381580642aa281c00340036000440c1154100301070884451554000d06040245514000005a10030808075040940250041284032242803410340140800c01095024103030078400056503521036100d42d0180c1280700202004d4a003440c1048002d000b81402c00240c1d03110f08807002c00418020f2100c080400e114000c80740e05001018001b400391 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 16386913 1250 16385663 16385711
    0x15061323060c070509130605070201050403031a100302090a090f09030e01080c030403050a03060b03040c03020a050105040f0308030405030403050d08070f08010806040b100b0a12150308040902090d0b0406 89
    0x81c05050181c0302e00c00a000034810165407007118000d141395030719664201d4080f1282e5000e80304d0740c100010b100c4225010b502c01406140030b6a001d001c100700c01e242100d2690300e0b07490703c2c0d500b1040781510b0541480c0301e40d0241403424001000600201d50364a04401910460352040145a0351507500908164100c0c0564250000a00380348810f41340944000c0c00f5800020809030a02800060442003e80319a201c24081e1401510043c0c490a042c1003401d401170349800201d000740045400410150301440580e4101d48000003100c590be402d513a5800101e42020717201312203d00c02440003000040e014050380041c0c05042da9203416a00c0d10290041203c41074030501c1c0184000c2e80e0050040781c4020030240c1d4055040b81c62000b103607c5210420b8107506c0280d01c041000b050108410312100da000507180768038401c0800500040c1c0a200b03009030312442c5448010080313030f8200400c12503075003690080c285000b0300805445441c7c0c407a80785c2203043c040c202d40403503e40d42c1d03d074544194130320a0140d400c0c40c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 16388163 1250 16386913 16386919
    0x40617010504180609060b0a0806180610050103020705030706060b190c02010507060b0a0b03070c11100c02010f05070c0905010503010e0610170f0706031e090302030315061323 77
    0x146001d4800001083e50b00104042c0c4056140c0d4641c1052100039003059014a074060302d883d80880c1d0f41c40b58a40c88007000c0d0f039001008508210780c660030400014086025040503502102642d203400010340080d03201907000c9030540424062200400c5c5a8411080100065210705541344c4181d54810000c2000c1101c0b103060108004401c00980da2100c00c3c0c0d21607550180d0001203500d5600d00048500c8200d40c02610350710000000c0100159002047d10400382c880d13407200340c0c0405180100190100300546440020300d0f103c034a000950b11038a010504c02ca003071300701646054070649030001500b103030350080b00c1c0c01a1240b0040201d400e09200302080000e154014000034103107105560407040c03152191204650750101042140d1200780b1520602601ca182103c8906541d80704c003401a104407010041c180701d00c00324a00c01b00c0000e01404559540c50360145185940301075596000c01000d8003041c0d008002803110a251503a0000c490001d0306086440e023120070708030102050942001c2141c140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 16389413 1250 16388163 16388171
    0x50601120e0a0b04080903010903020319090302030d080c1210060e0f130b010201020c060f0703140103030c0314070614090d030204050906150f18010210022107110102040617010504 79
    0x4410021440d45020b42c0c0c0074041c00c030591105e0510b00041c0c0140241c95a040d440c2c2281801090b0b000402000b0440b450400e01028421241003034603500c03030341e11001e909904036840316200c251140c01c10542c0300a40a116034245045262006003410040764048401c642140e8140711854000800c2c0030000c0e400ca03060b4001060600116a482402d001d19140d050307100c1c00d4000300ca81c003e4040d208502b0340c2600721042032402c0b10301e0000840080e80c420000c0b078074004a21403505d5200072028141d94050b103c1541c9003883d95000c9841440f41e101d4100e07030000c18400c3e000021a00d025944000000b40745081017070401110341401c060304552060180343c4100b00401007911001c4203160b01079821100d14601c18211000081607203d07007a04010702c90000628003021064400c401d41c9001000e0b402c0b07407141c00f004a0500300321310565494500b001d46044542860100700c500c0654081d80c103140004000c0c0ca0f002c219401e9030015001075010442041581c0780c01c10075402c0640c010001114140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 16390663 1250 16389413 16389431
    0x417101416030c1101090308150604050102060403050706090f0302060a0516090504020c03071403030106090501020109020901030b04110402040f0503190b0714040302030a030905030f010e07050d0c150305060112 92
    0x10391148102a8410a143c1c50b00b608a454901030a070700d0251200403802440703049418507000305446e0080754035100c0e058005040d03400e2801c20605581c02c7d030300180c000740026145c0b920b00395910707001000111045030315082c0c02d400040360401041285842500106520304041244078240d41004003154400019040d200d00c403258800500c0301280d41c25680103a03142048523000d070035031290840161240301074580f07030b82860130004001c504076411660b42c1d010391600e0348012400d0320303201c076000f95001900d44010300c00314409c0004250424440c100e110070024660010a003aa00294800c402c40c004201c020052401c0500850041090361500304011640c0c9a41d01070707400c00041c10351000c01007003603003c060b44407030441154080d58009088944000c00c5240040100600f030288900a000e003030120625448140070340381c94041200060202c5a0519040c000b04500010003620900004400015031080141c200c042558280e640801c00349009400036090700ca100103400751807441d010484c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 16391913 1250 16390663 16390681
    0xf0606040b0c030c07080312090111030f06010c200301060503031201060806010c050106030804050a050d21050f030f01030302120309060105010e060c1005070306080c01050f030402040204171014 85
    0x210180d40d0200c11041d10340a0030b1200501d14069080c0d1401c0a220308400895800d90000103040801d10740980011203580f001e41482c2070b194140100c000c800c07024808144800718603543e00368070150626140c3d02031b04113500c91044c80c2862082d1f5001600c69840c0c0000710382800e02440003e41000e400443c5402c03180b00038200781b05030510a0b20100002c400114803182e2042c1e402c0c10712150004001d116007602da04103030310f440d40203102c1c03280310b503d00040c00140c40c1083c04400c0d80080c2c206101c1c400380f240b2001191036604e020a4813008201d020042e04881d210a0805540220700503c00c2001a60451a01070716003020b10845641098051081200d05800080c280c2e0550b00700786040c5c82e40d10100004111b9070f0180118186040c041c46420a000c180d040d8851407040805617014441e0036030740c5c01d0840e02c802008141a00282c2c0400c0000e545414820065401610240c0010318107996403240c2c2c1c20301d0710070b40c54041c1c440e0401a60510303085042d02038000030020a8140503400d04041c004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 16393163 1250 16391913 16391917
    0x703030c020d0311031207030f09020f040504060605040603051e0102030c03180c0402041d0703020a051e070503030903040303080702010515130e06010b0a090b0a17180a06140f0606 79
    0x402481100541c102da01018403542c5200c850006600c1141d48580e42d00c201d0700c8460b90704950b40070010f40ba000308201100380c1806110265078018107090724440307001d01440041c1000030810b45800da1034010008040d1141c0c403403c00218003440240175201600ca4a4014051042000403600c1e801030040c070400c8280001103a801421914281c103444108440a0381800e000c030184981c0719102280000e40b06801d41c51015079161221050004bd0350703403080c03d400300e00400d2130100002d10b060191410000105050390701c0c4046840d22642445583d9540c075103144c0c422034001c0344582010500708201074002014a4204a02c0e000a001a28011020744c4a500313a40c040300d0b2140043c0565614900c0b80f650100d6002d41044040d2031240d07840e12118201d03540030300c5a0328002070551400140c0328070b115003039901d22a0280d44418690040c000d400c0c01009000c1d01c1403a811300700d0b00109024400400c28120140d100c3e03200802da100c644128800e0b0000002c041e00c1350000701c48100203e56543c001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 16394413 1250 16393163 16393187
    0x109050d0311010c1706030706020318030c0406090b100516080906090d12090603021c0203060303040b07030e0a050f090a15050a12051c0f03090f02030102210108070303 74
    0x20a98414292030504079510204981c0321080765180540000f086035020360301040c0285e121020b50640d4589030149542c901580c42048011b070403e0209241c058520b03d41c0114404008049560b070b488000300060898140d81d12030f00b0351503510504090304c0d0802d50b6000d00300c480d0a0a041c1d0600786006008210860001c3d030042c5407800000300d44140e079a0b03a40599028003005000c0c44220b1a09150082c94410041c01020102d00340b40700005c2c1c964400e00880301c0600d1803032814500c0c00d1a02d40504041c0d0000760409038503000c10300c4046030480008014205041c000e0b035424551102c00024040240700c960080d40c05002241e8086409807102080b464001a54820010f062603010900781505a140c0c3c0195522841c241000901230300360031440060140a681620038088503201107005200c01c1c0c580c8100455402c0410018450181d03022802c035500450003103008c0b040603070009003240e00c03180b041c1184403100c0390713040511044500024050b00c1c1380c0000701204ea05589018100d821401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 16395663 1250 16394413 16394419
    0x11d03040603050f0c090904031403040f051e0307110a030213060e070504060f0f050405030a03020c0f03060601080103030e06040b030a0504060c020304080c06071b0e041b0e010b030405010b090901090204050a0209010905 96
    0x1102040806101c1c1c034ac418620400000001d450381800c1c5003604c507003800070109a038a4414028403c2c040d5100d4040810400070200c000d5103496180d0b614106043c2445e0707091035124000c4800000540c6408290140d83e003c0000e0000301103081081460004102174469410400c0c28001844001e4004c100121b01210702e040c4a10072a203103640449803403140303800558044c014074401c1010160000b50384900c038001103d011654241001c00c0c107031380c0e01d411207006001500d80001080400e00035028498942405465a4605611990503c0113a401a1441c29050b0f940e0402c0200340411445030260800083c03001d989840e1130204282d60380c0c802e180f00303036103c3c40c03002a615040021281c00011080c061009440e961340d0340704180c01c9118000c440c1610004154600e021010f00c84240c1e0344140c0d402c1c07114012040e4200304c8105180e41006008071039541d82c0b08101511a80d5204040e44131b54406400803583d016944184400d8410241c000c03d0080d005100c1203001e03a03000084041911420703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 16396913 1250 16395663 16395679
    0x702090a020c100f0b01080f0f0f070212120f13030509040f0603050f1e010c05030112050102070c18060b030906061203070b0a06090c051207050c011d03040603050f0c09 74
    0x1162641407114202210403c50700e48400d5039044107458000c0c0081c00c0c3d0980f42c420050344c1c0c2803040c038514102142d50010240881000500d80b6400380000c070382040d400d104490100702410340b08541980145035013041c80d4030040400003461076440d440d40d030041904d00c101141d152540d074050024001c0174241c900c150b84a103948005000035520240086030094102c8601d80c4100b0700309511001040700c450602c072210801c605001405004181c103811b0303d0f035201d500d103070b21b0a4884069500d101e84100c640c0d54082260b400418401024000505035480200f60b0780c001c8a12400116021503100340882c1d00300340100710032142c0109003260b0004040daa02006c140104d103103d411032041400090801d080b140078401190595404041500d0f4030200801c40c80c4105401940c080c012034202c00c1c0ca4503c1103000580c0d90344108040c00311040f001c000443c034603848484804001e2051203109210350710208040000c03541c1070003400e401c2075980440d02d4040c140f8020900e058450103d2490117400c00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 16398163 1250 16396913 16396927
    0xa05060105090301060e250801050103180f0c060e0409030212030702030c0706020106090b090c0a0e03030405151c0b0d0b1b0301030503091008010b0d0908160507030b0106050702090a02 81
    0x10760111000785400070000c00240f5100c89504e103402800fa00c4250f5001d050121108a000c007040d19a162041642c540446903031a20004501800600006101810501085400184243d0b06a03030295210301c3d2421403030390030700c08010025140300412074411410103c40e0000f10b03401203401f1040000b402107455684d528140c06074a1445101801003043c86041c2000030400d5040d031000065480040302070100100c4c1c070007000007841c0c090390070303801a9004002000025000361000d60688001130180d80c00c2c180d480300000c95490340060b540070018000030720805d440a80c4c0c440401f40c0215140c04106540426010510444030f41c0c0d07001b0540c1e40032001103040d43c18010700d8144400a08540d0f1a901d41c3c482c0340c0307940c50390400c140150050040d040d025803c84c1c09406d525060710070184c9c91909000d0004550303805000c0340581074580c190104841c0000d140700329000e09600d802180181180c80c610302c0e1850513200140d1100c0c0410074144001801a5502030610303402000300d03903000d83c440d04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 16399413 1250 16398163 16398167
    0x4020f1602040e0f0a120801030c0620060a0915020408070b0304050703020901061e0905010503160e0d03031e0209030a02010302070201030e100f0b010507050a03050307120204030c0f17060a050601 86
    0x1081c0084a26104203290003a104800169124582e4803480c48010011740d80300341038529407c00e0000074035503030b007441083c40702d948580c1400540c1101190104440b00002040a003000001e542000146031504d00d03280a0103c820820201072960100c2186032030310b86511282c0b9028640204104504008042400e0002c100500409075400030540742c080d50b0342700e0000e06030810b00d5040140014880554030880c1340118690401c80b001a12010724517500c030140c0e40c6881d82c2560b096400d1140503601150340392211001100814401d0310001111003100805100100340a40403480c154010424854913031404241d610b1000e50a00300541c54034942e20051340a030440e0318170b121940c0308006100b030200b01c40e80c1103820047d41003401003140c6407050004541901c12190060f0455000807002c0000a224030015a88085c031403030920111083c050290050703901a510954549000340401d01c0b03840e02d00142070005160002500c568244144000383d02c98a004201000c40396a803070000303503507034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 16400663 1250 16399413 16399421
    0x6090305040b030a0501150e0d14070306050108010b0102120f04050d021201050901050414011404170f0f04060e01030b1309060f0c050c060105180a150302040906050a0b04020f160204 80
    0x410019010b0307440c2d141144900004040901c201c45c14a0761000300c0d01c04040c0a6142c0340c0c410f0b4005040041c2d45070344c03901d40e24003014681c8104881813003070315000408284a481001e029128a10001c00d10360640ca000914040d50011440f0700e41e40101f11400d0040d03401030446040720410780e140d4280310080d000044201074145d107288000d5007001c080081e8400c065000e24402c078450b0001101e40020003100a08890318680440c1c0c00b080c8200200300800d96008490408100e40c446003803801c4403001e4882126023048841403030500c030109081c4102c5810283c0212500001c1c80e0800a001d00d400001319509940a01c1081c85ca50720414801400030307075005140b081c10b94040c1030100000c03480000b819541b2410b40388049000d140d0000c03034030b480c4c030000c1e102c032802825503000e42c80c4d01e828684000070041d82a2100c44200280c00010044e03c0328001c12090f80e0150300006214580080848181c603160b0b128248128410400d140c1c1c4a81443c081c0c51200591400e16850a03445201081c020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 16401913 1250 16400663 16400669
    0x415180204080d11030d0c0305100e010501020a06020f0c011e1a0d060b01020c03030a0513080607020c01050a0903050d03061502060402030304060c08070b01030501050402030d0e0a06260f060a1a070609030504 91
    0x85080081201c4141e8142e00454041e02b5049400b003a10b5595450704150000c0a000c0c06006800c0706140e03801080e80c0da000b0300320391304095840354541200c402d00c660031a44502000312540450b8218801c0340d9100d8412070b603800740080c0d12221085540c2e0b0001c0e1500940703640c0180101c2c0d5079241d2141c5079200300424071810102408490b0f6500c45040c01428980044560203400d00d812100820078000214450380903600c140c00030f01b800701c0d40038019109a041612100b08001400b407002011401c208101a02d410075a01c0024506081907004003140f440c44036008259408032043c480162400030440341168503d140200b01445c0702d00d000768a51144c00001741002c007400d8004030034424103611643c043c5200324215800e42c0101001070b103001c04010b80f080e038440e2518400300203540c000c200380c110b02004082d0088a20880c80881008043c00343c44019101109401b00002401c00c0c034460300280401b03150303681410400a4030405580b01d00a0b0051031540c458901204140c020740a54000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 16403163 1250 16401913 16401937
    0x50f0d0e0606040b01050c07090222091a090708061306080a05010c0906170103021c080703020c040605010504080604060b12190201020106050105030405100504030203090415180204080d1103 83
    0x24598509030400e81e50101a61650b1149252403251107096000c3d10403a042503980c2030103020000c3c07900b49000001d41140081c020580b000c201d2103d0344042680b01040508191800014120001000c0400319149201080c0c001d61094050101301c0da08203c065a200000f1965200f03100300710030038100030340031640c4000031078030035903800c4010000103410040d40c180c11a618030f045030f41c1c1c1e62400c582c26840c4208960829014100600160070320b91010703150364103000c1c00e5240100d115614541d10780c0c81040c0540040e0021580003202d45001d014502c000c010034648581001e051000c00c903100c0c14083c00041050355a4012041c103074580c55104580340003030200765031000044490600017160889002c0380103528082e804070300741d0300540650f1f00984d0040010702e81d0452400000c8020600900160198802401032844d10b070b031070380501c03c2d001e201b00d070280c288145490402042ca1081c0c1109040c050300600050000140014903014945003e2420081c0468421a1142148510512000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 16404413 1250 16403163 16403171
    0xb060f010c150612080408060f010b040303030e01020910120b01050913020d1103010e090706021207020d1104050109090201261f0e01090617150c0a0e030304031a090703020d03050f0d 80
    0x109000c420703000b4201f1158030800790b804a94038030300c410310740010034000c01c40f003050203000910100e0322951061941426a1000614104071034001800345d05200c4a0705002410101501501c0c48150050500d040c1d020f0078804d04010360080050061821035072040d080381e50200b207152000c0c4030b03a0882d201c1440550711355035480d40c49419020140800303e1f10f00e40300d0b200d00c2400041041c400181110194141c8210f24104075241d403c0002c44061400c0680d04078001c46c5500b61030340d94901c40d40d4020260346000180400071440054040320700103c0b28181c03550801840c6100c4c41c802d011242c3c1c04a00d1050540142c0c0304013020701c000100359089600c40c0701001c0008514001c05a2166041e902200c070300303003010400c02400780d940707400b285d2007040401502008070700b5100c1500c5c0640328513a1941001c443d0b030030300c00b00030a284d50000d52040d100c10001501d0391114615286103550061024005044020b0854011031a401203044005003007100000b1041c400300c801e04251800c15800e010300b40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 16405663 1250 16404413 16404449
    0xb0705070203060f0403020706140c06010906050103060e040b01030f030c0f030302040e090a0c090b04060b0f070309050a03082506050a0504050c0402180f0402040506070c030b060f010c1506 83
    0x504039004500d049009104041c00304640050340c842c01e0f4400d581c50740c0101440c9061040c119001d2206401450610744288140710103c803041c4601350180803480e5000440500c0c160005098980070790108240c060f0380c0041c080403071403100655040d00c0c2c0200742d080c2385260070f1404498001041c2c101404080c140c2072800308056240d002401181c2e0030300f038440e5032912100c200c95200c030700840008082d0031070303203804020311805500454415000240f001403295038400342848142d200440303a120b01d100014640040580003a45840500820b640c4c00c20b11505654510241d44903580d40d4007882d10b420a03400010304000004000c01641c014000d00540c1070030500e000c0a40010745040700d081c040c000c440005400e15100f59904120ba161144013a0241d0b00184a4410150050700c0d81040e007c010114441c0c5400d00201141841901c10703480031859401d00744000b00014114a00c540f000c0049841c050781d000355000d10080d085008000454044442d00c401082c0542c0700031103003014a9007075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 16406913 1250 16405663 16405667
    0x702090403050d0b01080c0712021f0203180705060d0e1f020a0207140607020d14030a050a0305010602010207080910090302040c030c02010e030a170a11030a050103030e0411030a0b0307030b07 84
    0x20301000081c1c04010b00041c804c0c140103584502c02181c800301034078020f1080b80045000320114400c110250f0054428103400f500081c07032001442c10590f4040c0e900003090052000c0700c03143c803d4503026400064901c49040c01c0c0000d15078444c0540d812106629020b400c880300f007040c0142c641c100894066603400500221040d00a50800c1e030701c150141c01000400120350800106603510348000401c0140340100c2507003000465105d03014103442d03011030000c0070810704400304010243c4480c29122184c81e100415401425104140c100c0401c41e40107004c40380000e800c0c038040d6071440e41d084070084070740514a90100d0380c0c40c0d055800a0750050074801d180341c1480d095400b200e2411310315402403201d0042e00000d0b50383d034403a006070f40c0b0014032020003402c603c200021600d034208050380e82c080f030740344001c031a0112a40c10070b80300b29031071503502e400401c1050b400002007072500d041030390b003032190308004a070858890000824019441d900c2e0150500e40d0307030301440424003031a4486124000381c2081100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 16408163 1250 16406913 16406917
    0x23060307050315190501090615140d0c0201021b01020309071e030303020a0309020a0611190510020708070804060f0f08100501110a02030303090a06060806010b090609010c1e05010f0b010206060d08070209040305 92
    0x81c0800e807007094840c14400e9200d401240c1d00d00d40303c24082b5103401040b042003401820080046400c555003031204203001c0c1d115a84030f81e0520140700025849040141080c3e0506400d0750054064031541c81e0740c83c0e2a03144030540281240e801d030800603111044040290040d01c00c03075800075880004100007150460f04141110740f24043c0d1800c076504003500c0307901c0e0341c0000302c9410094841e6000d42030880c05400c4640040c0350551003601c4140c14508071766101e8607140c1194100e44041403e034442e442901d984040340010842c80b61600d0501804d01c80b0500c1223021990142c40e04002110a400d5201042004000f0945501804403030766403605510031929100b0500301100c540d42090740020b00c44100294840c1078582c070702e04080c03400c1407540c200981e561003168071034140003443d500b8070081080200348e80007004100721800460031440c9015421901201c410000181c509860030340903036400035580da8440e10954083c001000c1d9030030301c00c1c1c082c002e054000758026490360420080581c0100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 16409413 1250 16408163 16408169
    0x60f010303030c050703050403020f0402130b071e030c021002161403061e0f041109010b07050c09070905010804060219020a1407120602070c09230603070503151905010906 75
    0x10b07081201c55043d0b402110b0324480d040b400780004405010500152501c5042041d00806c01080149003030061088405142050347c00704120305008034818081c048050704070340c10941610b542c8580392090365005040c60f10344900c044c2c0900c801e03405000d4403d001300b1406036590440f00005c4480c82e5214101e038012a20381d001c2038001d000c0c4001058481c8806440c0c1301c0c1482c01042008019503a10312400f058400041050f1a1005001c40c0c09840c0d4413115110b6001e0042c0c0103800d5520640750034143d00d4000e144c1d00490261000404015106ea40304022a060700e00074646508240c98504102011303014031901c841300007014400d01d4050607000100207421602c24041806980090308299442e980184145513503002c11040303010019031140d0050450320b1003105240a0207444024400840e01c218a240d0220200303410b000c0070920328902c0d982d500002c205c000740056400c28000c651074908060310f50b095200d000004c9001d10302c0d4040300e0141c0500262040016695407404c40c000b410041c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 16410663 1250 16409413 16409417
    0xe07030212070f06050c070902070b060102150105060d090f0507080a03110d02030f0d0912021609020702031005040212010c08010501031a0d11030a0206130f0503060106080c1803060f010303 83
    0x240c0c50800c0030800b00da5030048900d07820303070101d03900d2078988151040c0c0c0c09164240242d01500320042104007803071000e005068022410b03000b841ca81130002919100f07498280235030844d24100100f003179a540c00102d4912071200d60010490320790500d8a503d120105003c020300398001d40d103000c225020006410315070180030f6038490b940c250f520907040b038950349200c0c4040010f810821880c4400f0300c05070010411150b01c028000b440c0503a82e2607140f40c0d000c1022a0600680000861480c01d601c0418444042c10400d8421441d20110340d001a94840180d090a690340343c451000809540d0703400d0b0780c0d280307508184000344100c1c24100001844c10409000e440c1c082481d009240030741e001000b296020401c0c0181841c5c154600c652102c141010003651081d502d0711400084100584440001d4403041c01c0c0e0755500700308030341401c029211240564002c10b009500c070300010000f81d5480745041d50811420a032040d51003503011403a0481c26500c103d41c1e03806104035000e112104034840100c0341280e0181e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 16411913 1250 16410663 16410679
    0x80a050403140d08060105120a09020a0b0c01061403010e0a0204050705040b03090105090d030507080601080405010e1b150307050d050606040306020307020c090901050105030d0810050a060c1101080402061911010e070302 96
    0x917800641d80c900612011035142401c002c0052a9048590b1003180c1280c0000c0c40c0c0c10540383e03240c0311000b09910042203800aa5101c1e5420440014041c83d200c0c05054128002d10220355034491607590742c03000341e0f4040e100b203072070745e010503001030251084802412400002550780d1400880c894040c0c003050ba030300451442901c20890900e880ba02c105030050441d66564515912030701c0045450110140003510766560707e1008006031001000760f403540c0880b00d180b0541c041d1022007000f2403248614101c01d41e50408000b00040c050b4071004407400d00c1507986000601d5150003022440d0b500564000410161000080c80081030300018030701c038202400c0700d50590a664001c100c80c240d030703820b20405030107500800800603050300482002e40e01150840c0d55452465030380d0001a9002c078540d11100100f851040d80b001800984c03039035800381260a080240d07043c00c0076808a91b81d441510f100c41c0c0c0c0c4c03e4840100ca00c000c0d1281c207071a040b841ca02c1009102c11824000c107180c8822051008a11850314 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 16413163 1250 16411913 16411921
    0xd02060c040b0f0309010b0603090a020a080a0c060c05010605040f0902040e0a0312020c0102091e01110705010806040207060209030a060b0a0815060d1412070c0605070f080a050403140d08 82
    0x5504101e8041e00c0c40e195001d828100f03082c0203100359030000b500402d030035502c0d554804d00d240c4510300070f58818002500100800d00360760050114810184d002485641c210030b00c6100429030054008046603842d241c103182052140c10482c0c011305041c1c21903903005040c04503400b181d0b1140c0d008080c68a00840703042125200390188940da801e24640020041840c4008000030542d40750301800c2d8152041d800585091801030000d41280507980c6240b0301d030316114008480300d582c030800c0080042c1044001745800d9040034006841c030070300181080c2c030403600058203100300301690301070310383c908005000c94500d9001d500c1c040e400380214500b0280200480d040002d911440010a00040c0024000a40a5032100010722411600008098035804c43c0394443d0307000704000f042007031182c0d01d040c0c4d0803640b51203041c500082c043c8610350085082100074010240071400400f40c170080c05a101258a644100540041e01e05014950028141e20b0800d99404841d00d00820780340e00e42096a41d5075030743c0da0303a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 16414413 1250 16413163 16413181
    0x5010605070507030809010c0b16030b060a0822061b26040209150a0e0708100501050a0f1101020d02040f0b070b1303021002030403020102070c080309100e0d05070303020d0206 77
    0xc41d4400b426561103110104045100c00707006021420381031502c5000062140c0790f40441c02c00a0310780d148245808044d10b401c007549803040140c03040044801a262890089004140040c060200c8205582d441c03010046848821031101003071354412024000754580e90012418034000c800703410080b541da080c40407003209001c00d9a49207009622035920040c0c0711b070340921010410083c808a0100780e492154281a03841e00d0309040200320356488940589050a0020850080640030300c1751411904c50071701050717821405543c1111054a0500700386001e44c08210780c10301d0189650350040d40300040e0700b0440c0c44981c0081054655442c0b0255015a5580031052144101c2001400c10491040442d4481440c01d13a80c4240a000344100c3e5101c1400c3c0c8a40c00c01c0341e0059030708030b01503980001c0d06e40401454240c00002021034201135414512810041260048901c03020b108206031480500207a40d07a18050100c3e035904802114281d0391a4030300030350f41e01250304290002d0310503003000500f058 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 16415663 1250 16414413 16414417
    0x10201061a0310090e060106120204060c030e040b0405011d01080309151606020d1b14031302010201090c0603020c06010e0106020a0b0c0702041104051512061002070305010e030d05010605 82
    0x1d030400c03101d0000708a25201001041e00060400c200c0105440b81c0000c0348502d80c050750f02c2029401340039003001d5241942c0035100030035051903845c020340148000c10110350018001d040480e00750500d000700000800000300100078105000340c0c0300b4a0000045115441d086040d4120340c800c0a165546076283c0398210703a05d01036405e82a0384400059200703440d070488a0090041040d808540c0540c0c25a42d0741c0d00000d9800606c40c0d10501c40d9951700c09400305883c116001d48407034140c14064076003042922114042d1100400500b1303840501414201164402d520090042d5004120724034000e4807003000038080d62004040c11840d1098000214904164000d450f04a84860b00281980b0010b03503038517042c1400040980d101e160040c403800016844e203008404140c20082e02465441d4149000c03c070014880c0c06880b403042c50103120040d00c0b8000b1400550700482c007164444101d03440510120301d040a640c00003070195007400001c0030024800406171401040d0034006003c1f07603807a050212002c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 16416913 1250 16415663 16415669
    0x3040602100b0901050609011e030f06060305070c08090303070f12021513030c060b03030706090510020702011706040209060706050109060e0402031e03130806010503100605060a0807020c18060102060601020106 92
    0x3c04074400041146190032001481050b00605041c4030001d00c0741300e070310300d054081000100881d44880c24000840c01c0d0b07105510207131005080412880c101580d005000000c443c4d4010981c3d4800110001c00741e9041007560405984404d00c0500c0300907910b400d40c512010b08800340090b101d0f01e020003d5010500506074440d104003001b0884030302c81a182103600c0c21a00906480240c0e5844501d540e07900c003071004080140c00342c3e00c0030817054001d1411902d41480c4040300428140b060040b040180ea021031031000c88121600c2c044d55035114a0700150081c0b04140c1650b0388404002210f0b0b00704a01398100f1030486200701410000903a403804000041501160025415007196140202c10843c0c4100290040004411603044c9000d088031400850390b250400c81540d80a580100018070701040a0240715045031030502c001072404010540300d006c0d1004107824005401c0c00925031a2080140d440441001040071200541007030010010640c00d0f11818010300601e0300042c8294014040c10040b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 16418163 1250 16416913 16416919
    0x203040807080a0c0f110901062c0a0b03130501140103150216050d170603010603030e10052101090b0103050c18150406020601061803020102100f0209040e03040602100b 74
    0x2a14100e90b440780001d500a031440700034841d0409140c0301080c14504900d002d90310803444400c1c80c038011020000040e805a1020b420014984440041140201c0c03180c0d070007502c20103481d0340742e40091001038246151074109440400340402002905c502d081d02002040340a44c1c005c02c407808040f440440e41403024000a4041d60f018107a500348200164024410405101034841d001403403951841e0414441c0d005c40000642c040704546101c40c1c4003810240c00203000c400070071030307145596406485582c05034105841500f40809034042140501c0c125a81441160703c255900b40c00d081c500d0340925000c3c084e001c081482c04002840650003445814003416100c0c804605110f002c00904007140b01e5914000c2d00300300d240350108140d0382107a001e00003510403a005031500d0740c10b0440091005800001c208030202c1041c00070800f513600856007001c0284d54100c046035022001908001034130076882e40940240c03801c21400c0480340080041c00950312581d0035079a6076072030781d00d5108c00e580000814a81c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 16419413 1250 16418163 16418167
    0x4021305100608090c0d11030717070519090c032304020d02040f0209060d0203010303111203010b030604111207020d09050f1201090f03020c0f04020406080a0e07090c090509090102030408 82
    0x224041c081c3e03034010f0784058540102c910002c8400041201e46030030103001c0b00c4030748000341195050701d010b00201c00644410070764043c0a04130340003515602c4941e449402d010345200d0100c103090300940d4401501a10320000b0511060500030f400400400110521b04a003500484000c025084032098042c0201c3c1c009200c08010119502007000820440c0188445241c0c01c019110f4a80c807400064082894031500051710fa41c51802d000d041c00e020618140000c0c1c00804604022200c8681a2819108641003050302c0b961107801280082043c04401d411580010440d400600f44a0203503d228100c180e081d20001e0f06807250503282060540a42580611007022a94483c02c1001e448900c1490160010030200c00d01e4848a40250650030150f00580012104d1100fa00348001c00c07003a96001034030210301c2d03d854040e00412407140501405206038590880401001d0b080010502402c140310701007008051241024211590610a05016401c0740b0300007440d03c034061080ea0721580d00007610038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 16420663 1250 16419413 16419419
    0xd0609060b07061e0c0903050c010516080304050a020d140106140a030f020f09090a03030e0604080304060c090509010f090b030c0a06080a140705040504140108280602030c030402130510 81
    0x28081c1800c500700d0300c4040d100c4503107101028801d00401d1741d102025103032485924214100030b0b0a0400204001e4184072040140d0740446003400314150049400442e029101e031154a040d50605171440d801a44c04400b1326500d800b840b25041d082c0541d002150001c1081d20b959000300341256003580d0f40070380d110b00c10b800b0410200306031083e0900b030180f0080409200706040b00000701e81031419640c000f540d6000794051f10415400d4410912680008001000c443c5090340c0c6a485600c4010001408503450780ca01c0c0320003d00504018000c0c1c10f00500c40750280d0b07122142d030008a070440c4505814641004824030603810045840d145081e000b4248454107820070100b0f030b07204800500a0011306507035040c0f52420125168920740030342c40303d6440c076660f603141c402044140d9a10042c42c5d0000460400104441040010900e10340504020b2602021100c0e2080c1c4005030038101c03000d05010300000820110344d000b1001144224400c49410024445180681045660403282d0000160042c0c4080c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 16421913 1250 16420663 16420673
    0x20604060302091c210504080303010303050a0f02150c0703021e0d02070f03080304060c090b04060f0f0503090c010f0e030a050606090106090803090108040c081f110708030604020703030902150d0609060b07 90
    0x790007080307061180c03501c2e88e42d50549255501c2640141c000400102d004140d40354400c00e10394062505200904079017180391451203000c6030182148071410750004075030040500078000101c68070307070210440c07044204c9802c0c82919900b040406000601a01a01045035904030303080809891b00701d0002411641d9541e9813070001e150320040501405074400307001804400c108010009050076980c0e1618040f41e490010700402c844ac50180280070040c0100300015000060026003002c091804007100a41d480003503440010103080c198141c09094604401d2200000c1d0481c0984000e03660a14142e9172a41d0858030600c0a00418403c1e4104110041c035a40c131810190f5009809600402c00050751060044c0c98250300095024020703003c85a04040c404007841401d450a20348281c0078644104d40e40c03a0643c610005140724483c83d07001c11310703005051195008441041d40a4140006108069803040c51070b08508881f07040b035401c0c841c2c003045088041c0107030302c03c980c1d22076030103401c1807101c0e511 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 16423163 1250 16421913 16421963
    0x4060e0603070c02060304030f0806040209010c02040906020f040b12060d050607030905031603080601030c050a0207050d060906110304110402070201080402060306030a0c060507030e030d020a020904080403020604060302091c 98
    0x8490400c0f050b03600b80c402507a0740c00c00940c02507109403120007c402154002400400f00100580c0c4103138414810602d81340d80145491404640c11240062003a0542c41c090700240074a1503034103440c56000c01c0202c1c1454002d802410540300c55001896a40e07501c2041103804290344000074219041940030864450080d0000701c5054840e2041c1c9040c02c0c800d0b20403180d440e000301e00130b600140c3c544050042c00e50301445061301c00c210601d40315282411004001e940c9142c03522480340034400c1300c900c000c18005983e20490b18582e100e9800e010002c810f41e400075240c4c1098074240c4264a001030710501d1490035108032070142c0d03410f17182d0590a640d6130f0204159038000922240c0c00d40a108030420008070f9039280315020303080780d8580c0c0703032201410704004100500c140502d0380642c1c440d0504100703181c0c00140301c500165040344d0714400eaa89602d85000c00d03009940c0000d400c00c80210317012460a0300341d0003500d826007080c0c912044c803040301c1044840c0e0b80440c40c40039056404511001160000b0010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 16424413 1250 16423163 16423171
    0x90c07020d080c0303071e020a0201080114040906090309180605030703030c030302070b10060f020105010f0905060d08030907030209090d08061002010204030b0f010501090b03011406070c080102070c03020906030304060e0603 98
    0x80803d06003042a511581180e0046a2a0000455481e1070082020080b04c0442042900f44000c3c0f1120340c2c242d0010b80321030010f000f0700c80b00ca401251a003146a440c1d4105d010300c550301440c103010094140c5009842d101c4140590910f00b0882d4240030452600d61050204885c801801499142d155413030907110700c081d40c0008c7e23082507020000240442c20001075140944800e0f5540e440e514a0803a00401e1050440e50020469040a004001c0c443c80580a41d081e1800800c0006854946c0c0c000a0440c04500c0001003141c82c0100411940d0030000c5600d1013264001c1d0350000c406c0c1c1c0d50000c86601c85282c1c600d0780300482d03082c102040060502144c04448060140001894142c03079803103002451208a0b010009030301a1401840a540c1c0008a000101b4017401c1e564159414030700c0107201c082c0c10840d02802201f0110303860081c44000c01c5d2080c010588103008555954103130401030901c03421804142c0c000c0c401540815450700700001101c0440710b007079559160324101d0000300003240e40054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 16425663 1250 16424413 16424423
    0x90d0c0f020616200d0f02150405030a03030507140a17060f0409050105060319020901030b040606030804090506011d10080a0608010606050c010f140a0c020f01020c01020405010806090c07020d 84
    0x440711083c0d03244011000c40010f4010380300149a05884800025030201c050441c5000740000c0c00c200c0c0c0003c0034018048249541150000704580b80c1a26a0815018541c40b42c2e901d803203110805420305405521140c002e00b916501d960324002c640c039008010307100b0b2590410000300c4601c11141c0c4402c0005500341c018000078a20b02c000c0c10f0102c0001d0a0b1070100c1400d0b80c15940d42c0f001d0102603c0c1c2000099540c000028601c1810300349a000039150340340502c4044c10240c8040000340400044d030b800040516440603c032501c40780c8980900001b4981128280d000c00c2450310207420542803c200d0b0407012070700401c20f00d0102001c0031300700d07880750002d00281c10390340e290840070600340802c0c0102c0005d8013096903010349400281c0c10540c01d40d51132a00f0020001e140c80050812100082c03102d81e0700290300d80c00803070080e40030075040746800c0704613101400f1548003042c1a618224190014012950300340d03140d401170703100c88042040700340c01500c003e142000b003040347c0001424050000d8402c54014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 16426913 1250 16425663 16425667
    0xf0b060a09020a050c010510080c010f02120313020112060b19020a06021603080f0c030105040203060607050703030207050102010e010b0303160f0606090b090a020c120d0e07031a090d0c0f0206 84
    0xd00d9441c820b03a080000041d01207000416194080a401d11030170323030f20994840030303600c4c1145022030303141e1110f031070500d0305041000450a01859070f0003000707226644040700e08910741d81d24244118103c54948203808074001412100c400800b04240d000300000c2d0750740e0f600034600d850040c01902c103048410741c010900354080c120100c0d0110781c80e480600082c0707020074000c0e070100091389401000164001c00d0201201174100c280704004000d03000b500e042d51002d480041c0c2d252294000580ca5001c1e03080024094843c030700700842003543c01308100080710000c3e002032000b10b0602c24002e00344c90826600e107070160f209100d81d014555103004525a06805244402440710041d02c070f00c4c0580e110f54000b941c9031f60303d07070318001c06906001d00c0b01544200c4070601141031503181c0b10180c0d110100048150381204020401294403009a44100d4500c0240812101c0fa83c0e6031b40f50114401581c40b0550203051551400500c0e5200c01141490034810503649100b042c400c0c50f590165507146031780b0709a03004002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 16428163 1250 16426913 16426919
    0xc02030102030108070e010803040f03060c032a0806060711190e0901090201180e07140f0705010e01050105100203030c0a030b060d090c0602030913020d0e0a0b150108040f0b060a 78
    0x8203200550290400300040d010b80350a080d4040c0111006134803605660703000300000c201e174074065883c080c196030f4442004581d47c4102e100c100c02425090584043c52800b01c5060b5400120145482840b0055038448000030395559040015074000d000024180c11605c204240c10f51800c4201c42851210341c0c00c0308041e10b902e481130180b42caa01240c00c0407a50703543c0e9500b4400e568001c0302a904ca54003c0c0014660a41014020901309401800300d400340140b4283c0c034410f51600c0010f54081c80071822079552207641c5400c0183c060000051700900951070705002240d0750404040319000032030150001c40c51030711005108800b650111035050101541e03541c00811560342d00000f02034400c4507480c0401c2d243d4580c02c01d01407070300c1ea5500c4901554010806034181c1d4a83c1c030b01c0d41c0703808224030b1801a29500380c840d5400140c01410000811402581020400c02480202250081c054440070307644c40c1170164010340314a001504c021340350719003140382c0c20009801918195445000503200c0760100741c1d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 16429413 1250 16428163 16428169
    0x9060c01090c03050f01110909060d0803100e0c032203020304050406030b09010e15070e190b03040c06030b010804150e0a0302010501060e01020313061116080c0906061801030c0c02 79
    0x241c0001c11981d1000b007410410600c54100848a401d0070118000c014890714981c03202910710441c21050b010320409400540296229180075001a0b00450040c1d0340345003514202c14111810f0040e0b090508100c1d020036010424581078031f2183c1a170420603c00207201c01d0101003941c200302c00440441c0710821020417951601d0062000662042442c0502420991030302d85c02c0d1880c481d42103089501041d0320782c00c200c0384000400c1d0071402c103046c06c030619040c0703c0100704143c01c10460f40016038685240000d000d01c201000710300c00c0d805081c0303200c0e07210780b25035084042d0341c1c400300e1881c006079481002c100810010418400c50700b064040000750712004820141c20500b000c141600541d54030300040201c0368104159500042d402d01c051441d0100e54030820841e10858041c68003001121340d0b0400c481841000140c001190300003c60b040240c0d40c1d4075065070740c401c204039540680481c00100769030b42803440a0715410011030300b008881d41c5030200110b0007040da403a0030004128000400c000035072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 16430663 1250 16429413 16429421
    0x2030606070614041401020307090312090801020f090f0a06090e0c0c150906011401090308030c0405060d020d0c0c110f0109050d061a0d020102030304060203092806061403030a030209060c01 83
    0x40343c8401402880d28081c10980780b0071a48400c244042d900400030040102e6003c5400b070180c83e0701080c5000e01140c00f010403140301240f50841c424a45c400100e65000000f51400343c000382d48226500c0d520b500c550b500341320600c8810f216000101302c04040611a105580c3e0000d07600c0010601e0302420321888030800d40c60508406d1200c07010074544c0060040d00d02080c40114094010250b140034a010607100007080814140304c09000e6002c00700225050400030000c80f0000c0c1001890746031203810380744400c0c00950001800d661074610b000d24801c00302e8007810701d05001e107400c130a19080c0c8005181c188034940311350720105810045201c0c00851113680b001c0700c1010070f40c0981030014058861810386000f8201580c8c01520132520075901c280140c0c0d00204895000d80d0054000d40c49440e00c011443c500020745450b11071102440c400090141243c80c2d91501990240b0806c2c8546581c4c0d802d8505200f400e403900b5505500100400742e0300e240280c00a1101020240800c2c2c5002c0161072060300712 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 16431913 1250 16430663 16430681
    0x9120f0306011101021e030a020904050c040f150f0c0515130c0e01030f0201111507050d0c030509030a03110d0216050d0e061621030f0c020c09010603020306060706 72
    0x2104000c03040c080c040d6444040c040d02e2607601e000840ca4011003590100341002103903400fa01e08000003000410074240f43e0191029458007400620140c2060b440c103c50b01d4006028440300010402000034140c04040707200c000a00c0561281540615940012a0110240c8605580340d210303141e072442c0d1304520300c41074502c43c03244074130b0300c0c00e5115240c500000c3c018a01d60086c991000c0c11001400851445650b004e0741a40c242050542158601500f9091007400c1801d811410711070350401805640110003481c04e041e95500c00c1150350720860068041340d50603601d84010343c0c010f02041c800207009034490b40c0b40b25180d4803501d007041d1f011110394059920900d44d90004038030400400080203410800c0708060030003400e20f0f0a48034800c5c004a15a80100c0303041d082d2030404822040244a0f5011141c40d030000c0d408142d40ba00480403101034007500c1075400c0148200d1130001441e100500c041140038821800812583c04c507442d18104030080d40026009507072104017000a840014510703c0b0718802 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 16433163 1250 16431913 16431937
    0x204140106020d030e0304050303090103020319020301120c050102010e0c0907050d0608030706060e01060813020d06020a02070e13020a14041e09020901060305010302032d030a020601050f04091203050912 89
    0x16900000383c02020340300101a11110342e881072106000946e000300c1610610b410070b203001a16a40e4840e03a4a400420081488a280b440080081100ca900c1d01c100300000380201c643d80700c801c0c0c0c3c9000480c01ca4411460a0740c01e0b03000900c100a403031a00c8500a070308040c9a1420a00380076186003950101c0c0d0040d4803194140c0c0c000a0100e0422516000b420010050204464859071400401810702c2c2d1008002a4060396038a070345004555400714803e01e401d0300020119190410f520011f95660300600030640004005400101c1c0c100910b4440c19007598041c04070200f00b032802041c002040009410b0030350064030307030309990682c3e41c03070100c484400e1941e140041000e007054014841c4021043c1c11a20825040000500c05610000346009811105411130b1a06911801a81d0807103c4c0c40000c00d52140400503110b0315241e40001e125069860071603c1205040d41802000304550360000b004200503048007c403540180a940181da1100c0410152160750b210524010f84680c00b82030301c511 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 16434413 1250 16433163 16433173
    0x612190203070608070c06020c0102040306050c0702041406010c060b030705181806100605030703200a0207090b0108010e090304050301020d0519060609091509060303020304060f020109030813020414010602 90
    0xe40c941004894000e1a0a0078040114100082c0003002600d05090151801d0f40029481c01c1d5039100350704640045400c19420415400d044003070440301d0b88403810030381c401c40c03c00304601c042c2c50084181d140a201c0503110031600d8185030b42ea41d409880303030440309907150069480003c0d081d01c0d030150506e007400d00d12403258072a2400340c1180d0701d40c801c1214a490103900010070040d00c0740d112120501030b250241000c2e6202c1d1748000c1708502500d180b58005819450f150041d031415000b031009000d2122143e001c0d1031040c1c2c1c8070340d8004110381c583c600040c00120184010440e450008007496003000100d02a2840d00d41c880c800f003800d981c85811507641450799801042810041180c2d02d0b54924100da07018410070b40307030980042507400c041c017507130703100f207584484006841068040401c000c00d04070b082030240356503a003006034032504a840f03101c003c942c070740d0482e0103e00e02c18803503403025580c0364903400010f445207605c06440701c181050881e0401c1d510115403114200c8000400c1c000e1a886d80209 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 16435663 1250 16434413 16434463
    0xb060c06060a0602070b090603041e0c29090f1203070803011703070201020a03110304031401050109050c070c230414011401050403080409050702010b0d030306060e09010b030a050612 80
    0x10001e10b00c10ba01c06000c540001c407003072103000420310443e82c1d12002150320544a41704e82c01c2020100381e0405141c050840c2455081d82040910503e540c204d46034090002d2112701070203001e40b40100700c0500e081c50140200071450b258904000ca2003000500070700034004045a50907202d103998418081522808400300042000c40c12042d5285d1188511030301442c2031007071b29030010f59038a0700480001c9c01e10070b0a18040d0039000e801c0080e50004c6402500d8114401d10038850b07140209028062404840d003403100080038120048210394081d5071002c00c51007407500d40080f2114408403440c02810780440d84005000c01da032030f401100002e130102001610294540643c0c00c070382d6500588164180320003480b080000c00c01040a80d0304560900c00003003000d03034514008900514a0a440d598082941060b00302032551507400601601e0003134031852040844d0380d0800c0b030204400d206404070700300304100080082145070425a04141c01901180c69260010100d03810702211200300359160541c1028a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 16436913 1250 16435663 16435669
    0x306010b0d050a0e030d0504020f0a12120201020901050a050a02070e010e06090a0e0a02040504050f0607090e0c040e06010e040b03030301090c0311130501081f0e090c030705090105040f0b060c0606 86
    0x142d074208030080020411000c3c0e030f488158490040603142c480da00c1e501c40c0090309548510301c200050724001070001100d40c1d16003003112400c00050b2015207031f5580000341c500c62140140700729102d00700142c49050070014126804c440a90180050318114000c0b468000340040e400c085250103811240f21415191604c0310500c0386c40d14008003c001d509042c249206d04543c13011805915031074041d03502181903981d600385245020700c15070545003c3d1040c2e4081280c2164003c8007041518184482c611458481a91007403403401356000342c0812918000128059601682d0350303c80e09000a00301185141900c80001c2c15030304243c0c0a100320903212415000c82c6581441101d42580748010b01c141010584484908184d240b80112814400540c0101e0b8180d020070703121811030519001c00c0044103448140b05560708405441c4804680b080b00701c030400740e00d00443c4d05400d51b01c000c2d101514581ca85000c00c0042d05200012000c000e607106172640c000d8030303030000800c0790094010040800b400e00c4004c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 16438163 1250 16436913 16436921
    0x4080706050a0215270c190e010b070203070e06120a030e18100312050f03070f08060904050c0f061606060302091b090103020a0302040503150108010609020a050304060c020a020306010b0d 82
    0x4024043e0780910405c654a8240311180124490b5103400590014525950300c2c5080594290580c0c000c045010301005400c51354007944c03e6030141c030101855030741e03200d9080e252406820002035146d00030f03200a00010504103100c5a0042c0010001100c01c04138084c003905044510302d0503800504800728050840c01c0085881901c5400d11010030281e191895442c100c22549009c024412180701c0e03000c40e085ea2142050714031079841800c0d226640d0800c0080030701007103c2003400c1000704611070000b90381490110012441160402e000e007041d008030070308000d070080e410841c05503c1442030000c1c04d0488400d5426105851281c1d400090750b60071070042018440009003040c480110201c54659801740030400c0d0780042c0820300b03015803144042c0205501a000c0c6030869074061103000c2690100e084500c12440c100d44c2c184008000040d2180c9000302a84545c0e07800d18041501003011030000740195011100c04103440c0306860b004111035000a0501e40c0c00e0b4044408003a01041030a001192449 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 16439413 1250 16438163 16438183
    0x8010501020304060203071101200303010302040b0d030f030c050409020a110616120203072303070e06040f0302060715020a0f0f02010b010801090b0406050909010e060f010803040509040804080706050a02 89
    0x10b50510345040c40c000d50303a120f508001412014958000c0b856039000d4011700e0000d194581ca0584550f00401c8015520b0308244020ba102d1405c01c5030450303140c10840341d01007045800d90303510100ca01c0320b00c805601400e0382401c00c00400504200c0058407503071034405008000103e1340c071111401c405411b02494141c014203560040080d040411299a0300200c0308801b007448003101584940e1070400640344550045000509103811022113144102d0881c0158810103003501c8012111102c0005d020b02c40c0140d000b1002c164002c0003085c0094580400640012889800a0150a030f0380f20103003020b903000402d125000c2801c178029040120b401441c0d021002c00c181c40200510080380e4002030036114180b14462402d82e80340e072840b0503501c03240c00500242001070030035151400c01d03440700c50003891002041006c40c0524000300715181c1c1110b010b00c0c1204ca06100850900d4105170030031107a590044e00403188c0400c2040001844001403040360001c0c0a141c40d207544440302c200b0080d0034590307548 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 16440663 1250 16439413 16439417
    0x6130f021b16030b090a0c090c08250509030a0206040801060501020f010e030406080a0e0106030506010501110106050604030b0702070807030b0103061a090c0903210c07120f0206030a09080a0201050708010501 91
    0xea50740c0400702d0034041820440b50040c0075000151076034441c240c103107443c1003009015200c0000d0042800741403600314110030025692082c00e1655019982c178a032005050050880028159001044a102c1c8000e071999850040a541c03200c851540010499031140d406001d590b5190791040102d9a0188154614905d1401c004e2004c1401401001c1d2a445a40034502c20b12402c0d00c04200d0200c083c6e8420b44604608000030010180c50341450f0b60742e10b2091090500190480c40020f142d0081801140c048600c00f4121500f8241160740302d42e10024010034200840c42035030b03000103009400700103c400450081d80501025415402d0002c03d4603046c01c1170300d54000e1440500c0e902e5449020000b5841a400384001d03484190b00c20009040240d02000c2001d8000c40d4540800d0a4203010010102c3e0a0030740304881181d41d9460341030b1429047e4000281004207000d00203809030800c03000a55110150702c1c400200e4261a5503016116005246036000503956041048960f0741c0242d40140034080034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 16441913 1250 16440663 16440673
    0x90309130f0b0904050d0318051f0509010e0a06021b0a140c120c010c020118090605120607050a0320030702010c0807080115050c0c0d0f0605010f0605090906130f021b 73
    0xd62101c1b680c81c0c07500010401019503e42c0724000300350000c0c10700b101e0154800f040c0d6442c0304420400c0c02c10030368040341c00d69645240801040402030148607104100c0f4061000e0200c1f070083e80c40b100700079041410040340040441c239003036642c1d0100f4007034842e0942c07107401c40c0008903c502c80f0152801428140341303806800b00c5a03080320510b500082d10381035000240b8210020820510049519104c50306024203400e44081c00030a0a4000703401003019120300391100b941043c0d0a40d031a590f181c109403090740c003144c0c003040b9120f05c0c58420b410202042c5010030300421380000d4002c0300071a0b5803044035200011b1755519000010580c0c41841c130390f00444a031400900e83c0d41800c1003203002172040040401072040014000141500038068111000001010f070150000d0a0504030800c02410070308444991814001040c106200c2e0307101c07400e8410607600d042c00c01e41088148030320220702603d00d941c003802d150362407020b1113624042c2400d080e141c444051384031005107600c47d003135820341c09a0304841d1b040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 16443163 1250 16441913 16441921
    0x2030105150306040902090a0e06090a03050306060a0e03070b0307030b0d02060301050409050a02192c0402040f0f090804090b0402030f0c2d0a08060102010509070e090309130f0b09 79
    0x751400380c0031201064901070341c1c0303480d22000076006101c165402504201c80404201880003598041e0f01000902c1c0d056411743d42e00c40f2902e135221060880000c01248007400454040d062040c054480030900e401e00b0b20503407084000280c07500c49030f0390081c2c02c111000070805c44a83c1d8103008010580006540940f94405035900007525800705001d4039008a9540b0002000d200c800c00400c084180c02400c0c44458403c0c2074006100840180600c2608076809603041c1c200c9070142c0c00c10040b60f170402c0a06606512994200030141810007031050398562285100384401c0e6031442580c1c90b40f889481c0250342d0354546a403034400c1c0da4407400e481e03202e1032040c0108400c03130110380e031080d52080300b0703041c5255502c001c4446d1075444959010010240342a04260b407070b41c1d8004800401007010a030b180e002c495512100124260f0380107c85600c1d43e90050941000011b20203c0c0f560782001850080d0390400e240c21010524400501045a032065100d100c80c0080043c2845443c00024054a0510709803034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 16444413 1250 16443163 16443169
    0x30a020a0506090a030213020403030201230f04020d0501050a06051207060203030604230405010b03010f1a010f09080d09050a05010309020913050c09090102030a11031303080901090c030503130902030105 89
    0x100301e00c80c00e4011040010410101c0c0e03a0200410f000e580e000300a84407060700d8000480080d000350204801541c607103c00c1c83e0700c40340c0d0034025544840019050304c2c4103a4519101c90412040030f403040383c201c2e800e225030300c00241081c01a01d1080c02910340000700c0d10f203003004001d5440c0440850554075046000240032150b80442140c4c0e0101c001c0d41c01040d01d22000c040c507925034031003a001d250100c14440034003007004030642200ca10100200d00074040d0440d600112400c072048400d03001d29050070122200405e5004146003031400e01d09041c254a41c0340d4510725581002c0344000400700082c0d00800510042c504000d801020301028a01001101030303a40c08900d10200292100410300e124244401c200a02000f13550344c0404094441d02d824101130822502079001524080c03880c03400c00105001c01c0d003030901501c1c420b1075080a00d00c0c60042c81d07241900c0130351010701b14000554032250190041144810750800841c071070750041d542c440000301244042d0489401086007540100010410b0f81c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 16445663 1250 16444413 16444429
    0xf0206100b1b0a08070503040e010b030f010302010e0a0503011505010206011d04030516020618030105070305090303060111250f0b04030503040e0a0f05011401020106141c050a140c010e030a02 84
    0xc48402e800304008641d031514600d022422a07000b00058000104001004400f0020b4000c564a040346503013182d80780d10182c0281e0004a03688003d4820010040000d988149083c40460001804035801d00791550042421341e01208440c6444108041041096580c1000a24010644000300342c518103000796584440a002410103000c2200102c1c0c030788181c1c0c150000c1810103c3c0c0c001c150f980d88040c5c0981400c1055207000303a0501c20751a050000351403038001c0c0680e41c801d140e401c01940c5145d4400f80190746400d00e15aa030ba4807841524083ca20180c0941c8503552110200081e4601c03182c5403428400d2104c1141d007014070f00b420700380300800000700000151010794034041480d10382507440100c0e0000030400c814884c0f910b1070510303000040c00034800d4032802c0210001c0c0d000348201c5880c1c00f04122039a80f101c0c0c1c40364001c00c045841d0442d03901c012022241441c03150060f10285910340d1505510700580010b8940240c00c01018102d00e0741c0c00800304818824150003901c41035030345800140100d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 16446913 1250 16445663 16445677
    0x30402030a0f0203070b030108010c03060806070807120608070b030411030d0507230109110f010c0b0a09060603080a05030915070804060c03020c070b04260604060905010b0901060f0206100b 83
    0x8003031000c0d0302c1c000310341d01400040040c06541214546940e0f4500d02980603000125800c0d010a2500e00041005040401d00328403415040c1c07184120781e15000f034100c45002c1d2007009094010b969a0340030860300003d02014008080481c200c84c1c490a00b801c00005607840b41120318071950102c04c960315001d41090588034038179001450692038244043c1c1c0079200780311011048029510f011406010049205440445c002e41513036007004100b030f24001900d00c5c6010010240640b041c02c80010102005ca80200411a00c0f4803000300c1d2040d0b07655105803403604019180804a4400b104000c002001001511602460809100344030b060051000d03041d0311001e4030140410381c89011442c043c43c042d404071030468402c14100c40742950f40354a011303d560020700460042c0021800c1075103840b0180801854600075010107040e890b00c503591030301c0050400043c02c5840e552102000b5149585d21044680200f1076522142103402e100b080003818210000e02d9402140c4468000340044107620040da0b0708 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 16448163 1250 16446913 16446923
    0xf0308060607020a0b030406200f0f07020d030504030b06030307080904020702030c030607050c010b09011a030a0f050f0403110d051b1608010b10020c012102090301050103050615010302030402030a 86
    0x2140c680c880407400714400c80001039040180b4800014079071420070000d40c4104d000f81c82c00c201c40e1072042c2541d0003400001d0003921240d0000d000c04960015400010003900000c2c1c3e114616007125a40440c481103c5410141e0120b18081401c0042c081c54801195121400f10f020350700d028150381d12904a401858000781c022540032038400219241000440d04101e00281280e49500d00148010682c0c0d228071740c8107445500b084400c682c00d05101c1040da040c0e908001000d148507003000c000500540000301a59100e540765080f1140340c030356910030030780964041c40d40c1582500d041d0030701038001e9800805100700c0394411a81203506507440700c141c800080000b1072462100301c8045060380b4110088050700001c4030a10000640200d0541c0b10110a080030307509020f8072032200c40240e032551400c01101d408180c407180510a04410122050030302d20142000509028014010a0844900f41c10443e4030381d01420502480081506040c0103060091900b54a50300d8181d0200e91251406440144 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 16449413 1250 16448163 16448177
    0x303040b0c0f10020a030f180b0c0d0f0902120c0906040b01030209060c030702030c01090e15011b03170a110904020d180609030f0302030108031611030d020a021203070f03 75
    0x54100401c0c40094030540b0300100b12200d8034041e1620030020343c4007a1041c40824074006030940314100303500555034110300070f4150460300c9440c0e8680144586004240b65001c810411840304615158824002c18408617000003419408a205203d42e141103442400c405911107180070f0b0307003a41e03060810f0784c0c000302c00e5401060b14540080141c01038060110031030ba11900c00b24268000070310000c0134012003402202107694071400302005440354841c07030003070011008540000072101201c54038000e40001041c5002c0e04009850a10200c550340b1000c6d08600141c03c01071102c40c0513a01851240d000244450b0410045650321040c18062082c904114029500480c151811002a5000d0503807640b482407000d01c21451490300c0d0f8020041000304030042400002d80d22078852003071003175a0596103500f0095103080da19842801744a080104221020003200d0700000203078030140500c006910280e001407000459500c10041c16521540e2000000c0d030060004c0804a801a09044040754160800c15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 16450663 1250 16449413 16449427
    0xc06071e0e0d021504090906050a150513180803041401060f120b19111905090a050d1403182115040305250b060306040b1f0306110306011206050303040b 67
    0x544501079036101902070307032807c0c07074000600c032903600703c140b08840070242040043e003c0c40348809464064000c0a40254000225446100e4250700c00507038910262000c0726400c84a50716440d0b5640202c3c0d084640043d400101c0c41005d109015605c044c2c0104011408102e090a00c0a1034060b0800400f0b0606131004000c0754002c0032481c01d25100c869050f8050240c40c5200b0301c44a290381c4240b070408400c1003a42c1c1000d8506200d1340980782e108074002c0007004103520301000c024042031070b04810380e41d581846001881181d401c2005103920704400f51003c280140040c1000841d1900c03c8003144086100306901703007044004191004140d080760215906c40c5c0300d500741101d20380200701755150018a0300381460200c42400301c00b519220b118035203400440c0d840c1c00038540c13105000d503002480a642e90002c503551095510428114581a43c2c02800340340d5292242019141840361090891200005210309942d00c00d4140c00480c101c00f00900104c0e00e4540442d580e8416071240d1040c8010200d112 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 16451913 1250 16450663 16450699
    0x13020f01121b050901090602032502030f010f0507090e01032a090c020309040507051e030c12010e0108060601050301030804050114070206120a0f060501080f0901020c06071e0e0d02 79
    0x307030005400c84011505202e01c2002c0281c104e5001400f1940451502400050740d28400400c41c4c411985003011800c44503d03c0000e046000b00b5130300101d90500800c0f0405a20386001d00c0740d1040c0400201d07002c500d40c10034541c05080301a1540114004201c2e0750700500224150710310503003c601c6807003424000300c80120801c1d0401082c41e04403604450800c40500d407030310b40c0040544241c030400c903030420583d01d6a0000ba14640310307148000304409a0142c04290000d1404040c1d507112440c511031501e03114402115000202d0300360030030100c0c85c180c180103018a80040210552081007130801625650540d11812490302442c800d1504014104001120100056041d504c003540c3c0a0400e9403100c0207810400d007202c104541e002119850708640c44020103d50242504485c41a119002c0d10340705c04580008001006080350b80303170740d0204014241c00c58200501d40c401c480700d581e10602d50b9400c80904100314160240b9400b0040e038118000c055569450f07042441c594101d85a4039034100304160 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 16453163 1250 16451913 16451921
    0xc011704022806030c030b011b05030d0213090f0e030d0510030215180102030f0904050a0603050a030504080f0c09010e060406030b0106030903020709020703080609040611040902070b13020f0112 85
    0x1008142420b41c00944011181d400c1c115810350321280c60601240c83c00440480403285500785041c0022a01c00e0700d50124a40c0c0c0c0c0e42040000d00030002c0d02d244c0603008407100240e034043e14035180000d0b1424010800960f10344618062509603507070034440c1c0800d5462142d030724050890041c90741541c9902007511014191103183c000c542c09000b8080703808400c034406072550480c45010143c14040d10810700345601c040202e40fa03c100503050142090b03a0070b010300000b01001062405082e6603600c000c40070580400410340c1151003030b034500b1741c1c5604080d107003420722405110191180d0b10005a40c000d5a0f200d17030406041d00c8988e205102c0c203950364400980a031400c0c2d80041c040440100011841a0b4142c0008035000d000cbd408540340196102d00c8071041f03100310100540001c0c85100410510718000c000150401d002740b02c0803403114a01c44d18886503602c183d105010250380029031500700710030001480da004a01c810b5810700d1000f02e4000c2000f160705100700d94100406040c03440c06410b00b0b644 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 16454413 1250 16453163 16453189
    0x117012003160306150507200112020a200f0d080103050c0d020102010b0d0303050619080c0909070801050f18030304030212030c04030b010308030907080d0203040501050f040503010212010510020c01170402 90
    0x81071800c1030807400c2019080c3d500505007071783c4000c456035003d110221a01c1c1c00c018880d00603941c8ac201a440610303610001d4201c510600e0070410741d29918512031201c007208030200b12400b8003400c400f03000c90f4212803601c521110b040c0207020f81b89004201103a07020405610b00441507802c500c1450003840103d0040211480555006041e500702609060741540400e12a240c107480c04030592071808859641284144542c4050fa402602d000101c2d05140e01c4a0745c200003031038101c400164440280500f903850844076480a055080100310082140c0680d0942040382003001d940f40d030030161070003511041821035a1135603400003c04511280708107003c40b0011a000303610406596143d21f0401100d40c4142d50080c424480c03100082482440811340c0c0700030f10900e4004524141c5001c0c01501c494000300100098440240000503560f1002e000428144006030410680e66060000700301a2407c1aa00001150310a03044d15919036007242290441018403030908003075981da072002410840e841d41e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 16455663 1250 16454413 16454429
    0xa180503071209030b130201020f0a02060702041104050a03030203091504031a040213090b09010b1009060f02010635010507050703050306030a0f0b0f1501081306140117012003160306 80
    0x380070402240d80c1d004170f6101440c404d03400d60380406050810302c0c0e030703a41d0b500b000694004410004c040c01480c00c0c0d1e001484c01030350000500d050981d41c1c000901e11901c554070540258200081c0c03484186812103642054603c600005820705045850386143c4040301c00c018011035124402003019540c503100840c0381180700b060180035051281c903090302402c1d41512410583d60a0107205c108a142c00070740c1d6410b0040e50381d1040716407460f0030021114404001081401d42d540c81002041e280e603640900341413030b40c86960005206468041007806030640c0d060300c6040341d00d40800e025500707900100b143d0140b0707054a03145449403030740300010703087c11010b01000300b10002e40034a010070000390301d084a100d110440070214603640c03107000c48941c040034882c0e06c40c009040d240c0010b0b010b03220440e100d000140922000240d12005102148100c982030304050202c6900b10700c59014a482402401800c00b81c110440748041700840d0494a1800054480c9981c100401e5850800074400d900c4240200000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 16456913 1250 16455663 16455683
    0x20109140703020a0506040803030c0a05131202011112030105040b04020c071d0c2b14040302030405041d0309040e030f0304030e120309031005100308030f0a18050307120903 76
    0x46540d80381d4448030352004030301843c4060320015031840e005041c1e5007102d4503140a50f24550701d032030301118103a021a44807400e00c00c0c18004664042c030745074040c0b0042c080d281025480c4410034000540344141d01090031408c0d41c0320401c45034284600c042624115142902c01284036615000010f019004410508102e032241c408001040c4ca03801c4100d0340c0e80401d03a0300007101900c0345110850544107521920040e142003005012640308015180028030444200000b00383c40004240d0503281e00a07070b801c1d00180d0000c034040c0150300c1c2c03511134032450100d103512204c841d101d0585295103e01a01040d28412903981d00460301c242401c0c42100e0f00c980c5a2035a4603940d1406240180010b110184014041c00d03d1113000c0e020490004111500403200400900610b000981e41d00c001d000e0083c000181c04048000010000702c02ea0051070083c00c01440300b007428034080248004031149803108a01104840415801054000c4111010140c003c0940268214203d90903a060980d43c1c8c0010511074a03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 16458163 1250 16456913 16456943
    0x403060207050c0a0f03030504030b0a0609020a030605010e043b0706030203041502041d0405070504020c030d150302010801060507030219060e01050105031b0f0a030b161815050a020109 81
    0x201143c0d0a41040b02290802c1c1a50307120710306209003140c940002004100100001d001246101082e02c2c3c0c0a05886401728046454030802001c2c0d82000c003c0c04007181d1500d500780660340e0004c0760514070201c2500e080101c119140000034520700034101500f0241c81c42074070800e0000200110748110809101155911659500000c009500444098609052940c00580245541c2c02110202c0300340780c4207090b08505a0781c00680c0301601802c2140c281c0702d0160000b6081e255800600b80d0000040c01554941c070901403503030190307030b128400d0103420140f0076030a10041c1c0e04021428151596890196103510300f92900b81e162040460801100901c2d070a02c2004100040c1c101c0c0d86514131403030081c007030ba90707a035014540d40d003030000a948400d0720b41058101260900400c41701c6030810080c4903030380c01ca50781d03124030012050076070b040c26242081d01080013400c1d0300181d01e03480359001c03031301880f070402d07e003159480e45036189001c44000c0100c000f4681120324402d400ca2140e072500202c01304540c0e40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 16459413 1250 16458163 16458173
    0x515090a0311010c091502012004030c0506030403020a0813050910080d020f10020c0c13090c0803030106050307050901030b120610080f0c0d05100908040e1521030403060207 76
    0x3164504030002082c1004400b003140c1c06000c1c58811800315200c0c10803040c14020000e001444040c40d03081150340e20150150102110030039000210080429144e550781503040c4150560306503086240035143c10400d100c0002e60005600194076001501070781c4404400ca600c14280045078851548030440c0030a102c2200c08600500c000c070b03540c00302150342c0180b010000303988420030364001c016036402c40400c8025100207600202155100361007600e03000b0b00c0c001e00180400b2115840061b0b0311b603403002c161040000780701240b0090704407200214151761401400a14501c4010074441c00c010b00410300b440da590281d0450300d600c40c0004c0c140c484074074411142550360390040364203001f80925100e00207455080803134407140c0292100060003035412031030203011003000c01a4003114184903440e03102c1071849a0303115003000180701c1c0354416503480c0780c41c1282d12201d00190000c1600040580700c40322950f03846050700395082c5a506141f41e1314030407440060841c00f039540007520b01c2e0300014401c82004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 16460663 1250 16459413 16459423
    0x207140a060c0e0405060a060f03020c0303010b040317030c0708070c180f060603090302030301050d080c030c0a0c09020909040f1425060e03060a0b0d0602040801090606050f0607030507051509 84
    0x240e681e02d03c894030030004104800e0b40c00c25075000f6040040340e54107001581c0702c0c0d01007038070404403400d015140441503030030580f0b141d209078030078080c0d004040350600402c004c10710f000c0b5100425010042c218181000a08000d1007000e030000c2c0203a074000f60280821009400c06001400e416444100244644e03410902805088400d035500c607140c0500482e800c1d000c0d101300712500390580d0003541560300342420b015080c08030308420794583c4400c0c4414803120380d04200400002644101a00400c00c5514000c1e1540000b50010010240180100c3c1170580f144480c0d6580716401540741c400b203071818201000549a2048005031600810058599400181c03100354002204048205545075440e807048903610700f9400321a82c16004080801e80041454201d0100150020038900c030365030450f42c03460101d074001c0e4041c0210780d4468652a0600c41140301c0c00f0000d01c4141c0c0c6c05100e0343c00c41c02c00107000e481800d000a0501102080040074007100700b19116645144000c0841c140c03d001c2c1d1401e07a56 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 16461913 1250 16460663 16460681
    0x70e10080708090115050603040204060905010303180603020438041202121b060711030607081501031a01050a05040b03040501020301050907020f06010e1503010603060b0a060203070b06040207140a06 87
    0x415400c601081c21020140300b404081020010902017207410982044016030000d44107a0780107841e503e0105440070b8511a040c000d43c400d0301c031440814090f07041d003001001c4a40c010000e2610500c0100302c5592124001d444014406407525003140307400802e05446035000d5101c101c04080403402180033b03658a284d41211900032070700f07000ca403518024010794a00401042c01c442e00f4440c1b0100c0c2c03080c200303100540210b620a40e56a0460006000402c1c6000c0045030700074001035110091004502081400c40910b0a080c40e05012040080e200c0ad0000710400c0c01c03050401000282c2840030500c00c0050354040c2c14540c1400d0b90b2400c141c241a07000c0c1d00207000b00c51055001c500410a02400060703901c1c1150120006040b0326841d1030500c060500c002008620008000d016489a82e0b07000c0c85444040c611480c00001d20341061014401e60310420341004056510401140001c10301201190b0340c003440491380981e983c0d08524104031075410b1041601e5842c41120f4060f410840541c00900034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 16463163 1250 16461913 16461917
    0xb010b0414030106051011190302010902040e010b03120a0e030109080403030f020718110d05040605040302010e0706020a0b06010c1208061903120c0203010e15010302100c0308010e070e100807 84
    0x7001e034000205800c8521a2103402c1e4880c3d01d080c003600071103003e120003540b00850181036a8a60405482840f10340c0c002600c201d005035525501201145414841d03a0842c1b071003103000704200c3d503940022030754905000700072070900040498100302c01031003455190141c81001d8000c2c05450101d1a160702e00b0742044c00105c011604105240020380d1001a01400301c49119000e0210a50741a610000528008044060080c400c1008810050017405147d00071841204000b50300d18260034002e08644410b00143d50980040c0420403a20f0740c0050940065a0000034081c1c580d00e80340e00590348610382d0302c1e00030140c03154144050300c0c06800400c0907103d01d4040d83d0441400000b511a08100c0b580d601009100402200045680da0703c20319131010701500c0036000103212032a0005d51840e0044000e014190108880014011810301d414001d2040e4440c0c100301100300c01e02d82d1301070f1400c00e05000b40303a0b400181100041c00300d407041950b01a1b460015040107203030f0400c404004c00101d030843d48800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 16464413 1250 16463163 16463189
    0xe06040b01091104030f020604030c031115040503032a06010803030406060509070507080307090f08010606091403060103140a020901090c020606030f1020030f0103020306070507050d05070206070b010b04 89
    0x28041d4458003960f840c524500c44040c0c40c160440d9907240301c681044905907040f040900010000842003000000614020500342011a5806003044002608028010f0071000d041c441008a51400410742d607503142484107641c05058000702006104030729845015880c1305403000001e98140100045000d04d028200511a041c0c560b018002c41c2d1405840c7e440000340c0402040d4040b0310040042c4d41c01100c145030809005545011142c1060165040031680b07964641041080503003100841c0010030342780420381c0c0030b000542e0000e929007805200140c50000c40b00708241d00488148403c50200368000c1c2030760b07090358486140100502007502440d01610900002c158980f030001341948503010350400030403a510050380540003503d0105640041c50903401c28400c0303481104d0380507510604c50700c1c0c043c2040e585035004044c60020050110300511004020034008242d000c100c02c42c1810150801c0340d034821861000c07a50354480c082d80a441e10055100120303802a420005000302c0b250f62402c81303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 16465663 1250 16464413 16464419
    0xe03040b131205030703030911090108010606110601120807080f130303080c1611041d01140f040507060813080304050106030506280c030209090910060902030c0a0c02040b040e06040b01 81
    0x1142c0b9003002c0c502501c2948203001481c0040d2181d003006030404d01c186c0224040c05111008200d914030284c00900b10380c0d44850051000c7c540c050603071080d42e8080f9000707060551410300076030a0204013002c060410000012004103000003201218440b5850540103582e450418005050a5810303001c1140020010400300300210745030015140312200c0001c1c00241d04e0080e5451320750742c41459100940013504c1d0340340500c9052010450040d4421541c002180080007225482d0f00c005005010b1010071180c502032101261001036100140c5210f820510b640f03840e0025a61407461000764003c00d2100000f0800c82000019089041241d00c6101101d059488001d50580c00f0707000d1342903210a200d128940180d040178141c00240c80300203035060051070070401001044442c0e03000c441001c85c6601c814100b6620004601c50100180f0f403001c01107003541061010039060f88140c0c42c0120802c070460315130030b0643d50b40b548940321078800200104420484400b4503511080c00721816501780003044000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 16466913 1250 16465663 16465679
    0x406061509051c050f0a0312050714040b0304020103140108010f0b03060606090f0d06050c04060206060d030c0f02040e0601080706030e030301030309051c0501060e090f070f06030f0e03040b13 84
    0xa0060b01d800030000728410340e092609008898040d4029942d6108a800404a840081c00005400c6001c1e5582484007242c0318020801c0e580041c0c940c03410817040c10720032500c6d20505010303682910400c001c115a25155400102c01a212020b40f43c3c2c103c000b004000a50624150300084010f60406001d10004041600f015100c9504072001608000200301c8812a07180c0034070300c0011000002c2121840b22401d85a07003089402c1241c400c0040f07400014180a0250108442680310034100c81d240101c0c1802e64000b032180d80a01001000020201400000c6503603a030400035028484904445440d070b5580c50856540609114400109140c05241a40d00e14080126816640c1503242e801a1034503140601c003800034458003c3c8840c0c00000d209000154080c000e4000501c1022143d02e05802c202c01c0581c2486411100e951880d4090403007000f06400302030b1074100301ea00906001900205003c0040c000d80140942c444290000047c0450640c0542001d020300d0b52000f801c2c221441d071030743c00c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 16468163 1250 16466913 16466927
    0xa031b0815120a0501020c01090b0c03011d0c190905010306050105040e180a0501050906010e0106030e06070305070509090c120105060a050301210506070801180213090b06040305030304060615 84
    0x1c40040280c0300910700c60141086407500701140700c00c80c212021008251a00c5089800243c61030740140d4503401c080b03007801401404a500015002807040c515450081c0d000010105502843d06941c1100001046440d400c4261a86076004040190802415030b038000c0143c40e03d402002e0200b4541080820554821015103003914103a404d00c0ba403e49a40c20501c030300300e8000091040c1482a2030b070301c00c00a502170103414001d81405000780555410318031003070325604058211804043c6040c180d49521a0002407198200515007000100d0303855500c000c07600c0d0703c00d9048860300000c1220070b0000c10010000100583c0030400d02e038110300e9032604100010b038802e60820700300040080c4014048000c100d456605d4040320800d100d40801000e90303655060090444001000c500941e004110030507080040c80320381c10507640110328107103001c0e8461240b64a00e0080312012959010480c6176502c030441210040c0d90024110707070306c03860a440c0100250565009020700005041450844640a060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 16469413 1250 16468163 16468171
    0x1050121080d0f021309050106020c060f0d0b0111010c1e02010b011d0414010b030f10050102070e0c040305062805040209010303030b0f1002010e150c03010303080a110a031b08 77
    0x320318501442c0000801c00351000c8001d141040e58200300310a00640c0c8546030300010543c00c000814250701d03282c0003034105062580c00501624003004500d032020700e40710841e54030280780704001130041030030001240c5800343c4407080740b070544c43c000300c4041030307504034504407000101024070240d1100120012800da6040e0b46180c1d000c200c00aa0700070301a41c000345000d10010000e000003c5d42100300d01d8840407031a083c0d0141b56444400001c2c862104056560150b1000300e1815400b04145000c00003503032034445200d03280c5503018103004100c0e410426402c030307002941c11804541c6142020b60165a1640c1c141d40340c202e031550215503485a407200f60244a03c0f4071340090140550b40e01c3c5803002c2e0017615008220b00d0380080742100c030506998407080408251480341d400007440f92980560640b5040c40300b400f2764640380f0102c0030400601202c20490341540e0385460a40350548810740540d01a0104079040124034002040511031039078154003508605800d81c035592062210000182c0c0c40e0a002e407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 16470663 1250 16469413 16469423
    0xe010f0807030311010b031207020310050609160c0204050a0b030d180e0601022a010e06070503030105040905030c010c050904060e060307030201050915070b0a050108030301230d0b0901050121 84
    0x30040001c280504034100c115813544001150002c80440003d0a20042a0414855410105201c0300b542010402d4a4001090010400c42030038110005201041c000f80301407502410a524403840c18803035000380c0c0800c2d0780907005114a08290121801a0a61011107802403083d400c000d03551031310501445020804010403100043d042c00054448520001c150506510032040d401c0005211581c140c400303c15030641d90820100c690000402038005802c2c0284500b005106102c0450008002c990445004890001c1c00015625000d400c501601800c0380d29540707440007841120750040010701400004590811003144c86401c01002f2803000c0d01e5054250707100220500043d40244000d000c03014000b459080503a080050801441d03012820071510801c02c41c042c007280441c18014180500224405035007158109681c90720304c241082d030340c41400311480046509989a01d1502c0d48030030b40126940c0d24600c0c0c8001700901074a0301780300e14442c00d1140c11280b00080c082c1107015032010741c40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 16471913 1250 16470663 16470673
    0x603170a0e150408030705070503011107020f0d06090b0903030415050106020c10180f05030705040509030a181a0c0d030507050a050c100203010f0306050603120904020c0a020405100e010f08 83
    0x40418441441d8161030002c120350310410002c10b441100300040d10f40184540000c1a80c60300340807d0509581c2080825030b950207081c0808801661503080480c0040c0083c0c070720400b00c40032400c0c01000f600800c98054481c600300407c0c45a070010120003148100c1c007407001c0c04880b0254403040d0301200c201b4828100180c00c1580b00c502c891074004210108603c0d949000c520b03640381c3e00d40384410010715600040203042c1c174280800c5117007411300a240040108a0f002c10140ca08000b6030f0362603200e0b44520501300300c2c1100c00b07601c40182c03412020000d45042141c100d03100f0700022074204030340c3c001070b040c14081c490309a00c1c101c0b01e071003030003094800c0d11280d413003604026401c0c0c4151800e410a0040c5070984c01009040003040c1c1080c8061402030211000f034281c4146181403440c2120806403815001e500501c54500c500c0403084102c5003140e5054a00680e10f0003030740d02d814105022a60025801800e002c20b03c03144805403400314042c2c8071a00304aa0950742c0e16426420540e25500c1009550340007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 16473163 1250 16471913 16471937
    0xa03030309020d02040f140a020a09051507060f0501061116120201050c0a080304031107060509010e03100501091d010e100213031704060e0102010902031b06070206030a0603170a 78
    0xc25005441c9642c40a05814482a00b0344d001505890500c100460000c1d5241002d004040ca150403040e04640326136001c52401c19541c0e17009000b800240201390141c800d140d280024408c0c110100c818113900f14400b00700c8242c518803602e024007020710900c40010850090451451400300352614a0854107000980c0c907458089140c50b41018904180e040c014207000741c100315241800400c84280c0724100d21952441d040c41c01411000a81315040d295610a100601400380c220085480e80306090900740c4007030045100003480c21f9080501c22503050308041c0002803600c0b584c2c02c03001808024800c080c41b03c02c010b6011a00329849099a1070807a40040114250300b0180d900808400c030010f4540a145500c80d11040000b1680307060b14a407412000808000d403c0e07002c50a01c90340d120900c020700480101c0d0f000a65184001001e004c55a030b051940b550f0355560750f00c100c0b140b203540506102e4403890101c1c001c400604407440103564802e0b182980303500c1071000004039054030206c1c4d1110910101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 16474413 1250 16473163 16473167
    0x6100b12070f03110f030106030c050304050601050d060207050d020705030106050102010e070314010204170c0a06031b0f020c0307090603050105010e041509030c061a03010b06090a0303030f0b0a0e0411010503060a0303 95
    0x10300b101841c145960b07074600d000c030300f03d22600030b00103295084403881e500c0d4507203000101160a0070032010b04001c000e001b400300054000c03441504580c81119112403006090410f04000e1155a500034060b100c2d400600c0452030b00400d61004480c0308034020000c1e00d9884005a09a1b05815203966068010400070302c00a01d03d8503401890049120005080507180d0302031200039a80c0c0180e4000c69030081207031008a00d04040108040c2220b0700c0d0a11624038209141d03001ca6610800220601c4000344114102c588204202e207400a401400c88107840d035601401c4d030081074103000984003942010008244803810300700880c02a0b0b03010b0041e807140c200d078840400042648141c12070401503c82c00d50804a411400340f04090710110308032000100c1842c01301800c40d600040814050320b01803110920075540c090100c41102d0305410b01081c08440f00c150040140210032a45600031540040400da10030000b124512581c82502d440c080b803903400005440714002183c45a910401070401880040c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 16475663 1250 16474413 16474427
    0x40504050903040b030106121506080c03040218070905010323010501050a1806030e010507020c15090406051c0302190503090103020706090f0b0a1d060703050705040f0806100b1207 79
    0x2900200360b03400e00303488508400391907000307a10403000036046c5003826442c0280c500c202c4011650034004103800c9864240060034000004080c40400c2402000203015034a4190001ca00c96503010402e0b6424a05481c024221303800c14043d40b80000d28019181c0500000ca911110b030220f8000700d02d903011f84c600001100c00d54002d1880200b00703c0100c240a036001e00403d01400a001c0545010621454640240703003115001031440c0b0465020408027440c3d5162810b04056040a83c031215650351b4a07400800d01819050740320903044501c64500310b2412500c241d60a0941d4882c2e803d45484504030781781101141c14001001e0503542041003401b0143d806540100040e61044001040015564592040e090310140040d100251803200308440a00180b288a02c0c0081d0441228020304185c01402d030356174001072040092655407400710303100c030340501c040d10010101034000d044510340310b0018070f072600c00c1901ea0420241d0141c0001c18001e120400741c03901d0390590385001c201a910500100c40d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 16476913 1250 16475663 16475671
    0x15070203030d0f0209040c0c020a0501031805060406050402030c03150109050a0e030706060503060106020115090207020f0306090706020d05070203030307030f1b0306030b060a0321031811030f1204050405 89
    0x52000300044000440c190142c04003950f0107900060325465800c0500c02650070404000041180c2c0c8013600b80141d1301d008840003554000c2c41d0000d0050030020183c000e10320011005003040c8514010082000426049284141d1003a0180c03038bc074800b680e050581e01c02c15000b050000321505c8005110211042d07004582c844030302040449e0102c40f0b100c016003540d02c0300c0404d0360311680700c0a080c0314504003081090700601091008001c900100481507444400383d01404100580029030701c0191754441400146058008003a914181054030751150303580118481c1c1c1d000b5000c1c0d8608000000d0080f4295085180c000d80910b19582d50000b0850003400c442040000040e034a03180d0820020034006c030340d03c440364242c0740011141d055041500130120000d2034a03100702c0310848140001401801024074550b20820110010095080b0503000b409828030340c5011407081c0846001444204441111102c2c01030301079480d11458800d04d0b07506e641d040346021101384420030041125040540c405684 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 16478163 1250 16476913 16476919
    0x30e04020d05010e040201180b0412050109020415080606030105060108040204090f0b1906170d050708161101030b1203180303040506030906100603020901080705160b01030b0a0c02060402150702 85
    0x16101d154072000088400a030030000195480c1d00030481196041556070400070382e15000ca201042c541070705001c0301e200c4e03405030350a5100b10070251810007800350000b901c03540c1e0007402131110401010200400030402d220342903c81c460b050104003141810f00c81c1501500d4107135607841055032240c01b40009003c541004840c0320300c0c0c40b0210030128148182142c0a09070070782c80d200c2c0700d00c0c0219550095417015007048540070f00c03410509004e044000341c800c8a0010380d050190b294003d500703000901d401a140250002c254406a180401c0350b455181c19919501346c90400003d030076001801900380c7c1c43c6c1000340303099000b0072100c0d040c4c2034640c041809210004040b00d10303094984003c10340b590816a142c0741c5035440401804400590350700910003500a901e021030801c1c07417100001784142006004030742032001c000b13040170044000d00700c0e040f07200f0341240c18080956503134035000c00f1100084030804103c510301030280b0080c5102080c520301540c0c00802c0782c041d1801c05905005254041340c0100d81c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 16479413 1250 16478163 16478167
    0xd02070f0305030f37170f0103030807020312040309031a070c021210020d0501060206070809070b1305030a14010c0903021e0402090901060903260d0e010608030f0403170703020604030e0402 83
    0x9840c080103905d8610800141c440c2da095a114500a40a0000701d03d265034a0101c07107041060003082c10100d20304485d01032815800c0390700da918041e42182301c1c515850351405440300c104803d041c1c1014030300d002c49224820848450001c0790300b00c0364000080d91102c0010765081140030161a00d9214100000000c00030b0321905082c1d56052401c903030000c4000e009444c0c941c1c0c010482280c040c400e540c3e00001a007030040f0a481c1c0748510f0fa84481150003180540c0002040711941d450058602101904028040320400499401c0c011646509100707509217542c28113002c5000d040c828080c44085030343c044c10700810389409200e01241004400400364110b50709000224559450b100c0e050300900c0c041d2903c01e421415824611201840302c5c0c50007410390000c20382c1c8154801810210340d000302449000107041e41d0945141405404031b83d014110710300c00407402640f03450040b8000d0007200c1c4030341c1d4542c0c4580e001030141d1165014514010b005600400c0000740441e000341042d50090400400c018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 16480663 1250 16479413 16479457
    0x3091503050603010e01060501050a050304031b14070605090102100902030309041d01050a150509190204090f0b0a080c0910030f0309031505010302150702030a0804080d02070f0305030f 81
    0x441001046004140040e0311542888843c2c1020310403008425049030090060500b040c0004e0302900c2410640e02c20401c0000014060521880500c56410452460003010154508113240140c2c020801c001c104e0241e4540001c0700d60141e821a1100ca4042e001340c8401038045d0fa40a008015081041c1e0301070000f000780c140f156a0328880c0150031413581d542c4110b00e4031004e40041c00c4910060844260a1900307a16a000c0ca070525240c004840741147c4c16552507403403410120104503414a00c51105001290220740d006103608100403812400d541009400060410061008500d00c100092a000282191528201305808540c0a0792070004444000c0d0b130f84d07a034042d000020500c1580003c1000f00c043c030030050108914440940144424842075045d60001022569074003210030596100244080841d141448182d094a40012600d03846903991a034081c0c0340c6e003081c0e0094006014040300410a8501c046a071015683c02100460601e002c038050200740340e01150034002c04400e200095 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 16481913 1250 16480663 16480679
    0x20f0604150f06120317150108060607030c020904061b0203040b040b0f040b04060c030314091b0111010911030c01021209040507030204090f0b120c0d0b041b0305070e0c09011b0309 79
    0x426543c0c2c425900c584040e06d45070030b4a040030380b01404042e2007105001c81c542a17130303074003e2201d42c12000456403d03039510110301d02a06c0c9948951402504a01000104024022660701001d012003100b80860381c424142c41040b61203128500411071064000c0c0024890a800c4602904440d2035400c071030342c503164030b400c5104044c2d0850790240c40042c504500140c101039250041621a0148070300c44442810045c130801d495074086a0800549124140c0f04200c0d61300c20000c0703481140001c1c008000030300a034203204401d0182e00303581500078400c2030f40c1001c580d4400160300c010b007032801216500f4124400c04020182101508520400d81c003444041480082ea02c61114a0345125038009000c3c14900184868030701c0c103400e20a8990080440108152289601c210465602c82d150900640d50391601740d6034110300810221240c00301c204003104100700000e003003050780c05c071340f01e80c495541d150303044450207205402e0000d000811100b541d00703004845902410b086446402c115003010344031120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 16483163 1250 16481913 16481939
    0x70b040b091207050f12040302031005090102041805010806090c1305060607061d1612060902040e0303010b0417010204050a03030807110d02030d060504020304030905190b0a05030403020f0604150f06 87
    0x4161040c2d00503108882143c0320800c030b8124515940f506c041e0030f151840c3c000940300d42c0f81c04400c601c0551200c1c001000000e00b035046a000d4101c0c010812400e14221761004c000340001d000d207e29612602010401048000076458031070107009041c182018288d0302804041d2030081c1844d500490180103031000601c0c2400b41071804046074441050f504000a000da18003002e03540703161615036810000f80308481429060103042900810049030360310312440410018190302240c113055010101c0013051001c080c0d4000c0c01200e81d104070760380d0402d0083c400701e800c0f0700c42c62103490b03400a81e1810400004e401900844c1d8000c030941001c03441d42c6100d007661070400c1390004100d001038000094a82da19213407841860301405c801d4400710705500e440d54015145800c14015188101507241b42d0081000f9042030070070103880321416841e01d84400c000040c089030419101100903015168624610443c0051210712550b0040c0c1215080c4001c42e204e10010010704851082c180c0d15908007003040c50000310 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 16484413 1250 16483163 16483177
    0x1b0a0918050403080609060a06030209060403020301020a03020a08070e0f040504050309030a030921230a12020102030106092103050901030b1804021f02100c09030b0403090801050606070b040b0912 86
    0x203000c21585082d00c0d00412075440100828030804c95030f4103205040e180d00003d00281e031110b01b80180c1c0c50240000065181c089d661000f50316600001c0d0050301035034550080c0590340d80c6510b0b03441c050385541d1402c0e114504e00c100c03403540244601200110501c0e0a801481c0c0090003401920f00e86000540424200010690254081801000304020349042006403100713038004020050400d4040c0d940d8168400155458132510150070802c80d003009205201c862001580309211141405000030081d001c1d4000b4402c101c04030f00300650004161034074000011507042c07144100040304a480d50700b5500b5405c520030942c10199908880d400c0b540711402c010200a41d2021504514941441000003c604841020a603500020b02c1d0507040d80d000103054081914001c800b16103088028801c884548081e48060560710745502400b060540045180065555580c002c1c022981c814091080707600c14524014034040e08000090045041c0c4080c3c0c1ea0029481c2090f642d0203c05800d33201c075540c11541e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 16485663 1250 16484413 16484459
    0x1205190216050c0102030901051207180e270a020d03050d090f060b030f06040f030c0b0a021306050a1b0501020c01021b06090a0c09020a02011b020102070203060604051b0a09 76
    0x56810410b210041000503080502480158544480900002c005001c1d40c42c44100340030f07070032002c0340000d03014070b4280e42c210303c2003104011700c59552030140201080641d042ca10480580582c58605a031020045403481c801030000d00d082d504075400d1020f40e000340c1b0701c150308100341403000c0d005c405103c0c00b0b2010050b000e0000710340c0100e00b508150007141d035180801d6100394401c0314040c00c01080480c0180d44a80c100f401070524030001d0800341c034504000c0078010000341c103140400c144c40300c00d80d0252045160301d40b5042c142903104c99041c3c42c240b0404000c1d50100741c040b0201c1102d000d68a80720688144070344000750a20803110301a42c04c0ea040048101100c07419480456064141040700503031040c180301c01040d03465007548500414000a01615100c2600010800b0002d4002d4115003108458003201008103803407103c00034001e4012000882c032038019840816180e01e0f046c0a5140594402810100241c0e09848400d49aa10840020080c410b2601c40042e807903501e1009241c01e030b1041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 16486913 1250 16485663 16485697
    0x50106050a0c1209050a0807030203150603071a0d060e181f0209030304080a03050406170c09120a050609070513060f050105070f0b0403080a0c05070b0c03100503030d0c02010e0d12051902 82
    0x510405042000000d59002d80e413002c4ac0410537a03076000140d60341201e100303a01030b000390300f07202040b540c841c03050a82015049013040400960042c024001c0b9219804034131103103030140c102d40d00054031041c100900708048101481d62400e4a20543c0c01000e1202c8014222482c19980e05221814140002802e401003840401e007000496009107a490103500c51960b00d0001e850301d580910414041c1a00c081e008507030303c841c40744086c50204181080f541c1c1081c11251030745803d00c2255614000341c09a280502103841c96030521010501800b0300f9160007110f0000c0441c2004011945900090802c0c2c50741007440001d28007003840460414002c40c000d560710f032004e103407040301c1d88240c0754a2620401080020004040416554407030350303800410907500b40303580e40c135503001e6100440099081a60700d40000035000100c910f40b40c3c0200c2c12521140c001384008680921070a032100302c040c0381400421003103c2e403118151801c2e44541e030311189020034040d01c829544a02d030226004191402408803072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 16488163 1250 16486913 16486919
    0x516060305060307061205071103120105010f0215010b0706060f0e0621030d050a0e0102040b030a0b0a030203060f070212070302010c0e0415030206070204020705010c020709050106050a0c1209050a0807 88
    0x403500520b54805801c0d0000c1600343c1c540000202a4084181280003140d664400b15a40c94420394080142e503104100301c070b032524404030b41d603160b41d41e0078071607c0e003c03600446a90401d180042410b42d2556a0305050010513841c01410706001d0380421030442e207070342d0368080c01b14090040300c44c018040d100e040c00c1080185810003d1000ba03030310240c50300d0710710300441400d0744d10783e40300208466000d0300020011400c3d4075040c00a1000e4455107a641180794004240031031280c1c1c070b00002d18404d2600410a12182c01d06a082c802030702c0f151301000c1d4058000780b0003c2d9581c03581c2c0c40926009030303662040725401804201c074002c894201e18412001030b5101c00c06800c0355540400601180c1c076003190104015028000c3c41c2d8420300352031000a003d52400306042007556107075415950b0698002c0001e00154106801c02510303168580140703641540b40600100d1079610034000c4c1d030540f54541c3c80d1041c00b89000d4442c0007440058082c844208000e01070041141c3d200c000d101d0000342103000003041c040782 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 16489413 1250 16488163 16488167
    0xc050f0601030506090709050c2a0102040605070201090504050403050313110409030504080607020c01050d0b060903060408030f010f030b0601030b0d0c08031e030c0403060504020102100207050604031209050c040e0a051606 97
    0x10140d402a071f9007d090030248942e848003034040f508041149101040302d40030401402041904040d4505500d500c04100000c5654101c1d000303240c064400d9885618007a00c400820003195420340c0d015001980c1440000c44a20503003a03840a928002c10442c0c0c910381d8420005425a0f0a000046000940103e01004480400c010b480d42054650016209203181a00000d0640c041c030b200d000d04032030711000d401c1410303140c11701122024840601910564613044c10148006d84c03059640303650208a81d000080c0180014500805880d07000540c401503441c0c0130300440141000550060784100f840742100c0c0050f221141460082c1340340c5016589441c48911440d01c801008010056102d204004102081c4104422907044d0b960000e40050700b6161350004034900207104c1d1218056500c0001c030241401400541244214400c1d41c1da050a800100201801d071461582c008120b6072101e80454010b1901c0d40100071900900012210604c04a403182e40ca0041301441d45081d2034841074040c8003c40d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 16490663 1250 16489413 16489423
    0x20a030b030a0506040803101a07140d020307030e040605060307020604020109050a03030e090903040e15030705040b09160516140c010c050604030806031002070803090106090608030a0c050f060103050609 89
    0x32011400340c090b00c041916401d0300c60100900091420000000059030180b180075802d01800750f055180200101401d09245141e0142c1e0054a104125482400c58014002001042100b482d80514101840f540c2c00741c0e0031400c070000036644180c50781d201041c1031b185c80c809103116050560040031707a0b050600000d424074190390080303405401c10740010f00210303801506083d0f01e0141510044501e41c0c076604600d007140542d4101882100035a0188203180411140743c4020b400c0850035294601d99500400007214010751150b500a0075440001d031120702400ca01c101075078840c1c20030a2410a4002064503503503145a0111010902da0081d2840791104000c00d4034a06000c1c203005030f00d40003e443d140c1e515880200300508001e01d510003c1d0064506114440c2c0103034844500307540710780051608030701d9500212009580c540c6405400a0943e581c1d00405081f280d00c10051843d0850b50703c02265503c400d50026030702d82c41080c4011070b0301d4404028103402036006401a20712801c004102c2c50600c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 16491913 1250 16490663 16490681
    0x50d0c06030e0a06021602090a0b030c060309011503050a0303060b090d030c02010207030c090e01050105030d0c2006030a020d05090703031b170309161e0e06010c020901030303060911041203050f04030501090303020a03 95
    0x14500d084100ae8440d1400520341030700003411201c0c0750726540c4200310b0a000d80b2034200070501040a189001080010004d902e0300190712072b480c24024241c8515480d1014041e180c00c8940c400c045d80958008a802100c280c4056401881070b90500340e142d0721078075541101648604040c59444198840c2e0030701c03c1c4207985c09403004070080d01d00c1070003211008114039452500074091030302003062030300e109914000c6810011000b0740000c0d103d00c0d000300320700b00075041055008041814500040c4c50701502050602c140c0707515803221421a0540078244004503045441200c14000d000e445104694081029610581844d402000d1803d981103c0000041c42c42c0c3c840c1d84440c00301ca07114898501c0e9a0b103420309580c4400d140007501e54440740100d0340d00042d20741c00707504104c0140002c030034141d01d5000030041e100c20a40a101106624400ba48140f0641c400e030004110100b9038400000e00c11401410100c0261511a08168598071500e0844503111011000b003540001c03014039541d058041d0400c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 16493163 1250 16491913 16491931
    0xc0307020d02030906030c03060d0510050604050115020a080307030b030105040804090c0504060504090c05041d040201020d02070612020903010e07150e04060302061c110a0309050601050d0c06030e0a0602160209 92
    0x24500004045056804040d00e0047d0f00d03030300440010201d8450858945065402400300c03500100c440c0d054030000c000c01e940440c011820b14001190003800104034150341c6016500601d2080c010381c403100096080680480c08054139041c406035155801d005580c040c0e405100080d580702d2812562000b11415000a002840402d00c001c000054222003510b048907002240459000d048560440e0640702d29003080d01040a10341c50341d4901d1848040c000d00c181e20070f0302120710341c1169190030ba03a6040e451182c81e0003e01c1c958110400051960050b1000e00000b4001088030b9003070308402804d00080d900010881802c0715488601c199129502c8072107410107540400c541401c0d40c010030907038890742c0400f058004d1806008640b00d40c41e9405505010240d440d02500d13030404100c0240038000b02401030310303d8420701001207082d1401c464003519503584000c2180b44a80361013020f90180544042800c07150140581079008101c00d030000301840c206040da0113918131590b1040104031034000e804249 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 16494413 1250 16493163 16493167
    0x5130507050304080a09050402070311010605041b2604080706050601091d13081c050a0e06040b09030c010507080919050622050708030405031209030601050f040f050c0307020d0203 79
    0x2800d5604601265006500040340e540d981481c2c00094907050b2555002e1f6820a10001e0082c0505a10003069500d090780140280201030b52241000266140a42c43d013a010855403900d1035035034000e03c40000740030303074583c0352030740066035514801914842154103460304400000c15600b08200c0c2c0c45116403100e02424071104083c144480034210f204000c030440c0000c04140c011510b8403c02e10b0b02034088541c00741200c2c0e55600c48010710303258a401d030052103004600380b0700400c682c00c899005160b014603101c4018446036580d40c6402c201004040c11900c000c6c00b00300b00e04480c400c001e024091142046440d10f8110f0305091002e030345429003160b401920880e00d904050002400072500942001a858080c2d055200b0f0300c3c900407a03085ca12a00408503c2001e1001840c020084040c00c11580124295a0030315002900b0040c0351044d01042603260b00300100610041c81c000020b5508031071302900005800328440e22020481c0c1c01580ca901141c04040208003c10f5170400c80e1703002d0402c0c10301c003840c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 16495663 1250 16494413 16494421
    0x31e0106090b090909030c120c0d0206060612060d06050a060303090b0a0c1103010605060c07080d05030907091d010903080402090703020f040e0a1401120c0f0302010c02040f0f1401051305 82
    0x2140902071180500c0c13288850801184c0c890604105981401e1148030560b00881c41d422000d102961003201107618902440b290400d0450011900c030b4482c11015004a03c0d0480d0800b68443c41c4030000c00700c0341d03c108440c10040206200d40724003403250307207007090010340c150071810058040071040d40450090b80c1d01f001124081a442518003c1d07440c0c1c018003070300b2050b841d040064003420580e040030350061004120f01d2140704000500d170741111444020703100c0c0c40e61281c00c12541403104480c02072855000389070400c1800e22543c44104209659895408080344041245080d64034542061b00005c90980502081d8680000a0f0b90030003124281185000d21002c52070056021b180b06040c0d007032200c1c00005034078001c2c9130405942c0a0000c0c4454001d50307102e03030f8044103171100b070081550034911900d40400c401c103044e2941c20640ea016141c004142c00b8a5003007101034090a41c0104025490303091400740d00d01c0c10f0060b02e0b08102002a0180c5d47e40c11b081c18402c0203031000c0c036a42001d0f82030501344 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 16496913 1250 16495663 16495679
    0x50c0703020c0d0203120c030322030f0c0501060509010308090a0b09010909090c0b03092a0604050402030a1b110c03061611010e1204090c03060807050105071403031e010609 76
    0x2503107120003510405101080384c00001c1c2001042084008801d100180c500c0c1c1425005c001140303d0417006110410000900c9541c1005886520000b0082402d2800c04800309000f10ba000d00384a218000204104d80c032040402c00c040001ea10031562801c02090f96031042c9005a1228003801e0407820070740c2010303211400240300d05502e2145c0000150348410201c213102060010310068040b002d44c0a5582c14a601e08580ea101c07115801f44549030721000784ca1210031400c5006c0c0034140c0c01403220342401d01380f204110081d800902410621a07032103005084806908c103140c03100200c1c1b030f00c5900703014041e13071101c5050110001c1d0b454840c0d00103100308181ca20001590150040192800c102c3c045460905d440c014480324001d440180b1801d20303562080152100180160340702840705000d42c0074001e5013075064805178002c0c410350741c10034079050203194451400340c040396000c1c0c0c214580f5640b2003445242141c2c03003500c942d9100164103003806200256500c283d4014566460b2010b0722925040348 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 16498163 1250 16496913 16496923
    0x70506130914040b0a0c050705030c0d0809060106080103060b060903100b0a0f12030309030c0c0906051002030a020d180306150302040506030a0b0402040f020c061807140901030f1b0e0109050c070302 87
    0x50000050b42d206071b03440c2c40a115606454140307030f104085a98522440384541c1e51455280c1c0082e001985c109c0c005815850045000c2e4101c4409444198060342150f46148c0940035401c94183c00403000d202d0041503a90404c0140051240c1102c0054403000510510007003001c81d81100381c9002c40d81504002410742d5040700340386030390903190000d4102500e00d411036503031241120240401080310000325055000d984200c0455000b19450030084180784d40c1642c070381c01041d24203800742e000700d5520080d141c05065032142250b01c26150301da829889a480d41d00329400100344612134410400144110300341442100d070454011001000200101ea8411684250040c00280290345542d099041e808103074050315422104007041e00d10510b0041c0400a4000d00b080c004190381c402c9443c00202044503000c40340480c203001e026400c480e82581c45040b9040c41c0c2d050211100c60b00003412a64051083c40d01c02d0250100080100a40d45001002020743d84058540060780c0e1b01088079400280e00094 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 16499413 1250 16498163 16498171
    0x30c0d020d02040603020a0e010f0501110a121e020309030f0a020a060e0f040507030b040f050112030509060f160302010b0118050405150306130203100e03040303050c070506130914040b 81
    0x5201403007602510115000d4141507000035040604140045442010201d400d41641c060707140d0784020541d07810046034001e0240408104a03040340e2101008107201c2c2402ca035076400c0900748005101035848035160380e9a50408d4101c016007012600001a00d0f040c0139030840790f26110000c281d101c005800090506003a440303410140802020560071680729000d4503c6100b030024000c100501d070510b00a40a845070794401407159107049036100619100d8403c45040e2071301003400810002d00c070740e4207686075840800e00550205041c403e0a0003103078144010442610f0901d03070112820346514000c0d0030b440c00d44038101e05100c1010701b01940310a00c0c2d0040d6003196011140402d958440401308c0740b08000c040d02e0103802d40240010005c1c10803000e04c445c3c4440b80300351304844503c01e076840c100c0c044501c00045010250410042040441d104001405c0d1044815095540721544c136070000e240b540c0302d011199080e80d020501040071450500c18a41c4c0e8480c2408054800c0c0307820780e580e00c0255030043c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 16500663 1250 16499413 16499419
    0x90c060a0f0201180614071701060302070807082a0307050c0105030414060103060b12030702090402090705160309030210050c06010501050a02160b03010e010515030601050901030b0303030a0603060605030c0d02 92
    0x440c0100074910035041442d82602c1c0c070052490a4000341401c20282c6500311741010b0400990011810603803180390101c00d00248864041910307400c0440c220069800305400313607904442403040b440032400200c02800280c4402004400540d064285520f0300c1d40136091158580c0c00c2030000c0c201080000c150003200700400d2901d1a6280c1d00c0e840c0c082e540e8000000b4110003841480004010021290710034103820000301c1c2d82160040700c020005a0364450040025044046080818014103080d510b20b500721055040160800f081d0140004030300300a0441580050004001041035041c000b01311285040c035841d1141c5090187d0610558866062050701d040020004840800d58400d1080300001000d04031902800307980c445a080c0c154000380a843c000c0f44052000044074a0409010807211908034540c6082d40d0f07800c00155020b40068910394185078031740c0700e0f070f80311568140002c6202e00e00e2060006209400c0d400c011007100c81c507402c074600070ba0140c0e070280360795074a41d007504200e15412 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 16501913 1250 16500663 16500677
    0x5160f03050c01020a09060e121203220f1a04020108040b06030f0106060e0f04050702100e0c040e0604030e040c02030405040519060602030a021002040b070206030a110c0312090c060a 80
    0x524003200c00384210b445602d00e6510100d207000300b40e54450700d4101158640d80d1481c101907004c000300300e1801801101c03103040364406070320094455400ea001c1d551184606540c0384107100d12200000005200c08000c44100c16121504002c101c2c09c2e500a0745025004030540d1802d00d0983d0028104074030140005d840c0a0841002481e10f83d0100301c070b82c10304c01c0c0d414000d001d003581d10f040150000c42c80013041407150f499804404003a040a00c40d5603c5600541d0007003e00b1000c03415a4401040888985805400f4080910085407214082c00382c03104843c1004007120710f41414024400c0100d002820b1165041c07030141d01900c3d50000640d801da650448001849441c0c4c100c01080700311a04550603d071a08001001514036000b1014001440035a020b0304c0c007034484452204100e02c41c81c0218002c541083c0f01e00307009400c0c450040c6500110310040020384403e00c0c1c1214070184c00001c1200316581c4001401100c40d030f14080601d030007160010080c4800c0c81c03c01d0001d005070040104140400c80b203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 16503163 1250 16501913 16501943
    0x30f04020d060906060f0e09010504080f0c0307050303070c030e090402130c050403020909030a1419030b03030d06181409060c0a0c0b0708040308070806010905040b0105120c03090d0516 81
    0x100d64800b5840c240d006408005843d0784540c0d128680b2280e201f030346880303440e620000d08a520b06000340351081350321240340c0786002c44140e9018136a4000a058940c07510003402410000307a0100f000794094182c0d900d91812031841454000d003528a41480b01d80101841d805110050300d80d01c24035400c444980d0000305107401e011030201d41c140280c2c5e2001e5403080080040c0114600003200420055101e41d49103903011403025150702e903500c500202a1804050884040c080a10960080d0041440103054038030748683c0405020641e5115046170982090b82035a080346500e040c880c1002301086000e4040c1a880c21a002035210380c00240b06021803100003905481d8a8480c08805d409554011200b5405042c414401483c440c2c0c11103080300815003020203d20001d00940c081f07841144141e54050165003050103010183c0704c0303150329034140401031180100003403480e01d04034070428540304155128a05050280d04d0030950380c9441d01480000c000450305107184800390407190750490780514074525 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 16504413 1250 16503163 16503173
    0x8010612020f0310050316081906021903061e0305073003030b041503020904120912080702090604050105091b040b03130203010b01020706170a18030804030212030f04020d 75
    0x10841c1c1c02e8140348140082080390018010040e9010344134141c00f180c450f0158004e401d01080d4482c041c1c100d45501c8205a1040000b642c2d0b400300c10a4418031f405810301200880c074512654000c1c600001113500c07881d0512201d8400754040864254102c20070440d54950b44070705856804a004800240542680a01c064400c503030178056000c0f08008820215180390070011f00500610107000d00c6242803070441c10350384c502c94901c2c0d0b0982e03800402101c4035841d256555400356802c00048824005408000514404c0030103070209098000c40c100e030f0360340b215403040080c4058000c200307a104910302801801141c444120096100d80140e460311007192080700000b43c207004941c03100240317000000030407202c5000c40342c0c003589141c800d5000313202d0241503900581c0c0307891b018043c203800941c140c3c14124440c1d901821260b00b20600440000c2d072201440d0b10f07407036111038a040540c00301d4040002d000030954100100303940030315504455400c0d030420401108a1000107080a44030300421000f43c01405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 16505663 1250 16504413 16504417
    0xa0e010809030c0601060c0303110306011205040201090503060705040504050c04080a0f0303181103010506030109120c0c08030403051501080105040314072901060e030a02030303061c12020c0406050102030a0801061202 95
    0xf00b10301c1110100e41c1c1d40c0b0340045c0445903642c8201c002a041015456014001c0c00c01e41c0d0051505031510001c40365a00303005002420014023390400150380c5002035075440600525000e18015513440355110f04000610082c0c45000d00b03000a8048104020842e0364000310f030001500ea4001e500414400340c41c14200c4c0078092010b40304c00d41d080241e40007070420a8299020b03083d540258001e001503900c0300300300342c01c0f07035500e8001400e028589418450382074420075181e030b0031a11a10403c403403161030301c40b418a9900650410ac07542d40c02001d895400d603951851103401003040d0002407005240a65004110900704400161a04000300e030700010001b89090312010003407400d148031604140042007250042003171240750301042c0d440d00711540e141030210f000d4003419005002180366480e813200b4421010103150b00010440e0003042c8401c009009405540c10b500095801170848070981c40c10082110240da0100303040d9801080032913030f10364210b02030a0464000b81011015801c140ea00000a4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 16506913 1250 16505663 16505677
    0xc03070803010e0613020304021302030612071d01051f0507030509060a02100c03020a0905130605090705070302061005031f0204080d05120105010801180525110d03020a0e01080903 79
    0x2180d0100c00498003110100307a00340b141004549410950300301241041c100d20003a00c02a420001d1002c2e001d684003203503001546c005001034890000f50707802600407800d14009400401400600641d07086c808184440c20a01600080741c500d44020914041c0301c59000320700d40b2000074807102180820505010340192040c505000c0c00480e80c403411400029120382c07800f010584c03030524000030210f81511038070941e81c05c0803840e121a0345d01070500741006038145030002002516511303501c0105090700e4018803280500c80a4440c44e0303c650052070080e040c1000200380008e85490700c04200090f079000610041402040d010709100e10440c0c0190802138811608199558450501c1da11420395000c001003100b010320504908a0380d13280c100444014500703210b981d000d80c40c04109050040d0203580a5074024095030840c40090717030070b400444070008100b482180402c1002001e100d400c0414007100c166040b02c0c0c9001c600d8580b2351100509a02007042c1c01c0c03410881200002aa001020021075185c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 16508163 1250 16506913 16506923
    0x7030e030a060504081b010b0a050f040f0908131a070602030406060806071205010e0405030403030f02030702130209101e0c020a090624020102040b0702090a020d050a05090d02061b0c0307 82
    0x40e502c0d19040c1401c00350310000d806074001d606c02103049074200c1e0621034500c442400a0088102524020400000d0342c0503428a40d88031f039a403900b01c210a1134610a0b88a07240c850342c80591604e214860101c8544078560044c55110000258a20b45000d2841151070f020b07488180140c4907152414440018401908200c01600c1060180205c65070889880c00c42214145410310085e03890311441c13030070510240ca00903c0d90340240400c0c00003134002d0f075044003240d40d2441224200411a00040c2d4000a4180311901a50340000c00f64824100b038103000460040c281810b0b0f1800070f44180308404020500d800034204442c814460086640c1c5080060041c0701901050007200c0d1241003046080c5051f0816900c4001c41082c0c1c00545401030094034200d174098000c543c20300c522a000c0c007545074030040c0300c500c0855003005141001e50785482401d0052203e0325000920b481c0c120301c00340c5885204805402994070000400a01041c0b03140203e0a9903004404507807281c0c0004c03800c51844c000d24000030b00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 16509413 1250 16508163 16508171
    0x60203180601060e030f0c1f050d05010609060305060402070c0306050703020d0e030408011803080103120302092805150405040b041d010e070b1c0b03031902010203010513020a020307030e030a06 85
    0x1e0290b0b0312261810810904400365041c12038401140790b51f460794490403079005548070128401c60b9074408848110b2400b2070030540e1510004207004000c1b10000d03044400450240b10041c4807050389407007400d0b8004803c0c2c90841c90324105841d1210001041e102c000e20450300c80c00001e80382031094050f255008200c030804e01071690054003450b01d03a00540907014096203400514061003507000085c5000d20340645402c58640d00f0340d11882e8040d03c040e00b0f507000380340c3c00b042141c03415100c009440c00729807107802801401403089082d83e60b071640d0f81c5c0c2c46184906416080383e840c0401c0901201c044402c03c540000740541c01c54085005007046110300e520000c1401a0310030800819007040001c10048002c0c1c0318142c0d1100819020342c004d10b80d10621a00556007c88040506940000c400c040c00a0480c0d043ca0b00110040c60440b0f005142d26005075008401003209007085403041c0c4001c81c00035002d41c10640200f00080d5203028a000c0030b420480e070f1780d4000d0100d84007400300703899850b04448140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 16510663 1250 16509413 16509419
    0x1603030b1c051204051507030201060308040303020607110336040504121205100510180810050109060303080609100302100302041404050103020a17030d0606030c020709020903030403060203180601 86
    0x70452100c1580549950041c000b4440003d210103084a080c1c1c0c10003002000030021241c0806010303006144128155940d42c1000b02c041215203000d04000d510a500805103807816100c028103016052050b1171749a4424086050070042076121f0480c400500c1990b0b0110390a00c40f081240354200d060110f411919080610091108032a07c81601140e0384c0c644c034045050280051084030412605014901c104590900240c81d224894041072015454100001c00b80503a05600c07400d802da0111086521000c580070405407140130b003d0051035100b50801800b0300d1900d014003084402003034588103004000004010100300c0e00644013075900904014100c1203072000280c005d41c4680200d5a550012400d070440c5494507001d21810b8a80c0500194401403a06101c407040d000c1d5103c00c011540414454001402024400d4000421841d5804100c01184500c040d0504200ba0814a0680d004201c45075854400004032401c495011200607902c0d540c0e80381c103441160080c100d8600c6405020000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 16511913 1250 16510663 16510699
    0x60115110c13060608090307030804060e1e030a110c09150604090f090c0e04110112020702040504060515060c030f0706180501050f0901020405010e0f01020703020306090604150606051603030b 84
    0x40f000e541e2282c071506400d8480440280e5030303002d51030340280000c1009000500050081c0c1000040314440c01c1255a100a1000316540010460303444692640c80420140700d6294040c08000b91400140b019010252001c008140c3c0340400500e511030488036510144040c1d00d42c2d40444005110030a020040b1250f03c9018601400c0249800c1e5070040c00c1c00d0010540050311618a4000d13580440c0d00341c0d5407002000107440890805900845940d82400a0400358841c0c0c01094421480355100080518290640d0310941c0c1d5400221406150148030008a0b00400400c481022030308114a41c3c40b107540c0d103000f10103481641072040c0c0381c082840d010b00070040c05400041c00741e980d160030542c807030303032000c0c1154201e000740d10132280011000740c3c1d09500c80c03c0000a80d110201c0600c169140c06449402282c540542a6510505507100408201c1803121001c2e00820303002008100b132001a1500c44001e045026a8190202940008800d2400c06009610000c61000b0142070b16004802407012 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 16513163 1250 16511913 16511921
    0x803040b1305060f07150b060c07030b07030504020603011403070b0f120108031903020f0915070b070207060806060d0905100b120a0b0f0907030507090b0f0102060115110c13 76
    0x412070911007892004141440c1a50a0751250140e039841e0b1410043e5503181e6007011480081c4080c2096582c011071415a01d5120003002e40101200080c00054034500d403c41c0203c400424030000c045c83e1806000059032007900f128110b8200f1440c20704034001000009041110701d5000c3c20146900044140e0907008410240180c0104c181100d01281ea030f42c9ca00903103030701c90b0b0401403e03c90519000541c01c140a036018080744c060344074a40c0e040015060110381d40d92400c0032041041c60020400e1810801280d01142d40041e40340701505403180b504001814016000c2e050510034540031401c02e00e80d00320b580c80380e041ca070b4101c0110382d04000094046401880b92014060044500300540700200e031380041c10301c402d2a403140b41710001c0e5542248840d400f22029194018501540c4c100101050040080e0405091003410000741049a5010883c2e2500b800d42454155041200100228800518500b9100c156401c142e041041c1c2001041d0070301d000c8200e02a8022800d1144226124060b80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 16514413 1250 16513163 16513177
    0x903030911091015030b0d03020601030507090b031513051b0118032006070f0803010603060503010504030207030212030403021903030207060203030906131a18010501090905190c0803040b 82
    0xc0e0104688000244841c0b401c08480c0d0300011290240108055444402100410f5005240000d000078014001585101f0790400540050340088014020300c0307001d108160080045510800c00d810046020a41340c1841142200318290b160000845081f04130510350303480d0ba4000251016640b05010641e0341d070844d04d842a0000f2800e12200c514500d0800ca403400b5690002482c1141c0c44000c07800d0941da10b00c0303000c0369412041c1806a040020001c5030f050701c0303051040e44107035100d604100e401411109143d200746c0c8268140f0085c4008aa008a0000241c80e01a074407003050380c5140920500e58411503000a4000c808561454031814070a056641520700c0f0b0f6090300c000035a0381c2c03000c81c1e980c003090f6449201c035001030001c20414117581c0d0324a202d203842044407007420010784034804000c000880e1030341424009825000381c202000c1c8106405000702c00800c01003806039445040c2d07960350300000301550303000180c40e040510460036074020007232070700000300d0356501c1c3c0303800700c41c20130f504800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 16515663 1250 16514413 16514423
    0xc04120b16050c0601090b06070c0f0e07170a0f0216030801031101111c0207030c08030c0c15070803150303070f060506040603020627030111041a0301050a05060a0306080109030309 79
    0x20758205490742c4a60100c0d40c64251038002040303a41d080660b218018001d21011544c440780800c542c0b0002400040c00d240200b20b00d50b803424456242901c03950a0000040100040007542c12442c01c0c40000946c0142c0c00c40c4038014000741044c0c140056400038486e00e8041000f0300c4082d002c5c00105540b01003c141603910400c01c1d400b41d46204d40c019240000490001855030f0010600c1d0700006442c500e42100901051048034011542d07030300c1c0c5d006036090a81086410343c0000a41400c4001d04218501600c038090f6007005035010b03805e4440b06140900100140f5480c1c00102003900e04000d088c4e980d0f04650700a09495881d03040d490900450000c0b040304440c41420400010440e26080c813400c000ca0b40c0241c2114640b90079041c210102c1d41180015000403180c08800c1403568500744200b149004000d041c0c6540c403801d120054400d100100707140c07280040200014011a140c2d42200c0b0100c51080d191261a43c003001c03000d0713000d0503440c1c0201c8802d610f440119420306a16802110b07001d03000b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 16516913 1250 16515663 16515691
    0x30f0d0201060f0e06010f03020d150e061005160302030405361006050f07210207090204050f01050c1c030b120a0201080402120a05030313060605030a0c0308030c04120b 74
    0xa4a00502c03c00018840c484046450200080d803e500400d101a000302d240e10300149091403030281d50044400a4411401c7c4448a0006001400900c402641c020104070344841864103110300040c5075126946100c2c041c54442581403040500030410f850140000508012020b5810760124004504a045d400016155103558240c1c400c14503800034040d81e03001c052140c0f41c50819000f600c059115852440e903046040100700003080d203060940340c0d0503510740221b45020b604003100928140180d003001e40d100348100300821180d90350482d0407c0a0b582828000d85504d550303075020381000020b01c80e041450701200c000340003a551541c08120180b000301e404804098070860003a50b41e40034054000c0c0450000e0300406c01500d010840c011580d6107143c22251140c282e955680e045400035105090041c621074420f030104030050143c8005090158003e10908411303031120103000441f484094044040000403600c5503041c1c808640c09000e040300001005c4419203004a0340d28000c403001485440a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 16518163 1250 16516913 16516919
    0x50303060306010b130b070311030c0f01050a0e0a0b1b0406051c0c08061908012307030c12020703120515180c07200907020601060207080606010f0e01090302030f0d020106 75
    0xb655095803d80220242c402107102c6c18480d51203d15841550140e01b0700441035200c1070030040400040031900002c20161444100d0f55800e80d094603c050640e608040c10504405120340002550f610b4260300110040a50307190401c450510f0f07007081034a0102100c0010380403c01d107030000020821900440e00e01e0100c0e00401c856041210010305004000540c408041201032411407038280d112134521080341e000c5540c4040403800c484812254101107400041050301c0c040c026038119500c1707000c505061280345007000004015510b010400707031420b0f5010590740c040c1441180c04514410120208000c2d03030410130030301d078010b41c071840c0ea441c801d100c00c1d6030009810000041042c002c40c1c40140590810215036100612100202038203a1089074500b00001070741c1d02d10070401d0003408030743c001d00b03070725418207000a00304000d54106414543c084010b0005a176400086c4d851200003614080d80321a170b03a40700480f0041c58650002c0c1d032500c11400145003e81010950301d080c00d0094000700183c0e59 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 16519413 1250 16518163 16518179
    0x204020a0c14010c08060103090302010b04061e050303070c0e04030207030204050114030d0f020714030312010603090203060903190302030a0e0a0605100e0c07020d020d1509020a060810031209050d05030306030601 93
    0x302c60b49140005e20344000b040c51540250803511281d0b20a00000c41c28000c00000700742101c0071a07012081400d281034007110f510ba0940002409000c007540030350b00c2d08050340c4813854240840d104e8622221500070000e424140300384200c0c0060342e4002c10903c602d5a40755021101c580302d80c1e248920900404c807240712142d00070007000310880c400c0e80141c880d141c900f84000e0304405081c603200380c0501003004407589220881402a01070042c5031400174801c202d07801170501d860710040c0811900d52003040307040c0b581400041040340c09010762a016a880d40d07402c0198000d00307040965440d99208110301e01041100940007148295003e074140c188140d500c010001900000359800d82c08107200704483c00150409040070f4000900160400700078000c1c03541c66081012000c0c2000130f203240d454800700114580388a04500505113403170704c0300890070210002d082104240c4001084558007200440629001d100500003c1400808000d140000d42c10441c0e1258011100c0d144030b80a504004202c0300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 16520663 1250 16519413 16519421
    0xf0f0c030e0c010f02030c0111030403020f161a040305030703030e06090c130203040507080313240e040c02011b0305040c0510020a030f03110c0109020108060105090f010309020402070204020a0c1401 87
    0x203101c01c001400010961030042d200d038a0f902540a0840c00100705010380042e090207a081400d0402e0340d050b0340c0e8607003810000d0038400e07143d480d001c0359000984a12100d480c448c5048041d98039042c046a9000e40e0500741c03001ca807090f548020a24000421403c09140e0550f1180101100c1042a201140e4601e450b8544034803c540000f0ba210035100301740c5001c4070b2594003456020b03104100f15107a0503114290946140c02c0044010001003a003e814804a00000102807400290000a43c0032450784800540742a2039108220f01a82d42e450040c40c02078801d4120700700356400903041c0b15400a40a5006020300011201500c51026a400014440c2440b1080601c0408070394098044090555001c40304100c549002d20201074840d070980d852045000700501d1140c840000005203001248005884007e0052915040c480203001c10703411603c5189c002c025448091900052449441c4002170003401801d20203900f180c4085079450260340c000c6c00b04000c560098068018504800505500b61 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 16521913 1250 16520663 16520681
    0x20906040902090a030c0e07090605090109030f02040906020a0c0204050610021504030c050706030203010603181110020102040b0f0301080f0105130b0424020306040c0207050906011407060f0f0c03 86
    0x4a0411042002045580c0903100383c4000608041e0708640d40d03218810009000c0e0030a052030070104082c00603803504080000014412820041d0030001038000103801c407012844058014040c0720786c804119903d0754007124085034441c1c0119100c0c085154024800c50600200b2401140303481e02041e1241341228051300c01100039070003010080103400c0000500c0740080d000724244410b400c2c101d40064814003c4201815142c4e40050310b940c50031000405031000e1052074006003c4190304000822503c1d030070340754000000e81c2d400c4400805410101e0080c800c0c0e0340711507881e4001141c500340f00c084143c01503040f50301034021a070f0740506215480d800c8070419a0104801c0345000a13002c001030a01185a0340b05016031603214a00e280448400280c02c1401029400c059002040004518061054100d01c2c0c81a1009010386810803000c95810030340603144034180410032020440350115582114096503210105100101d1031004ae10003400c400300e1348144590412801d0803d49120341306103040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 16523163 1250 16521913 16521919
    0x5030105010f02030c0a2d0f111909150b0d0606030b0a1217040306051816081002130302060c0102040602010b150a0e040e0f060f18030f03070c0f030206040204050a0209 74
    0x2008115568400c3d080c17925812000d0181800720504c00701098003401c500340780e0b000e20b0218000300314520b010012000240b4015102b02e80d032144102003030000e04e044c041618000301c0001038007031403088040d05281881e03001c0c80b2100c0b400120950307010f005400080c1103031400e4034240036520000741088000d0046000e1002d841030703116034000c0030030b003901490034200f40c04100c1603240a0322515030006844080703c8204000c41d0b5100c2c90283c50400308045655032050026012059003401c90b20b58a0b133b450a5451a00650042400e050085039881401c0c001c6a0080860380d6400c00c030799016020b03411501c1254055480c00801d1049403d01400565042c0815040245004100d65040d503000507610b444603009070307490007c03a405020400842c116940120010881c6150121150040180007001104240c050032004903900c4000819221503c01002a00740c59a54903c0126800080200b014044001c07400300301d814180c020840768000d60080e1402d000541d90b2070720390000d80c814140f80c560 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 16524413 1250 16523163 16523173
    0x108191101030204050612040c0603020c0309010309142505040510030209070c0206040801020403020a0503030a020303010303080403051306030c0806010c08160606030b010902040503060901060302031b03030d0c05030105010f02030c 101
    0x1002500e010100c01069205050060501c0d441c0e4020803499005455180380c2c0340c0b0068144428418448044070040c14545402c0d1b203443e91121300d903600c03800b48602c841c0c1856142c12880042020041005182c1c150340c004407403800c805c03141c4140782d514200300c0f4110014021080410541010701856101d0b07600071103410000d81c9980e0910600590090045040005c0e62900c040180e0b44c000040004207480000503841c0c3c1d00310b0040115010b0f955011601c07d40c4204102031003184c002c4142d0381141e415050031700040d551f9042c15102840343c0c0003080342421040b1000b040b104d404d036004007000c440d281c1c6e4451282d90354030010758940b20041e1024141c80010311070246c07128a10300d0084640d61044202017104c5580307a407543e0440034281c01c207240d241d402281c00c0c0018202003004903482020003000f40a03040c619008a61107241d1382d505252066225018003031651010002c071080500c08003c104901c0304d85441c010042e800038010b0f40d0001341420010708050780b002082d00c10707480e0000082e00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 16525663 1250 16524413 16524463
    0x10509040210050c011e111c090c03060e0115080604171b12190c080403020d06020906120118020708030a0507020a0c140103060f0e0601080709091e050108 68
    0x3000251158000c20008000040e035540d0203000d80c0c022580390507400300200d041c0191b904269601c0130100c4c03215400a018031000c02c400c05401c404511450000040d040046090044441c0c000d030300050192401d00d180d540282205600844401c08005520001e20740c58003001030b2a03080c191406486811301c1d01002c801c003803560005100c3d03402d50680e1000d03010300403503003281406040740e900007003100c01144a0496507440780c10840000100d00d0441b4001075150b85a8503d03005a00020f400f54940c66610300030000554102d41c0740d1800180b140c2d84649442c04034807504442402849000111034100342842d41d401c2c0262541036501500c20703030556658000308401040e000b403041d4114800c0e100340501282c031040103880901014140c081e524a914000034060380e109a1010b9410002c0c01030070898140e5160100f50000b4091030700d030031030b902d0f16001280e40350055000003001526190507c44107c0e407626118280201402c024012aa41d400b205919000c180800e000001051a102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 16526913 1250 16525663 16525669
    0x10801030812150a030309080f030301080706050a18090c03110901090504090503040506040618060518010c03120507020a02010e04090203070e040501090606170f0a030203460807080105090402 84
    0x82d42d02245948115441c142e8100005011404c0b40c1d02c1a004104062001c0c0140e100502c894141c510208001314a194135111982d0354883c6a48501801c00c800030484501f001d02c5810381105040c4d03d44070f0801031545464001c1c00900c031072004800400c2c981368041c014952032009130350f200c03101610751080b968544030078840604595402229240820840410b003582ea01c03010f00b0140c01160b43d1061a21101071030400d0f00c0d40300c0d030003500a120041c0945184036403241c4802500700070038640103400e01001c2c501a91100d680303040c0a124a42001e04114845a0004920720401d000342e8440d0820000b40007440121113a10701d02a400d43c0080078240306940504101581141c4920f00000700c4603410b403605000c5440035001041d512400d03104110700c050341000034070381e043d003268041c2001c610942e0717010703540b8420382404d80070500b107264030364254640a2603004440c0c80d00d0410b00c91499103004080a986d0405240c11000c1900301c40803941c4c841c0b0074611603040c0c034006010600c10707407038680030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 16528163 1250 16526913 16526947
    0x705010e040f02090909030405090903090d03030c110709050a0b0f030c090c07080a0801050108090f06011404060b0301080304051f050a080c0403021f110f0a11030309060a0c110108010308 82
    0x81c1c2e1100c190200182c00c1c1c9500c58041c03082c403030803005000d50703186e606003400c00c405035902514502a5900c107108114180d81c68001e1206131a41c1803c0026130f00820200075038086131041c0f011500c1d4015800c0c0083d080c0b9281d002540310b0088150108120540703282000414800e80b0000c4e500740e0b004c015032a40c02c1c1881484190006000201142408195524004154800e0a401000460400c010000e5580222006030040d040e030005d072401c5010580790503a10281441070303550a00b02c0c0f2554210702d80b242c1d4400c10141903c10441075072980c40e0007006581e603100f0f21a40c0c0c06403044200d001000c10060310340f40c40187c070554a0519102e02c140080b50301303240c0504588010f0b0000c210010040c1e44601a90030400000d00e4940101c10000758007a04024000000300b009070003280c01c25001100c04120744140740d500c001c02010003191039004c81d1550040b224001c0c0c02800000b4103000198209191142152069031040c110300420703001111641c00a12000380b0700038061040032040251500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 16529413 1250 16528163 16528181
    0x6070f1103070308030a1401051f0e011407050304080c0d05062802070311010e06090a030507050a080c060a0f02040308040506070f05010f020c0115060e0d06020c011b110705010e04 79
    0x100b1034a050303840c1e07103c5004a520a85410a0403581c0300708403412a0b590312801801000100c440009882c80c58601900c3c1814803910b07a01040451071274440c00b40c1c064903c01c100c0c0d0034070014160b1256200d14240e917a942c8180202d1002d4480c0c940850403d10308250000c03001c0d940a0050065512290340c0440411340b40000500c41409000441162402ca84041c1900d1402561005161145000f1031800c42c1c0d07000c03041c03500c41d4010408201d04054002141050180d1500d8102d40d41c400340e05003070b4140742480200911040c800500d0300b020282c00603c80c1e000710120101080b4200017002d401d000c030700c030b00e110080200806000412061802402800d02103006d80060024202c241d07440301d0031a0503142282c032070a80d01103074244010b44248142d0300031050903614030242c9410b114024211050a1413028400c0003029155003c00843c2c0d015a141d00e1044002809000140c07034070034209001c14442c210008403034007401900b01c0d03400030303c007070440e401a1601040c0501103010700010304ae0080d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 16530663 1250 16529413 16529419
    0x50a050a09030f0303020d0510080705060c1204030606030c08030a08010506030603010f050a0614060f0306040209030f0d170702031602060901020f0a140d05030f07030207110d030306090b06070f11 86
    0xc800004100c0d070082128020713209940c0107036070701c2e80041c081e8110344d03002d00b0300890014075032000c0c00310301c10000b10581601d9003191400d8885d00d503580e1151a21060241040014802140000402c41142c015100740c0344621003541600ba12282d0f16940c03405440c012000003201100100411304042e0700940d0005400f900109103002074190040640d0300544424584c503170f940d4820070421661540c81003965104554540c90b001ca0b1744d040b00d1890101400359031260783e00103042c0006940400020708882c1d884001d440d00d103401107002905015a036000d0001c00c56a00300000c0d921440031003114641c100c13003082c61089991a8084c459940c1001740a02e05522034a040c3c403000c1c1c10700300036079801203100b42a141241c2c014000f580b4140314101d120070007403007014028401e512220140140e400b040d03500d0016200c05c09030030b014051a104840858200c034011040c03000381641074001c0c90a440302003009200d6000301006200c260f105900d409440700c1c500100710f0300020030f85036020483c42401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 16531913 1250 16530663 16530677
    0xd08090418060e0c0406050f09060402130f031a0c0c0a030c0201090f080304031109040b0a05040204140f040204050f101e080607180e010605040e060a03080a0c0212030a050a050a 78
    0x341d82c2c0c040440da5140c0002100741e0041c01070241c145041d00400c030150a00307603480003143c480b0321701140692038064402485160045000d075074048013642c20034010300c0d4003a900781c0c90640d60705151001b5605542000101110140040c940c044080c040340d0304007030340c200105102d25107620100c481c0c9407503103412410804403c000103100d0366250f0441d0081c00e520300285d940c841c618505003900f01540d455442c000c260000c00c00000c20248060544e0200c102c1001041e80e90303c030720004e0010812500003081c400030348070a1141c0b10044c1040b545c1f00f24800d0364104041d450700301052201100c21100810000c2c0440d0043c062814072100509001400c0c0d00300c0647c0c5c81d10f40301010304060044a400300050101e03251040b03400011013600d801018030504d000c0c05c950614500a00f140f1950149040c1f8190a501141664a0311100c0100860308a152991240c548020050805541c80d5007603100b000000300d03c0311030034008401c542481003243c4600d0b08e0102c1240003a183c54000340003003401d00800c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 16533163 1250 16531913 16531961
    0xf16030e0c0a080c0a05030d0504260304030b04021206011503020702030a05010e0604020a06030c020601091a030106030311070603140f0405150c07151a090a0b060f0a030b0d080904 79
    0xa8501082c040c1030740101802101d0b010106011a10051340e122502c07a911000d44d603440c19420204481c00c2d13171038085d1800c2550502c00380049540c208a0354036070103488005070000521060450b00c3c0d00440c821034000c01c000d031262403c1e0340e076a90203000e51178010a0703801c8551080c50190b40200070491014040c0c5800c1c80e055240c0e5403c40f8071405607a00c240c0c000000f04011441c1c010307141006810300d4107042180707240c0311070000d54681c070501034044403070350f1400005981020b6841d0285a088014001d01c144d545901d0004d100c808181c0c10302e9000d00c01e001000c500f207406401030710840c420300c103043c1e10181e83e8001c0301e401411000c1d0060320035001d6000710383c42520020200a2140b80c881405556419843c0313801d06580310540c2c1c08900c442d15181800c03500b0b000d41c41c40c01000c0481142e013410300b51100318200006110b03070003a8030b41c4030f00300152100d40001c0f6035000d840402c0564800b00600340e400c00510030f940c00300340700c004e011001c10031089a84e85465801140701c202c1407807a43e803180c50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 16534413 1250 16533163 16533169
    0x12050717130201020c030d0801050f0406080303070c030306060309080904090c0b03070e0f0901030f0609080c070305010e1501050108010312030b061206040b01020708070b03060d0f0305040603050f16030e0c 90
    0x1025078032121501c009904500555804021400c00120198020080c2c0891b01c1c100a04c40001801110300c201a10a05e4080d9a40da17900726801a00401056a90fa0b040000d000303401d09403851400c83c04603003000d2000545d42e019105001102e84c01000e65881c00c2d6140042000400c2c1205048030703d1101900085900e07911031010314824a6540c40d40c16008071001c00f00100c2828000c3c1141c0b050031410010720009141a0707007810341d194043c02c046490100d51402c0c3e0070344d0051000d052441d226800e8000148141500442840744034801540d003408a0b494440811003024000c0c0c0380464800c500402c00261202e0908940300c8443c5400149508408002660340d0b202209210892407440c0900000d440e041c45500700d920803d00040c4007461805c100c1c00e0720b0394800c1c42401003142c2c01000142030303503c1e03030103c3c0c001716a44140904c00302c40907841d0141494005014290000b441c0500051891b01d0b65040c80d8024800e034080b09051030019901180035000d03c650254060094900b14a1261 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 16535663 1250 16534413 16534457
    0x50918030705030301090e0616120e011505090a0507020a080a0201060506131410140714030a09031407080a020f010302071407060e0102011802090405030f0a0f080105030c01120507 79
    0x40c0c400d0010f16038a5141c0303803015007650041080f80920b500548280800c80000c0c03106542040c4072800d0504030140294150002029121003105032542440f0825800e219480c800100b07607042101d14481a0316111301c0801100c0086861401592040306000d0204a001d0b01904540c01e041c40042141c03619240416516084100030802030030901c403042c8418103c0c800303950005001a143c000b104011044020454142d2103211250303444002001400d002c45111401001290311048075618025004005c00a2040d8031040c0c3e05a10801a880304c07451012030307404201c41c4010300400045c102c940800002000c8000c81c581403550800c0314100061620b82d010a0280051010b401d165107000c074050100214045580e045904d0030360084940c4e0300712603a0504640d0149d48121701541c641c070f002e03451446900c0c40c01c2c1121802083e141072440e4003030101c00f0340d0384403170b52560280c0e682c800c2419502e6901a0340340303000c54000301904091880b250301061380b082061411103102080350341c1340d40a03c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 16536913 1250 16535663 16535677
    0x3230708010903030e0d1403100b0301031101080106020f03030c2107030b0901050117040f02010903170304020a050108070f0e06090a03050102040f060c12110a060606020a1703090705091803 83
    0x107035111008141403607014851740c0c040f40c4c10f000103444501c044040080c1008a11000c00845039030100c04581880809041000035091842d4100c2c0d4a50b141d08000003401d280e82240c0b0f0010303c00e02e00104802c2d102240f071108100080d802103080d078a5014440c07442c2d401055040710b1807843d8100440c0ca001070112813601400c255200010398080d02c02c20f0060200c0140c02c024180106500a1a00d2030f50311100c1c1e662198000500d030340c510760300d4401200c00c54619840a030203400e4000703540e04600390cc1030056014a1080718a5940c07259601e0054401c000704a0380c0b400855440ca004511560156180709130040303000300b180707150155a00000d6510045e81e002a030b031583d030204052144401001080b00601420300f005904003c05541c0d5001080c0a901010104030151f0034610600004225240d03240354010300070b100d0b643d11417200079a1030842400a90f4800e082c0c080700001c0e5140042203038040c5070440060844282030005206505002410000c04403691905106401382d0620207403141c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 16538163 1250 16536913 16536929
    0x310050c0703080a06060f030b0d08040e010821030f13080d060806010504022503021207060e0c010c0b0a0b030f07080708070b040b07030e040f0608010608121201032307 74
    0x9826941c20001e03c100c40042101c214540f07001414401706800200c1d2010a071603030300d008280d000c10040032420b051003104000300451000700700410551818040c607816104400200c50000c070011880d5100c035052941c0512843c541080401c0340d51503010f50140d400314034016250075110003680c450720164004042030819075070301c4c50180800030042c40a1401050126420760800400d040300c1c1980d118645180c402c400c0c401182d41c01010300074092900c8440e101d409207525240641800405841c600300c8200b103078007804101003030560080401c020125002a074003422076941c1e0141c28001c12403a80156498407400382044447c0000700f04100240209001405410303103030507101c074500348070f0707801c11040c4c020140000c0c05201119402c3d40c0c83c064040c9043c8240803410310202c1c0052aa2301c10003106203082140128000d181508614101c8804104813003c1d8503055204007064007980300407562010342d04e801003001c2466615400488aa4400c1d000caa0005650086107807000c69440000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 16539413 1250 16538163 16538167
    0x6010602030c0d0e090c130f060201060501030b0102160e10050415080106060507150f020d020d200c060109020901051c0509070e070e011805040e030d060f05060a0305060310050c 78
    0x110005040c0508060501c40703044c07883c6200b0000740040c0441c1001040550f032840003180c0b01028603442d0f40000e0080c9401c8240014250320754400a01a00483c003900380424207203000c404007940700103406440b602150302c00b449030a00300f014041001e00090400340e40303080c14a202203110390b1180f045100d04007481c581560343da0b00d040d0f070090035030349968811002d203c03082c0400700215014094001851407000c0c1d0004030f41100c011418001d016811952200920220305040703407203225071007101840c0c03401c0c1c043c08040c05001c5a200851240074824071541c1c106100401840109402500788401c05040c482d0920b00c4600b03485001e4512510b01d22600c50320f600c24000c0f004018030941002e4422000040c600780ba0081001d05940c8903d181c0074100090480642c1c1d03203042045a15028110003001848030544c1c6040c0c295983d0130110030040268a414000200d0300c1c0340b040710f00210359014006504051718080c09a008040043c9600e0b010b000324144001c84c5102c0e44503140c815445a10702035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 16540663 1250 16539413 16539427
    0x40320011e0e0102040305030d020a02070f03050105070e060a050a030506060403060e07030c06020c0603010302120a05010c030c0206060a0503072c07091401030507080c07030306080f010507120203010b0403030804060e0601060203 100
    0x162240d02c00c920341c00381d00c108130a0020460100c22140903580c4148090390720320703105038100d21300110303640700d101c983c8004234000c810000190401405002240d840204089440301001010310980414002003801005080100c0d03000e07400070b03584944000c3c045814295280c444009480b0021002082d68003c840103100700841d542e90301028000d0751000b03018111821003c181c0034481070102910a0007070050035103100108005041100b50b102001344500204400058082d0201d20064805030184400181c40360400442c01c0b01183d10080092207810328043c5020003007020302e58400d1038846222001c62118002100b1107018202d25070b1490041303498107411222042654214074101401c002c1449a4954070000386a040051103008560b158498503064008004a500280d014050f103051681c1041b410340c41a8450050341e2508442ca2070014450000c0b44000d000d02c6140060502c4280040f0744600400383d401b520480d400111708480b048640e1800000b42d0240d0f0050344006520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 16541913 1250 16540663 16540721
    0x50d03120908040f09180f0f050a030216080c130b0312040e010f0e0402030a08090f090412020c0910090b040204050607050a020109140a151803030903031701050904032001 75
    0x156004000006040164600c8012a02036508980c0c4010f031400d201c5013000f0b41800542002000c048e40d0010441c1c90b490410700e0b000e07440700560f40f00891407044174240044e0030480400d2448000d10028590014600f0309120034000306104006c198140c42108000041c040c151002040500199603540207039615042c000e062441d01d50f080342c0001d01250040c0300060f00d00040380340090303070700003003460300c0d40190000300c0e292022901500e5070144107403041c40140b119034440030600c140203600343e441084050050107058402940c0541600784084010002c000640c0d01441c07602000078805403400c0d030342ea400034100390443c11041c1c507540c01120450085613000004040100040c07192101e948180d0b2002a01140c8903104501860040143d20059140724414045504041c0000d44030a141c0301e05005148070a540070460100c0c50540103c64401021b4000703034101d8000400c80c044944d6666030865080c072070594910800c1c40307040c9521218800038096242d61031036004100f0a4540c1380101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 16543163 1250 16541913 16541939
    0x605040f060311070b070212040b03040b07030203190b0a05060a02060a0b03070515030a110307050408011401120f020406080303010801290a031e05010203160f030b0901050d0312090804 81
    0x9042070602d8698640303a410000004e5801d469003000711a6450f03a101d40c000e030305060040c038130741c0030305940001c0c00b14060001c030010314040d50007a0f8803031409a80d4400144e041384026510418442c83e08402001c00d80c44540101880702ca000e0404801c0b5075031000429a250042d401d2040542c200608101c0500e0f1144a25054018214010401d8034500000300d88807403e0070003c0750300084d001000882c110007a4008071685e0030202c00c43c03992850040001802e0b41c04c54000c0c46102c2d4200202c044440a908103183c0c10380b500c3c201079034090841e507560422502c21500701241c0183e1a00e1002807a800e051010714000c19070000082a61355021b42c00301c45044812b81c2004040260764a58051070300c1e003040b190181e07503000c0c909809a100458490780398520b030b60001026507000000308002895154840400c0200a0305c86010202c002401a420703103102c0511582c20080c0c80004000300d1620040c1d90000b5802401e0614100305100e0412041e180900002e4641a400150402401540500c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 16544413 1250 16543163 16543169
    0xf1e03040b0609040201080106030c02030f0706151d01050609030c03010510080c09010b0a030e1207050304030606050d02030604120504030506090a0203160b030403030915050f0603010f06030201050d0207050c0a0605040f 96
    0x41d00c0c886602c2e003175001801e603200c180103030710805941d81e003031089241c020000c90343e8808003114460307210440c40c600350000d0414000904a088100b000c0011000141101d030404158458580d41c1c1c16800c1c5010310049800080c00d80b0303818404c5030921901500e0a1107880d004110484410b44c48505010380c42e4a00b07402908000d001c0d0302c3e000300400c80a0401030a407100750015160105d2101d002c004464a4198030420321b40c090900016418200000040100100c070b00c120b509110a65555080204102c2c0d0b4000207501900712030000740c0081c05810340c600300c991480c201103003407a032241c503542c0c54400300f228513607a030343e02014900040d85010051904100290150300942a0910780c100d102404060001824581c4882c400003c1001d401e114400b510301d110750400c030603e084405d28010100995070f950180d407911640c480b150b5640d01902041e00d0301078480500c0c06541039a44030081d071103040c040e41c0600810502c1503580d41c0784555580204402e9407440e031540c1c10003c1d0800440650b80c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 16545663 1250 16544413 16544419
    0x903140d08060f030705090c0c06070314070c0b150a15090e060603090712210c061d030f090619110106060f09060f0207050603010801020a0206090c010905060f1e03040b06 75
    0x1d0f288199400905241960415030303002c05580c44011130342c1c000e13005540014515020f000b080100c070a40c560300010164000c007488034802c0e103d010040d035490220705409050180c02c1d10000d003400803c1c00003c03032005d001500c02c07005240d84444840c40501e0700030014002544030319040103208404590a600103008031402840c0d402d081c05c009640b90181e00c07800030100601b821b00b0043c0701c40003540c801c3c00c041200c40068940520305004090391041c2000f107a401b031800001c40301c40910110370706185d245000c01103140c03444005001c0d0392038204a90700c2d41c1c002000c000d625401148040101035002c03251315460100003590444030300f91200d5800400821960b5901c0d141041d91201c02a011113460f400c10402940000030b089040903002e401a54024900100002e12070405500034231b01e0400d643d0039564582c548402e07581d15603c07034080c920b0000d98102800d003d20720785440200702001070b0044030740c5000303503c4024a04240040001e41e100f42030110800080c0032680c050294000c44c12 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 16546769 1106 16545663 16545679
    0x2011218060606120c081302030f03070303090b09030a120c0c05060f06030d080603030301051908011109090c090d1b0f0f030c0503070602100c0903140d0806 69
    0xa80701c2c42c40080c034074081c0514004c8180c481d140000c40c036170f03840307602545401000b00505802c0900603030b85809244903041c0c8504c030810080130110f200c1e40380401d49a840b401c25110318480181490426001003220000c1d89500c40911902d03101e0700781000840a4a40e07100321340340c64001c1d800a102e4841e174400d01584084101606104031000c508640c100518070b84100c855920943c1c1c91a01580b0600043c0554502107010f8110700030400501a22117075605e0b400e60a484032001900400c00740021f510040c1e081c440080da900c5500d400c0d41928008020000c9034000106da880070b40740d803a103820344011500d0115601c6c0c0041c00010300342802c481d1200f030740001101c0584011519504031000010352803e002c2140030882e012030300500b030003c40748042c04000d0501514030000700011100d0100004813064002a903060300303200200100220700c80041c0041300041c10043c483e50392 = true := by decide +kernel

theorem cover : BRFrame.Cov 16366913 16546769 := by
  have h0 := BRFrame.cov_init 16366913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16366913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 16366913 ≤ n) (h2 : n < 16546769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
