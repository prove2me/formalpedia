-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0753
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:35:52.023993+00:00
-- url     : https://prove2.me/submissions/a73ad86f-b69e-4267-ac7f-b9338f0a7ebc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 135251798 ≤ n < 135431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 135253048 1250 135251798 135251803
    0xc030705090d0b1e01030c060e01020a0501060305010b150903030403030f030912030507020c09090309040c09080105070c02010905042003130f050607020114090a020d0f08030a0603060c090303022802030708 90
    0x10390b8100d0150300c0e851107031138420004010032412694451481c01c096480d01004848949403444440c2c114050200703648045642401030101450003031b400004c141c101c00080180c01190010010300b404000c0c46640441d5601005680071290141009032442d002c40004800030034010f100244000726844100000e80c0d41540b00b82d10560986d022605580c00e65410411001d00c1154108000c0d03004020403405401c0c190003103205100c2c1400d0101905456141160075070344100c58403c0090000750f500e00956030301154900041c481942c0c03c0046540e0040c41002c050810701400c498800000302041603000407050346141d490304001c03802034003042480d0540c2c8500c002d560010040d07007001d10100103e480f50440b280a40c0070000200442d40d116400d1000004102c036081d03803e80000045000070950141c002e500c200e00c405000901c4a09625228044840c0780100390304003c54460706000090b0001400ca8820014090300c0303004001c0c108140e01910000d0344000d405000f08070000070b008200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 135254298 1250 135253048 135253051
    0x703020f040b190e060d0510180f031706040b130903091d0f090601061e02030415080612030315120106050a030317070e0a03120201060f060c1a010e0c030705090d0b 72
    0x40325013680d0381d494000402460a070800e202600981060803400380d079a040d0f5005808600a0741002d83c074086154441d18889070300c94000350082840100110172100c64860155401541220100b050200e0500842d60b9640c90451030800f40d03075140c1003d01414081e28000c8003c2c080040c6070301910f044818003000e005001e0340c86030218110280403d142000210300181030f1180d960380c20f0b4220041c00c003e03250b0781141061444c00e40c00200710100c0d03280c41c0d0027590b680c0030446403142c00b910b003464018420842c0720304e8144c443e0340d00b007401445480000320301c00c50901c4408455542800000200a60041c111030f40001d600c2902c00c0800020507422035138241a00d0150b04038540a55181c0ca02550180c40c00031290354442c076003900510008103105541500001140300006820f902c542843d1002c1ca12a046100400e5807001c02004000c245a080c0740c191102100250142d49030403507002d9a880003801c04482210007000140340584281d05a45100d90000d042c401c10440c1d60030b015081410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 135255548 1250 135254298 135254309
    0x906050103050c07050a02060f0913320a0b0109080f0717030f03070311090301060b0d0c09150302090607050613020a09020304030f03020d141f060906020703020f040b19 74
    0x4202c00581400100000d4074129034010303016001800300c640c00c118583d841070221084840050080c0d002c0b82c0c07903024003030080e001603401c0020281144d0740310801e016100700da40010542c880c511900c1000c08a05c075a900000c400301d020911200c800300580b002c3c00c007500590407611680c25000301c50381e4001403003030440c0c5841c10403006010b124a04144c582c4201384440000d50360410100324440e1181c3e003c98566462880400d08000c4084002030a41d0a141d00a036100d02010070b455400560902c0ba031a00245981072484001e1303d0308001600c11441960328200345940070803540945e89a40d0200c07402150320030b0035505241342802600400501d0000107901481c4240d001080500300c030300c21640915059207403141050040003044010b58000c400910056480304502c11007540100d0079039000783c0c2031040200940803000d212981003032440d40001e0401c1a0040204981ca13004106441601c0e015101d40c411000c0c0c5801040251000d550301d503410000ca00c4daa40c2c40c030359100001109648 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 135256798 1250 135255548 135255551
    0x11103010f1502030427020a030615050a08010b0306190608010914090312041b030302011b020c09010e150a03060c0905030706090b13080313030c1212050c10060906050103 75
    0x1511002a141150242500c0902503801040b0a00c05881c10f859121b0104807003005000290b408809001c099800c424902c2020a132588000d0008506200c00c0748442c0141e40340050902107031550003000c091040c1701d83d80d0a10000030220340700d9203a00c2e03911403850b600a040c14415940c3d074080100b01020910400510500e80310400504c0c44c2c05602d16405070103404011401c0503500103005a00752005007040343e00c500c00080c040c0b800520540c50100450117600006500c14a05c1722983c14110b01129032821034000d00001301050360707010311081c1902e105168400700765441c00d440d100e403c01d84128003903111100d44000805c001d81500800d20300f800581e10800341640d21428155151000d003d0350700442c111200501c254004003028140c08190b220200c0c8405949035002400c540c004014000000940344060091002c00080c000041101c0c01d1002e1442c590750700c41198004601c0c4940040040015000c001c540080000d0161041011410401030b980c8008002c001e120b03074424180443d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 135258048 1250 135256798 135256829
    0x30e040213050f03071503091e03020a03080a0b0a0e010302130501061b0f15090210050f0a0509010e0307080105160509030322030f0501060906170a12020f01110301 72
    0x50a290003540c0345940006052100c040c14a010401c1903050541400d41602c11140e000450b02829410200c03050800d0301c001032600d01300e040015071441d450889414401d00b000c1c280c03000a50016090050581601d0014a103407a00004080076010700440c0551003401a00040b40d401d4600070214102e900c03c4030704088150010322441c0590740244030340c4020580d400100d10b143c901422066400348c0c41442d02c1701000c0a26950590441c41c2c02c10310414040c0c0c0ea05012046040001c0800c0d001c01040c01d040d0f0601c5000c0c407032210a40b09103203042c0100103010800c496036074000c4118900d0010000c00341c4510740d0b2200c12442c020001140c8011200b803081d604020303641c0c010000c6407060300c070240c0610b240c00e00603806000d4079140f821460100d10311841000000c5101d010800d004c00c2d01c204004114149840b840d039060f00c0342c1d9048a42000104018000c105500207204104254010f2402010b030144140607030514201d84281000d55080201801e040c1c1102c0740154140c803020303201d54560 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 135259298 1250 135258048 135258077
    0x91d010e090f0c010f1101020f190c11060913051305060601171308090d03030212010605090d02090606090618090906100e0a090f0f0303050c03060d08031e1303 70
    0x8401c5400c036000c0c2c294004296400140d403240380151400302041c20b101361400e400915803401c81c0e00c0241c0d16155082c0219840280365050055481d49000600e0405040b40c825110f0440303030b920b1b4108091003600005261400b949403180740d0040220501d404100314a4520384414500410340002c41d031a000740400100340390700443d40340d01d40000042205030030f0381d81c2d2000203812515042007501c81706030600c040103c5503034a14070500164400c0e0b03005625144034128411480106800207401d000b010300100006807101da590b68031150701104d500c121074903100701140107440b40050054000b80c00040c5105010030280141c2403601090794001440d60710702e41c505858020541c0ca44880c4942e41e10100b05c120040c0d2003154019220070000160b0851903950342030b2006814070212421b0107120850343c103040c3c15101e5583d11842504050780380d03141000002c1d607001c4200300001d00340040400032400398150241c9904c507140c0c100c00c100c01c09092030f140c22029070b43c00c4581140040d0480040b0040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 135260548 1250 135259298 135259303
    0x40e010c08160f08180106030f0b0a110d020901030609390c0807030306050603010906060305091612030c021e1201020f0304020d031206090b031e060610091d010e09 72
    0x444855940c915242043d00701c01290120300182081d004510f006000455a00080c0300e4440110301c280c2c1d010301494074074038041403203507401000004854a04031040086000c000d0880c0c080d44c0d0411401662000b03030000507802031425420418806192030310302a03600c440c0042d04601c3d0300103599a6580302018151f40002100845600c0002508240800c4001862113000e884010b200341008241640c0b184080b82007500b00343d02038190180c403000200180ca42511038940c100d041d80c001f50900300d41000e60f42d0402d031b0f40c61040f881c08000503100134040c140308501020031581c3c010314941c0c4644641c10300c8400380380e102c00080d21400032a490281c03410014030032130b40c0440c40f41d05c806086a8854080204850402805030203206800207c01c40c81c0a9510948000e17006041002038208941802d0600d000300308140c0d000c0c580b03001c00b00d040c0454400aa26903000c1011074a000003801208030407030320000160301080c0b28801d9101001490182180024113994140b880d00803180c1d200c002c0b195 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 135261798 1250 135260548 135260581
    0x1006030f0b0303090d0203070905130308060405100b0a11031605010c05030103030e0915040c0305011e05150a11191101051204200a0905010503100e03030a09050c040e010c08 76
    0x42e03040d4010031420000d400c0c90900340d06410700080a8410069039641d4080a807541101d5240ba80480c0e4001c200415420119442c0c203d07005a904008038a0000b000300c10001c0203028080d8803040200d44064668810b180910b0101c00c80410390751510b030070019913030030100d800000b101c0e2542440d40c01303044244140243c0b8100c03a003550760005039143c008180546004c01410042c042040d00c040300803035881701d01070b5044080d500e590004e038075850400a8660017698800848005c03000007000c12459540320f640e0011448003410703442d5140d072500c0301500d1140448030544928058040350a040c0046000c59a040e035004d107042e0700c6524280001101c841c0b0540410104003d42d51300407a01083d82c249443c48003a00c403150300d8800000c001d001a031841500c2d44842034081d1070340011b0010b03050500c0480d480b1600c1140c14019000321000321a100d0000801c02403850380d031510b83e407007030140800030018403401c00b40013001200101c41d00617028103c01c0250f00041a640000302e1070718036003200940b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 135263048 1250 135261798 135261821
    0x10f021c15030215070209070f12020c01090218010f06030504080403031b080310141806120c1305070f21200a0507050f0705090705211006030f 63
    0xc1a008101411000242a010314180440082190110050302d81101c420003064146101c03c2d180d0f1024070411200480090075101004280900c00d482c240d0407007a41c0c081c03103410034405612440f054080314010704c0c1404000c4c0d88003c107140540122038103940c45a050301d0b0700903030164003117464090136010386200b61341c014940503007000200086449084488200b070000141000840f400d43c44150158000381e5110304a0ba00b085020011509502640398068102781c1d407e2142e0706212242d40880e801c01800d45000d0411f010408005000a20882c12a040010290a200ca0041c00c911004120880301c000114060342c103488405c03400b400c03003040400f200840c03150504040d03030081c00c00b4084404010074040c0f14400d020101202a0002c0c10000c041681c8464403445982851840c1002d00310402c0b2040d044007100703004a484014200b82e0040550900c2c941d01c001040361198004844002e580d8020520000d129220100500d00ca08807011660f0a200d06500070f4030400c2110400f1141c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 135264298 1250 135263048 135263077
    0x2060c0105040b251b1b030c05040e013e0d1b081303030e1612061815020912061501090801020a05031f050303030903120c2d0408070e01030203010f02 66
    0x11008100b101c00020035211b2041300d01d0103041000f07010410101c1001e41040302c0100d81080240400d080c184100a00604c07004020f03c036a6600c1801c0d00043c0c240400941c1150324944911034610040441e61450300c0001d000081c3d85010303035100c2400902a03d18030700b01603e80124100d070b45500c03c560440c00707104d41c1001004a00750554040d401445c0c000081c40c0603000300381d0b40c02a40c0c0100404100204181c408081c1e0440c01c61601c18102d440210000e8401c0088046520214609418554000e241c0728401650391005000040240c0e402203c00c484a01c2020100541c1c0b10102c10200b401020a03200d42039059101e040640c241d02032800c0c92400541c041c00050148402c1c54014070380382500010b80c4400c180c43e08042401c1d540121104000e5074000107100040145411003240d100031410043c0781000244500103003000d41810040c0b4140240c64078070b014802d040d00c00c0340c0003001c280c0e04503030006503100d0150f40514801d2205a10035480c00300500c4404401d40220b03500d2500d0b42c8403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 135265548 1250 135264298 135264317
    0x3070c030201060506130e09120d020f07020904060c0e1c03140909180606010c0c03080328060303032405060703090815010503010b0103060b041202060c0105040b25 72
    0x412100860040400d40441d07403550350000710703900c440c0300030444511401181401c281c1401080030280002514004d420384c0036400400c8051030190940d161b00e0004070003d40e60383c0c0b00300c00c800d400f802540d0010754401104c2050008114140d4815103030406c40e9241c5070703800c0b41c0e402c4c01c0006181c01c0d241800180b00c04d403840b0300300003882425400401c0c46c0c0981041d041c109681c001c241640011150392540003400844001106010400303583d00860902e00703403800c04103d5585200d5181c452000800451000c400b22314000c003070740f5108240c0c10100d41c400c843d2400f04080e80001d82001d110a9001c07130b2800755584410441c0c14200564441405083c40311b562610b0140001c6601c03e4800764100b000011010903079030400d000f00c080c8a030010007050495410101014215001012a2418140f500c00100a500c551205a80c00c403842c2c00b0010008510728004641170f4840d401140c0540d51906013044204080c0e1707104203015122580c1226010121441150355040302c0000c50800700d0340500c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 135266798 1250 135265548 135265561
    0xb09010608062101051005031905031b0a0f0309050406050a14010f110f070302090c0a0210020c031e040e090f03041202040f05072c0d1101090320040606090b03 70
    0x702d108440860100b183c094810310032807403803c4a805a48800203030003580700030419031604020000d2075110144d1180d6050072503a4806030b603441494508444041c00100110710703500144500e10b01c0d95049000c049154180d0b14004299451a001e058402c41c43e00ca00800d450500034040170540d140c02c80780300d52101c1580010b483c0d014101c0441d008000301030f508044002c0050082a000308500401000507a00310710400c10010402021564154400c3c0400e51000340d001401e0b07004410360480040e594105541b145d4294450321054a600d500701c201c03800c40341044034006000322600c003000120744d92203100245031140c0010b2104546944180300c14480c0b40d1494084ac10300b00c0c0f006000003140a8840a03001c00d8550841c0c1d0031340840c264100308c024407064001500c400251000c00f41000701911340004400c1c509040c00075051052180b50849241d02540c0c1440c06142c02402d0480d108480ea1650495080e030441d40a0040d07040c444002106400307030342c580e800e403801443c0c594110355804 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 135268048 1250 135266798 135266809
    0x90b1306113021040b150603180c0d030909060b0405010807030b0a170604020108180d080402040603061508010c051303080706090206040b090306010f031a040c080d030c030b0901060806 81
    0xb001103100000c0c042040400c40800e84407108201820308044200300e00d440d0804600c45000180003060ba010410f0901206640704000c407940000d0307410303011811021842015142c200d0400803a80c00c401c070301e10003800345078104d143c1400b1500910703800d0100c103441d500d4138503180c0141e100e0503010403d6127000c190600e0203a08002c515110160421a0881d60741d140e08568440c01d03c918095508081c040c0f000b5564003140e45944510350707080499283c0441070320076540e4001403c2c20000c010402c0c01040031907030360789c010340000d40c0c0100e010300c6140710100a00851000f00e00c00c101496103049d49400c2260301860560701e142c0c00c0781c1c4201894a203103444120650b03004041c2150900c1c2e403080c15030010780e40c1c000900064108039101d00d488510314018140f6201c01a080b20700c10190784c180400000712f41408520380c110f5400c0d250715643c3c5541c9401c038045a581c0d04280c2450084200400c101507050f4442121004140d80500404011400b8004182d0742802000002820308000402e00c1c14034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 135269298 1250 135268048 135268123
    0x60b12120f0c031c0507110607050d090b040b0915040b061c0c06200606030c121905030a2607050c03070c0e0603121810090b130611 58
    0x151092685421580c0b90141c0c00c550242c40798142d003260082c08031035914a24800c89a00120b075081800b451048013104942d0348900904980400030000b45042484116403c030111070f580c09900d03260b46041525214602007422036100d000703032180401c9003030405013a500090003560050740d5540d1980b180e03400d0100320309880c82113164031000310f9500000140709510101c01081d0a07a0790300c0440310030741c098601d54000c58480c1d030100d520140070b00046a40107d071621400d1001c6441a0340075154030329050501040d20380304a500070b040c2c803001080c442c0202c010301c2c6905041d50340c2034000d02d1400000014102c0311700f403a002c041c1c1d218005100d203030082e00240100704141048a003040c44603610b120b40320505410860500310310030141310083c1003c01090018442840b82c103414403181035030084801d645004442d104918402c0c854a56030301501c240703000740904006055a40c1c009070b20902d1002c80c0c62084800141d80d120304690390000c04078200c0e500c00d0203021603100200f061505500140315 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 135270548 1250 135269298 135269317
    0x3010b28050921030a0f080702011116020d02060a080103060b010c031e02030c1603021201060806240603090102070b0a05010605090d0c0b03160f08040b0105120c060f0403060b1212 79
    0x49000200454403020405010317007260a90366085c0303200703800c0030040038a640a40b04005582c14144807101c1110034100791810b900e003111040400418500002da01031141c004040d402290004100d20103590150009040c0c034010031003880060002c500454001102c9400500019420343e1100920117a040c15000d1501d5144116814030001b0310a113810010f840301f43c2c10546038010b2742041107042000200b0a0b00040d0345c020000e9078030707040200381c071010001c0540c04004040c3c4640e000500c04400601c0350698050718403a140e1070107100d91030003544030300b074203540209401001072a9a0014000c03681681c0341c1e82e69807801e06200300207000d10300000c100201c8811150150100303034412410050351180e001407010300f449152068000c2d0181d403102d2282e40c10418902e0070080880d05140e00c840c11a90156071100d42e08989109641c10890f80045080e440440000c90006c2600b410000d0000c1c3c4c1d00801081025110003400c1240c16540081c400210b90000711081d0f001c0070054000d000c0c40341 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 135271798 1250 135270548 135270589
    0x60b0d02030304060e09060d05070510090e0c03040b06041506050d0b15040e09011104260601030615050109050913140d0201020d0c1b1707020603010b280509 69
    0x415680040d00b0354009421450000b10080182c01244c54560030031070f00a6415500404c111900341c48064552645014983c0599100510540bc503841151158010300c22080c41980900f8100307001101903001b61020745240d82100d01207100741c07800d80310708841004500a041840d9180440588040d0000c0c0b804015059481d2410000c0c0e8660a02c2414806103556000d5683c500745220a8100a0040d0071603c1c0703a807400340800d1080955100700c9056403200c00310000d200040208400c1544a20020805a8000d9400000c100800340d040044c1c2000d6680c600c1c0e007015120300044825030043d00c40d0961050708440440c004c4241025110801800344040103140c5145a0f01589001c4140100c0c90060390700081303071014800940b04d02c80c03006119141498030120590102904004000740241c640c0804460490341d500c10f040407034400d5640502104d4503581d40325100082d03500304425104e151642d4401900ea004180c404d1b4405207034254503002c6c14075230844107000c2075415440070b652020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 135273048 1250 135271798 135271819
    0xc0c01030f140c0a14030f040f06090516090f020906040b09041d28031205070915090302040608030a0504091104090e0c041119141909140607080403060b 67
    0x90300c0d0b82c02c0700c600c83c1d403801110301da880c1d00c044c04c000c142228601420110400900621081c0101d80000030b81003034215540c81082c3c83c450600303200804005400500921a03d01403d089034582186541110711901040081c5180034034500141e00c40d0950032039000380c00700020701002c210030000c1e040c0081c0141c03001440540030100050500c40c1901d010503a54000f940600448a0014505800004e4074096180c00c40080da4080c2c5405000c2090301c0c502d9450b440040c00f02031281081500a0050300d94161701412240070181942c52075010a038000d81c141407003c030300070320004100d401c041e9056548034509031401c82010001c3c4582c002c401c0c000f180c01c02002034400e0320f5018a6401100e1a4090407a00001c8000c100494544043c0209400c1d0b0078403540d4904958104451400d1036641050055030401090024640c0300d0b8441c01164072148031120030400383d1106500c802d5403012480030000c25107000800640340220710700204905002c01083c0002202c82d0003800c50000050b1817020300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 135274298 1250 135273048 135273071
    0xd08090301060605031803120f07030e120c070b09030a02150d110408010b040603230a0c030f0b07090b0702010e011205010801052a040302103b03030c0c01030f 70
    0x940d00710303038400f2001410110504c03001c00000140d040049882a005520b0510321140c0c180c085e41d40141010443d00b569800105807501940003003001c04481d8081c3d07404000f070420100c82c00d0300458108031161280c588003040941081c02101c04003103000300181005043c9a08020788030030f0b00d15620b07103c0002030005281404150050494024408541a80303643c01c0c441104c1c2100c0e0300740000d40c4210304000003000442c41d950180070101d80707844c5041c440081000d401c285842c10407440105400090b075030000038080c1442003403e00c0d40c440c0c1002866615040030880d28800c250080c1d0380070100c1041400c3c011742c00360454000d1403006041080d1560144050082221403d92066038075944030720070401d400d0b407a400380d0203242410301c030400d20104101e50400070383e02503400000d020381c1c050035041d44214041c0b8070b400c1001c011200070b074030225822030b0200780d01003c1d05004e9201000c2141101d0541ca004000e90782d14001d220000c01e54410018011800740c000c203808048241e5481410781c0c103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 135275548 1250 135274298 135274301
    0x302030c0105090a02040e0a150b0d140a120207030506060108100e04110102120f040509060301021b0f120702180703020408010c050301140d0b040b060f0405040609020a1509050d08090301 82
    0x4200c3c19000580202c01c242c1c0140416100300040c00445600704015460025208200400c00712041210002c0e010640750301081c80d450034642c002d409641c0200e2140c609800c00a201c1c0c40c040d00c43c034071000130313034403446000c0e0794035019400300400d25000900010700c9c0d9480f6080e01a8008004865482d082c0d41e1b41c100711041c0c000940d01501c941042226200c02540c040180780a00011100054504182d45107600524011030144502c10381c21900403c446a0b000d4064403040038050801072400444040302a80d01c020602092450b07008a041002086045405485040d90050100c902c0c40b400f9118001035818010a03070f006140c2d00340808a0404401d00c00c00c403001c05075443c3c4a54a504248402001c40080494984140c410248240000f40044c42907504142e02541c5801c103078494000103886a0421000f03150400c0c0341100308010320100350003961206000707403600303080d0070b481d50f042000e048101e101c0d640218100d6103040000d420400400c02441d80903503440b60401a6500020f0f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 135276798 1250 135275548 135275551
    0x303030e24071103040503030414040905060708040b010b1602040504030314070504060809010b180a020f0d0c03180b070e0102190305190e0d030309081b010c030e030915070302030c0105 81
    0x552418480100300b811900b045004103004084001942490b1402d80080d6692255006c1e10900240040165802d5200c5401104500c0e500409a500030724017034500601d900d40c02c5400752000b03000c080002484a52503001c5415403e0000350154442d0421b8080c41701511014108404040d59410801b1440320f00c03030080d60103103400b0b41d19240c1d5146080c50040440354080d10b03e00310359141030038014855071031400130080b0b01b140b038003c2c521030f68410718000000c4c02020340f0110400800611030701c3c1c0c002030764490109008280c508102c0581800071401c0300c400c0f502c0c4014682210403000c41d50040c000d090803a2140f10503c101d611aa8144024903a0b2040d1040d04601140d0b02185451200382b61f80e0301c50f000c120325844c02228107201580099041c40c1118009000c1c5552a0b02103802e001e21300040b107244d500c401d2122861041568502802040c03003041c0400000e00d003440504920f180072080b07401103e030080c040511840104043c010b282d000e0030048055100c01c00140b42400400e01526 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 135278048 1250 135276798 135276853
    0x203060708060a0e06030703030f020f1c080703200d0b060d02030a0c0c0819050d0e100b060721030e060112021c0305190509040f060f0e0903040303030e 67
    0x10300785052000c00d00c150b00e0003e80012811188420401c282e030b0b100090071400302c0e9094034040080c1d003110f11050303060002c10414a040c9000307030303000318641141d50b0811554440c1142d448003140d9990060480072104265006003c020b01140c08501d0032200b40d0140000c003801210020b003c9001c0000100c0396480041405000c40e0044200400d00801c1d129506582c01c550510403500e0307007640c1c0d900b0005c2c891359140c9000990000c050b8400343d072060003586c85007007010004206079009002e900380e840ba00f288120b0b045500b401c250f010309040440c1581d0300380b2350186003042d8082c444a42c64007800007020360074081660750000b2016010080210600816501d050784161250300d005000120000c07904210f00300702d81501c0c400002e64000101c0d041c42a000390841d0310515415011a401c6c4240c80d01203034050300341111b410408895a21400440d100003885800b115075900515010301d104440003c6560400c0c0700410110340260000c00040c14a00d09540c00c41301e424031507401c448008402d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 135279298 1250 135278048 135278057
    0x608031b070e090a060207050c0a260d0f03020306030c04060b0c07060203030c031f0302041518060303050901140405130603031101060807170307140123010b0318030702030607 77
    0x8180e1411401e01180d8050401c014a2000724034211a07220394070840c80308011302d0140d0024141c030500005100c0000269002044e14902c9688d6450002100040d106103841130074281c0e141220509001525000728007203030b110031051180207030b000d030000d4000910040e01402111565091a5030781e00c2400050403030b1554a035201c0c4421608245450215003000043d98410824080b2200900e01560341c049400c2a050040c501c512500e0f00401099510007904903083c44003482c0200c500354440020359450880b01c0c030705113940c0c044010681d8810320000c0e010400c20030070984a5440380c8065055401e1487e0303580d182940c0c500104490f41c0390010740680003a80c80c0001d20405d44e1001c03045980036400c0c0024800d480c1800c0403507480b40c0701ca02c50300c0701110041600d03205001080c810307200e0b4940c10200b00000d5824402c0105e018001c1c82c81c09034140c0e0440c80071600340c00b140d0702b20641603031700000969003107a6858111b002d10064007003003512540b001b030111800507034041003550f109a4407541c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 135280548 1250 135279298 135279337
    0xc070515070b07082a0c010c0203041a071a070207081501050901090203041101050c0f030d06030203070614030106050306151801030e0a0506060409030e030a03110607081612060803 79
    0xb4020798140c00a0400020030046000b0303c4a07802c0084501d1242c00e80503800407001505002115603d4814030b648403281c2d50800902160141c0c003c0042c1046801c3c0c2070f00010200880aa0040c1901c100000182400c0d40c001d104900d048500e507005500c00807500403102c81c0c0d9241c01c3d0071440d000522802d8491424407200501150520320030705401030500e8041035085080039030b0f8000740301012800340350400401240c04031050008015401030100f50384140d80c0d54000c01d01c44c032400f500c014001a40030f8400d024000070454496111821840b44040845046900b00102250b00764000b40c02d80350300040841403c56401c0640d00203100a0201511800c0005501030001d8291501d480b80250580c1001a10002080021420302d5000034101c400003104145403900781c0751760300340c0714140d5014411190140109a00401003511000c403400444195a5418104a0300042e00b00c6011300e120742d885805902482c02503103a2140040100d50100b0301f16207503004645141c020503c041c2039000b9031034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 135281798 1250 135280548 135280553
    0x15030a05060f01260d08040615030530041a0f0d020309010f060609050f0d0605070c0312020412020603060d050d1d060403020303090613030203070312110c0906060c07051507 76
    0x3c90868460a00782101451424850001c0da2600321005c014400d1250000010f0100141a40807821500c0e00080d00181107849040c0303503684244c82103a4045007001c9107180e45806040103004003803d88030b80034151415040c0000081d1007601c0c420601840030050249950408082001e06815030f800a8010303204e20f801c0b0389582c01d40d00c2554174142883c0c900034041c41545e81c4000181c040e43c4042e5030300450000d07000080b401c02840f044010b0502480c1600b44461150b0212030560f125009a503403202840843c0702d80310891156110300552040107a0490b4010305000019652080f0020420f003459941900c401d42402c880070020303400100642a03142c0307029000b108080d020302064801c5401c003811640400e40d64413803205014403c030404580c490003401d13011107a10166a000d010349000c1c0e540d030324004600400c00303820030f004900c0c2d01e4100c02c2c451000082015140400404200a60b1610402d1021a5100045a402c0c1e80101c4d04041450b450340140c4105a480d48540300795200c2060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 135283048 1250 135281798 135281819
    0x23010b04181211100c211b1d0907120c031509020f0307050f16030207031e05150c16050606010f080f010501260a0605100c02060315030a05060f01 64
    0x44000106000706480340301c2c09000009442d000c5000341002c0020b00c1c5c0003030b0710182c542e203140829040d00392468000c6640340d0f10464100c100d800700e0000c0c1c03079441404010b1054400e805d6260a01596800c4142d2041061400d030a2036078001d81e090600c1c001c3c881c00d1018031001d4420b44142c10012980300c01200e121030705107444943c0244a10442141800315940c03403409176100c05410081041400700c0d100d40078030700707450498040750080f00060051500910340651103207032601c010b89005a120103c100711b10244c40f42040b5165014024181c501014028a000c0d2800505440c5074810284401481780049141001889004d9001800da5250503000108030054030001c10041000100610100e80e440b2004035054950900b017042c490605486000b00c0f00785103a054080c45d110300000c0c4544030003164007010039104292a9614400011300003a02d8980b581c9500a4100743c04000240c081c1d0b450004a08440d1002400e0315040201c548603a45013280070b40e1185180d070b00c540010061280003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 135284298 1250 135283048 135283073
    0x3061a090105030f1506030c18070e01030204121704090204060908011107030c030e060708030708060a09020306060a12020906040611010e0105060d030c060e0708010e071223010b0418 80
    0x320020702c001132801142c662180d02c0c4400044110720783c2c3d0042401d5a9041c8913916814070b0107000c44a01040c04c083d2445c0400b13050320701c0008110103005068055111303000700d4003131351040d0340b90224280c0e855454202c40c011140541040344014007003c6154960f038001000149181da513002c4029040c25000750840302d400b50324007101c9104114080001c2d80104c6850070342505400c150380c4100094010403610b10617940000c041c648008208600e1030703000440d181c0900b0090f942505031503103c1101604030f00c401d4841d2644554188800c510390b5224818011045031165405414681d101713011803043d4101e60800400704040e54103000321080d09103d810f00c09070401e4001d021508040f4041940000f4088000d003c201840d80c800e0144180d81d005000000f008004941d03c940e5a038140500800b50041c50107070f20b00032100d00280c1091241c0f844155541c00134aa9a00203e01a0000b040301208550280165483c1c00301c0807030a65481c410b03000348000c006040304031100d2615104406090 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 135285548 1250 135284298 135284309
    0x402180a050d0b011503090c0e010e0601030908040b0a0905060c0c130606090501050c0c090910061d060613030609080d0b1c1b03050a05030a0201110309030f1303061a0901 75
    0x500e48246004141543c990314111890213016003030046403844100c0207072510040150040004000000d50803806508845c12584802c418040940301c60b801142a01e00c0e0020141070094180424095000c4010060074440050304290213003d6556002c100e40342c008458034100740e0014504d107101810444c0b03102c031410f40040020042c050800c0c402500d02401e50145a04100700401c1c894820402085045020351009140f01c00da440e010b00710695902c0e000c2000c000460a000c80000c0100320f1f50094406402110400e84680c3d407841c06008080c1c11003203981411404914001005c901d85129029000e4003c20000e0340e101120005442556031502119000350308138080e0490001d84586040c4a00c0d91240d6400124108007400d12500d10103900050828060080d40c4420070000000034a4200c005800a02010b81c40c1420b440080c00101d8442940307070010002c0d01c240300c1034000102014002c003a0000d059540741d4540400301e4049804000d01c82c0703e140d0340d200d0300d4500b56402e24014074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 135286798 1250 135285548 135285559
    0x6020d05030c0d0209030a110f0d0f0b101509081501060c0f05031b0c0420070b04170403030c06050c0301120602030402060c010e03030a141314010b0402180a05 70
    0xa001001011448010411103540b0302c04111590009540e030101d494040004044844207207503401d04055003044140c801d0702c5040c00100c05882814a400910714545d0042040442c0b040d40e600c402003070920081070489484913004011551034070f1100f01e920041c885556a40411b401c004a20380741801c07c1502418582e079510040003115070005100300002d5000900440c038001c18a4120b00e14062200552603105461101c0415150b000402100301e5404440502901e240022200c6002c007001e88100d030b41400402903000402e1110f8600e0350450311074035030500c02c042090032000c00c0340c000d42c00c1140010840034403c01400f440303008064020103030200f198515458401404000301e44400c00601d09a000f00c0010159500c8009581400c0b001c0b80003030045022482e019034803984100c45d400038051410600400c00c0e01c400603014800d0f141c400821082400c1500c43d5800002c01005100e002d64950020b40c00c151101d00140a00c01d040c100652003010241040000c9a40c0c190445030064 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 135288048 1250 135286798 135286813
    0x16050708070f1d01060309050106030606140118060203030c0a0c0f0b01030605150f01030c110312180303061e0d0f03020304061403270a0804240e03060a05060d1a0609010602 76
    0xc0750000c102e04540546c2400250490f1034509079000d131403103a1002c4c010528010000480700300c034007c8150503100036642c018108201315060700c1c055506d0302449005900500002e50394a281000915104100d4100114090290703980c0080426241b541110b041c04d00d21b00400c100061801407507005070821544641c00c041c0c000105108009501c170145c105915070420944850050720b28030f10f03036079201044c1da5480c51400d107183c0b40c0840c1920070b180841d4200e0048008501d022042e20700070030008140e2810015291200d56603808040b105951000c400c90304480020506040341f9070b5640300e60003441d01ca6240c40c0d0b002d841091a0601084241000c10030481c401d4404c640d00340b00708011000c0101c04206080d8103619010710224000e04510707000801041c9038075030042628030101e1001e004001c00000d000f0440f0021030703c0c011242c041c1c1c056404110790300c1042c0c02c0740b5800311000e0481c00c6e070258152207844182c4e8010001c401c50405110600c11345041500f111070240440b800140302c034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 135289298 1250 135288048 135288089
    0x2090604020717030604140a0c020f0d020606040b1512040b06010c0512031b03091b0a0501080402040915020d0509011805030f0a0212072009090c0616050708070f 71
    0xd502c03c06011819105001001699642c2c1d258004507100008280498841c40d01130304410081070310b031085c0c00241c81081951600503200040185401c0e04036406460180c40f15030900015100c01d0001c0c6074000d401001820701d010018025203207400032003100130700c02d08060034804491280608030070304100c46d0080b010041200003510b00c2c980100101d010f5907e5036100715126030034407030030341d1262501c00000c03e0056800000419225100901d1084600c10f1003240401042000621860707001c900e4010028015141507841103441a010b0207040c035034400ba500c0e20408030f84c40400d6807070000d0799807024490b03100d00c00d00c101540790f0740d00c01c4052618007050b00d0b015528090388115548880700090002c19151090020b00824410505010340f00c81c1e8501d440000c001c0c041d046090000d2a0301e118a4062400381c481340c1c0100300340030160201341c40e0101409450b03803208162100c000d031401154000503004000d010024040e18014000715410120b1142891183c1e5004400c00c20390703d01302180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 135290548 1250 135289298 135289313
    0xc02150901020312130b041b060206060109060c030c060203130c080105060607121407030809010e0a17160b09060103030215060f10020c04060b030604061e0e10090507020307020906040207 82
    0x1603905900204c029159500d4044145010251500608002000090100b040301c0c072000e0381081d100748601e150a1a454801c100d980381c0d01100c5507400102c91020810045000c0c02e0b030074400c0e80c002e103031a00c40030b082503c1d018140d0b071082d954008612040c40c421014402001c001c10041d10110740244054148400010b45501981c0406005910031240106078240204a41002c002c00f0004060b00c5486500f0094202c0c181199040019400c10340100c0d0000700c0424001051a4881040b0080400c5104074585980181c035816000f05009041200498030300c040592040b882c000003412250305528000f030512000341c100c20958001302c418010f403503032102d140781c0b4254010703500500b00040340c000c124a009580d03501d46812500d0110082480c4c0046e0004503c0b9240644040c084c8a684490074441e41c40e140c5004495407100000a00298404c02e98140c0c000802512001075280c03241e41d071100300e81e000d0718440c01507800000d1080840c00c1007040700d680300740129011820b2800d2501c80c8503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 135291798 1250 135290548 135290557
    0x142103070e0d0b0a150801090809120d0f121404080903010c08040b0f040f0614010608070f021c0309020a15020c0d05060604090203030d0906230408120c16030c021509010203 76
    0x200503500c5845c1000039035020080c0000800c0d091000b4001038100782402e090a80c08801d8075801136507505050035040600140030303c88101c00350b840c04104c8015031000c444001031102c00320400c685a407001800c411250300441d01903406421200d603118040801c060864643c1c02c51941030000d03600401010440c961010b95004480140c1000c680c1d5441c9484d840300d4840c080000c0103070b4604000b0741900c0402e0316109041c0e4549031103982c4261181075050740c0c08503000f0060001640140502458005000318034050750150f81402700f84820a40d00080c80900c45410a410243d105108030320f480d41d04001c3c02c014020f040d190346000d08441d07250b15031030380001010030340260389500704001152410400c13914020410700c420080b00240d49481005440000c200e000b00324055502d85c2d0061352040840c500031603204640034a0a06d0300c114604600d00000c040c401140720603c020a040c2e2030120080103d40c1c80703a99510960907032441000044400c8001c01010313030805000320481c0366000022035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 135293048 1250 135291798 135291811
    0x20601080f06070c11010e100518090c07020d0501060f12060b0105040501050a0810030b0901021305040506091f0f0e091006050303090609041d010209010f05030601020a142103070e0d0b 81
    0x740c44405000d00588944100003401030b0800308010f1050070450348a8050f200f8410060704055050700f02c0300c100304451408cc1d506400403042003100c1c0c001460140310044e450f41c0300d4400440c042d42d84001101900c031582c0d100030140c1d5000c2055034204141c6200e540d08650090820a081a0a000000702940a0f410002e070031706c0a0400490f0501003003211603801164014405c002a11f46030341444c0c043c2d0000c890340c0d0040c025400c004504c41c5468018079114040142c0101780c01c0d512a200080c500002c01000802014400340c086900754481c4609005004410240c000b142480039240c0d1805a4602c606080b15251074000d021507a0040200d4004960840c1c0e81790312421180005802404100001c100c0040d402c0070424503640190050300a001e400d80314210420b02c000026101c9220403149540182c00c51441100058920000300b100a45480f0403034000700c2d0409914107400c40120080d052200e408010456030990040c595952804265000d10003042541d503511994000501803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 135294298 1250 135293048 135293063
    0x170d0f110f0106060e04060b070602160f0309030309050f0915040b1e0301061205030d110d0c0206040b060111070b0a02120a0c11040b2d030a03020601080f06070c 71
    0x58500610030040105180242826034035160400080c0c1d60003007a592040001048210110720328901d0203205e500202c0b441910400e2400800d03566840084d0b00280301c182802405240d03007000b08e42080100d4840c02e100c1c1d1280d1003200c0c00c5040140481c200d99004074030030308160034600c005840c2c0c8010030b43c008040360448212910782100040103880d60094558120410a0030802d0207640c3d139624880c0c0000c1503008004068844010b420a03469980300504158030421401c4450b109a6021640041c004020a4105071030b0006000a0f1080e10040724010380c070404c184030038041d0005860782c00440908007440f200d03440c02c801603102c0e0301d14031585c03800400110360f007000c47d8000d10505004061101d10302c1d07034403a0311103405040c10800da401a00c000200a8424005081511070701c3c0c9030801c0105a074030402d40c4046205034116a600466120501c8101c965090391001c1042e640014440e0300607180c00d45c1000c0440d40761030400703444003407164080380a00c0700d0343c0c0e0841c000d81d2000d90080751 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 135295548 1250 135294298 135294317
    0x405100e030712050105150d0f0b06042901030e011a04110d020304150501050406030206160204380405150d03020109080a110f0106060909090204090501050403030207020109170d 78
    0x41e04182c41c5074403d20741488441903c03801c100c01940154812901026407103e075548100c20320800c000c0d1041c0081c06070743c40803407030300c085880049816480b030801040810b8140394032a850410042c04003071282094a120494007440d80c240c0101141110720100030841c12464075024080190505d01d014000c40d83d605040c8100094981100e07070b4807107981740541d501d082510301900100d10b543c0c1c001118601c0d080002c140f03071600d40603000c02c0b42c1e00201050f0500d808240001c0711043e2003801242d01c65610000c01c2d186100312500540c00903c032080e1011030981145040c19098400d035200c5218514000c10040f038041e5800d80007c11503001d0760803c09200c09854182d004244540003d40340207004503600304c840350700020180e140c00e0040b050368021a601400e641c242d40840c0682c00202d0840b4005011840391980082107131400140042052a00381c0c0320607084031810341d030940005c0d40000701c1c1c109550b04180840000c04120303000ca031000c026808d41d10b85440c00116018100a03006c107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 135296798 1250 135295548 135295577
    0x6030105040f020910080907171506030a050a0312140105030a03030b0d14060601121a09060402310e100311040204360209031c0504030b01030b1902040510 68
    0x14103076615090090607428170039175035034000b030310400085034403403100d01c10310002095020b80c1180c4108036104042c002d01000c5070703040030301c0b00780d0700f00401032905031003500d03210780104104000c2c0848617400313511071401009203410b01b1815143e01d210744843c0f040c8070b80010040d6450010302d40c110b05404d45000180034800d1130000d545005a240c000d080c04400038103480380c0140108040c0c0c000c04d826240d540843c00e01c140071001f6240900d0982d100031105051042d014180402255031001005000611f880010b10300c12080c500c440207039500f2080d0b00c8000a0943c640c468a050207030061000a4038545400f0a4be04044003031030000800c22080403c90100303988070340c2c0545001c0c0c001004401200c01c0c3c10680c45201a1002840804884910041034006e01315072088504044014014042080d8840c0c80c140e1a40842c092a4042003000c0100102041c0c195030040d001e188510f081c4d05c0d090038948100d030704611381c08007882200342c410401003050b56180c140e2000490b000307041c001544007006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 135298048 1250 135296798 135296801
    0xb1f030e0a230c12010c02010506010813030305060f0a090209030c120307030c0201090f03030206061003020a0e011b05120705010c0305130201110c10020a0203240f0414120706051506030105040f 85
    0xa070640d00800d0880343d201d000c0b44c064004808001c0607500800c40d07551440e00454540d0004d540e82c0400181040044000c41d00c80d0700305035880341c00a0b00d003c0390442d07aa40450b01c060030350f034080e540c0703d54049039a0990380380a00a101c01540c084070b0420040c09803040340703912071217400002803c2c414001038440459010b10b070100005c081c0000d00118440d643d0a01a407220000c480c110f10664100b4800101c01d4001c0c426210801044e90321a0304801404006540c10741841134190305180e13080303140000185003000462440005000c81c0c50f00d503c0d040c40d0150035103500c10f501409043c280706c2041540014002d04000c40c64092802c0d001d03481e0218413190610040741d1889801201c00704404107e03540005582030124807d0303044074510441e5003901820512014014044002a8000f04841d00c0301001c1098200f0300842a0040180405507250700d0720b10340d1100707001401c4000c550711040c0050340c814503520860f80309400313405400e12070001e5498441402520310483e900c50903524001c015 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 135299298 1250 135298048 135298063
    0x13030f0503070e06040e160c05030a1b0506090109050d02010c1202030703090203250902070c060c030512040507030c060f0e061602040203010b0904060605040b0d0b040b1f030e0a23 79
    0x1400d020341c1d13a1b03100c07084034560410031900024496002c903000402680b003804d00151054011000c3c0d0b0800c02000300840741401147c00e07452103121800100004100c0c00e010301c3c0c1c09001480c0000510081c18504941045038400c02c08040d64034106d215800950000190b0041e03500d401401a6265511001980200802c03400690988a00004000d4007641a11110a4180060240b58095580e161484103034442e8034001010342044c06c20800807603014880d010a0079109060290030034561038150a40d04034100c600b5110342e4072481d020000d2043d1101601d0144c03c0500c0d298200101a04d0007528003c861307920a800740300700044c0c00c5001410407200910b0264003c0040d9942c0d41d5603901c0c15021340000c045240b10314902038000503120300900c2150203c412a07401c40d82000c0c105201c29008041d152269034000e40c039080c844072241d455801038130000b111001060100101180000d003200c83e0071502e51306076440100031401103644000b01003019040c513440c2960055801c81c0b134904004c1ca = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 135300548 1250 135299298 135299327
    0x609041416051846050a050604030b04060e190b0606180904140d0305090c0108010f0611030403081b0705030c0d32030715090b011e0b1303050613030f050307 69
    0x802d0711409801202c10b0f440d035a6001c0b0040813900a071030b164410085401c40364070800354000300402003000051004007095600c94003a2400080d50307080102c240341401124440100d0072a4501c1140301009560003015030000e0301a1020380c00c211400c1418088480d0304103846100f142440d0006040104800095042004510945507000c00c2564040d001c4c007400c3d07920040d10f00800c030300141a9440707501841d04071618500c2c0c01c07040c0c07842d028040c1d4030082104000c480c00e001c1000080007141c103143c0203042e11032080015428000c10300c00060700303021b26604418805c6e0846100e06545039500301141c0c0600e508091209020505d8002208038208811520041c554488030400a1180003201504060780644800c40c40703100820220750485030340340002098664040700501c00e400340b540321074815007821000b00b10410303100e0324000d550350040e065041d0219a820b40174003c1140900c00590003064618980246850720794000d4078880c0f44056013020440044000740e180b03413142e000a0303d90031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 135301798 1250 135300548 135300619
    0x7060b03030a02070602061b0a2a0b060103050901060e07050f04030b01120507080c0102070306240306050a0c051e031b030109050709080303060a0b030606090414160518 74
    0x41c8568400fa441d0b510500c241d4004d8000d18001840154020301c01d1165902001c104918003011134038252880301450345010303402d2000e002c61489004426505100180c0a00e40d16032451403d01c1c00101541d41c02003062040303034104a810441c0490401c151b0390400580d080054070340c0c0400d1400f01007405250f1015043c22035a40000840c08220789e00000064091020f644016403140803d070340e2540c007804610300581c80300104001207195a84080200401d00f2405201d260954182502400c4640c10a480e92543c41c014007045244911900b20904240d044c65420454004800000d8a0749900c44c8040c1900020020b94040300400700c07a5050140d1060281d2256150440700d0024641254401c010070100003000c0b03958640003065038443c9a00900ca240c105083c00c4115a40d5000603010235005042070040080c00e50301c5016240c2d142d10507110400d0303e85410f140500170200011410010301c90704120103141c1c1052902030020001c4192208234010030ba460392030141482d032111108040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 135303048 1250 135301798 135301807
    0x15030606050907180501050f0c0105090c030708070b0423060705030a020d09030b1f0506070305180d020604090c020c0607030e0f010e061c0914031908040f020607060b0303 75
    0x540c408415154140e610120355501e071a02600c2c403040703030000c070b0140500c008402c00030307584280020030030b09850141d0b043c00d05000c0c50803142075074800c2d07980040c2c507088412402c080b800c04102c1c110051180300010502c0c40d04c2c20101207024469030259102006d40121208072010b400384102c3e1203002e0207041c4554815250510549a8100703400c010018020f48801c154294032610640080d29000000821940c070b844000000200c1042c8554001d20021900014596a000d001e0000180280c56007075884000389006d1091800f92078805120700c80d981e1201000d0303201e180656003a203000100028043c614658140c0c43d01d018800303107540c0090f00050b00c200701a0300105450a004040d154840e048031104019541d11050041003500b00d03000307009203455035403400c801410611000300c00064000ca941c80700e0350000030640a4604c0c40d80000f1b070214101c02c09642001201d1500c2c0f4007140da5003440d03640c0200a0040e1b03c40a485134802180a00038080b095004007031841c0c005007141e030348 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 135304298 1250 135303048 135303053
    0x615030504060e0601081014061c0311010606020f07080d2a05010908180907020d0e120a0308040506100303210f0e0c040b15030103030318080406020312180d03050a1503 74
    0x11f40e000c00001d0050b00c0e01303154000203604411024a070141c44010602020b014041c483d0b00d04100901200360308010380000461204071003032062070041c1000c2d6000c0d0414802c0020020320f410300c1c0d07502c140c00d03a51007404244280c642c084004150b1700034000c1ca07441007640a20368031764a101c5d10714018200303518000c05802003202100c02002070504098030014491009004c2103440401124000c0160f00041d800034002482454600c46024008001d0403501c881f241405140c214803003401c402041e1034800344021301c90100055540201d850025116940c02d41e41c00510301e55840c0d0449180140c1c2000c1907207900c1d00c5801507841100701e55003c01640359088001e550303580c0c44602c4c05000b00e14040000e10380341019042c0324101c248411b0b55514691071658118000c013424203036a0b48081042250f01b0006459200a1000385081d03402980c0f900080607070340800c188003902201440041307003602d2900c0c04003c40d240c00b4101d80c47c05c000565903a03100400025100101c03042442131b00408000c0708 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 135305548 1250 135304298 135304303
    0xf0c0803010b090f06120c130f0e09010b100509130b0402030a060e060a030218040303060e07050a0836190303050108070603050606040314010f021b100615030504060e060108 76
    0x30040400c94046904d249050207004140c401c4d00e41d03480c2048406c0700005d200d01103090003049159000303545072020ba540c505082c2801031541c1c10541490341c1c44c10503c0880350090069046d050320403030344140e03281e40310100030f4042d2040c028100d0060b0700c01c2918080c2c022981e840030392440350281c0255928a002c2c0e03001ca0003401c090080c9003101c0c2e4550041420703410f1003403038801540e034042c0c41e81c90039401d2003070101d42c10000240110105a203510011400114031007040c1d01440300d64680380c0e15114084009000c41600500e0004400d10707803040103003021100404032a05a540d080d0f805011511041000d040000c410803030b0a084180d821104c0806034141c0c04075040340d4101c42910300135074035902c1c00c40030344005035116580040b0500c0140042080c0d504102d10581c50000005401c1402c01001c40c2a0780101c021902005014031125403042c0d024845800e0b20400d00d0020000c0c01d05020080724009150b0504404241d90350700000d041122951094542c20318100c00c4130155a964081d8a5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 135306798 1250 135305548 135305557
    0x6090f03080a0c0e010e03070302030106120b06040504031b06090206030705040608010905010308270409080a0e03121e0408160626070c08070b07020708011a0906010f0c0803010b 78
    0x40c0003914040004550644601c11501003000300e0355200711554100c40111a85480b400311243d05014003500000140d0342442540c004241c40000030854414604011580e00c4000300602c0c099810542004002607110648035548221484810070711a142d080410040c0100800250880800014080300783e8120002c0e008131100c40d515025a40e80b18880300050310400e00c0020013040040c4012105880e110200803416100da05c5076070110100000001d0603260480000e40305107000141e402002d5510156218155609400a0040e01c40824080b4802e1051450301800f0440c500c000e501d80000000c02ca0300180351200445000d03041802c00c0c529520f1840c8100c00c04070344801d00b40d042c541000304c0b00c030243c0c443d98050306810f6954010700b600c144681500440344800300b04041e0001850607030040d03015542c0355008080351410181c019086a44201e89805c11581d04c462803001580c510352134035031250080ca00301450741b0a404003a14a040805030081c03940d0701c080000f142e10f00e40d040251 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 135308048 1250 135306798 135306803
    0x315280b0307080a020f01050a140706020901030b0f0108010902030c120c03090609120403030e010509040c020a031202070b011401050c0a03081b070b0a0b06040b13050a050a060f120906090f 83
    0x110500740d80c03030605a54a03200399071300a4016000c4408404d03658002ca015185015050604c940c27030705104443e003e001d90003203404846280d030101388101c1e203592610400020f200705a6424804807000d07400a000491705206100c1c03201e030000001078107600e401c01640c070b007a4044003000a41e82064905980b040c0c2045441d51514411940001c01018000400050200007003003442d14090554504503543d540c20000c80b418450304024172113007502c2d140f01e00c4403140c01950207002c583d80d0130321300106800082da0794220b181340140010404620322912040c1190001c2c01c090411104400040e50340340105092540c03513002d1846030400f17064101205a204213840f2021600c21b8014908510142c010b112000c2c0038461034000088402c1c10a62000051030340c001c00443c00d0680d41c80202c80e41d6030003407400700e82141080804000390700b043c0240d840074010840b000c11020307042140c02008815042c111504006210341c00c2000032049030b20141c1007030380100e42403201c01e00e541402c3e003d80b003800340308 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 135309298 1250 135308048 135308053
    0x18080903150103030c08030703060e0109050a05090c03100b0f09010810060b0304080a0f02070302030f07050103110c03030606130902130302010e1219032006240315280b03 75
    0x22001e15003429000c241030b00e6143d281c000f01c0c1e6005841d0f0707104070b0304000e088505041d510400840c1180c58105414020000400701040524002e00075000350350000d080700820354444851421123540110300e180e40302c2031000c00020100c0380c0c1380000e40320300da40e080034603003203001c40c03002140c1c1c907101051040c510480400203022050307070b17503207904020311048802400452046c0300d207a03802d034401e07000d83c80704040034412201100d4480c0c0000b0308049540d60b1150095001500c20802c550f01402400c1001145102c1182414101007000d40caa04c00100002c0c0301b210005000c0da481d0058503042e0010f026400c10454440c40c42507400c1e11260300314002a0b010651151700f2204a25203002c4401e811030440014003d0510784216541c0801c10b601c50803420b200216294003002d800310700d03c00c07542c43c1c500ba000b4819402e082040c560700129001c1821a03101d0703d01e0320011075840001d407024101540100307003c402d030b0b9060300c0e4601184d1400130b040107280d00051a180040c9850300843d04081c0120207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 135310548 1250 135309298 135309313
    0x3020102060127020f12072f03071e0f11040506060319020c120c01051f03080f030709030b0906220f0609020f190305100c021e0118080903 61
    0x4460484602041d003044818100c0c441c03004450f24580143c01005102100d090411000120499040d03408803412000614003100803090b03030ba00c1001500b841d60454066000b5444010307205512072007201c801418880740040c17030700d0f10f07100a000c8018500384c101400b04107500152405403494080210040c0c416800c101c0403034243c1c40d100c003c0380d0007001c40e120050485048000c400f0044c2d004960405881d000e500100700c0c4001000000300000d180140000641c0c0c5046070304e038868070400c0c0082a01072030022000340b0025000c03d00302c90004031032101c0c0e90389a99486200702e5418a0b2604003c013640d01d40340500c03e1000300003441d90300465050b200360716803010745e0238007010004441402600f0390500d100250082520340d4030032a40710303002410a441c2880705002180040d44807944211700482d82c0786040003031110500403040045540c3d10f0a01a4004441000b50346410381d50441003088031011035090300c00d0007580302d141c80030100502041c01150600b081c840c250016103003140640585031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 135311798 1250 135310548 135310559
    0x14090c1b03071b0b03160c050304050402120402031507020d030905100c18050102031e091219030810050f0105030703060906090218060a090e0c0403021507030e040504080301050607060204090f06030201020601 91
    0x9003900c0c81070010131207400c00803c82c8070301290f801f050f01c00c05440ca03000402021965890b41e00040004041181d1004140d042ca441070600d800d4003110007118040054081c048402c0d40814001e0044d8100c1c940030070910b002d82042030070401e0403180c1c0003802d0b26015241040f503030000c6044040c41c008209031411580e42e800103a8807172040100110b0b0880742603a2420015203200040c0c448441c0c003901224484243c2c80d4060700d400902018100611038401d00a4105036008000079440300140224105039803408021035950b03030904c41541e041c068040000f46101c3e01c664040401458443d00034429503542d4035100f0000d50121a6580c1c070100d400e0110765030380c00c0100c1285d040c6000d55035015882440c2c481c01d01c1c24a40b000d00b100307100a004100000c00741e40c444d04a81c0002501140c140d07075400700c074500984001c15000c912405542882c08000104550710306580c1104c20581380b0903074484032860808002e204030b03000b00d0b9508c0d2801c243c880c078200343e5a008900b540d00c01c3e021200d07e6601d64 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 135313048 1250 135311798 135311819
    0xc02180106050d1d0102041205061b07030309030c0506010e07111203011415030f0708011401080703050c0738010e150d05030a0e0301050114090c1b03071b 68
    0x740541c0d40426400c110404030b240e0160f001c507034051a0501800300b441200070400742641c4c0198441d4190815540001c000e02c84284180c680004c0c41c0640d05141000c0e0384058000e60190f1308014003415610045403061601812414500e46c8d401030990300c80350b03124104190100b0094406200044501240a0a6980c00112565003501613240c80d802c60303180c0440c94840d8101003a103a5000840d07d4903002c041c0c82007102450241460411003282403404000007003034010140c4c8600911100c0c0203200c19540d8005105a8002c81640f501043e6983d50a0070b0404a12401c0001888100c2d03000c002040d2556072640444c4a07006500c0c0c3d480c801c0054020104914028043c0ca030303174a54020082400300f22000c0c0c080402e0354001e000204441502d44541c0d007550410300288000c982a02c401c024146003c1c40752a02501d84500c3c260523103980800030907004100281400510302e00050340740300c00405241210341480748801141d80d5100300b454010500e0001000b610a4000c10300ba000c01e0b40d0684 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 135314298 1250 135313048 135313051
    0x1060608150109030b061503040305040e06010302040311012706050306130b030618010f02040602010509070f080d0309060204050604180e0604080306060307090f12140106050a0e18030a0c0218 84
    0x143e40d40040d2134250348841a440c40054100f40d804240c032640460b1400c848400f442c070480c00707074541c43d41712894544840b140a000404040c10540304100c00c1c0b00003284031030001301c58102840d014a064407440c0c0700059081c400c44035841d400308801d00c00104ea0f0b501c007000394483d14003078074222001c01c0078280d1201030700c512001569040c0c10050000702d50345140c10132580a40d0030500007040e07020500300e10300200d81c4690814030040c0d4407282081544401003101000405900050b1400341d07242003982d50326110346d51445810583c5440b0b903107041c4511901500c02421009020540d5190350302103c000844001700c030414414104400e954402c503000c11a00d1040350043c07070345c0313207181c0d070f00380400103954401840c03c01400451040070031848ea01011030806000410740c18044108036007020092524071140000007a81407182c107125a0700d40c4a2000100c0da14080c4100e05c0d42c540d01c840380c0420244c0c80c06c207071140c4808144030848a500c400c10088803802a140802402400080480d042c1c40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 135315548 1250 135314298 135314341
    0x7140d020a0201060b04050913051504060b210714130501060c031202090307030b0705130b1b161505070b040b0609091507050a110a0b16080112030302030c1b01060608 73
    0x1003040c002004440703d603c2089c00c00d84a0400c0e104220005036160030740850680341562070315610300e00f1300880c0c10040c00c5440c90600c002d0440d09034100d4006060341d203001034081c45680000810b00f0460980b5170942c0c8040041781d4507000d02c440d40e10b0721030003080040100c10981c0003c2000707548401c2800300e8403c652281d98041c018000c03460640c3c440480d05140505a0702c2040820080c800d90350081c1c2004d40042c080740d1142c10344c2c0b003400c160003952010840010044642084180004401c112141c030030856041c01880c0159a0300305c4401c6d20309000d2003001603e14001c0c002000200030352500614072645046900c1c150b10340b207034101c41c3d40c0c66546400403195224004046a802c5001d00b0107000e100a040c41c1900c500c500b04030680e0305080ca5240c0840d805098807080c0605403041c0c02100d20492403a1811481543c548558016042d281c5400070381496400800304400b001c01004403600c003e000212031100310b01d061640390007080140f03e180c0010300c450000c20043c0c180035000086140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 135316798 1250 135315548 135315559
    0x2409150e0609060d09050109050d03020909010e0403030e190203010c0309081204021c0f02040f0c0801150e0a150e03030a09170109020414010f0b0f0406050307140d020a0201060b0405 80
    0x40c03240041c8180d40e40b01001c0c0381d5001070706001400d004107107401101903240c41100041760b10311161501d00c2c6031080f8610880b080c140103104521550f10f5151001e81181c0155000042c01e8586050903030080100b10407800150103150400d441c03c2e09002d4448580d140700345d0080080d003000280032401c07103109440c003c02081d0204101035110882d5507000350404c0c00140b90070070900390f030740f049101c044000750204c405601c280b450405508c0c091240100000d807002d000d0192074900f2000420a00050050600124010328030035286441070900d60020a4081d0540e04141c0e200c40300321000401c5035001c40005418203042e002c1ca070a000c4242c1c2c0c150315807030322200c17841c038248941c1c842c181300d10a515903940c0d943c0351100c8015945a026016042074402054020340d41080c43c0b400c02d0080e540c21482244008000601c05400150100c8049032880d2506a13242c3d250520211040c18824000a190f14070200c2e0004240c2441d90050034840000d4000704400c554409040729180202e21a1aa111 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 135318048 1250 135316798 135316817
    0x18030f0306010f0e130603031d03120c0102040e0f09010c03141612020706050118050c09090a0e06070504140a050d02151318050705030f0105010e0307240915 69
    0x1540580c503c40c048041c40d0030141e11002c3c0c6100460302c450080d04d20031030302e01d455000410600d40c00482d01c10305000d022180c42404401003011076603940350f00000d603078069070004403441071400030742c1070340c020b04055500341c111410801005d422000c0240d441801d41d501c0c203a012000a4000e200e055030024900c484030800e5507508056903d0001e640480c60140300400401c000c1c0090030307200074070a40e0b1260b80d0000303055042880d40c0349100c03012060000390074a40001d00544034504000d50f10460800c403003040d40c95944401d103501130503000880c2581c4d84601024442c106070080b000c0c1c0251404405449607d80c07240003040038000e020f10803190040a82d208180c00344c2000c40007100804140c040c00c038540a04140200c14000150344951003486655803520030042d5540521038201c0741c1e51600d9811414008420351b0060b8062203428144805200103144176241440001d000b00004403001c00c403103948030450340780288500e147c0c0c4005115507402261401c41f8507c030001c3d010459440d890341 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 135319298 1250 135318048 135318061
    0x10506031506040f0e0102040305011b1403041410050f1605090907090806040602070201090f1d0601090812030f0601080f01090b0319060b0103050f060f01030f180b18030f03 76
    0xc20401a144582003501d4681c02d103c0c4c8100e9025a80b9072250040005a5861550802600b121044c805c00310140356000d441c2000303540c2c07021504602080d044200303951b940340d6103003205044050081c00171180c05511030b5005403400e558840f41c401c41040311070140070342c0c4200c46040b14403a04281a03002c00c605000c04c0d68541001c01105600101d507041041e5482e03110b03002940b03400c908450480782c01e50006180011035030b21030850740c020596041c40d241082e05000b1070080201201c00c0280f00280c2c80400140168410800c80b002407640809a6050030944c5408421941c002c0b915a2800b1088401080182d4420b1260f27504c00da101151001c4280d08144c440006841146006641880f80300310240c0207107121203281030720501c105000580b120401c4000340c29650020010214800380c24100842c549400c042d01030100c0091070002102114108414001c004060890503030320307900c1c07803504200000001a140a10011819040b9804090030400d5882c41180c0d401740103482c060000c03521 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 135320548 1250 135319298 135319333
    0x11040803070f020a0e04120f0806090c071505011811042103020109021009081624091208031015050403030c0809040c0f030e0109080702010c080c121b01050603 70
    0x91000381304204866450808046503202130f00d00307464118a581c0081241508a010f88940f410181030005003490441c000038080031008280d4580e900c1d000032104108038038402508203642449a00300901e5031500e18081034524061491212146020300c80040000c020043e2400c580c50040d0001389200001c801941c4503440403402c034255920f40c00c0c00303001a0f448501150303110b0f08581e00c071750540f803511007958501400040c010809109502d01440341003160030b0919110701c045800d402005265410468400301c41e0b43c049000000003005038000c11510b1300065018948400c496045035483d03050711000c4414000701d403030104404000030400280a04204241d4900410b52682000c81da80045001d4840094851000032149017003c07043d107405114806031008075400800c540718203990b42c4200c0740318402c806070501490308101810018a00100d07039500340080f00780c852207c3d08550784011900b00c1310480c0c180700800c0210308200d1005101e11803040800078014500440401c01200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 135321798 1250 135320548 135320573
    0xb0903070b07180b03040b060f120f0604060c03050f18031b011d070605092e02070e0907081510170c01081b1b03091009080c01180e060112050403030507031104080307 73
    0x1504080348010b818ac05480070302c120301d040706003400501040d00d07062501d00110703090781c0e264105041c13900e0b060002004104490380e0f444042e048030b0201102040851500d94001e403c00c1070300d20702c5002d08015a420064000359008005860380402d41040580740e181ca40701540118400214180805001483e00341e00b844038034041409241301e1400c44181c0c0000300728108088801581c081c07201041b01c5222400c22542c070000c10000340440343c4c10041490b40366000d0004051200182c000482d0004411424910003080ca62003810310800c00b03907038160b0700d451640c454680030600d2100001c4c84404480c8580c00004a0411100c0c5481c8505000c40d40709640b0703e800b807043c4d10042c02644030580b034141458007101c03600d0311480d1040e0f00c0c4c5100c181c0b522206140060401035215202c0c0c0d282005810396000303680e1401c280003000c0ea28480100d13114503041c402240f140d804c2c04144428560594440c501641e060b07901817022521480c0c80ca11684551300c18050030754810880c0c000454003000040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 135323048 1250 135321798 135321829
    0x15170a090206040b0d0902100e0f19050a080d030e0102090a060305070e1201060305060a0903020d110307061b030515013203010b03180a0209040b0903070b07180b03040b06 75
    0x2604080d222030510082c0e801117a000c8202c0d590301c07201da40551400d8101d084010070700340303040d4008000d85800308510511481d011409a0a00c000c0104614031403c2c00c8405031a014140d42c0c100740d5980d003159550380c412402800401c1c41c01d206c0b001d4425042c022030b4041c00b0003400c1d80700041d03d0b20754120020f0030001c0c644000c0003c02503900c45980c1d40c814224650308840320010680d9400c5090a42c2028805080300600d02d140440d254002030300800c0681010117103041080e50025014507080c114441c0d400300812103890524810742c2040469900302030380d280350b80e00300056503901c0d02c0110b031507421945040c0400c1c2d044290041103403003511100e41c0c07640c500810689614240c02c0400903500280c100c3c000c83d034800700400020030151410409041683d10007000040c90603004901c2940d4040c00c0580014000f0000030f0010700708104070740d0000d070700802c0380c45c00d490890702c01001d041000c00c400c1c1880000a03000903040190f4010389000c5c9421008100c0f050325030394104440340759040c040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 135324298 1250 135323048 135323059
    0x7050607081e0408070602031e0c100e0d0806030307050703060b0a050a03150b0118120f02060a0809060a06080309060a030e07030c05130203070f030b041d030415170a0902 75
    0x70702100300b240704002440d255003001507211400e00304054246070884d0882d1045600602282c00061340d160211004014080440d41d6508a500302c42da04040140d40b01c041c03081e0410b44400a548800520031030310318000c1d641d01c805034440383d003059213034403031004050025400840144003048032a03000b030410107002031008061aa82d50045985604035038070907121000e901ca113070406020240140003034038000f441d0200e4168030700d40103142200f6141c00b030b0010500440712803a04100d03445017440e4080b900240800d03201c50417468024600c2008030703000c62a50207500081070450f0002d00690081c0c034800d1001d1070030062400e09018030358001074090340415884005204002c503080c444000610301422494015a06250500141d11048000380c0300351481001080030003a4024030068804180d03203408a48400741000140241845001d50014910740d0320040072280740000040c002c0301c40f461006500c4001d59101501c8103491101d41d0601503d9000025844c01c02c0c5038440d20300b06200611 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 135325548 1250 135324298 135324307
    0xf010509060f01180e040b06030109170c16031b0510020c190905180c0a05060d05150406080a030e270901020f0406030902011701150c060e0d02030304020a1203020705060708 76
    0x103100b03884c00c15a20010000c4112401d04c0207210b07200c09a030303a0000040d0000e100312400c5075503010004103000e80c1250884000310b10030307084040601c08c2c100c455158114220005072682000e6002410143d00d0001c015280c4400013110300b0a651156a090ac9980180c02c2e80c609010904c0156061441065a000c44000740890352004034400d0502440c403410717031005a0032800c880d1501e0825001489485042014030801c620f540c0c0300c0883d44400342102010419448260480128040324204158028285200803072666000681e000d8454084d0b0350740c91040340741034103200d02501c5e0034400b5070018040c8800c50510000d0000400c1d00a011180010f00d010b0703550541044507003207904082c00090f01c88555070b05544c1d021401040b0b03852010b1140d001945400e80903042154211103143c00c0c81403100c502001c7c00501e03480842c644120b44140c4480c07070000709c8001c1d1a40c1c0200d5040b03210300f5a86802140e940c41c07126401208560640081888900700010899160030002d41218039640401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 135326798 1250 135325548 135325577
    0x609010e030d0503100f181d01090b10060804050304030212030d0c090302100201021306031a1314090a050304030303050a06150c0501061406160501020c12070204050f010509060f01 79
    0x442c50610403160b40301900d070308154043e041600392507407081004184041c030600c243e13000c5102403031b01e030041c950001802651349004440141044842e030442946090704080601c600c2c2003030207204014180303442c41c40d1500c40c0401d8910140c10f44000c0d065034414001807005080c4850b04009420030301044074140031001c0740c01000e40c0e1500284000040c9404010002c40c1064034441c05606030b180000d600302040070b024164540d0451060408241d103a00da240d00d18407000004442d4004054039862400303802c2c040701d1018240604070b14031880c04580000703542c02c3e408940d039500d442d40500074510389855030b20200c000e824081c02080009a884000064041c0100e031060b41c810303d243c980d10540300650034000d0858600e42c0c00030009051156082c010380da6810700b15600c10044080c0002141c0700d9040503402801080c088114a201d03010300e02c501c1e1090f8034007914021b4400c5038203110664841c50b441c0c1002d442071040030f4100d102c21001c21128a000408008010418545080341100c0e00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 135328048 1250 135326798 135326803
    0x4060b0a0f090c0503042f030d0504210506160e0901080c03010f0b0f190e130606080d08060616020405010b0909090a0203061603020f0706060603050709050105090609010e03 76
    0x141c0c41140a07010300c641c104445200d80c0600c654141403400c140d821840c1a45511744016080e152480708040c1000d48814140c5050010485409000e002c8a252100564018240d64800c3c0101020242d813844a00d00040c0110f519400b10366010003d422075448092140d40c0c3d00c02d030300501d003007400040080840182c84403002c0a00900301c002c02080c0140880c0f0606086550341049109070b142030204803009925101200924444151243d0100c02036080c64103030108160341000740380205c281c1c14403810900446126400d0b034014402040400d6503012220307030794500030a240001c01c039140c000038001c1c504640680350745500b030798219082e68100e40c002400c40700240c10800f190107001c101c0044a00302458016401801c080082100b10700940000f50365800c02084038102a0101c015000702d54825019103880e002c0c4452a25181c13001e030b00e416009000da60103250002460030000071600e501c1207404608655040c2c40b124640ba41c6d01c07045c01000c3e03214400b1103040c0090380c865294a51402c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 135329298 1250 135328048 135328069
    0x15060503010c0c1b080c120c03030c010903110715030b130603081e070b060f06040f06090302120303060d02040f091a0a0b0604231206070804031e050d0504060b 70
    0x90f03841034551100c80c50203440c25603131040030854442d0918020303c4400300015201a2000c81201c44000284126442a02c0d01e0402c004040e01404081040382030303040305401c0741c4501307840707070b101e10b0341004661110507640c0440c0d100348100d80f005030403619209406030303002c130910003405421400c1c0b40a00080140a4030341691003108d06200000e2200d0050300f846410440669000c003055240c8800c6483d2809200f0018010303603c5000320070f01318aa9551030804940051030300e1007142160076555140602145a0ba200070307806081490302c40c111020f40441141d1141c24020b021500401c2150203200c001d0034120040343e50241c0d105100f001241d51540d580300040340a40348480d140c5403410b2240c00352241d03c070010340034040078801444903a143e440a40600440804020360b5411a43c0c00100880400300141046c2d000f20420b0218a56109254074412030180e158220a14500c10b0034400c207200f00c0e800080051001d00c40c0c0024003030700e5081960420b01880c0c1c0890b10030036040000310746214 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 135330548 1250 135329298 135329321
    0x9090b100504060b0306041d1227010c030e0102010e1006050f060909040807060209090403050a030c0806060403080304050102040e100f090b011409130f15080d0203071506050301 78
    0x48080410000400903515000600400e95090003040d151100100e01c900000e80030a1055454141d0301010700002c80004c0d40321101c0c41c04596040f4080f4200d400c05600c4540d0540b601000407d46055008030452415608034040e0740d8a00302000e030741c9040301d600d00f0400c4c81e00d0440d5241d001101d030500c0100f24601c0e03980350b000000a0400e16040c10400711030482c09960b4014030050000005903665219455882134202d0074640d40d60744149840002807190005c0305d1782c0061800284001d0580c00700241c2a040e2003618104400e2a150005903001e00040b103000b58040340c2044188006075800000d142c01c9403040e00054106a1125142d0340300300c1c421161450022a600c3e010070400c001002d8290052140340020459100380703100080c19141d2030445402480c0001a0148442c0c40e03284540341060182d540c00c00121204204040151030303070070044070740c0048420001c03468007030101300501d2420b10307a0010b42c40c0a04568655402c42c00368508244550b54451001611383c600b0b0040008080703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 135331798 1250 135330548 135330563
    0xa03060f0f06020322050a03060f1a03030318010e060408090a150e06091314061503060310090221010501180c2c1e040c05120609100909 60
    0x241045214400c4205961207038200c08440c031810000c0640110455064a0024203c00c03c0d6001014a15000c0c00165200c0b94006d004200c0c0001440403a903c42940800007140500000c20621152a880c0e0038611403240d0681080010910400410f644401702004281c004a5081c50582c6d02c2c40c100f060440301035442c440c00164007080d81c5040c0300d02e80041c4c04101c00000d001c00502c0c500030009049010b0340380c050700c0d0000f2220840c5e9521581c106000074000c0d42404940100b00c41e0554803901036a106006003400c213913244100c040b20342940c0c07284c00090010b1540150100e10034000e03100c0d548040c1c1c0c000070aa603611320141d04401002081d42c44007030010031a03500d040c01c4403101e40704a00c84001c3d00b51802d40510703040c0c2d03801000301c0d01890300428828035040724130000c0c650314209000f0141d480004440502148000c83c0190145038500319001c101200c81b4030404e031034500c14907040c4040c0d4110305001645071301d004203080350001e607074020342c081d8561510141000c0383c080484c245c9404d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 135333048 1250 135331798 135331811
    0x31507030603020303030f07020d0801060915091806060e0109050d0605061c061e140f09120c010b0f010513090510090c050705120405150c0c180709050118030201051e0a03 75
    0x40d50100084c00032ba08951500144a43c0341600040c03130803d5900036840382e0001070500c000740500c40e2030b10f0409000000710300100814814084001000315115071008190040640c402542c01101c11400b183d1001d40040469101e41e5100350080800500c1d650380070309810320351843d40c0c150314507414642c1d100d40c1c40040c0d030100c4401e9500007901154000616581406048540d41c010a01e0103900040755459845160b2194440c01303090403269881c0c0d4400840c040b4021507800c0303054100810303580c0c055030210801c2400f540110341510585c0d070074081c182d1440404000c542c82c41e50006900c00c40700e0700802a841c0d190040e12341680c400c107032204006040442c05100703206040c0b000150307100c00c51040904c0d051808021608a0030103d000e2001040085101c1c50600c5083c0302d48080500000c003014200ca4041d25600300342c0d9010794108000805c81c010108982d4001d4500c400d03099180340009140602e5580110341e030b58002c0d4101040400c000f07e02c42d02d1610094054540d90800d03440c0840d0301e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 135334298 1250 135333048 135333061
    0xf020708041d0403050706090302010902042301091104030807030203090603071706040504050c010c03021e0a030f02070b0702040b030a0c03060b03010b18010e07090e010807170c031507030603020303030f 89
    0xb14410789245032411002d203024807001a4110086a8500b6480300b0049045860760030281c5c010325000394007940040c1802c00107840e00c49001882c41420131601d01402071a601d450b42c441c100c4408a0112550460412013030001c40da8000240114a00ca0710403a40703400b6205003c6840c5e5001611030b440031070100d1150b00488524403074041e0740030005407070030440341c0340a0300c4259075030112441e0f40e814402400c0d51001403603c01d0080030350440700c040308500c0d81c0c03c009143c2c59464181c00000c5d4005031003102e20458891000c81d080c0c00700e86004806604191081c0c0070000242494041190b2601c5620003000001d1211141440258041c0320002500c080860515003503031004208103201d07502d00d0ba42241c5c80403201174070174103542140e1803a020303d070340d64003090b1500c2d0710039007014144840300000011600c60010b0783ca01515136aa505900d00c401c044a155591406060669032580014048408a109080f0499448220340c600801c4403a902d801080c1180e100740c90203411410541c04102c1e2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 135335548 1250 135334298 135334319
    0x105040c09020901120f02130e0907063b0405090f060a09031403040c030203060f16050c03030f070207090c1106060a030803040b070e1305060f01020318010804060f02070804 76
    0x80c001c0e201e0070361405180900003480d4024600c10054a0ba50703841200b4018405541901c80126142920180c45501c510311280c0c141d0085480c056035108a87c80030841510428043d200180400c42d00d0320010406142e000101405045651490000044101d885c4d074946c02010700424810026158000002e00042e0401c03000409070714003d03080141c0c080019034000303a5030295612200440ba00c94980f86840060114207600c0a540740c4100c800740070f90726100e140058000d000c0d1101d110154140200243e540b401001c2c1511800e4000b0700c00035910380a2401d02640c833440c1361040c2d40748184c4a88820040312030f50851580000c0000c5408040074104000e240d070000c2040342c62210b400d1841d6550340540c80020b100074500b6844502003840d01e0b001d202c041d164060700601d06141110380c01070b42c1000b00003c40b26940b0448244403600e10550000c81100d004450303140d60769203040c1e1010015a4490800b40c400c8560b20f07170b0341e402c20202068903c0a480c00740d2040350140e6486150029409 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 135336798 1250 135335548 135335573
    0x15030a210915020a02150c07030305041d190902180a020c0601140f06070303140c030601020c0904150e07080f1f02040f15050705070b0406020d03060312140f0408010504 74
    0x2e0b00268a070180c1540350f60000780c00b125183d070442d01070350902c00c44100402035001e1030100080a114090020007016004405841661030342111201d00000d03081403840005130540d18421039034004100400a415190000c11700d150001d00030501c0048034036910510300d0b81c21951a049143c2c0800c00003c69002404021b00601d000a011002111000001071012108000c0548036600002c4ca00003010300a400040c03034201c803c82444018503080c07020b20341e55403048079414010b00a0301c201e01010b24008040601850708844085441080c442004009104580e41c0e0145c034407800030009140c241c1080210452040c8030040c0001c1c00c000d01c1c034450080c0c0702c2644502468014841030000007401c840310b8049906c0f441072000c00c06d090705400e842351f12850702d000d450381c000c42c0c2012548410800003402251526401c4503002254041d04030100ca907140001041301039941502e2801e14810001c2601c0c1c4071440081c1e91501c00b01242c22409a449075000c40302c140d44070400c01080c042d2643c000c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 135338048 1250 135336798 135336809
    0x615090d0605101a19110708070603060b1204060e030403170a08060109081b0a180507080109061211010e090703061a03010305030d0e0316050a060e07060815030a2109 73
    0x3c0c030401650a11043e07180a00c203114172015514210034000c06100f43d803501128680e0300c059500054803440b800352248003e00441d00401e04060340000e600640750b0850b0b1423960049500c84154490740e81c1c46025154003401c09403284070620001c0301040c565403500d40318161486002c2e40d54602a50050240007004003a035040c410115010000700030702003441149000008030320040d07039060200045011480d40c0003002c1d140c0c0d4601d000c0ea070004503541301901a418035100c2e4000c07680d91310b40c0c0d201910321a0280d9002000c0400803800001d114204000e880344050402500040c40d1101040d0740d2201101e80c0380c0042e807208002c1140c040c190490300c3c10102050542451903045441d115624400c2d6440c011406a803880e10141980080c0305036000040640031149450141c0e0030126036841d048030003580c46601d8802c0380c0007441000240001250381d40d4441200035076030303075a484800c0c0c00c03c8a1000e401d80605240c0200017800c1101c0c2045040300c8506110804400c0d400007040d0a117160000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 135339298 1250 135338048 135338069
    0x1c060504050906061008100b070302060901050114010e0402090a090e06150316061b1211070906060801120c09020d0e10091713030501111c0c05030615090d060510 71
    0x4c1c00300c81d482d610440c103101101414084a580c59128518203440303041e6120380148000803505e202055804114103009011010090095980301c240c4940c200300b000c1c0c5418003249140008200701e080c02e4000c1d00300348400400d10400683d881140e6425210751034094210f0b0b40000e1308000111384811144043d48006070024290b0305842c8a00c40040c1200340216000c0c082c5810031105c00f14030164887c994168000b000c14040c150480c00a003050042d002d252685004403140414406098031035141169050782d03510001c5c1e464080c0d46401d1480506080d036914902041c04140024207000406000d07034440b50002c0c40c1c010108280c4d040101903c04040f490303041958150104030400c0000601036020a1115030718407030344290607000d4100360300c028605e5007440c0220039000c1c0040044d088912071704001c0040241c1c910840c50444140705c001e000814030600200301d66043c442c5aa560310000d2a103d28548031500d000a08500540d02c400c860941c3c41d0300400c1140e019840c012001040c00070803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 135340548 1250 135339298 135339301
    0x106270f18020f040b0702030a0f030306140d05070311060409060b04050901061803060506040b04061d0601051207120e03160314160602070c031208040201021501080309010e01051c060504050906 85
    0x464a45100c4c43c403400401031404501c039010341d941800020800c0d60301c00d001d000c3c1d070301e05440c02601608582c4902c18081101d00102011410400b1000c181c007a4014041c0034450f0079680d519100c5060721600a4214005105c0414460302620a0002921401c0d504544481c40c000400c4030099058200004000d0540301301507a04640740204402c0e242d01c40b60103c5d05507a40c1f00070030010111a1049030340203003000400a102d00a03a00c1c041823000c04002201c180c0e03642e0708010f654600c6401c0c0c2004944844000248413184544084155001041c40100f9461481c0c802986550041044406074a060f85210420903811600f9881000c21042981c5e05000308501d41c6403260340d000380b000c1d01c0d1540024803c820040290040c5010315440f18014038100c801c044014100c501c01c41d0201c0c054410418800744002040d000207048075001c0300110b01d00740201c401110340000e040f400c07605100c000d01903040d840940e07800c102c0681a210304009540e1703280c0010402510409480311606410160 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 135341798 1250 135340548 135340567
    0x8070c1208121f0f08190503030f1504020a020d1107060e011b1e14060115050903070f080a0302100216020108040503040e18010b180106270f1802 64
    0x9490300ba421180d140840340e0384440140d514508103940409200e000b08030007003289928440c45a06461010080b43c00a07258010f0420000c0026500901f25601c244001104040d0003084a60b0003051145d6240c2c00d400340030042005d981007450280e02507044020358031500c542c418070744143d10103880000c0240c40d10f01a4054810444022180e040181280c8021a190301034540c148000d94424640320780e8030881c440b125107161041e10304481942c00d800294084400c00101c01d8142e8089000e031200401d204101a9041e0b481481081e0300340c0215400090300380a00d018003802400300001522143d0b9091038028203180c10118001903141c03040c010302c200c01a90385102d032030907a42800c0c41200c81d2a40d00707005145000741e0b4802c10070400414200211114072501030104440301a00902000007100204a4a21281616126600c040500411080b40b00d18584200b00041381c407002c01d440c1141c202482109400e0708284c8040546071302c02c005415942001e01d800007506001141415480c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 135343048 1250 135341798 135341813
    0x711040c02060c0f0a09030c090b15070206030c03060d0c140a050303070b0a02090102030f0705010623030604110604080f0304050a24030906020c01021c060f0303020a02090403020a080708070c12 85
    0x130b080100f840e88011441004480c06107884501542e0030055580255990f43c40c000040c10142ca0000d018070100301c44894014021400d50700b030603500074031042c1075030707220b181c4174890b82c00c010b02c032561082c1c45084a5010441241800c40604030000300403100002d04000d01280000607030010380aa8010000c10000c01d501541e0360ba08081e6060025a0310712460300101d196008020841403600400600b14040100541c4400100c4400e896810810050300d0f452990403816500c0303841e0140c002c00c001400058082a150381c1000d0014104c604003a125003805181084004680b8026440002c00388410329042d02c90500902d00e81007602c0700400d10180c0442144400e6089005150705c42910408000c91078043d200f011010340021500d900d8180141504d40840041000f5145e1a0980c041200c1801d5107207003007038079055001490049000c0e803e02c952044001d0040c0d04501641c59080001a242e100038100f0500420456840e01100d007088041210103a0000c503401d402c4054110028104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 135344298 1250 135343048 135343057
    0x5070306090804030c06020c0a0f120f02120706121407020d0e0105070b0c070c06020106080307110a0906080607030e0d08060d1103060106020a060506060a050f1602060711040c02060c 80
    0x120106000070303503107001500350080f44c000400210512001094040e400564400085402c482001b10166a45440c2046030624090015003400c1c1c0e0510b0800b0900091a803000a88081d20ba0008882554100f600341200b9412210004401c10b10340500c0c0201d9018414800841c8a03503000141440c40d8086d55850219100d442800340c07903002e0010707580c003410a03a400650061b4603030a0500c0c02007803180003688017110072120003600d00ca010910b03600c144105016a21040011351504041da1640f802d0540c15031141a0702003205000403802d45424001c441c02000c0b120005c00c86420854009000d46007a403103402d800380d008000f420321103540010003607003080c8103581b0b41c180005e440c10046aa081e50701038240d018440d150000804030381c00900f0100c1e2a0081000300010b440b15402c10200c0c4c81000c3c45000024028410920303240c1044000b4444250003034001c0056080a90200b00b0360741004d04142c441290f0341040c03034144d060a008401d01051a03101500e5513280c0056444090302a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 135345548 1250 135344298 135344303
    0xc0f121a010804060b09130209090601081209060f2d0702060a0305150306070e03102a0210051911070f0809030c0a0f0801060f080309042c07030308060d050703 70
    0x1940b01040c10721000da032181151110140c0101d04628110015404040300010101d006041c080d0000ba62100e02142c0701d0b0580392401702a10089860310843c00040e0008000c40d64020b0b8104146501f4800c01030080c0a2868644584c0010080608481c0e82c0e1020511250b1a84c0c41c04200c0b0300d005a94000031601030b1003290400248585400070703032015001700e02d8103080d09031190f1402c0c1700b280c68015011040e03030242281120b01e01c0101290301019201580f000c0d5545040c01e010621541d04201d248002521040c8121403083c404001000143c503800d0b54068040c11410a18596020080c090300c010340032501213540c9010303069507407a85061161007010380050800714045103e990203005001d64482e00522001d8210b85490080001e080141b140510710742c0f81040010f41131901074400011502e0001c0030307605004125082c40082c101c800b10f0150740401444012a00400d0140158420a10340005085003802c6107030140c904a0050b0516104414100d120800501c0014240f4103503607 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 135346798 1250 135345548 135345557
    0x108160e0703020307092705070c0b0105090603160b0306010e01050301030b061e220507020f0709050703020d020d090b010807050609060711030d180b120106110f010c0f121a01 77
    0x6035852022501941a9003080c81d84204495800405010079081034047d081d80390310400c1503444096080d00c0584400f08010110146000108000e28040072001d51018014060341c01152901d84106030318001a007043c0491240402801081d5a1080b4503100d50305c000e09020b4910f50440c1c8880750604401010390303109654000c0c05101c030201111541c1d554040143c03958440c4d07558200494103000c60409055100c4e841c020025024610024983c0ca0b00d00c01344000e0b243c00c1e818204100007a01c8000d10354414035400700310850001c041c51001307102d49511042d00081041151408500010041e030104155901400d4140103603501c0c407003191210881220240d0f42ca02c0030f0725001840c0e00c02120340d02d030b06004800e800c1f80020340000d2074010780c1000e0b400134841c05403124003200366400740700034090445103408014001640954014100060484c080322005481c0500c5242541e13583d04845001500706030801c0b4a90f03800080c0380c070000ca0280300901440080101110360800034001190412 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 135348048 1250 135346798 135346801
    0x614180307080f010c0809060f010303050c0c0d1109090601060f0c0309050a060903050609010c0c030e01030e0a060606020c040506060703030c050f0d060501090e0601080402101103120108160e07030203 88
    0x1503504014840041109400303443d80c403404101080c3c000c00e0304000940c0400d21207030004100311804109140f165500280380460341c0d007142c8044a0982000c0c080048920074011849859075640c07141e4404c00c0d204048407441c0c000719a0501252070300c0501031482d1603000c3e0005006054004eaa0600c1d600c0c1701c1d10b484510291503090031552820f03280d02035900811783c90408940d4941c06180101aa8060400c60340c0980700c40d0700241c229082170082c90009400420400300103031041d402401c410300c05140115079107072829040b5060a5000c00c0c1140c0c66580c44804018070b070b8040c06107041142003190104002c2c5000e101050440c401c02d0001410166240c4501e91824040e41c15100c40b080c039800403c0c1c075a1200611207000709000c0c003419002c00c02c020000280700c0c1141d200d42e4800c413810303907030320055841d564203100051580e200c1e1035090003802c00c0706018402040014002c0c0d5440759428038599450314a00030b0500e41603541c051000c0d0002681031002c5024074801c0b5400c00c045140041e0760b0f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 135349298 1250 135348048 135348097
    0x3130209060d0803090609011b050f0306040e0d1d04060303020304050d081306020325081c0f0c020319050a1e1b12090623220602070806010614 63
    0x942c01403850003040c045010003030141444000411a124080b101c001304460507045006004003107001600900050081002d9030201104601464102501800104000e404415080e051035003c01e034007000102000d648510b241c115401d100c20603a010380303041109600b5924001d44030310950085600580e66047e21504110400c1c003111349154400603007900340342d00e502d0002e4595015042c20200080b500718500c44100802c0c135550b61141c0d00c800700c1c1d45049421620381c0e9140010800f0954850703560300d000c400c0100d050144050000c0319a0195030b59000e08600e0880e8420220b03544420810b05100c400c0082c3e0700300042e071a89801d0000d50310461105c0e003408071380c03410b1a5502c0e048010780c0312000303408200000c000c1004c044096201c010f4611b40350081240c81c00280322982000320700c410742a031499450030004200302d0803059071080601d580b0300e9000c05002c0c04c5620400050344001400c0203c0a01441481c0c003410103454050201d02c3c030000302c19158080d094452501042c8145c8a481 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 135350548 1250 135349298 135349309
    0xa032f100804150908070b15060a0e04111602040f0606080f04110a03030507060b012a110d080421050c0907021011040501020705030c0303070314040308072001050313020906 76
    0x41c0d243c0c10036814070040009140c44030903a00030100403111140183c003c0703400031403042c1440d251007034041c1a40d0b081001d600002c0350b13a800c0000345503030856920050b010412003c0001012901c2141c084046100c45a1051104035001b400d81d0100c00742c0707403117020300c21a54022607641e081080040b1170b02690b22281007085980040c0300100e0350100303c983d000010150042e02404405006030810400785003450015a60014003d0894041c805031030700c07618042c14100c0c045a07265029442c20b03020461007401041c545c5000760340035501c0f1040880d041150410841904640a1449040300c2e400000ca0703481c203944001c0018514030a89001002900300c5100704a012044000c1c09000d00140303a14400c80c800a40c0030380035483c01801000400304183c03d00207011486078030058001d41c41c001640e18200d1755440d090384401ca800a0400c40000441c0141026144060090201c280b070549080c1c901006e0a008100366814406d0500030400d014a20381c042c01005501a00c079040035690382c000141 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 135351798 1250 135350548 135350573
    0xf15071401060905040308090c010c1b08011104030506130c03060b010509040911010306320402070812071223040206090303040f050a0504150b070305090a032f100804 73
    0x4240d42c80d00d140001c0c5032640e5000580240c0c002d8542043c6622468a03003600d0705c03003403040315010546404400000984c0411009407060307041500c41c4a803500d4008c5035094038040781d801c80c080d003c042000c0c400e20006000060300032070040c4505114000a594040d401041c078031002e07000303c0c5e443c00e02c100164010b00032109181002041003141009520f406080c008a0103407590001e0714000021400410000b040d03001070796100c840e03401400141c094506051460540b144d0007640a2101e4000508040050180201c202112841501c0e218034010003104e02646044c201c0c3e400c110245580080c4c0b8907210381c40000c8880c0085195071240003003070f060f11074440d00d6909403100007400142c8890845052082d1642100da00d4802c07980c80c002c00055400c102c181c00001000c03203204010a054000003401c1c40d0b44207003002414140b4010000d6041d0741075500a41e20001c9070071084c024040240c0c80901084c2d15540d61480405400000c6103000000f140707403906200180d00405c050225082910303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 135353048 1250 135351798 135351833
    0x7060207060302090f100827120d060b0406020303011505040f0e15060d020d0608061e04032724050301050103020a12020a02030703080c04050306040b270115050f1507 73
    0x1403002803041001406847c00301c1c2c0306001c1010760000800c2600440f011007100c00c120030000c01d8100703001105100fa55000b0103259002950703407040010340e841504094801030425070040d680b03a41c90704c106048040c001c4404072003001020041801500c2404060100395040d220060001d90707100301c00040000303680d402203640300d00f000c01c00f1301c00d92060760000c0484803803406061010310b603206a111342e54201a100d2010100e0078a400491420041c42c2c07040d0300600034540394190f42e0103030348040d5100020094040d00352181403010302c14030f100e01d1350700c040f544510783e490040c0384c0e841d00004000340018002c050400d600040c0e01c120760340c800c40f07c940001803200000c565a202084000c0c0d90703a0700040045011030310580010b0340605002e0b060310b00b11040503020b00713901d41da80e075229000100f000b4001c000180514005105901001141d01d8006a2140001458031a028100140541207900040c8215082c4004841036201c1800c98140c10003c048041e88880461411041804403c80b48 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 135354298 1250 135353048 135353059
    0x190501030c140607021c020d060e010504060b031c050c1f0605091b0a050f0c010e010b010e03010c170a180302160b04061d120a0b0603070807060207060302090f 70
    0x100038440e114a840307040380c055040d20a0049184420b02810307000f4214060740c401c3c2c01c0f40c9501c202c010f8603403a002c0b105200422070f1418460300d64649003214100e200016590307565008010821400340f041442140c0f00320001d2898aa130f2501032110740d4904083c40c010014049560740103c0c2d41044100c3ca0502d01c190b2240d455403540b001c0f4001030110340f00781d80c811494080491340c00040ea8140600070078031070804524013080d83c2b00c10f0b24954040403d0360035a41080104991000082c410350403540f000a001283e1801384800040900380c42030310b0244243d142010100d501074120b44050300d181c94140001d0a940d37036030b600290041648150703144441c9004c140400070582d001c14028448060b4601c1d2150300b54484c0b82910a90055014000c04103941905100000c00c4203010920500002081d0202d8480380321200f9080c0800840b04840000680d07082c0141454148042800345c42800e00070300d40d2615180e002940c80b04288121800d043d03000407000c96a882e5031002100f03c0401030807 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 135355548 1250 135354298 135354301
    0x50f03120a0506090402060d090809220c0e0a0905040206040e040b010609120c050636030606040b01080c0c0102040e070c12020a03050904020d0b0d1101180515031905 73
    0x144400e11008032000c030142450080041d03480d02d4002030442c010754000d40001c0c200129149240020802c0e124165078a40d01407140c880c542c1ea4809460842c0101c4500102c840500049031406940519035650240020141da0000f262228541c640c1120740740040810f890712070380007007849440b0319080000d080c0139400800c4180114082414100c444543e50750b00d0095851300c8a0041c0303900010020034004187c0000c218500c2c040015090700302801744605440014800c1e04108600e1501c04102e4401000c00c6420462a0034400d00b0350012046c1d03814064590039000007080e00074002c0242c03100000208240720520400d6050f5000b8040080107801f05003007061000e802000424030803108240154010b840040c4041815103201ea4191603650a0101301410080a50440703014890000c7d42e500031983c060b5036030b100c0700d488103000d0510600307031160080c0010f04061990b003c000d01d40305222403c0065445a050001d8405102c061081d00c07030707d0b40c0403180032400c0e204901c101224142070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 135356798 1250 135355548 135355567
    0xe330406170106080601120503030c0c0115030302010608150f01061b080c06061f090510030906020301030f0204180308011e120309050102010e0d08010504180503030f06040f0b1c050f03 81
    0x180f041c1e0543d003400c41181c080d41c2c0c1e680728130780c141550900c00800390342052002c60718181040005d0552910380c0e40000c114806240d64100c2007030680d90003600180e45901d400c0002d4075052040c10700301230209034140803600e481504200280010b1095400f00207003000c851002c140454065010240c0c0038000507135516984c0d158581d1400c0a50ba03c904c00c40002150204407600030035070144e402c206440c1e03409494640003c001241011014100901d611500030b82c00051013880254080d6105001c0d01d003c01c541801408211848058480482d2940000784008243c000300614110741c03100340c8040c00300100c0c0c0c1c01c0c00c0e0346552607803044c01e100d5160349822042582000e940c0c1c0a941080e030007004901c5440a007d0755450800c0103220101d0b07000030050200c0c0c2402e0304000c5503400c0401c80700030300300e5403035031481c0c03841d0f00450314000780d03090103001d0021510b4203008010008003010803e06c006100600003940c041d520001683c182400039041204106090100d000c841c04801c095945444004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 135358048 1250 135356798 135356801
    0x102280201030f09051510080703030504080706050408060c070f0602030702010b030c1c1104200d0e0102030c030112020f15070213151e09020409060e3304061701 71
    0x1244228082420408001c80070141480b8510201d600303e0014104101074481640d2200c10181c8402080201448081030325441002502c00661180e80d8041e40c07149841c401e5402d0240c00c0e0007880030010704000402136503000151490f0002d0034115840d40d40d4a0038605240c800404100081c40c0034004010000e12640650001e010b21809805840c140f0350008100304c91a00714106106540c4400035545000c241403124440780e103100544002080c040015482032440c00030286150110300000b005c0c481041c55010310032405100c1e000950850908050b00740301c5000501444041e2000141244103640e81e440700301c0e00c14003002d8904019108101c4004650340c6c00b030582a13005480d845030f001007a00030f42c441c2e48034420408944809260400a05e8421030b907006080a8003a40c1100000c60358504500c018001040243c1d00003075001c1c03402d41d120510020051409151506454031300b050340c103141599200e41c03120030001031120708400340010000e01064011107000301020030042c0300784205 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 135359298 1250 135358048 135358123
    0x7030c03051e1f110301030605010609080a0840090b0d021305070908010c050306090c18011206030c09020702090108030a02101812020a12031a0f0102 66
    0x600c080c0d0304001070220325103810036035500319100c40f6070140095110f0700150300104411000c045034049403503100281106840e801c282c1080d0b4540e6a44d0300100301c3d00e500b10101400400140c00034000554040c2c44513010781c040c00f5141c426007016562a44514082c05620040309001031942c0b02001d15840b0000d0311082890180a03043c61030111444294a01413104802d031540c01031503074040303103202480c0c03034050700d40584140c051200c001c0001c00c0c032120a010b0f000071446c2c1695001c1e01ca1801c1d00c00c02c00c080c640540410101310003041448140a000016241c0381002030910702c0f41426220304d03c1d4028081ca03800a40f241508145c00320f0003041c1c58004000c604c0c001c683d42c070816602d40f50883d40f284103100c0341c2d8026030300c010782c084568051908403190001c52008034801c50b514549a00d0344509004100b40b00580040c080d035010000c100000404021041c0350410014184000145044281c0c5c0c502502c80c82905020006c141e2080040300038100182807146003154038a0100303000610b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 135360548 1250 135359298 135359303
    0x7030806040c0e132c2a010c03180911070c060f05030a0b0f0d080d0f0605030a20040204030f060506010201090803160e0301020a0203040303020c030601052404050307030c03 76
    0x20b1580524000303114292084008800408541404003a1245400149070120700b86280c0907191241d1156a000414481160010203000c0d00704515644103090418110300b403000d40e6031981d6500805140d0b03000103001d800d1507160a250284a400300c403049611074032603001c1d000071400e003050b6014207494540138101e4a4450105024000c0e1668025036007030003028002c1d000101c05000013120f40641c0d8121020004002e012645200b603070720f0204142140c0c030744003502d103110009400d07030714a456842001800580808100551414000003a41302c0d28068400b80010103040c008840d40c0441e00c10076080c1d00e400801c115980d40d074074a494450942c241e281658001e1820002800c15401030050907211030740702d65028510b60f11a0052042c2000418100341080000080501180c030244001c202400d040d0f00250b80b07903031035850028034000c031340d031140c1d07000c0e42005004106a48070201601c1c40f141442808030111290461440647e00580d40010b51610904200105203c000c00802040d00e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 135361798 1250 135360548 135360551
    0xe041a010f0e0c0315010c0303060801060906050f03070602030d090318030f120f0807110109020a06030b040f021c02161506031103010207030905061303021215130f020f0a03080703080604 82
    0x207456103c0e500703c42c08200d50301100c0c2000007030072040c1076114880000505109080001d6030545502081d03003120703901d07000f14040d06d59940d030500951514400702c00c1100d000710001e003445814000001c2d1203002d0400c0d00a862038642c800f071010036001d03002e100e203040c4904070001062584d03801c0141341c1082485058602d0b00c0496400202c207403141c0442c0d20328980327503216103415032680d00e411914180302e05542d8805544e140c40c80700c01661406104801051260f40114442020104010840d046031400180b018410454030140e040500c2009414406034000180c03204040c201403400d000304440010034903001504a2a00028180d000c9030603240618000410403002c1c0c01810300300d01c80e104018022400d0790004004510b000e5004003488404602000002c40c0e89901145054410b0341041000d03401a0340050f8203550031041141c0d0015507040c404a10083c541c40c0c01a90050416002c0c2c0544200003456400380c442000c1c0d40021580301e0a5140d032404241402030015500b503038200e1003503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 135363048 1250 135361798 135361801
    0x309011211091e040c08010e1f0e0f061509030c060f04030209011215050127020409060803180607020a12112e09080312090f160f1a040e041a010f0e 65
    0x5202e46c980a050b01d0100304981425201c40ca041c0c03140032040403412000c108810700110340756903480c40c0795000d41c0f049a14805c50b400c20030100305000746603c1011034400340c280507080d45540c0c0001c000c1100c8070152511b590368000008078a2070b612480d0000394110700e0741d5000255030342840c0c15104103d8090018107401d64000c80e1038005460b0217200e0b03180d9107040c5d50035003003d070384044507245580e068580340103103040c0e554181d01c0c007560141d034482c200c503401c0490340d4841480b00c00c2c00000741400c00c0b45c84601c2c2004a40c00075100850900078a807d050007004503008000c02e80f81e61701c04494000340b00382103c4000301c42d40c4159502c4443d00304104c1c4272132185001307030502490b4020296034035507000c1d506104070f540c0a061a0480205901c0310b52248440c5114110b02c00c1c004040d4280000e8412545542880140000400d181e8048600344060389520000144120141d409403003d215001700c00752900c1c2400b5580b014410020020220000300015819510b0689a0700f150340d040502c0358036 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 135364298 1250 135363048 135363071
    0x6090a0303140f04020f0409170c01060f0b2203061401140307030203060604090f02060307050408060115050406030902010c06050f060310020306030a020f03100906050a0e0309011211091e04 83
    0x552410f036070780c42104a219011070700501e0070310f82d941c03415030303000e0300014a00305036442c1c44106440040001c0d500c0c890020300e0700e1843d0001c0c0034800280400e143d90214007450710340002a1403003440740b202110000821140c4003110300004c250029500700909202c0310600e81a1041490402c0c85929202c41c10a5044216030802003103903400c0702e80007000742c440c0365905010b0002a00036848101e038601d15002c003550060341e481c4003640c09550b0b9559020b80395410910003070b10300b8406070840180d210b805400d41c1042ca600100701d4050303480034900869003d2140c40140d0315203030100b10007410345080c0001c0000510b8165002403090104404654810040c134136084124401030b80c071107030190030054006c800360a004010310664103001d02140c10b03482c8172090500480e91044001c84219440d07030103001600c40c060141600c44507680016524001500700060042c002c50b00c505035045440e0398240c80065130362020b86504040140494480164504120032901d8540340303510b103e1494200c001d41d0b0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 135365548 1250 135364298 135364331
    0x60e011d090403030f0204050d1103070e0903070f060b091306110f07020402031b0a0c050d0905092e031401050c03010e0109090807120e0a05010305070203090607110306090a0303 78
    0x400100074000303501c59200c2d528218058402290300f440c0c182d800308000140e83c7c45882c66010742c58007680c0103006481083c810075081544990000020b44c0110060000f05080841218083e40d4020700d61800700074a85049805000800d80d6640e0202c40402041400c0c0d18030720060030341e2071140208200c01903246607025214050004444200c503000d1100c44014145503006580040c0c003440c42601c03600203020030008a9000c4a00000002c20354000d1200b000000c02102085c0c8105007064400b1500f0171000ca03561520046c0100300d28214034000980c003020000e0098002c0c4d000000001c0e00680700d0a02101c2c40c5442c407410f00e5150318140000d0840405081072301d060311162252a19540d00c0e042549010b040b00c3c1d00705441d005003c0007004002414211640c0c0110728544818031140111800c00c0710414490307000f281450b00b803408000001d907010007100c1001204072105901ca82c242c1c1442c010170700c0804885905807041e1410b002c0c5812001501020b100c0c8a80c0d0140701100c1c051103c1e68 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 135366798 1250 135365548 135365597
    0x130c080c090a0c0e0409060204080601120501060b090907030c140307050a170106020d120228030b04090320030702030304060201020423031f090f150e030c07050108130507060e01 78
    0x140040e01301c1c0300b000381c140380130381003486820b014000c09820691a4850582480c80a9014041c145e150200d42c200304039080c0103010040c07400c4214141000301c1c9002095200400420100805070760748000340446026801064600544558864482c03505200240482d445449018040759071500319207064846401e0301030583d80c9540c00b03060b810542040035603c694040300208880c40c1c00707105408030840301c90140020607000e0002c103800510030b50f00280483c1c2c604040d40740a94208000c00000c82d41200100701014044004201040208003d003400c500030000029814000000c0004806038150017500598803c1034516480e6508a0300030425090248402c80d0103400c000d40980030044502d01840840070400e0000c10308120996031000344111600d02155151007110984d4280d15552240b4404001d621000314509500145203607907072401e80c81201e042100000015640b1011205050303510350f03200c41102c80060316200702520303220902d11a40d00040d4140102643e00d9100510340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 135368048 1250 135366798 135366821
    0x1603050a031d0a080a050c1f05070807080c03150612040201080c07030903080a1b0605010e131104021806040303020601180203070e0f040e12091207031a130c080c090a 73
    0x6061810013551a00c034a030b0481640c14040c80414040d03140c0420050206101028802005036449031000b078050040340d00181a05003000b418104100107650400451070b006a41203440340e4032030352410510184080c400e40e0740c2d5000000426011200342c0700d400e02c3c5014910036241e00c2000c2d07543d6201c82c00f05020303084001d800138088013010404200810001c20303944aa41c0307090003203485176511080c2d20742c103c0081110115924001000382881000f41b0b00c2e00802d0280c0501c030344842c26281c00341001116202103218541c00280c0c0c1e00f00c00e514074200e0100c1c800181210703403201d650341006500d50000348250905001e44c00d030f5000a603560340c400c603481901203840d400280c0d2030100030300030203d5141c5080358005030b803030400310725207401007003020300c04146239010b241e803811104180a03081c0a60310405030745607c00c050a01c00525844410010a1184010340c089541e070340e8105402d6013240000170b40347d00c4440d480818905004182040c02800c103403240646a11804d420608031410030301403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 135369298 1250 135368048 135368053
    0x50705060f030412020a080406110609070510050c03070b091c0203090901030b10092c0328050f03010b0d231302010c0b10060210050f0109111603050a031d 68
    0xd4000f8400c204c032060440fa80d80304940302074001c0c0d5250201c41d4080d41044000c10188220301554140401039150f01128040262940c02e14240c046502c8102c40c2c0f1403003052100103e104280240100305440b8203940061b552a0b8078100746a007546c9031070310302c0001d04501c0208415908060700000403199001c00c003034802d00060b861a12500c034180e40180c81805000c030014800903540065014054a09294014280582910207401c1541000c403140c00945a0400d1152402105214803100c24205070083c030311100d141034203000c413207034450b08841e4082c0610210001c130740c1e402da0f02e02401142500c440300b0001101c030303060f0700d1903449019068031001c10680800a2403030340504064464052060400286180c81565509a50401201c6100307680358156810001250b04100c0008418203d501c1004242040381c413408101c101405540da40685072003504031410701040442d01e6200c0e9211840000400034078004010b41d224540c03c00009040000310304e50025110000540c030105d1100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 135370548 1250 135369298 135369301
    0x3050709051e03060901051f05030a080f070f060912030506030c0103240e06090c0a02060c07030e0303070605060f040e0604060b0414091c090e180721050705060f03 72
    0x1040521102c90582400020407160701e011162802c108103801000303100004115890228242c0070350380315212101c00e90a4034040304200c00d480109001c02c03900d07007005100340d4071141104018a14460403030014240d1035035401e000148803150780070000c528460350420b002d82a15403401c4051b01d1043da8070503816002030841034155030081e40241142422840d00494440390310015582d0480d00d5403040341e424800104108980c500b40b48226842040d41018600b03082c3e804000039900d5030010941211180700250040606019080080300d0a1009088a40d0381540e80740048c00361130156a25401141c5050703005940d0f1426024415240f10340324010141540c581e00d07086c01030802415003540080d40e030138901c20299800e1205620644c26000146000240341d100f200012550f112610f042141e104401c4c400d89001f00e0301c2c0ca8200113082c1062400e0403500042e181440ca03180d101c0c285c0515802c09155200b482c042c0146002c034062000d441005a035042845110701c129040502160780800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 135371798 1250 135370548 135370559
    0x8040602160312030e10060308090901050105070f031b02040f0b0328080f0d0207141015030201180b0a0f09080c030304031506030b040605090c0a030206030705180306040303140703050709 82
    0x207000940c1c14042c030040301c50030180c50f41c4c54000c87e0150f41042ea581800014030324a203042c40300c4564010b140a10b401407603c00141c54179041d80701600c2004040003070990000d0808121100f421030703d030780c000f88100b06250358100080c2c000e00b2550a401e0207401840c0e4812250030204805000909012000e400241125035545005901070300c0003c076000e07400d0011080341d00141c4050f00b20188924140210705401c003e042d41361034151350308a114603080c080014031909000382c010f4103d0340e080c2080d501c1901032081001c3d405103103401c04005860f0105a01d00310a9210000d9600d035900e03078440c44001030f1503410207602c400d246410641c0541c010481000020080411141e40e44000800080d12546a6548960a00040d101a28419100e50038001c0301c08050050303a000b940c0845803c011246554041a62400014412814804081850f846580c20700c00c002c3c1e00e2610090503102039281034a409001440600c0c031031b451070b001c0180040e0300d484c040d10505000350307035a40742d4000c19803520 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 135373048 1250 135371798 135371801
    0x907050109060f02240105031e0a11030102070203010906062c0c09010917061b12010902091c0b0106020d0503010b0f0901030e0102120a050c04260a0f0804060216031203 74
    0xc3d04034500310f100380d190610b86400000b00f00b0264101d4100382e14400e525045c205443c06d54401d4070a0310480e2010000c4002d4003000405840d000d40c08042102e907103100500081c024000d10300007941650078070458a04211090388180309541c1d1080c2c8508501c06c03142c1032a1446d90647d5502c030303003010400d00440c40250f03a000240510060514002451513280e806036002da041c900d50800d5164815400c0c0444100c40d101060801c914800d0900c0c180883d19022902980301032156051080c2c0c001240d480a485041d6a00e400342604041400d092040313191203285003800740300d440c005000e40b0000b0500e03184908100c3e4100c0300e03c05005800c021088182c84034592004450700d050541e00c1d080c0e0698048280003918420080035030f40b01091800307688079000c0d00c9008204c020080300400c0309009200c43d0245050140104481090032550b101c00413620300303031581e100030380104944507006041181c084000c105079402c41d801d41e003170706064942c5140305c442d0a000c001c15082a400602017240d109 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 135374298 1250 135373048 135373067
    0x203030615090a0b0406030c0302160f21020618060f010b03070306030b0109091b081213090e0d0e0103090201050a05030a0b0a0b04061403071b061e02070506090705010906 75
    0xc454600d410b03007000c00104056090392212661580c0410100003058251140b002010308a00341585408140100c264541c442408018845500001481d0500038915004003070407000c4d0716400c8840015000296490504a85440e03081c81340c00b40c1268002004a8014000c80c204891b500c80ca901340120b04c0d85980005007482d00305030f0342e9170b800408075441c940802d00030071040c07100041c044950308024440d0407005d4143c1c007080401c0d070b0701007003000000641400c6c1e007020203409030385404c1c10450582c04440c80d80d000301003260420a400c0501c000100c1c6c00300c8070313009944404c40e1904966005505403404d10300080c0c0884c01c01d200145915014000a6900000750040081d02c0a6040c000802007132441d00a41000103010605001e8a50002c8100050100086419003545480d00004000848060100306624102d0030260b00300915500301980101612901c00221664110343c03000039000000c040c0d400d44a0300300031403a0310b2000b28041040d10410f035103100031a82070800c2520081d08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 135375548 1250 135374298 135374329
    0xd0311030f131d1b0f0c0304081f051b0f07060e1e0106080c01050708070b130606240e0a0807080d0809190201031e020c0a1502090102030306 62
    0x30400c1034006410089004044041641e04201c0d80e250070030508602080c801d030108440c500e00c1c0e1090054a501301d240049940c11303980d03c0c0e16607402c0c65040b0300049024518148031188000301e40820409408030708001100d4102c9441701c54040602c00000680310142c03240c206014024000c8580f95010324000c0c00e90710003280b42649080030550340e441c1107601c18000d0f5007003030700428900b40d00d0083d480501304a00703d903180203002e01802c14140c240c035203000c00350781c03410300c04009032803010000c111b0140e46040740c100d001c2510310314004407020615051040d04480c040d1a04201061000c13030b0a14038071680580641800b03051440d400c0c280d80040c9210344895101142c0e4000240340d01d010090704002c1d0059802606405610b510007510350140a424291660003d04141c03190980e80c507040080c581d02440c0120317940404c000f10b01f040a82c4100c0e210300301800041c41c00a0540f00060301030109114103d03032080025010210b0049000b81030072240181c10030000f18080e49414800500004c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 135376798 1250 135375548 135375553
    0xb0403030e01031d06160207140f0a0e09010207020a060503090606040b0f0409030201150608060d060504032a14011a0405040c0b0a121406010c0b1f0609050306060d020d0311 76
    0x81d40340520410b032049440c850503507548044200244520a00300406c4882d40e5400203221f621b0500c84d82540f1800840c1c2d0f02030090271100e48851042c1d6403c0f408900403c0c001c1d14454050400c0785506010b5440700f00b041c1d004007a41c1c100041c0052041040720311074100c010140406495880070000540304001c092035002c1010b605100090780c0710720988000030b12230f030000103140305140d00803075081a4940c0300c00180600081048403d84800c6440c01c05a07500c4880000c1c9a1b98515007a12881c0070300030340031071100c3c0f580480c07840c8044001a0303002d464004c0d240d1303074450681105003a0a84450160604515003201d8440b02242055001680c015100d1282140c0e11521039074510016044011400005407690800081002185c4101e0b2501e58124000441c1d6143c1b44001a140100303440d0000d050042d0130000a1001c031031080988101410f40103002401561030000420780010f50003801c0c031038019040401c420386050240d480c0b03803039406408810b44d40c0341510203032600302d0104602d00d41c50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 135378048 1250 135376798 135376811
    0x30e0109060507031e0b0108040b04211709120a050a0e04050a05040c08070b030c032203020706030c0c050d050f0708071a01050402180907020a0f0b0106030e03040b0403030e0103 78
    0x1a03018000c2c0351040078155400128031a560b480044140400d410f0380c03101034600720348043c059a21981040e070040e00130803c159a61250b140c03214600040304c5002aa07200300c2c4248882d260790200341c000403105806000e0400e6204ca0b9501c40c0c03189441c2d040da9003c0f440400010b003001e8000e01c05400c01c500103007031072261045200c01081c1512011101340d101d0302d540740200710410800d510410040e050180003014075604041e0080d111380b1020b000b1445007d400f00000d0b20079081d280c070002180d134108400b00060341d05864040e580d0b524601aa10204c0d0515080e40c4442d03201d491a14002900000200382d24030b103603070050320294854411050fa0400800c080404214094000d2810303070300c201c4268030840944000c60400080682005101d5401080014890b01080001d0016250211020341c402e4a030a803007613107403510f8030310002c0843c21400e603440240180d280d64141201c504d500d090220840070340071192203204e140164405180d0900051004c80c0c4a010900b40003c1c0606002a10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 135379298 1250 135378048 135378053
    0xd09060e13020f090301180c0506072d0204050a38060c070608060103020414040506010908120304021c0f03110a23070504020c0703240204080d091203050307030e0109 73
    0x40e6400003050380c0d80fa140014150215040c00d101e00444000d0382c906010310700c0041d6031404608400792040c40d01c10040845c4000a01209944c00d240c1114644c00c071491a01d028903200c51800c031840821b07442289004009984100c05010790030112001c030b010f4107180505401074039400c40c8020070002d03000481c400280070540702d0720001c0c4280486440100059860800020000c4400a104030704041c01848104440d05c1e18002c159004041254041800c3c0c0e10f400040344d04259076846001039108294528022045080003980941e00a03507142400480400c4114010803c5a10040c2800041004040424460751700807030440f03600d80c103440c408111521000201d544610250000c0030000800c00603a600401c0044014030b0161425414100381260440e1241000d20024000c0b910b6070b690440b10350074200c408003680a004404549550f110069107030b0300c5c10003034403a00202c1c1c0c49100126040005200030001564103940c1e0798515620610b007180034005140b5241155900c48004100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 135380548 1250 135379298 135379301
    0x100e010209030115031403160f020d05060711010b040504050c0904030c0f0c08010c080c0f0705030403080408011b020c0a03140c1f030c0c0507030803040201090b0d0209040506030d09060e13 83
    0x441c6132020039a00d07981d904500301081c800c81d0003009125240d2041001d030942200c0e01903139290842d00a00e1051341c00496002007440c0f01c40c00d0700010424002c1c030040052003030f00201c0d22020118040020000c91080d04240401c071642583c0c003600a80c070900c8040c2d4103240c21110590b0140c440d00e03124154800503910740b1240a01076400f01d402e58081001403003000c2c0244503041c0c442c1d0030780c0340c5000320741807000c110001751003141c82108110b04000368100500104008880003107501445081d42c865803106a54000c05041c118040e84000020410030704c10f1002a003a80290300c001c10410200d8074580d100d40616030b080c1e44034a454000c81c0d810003190780d100480e01d0a4443c1ea0340c100910284c2c1c60100400721001605494103000a030850540820320000c2c045041c4d0394082249076490b00d4600058814129541c44a0341038600064443d10403183d54014014110f802e540600464851508041e00e507800c15000c040004c4401c44104050b174490f0080c51081080544054050162601c0000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 135381798 1250 135380548 135380561
    0x1020f3405010c08091b04051017010906061a030a0b0a0b0a11061e0103120c020a03200a0302030a021e030714100807140a09051f110d02100e0102090301 67
    0x880e96503407521010842600450302a6000303d81c440600090b0254402043d80411004001c0f8006c48d60b4000155a11010030341902c00341c4200c441c100e40503a0500c5016000e080c003c441159001e040c5a40016003402004c92a414801d1486005085540e81e641d000014218004541e07404118142c0019213980103c00401c070600c09580c5500110b049003420f43e14095016202101030110200301c60141240d0059450559500240c810070702c40401c2401c031416455020f0295100889a10000c10880780c0047e0f007031031801011b6240012001c43e02008128504c504c00a905504041c0100d40140b17046d200840b407541001100301b004c2c030500c101091524900e900680854083e5840000c101e01d08070400c4507072100e03146032601103450900700041000103100c40140c00c1040100c0d1b184040c40c0104416000b514015011494822403103171a660850180442e4070085100501441140e8074042001003050280ea00113004030315030130203000020b2078000c512007007955017400000801d95082c020304 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 135383048 1250 135381798 135381803
    0x2070b09010c02090114030111040b1b0f0f060a050903040312030e1608030705010f0203070906110309100504150f02030322050d11060a060e060d061407020d030e01020f34 75
    0x1401b94203001d240c2160b2104694105c1d00e503042c481000030f9589103003101c629003600b82c1210520144000c2852504000c2030340d0000c1402018011102c845000030650300c50318506005000704d48444a56940340e118034000a072440307021403002041c5c2070180c1c100110300c5030340344d003120000c0301125441c40101c01d464000108607000000c1345800e00c038090150b00d080e010314400442c6107050004000e00350901d9403290300144144294034082c0540144107807049075902900d03200400144107001015a0f00c0340c05212801030000809500551041c00d860610f25406d800551554940340410b00300c4110140650781d004501d44c40d5880000c1051041040559094503007900c0e801c5401070441c100303e80103110958403842c140b0100540c42c4403150b1290040300c1500c000846040c80d0800354068401100c50f01d59002044040c007000c01d42c0010700800c14026560104000e06098480034243d02c210b103040c1d10191303420320000d140015200f01d010104540d9a014810003282c0340c103450000030f4091000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 135384298 1250 135383048 135383069
    0x90c03061f090506130506061e09011b05100e071701051509041a04290415061805090304080706050a030f0b0306040611090a030b04050d0f02070b09010c020901 70
    0x107141101e8030781d40d00c80501030102c003d2040d85020030100d000a6441204200d40a4070b400c082036407a15030340211003800850201940e880c3c1c0790610308901c103030311100c1e01d54005000f005800501c100c000212108582d44072000d00303801c404880c0d200c805045504030840c0c00c0d00991900150040c002c039a181034040030600045840e10f01030310403c2114440b0300095000f042c200c01044002003003280c1c0035403036401109801015807a9400c114140082d221001d501080d03240c858031080c55001902944524480c1045074074275070300d10280c0000e40769540700350842c14a0a80c207008444c041a04460b0b80311828100b124100740d55810824039000c0e20b0343c42500800c900140790116268907004400100d40c80030018001c60548502190f503c1c0c000500242c000360350784c2588403803042014200c95014100138007800301c0f940c40e8281070038000f00603542241c2620a50a41905450207191403112916464001c3c04d01030307150003035085442d84441e8044d410040c0105188006a980030300180c00b0301600e825 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 135385548 1250 135384298 135384331
    0x1230c01050f070e03150a0221040c050415060809030f030f01080c060906040311010c02100f02150f0103120201060911071112210409020c0a0317011d090c0306 70
    0x110407078244042c0c03030f8000704100b42c0302c000da0588000615851078038208102c8000f540d600170514009000c0e010200015080007564042d10300d281100541c051402260b246143c641e85d04100400c0714040345210301c0d0010841c10401000f802151400d0f0720240310002c5d24501042030b600200c95910880d800742c01082d200e001808034401c1008000a066400e60b2018549100314001641c01d000c2c5100c020924260340514800f140d2144580070200c50b40a00695084c408000010b0020030300c41c2d007013600500c40c00710350101d190364100c0d0060203100030b00e2101c503540c0d00715106d001075016a90002c00542d07484240006c0d00c04000c2c815024072a604c002100d8943c00b6610b802401ca4015000441c40ba64901c00707950540745000c140c00c0e126503400d001031101c0c5200d4854403451401603a2011004031300c0401e0791808030700c0129043c544580701759241c145a0340580c4190030013110038000c0d0180d02120015042c0503203a01d800180c1c203c44c0c488120f031690000000041d14103070080300d09900f103101106 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 135386798 1250 135385548 135385561
    0x14040605041403071a06010519050a020111040b0901050c031c15060503190f1d01060f0503070b04030f030c1b18020412200a0608010302091305030901230c0105 70
    0x503002c965501c410081d40c03400e030650711010304c041040008500070425000c04204143c0c0181304481c4910304041101100010665024081e40c1004010002650a210941980800500071181030311501c035180c3d03080003640001180c40340c1103101c11a00520040118070201c00407983c05540150008101080301c0b40c1410702c801014406500c48001e00c0000d0003170024180510003e03100c0380480da1400200200305c400070002800c0a4440001c0e41510f469811081003019009001503032030507840d000d84030340c0d0380c011305035500c41a2141e9004500e00380414030001d54814100140b446c00780ca00361140d00c00a848180302c4060840b03120100c1d1882060402c0350b5200403030500d00611200b481103081c10b01d4114210420744541c1002006036554503180c030095540399400780704800015081108071030701c8810203131120710280820f0344203540507400211b12030f560040700903000c0c0e44070001d181404040c40040d5108682000003040d0343c103040d403000100a802c030303010f0148a8211000402c1605240 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 135388048 1250 135386798 135386813
    0x7080304150903050d05040312020705031b03040302130902010509060f0d0b032121070c051b0d03111c0e1309020906190503191a0106120902041404060504 68
    0x8519403100d582007010791030100e50004255881c0c04940b850210b680d547d00d1030100c03074000c9148449000c05201086940500c10008090842ca820b111005280c41c0c03400840d0366602c0c0210320000f0362140035440c240e0050703030311604040000d91041c10002e05112850b030000d42290807109041d2810007001c81c8210460540c0c1c0202e1204101c1503000d03010f00c5d0084030054590320340c1c1010101c1e8000c4009030070b40050700d18240c103103c40307130b99100010721030b02307100f01c00905081e0030f0241910140708049180071040350100d10034031501c500500749800c00c2c600c0e940554003000b001c805846580150ac0141d140c0c155804003810400213156034041c8404000802c2110491403d009085840d2800c032900300140c40b4801c0c400e0b04034104544c90030640d00150114111011990401a0140034640c00c0b0605051904907000300544501801100b84035440b202c20b00c000024820180059140c103c50316000410340d0000c109240082c1001c40c00607c422800c24040700240d9045400703540e51020082840004c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 135389298 1250 135388048 135388073
    0x14160308061c050d0c150608060907150f030f0e07030302010b18011a030c07050f060a0507080906060609061204350306060a09030203100f0609060b0403110604030807080304 76
    0x2d4440304144a60a4450315a84d20000c150300b800e2195001181040c0100f0442c10840c0d4407000318140b00c015124800680c60340340550706000350344600b900220720042118100c4000640c0d41c0e640240da0622550300320082c01c0d024100c550700641c5d42105188280060100202450003074001044d641d0b610014403450075074503e4840c14404200005100b043c11030b01c04526070041b40942c4030f4803a10344104c80e0080d40302c3c828004001d8030940d8034581900f0000300b0a01d200d007420000130403c40d03481d42800d50720903500700c800c00074030780100000a207545001c0000c4e0100050207008141030a00428a141c41d404007520150307030b4800c8554680e11141824029401411403103500040d25168031000d02c0044e01020745214442e031000b05110300c0c0c00d03200707030408402142c00504450b003440035040510002c16060520070b08146c18100c001c6a41c840e3b501404080351113050301e0a29003403454542502c503160982851342d2184d4108000030105050348081d1010a0180d08419520b0070a0310702035805000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 135390548 1250 135389298 135389329
    0x1e051c02010b01050d050c0c0a05010501050f090f070c06060b041707060e0a0e04110a0605090117010501090303030e0c061317071413200d0501051503071416030806 72
    0x42c50390079009640c0c00000d54828a40040c8081050340b5400c80c0d0803802d00600700c0e00641032088c0d100c91b10a100b01500414121002900c05010f01020712003400000c040460b9a102c003400c0403804566128800c0301c0200f9a80d0260b140052103d48030402c40720560300940c01030180103c0702c90089980103050001c100100701c681054103000d9040f00100d0481000c5215000c01c510124000400f4010b2b03000302c962040c100100b00002e525240c00c00580b941c1c02107021640020581088944c0d038030070708000a816500e050312080c942074a95a02180588175121580000c5e0140b101e00314910b446807c05400c106074121a1403d0040c00e203000784601614041116000c3c0d48044004c0048a21080c000c12145500340c4140035605d04d001b01c0b00c0040c00000130082068014180b001c0d400000341170282c204194540b00910007641d03580100040710704c084521000704081000444d20301400f815511250280f14108075041100e103903100701e60850107001c1507004c03940e024204036203494036200140180e88d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 135391798 1250 135390548 135390551
    0xe0618130c0f080109140619080d0f0e090105011211040906030305070203150601080a020706021201090f0c030506030d05090a030804080703030f0c050d0e150315010e1e04091e051c0201 81
    0x30fa503151000746d100f40a400747c1c0c014251700896051801c104440d51001e0031501c0201d4400200141c1e00a20712010b01d1605000030b2204110980f035807070905212812610142e42c0d1303046401110752501c00070800301d02c840c007590708200800a20340500f4007132040150b0103500c0711602c40445006060600c601c0a1041503002400810046543c1e04020800d4008290780c2005881c0c80203880c08000a1081060790315a2821200c00045c540f203483d0003050314610203010900c0a0303101d400090301682e60541d4400da0580101c0201c49070944148081c10b10800c1c01424444000d0396a1510754a5501981010b44103802902c0306000f4140c000c1e0401303481011b50b00c0c105100d400c80b5220790381c558a003501d80c0300170890740e00d000c002d041c0e07201d140c190f000403029014a0354030700705400c100e061404c031905168003243c1c0320310020100345081c0700d0114221a4588a9885c6c085000c0c08001c01481601c40481d1500054820a5044480242c80c038480603c140003c00321110790250040940c50b081c00c0c10b0045a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 135393048 1250 135391798 135391811
    0x9060906040512090a0314010c0e0402070209010302120a08070501020c19050a02040e070f06030b0a050414010314010f02070b06150c1b03010f0c021c0e0618130c0f080109 75
    0x1d000181c2c00f800d0b8050059041d0716001c0110024012100030391018001c1c1c00c070701e0b0000f51005010350120304261419140c0d00455100d84090109038000c80c8006503120900400401c00350400c00406110300c80d40d6400d49000b81c5140d61020381d42d4028680540782030303602052081481c4020000140c207600741032110300811300e096546580e60100118024000c913102c0b510102c070041d0801c110000350100310071410345640c42d048010000c204145030700d441410031000c000781e64181846089a0b13468101c40403542c503800e5440f04404150001488489503503900d40c0200e140340c003840503004261113001554807500300401000040703c0e09548092500004001150461a0001d41700c5600c4e0800c0c880e2800d08803102c0006401044e002c0b515a05060034600403840441c1d01003010b64451b83d910514207510018600c003250010115201d0310f820600070010400d10404451a44d04428001496803802c82518010790090310700d080004030110301031043c449149034000c114140905403446082009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 135394298 1250 135393048 135393053
    0x80307020603040f11030f0a02090a02030105030703030c03020f06040b150108090c040c020a0f060608070806060f0d39351006030c0e060d0b0f0c210906090604 70
    0x14030018000034030110018944c80100b200500f00d100410314010140c48413180720001294540248840817403188028800064140c150340c401d6906031140a801030000904507542611500c02c031400079000e500c15145007042c00082000703e103110318483c0c0112000da08240320806004155a00e105060240080800006030800152100f407000d0860700407401c8110a901a8101080c5c01d4016040550091503c028010300760400d00444403010200c078a040d03030340c4e20040d0f12450141d901ea907008580101880c820302d08520b454003064015906131540181c0485000740c0c40b030303101c10700103503028890509004089041010310020000c00c0d00041070000e03901c03030004140590740440c1000a0000078a8401007800b009804040c1c0071f006001c200300e039242d08042e01900641d200c0c1703840460300200021106d0802040e011025540829941081c2d101d06c00703e0350a00394003e0030a0303100a401d01c07a0240008410512140045007602c0f080c0b03490810080c030790b040c510f00030b0401100ba07101d01c050000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 135395548 1250 135394298 135394309
    0x6050a14030f0f1b040b070b0f090604021306080d0c020406050d150507090b0304080d0c0c03050a08060402091305060a0b0f040b16060f1401050108010612091109090d080108030702 79
    0x6100701d83c842d00e03ca503aa034850038200261070698202901200c00b02d40881c4201c8000d008198050041407000003990b105c0e0342d508503000041f200b0700c05503084400464014100840c02c50380d882000d05e07000c198140c80ba0107a07494a8000c0080400150751000381c0c6d41542010702c9148090031064601110801542d11a014840c4505059185e02a583d00016800a01c102165005040307a007100e280d0303c1c2400d0510300b1042d0880c0c803403d0704e418648035180250500800c445503046606071921401c6c01c40d1407006441d07240c0c0c020203954005800b04144c888540e65001c8101919456031400100d41c24082c042c405a144150008002042c0802c604506103010801740c504460152610543d181c600381804004000c041d68014a02da050401020b50350a13290010000c0e0707007150682c802d150780eaa000440f0001c40030f10480021420800c028584403a15800c40300c07201c0d00680d4950403040018010842c0c01c81d080700d40302d4090b0040007844a1241e84604010b004041810045040c50003070b400050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 135396798 1250 135395548 135395551
    0xe0606130209060a0c050a0203011404050114011202040c020c0901080d02120a02120d0b04020318060a0b09060f03071707080706020c06030a0b040f09080301080d1806080402030708010606050a14030f 87
    0x713061051401140003003110800c82185250703805002404034280001101007080000c3c2c804456650820018402c803400c0cae10350650407214a4004841c4840050b000e100083c484520500c0c02c41c000c0d01840ca0707450b05c4003013407a4000c1c00b5610040c0b10f82000741400900b0308481141c2c25603c11010011b944030301d640091301c0c050114031080200da139084a1039202d8001d21b45640c41d16041400070040001c404c3c50084101c225243d5501607441d16911064107108403090204000e90084038000402c2c07007030a19420700d0050640150440d004e250b26107140510560403550030002e03070390102e00c003804403160a220034001400140024051580c0e11030006249010041580c1c031925940c48500505035a15080f90070305d1004404e00f04014031700c506002d40c90394000d011b071504a01c02c00c003141c0e180714800d801001c40d00030710501456405080000446030000c0140050360f151050b0040030030114028842c03600240180d0311055034a188600b00503103060380c214140d01098209104000b0750921009101c2d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 135398048 1250 135396798 135396817
    0xc040e100c113f0c060403020102130e10170109050616170108070303031125050c122107150c020c1e0d03020712030309020901050307150302030702100e060613020906 73
    0x11002030380510801056801343c1001003c807441018240414550194001c01d0740c04c3c81d00c0c0940d80340381c3e1510070440c440d080944415810909014040004281090300b045495a480b030002c1542c1c021521214030b0444161280040c483d0714500c01503440340c0250451058507409200648a50300d8484507688903030440c0f00103801e068603041003a440300b44034802c035081d00c030240303d040850f9060001040c0300e00701d0b01202105c1e11f11404009220601c0c00104100314140d1580040030204541090740b090218020a0740d440002c042c007141000940c0ca4030303140140c401d140c0c000950000401f60080c80e024000750903d008103c038001030503d1168041480304d0b0308005992010704610145400ca141801d290300c144c01c23940400200904269164211075602402118011516601c440030191a0301c1588520008004144001804d20b03009802640e4814800c0c0180d03a44e40003c0b01c44d0200340d51040c0540c00180d0001c004202031407030305060104404510007000c6003001100c4021425920030044403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 135399298 1250 135398048 135398143
    0x904080318011107061b0203091c0218010314060a0b0d1e0b0a02090301110a020316110405011203030e013b10060f06030e0c040e100c11 60
    0x480194007400d4000d00c12141140c2c2c0c040365251003608142e070007000d05820880c80014000d5484100c02e2001007510049000203104111346820303403464805185070740702c08981120040e0101000c01c4000070b0414021401842041e0b08507000202c4681030000040821404a141c42d01d40c0c411525186a0b1035019548642040000382c068218178224a032418001014124090708210b9114150b40107021448802d0b0003d100502c1c002c0100c541034000c0d00f5449005a20512a800044150440c80e01c540c1e4020b00721031030002d41c250f0114051b240260400c1904a02c01041c40301055418170a4100540825008104c020840f90070390010362908a1901791f40200070403c8050b00b408082442c4c44004008119000b8040f003281e80009000c0e5482142c0e018900740c04001034950181c081e800b00b20100301c0140c80c0c0003035070204000080842003d100c0305803140c00b1407080a40014031600303400340c880e5210140c580d003202d80c03201c1c60f11414000c03003011b2481c201480780306611b4240c0b0842144040c07004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 135400548 1250 135399298 135399331
    0x11010b0409061d031303120c0203010c03020903010605150d1d010c02010c08010b120c091c050d081e0109021309092402040602060f0a0e07120312050c031612141509040803 75
    0x403ca45d00c255805022b0b605518000f00e0140c4070750113034020140000d050707000788140e96940081084c1b40800900d49040c0300e1041000360b048100c9030380000e51158202180803070903514a2142030031520207040c0500540e5440c0021800b09807c84406401058040b2035940340502e855040e800c0401c001e040c010740b0075400300d80150a603a0b07a2991089207511002c4a0001c60b44504045683e003a585181002103080358011a50300100c000c604c981600080c0d91a00c0c445e46020510b000039800b04686c05a40103180d040480d1800147c02084003e5005200b0b54aa010f05c5103580d076107a04c0806507201c1c00c107104120402ca05500810841e41c08054404004103955554043c0c00140040802c2c2107214083c80101088918400300c0d0054103600170b985401c0c5074122606030008645e410703121890103d00910000301135040c1120a00e40040d4146014244000241351010507555464401417560002c001084008e280340c1390b49407440c140440340700391241090744450b10244809071010101c1c4101c1304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 135401798 1250 135400548 135400583
    0x307050a230c01060e0a02030c16150f020c0606010318031d0904030207060314220507030b1503011404030906050d0204030503030f040b07080403050a11010b0409061d031303 76
    0x16818440004031501c4659a0100d120515000b041e0714018410818a0000070a184448901c00c0ea441000410768980c41c10003a2005d03882402e01d040000ca6610844042840f000c0141340076410910664801c05070326509452129070400100404c042e040500e03040b0300d003000b034a42098180c941605030405194001c0401c41b90a5044021003545420107d4041408209030740090103100322811a5410030128400d5502c108000c1c0f400e03101c1000f84491103100c81380d401080c429402d44c1030b115408862074569280c0d50341000c8502103c1806070074401150003402406d080c01030049002d801300c5200c07140d00c1c0680d0040c2800c080c81c00b0700ca0821501007035001d41703031110380e040f18051900901242d0703c903d8140500f1903030a9003110100e5600c100940820f80c2240103064090043d41e00d40c880c07504002c62441c0803683d1845100400303030340d076494446030600e98a0307501c103502416000e800081002c255603503020391403d000201c0d1412a0784200603036580007001040d45c030306980d40410400d601c01c41d60f2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 135403048 1250 135401798 135401837
    0x1617011503060504020403141203010e0106030507020102070b0a051008030f03011412010501080c040609090308061009030b0c04030c0e1005010309150507090312031823030d0c140307050a 82
    0x1a0403c540003440010048103018078002800b102029200803181c0640744000c04181c60301081c8a1480e0000c0c0c0c0300014041180203402050380070700d0600c00141844215107880c2240704081c0ca40030807180e9500c00b401054040d42c41110060221000210314183c600d41310440700c6e00c0140b20b09110500082030b0007525649a415600201003014002e00003940c44c2d07000d0540b02d5001c4032181e840f0310301e820b44c0041c0360b6410b805010b6a16406481c1c1c141513690b0001407180000700f901f411010800a100c010000460401e040f40c0149101c0392066200c0e421032401c200300b05201d41116049880705410003c00c10b071a03c40f100187d030021300e0040340316000c525203070058101d00410202c0080c100000c020509500c0041c0ca000c8901032000801801c1580070140e04036000c1c8081e507c0c2040f946c000a00110782905403c1c400d46503003114110716000100d642a066806c43c0907507444403600c512844155030f61180c200415400010522803a50a1031301d000b0f810341c410305120070144146102d041c01651881c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 135404298 1250 135403048 135403061
    0x130519120605060405180a030f050c01020406050c060901140c0a1e0e040b04061202011803020406060c11030706080a05150402030106020703020a080307020108180f12031617011503 79
    0x155003040c840d448507807420501508003111524000c034907203030004080b40c01028181001640b550054494803640d900d04459942042d0858028490100040e41140d182480240000c080b15650070340c5404d0f12441190404a0243c25030300c5030703030400d03084003e5501107004407600064000d074901e540f035094071400d0b9a03800310f50421001c8070b0b401413500c4058540114000a4281080703074200034071482002000125002c50040300c0b00041160760040041d4090b0025460b02c0d454000084a030315540c0e4000340030344401fa001000080d6615109608109040c0d03418024100c0413000350913000c5c1800720040c01c004004001402c020f49400c00704d006600d444a00040c02c0707034040e006550343e40e11150040d6580352140710480c0200741422000400d1803000c01a01e007603e5050b5900c425903243c081c502c2c520310010141ea103441e4003030a1608100b0000803c224099000a44645030322450200b0b07100c600c003c0b40c2c1c00003000303201242d11034440c400441003030941543c2100fa0b035001c20142680048008084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 135405548 1250 135404298 135404309
    0x912081506040906060e01020109230a0b070c0b0a110913201903110904020903070b0307210203060d140f060a0608120c070308031306090b060406050303130519 70
    0x180400c0700080ca130409003c0d00d825072201442401c120f4012402c0b1101c264000d00a0644583d0520a040d945400360000905040803500c4065040c0c0310042e4410094071450b010400c05d404603c03c01c03103c200702c1940000003034010048590448618420340c03081d031041d1031007110580b80304803102c02e5503408803d1000d01ea2840c20580315411200e035a1a61240020090010014100010580c071a000f13001201c0a51a2103a08002c05d000c00c2c080a900500700040c2d0501840c240821012040400340d4851009030355504185400005040c5080444031224450540104100000c0752242c5602c0070b07130158401640041c40302c50421650905140e20070302030007806140c0611281d000c440c0c22281c280e401250540784946100e6810942511810300c0d858102e412102081020410090186611203400180e05817403140c0b03540d8050480768201402c03103141440400b4032140303003040c5c070880c0c01624042d0001d5181860a24505c403043e462482079600c220003003074000004c500c600055000170304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 135406798 1250 135405548 135405559
    0x302071809050105040c08101a0f0402040e0f0a0c090302011d060c010c020f25060c1110050a02060f0c04140607060e07090c020a02010807050a0201091b0306050a09120815 75
    0x20146401c06c0b6036800c61141000302e00c52100304100040c00d07031094004165070b461441500d5000c8105000640b6000112a5170090f801c3c0400180011408211440b40c0744005029009241c1000702c1012a492541380c0c8041105000303013400181d0308521401c244964058a50390300300040030018040c3d03c91600302e1500e40d428860545a090b80008854050749842400c5c5d91405d50003a10b00303403100a001d4450341c1d4490790150204061070003000e802d0401c0e400341d001d5408440003040454110560744c0d0707100c0c0c002840080c1810030305605200c0300750404811059210700b4140000035124074000ca0250107410501c400e240415580d076581150580c80d0700910030301070040108a041d03102d203100d106012113907040085200f2503901c08034040380740d10707416100d4481c2c5460f640300444050f0801d004041c2559610f201c0400403d243c0704030b50780034100c41d026402e5200e0540ca440029500050400304200d400d21401000040383c0340030000e078906442c9810411582c0306054040c070103544050060304036 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 135408048 1250 135406798 135406801
    0x906270b0409050a0207020a030b0705160b06012c040b0303070501150509090303010e0705030402010c05070803130e010308090f0a12050c040b01051c0b0f0604090212010f030302071809050105 84
    0xe60320001600848040303040401c007641d0f070405603109030b20a41d01c1c000d40c400c5107074405000182e05607441981103000c52402d5800c14206241600b10341d0702410303098500b03940d064208041c0d580e01160a4050b00700141d0200fa1403c0410102e120b034018189600f40f02d00d894840c501c0c0315440c20015031316841d8008c0024031a85000311032642104046000d0319000345c001e0030000d19801c20020889040720414800510503944105007100c40b500090400c0f8100001e0004810201c6c1d400c000700740c050555080a15a600c000e03901c605200342c2540d01c40386903071241d40d00400210b07452074160b556502c803d803654a1034050300400aa0040701c20b0300034018902032405801c0900400244006041c0e10a94040140d04c02010041d1082e0003402169001f580c0d646a6074014101d50703030004ea058001c0035013038010510403600000c0203900710f500520b1820313a02041992076006e460100e41d0041c0f294250b10501c45045882c025120321550041418505203491810145400c5602c294622a0004020803ca = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 135409298 1250 135408048 135408059
    0xd03021c0201020d0501151403070819090212100606030c0509060a140a0201060801110304081c0e01091a06151b1603050c01020c0402040b04060c02030a05030703081b0703090627 78
    0x118038041c2c4107c0008907040b0b1240e182c10710401c01c0302c0c040d0081d500c078030089070307686081081b100d0001603030806c0c901d4440d0aa44010b0302da403ca14004c1558240280c0640c6510500131070448890b68071400030182007481c7c00700829004030072a454410240ca089556803480c1c48147c03902c00644c070041c2c1c5103a0000030107000701070f819800700c4140c8410030300034050203200c62a15200360201b501d01500303043c0104a0a0f0304481e42c03000d8007056284c100d40c007007420480026510f085030988502520701c80700280c003408009a050318040c0d4044400c80d1540e2134000c0710102039006004070803c03076125482c2514500d240c10810020303281240005490000c0080d140e05c4d207071307031030b0036181d8481400351281c603403250101d01c0d050007514140c908070401c00d41440e1030701904944042d0942421703a05401600a0103010410510040c00e2660007501e9444007401c104062440140c4c9130040c881d43c11006002000000e0390041124040381e51514226030f680300c2c19500c442c6500c1c048070502c0c101c0342000900091 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 135410548 1250 135409298 135409319
    0x724050f0a1514031c0c0b0109020906030a02160501050705040816140603040c0e04061a0109051e01050906070602091e010c02090411100f0e01021203060409030c1e110d03021c0201020d0501 83
    0x14158494002c1f8a0540d0342d9070340300c0c4142e000d107002d21a0301900c1030001030441e032a070303034090104441b05000d0040d408009850b02400c5031401c2c4c8905001603c002010f000300441040014915403082c2c5524102514000c10146030b40000b40b0b0407031040307a000002c9414041e0a91826020340903600b040fa8075820075140c514002c18484440c4201502c000d0021050366018282c442c00300e0308041c184054001c0d150400b44059040d980700a0b05000c0240800d4049803141130140c002940318400040c0d4a071010310402547e5204a48001d040c244000000c007a1a40d1080fa148811030703040c1c903250641d45803454031001c603039422840c40b500148486104000580c0c0310880080e050f0081c0c4880c1c0c0d220001d8401280c0b03d044042c07410a21030401c00205c3d00c242803580c400c042c12402441c1c21803d60065030f40303a0390920405203000d62070601a9491350280700304281c0c0e401f5a01d0044138502c040f00b07001d503006511210341c7d42541032884064840d81c40c4a90003901102c40391205502c0c1000f041d81c403124103c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 135411798 1250 135410548 135410567
    0xf040b1c05090a0506010e0703060b0d020a02010e120f0304030509180709120b19150605030739030e0301090b01030b010b0c070b0724050f0a1514031c 66
    0x142580c100740c0894500d10000c90498546900080545040da0a24041460b03004001d4014010150344810000701c000c00200070b0041c40d0103c00c00980c0e40c9030b49800084c20344113110b020b9034080c3c001403480c180c04070b141400c03290040c00c80e09045441e41d5903814160b030740740109a4001e400030108030300cbc1100c44a20b00603142c440d1041d601c2e0203141540700e80c100d01441d880401c0003000c41c420200425502d4441c1050041c13030000d6007101040402d1b03200319a000c411017075440800030540c04014804100d8004081c11001580da071322074034480040703184411410280710360200782c1c2c802d264210014503100d188880d000e2000a0002d11620001d071600f6005038409104c140c6038855200300124000414000f12102218204020901c0d03509080c884241c1d0b5002c000308945080303841c00c0c0042a084c1c080050307106020040400107440c13801da0119136021800a00800c2c88500d00710142e045881d0f806841d2040d04d420b1b01031820002c82e038001282c981540002c018048403405110381100300c1d880003406c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 135413048 1250 135411798 135411847
    0x60415091205030a0c0302030603030d02030a0905071d0705090d0f030c1407030b06060a050415110607050417010b0102060712091709030d0305040b13210504080d020303010e0103080f040b 82
    0x400152843c181704030304078082a036085901d6001085001c4203440b40e42c000e9504110300c1e010001d0b007103100d0741d2050f18201881c1d2100c0b0700801c1e01c000e0702c1d00440040200326401400d82c20f055240420003000520310112243b0001d05031542204c1200030305114034580c4c142d86500140100c00640f90040d0541d945110780b00849010711034000080c03040c200482915102c3c481c03900d429081600b0031242c04680c140744801c400400c907a851700b0310a044000c010b658000c21040d118183d03200e04001e003000b00d003198000081001d80c104401c84546990028405500c08130a00e04204204650150000a4002c0810192200040940707004102ca005402051144421803c036044410403103c1a002e50302c048030090003602d080000283c1e4190754110200300c80d846010b03202095070b522840650240a04a0940001103000c60113001242c81085140c0d4840c08c02c0c00114159854820b00d980003c00c1400010f2005802213410141c41e508603090320b014140c142c01e8a0340f90014265401c0d02840c0c981400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 135414298 1250 135413048 135413051
    0x21c110c0102070b0d0b06070615030606060513030b060123030709050109080a060c030b18010806010506040f1205120f030a060f0302030a0b060307170303040c06050408060415091205030a 82
    0x14400355800003d01c1d2085850b11880e280c2000055800c89005040560300582c00c42c03010001d02c4005038035449881420f03101d070300f14540450700b182009011520320743c0050003803043c00c0010300b41d0401444003110880b0340c02044255155200001290060701090700045c2218107030304007480d250001c601840c0f15800b00e9944004e040d50301c400442d4848160720484065030010a9200003143c1c82d41c110a420349081c2c1400300b1a440e074100810b0f00c03000c0d240d16a41c034225140d00103201051050004d1401001e04843c090b05250501d03101d04202c8019214440500c0d0642d42510100041400340c1e07000031800c0c00d406070325421b41c000f80303d0391580304907140352240d4a0f0000102c0c55130482800001900c2d0003400070a241d480319992000300c5e14001d0801075251081d01800130f40300c440d8402c48400c00c840e12001e180c036030600740b920400400c00d0b6040311060000030b12050054900000d20140d01540188914149220356481e05004003294000500040c1c0319100d04400e8641003c002c0d8005da00c003100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 135415548 1250 135414298 135414313
    0x60a0c1826010b0a030609050a02120a03030605060a0906032703081b1801031a04020f0403061a150f0f0d0209120111090121090302010b0a0905070519021c11 69
    0x7070311800c0f00c040380b075070316407100071072500f03102162403540020070582c071401c110b601c1d00c04140c00048003840d0a11b008005584075101072802c0643c180a060b0040509480d054103201000c04041c00c045c0c03d07030042408255440120710541280c001c0b13941041c43c01148000b80540603414010a81141120300040d91810a0040b095003800d240454600c103141c2c0f003420a1610740e1200441c064001f1a6100c40450003400c4402c1c8180d445200501c8010349440320155502d25514200040d20121200c0c03821038280c03900c5810b0355442d5906160300c40c9403080e6400c1c0e070f1182c0c03020241c203250080320080c0fa15210085164a10041140d0080440b040215480b13900f4a281440407801e07159550403902c4040003d00c50304000703500444110b00281c48280d10130468010117080e0108403400100141d0040c0e440322920360303080c1406601c6401a1810a0081c4424505000040c02c1c522482d40b98041303411101d0004401d10340b0903c400f01b05030200d241035415440c5a01801006843d0400480485001322003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 135416798 1250 135415548 135415619
    0xc0203120403031403250f0306050a050603060d14010513020f04051510021e06061f050304020f0d1b030b01080c01081801060b0a03060e010603020c060a0c18 69
    0x1040d602101d600d0340d00d4160001e0903010001300f80d00080c3c10000d42e40002d03e6440046100a0034103414802c00c4e513600e07200e51107440d00c000c1c15200254400b50188010410510407071b12142c003161b070b000109aa4071803440c10240352a00640c1000a054107041d440d08003440035403074a444008a06900807240c00f107180072150304102c00c5803402e031296681307000c81006030b0955040c0380b505124401c41500595400b0308070303905004e20f40d050001c641e00c000e802c1401044201c0c80c0c213038080c19a01d1147c1c400403015040d103610280c050302c40071b000688150340102c0200070f03607554641d200048a41c020a4503d85d010000c40e480d100c14001d000440300c9a0080c4008906254000390071403840300140c1d21801135450351555881040c0d1040740c4101a07548600010a003402c0030030003003c60413095940000d400303241041182e01e220040e003080701010700402c0140301c00030000070030b6508011403510018200380e04c00301c15210010020a80d40020800c03480025400790b40204071000f0b0190030600240c003100d2076 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 135418048 1250 135416798 135416833
    0xa0204110c0309040e0f16090e01060e1f051503060102010b010203090a0302061303050601080f0c0103050c0904050a0603022d04090302190c0503060a0608011401030201091e150c0203 80
    0x1035807095000b4004109103240c180c11408410083d10b0548a203000300c120014180710b100b0030900d0038520062400c00006003148501003040f45080002c008080c07c3c503000100411001e80410886152101003a000f00d09041d8600d00414008080e00c595206c0054140311540040311041d01552904189c0340565001208644480d9402030502c4070090840c4c5c02c0090681041d07500750301514140001000047c000c000e403501800d4143c0c02440d105034071003440e91400c80c403420342a04260429091084818140060394803420044401044503540d003840342000340f01d240c2c806035000031411400118440d00410a814140310039140a10f00a540c07420700c410399101e0700700140145e0090509407001c1c2c28109014049074810102c010b0500ea581000a20f40402515030401c1107a641c071081110200900c900342040750005d4440d603a940c0741d6000070301b90605a1084110003030300004c04c1385030b01c1c2d100c001c2d000107041d000c0300b45034080640020003003240d149100224024810b000390b415010340c14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 135419298 1250 135418048 135418057
    0x40504092a0b040b0703020309060d09050d02120a0f030b090106091a0c0d0503040807061b1d010905060d150902071a1b0912030a0807120603020f0402030c16050a020411 74
    0x103045405140034134000010145a000c1d06050301140810303c0103010396568100100710368070006102042541e054140f0a05060303d521114065500083c0c1a040d0b940f5440c2c1566041d00003418142000010744c5020340240116401c0c25030700000840c008100a508024080c1c2941c8000e005102c0d00a04111440c00c1072040204240c0240c1c00709540d030f00c0d064814030043d039000344500780c110308041082d81d861080e200611f5601d4654280300b5051900c6542c0558401c00c03250000103207902c804603040000e406981305000d0729000e06c0700060300485940301a00407003400e0709154503076140a0355403100034000790407203030341180c140300d2020741804030700803c0c80501d009040e50b160007a20a070480c62410303113641c0b000041c1500101201050091070405101600546a03103031030749001c80c0f800f084010280ea2420311510b03c628074141c401d00260700e403141c4505902e00242c40040c1e503034440f030324070004070300540104005031442900c02e03500f04100441e2100c0c103a44281d40510040702c0300310030341c0400c2c043c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 135420548 1250 135419298 135419309
    0x80c101517030919050a1202031002090d02191701060906090501050109091e0507020c01030c081302121905161d0a020a090801020d0c2003120705040504092a 69
    0x2c3c0540101d0b407030910304040030a074030b1980c2224040d95031004200490255405070340350700302a1400a0075810b0521500b000111840780c03c61900c1c003140f0010f0944034800f08081d000d80700e20240340701134882103a58000a40202e0001502e101c000704055070203404a0700421440605010000452020078010641618016140c1440503400c04030b5034802003d60307028068008040c8907824400c1122841264050b070041d501528440c00d6180001d401e4a07104804401003100d54801c10080c2038a1510840302a0f81c11a00c51030203140c0241250700d008403d8003104040c04020700110100709000a0081450b140c0c0804a403d15a64014001d020f02610801d01c2801c0e4400000072a00c4030294000d0030030203140d0130443c1c5102d46500210f400c90b0000240310702038566800a451403030740c020300b4210400356000010350340a001e80b2031281e10f134007564259100b003041e140e000c079840d58094801c0c1d41c040e00c1c0c0038200300480c20003400d140001c18000b085a540041c02125983d9001c0460800c0c4d070251407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 135421798 1250 135420548 135420553
    0x905090421050f07080406230409091a010b030702060f07020d050f07061a0a1208181503090a1e02030a02010e040f09050609060601080f04020409080c101517 69
    0x84603006541c24040116144204482005020341d10000d14024188550250790015126402c01d4000303800405c1c108104c4415410f502c0004041e2440b07481200c06981c2c02c000081030b241424605403606100c2d004212001401520002c11041203c401541c41981c1e07907400c585880d111103820001c001c03c15104100103804c8030070346203080c2d0700880040003071a0007500d03410314143d1142c40e4001100d082941201c40110b80710580b251510700180b42d500a4004403041c0101440c0c10f0750354100344e00c1914a00b07464802e001a010035a031313849124880800c00002d050075902c1c07810030f40c0903898411000c0300300c9203c0441d2111031204500c0c0707840e480e021540076006010900d010340040d04c40040b01c034085a8000e8860304542489000c50168840725403003030b402031015041100600c0e09180300101254108000300c070400c00c4a5029209098020390182c0d0001102c0c0e41c0350918441c2c41c0700b40c418401306841001400410004180d1040041c4c25001c9001214952600590000e501e4200018075442e07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 135423048 1250 135421798 135421823
    0x40302070303140408030d0507090b0c150a0204170102070c06030b0102030d09140d02010b090f04030c0f02030c0d0809030c0a1203050c0705030a08040f120209040f02130f060609050904 81
    0x3c0c0540020b40d000030f40346020f0b5042076543e802c11440d551120015041094449040c4101c494016038094003030f2a400d003200307040c4030ba02d07050030383d030b0300e006459031203030f007003884012030706011040c0c0c12200030f450040b4204200d201c4844e1418080c3d4002e0344203c81000700c0000010300f0340c0c403d100b05005010140d0145143c1307000c60321078501070080030105541c4c00c80000307445401c820041021000c0074104d900049030303280c0001c0400183c01700041501080c4d9040908100c002980104400d203020303403200b058018850340703001103407400e001c801d48103401456141c400000d000c03110001e000580c1c070403000c885004507407109000240e420741c46111900e03018402d0b40e20000b40108040d004000c07442080b60801c03a40c9000091038003036a1842917035601c000080910011942505a0010780094040a2100d081d194007040c00070340c0003080506a000076045190031540c42c80e114004a1030240814401401c007004000010030561040354081401d410000405003040812244195000100b890300d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 135424298 1250 135423048 135423053
    0x506090f01121b180509040f0c030b071101180201140702011b06150f0f0605071104050c03010f080f060a0b0109030c1d01080c09070509150301090507030c080403020703 74
    0x100c400d124506010030601001e403910503520512409220601002142428000c2c000d003c00c1e08510a0074840041d10500340203617210706c00c0040d0000d0b48800002500540b50031700580381d40c0c440d000101a054041e040c0044071b90301039021141520348100070000c92581059004015a006100a02180d46049002c042d1040342c0090030a4a006052019074444560050411180c2c1c0c00c4044514a070b07031740445034140308c44c01c0000010300045e2000c185070301d09240082d1100061072140d10100880010050b0400545071400c001200300544140304c13a0030200c0884296400900441102c481d00c00790018244000140d5081c084030914003829040e200ca0a120380070702145980e06040c0011004000001403811906900405110030707102a018900c03401c071040341e03a060340808415070050f2880040d82c0d40f0a68980c1c0c210340700342007090791000100085001c5c01c0e92003d180d08400c03000b1000003101e000c1c80d00400d00c9080c4660b000c000901c910035040c2c0f014542074801400681c4050703000e000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 135425548 1250 135424298 135424309
    0x30f020a0506010b0f0c061e0f040314030a020417100506031504020907020f10090b06060702011d0f1903060b1206040303020d020d050109090302060f01061d0f04060f0f0906050609 79
    0x1c180f085c25503d00507a464207079250101c00d071282d0794801d102540c001c40040d400c14106800100c400e508030b0682c102a1002003450020300c12400708068000b02141580c5c580e42d0450b0010000151601d825900b080d08540d143c1a00042c07a000c000d05240c0011703d203160106074102c3c2c2c003c1c00150207860b80c032a50284911604024070070825481000c04115007074804000c0c205042542c41c00228804c0c00360724050115540c041c000c0d60082509114440050f0780081c850748969400c0f1010b41c10980c00b0754000745544071140c032070b9600b0a07050003403c4031800d014070f15082038a0140c0300a02c070560814080c422030a492190080032900850045030009100b90010005205589800360400c0c0300180224102c55080c0e1144181ca65545540303001c040e010b1200c3c96000c00751420080c03880d0301d82a0040c0030041c2a070003a4103032a8840070411142d40e034020552101c8540504200f18080d100c41e0514110030460144d01c07000103000300001000509030040100f5282d0240c02542001541002e008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 135426798 1250 135425548 135425557
    0x60f030e01060e100807050303040b0a0e2103071103120405120109020603010909120305360f01060e0a0b030721061401090c0207030c06051e0412030f020a0506010b 72
    0x20075520746100040318032802107402c0c000c43d2003540741c2031220320741540c03645817072020742c405c9001e60001d000410610260700c0940300442d05500708020503492180000e012840a0340e0285003078000c07425100c000d194000050718000d03101e003c00801c8848810105540ca40309208a8150b1100412083c171003401c1103000d2408000b0340800101e6140b2060f800101c0542090f04864000c070350314a1000c01b8012043d0b140f019400c0300781010040d50a040e81203030084035030030170034944245c682d614010043c110003a4502500e0a50025210101d918608407400780c0b64a1088000444400000c202e10703011a1180d044d001100a004280071480c00d090100905506110b15210309000500c41d40801d0160003105182c0d060003890050a41c100036003401140c4e16500d5000855002c43c03410700000314250811420385500342401d80d00c815000c3d04110703148400d02071041005401003000074080a029150700100c034400c0e15080b02040d1000d0040365521641d0001034a950312050040010311191030060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 135428048 1250 135426798 135426821
    0x2010c05070e040503090f0117011403210d111303150605030a030309030207120b040602090d0210180b0309030d11220e0105040908030408030a0b0a081c0504060f03 72
    0x80e89440e940340307200700b21510110b9050390f01d074000084a9000d03241c030700e0000348140403d0a03c0c0304005c003041c40204100505000718409280c40c0004405076503810040c4440c03011045c400c01103482001c40302c410705608081c40600c81981042051f945440c1d125064034400c03074081c0d1079042402d00d1034881c281c028203042d561802e0346642d5100070619482c02c0c08200302041c0651000b00700340c4880d00d402071504105038084c6500c103100d0080c090000380ea12111075002500048056224580d00c0c000035858401540f00941c40400910005101508812101c0d02412a03509017868265169490011440120f401402c0d5400400014886000da64010382c40303002c205084906007241000014861100d408201d0501070080030100807001c24240a00c0c05404261030501000e003042c1d0300d165090002400003465648003200040c580c0100d640810b08001d0010110051742e591815150303100c074241c10300344c146901070408044180b8041c20413141150340751398842e00b02c5140120300710018100705051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 135429298 1250 135428048 135428053
    0x1020d030203060f06030c07110108070c08250f0605011208070209190c2003040e2205070e04030f020609070b0d0f020d020c100606020c010e040e0f061006090b0702010c05 75
    0x3003184c103445036406940f09080c0704900790f40c0c650072030910036980c0c01c1c00f10300f440c10041c0300707002c106c00035030b00c0041d50310b030b099000b1402c3d5141c50300301038540d4909000d82c501100380322002c2c07100c1003400341c007038140501140203039030404c0ba917600d0f1005003240f11440100548039910401400e001400c2034500300f03510900300c0c2c80001c2c0703400102005e08240c070040e01c2c000c0c00246d51103000e60795464038248542c10704e64001c40214a03203442d1070300c00d440d40f078001001e11404000e901070b07402d080003150300c0010325990300006940c0050744a401441d20041c042d501a00010041d8101b80401030000034154001c400700d03401444003920f0a0403200c09944540c440c0b9040e103840701c259151000c0350b070000d0022406660300150720341c200c4100e03080c034050311030075801105818010100030854010500d00050303007082ca0030000003001031012402400c01c1d01c240440503c0342e41cbc0080300b10340000c11000e00034040031940b1101e06503150011a000500c5005010500804002c1000107600071508000603038400d006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 135430548 1250 135429298 135429319
    0xf09010e060901020d06050105070c140102030d0f02030717060901090f0b1c0b07140a1b0b09010903030b032107030207080d09090c031802040f0b03030a0c02030c010e01020d03020306 80
    0xc6091060540c0d01d09096074000c20000744c0705096026003000790100303103010303414002540c0b10307003610710007a103e40b4010a008981c1810750ba4820300c1114400040082c0c00d000b4007040380c0c1c41400a6104030f4406000851041003200c188613800da055000c0c2c5070040965009074208080b000080c100e02c0b143d00f0f0559a210142180c50710707000400d80032004809240eaa5403881800d15100f0b0003c003e211004200c00008030355034010303500b400c0c1d803a02e04151030301c180c45107036904424142c0f1040c04000341c11095040c00304001101c054021051040c4644e4007880075100b584c040c540d07180b040d00740b40d80900303040c0c0f5102800302c0300c400058112031303009104440005986410803030030042b0030741c415800035101c914140249511401000788124041c0345c20000741c41030701caa000704504c40c1503009100d2a2108040107054507660043d22030441c2c02800d032035032481d803910060f0949c0340c1034030700b01d009000310702d102407596014004412903d001a0068040d442c2c210038204d00940c03000309215131000030b202 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 135431654 1106 135430548 135430571
    0x102070e0405031c020306040b121504020a1706220201090501050a1103030a0e07050405150d060603060c030c110606060a03020a0306050d080909010803070201080f0901 74
    0x2515000103031160300e0124154410341340341e0320881c1d03810111000c80059590096000c1c0310116030810610809400b40029900100a00d4900743c003d80c542800151008032000d52040c80103006242513525004094203c0722400c0e0100001d03448141080030f403008180490100804540b00748900824070342c0000e0040446009281c1001000700b0141c080302c1c0640c9050043c0c281c040305480e204d10348210a800100701c0380da6580d055100b60400011982454880d0718041e4042c01d940341d00d12900001841034030385006204136080e07640c850001003c03130014442c950030441e03950b9000c1907401c45c0110003000742c1c082400e0703d07143c0c2e0440c0092102c1c542d901070854020901900b009178582843d0201a401002241d11007600701d004c4c11541030802c80500c1c010024030b8000c841d08003103a41c07150b40e03003983c81c060203900a011503d0320012681c03000087c084583d101c40b641e800410f200c6a0003 = true := by decide +kernel

theorem cover : BRFrame.Cov 135251798 135431654 := by
  have h0 := BRFrame.cov_init 135251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 135251798 ≤ n) (h2 : n < 135431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
