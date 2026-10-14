-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3610
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:10:19.937493+00:00
-- url     : https://prove2.me/submissions/35b23702-8e46-49af-ad44-b6fa6ef6d11f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 649100719 ≤ n < 649280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 649101969 1250 649100719 649100737
    0x22080114061806060d09030c06141e070207050a08030c0607091203050d14091e0a03050405012010090c050a0302010503070c06060509010b040305012a050903010603020312030f010b 79
    0x2d10401c050990001d0204000d19040d403002082217294451300c103900ca4002c0a0b1701030760f41d86c10001903d14004040b42d621040407020840100f04000194044441c0f4442404408030341c040715494444090741b61040c41c1d00619805600d444c004907144000101600001e0042001c0b40d8594654a00070f46d8a016075000e48040c1e401c0742218200407038014402002c0c00c0079402000100e548400c600324059080940d891101508103400408645240c0d902e640c4060020300c0291240310540d5502906610452041c03a045c49111f9680c03c801d00b0f120442e007140d991710320341503914440380e802e5018010f124482085400da0312956000c921404c1c18078100c410340340d068455620356180d40341c0a50b049401400111002a103507640854140c40d100901c031b00078079200c800d2a80b07071410341c9003240c21740d100c0c4034440009124040c0700c6500d2840000d03040c0240072890a01558440300381c804203000d0111500080e405118150800030004503120013548503d0a0f20303005100c0303036220010407985102c0e074950 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 649103219 1250 649101969 649101979
    0xa050a060506091005040e1503070602010b0901050d050a0b0103081909080601210f03030b090601050c06070f0309051510060207080a030513150324030c17032208011406 74
    0x10010144c01e08140044154081d03082c02410540d4440702e0031900c4004a404205101d00c100d41303010181001c206c42805010b07580000e111071413503000828510740051050912078850320030301d0802d000040c0314004000350000303034000080da102c0c2084c5c640d6a00070014102920140c0d140a000039110b090b0302410345001c10058030160346000e140300c4000b0010484008501503c0390070500245d01480c902a01074444d85001c5803880c0c400c4200034006a000700104d0502204000741d103085040030a00c682d03c841c076401c004c5c5071300125040840040c450128018468030444001100682c21400414810a20411400c20243d00c941003281c079210b031071051b00c07150750002c2102800640148007a11350010000c0e84000415560364040600141c1400058082955511081f4204159031100c11405003030101d00c1c2c0c00c036855a0341e0030303065140500c61620985449031402007454ac1c103108660000748a01480390140760841d1484040319031a00c20101150300c1e24081a03100424021118400c00d00206 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 649104469 1250 649103219 649103227
    0xc080a11161a09091501050c030c070806010608040b0610110a030c0b0108160905040f08160213050603101a1011011a09060103090314031005130603050a0210020a05150a050a060506 79
    0x3001113044c1c490400641445008d0110040d041c2080016001c4400f0345002040a149050701c0701e4240071068000a0030020048204008600c12900d820b80000381500c10014404841e5011940085104e0f034941e454042c0030340c500117040d400072806400d54040c0e0003800301640d94045081d0740c0c403408000d4101c50140700340d0400040c800c9034001c6a00c80d00030400034a4004032a0f0711b440b41580141d60350714400c1e00100c641000e504010300c0408000d019507008105a081c42c00001e659007540141c000d0070580c841c031107901ca18022130703802c01c00450003030b00b24107031054641070203070180c42c0583c0e86543d03070341c80c04406c09108a2042e41180c651a400740442501e0385a000044020b08a507000c10f805100b03549200710800320b43d40c001948076540c20000440424280304c10409583c0350050009c501c2c501749001400442c8001c0746042d603542e411a40705110300940b48080c1e05044c441c9101800034041c0c8003104d000b583c030001e80b4134810011520104020382e916000401210034a000350b0341c000000344 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 649105719 1250 649104469 649104481
    0x910050904051f020c01240b09060d0c091a03010e1b0c070906080114010302060306041509020301030506040606060f0c0311070b030408130f060c080a11161a0909 71
    0xe45440e4000e40a0401d50b0920400450304810a100400030304a10325030000e00700e13944175420321072030843c510f040b034180030b014621300914061251540209620000c0024100c020769449408891914600440500042081c02c0c8090030000311807249031032080310486c0742c2805034080001c5038141d40c0c0c4000b280944e625402200c82e400d8425003250a003400c000c01400c01039000c1000040003c285a15000c038409041881480c25074281c01c031811442000c10005000503a18481640e92004007564006440506032055032144070b03003a8000c884961001001006000002c201c1c248628050b1105100040d981c8500319001901130309202c0c00074581c10f8100000034803541190310380d494584122200d09440d01c2a402180c1d006a4044809403400182c0900745803c20306220002c0c00c0b1340742e0043c00b40f8074028000d810b0345031061005004903000141820b605010f0000c140140c080b50701103500e25602c0080350081141d0720700070005420300441c2c8010b8804000300440b00740b004040c1041c0c181e51141 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 649106969 1250 649105719 649105729
    0x7080a05210a0606020d050406021005040f0210090515030405100b010201020d0e0307120801060f030c022805060603030c0307150e150103061a0d020d0203010609022106091005 77
    0x4440c401c901180c19444510060001820050003014210000210103140160103440c1604081c4110280503007844100200e0341c0100d12144940c00804001c01c595545142401010341480300c0254450034005044a2560f4015800c2064650a9480c00711f001d041503c90301c050b0200f1507000700145d001d0070010030003150782d4000c5040c8980600025060010840294056640c0c2141c162210751001c0307450018001180100501075245080c0582c0c0713541040390091a00030310f0340307000c000c1c940c96800ad4081c49208028000317200b541004002c0d13410b0495842101d540c032070b15106442c01d01c07480001c0b175500d24020088070070000701d40c4011403402c07600381d42e01550865100c84212107180d645c141c030641d00d0801d001e4100480c4041400d10800d41c11481e20344100c401e1000ba5644a1080200c240901d4542031281c00ca42e40d0100c410411100d035910010707016244980000041500201e240805001010b0701051100b1044507031071190398900b8107102000004403410407910b2102c8004001a0420f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 649108219 1250 649106969 649106977
    0xf020d0306141c0b13050105060906011403070504150f0221390d080a11161e050c010908060c030606070f0b100323060c2d180607080a05 60
    0x588100075a4500544460903140d50480341c0b01150000d40c1071705000c0107070a2150780da11200c211001d40301801e002000810700c28940408004511000001c50f00450041f02070f20001d01491000e404c0d4501c40e0003005040c110103039103a00c00341c401d50b04800c60034186000300c100710800741c000003030400c65501c4e450681384a422000d084901008289850f690720054070581c90b00507408000d055080c24080004c0c01104020240d201c8245441d089042d032407a00b03021100c00c0400b1181d600319545d85c6040480315540b01c0d00f5540d00702d03a0201066000c02c10086402c043d211400d80321041c880d0741d10b10300c054071748404440c41ea003450000c00004120f482c004020304a51401000f102d40720000650701c070801118155903040114240640410800c000410580305075810000c1c002c07161307558032014607070320342000d001018110004220310300d100382c2c0b00052100620382d8028024481e04000c49903651a8070004218041c1d07004524a0304441c00e03c41c00b140c01040d03110013050704d0251900c408440c2900 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 649109469 1250 649108219 649108249
    0x50a05062b0e0304080a0b0627041109040308011a0915070f0507030b0a060b0c0613020f031207060b0609010507030302030a090b01030b0601080603011503060513050d0f020d030614 79
    0x350301c101c01e4048102c01c0020784003518a1200a1401900c141015404050000e00e018800c041c3d605414564114a02d0320391800710b5141a00394140e22146031040325075088902e4560400c0701c1108010a00d81c0c8044403078103c4204801c480711141c5120454541c5128403088103410420030803154614900b10001041000d002e8442243d0482c116521f4609114880d801566120b400005010006125120302c00060000c4142c0c5440c00091840c1a41c840900400c405190b8400a20040c155116050b50568000c0c0040035140320115404040d0320039002000d0a6820b141707407003608049401d00c0022a840000140c40e04d600340030b81540c04038080d500003000503601903210440d050014110000c003a020b941314000302e101520302103000422981004060511070b80c1414040c00d4490707082084d00c4180d9401c00004aa2543d41000c01603003519140c900900d18414442c1c01d5502d50751200041e000d10780c080c0d0075103040629102086017519911f010300104100d1000422950b407410484000d1150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 649110719 1250 649109469 649109471
    0x1009080a0b0c0c0111040906050103021201090e10021c0506090c030412020705030a120e0a0b16170a03140f060315130c030b090106050d0b1602190309050a05062b 71
    0x74583e0210326080d51100d400d000901840031900b407290341c0441c0580c2c4051f1000b8601107003492004901c5041c1d4210601ca0305040990310401841504410f025403800d0740c145500075541d489410083c1051812264400941c50f0724000205200e890600c4031039024124528000b800c6403981e40302d18000094442404080d841042400646510180f0500207442c0c024402d03600c2084079400098544e14030364158902c600d0148606210445020301581c40b45020310300c4102406945180c03ca030485901d42e8081d80c5007801041d801032069040d00000e00d1007034074100e40398407a101c035a40b10100810070748915078160082e141100c1d1407010802065885165968116010241da0715055260700c6035030030541302c0404800421456410901985004100c2500c1901d4012400d03200c030404110047c04824908040d40d82030124140300b0440e2019628825500c081ca0414070f00d009010001d8034440c4502941a00600240e01d1406000382d0303a18648500740005507107241826802000802480c0e03144003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 649111969 1250 649110719 649110727
    0x10b100305060102210714210f0d060e0604111e030403031113080105090307031e020132060105070503090906120a05160b0405010f0503070c060e03091009080a0b0c 72
    0xb000070414990860f0303400840320350740c43c6e1300340c05c0070302c2d0101030100b4808241e170202032090900483d011042d0000c68404464545803c00e541502895101306144d52240c0e038100000030403c1d00107810190300802c2c08507010010440c051404004501400400c2c00b056046040312692041c4544003c682c0180301e80390000d242035206401070105d4103d41505581102010001d10055209108142e0092013450055041038515074005014103000e07011141a0000d41c85110040c3d4000d400a134050710696501aa940e03078140d01c05d400e07a80140c1690f40f0440004d2003c10101d50003602151002d9030814041d6140420880134024018409040d968000b66950600769900c08148208a9020701c51400b8204150003100c10311182030041c2c03c1506010010081042542c0e000404000300005504240361070340d5032002d09461408000002801d2142062400400c2178004001881d0880c1c00300c0341e2a0b0b603000818021203240301140103480c240e0344000142c0003c60142c002c5164051400c000310303031074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 649113219 1250 649111969 649111993
    0xf07020a0f06030207030801080c1011010e010e370b04020114031603140f04031103131206050f04050c06090d0210030e0d021506010509032a0a08010b100305060102 72
    0x918260b00c40000039a010032007404144d488881c2a0040c18060000c120081c0e01500003020350340029207800502400003000d000d00b020a400c10300c0c2d1681808000c221100221541d01d8840c81000a805040417a43d10340c41212601c00c4080101d0301948580d40548100c41d40d1170032111100908141c0c10300c0341074580300d1113040b1031070025403041c212400c041c621112840009001d981a018607807182448217420020441551690541c0c402d0300b52505580f04804c40b000359007144030b112803040d201d440001c0d01084824460a000010354483c0e00100220342e90b00d828540096000d440090464101c042c2c81010307032400c1d401400c00e40d60f006003c101007070349070340c000f031543c0c401e010304a070110303447d0310800d512410240f0124400e0242c0e400906040c0c1ca4a502c00d03072000f08020261418401d0116404485413820407280241d420002071800600c4009001c21424010404a40f407180c01000004511b400040c001c40080442c040e0180300b0412a00300c050300640002001c690441c4035040b99610 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 649114469 1250 649113219 649113239
    0x90c3503190512270a0309172803090e04060501060e030606030d0e01020313260a05030a03050403051902010e010501090e0604020d140d0c150204060c15061502061602120f07020a 78
    0x201c5d05100307031601e0220038a005441291010311030300b02d20035500f02060b002d084158840914441d1040c0d0043c030883c140ea03603d4181c0b0b50f4882038204c211103d011008000801410b81d01080c140c0c1c000d40c49080340d52921400305035441c10211203058043d00214800e04500340654820f417440d0805005483c2401040081d00301c1c031003580d80c88000d074044220f046400004080e03100b1402c18404038041c040810031502d40319680c0c81612615010944d0f60f4000409151086040d80c81c0e42000f92141c010320350305071000a018005580c4254400d500c0c1c4000080d0f41842da1240c1da502d1700c180c40c054910384e651a000c0141601210341c054407080c101c03140c124202182881114050482d5843c1c00300c14100f641441203d007141d02c01c60050032841000140007080d00001e4017400c0c164026080c00050f6816407400c0007900b4103903c5801c004200000c0040659004a20345104460403030300e036903020440207000c0b80e44100f00c81c00d00d01e81c0441003040c00c05d80c92511000f4909540050001d4501300c0c2e440e1300b010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 649115719 1250 649114469 649114483
    0x90d030302091c03050414180f040308071e14090612160e1c1a09150c030c0f0a0c0b01120b0901090c350319051227 51
    0x5000030790018020701075141c152852441d84011003944101c01e0001d82c0d02074481c1c81107001e0801d1000c4903450b18006030742c400340d0706d400d4410b50001540c0300c2d0401c4100d5140001c020340c3c040b404103000c1000921001d02c640103540d00448480c10103082100351410a944131001e001c04086102000c00105205488060007403e0401c0048200a070034603100524174102a00e5455031010800c81111701480d031303502d0b240c200000020b00903500c45540b155142500d0082d504484440002c40d006080004018010480c0100c4103207200c41d804039540c3c2c01400c0708092000f1156000c1114007808500c10f000310340f0300980340444107824160411580c58a0b90744c6030180990220015640401c2d0300d100b0070421107140c6030403e0200c0024801062281c0d00c03010007140d00c2c003c019142d034a503008002c440c003025450070f10000070a540000301400c040d080d1170300d91740b1442c000d0589a090304131040340d040c03081c1d04891809450141030361081d150060701c0043d00c4c1d03106000302440001c9009944629805008072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 649116969 1250 649115719 649115723
    0x20130b0d32060c04060503070320090102011109061204021206150a061d09130c0311011803110105090604420206040825151b020c040e0102090d 63
    0xc0c524100101403159503246500c069550b4000074180052031054000341d5041d03035010b08101c1d4681da1008004c0f4014201980300c41c035440c062107c62503042c100c000003056641c0082c2c0c020b200807440151004410712481c40c0030b40d045401000010320816020084503000b52008045808000341c03406c4851070b1402c1969411380d6140200c214000c0340c40e0140071078005003250b051405a007008002c5000035203000451041c0121004400210100030400c000d511140d804620180d4143e100e08041a500203684407050102301c1c0a1b0b08843c007100160110343c11203601c6a502c61180700910011a00350700300c07100301908000d00340710105204501429061000c0c19294100f500800c030f44584c2c0d200c003003103030f6101141e05004000b400d59040e800f1a503503910907044803150703541e80044c5c694000c4881e083c510b510f202e840c581c0040c5080002c50591008490b454080510403010341c070f1070500300c44100c0e41030700015034400c070084052414035410015559429100040c2012045408540c10001c20882 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 649118219 1250 649116969 649117013
    0x803040e04060c1b031d0901180c090f081c08240d0605010e040b01060807050414120303010e1005040218011815020d020f010203060303071b0503071220130b0d 70
    0x8411141010501b00c0070300c001d0200d50912455140c242031094114252180714026503e4881070080140a03031724400080c110003040c401e038a41e88089582e1104841b01d41c1c0034142904484c241d600c188070b460510300880c59402c2c3d01d4a076005441d0303055907043c2e030b5011403504081c48098034000300318548202030003400300c07000e2401d50f0301c2c180c0341003950444160000b005002159042c40710040e8003e0645042c1d40041610484804d4000005468611151220300031440b00100200b14001c0b0920141d010303458403686241d813140c46204100582c042c902c2034410101d01490769510340e61044810a02c04210310162000c01e64980000c0c1c55540780c020f44190140c2d126240503101e07143d040000c007032010010300c000c60844c149070002075101d100c2c0040c00781c800e0550f081d0201e075200240c101d5000030f040090444407002c0e50b410040c41c142c0012070051300d582840e0240c030b03403001d0404045c075101d00c0342c000d20181c0d0034180d0040040c010401803c101c1d4000304803000c07420016511601d2419050a00c0c48 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 649119469 1250 649118219 649118237
    0x1180306110901020607020a030f0e03030405040e1c0f021f0f050702010203091501050a060c08040f080c100305060102060606180621011a0405012607180803040e04060c1b03 76
    0xb0002e850104c01800000840d80040e690f08042a481041010340c480c0c10303d0318001440740c090003e071540c043d40d003140c3d030300915100020040009c000b903240c0b207100d612582180518451507003511100c0e10580ca02c0c01503009a104a04410b2032031440c070f803d6548224002508079512801c1e81c003151411a0040c2c0940c0d40002400302c4500c1c10482a801d8a42008a50100358141404074105c01c90780e104072000e01400340c0740b12040020304011f5070060b105102003240c085603201d4100d9036402c0800f1035a8068903003027010114861090007861310944c0180c004150b12b8440c4024040103a02001810140518203070004e4210368644000302082290300032401c0c0e074103140940c60711809c5810f034050558801071400d42d2004aa26000fa282225000d0070f200b40d910300264124a103003c131550840500c07400250801032000e401c10308442d15500740503440f20a03651100708056aa20450058044644040c03001400044054004090010488c6081c0303082c1884134016a200d924001001c0b40400c1c0c0800d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 649120719 1250 649119469 649119487
    0x6020c010f1508070905250f1707050319060803210f100b030c120c07170913020903031603090810090305030a0f200403140102070305090118030611 65
    0x405401400c56481c0e642c2401d0920f0880029980c2e2003600c0344c00c01c2507803190001120030446403002a02d000f2a003035010103800b14003100800c80b0411181c0f90003ca60010680d82210184264503442004207483d000d02e1900c402000000711a407280c0d0499000b41c451901080d00b82050001c0c01c1e0500030141c00742c60209410042c0d050980000305031800025484003040002041354024200b10362903041429a03c0d200c0c107842a0052062300350013140c070898001800051203c1c0c0b4010320000307020f495800080e84118402c50240d110740d104c40e5030302c00c2c855800382041407550381c010050b40354001e0440740760880c1d008100042078840c6800380e0114980d02403c2000e250140011440c0801e89038040104c000d455802900c3e6020180215000650f2a40a6075402c141907102502d402280181002408459264503070250b0042c00708030f50305001400c401c80c0d1100140242ca03e92503042d2621401c11034040011140445400b1141c0fa40e00c440c2000000810400d20417070661106400c080d42e9a04010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 649121969 1250 649120719 649120721
    0xf010e31170d0b04090f0f030509060a080117070e400203070801060510050313020a080d030f05010509010303032c0a030e100c110102010209060309060403090503120d1806020c010f 79
    0xf80c081c0901540c148000440010f40c5400700009060744012107501064860404985500481c0e107010b4100d80300082c286156900110114100ca41d01c2254900003255101c40c1a15290684901c104840200b80031404000d5036001000c01641c3c0491600310f9046400b40880c0710b403100007040344480c0c415000311015400c0034400080038141d880e00a00400e440d10b000b217013485080e808c24a08120002c004103d1500820120010854000f01500da0352501c07100f015480d6414120f2a0340030134900f8a00344c03031a001d81e00034941260030040c280c03080340e841c0d40ca0a4002e0041d085001e030000c0c120900b98164031500c4c110329407000040d80c000f000040110310340a011070780c06081c0310744101a80c04d4941c14090b4480145072442c0d81c4866200c0414000000503800381c0104030000354007400100070000c08204c000790041c03042d8001e585500e03d0590b268141074441c418449040c240c00010042c0c101062101d400c24810640f20f101541101000754480c0c404a801c803000d00119651240410898403500b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 649123219 1250 649121969 649121981
    0x140a0506041e050403180b09041107020409230706080a0905030702270a18062a110606010306051c050a1202010f0b1e010c08040506120f010e31170d 65
    0x7074072020f01b13242800c1a600710344900a80c8284e070700c655110405900f03ca00030000f550320482c1c0c094020300c61036106203020b04400c1c2021184007505c00c103001c440c220000c00000c407841100c140d82ca0f04415900c03510002009020140416205840104003801c01a211842421154010b8940d00003061800c90300011400e8030150031150322900b0000c0500c0c80c0310281c040000900d038070210000e812002c0c200503940c5100e41d80c10803544000c0b0140001c0209811480b8091650308071402d6030002d07580d440c010360844030315004568001ca031410400000030031178448911172a02400c101d07000c0038070741e036500c0080c0c0c0d03500142030740140d464003a8101e890a00c0d0244104980c0b080b98503000c6110103034078142034840500d9009040002a04544080c008241e080760080d04000d41010b645100c100f0090550b081c080c2e4803c1d000f41c18120000845004901307035a40243c0d4800800402c3e40c0b06810448500c00c40f00e528070f60031649000e610000204008002c0346074481c400021503c41000c80d40301411159 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 649124469 1250 649123219 649123247
    0x307050a05010b0105091e0307150509011e1b1a0106030e1b012f03031617070c0807020414090714030613230a0c030204050a140a0506041e050403 64
    0x1c5d0034812204156510f01d44009084040c0c80c40321459134101000170700d0120755511100700700104292180368594040001c01401200383c84000b058204041507134845aa120100307800151013001c40c20820071241400c03042140102400c646140400700c88002c24002a0300c000046652140980310203001403024030342501803945403420100300c001c0041e00481e014483c2e144400c140d203003a40d00300e03c070b0841d0030007540032450700711303502c0f0302d0185040070071610030780d00c081c001ca4414001002250342d2030380388a10440c450740d8ac00c0b01d044010f07652051030b40c209100c101d82c4561500803014400111480c124032801c1c0c013100818211f440c000860f20b102451403a100d00076004541009150030904009001050b0300c03103000208544071030440103413004402c0058080c0e014150f20482800394110280d0306603802160200003940703411426a049421180001d098281440c0000384004507590010b03500c004040d0010075a480c0740075808030f0711420004c000203182d0303864041c082490391010040c04014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 649125719 1250 649124469 649124477
    0x91b0e060a0b0a02070501110a0c0314070e010f050609010306050310050117010b0105160c0f060203070b07081306051017060103060c0825020a080f030a0f0b060a030b0409050307050a05010b01 84
    0x1143c1d0b424002d41758031050048a05201c6031401c000c050800400901c1b800701d4204000c4005261030b480d11310065450282a6400c0c1c0c801e4a6010800c031a08480c164101c0309600e0500b41010318283c2400036642280800e903050550b1840e0010b82600c05006290803004d81030790018496040c01c100c030104c0d9000e000c081840742c1c503000182e185a42c2020071200c2d0207a040b19100b010031070a141400d20700070550005125015801400075010760000090244203200707aa0310200e503514804c1c100d03000c000450b1582080c16400003400045a4541d00098101c00c03150310300c1d8490340d01c603244800c010403a1058100964081c400420500c0501d210304040041c030380c54030f0303049801e0030500d40c0d4082c045008403d131800035884001ca26103000b0001304149640c008807054541f030b912002c40d400ea82007220350001060800c080041e04e60603d11a00141d204010b01c15800d140140008600401c65003140c6c9802c10382e64500c3c500414000c00c0039006c03136403140d0000c082041c80e619005007900c100c60710103810300c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 649126969 1250 649125719 649125727
    0x1505090f04024b0609120102040801020f1902010507080103030305090f0105130614040321021204060902190503030d0f09050a060b1813080904020706150f0608090d03091b0e060a0b 79
    0x113556440c21241c4a81c03084070320928000607040103e00a03c11039100c60595031002403071045650b03a10011380590010810300ea0218520484181d09031881198040c00103040d0000500c00640030b6030069070405107403c102d502c2948061004d0707084400c00c1d07480710101007038943c001c030170400d807401191800c45181382c08100303504041d80c025003c10211503003075602c0d075400f0307100c5100001650b040c0d0b10800845100c00411381010706100b001031180c51020fa008030140340d94070b82d2000718240078808440002e8003c6162040502e2506c0003060121181d20040ba01e4240010208000700070034021140078900000d4541c69141c200011b61900e1102e070500d40d440b202c100000c03180c480100c62000f5400440056661f1034640000e402442502c600074802e41ca80f01c504080701210ba9a408156001e6081031030342c41c0d0300e4000546100f0300840d481510356015150404d50305100c1d40040c0300081c407d03200342292540301d020f100c1550300182c02070004410440c0400815281140c0140024030380840c2071450 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 649128219 1250 649126969 649127119
    0x8070509040f020303121f051807110f101a090910020901170a050a0605010c08160f0c06050901090f0312030c0e0d060501091505090f0402 61
    0x184003001080500700071800c480100079074405100300ca41c64440c4840c11003031854112120154202080134182000c00041c1000c038560418243c980000703c90000c007403d143c0d4810308100c410700c0d010b10711011507000f07603010554008810469924094040b6402041444159808a00070002c140034180b0841c5001d003031112a0001043e0641c00342a800d4025079035014400041e60f400313018014001d08030031500c042000024075603002d940121f00045082c49081d0b074810044401075000a0b01400c1034508121b06a161310381440d04194103441a005980c1c000300e03a4448600d03240040e801040407800006842d00a903a01c0b02855018180781144181c05a00359203070895070307001c1c0380441350078155184802c1c00158001c00c0c21040002c001410710044042130f20b00079015050a104000c0840e00f040c0115031170010300c0802400b41c80b405481705285903a24a08034021000142060340c20956003061003d1320340d407142d00c100d20440000190814100030306424121880c0e40504140260740c43d0307110100b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 649129469 1250 649128219 649128229
    0x1e010608010e06091b182211040c05130506030a06030f0f0c0b211302060408030414040e0c09041e0309030b24060d0e01061512021602061c060b0c0106080705 69
    0x103d103200b9008200003a40ca10050788603844541c3c050030380e81c030300c418500f00800c11010000c48e07108100b601c0620042130b80b000165068001e50240d04806142e07000d05000c24100f080140d80d100244907004584103640340c440321030713554100009035a00c0d074840d80702c0c04c00d20000c05582c43c002d00d1860344492420307800c8040324032000e4090352104507074010440480c41d4000482c00c41105250014141a90359a642c145250f40b9442446151009848010244242e282c00e2042c19a01825540500011100a030400820100c0100708075500c071b5205441100010413684003107440c0e4881d4685858490445c189003400b50401003032101c1c0789002c0c02d910600c800c0101c1a28222640c2501d250b911000b04c907003094050104140303001c0b059032826400092800c00340c8030a240e0b102c3c4a498030f10546610541090582c0700e509090034101d003540c02450f0060801070b0041516500002c1c0300101002103040f048140e40c2240d111400009021035038900c001c400303104100041015000030540c1c00c7c64480421 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 649130719 1250 649129469 649129489
    0x301050f0f030f160819020f240408211305040e1e0102030601110312010e1003080d05090f010606080c0a0528120606021e010608010e06091b 62
    0x203004016001141c00c03161010031000c500000031400307030307510024403c0c1141500d0305240304541c014401d00081040c1c40f44030105c008041d58000d050a880080030b1010300800b4608a0520598540c0c0031600c1104020a80040c00182401f070000d004005d56103400c041c116000084c618040950802c201c0903c000000d1001c0100c0360240c4000c20090341301c41c449400d15a0440054a00c0c03a507240403c00502d00650095100305c0c02602d03800420000581c40030342c1e034001d695001c400a400c840060210414100039643c0c0004280d401e09001170722540c844429400002040f80529154020711440d01003c1c400b0b9000d01c03008a0081002c1890050010140030000d4040c0039030290000c0c9481c42584110103c83c0d1140c41900c4139041c1c5041400300c00d007450024010500010a060000c00c035041490040c40211100c40d4010103890022040312084000c403107407641145c0d0b61300c000003d80c50341c0030702070310210080704d0000d05098a403a600c1503040c0105104a4a4480c08040c580b03911075492841c22 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 649131969 1250 649130719 649130749
    0x2010314060105190905060f04090e03090904030e040615020309131a090a0b09041a010e101403070806091005010801020901081b04240f140a0c0302010b0d0b0417030105 74
    0x144075002944c20058542d84610741020744c00050003d480a007607180d82e80108222188050100105004056141e4a900403000000d0740510048007007004a8840d03c0c00816107000140001340c890b03540d00c902401e941900c03501c80d016800104144841c2e24240e003109603004c1070080144000101c00e0a501001041c3c42a814811070480d808507001545075070050040450140003408281054100711031106940c4603000e01521050001084228036203050b50300408610f00044602c9082c078100d41040d0440040854042c032480070001070413a81041003500a01c6040060164201e01c80301754815182c05070015803e0341c0c0100b0204500340d0340079458640c40680b40308665407401d684900740c2003c4c4540d62041035600750300e0300004403402e42100c041c09956a03584500d40390035443d640aa41c8912030540d03084a00c1002d1280300e15031401039003103001e2103200c0d00c00010b01100315000030318421643c10082d00e9180c40101000100301c01155080c408000c02448582503600d0314001495180d5002a4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 649133219 1250 649131969 649131997
    0xf07110d05090d0c0306020f030f010b07050715050702040603060b10020114010e18060a1a0f01080115090e180f1f0f06080a030f030f0c0c0f050f0a0f02010314060105 73
    0x3d400240840f4400385405540d001c0b034295695a842421440541c10a480c0c4400c540080000000d46e0030303100c81101d40896202c070152960728a82030042076041c0b00b1540032801e004041200400580c0c441c0700e5030b4017943c42460b0021329112984203100e14221b04017808800e681c5070410f6036962100c03108400d41140c800150f2000f40f030340c4666003111050006010b10900b403060310140700d0700c0f2a040d08020b10311a803113120f0b03500b4207001c10f081145408000c00d000b40401c0346100180005a02c83c2c0c0300d102c5900c080d00303042c00d10b1a50344072140100030044030700d5000386040340c1c007086900b1401d0010700980c0801400074012100381008480380081c0c00c0c02d100c4c000d9a0740e901e180d41c03401150340041000344410406daa840c4405c0d814090f00300d0314480e54010010340b0301240b207644580e240c03040003043d410070b54940c5001c40c1940d40d035608150034030b401500c061003100780149141c00100504007100c0c2c403401c2290101c000e0f51002406554110312251402c91202003000f55a99111b429110a0003a1440b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 649134469 1250 649133219 649133239
    0x270c0501141e1308032113060527010b09062b0303060302060d090c0e1501030b030307140d020d02060c030705210a02070c17030f03070212030f07110d0509 68
    0x2100507251003940c3c06660500c3e140c80c0000b071414004006842030079844024145550700c901503540400408440105881900240d40000308081d03a00055105040130384e074401a00c0941400a8945550007408040b69111424204681440d003103060b001202a602907220301c1c443e50040096140d05c044e00001d500e8035920140074180b0a40025000f5a0040c1c40356594170700741b0b081c80c400f4101144040d80c4440c06410006440b5245007a81840b034a80d5103140441d00f4200d0004501500345540201da0500c000c0c016100420701c9151003008004c8004007c2491008902d0043e0034040c00044071410741d0450000c0044a400140c22a9400040c230f10300259a5108659040d840304145c0c4000c80c1d40200d50010400c0051740c5500418266026149100c0e8807640c070407000ba603081c01c1400b0f40b95207800c00d201480074005120040c6420221074010388881c062843e8076008560000c032001580f020011040c42001c44d001407030150b100c01035801520842c2003416014140d07202d802e00c001d014002d001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 649135719 1250 649134469 649134517
    0x504020f09040b0f100f050f07150b031b010e0109170105071e0813020102010e121e0c101805190c2411010e070311090108190f0204270c050114 63
    0x4421604c2341030340300348441c0e02c03520f10341483c5090540c414550214545850481074140c68002400901c0310b04038030810b07454540c031500440d070804855000038140080100003054014490034400469801400001403d1030104001000c5a50102121401c07c48901d68800610350180704560b024030000c120805031100c904c0102d006011200303015206e4044c61802da80d001d1401c034001e014008618820244400c402150013459114040000c00b55a1012040c11040000c83e08000f0741b84460360900541d00c1e085450740c03070500c080d40402034200e98441404104010341000420060001c0003c04201203040994203002c83c0d1102030800140403032203240300500e20003500b207d00c100f00d056013074403440c5d60350303140002981518407189481810031100100f103006000850700c02802c50380001c0300007c01a5201c104090407480f0060b6007203a101d101541d4106d501100f00480400c1c41c4002407500c001a05141d0740f82d5074203410a03410040c001903804009403c54090786e00c400c2c07552010102d406884 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 649136969 1250 649135719 649135727
    0x705040b060f0706062d0905090f160905150d03080a1b0806090106110319030f1406030c030304180f090b010b0406030606091a03040c0504020f09040b0f100f 69
    0x45895414645001885000b0080190000402c489044c0d0440c5014500c40ca004455040802032454550300302c0a1b0800c0040300c02e400840c3c0001101d425110814460b0b100c05051000704982c0702d0621451641c100503180c49071240039848180b00301148035241429000429480a840700a01000489000f01d1a0f010a60b03010310580200c45144140070028084050109282112907034403400700130313000184407401980041c0d8a241c10002a5181404240c03810441038080440304007015980c0c4c41070810840140315008807000c000d1401115403030404105803410402000c000c0c026001404104640140755807040c50911040802203004890750700c0274401032040d010094610729209000081040210000300141e07051542e0a0104a8542c0801d4400301294481c001032000c0c0c60601000c0b410220010b1600709101d0000440d510340c0d58000074007a81c2240110030300c0034100140d070740c000b40b40c00d10030f01441715002e07500054000340c81000507100345880c03c4810144204240c45104440c81 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 649138219 1250 649136969 649136977
    0x70c03170403090b18030609010513020108041406010905012102011b0206070605011424040b030a0f0603080c0c01021204150c140703140a0c060e040b0604030b040516080705040b06 79
    0x81c1413186803540307000c528040848900852540c06402a20041541000117000300307842866640208500c556032a070044a00d80401001940c2c1100450340052101100f0300083e030003840c0700000400e0550514400300f012812281c880e0b800b07103c1d10f114080042c2d82003404c02014501c401d209091940c01130000c075007184981e44000704203038074180001c03802c920000e850800100003900d03600350130000024901c00d01903000801401004040c4010040600c02d1070043d94031414900011800c403080300300c036070280c44550304100c81d2180f001c03844842c40d100820006046c20001d20007000124182d010040c0035104c1d42c050b02c1190812004604000d901400103282c074550302103220204100c03c103d040e41c0303580c02030008450083d040706030b00c11010000150845489c3e0407903601003c5614140701a40d0720710415800c02c3c0c11907281d2001400031341d56000513100a6002d610405d40318038141c9005820103c25a00d9084401c15669042c803c1040c00a107680503260146e4000401a050000107003550003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 649139469 1250 649138219 649138229
    0x1051311040803120c1606150320150909060d0201020c0306330907030c110a0803190203091504020d06020c0a0309050603071b08070206130608070c0317040309 70
    0x1000140021104030000090401d228140301c00751007501d902c40b18150300d1051301084203880900001b030b9000f0401c00d50021014034621203904a2041e0303240d03180c00000c40c400040706e640c160480c14200300380c1420070343c074040c2552848089103442028000070300c90000c0035101a0003049032080d82000c59000b0000741203d908018116409460324070444105002002c0c4200f9800c00a038036042c80031440c40020b8500f041009005001e140e840e50f404400404c9088041c904005082003200c2205a0602801038028000c91100c1d5491401d00c0d0600d004030f0302c0c03410503c0082d104108000c0b20440106410103100c0c2851510fa40355200c03800000c2c0d01034001d0001415451000944880054000a44003100c5200f078a81214050707a0310100000b13404100c030f011011801040c40030b01d032660102030011103039101e00d10050814082d9000b02c1c00c180c0200d070b4981407000c2031036018000e1fa84c1044945038801c40d5864840c0110146590082510000c4c0d03c00072207402e0103c0205007003500400c107000c0544 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 649140719 1250 649139469 649139501
    0x1503080913110c0d050f12100b030705072a03080a09080111040e0a050f0c0a09081005250c120e0d1212020903070302060918040c0609050d0b010513 65
    0x441d0740041d03201c40d4040c2032042002d10031301d49240b000c58060801d0380e85051144545504110002c0040640710360001c080f0b40802550036000b242d110b81c0d80e005940180300f1070795070f2511210289404060446c5010160f07140e01c081c403910007082d030800d0a00d4419664840321064480e040c0b104143c411385d1160301b122102c0d50902c481c10507001c00150160044940560400c52152103c54541040b41e10a6501c88000050a00054071443d2154010000c80c2d140c1d00d0181246580d40c0d02090a08400c503012048158640045c001c212081e010740310fa0f6103840d0240310b00440e002001c060408240c41da00148079041060b41c010486008d548003203081d0b840906441c0c0e0a0009281070140160802000c0012420b80c4040120384c0c00c46200360b403855000075009000450450302000501e8000313940c99a4400c2602460958139404c0c0c501a0340103c2c070500d803a4114908010025180741c959801c03050069141105c0107000c103449002d0f541c110341040c1c03800c0804003003190b6107002400001c82074a03490 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 649141969 1250 649140719 649140731
    0x70812070216090e0c0f01022508070e15010c02120d09030624050f06161103060f150f0613060908060705040e04031b020a26011503080913 61
    0x1450300864010b01c410649000400a00d48a90300e600484a141101501c6948404c0b01000203003048001c02108450500490b003107409202c070210074105031510300c0040003140c010100008003042000c0b02c040e00d44074403003030320034034080c02d0a01001c0340841c440350400c00d00e94480f174295100c030342000f005081032a003621101d100360100600b01c40072a00c400c840240c070b001a41e041c01c900c0b075103070405100700c1c1040001035545030008000704018035145c15640305008000040892610707402c80700003540308065002108003d40d00f01814000020240c100441249007048401100b070f05240b40101000c88140201d4a240400b0401c10701440a200e031214008500104055400c41e06c910129400a002c5400c103507101141101d4500841c4284c031680b840180100d00020b0003186491049214589400c0ca00c002e03540000d09202c0455021002d81c0e1700f44648407510b441c1107c0a8034125199100922130055a50201030341c0307024520015102c102d001c245405c480d034550030650b4407600d10f00010f0000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 649143219 1250 649141969 649141981
    0x29100c0512031902070f03120b010f08090f0109030f09050307030f120903081303020909030f03180c13140a0b03030a030f02070615150206010315020f0702031f0f0501050a030305070812 81
    0x8400c40c6c04006401041d50040c4031540c0e1003881c09607100203601a95100c04402c09040d060340c9d1144050414031050148440d029880b41c0e09200c1c0d041002d0080d9104008580d549501030203142c0c4a070802402a004110180085038400200d00c440035440400540103c0d4152401c8a505e40c0781d80000700107100001c2c10003082d6241003c07c005490080712821a42d8480c0c0309005c0da40d104203417a0401c147d80a20004003441d5a1100c07203c1d03903c4028040d5808000d000c4001a440e81d85c4901d135a07140d5a803480d03411103031018a0b22169128604d602c0c01c10003440c503100080d55a0164100300f200b0180c82c1c114071801c0035880e806954005a024406018608018a08618903540b500466105914020210001510004c2c00038104c9801c15450b48900c2c2e18441188040d40c030614107044c00550801017040143c034200f0954900c40320100a000a00e204c5500034002c0c0d03007241388001081810000148070b01d0380c0740d082010880740d01d030501d19580d415603d8019518003a5101301d40981d403141003048a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 649144469 1250 649143219 649143233
    0x3020a08160c2003010f021c0b030a1a0a0515030a060b0a0e040c03111813020a0506030a0b030601090207050c0409140703030f0f17070e0429100c051203190207 70
    0x3100d143d00328024000760a900104004174004d002c2d07507001030003402041420324002d50744603000c00030010701a252140c4e12a1141480c4c40100c46c2d0340f4401d08100000c11002c100c20b131144541001c0408514400f4800071000a95249078802024106941e548110b114543c0d40342584002050f640d04040c0d440d103000e0812840c940e80c688401e842180c0d9a80180c0340c18500040e000003e0401c0d54108880e984803101158030782140b007942285c0041e014140810039580c1c0101541c4141c12003040420124a10402c3c141082010f9100d00365440c014481c42d40010070101f0540090801990001040503160170a88008141506034100e140a234020200900d603222403103400c1d608094a8107568101100002c6414000d0320b01101820404a00400c010510815403046207450090002c15111242c68200040c507038000180545110b000c01103039503d0400480c4680200d00c5814040c1c007001c01c58a41c0d0b52942040400d511141800000140c50920300c116045064403401c80110b44984003071030880 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 649145719 1250 649144469 649144523
    0xa061202010f023f0421171209070e07020a0311030409060e04050c01050f09040207140313030c0e0106020607050a1101060b030103111504090f06031e03080703020a08160c 75
    0x4130360801010708028100300a84121801c4820500c0c035802041840340358003407000e42d40300045031000c0900410181c1ca81c000c5020f050000000702c018107240c1841c58400307240101540c85400b0a1481034204500036801040d01640315400d41002941ea01d1424006d0341940701315001400d0251800c8070202e0080640180e480c0318030b1080c27040b00e541040302c0d401034a5502950030030716888181040701307807014180358000d0486e5510661b0140f5071041010b10850458104280b508898088210200203010f241c811500017000140700a001650420100a4a9003c010103130400d1120001d40c1e42207985c801c401c008620030303000008102040d114036100b0416030080c80192134094030480c02407464a03100300c256403450b0031a0001031425240ca00b4000140c407140f8090a03c140d9220b900002142004034a010a60700100d0f80c0f8002030603526000c2c01140003e401941010300c140070281030540c11105071600300c40340c1000b2a0742000c00745021190180a4100148100c9494002910031b9805403d20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 649146969 1250 649145719 649145803
    0xf0d060c08070201020310050409020616050309030706030b0603070c0f05070311040e010b130b0402070204050a020a03110c0718020705151005040212040609050a080c0d080a061202010f02 82
    0x20304458441c2c0ca412030903400b095868160040004034200400c0c6040e034080c003211403001d060035041c844107102072403807603000c10003d82d47d41d080010711a00303030300c2c0602c03140b405000141030070000f0803000c00120300c880c080140120709000c1c051001000740000f220f00d0a801c01d0713000c81110038503a120700e030071400249100385040c055410104401c114030410b005000d9080d201402c0c00300c89006050840d006800110f10064129030300700219800342c0c41d00d00031f003442207a0480c00507039a18200700004044880440700c2089030441130040c2110b0b0070340455007804458219800040414a055200b00280b04544005205110b400c4010705c004420401c8907205121588918402c03d50380d106100913031103600030800f803540d01c020004c1c1c0011030301d07842900103038043c904582c01e141041e80d844450703500002e0440b4442d481590000000e80d4030003815544503c1c80d00307050201524014031000c0d40b0200c908020b040c4144c003408881290710812080c00c0031000107041481042c04800c400c503817003100c1111 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 649148219 1250 649146969 649146977
    0x302060f04060201061502100506060913091a06090106270608100f080705120715051201050f09150420070c09060e0105060705030d1505040f06081b0f0d060c 69
    0x100007265040e11542081d50380c2c6c59009001014100000030340100b030024030455202805000c0285c0e242c9809100c3c2c4200c2d0001000002d00000c58200311603800c5010305c480420140f100d0070020662900049981121802d0030170592005040407004544403038403011611104000200094080c0d03c1401a0702480400d03128404641d210f040000180324030707008545142d40701100c01c0100382002009404c40c0b6103a64152490140c8400d108011480c1083c014000600085100c0510b02c002d411401e006140840b0170010005d14940410650180140f0704221140d9008000a49072a550400d404102e00c46c168210203610200c4041c00035007051006464070a0030100120750100d4034400e2a0640700800406802603180504000d9140c0c4404400c95813400188094102100e107805844035800f001982010800d08100620088030a4125545400b605000041040c44404589111424412460030708031404030408140401c000c40140d64202c0c1004048406028a030707032200c40400d045540d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 649149469 1250 649148219 649148231
    0xd271509020402130e133507121d010c060f09020909060702010c0806031c0909050114010e0303090d0b061203030c0306040c17010608041a041b080109080d050603070302060f04060201 80
    0xb03606e0032030300c2c0610130040c50802036081c4907030070b401d00d100031408699100c0e42c00300e518003400780100280d80221700300701c40301c02c540000e0982e480c1d0030094032425606040d4124154411a074002052202d00480141404e82e60300d44000c205042c50b000703803000c282c000d0a51851070415800d00313031f0340d4070049130340d0401546000c616089403441030742d9075401508010001c1c00110303a69846504c00009040107a01400042c20001800da600c6028481c02000810318016895403808005000c20312000602c52280d0801c0082c800b482e942c1c01c0715034164507004888103030140d032a200030a007184c4292070103010702d00c401f00402c0004a1034400552041c8003d54052262007082d001c01e60b4120980003007244502403000040c0000c40c801e5242642c01401b520a1148040d20011401496a03050300d055070000b42c0284e9030840200403251507402088418020810841d440d1110101c1d409203280300d102064990b0b0204900d50350800a0002031500101810b03034428840b50000c5d603035840ba200340707070155003810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 649150719 1250 649149469 649149481
    0x2409120f0616110a1e0c141f0519030b1810090504020a15180e0708070516020f0f040510090f0504020f040213030803010603020d271509020402130e 65
    0x6810000e12100b00401080e902c0c240e9940e036011032031117030000080c842c0703aa40c560020902100702c0c0001130540d02c441c009940f013480103006030100a00301914401d43e0520000380b00ca036100f0704580743c901759601e9403803e802000408501400365003500710751220907203181418100d0f0011038180100000c0d000c5504096072030944000340c1d44100c4003e548001c40d5642000f260010701e8102140542520f00900d80d40700b85140e400c0c940c1c00740d412100c1014683d008001c01640c0024225400411509080d805c21024207a0038881240c8800d00a02504200e040c0b00115140d404406a030000c0051040c0300b5445c20303950700031001c28540f19a001c0035003000c0c3d01a0404103944035013030040d900a84040c05126104090201940c03002c0b12090144004120010120b408031001d980078040c136640150395540300c41d00d80c40035160080c841422400001d6587e05405064100d40180907510230220310082c4425240d20700104991180a904640006006003000402541d848240c90031919140c3d000d484d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 649151969 1250 649150719 649150727
    0x3110a0822090605090c0f0d0f0b031911210d05070213020901050a081509090d120b06090123031f1401080606090307050d1109062409120f0616 63
    0x1340f02d200e070020441c0021030303241c41e41c8400401402d03106000340c0340b84c400400c14240403030b102c51540001c16130382c3d21442d12082c502031080300d911003000c01c0c2218441c162a254150f0303100c0e101000510034031521015001d40c0c1400390007103210b2902407095503454803950001606a80c00b41104a01c42c0d105041c9444401010b8402d440800700e040c0d5409080240c246410303a0248005401020012808c03034200c004c95850144080c81003c03540d0243c246042001405440d09000a02034110725081c101c2c581442d0f200c48068414181c0240703400d40a80340c284000a00c407403441c50500c01034035030000030403405407001c00840540140c480c0d44940810f40d42c1c1010006410b5000ca4140000e0034000818076a00d0709802802450ba07005003601ca16a5480c030010315034450001c4c04540c0e100004506807580c1c81c20350365179940a03605840032003001c11100d843c00d1014a55502407440c8007000720b030402050329400c0c01e1804852500c0201c0701c041d0340315902c01c0d07690801101c030000710721848030186000d1071003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 649153219 1250 649151969 649151981
    0x5070e041406010b0d050415090f030e0a03021309031e11071d04060f0e100b130e030d05100f17070501090b04141c21021903110a082209 60
    0x5001501d0b802c2404241086006d0074000c3e00c1590249030035501505920103030300c200803030705106040c140d414100c1c0d4a800f4014145e5a22481e01c1990800020009a200e03a0040c000810400d00001014141450180c41c1355014066040005207500100c11849800a003024005e02d40c0c6d90444010300d9584595600c108036922565214028403030120300018080d8101e00c800c1d00541e44045114140400014500f48040b22185c3e81c140d19a0b00740801820800c80f02d10384c4550528040c0040402d0090540e0307280715a00f440402ca070758841c000703069032486c000c5210103004c02c0c901c4995801c0e0346960803070a240013000c2c07401e094040d0f800005a90740c01131114100300c3d1a10f00c0801c0c1014608441070b4011032600258a40000301f46140c01c020030303914102c2000ba14410411003603031501d03010301017090b8181c01d802c100640d07000d80000410000c02010b4041850303403620b00704620388900d07030549007014940c1c3c1c001004110042103a80029a5580e038500d4448240d03264401c1c0c003070765503d10320143c0300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 649154469 1250 649153219 649153229
    0x41e1202010c0302010917040614030601050306311e05010302031f0f020c03130f06050306122e0e06240312071505010e040c0b0a020a05070e04140601 66
    0x1550268000550007440400c0ea050b0182c000092400042c2c0c49620860600c8086003e0500000500340109608407550301e0301e030300906020758258641980040c0c600d100240c10184150b1070520044c05114209607004441c0e4409000758110789420114600a002c6c409241030890740140701007500304159110302c40c12aa00180107149000040071212803140d003901d19600c017140c6889416000720300e17034001401825090b90056545491545000344034545a030000b0900c0610190200b000396809425250000000c40d00e411007108601500c614000d1000030000f15110000303101c8072042c000a041034031454100c0d8080c000364101091f441c1d2202c9042710103480700c1320481e041070180320700340303820002c0320401078101d0b4008660030044d00c3c0150850342d41103508070240e2083d41d202c005240180e900519100011450302e0525540d14150b094070342c06116220a008591050904c4c0301300b02e008d071425005009c1d21840c6031642001450b414044070141c60340304070078a40c000b2044002034542c0c100d030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 649155719 1250 649154469 649154489
    0x50f0402010e0f120703050c090121030f03060816090f09200a0f0e071d0f040506030705040612020418030c14030f030c120907060207050f12010c05041e 67
    0x103110810010142400b003565074010f504007085401136103040041c0000755001c5d0000744940e01c102404c0080300c103c140c004003c0002071900d00f07070140b0a601c928546969041c140320031036401d0140c0450041903258400041c5200701c400c46040085548104015100072410910001000c0780703a040a451401e5002040342174540b403468990034411141505081000780000396075640d4004000340341040b50050444444203606101840f0b401151184664402c05607030450a40284002815014440211401141c440c00010a50707681030201c480078001c0100104040f80e10342c00d185181030038915007207000d01c0c81c0284200120440400c12015103525503176205034880306a0341c0510100c82564540058401800180c03000d070003c1010703500c074018000138503848980d0300041405081c070180200c8a00e42010000340f0516a021039000d09a070000e0b64510384103044440420742040803c100b14401d54a4980e450f40101c1c1d111004008a40c0c0c18214035150035040b8080d840014058400e0007038071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 649156969 1250 649155719 649155737
    0x31104080a021201062d050901050609041a04110915040f0b0d14390d0c02030c0706030605010906030203060306060d0f02040501170706020102070c06080912120703050f040201 77
    0x510b01148202002c0404034008a15140e681c14440803411480000e4010784070346c2031a04040c400034203080340041c00c08a400c80410352500010540c02e1041c000c01e140a143c80301a00500b00100044025075800f015000300050700c1411460115a00040085840344a2029032074030b001c2d45140984003550705088108a410740740c80b5105001d64032049820b04215160020100000d000380ba140d803184803801121f001c0c0340c0740d4000c102007a0014003c2d4441c20440c00d0441580d000c201825546440343c2c3c0c04002603c490480c1c802c0e8518000c000e56040c2610491401281443c1e0603040070044880c04c0e00c41d000c030280c45900590980c01700315100d603095071007840081d078140341164603840424040c8546504415007600840d0544000340c00c40c0f41100000c81c0110501c0608200e0000102500e1000b1400c014090741c40150301403d81c8200c078200500e01000c5414108240103402080c941441441d903a00303140c690360007104504545080200e85403c0000d00310910340795219202310380c165208450 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 649158219 1250 649156969 649156973
    0xa0b0613060807121407060306090c0302071a0702070302090a1b1b0f030c20090702120405240403110a0501050a02030d0c03020c1504050f01020901020d0c020628031104080a 76
    0x3030704c0c00f52043e10b035171051251603c1e0800040c0202c40203002035550103d09603060081a0050707402141c94003081510400c030100118540840420540790342031540d480544900e01c040382740003c140c1020394000c1080c0b040c0300104500741c1c0a000380514402040e4004095014180ca080403074000e005591030040e440c0000041d006044041100d00c40d050001c4402c98945840800b11080407080d00c58514801070386c4002c1c5442c403105648009c0034070040c480400c01d00b15030300050040e8425140100324500000041d03074400540d58000508078481e81da140c03035980c2001c01280360b18080c07031402103600c000d020800c2c1d482041102d26000c070b00d8004625002e41c0d0310924001f0000702c80032008042d402d12a010030050b00703000810f046070140840403100d040c5810401d007001190f5150302940d030710402c4140d607103980120784c6001c0001e403401c02d06450400c50012139201d100300fa85407190388000d03c80303c05499440010395002004281d908100e01d5155440326000e5210340e0013610040e600040790600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 649159469 1250 649158219 649158239
    0x904110c280b1b03010b0901021209010e0f030a0f0c030303200406111606050c0705040212060607030c052d0607050319020f0309010b1207180b03030c0a0b0613060807 73
    0x3412040c985981c0444420f49150140c1a82003a006010610b5000070804120341e410489948003919001499292080c100300203419043c03400d94040c01a00c00e03031082081550148801c1290356081103144c074081c0400e00c1c00140340e0b10640030441c0071a10307128003030440e100304004034006903c1038490680744c9418410180c070000f200c0040c00340c5030b01c900e95040704503034908070300b960007000c9513200e040d01c400000641c036041490f2604418015481070200c000420821826982c00143c10b850381c40d583c2c103c2d402c080320301403801c0c00040c0841c822081c400014440892105c9145040303d10f10311500c80100760003e0b203411082d501500003d42c00d00204100110b40198030b15110300c040c100601d098005403e08070550004c4440e1840c5135510100c00000ccc4c140005140781240c000ca0113800c1c42800e02c4003240c2c2c0300403503c800503007007651040c0640464600b0412070701d410041d0f0040b50b811446600e03000303d00c0c060442d0348a0080c021764807500102c103190b0040d41c0070313604003c020340011410481480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 649160719 1250 649159469 649159471
    0xd05030601050a2010021305060708040603020f0f030903070303050f0708061011010e06060306010605130306020a050708070c030203010b010302120c09010c140d1b1e080904110c280b 80
    0x11318458081600685440c820813110114002100b009a2204004c0c0c10000c400c01c1151300090044404105e400005000c6404440613100582030050703e41014900c04507850040d000103000b003520000030b01c1008030b000005440c9842c882c3d0340034881540c586031241c1d4150030968a42c2d0200303a060021078000e2402c407000d010f10400d2440c0404040400421084c250703800084200ca0303540220382408410f060a0128038050105c0d402c282e0710b0b00c100c081240d0402c0e0a903100280000794042119100a8400c1040758840381d04080c2c081d80707500741410980c6c41e400d6940f01c03c910941c60118506225406402070742d21000400c41c12074407907611858907541a5022405903410030036103640c0c1100042112001d01940301424009040c40c0d2504000a01001c0c080c000c5500503042c031007e800c0005001c0c05040c16074609448507400c83c81201d1800e10700c24000c0940b0a940301e81000f49068040080002500c014002c050440e40390301c9414a4a40c83c140018560301c0403044207007055000300745400405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 649161969 1250 649160719 649160747
    0x6150318010e1902032b0e01020109020d110415150c0809040e0f120403240e060a1a0d0b1605070507120302150f0a0f0f090f02030d05030601050a 64
    0x11841160840e0018104440f01c80d240c1454542007049005504040103500da604464200001c090031210104400240244102c902040400140e43c0c510364400c0d0009100c1c694090400d0141070038607d821100f50441c180d0480c0501c0c50030604013058024508140101d070581801d01c1002d802100b0104d0f000704040c132043d103c1c0e030010800c10600c0c0d240d521524126400382e00182060000071034207a030500802c000d0380e03c0800070512092010949141c0c1c21400448940d2400c0b000c02a004444005000c40d0011035405000e0a0200510b00809400c25040c50a01405004000b43c4600070040e01c0c0f10300b044040e1410003030f400020400340c801b029419420015040c11814440c00d541d41914110440e08016814100b0b80718402c10076404100440c8080002e002100403880c0005c05441c2840c3c0c01001c0460864554501407180052540146902c0c00c00c07240900c40000341d0309008400c0340d00504128002d21131200c5114000303100f0000d0340d000310416581c05290202441c800c541d211100340f46 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 649163219 1250 649161969 649161971
    0x30c050d020c0a06050a183003050405210703060c11150a05040206130603091109040314091318120207030302100b0f03420105091e04030203120615031801 68
    0x11f00b60700d03004500440145814240900d0b1035040d41c0c1114250085001203801c02050b0300c000b20f00190300081036a05480c020784642c920700031010082082c10300303000381d442d000b80240c2c0030100500480c3d4100c0104968591111113a40c421031210039500d0300d4000c682c520003004072001c80c4240e07110360809500280010400d50400801c1c3c0c03110380c00300c0074a038000004a0f42d1f0301d50442c1084007894000f03c9214007113860700902d24054801030400c16221196a41c0f0000029500755169501c500c85104401044410844460440e00c4c5100b40b0129000546803046480c0b0b506100c5403002039158180d0b43d040e40074201d8000c190404602070183c042042e640300e45d0302003503008691804c01405800b02050f200309030f01014424440c18000100e0081c0b210035021940e18010007422a802040c1154425508412260703190300500851440080c03804d003500010f00148024558008060490007042240502607078503020204080791003206d9120682140500024104903008403c042000d084080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 649164469 1250 649163219 649163237
    0x5131809080f07051b060702040906020f04140a050d030207170705150a0e090108150c04090c09080708060112030f030b06031806090102091f090e0103030c050d020c0a06050a 76
    0x140740c0d500c5800500c008620507202050410501c5820056401c0c6650400320700320081a03003401194040c4501e1340040c2c02203403110600f0082000030340c100c52216240c01c40c1d40c0d480390b0716032011150a90409080f10b225844180d400314062070509030001c056945500103142c0b40d440c1c003d44003104851a40000118010303a240029191210074101c0c03000c4000280d102c2d9160910700002e454100000c0743c86001d90305040042c4212800018444e200b000c901c00c2c0b2581690343c0b1903e40242d4841e5400070712555003402003004115401c0706421080e0703007400d026120303820740b90b000c041e603140300920400c2c07401490840010003080c000c03400c02c0041501c03464041a11612800818420350040c1c68940c85081c14040411710030310b080c00700c907401000d801d0095240844501c0010501040707000b020500141ca0384074108a140286c40030070040c003e401d8000c02941e904c0c1409400242c9c001303400c0d20f29000d00480038141c0c2d840403414425051000304500b1155080600445403904048007175402d100a0384 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 649165719 1250 649164469 649164473
    0x21c080609092401080f0106080601050f04110a0206041a250309050f0f010b010503090a140a05151806060108010303120f18060e1504080304020a090906060f0605131809 74
    0x4001c403083d10101192000c0394540040540b0309440b17629035007907070703490305005000f8550081000307811100100d40c0c10a10101c07050018006210915210704048000100d00c11140e8000c03480a00c0f0314014181100c03841d000d200d4880380d091088469410700d58900c162000b12230a14540c108001032030b442d0004200790b0715540e04e40341180e80c01000140394000d2003001c845041c24003644c0700c44a428038240c0d04604040003029610007003c04000d0251601c048144c032204020425445803981120840702d82071010b40b4120304103141518003035039450381c143e500c180308180061207034050070040c0e45043c0203a11790b80b4101c90908031101d5103010780b6120089514090018010449201b22540d1420810b007041c2c54480100c844141d84078046810070803911240288154a40f9449a00001c020795241da49100007030031080c0c141c020090503131130a100c001c24801c40f07510000546580b649c0c200308013503c411040d94640549031707095480038003a6a003404243d150110740014000341d5071001c10402c6080d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 649166969 1250 649165719 649165753
    0xf020702030d0c0203102f0f0301060305060109050604031a090708070807051002070501091205101406120106051513030f051f02040308070f05150a0c021c08060909 72
    0x20b040c10380009184502a4070541c5000c0c40081c0320703851041c0082100880002c7d414542c0030350f00c0c1c856107980010b206904016004942110110788800405139a1381d0307190407020300101010707103105000802410000c00d041c1410b40440d0142d94101c10042c050304010411502e503140001d180c1d030750a0040c03800001c0c10002c100001000341030120040e02c8010f04000500c0200103100d42c2e4041190b1051004200a0b60048410400d131080d0800c110300f00304e40750501a142c00c121000c2c0c01c1001e40b0704417483c0e440c000001003943c010001155114540790401d46410f080e20024003035964410000c1c00ca03034488102540041c2010141035040420b855901d8a420080c0a0030b0541900d00d50032494558808005107400540614610402141424190b80340c0e001c0303034054031000070211302d091901081448401c02680911244408811440b46845503091025150003589440984105408200903000c0011420464402e541c0c17050f0703056480c44100411300c240906003c200e4041e403e81010142c00c070f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 649168219 1250 649166969 649166983
    0x60f060302030304060509150a0e060c15010e06040e0c0312090d0209010801050601111b010302070614070f09050d21050408010212100806040203070308030606091c0303060609180f02070203 83
    0x3451706c0300d0f40c54994a00c01c0c05a2882112800610040e040141d014150741004a00d948400c0070f680980d00e42ca84926118500901690301c0412000030200004a0208010b40180300b11004c1c0c500344002414040c0180e0b880c0300b40d4403880d90641200f00140300c141030b80c0c400b80c000810004c01e401c04107042031300400c0011600381c0114802c0d035111b00c2004400d5802c200101122507424009005146000741e400000c81c02c408420b604142d000203a0302c00f44030036500011206103211503d100c0a042203a4040c150010740d86085000c114180000036071482c0000040021941181d602c01084c1c1e4501c1541408000421018082c00342c2413201050705c07a0244040c0c1216600900300c00101c1c1030100b2150254856036006403807581c420010080140c40102b0034004030303035000f20081d880e5280c07140041c0072400fa02c01d2460b000707040305440903c00305019000d400c0140c040c1c3c400b0080b507a151141101e40f81c400e4000c183c40000c200b0040444075080b80d000c0c1c00f80701e490328401410051103500103410700d11 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 649169469 1250 649168219 649168229
    0xd05010b030402190305071a2119060602061504091a330405060102010e0f030316110a0b150904120305070f021e210d0b030705010903060f060302030304 67
    0x1c4100003c6052042484040300441d0f0910300d005881c5030b03203150fa01c1480e0701640c6001a541c07110303004008000005d1302c6000900b4041c521801094021401039441d045551007205100910402e201901c14411142912511b9000e004a60340b04403458180c045030310300403030708141d403038400401188020b030005000d000f1b05000700c1c840d0708101c0300209451071104040034440c00c10312450300210100e02035a4090721400c0d9030200d1960f0b22100141d0050250084a82e042d000b0f8561001d50340f50080300861144580d91442c0c2c0c240640c0d00811501031407845c0c2c001c1080c1e44510b140700c01244e0092500344d8010140405500c5006980c0d02041184009560464002d6140c08000300e0b01601030080c10743c00052031401d44010003103250000d54031440c01d4118200d8402003400306200d00c03018000308010f00c00e1031245800c0100b0410340c4601c25400001c0c1c40303100701c0c13804861010301d21b404102c85044480580d5a80015401d50310791030028854100d0724a5100e544000c0000180c0f424000350000f04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 649170719 1250 649169469 649169489
    0x501020a0929072012010b040f0e0304050d0602160609120c020a05060a030605120c09180a060c02010e0d0906170c0a140f0d05060a120c060f050d0501 66
    0xd0710b4506800300c40881c4880540a80301c101032248205035424040da4841c9030400c0c0c1c001c02d50300c2d03030312100d080e0020703814185a0000e6600804454071041504024001071040e201004401a0600c0c1c513000c495101c0700c41e001c2034004020070080c902c0c0401114601d54003800c4014036041d03072400080d40000444008171601c0352107517802c0092001061490380070701d0240c10035800024a6500061040c6101c0c013030584aaa0007103407818449200c0d51140d0086e08029004800c00250144d40e41d9468011030b00080c420406a000540310880418030461415030020042011403482e40c0c0d81c1000c0c003944134002c0115076a8489410852504008654822100380c6600480c1418004024101400d030400c1e440510001d109020301c04084404444403406c90b0315001154101d80c2c41c1000b20341c8103e91840c441810b01058400281606600442c01414211001c918240d69459000003848020001a02501e86014104000d81c0140810180e21049141c040d150030207610345030b4100c80d0280c001101310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 649171969 1250 649170719 649170737
    0x211018020a0b0a08160c050307150b06040b0306100e061909060309050c04020a030b090903120714160203030c01060b0c0601050a150c061b02010e06060a2607030501020a 74
    0x5810060044006041140b505501d03040b01c80768082d0011401810340c0c1001c1c800d03840ca503595184210f805000304c9503c0400e8a03518856410000d091261030404508101c0c5000001400b40ca070160440e001c075001c1e4404a03007555504401c0110304030f11040c060301441000086407405903100e20081c01c010948040d08440c030880020300920618203070b003168041c10302d02400340000c10f0000806a620190485015a83c1c503500c0404130090074000e80030603040810f03e41804040301d00407020f042020b07003042e107100195464500403941d0540348181250480c40800c80603402e84401d07240341c4501c0d40007400f00c1c0c1c500a0001011421619a540808111072001c0f4406071280414821940180001c403207080b203950034140740040a0903050700d03400c1400480141c1d50f0400045410200c0c03901c105091ba2400d0148030a4068060819001020302c2d40c0906d400240c0185404200c40069450380c00c1e100c50101307203603841403192039000303d1080c602c0e11860030000000b81c000d0000f010114001d135588440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 649173219 1250 649171969 649171973
    0x30405120a1203271a090a031e1b1731050105040e0a0e0102070803061c0503030604090201030e0d09050a09020309120702040209030d0305010f0f05211018 68
    0x500c02c0c02d01c03010002c050030721100d030003940ca00c101181c0784001003129070100d04d82d41e840c00c0c400064150780c81c0a0100311080030080100008541c0c074042c14001d4413500c02e600d1524024000b925510401c103400b040316082c040b440e050300745018180c100c0c4034021041e0740b00c0c50244c2c250703038907088020154070320016912802042d8070006c111059034003c14095500032070a00300060200d002d203006082540c1c10300300c000342411034160021548000c40c003008659071101810700d02040d51044a00d54018003059448094010342c4c94208e02d055500003001d1800c603180c000c2044041d102c1400b040c2e04140e20b40b440c12607c800140100c1081d0f20312903c411880901d003109000640c8110b500c1071080e18410710420072400004104603c10b81d481e50803a540c5c8a005100190007030140021207074040c41121204007089815902140c181e50070a680701c101c540c0c2e140d40d04210b0250b03038014160400400780280510903141000006001149010768200d40840e4260508482c00500e503a146da17040b455150381 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 649174469 1250 649173219 649173233
    0x12060a0204140414040b1e0718050f1014070212010c03181104090201090803030717060a05011e05040e090d03180b0402010c080f040b0c0c030307170c030405120a 71
    0x11210b1043e1400c1c03144900d01a66080446001040a0802d506120009091003c20070381c9a109241c248000141c42c140464002c205103074641c000030100030100c90201d010315001c101e003140d080000f85100141050302d035040301d1a40d94402c4292000e2000c0c0944001a5201281c442200c90074100004e80380003125001000d5504654070001003146890321040032942d40e0410a4038a1f07400e0b50042003408251004039041012070b4865100d07400003200b0300c142c640d40000e40c10705031a0722013807c81c00750700d8400800035075502e203104444c045642c4052800149048000840c03240c1e82c5814000d08003941c5d60100c58851404035100c401e681c20014a0264043e011312860222a040e0041c603118040b19550344441031401600181c184405036120104101e0300c01d04483d0f00f007a8050317442e42c41c1c41e592003440d12580c00241c2c541189000c0e6448038592410000b064030309154214404025013a5480c240c11a50b62203544000c000740030800000c101e640345c1101d54016185020020305916408d810300607 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 649175719 1250 649174469 649174499
    0x9060f0f180304150e0a0b1213170c010b01020105010b1c0513020406063506040203181c0e031b09040303020408070e0a0e0607140a02030c0706020d0807080112060b12060a0204 77
    0x2501800c18840034100c01c43c1c0380e01095001c2031040b51000000c10505101c00d203c503030040511030300350000401c01943c00cbc0640140c003400e2800c0e002403100741d80b0741c440d1062034051807a0941e641502c80b240c50344200d00640180340c001c0300e00240300050000300d170081010703150a600000082140e0603078030484954608943c0c162070f074400b001d40350140e001e03800035072000e007004d09000e11a58001c0040340ea25100818010100100f110803548501114001c0b00010038501c40d030003000c101160003401090030086254008180c0d448030b1584410b40f44820050b00d840050000d030109982440003041c000c0041141c080641b980108866042c82c11030740c0d0005a41c032005440e00769070002c00500c005160014114000c0003c240c911075100c10901804a15601541c039001c2807a1213050380014800740c001c200e54140307074101d030b49100444c0d50303480301901c24000a11441a4a600007484440803c40590000009800040c4143c000d5080b200a861405505403203011005600283c1003200c204c0d070340040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 649176969 1250 649175719 649175729
    0x180303020a081005061222110a081b0d0c1203020304050f010c05070501081e0114030d260a0f0c09061808150a0902030a060509060f0f180304150e0a 65
    0x40003042d070031301c800b0842d2801242d904007100e80d094008110301c405012200320700440040c2485a04106c01c0c01c204440f007118040ba903002c0c0003400400329102e43c0c0070468103507030140e001601e000019030809010f5000440e400c01d681e402c4107140c0101302c0020b4a02844039181c0a40c0c01544c50f21b0030f04081107004c00c1e1342c90181e4140711031280c0b400c1c00104042200c0c0d00f140c5090800e886e40350307500707a500c0c141d200760b4900702d040460130301002041c0d03000404080400e42400360f040f29127292103102e00b0b0b25141d40715055644003011130410034504074111081c030b076801010250301041e00c500c08031040301503030000901d4002003003541d07005206c42680402665040e09524120320798480c901640726444e0b0320b054035894401001100026001000c41d08482c000766805400c4400d83c1140c4e017080c9004203401d0340e10080314018080030800c0300d5201d900180c09000881000c4465440c0c2004088514444142c1580700380003d03c030000d0024071140300b40111581c1c0351101c0414100c05030800030006025008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 649178219 1250 649176969 649176991
    0x60b03030c1014161206080d232701020309040608010b120105070f0507020d290105100503070f031407090815100506210a06030b0f040506060112180303020a08 70
    0x3085859604844c020818450364148504c3c0042c5080c41e90005d04299005240070341b0074498010882584200b441c640c1c42c4070701018010015282e0b140d00f81c1d501c02c202643c43e0f880780b0b001031050050003002140b00c102030140103e82c03404401101003010740700d95a024090070b9640c1c2c0d01c000d03500d0410b5a4141500000700d802000305142c11000075011200b03003e480002c00034003040b0b40e07086407100e508032804a03410500d00002c1c420591010042d0300024001c00185400c03201c00020315040c82d0700070100d01486500c0e500d0840d543e5810888000c0401c80c03c0104041d00c8003010901a260b8036151070040750f45076039030380d002d07400c000c2c4680c68034415030304c01d4042400c4e80040003005c900911132501030301c008491081d5100c14030040010301c1001d00703058400001f41c44041c0302d000221517200034200c0344511003203500395a50101c003200801040381c000d042d540140e00000c48640c420041e5007404c03840028000317014501980c1d0b524000c64003203400c0300400e90010307103024481e400c141c025912400240b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 649179469 1250 649178219 649178221
    0xc010b180126010501030b07020f0c030c0d030314091015081b01050418290a060513080114091618050411131d0307110d060b03030c1014 60
    0x40398490361814416003001c200304100e80080c05030a80300b008a000e0000c8002d11a42d6180d0810b40f201104c103480c081d000d8460307034944451541010541181d00e0000070050403c5500e400144408860b20700700c11001c00d41d889400c8000441d140c0300d0709008000c908000c003850b403c02201c03201103802c00e44550441c1d05442c98104100100000c41c001680c94180c5000c112003890030060b140e90049802103201a6544107010f05042800d034000070040070361143d89460007241d074440d81c00c440103111410385c000032651020f100c520f000300002c10002e00800c8003402e03201c2d6250311190071551325225400c01400f000040c426100ca04110f121320f50842c0e840011750311403412441c1d05401c81c41610081c4101e44920009042c44100301352a10815009410841d0b03818109030150010003403100912144110390814407008040001941e40c01680100d4440e50215074400b0001e4450703018008540c00354881c0c03503142c0c06440920150001020300c1c4020300c8407103400d81d070310b20583c3c4151a01664244142c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 649180719 1250 649179469 649179499
    0x180f080601090207021f1710030b060d05030c150411030304060203040e250f110610170123041101050a080403051308070b1201050f030327150c010b 65
    0x104030a41142d00102005940e141503201040a80165080d07052551481c01019172040c1c1c0c200d841d811030300c0d482c110faa81c01c0e03541b400b18034003002c0702d24000500744c01142d600103400741c18038510a099080c010001c5904000020940501d010101e0040400e0a51014180010400000e480d2105054124095400d007070412034002c0d542d0196114940050300c0860204421958041d40300617661102c84c0a122125603c2c0c0c030241c41035018654680c0018598481980202c00101c1c030030f0b015043c0c0301c0700c00d175400e49084900800c1c4100910601c2013035503907503881c2d24100313402d00030f0070b0000e4502011500e651516003010b81c814641d107900030f07061240030001c031041c01e070707006501c664481d0307241c1405615074416a01407680c0b01525046803070140710b810400301c1e4280d0540040d02821341903507801d00c100e0b07883d24144104404200c0041d40c0681c0203010580f280780c10602294000d0702d500e00b041180706030140024140324200654040c841d040005c01c071403158400c0c016201c40c0300090b24035100d5031000d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 649181969 1250 649180719 649180723
    0x5040b03010204151407120816020d0f230307020106050a0603110301060c110d060b0a060201060503211c1e0c080402060d0902180106032403060510080a03180f08 71
    0x1e407030380c00c0070049040c010382d00c0c400c0d09109480c005500540d04807c2e4007003a42000c0e101034011340d155032413013000c01b0104000d00d00c000b440d40800350540c4e0303401101000000c415a048001e50440c6901d0326500c61861005050120142d407044031240d001180c1145030105118000a80e5048441050f041c00c04143d9113412610132207044076182c1c500440ba481c11410141c0844038903600c05c0c1d5101c120450752005210030b5401034100e0390002c484155143d81e44100c207900f21200b511131160103400180440b0720201c2c1202c0001410380840b40c0c031504e442a050b4280c81c003810b0000e0400c4059958041c8441c0781c0200303420362042c030710303c042d020030603500e000101a109200040c8001d104800014800c980e50b405d075003144100690280276160b000b4522001c4a180031024010758000a26000c00c120040075004035990450340c0b1a90100589d074250b882d4000600b0307004000b9111900d04410000e40388208002149619020f40e0702c101c0128211503100c0386c455000e903c6044210382d03242041c000d071a00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 649183219 1250 649181969 649181999
    0x5010906050f0f0103031e0c020306040c0e060a0617091606050309100c1e23250201080c090414190f0b01170a110301030c180908090d0c0f08010605040b03010204 71
    0x50343c4910401d01f600c8085820441c007100094050058005003c204103120b4507110654070700b00d1000081d6626141071000000340c5200f080b00181141080740f8581181d02c1000d50040364000648060544e110a02900000c043e80040c0c00510300008004501e00d003808145100015003009002d02e00c005000204402b15006214030181c10009043e04028080c500c0041240117034110015401840e040301040d030340040c0c2041d02400c070400d81a4900a0074040e6968089605854a5100342c5403101e100c2820b801c402080c50b0840d075078042400b10707803034110645886950507407000c0d194242247d5150060310003500c10291460b040c070700d0142d010f82c0c00c5000d503514001110042ca816034ad07121000006440c100f80006504c0740008004000c0c490903a02e841d099484a100b041d841f00704503d98a002c842904c80d0140009800703024009091034407a1582c00e1150044026900154aa0211040e0010b440e03004030020382d920041000036003014000d460080c00202c000314101481c1c1701c1c09090240c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 649184469 1250 649183219 649183247
    0x90507031802090a0e070b070203070519030f061104301707151505090c030403081302030309041505010e0f0907032706063012030905010906050f0f010303 68
    0x3c0c2c030000507101160035032020084074105411103460325602c3c144101d060707104100036402805000400321740c0c0d04101100300c16006c506410700d031015203181c50f003000e0806204001c0780e6043d01c0c1e00340d9140c110710800240000c2c001481ea0360810000d09118803480070428588516114034110102000c1b412008500040f80d040040040c1d4444003494070032808030b064032040c0c051600d40f00078040121214011081900c0060301d8000290b181c00002c6002c0740400ca8004001a0503a0001104102d410880c05109031016003220b00b030410300400242500c0151881c401220303d0040108090369110417111044103041d1a180d44601c100300100e03200c00001002542455150030311400b55441102c1031403c49505c000d0150b8030120309241001c0504814451a000e00d518600010401c1055a0841d11108841c5000382e04403100d80c2d442407070b451401c0a01e041410f5071000b103000840c20038080d075451184600000602c1d407030314070b0b00a41061005000007200b840c500d401440000c0d005400f02000c1c907 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 649185719 1250 649184469 649184479
    0x9050901141f030f0510031208090309100507020303032401090815090c031009050c09010503030d0b0102030f070807050f060708074514031009111504090507031802 72
    0x5110102c1074001e0941d40180a400301e00d490104090801c0030018041a82d01c10352040306000071700081200e003030100340c6d01032002d41c00403c001201c0d441c280410030a0a403da0408030308001c29500000d0a6070421150a03502c2240400b4102822076280c1100403648000d0810200417401c0010f940d81d074501881400800035408408180c4512003041a424210001070460b8801c80a030340d0300700c0203816200401c81c2ca130b20540000b01094a020091981030b079001400a600340f40801d01510007605880400506502042011215260704000145826406a02425038a03c0c031450300c00d2400c100800c40d42d2050304080184a106e540c4100c0c100e81010003460704e5a42c88201602011781c21442ca480404460780015000355481b004c504d092524108040d9049101c03a500d241d0b240b400401204c00e07550540000000c40780c5605c5583c07140c1c07003181c0101c4c50f00940f489501e011444140b018503101406044c04070342003040309407a0180c4c13544100c0d03510b011702801000d600c10700440401e03004d00034419 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 649186969 1250 649185719 649185769
    0x110d050604020d1112060a0303080705222c010f0e0a140703230402030d0f03090204060b03041709030a150b090a06060207050420030c0409020a0905090114 68
    0x56860b90199201000b0031101040942188111041242e110b188090660101180040e8046c6480407001040b00d40584465401340d99801c000c9446501c900d920301c1c40740c50780d41e440d4510b003003040b040c20014020002c100d110006009582100e0340c4559100d01100703010a60044c0038201150040c2000c44580180c07080e940c1c0c4408941c0c0020341b160050410145c25220100000580d00d034104074545400d41c2e640300149112298030504e0b9280071100030350144c0c4401c07100d01013984030703010b4590040b5107413800054400d4030364005000d9031000e60040340506008800e010070b020682010b42c55000e0101d00140c0f4024503080460b881c0d02c1c00b207101401d0603545180f80503002139203411000e0704290080000a0310702d005000300c070081c0124010000103100382580030a00341050711641510503a01030200784201e0b00d0559117051030b8001000700d401202c050000062401d40d41c0082c0420742d541d0b441c0c8150711420001848000c42c81603001e0001e600d82402200c1e016201c81c00c2209070400000640c540c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 649188219 1250 649186969 649186981
    0x1a03100207030c05031810030b0d0b090c0a0b030a0c09120b27010f0b0607020d0f0503090d03030203010e06100c17041229100b070515190c03110d05 65
    0x40419000060f20b64000082d44d00c041c0b208101400ca006c16044402d00080c9504240c01c8040703409500805400181030b01c1c0b00c23004940307100c1940754441d4014040b2069206558049003c00217243c0c00083c1c40038000c000c0c0091200140170316002d958891800203802480c158150034494500d50000e8080e40329900810145001c840388190500c212801c0d1108150951440500034940f10204000240c9010004d1643d031a00c0300032144020740040c11f40c00405242c1d26101141400007904071400c1c0f004000450b80d80d2666102614803d0098800507180c0d071501d001b10820940c02041507105070942258561101d400490070300c83c1d1904111a0303e050140f001440b400d07441140c214201e40341187e40c51500f082101c52110036000461801010584200704401d0401039040c3c2d0602410b4001c80028080e003054040a41040750091045800ca0042450740307808590341030750302d406410b11140e2505407140750703800381a0b0403d40c903241c10420800c1d10b9444118902440d0041d2a006440b500886d034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 649189469 1250 649188219 649188227
    0x618050d081b0c090112020906060306011202030604090615031403030402060a0e040e1608191a0a0902091312090803030705070215180a140a1502011b020c041a0310020703 75
    0x803c07100c000e08101020b584070346400c613545030020005c038403426654001400904061054030f01130041a101c190911500b40094000b07508005c1003150484d81d1408100041509406044005200208081000790031810540e51030413052404100a070b200304240001038940900311050780d0340900c1d200503030b11074481c000f401900042d40010b0f6175204010074904000c072401c10171002c951808046400c0110b49000501c9900d5074983c001d0a80e104039030584400a0052108e19440018003400042038601e51b40010358800054810002101c1d108010008001c00c400024031039111900f043c032a039510300f803080c555904c002850001003081c0400e1010441d2520303d001092103000151540c0c030348952801002c0c101784101502407041ca40841d0001d20302d400c41415091101e006403003a1081c034244016140310401c984a81001c5658452081000c40316480e5010142017499024210b01c174100800c12040e02c40b080d0b0403424010624006504550300022840e152140c0700b1070141e2280910b0400351 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 649190719 1250 649189469 649189483
    0x5070305071b0807150c0c14130f090c0e060306062404180c0c03020c09070c080309010b102f0f0f0f010c080105180604150618050d081b 60
    0x198440038180c4020030f01050200740d080944160f5140c200108800a40c1201c82981e0074002422848a598080c407141081003c0101e200c0d502404030300761221000d4101c0e08448059403d04c107405d64680c0441d00f000400880e94005102c1c0201000356401c0030400030740c50f0710000d48014801c41d074056503600071100840ca451207503044044219100d035070b44e00d84400211580d40c44210820b10b000c901c1d14890380a01443e10549800d60b0042030341d11590400d10114100103800d000a20181c1d10100c80055040c90080d84903080100020075214020001e00900d01c1c41503c450381804049043d040b0f51150b12803c2c903181903803160365401c1d69800c0002c84c1e410f102016051564601405c00c103440703406c000017602c4600345007800080140300d007042c6003180c20200c04c0c0206030f440311803c150046403e541f0242603412020050000601c036283c40440c1e403600d041c42d0701210114220700d6000c0c01d402e00d4489084018041541c4600280b4043d6507180704c0c1380314491001020400140403c680e002c2e01f00844 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 649191969 1250 649190719 649190753
    0x19050928020f180109020307050d0606052a0a200409030c110607030813020f030d0f0314060904030c05030720090702150714160f0b13030507030507 65
    0x95440315000c0010350028100405041c1d00480c1d4030065084141007030b080350784040f00079210402c00c0f0303400d0507500740282d4800742180040003000d03c500b08101d4410f01c141c030020411603c5465580e80580b04c01d000c0c0c0403c0015140e0321003544402c0d21003841c1d0100d408001c181d44000f007041940c00d581d6280b41c10507010030140ea080b500e0b0022a03020150884124600b41d409084400c0703e0101010030404188240d80004000030300304e0b0081001c01c0e01080403415101d20050440c031400d811240401e1911613400082c80009850049400442d80c04d0702c1040c0300c60810507425440e0749400c1c0301203440118003604c000d081040c8143d11005000c020710640303207001e0340100e007400d260b405050304052a081d9500c1d200c0c400c004030000314201300d0002074000c00000c0d12551840c0d090b50303040000d0790622203054803c5903040e01000100c200c01c10380c42690b070780c040c41042d040f01e417007600f400c0020141a005020040d4002c2c074404000110380c010054990455142c030703015682d4040c600e00142401914440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 649193219 1250 649191969 649192003
    0x20a031508010b030f010c0219230615031b010f05070c080307021008070c230609101103010b0904150305060420010201140105040e031e0a090608190509 67
    0x8041252078064105412955085003240c0082d1039a0f03207414200c50454251f00d015a00a003245400041000d1042913054041d0040d104500880010349400501250322184a9042502008641e80884880d003034030960960007017544640300160307038045582032482903045c048000034a4000030720034000c40f00380a03800110402140e0707641c1c04290780c903085500c01301e101d602803169115200703201d1107000307218801c81d03a80e000000b130040d182c040d00d582c41d2405089400c80280f1440d08a01820000700d4082d45595000b09112030540342d10204840000c001108481000c1004011500410041d1810328000b00c50029060010344110702181c2865400140940107010401c810300040840868040c004d0802c0700d1100c03815200124202c842d4404c041403005d82540051100342801c2c0d001203271500300207044074900740c3d1305417407017039402603085000d03115010000e02180303219409440f4400402d0541000c580a08000c00c0101c117041d94264860012a41d03400040c040580c00c100e00c561585441d80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 649194469 1250 649193219 649193261
    0x8060c031f0f05100302120415020f0a08060f0604060f12061203080414010e10020c1005010e010f06090e0c070c09050a061a0c0a0803040302010608030a031d060105010909020a03 78
    0x581c02103940b001c0c0701e580d128102003014071615030b0007030089402280f200400e4a41c0c076903907651072142c09502d00c0c103d0801e056003400004038600401c4020a03c00445844022180c5001d00400c11b01200c8000d0081c09505d003404100034040e00400b1500e0000040e0601c5030703007004041c4000005003420762010008e0000306580c03005060300500c92034003a82c062000888540345009000342680c00e0000c2e40306503503000240c00c07004000c45074042c10320041c0110076603248411808048081e1a002c0c0c1004c1000c07011240100945890141c507003005185ea810515149072800c0001c6007800001001c400240200040100811440450900c081c00107030100f00801d0030441d502c00c000b0055409501009000c1d00080031301340d4250401d840d0007510100003071503000040d685041e002d070005002201550349a1102040014052024150340c6846a60000d22141a100e4078042407045e2350007010107411101c01848141d0b0b000341c1803010355000542c01769443d00314007030440040c180c104a02e170301041609 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 649195719 1250 649194469 649194479
    0x31205010b04090b0301110f0d020405091015020f1b12010501060503071101020705070b090a0f090b2701050103020a1b2a0e06130e0f06090706020708060c031f 70
    0x120242c0180c0d800c20700704002110741d5070107044c00c851502d0348031400190305100307120074620b58000134003075120001c4015040c15956400f05080d8042992120120480110705005210780108101d025081601c028a4980c0c0e00302e0b965230701e0311540c82c0c250b081340c0720075101e0b51401d03242e0f51514942e420f00c61008102c2982c0d0303605c0c0206503401c02e480034400248030700103101c841c043c14020f6403403090700140907022084c980500112281d100d15503107a048401554006241d2141c04c0940005140c13031a0007103a511060802c01c11441c40018220f0340b45482c0c032106000034500c200d440e41c19101c0a0138010380d030345061541503070328140d110015100503900c00a400104507102d48010502d4100700c1c02c0b00d101d42003449096411002e540610b100807981c3d0f400140c40c07890601020b0f181151030040000e1400e001c103021a050404840c49001f036540514144080800704100010051510388090160203092021154032044090802648241c021000c10300202d001c800c40310442268128030556145d0720 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 649196969 1250 649195719 649195739
    0xf0e12060f01080a0c0504050714040801090c0b0a020c010f030b1c0501050f09060c13030b0f040c0f05130f0b0a26030712080703090b18010b030a020a060c03120501 72
    0x440786400e1464034007000103a2050002485a5203540c002e000700001c60030300d41400014134009010f001081820f0300c2c0d5643c240340c5c02e0014005422180b001050f14103850814120919080c0d00c011200c0100700300340c040450380400d58004100c0c00340b0384450b0200c0700f120120042c02c62000c1455100c0c1002e0320040c4c11111a14000701200d108000901a541c0c49424940010400300d5007542990000b00000d0300300400c0c00000e00303046840c023159502058403501d508156103400c44140c0f60108840041c0004e001c6c0c030444c000010030841d0740e40e494060902c0d0115125001d0010000c0340203840d20342503035100300d154015a81a48018010016850307895000c948002a290300040c080e10040101d09031002004c000c0314003194010f44c0e06030111200c42011107040000404ca081010340e902c4908002070045090180600c3c440c80c4810811601c0c40c0381d003405c580201501c03600c40e42c880980d09e00181c4542648038200c0b0310b1420201111003850805131001c100524101d040c0d64900800420010301c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 649198219 1250 649196969 649196971
    0xa03020406110307030f050a0c17071b14040b2e09080c060304031412091b01022a150a091511100b060f1201061403040c060f0e1206 58
    0x70a94030000d4030010b120b86581c4a2050503005400542a0b00305044d030103004800403c0d4500b624170f80101e01d4221612050f410300e406024603c40983c0005a2206200050b14105400e00c60841104000740ca03084d200060781881d030440c58010390711181c0c005540c1d5980d0151b180041c00818510340d002040c400c07000010700e100448980031901d50a004910500d000801303506a860142446285445948003542c4207101d100b20452414000c00402c040b04a0b0b918006000d0b4400600402c1e070440b00700c0c1e10740c14500188400ca4115880118003090001e609210aa90700c4200c100c01c00c2c0b00540c0d4000301b44036903003d080e0501440000512580425131000d0f001044820704000c0c03c101408400d4220f901880071100140c0945c07003080103060b00407a9600440c05100018101494a003280030904000d801801d6030409104042004114203034014100c0040750031b0700821301c1e107103240c81e90340c644224005000344800c0243c01803142c43c0c40c6003c0c0c04541a6841c00800d01d0030b00f0920305214580d42c0b28 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 649199469 1250 649198219 649198229
    0x41d0a060509031914091c02030f011814250302040b0f1e0307050d06150509010506070303110f1911060928020409030f0207080d0c0f060e030a030204 66
    0x80740c01c0000c2e00d65000401500c032000c41d5500700b03110220604c0c5040700d046824406000d05450304101c1c0003299900d41c111868601e031258a24491207006004060419003c035002c00785c6641800705030325144500c000170146403648075500c078007248a8203005900d400002d86c01d09030300d075a0071810214140ec82d01c0400742128400c440c00d02108180714240960a01e10b2120a9003008080410b41d00c09a4a02110000e0050160440d007600b640c0d0030028080341401201680c025960f41102050700f90f8052191002e0070054a40d0300a41d494040454103d2040000c043d00700b40d590310340030160001c10b8007100d03e40b0000c0004103485803406990325030312002070a12100890b0b00b071529400099404a4503510901e40c9034040c114012885c0d00e0903480c100c1d44242c010280e4854103c4000517580e030300c00e00599500039510181402c07114200a480c180765508000e04030740c082403104541c9503101c2e510000e065070019003981050303076a1501c50090300701803050003120301000c55050901c0b68103078082c00840e5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 649200719 1250 649199469 649199471
    0x1022a011a0d020616080f09010824090403050c0601060504061704020a120c0306020c0d0f05040e070509010c05100c0e09010308071e1a0411040e0601090b041d0a06 72
    0x1000303a9034080d07102001c400c5526000002101c4000151611401915484000ba280f810440d07030650396500031940510030100784050086107040c803559010001960007a01480e080e0810b80031030300003903800081c142030a0b204460050025040511420a5610f4110400300b12850b03035845460241c480c6d085800350900041480701c940d10141b205620702e90007141c000c0c040c8804a4100350f11070b0a9800d4085060b500340d408104000300152a503c0103040d1000307030340f02410045005241c010301d0080d18049100c20414244024880d400c0d007943e241d50403442a05100f6602d2000c000140e41410081c18080c2150013260f400c0001040240c10040602d090369646000082c0c1420400c11108001c2c000542880028082d1100040508810760354a054514200350742440301d0707440c644201800e00c0d11400c80c00e464002d000c204410501c50320b454803400c81e0705100381168882d03511b98940b0140301700003c0640312940002c860711260300c40c00500d400d07202503036a030408444289a403403118601c115009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 649201969 1250 649200719 649200731
    0xb030a050a0519020c250f050a06021018150f0e030408150c070c080f010f09050a1212140f060406120b150603090a050d0e01020c090901022a01 63
    0x40303a18490a88604014011114611550800040250041a00c41c2d501d40704080e8424045401020745540c0321140311041480d041c07c28016858a00c03003540124000e4100c0e100500ca03058020484145420891000003003244030f0800742c2c190072603490006030503048070300024242405070b07030010566407819000502a07440c030b200d5201d0390f070302c914802c072841604441402f10100d580502842e81101c92018440d003452025101c200844c503c41d4841143c0e0f500c940c1302c20503034440a001d44500b540b4000d00400941c2101e858154032018051707401082e0481d030312242d41d140c50040240d26507400c02c0103002c01804001e900542490030081c0c60310485608035600042e000d2501d406040180d0f000213603102d4401940daa140040c405001d400080c8007088080e0701b001d29150305d009580f02e00c940c000188150000c904080d410b0040d402c503001d0404c541d902e034150301c603600004c0e00010f440040e07070845202da540160290080c01034070b01d41c0a603400d50300018007000b1080728059280701c070540c3c001c1004d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 649203219 1250 649201969 649201981
    0x18160801060806220f1b03060815060402030604060801051503061f030318050d030804110d080301050f0312070f03020f16060e060c07030506180303100b0c0f06010b030a05 75
    0xb4000c8100d40e143d5004070a5054801c1060010f1a044000401e0220209414125400300000e58030b1000c00c615044084131042c1400710b5040c00317088010300e9501d001d400c0029400c0301c00c00c40048001e00752400f540e0000040f840d00e480c0e81d40709000801000c0300800081c24081c0409001700300e8440070074484e22500000c60511410300c02c40602030b801c4500711010651441d5000d5070800d085090a0144041d04100000c5a481e4860481516072082d541e45010b850685001c0d04405110640b840c020000420040e000402600c12681510070803254001a01080c3c000203103441c0c5548512128502c021408000b04011061458182c0d8829001d5038004090070345070984d565850b0340520480b096214040000b14000c130043c29180e83c010305898070b4114081c40282c0340030190741c01101d5540c0494100151840c1580c2d0760000500400050341c03031400c0040d40c035121030b40103006111100400044011455100300190b00021b817101e000d4600b02c2d0796a10900d1580c2d042120b00c66403060401000509d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 649204469 1250 649203219 649203227
    0x70635010510140304030e0111060f01090c0e030a08131a0903070b03070801030209060a090504240c05120c04080604030203030402040f1413080d0e0714010503090303070e1816080106 80
    0x160080744680604d0035980c0f6600c1c11940d1030302a0b60814144a1510103407070a500c3c06000d0f840c4075501395a04000700f5450658000304644c07640d10b0303043c10881001c0903a0050766000c1000400203030080c410075290090545440280c0c84280d200e402e124196402c3c0b400610080006000c007040110241d6001980c0ea88a1901c41d1000301c034000001802a4011b00041c605890116085400504036012503625030300e4043c07c580741501d0a8402c170b64040319104403c2c110659810140305415002d200c04030421502400c41d0180302c650300c441e2440c0b0320004503d411030100fa60000c0010700104d42d01414a401d000c1d4480c3c1c020b075003c2e4019401c2030225260131115024000c5114241103a002e082d65800e201001c0c00c0e070707102c00101e03000328017003248000c02c40b498020f112400703008001030030415180c401e0310002c0340c4540038002d05001081c000c0190000020081e65484090b60400800181150001440c0e10010803c6014600320382c2091008600002403405480600381e101c0041d02d980f602c405403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 649205719 1250 649204469 649204487
    0x3032018030c030c0d080a120c030203040203011127060c120c01050f15010806010e090a06261203091603030305010311030c06030106050d0603120507031808070635010510 75
    0x25420041445d00c2000054003403006000104041c40d1801b000840042c1003001d550840f07102d0030000c1c2c0c020041c00258902803007104c400c40404100741d481d25100c03d804203400c842042c942d02c3d80005210740c03010203480c0d030310403070302d0340200b540a17140c04101600300190181c010140094803586441d0004260300c1e40928440d015146c0e03910a200f2a42018004561040c0021b000c0707810001c5107883c044541d01e50200a900803403032050045281400c0110b030300380314440c031030494880c6184a4598091410041001e50030b45004c142815034907030b00c000395a490000000c031090500341c0302c401c00200345640342d80309a040c1c0b84181c403a201c21382000010181d0760020748035030b50b5000c0d030104010030540d8098002002220110f40020a405642e5201ca0303180300303460000440810f6001401200b050740c81103000300d40c080031050144c2200e0070544540c0d6038a00c10f00504013801702802d0b84e00041c8480f444800e803103018114040150182d1105801d55202c801e119960040050004d0720102c0c5005060710 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 649206969 1250 649205719 649205743
    0x90201020304050409021305012403050606040e07020307080d200705070504050a0603080f0405040509030301240314070201090201030f020715020f040503060117150603030703032018030c03 83
    0x150b0070181000c0411008104100c000c0380d00a60701c684e0034030008010b0103224020030940203007100f09110340ba0282003d040c50a507032420035180008202281d80c4130401c2c2c40544031116080021991200010b030318501c216800a1b114104c0030031050a011110703000b81082022580080c1c85003802c2c10426011405000030007020340e00704920a0050781400d500080d13000c190048081101560f80c3c03210300701036010481c1c01321856000101070260f400c060203203541101b03c22004500d558503100040d02c0c40450054035008a07003540f0402464580700e5000001950040f6810b5011401c0c1604084d00a203501c803c1207012a0401c0500400008075100351900d42e90488007500c0200349030292180294441c401182c102d89040c407000c00c95403820041c01c0d0103407011042c1d85d01480d00c41c40d0302d07038540800c0382c50030b1124811840030028161404001c0c0c40c00d1540c103042c0490855440420300c11b04a007103000a0300746a20100310404810101881418802ca0a17000d072006100b803a0300b4580c85003003072610 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 649208219 1250 649206969 649206973
    0x303041e050619060906090b10180303050c1219080705040803040b070f0c03030215090c0109030f060605090c2d0a0f030e0a030909230c161a071209020102 68
    0x29000fa040718590705100109840300040140d05c0d081124112101c0390032002002da610b2680e020242401100f2002e0001e441c00c00911119055403100200105404000c04100c0702007103280308000c00300580b20b44400743e1400d15807100254032404001100343c2c040407000424103c0403515103801031701200c05841c00ca8000d503251500340201c610540d48007420031640b01080207202ca0119000450801c0698403e50152041c440e070402d80c00901d0074050f24080d016005001040c2c5240e0700450b0000071a680814034034010065424030034000c00450344031540182e050f004212440c42040002e001c101071000c94400c00c041c050180c8200c60b400b0b49100d00306000200100c03541c45003d031441e480c0c0b00c0100c0c980450101e005142d100e0a00c0200d500841c089541030b0414410200c00e4021245006000001030f802c0081503021845140000703044441075001c0000c00e48130010366002d103500070582141e6401070688500070982c3c040c50085551c1c40c00229003c2240c9040c900f60301070742c80c0c0340340c050340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 649209469 1250 649208219 649208221
    0x807110c01140c0106060206100b18010e060702190503100204030f0f050709020c0607030b100905010305090f0f0303150901060503010e10090507020a0c0f05130b0303040806090303041e0506 83
    0x42d41c030607603801c2c0358103640c1109210346820f1800c01d00841c00580307240c0c0d0180882c0c1c101550081101407554021400103002440f01031214140150301d000111b209190090002e180b0b400070602a00c2a920040d4008420440c0c0c401440000b070741d518100c44050b01160302c80072409908100728016400014620181e1075142c07008103000741d400d016042d010304140c96513a5640c0181c98103d900802a4065580204040126654141c806e500c064802600c080f03564410140005040c40380c0c900400c0c0c14140d469000c11240704c001c015801054444c40d007203a444544a110344c503a250800c0340c484800d1500381c00410003900b0b00090690490f00315840311800c43e401c000c1c07480071798a030041c641620001302000003d041c2c001805000d00405240c2c0252210580b9400c04030300018840d001003124003000b0804000b10788810186904d59111034100241001404001030304600c62903210401d00e204800c14002c50707401c040011030081740301d298880203501e210401000803d030ba5400c068881e8010700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 649210719 1250 649209469 649209493
    0xf140402030c2e03110c0109021503040827040e15090106030510050a09061a010305010e010b1605010e031c0632040e030301090f0501211e0204020403080703080711 72
    0xb000403c10510078100071070f11a0880714402e840390000380c00c2c01440c0e03444006020a50030511000544031a50618061a511f400d03100e00c1c02c984610080c1c5821b00c4003481a03d06180c0b241084034058103001481804603002030609941d4130800500c02450f03c40c2a00c0124502e048148509000c0341c0d4071401030b26400340d8003020321000b80390042002400b95101e0707041c0000941c0300c1c400c2031a80300c0074840407681d060045000400b100d0058009068080c40300f0014884812020142e4440700c05c0100340c0d42c24030205150142c09410001c4184110784800300d030060000c0945001601c441603101400c12401f681c4041c8900310782074a80750155540c2a400700c0c50450005961101420600540042109200302000134690b40c0700344e10800342030741e8808030554605d01d103000302e0780144000c2c81c1015141200341010080485001c100078260700310201c101100780302d1088410301c2e8940061085496941d40c0c10304c0d08480c0c2c0100000c800144448000605107401f8400210b0124903a0008100110000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 649211969 1250 649210719 649210789
    0x10b0405010c021903060501030803150306040b16021507020f1c0509270106020c10020606151b0a030c0606091515030603020916110f0607080a0f140402030c 69
    0x10000050405004d60010001c61418003e240c001d5203d01601640c0346000340d06154442c2480000a102e60088028440494030004007560404009113219946140031070060346844149d908100302d010080040140c0aa0003049015103910600d0070b40d8003203092610b03034070f110106494001001c11020300141019041c0a02401c4488442c84581c43c602d241040f80c1400d922826404007006038040b01400a032070074065003103a80c01d1654001404135003041c0c0c00281c02030a044c0c4184d07a56030720103d0141d5209900c054004091002e08017910500c1180e4200280715001d100002d582d07860a207180042d4a10342480359420100c0c0080603042c0d050b0070011003200084c00c0c1c02c82c41c1c0425032584030220141e9902a1803a0044501d018002c0b0307141d01600014103031f645030781c0405140c0c0d000105544404400424825405280c2e442c180596503242c40d41348004252029501045034070340204a440d180400c040781d07004500840071240405a5070003001808140315420030315424007854022402042 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 649213219 1250 649211969 649211989
    0x30a03020a090b030a1d0714060703021c0c0302070605091f051c02030105040f0b0d031b0f030302030405070905070903030c0c0324050604150e1906080304050405010b0405010c02 78
    0x707607203461908195100e8400304960000d0310381450607503440031640c54240d1007000c01c0003200d03900380240c0070503490704050b82020b010301c40506000f0840050200c04252083c888050566a0742c1100c8030b0307082c081c0c1c40040c16200f902c2021400761080b09000714400d4098000e440d00808001c040300c2d01c0e0001e03125141da0880140c1c00c0803040c000e090040c03108420703040c011021240584000162a585844200403e540c2c012022407525450002ca034a16a20791607040c810b00d07074050401d85000f03035816031420000745502c0d01c090142c03132090310003100f0154590000d5001d14007880403502c145894290030b8040b0380007a03d948001c114210340410000c2d0082415914030350042d8103989002d23540c2d0311030307040c041d52103410b0241d10319007020300d02d140c55414807a65801c07441c00c3da81009034040d40c6a1401052a1501070b124100345050001100c000b940c091001e010301070304005004041d9141301c0d80d03560f44c2050003001d118038180b4001207030b056200ca00751000c540050796040003a1640d03800340842c142ca = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 649214469 1250 649213219 649213237
    0x1e150c060e07080318120307020918011b0f030c0806130b060d091203090803183a11120f0f07030203311518090510060c05030a0302 58
    0x1840d42601c199802040c442c2000415a0394065940da0722620340e59500d0b040d14024661040340c05486101030748070b000003038410725903040c1d442c0c00302c60300c0f504049050708503c2c12503041d0540c2440f4201201044560601880d0011500c83c0c50482581c0c41051301a40c000c10075210008862a00140282c070302010011011101c0c40b40000341c0d50480b0740462601d034420043c03100e016440e4901501005000300c7c00d8003003403040d464108020707091640c0e240810320024110003804801016546611031091042d50a0130348407084862441c00e4011a156445102624101700c01c0d100b2014840b01c1806041000745421810000c0c1c109000055069640d6422880c460051800c05120b40c1c400c10624500034900f85009070001c6484035042c101d03030000a162200a034051900030140d07489119054400d9205460103010340800241c200c1800712043c103484d903500c0c03e01010325940059150700a60001c0d000b0f051aa40f510b48481d00c0d40419903220342801707002015548108a0400250310a030b020700340200f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 649215719 1250 649214469 649214471
    0x3030405060a0b0a030b100503061609140a0e040b012301050904020706181410020c0a0b0603011e020904060b0c15090a0c030302010203060a06020706052203020d0c1e150c06 76
    0x50710b0b61182e5040b03020440d100b01c8051f070340003000d0149160801141d58003113031021509030121501000103107494041e10400743d03034040040610f01ba0380d8440c25060083d04001c5940141417a050800c040b13400000c3c890225800510812140d00801d0210b040382c101c403041c1c68031450100d0200a00000758080d0009582855440004105200e4544c5481e0031711801000d51a1701c031104107040b6070405510794051600144100401c901d040c40100b4204105a0040103480c4283c2e100703c042070150a5074820b1012050800d400318590342d5140d40980750101081c0d508004940d100c0b807e41190303202c0c2d00d42d002865030145c44280b00071500c1c44501c903401011202958010f514503600c400f4840300c03e82003100584d4000c400c216081c105802c0d09802410b40c0d100503c4c4540ca081c2001c1e015120b40c8122541d08880301c02a80d000300c1280303c058009550180a1000b4602c05040004d01c09000d0f0150308850f065120001e411060700c51401020f80341300141141d421005a4410b4030194086101210b8203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 649216969 1250 649215719 649215739
    0x90b1b0304060206040c060f0f1d060406030e0c040203060105091215040605090c0a0f060e01030905030a02031309020304110f01020c0d060e0c04060e01050405090a0606060504090e03030405060a0b 86
    0x1500600c040d00c020025038009211a080c10300d005d80090100f60085005c2154148044200b40e0748203455505480d034504241030b210754000004c0300000c10784600c158211300002800190b0a03410b60100c0c0040c0c101c0b806407420a0004010401030b4401914494001903051080b02c840340782c010510030341e1214040171901000028071907011012002c48040e034401d9603501c200701103100e007401102034144c2d0464900c00c100e82040e18800400400d80612800c01c01d1121800d40c00340d010340d00105040c0d82182c00c40ea00da4218241c001e58030b0740403d4805d041c54065a500080c440034900a981c02103920400b401402261101808008625400140c1c114840d01c10f1880664540c0f030103402c8414014400400d1543c24100802d281030b10340081c440c0564034041040103200c00b60020281911411180401c06488000800d0b00d05918644040c0c079103890014009040754000d002071044401558041c8a07000d00d65910940340e01085601400c40e403c0407000800400030b550200c8d5103420010040509 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 649218219 1250 649216969 649217017
    0x3060b032e12060e06090d0f02070302031603050708062e1d010509090d0e0d0f02060307050a08070306081c110307082a0d050d0914010c0e04020307090b 67
    0xe80c0c03420b0344910403400004410a040c80018003c1c2644003042000400240c241054203e0381e03000e0740d0840000300202c10380d24050751071081c40903000841d0010f088588028481c0c16400310100140310444807403003a907500048183e8003150882c8a40356680640349105040550203020508001c1c126118000002010071805001448012030f40030300040d481080d810705040c4074071600040d20040050780306049540b44140e100c03041c2203079000d0a41d902100301099140c01003d842c44020000e5011801004204105506c03201502c0400d0890fa503040c455110000c0039030840b4424006e441c0580c000904050302880e03161400d002c4a009071801001004905c1842411900b140200b00c0e0020300c00201210101c080c89c48038201c1000c808401d1842c01801420550380f085044080d034140000441d41400c117058941c400341005d50403581c42c20710f603840421210300911b4660440004510380e11100025402c2a20a036031192007540c490b0100b4500781040e440345c94000144030072440009841c001c070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 649219469 1250 649218219 649218301
    0x80d0e071505120c0f072424060507080301170a061a010909150626130210140301090e0304080703110111010c050301050603060f040903050d0c03060b03 67
    0x800c90300d1550b90aa154001e50084140010028240e0032250405014000030f4800342401c4a0105a1180301c00c17080c102003d0030303000404da1010801d44054070b045070080d5544031080140702070b14001c91302101e180ba1581420ba4041c0518075001c0d080f0b0f60113000610035214080c0c040c0320700b02203020440b142082c0782d58035841a600e80c04003044028600403017004a558001c1d43c90400380c02400d10502400032281058030503100913110f100704020710a0300885a0205d14880c1129070140401d0410076417808513880c1c81408904101240108148451002450707c100762403091040350a1100e86180d203419011303400b07021204080c001900003000000f5030040c1c2000600e000354400c0c0750181018031900000761400800104006040e4105000000704540c00320440703041d02c4088445035100c0d203e45000c41c240d14422200103422902d00508082491340107005400c40100720f00c018860f035010488110180e8200d440b4444012500380042007810a010801200800015200841c1e00480d0301901c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 649220719 1250 649219469 649219499
    0x130209090102041712070803130f051f0e060a050606040f18051311100e03010c0306091505030a0b060103091b09110703050307030b1203070614010e0103080d0e07 71
    0x40041e94002010455501d51016900c0c40e502004003903c02c102d010442202c040c0303d54003004218090000c005226007010500301e2a02c140c0100039641040c000707103003a1b40c3e100340e032140ca01103502042c9248030191100f0b0040000d1040001d02a0072151540e6440c07001606001e049254044014480400d59410074110080245010003030365201d82c010301c5400088510140c080048244540342d41404034502031400c103038021054038407540c41c100d41241207400e114401c1c000f69040d401c006690003659810380143c826600407400070030509400b140305c141c190705140310b0580c00d0341141c001000400c078203500c0303164016010304000c80c50010035955030000c0c0400070422640b1001941e024408030215106403011100c007228450300d8068070752005411800f00900420070107450b42042c3d001525080c003c0034400c40d00004407900d882c0c2e2450028083d007188000c14200701c032403100004224a28980b51070499401025440c41c2000e98003681000c0d121801c04503116208442d400655499601c2010f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 649221969 1250 649220719 649220731
    0x120a0b060c0606090906090319031127010306080c1215040b090d0f0815030a021e040e060408041a040518011508010506160c080a061b080c070605130209 67
    0x2c0e0800745414804c2180102c0040c0000c10030754005402c0010f1900700004440d9100e8842041c80b0741c0e0700c01501d0883c09407903030400c004030a10000c9610300b51002150f640c02940c0544010389000d603011003004404995140c030440d0702d10b0b40320310301d81c150078200a511003003004419001d0ba003c40040b0341103c01c038641c0903203080f00c0d4510314004229588509218900c822f01061421400c20300064100400092001c1c01c20313402071440000b4078840c0d80d007c000ca40c8107240d000d480665a890b40a0510035528800c0341114081c0e810410517407024030003c12007e1280d980441c4490800303080a00c04225400ca41224040030708042101143d2542c809640000d001e0200030424100e41c1402d11443c0300704640400d20303007030043c408014002503807070f08140c0d02c002040400a20315039629003007102c5110141e030300034210b9000f2a018032092140c0d0341c10108482000c40454071080da441e400840710302c0c4080f00c020364241814880a00001d0040e00269080545414018800b80c032030b80016600802c00c1d180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 649223219 1250 649221969 649221973
    0xe0a0b160210031404110d0b01030b0601020d0513060516062c2b0210060e01140102070e0705091206070c02031b030c2701030302250b120a0b060c 64
    0x1003802140382c45000340003812114603041c403400c1500c03801d982c824030b40500000c0003d0500950902a40c03204405820800d03006400100c131075959042c2041d1044d4140d0310180103028000900407128010011036800d000c10900b8000c1c040d140c05401c0f2025003110074040c243c02400c001c0940840c40e540182d450308075481c83c44800c500180400c0e400d0700c044032400304030740b904031401c0c80448a11055540c43e041b40801c41c214003407030409408074103140010b944442c02c107203803600102c1e0040411000c64142c8034485584648070310340700d0040e079449510703200312407058019a0020b0031a510a402429a5500150400d06000704001203141041300884800e40081d00300c0c0c0071a015407508011a607900300c2d505c000305800240c20004a0f840701640030529014a0083c0442c084542070901152100ca80d00d907050209542c40c0c1c0783c020f4442c500380c030390001c4101000d07410381540b42d030b90841e5500321001d00185914016100c4417040802c000289502801035540300250ba10b6207401c4020b01c041860440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 649224469 1250 649223219 649223257
    0x6240c061a030a05010c030f0b090a0e030f0c151e130c150e1e010c02040e24100801060501050a0c05280b0c030402030a032a0b0118110a0e0a0b 63
    0xa401070481d00c03000c1508c1c5840d400c1c034410a07640c1d00c0702000329070001d18008005c5001945240401e145105a0716512007101c00015003501d4400042a8805074458030401d0110607250b1004c05c600906414604003e01c5400e4408240001c9401ea1080c0720507100e00d540032201607917100e2182048140100c0c6002040e9002c0240c5914501944001c4c00e80c044040141a41c81d03403100000e04140566400a020301d5490103000d40c540310400441d171f2100b82d001c204185c41148c031a41803030305c62415600314842041e03902e001300d2140010700070030301038410603954181802e81010080340e04c8900107034282c500340165a03800d9041d2810343c8200c3c1c1c0394204101c0f0360946507454546034212502c000d0a82101c14024001e01c40165404140101c220750035140c000f43c480c02c880d141903440d82424401582104944101c0c20400c40d000004c01e04a61001901c090304400314450795050381c4064000005100c01084216806805814218066100a4211a5400e4450310014180e5000d00d0b00481d031180780352 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 649225719 1250 649224469 649224491
    0x10617011b0203180f0409080c0f0706080f04020d0b0a06140103060b0d230f04060b010c02180910180b060d0809150903030d06240c061a030a0501 64
    0x401840e1040d440705041030511201c00c41c0c000d4403402601010b903c420b000c541c41c3c154030380d590303c204450703400003d2081040307002c240b0b001c8031070703911040342500180119004000d03849008103071501103a0103600c403140d05948074000c0c811041d2000f8000ca9024800109500c0411280e4400300e214a501c9040000d01c2424807075400c0341c0030380512149041605109092029204407825141d030118a5080410035000288050501052241c0c0ca02c00d0f0300251000c1241d50921101e001d8056802001c08110b03868000c001180e0403010b100019402c001501006031203a50511500d65106240900365040e8003002800e4005940d01010a00a11030304407540c0320500264440c80394000000b100c00301c4100350070740e03540343c4a8090152168855107260b05108441d0080c0c908441502038001e06590380c4513003640480340140014002c0072502c140c201d00c4480c0c0341c204e280e0040c000016640b070b01e03500b0341d00d11303a507000c003400c080014140032500c1441113400d991000c00041c1011403295001007090340101c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 649226969 1250 649225719 649225721
    0x601020709020414120106080d02032113140c030d0207151701180f06060c05010e030a02100b04090803040503190207030804030303090c180e0106120b06091801061701 73
    0x41d08280d074102e1041004004120303856245203070080c0196030309640401c09032001c500505013035000342d50b280107105c0c0a441b00e66011005116612042ca020140181159214440403c0444014801c0e440342c080002c081200000f04418210002046807400c00ca00408a410701c000c80c0c030100d015902c00c0500b0700441c0105d26000c08402621300e007110004810354003511301a40180b240d1040c3c4a4502441004592150003401d02c0400e00141440096980c1d003008082003c90781c0c3c160380b99441c1c0340d00030120071004400c88044075010b90040002c064040000002017110070310180d4010303500d500707400c00111924041d500c03e5015001031038a9910309070a100c00d0f02c207404801c100710740021906000003032450056400392070301481d0028540e48145400081c403421030700500b02c8110103c40d1810001020740240c280020b513003000303003c250b50303c05110b44140b200c0080100506503010009001d4104002100e45c440e01501c0d81b52002081c00c902103007126220342129140052106141e2140c46007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 649228219 1250 649226969 649226983
    0xa0206060607051f0204030501150612050f060f0d0507060302070209070e2d032a030c060f1c11091507050a15020418050a0c1b080a2006060102 63
    0xc141e421030b00e407a009a459075180c10040d41c800c1e81c00014609580100300c1e196050320302550380440204415485001c1558001c001407090100103803080040807142c08003409a05d02410840e0741031442c4e51100700411200c0c1e414040130581040185281401082e800c01c101001469607480041c2c1c0e403c0140140400b069004044d04103100740001d0f042c1044d03d40408d00c003405480e00b802c2543c104040d0001c01203401006141681c588a50034402d25441d4075407994800c2c00441582803588141c114041c10f403920301d0b12603840d511060030311a0440f82083d50000b45034008890002814044201c100001221044555150240004903010b61642003c281c1c18004c075a036034521509200007541d442c3d40e03550102000a0180303412103c45580000c441d0140c0c2c01400d0301103c3e17015422034510800d8002c24085503241241d0f0b040182c00f00300c1600a28034844010000d01e42080c500c5415200e003141f0783d00500c1c020702048040c0640035072070f003c01030070414060f020001800c0381c1e00f0040c000a1030701c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 649229469 1250 649228219 649228231
    0x6023a080903210105040b0a03030801030b040303091202070510110c0616020d031d0f03030327030c0318010c1502071104050c03180105060d0605090a02030f031909030309141906050a0206 82
    0x11742c8c038400e00110750444c900504480d40300c90404816034172440c0890140c016504010450300c403030105202e8851b000700e10802a07a0341542d0360503003082540d00c1224002c0f10a03220a1194010319560321150910100a0542c050703468810b080c4103106174081000042114416000034606416491100b2401c5003401120b4508480040c0d42c00b5004002a450380b0000c1c01c1841813840c1020740707600b080c2e4903403451402d0a4400702070365112030900641684031791000100910b2000700500f441100d41c0200c07544083d2a0304104009606145886e40d000298808101510401240c0030702811503075440c09514032070042a9203503503e030b080c8003024001c140b24600700c014403a41000304000c555100c0000c0c0240c0315820440c007080b5070325400b2003113003003016103800a034060090358150000c40350004010f1030390284022460340c00b000d10b030034101d031405400c0c0401130011307004440c03c01c81e4041301c0e800042c94007002840c4140d0001640c4281544001603848080030990215082070041d405204042e8460 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 649230719 1250 649229469 649229479
    0x3042616030c0909111314100e0103081308013603080a1a090406061e08060c0c190c15050c0c01140705030406023a080903210105040b 59
    0x81d0a5075651503201c0b00038000c80350501d5807034840c4005d0202040c0c3c1802c0340c00c03010700303d403052a81d0800754401070480d448540c541c07240c081000c5000d440c0101d041c807003187d1402c401e00000b0b90966581c1d0380990b0003c01d5141113100c5001003c6011f500070300c919104010505502c05c40c220078228001510031902560b01984034860105501181c0c05c664402d5201404401c00280380591501001d00c02a034403032456001822041000200301c065406a03090b10003481c551120b80e0340400c5140c5a010281c0504146d41d0420400b0802000e0341fa0040e00c207056005055035943e4031007244500303030020031840545110702002001c0180c00c0c1d801d504090542c1007032920925142a030b1003a280c0d81d4000014032410402544511525500ba20055403040c070307031020969646550b1618001d45da044000d8000d4598800c07203608009041c0c01c001a8800101c030000030741c0d118820440c0554500c4002000203070a800100075008010100c003070300030b8229400422120184d4101014003044a441c40949030082e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 649231969 1250 649230719 649230763
    0x2704050901050906070f0507080d020c0609030c100c11060f010f05040b281a0414010f080a0902011b060e011109011b030306030209150108070e0f12030426 68
    0x90f000c901984d004c107041c28a80200189001c040340c851042c1a4080d040e0311000c03540040c081c105400426185c21500107c961685802d81103d48074480c900c40c041d0194050b1140c100300c890503803c00701441020f8201184840710302c0e65110b082c60710445040004450f14001440003074905000c820203490161b504000300d120400c0450290400110fa05540c13001c0240b2890701c5800c04c04a81c00500b4090003403403180d451124001c045a04140a01d841c1c0d40205d0765160f0071540b0824040008140660364100c0c5030300ca981100c0000d003c102001d84c104180c400d01c00345103c00d072961440c40c25119500000d42d02852010b0b175802c43c0c16040540d0a882810804003e09030380c000d640c00c4003c2080e0307120b1210484d40307207010740042c02c081c0d00c020740000154042100c0140c1c2804040546442030f02c868043c0d0742c8075a000c44071000c1640c038207a4000f0300d503c4000042c2c1043c0c903c01c112070350100100c0c0c1c907007a00e80803448080300380e8040701224006e00d20f2588075081010320007110066900c020184c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 649233219 1250 649231969 649231981
    0xf0608061b19022a30010204030f0b07050708071101030f02030c0d15030c0b1309110309100e100c0c06052a0c0c090a24210f0803060105270405090105 66
    0x1071016040d90140341517000c0083c000c5400c460a8403401c1d02d60001c0000c541e5540e80340390001545202c0c80c41950b00140038000a00f4003030044049032040e40d800300a192078807075159941e81090b411100031a040540d1030079903401403480340c401180645e0072960410385403902d1801d5003090710528840e0307183c3c00c4101d200c1040000c1d01104940141c40c00144100c1d00c07141007608150009109a204140003400d205440381035a030844029401007104070255a18041920448000c1d2101324440e0f000581c042c11007040b402c925544a0184103525140803100300b222900c80c0b4082d0f44d02680c40c0001d0041021001c0300310741002406454050900b014642054408200151981c1d1040e40d4240941c010074000383d4618104c0e0f1102c2c1d40c0d0018500a034200d0030448411804944060042c00c3d5546045505145d0319501c400c000c0152691013909510700c10780a640c1c0641e03607000038000c00e042c444d081c0141190401c041d1000300910051300201d24204000d40c01700020360b000035245095503413400040c003803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 649234469 1250 649233219 649233229
    0xc0d090308070f1e0602070605010509070f031a060d1a0d030e041d030c0f0f0a050615270f06040b090619170705040f0608061b19022a 59
    0x5030082d00d0302c1624620340c20800c0034001c1130f018640c810f8902102000801c030181d406428118040c240c10001d580e00d0780180b00d8818015513211002c1740812402d402d0007882038104240c0c0404511945068889d4800400c2c03268000c50740b00d540841d1600d40007244000409414451843c048450100080d00c03610040c0c01c005159584038040d5445800c0d0300141d0303200039803c420030175610b0b04803951102008901a1220060002c1051a0080013404001130400244d802406900f09000e000540c4038031049202c00e0003040103042d0081242c190b5071158180e15000340c0312914000b040c03580d00385885004240c08102c010039252041d803928040e9036942d01c903c007166501c00001d541c2194101c1c822010103002e02041d51218032185068145200000e20101e414021540291414414401016650b2041c1c44040c000c1031140e40c01a030018005088000640d480f4001441a492400b41e50b59220004070300e020300c041c03002d0380c000180320410000d40da5143e02a02d800488400003641c10b100060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 649235719 1250 649234469 649234477
    0x207120f05060c0a0c0f1a0903130806060105040b090a0f061d150d1802041803140315010f03090605010f14030c010203040b1b07060c020907021b1c050109080c0d090308 74
    0x1034205040c00404030100154440c0403641f20005009140c41440c2c071160440e526030040c41601001c0f050000c0008582d040021150f004000c141c46017420241429010340741c9821079901c0c9540840c0c501000142140381d0019a80a0072540d550503450500c45509030b403a0041c0a01903e0003010140001c6040b9038004041c0c0e10020034040020030045425100340d4094800038030040d5100345001030400c02001d41903a84400d1503c6030b03e0303919502d4010040105580400c80b40380e001a800034041c40340640c030800240c0214222410300107161512526042e04650007604840f41d807245285052100b040c107401810314802d0114020183c1042030340000f0749230300991040e9030b00480040b4201d102c00d01d81009008940041c2070480e03210070360340c450041118410000583c020141d078800318031200d201180000d08000f941031500c0003c00d64005004a0608003000c0c00c1510000c5580d040000e0000e010320041c0c2030051100d5900c035071b02c528400d410000407101d483c2c140020304a0030000143c168040c0c0e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 649236969 1250 649235719 649235723
    0x90311010f03090c0803030106110c03071403030c010f0218060903100b01090b0705010501051801150804150c0804050d030216110409080708030a0b121005070207120f05060c0a0c 78
    0x41e1140c4070121205401410300c400d0010505440244082450940080914100c3d1207a50300c4184012040c0041030b200c08803d40c6c3c55406402c4450280440b40000a61042505028003241d141c114824040d0b400c44408c0344148480c603070009416040014803207411100b952085410b1860111050b00099079802c1a02c202c1c04d14a03250f00e05005681c0c05603115000518280ba040d541c1c0d800a440c046000b031400f4082c4900c10a4460b1514400c02c0603900303540d050381c8908001981c03201101d80242c030a088005c204a1349250304152003641d034042402401a000c650340c450003a141041d24205007480340f20b2080c1010144140828001d41c8000c0441503080c2d90041084040f107074880000c240604030301000544a52000076480c01081008002903101c4c1306104410000c2c001040304000180542d804411401d500c0012000704040c203036846907401180a00468801d207a03549503180c4000d101c3c81c1c1c2641c0c030403c0010b079107052100034480d05034000d113800c1c4402e1410195410181c0359413000200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 649238219 1250 649236969 649236977
    0x120307060e030c010609021e03100924060f020724050c0307050f07061101091a100302120a03030e0111030403112404060b030a0305091c0f12080709031101 68
    0x6103982140d020b00840f00d00f030301e05000900c0401d45400e2824041e5100b04043d100c071007100400c041c80300b06014183c80c001c601000c03107181040c0c9001c61010140c079007500c030b403041c244004410041d1140900f61b0b100080c40c2c561203110f100040c1c054060700305503c0d036110360000e03075421a0010f204100710166000f00166070a0242d11005100d40a61544c040d0035001001071040d02d51001b800300000501c0c104641181c3d51b08030a41403155991030036510358010047c090344001111442e44500e480d01150301802e0110350740315156903600043c80c0c0c401420081100c5130403a8108406065050182142c4845084000d008484607402c0b40300b141c1c4001080541000340802030182c020505010420900c84000300e1081030070f42c00e030030500f800300043d68101ea0b080d01d02080032105040202c0c1d078007002e9030140ca407682031100c00d900340b00074500741c2c010001041513500740c5207001174004104424058016050001c419a100030040c04031b0724060285810701680c001d007000001d07100120040d183c802031074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 649239469 1250 649238219 649238231
    0x30112050309060c06060a080307020f0402030703090204090b07030c020106080a080901120203240d020f0919090b4606050915090c13030b0c0c031303020102070512030706 75
    0x804a0071402101581c42e0f200710002600070740c403040050300718001d4104885100817107071b407824240ea8900c20400c0081d0021003500003607060f45000c0e405164400c2c1282000b00740c07003a140d400202180e028101c1115942e8200007842842c96041c4210114901180000c101d4107040c05061175907070165602c01071041c06c0000d541a0107034800e008022000084a030b0641d200d040050001c00445071500041e20742d07031911440750302c1600c0c041c1820b03803078103070007a2920308003400720814082c090f840184850750107800090031203800b02641c414000002c0c001c40450030f107424000034082c0c0745a281c0448502050841e980c64221190400d40c60742c1c00c81d400c6650342101d03401c120140b005400d441c2d0195a0183e5020300b0041c1c1c0103900c1e050503000c6101260055040c0d030f14403944080b58010380d8070690320003410080c01d100041445000c560048120740e880c0782010340c1540d80502d154800c10710494440c000300810401c550301009024040e080843e07450012040321b090b881c3d582c0c054003c01401c03e03500e0308 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 649240719 1250 649239469 649239473
    0xa03111314040302060415020f0913110d020301031b0803030106051c0509032206121d0718050121020d03090803160c0909020a031b05040f0504140f03030112 69
    0x58081c00000945641e4482207282908010f5241c2000315010354002900703404084041d443d0f4402c61f214408030700f9843d414280741e43c083c003581c61482d500e4504c81c1a078459006035055020800f0f0400c001000b2005a40c035815454038142050710150a40300c0d80030040c10502c400a008010b890640e0305619000351501281550109000b07081c1c203403515034038039160520000000200c001c0c100079a1210328005880c0407941e110003220507600c180310004101203401708405c010707508603403809040c1c03c50004640150552035070410855512800d01c40021005402d040d088501455006281c0d1000b203001e0030402441e01d4041c00c0020380300900c240c5408503c601018020420240507005231000c5070b4540c0c0c10141703506001c840e580342c141c4d0001110b16000507203540c00c3c01600302c1070368003616101140746550b03034001e5452208040000e0072009040003003030300c3d01d0b28401e2030842c00d100e040200703503418581440d40d00a800c4816070105d60f040000c0c408040e080010450f030440d505030041d00d45404c0d0034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 649241969 1250 649240719 649240721
    0x8120715060e010905011d090705060703111204031a13020906063f011a070510050702011512020f1201060302120a02150703020a2004290a031113 64
    0x9070004082c0a100781e00200d80e080c09980701d00e0599a401554104103040014020040d00c8100e038022210742c0030041c00e0000d070522130301504603240709040c080c192a13803204a05061080c03000b00442c401501107010014030140d0301452201c111280c4000519041055010f0f26000702c919029005d0741c2c01c200400c840352184405c4032110000c114101d4020b24480b4a05001c10031308000d030307242c00403c15162490401401c018541200c1045800e1069a42d20b10480c3c1d14940240205540034060008401a80300c0c090040f240700c0d90150f1f0001440d00304404031800300a66580080b0741c894000340d150401621fa0009014902ca0119640c500c02d03145500700030701510702500b00942100125000b8210200005074041d8141c6c0708407084924001082c4040603240141000a401a031002c054840403840105020190b080c80310824a650440c04000c103086e22411f60516002c1d2804001c4124400c140e91060071520400703d50131400c1c540386807034100c02607002080251041003c034003144000081 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 649243219 1250 649241969 649241981
    0x1c0212090a090203040c061101060b120a02090a0305031c02180f060405040f021e0a0804032d020604050606010f09050f0612040c060908030310090507111b0a08120715 73
    0xc0b0082999079192030b2404015060b400d100d40004510303c0b0f0002c8400c403006004c0e1006540c0103075049130820601844a0406601c0075101d903485e503a0801046a8503240c5408400285001c8c100a686e1036036441442d038601c09030b6130b0707014505900c103000b8901c081150241803102ca0f10110b0f00744c280d1840450000d0264450366100c030750721615200d0b00c0d506c103051a4014090500e8220904000c0b02102d001c0c1000a2181c5000d00001403d407400080c0046d0143ca030200f0001c00ca05180843c410b0103124014480f80710340002c0d0090307070000d0200f10802c0020401d01e0f5000c4028a0007010703640003004050306405460141e5849030300d800c0c1c4054100d40300c00c0d0540b560503032601400d0000d03003000d00f04412190340e035018442c00122500d902113004880081140e008030101400310501a24004120b00240400f0f01000100010705542829520003000050801000c0c2c120411584103074404206106000f6400446660810401e045032201d2003c1560f280c2904010064180c04010442d2001800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 649244469 1250 649243219 649243229
    0x1507090314150a0b18010807030308041e032c0919110703090501410903060a020d1419110d110a2615040b060c0f1c0212090a 55
    0x40042c01c03c2542c0d20144c02441342d850003a01e060a0030b04401d80b142070a89000d02030b11070280d01030402000081d1040c0c0520b41d010340540b0203c428800400c850020380017242d01e041d400520703010900c52010125039894800342c040402d040c0307042d0300c0100214104c000018548a4140720600011031030012580124042d0301030301c107440780c1d62003a615014001c0f449500a050003d00e10021010038849100000c6910b40c01141d000d00680d0410701d0700145506800c3e40030f01c5080b80501014100b92001c2142c2e80c050f0340d00040150300d07506c007002010200c070001002c0c0b03690606e0190078060300300c4500307206c00c41460305244085200c0d080018011514490381e18045406440d15403c42c0c001070424026040d040700999541e9002a004610500b40055031702400104219800100c0c00801c904031011040380c10180010605644690003c5c00b950045210364070a07402054070050071200c11f1045851201c40740c40c20035208110b81200958501481e40c0e0100c20340e4000502900ea95210624a00181 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 649245719 1250 649244469 649244503
    0x512010902120703120207180b0103020f0703030f0b06160b0a0902150d05070e031b151204060c11100c12060b120c0415051e1306021507090314 63
    0x4080d800341c980c2d840b903d510060382e89800006406050500c0803420000703c440c09070401ca01c800e000e507a10001080344004090505508006056441c0d849801404106019403000501c0050501140064810403030150748201000c10078600c481810010300410103402a640d001117544100c080d80c010014000c010703620182d0386415000d509140c50040940d42140c080620107510b0320242a0345424991881d940d054010303020b560401c000c040c19031440c4201c000c003081e030071010581c1d1881040d4040c61a01500c844140200802c0c49003034002c40e41c1441c4a4608058140c90003e012600d820403c00d040842541310340c01015000d1284100754040f0140003002c03c00300380d685003100b055501803484203110f0140c100000344d003180918281c41c103e4a0b490503000100d8a100c5080b11581d114646002d91110351402c2c0d55161300e103400150a55012442071546490b0418a01034640149911056540d450000c20020600d074000b2100741180d501400e100200401c002c0913600300100110314607480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 649246969 1250 649245719 649245739
    0x20c031b0f120a0f02162705011820220306110a0e0109050310020c1f090201080c03091c0507051c1101060803090d05070806040606030c0902130512010902 68
    0x440c07148000384a4070310540c481d0b0341c2c6034540c280d0590302c81d0a5250701d10981c0c160790b9030811031005c3c0c1c0141845102c04040d6003080c01f04040e000340c030440d1020b8101820408104400181403a201c0c031400d00310100503030500c40c480e800200e852106110340846540085100700c405124035151003081130140d60f00010510a0701310518480e29140c04c078078007500c0020110007036200a0b500500428080c0c17180500640800e13070742c006a400c069031105824040700d2180c02c0d91365000700c610301148841603c511201094452150000400d08480a40748041002007003043c060a00d00000e88281c0c04080c44003100c06203030016000f41c40e103000301640600540544141510311004851030311395040000d495104000b045074507900e0880c0c05a000b00c0d0900d6104220305842403410400142c80107204100b107419103901c2c1d00b0842d05020042d20100c2c1d60701d4480405008020b00317014550043c0c0000d200840c103055000c424000e88410328400c0c1c90245a0007440008103410030340020303022075000782401e008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 649248219 1250 649246969 649246993
    0x40b0d11190e0406051002061f0812180109080c090a0b09040c09061401080103061104150e0109090c020a0f06200403150209031f02130806070f03020c031b0f 69
    0x240303288010a10f4800c40c0380c003901003401d281081010b0b0107141250b004140d1503964a0160302070011400400f003110751620800110003600b0800d0ba80c20705160341d10151074035084140d016108020304091418814135070420303c011000003a0700340c0c51601c1240d6242c40741d11140c40907c001c1c072000711040e4020200d007041005004586c00d00d08200c41c000716040144982d5020b80040b600c03803081c06039000448c445c0041020500c290405441e0714100b107c46850541d94140c00e08802001001c11030202e80e20003c4684a9030700708814000401d10380e04103109140c09900020f44400d103100d03005005100009205051298681c84007182c1641104201e02c981083c0c160182150054031088880d002c0c1a0b161840b0f50300c06000b9512030b184c02074010b11002c245106461107001d07541c0c14a820b400e500f4405034960707210480c1c82c5402000030b140944114146010000c03d0000d410340ca6505050040041c000c82038000030494814030584401d581046101a2188c0d013010b1101c400081184180500804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 649249469 1250 649248219 649248227
    0xa0f061407030c0e03061003151b1d0603250c2f0409020f0607030318030c1e080a0c0203031209165906031002040b0d1119 54
    0x14452034140c1320071038408001030425035619802c0320710b074805010005003000060055003415032103010b14200800c0d081031030340700d403200300520101820006002c041882e5803051a80c0d802e0710090301c00c0d19110b00e07601c0c0490f11001083c91465141c425021400c1d090100e0921500d07010449591143c6108115000c1601d2860980c1d030040341040c00303049040c24041d540c80d00388101c0e01e0f4030394041c1c112000308a0440810066800124041c2c0a16407a143d07010800c24107181303c140302503c070391074480300d004040c20031a02e4800d1a60001090b41804140b1201050f651016075000001c10710303207402a1a0700340301003803e6009202d0b801c800c1004890501c0304002c400308007000450050504440120350724035404e111080480000c2c007081d8025005500302c0160380c5031240300c0301020700030381c40029503101c0c0d011010920380c410b500050441c0d07400e22029250900c1844502038007100705604041c24200c02d9080391141021810a00360b83e401200401c0e0041c40c2520300b26a4540c21480050b001140050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 649250719 1250 649249469 649249481
    0x6030203070207080105011401050a12020429180922080405040b060a0f0c03030b0d0f03082d0703060317090a050105070503090d05010e0d03020d1a030a0f06140703 72
    0x107009800f820340c0114802405104950403541c0c0605007481c035020b03250042d50035a1003262050100b01403030911550420302400200006d000d284004800100c03203900e501024080140c1942041000f0051404030218581601003d20b10844000c086911034692002c00422551699054050b00c4003901041c88180405041250360607103081c0072925400040180a10a080781d07031010071010040a00b9152240f074035444103134031138100014010500d6002401c249001e0204407441c0c42c0361100c0307908040e4818580c680100c01d42500e0042203c2c88a0703e00d01010b080072602152105260004081c5442030308107800442d0044402c02040400440310038072640504c0c0b0f91030243c01c032000c00003807a5201c0c0d4102c0b00400d41240c061410041900300f0000d0703510a0090270340d170341c0d905d400c400407800d602800b0b00018900c090724016070b55025088030100f0b031035175500301066000c41e650483c18261404a24820709541c00f13641c1c01c0540e52186440e000604124048641d121054010000708030b0b01903100c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 649251969 1250 649250719 649250731
    0x9090f181e0705090615220902210903040306050402060d060806041a011a07021909090c050301020703080f100f120212070f06030c0e18010302210c09040f0c06030203 73
    0x24404090b1030f0814044026426a507040d0402d0701c000501e100d400e6041c2c0a84904001455001d414408103d00301d507255510750030031588150300040342e0004040724500d100c0e0040a03a1401701c000d20380001c0c0c41f034a82c040c40c48080e09c507c1d290000a0f04541d5900b04840c3c4044200008009680e11060410f030f0b00e40040301d0841d20740111f4000d80718494600c02000341240c041c00c01540e101848420a00d00c683c028040c1281c00101420074440c400c8006007105000d040d4641c000a031084250070031a160107611340c8014042d910401c0f001c0d0200f0361242c500760784a1080e07200c403091501c0341c1c40451502003a5600410381d801d8a1040810000317590785003440d138a8022280b6240c0c000c080b4481d561118400d1140e040041356082c401c11a00e406504060105003043c00c2032034821400402080714810280100410f55004000620461500c1d0122403402200c6120404000c208281180d91390790500e580310b407058840b40700040030401c10481d40040d80741d004110b800216555280a00650015526 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 649253219 1250 649251969 649251973
    0x5150f040f050f100603020304020d1415040b070f0509030a020603061203030c0a03140618060301060314010c2307151b030c080601030b03100c030e03030403090807050609090f181e 79
    0x605541b10b030080e40d01440c3c00500c00c01c0175903540e80c0c0d2410403c03070890131040c0c140107840e500d440b46c000303041c550b521032030140303610451500c0c040000410011020740d1440c140102400320b40444c1d10f0018548440b20350503101c6981d070352101d40000740304c408040104941d0f07200010030403c40e04150005000511000d4605024160b84e040100b001e80c541240c2981e00324200c2c240307103050420050b0b9181c0d00a2006000014045d841e0740ba01c807400c900100e03580c462a9110b0081640705903210307903041a10903d2552041e940301c0700c401000e00c90311855102400d501c804040751182e41c03e0315440401407440c50000306646907082d4801401511220418001107100d040004842d54081d00803148090401005089018011000e4000030324a040349401016035480e64200d002000b00011800350703000e40c071160381a52400110074036115154001c24010341041c4545074183e250b071790f85150000e01400c8080f600d561507070854105034541d0321083c1e64034880c46507014412408901c00f84601005041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 649254469 1250 649253219 649253251
    0xa080915030402030c0904020613081c021515030c040f0b04050a11070204020d09050a0f140c06030604020a020111040f0315050903030712060b07060c0e0405150f040f050f 75
    0x200d081034001154042d40540120f164016189009218254407610080c11075091443c0f01c1410f95030390381c10b03402240095001140d080c0d500c100c030b4810340c4404a913034402891040124000102583c0024194010b007031242d400c0514281d40c1481205404400034000300810306c102000c0502030701401d24a44d0160749040082080c0c44458000d440d41b4918006c4018905217895007400000e5202d00c51420801d41d89040000000c0c500f4400a4115409400150200c841c0c43c1008031002007242c2150881d0b9018515206d031644030340303082d00d41c401411240140c5404101200f6400351100c0007001c0c07500320300041c02041c03801508007194141c07402610481c0f8009029809003049400a40301c2c12919881440011001d507c6440691480c405d80c03072004c01c04e59990140010103422a0750103c0d01242ca6940380c02c0c0716944000c0907071380d00320204ca007400306082424519690300891500140240381d01031603000e654585030007520120214081c02c0081d0328080032100c1d110740301502c210b928240402 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 649255719 1250 649254469 649254499
    0x70b010915030203060c0f130303030504020102100b09010b0903012a030b0301020c0a0209190c0e010809060402090414031c0e06070203120105091009181e03080412110a0809 76
    0x10500042c1e80e4050014001500c441040d117900d03821a00c0306d0710018100308655081058150880d00c000c1d40719403004141810544006402d05803200f800315000351411742d014201e581c0c3e50490790304444540d9811541e1388003c80110740035207140c4603040c40c84030b00c0d5240701544070700e41d01d450030040e003551383d040011114650405090340705255104040358400d14840c40236152940d8a40c1c2c103e0305032184011144046102401070340d02c8050031801141000c41e00700081e580000312241d10020700005014680b4280d13002030071516010704040d00480c54040325200c22003082080784c84580001c060904d03014024022000981041d6408000900407a400300c2c032802d000106a03008444c09007500080c9a00b4042402030070900180301c031200e00710b10400040d1540701c41c0b140d00c40030031415400c0c5c4440b039940d06106110484600300e0080040402202c503010903402070000303030003030784c400300c080032600c0340d9041103c0005010102c3c1186000d01103444c01080304d20303402459000c500380c0746401241100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 649256969 1250 649255719 649255751
    0xb0411121c0302041706100e01030510090521040315050603120904091205090f0f03030d200c07080606060a09182009010905030a03020717070902070b0109 68
    0x100c49103040380d90040344000c5101e240c44100c0304801d900d40c41d0050400e035691009144070301080b50291501c0d0850400c3c400c143c4a04682034014140c22a141884c0d03500d9580c6583d501c00e0100c80308108035540e9509542000424003000b0200702d042c0d590448c0a0011a4842c1520750203440221603090388903801542ca040e0134040c05104481c003d02404011405501107540c50f80031100c13640d403082d07550568200151600042c00d20b46405a0383d41078583d0450014482e40e8207880081d80e1003080c012418603042e82c2d0010449120489180e80400c030b08036003003002400d102190701c21000d140804104440b103103000090790004c680000007290100d88400b0180700d80d5114480080c07000900c001014460b0394004c400d250380b41d405603a00000c00f00e1140c5221a0f0005088501c424859400100140c1641c5d2041c200009010704802922007500290740107552006148200b452540440c0e20008940b64288500c6004007006282550b41e408a0319080140e47c00c24000e10b8032052408401049801d56 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 649258219 1250 649256969 649256989
    0x311011803060c0207050f09090a0201080c07050312061003091101050c01090507080f0607080103020904030c15060605090f180a181505010527190b03030f04051c110105030c090d0b0411 81
    0x800d078042d142b03142c020340046440100c010200c00c1c0590b0104280400aa42000145401601200318082506219041140d54115455035908150400d0160340104090004106080c6400d0a0a0303070394122540485026045020f0060568042c406000134041c0717000c00c40142c110758000c160b80c0e0540d03680c81c2c150780c002c0c000e01020790040781d124006030009016080c0c04003018060098010f40c0070f50482048180c4503590090310014101041e490310508240c0004c400e400c508541081120b1104549250201d80061000310b507151581c030345413100c070070324100d00c0710144d00aa42017042c65000320220000d404284241800344203641d5502000026001b002210710b80080360901d01600e510420403124242d25810f6550030386d4808500390703240d50800c000c2101c003a0b004e180d03e07119454141002280b03138080c651081800c00314003032040062200c0300044400002420019104d45441d00d110b2818060b01031800d411000c03440c4100c0500c4200081c0303d104500c14000203048003c8030052007a0840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 649259469 1250 649258219 649258231
    0x40507060e0f030f0705010207080d0804081e130e010b090108041203060f12060501050621190e060f0a1b031107060203040b07020c0a0311011803060c0207050f09 71
    0x120000502000740700d005075407048030000788031509000c1c804002900340301c1d0791112403803107a001c211700700810750301803120700000c20380c20010346541c2e5003501014064a00c02480200302c0180090390440c0080e000700c2014000706004509034942c1007a400702c03004143c06c8c0c000c0d00071583c3c56000016041050340102c1d00d9581043c2e58410b107a403104e40da011301900d000480ca1041c075440c0c0c240402d510521510306402058801010310483c1180c1c180003084480607040385000312800c0002d040300c82c0b2001e81520601c201025000c146a41d5110349031138048200b180c0740350007824915441c82410000480300e0007441100d005010907241c01400c04101c606540307045503261000c9a02024140c06540f142ca100809201303038501d001c51f6941d40608a910031101110100640c00078401e900d90304200e0040440010f49a1900703150864a403003580907031100481d07040081203021080f04168031005080107551103001485080180c0388043c0d11000c081c0180da00131101e011281005140807030300c0c0b42c0210 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 649260719 1250 649259469 649259473
    0x100f05011205100503013206010c080c0f0102160b0a0501051f050705060708041209050307170102091509041a0d03050f0c0304140a0e1006030218060d02040f0e0405 72
    0xa40c1c00141202400c0001c007a4001c0307240c09900001d480c0c03400e00400000f0712800444600016510700c14107103c45450682d004038074042400c0040603604421700012440d080780203e500c0b10b0822444c189031203502440002d455002046420b01c403942d4510402c44944500d40706010b07641c900c5007200455009101c1c00d580500414080b244004208121028130b041a2601c240341900b69140d452414109684000009428104101c10301c202c0c1c540c4041074905928040049514050000780d54120314010301c49452507075200d0550550096040f9401130a000d802c01c00b000d00c40030780248164200c230211500682c02c10b800ba13841012494115410064024165022284030342c85c11141a000140460382099040100b505102c40c1003000c1c01c000c24045042c801940c40c46401d00c8107010761780c0d000c0d0030b80b1030006080c040000e507040d00035010b80c0e2180c90010b8a520383d810400c15032682503400d90350070100004031625a455250010800d81c3c0c019086599215520310301625040400c450180c40c0b5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 649261969 1250 649260719 649260737
    0xc020d080c1c0f091719020a080a03050a0912020601091d12030903040b0403050102190503041a04031407110306060105040503101802060a02100b030c0a06112103100f0501 75
    0x180c40c550100506500342c040004602e0720640d0f9581c0364032031104d01e032138617050081021b140d6081c0c0703c01040c0c070740f60f19031024000381e0009690f1208070740940c0419106042d11a4000741d5800d5a65001d201c505411503a52001020400c1001c0d480b10828024804458200b0151909480e1030b0540400580e10500040410382d40c5c001c2c8030485504003801c6004280400c02000800084040c0500060743c060000141d841d404410315040030442140792400380401401000041800b000c5d0105840d01e00b10140084c075542c42c40d00f216a51000c1449800e648004582502444072045203050b94200c207070112001c41e114038005607036070f000d94070455500d81d0010b500d000280300607030840c0c1295404c520038441c0300440b40c2d00064003a0802841040103034800c2c0c910000540441c0a404603079001134018144080c0c00d90080b482c03800390380c0900b4080c44424440380071844010800d15603032009000c0000980e03500d0007410b81c42580140c070707200c0c2d564403080f0001c40c104110440240445005855002d04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 649263219 1250 649261969 649262017
    0x6120f15171c0909091e080417060c09040207030e041a12070e0c0a03090f0f03030b04060e0c220f03020109080d0203090d020d0501060b0a0314040b130203100c020d080c 74
    0x2402d40101c0459038032511a286c0500707460210000c4d48020b02c507084694546040500c00c804074904100361415680c001414810200d8030042165a01034082d900942d841401d42000c3d01e617502095109904507103420f40106000b511100c07400c41c0144101c07a0400c2850032400d202d960741806004001c40341041c0008200707203800c060f0003002c4107012820046926580c3d0384460f00340e0031055100703460032116903641c082096410b00c40c403111220304903010010503040c008003891a0350300130605c00200c0800608410901415140c108101e04106043c178680c0e0303110400c0300a00c810034402280800c01c1c003140032801d86030108007100080c0040e4000c5d802d20714031a04014545980b0700b1300ba40c00050f92100000401c0080c05050060a0481850390740c44161a10050803200d0120340001c0030400d0303600340000110505100b90700b0058068001c50108035600001e410100e24600d511840e601d007410400e0596008900d40b40c4082e59511040c8480c3d55112150b05280316202c0841502d0300059098a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 649264469 1250 649263219 649263221
    0x1401050a0212030c0d1407021c0201090602030405150106080c031609240906110606130b03160801140906070f120c030e100606120f15171c0909 63
    0x10402081c0c4111220000c18100d910065402969461246980004d0600b2000c80600620300100014001d4040c20700c4c2940c4c00a46034000c0b0004c5421582400f00c0c3ea00b00719101350041c00089400403011503403407c140c81c10a50b140f00c0d5608203070b030f201d010400000f4041d0040c0240e81c0b0416040d8219840c40d6a50010000585441621142401a00e4002060302d800856041c590000901228200c405030b0b0a405007525910341e00400401c20202d1405903c0100842d0f1550000025039802034000102c04040000e4400d41e41e141d50540300e40200d410400034564100000c440b600002000203001941c130000680000b2030300000154170020100310040d100302d01e00501c00b1017a2601000d861aa01200d00544041040040005c0d4803090180c01030031092148030f140d081000010001103140880141030444080110800190347d5840e04c045032185402419901c0784e401306020011341c075412240c0f15102034031709400c011300c00c10460000e20282150300980d5141c445e1582d94601e4a030602d898 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 649265719 1250 649264469 649264477
    0x150f0e0606040e07020604020f03071802030c040308070c291b0f010f060f0b0c150a06030c060f0813020306130507050301060e041406070e102c040c09140105 69
    0x41c1d00400c04010000c3d4512035207002c6800351066a018180034180340c0100f0001100c3e070f41c034440c07203074110050410006a0088140d40e5074803280307502503103942d00e160900d500781c0103503440504001800607a04c0104102c2c5102001503403d60050326030b1541c0f108640a100c071003d207107140d900d064100117014007030400042045204040344211941d0100e0800c2132820748101d800706a440c2a1952000e00104180301c01c440d0180c20505217645c2090341c0710500f1582c3d80454440d401c60203d0490101d0811401038001101968014003075440041e9280c00007482e520384604440b00180c000c202240402c22407007086001190010000c0245881d070600809011b03c500780308807018440c683d40050340340c40038080c0c0d800411b0543c0901d085441c01d8184030000c286e2051140c0302c50b8100000f0040c4e9140c0050900b00648000c2d5a030001c8222070200948665080c659108840030820142498060002d401418900c00035141132112490725030b42038864054901408048030300822500e606035100f42c0c054 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 649266969 1250 649265719 649265731
    0x31e0e03120919110a09090203070905090f0615011d0d1203020d060b04060807090e1302040207062c010b010903260d1a0d0b0f040c170a0204150f0e 65
    0x55084416480d41d8003c02d080740d400110740c00c46180951011a04e011250320b40240f50300711041c05040340c942d001903201c44481c000c28030f0407961030380031502496042020203520301c0148129203560500c42120320311600c0b2803244600141807803500911840ca0300c1030012941c00c0160544d20490b50701c2c0d0381c0e441ca880c2121750700000c041d402c4c41442d0b0480c6841c0901c000505ca1005000d40c2e81d400e0100050001e200100b158040c040c01c50f03000c0200825000c0d103981e121100d44a640c140380c109100240192260120141081e400d080e400c5000402d80781c0c1842e00d0300c03000c02c028400306c000d1119103800d17101c20008160200c2c1c0080010030100d0a110307a0407070810012a4044a40b8040301c50720707a4250480800781404580e2100d44130240c03103402c12061070b1480103c45450401c20103555421039001c004200d000050112000f0600300542d40c0314120250000400000e014004150007031b5490a5440701644220708184c0c0599004060142190680340401880013440e0301313240c04282202c50203081 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 649268219 1250 649266969 649266973
    0x1305101e05160c0503070e010302060f030a02070f0506090c0306070f08060a0e01030c030b060603010e130231050121030c0302030d110c010e0105160f0c02090403031e0e031209 77
    0x180d000403450000c1e02e0041a1054818144050400c02858034103030b13154000e24818113481c0014409a5101c409548484030081016503483e039840803c10068000c085d0000c000c020716901040820201085091040007550100c58012201c1820942e58010542d45103000c030b0b0040a844465901c604e001a51140010741503c07042603880e4480c001d8203009038011303600c940341d0543c00e0041004d01100c464206d403084030380d00e0442d410400c010000b1440900407050074440b21040380115142c0c4c0c000c195000800311002c0c45400c0c0520a98041100300e02e500c1c000c050710740000800c190440702c0d075000550361030088041c0303199030b43d54055403441040c0e0415020752205100c2d40d400b07003516001c0c140d059110300e80c003030352565160111103094941d82801c0ba031720b6074182400c124640c00d0020319080944420f103008000102c3c602010781da009011403000c0d400105a8003080240342c0c00d5008928042e10820989c247c1003644c0903542c044481c840d8800d00207030010019190340c6200d0a135030541040329072007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 649269469 1250 649268219 649268227
    0x1a01020c041b030b0f0d050706080c07420e010f060f14120105090d0f1b230f030c0c09010303170a02040503060a0b04230f131401021305101e05 63
    0x300080c0c21b103d17042011102e03075021ba9018050786d81d016040580250f00c0c000d030503003404120350300c5000b5507509075601c0380d580240501d0102c81040040300101a4000501e41910302046d1218032000340044410440301c0d50700381040401100c5591040000311060403400d1403c43d42461340d42d1810308841c20115900c032101e1040e4000c060b1003031082034040c440b030740300a16620031201c0014060791071705d401c004180030034181c6076207143d04410b01076001c0c00d50003161100f80e95050a00d00442800c401c1025151740700c0d500038a446140d000000700243c181c0c2c2d4007140d9070300007264100300881c1801d0100800181c02000c4c048205000600e1660f00003c43c072002504081e00c90003c68500a000c8a107e1921521100210418145441170715840c8000d414102a60384201050359040100030b810640502007079130010340c0700c034102e16007020b05e2980401010381414a02000e64041c0d00019402903584e00b88600c001074502c1c0000c4d45e0b600030320740303522400710340c1c4c014030000e0b03590f200110486000d02200b00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 649270719 1250 649269469 649269499
    0xb28050f031002092b0302060601050a082707030501090b01080a02060406080c3907060f120f11030f070509090f0a0e061003050c1504030b070c061a01020c041b030b 72
    0x31076080f03808940d40405c010640700c603040003803510001030301d031a052200400c62a2091580006025441014101282000c4041d0b4a03d07100c945004501702441c0c0c0035040b8084100f16040d001101c0c281c0c0520703245001d0342d80790742c0c200d602e840000030004c0d80210200420000d950040792415407000036580340c01c1c100525074203000070200c05d0780d924005140d410102128801c881e9018521080c200400900250341001da02511200718404018103200b4174900354160004250045290340a038080b060000c9022007942451300d4200383d68100c10611102c0004480d40d201c1c0040e0389180704010040c50f01900c854801c00300c9041d02400c1e08241c02d860314103190801c5400c0040c2d03801181c0d41d01180c10a41e1035800c24505000c10103011600c110843e0940904540c41c00c01640c007641c0d08159080c206842d40402991314110321100108110708000407445a050b003c1d170014440c80c000c1e0261401801010204400c40320350030210480008841742c0f82c1c242034403d40c8000108540a0b0000c12150604 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 649271969 1250 649270719 649270759
    0xe07030902060a051c09390b040f081204060305040809150a020c0d050c060a021009050106090b010318080d020f120405190c03030e040b28050f03100209 67
    0x503003040c4003041d00050034001c40c070f1400c045004070400322a0208040440d03580da600d9000c00250250320354155080c05868613066107035010000c600d072880b201f11a103a40792480d048541241c420403151481c0340200264202010400712883d610b200400d81c074090070040180c00604003d030050700d880703509006240d002c0c1c5a803145039580203900d090542e2942e032541d0000b4500140e219626000e840c210300c021001400014021a05107030844400d42c039020300c008105e2a01440554080100c4c1c00d00140b02e003030080c1036000400344d40340702400380070b07610800005405a510360508902400018070204002c40c101c0300c003900c9900110f000161034121001c1021040b03400c07114640d0080d42540782030200700241040050318032000581c0350004c201c01a11881008040780c803001d010f02002c030a01781100d0b0307107552003201d0001c0c2c020f050300c86201500a1403e1401d068581608202c814100c022500d45005016a0a480030090091108003028107140300a03400a000c51030f0004900003500011101c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 649273219 1250 649271969 649271977
    0x12030f1021020f0d03120e0a1b08060f0f0403110c0a0306150812030a02031b1b07050108060d1e0b0405060a050a0203060f0d050f010e07090e070806010e0703090206 72
    0xc000c140d101d10245004000c07404410741c00071446421190080340000f03800c45020700d04800040700008002c4003508086003841d4034007400500703102c05201814501c2c503e82e10340340f05443c03000c41120b0b225a203094080c4a0258103440703585800c001e02001600080c8121604030389801800151951003c19001051804084d50022111310303480e804404541c540b00d145150003402007000415100c00d605031150001d120241003500f6a035000000900c1c110940180c000065446045203035032058400f002c445c101a00140c070f01c00600032103000256540c4654a4203009410081646101072415030301c00b82c1c036405800090040040f88492840440e4810b84468842c03130060001c0c0004c1e14009000f00100e4034001c040c8050684144140801901c4041c1c21144058090301e14014501041c1800717890311181e0711240400b5801e201c85280c40a00c003241d410100d5403a248203000340e0104980054603000343d4010804603078800c0c0010404840e105100035005403180c10001000c46054011078800d0b88 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 649274469 1250 649273219 649273259
    0xc09050904060618020418140106120b0306010308180414190e030c0109021005130b160b1021021e0604090c0504030c12050604060f1401090501061112030f10 69
    0xb03170119003004052040307040c90440c5500701c00100030340c00801c280d00d01a075074103020380400c210009500c540c0d1000035511801400300001c0c1200c440b07680d603203032003c410f600001800030300c55101155090b0b40c1c2400d018503469001006105845075580300c0f040300015080340321080ba455142d26101d204c071003051004103258030001c170001c1128225401030001b0340d142103409008209007041252001c0001804003016600c1c800542c6540d02100309201f01c107544d0001f00070705540d101c942440310386003020145408031246680c00341e170301304d400301d246c8011100036400181d0003a96070301c0380b1910021402000541302c03000401d61801e00c1c0c1c940e511101154111807150010039800601481881071188400000f0300d01c080300007104070025910b1989a9001500c01080d00351618040d10f007410721900410380d40e40c12400c9620301076035134000c1c0c0000f4140a2041c0350100c1c3c1c2601048491160200f00d40081c2115114198a1500ca20118080c1c0b044010003074042600c3c101c8003c14210740d20000e04800c0b40d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 649275719 1250 649274469 649274471
    0x30204023006240403080a09150c0c0b07050604020d021503010608010f0b07082d0f0d0c0806030d080912040311040b0102010c1b08090907050703030c030c09050904060618 75
    0x440e165051042000f400e00c0383c00600340034501182c000744411000c48051700c0e0301c104a1134840103030314000d8902034540d070055590a0600f20651803401d60100b440c40b00300d4001c2c2c0d101d420540d41c075004140e0600c200e200c00341c00c9400c2100000c000d030900307503080c030b1200d880a411000b110341c02407080202500283c00ca500058051001006400004a0b0480107880b2034103125281041da0b5035002681d10441382c002240c0c6002042c9000c2500e9101c880c0c0f0700c140c81c4800c8180c2c1d00c803906001c1011607030110503d14451803400742e0f280b0207548911012031040002a0040c03d000e014000705942c812002400401940b0440250180a8454034043c1c402175204600182190141070108000e690301c1d0002c1c0c2e811685071408050a9950004118405d00c0c010005003c0b0a011030500420034400c1040709900302200c141804003166001000742106402a50104079900e4804002c03000c1d196a10641f0002600c03100c41400945020851a03400600c2280000b4036140d03280001408410310641c4000300d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 649276969 1250 649275719 649275721
    0x204081b040c0c24020406260f22021003050115020c01051c0609090b0106180509070e13360510050405070909080d06090506010206010302040230 64
    0x294011000c540346a40845081c0200700500070010400302d8002e070301816641030324226090704002180011100c0440c48400e40d51903450b4080541801c17100c00b010b140b10348501c403500d40030140c040a0b490041040642e0000c50703803100201076a20305005c00646007404500030b03011005956100ba503460640d003946011501d58907102c0e9540f50007441c413445030155004038007102c2c01030781d110701120f84016240380c0011801004441c0340005261980281448c2850403203141e040c070003595001c03030480fa120b42d19084040d20049501d41d140403d40304907038001c030106001c0b80c1181d0040840110341c0e1400380090344010a00c4802806803001c0360403440704103036801e143c0022607032040d0980e40601c03102d1100086040c1656262540c43c00554802030040303665102003000c1100a1102000a01d40b025003800261464200454580d024042c1060514905500058280718034080d60780b0501d0160068a026881c507003d101c00303584014120910b01400080700781000fa00d04000c2c030f080b01ca02e01c1c2c1d00c1d00c032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 649278219 1250 649276969 649276993
    0x102003030a09151406010f11160e0603031c050a0b0d120e010e090a0b010c12030509060114092a0406090306051f12020102010f0606020a11060a0c0308090a020301020408 74
    0x20722409815500801030511040c1242c4c4025092143d030055020319100383d0740810804203e84001030f881070317014540142c2c4070341d0a449400c40c6041058030000e594880d4544c940504069072031040000d503c0080100c080410840d1440da0b100942c04904a03801080e90f02d80c07540062900c00c1d81c010122150545240818507542c1e03c420f85140d540020b00b40a40c0302100c07200042c044031b00c02405c20380d0403a19100c90340d84913446403034240c442d1988000040040054a00050050302c012907a0000b18400c5c1c4000050300084a000c220003064060f001c031405032076030311110648010000410f098804607070210300a030040080100f00404040d66a041840d083d46010300913918068071006a001e400700000050042c1010746104507030030407000c010410300510040c5e0140000c00005100e042c03034504002071031a004201d034a40c107031044508805005403c2c080080343d009400e20240045c44086481f4006070003201c2043e04204120221080b07404154002400c0e64001c3d003108540350050b59000603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 649279469 1250 649278219 649278233
    0x31803080d0b0f011209050f1e060c070308010b130812070605010b0310050d110a15021c080a150f030f0308150607060902130504051f0506102003030a09 67
    0xb052030200d501c01c90580700d4000003044c040a01d0000091143d5840c118402c00804112000b0f10302044010340e000f203141c11410704600b45403c080300099000c1c400000b005505003800b02da0b401030380f5072900300ca540d09221640696401c4000c3c01c1c0b03541940c0c201c011039003070b40401481e10216100300840740c0d90130b0649440307025505c041e409014280414410f02c040f1551442d0390006440007aa66900000c0b820b061060802e000c044110750400445030011503100254151106018083c0e001c45030800114601c4030030503041c00c9000c400084920300450440005500305800310607a0300c0780012650b440301001ca00001c0241d008582421040c6404000c064000b00d00c1580950071045140700c2c00d0380c50000c15200e100340c0d500108400e03520650403046643d500003850308560030005c20047c5190614051341e0315071103100e1130400545e95281000141c5000d00446204150251400031101c8800200741e400c0319002c5e00349440d020200d942d02414407020409940b05040c0200041401c0406003040f0b8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 649280575 1106 649279469 649279481
    0x5060d1403130803090a06030c020a050313060e01050f0910051605060106030e010c140d061d06041d0a02010e030304091a0a12050613031803080d 64
    0xc812008004042c00c2110b8000c0d1250507030b251951101540ca00404045592200410700180a024401d42103174074003554034012202d0070085a80d40703c3c250b403c1440f414030300b000c959400300041d40c0e000c2c440c0d0811240a080040c03038202c140340014020710480e1146809003a4183c10814a584240c00300c8085a90007614201c07505050724106454004c01c0c861071002034108088105462410720613068030103e25106c1c0bc40a242030b40440b0a640c008611600f51a030b501d40002601d039501c0602e50000550803108422286000001c1004448900b000744d086a654149a40402c42c000619840c40c5a02401e01282c100c0c1250000b82c910b1045410000502d424072280100d0032401500309040000119173744da5800391201c00108103007821501c06401c0c1d501c5040807500800d41307004248200c6001c2c0c80c0000005110120422680d00240e1085484680004128584101500c83c0d6 = true := by decide +kernel

theorem cover : BRFrame.Cov 649100719 649280575 := by
  have h0 := BRFrame.cov_init 649100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 649100719 ≤ n) (h2 : n < 649280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
