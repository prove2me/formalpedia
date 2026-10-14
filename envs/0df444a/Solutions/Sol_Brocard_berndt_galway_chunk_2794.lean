-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2794
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:46:07.053505+00:00
-- url     : https://prove2.me/submissions/36c77c73-636e-4878-ada1-2f6ed65202cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 502338129 ≤ n < 502517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 502339379 1250 502338129 502338149
    0x513020405070809070f23010c050106030515011710020c03040306111e03241f090512010c0819060b0703020a1e050a020909013801030c17040804 64
    0x24020103580040590344139400c00c0c0704a948042e0746414004211802d485071804071080740d882c019116070310f06209525040f040c1004007a4141319901c0500f150700c2c5038415140c94208260070044001e030484003e0040c48055a910382c41e10b02c070252280c03070b40340c14007a1038241d9038002843d840b018000d00903200210f8015408000d00010405116101d601901c44401160300088001c03882000300d0090720300410000180da28110061008030341031040240c140d0768440480a400720340c5400303215900c1c20b0301c1c09564508c90110702c0c0c1420321a480d20b8405049e203031a410b000c08841d01ea0390184d8001d9022401c5603d54400c81d0009102d80002c0000350011803144d50001540000c0c180c00044d00074240748035075485480c038a0004050000c1800c5508000c0c01c0c0e4001031554405450903403030250b00041400e000141c116100400105d98402c40804401038a032580710442001c81c48000c0e901c4544020300b01030013074108600d030091502d0746400002105912110110f014064800f095034040c00140c02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 502340629 1250 502339379 502339381
    0x307090f0819030e1831151b0e010e04110708090a03080c030a02060901540c080c090c0f04030f0b09010b030705060d020a051309020703170412030513020405 69
    0x1204039001c1d2011a071a00303245030460190749170f4031030451410030110442c0f51610000350144d0303111039507111465084107c40d901c44241240b00600300000b9404a046e0b5182c40310743d98030400015107940c00c1104250702c101d240000403d80c071040b40003100d0035580c0c410b98040ea210f2004c0001400c403640b0f900050f000040c0420703000042c2e40c000008100c075400329000c94030b01c2e560788803182e400c4e51805459464100b511405002081030300741110782c80070340551540c018038a04091282203c802a5a103282904041100e0754184022205200c000c0c060f800b001d05041040b035000704040302c0c4064414494084005501c540340840c0506903005503a021250030480c9410741040b200d440c1c003ea402d1025540390012400d00c0d03103000102001185d00141001d8100302d45014060002e4006803503007018401c0420100b0820318840041c40f014101d26400141c640006040040858003079040c00c1900d403000c0004c0c00040f40b600240d580300d040b12031074007003180d0740e580c8107201244600303280094000e400c3c64 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 502341879 1250 502340629 502340659
    0x907171801021b0307261602041d07090c180b160501060603021201060c051c0c0b04050f010b09220606091e180b180705090c0307090f0819030e 63
    0x12000740003440c003860b100700d40415070080c80a450131854461025242e030411104807d1402c08500010560000b000090015800e2280c1c01b503e0300003001c5c1c59055000048148816291441526518011407504002e1000003603152000c3c500b041c02415030390800820009480b600e4014000d124950003030003802103541e204006030103508500d1144102e40010702c00800c8451042a4000c0900c0d0444000d0024081d1a0f5064544048900842c030420040d80c000c01c3c00b14210a46036405a0b100b00c006088001c80c03d4a420708581d8001c2d48644960307a100c0901542c2d0308040b0485a9000401d14442c2c4000450724044c4002c0420358000340c40c0324101880f985c0c030300601d505903e459081c5901d00740f040b2005108001d40c07615580b40300409410301500450b1641000090040c030901e101e41c00c0b10352064480340041c070b281e10101d81444441d0000000c111500d64440c210f0b10040010f449080d00f0075080043c0d240d12804615050ba45070030210040106041c400d09601c00b5248021341444240d803590 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 502343129 1250 502341879 502341883
    0x1201050a0501050901022e0c052502060319060f030809100302160f0c051c11012c1302040f030221060403051605030a0306050907171801021b 62
    0x2446054030a1940100028440d401202281c000c060141d000c0c00c1c0400c01a02c2d0040c10181c84150b04442480703102c110b020400140c405c00044120a890703040e00ca41101b18031071a80440162505000882c04031054016200d01007641d41105076031200b001000c02589142d0b0003817100340e004030a80e0300c07118400001d00201200034400d0010642e100444841c032840e065050748540700d0b003200801c6d10500080c010410a452184280c4d20865a080c085686d0b60005032400820100010300b8100265036141040b03019030001007610000e003400030007400c044100c60490080c5a205c07411008514851001e9662201c1c0d943e41c1c0a4682d160454540d5200c507107624070741c0032700d0004901a8441c60020f030a07045440c440a503940b400c08004240711754990350111446d03002500c98410605282050000080040c005824080c1030b66600094603841c00741013103c2003c01074034050034010311228400c2020f541c42c0c8030550001307046c050540000e021240d860300902c00c0394041248140c200c0407072800b403040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 502344379 1250 502343129 502343131
    0xc0901031d030f0c0f01020a0302040806090c010c031101090b0403051b03250203030403080c0a060b040c0807180f15140a0e1014120412030b030c0d020301020f12 71
    0x203a90801c5008062140d0140480004601561581c01032003080e40c0c03014a4802000b13010342c00005d40c1c0020000e84040750076078110500d07c00110380c0100d001e01c03000c407041108941c8060f5080c000c00c0e60340744840020748482d2240704003808105841e0f514403485c5c80d094200d90880c540c451180c052a1806080045c000c0d00f269211a140c58105ca00021004100005403014940307071030107201d5090b8415103a14143c3c40c0344c1000302c0e054001400004003082000010f444a080c001000d810400c06d20301c0e06a0440b810421071702c4c420307440c188009000c07640c46071030795502c400c00741085042d030755800890004490640e40901301a01c600440483c81e01c441c0000c510104030356444210440004201c041041e00030703816241d0000d080000502d54514103103a0012020002c0d0811040d6041d03031808403219540181c90429801e044402400108180d04d4a203c44507111403604000e14002c83c00000d07241c003840020640702d00f02071300442c07042d0741e029070488901002c0c41e0051503135100707060040080014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 502345629 1250 502344379 502344397
    0xf0302030a093f051b070b16050c01030203010303122a120515010f0f0309020d03022505060f090f03030c1c0f090b130806070504050405060a1202060f0c01050c 70
    0x150000728440d070450310b0660404200540c507030314100300d4512130311580105e402014400a1103100e500085020380f440c000c00f9840c0441c04c05210010f00e50901d01d181030325800c0308a0426104000400110340d0000320f5124110106402055100c9514020482407000c041511011200c1d100c90101c1150014070602007280030030000d10090341c842c0001d41c81e07200469242c40c0810000c840315104944684042c00c90403d003400c00003007004c15038011514855460500320056482070780c460f107024a00c42c22105c1c0c000e248004400e006424240441ca02c2d004480c107001c40c0c81400300b04041d0540d140d40f0024000b140140c00ca030740700c05601d03061965421401412214046001600c114468030400c0d03a6044454681c4648548514110028540394002d48103544411180716010034040d41c10300400b4012103c2d40e4880351142d0030202040121070000c1c00644c031913080080e040200080403810340f205c581d012114a03448124164a00c003040c410500c82010075482c0c03408022002400c43d016250b400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 502346879 1250 502345629 502345703
    0x5100b09060d020f010c1a131a010305070b07050309280902070209060d0f0f080306010e04140103021011070e0a0f0b0d020f06070b01180e0d0f0302030a09 68
    0x10321071005120041c0000c29020b50402d1440c40200030710350041001c006003a101e0340280d140c004c80756058076107008040d141e40c3c0321050442c005c40300380482a414110300c50f401810b07050945d490750344c500399180c929200d01c100103c40403032600180001441a41c19880001e0898111010002c55541d641c1441420048042003021400f02d003042440c402c0d9000a580a0328075002619074100300035a40c1d10411044030f0070007a81e011640058a60904030491900c40c4a5941d140d00b080b10000d002c4201c400c0c24140034502d0f082c6807520784410140642c1c110b039015624138420104420b0203d138412a01450301a603403080e40c0e400a44115100c000070b126103006001080180084d15580050b1101c0c0d14500707600604800409001d842c144008803841030b03000f0601450304003507a8400310350100991102c0c240251001c06440c11a4250140c096859080c10142c540c8001c44140600520b5901518000300b603404000078002c0313805540060012034100c1c542c1002500074a0380300c044190b034503030320816032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 502348129 1250 502346879 502346881
    0x9080f0f0607051e030c0405031501030c081609020903030906120406050a0504150b010203090d0515010803030f0c07030302120a0c03110301051003150e1006090b090a0b090102010905100b09 83
    0x2d103120b030050303500c11840c01161095045041001042980018043c0c00510900304000a11550104a665117400083c0a003100d158514140101154110340c070072402900282466030981421000207015100309010050320350f1035507404070340780d4096000c08903041040010000d1003016102080b82c40396110f040c05014981d00c4940740c00c240ca009490003011110316500c200c03500011600a81d0200c1310610481f801c101c00040004c4250300b1005003504e240d0801c10317a03810390f44050172a050140800340b0045184d410b08808400898500810190700c2c020701003628000c16100380c04841c0c454180c4410500385090074610a402445224400c10100c2d2500e680e011984045a040c0e03812140002c00d8005140d000b00802d4014250300054241005c14007030000c24610285080280580d00a003c5084501e0a050025200030265000720342d0800d010701c10781d03d07241d5444580da0242c5141c254419254184500141d025100d100d130000c0050141011100d4044610381c410710340c0e00c070111045016 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 502349379 1250 502348129 502348141
    0x10303020f1009150e1203010f0e090c0603040f08120a29090a0b040b06040306021b0705090103230d030506150301120b1306110a12050f0109050709080f0f06 69
    0x1190141d0f00000c0c802d100d00c0c131a4200c503544e96481390001c60202d00665207000160907100d91103031f10036080309000f001e09420a11410207000b10581c1d022910300002d1100365020400220107000091005000384642c0d00654104144d13003003540c030b4040234031110b19070b80c0c104059640c020b08154015504110400c40000042800c02011040c804901a003070f40c0180c2c0300e50449901420746407031141d07001911100e928202d511014010070085000c1c0c0c4c4016111428841c000302ea00c14280c204a11b81e9102c04800d20040d582d400700103044a0307010346a6100080c1003449446000e8007040c840403075003d0041032101c00b07501038000e288201c03403c407244407641d2a5004803400c540400c1c011142c220410b143c00307600240c03050f600560007680d1042400c844a0255488005581311041c5e80f0454550100e04c1b100900d800c01c8480811100c41c2e179051066151050000160340014803a00071081d0b11100441c051030b0140300000d001d455203005440e0720715030080c46996107000c104c014840511030b0b0000114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 502350629 1250 502349379 502349381
    0x14150a0c050a03020a02090c12040605130f1514152713020f0d0506060d030e03071811160b06010e0406060c0203100e0d0507080d0c03050f0609070e13090803010303020f10 75
    0x40c2700702841207040c0391074079224140100780007000e4141c81f42d4810f0002c8041144070f40d074200d869102d0400100314100c112072550550340d08003491a1616804030501103114005032281080381c4040e6540c40e54210310040b5000c1080318500080140524102440a080c0c038090b00049400d000341c4804001035000814865000d41e0b2039400b5205803c2000030a8240c0f4000d0030301410107000b883e11c50064450b000c000381c00c200f0342d5405511920300342a090640d8101310b008502001c07154141d01428142c44085011168a02010060420140c0c00008501d03a00235079402480d600081e02c00c20000303444440281140000900c142c0c443d1003081d102d5030041c000ea0044600320300c1e07620058040080c03180d0701510f0039007220b14101d0301e80c0c40c00c1c403030705070005914412007000c3d11940e50081024106400c59640107c005440b00b4001d00d00038040106281d00521b0070340b60304106940c0c0081d00386211403d44010140e1000081c0711080000000041c540e000034004070200c0b9802c29103060002c4000d0580c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 502351879 1250 502350629 502350637
    0x20301030f120e0a1707050402030c031b0702010c0609140303100302010e0f03070b07150203190c020105070503071803020319030807030605100809011803120614150a0c050a03020a02090c 82
    0x80e80411000000e00c400307402c010b000d00840e1105c504850009403224009000e90b042160000f03840100442004042c01700300700e4003460a00b20404072494555680c00080c85401d07030b0240544000d8070392a251007042101d00440f01000e2411050b2502c0381041d40d0031a100680c903102c00c1c2d001074800c2a0700581450481300f20000c9450003401840300c0c500e4101035a1075504105400c0e1501f82d0180035030704500075a1f000461141404100c2141e4808a203032107078003101c814500e080210380c03418040101c081c1d008000c486d00603c45080c5281540054003c11004240303d802c02905405405803141078650003965640b0142d103c2e488209482d92103010031411141503108080e4031920b10702c504501203016840395a04170a000002103081004601101c3c1a403c1d40d8804a0006e9011485030072581d01c3d0384146006890081c0b05044400d03010340000701d50130305c11950550072000001e104a1443e01a070100962a9406800e40d040f1160600300603448900318481030303004d440c0800000324144100801c0b030f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 502353129 1250 502351879 502351907
    0x608012003010e0c0d02042417060114070602070b0421090b0a2a05071415160f0b01080706050909130311071707080a03090311060d020301030f12 64
    0x1181960f10f0140303042150400600112407500040100400054080c00180082c20191021400054040c07501c400148180074802c003c104103040c21441e1128884607070f0343c1100007464002a240341810780a1150f20407884020000c42c4001999001c0001c9070b04a01d100301c0c01641c004100e00001c5942c4418801c02c034220030005081450288061140c1c40043e002016252604541d404200d40c05628075a03250328103101410148045c120412a040009002510100911030f006109240203d01c4407a68012100c20310768000c1071810302c0c0c50554038481001c0e40c00c01e079010a1050715082504d1201c00038028031400d4003a00001040090044040300c59004002d8440900c6a6420840f090395100d044821810441c0041801441490401940028046040c40e031005400c624000625184d4181c4c4054801d811000558000c2500710210408403500040b4814003600058000780c1c440c401c0c0c23181d1070034a500c080700100c18058401c0403005500e1050b00c0c1350038050601c0b134007515040440681 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 502354379 1250 502353129 502353191
    0x100f02090303070b041106040909060b100905010c0501021e0409060b0301030804051909020d0e0c03061e0406023a050f0c0d09051902100c17090d02030d03060801 71
    0x43c0d48002110044400d03400740c05080400f00d200d000e20300051070395000d9800316071031300e0b140d0381c402040c061039204007107036081c003140c801101a22607800030380040c03c01d118031414000036402c10414410290100c404001c1e481503c0b00191102c450301180390740050181c1c0a100d4030b80480880c1da03904c20801ca170305881d04060503500b083d1070a0f080007035080300c0100007001d2815007500021164030f580050100030300c103683d011234a40381d1070325030500c0d080710400d0f8038cc402c0c1c1c881d000340961071650b15603001c0b8100140c4a107800075602e40c141000a88200204030085e510785030b00c00912030800000074085121205e43c007a851048110711f9000b0f940f8103960070200e0b0b80000001c5001031240c1002840c2007110f450012038940484d80703400d81003500b01d000010300704219605040031403608030075200c0880c4403802c0100300c0c505161500e1100e1030100c0c261404009000403c24441e907120703414055003c0c1d008046031040c1c10240c1005019222500c20718206609140c003844506600c00c400030074801b0340c050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 502355629 1250 502354379 502354387
    0x305060105270709061103180d030507050a0c0914070e01030c0306051504150207240309140d0206091209090424020a0f1b0204150512100f02090303 65
    0x400c00219850902c42001c0c10280700c45070001c08080880502d1042520703032510710306186803000213820003224a003100391075081008500d52001091582580b02c0303406480101e03144081385801c0d01d26114402c009000391140903142410481095851826658405010300c011107a03400300c080121820368200c40820300c40341201c16154426889418030030918900403469903a40e00224a000b0980c0300d6118082c2400a010320200141c0d0b0030490036180244003d10302039181c1078104a58030102a64500e01240103000800c405e84039030082101a82c1107820042c105072070907015580c8041802ca1031015000c0c1000003081a5030105003142c0c041703101c80141d0314000405082010f0070783c00070070859606142e002c2d0742d01280600c0c1064000240403040040e038030408403102404240300c083c0c0c40400c011410340c101c00c00401c100c21019200703a040d10041540d4203070f160380364074071102c0c0c0d0412600010715100005c221000000d4111030500c0c10310341085210340a5142c8000d0307119100d611905581300300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 502356879 1250 502355629 502355639
    0x812042306130206040f0b21010609030b04020f0909031c0605030c04050c1207021b09040807120c051f1119140409060605030708072307020117040614010e0103050601 73
    0x40d02d85240784010a0245840d0312030402900121940e0414010f0078000300300c16004886100410881000300742c6484019890b010005290180d03d00008020341680c002250854503000c00c107690b6140001c03c07041080c0351618445690b500485003001c00110245185180c1d4038040c410300040d1400a00602a1400e4807418007014001c050104104204100202900c00c2e40103203c803809403015601401e4105080e03606400f0700040d14030594801c964000510001941c1d079001c880d8030b5036100500030400c3e4012038080c2ea10040071240a801383c024216600401501d40c0440a41d05001d80010400f08000c5036042500b401400d02d1074614038400804002518001c4640101038400d01901c135181c07989940682d816580d0b07551100380802d1307000c0180000e80b600000225032001881c07038040056941194031484000b8945a40005003200060100545e445103202c0107160b40320400807889030400d45400401800d0004000000850720b2001090020304481200d04a0fa006802403105034205 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 502358129 1250 502356879 502356901
    0x1120501081905031e070203160b0a0c03031e0f0c031107060b150f070303050604051e0601031d06010e0f090c0f131b020105060613120303090812042306 67
    0x250800baa5144024090110f41d64014480b01703840461602c4060b84442440c418149001005401e400d14a404000280012450300e419160345040c1490468000c11180c01c00b6001040500c7e80d80c01c1d020041c5690014030385c2c164201500b0790101c46000c01801e81081d10072001c54400307903600c1038445010001c0c0b02c003194190300410000d4030000c1c8550010440515822529881050740040e040307000300d65074080c1074151145d158010f000f6030b0180064a040c1d60499071030001040082c030090f00300d02c042081ea9201e03601c101c0510b02e00810001410954000880e5510405d11410313082c1c024000c0000c6000c20300f09003a60103070500200a220f0b401d1850300b0032507904020003180c0e41200044091116180440c01000c032038442210215409580c0804020f094410041405019400030044042c0c007003c4003050000300d6103281c4074909030009524007100039150204018201c0034020442031030303c03010400c0c11070141d0311401d00b440c200c0f1030250b080300290300c58501454070340c0c02103800100c4120f00303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 502359379 1250 502358129 502358173
    0x307080301030b15120d02060a0b1311040801090c0504060803040b030c030c091503150a270209030a051b0f0f06071704060f02060f090c12100c0309020112050108 71
    0x1141c200c0a070a40c10741c10200c1d004104240c5d010945c0c0e070111112910a81c1c0601c05140c1114542c4024000704441c000490406014441640056503440d101c51481d44010b10075500070b401c1000080c080c3d0b0b400344c141003031035440c203010b22481180340110011700b991002080302e04aa0700301c5100d90071691031640c0e03460300b500010301845020074201300400c0681e0369099110080c07600c800c090350f01d0717080c4011184160070701e6407120f23801100c1d02902481210600c410600c1c1d06004a0b84e80b40c040209506400040c1c020303261442c6d0148507c0c450002004800b24140075074818003446000c010f4180410000110900503041da000528014450b00300e0170000020000640910142c405a50003015081c000e40c0c4640d1005000900c0c007003d41080c25418440c41341c024040d08d81e0100c80303080000d0308030f441c0c40080040e00d00c103140741c02010941c070105000010b50f1a4244404000464660f8805000340c10414404c03400039050f41d14a900720441031180e24141c50300380e4001c11a0b03030000b101d07220354012 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 502360629 1250 502359379 502359391
    0x616050a0905030109200103060305060a0e070f120506090303100b070206090a08030301080106091401090b011806080f01060c170a05070510090203150112080a12050916080307080301030b 82
    0x4100351011450b07440174094003110360302c201c40621403001115034402c50800e00c2614681014102101000410707000a2070319003142c1d018100203030ba800b03d00f04491504071950f0085a402d040d600b80020300b03294400c0d40d404d145004905503000c59607421041030b280e1008441e00000300300216000d200f05801e07500648042480942618070300040140014155052903000130580ea00000051008050a019610040c02d062000340156050400c5038440b8403014041c82d00902c0c0c0c0e400f0410210f82c03060041c1814120f540d042814159100c03071000700301e1042240d010903500720600000a0071480f8080031903286412403000b43e0102c9030b004051586500c55040041001360038080395002c03d000f404030074000f400d40040010250040d105050909200c81410038080d506c12004024103264007921008c03d81d4460040785c0d035101c000c8030964110454100c45985945020708014948600060040800070b850340701150003991086120b5580c80342010040502c07105000400016648100d129000070f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 502361879 1250 502360629 502360637
    0x3071410060f0b04121401020c1c0311030f070c0209040318050a061707020102090310091101050c031903020f0d090b160f0305060f031c090b0403020901050918011b09080616050a 78
    0x5444081b80c2c50980e0441d0301505034035004100b09640c00c15000842c605d132074149003003d12044135205071003509800010020318002e1100d00008201d50320403001c0740c01c0c9503030041550303000782003c1c00d008048001c20756802031400007415001c03a00e8903000d008101100d10076030303522100d1596000d1140034a41c5c00340c0081c065640910903040130340d40a103c205550716600400103092402403d240f0020f40704184954140700b0b081004050b80301010048400780c85c4005030009006c2c4041504900902c5500c40d08030706000080b0388030040340c411703400170070000c0d00450110030b071500c2d1403000c0407038490031007004001b00d111410b500d141140290056980b04400610f10b10b0310000c1000402d0074402d907203107008900c80c4027015a03000a0341041d5104003400000414078202411580840c0c2c1c109010701601e84943c003800d000138200000540d0b503401901c6018000d126641aa0780208203100c3c0400000300070402080c8042204100020418400d10352508201660501980c05a03903607805000054100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 502363129 1250 502361879 502361903
    0x9010c0c0512030a081b0405010810050901030f0b06040b06181903060c0207060513091d0a080910080402031e03071b031e022103071410060f0b0412 65
    0x1564400140004004080703000d0f40d510a600303440240700100081401140c1c8426284081c18a46110700ba14140d032400c0c284903079075448003802d90300907402030f5010381d80c0b00c0b240c2c0f40048100304101c07140c200c50740e10032a950401e13901c9000402c010303a1801e0307402d01d070080421300c032a02148001c0c12071000c0d0b00764007400b1800090003100c9841c1c5416005e400690384144c035107462000156040001c2801060203207030450a02c01c00c103550f82402805803140605e42c640f500c829100481c0b41d024545095108601143c003481000c1c60402010741100010710f20500c05680d100042c14081d03a4114800e0b54000d01070010140311403142e00f1035030000354207001c4030312003400341c0e40006851590070015003090075041d800152a520b4091160070004442c082e00c454140701c1100142c5400c60403501901603418615000c10941c0e046510310300a2007006404082800414139414070080307010110000140c5042c0715460300c61080760b90011052065640c0b5050410040000540400081d0100c41c801c003058501c0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 502364379 1250 502363129 502363139
    0x20a050c060c070b09071805151206150a0e041217180d09080d2106090f0e0a02090a0f18030503060a060e0303040501030b120115090c03020f09010c0c 66
    0x94030804070307542000682c00007101014801e90310300482d0700c150681c3c010310782c1905214207000b020300c0b062031805a00703864901081e00c42c90b50745030140803202c014082941d0000004c0c47d045c2e5a800c03d58000fa800c9500740203015180c141010f034007091300c10a0030385141603119655401a003c1ea0b5200000400030034004803203002001c1210300340a0a490f21101040c805c807440c4090401107400c04030310501031844010841c02c0310101e0380d00c5841030346041c0b00f140a01025440243c4a243c000850200740c91b106e004103162080390b100b0780310110b0745441000150070b440079159071b466039440d02039404100000022400541500030181c020011413000c02c0c0844a075014404d0004c0f030b0351080700401d00105c100041410141d541400515541c6801d550111051001c251a8130480c000c89042540f21066250180c945000f05403560150100070449084444050784001050340100c64903142041900e0300031621900a0750301041404203140d1515025600540740c040458108580c204408000051 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 502365629 1250 502364379 502364383
    0xc010204030c1203030e030a1b03090b030a06381303060606030606121b050d091203150626130f1101090f121b0b0c150127020a050c 58
    0x1000b000e10710f082c0c03052100e1610b0044c0a031303030304000c5ca40f159074020301041c40d4190b80b10982c281c030700e80000c0f070380144104141030440d130180440c0c1240d180500c000041c0700400e42d0702d40c0084100c80303480491010701c5414200c11891000c104111004140780143d9015004e0150801000042d40c1c00003444035143c2e0303136034500c01650300701e5002401180c1d89000c2003103d0358119440c0b2808102070101085040c81e50b0800f007801120160070b17142004008030fa414204842c9078091240c0c581c00121002504801c1e1030000c3c043d01492942441c0482c08040000e00c250065071802c501c0848000300802481e029101c14181240041141094142140d004008213020800710410940115400544840140000340c6804519440b00710700a400c5941005540d03001c1c807044901d0741e4010310f170f800301c3c0d483e651030fa030300715061900301d514012000902e404020000003051406080c10100c480644c0ea6a0340340c84400c4602d0880c44501c44c2c10150810001c07074410340c000e1028590038101581003d100030b00d064 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 502366879 1250 502365629 502365653
    0x809071505030420090403031113152015060d14150c0a05040302090a1409070513060e0a0e070812070203010e01050408070b06010c0206030901020703110c01020309060c01020403 78
    0x3800314030300005000074031403880004000e4458442c4407104901c50803020407168103009001904141e0384400d420003085006c0c2c202d510b5000155102c3d031206854900c81d0180b04003400c20744d400b050b0030b540c6124403407045007021810244180c0180240340c0c00c420b4009406803008140d160b0200482110340d002500317811400c008001c480c8002c2403442e0401c020f0b4040008050031141d8805818007000114a40c400111010b495040c0c03050780442d1074075080c10340502540460000c403036044500b00705072908000b030440220742041310305a03c0304481c60b43c14403c591241c041c10b80840803000010310300d0321a075001584030120603011103541079610003a1314202800143d0380341c0052030000d010001c3d807800340100d48100241100170442810256206120b91003642d0300200007010a000061031a0701807084802e000360054030280d903910b40300309098000c1d80510002c4004c58210101c5603010180002d4807100b00c44180c0086107428914030400819400500c5007048642d0200720220020303810340010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 502368129 1250 502366879 502366919
    0x402040308090118050d0f1104110d050a020403120503070212130513020309191a01060e030d030b0102100f0f06030302030c1b010e120f01050c03010f14060a080907 72
    0x11a888142e008001400c043c08090681070f0511040010301c40703a660b400c0d40c000c2c0d05a10000c19000d007842850f01010b81c150f00800c05510901d0f102e04c8085404807070005002220035510700700040e0f40c61509583c100d005602024000d086000d0141160030301940095030080d2007401254001050009480c29542c0049848c1000c0d102070381040106003800562591962407000043d0304506e004040c40d65034040540c60208002600c081d91414082070410b0450b5061095182b4140c039a1110320183c0310f0b00c00042c01c103000e84100c03241d00000c0c510900c15200d00c400c059001c0c005c00c9500040701009800c0341c03096007100c00d0740c8584900701c000d8135110f40001184a82c000e191075400b41c0220b1800e00121501d80d2510110403002500c25a9025041182c0e04008444c50b0390100c0303401c904545840c8041c0514800b66103004144040904040c01031412500400306a00b1101d03295111111098000801660005014070103102c102e8018510380e54464840301c1115402c0b980c400c2403c0c000b172203841c14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 502369379 1250 502368129 502368143
    0x11190807140603010b0a0e0d080409060e090109050a1b0503190b012117040504050a0902130c14030601110d0c0c090203040305160510110405100c0f11030c04020403 72
    0x40109074041000801e0341c0300308450307840c250340c5800e105000500c03400c0c0340740e801c00420034801e1100c1d070b6601c1807039055250010700c016103540c2c03a11422801000980500d40c07482c18050b0000b4101081400303101c1509a21401502c054040f5664070302e59a940ca454000011912100c081140d440410400d50041000c00740b0070055076160400303038507096060300401c0e01c002c0304074810b841c801d10001011810030350040544141400340d00c0501500d0185800c41c507481230900e001e204d108401d03a0851040140200d82110148910440326421662140103840109402540d190010304050001d158080c00c103040500e0b5040c40d581c00745003060228a50040447d100c01076070030074030000f40b6900010f4610010704516505013524007400900440d183c050040058000300c800704030702031202035051000b4000600481c07074007111400d070942050090902401c0450800c15a9512550124100b030380c00c01c480d03000d540c440b92a2920b03502c002c1080c0075050300c95420540050744484c03004000460150003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 502370629 1250 502369379 502369393
    0xf0b0a021e22030b0c030a1103070513050603150904050a0206040816120809060c0705090703091104061202090432010b030a0b19060308161506080307111908 69
    0x1110703450100c202c18100110254108003440014119202d45411446035484181c0326500e8500107009800d8030482c01c110303501c020051100380c54022000d00000d18456a0001405480e107092100d01c3c04200e41c501c40103200000c5020150070030f455103d40207401001581c12505898005c22000d5001c3d07406605541e1040d09000000d0040314151805021400040a84040300c2d40f501c4039180034495074948074080004110a07040380c1000140024000a4420051450308000c054010490a002030360745859980d1065400e18007032090380e094500c0c0c05a1402400070710307002c3c420500340003042100e0580480001a8405030a0011980c810851440c000c48140304400c207070b030030f41d0005000180258070401031400041c440d0003605911801c880b500d400c4608102d42c04a02408160348003900302c0c180050f585840000d24603200460324021816045a540885041003c03a01c0a200d2851290014012580055809132507210b020344014100c0000c04100f0700204603200c0a40c0c403400c00742d40040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 502371879 1250 502370629 502370647
    0x5040608010806100e090f0a03091703030f1303180e060a080606010c120903081903060e0c0904020a0504030615080f010c08310b0702010501120f0b0a021e 68
    0x100c03440c05441c5000240ca0340d81440c000c19070326134151307008084002c849800040d94100303003000100e070008a400201c403174040c01414050611203d5000d2001100080340560702c0e503c03400004c490248110b456003221b01d640c2c12400164010035404110200b050188401100050080c0c000000d0301c4112147c10a41c1000f2080000d0804150b200d1546508404100400b580c0c0203a00112581c2d04500b603e11188840f1100315450b0410b81c03c010002d040108009600140e85da5004111a44503142040303000d4417400d90303c01800d0225000e4600ca441042070501c1e82c02d10b50050840b0b50080c3c28800d080c2500c2c0d03a104e105580c0c00050440003411141713003c00503110100014980b07011408000c0010300c03414913008003a220700903d023940c541d48072540480364100244e10490101002512291440303110321f0456038502c41501c0c548015801c100000c220b1216403241c41d0890380c0e10640704d607500d07620f030380d124200e0403002808181003d40c02d200300c46000c40d00e1704003100c0d0104030b8801d00e56101644 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 502373129 1250 502371879 502371887
    0xf0c010f031406040b12070306020304110306060303030a11040f121a070504140d020607080a08060108010b0a08191802040621080c0a080a0905030c01110c0105071106040303050406 79
    0x8042124101400d058621030700b10700a103041c58000c5020f9030003007554001000820000030b6400c5421b107080c45a410000140704071540598000c2e0b2161144c0500c04994500701555440309440a0f0303410317017042020070901c10032503225607114814802042d0034070b44d071440440d400c9003860344401643e00a42c000081000758510303901c413040ca4100c2d440040303428603440083c104c0c000e60065001784100e10422041c2641c031100380680281e401806180e0301c0607145041c007e6908a2103820300810f962901042c925130041d01c00c0c0381600c028141050a2900801c800c482050700034100c40c0115042558400c018907003800344001a4802e07400d0894095458414042212001d506c28100d0591742400d140030080d4002d000c00b603035504501001d846650704407000b0f091100040d001450a0750006040711303052340243c0810b0072035500700e0556000a03000001035500000d01d50b404e003201d811111400c0c0c86c545c0076170003404c00b45005481e90b030359141001000c280c1ea5409500240c0102e600428100449a88 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 502374379 1250 502373129 502373147
    0x2d090408070302060a1a040c05071b050a060c02010c1e050f070f1a0a030b1305010e0a0c171807030b0c03090607260601110102031510021b0913050f0c01 67
    0x50b81c0c10096040c002c06c2c404802000301c10725510a9803944d40c01c1e80d49620410076030f81c41130b8000c0084003070030320711a40d038810600242c40b0349170141c8010400052645d0003225280a102c0d011384452410000c181e40b00c2100000980403040c1008035031a10102041c0100004010021142c00070300c0864140900700c0c1c4004036503406000911924001840b012031003000380c500700d004a0038085000c02d0001e0004804020034004442000d28040000600c5000040060301070800c03814200511000c2500c102ca600c0b200c0d1080790341d03040e0150003040141c031000510804c20201c213000c0c1c41249460380c0d40c10300c13042410307039025420820100c184000080306100d1749410002c681429030000d81072190141c0040348490301060701d040c003003001515a90080350201501705240c80210342d2460b101848529a01c103641070716008801e082f184280040c0002200700c161104809111840301c001402c21190708401000c61002034040803e5100082080044680c6000c007032000d4600e48000c84001008418 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 502375629 1250 502374379 502374391
    0xa0303050609060f1f020319090306140705071716030c020405090606030714040b220f110405041a030d020615010305010e01050607020a080616120504022d09040807030206 75
    0xc00c00403605090b961845042d45c0b030848442a10742c08410120b0580c203501803260b15080b0b50b50700401c0381d0085d47d84203c000c01130f82d1044904104000708610040603051007210b008010400070400c01010800c54000301c0c40401101d070300e00d86041101c4100804e0405694011004101020181421031801c0c1c012a1b501c45075000c010000c5160010008ad900c4087d886030140c080725a10816116131030340d40259030901302c050404840c046c5c00da1050f1041c410418100403e691400c2c40a15000b40140a52142d040080c44098185410402080300900c03034501c814510076045029991a600c0c00d10800d14907580030b8018102d2450000800801c1d000800040c80c101403404005200c01200c00e10890b0544805581a5032a000342e031000ca0200c80e0301d5040411540308001c10800224200564100c042c48560390b000d5821482c4059039040c2c0c0c0301500c0095004541d924044010380300040000211480a0400f0814180d010085281050169015554000d0001d2414140340d010040c06401c88 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 502376879 1250 502375629 502375639
    0x40609060f03051507080c0c011119030b01210e0106051804020a06030c0207090902060706060e18011103040f030507060e0601063b0102030c0618010606081306050402120a030305060906 81
    0x11801c0c17100144030003401820340b9401300001c03d11030040a42540183c6001c0f00086a03035a40f0140001d2840c0d1403441c200d410300029007407a030241110f5200300e00b001151140032180300c07162540403090201810343d5815040300e0399a14000041c2e55950b02c5011200034101c1c41d680000c608040c0180201e980168001205060074411031198407640019950212914610001080d4111b403000038020b00c9500d6001c4c00003030501c50080b0304c0c40712058540d8000e205000503000d846021484003826102404441c00c0300c840240001004218030984010b044d5210307290043c40c01000740d03541c00443e40400c144400390f5000c0170042c00307019040104c1e40701070300b60182c1302c40421000c8003030800785240a00c448501c02e800c120304c59040b40d0080041e500d4209003841511300c140b41c40e40724440c112044000e20f5a071903082c15000600140a0400c46000f10140c0784081c01410190702c4190103820b01402c1281c12451000c400c0410500c03d010f00d880c1e1600c00e0381c0106240c18100b0802001540140c0203d2090f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 502378129 1250 502376879 502376881
    0x110f010510091811090a0b0603180c0a030213050a150806061801030f02042d1a0a0b03070804020609060a03020d050c0a0504060815091828020d02040609060f030515 72
    0x10038050000700d855901d01704ca0501c816550258200c004d05072030381c1000d82108003c42442003000d0500b09000c1903110354001c403104000c0003010044040500d00c0b0282d00300705110a01c045101c4141c0102c2e500850312500850303029403113041801c407545c40b0381c00044250000020300a075442c08050484505601c031540403255411515010680705000b08001e01c01d44c1d03110000c0c01c40302300d0001c3c14104103000b00d0b003403449042e0b180c021401628140340d00703100c1d00b14088202070040ca41549007106480d205207804d4111b5031090303c203071a41e280181c0181d0f0320203410302820b11140c2d0b80300f006058490032660056110002d0300421010b07108054240300c0c4002d001c0c0004091603601030280c038101d4025182100840c0c580503102c116559958640399003240020042000c50382c50744100000c5141520704a5035015507841d80c6190910344403180c911403c0d5000a5000075180c610041d00b0303802d00061001444e1662065a0022a81254004c2d80310007001c020400a01c1818003178a50460041c0c020181c407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 502379379 1250 502378129 502378133
    0x4050d020c030c0a090f290a1203170403021204030804050906040b01140f0c010f0209030607020604031e0201140a0506010e09011a030c0412030c0c080d0c03110f0105100918 76
    0x1010134005d040226030b890380200701003840781c1c11921100e8984090440c54140d9840c20080c0100e800c11298042c4034165400504000202502001e0743c0d0595200050000e60b04c141d5100705601901c01d0b401c5110307440440142e5402c40c0d0003013005502c218030305a503d52416090041083c0000c00c03940c4681d04e05909540310341d820881c5800c2d82a080781015943c0c0c980c100c1e400100740a0100b200c1c5d01c561170300306144181c90840e80282240c3d0011000c0754016a19090b0407665010b04440007800100192001010000201d50401c00c1034150b00012074503000010b004100c0e09000c64050880c10780710820700c407071540c0101d16465181c0007644d00c0c0391590304020078210011540d08407920040c1000002900c142c2425059402a0410008064007a801c900b00180203001c0c0d0181511445900240000d01140010321100002e9072900d0344d02000c10f598a05a5040381c0c050202c086500400c0c900504400c03080c03050350703c2230407072800c440182820405c000c02220f83c201c0e110000c0c0701d00040a840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 502380629 1250 502379379 502379389
    0x1e17120d020a200a0813090207120207120519140f0705012309060f04030c030c140603090c121606051902070506030406150e0403030222120f050c0904050d020c030c 72
    0x14a81c10600d1036541d1444201c81d46c481403620750040803034030310201e1180c0400c440c01d0034407101e48a00d582154202c0d6115101000389c03943c801002021584110714040708409581141e0074140c1c021000406403081803100306042030340c015154082d94005400900c01580c000c2c8550402900503104942d44504e011851481c512940400e03c0c860036000c902d2a1441107200210742c00307194001262085550f45c0d00d04000507079120b0081540488500e103241404d0704100c02641c1c41199980002c060810001c014407802c140c5a850484283c02500da04039140c2101c402d00e18010070f025030701c055442d00070001954100c000181d008046411424081025584820540b900030390071410004042c803100c4032500c01c144d4160320040c079404030401080b0034180c15074094107200c059051850820002e0301d80c0b10700040d041e070155a603681045481d0b04003280007807040190551050040703a220100f08400a841380c07800f140c04541e503602403405080000e6041c07054010011059004065031002d40700068 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 502381879 1250 502380629 502380643
    0x20306090115140a032405070e0d030507022d1302130611030403150b1e03031c090203101e05060105030402010503041a010312091e17120d020a20 64
    0x181d0881d01607880c0f19440d0354034007880c401103a00080000c3c020380c07680380307525014520200d541c100b5403030003000460060180400b0400208010052100d1503600c3e90180d80a800c200d5050785c001c5041503030405102c8043e001c0d1008880741840d10b90174a044d0b90200088850348103d400f900300d00520075018102e21002462041c0d038944d0802801842c00401c036180795018035030014203000c5102541d83d0000366607600c003044401c01076821704000c403a005040c03144e008440403425050b074000c1003a4121100c685d0344403801c84e003041710041680e50840c0c000034542010402030464056660059141005075251804190044138105200300e1400b040047e119020082019052102c000009820070126000b0844080c1304a40c200005584030700b0004112107600581d000402c0003aa0301007030061114042521301c200c0e88031203005440c24407072007110003041c2101d500400d12410440901c0032a00c10054034413020684030058450090f104000c040518101d804140040e141100c0c0b80e01800202d0a2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 502383129 1250 502381879 502381889
    0x2303030702011125030b0903210a1503051b090408030112062306010923040e030c06130b01060e01120b011b03020a06050105040b130c18030f020306090115 68
    0x141c43c0112403070900a051141400c1850104800ca00c440803042420081242c190707801034010602590310082016640d11034401c0843c40581001c1c1c0313000ba42c034034125805501c07420307080002c5008140150320171643c0407107070070440746900005404002c400d489000400d42160465000d617460030292035450003440107000b10034080621548503800d000007a04244500e80700c0180d00c0c03182c0d04030b00003211001b040542e210350000e041514000340780da89190202200041e403440f440419490340c0c2c100310061026030400301d91f80c0424450307003448000038000a8403480390403036400001d482900e41080301c90416000801801080d994248290740d12862681c4440c0e226880021880c1d4490010b8460080d09141c1c603c0880f1000000b0b020541d000c600840c45030b01c03d89003400b00da40c070ba50410090301e80c0c1c0c01320641c00c5210424981c2c0c0340c40e2560840e003c1b40d04a810301e08a00c9040c0c2c038030300002d0041c42d0000d035240c070300d65240032003181000c10a0039403103800d00b0300030071001c1502008a401d40116201d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 502384379 1250 502383129 502383137
    0x4052e05071b06020a120f090b09150f0406020115030b0c1803010c12150308070803150604030807031706090112020f09092802130507050c0115230303070201 69
    0x1000400003904454a4121140002c007449030f6600c8100941d43d100703914007155500503821400302450b0162070903421802d05a140c040c032045c1814403212040d0005841203600c8646815412200310131800185030454441003403070b0f950750904501900351032202c0c516070440f43d104801000843e0191200d030b6007003100c0100d00d50740c40c4202803c804d100341801104540c55427918054a00003500510040b03030b843c100a4080c00521781100120889102c984005000d9500410107440011080001141d00c40b0305d0800c5c20381842e03c0c20021a200b5005034000703c0781e0403000031780c007414142c1100c03140030380d80030900c003030800f91500703a0208060b000b06100e0042c02401d0110f0f030f031f004c40d07490308502c05074100c014200103454030381a04140e540307081d0310b000c051252070036000074003140c3c0315100c40000d07541d00030f00000070007146c00c05104020000101a14200101845040f02d221420b010301780e115103042da41010740078140124070082201540c29908207111004940c0d01c15280030007954406074090030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 502385629 1250 502384379 502384387
    0x90a0603050601261605070c0603051801090c033c020922020613090213090e150606090103060b070c030507050a180903090b0c0a061b02100507021f0204052e05 70
    0x5c0079a660700170a40000c1190709200c502083c100c0d0300d5070110342300c2d02e03200c1418010509800816422240c01a2018042001c000424004110303041610804a00265a6203034921b241150b6103820400744d00a40d0b4060840c1e0081c60254030700081d171186c20181c07941003a5002031140e4030f02d54410084840003401034802280c1c2807411f003035032140c09000b040b410100f59680c00d100c1c2c081d4400e4510074080c00d000c9500d828240382e000d110014541c00545500450103d442d00c80314200101908040001d0341003580b0b9200c00311304864128060000c10348145007500c5045d085142142c208015500102d0003001e1408007007003100581007403440c0344030100704001021034190404561580082c2c11806a4003400100740c28004030014114002d580110000c001031292081c10500307840e0034081c4140141d1015000700c41d20022580440e800c81d03001c0c01207601d640203007046154001c1188a6642a890380814200f0080c01c140700414421100e8001d65103c501680c0161900708159505002c10098041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 502386879 1250 502385629 502385671
    0xe060c0c010c020604082b020604021e0406051003020c0f01181415040c1508040309090507112a060a0f081008030d0b040b09041509020402090a060305060126 69
    0x2008440c00342094500344c8a5412030a0711407e01002c03031704040314180d01e08035112604d443c4081401801641c1c010051510b00010814983c0c507288440c010310f07440f583d01c010014840e1780c0c00c000ea1401d401251030140c0c0315140c00380d21b2130505076400c80741e06684c2d041005403100c02c01e00340320041020750b01421071240300810004451038a1104840d0081c0e042242c4144018880001c881400700c840301c05000087c4010100100d803600b4040e28010082408004103000d06005508a80d6001d070b0589810014400c0e4108a549030901d0b0642c1c03d41d0031500c40414004a005913808044050010754039036180030514440280040c0c1015502c00810980c400410303240061a55540c000301811800c890b02c48905d901e6140061007c105110f02c650326100c00412141095404503100e1078011551000050115002002801400c4030880c0d10035820040c0582981d6881e5a090140000c1d80d40010546001d1002510617080112801a88000f61000c40805020716080ca54031041c80a000c40b4414500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 502388129 1250 502386879 502386889
    0x4090510020a021006170d0e03060408160510051504020903060f04020d14010203190e0c120106090509070501020d021504020409110306041101030501090204030c03061a0901090501060e060c0c010c02 87
    0x1800c2c002034240e0420074000b488001c0506e07210300307400e03552040c3c0310b406c8025501134801d400400240e54168111500140100704640c015101d0f28120001051440004e03648440c00c14625001e03100030b03a956842030000c0384200c040411454002541c04524124070200042e94800000b054011040c400342c0000303045440d128445901207a0058000e890503400c03501c0c1c80c0c007039082200c1150041c51040c6414442074541e0182e60602c200c050098410404100f0a010f01b45602e182e800000e0f64940d0760021324405688181849146408090625141407400090030103011482c1c1e00c00b10f5102040d0319072460101540740c0d40190b8101d40c00281c0e8040c1d442c083d07403051100d480e1035070704d4000c0d482040284407140050303e00c0c9410980c0d04112030b07a2610511000c0f80a10b00002c1d0100901541c18400207069500a109801407413100e031034250381500008a1002c000d030005010a034903a00100419908484150b503166003c40d41c2508000310310003a03d6440302d21065103130400c020301c40160299110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 502389379 1250 502388129 502388143
    0x102030c0601122906040f0b01210213061d010c031e0c02130203040302060c0f0a14070f0c030c050a0506030703020a120c020d020610060e19081501031104090510020a02 74
    0x40c0c613911586500e5140001020b90700031520036015a00342006c03499920040d20400e220980141c44c1e00010308640c08581c0880c59482c801002c803503a081004428501120403500001e00942e035408113400c1011008410b100d5202c100ca0303050060700d11400000030741000b5554801e4803010800d54040c296000c0480303a955070580041d40010041203801241344580e00110700c52802a002c86036142c5900165448a03c100611304100c1c81040c000c074140346114110300010364503124402070404400c0c2d154100c2801e040b00c8119001c4503c004200204000130b4864001440c1c00c803409111540381401107201c0d44002808003040641c0061480303081406461040c80c4011248004c00c040d055a517006541c1e2038482240304054860400002c00e18451900c643d000e58031207540e80502c01b000d10062160200031000181344821041d400420302807410405801e240104040c07800007545035003401c905210b03060f08001d004900b01042003020448c002034401280560010043c1c1d5121031030822802e101c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 502390629 1250 502389379 502389413
    0x309061508250501050f0c0a0605070507110904110f1807021510030c0515071b1a030c04030b2205010b010914030606090a0e010f0207050c1c031809051609050102030c060112 76
    0xc40c0800742f2803015030200103803242c5889884450f180c01664400c11480c0441107070000d1010400c244508020301b40200300d0b0003520400780c401c210105918a0f8200e490b013085522100591200e0075481049060501064000320010a40d407445070864851460110031405a64080c034a1036840c104014012030840b0074840d0040940c5000701006102c0140401c0c0a00c10007074207502015818008045050460740a00310150440389094038507507506050103c004c2400210900e031500801d900240c1d104810b0005201300c2c00021004003460000d040907205410a241482184960400310340300041d81d41c0e000481121001c40f20758640076a0f40140c5030600c08a5065403c21641000310b0100c0d0b0080d1101a204a0a41d0751100009050005045005d84003001210141d10f86001290156035039681d80484482c070000d815881c1c000160665405a0b03030314204088020a01c201180e11401a03000340c00b091016500c0c040b55444140d035140b10601440b130b0b0456480c02c11100b04442d155072030403900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 502391879 1250 502390629 502390631
    0x90801020d0902090a14130206120703050601090f0b0304031d0a0b070b0a050903041a09040c2d090501110a170301031106190309061508250501050f0c0a06 68
    0x2850882060002e00000c60b403c13406500c0c03203004909440550b029031098006544404080b5030340d0a02240240c45480e401641c0050381000000010703070381505064071410301901c01207050b0500340c00061420300c035540403200610710020148030074407011080b26002034041c03038041403080700140005295501241143e80c050780c00840045c2e40e006a1018010385c1d40241500c080503a500d42c0d0a0007910401c4403004041d40041205000005920000c0c61a00c21003480290a043c07015001c1800c8400042540001c40d1103122030984010100d4000810301171030310001c0358010495a00074064009501505040c090354070f1380c0018070201044041802900559264012055500d280455501c00c1c00140c652400e520701e075035070350b0238003c0442d81441c2c8000e40d10075550540e031804400400480350100e8075039031140c1b54200c845061040c2400940054000b420b6582079601c000c0d19042c2294442c000c010a9025003002140c5c2c0200a4079403036035070405015654106904094100070451000804007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 502393129 1250 502391879 502391887
    0x106050a060f02010e06060307050607060908030c12130305030601030b060d06060816031802010e400902030a0305130e0f180a2d200f0919050709080102 67
    0x1480c0c0c055111030088142e500208124a6583d50381a190841180e01b507800d5800b11504005604150b0010401c441c041c15001034070321800d90b107560030b55000743c400244490010503100300500d0034021140d00050f4841c4c0400102d5640e68024001c3e00000b00030505050f0f0300c501000d9a40c0741c85048820928011030100320850326444080c1040c42e060354100d40a044045120030501c0c007a01c1a9800e2880780414914200709030f90044402d5102000e489070070820700a1000c0c02d05020032061030742421740c084d400c02884440c400f10444444112036100d030702410300c60101c001da1800325420b010150035180c0f55540d5032031070400250b16102580200f2500600e1010000d2600c94041114054180c15001c2c480c540040065269034030f6884802031f10142480c1044a58400b160344240039141ca1f4403020803103640281c0303c0740c4d4442e040380d05d4814a490f00741001550361400c3c6901c82d000030012111021075045c00c0d1801c406450088440c1c481082d9107201040403140542c85103801805038000030342da2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 502394379 1250 502393129 502393139
    0x300908070611040605071106090301140106120209090a05130b1f0e150103050411100509040f06121203020405120d020d0f0c0305130b03010320040c0f110106050a 71
    0x15540884000c0c0c800701d00c1e08803280105082c242c2100c003107030025540c06050441e1600c1d04c5a0b0507608010080c1e1102c02003002c139506460a00404540301701040e0510019858100040e20005402c0491026644100483d500d1603990001d91600308104002c00995665800411100700b10200009850a8100d00820910000076111007009444200841c0c00301035840102840354041039442044042c40149980860351203a03110300d0b4007501407100e10003120103502c0450894001c0d050b20b0000101d00140034000c60419002300c8141d070faa82d9008000c0e4900d06105040340c0c440d612070003800010301e1404101042d2098054a01901d0000e01c042103c56130030380c009540b0302000e050803003d070182e800f68401d11341c018111010600803a880f00550103500399401c84040e4424001807581d0006100701160141c00c07400510701a500c038001d8070350302e00c02d2281440700340031030b010601d44a80d0502c0c40400156521010441400616050603040e00d14070415003809004541c200c076030410021180026 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 502395629 1250 502394379 502394393
    0x6050403170706050103080408150709091a1905031c020307020d140105010905010602010f05100b0c100509030c1614090408120a0c17010e012c2502030a3009 69
    0x100c2703210600316860f91003c03110340c484d00c1e501190454042045280204005400741c3c000d248520142c14003125a281e115000504140c1074071144e2945551590050295003030810400d07800310601000c45007103e0030400700075528410306000074000c2c040018030008001546030f41c0b10f42e82044800038082503840d0050f41740200405d10a9800542c200b1100b000c811714148541360040d50526a213000361414070309180348940c811214400c0510481c6070610740c4500c58030500b40200d8540380510342d108000810b15103000860000c2c18081e4070b1202040000049080a080e41c20070151102c142c01d41d03c0b81802042ca00540d403100d001403440a0401c20812280d80c0000040c0310b568646080054140b0104881c842e02401100c02c2c110340d030b500510103400624000c00c0c4203d1490115226030728030502c1e40d0b80303a5500341d400d03104240780603040c0c0e244400c041c4000c4841c010184003c504181c0410002807450340d2440c0c0710200c3c07001c5092901010340420142c0301c40307800b455400303024019491800d20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 502396879 1250 502395629 502395637
    0x6030807060b010513051e0402040e0105100f0206070f030e0303131b1211060c0f030d0f29010509030d08011401020706020d053901060503070605040317070605010308 73
    0x1d420900d4400c0100c1190702038010b40b80c462400548122199042c1001d001a1800090480c64000e044840310324044e0f540d0300003000a0084561710301c615505d818188003c661100982d43c06004949071840c1035950700084c620360201c85d9103006144a0315008050300117110011000355540000810040056a028220740036240700b200c026025141408100c002a00c0902680039170301c4118282c1d5010171075454524a05440040080c2d21300300303d511110b07140840d10f0f1740054141c0c00214140c44060031a201e211882c14071070400b840318416a03915030b02c005645060001014071220780103000d90b4030030429072300d04034000b83c1242c18402c401000904051024070410060110499110200d5440400d10b0800c660a0f0340090010003070b2601c0036240c9070841c4204030031408a8031490b0118005035495030901c0f800820414000d0b5403045843c80c2942d155800c1140640c2c01444100525940003048404480d007200c1004550301e0b000300c2c18603c1d403189520203031110f8140f0b4000310130301400380014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 502398129 1250 502396879 502396883
    0x80a11070231020903030f07080c150708070905090610030608010c0203130f05010f0804050a06050a0203040519050d050a140d15080d09140607120306060e0d0b0411030f0106030807 79
    0x112108150b00381034405074842ea40500d50550018804a4044000f02d00074150041c81081a0750400b01c100300c90618003d040003406e151000c828050000c3c0c10f4000c00e40c40c1c2c00944a00d0259045402c0402184002d5005044540988007410020f40364174800d078040340c05041100000d0058180c0410000d64036041500742c0030303803011101030010b402d00e0010f000e4000ca90307043c0c460b0711034101040800d40b40300000030007d131100d01440c5014400140c03e44501840348004003c0181c880c14035040040c0f500042c4115100d50501e040c3c41030010030000900750300840030300d01c3c0556486005580803034001d080e81c940164001c201240302d50050001d074001c0010580c404049454039561012850703031b14180c0c2074014011841c02c0400b40200701180b000c0c1c0304072040140240745000c0899807060581e01140450f100000c1e501e510600105a22040c852280e03403003103465141a0b80d25868220042c0c402410040980c80d0002d015005a10144003010811881400800c82c0594034100340015911000381 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 502399379 1250 502398129 502398199
    0x90f01050a06212307080f0f060315150306010b0309250501030c0c020306070819020405151b0f0604050706090605121b04030501060f090c080a110702 66
    0x40071800502c90041c8401440c0410f802c0640328909450010007400e6208411a0740b401d1075a80340c0c1180e50745107125004d800c0543d101c0c006407a0080d003075803107010040c0440c50740100d0790017480055a800543d42401c0540300c000344010b611610342880c0c5200b850300c0d40b240c1501844d8000983c90320104050361050541005a0b9126040c0d6140c0304082400351102e0031904000e518107000e194800c0d403280c14910241d00b800c0f13207040c40c0754001a00d041400c032008400507603004100182e94000fa1500150010040410360805081c07074002143c1d034814224a00e030381000494001c100c000418500c0a03042030304010b54280780c40601255440c0c510803a0180c0d6035125100001900520901155045403401d960311401c0ca01c2002c1c01008844025180383d411880e090502d8040e09029001480203511402c000a80c1c186440c4400c07135259040d50203170840b54540328140300c045d0340020b00c00703500c00c54814000031002180c82c0001020b0081c6c0101a41040c40c5044140c4200c0d2a44139544410b0400d0203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 502400629 1250 502399379 502399399
    0x63705061f0c030f121a01031d0a0303050903040b0403030c05071401120c1202040602010c0806030102121801020403061505030f06091e0a0609030f180e06060d0b090f0105 75
    0x5600000001d40ea1020380010341607036500300200784500500240300c00545049030b10b001c4c44644a03026152840c0754100b08800000341c924407503806208017169046150740841c01008914100707600c40842a0002e0285615003001600b041810f004070f8000d0070070140c0e510740b141e880e800c00a2111202074000c07102d9115801022645000d201842c136001c02050b543e0707007010200595000080c02c1400303010001d01a05104809044040d4000380c0b01502c0558000030711001550001021681302920090082c0d104211300c1100000c100c1030507a2000584030000b8400c005400600c0c0248515800a0000c80c9048404091840d546501c0b6044840c1102110742c451075401b5001d440301070646207400d0652103440c425010243d011404282c1c400c1078810380746008110744444040e00d107032500480024480b81040301e000740d0804074014007075403824034000f4a907003868450300f441600540b03c42d02c03628000c1100c800311444c980001074250006000d00c80c440c14612588404c800007070040500c81d42c2250 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 502401879 1250 502400629 502400659
    0x5030304140c030709091b0608060a140d0602090d08031512030307081f03082a03040303020a03080a06090e01050103020102060903090604090e0c0d05072606370506 72
    0x82d0016400c00000c002d80b2030b007840e2007814001094403080480321038a0220141282d6004066540000d20007500d03000352918184040080f40300381070700200709909041f4515001c0f5110304646c2d0740d100381d10520050352864a40700180000803030080081000d40300004001006c26200e600800312070080d210150b00f02d406060040c0c032800f040b42c400300001c00c144002148003446401011030008100780b84a070345916500c078a00c6540c0405651800807401c1c40545c0c7e1b510360501d81d83d120090280000d14101421907400039100d507000000542000054004980440001e5100324020705190b40b04000c601803c0e28658060039091100364054080c00000a0803168084112150118020000d514003803c10461034014010705021410b80c0c4140070701200c003501c1b0020b500c0c0c0c0c1d540c0910000c1001030302d04200f0401008014050384400c070148040d1007c50741d80001d00a80000000e41001d00032121705601461a9040c00e11061030291000307c0f550961240391302c154000d0406440040e4281600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 502403129 1250 502401879 502401883
    0x15020a020d030b0904020108041502070f02190605030f091006091b0f090b030a061a040e07180e0a2c01050a050c0304021c0b071d0a0b04090908040806040503030414 72
    0x10f0724441c1c00c030a80d400045c5c0158828489030341e1041c441c1d8007010140c100f0340060022078100340021614004564a040c0c10740c81d148140002103589410500e90250070300b00010101c0c00080c1045580c090806c000c282242414410724260b1401c0480400c0019602c1c0741c18002b601080c0d0442ca810013103180d8405605120f440d000080c01000d4031403140542c50300509203190307480180018019681c0304d002065500040a4030b00040c24040703151a00c840c201a00c01402080107003038001400000709041c900170b02901121000c564424600003065a6010780c95170150000000c0c094050b080e5803180d10040880050304494004150000c020540d02da03608201207034003c0c0d56408140b031041c4001801854044103002400188a210710f005079550390f114061030304250340f40c0d40440c07136040a900d09610081000d8020b40e03412101e0b00c01c41c51500312a0801d41c49240540e4a04075110103140c024400794134201c030002c1c140041210018030b0103050403500c9420030703242181d105400da080324155401c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 502404379 1250 502403129 502403141
    0x3190c0b040f30111221090102070b040b060d022e020613060b03120d061401020303060a170a080f04050a12120e0109090f05040b060d1707020d15020a020d03 69
    0x50381d1820280380500342910041c0c18a1444812841401780c003a860882850240804403007504940a00310055020b804e40c0c4440246001c07002d0b8030600c10700380480c1c1510342964006070081d04005594441002103814a00360f11340283d000799980410380514010b42c2d45170703281c0300c200d0716440380c0d0041e414600300e0701d42500b580e014158400600d66174020800300d80c88141c80c0200242201c50b014050180e41001d03401844d80000040c1c0ea865003000f41d44041c50181e241d0560910245181d46406400229104240d000b02041d2600d800c44030001c103c4100a6080456080392501d51690805840500315034045c0c01014000c2203aa0000500450944070000c0d640d0382c0000c1c16030311405088001c41c0c0003140400c10321704003d2404000111605544101c9408460f0394101041c54074160030303e900301041c00784c070b054091207003010303c000440d0b02d00d581340031a482002d103859078031582d5000103112140001c001510054038040001e000450b03e034014000700080342c00740c0d131402500c000b0903011a00c1c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 502405629 1250 502404379 502404443
    0x60a09050303370b010e010c030516060f0e0303010f060e01020d110307060e01050601080c0906160f0b1008060105011d0d021333050303190c0b040f 65
    0x210500c0811158035001c0c240b0703504203400c2148448070543c1144503005240600214154056460310048000d50b4465240c280c95002030900c12000c00940d90000c20900c0392000c21080c801382c02414404100e8181c001ea079114080210278000d1588215206807240c1c020300c038410403e030107a44006101802402c0080c49d880050700035103d01215007400762400a41e054078680240030070070440000803072510910000885034400041c45103440340c00075190b41406015004c01c59400d110905141c2e81725000c43c1c003065154074520b2407034005403130904818070388414000d181d895554204080e01404003004002c541c580e02c102c40d020b990b550015201201c692580b4000b00c0940b291549d12400d1030321580d2078151002d045500318440000c641000c8030050307400340b0381c90107804480b09070300c642d2582c076114521400000c07190424a0040025542c2c07007a00d102c84d0301400c6c0c80745c094407400d010f8a1640340f500d41250b07442d0207d1400d4944600440007121049499940103a06000c0800c643c8a82d81c032582 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 502406879 1250 502405629 502405633
    0x40608060705130302090408220510050706090b0a090c06030c09050120010c0e01020d0e1f0507050706030203270c120120040819110f0a081c02060a0905 67
    0x780310640100c40030b510800002c600c9440c8440c00100686038102d0592145c2d025003403194a4105480701c0502e0340320500303000b41c20501004000c0c0420b070355000c0420315810503401c00646d80e0b00c1900c1c042c40544140702000c0c4c1108009020401c01c009160040c02e1104e101d8007410289c5901c406081d81200c07900450307400040d0182000303100c55402200080260140060120708800103080c0e101e0079504840810400200000b085280a5804104024100101d4100840e5070400c00010a00200140d81c3e41c801d0300444000f0045c84074081c03005c80352807540040c203854000303071540009030183d030003510b40b00394107a4490030540c04c2403041e1007504941243c000107044144a14820402031540881102c1190b560300e4080112011340101807401c01c0b02e0081e51184c9461600d40914141340521000010b459150300448000603a411444030b6500c808940e40250900d0080c046014031205401990705481035607030040340300c0401d404020400d0301550842d212941c0d00d03120b0b03105889044400400c03a07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 502408129 1250 502406879 502406881
    0x1e330c1e090a090e0f0616082e0905071d030d03050402011202070b0105030c03030304080d0f020906040323032502040906050106050409050108010b0f011107030203071403070504060806 81
    0x2400c1420001d10441e18000c02d540c01150320303042154221000b40c0440c1600d6800b0501600032510180443d81d401249580c103904103150801019011090040814000b161100307946e4407206a000b11419032031205040142c281d0361141906c00041c030b0162941000700c2d05142c0038070004130550400361401c402c0600a0039a6440c1203400b500600701c0540103c1c180418000000c030400028409850424001c6000c00a03551501c1d05141c24002c031400d985001e90420000c00000c10010b908454401200640000b504040301541800900824070001c0d400304000500105014040310761010555041c103e03a45c542071101d060340d54034841c5039480681c154040c002074455045800810b0b41c203900180010603802103d5aa42c02204d209170040030104134003280034000d0120301e20805015040c030390001c20520a0380d00c00034403202400680b05040000e64060700c00058802c0c0042c10003990b01134201c1d00c400340c0340c0c0503e19945040c1c1c65181d00070311031810700217094a814000e4008448510b0701400701 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 502409379 1250 502408129 502408177
    0x31b080a080412110429030a0822030507170f0d0813080403140304031a1b0307050d110306040b09010e0423030c01020d060509091e330c 60
    0x100341206001900c1004075081c0c6041507803164042c00032142801101c0c40242c40c6c000000b040950035040d42e95000391301800c0400b0006001ca030441da07481050081d18003200c881e50f628000006881d400040580c000d20304000340c441c0ea204c0242407010350303182c161881d1829501030507a50304002d5410f00c00156605002ca509071140701103524050f4000e0390b200b40780540b030b511010451207910b01141004d0340009010414007000c0071076201c810341c400a00445609060781090781003490100782c07141c40b007400004201054015022202c3c0325510110620510041182030200c0703030011210389000e00e042882c2e03001d15152480440b1f0503640e0411011181d0749860703c400c0c1c0b02e080f941925140880d8992032203611b21004001404829031000005a036886445038203c05940783c40d0700160042c0c0014060204860000c40d00c16150072918034149030410f401501c039850404801c0064074558051000700800042004010450b07030300b40000358040341c40d0310351940b40c1e922520540c520203c0c240b90307032162 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 502410629 1250 502409379 502409399
    0xd2709050a180506090d0c05060601031a100306050f0409030206131112030702011b05031b19050703020a062a1109010e04211b0516031b080a0804 64
    0x207081007155800092802602040d0b5904140501c000d80e041d80c081c074100041800c04000d062110000381c5440740d03082c1e0f06a40c0e526030b03500000d0881414540c03a01c090100d2011078402d81d40c000000101880d05640182801400805141c080d507030041c15140c0180303945003400c3c0a510041c5130f050b8000c090640d560764038841e0200042c2d50464040d5001e2104003010f039180d00212140c9a1404003540d690040c0b480050038645100c02a80c41e01e804103803594010910100607600501c00380009822542090140e4a060900361514202503030a1081070f44184100040e03070600b5a442a10848003ea0b102e58040d90010140c12a40e403952540e5040080d500c0d40c4900c0449409210f41110079490207400000f40055409800800e688001042008103100c01c0c03050310b99030701c000034802d28019090704c1d8000f0322000240404010303c10404441608200c2d04001c003503500c40305001e0b4035403c0d94480c0b4000842c0300c400c202000c00400512400b00b02200d01003911003005a02059a0b482e0600e01100780c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 502411879 1250 502410629 502410631
    0x3c0f0114060d200415080a0e19080d0c050d0c0c02090408031e090a032607111c030b041a03030405190305100b012319020f010501080c01090b1e090d140d270905 70
    0x280d80c44812f008072a10704000b0701900c81e4100064862a45840034218141c045a01c0003146004002810a000c4050303142c01c40015017180c1c01440300c90f038a540354010000d1100042c1c080800d50150b160411814003c04220701c102c0d240700359116080f9411801c15034075103450151a070010038151001242415004080740c841c802d00000039280b9400100d0351920900079038a01103000b00303440b00240501490a486110241100f05c001c4e29132400c405000f0a94038000c41c02818080e1a07054440e03140701000d40317080c0000316400b100310ba6420240180b040c020300005d55071a404110080005030800381c681c500390301000003030720340c4c1414880031181010540d83d101c803003d019030241102910020300b082c0203d502a01e03402c40203051005511000600c04a0b030f9620440c10f034141849010240000303043ca11142030444250540c548908000156040910302c4006000100e00440300070310000c080b0700303003541d55116119520000804076040103800c0884030b00e26200b80680ca8240084a0603030301103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 502413129 1250 502411879 502411883
    0x8040210052a0705131b1809020403050d030605060a050915070204090c080706021615020c0616051203010e3c0f0114060d200415080a0e19 61
    0x2602e00c000164940461400c0609020581d420200c814045030510314103003124001007031410044010703e042592851716445070042d08000c518217040c612601058500000790914400c1155183d540340390003680c4956102c44140800d007440d02c0001c8514206095824050b80c680340e0900e440500c01c1004500e14123581d029003894020b110400242c1c0b00c5100d110440b030b20590740004072a04010302d0619000040c0c0c0a00c04550000c940c40844440811030b1004654128012020701c54450780f06a05040c001d04c4041c0d001800803841c80c8000c1c039a4a01f0354140360056054a1454401c4811900584400d0107a00004100100421240c1140d06550050500b10100d0b0310581d110080f440b00400780c441204c1130f14403441c1c1e010322a48910700d03840b00d4010146400018060600302c1301042c400c0c0a102d20010b4429076480940003000704090070f0601c482500e05426950b55201c00c1d441c2440920580d01c10001100000020240007140c41102d40b02100d40d070080041d51096071612200c1c01c0c0440b01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 502414379 1250 502413129 502413157
    0x70605040609141c060b04050903031003230d09140603040c0e130c090b0f030604051f020913020c010c03090809040c030603140f06070f1403060607120315060804021005 74
    0x50300b41d207130f18030320b292a8880c0301d84808680c1440b480b0810094920161221410350003c00c24041c503021400304282c00c99500c20300440c00300e513403400c031281c0505c98203c1100d06400307a00d080b00881c5502406034000d071003400c4000c2440300305400500c0b441d804211001011f03040c0b6030343c050008045000401d44d00003000030003c14010151354032030701542c499a0110030a5500c4e407904440c0c1d880d00082c80100800d050340240594604cc0d11055607442c0c204404041e00001180e00b10304003022901241c0b404035019004081640d14540d400b402540500c0d0114019460f00d010120458403034042d040003280c1181c8072904040c2648104001400c91101c0c81042c150344210000c0020185c5c0341884001a03850040c00600718140001da0403c0d1000308000200f1604640c04014503070480484152000131101d190f441e80d840001041140c07041082c06001d045490b40507820701c0b5815000001406408510700108990303480080e52401d0090700c0c000d41c0b100080c0141c2010501c908007801481c2d5400300c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 502415629 1250 502414379 502414399
    0x30b090303221103070b13080c0603060409031e0806120102180f13111201080d080f0402010c05030c06090c190e07030b0a0b0702031b0d031d190807060504060914 71
    0x7000a00c0c10917182c0c040340c040c0b0310118a21403102261480300000304031003030103090080303a030340c0004a9070700c0003c018034071442d074680a200030b1500c01c2018000401080310028401c0c503d40304c0c060002003085480601c11001d071520304546890600135204035103810542a04a030042c2401c01051a05011119401c500036015040c23405000c0e0164014165058114a82d60984070400c01d03061001600081010744c400b407164403a030399020b0145580844200c1c500c0303070103891310310040303441903500347c8040c1980c44082015131502c4800b2444500a64204c070403583c10340040701c24001056000344c0e0740a40031960610421100500410701640b11075103140003c0c0c03003030001000500b900d8440d040307610b84c2e5901150940c11410104540058455500d2500700d01d50543d4000400600e02540e00070300304001600c00c1d2010a08a103180640480014a20300b0132000c0380d80d001c8040943d510903078070039100f401c00001c0c215000e0700c01c980c241c1d0070300d50350541d14030f00f4410212070341600f0803011500320031085 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 502416879 1250 502415629 502415663
    0xc010306081c140a11070f0b0406050c12120702160f03080d0b03010c02030733020d0906020a020c0a050d0201080115020307080714060709050906040b010e0405010f030b09030322 78
    0x40051030303c84e545868071030010480d483c0851814016070000001030803030368014404445030304265000c0ba15140f51480d95a64006103a030f050824501460b81c0303490010503c3d0410920120300030b445401310b54210740401100c2421003045a80e94070811944104510382840071503070880c01050710302c01c80356001c68032420f840040303401c5851150710800103800200d015420003071000785006800818010000b0256804812454003440241c1c0c1c2c050440c0d40010202c8081545403c621000c0740c100e40304645a5070108406522103102000b642c0c4541110803010a46240421031701c40b141c0d40681d1020101d82c00c0059481107205800d0501c004d510081c0300590010700b820b40142505841120400d280501c00c54145180a00c042d1069081c40041e0005014030744918540756400f0200301c1d4041111461080141c5003a149040c038903030014107203c000f0400586032090501100d104520f0700080f80d8822101d651680020750317011440710310f41803424402d8070707002e803011000c203000b40304c058803a8841e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 502418129 1250 502416879 502416917
    0xf03090821040209070206010609120f200f0312090d05120c0703060f0c0c200a14010806031203070810050d11040b0f03122a010605030c010306081c 65
    0x1a2035030714000514608001c03c40c240540382c0d94111910b80000e2a01c2d5040a1020740303203280c7c5000d14104100190004800d00100c0c2c5500c0e8005a007000721005c1802e200281d080d0408025408140922030507450280181400a5842d2159900c45a45402d205c1c0840c104000140b680c4d0041d00c0c1803040b24143d0180740c10000040c454020341070010801c45203545001001e45181e400d03031200c0705d460306030104031490f000011006502d51000c4100164903440d40502a000982911140c01400d0f61102148803040b400f502c042039142600c94203455a034410401d80d45100ea40070b080c1c4d014034140041203510b802000c00c81e40088a0308a20400d541e11b460202e1011000d48030140c4104413568140e1005003418401d29070728620540340360015211075030120341d0301e441c004914115050300003403c2c4070f9814011250b60350001c0307903640c510711043c40030f003d68060801405000d102c2c7c00781d8201c0e0800b940c001d107c0c0c00201e80307000c0c001c0c001c044030700c040310501080600d00c40300c28881c441c1ca1881600300d403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 502419379 1250 502418129 502418167
    0x2010503130507050901353417060903071a0604110f0307030606140417010e070b070302070f050a21021017010515121801020f0403020906030c010f030908 68
    0x24228203124418202c0c5c4507090700000010b004011041c1510a01f46012004030f080714080320170f0400034140a50a41e140b40e6541c14109100c80c5050b0341038008101610b904110007010005581121143d846034902d60743c407449000c00042c60034854401503500c082d1000d9120394008002840054103144d0007004420591000c242c40b52486000420462210740505c5600d0242c290385c074144540c100c0e940e01c846403c2c03060303000c0e08001e01741c0d205c042600c40e01f00b508440c01015090702035801c3d00e9501c00d260101d541080c2812400350291840218684400a10210854400a00320b0140310316101100322803003a500d0304500f240841010b42000f40c1c85e02100215204099614039114034082c01140d445040706130401803294412150904400c4443c805484d00d0824240c444240c0e5101ca282c0711484a00b141c074207030850350001c070700c05010549040c050320451b8001e8912500940e141801c25888015549074030b8041044601111010f622030707030212181c2031090340c00914140200d1101260313a11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 502420629 1250 502419379 502419389
    0xf0f0302120a0902030f0d0503130507080d02030c060a020c0a02010819110d1a03031207020709140a0609020909160509031204050f010503040b1f0e0f18030702010503130507050901 79
    0x18543d00340200710704040240080048070000688049001484010020311001d08840d45035400d204200307003400800c0c000343c80145a180200e03402c40c0000d842c065101e80203418a4122406182c00190200400e402101e60403451000508045401c0350700540e50741c103000d8403100c5030324258420241410030600c203841c80d00c0b9401d1b0700b00b503e4480151a442c00c0d01c005600458510580c1034a03034480342c03800010794400702000d0705000403950360844200d01c0c000c2554801400e841c102409030910700700809030107000d55030b04042400703000d44800c0b002040e40314040b2403982121000780058400c18140d110b1603c2e411a516220741b034100c120780040e01c0c00350300c41c28240074103c0002d01000385140400c4c902006030000e00304941185810307110030340007410003030122082035070710340e0400f030070401142c2c004000d005101c800f8a403a0400c11990780304040102c0d410304400319095070419070408004265284070340e0503551340c0c0ca10769855017a0b43d01608011411120341c8140440031416076144d10340f40d8040c00d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 502421879 1250 502420629 502420631
    0xa02040806041a0106050708040b07030e19140f090403030b04021e120f0c12090a020a0e0603070602071a1803010608060a1433090903070b09030405010f0f0302120a 72
    0x103950210501d03c00c0107a001006002040043c076001403690400d8500700c40c1c0b081046a120319103414192440502404020761118220f000070414070213041601007600c0c04c00017480002d00d41c1c101804520010500700720390012541300001d00084c8650003600c1c1d0b5200141c005401d004032880d0301c402d034a03910091010900408107598854044149590740d0002d05104001c0844c105900784410034807810a18400400b403001c00a030507803900700192910254042e151910443c0c2d94030710784900a409841c0c592080c040d0304000501c252002510b03c00b9520000c04000380c85003500c110f542c19600c004207508600031490607201070ba80e02032103480300500e54a00609414a0301d810500103c0710201d15520031045480c040c00380840c09100054a100f10a6043c51825404145c0034803c180303508607141c3c0d0298400e404c0003443e10b4044040c080c0940724824030309007a22100d01b80781e02e03030149000340b0b40040d00d07030090a2b603014480c404580b140d1200c2e040c01450b144407800d02c40140101250803140b11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 502423129 1250 502421879 502421903
    0x321080a0c27030519020f0603100e0f01051c0b06010e121005100906060c12050d1a1c1115040308030705090a06030c09170114011d01050d080a080a0204080604 70
    0x840024010325145c1034803e400c502d00e21006030b0024803944140051580982004000204e95001d40b06102c0060321001c5c15102a40c0740840316075000304400d0040780d02500c000e01140500055a98030000200e0f400183ea080540c1ea07680110ba0592070405201c1d031140c1d546403403a455460602c5910700003d00c002000c04c0600c0d1002c46400b08030381c0e42d80301c1440b1038035060302008515842080c0d201102d078480350801c8101e001000c126035a001c2d03041c90801961070480ca075078411080200a00d40d2580c1070b5100e01000000042010b80b4090304070014160080e83c681e001054a0000706154507546d40b811032074200303910703600c9041075a001140d2800c00b040002444029505c2c003a4a04c1000b41054601404040840c0d01c0060192640c0d01c82c1c85450340814401d29681340082d0403615025801a911b120290381d2846907010312258080465510316100d00045403500704401c0c070031801034011034410302c2e1010700b03507049620000040c14100b1031542480086074003001403080c2c070300440c051340f404408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 502424379 1250 502423129 502423133
    0x9050105060a0806010308030709080f0a03021b0607060504020111030d3804050402151206040f0501050108071d1f020f03030912072a0321080a0c2703 66
    0x21250301400440c46810324090800544100243d902d064945c841d4400780c507030301c4400099074140030300e40001004e4040e030070001241400020304d9905c03840c002d0382102e0001c55030400340201e0f90016503e4540043c81000f103000814425002190071038410314000800c003594a28150958200d400b08814140e1140f050f030150f1000c41c07500c41502c910002d866011141c003440010800701c0c096154502860711000000d003990365441c13204244280c0e0901e5640e4401000c03240c848002e008860051145150020022000c4160300c5110306840040c0c50b002100d40f140402a52400010211044c0e17440400d030341c1c441e441d113400312100082d0312046104200c40c0ca003108083c3c18600078001c1c2c040c1d83c0d88140104800c681c000106101103110010b5010350366204c5041940c011010309014940c4034443c00c0c2c0050000c07000314106000c581c01142050600c43c3c041010306800000261000001004240841e140b00e40907400701c804142d00e400c000300622a03140b440c6030060368075544c200c1809169102081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 502425629 1250 502424379 502424381
    0x31a0103060b09240307030206030a020a0305010b0f041e0906030c0806060d0c171606080712140406020d0b040c0305161103040621050112150203100b09031e01090501 73
    0x1000048072018000d25000c0700d01420079281e04904880e4010f04e0403080410784061146201440e0040c000c01e50f00c3c0740c11007088000e0341c00b0040d51030020389000e00007d5015501000e481522000d00b10b840d00c0d00e80f8020f0035080c90101d04400c2d03803d1124000700003518000c688141b80c0118820409890300c40d00c1d050b84c050800c00002c04142c010038403211210700050001074114103403010445503107030703001c0d0030004107290107505c074000d0358001074404001c50b000390400002c1d8400c1015a407100100c45c071041e0504180c3d25005442008400d000f00400e00003400f030303006860072421030040000c1c11080c29000500f80c8465841c10008640d860017804018803100da03807038180c0603e1b0f00b0f012214034415100a6528490f510030a020408001001c4140c4e00d124040101800a0b400c0288010f5071600c0c006440c21080c410202c44103461011038080f903c2c03c0c3d0003540d104084518818890701e1804041004070380c03103240c40303583c50b01030303e8003041001410441c551030b200c840f040005101502c518001d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 502426879 1250 502425629 502425641
    0x13170a030f05130612090b04140d050a0e0d0807051603021c02060d020f07020910330309031b08040e010f1203050c010605150a033e04031a010306 64
    0x5081110402c2046014850f08502c4800c440a602d8800041034001000d0ba0007400b280070000e0106000da0244400d200c410304c04164204100800d0380c40c80700c0181c10030342e018400c2042c4200800c1c0b090003141c4207450a81880804140074a0704545000d15981d43c850a0200005e6501d541e02031458042c000d50600c0ca03181c8100c031940d440d4400e00c50500e0780004d200c078010807581901d41074000452640c8175046034160350303140d6409001c106c0c00307013404100785003503480e01d00410024a42220354400b04402041194044000e210010000c054800f603003140a00004038058060048030441b200c482800301c00d904403900d0051402c0c580b61800c0c02c104850004060707000300000083c020060246114050104426583c1810081c0d0f480307040d00011805490f040e0302403503101c140580c5038602800480e000f0517400106641c2004000144404006141c2d9040c20290141c079504821144248003030114640c0741c1c203a01191800d05a5a0f947c0308459811001d2207014884440010810002d4a010360 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 502428129 1250 502426879 502426907
    0x2d010c060e150a0c05090f0f0a03081207050a1d0411160302100504030503010b03091002040611060a1a1009050303340206160201110a0303051e01031713170a03 70
    0x40c13290304a00c100082150049a090300d100b541000b0282c04982e9500002907003201c3c01804203180a5031341d0401c0c074000d4001d10740d85001c8000b014001038280d07201d031007220610002500d402011842484420103c4481d00e0411070300715984410300c0d1840510300f000360000c9070300848440341e1102c0350320780203050503040c0790001030b50b6003000305200c00682c00000352419641002a9a81c0720b50780c600c0795526041a10b1007401d021032002501140e055172107400005070361144803c541c140e8440303001c0c1c0d03c1142ea001a885449200003410300c030700e03468410398000080010b460955185034690000a06560041c00f5207a4a048041c416128110051002d614500c01c00b10204a40440329000303e5000d00c07035102c07450503410101c1406070841e0700888941c804450a0307012248541c049240c06801480142c0d000104405000850350460b03004c0c0c48101e0607264031203112000985044041810b9410407007240111050b044030112f00024100101c08501d1520302c0102000142c50401804685050111b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 502429379 1250 502428129 502428131
    0x1032909031b0a080412020f120a0b060402040801050f06090c0307020706030c030204080d121a010c0602030603011d0106030c140105120702011d010b0307052d010c060e150a 76
    0x30840c1100c0c000c03041d640200c00e010218807448078451031890518180b01c0008191030f03408240032551048180c10300581c40d10039520381201e07000b42400c03c61001050500c10109600002c4e18600060b60318102035080b0b030011b84050b050540302c10103a402e6440403a540300c001c003c1482001042e107498640d050700b155a1503002491030520540080d03c41d07407180101010f140e2245e804105403846076044400406a40302a2844c0030214100100f08003906070320419801c0c00c1c4812002e031003480000349801c1c4801619560480302e0395076030710341c080d400040c14681d0656a9072501804c1c0c1c0c05040f0045072002c902c030000290f0034110324000a24601c240c00580081540b00b200c6c103d01d90300103080714516030314100c80034465926084101d000d008150300600c01c12065000c120600c41054110800c0340c0404c0f002d4845194403403062107600c4200c00360000b0507900b0341c0c00758032803c0c584c0c00d1566041c0b601850b21961102c3c0945501e400c0c0c80b05906803059580c8203000044078181612281070b005144900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 502430629 1250 502429379 502429381
    0x339111905011128051308010504110307050310180c12060f060303050724020d0c0806090402092d16031a130f0609110a02100501080303070503070215010329 69
    0x4c04030f0700c1d032142c070119025032000e01501002ca035000fa02511445100c0b07241e020001500d4602c01d501919058804981d0304c0040100b66107180380104d40c0100b5207201500411001c030b055a038007006010700302456004504020000350100b11054918005000011850740c4407249514203201110840c5149201b078920b8600d06000007a40a41112101707a00810740080b0102c59401c2500381e404400420a403040c80014030900540964000111012080d2551802907070349000f030250b040300403240250300041d07242c002884011950b91101e80840500001c50183d0b9111418100621058408000040c0f030b20341c088103103603414000c03059070010520005140303000c0e69012805441b44038000260070b5031580381c003510380e141c00c4e80507500500c0030100c140002d0048201c401d40310343c00b9011030300041c01749110304201e05581c0d004c3c2d14125101500154519581e4036011601d40c1c2000e00032004500803102d00e84140d800108000b0301031030083c5029030195a2a00c070180c00701003c4540c103101040444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 502431879 1250 502430629 502430647
    0x41a01180f050609010e041401080d03020c03221d060a050301140402010f020111040b04080705030a08040605090d02041e06090c1205040206040b0409060603391119050111 75
    0x1041d4a4221201602d16644031428240141e03100d00c2c13201d041540052802d0080142e079800f0b0340c5940e0403144108217503605203016140c11403da204500c40e10340c403640100142c4211070007404078160703041780d10700007a14015103c0d01c5109107080300c1060b890300005070400f0311020303140c13610b0b04200034030080340200301d80e60b0003642a165074007000304080d06000d00480c05d0100c0c10700070b410107201c594050084c00c1e034990701c680941485820502a14a2502c540c1d2000315007414009a19800e464000a140b81420310341142168154003018106800c1a400c80359000140c031503000d20b081550564098004840b0760813541e50407510360740d02c2034107040d060003008200c10350080324850b140030305030340d001c030b01a5218000b2528920990f071082400d0440001c000480d03c00c29841041a52880e0750240911a407903440d01c2c0d180495030030007c8401c2c54140d00303000c041211003400c18003501c140c1003041c60b40a030b03030708043d05181d003501441040422800a40c800c101c020b02c100103510395030400070360034940c1007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 502433129 1250 502431879 502431899
    0x315041e0e01060503010204120b1b0403080a03110a0f0e031b0d020a0302221a180709051201020a082d0703020d1d0f060c091509041a0118 61
    0x140503032004940e07454920260380301c0c082d0402e00107420083d0007590b45031759a40c021224800103040940d110580e86001c1902901180385002c1c030302c1039043c4200d04040c1540c49080c81c1c1d9105c1200304080c583d075400600389a480384000391290003000d44030381000005055000e400b04000ca241d692080e00400d015602c014903803120352011000a6a41e00b6186034144041013034040c05030806540071020b05860b4039540707031443c1000b04c5550000414070180c0d150307180c02000043c2120700d140d88401640e0f019448505800d0009520003030b00d203061040351707a070317400402c500036400c21302d403140f994000a5190500c0d4201441135007241d8540b42115a407581c0800c80170040409588840901540c0380c0400c0c2e0b42e038440e40540340c40c8401d401c02040007400034001904852812101c4d201300740074143c014150742102150381c5220701640c440182c6000c003000e08000c00740d4142d07041e00c0100c400900030356400e604c0d584114950b4441070100c000da4116054000350030384240c0b40100071a401403070341c103001407141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 502434379 1250 502433129 502433171
    0x20a060e011722050c030307110a090207020612131403030a0e030301030c0504020c161e0e0603060a0506060408030c0615031f0c0e10200a030c020f03010905030a05031504 75
    0x450f0484500b042c5503480c00d107040000c0072403240c1c1e1510000c50864148503c08100a88003503013240e2550100741d0326485c4500341d000e40003019602c0102404400060003502c80850750103522044c88890424690750741c1060381c8003000310b0b107407203034000f004000b02800d551044000b08410300b0b00a50031503143d07541d070f4101031801c0e001e42d900464002c2003013128404100078800030038408a44a082d06601c070007801401e14405101c2040c12020341c00c00052005417956458014440038018160a990310700c1070354003414000d00100d4105004000024009030144050006800550090606424203240424404d041c01d15a140320380c1044120004140c40042d0340b140301843c81703102103000365141030103880c0d0343ca17002031080d0411220b0845218440e80304d03e007816440c000d00401001d18007100440c03607883d0441030004021850f80b60610015281c00041083e80910040000c00c8900301595240c1c10b6030412207030302010403004024040000c031072501c1c20010324801e803020401e09090745022407007229 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 502435629 1250 502434379 502434421
    0x4060f0e0c0f0c07090b090c0307200304120302010b150c060f1b041d010605090d020108130c030b2a0a03050601181404150e0403080a09020a060e0117 66
    0x100004041d510011808280c40c2c0c4001c090040d84d40080c1c0c0d40046902600d142260684500254000100c00c0c040f0b0740300b5280201032035580c4407000d15000c054807041c2c0618011802a9100500000800c03819a507a5500d040e071103039001050f408004c1c0240407104000070707144210301c0030074426003207020000540d01c0d511407104c0c0000c010320b444a602501c1000e219a84446c0c0b107050014010500b006a101c2c2e0900020358002c3c0002d06070398481040750076004945403680e00c079440030358400140d8814260300340c2180143c800c4160040450395840e41c410701d01d40c411188035000a04100e1305180d181c504568192403e9980d501c141e400e1007840119125241d440c0050542d41c20102e803059120f8101403840a82206a50300d109465034425007040a040480074469401c1c0582404007070b640d031447c0300881e04d00b507031000310b1500d071035030700395100900140362041c0305a483c1c55080c00350352500c44110051440f520344c0401e00c0030383c0d0001000c081e00300c610601c00041d14014041c00709910201070705414 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 502436879 1250 502435629 502435651
    0x803030106170f01050d200303070c03031b150f2702011202030c0a0c110d0b15010c020f1c05030304080301090e010c090b0a1107080717060714090d02030a0b040204060f0e 75
    0x500c409a02e4950300b003038418070b641609c40810444100048001d15505807130280d1200000c1c04c044502407022a061030307000600144005040403180e000582100549014204000c5244d5010304a02031909082c1100301c4161480400c0c01d00a40d6000102481040d484074810f51840c50301008960552003002901c60030801150b000c0d0043c0b1826404140703840c000103001e0078032610181020340f02800140c60302c199000602d42d90f080f10b903003e125003019059026101c802c81552000811600885080c2d41812a0541042c1000003c0b014401184500c0c41414650b46a504100703c480481e008510001b069a15000c40c0d0301c0d41e107401c640e09204440316124240c1d61218200000c84480c412150a04e42521030300501043c1c0203008205041540c0301d00b081c0075034805003029080d54414050380c6240200e2100000c0d030020300b10200c010002c1450141c180e03034400c0480d0340032a00c0d0814010007990303071110384411f02046241c1070294500a0007028045070703100d814007148450817240030b40240191 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 502438129 1250 502436879 502436903
    0x9040c1418010302160b0a0e03090a031b0312030e0c04060e1303180f050f03120d09031803050606010810060f11211903110a030b0301060803030106170f01050d 70
    0x7a81c07107501242e54a8450a05141c00c508070b603e4411038201041d0b64070300380340e42040c0416028190004c00e40350341e180c008103a0125a071860315444914541c295041c111251100004808070303480aa510710400d00030340d07000440131310f0507000c1801c001085000a114605142081040351a88081c454128101e9502d406034120103150035a0b01010204007468003003400a0005070070070b04010b05500300c0358240c0d0f4000c503129134401099200c034a5651341c814400010b01007007004000c540c2c85100e085100307080c50059a18844400c078000d010962080f6070640c40701d41000010751f8002c085a40001c02009001d0150b800d06038003030700c07540d03540c1307a5202005240e110a11031507030104241c51400c0010303045c4120b510416241e50360554402481c46041c51402e880c04200c0b24841d20a40402d85101860581854150403048010b813582c0300704240d16640310140420080d10910081d402408541c90f035101c2e26a0103c400700000000400b0010800d0324100108480d803a40ea102e0904507910179102d24003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 502439379 1250 502438129 502438177
    0x61407151a0909070504050109020a0c030f090b040902030a0c0c03050324040527030703140705031903020c070b0f04410a080606030d03110d05040809040c14 69
    0x2032190044102503002c88610240044424046500800e4407020f0340e09000b5681c90704001000d922484010ba00054500c2c44944040380c410921140b0f0381949240c030843c4150348020f05030b09500943c02c40b0340d00030b5000080c04201c000a1240004800d01c5050001210005480c054a14000100944850542071100000102d40650f00101d1428014800c020b2414000240d0b1825512480c0310956030344041115040170500000340d900d610351603a43c034201078000c0c180040306a0031500003281e040c4801d000b00c2001342e1500f219050302c2d526690b00182ca41c1109401d076894a00c03130780d00603e8100c02c2080a015001d1183d81124242c038981082100701c031960484203504043c0542c03001d0340810309050f5910545c1e81d109680c1d40b170020211050844192142465919240195002503042d44071449001c0c02ea4066001a005960404445410a01e2001601044e0360302202d0866210000140b1002039103010b03c00e515602c070040c42c01c04468a0741a8540c031051103100309901010300e0100306806 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 502440629 1250 502439379 502439411
    0x10020a03110d0903031d03040311040e06040b0f060103060b030609090307051b01090f0e1302010e1008010e07050306090103080c0307120e0906030309011b2a06140715 73
    0x14034080240900381e561111481c00d24003c240e04541200001e0610041c6030b0801e1458250090242e40d403000396180c0307480c564401c4072004030500201e4000c0d0715802c0500380f1000174081c8501c1240150280c03202860590008400200d009106505041c98540c00b440700280764010ba80c1d001c0d0003501e0600d680d845104901e0710754040d0100003040742c4102031034003505800c188080c6210a500f070702c485200a03242c43e02e1060701211030203403d10f42000c010000310280f994041307502c0c1e041e006040c4038401200354004100561008640440424a543c004202c91030b802803070b0f6540900c10303240190840c100301c0005440c890040c80041d012140c04190f80c0c0b05010b0038000c582080354000e04655140c1c001d11005408005141102071064240100003040c1e820f02104407020b4100594940003503030083c0c10300c40c490b40512207007074903600ca10200070950664110b62407a01480309451081c1c480303240010051043d00c10420083c01c40d10140114000101e0f800d40c4008018109032001c104040d540715846 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 502441879 1250 502440629 502440641
    0xd0b010933030f0804080a031d010c08030601030f06030c060201060617070807050a021005070c060e01060806012105070618060e01020c040c020c0316180506060708091c0b15100210020a03 82
    0x80d540740907c0500703408054201c010088a104514400c01d01400c40c1d0005503018040300201a00c130b280c0c10000942258429800400d07038001c03400000541c192131381c5a606260030341780c2000001d82c1d034039034040c00b02e44d802c000aca0320a000320015240d403c0c606a50010810301001e4041402c2c000c01044402e140d900a00500c2c0d010140e03108104002e150203100100b106064540686030a842c00c9811402c09106010328400d1f41d00c8900140100d034030b41011004005050711108200241904000c80080e00c00c1c80410f0091656030784003d9501c03011031030002607803d594488010b000301ea2044200300d0342c010a0304040c5a40468000500100c02d11050341040b00c644040c0c0d07418013480359034010190b40d60035140c05869900c0da400b48440c0c8106c108408407901960210b50012083c4542d03400180d00741c00503c90418041c00f0f11001585006883d0362b01c403544402191000443c40401200142c2680d80c096100e60440e10070b5218148508043c2d01c0d030404014415502e9000102035103154000e800c10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 502443129 1250 502441879 502441889
    0xb0f030706050715050a14010b2106010c0b0c070b060307030b060d030903060e0a06060906140402090613060306151d01080a110d0f0609290d0b010933030f0804 70
    0x2e20070fa191070044c060080c0130900f00b141c011f0701d5070000400d100645a0a65650500e4080d51007007094001c08584400e4000034060b40c10000600344010006402c2450303240142e03c10034810380c03204020700c0c002400c500000c01043c06540200c0040010403001c0c5400c45c0c0101c2c082c3c800c160825507504040b45d12180070b42015000310300b4802003002c0040300203030884000c1c2c0290030030081680c80380442801d44000d4420824480700c4d814a41c1d103585807980c001c240c544002409545070081c0300400b40d0303103009164840d0003c00d90394942004098030b800e04030314001380b00d4645003d105009640080003000801502410040e856002624240c1598004001059001f1803142c03608003d80c440005440e406802005550904c3c80002d40c52041e40109000c540031410303403003849201d001045c0c41d601001413130607078011000344950740443c1405001038007a00d501038001c650300d9100700c40380ca0f031040170805400007921404d651030046a0200b81c5074055943c09a1118a0303c0450f0a00f55114003503900300e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 502444379 1250 502443129 502443131
    0x4140a09260d0b0103060609030809040e06090703050d0203040b0d0e0703081c0f150303050c070f090b01030e06010506160c081903021c09060e0103020c0715030b0f030706050715 78
    0x1d100c0501e81410240614140350303a42032012441500044041c1c3d00148688030104d20981800d000150000c0c0c060106400082c000090b80b01c05000302c24075081080c0c550010540003c0c5060091180134401c0041107226070001310702d070616050702c03502180700c0d00e00801585541c072a00c908800d581880002e0085403c49100c80d240d04120781c1c10f8034200ba403e680c00651504c5c00c80c0d04545c000f540e010301d103c400001200341c2442417454400380d03102c0d846040da0500500500304081000784c11b07822000051b00d4003039000180194804005400c5a101c0703100c40b100382d4003102c010801036070340070704440c42410041c5200305084114a4440003086031034120380013502607003030025448a1206100c0804a000f54202c8806080100b058010a02c0800c020f800207107000ba800e21409000e00c20100c0d1145040c50b00610f480c900c494054180b9025402c4003560b0541e00b41400348056040c0140b40c0c1490f8200d550003000a0000c001075500c070024450403081c00008154001444000b0038103041a44417814 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 502445629 1250 502444379 502444433
    0x20d0c030b183f180a0b03040201030506010203120403090e180c010f02030c07290304050a080313080a030e0c011809092a150f020312041509050609070504140a09 71
    0x6084403c98111040300060302c40e100c540580c4c2890107151030011200041074051650310380740c004401030b0000404941c150f01c010004409001000030300c1d40c3c89540259510008181050312003c3c681c0c1015000c44c2c0076440680b902c2011400110b0802e20503070007402e28070800d00100300300f0b900314002d200c248d200c00c4c0210030300050030018000541c0f01d42c00c00c011131030540080c5050100154002540e0241c40741c0d01261100c80003440e014000c0d0340004141e0340c507544071326090b601c580440d0b02000d6954006a00c1c2da407020011901013050341569602402c103242c2003100f10080d0007d80500340718000110b070b110882141031081c0c00c50710416101200907060541c004c08206910041c81900c500f102009003c180e00c41014403ca40c1040008901e6000e1340c41c1100414102c59040000741040da840f07d52880e5031081c401503886000342140c0305002810680c5000300005040102d42c4d4001070289080006860030800c400e0001640000312420000780c000040c244030000340f85811440c07a24040d940c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 502446879 1250 502445629 502445743
    0x12051206090718090209120307030f0305060f0a240905011209060b0607081809010302090a02130506180301060b07030507031413090504060f060305120f07020d0c030b18 74
    0x43c001b4600500d06481040682c2900051941e0324410b012000d40020444010038107514804d411540c0c102c40c00400c10012030000e04005144002943d001c2c00358000a044200780600580c0403c0c81050300c03034100050000d1030400007038900d15441c202503107225600c44011042200075030003c203110002a110a44403d038515183d50319511100c20491604079820f8030700c0d00741c03600403d006e060703aa01501250203921541108000b941050154040310030600740045002d403a01000352100e24100041504030440d054185421207510340c00024500c181000030304046034201046402e07483d85032800100140310041a0b00c1d56001c0d940045800e104c1c0e0450010b01c01d01a0b0300601e008034041c1a0070088030405404c1102121041c0c80000e04640041c6850021801640094060740420f0b40c0640c0c07a04c5c85a41c00203050600840c0c0071a1207a10100f0284144403100c00c1043e440b0b0340c041442d1100c082c01814203a0355003030910b080d82c034a070351220300b40090404440d40d808154401c1c84910804601d41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 502448129 1250 502446879 502446881
    0xc0306010f1701061808011a060c1f05010f06020304081921121103190c0c06091a0c03190b150a230f0301030b060103140109091205120609071809 64
    0x2e202c08a1701000d0300d80000c80c0500041c80703421080203070300c8030075000c0c1e0081409014441d000401034017041d004590686211110b100b1501070b105041003c00991981060b244c0c94924410fa000802190300c14007092000010000c1c600500c3d401d00c0424040c0d2840c240b40c03a00400244000c58240400700148040c0d1a0782c2214500c0501b8400000038030090030417801800c080e0000310755941890480b2012000032000d643d00400c402800d40c5020100780050307480e00020748035062801c41d890490708980f01c84001c4195095500b1144c0224030324554280050303401c02c611070082d24144555500c00001410b41da48000300300700400002e401540350800c806001d06032504851740055464440e9504142c0e21240c10116915049201c0581341142d085448a9110078401003101d41810394888500890030141041203000740340c40d140c0840e080342241b8190511400040c0e5250034042c007880011400c0c0345c1c05c41c0c1154006815102d4504640e144401198483d844210020f0901d41c0c40d200844c1305401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 502449379 1250 502448129 502448147
    0x90d0c0f14040501050d050d1809020c030c070f030c0e1e0a0e0c120a11030a0f140114130311103b03120a0b040c0504050f04050c0306010f170106 64
    0x1c01c4500304803036a40d4800b400000c4508000c010030503000b1a0309086124050707144514059140c4250f030b00d51513226402c900c121307480002c070040180d00200380d08800c0d0b4010020b0f40003030400804090304651441d580c91680c0701980c022485032269400c0002c00c040c030b22001d030b03103e07100480c60f4000341030810340d4898005180104240c01c0364000c070700300b0440d28188000500880700b444002001681340e141c4600c480c1c52120f01d2a40e03814080c040020000c07440340100525014002c0c5811540440c10300d030194215001e46110404030200c90003004500054039004500140c0c240c10401c80d03002401c00c51030704007100c00f01d9001009150106002c0228984982d04011041c4808590080311500c02140701c0c0c1c5841cbc0c43d2410060340100304000c44442060350a0f034106208000214921800100060a4070b5102c01070784001440490200a40c1c5040800410540e5003541d04110609007401940078a210060100781800030408042c40782c0b41c13241c5010074016a20100203c0360b0358440c000144543d02d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 502450629 1250 502449379 502449419
    0x10632090a1a15030a0c021501030c0608010e01080c01111504140c010e0f210616030f020a0f05030c0f12010e0907080d080c0417010522030203090d0c0f 67
    0x20340e0203100c914070b08043c4444480c0b014450821401c680c0c40464440281420303103110000c50240c40c0000150388504207506001e14850025000302c01e09040000b0101101680004601619440108a50030b40404c03192017410b001c0c130b0404818054180424a0109003086441d0a6094a0f04004c10f0021807014003000003001c8050741d204c01c0007440110b0b00b0f000982011544102401c0d40c291291421b1994a000508040d00f0501030310680c4040c141445000c83e41365054158903a103101c80c80b54103100d40e261000504004504080b6075800080030403100543c01020b1100001c041404518040c080d14420881028416610079200350650f207a11020300c1003103a104025800f0913005040814110181e4042000420006403110310840b20500040d1080030005000c21000c00d0b03600e6001614030b030f00b000c110000718a40c10034040c1c0342c0e8034000c07221845280c00ca00c904800700295001c801c6800c20103007103622040581140c101248010785c194072000400e074943e44005403000110035000b040c1030f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 502451879 1250 502450629 502450661
    0x20708010b010e0f04052a040812040305030d0b011107030f06060f08060c0f091809060601082211090412031808090603040302010603020909030714010632090a 70
    0x41c84000040d200b83c042c52021079800319042d4000c01840c10203501140d400348a50031013446088050014035115550149480d0011100040910004c1c20800c0f8403042c051002c0d0059103050301c0c40d20703643c1d1280150700e240001035840e81c2d810320440c2e00c01c1a110300409600b03010744003515681d181003400c0d0042001e0403540d5500300b600010305c0c19203011a260807250140003a0a069541907034245850340320310038040415605201480650302c1c1d000310911041d041c4111b40a66003400340b40c0e103140040c02080b40d8104185942045482c000111292400381c0d01808a07111101691900e16054251115020b8108d8041ca0402c8103015550f521a01c845d5669202041814017014450b40c81c10300308030000d05486000c1007141e50764240324004540c014024400015019103d5001412072801a102820036078008901e41052020000c0111021031546008111079403502c410750321070341c90140810300d125981480102000766404840081c5400003440b2403502d1824121550003091003140186800c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 502453129 1250 502451879 502451891
    0xc0f110f30010501050a1e1e242a0b0a06060f020a0f0312090203101e05130206090a0b03090d03140403140d060f0e04020103390504080a0302070801 65
    0x401c5041c8036040c142e582c09010f07010804e0815612100203a169a066002ea140c2160002115200580c0c03100e981100304400d03041c40c91515105850f410001d0003041325011084900b40940b9412200d14003000080c00d1704004007440f845100c0c1811900303c0005130002c03407514100302c2801d90f16070100301030362880d4a845004035403110b01240d8821130003078000d003038041e0082c050300800d01a00c0d800b11201702031000410320003a6540880e0405c55100c49000f480380c4c480600944074000030b5281103400d10081c008004515180c155044400400c00020380101d40000d590440b58031007082c003001602c4441040ea40e28181005d08039916032103118241c0c0001c0c9000c01000e0144003210046024039016a510441070201d8100040c4680c000c0d85500c03810b69959400141d500580d0001c4802000080c80192003840d0900024085c0e43c102c05609000613820b0601000c0102d81d8610908060030905180d50103181000003a2902d2080c2e81100c40e9520500d800712081550025401c000c0d01e0b00300d0020300070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 502454379 1250 502453129 502453219
    0x11b1e1e0219080a030302030c04080a050709060501031104030b13080304030e01090e0103050319051b0601050906090420030102070212060414010b0112090f06020f0d0b010c0f110f 79
    0x140d94071900802246404c8a5400000b0a110b40c018541201010002511302940d52401c00d1921342c00400c01ca4068000c0c14040111201074450680281402c2c02d0078000100c10301c0081d1580c3c420741c0030041440001d01c0204d002c03252948503031b01106610954142c1d40c0d040500300039101c1c0e214508140d000803c0242c010400d200494800d904880e440001141040442a130300781005084030f880c101004014440d038041041244d919040c0703058181c01a0189504100074400800002030000c0c0c0900095414400003541941c2504648102448030780d80028103540080d01a200d8503c000c0e500c1028104016215400861442d005a1280b0034202440a0390261642a28555006103010401b40c41c055040001035030000c000c698400d151503680c064140d5102d004a81029a2030707076120300301061183c13100d0203511801c0c00c15242401d00015074122540c9400340780c64821030042501000da00807010b41d440720115005400b000a25801601e4144100b144158001d0460212820074030000015 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 502455629 1250 502454379 502454419
    0x60b210c0f030a230114010e030d0203030106050f040503150603060a090209070e01091d10060203070b1810061e05040b060409050c0c0d02010902010e011b1e1e02 71
    0xc1a0700440c0e1440c0c150ba8802c03245100501c01d9941102088a4801405a0100c548200c0901030309130040b4640207006214001025102c1200d0315a005e9444059070303101c8140c0000a40713045914500e4443d5a40920b1a03000b9000e008950285030180315040c400501e0fa0300369920320348101b8050b01102d10607601c0d00b000034182c40d600715010390004d5014021031009441401740350001c09060401ca422785983c0e03910300d182412018603a0204c20310100c2032000120304145908000d1030703984001d50800d90315895410a1232000b80254010240103e0045c4d800e07002030015803c8036405240030091282e5900e41110060b0388488685200705542c140800d15142a2080500504014201c1340c145801d003019503004200c05890010419400d014101030390000700b0181c80300c88156030001c28103424a00c005052110b64100d814107100c041d103000703050101c80e80e2184250300d41100449440c038440c001c0b8010303041d00d10407010744007600b5406841807002d13074110245070141c03003580c1d125541145a02104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 502456879 1250 502455629 502455637
    0xf060f080613121e0f12150306111213140d02120d0902090a1509020f04211e020117010b0915210103020306010e130f06060b04030b190e07061101060b210c 68
    0x1f9010b884083c4041139081c0d0044440762444807507a450074400c20b100441b41c0d0350444d08589160402c002e00b00400034004900c003060745603600100300342890700201079191400c3e102c1f4242d40402c00716160408604980250b0b04146d00a0040031381e41c20200740d02000b411181108070749040c016080000c0c08051403084446a543d0301d01914101800d2542d020b01a0944031380030199071503201901d4011586811f540c0e86801c19551061040381d65610025080b00315001c6079140709900c69004110680030501202c5001508892254090701c103828103e40e0b50084014264a142a400003c1007803844a45514140ca000300d040342c1030b6030382e00c40c0d8041c0c824008079102000c025440050100143e039a6403030301541d41c410003012032916200c2c0810030031504540e00c19500100520300b84403241501d0700d001d80c200b01249000340076500c2801b054681d030300068031030803040103600c0c2e004c1d480d160003e6200f2006000840081aa14550510500318080140c400f0405d0850349002280400b00140100c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 502458129 1250 502456879 502456901
    0x50c06091c0e120706050a0806030601062007030b01090905010b06090303071403040306050a0506120106030305160c0f0f060f090303080f0603010b040f060f080613121e0f12 76
    0x12100340c46000c2011500502c01c01d418a40190320314500f1a42c2100c1800b4003809400203030348564956003808001042c4400140c0340c0313402504a9001881103a50043c0050341c83d800d94800a103000e8100e01c0d00d1841c0ca8160f81c030141003002040b0021450703040c82d800040405015000074440c04410034200a00351080e9800c05a01da4402c100080004161410305d4032681c9580007900c3c10b00d50760b6162a0143e035403c488050b0180d98a000f0440c1c2c0c0e2800400c0c1024960380d200c0204a2581142d401904500c03034620040521401010f40d034080000345c09655028127185d0403144085580c0d00110f00600c00d0a02403d40400c1ea0801101c0351540b09081c0703a01280d40541d40c02d00c3d0f40d10382001e190704081000d40459095500c841c5428401d4503a40540d61400c0e58203140000e42c00d1400e2207100341c0f883c884d0021010b50300030000348520040c02c0741c3d07030284507500b00d04c8044d450f03c000a02901c201404900000710b0401030100c0f83c8000d504440366148101c09138407099880003000302c038101160745d19014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 502459379 1250 502458129 502458163
    0x522030e0112050906161205010312090902071502130302041107030908030309030f070606081f0b0d05061801060503070308120a090f060e0c04020c03040312050901090e0c1207050c0609 81
    0x6d06402001c0c3c04040400302034200f512840004988400036640300b60000d8841e00d44003071842034143d9008407070f08010050032408505001259a0304011560341c1f4610015290b0080362003403040100911050041d58014001c000000c402207903d28903400c50130081d030100d10014000140c0d9000030003100e00c03409290000c1c601e04860400d49054030f401610080d2000e41e594800450602001c02c00d0216012042245484c1c45500e54100c4007915814100940100aa040803200045000980c0c98002c440d500360521003080845260f0300500180e808181d01d40305480b00003003440280c40c01005c8400075007910403ea50344000b200401d440355144020708c0291540b4956020a031660702115801940e00140d0320580c80000001d070998000901c11a800d1b00001820810003002116841d48224503040a0341010f0b803a50000c0e08401c144c0c411402c1540080d80082c9440102008440701d50384e41e211001c40b141050340e40204240c00004101e80b2900c42c15021032422a000a09001110590b2107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 502460629 1250 502459379 502459381
    0xf061309290f040b1309052803170a09150b2b0b04050a02100f0f0306050105040302060c122208070b0301290a03021209060907060e0a080a03080609010605070203060a0522030e0112050906 82
    0x480c2c2b50150400070901e600071a56090300350000f80c031032003030048070001c0254081402410201004070644c52648a4014082400f50b0900c5050020103081c05407030700034014241c41e607201d0030068103120745401700a47c0001220591403229801030341c40994500e050703540c4410811445002d604480c0c0341e00170076010030410b00003040149411001010310b03c96aa003555480c2006189010795030300001c1140803c1e80c8403029480101c002c201c0390070000d0068400502c5c84e030f4503012001c0b849200c1070103080b44610401d0242e1201e0010410b62200325144400e4045d601d40c00c4200c018000e41100c2003600284141a02144a41200217050b41c06400082c018002162415406907030f50380003d0a50340c0c0081c6d0b0300380e0000750340724103105c402e8005019844030f84035468028104511210143c116405009040c01018007589000903d02e510034003404001039151030b400304014421301808207190000c514401031604065021410b8081c804080e00e035221140c840c0b140700c109545049801013400ea2180e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 502461879 1250 502460629 502460657
    0x3020d02040e04031112071e020904050601151d0d05071a120106030c171b190905010203030405030f090d0206031306050c09010c020f061309290f040b1309052803 71
    0x150800809080308d07084c0400d0b01d499074040396010104a0303081d1915004980104100300480300c0c0d0b04042c038038900d0405010700d040d8111030700030090f41d040c1c00d014400d00d8604404002d41000500007900005d00c8040d07400603d0501e90360170b9405540d46035068a4040300014459003c0d0040389001891503d910240c900400380400341003500a212541803890078650b000326903c800000e05160031180002510190741c0fa00280c0b41c0200c0d50f000d01d04540c070400812001c200d010041d11070000c4000c84030b640e641c50190001d80c06140c0c14401961000c000414001000c502c070140034041ca00c900c00921203641c0381c0ca11141d45002e20041c1602003441481d070b090051608046a503442c0324018202407c0c0554111030030302d01103550b0800c0d8071440d40c070007803104003c1d0b080b580c255004010507030107401d1031036000109034a85c1004032070398001d9032603121060280d510001505051406840200b0165007107041c11503681100a11101c62941d4414951760002c900c11259120742e60540c0f03400c0c2c5034548030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 502463129 1250 502461879 502461893
    0xb06030c07150605040f02090301060f0815070329190b040e0c120711070b040b0f0309010e0102220e0f130609021f0f02010903020c0f0103020d02040e0403111207 71
    0x60311584500b181d0310a004141650303148269200b04402540050f201e410b48003e250845016070003203500384d050100c0810210300d00083c14100040c0441899405480b560026006000c0c0710203420003491003440d0359510000301c1500400f4080d01120810540300003061424403681e418010110a801e0800c814041c40035804a41f6802c0002c1031000780c40c195020703c09100780d040680c0ca190020300c06484200c0c0d440f13010001c00c005444595210382c03400740360180551240c4a805c5d40c2c100204c00c0400003d010b031200b03611100c44141008029940c48441805030b03451004006000e1030a501074036000b050020402249038860301900f15840110b46a191802d1031402a540003207070060344a04100006844400002040c40c87c0c0300f00b28075003940d140764047d100d919180d10309811a13140c2a416004030754001084514081c068641d005421401d0700100c0281c402c0000840c101800018002441c1681c064014441e600a035116600e0a0b400100386480f441800c5036101200c0f014465040483d8078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 502464379 1250 502463129 502463153
    0x10302091c060501081b0d020d260d180507212f0306040b15030c06030c090901080304030b070f09080d090806090c0a1404021201080106090b06030c07 66
    0x4241c2410040041161149421907541c120391140d00d600040042d04800c04c01e40300040d4250700311061084450010800308007518801030304c58010030011000340151079051030540641450324150040b9030f880d425409a000e0030414082c1e40c40e0001e50030310620720b40000300c401a0701001402403c0e10700421814145201c0d00d00b042460700007440c0707000040c10310b008141010700c6908030110f0302c0314041d41030b000714400342822802900a401048002040090b00688c0300c0c0180a810002c41d14010200349041140d03070a0b6030b081031000041c482528609070181c03030704200440e86041ca5a8890a03026100e003d5448010150b0255070081000300340108140e68585080d46003203011143d480324014030701004034880ca0046503180304e050000550034014142d2001d8060000d09074141080b001c5203070441ba44c402d0000c070301002203125140e43d6803501240c505a440d1007440e2035550f1210700c204e0003409180300f140c124914061403507102d820314005803441907421a02c418141106a10b0300408894 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 502465629 1250 502464379 502464397
    0xf09180102250605060a05060304020904030228050c0109030b0714090604140411041802160206070c1518180b0a12030908030f0f0a032307030c09060905010302 70
    0x5002c0c0001440754581482c840c1c5403400c0c0c0030386212520300c01c1c105a0102c0d1409001c1300d0103081d0400d014481c646a1000f1203030401d038195400c03c02039540b4201207080ca050f191400c07080c2c0d1104c86241e1060b90803561a5031380341d4011000d6501c0244080c0054850b000c41d0b22005011518440014454a0180d01005451407500f62072901c0d00100000007a0395500c01d070002c8034580421902d460080c00c1904c1030880c000800c0000519060500340003413a40922080083c00d11a00021042030462001421110f035542c05080e10b5120300e6680303420681503101d4001c80d40c9201c00c109008198a2003017a05400c603006103c40d0840e4141041d1040030302100c15084851100e858500548454807a0a00d68006000e00b400da44090125890002d10042142c2c1c1f2460705540144000070030318110350116403541048689059803107250b05000d5000e0702e240c1054120000030451090307841c2101d441254401e0a86560400c80800808001c2d0343c00362184c003510b8001900c0701d0080c4a00e5010350300a00200c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 502466879 1250 502465629 502465631
    0x30a080d0e0604060225051e011509140a0b0117071704050c0111070e0a091a07020d030f090302060f0c0d2c0f12070602070203030d14060f091801 64
    0x7001d40c4a400740703001000e640c1100c10650001d6405402d014182d8403003045a20360f5440c2d188000c00e0f0300c42175a5820400e0750380e02c200c0c0d024070304800c0446e001d40c403140515034100400099250703904c0c200c100400b0380c5440c0981101e06a40014907294a0f44108008908140c4400001c2070b03450035512801c4000400180500140d02c54030f101d201c1400302014456032046004103e108980000144404503c0c0c8007080039501c00282401031003c04a40c1503030000d0b09860000700040303a4140300949613100d480c540c403e05c0e040b4042c07198107980865074050010840d1000d00650681d5040354040361600900540181c02c55004101c003078a00100b0310703401018a4072030364140781ea5500740a085490388141503035a404101e6500412030f0600324400b00c09060340020b4880303168543d40c5607881c0c10590107070f08030180c000103007003041103500d80c15200c0c20768020f0116503d49021505610007030030701c0c01c0054244000e81c0b0018005152550381055910030150004803d070b12040325000d4120304501d0504055 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 502468129 1250 502466879 502466891
    0x914121303241a0109050303120f0a021605070905011211040b0103020d0612050601051207060c03120e030702090c0a02031e04090903080a0f110306130e060709050a090b030a080d 78
    0x4982d01e014000403409140058888220400005001c0d901c0c16481b9901130b8100b400200418800e0303020f010340c4a590090285600d98482034900028495128400e400c41484181c103c184030000880b2001c3d1540380fa410081a41c8900380348205e058860740050040b80a96100c0f0306070700b000c3c2c02ca900582410b0402504100040f407290040d00d407a50054081f904141c1c450805200c4100300302401048195034200420541469250310340c1c01e01d00454080c4205141c0070810140f055480c0192400201020022110a00030700c5885e50300214007680324083c0c03240424003500f00380080380c1c10b40c0a42d4000b949085000103024054049140c1040c0c007001d0700303010009010703859004480ba414800e588809591908001500071180d4030540444110710301b40d0120700d64122103089980000d0300b1500940c01d0b100460400c40940b0344100303182c450740922000c5c802c0c90b50b0090481410345c0c001b207030b010f849191160089001c036040d51900c5c99069000350186408618050003d100c3d181e0070717102c00b00e20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 502469379 1250 502468129 502468193
    0x30b0603010909060b180115050715060e0702010e1b01120c0801030201020f0102030622020d0c0f030605031204141206070f11010e0601090509100914121303 69
    0x8180c000740d002c400c4864440744140b081281e1403003154000070f03003207500498101841d0a003648201050240c1c001c0c10454032410346605000700d0a8032031b01a0300182d4440c00301d1100401102510a51107100c640008e0000424142d17401805600b8003548214000c0107580c950095041c1c3e440c7c0a000e140c0c1c1440400c604043c0e00d034005004e411000a55603d90b500503514500c002443c107401184924041d91040c8140302241d0b6514100c00910380030b80c5209401404141a158028032500c840484031a01e0000b641c2e50940d04407401803048500d03510208005962042030685a020021310300840702c1d001c02061064840c03140d00c0c01004a8098800c0005000707540e2841d24100d010360321400401c0004904804079644468620342e0250940300900240980c030030076940d140818002c1122858032400003c00814080251201c2c540d809503042c08a90000d040462141c41c011000504900031305948100000b5400100c8150303540241c402d55040d869600c2d8401d01260000b0800c030f04094000e05404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 502470629 1250 502469379 502469389
    0x31202030a1d06100e0c041221020703110a060206220213020d060f03020d11120106060c020a080f030d020f070c060305100905011805090c060a1e0207120f03030b 71
    0xb4900c1099001010141084000c0c0b140e61000c80e8820030140320300e03800700103103822018282c0341100e42c0319001002c10201031600001d0940c51708045440da11908440051841d80000c0e40c2003201d00840c0b851141461000c14030030340d860180103a90241e800761011030000f182c8407051000a8546200d64010148a40c2c001280d900070030420204494020448000400d1640f00342c1004050740ca100c0b00940d03140d5408a00705152528024100164204500e5215103c802000001410150003040101e44840002d40982d080e018241d0145c95425808103104030001002c5940a80000c011801e00900040c80d9019602a040b0b8981c507400c140611000030750180045c002500054401040c603241c040d1285040729a6640300d140c2d000c0c106001009401c001e910b2900350b400c40080c000c1415915104201d00e000c1d1100102034101d000060348409441e48502203580072a2008000b4400c0e940c640c0701265214000e01610307100041a4110b200005e04c141c0d45500c800d0312904000c40e1820425000134 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 502471879 1250 502470629 502470671
    0x17070203072a03081e04120b0a0b03061003113012031006020c0a0302010e061305030712150504050c060a0e0a0b040501030e0313120804091107021c031202030a 70
    0x440364040407a8170000c00c032642540d4113440d0b10007410746041a280602000d203d901061010702a0a00348011800d080c4031504441c4117060040e0449100e0304006100c442070344124401594111b0910322041042e24122810395421160303086001100e14071230644644a0b03440034052855481030160106840300d0800203140301d900d8400480e6121494000044c0c1003a6102c0003551042000d6a4140700603030b08518101c00290040d640c41d501c6d00c2554901d018540c0a581140c1d500d413042442c005900841c5c1e890144401d442030418400c03031005540c10030280c40d0143d8004183e42c0242d10030542504002028014401191030800704070800c0c903000c02c20b80d1100c0d41012421300c0c00014180000e5030035018548401000038000d42c50a100d8000c403082c844507a004404a98004400d80c00c14401110103640240013405410058507040d00d03011069503004410881c0202c070903c86012040020030b40b11054140c06071039080d200071060400c80029032000340214020b59880c0910801e00c0d00400410f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 502473129 1250 502471879 502471883
    0x40b160b040f1401020a12020c010209040504050a03030e03070804090903120e0706032306040905030903191101090b070219080a08041d0601170c16050c0117070203072a03 75
    0x5610307024050f040c5401200c0f050031042c05568010001e0210304c0c0e40c090380c030b000065000c40005807070381c0145e224140640f0420403503a900c641000b0500040c03103c081510100315229403410807102805101e1b140d142d0180810150511506010410481030180c20054501d4401d00e42550f60004484022085445482c0346004542c400c0c2c100344000d503094890b0b0220400d09521400c00300e003c0b80d1485903001401003c20303000b0b90303c40090030104202001603ca40141c01010b5800f1100008a9001e460004c6901581e80e81d442c06407102c055409003a000701915010300c0765a00e0003c07940c0900100c0d0b5401580d14030400d02d03058000035440001d010104030284101c0015513160300d0900c008140b094401c02c044c2e175007400076060103810fa80021001059080040000b00c403a40c80d01c40e2128940600180c05a52088544440041040c0070800d64040c8034241c903030662810071807412502801003140d02d50702680c010091180801c0c00e5100c008240c07403030703030b200f0013180482e0302c00103801071a00b50700c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 502474379 1250 502473129 502473143
    0x7060f12090b0117061f0315090c06050a0f03180609141014010906080d0c03090e04110405070309020a050d050a02062107020c01230702180106030f050903040b160b04 73
    0x49004c6003142404034a800025101d0001b0320507040584881400710548801008003400a0403a0307100400342e0800b507200354110801c824000c0d40d800c009081984180f21000c00100001d4402d00c1443c003c1c481d2180c01e40380e020b040f1508811555401c03006040c041d03410742c8e03205d10a654011f12420100692510420301e00004540c510301044404e18924041e04007180c842d04014080c00304580004c0c013844c2452203840c0c00c00ea0409203081c03c0e211000141c00005802441d03204200510040c0306401c036406509540401440d61044401c40031111949002540441506020801440d03e16080c0c40914040c034260341960300b0550006280d9400b408484103aa410b210f401000d58071107071501076005200b070001e01801555800000d24524901e2181a00c1090080200400c10041c070f00380e4100680c041c1c0540c7c42920030750910f80e06c4550174415040001d0a10b440032405e41c081e4001d0030300a0956400445c10503060403100b2007203811651034280c1c10b90040c102040403901940c141c40c0207500502c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 502475629 1250 502474379 502474409
    0x14040b09071d030a08030c1b060412080a1b0311090306100509090d0c121e030905010e030403150b190f090501051206150a180506030f07060f12090b01 66
    0x204030b103069030b20000758078880d820901050b800b00e29040c00303c80c0d020f0034202c10a035442c0041c00c1e0614440ca01506410b03e40d10400003008104280203420ba452881151070f2044580c1e240c0809005a86c07512103840c40060100f4510309907140603822142504402c003420360f041a08202c0480c0c58034108690b09040c900a4110400140c200380c0c5074141c110403031801800500c6003d00303028040b00c0c2d40d03d034010700520304101c800310360b076104d50b40c1d14105106441f401d030303004450901d00401a001c8800144c0e40d41d4604104002ca000f030003c201d900b242e9006104006122900e81c0c0c12008104101d15160401201c0f0000e10302c11410941c0c0102a00030f812014104608041c180011114140c00c2107001e40125141042c80321400929254860100850114041c000101243c0507601a5114034103c01c40b10030501078080140d0446403003080c040d82180c002401950f54540c1d140c01a100300d102082411a0b044d50b8a489603140700602400d1010200c2c0c45178559649409498090784060003545400c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 502476879 1250 502475629 502475657
    0xc1902061e0103020604061107030605010b070506070e1809150c04090e12090d0302010b10020109030212030103080a122004030204050f01081b01020a080a030e06010b03010e0114040b0907 82
    0x10100c201c00380030a200c4540759819036000c50a0707441030703010703003003e00800c2c982140260400b040701901540d0b010700d00388010b5075600c8900035982c2000c9800c4900303000c0c44000605061040801c01c01c00b5100903d00640303410303224a48540742c100a81012a1030168001c40010140000020390240480c08450756903180740020000841d404402d404103580c101c51800c000104244050342c0d064481203910300c0410105140c20f80c0113013242c0c4566038000c940c0311000b45500e90190b00494020b4001e401341c0f031182004000c842614070007404001e102403428001e100f8034610031040081101c84407180010311000842d1280e00704203030301d0050049910001024030450406001d03030b0b078010030307002c14400c0170794180010b60ba20350030700101d0003800a01e940d0f40c1040f50780c1700b0000f94200c00e41003c425541d41c00c5d030074401400b603c40c592607008580b0401000040704500703442224102d641441c041c0007c0e90070420301c00129140030303410300da0188c0c81c2e6809840f980da40c603a250b4000c02282c1c880c202d11212003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 502478129 1250 502476879 502476901
    0x1603020708091903021f0f1215030303051b07050d0807020a0b0103050a0c09051b09010212030a0e07120f0209060105070209090c03060c16080a14040305060a15030201170c190206 78
    0x101b00120310900c03011441c0f10100d030003d003502c1c840d89890601c104140486054800200446800c003007103200c107501c0000501d5010b40c0801d000d41c90866a4820140d0300414040302c3c2d104034000108107620810500092138400c503411600030320a0b105030341214100d070304d42e503c803500c082c0c100340c031740345c001500e040700704080841820700038415140c00380807130707c0e00146600c4408120109241d8402e0005200026a8030031b000d40e100400142000580360b041144603d40200700300c00c0c10008610900ca000304146d50402c0d040c00f51150b006035041800422542800101c0304090259410301000b0300c8000010390b520400e0b1449182c01c0300040030204181c10030140344c60005040d03180e220344100701a40040751075115481c08590015105030707440d07542d00021184c49001d40d200303901e8a080801e012041080c085000c41c0241e002407802d1140006801d4482005809440020b01242042c450181c0040166101300e502c405210700841c2401019085001044001100340b00180c025404201d560600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 502479379 1250 502478129 502478149
    0xe011e121203140f0412030e0703110915130b04060306110316080910020c0c060c100b1905010c060b0a080d1b081204050703050d03020a080906160302070809190302 72
    0x48008a8040d400c04c104200d0026402500103005a031000320344520f9140260410749010805034200ca003090350303900f0a00c008002c194190351141d0514004035803500614a01c0051400e070090006100c81e03480e000301d400800610080341c0c3c0042c1c4a200020204115109040d89441124540c0390359142018043d0301c25040070701d4104c2840307520000d210b05030000280304644c840c03101000582c0c0b4401451507a14240c3c13000215640f018000403d03c00240d0b01141064081c103040c0d00030301184000b8410070484120144c0c51402e01c1c070f0001030803c0990700c5a0210052030b40554000214002190003003000c060454020395038640c800c0c1c0070410555031001104207140b03401980e2072032004c0c851340e44014600c83c84481c5541c0401500c04141400014030110000b182d2020440d04a22a19200a000b9411038481000410b1080c8001000c030400803590a10800d4010a82020160708031416402900150401d0303512100c240140d1b0300645600c0d04070607014000102c044452482c0d4810480600c030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 502480629 1250 502479379 502479401
    0x507051504110607210c12080105011403041115030615030f06011103270901050f01021f0b030f0616090806010312030e190213060e011e121203 63
    0x3401010070010a4000e0340e0200d4400040fa21256510004d09003035901126012004c402c406520a10401c0c254101040c01c2d03520f4421600e0101c8103094a005503499207003403003464049103425400c2c01d640640c00740113540c40382c45500d0030751001d43c40401048442c0b000024044030300b04004203210702d81c5061501e550040008901c100c1c9540b03450260b840c08028058185410720071000c0c078400d5400018010780b0071280000d8402c3c0b0a00c00c26078000c4054840030000700b4010038000002294600301407041c8100414103030024403581030048005c2c8608100c00f032510388000d5482c0500b1714140d4060040012080f10000100450308006003c5c00300d080c1400642e1003403100c10023041208042c0030540c41d0441e030304111070784140106140d0940240c50b090007030311301d40c0c010b140c680c1500070226400d070640345009607224100c1144400c490381c1120051300400000d072607110010000b981c01e02000d1a40d0519080c1110001a074a018804042c1c41c0c00a0803910010080784c5440c1286c0d05218000c8800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 502481879 1250 502480629 502480663
    0x901050a03080d180209160f17070e030102190c0c06090323010f0e0124080705060313020303341208070e10090602060a1b0c050109050d050705 63
    0x1407a555071500507201d00755440500d203490b540c58082c44e100c501c000501ca1384d00601ba54a075843c0c154a0340f4003400d1185900b0b004a02c10500850f0082d03c1150700210001c00c0c140e1002c0039444800c0140c85500100c0740c81c950540d0200900030182c0c184d00c81d03600384a040d40c2c650040d14062807800702c1100800d0f070060000c004090404001140c4401110310004100a000b6207040e00c0f0300c58841d02420748810400101c0d801d2900b110b11038074055010040940d20010300011403828000a140700701c86030300c10a04581d000d80400e0102d071502000035601301c1c00014101400800c80da0100e419034004188040194030255a2050032100705020701000c07804418000d18100d401e9641d075042d00e601d00c40e8074000c02c0138400004a041d0302a92241e0704010000746a500010030b1840000c1c1000101c0c0594070040c003800c80841c000f401c075070140751030388100c0b40c03007010180c1c842d40030440d000b0410203003c0d1155900c407007000c0b011680a0103401074461983d039800c0e0b0344217424104140360608407928841b0403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 502483129 1250 502481879 502481899
    0x60e030d0c120513020904080702040603081902010c201515010f0201090302100203041104110309010b032410180203040c0806060a06030b03010f110a080115090909140a030905090105 80
    0x48188001303200a540c0e412641d5464a80303c608100c1503500440a0083d00329180c2040402840303c404040c01d010030b9640e0b850311252405203001ca0983c0c000f884403c01040c189444141034a40c94554800c60791881011a1402e8000c5c00c0361500142050b6a804200e121213404841c165902c0303055506080700c40c2c0000d0042c0700e075940d0020341d81d4a40c0190304065540c00700104080110b510364130318001500420601c112610240d16810990003a240602c6079840c0000ea542039083c04900003c0250042c0d0091401207614600300918010042000a50302d007a9800440c1e450142c4103500c1021402c0c0400603201d103454a401025140d480e00050180d40c08001000101d40d00c001ca404d0079a0400c0c036020a046c1d15180100e4050310b0301c1c030110402c10f801c202070a240e206180b4003400b0b1300312195580700f8a81c0d0b0382d04c0091901c0c035201e04060002a901800900003035126403c85030b41d05124207050341c0d4801611a18030b040803510311003107002541620081005140c00a00369000d00011100c1d9003038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 502484379 1250 502483129 502483141
    0x6130501020f120a1b050a0b0a050a27020111030304030c0218010806130309090e0c040f0209030a0308040309031a1e010b0d0b030307021005070501060807030803070c060e030d0c1205 80
    0x3180604481942000035000040401c08140f00c400c05e28160700400319055030000785000711280d00c040303034412916850540026503e92240c01001c60b43c904040b070369403201c022880e54106071800203401f42d060000003e22a9602e03e020402907200c1c03406a9102510050b591040065444e45215480701a0141c1801442580400314003070b90080442c0040d15116030b1035207015192620743d0b6218074a51840c0c00c4002d80e1651002c0b03400241040c0c215020440304030240401c80484c0142e40d511038040d8429840356000074011034446030482e0003404c12a142c50b991b5911b014000f54012001e2440078600020300c1084044044103c4280e007c00c6e070090001e604004086604d8018802c034000810b48510b00101c03162400e004803001940c01400d00340c040d21124030042d000b80d00c1190100e41c25840c0800000310050080f94030000d4170760000960303240d0b854800e0110790b004144c0c1d0080e11401c3d80d5090600b4203000c01c1004003807801c1e4040d0007240e2002c4060000d000c10144200d450182420301c0e0030012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 502485629 1250 502484379 502484413
    0xa0b060306010f0c1506060e0d030e090712091226060607170d0605100905010c020105091206010e0601020c01030905070308210106090e013206070206130501020f 71
    0x1901c120700380782030b024910200d8002c03a104043c91102400003005100180811040303030700b0440c140c80c02d170b84920300d00010900a11600f02c3c2c0111000d800100b111500050038035044050a030000000c1c900f80155000d00c90382032003125100f00301120040720801c525100300d0303040750601d807445403420225908084459200794120000600061142c000010745004104084442da40d45151500c03840c1c0e20303120f940608500074600790181074441c2006d26091000c991080d07500e0015618103070740f24214100305a0056070741e5001b8a11142e0300001440194150007800c00400b402081d180352880c110b420724000190510056102c0c5904050030a000034022840003d42d41c422a0382c0244650b0307a403070f41110344800007543c40c044001540b00c0f280000590341da0040d03507081940d80000d01c0410690340c0d000c4e0200040744161441c649002460129000519400c144200700f000c090103851500006a00086040d404980039000b00c54051b0f030203110b01d5038100400818440c61000608000c10308640c881 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 502486879 1250 502485629 502485631
    0x306030606012a0b01030c0b18041109090a090318050120160807080601090203091e030409020d060e0c0304050a062a03091101091202040e0a0f0c0603050a0b0603 71
    0x2410302c016080907030030f0468a2441040c4002c1d071025110002005890704007602242880142c5404068003400308e4080a600112004030714a2184428608201c0b003d200c003030065120321703215610052046030480d80780c81c12014814185070000241a1001c2c1c078000c0e00168081824a42d054003022091103181d0700a00450344444005c4074031904410050381d0146400d0b0a010055002c0b40700000c0007890110004803070050303400c50390503103403140c1c0c8035100402280412030310100c1c10b0340903c110f0751110b91050040c034503039048101520b18140d11504101d007668070080940c400f40f48d45000410600354401c4003a03401c8122000c0303182ca1400c0c69218680e8640c0c6000c07000e009160b950381121001c28110340c6501c80018100ca20b0300c00c0d03401914024008280c42c030310544200c0c0e44805006255840344042900740d844e980000c81c90308445400780030041c00c030340143c00742c14820201034034003040002d440c001b11b1130f00c40e081c0307103602900f401d4000b410340708042d110640950400d08201d9680d038440d010340e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 502488129 1250 502486879 502486891
    0x60a12110a0c0f02040617060901050f040b0103080304022e0e04201b0d0f021608031912060f03140a030e060d0b04090809010e12030409021315020304150503060306 72
    0x40b598251130000800800b0103a010205011400c4000f0344014801b0407028070031003100c0c008000564501011400c050b000300c800900c031150100042c80000c3c0f0b494055508030380007600004041c2202102c0b8a80291031140942c00d0303a03c010010078255a1000c1048403180f42601d05000014080d6040700241c400c8440422401c000854040940300c4040410405441480c046a0300c610708900301401525096110f44010700070040316022401c140290319040304d084400840c90543c01c007080340c5822440d0a003620401010080510740d00e11a406060080d0207070078000d0041514502d03201e01003801c09501c040311034208098043c0802d4022401c40c010f0305064600300c0e13440d0001411b4800501e003005c0d000303a00a01d0110805c0c14130160724082c1c5014034003a208c1141c0b18030000208031019100c180905030300d030300822060203586a55005071001900e04082c02c103d91707898104004010440d90200d400580c0003007030402055502d900c03c4a44102281042d500d03508207c40883d8440e5002024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 502489379 1250 502488129 502488143
    0x70c02130207060203012c1915080312071b080901090801140103020301200906131a070c0b04030f0b09190b041202120d0b0a05060a12110a0c 62
    0x5005549810500314800900030004568400b29858000001c0d0400c2c062620328032060301c840c400361000070f004901904007820248506d07076202084042d140c0284014640e4980c2c4500c1001002d542c5506580090a0004091600c419600c0640c040c12207008000004101000500c2c2a40b000700b604070a450f40c0c1c118140d03d07601c100c48001a20104000d0703003e4856517181101e11100e13143e1941c0114140d80c03080300244003500c03496043c4d6401200100c541040c5220800494040b4a4500700500c1140d2031040c0f010a1545e6034170700013529480340c11a000c054500080d1300e10410010880f03810240012035003843c01c00e0b085454024000546010003045850f150001c00d9040703108104070861042d60b081c490400e4140303840c1104403a1016507088400c100445080072100e4008102a800d10380c45a0303602d0309000f01280540003400803900c555400145100000c02d9985440000b08107202c515128452512940d1b003052048513124240402460418003081a041b64030800160b140d43d04000307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 502490629 1250 502489379 502489397
    0x180c0907110102070c060f090b0306010516050a1205120f13020409060615121401051c060b06030f04122f0304050303160c0b030c190203120a150602070e07 68
    0x44807600910640c0e4010300f248020344c40024006a01500c10721185d10b203a03036103140300356440c0301170003540c0001d82e051400700d40284418202d4120648095045038015001c031200d0138143c0c1c903040300c00d80c030340c070f68401c0081d00c0000d2808001e030102e11a00c1c0c001c045811034481906d080154082d5009200030002d2185450b0b9440c0c07000d000c9941c100c81d02420040019201d06c030000e51000c3c260240300300202824905103800351081780341c100c002d2030481e940500840348040a860b009203150f82c041b5022146650f651000783c1440c0c40b240003451240040d42c209604906142c02c00c89980c0802d46a074004104260002c43d00354000071000120f0001148000300c03104150302c28040c254001c64015030340501c4046400b8035000341407101c9a000b2405030001340241601d64610402d248800c55044081400c100482d137510f0f6540080c40c00a002d051054904003111030044030741e505819078028034041e0321010701d1025841c003c89580c006011a00080c401c4900e0b142000155180040190003482418a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 502491879 1250 502490629 502490657
    0x509060d0c0605040915080a0609080423090903270d140102030f010506040602070b13051f031b12050c1603210605010203090f190e180c0907 62
    0x6001049059401000c840c1c801d03460b004000d14541161084005140c1007540103189001c01120103070595584c2170240c0700b100e080e5114030002d40001c61040740e400c01e0402001540764100741c0401400e04c507094805185002d90010482e000d0405031400a85030000c01c0000140140c4608400311082c0345809505078551100000300000340b8054080c02901040100d5500003c0650065110b019400e03022402c40e6200c0c801d2112502641c01814056031082c5428040d0030032400150002c052040300000e05243c80c0d6000c5134440300001c41c40c01a400c4c1070b10442c000940c140c092803030100402843e0810050311501c000300801c48040705410b166541d4000305a40c3c000ba070007111240c000c294107107100400030b840c0091112006021a0251601d10200b80002c49201e019510844905078020b5042c0300705030080103c1d154240c20303082e6010f503800000004030501020820000c1550205030040c500e025603002d04105500c41024103150840030304d5400c1075582480c40750f00b104141c54903440c003003961 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 502493129 1250 502491879 502491889
    0x10020d0e060f2a0606011202030c0f0d0915050606040302040203060301020403060c020f060f04200a030c06031a06040b0708180603161b080409020a0315080a0318060207050906 77
    0x1c0c0280b6400900000300704807140071240241e0004034039090100100494008802d884480c00e80f030050000b5850700010700c01030900d40143d030304541c90a4196240c01d107588001030003070b800b0140c01d841e9a6182d070744003010b00103489000b2107010001e000600031032410900184841c41203010003071003141e020000c03c0d46030314258141c1e005194403c80400811400b080060340d50341021b00451028412000060901e01448419a000f958400c41074011300600c1c4160280d02d402c041611900000c01e11030010205d410706440000070700c2c2d0f40e01c001810702c00400449220383c110a0102e4002c80741040200445c0000c1021509456085201d050311440070002561032594503c80340e41c0d01502c0402030024084172500c6c804400d0750613031100310403c1c0302812800c22413414140003800c0d07607005001c1001003c80c50780080150118500d00051048100c220407250070741d00d07800681d415170280241d0002c041d02700624150700b5520042205545250050080d0b407800c003030088900a80c0d071140400c04075154 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 502494379 1250 502493129 502493137
    0x1a0316061418040906090b070507051b1f03021e16020409020102030f1809010e06100f0c0b09100e03040b0304080a030608150f070318020d020607080a0504050103060510020d0e06 78
    0x200400c02d0284c24003e0038600c000c0c05103180e01382c441e0741e262404a0903641c02802199411940040a010316401554500311401101c400c141e4124401c00001030740709013820070a18041ca1241c6005880e40c926141002c85a0360303605029001240030010b091540c25100840c010007503040324003042030b02044c40101d0841c0501030f0000442600420034181408090f01c90000400d0144c0356180799a9035402420710200f015a581a0401c929240d5400d031240719200d08a66001581031034100c10340103030782d2119682d90499401e002c42e0400860b40764846102d008045d0711041200c02075040605000280c1c0882c44090700040c0400400070704090951700a400c443c0080001c2e40c240d512903003024184010710001100c5150141f41140d0000b10018001c0c4110055200d1318050329200e00c08580c01d10030075142c07904091380d1200003803101c0000611800e00402c4420140c0d511140c940e4542800501504d199420840c0b00340400104000255130010302c1e58003008031407500e01d4642c41064040f44a43c4a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 502495629 1250 502494379 502494427
    0x5090f0711060a06060f03181101051c050f060a050121180501142409130807050f0f010c140a030608030f27031f0608011a03160614 58
    0xb0712410032480010640c0312a0465910752922110292400c000302d00b100c001074403050310350240f0b11003040411000000a00d01c0700040c10540e00c0d041e448005170081e80d4403107070340b000351301e80343c408000300000c0740b80b10650000c0d01a5042c00c016414040060b02024200350359026081c515003440c06c0c004c0791038104403550038410000703554210309410403601a085132500b0b00c2c140301020340400c8440d4030407415034440804440e043c031681c0101000300040f041c0301409c0340d518130254a1407107000c20010801001c40c107214500030010080005096800c02c894803d8090090342342650314840340d6003004408414051f00d122159072080004401e0740101620b4020607040e101c04150310101d10399040080100303030001a210380745101c1800300d02d402c94500c010801e030190040d01d8000000c9a0010b5818038a10310190082001a180c240d02421900b4810f0341c0d0440114881d1403503e00d04041c031003841d6441952201c840000d080c00701c0500342d03d00c000350003120b05e0740c001480c04600c6080814142064 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 502496879 1250 502495629 502495633
    0x307090f03120f020601060f05070203030409020c0102070b010b13050f0d05010507090f05060f180d05010207060b010806090f16090314030702040b010f02060112060f09030201051005040605090f0711 87
    0x40e40300e081c045119502e000b1040003280c101c0c02001061400000c1c640d0481e5201d41e03690209421b80101102d190700300c14000c83c0c040c4014400400c00b91200e0000c3d10104551500042e195241403d1000045030181d21442c5080c07020020748290300c41000c280b8065070020303a4029070b0035090340080f030000d1380070300340c0a071242d441c3c401400119a40b1005000c12241c0159213a01191740b01c0c0100510307880303008030820422300108031050003040c1111043c0160100203007a105d610342c0c80c1d02d540c1d0070b81e44101c0c42210000e580e1003d9110b15a0400a181d03003121042d01d41d8801440d04585010116034007510303c0c14a60301c42c00c211030700740748651918000b0b554401c0e0341e03a1210700c600303080542e03e40004008910560600c00c10145951041442d4410142994010f001e02d92814240e5501501c10400a680b8541c842403e00c00d816601c0c001e9002d9107103e5400000c051500e149400c1080550f0707001107109504190702000141d070f50540303071070b00300c4c5d0410142d45d12610341a00544100c0300010440040d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 502498129 1250 502496879 502496909
    0x705010e0d0914012003070203031306170402102d09030506090a080d09020105071e030e0405090309060903010204050a060c140601122003100902031e030f030709 71
    0x100004240c01d00200e50035100d4034503103030700e80d07952640c4050700c000801d0005480c804507040f00c1c40c2d1000903524045a80e403e4034030b003002680200703045130320085811000d0140700d102041061360203401e01d50413507481d01d44048542419400181c01441008400e1708100d40039100040d0040003c0401d43c0b6503040c014552800c1290060103030510000703100c156200d0250800149800760b02080740444a644040030303034a0140c02000300f00c010800d00354280e0410030280102c50000d0740d95100c54190400040c4841d80402a5103001803048072031611a038020b50420050040703910780042030700e104000440c1d03003d0b107540510011a0081c0aa0703031100d0340c0700005c0e03080002c1e466000074004107018000c00306242e0600e00d080e55241c0d00d0800b84645141048204100b401080101d048014080d0204602c079040e80074000c00031303160500141100403002da0340c01c0c0c2780046280800c0f507080c114680010a1803d00010101c032600c178000d043d095501910008006034440e845143c00002501c2030f0032280c070760 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 502499379 1250 502498129 502498151
    0x3100b07151a03071703031602030f03010b120702010b0f0d030e0904240c020706200631080a0e1309081c050f0412090803180a0506031504020f070501 66
    0x6001c485100a00074090600041a02d1740754400000d803d10090008500e0b5031145d00300d2071098241d41e1001e03030031400705010454040c2d8902004600a10a40740180e031190310944800d05a800040d01c6041075a242c41c58910309a1121002209107d008490110301b841703407400d05071900b0b10b4070411030b40c0c0f1030032000410041004079440c2c25940c501e51584900c08400d50221b000c00ca03142125003e000d40c1c0032550420807640b0030003161000c489035000000e00c1c2c03c0d940e940c052615600350340358441c021403c02d4010646603030494584444c460243c40c2844001961a0000d4a2150504c100100310011003200c030300791901c840710069210341e03440c20000036942d414406078680012101c07066043c02c0c184200a90303c00c5000e4140250030307000104d10280c036660748031507100400140800a2211030000021000700510240a01da0100404000700040080070081f68100c01e40040e84940018028040d9034603205001e155048826500107030303201c2c10702001d140f85008013080240b5940c00c01030b031101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 502500629 1250 502499379 502499411
    0x506070b070201061e030b061309060603020f03121b07050306040f020f1210051906060c02180f0a0b04020706060b1306020304060c1e020a060801031101020303100b0715 74
    0x122074001c0b54020480c0030749a18041104240c3d1007980080002e0101c4148003040642c180c041c1c004800404200111031100038400c2540d00c001e07000c0c0c5003142d44480c100250700b0040c40303104010710120301400700d60030407071400d00080c003569101c42c40740c0c401c0d480f4402a950040100001801000b01118010320782490000004220450200e001d902420448451414864481400205804050f0040e51401b4543c0b0340240307401040e483c0c84034402c2d100000d02c001c1d2440340d000a080e542d079540919403aa40144070780c1402408200000c40b40c81d008000d00803d01601c55074200c50350000202e0181da501c0c0025010303004112002c0d00c170318500380d4006030044180380181b81c60301c0108401c907001c2e13a032014280d03200d0150f80b0622004ca1900d202600001e0540105450300748103124108200c88115008207080e000380703402a002213410ba0b0010700c14460ba04a200420040900c011407461402202c09020750040f44950200c0d201d000c504041080314014001034030500c1500b040055040780311600e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 502501879 1250 502500629 502500631
    0x40213110d06050301060e07050d0b190501110309030a0b090f10091103060f070c0f0602031806010e0720030d09081c0629160309090b0603060114030903040506070b 72
    0x7034841d280c614002040d080602a4800300c032821100400070355a0040207503a2540070f10004000695110f149000c01d40d03c0600041c00c0300700c00651900080e0070003001402d0143e020ba010001c0c0c2c0c1c801d01604030f182e58000390010b0b07060b0744002032981c940c03035900103c0c0c500b05458611015038043c0341c1002104202c1c2d584281c0100c1c1c010182074111300750500506072039507025a4070040341201c41c0300041015000b0035070400c81d0740c81280c0c1c4911030039003512204100d030400c0e01c02501c038661481900350315200402c03019014101d1030004100906098501814025980034030180207021488000358aa1040c4107079038840707540407014071204207076141c080d8059001190006010050509100071001d80348a0302c8180c3d04100001c0803031141f114801e0030a20f8034111600002c54041001c04c03000045240312143c45440b9481e40d514031410010000c003529040c0d24100d024560501c00c1041c00da922940507450960410300040e13807901d5640302d103400c610640c0c1100f608040006070340d50400405103109 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 502503129 1250 502501879 502501897
    0x30f03051b1f050702060601270f06090b0a0807080c040e131b05130213050a170d0804020f0103090309050a0f0f0906062a02040509030a080601050906040e04021311 72
    0x40c42d150103070400502150303000d80d04030700164010700c00a0010b50107200214599000b25242c0070b41d08040c080020a981d982c0c0c0c000120142d40810100402904940340101510003810054101304907240300802081e4001c0500381000900d80c0803801114558080700c020780080a40354040b49040d800d50107074025a94000c45400101d0b55212000c00340f000591029a079008054842a07200a84030307001941011240c45030180f8407180c000b030070b9615410a4401045d070b0030079000c4103c6001010500b004008043c0c1002c5c0031a4000300001603850240c2003001c81e4007401c000841c182182411100c58020b500a1904503408400202d46a40106000003c0714280c1d08500e0420307458141400580e40346100d0100495450208000c00d00c0c208201610041a03403880041c41001c05e4000400f510000d6440b5085a000015041003156110100640c845000e08105107400c1086020030035900c25841816445441300c0d020608541d950460030200c0f8000c003505001c1d8640c0c424030b0708642d900c400a9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 502504379 1250 502503129 502503163
    0x1303080301060e10030b0a03080714060708160e06030402012007060507050c030a03050921070303110606010c0b0612010f11091801050904030806060c0a030806150310030f03051b 78
    0x1c052044c6119001c0c1c1815044064600c8103040d1131965000956040900110b4481d05c5058454500360b10030000d6602c07504503951512414108a40c0840d00341286058450070080c41801c0d41c00140c0b80d5800701c9030440d90a107001400c0e4205282000d171541d59030384240c0c100340144807001803160350242c00350031641d0054054441034600d03541010354030911000010045541070204404a2174152001c1010500c02207004840681040c6c0c0541000c0007a04100d0110324509211390248504210542c3d000400313003016044008103440e02444e08400401503441008450f421220b007030400c7d0803509966203c91420b000400d8680100702c5a1f42104821600520076201c400310011030380e480180c103c642c013130450401d64803241c0701100c0d010f000800c1c40e90080b800300251441c1071000c001d1380c91954003a9440c4041420f0a0007042118000015540c007464410b01c107210f0114010b50074034040f0780d441141140d000403d403800f91421b00a412440d1001c44c10000ca40302522000300703820f0032400320002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 502505629 1250 502504379 502504399
    0x9110111160305061f0e060f060403050d05031017100c0302040b1b010e03040b09090601030e1515030307051f0605180901051e130302120c01020d0c050f030c1303080301060e 76
    0x100520a003144900100c514240c1b001c2401824608003010703003a0b01c0544000e180907100d4440307a240030300c000c4515001603000030810625810360841c00010703001d5104150040030b9445203a940d288502460a1b12582c1d851031a030200a010382e04441c010462440d101d52656011404000d0241d1884000113265092400018040002001311420b03524980350003403c10140c0c00a101c1400c0005101074141070303884683c40a03803101000740d098050405031729412646014100e8451421200388801e002c0c0e441400036000041000ca0380c03c2e000c1703800301014515114015010005040d19604c041c0c0c001d100d580004a2149519034114030495840c0002d000c01d03281d03400d0001c07241d68440000480b0980c820301040160311421844d408050080c411a41c6a071398402c2411481d41c014804034895a50000c1c200c01c4071110b0703008079130003020181802424003611420641d02c911000304444440d4000003102c0c511031141c0340e035900c0034540250f061512580c481c5009030190009021032403041d00145 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 502506879 1250 502505629 502505671
    0x902040c020d050a080606070606080604030e0a0506040608190603031107060513030b100e180606032e020d0f090203010b0a180c020a050a03021e010911011116030506 73
    0x2c80c0303141c818655440524040da562030031118070001410031684a04100580400f0074654000c0e01c0140c260a009400e00c1c1c2018600074050702044100b09000380750541c41000140c0d2034000342c03821615182840c01880c1e9522074000c058081401c0c10003242481d101010090650110608506c420003400b00d0355038039103803c01503880b0701031001e84100b2102220f9050000a00c074103003940e000001244941c14941c0c486059080600040b10340c00c4041003161500f003100300d003c1003002e4112070709401030105443d5079000c0301047c0c140c0d00000004800c0640c5000c54008156048404801824908100a100b4200078802030300c00c0c2c90b0246e203e5802c1076017070b01440c5000100001100c46a402000118030b05c9298030f006001075025520550058010110208070203110100c1101d10035806070400c0311351790104070150b858a0200b60b0140e0703d0006c4400c0040c220f82100c140074142400c2c10540c1404040d00315180454100040c80b05c5040044004108100010001c0c002d0340342550320311503c8038039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 502508129 1250 502506879 502506883
    0xc03140c04030c0e060d0303020c0f060705180604081213031a01140405060d03080910090f120203030403020d030b120a030801230121020c03070506040204110a0819020d0f0902040c02 80
    0x3585d40680c0201a00c02c0310b40080d0080e4010400c640b01c9a080e20055200701451b5418428100d41030fa01241001500202d8811152003001c80350b04200c940504040c108080c1c19030f500c403044802c00c0c0c00c0000003a036040c15070040c0440c90003503501803403180884000281e85407101c0401e00c90001c0e007101e07400b51000545024003415100301c00240010240c42e130103440c00c80d0004000f07040d0038024040c0009004040c130a41c011840081e01400c0b88a0240013249011100000301007203020441d0814003c3c80000780e070102d2490b007140343c285004942e040399500003884e45561804600c9031403042481810415402014090407601c052030917100030300200c04011442c00c941450300d030004079565600419141560301c050200100e03586d00604204070015a285907038002c110a03201c1d940003904020840c5814000c941c80e0300420b41182e81800d80011025042c90b41c00341607190828404504007254098560544403d030b00c554905003c10070304080c4807801000004000d9015a05102d4a0403541d800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 502509379 1250 502508129 502508131
    0xb0a02060a050c0703080403180303030b102a020616110a05031606050d0f060e1b0909060409050f1917031b07060603060c050a1107180c03140c04030c0e 67
    0x118150252801104e980c0032120300070001d00403001d011f010060080c248019121413401b5501c41d4500080e081301281c1009910303200c00702c0703120811034081d10303070601d10982083c04802a803810982d00003032801c0c0c1c40040c460b0b0141c203189c20b03c40ca0415800e0800d0080300c074840c074540e06056520019031611101030544520f000c8070114248000030104001203445200180582e50703000d400017600244008080707042d5205039201c4440d89481d04180002c035195514924036045080220034908000600815107210f80104194415569111400e040c09010300c03009000c1c1d014201130340c0b041a56003a1004903080d01d90400d03540441007642c00c0322191580d008036070240e0800030025251410500b001c1074181e0040c407048130346541310400000018464080c5541c41c2405403100c0d910b40c0d0f21450004d0541c44030703115032480c40d8425081003008101100341d580003410f10140229030380b030000cc401d602030252092580ca000314134004008100005602402c103403845030000d105c800e6964010581c82542c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 502510629 1250 502509379 502509391
    0x605010311030c10050c010624020d020615060c210a0f02010209090402121504060b010f020d090e0c160c030b06010f090509100312120f1107020d0503040803040b0a02060a05 76
    0x520444c954109402040a000601c0c0c16100110f491a1161400c000d141902e46440617950b20002816140e03640502c14071411400740d1004100d28a032481c03020140f903590300da4a43c01107100041000201d08107014075891480700400f05e00c0d04040e840c207440d9680c0d10101c00c80001460500190000030302c18000c4541c2468010040742c22034959800b00f0500c0c40f440c1d00041c10500c20f0950b240e0307100030034440440c4a00d008010000d210b40100c0c0002d4082c1c06032402a0b070841d00014002035990350000b10243c191821004250700303507510540491494400c1c50400d00109030500d0075441005544070340601581e2040e806017010752103110065078400c40100c0700e03101040329080248042c1c04c10303010035980020b100d116850450f550ba21600d0300b0403030144511000a003288080d10703117800180510514001c14210401c050030000a0b6a040c0340510600244521071840d11396007030180c20004d0707038007030403a003000c2d40c0d03480e9a00e054501c615032056031030602600801c0000b40f40c050b20341c41401d11941d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 502511879 1250 502510629 502510639
    0x31407021c020c01200109020d0b0604050606040e07030b0a08100221130f0503093610060320030c0a031107120c03090e10030606081603141002070605010311030c 71
    0x15051820080c5d007600d00138402d031107903580c0c8180038050b03030714840b210420502450000c0400c2c142001400169440280000e001d0402088108880d01078400e400340d10840c9440c002500c41c41010024100307451990003000c0130320031408040b081e421554010441040c800980c01d10780c402c503c0c00c9000d140d0b070449805501d110641a8600030030300c000451810140700c3e00580f031901000e240002c0c1c107102444605400340b000c09200000c443e2485650301103c41c056049240c40d807504401000540d207039030082d80105030310303000750000300d11810546642e001152035172035449142030035400e070342a04140314074070019003081c0e44040c020720800c00700d40c05580c224030891124620000c003950345007504a000c500700301922000040c19001c1c010158010272541d1001141e1038075508080041d51a01d4200300660b0300711003281c2c140389201c02c403858112030b0700031640301c0964804401903040c4240286d000c0c02035400003601c1d00070003140e54400d0341a00e00c00e00400181140328024182daa00c480c0c5140c0b9040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 502513129 1250 502511879 502511897
    0x8040f08011415012102070c08060f06030715090f0303022802010203030a0902010e04090c06020c0901380c0705040c0203031302090a0e011a04053103031407021c020c01 74
    0xc2d5200d415144103030030140c1da43c0e02a0302c201917104c00403030303001ca00183d4410413a05401d0103521018019942c000d0600480c0400701d040000c0000c0d2036404906c604810700c0034891b210310f46180030f0710305d040050902e54044000b02e5030301d050107503c1d6007c0747c548080545844034031001c081121649200c0d896010f0b03000f0750640d982c101604c030003481010b00036410700c071222404454070340d42e0b8001c05400358800c01030f0f0b00d01d05d80762441c0640707003040301304003544145181e40061241c960a480e100c90901c0b0709041c0b210710340d210b80445203a0f65803241c40e802c81e003910016994403141800a50681140c00c19101044100816202261039000590b951980300210a81107000351400000c1e80350010310f401e00c0041c501c40321104040c2140c0d104200040c544900c001207441e0745c6000d2240d84c3e800003000f540515124003008917170b0340100048140d2081d138480c1c030180400b80340c420b91000686164482c0828141d0a0981c4003075556240001545204488001c411090300e101207610201c002040c0c40b51060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 502514379 1250 502513129 502513171
    0xe2805060f01121509050102160b010515070609110a030c15030c050a03240e0103020f040c0203030403181208030402030d020f07032603180606030d0f0503060d08040f080114 76
    0x2210b130240c0001812a600e0350410700c0030030420b100034040d00b100407040c00b041e0355062806001540341644110311034500c0040c142c100801c080100c442c416403041c0d0015400d070f06842c28121441201801542101104402008200d0600d0900068076841200b4010500035003004506851042d5a0300c070009000740308070704a05000b6048a1844100c40c00c4803400780043e003004868084460f40101c101425060041040d810b00b6841e03644101002e40307090040300304440b40a03580f840094802020061111100c400d0061a82c8644d8040d060340200b00d2a01b00c00f41c100304003141c0080d50141d1003409036520403140c2030700016814800c4101071019043c542e01d161a280c0c6001e8017200b094400803a015054520a000b090045202c1c20070400c040441c60000307000b052600c40010700c03803801b9500c013000c0950000c1c0c202c01c141f0502d070700501d0216502d94506002c250400b0318070200900130070300820b0116a106d01144101e09807040c0b400208800344040e0301c0001c441c8003d5618451001800b602069 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 502515629 1250 502514379 502514393
    0x10911161101020708030d141506070308040f02060a030b011d1c022215060e010203030f04060e07080607031a0f0907022a0a0909030905040e2805060f0112 68
    0x103036a072050041c0c03804d0710f0791102c10b5400d6500085481c0061559140702040c030304052040c0707d8111603040c803140002c032220b10114601d44240c410140034092030f80700003000c001c00ca0b80b10b000c60560140c003050b20f0700c2017544080c0140c406c640910380800d6103607102001c02d80825a0340702549a0040c8039010400020104202c40c402c07260003a80c2081a070801c41c5007490741e5406a00f0071180038040020b01402d103600c04586003c1d250002c40401008072031b81100c6a0b40042901c1e003010049110407026250351034101b004040c07103001d101c4a80030b0117400084007030000c22024424910344e1018050300071401900c8039a03c0e4004841c5038803a0080109142909144142680c4128640104c0f40174844c2c8101042080790031400313401c01d04041d0300e115291802c003584030708010800c1c1c240c10b0100000f13503a0090882d5a040c0102400b0300d07950900a807428404001c1501042e264898000402a160842e0f0654650498096072144a5440420303030720140b4034501070407681c1c0d4924040040d0b6160340c4001d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 502516879 1250 502515629 502515653
    0x906190608062808151513060801091a01080a0503030f040c050307031101021e0613020a05060f0c070b030702030a0f17180706020c01051209010f02040b0301091116 72
    0x243c1007280c00528001d03094220041c50903850304600070100a0349070132200d9181100d034051450107452050103100400d4414050902000710032565002101100d9603550001c0131158003c0d0350320360a15801030240004445a9115240000d1241c0100ea807502065a940e800345c900c0109103500c10800038020020005030141c01510402e4a074680d541d403030000034a023180640042d43c10425001c01c02802c1d680400a01060701d951002042e0700116200c8125165030b00108503009104900d440d0100719a0b9000111014003802000c407a11180c00b500445a1038109190301c103194071800c040450701040078016240305030f000e40d00851416010b00d504680c80100002040284400e5010141c1000ca840e11801e2060003049075211081b1841200b15103485510303070001082d90811507420010381d90080450306001200c1184011545034466218014200304002d0000d492000c94042035441140c0000c604031174954105010108400c10b120205206044c004008201c10a82040018403102411 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 502517985 1106 502516879 502516891
    0x20c0a0303080105010e03010f0c090f0902091014070c0e041b0803030c130f0b040e160c06090203010b0d08090a0602070803030114030a140a020906190608 68
    0x25082ca2410301505041004805002d20f550300c09400080b04100c135400200420707141400c00400b810480c5c00b41418440501c40c00080c00c102c18001d81d042003c1c0107140c0200c030f04071440151484090004501101d40c02404000003151410003450300403da41c00e548074091404e440c2041c800c0b8154005000d4a079240d48042c4008980042900c1e44004104030484c0d540c1c59410400030b1f0130040303510100d81d0141803900410f1001e41031005d00215a41084080002c0d190b04c9589020903526180709000205010030480104005410040f4001c1c000340002a900001e0700224500441d8008160340140d00000c000042d0b00b8001500070050800744054601c0b035042001c502d44910040c49156824100b521080b20103603030030300c22801c245500c6070601ca03140c0f410080b9140c84d0600701d0403d9116400c45400148281011007010910031030494007558207d003404c3e0183d0707001d0805400 = true := by decide +kernel

theorem cover : BRFrame.Cov 502338129 502517985 := by
  have h0 := BRFrame.cov_init 502338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 502338129 ≤ n) (h2 : n < 502517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
