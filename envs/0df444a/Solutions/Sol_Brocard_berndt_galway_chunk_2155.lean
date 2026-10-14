-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2155
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:48:42.696848+00:00
-- url     : https://prove2.me/submissions/cdbd01a8-7a05-45f4-83de-65f3b6ce0966

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 387410071 ≤ n < 387589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 387411321 1250 387410071 387410077
    0xc05070e0f0a0903020c060d0f0c0f050f0c011404050a17090105040b220f171207111f0201020901020c120a0f0602070503040306060e1302011b05011e09051002 70
    0x11a00d500780c900400c0c2c1040160344510350f40e61080c012110804008030100346290810345e100155140d60300e0388010104924003411751819034900d4010144240700e035001c1c01701e004070080901020400b140e0107901d90300940c4442c2d8054121040854103150916040d940e4440300441100c6024074030460040e600708480548000f440c1c141c480700d0510307040190103003480d080316084801000803404007110f40920806441d001d000c0d9050025144c0381003007140c4403520b08544c00c0a81951244a42000049a04080c0c445080d4410b0b1861400302c003800008110b21051049612240300e000310003e0090303015401007071500c0007178098862590104041286c0c9400020034a082c80d000145072800003001c02e280d94481900ca400010300300445500d03214650381064100b215225520042844450004442d540e0700444c607940000c1d82c005e1550000b400d482c0c1800050248030b51292540042041c05c0d08900e1841c00c1e01c0060360064441e501ca0301018101c4000240d800b80541c1c0c1586400107078900032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 387412571 1250 387411321 387411331
    0xf1c021b1b21100905030a1701031e020f040e07080d090e07030c05250309052418030124080f2a090709140d0312050604060e070c05070e 60
    0x401100016009a6154181e4111500a1032801140900f08044050f44078081280d80100c0003541c91742c0d16494090704418103440e800066842c481c0c01000011b090000340b1402c801100400d0581c80894404502c00000d000030740c030f901c14285080c0b08080e100000303074a0102c92103d4122114005d0036541500c40c0700060040c0c1506206250000c1c0f10540a03401c801d0300030103540781140c5840000030358100c0da82c034450620f000d25925801c100050540c44242c8002800003240c0c0300d4110500760403d402100518844e8482c62000818040085010456541d40c0300234081c000340300d1008441135100c0d030a085d06200e071040c41c903540300200d00100000340306200300c029403006114600e02003601d0b400d5a1030a100c00c0c0032540e90307107442c1c182c962244e1018501070b0981340c0301d150200e070901c080d4490080c04102818003400c0c0a81d00c0ca0082988050002501000c18000003040e0300e9000208020388020741004925801002c00e10020070752151071200440d0141080c0c0700b65907102e1034000000c603400e0358 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 387413821 1250 387412571 387412579
    0x180812090115180902010903140a060f1a010f02160e010305010e0f1e0a0204090b0708070e06040306020f130f1401020d090608190e0a1106030106050f1c021b1b 70
    0x2607000f40f050302544021401ca00504094000d2a540d83d250342609501e0040d01c02c103034110345003540801039180101c040d10400c0031410300400303403c3c0030521850a04802030504104210250b0a891802806642c05008840041040c450303111680602c1d119402e10086400350710304488003040c43c802007010241c41855102a00350940701641003000000c1803102e0240300e01030f545000005964038420218110f10510300100d480c54460b2000e440d4040052600c810b100804c03001c0c0c0406d513941c40c01c0750300f500c0e4001c900680750160801035080a0203003040350003d12400c1c240109001000c64880021210a010380d0710480b2801d4004a8640190031541008600c608405101d114040c010305a404070840012140391106000c014060710002046183c0c140c10000d482c0301805500d903074181d4484401d442c40e620310351420500034923511031550300705c0407040c0100d803101107800070403a001aa4402c0341015512141c404988070b8469061480200c014800c48603800070303252102c00202e6038064010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 387415071 1250 387413821 387413849
    0x309050f0108061009081c030509150a0213090c02031e0c0a060207020f030607031d06091c020313030b0105040f05070e0907030209031903030c02060f0703180812090115 74
    0x1000c1c0310b04800104051310602030340d43c03000324a13240c08100e0480303128504c0d0380590076880c0d028400b41c00c855019043d03c03480c5d0001084039180800040c2c500303070003070000c180069070389886150824a1100c00e4014080860901c42408500ba038000098003e4059002030f80e810308220005a9000c0d01c10902c01a400d80c00401c082c2012413580c0e4041c00040d400500000c01e0800c4810000742040000c80c1d1050120366560070a400800e1030007010b1220b0b80c1444020070702e6003450381c1607036035a0150592074030503402412070305800d003482807090340c100f410064421403c01d42c4a280c0b03000403034800d02039207000d03500d4488101080c1c01e032802200c4c0906a107444103003003600c00c48280901e540707005141c0024960208960007840d00e00300100342440072120b120b0700012405260050a55415030360a00840d4082c50a10829055810f07090750000698200014800e10584d0710302c00c0c2d840c1d10b000103030000e4008038403650062440c0c95200d1055151800800c602c049034500a58101746c0e0b40138904045040e9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 387416321 1250 387415071 387415081
    0x80601170c1219030918060f080a0201020a0b06010e030307120201050703022502150a02100b030102090a12030201140c0903010f0c0e040b0d0b1e01210f2303070309050f0108 76
    0xf0030f4802d080d180207181000034140c6a1903c20500e020b00b4904c0140710707a9640080059106d80c0d0200000361500c43e018115076110760700001c1d030b901480386001c0c200345600000704485a006080c00f0b030141c00098190307611407a150524440d9100c60414002c013550034140003038141031080c070803201340036a10101c622000c031490345038200c0c024100e00c003203801c11164520441039040e01d00203050b84490641c000d0243d00424204134040c0c81810a80c42c1c0030303a0060041c8101603079901d40c181c06480b8203400c24185400d940c1012400350500d41d204e414050801014001e60f960803100030442460123500a2204500c4880d101d0226054800b80a0001d50f02412542c454034154001070f03801e880052505070710000546420611074401c0e203140644448201d0070f03400070029440d800d401801001000c1007102c582d0014540c003071010355001400c0302400f499440401852941180d40321440c440b5103001d04100c00c260300e41c2d90340005400e40214000302e04c0040c10345402c004052481106940d43c00b2140c5071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 387417571 1250 387416321 387416353
    0x10e010b0a02100e100f0204030c0b0a03020906120403021606080105061b01050903120f060a171005090313090e0d030c090e0403051201050904030f0e0a080601170c12 73
    0x10800600314060f03d920050350110798007980c00580d40031005403031441d11860841c000c07101568400780405005000400104003404160421219490340599a0b81241d820840c028400d400300325520160209016842420411100b44070341e100e84c088460300444210048869280d501c17030303280050a07450050206080680160440b241000300708484000c00c41e0495007950812076200380d00398030114104500ca643c0210181d0040d07004541d80c13540b82004408203048040c5401614000594451184c110742e908120780240069121020445404c00303c041c107031a54054068844040884000030400c02e030303207104103104039140c400201159600c40b50190094210482c90307000340410b8020014500d156408000c3c03080d031203690751660b101c004c8001003400c0001030b0010350280294104000c0041d42107681c804102c0c1d503900309031184c4100d6600007014008a500144480e028078000006c1506001c00c51b03641c0c00b0400d02c01d980b03400007a2004c1c094400400003441c5219442a0345004010302 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 387418821 1250 387417571 387417577
    0x509040f020f0f0405010816050d08070605040f0b160f030b180a150909060606050c0a0605090f030d27080a03020a05130b0901080609060f0909011d0a0614010e010b 72
    0x50401104a0f900b00002400c8590990041815400841000007413009040c801030142504449030301c0407075000e84801e0700a000c8c46c507009203101da4810208060081c03401c4001169540001a03c84d00c5c40c04c20040c03005510000c400c4008030355400c03001842c150003401100705064025100d8005070001c0d901c640104603014100d21860303a82c2c0c1e6030007041c030300d280c0419038054160700902050320112031034503400301d41096000b1020000240302c42411400045007100c0019005400800d141c0c40d0040510b0400740c501042e6803592200282401c000740403a04450741d1540600c0080400d101c5003241e0b0002030288603c0108415420028440018083c1e0701901c02c4504910b03205003010b9075261603c6410b0703a2034012040b001004120b0000319a44807292a070304c10005e984095603420400003040c0502c07422003845200d000d200c4001056200b00754003141d0b1184403100310301d082035100700a858407003900b2002554510304105010381d50f00a83c8484a040319100c3c0003541c0700368648404002c00303070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 387420071 1250 387418821 387418849
    0x80c040f090501050403081006090e01060503090705040f06050915060405060a09050306040f061a150a120501120c062d18170d0306081023040b0403090509040f02 71
    0x1076540080c000807400034070400b41300e24800e450300300250920318030b0681140c25a41c030140c10041e5261050010b20200f0403110304503840c6050540c3c0326190708044900382442a0403880d001840e00c40c419070200c04942015080740c02c00d4039080311944510010811100700560713500e400c41c40802003001142441401880e072200546001c0c01155111400a810550180c40a84881c409203544000b40460f61140184600c901600480040301b1400482d441580f402c6004442e014080364021050f0b000700d040c01204e40c2c0c000010132544d0b841d5088003402190003441601c4100501c2340c003103003090050310703c20803101017055502c60402c1030942c0a5600000102c142081150619600c50740a405034696400b801c1c3d00042d1003600301c03200100f90b103424501e940a40c2050b0601d002040b90001c041004c004002200c040400d0340503041554240070442c40c1420b46403a11100204030a0088001d032290040d0310a60703c4d240d07100d0351007003000a510b4040d107010b03100590504e104001480c00b0074584060b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 387421321 1250 387420071 387420101
    0x5060f060412030f050c030c0a0b060d0210110f01060e101e050409140109050f0d090b0d05040c051306060e0f1e0a0b07051522060e030712020322080c04 67
    0x40f400440c0054210b0300000c51142d190703440a0311501c03c0001200084d83e03c000d0079505030704080d03080d40004400b1465101c03c0414880122030310544071070144500391070414090024031440353d9840e10340301c0d8010212084960038000f2240840e0320381c1c0030501314040a159881501141e81003100b004003d09810404452603d40051a0f000e982000c0c0a058100380c000c001600701d11034201e10035030030039000c0320148041040b0602c051001c0d183c080300f0b03128040d80741c0100203002d5807580fa0014607541d060700f11a074400484503041c031210003903411040a4444075540c1c00303584c1d464442401510301c10307002826400003d928900c100340c0030b481e070200001031f0014102c100141da0340c807075100c0c1e41d80004e40c00d46854000f1900701450f8036444e18259001340b0080d8810007080c0d451081819401d80e5048010242e42c1c07219441c05103060b00304141c0c0c441d03a400081c20000c400413405e019588c2d03405800e090700e0440e0b444a85010610910b16950300b00c610100c064200d0607404000c1000801d18104a0f1a503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 387422571 1250 387421321 387421327
    0xf030b060403021f080c0415110f01110301090c0905010903121e03090b09070308070b1308030a02071211031b0a0f0b07080906070c11010c021305060f060412030f05 72
    0x25984440c411601c0c113152030b03000008114181402025104003c0801d9070302c5200b00803c01c010519184413445a0b000d61805071f12010b0a150200e060511070f182c0d031045582030032030a04462108a00550403103803150000c100040300c0300000e0b126280540304242c0865031140d41000805d408102e4489141ca4514201c02c102003204107084568800e28048400690b40351700400400030a40c2ca0983c100054500521000c0d2556a03031074914840c055004003224000340c04149a0b010041440e441190702022081d142c2c90440c64050094100e40c006807084892034007900450350041b950b40c07030300c0c0e00c2c0d400185140029521001c180a00880304000c014800d0f40e10800c042003917109030503040c910444400946081c080001407003003401030078018998101c03c003802000c503000404200c080750300142c521140c1d6450743c010303582c1c01d1004001a4000b4034100c0210703664807580d4444c078443c00c0210b550000309000201804003074000c50240002c001340d00c00b24407000c64000c809591040005203031141c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 387423821 1250 387422571 387422573
    0x10311011701091d0604081b100222090504050c060307051b01020d05010b040b12060d05060a0c090803070b1f03230d0305060f0904031e0905030705100f030b060403 72
    0x2401c0c0c809910011a03941d0b0b0b50040e8842d00c1d200d02a112203540c680700289031905064543d5a4a403003130820705050303a42e03150030182e280f1006001611880340381c00400c64444100c100780c0c1c0e040c1d941c5420000d4035003102500108080e51030b0312440d13004940003c000c0c0388580030403050040650000e004941446004e102e0202c00350420030302e200e41c0d0f002e4070f0005038070740601e07d03280d00039940306804c40198580f0a0209105650000c000d54021180428110b0070303a03201c0b4004554500d0140340302030298080c0c0360800201d00496004040600d505644d845061951000b915889000303880004014000110103d0f000c0c200401e401440a12040e50f5048942d40d2070380d520f141c00150815282c442180307086203040e00c850a11503204414a541800c0c005807402c040080d954072038010780305200d10143c1d008142414410941552408514002c01e0721711006400e0140c100c5c500b51150720700c04d03c00c50502060a00f80012111040c80050f00e81051481d0702c000e0030f4003c0e28a6089071034010105100c000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 387425071 1250 387423821 387423857
    0x60f0418081306080c0d0b0609041107121d0f04180f170406050403030f12060b0408070902070503073e0108070f1b0602040b190f0c0b01031101 63
    0x100d4161149080d01d82e607001840112016071120340c014002d01c500364040000c6202080121a04d0b8160700c07030005130781d1030300e41d0000344140100039155420034541100b0b00200c0c0e540ca8000c01c181e0b03000750009206198000300c00c4031030426603502c4d140411000c110300d0a031403c04841c0940c4960b0001c10100300c1c0d603e5003209541882c0310350000c1c4e815034010340100042c00036aa1b0141c0c01d00031050000391500d4102000076104d071049110050030840c4102c041a0342c1d91040c40044210305800d00d0602003965038403403d00e256041402616814001c1940c0003d581ea480c4c400c0322585a4401c0c055410922291502e00d00d1004440600441d0320240a6030581003007040d01550740140311625004500c1801d200050403080003e0054090148a44404e80d019410444101490024030b1044030b4855541c074159029000c4c80c0e0042c40c083c2d401281d541c11010011600000390000da684036100856218011540b0008040703000d0320390b9064000600200b440c010203104614410f0400d42c0032688548048 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 387426321 1250 387425071 387425111
    0x30f1e091e0b04021903020906060c011d16060201200c1e1b010806010819090213020415080f2202030d02070810021c0507020a0203030a12050604050c03060f04 70
    0x201d5044a00b00100011403400d8007000d1754804d5410340003940b050840d40401c8215070081d000c00e00c80c880201d4071100301035007500100348031205820116003940040c10b03130a5443d000003a030501002c1c01c00c1804078004d44140b02e118540706840f0580a00880d030b80303100700c1069110f20342640d8580607807800250f89414031610150800c0345400201820f000100658104001d02500c40341008920824130200c0e81c2d101c0f0101d0341000ca1260785119a05402d030035000103101641d0700a412518001001c50420392a90180c801c036030100354071030245003c0580886074010211000f589102181c004283c00410b041090a0781c1200e60300d5040300b413a000d8000030324141704508500c00580c02460b081c070200e03009005102403290f8640d425828001022440044040c20200c1c030010300f81d981001071a445d00c20003410540c2c07a00078058030303920107038004000d10070340100412045290501002c1070040c102032003000c0c4035031240e03400e1504644541041100d587c40034088264807a8980d102e0111400c030007402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 387427571 1250 387426321 387426323
    0x3030a0218100809010c1706280914010609060c0b0402060f0f1314011b08040906030515100b04050d060902060a020102090108090705183103030f1e091e 67
    0x541c0c0343e58076094030110700392051b81420781e003080404a003205100d0350024003107800c00c81c100c0b060031401c5404a83c24143c50901c0148000c070300c03620790707000582d4070190340160745131007581c00d01040c0740c4e072101d10a032002c0905100c0e850011b24182460000303e0301c01c0d8541504070f4401002c00e40742900c0c688032959950085080c4d030056090000d4000702c5030308026504401045034401c04402c560b803046c000381022640c42c0d0703007454004562644500f00051607045802510000000b0071002e91241009640c400c000c0ca01801d4032018400403600c1080300b0038052044505140505182c00d0820061002442d5071100803540c00b034031a40c00c03200690340c036405058400002c1d400142ca83d004100010b11401c40500000b1b89a040030078184800e03203c0e202c81d00e00002403001103507042c3d111800f40f503242c00080314001000074854140706600b0b8000c0c00c0e00c10310540c060307642030107803400039034100707045910600c0b00d0301c503041d001144034140883d82d4100149890040e11049005003c0d00da41c24490110588 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 387428821 1250 387427571 387427577
    0xc030311070606050414070914010201090503030a060501091e092a020c1503060a09020702060f0c010b0a0e0f06120328080f0415021309091a090f03030a021810 70
    0x401030200d41054811070a080f031840b1b0300401c041c00c01e000d0140c0303000c0c0d443c000d01111071101076070301c20541d00035000682659840412030b9924900110b982000388054022031b4001092490b00140390602e0510008141d1a000d281c4482c0707a10b07102803003001746544003c100d003190160100b41104200c1380600f894090050b00500021802c240c10011070300018554101070060600601c16240c8075003007041c055681824005076283d00d1400014090700404400d4205035000080c0e034040300750b06400c00c1401500a4481300c0400d43c48603407201f107074001201e020340d21050040c002195450450711942002c1ca540d82907900c0c00b41070b15181003410303c120b42e111011202017001d403c9020703030241440360700c07044001c000d542c281099520264a40e0076400350706141d64020511050030081c90342c0c100000c10141b04200946651031500c3c6558440f840c80c04104040010009040c0070750115003580085012805180740d5039501c0201c0700203402040108210310b00603116540151071705400c20f00d56561540b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 387430071 1250 387428821 387428831
    0x51501030302010b0a0317030a140c0702010e010804110108061504080c0907031404300809060603010510171e100c03090803061c0605011e05090603030403030c0303110706 75
    0x800c010382503404c41c5072014000d08501d94200040303203840e1030000c00320022280c1c4a503a41c0b55410760340050103c1e40c10301004c0e0020078090140c0034003001c0c02032095074401e0300c801241501e80c10041d1040c2c40d00b2140941030031003a40746032403558030480340079501540c01030030320f210030300003c4620305550440d80002d075069020f503201c3c8000b850200c0e06035510007840d18041c044c1205400410707081910240006050b050744000c3d0300c0311040b0782e500310740040300015841004001d084100610381102641d1840560107080c011600a09060207018408d0642e0242540c06d50b240c448007280014114044100d18058115a0122141d01950881080585000174250945102c3c0410200c460001c2108107040c03922034000f00240d480d00c01c5e250b01000490b05d0b41f00f0a4080303040164694507003200209602d19000001c0750341120312132001c1e0041c003c0184420102d0300c5000780104901c0903146e00742c0c583c1c002c3c402000064440e40c891030800b8402d11300494601040000040c0c03a400003141152166150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 387431321 1250 387430071 387430073
    0x5010507030c02060c03100b0d0b19062003090f1f080403080108060f0114010c050106062615040209030a0b0c0405011d0f011d1804061503170304060905150103 70
    0x4020040d0030141100e045881c0d0300b40240509060310391423142005104021801c0460321440364490b02050b807000d024410400756480360250000c5503030080d40c0c0401c401c0c84100110042201410030207040d89002140351401c500200310080d040325281d01e030302807110b42c10390702e040303104a03640010f4103400d86822002d8101841c0c050301c0000140c0062000c3c2c0c2c842c0701081948a10200f03014115030140ea4001006217032040121001c1c811000c004d8520f60904100044107980702c05130150800d854100c41c40c01d26030398054443e4100d41521441c0718814880c8d007094140c40c10b6402000a9100101158866400d998a0f4070814800700c41c81c3e2140d18000c1030400240d41c0028400004940c030801c0c0080e02d041d00800505103101c5508410304116811411403201140c801d441c05803680010007290300b40d20f00c1c0d01c0d0840c003030904503811907903181440100f41c2240801d2200030142c1354441385810030340850b00310a00c09a00020b006480a644680700800829020300003812041d49200b02c0d1100756041d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 387432571 1250 387431321 387431323
    0x408060601080c040e040305040b2206020c0105040b030a0e07090501080d0905030d0c0c08070b04050a0b090d14160603051021140102040f06090810020315060a0c05010507030c02 78
    0x2001203050100034820016031043c003100325400c1e03507a000280555526282000c541c5030085410040c0c4021000550034604055590011032902c40d60844400890310342800b00d8540b0310340080319000c111300707001c03d00a03030b8808030145130b201d94480307000601a40b10083c000d00c3c001181d4000095169501f0051203111002e201031038503a036035800c1c010821440c3c040480c0d940d21548042c00b04104a0710341e070600704088580800003c0c81c0707801c12a9905031b02e8000072038050740f00f4450703a4840c6000950000b91105d035a070540d842024000c043c14030981b0140c646400310703890340716220001e00451160b8440200300d0400e03603014001e10f81c3c000400703160803008039a2011080c0c0042840082c42c4a84207031800020310440006540107400010140c00e4220707540c00390060f5000b040703407983c4c080004251194002d075480121111760302110340995108546901300d10090b00c002e60341c40c040c444010b4a07070400781c2c01080c0d00c3e891854280030968880e1207041c05c450041d22100c000070703203a413402c50803140c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 387433821 1250 387432571 387432583
    0xe0111070501060e24150307030c090503150f04050109020a060c02120718150905011212090605030a0905030c1e010c0e06090103270b1b0c28170408 65
    0x21018541074505003060340d4100d008111441e003000d00c01551885905e070304c50b00440c3c5c8440e40322141d05512414081009805001d4191010303001070070700b41c0000b40d503280002e02c031300c80e03440c0164000380b05850b18080b0b203940600c0144290380c9992242d0b44400140c560303880c10360007080150707a02d8003100143d00c100322100500d00304144140c1d00005091000b0564240b5030344002041040000381d0b02c50340d80d0b0074090f0760303c40e90100079250300d00340001481407180c0d50349400715441010300d01542c000e0b50b00240d8849003507000ba2030008905000080c006180c84c0e0002c20110b0280c000c482c1013642c1c04003414a0402000c1b5100260464428102c018490034016011034464a0400e80b020820100c04038121b402004402810151103140c002500e650f0150480741d070750005075160042956030700307022072080310a6810780e0100d4481c2900e83c2000050b0000c0e02c04100000011b000e0710541c86942c4007034450300001803a0000e512a0b84800010f404015030106000001c0b041500c0b686040710b81c9040803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 387435071 1250 387433821 387433829
    0xa140c0a080d140a09170c0114040609030f0c030803091e030403020102250b160201020c09090c120309190302040f02030606040b07030203040e0403050306090702030f0a080a0e011107050106 83
    0x151010810710b66154004200d1030f14410504071490b11060f8403c011100c5181950081800d64404440008414408140b00306803000c01e1300c40b6140b4106000a418441c4503c2c4a803600007000000288001410328943ca54940d01801d5140c0d069a00e0381ca56100c240d0080c0c0c2c11200c0395001c0c00064040d0b07601c0707903210410300042001071400d180c55030300040e441d60740d4098240000c50342c2d101542c60700c5504018007030142900301c05894440c2031030103049000203d1210240d016108043d4030100916096190714400c80700d5030007501c4060303d00410b12802d41c41e03412440c12280018010800d458440c101110300c6c03100000031001206195006200c01c0707908107c5120a20303801001004115200c88007282c0032a92040d00b9680d0341e6407141800c03402d50149401c40780a401500d402c0c801410381c00800b450299408a48091803a2184003081e41e40f8070908034655070b8510140328070310030a800703400050b501c0243c0460200348042810400c13400c68150004061401c0008100b400521000f4410400a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 387436321 1250 387435071 387435073
    0xe3c0403080c041a030901090c06050d050a020a0903060207050f190b0108030307050301060c080705010203130203010e070612090c0b0310030c0806090705040b04020706050907170c0a050108090a140c0a08 89
    0x14101808040e80303c61401003064441c000101081b9100000d40c010000c00b900908016103554555900411550204850205076410200410b203007021901c00c0300c0807003981d910b4039001e1a01e9907075000081e4000131816200d41c000c50140c0900d403070003488059400740401901201c25401032070801124103060700b001d030042c0c0c410320400607002c0d04441240d040d40d55030709000769520814504501c940c031841038000d0082d4000b109005080100e4100004060b208800030b100383d00c0f9034981240d451a542c491000020089a0200c0c0d0303444041d0310680f04240102c801c0c0c0f0b00c0319144d20000d4500d03401962561201800c0410070010301000403850400342081c1c901400d1107040c08045981d542c60540109445646d490060314034641c3c855044403001540031500f40100d103411080d031600c4e00c0240c41103155640c0e656070300e05980d40010034905c80e03468009120b04600341c01c11004450482006080807118800d00c001c0c00003041e2030805814100700014001d100005810040c44525900c9920075902 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 387437571 1250 387436321 387436327
    0x3060102190b060904020a1503021b0606010c02091b070f020f0d030e15040801050412020c10051204030207051804110a0e04061505040e060a0c090e3c0403080c 70
    0x2d16440b9805800810440303140c8036a8866000144a0a40d250300c400c942001c5c41007401c420076003540140c10380c107552031a20003903e840f07003042c5611424220354403400990319032003c400501c1c0840a0f1600071410800c091594246412114030316809143c0642c0d00c002201e0401045213880d10004420480684003400e007840346540c0900025590000d9a00c01c0284508644101c402c03481a140146903000013072041d4141410418101000517255500500071884031818601303143c030780d80222003031680e103032441d08044070f003c9401d0310000b0b44110110b000342080054156500d1005035000095015104458141480c040000c00203101449005161102c4104a45115001c8280e400f9402007008540601c1e2510942d5524805800041d8003a01d045011028403100146891080464030740c1040558090001561082058421070b01d9070f00c000b00c00160f8480110445400d00d10000521403401050b8104c1c20f200d01039150000000c12070984200000e266000f11119004000078425502e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 387438821 1250 387437571 387437573
    0x30d0e0124051e1f0c15060b1b0f120d051003030f03091115040303111606051608040b0a0f1d01030c02030c0d0503090d0f020a020915040603080306010219 68
    0x4043c26000481c0111440b420784400303580366140180309000d4520f501c0403004010b201d000e018070304800c100340d6844003050800312200700c0030b1007008242ca06101c416401c00d58201c8100800008013105080d4600a020200c0413014040060b2a010b080c92200d20341c0300c1c1003244d98002220001424034005800c000c20800119402c2240ba030955035140c079011840c0002c80c14030b0b103020100ba844464200440807160300d1080414400380c8141c9100c4d0741c840c20342c8841c00009070381d5894055081c140d0100b14140c108000ca00171002070414040364034058244640c06c1c0ca450005801aa10815095100081340260784c1d92155410100103a07500703000c088040d0000c0c0386003102010803651410b155a400c010b04000303008000761011906880102c3e07410b640d1082c8001d085400c103030b450750303a50b2241148420285001e86a00d1a95840c00d60003010303040103a408000070f003c800750803c001d6241e501410074160b1034602840300a1401100037584d42d0900c007000a1030590a160100d080301f519480501c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 387440071 1250 387438821 387438829
    0x501080d1701060c050c03120d0b030c0603010b0a02070902030109021209152d0a09060509030f030406050c0d0207140d05040506040306110c0f1c0f080f09030d0e012405 74
    0x42d0540d401d6250552404015181403850980d12400d02039044c81001140418100001b000b004601d0408005001a540070010302d03640300750889100e94846014001803010348442c00241075140068811200543e40e0303215404104c2c2e000380c00c60301d94185c00141914929845c0c201168000e41010010a03484048640000a079040901049007410070181c0f03411404071580031040c0c2100410b002e6809908065070208000c01550704112103a83c1043d00040842c1070210640c0c0c036003d9502926031842c0c0e01d0750f89000081600500040d40b180050000c0c0641407454806040d50611688052a0340c11041002600d451100d0340f9000400504000c00c0c422500c03400107941c02c40b80c2c40000030805810610b52028240507440e8049007521600070300f0070710400002114180c502012600302400c005100044845c040c4940d45113010500d000042031082030084c070055848a8050150783c14200450000000e6030b0100450294a0791101c1110b80080346070322591450442c0b58411021700c0b8a814089 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 387441321 1250 387440071 387440117
    0x31203071e030e010f050a0f0902180615030108100b060c030706090f0f080301061103180904141c09090603020315040c0e0420010206040b010b0702030313090501080d 73
    0x110a281c890201c8407104140250440018048040020f01101c14404520001800120f468518070ba0900149401c00c04d071f6131081c44581a0050550031030f104007805018110301b0042c09617a004402c0d080e032008143e40c0c14020b14081c01d14500078080028900b80700006842d0700e440b000303220b0b00e020006200c001800104440d05154040b0300481c90540314280b000c2c8058401c00301402e4112404180803c004c01d0380001c5050300c260b902c4101c41018a11040b5540c0c0c01034000380204850440b518152518000c420160b0051252040c10a8400c2c40c03481141800c404513400c008030003c2102143c546500b12074a0000391500da40100491440d5400103590b501c40300c210708080c51174980c04039007800f00440000000d000c1c0d90301803030041d0900d4a03210300c1c0c0a91000c00d14044920340d4410740301c6980301148840c051500115811401e0b400d02c2e8000c205513104600403a81440b0401621103d410011281001008030003000500c56260041c030314141540981040100015807541c03c04c42c140c050b82c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 387442571 1250 387441321 387441347
    0x30406091a390d061805010b03060f040905010f05060f010c1208071107120308180606010e03031209011a010f171e10050a0503011a0f0d020901030c0503120307 70
    0x1a84500041600b01c00c41282219554054081d01c00603229101d8400b6801040c1114460001d02024164040070241140c50a01944058800401c0415800c0c90012602001300350010400941e05000e0764403182120000d40242c461280c036402000101c0c40c00c008011100c8000b820304109044080c0d44001010340c010516105001e100f40c0441c85075131040f10300c1407800e10b10000f22a44161911035640c0c2c0310540c408100c000130385e039070000f462008200b04500416040c542c000c0060351504401503848600024509070944024050346c0031208409500500a0311004000901000e0858030b1000d88000b50f51030f0743c1441074a841128446910040741d4179400a80b84007903c40c2e8583c0e074404040b8000310030341d440380b04141c0c02c18080c0e40c01e10660030004481003210041902652a01030509035416000380000d00d442c0d41d088100c0d5404c10f20041c400082c0010b0216000f003030030b640010b50080b420f81041c9d1b40d4080c882828013184c24100a0042d501c06070309003060851605c02401444900d000c11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 387443821 1250 387442571 387442621
    0x40b16020a230d0c1704080c010c030201021608040e07030902060301090b0105040b070302010c0207081c08150a12050c040911010c03030f1b090905010303140f0906030406091a 77
    0x2001c1d451850b03003844000891100c10340e030318800d9424000340407440915017680d00718901048819603080d1341c02100c00719a1444c02402a400300080103540c0b00d24880029005d65401f000303c5100003140107003d01c030407881000e842d0345540c240f50100c510b82600600990034180782c0a01200036039281c0e41941c0c111025900041011451000104c40d140603d9025541091020400c1010103170190402c0ca20141550b0032038850783d640f03150280d07842c3e000300c42c81a040c09140701c1c4601424070820641e1f5101c001e14400d100340241000c0403030320696455001d100780c007916200301420000300388401404110201c800340031051a82c2c43c1d00900b2843e07841442d06020500c2c075000105802600b205600705440103040243c1e0b2100e074414100213080c903c406001944d14035001c14240c40078810f031416690503684022084aa2030700c01501540025441410010b05124402e000d682d40070080d48150b100e030001103004240307031512105251702180d0344101204044204000714025050308058110044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 387445071 1250 387443821 387443843
    0x906060f0304030c080d0905010506090c040b130305150105100320031302030607020d0e01031e0b1201020a0e0a080c090a050705090301060b0c0601081f0903030b0603040b040b16020a 80
    0x468261350f00d20a2080003401d8240101e0341650070040c039404030418a000340000e002c10b075100c50030440611412100c002d8410f00900c01400a030382d420020f81074070401d581726a05119120789440d80750182420b0001e1020403c04014006800c00c02c07180100304840c1c0c1024071044090082c1d0140002c81c0ea402001000b90210010701c1b84822a042e81950940190984000b81441a4000e40f95422900080c010443c0401c4080032035101e03101c1c030a407013540742941e4415644142c8198010b8141031000030381c0454424040084103000303200500084a00e41c54440d024a14401400325249803076021820079001140b0528040d2039203110035030700154010001803940d48003001518640540d80400307403d9882c0241c0801c90010242c010015980c1c0c41c401c942c1c90340e81e50040650303511034031080180070164240d41c1c41407075203a98000301d003001d100341030210302c41c04290041b541540040300e050350690070b81814407091010320070303103e50400c00498041c00e0a5420000c040e40d280d840000040c0a40004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 387446321 1250 387445071 387445073
    0x50603180d020d090302130f020c07090b190e0c090909030a0801090209090406050c04091d0606120a0b090307140d110601260309060403081c060f151e110c0906060f0304 74
    0x554000c0312340e0b000c06081192600900c8032003039034442d51030059000844c54002520424541038401715076a10200c242030419034107000c01d0003110540608042031591040c44140710643d181280584544003640082d511076031240402090260180e000e0001e4910402041c90f0a460b003a451581c0183c0114000c01d05498124440c0098452a40404101e601d0201030b007920094030f50000c03840079001c5080385d8aa0b10380c58200f06c41c4160141c844541580b02610000004152990840c3e0140c600da0640341020442c0d11902040450040c0c240c00c5c0c1c0c2c0041a0205090b038100025111603042203008001543c1080481e0b1045500300102050742e028100000040002c01c000311641a44003074501501d503030382c0c0e103000002038112400d5180c1a49802d40c000164500034030900c812101121241d609003440d2000400561140c60303c00000c22900c00700803d18100c10f01007880851f00550780c0d80c0d2800c55881d02e0f41c0d05201400071082d11500150090050681d2000240d81c0031460741828079940c0e8a0b0317 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 387447571 1250 387446321 387446359
    0x30406050112080a031d0f0a06060b0c1c110d0f020d110721140d09080a0c06030e01090c032105040e010902090319110a0803030f07110106050603180d020d090302 71
    0x240248100d200d6002d41c0c10100b4400304108c0c503010710581c4c06100c00794881c03650b50811300078101e20b0b82255005200f09020881481621052205a0308109080398040c541c480d080503440004130b40403e201c440c00e038600941c1007005c4030121009143c401c40b0a0b060640d07090703c0d0101442040314043d055074a45904203c3c010510000c2ca910041c442031046046014a8440c4204090300011482c110070004030041c01250000c25031754014500c214090911206030020a40e07804014071075076881e181000003c070181a610043d60007211844088440c00003c25841c0c2040740b4003108002d0b05204c10048444000a554195543c18001685a80510020034a40302009020341005406a07014000340702c100d80140e24282c00944003003407096110440d40c0d80c1da06c02a0340708180c0071117980c005200c071031065000800015400c5c0c004500b0b03a5840c1c0001b00103070000c0ea60740040c940301c01840c01c03d103e0104240c01e08000311b40003170045802d42c94405459032001d8032020340038000b82c8000c6c44120341c2c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 387448821 1250 387447571 387447611
    0x30215041d090d0f05030a050a0b0612010504050c180d030309171c0c05122206020d0501050108093706150b03010f090e0a0501050705030406050112080a03 68
    0x340c140e030300c40700301c0100440040481005803540c10050060790100c0b50100c3c41041c83d03501da041c10351100391442d25541c18903001400010b00d1014010303038071030740c0e009103a07641e200415601c0100f01100c3c2403035041100308000c45138090b000002a810800020808411010034003403c00000c445515900180341800c1e00030300300840004000f2114401d07400d9a030300152028001280000c1c1c0d00e9011159550002c2c000c51301a20040404120184041014900d0546810ba4451415020039503401070001c09542e14000140c012914035801184101d03041c01d0314402c441c0100000d203002819420000144e94440c103083c0c00c2c8030f491040d0040e0303480034580c002c9669418203000c06008000034003141401401403002064003084a12100000074264010b4001d41e03069840441c0100b402520300700c0c900008044006101120340144003920010590030310440344a01403645600341e0300cbca89450100122441600580384089016403a02c0201e0b0217a01516980c14050400003444c8000c010031029100c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 387450071 1250 387448821 387448829
    0x20409080705031209060708101e0f081b0904030804140c0a030b01030303140705030c0c0a02060f0919030302100c1b050706030b010c0203030706230a020414060703080103021504 78
    0x11100044142d00c055104da40d83c0d03c518020300c2503c0d059220220119240308040d55030140d41c0c8040c0005020201790101031003000781c3c1d102c101c11030003a07490b808140c1d012125485039041d60805985161500d01191008814250440c3d4510f2a464a5940580000d07400b520161941d800d50442503224042001000d4080e44010310280f0b0050b60b030b00d41400400e00c00d00040700080c3c02e000e00300104c25500862140202081d880e12421135490351031444042e0020100c5035118842c1a14000140e1510002032024041e110501036032584075809008003800458108141c4501c5202c04101103035010642001b03603021900d010a02c480403c40840b040441100d0b03180303990b00c584105400b00000010084200c440b152000e000410a4400644010a8004c0f0181d01034008012080004000307521105120185200c1051242071240c859032000c0002c40e80494699400103043c433140034040300c51124004115000761500c034140c0e800400013801031200038000c0e088030307803030300c0840008105443c064 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 387451321 1250 387450071 387450073
    0x1211030907120206034210020607020a08161b060315080c0114070203100903030f2703021e03180d080d0b0f040207061d07050901140409020a0306090b0121020409080705 74
    0x1509030901ca06e601c410f8040c00740c442d03c2e079000403025550011440c81d11840e030a8010b0300e055620303920742c84200d6018610901d444140a0901400100780742c80c800c0110008c0c0020011107400c103500078084440322405080c9401c1040d80170024403000081c51a0f83c1c00c02841d0503003078031440300c0c202a024014010000c1d89030040740c07800141d0305005c2e8002500c240c0a070750140f0805a034462813004070380345840c4000c00b42980c4002c2d2502058034101d40d007001442031045480c9003051145074017a074102010514009d420000d00c002003040c4200d114400d690302141d0f0759810041e2030f03880241501c2303a001c0440c9015201c103046085662030b07011440c140f48014000b59070741e640510f4005d000700609605404101080e441c0b200039400700046c684c00380d07080a0300107402c6034208002c500b407019900401d0b03944240c4400301e600040c2c46900c0044000c52141d00b000ca680c400390f24103508060b030144c1003e14904065084100c40910450004100a405440c002024000d0307007030960380f034443d807a406055 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 387452571 1250 387451321 387451411
    0x30c0409020c190b1b0c070b03090a0f0c1e0e01170c0a06051e030103030c0807050c03150f07030b010516020f04020c030c120a020304031101121103090712020603 71
    0x3405800c2e408244608440c0443d480c2444264900c1d8081e0300403450304500c580d03c021400d08c003913107040c8000e40c0c01480150490b403288255584224205043c00e81c11100d0185005081080b5145241c00c0030b40021008010060181003840030041c0c410148070340580940c6003d040d001c14441402904d00c507800c05800342e60111b032240d2002d0403541c04090300d8a86000d6807a003100d420201c100070759051b40d0381a541c07a15101d226485840c1c254118000030380b000c1c000c1d0407000415690801280644840c000f0303a185c09450810360400808074000e12420034941026400c400c1d5a0707101c001c540c141c1003980000f8148100d64000b2800080c1a02c4206400500c00a04192400c5000000c1c121604803442241e5001640010088190103111035100159205001c103100094540b0400200300d1418500340e0b542e0281e649911050b41c405030300d00c3c030f40280000300380010810240a01d8014001032061400c000e9401d60206583d84402404003e034a46040b08445009401100d11004440c0d480d00e1103003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 387453821 1250 387452571 387452573
    0x309071d0108060f27010524030307061e0515040608010e15090f01110d06060c0309230607060911030a0f170c070801020406030605010c1104110c0d0201050615030c0409020c19 77
    0x30082005488100510078030607001407019040b08c02e0210404800b801440c10000306555000c017414400b509030029803130b113026000018600d80308180c40351b030041100501040b0900c0c180800c80302190051620359051421844142100141c500c1d0711800010340091151345480946003804d0300c1001980c42942008403984c01414504081c2c428465045c008200003569282c041d5048404220000c0100704400020400b50300d141e15440301c01c040f5113160610182c40d00001503d40d902c0200c0403a041075642c20b1080c01d020480b15000341d203602c143c00a080340c000a0700d600c4080880d08000501803540040d1558108120700c081e40d441c40310314412100740c00d45620003103000c1e4116000d0000040d00d031031f600195070b40c0315804580308141c0040d6008031003032021050001901801e0000c5151020400000c6139100081100d9040b158155000084500300903042084414000303ca044a8036000c0c401c1c0040c1c249940c00725000c40711840301c010307990300114142c00d081c18101080e40001440390480c1d00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 387455071 1250 387453821 387453823
    0x1e0a080a0807021315060f05070b010b0c01050f012102040e030309070311010c020f190b191d0906100e030d050a0f020f0304050d0f080309071d0108060f27 68
    0x1240b12407088400048601a1904da40c0071184090030f10031490114640400155008400511400006240091404005860340d48000e003081e885103210080002d001d1029041c01c9c4507a940114160661092952505540700725210341c00d40d100e050300340d103000b81c0800c5654961080118808800699447e0b01d0600301041d25208940310641c3c119900c42007207501076105003004035210390f00400310552107503800f0611103904e580002c1c085280c41d01c00e501060340c0004001601110701c0309030003043c0005440a004110f1094845103802820505e0207240c116a201c0c10f6895004100303461815003045516030480380c04012503101c40c0c160180a0380701002030b600400030485812191100300364610341d503e0481c0d80d20709810124000750410300040c03241d071510003000302489000f149100078440302901c41649a9006440b0070301341394080d15080017203072010018814000111040101650b1501d545151102d8006020b08d10413003081000640c050700c0105070b4000200c840c0402d50280007011429 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 387456321 1250 387455071 387455077
    0x4090c0f020d0305040c230409060c091409010e06011214040c060806010c1101090305010f0f060e040b070e040221090640051b0a0b0301051e0a080a08 66
    0x3120041c002c01428101d210b00a00070326000303a078031042500416181101da00d4842006442c191500280c1944110107a520b501581c8503003801502d0010340081c3d1440060304440716a0305c28140c8400101c90b00c08240d81d01407100341140d24044100540c4d9076850700407540441d48801d444040c0d407414107841408441d00c15000d20452103480b241c81010f466050660b180c0104071907580c00901e110305600300003042000f0785a08080c041c10079840503505c07941d80d603095940000d410070100c2e543e96800b446010450107064020000f60b1284404d900301925907128150006012400f48007420300f07120016150b41d41111039104064503c2c2d9a2205503180c400462002920340720540e00c40d010104904942c082c50071210368602d070f08900c03940c4084104c05140e54103401116a203000b000b6070140c0204400340040340c0c40b0b41d6101c0c403e82034440c1c40300410142002941104110310340620040c02030f0385400c5942415080c40e40078504031202da200c00241081e031580c0007402c41d80509114602004040009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 387457571 1250 387456321 387456347
    0x50408070506032202011818060b0906040303050c12070b0a0b040b010531032a051008130203030c010204051f0c0f05010e011a100f0206011a04090c 65
    0x10346004655820070410140820741c0d4124400c140100060050b42c0100000b11410b481130414540b14441c445450544401d1a40580c0354058040d85500711148980700d030101038086a41403905210b44a808986e041c01a40401401d0040024050184420030030160032083c118050007a9200898607000c0401e0005480b800d00301420101d190034a840d0074081c81b0005a01070b507031a802c3c0b545484903509641c010724164940d020181c0c040d4102001d0708641c55000d58018000c000036021003d0200340d00d0722118040c03121026903c0320521241d07a5404c1c0d0f120035000b0074986110b4980b2140381a0302a8403180c14025854480001e20942041043d0054001c8a000b00c4001c800317601d1440203580c00c500355103003410014401c0c881d100000345041d2401d20105000d1000010481d941c0f10f550303400c40b540c040c004800c0c121b858901c0c81031450074600c5603c03408e40c0c03490a912080800b84c030281d666001030058820041c03a4482c60884511084165070040908607c14840c2c02d031a050040d004100e0b0100c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 387458821 1250 387457571 387457573
    0x70b070c08010f1d1b0609040902030d020a02030f03040f23040c1d09040f1e060e1b04022b0b06160606120803150f03010e07090c021504020f060f030106050408 70
    0x10704003040750000320f105c0d805100e058019030103640c0300d00708110640d400541c000e40d110350794010303840158a08000710700801180346c004108004550040600e01640a08164001d40c4100010b00c0520030131410401290b02869030068141f801070f00d25440203d54506564200380f402010104a50b40508045000c4541d095410030380020712051104800d130803100581405040c4083c03e0004914080440d42c440103201502080080d41d035a02054131040d00d1030500660007a00485132000700603541e6108000d04132021840c01c2031110041001401e400c4070f2440c0d8001a8207500d04003146500907000f00903000780007030b640d686406003411600540400544075145412004540c94010520000d59950081c041a00355581c0c03514803071030b03040103d480c550007a0040356041100d4600b400b440507840c00d0080504103090030404c9201c1242d01481c40c50b01103600c00c1805a00c40035120000641050301928214060844400070036014401c41540d04480a40040000f9034942d002e030180003a222080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 387460071 1250 387458821 387458861
    0x5070912051506010f0c0206130e0f011d0403020a06051f08030c0f070f0b0a03180809030d0e010c03080c130e100f05060409020c010e120a030f0e070b070c08010f 71
    0x1c0044882210b258215808520004c0c0c404025150923000303090410b9220108442e001d4031030b52120f500c00c4042da00850591490700040c41032812041c0880e15814030007800d4480d030f14164030000c1d41d50b0484c00e0054007440d5514045541041010301c1e51200c01240c0c9051184e03155103200881d500e034410b4185030140e02929140a80300807011a04008848149800001550400d841260554003281010b41417594944031204109040b090b1040858000c5c01000d4039880300c0000d00d410003850215034410000035645000d1507070303007006d2009040c0d0780502d0a844c49513241c0b010707440184518132083e054000081d00026801c2500c0c24107601c507500d807141c10b42006503990007581ca00e031068090b03164802c0c010300050000721500d502038010f0790070300c000219044424004c10390420070444442c00344d209000400040c0c2036058040d0b0042c107400c89000f0000c40707a0b98610030703464000e1402080200440015075400703000322035803148050002d50000700101401c070380342403005120250002d8000c0c01d480d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 387461321 1250 387460071 387460081
    0x180705070b100b07171c0903020607090f06030f0b0d050d0f08092a10081e06060904020a02101a0405150901050f03010f11070611030103080706050709120515 69
    0x103000011074a20109840c180013507541d40c4160382105080300e6000c40c00c140b08a84442c00b0708420410781102c511340018102e90700d41002030030408002d0200040c410202d00401800600e8409a01118410f180019020202103840c001610b07840280c9903101a40342108002d010303000c0340c0100e0908803922030903d00520141d056520304030480d90041030350002d20521701a8089801c002b030f5a4502e240d05503c00b031500e000040d050003d41e40b1174100181e01c007000c0002100f07865080500c51025410000f8141c684580004c001344205040c03240100e401180d2600b045d03000300114101d400c00c0420900c980028030700407075446000341162078492410013011070541030a440020b540508007510791109a800c210034801003c4003904240d03015035903004007080d601010f00c03c1c054038204d11a40b142c1d03111918200041565a1081028020f100820040000440380c4c070444a440b03900110114490b541e600d0240d0780f049241e0301c030100401021640b0010404040303034040722080500800907a035114 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 387462571 1250 387461321 387461341
    0x50f060f0907050d140609101a360106020307020f0607030f0f0203040f0b040302031605060304290132010c031d060a020307050601090c08040b06180705070b 69
    0x15609002590050303101446103041407200c5610850060781d90301c0030791701c0440c4054034005040b00c500e000c82d0400529000c010606004c0d0504520f8149924807811080300c00082c20390f4401503a041418140000c1c0a030321460011030b07010303040f41f004240f078030541e0f641d00069125844050708030b01c1120841034078002898400256070703249805071344500040044d19000e841040c0e00084560651006010000700d04940903407030405011000305440d02c461039841810f01d08542c1490281d10341808074014041d40c5c82b07c80c02d49a001d43c001402096558004015180d229614801c0c02804540540085040d4400b5489019401446820340800794000c5001c3c0c00c0f4002603004450000b0811041c14011a1141000100030465800407044240114000a080c1c1d4401403c00c40541c02c04245082400002d02c100d034010510030f041031040c0c0302c422030020510a0000c1004140c42c103c1004603669848480e103166580035500001040380c18000005030003a0014101218104180310025440500b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 387463821 1250 387462571 387462601
    0x16020d080c0c15030a020702011e170c0a02060c2d0403020112110d0f0609050114010f11030d020c1005040b060f030c090c03251d0d0c05040203090a0b04050f06 70
    0x42800851811a141ca4041d8400382d485408207071704120582403402e880d60f2b45520f000d005405180c603038019842c0d039041c83d010103c03002843c44181400c10711000315156000b0074a158081c400290f03c554038044d90000b28143d84c1c44114011101003440841520400c8039070007801507a000740c03506400d0038000a20642074669440c002040c03204144413207214007416803c03070015507035070380000b044a94640310b403442107807000d034082100c100d403201e940551940c03c135403280c00c03a02c3d0514210b00c0102910000b2903507482000c0c40000c1b0300c0d0340007a201c844e007501800203400c0303240209000c1c400c2c0d06050801391800381e81a00c0d4540725440030000d00c0c14a180018141000c202d018018503066a40e1110008454100414404501444020840d400d4982014410854030341e0346801e0f1f1880300c5444110f410603010b451881c0075078000038076031010030340d00400001103038401c9a0260307a90303071003480590910a030404002c0c411500c0320240f00030007101141001100d078040f401c58006507190075007046028 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 387465071 1250 387463821 387463849
    0x6110f101d01021c05130203191a1303050f0403120903050d0905180603070b0d050f060103090f0212071505090306090703031202070305040b0a020c01020d050c0d030216020d080c0c 79
    0x8290101070744a440901e4006550144100401d01c41c00032031b90b00861300700584641034040746a519a02042000810502e03400030048450398200307180740840c64820348d4a40c2c8000a010300c040801c3c459461060982294042c1d40d002d680d0503100c10201748050801c10031804121182d00405890841151203400d01c0030844000802525104032403100868400c480941031907090f0081d0030010844001010003000900586a0001420b107070081e85100c000d03801520982c105800c2c03200c0500840d502c82c03103048030103404a48034400306036056146031070a40d1580c4000201420144c3e40c0c0e1407250400042c101e15a402e03001d0b1941c81d50f45080b8180c5550040c08003c01280011115980a9995502420005100c1e0038914642501e840c1821060740107824000c0c0142e11034001d00d800c6590600c9010422200d60624500f02815000a6602d850981030050200365010414140700c3c0390300d91984c40100d4000d880000884251304062200f41e02a8000d400c0a20510100321958240303174000360462 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 387466321 1250 387465071 387465097
    0x5061305040b030111070503031012030f080709030b16030e0705060304080703140f0408010f092a0f0b0301060818030a0806041e0605040605060f0406110f101d0102 72
    0x18a0622080200030440d80010b280c1643d40d802c00d01c214040071000414000d401080110349130b140c4458082c1640e55180c102410342c0484002034000a50440308814003c00b4030b040003510342e56030110071922800b0036400034110382c01c0c400900005090400d21402441103964040c440d02c440605c3e140d64903103903882401d401c80003c00000340840c282c1c2002c0c1501910a10340072202018248101c001d0380c00035444070100220004003002441802d11403448041d01044050061414035126240c03414000e0302c803465000740000340350b441144c100c030710f90300a4040f481c0100211a25004c0e6103800f174000b40900004206040d000c9801108e4903900322500c4410f6034020751818000301c00480c2c04523805411700740c025844e0100c40c21015454424401080900c02000402c02e24110030002541c51540c80b540c040c0f0790402c400d4407500c0f2014100c41c19106282440f04400c2e1240c400d02d40b5061110003204103901500301e482c20766045c0ea411100002006d4201008010308640c0898200c0c415408178030b10b2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 387467571 1250 387466321 387466357
    0x31d090106030c18051f020f010e0601061e080103060f060902040b0307111c031e09050a061a0609040504021f0302030403020c010509011e111501050a140a171204140a0506 75
    0x451b010403140940200b6241c4141c443d58444403524600b9603464a020f103d15070880700045c40a954031031000454280055109501310808150250a010043c000549101c1d241c80001d13802041a0304260024004d8140455031070780d86400d000d105420980c3c2c0301000031f03480e50322100c821400141c0c0403240c3c0d04882d40b0742d0340041e00041c2600200000f1007007034804804400304580040451081d82c040710b014201501d151106485c14004a904030b01c40000318403400365000006460314400e440c2c4030b201c10703500003031161a04c0c00003890b001c003506244500011400c500c0d45003294183c000d103000e03034420b17022640d000c4080c00064407140035202c0004e0010300003808544048000500902106100b810000f0781c0300811b145081c10803140c3d07544450300e07820349001040942015150100109904a044074031030800400180c03171694213200d0b5050324111b482d2030300205d46003488900c0b81c0c04035400c1d40607a1540d680ba201602c1c0f041e6a00207910079814000002480d051007030480e0549400510a414 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 387468821 1250 387467571 387467599
    0xd0c0f1502250504060803070302010e0f1b03250305060c160807020a0b03181005010f0308070303152705060f04150302030d0504080609010c0c031d090106030c1805 72
    0x1c0612240c2d5100c2148502c0280041c090f00c0b144200405008110040d554031a22410060300755010501c41c48025803041c10040200c000c082420b00305100003500c1411003120300c0e00064500345241c24111032220100c001103c2454418441400311703171148040c2c0f0802c4c4da400d0754400c1705011700c8142c8648512003948800c00121014010009184014022400640c442c40200d0340b0f90011604000808030100308074880c00b03c100519a070b0105c5500c0306115560404000c0c60030007090b0321006154080102e003090802d8001d07040b407801161100100b551803a600c207240c010215542640c0d00a681b180c41c5882212141b80c09003512512000c0e12106694440c070040c00000c04200b541d1140140c2004004001a9001e1041c0040c6040c10307942c9a80350b5080500a5040680180031a403060707240010340a036292300701c1031078012a40c2506000c0c0d050070400480c11003051094881070752120300100081200741c0c155011801c01001c5555103400048402004d140e0895035010b06d65103c0e00c0b45c0307005c1d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 387470071 1250 387468821 387468853
    0x161209030f11031201060315090e030405100212030a0b10080f0402130f02160303050f0f01031b0b070605011a0403170f090a06020601050306060d030e09070e0d0c0f1502 74
    0x1d000c5141240c203c902d0034481000c0280c1540d001c0c2c00980002c0c0e181e00703400b010001008003003009032000910070050104044411583c0e84100d00c640345c001c1e010390b0b540b0207641d4020302c0b05400c80d80020b088140d03203242605049005150981803103203e40e00d0403005000c00d074441da10b05031141e0380a10102509031925004c01000700604c2140403034060b12440311042d40b0174030f80050700e001d06010241c0c1c001e010051801500f1f07900024404442c404141082001042940301c81c1c40c11207420602c1310307401c081c108070411901d0300135800c680300306100010a4010001290710003030481c1ca08642c0c032000107151081c1415148614880642141000e9841043d4041790100410303201a111000030b150401c0a0302040808940c0d03404240507070480380040005050a001c5203920500032170b401d111412040c0e40c05800c900c110b4400d103002e0300900c40080c015a0094401500001005200e8000403e007490b041c41545964091049031690b08070b030000b6200c00301108a004680b203a00a000d110020000e10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 387471321 1250 387470071 387470087
    0x307022d030f032202010c0303020a1704080a0e1504090b0a030f1b051503010611160b04080c0d020d0206160804090204080610051f0c0506161209030f 66
    0x200c850300c11980321042540800704001c00c0d9592210a105480b880c00003107800e040407542415240080c43d08443c1001070f0707030001c10001d40c039915041c01a102c64200404880c810703480c00204200c4002c0740140001d0104100140070403107126583c0c101c04151850603c00307802c80f0706c0354016162a0074007060100080d01d4006019140380a0400c04545e0740c2c5c0d07180d05c905c041c6d40103000d07943c1085581da0304001c003001078000c07006001c0503201c88003d03410848503e00c4e03900c81480b5a50130400d0036444040b841e5000c2c0711028003803000d80100800103032601d8055901d60300c10310590b00c1c3c501c0f907000c003100c0c24141712410300130080c4c0003010741000815a4090103110360048881402c004d104000400000b5a290050006441d41880c0143c40d00c0c1081c00c01890010301600c20130307106000c081c007001155107850030004007103a0703c10004021008010207948507000c2a100810b580a80002c0041c043d0f2015800c4440f40e100c0e540d9080e410391001c035030400311290b9000140005948022903640c50740182d200d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 387472571 1250 387471321 387471373
    0x1e030b0f04020a030f02030a0c08100f0b0c0a05010c091412210c010e0d0e0f09040312020f19261b0405120d0801090b0307050f0111060c0903070902030702 68
    0x20101c0c01c401c14011820882c0e0044604643c036a64a550b09031302d040d80000c1264bc402e1340308152080d903a05000106113030820512420f001c0300740020390003400a100340555042258805c00038803948554080c090f08411103401200c0c0f0400b810500c1c8210740c0f070301c05904462204130502910541590b01d0705400361404c81281c140741c4040030064411202403d00c0b800c140039002901810350106003140c01815100b00510041c8201d0301c80b00000d0040c0c0c4c448507415009036142c1000300c000300702d00d0b00380006405020010000180e003c502e440c02c0c1d10520b05e04c4ea20a80050380c036010074001813444800310080d81903e070740d4004c64410001345101050049010501c00c069001410203654200140742181041e104403440d80140010034243c6401c01d102074058074121506010481e140070220b0f070340d07000c3c92140d1842074605e80480c0c05582d001e840600d6906a09605442d0369192188091744c2a50000d40e0a40c000c1c80b9800000076104240c0c03081c1c80c0605002e5010b050010100c5c203006090b4050048 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 387473821 1250 387472571 387472577
    0x9061207020f07060206070e01030b06090d02031e060103020306070f0903200604030302030c0d030612021e03010203090609060705030f040f150513031d10051b0703031e030b0f04020a 80
    0xc40b01180b6007040b4400080c95941c0c000d040d00d180080c0300500c840c0d0074032089814036003403450040c5c050b61040140c80710190162003418000b40309000091520300c220204500c81c048180e204d80d001000440c44a05030390003a0101d44058035808011500070f9003036111180002d4201c2c50030b0000034105c885e500280300881c0524812107245d200001c807250701c5a4002c50250344006180c94080d10180000a414203090074100041454407840b181c420004000c000e1242c40c00300402c0c290000c07188130500030600040c00840d16890000b1105598080a0740c9030741080c41140c0010300414031600440344a0105034040700d80d261101d40c1c4800c0c2c82100f1600444003030110440058840401d48101403050480181080c80d08480f4140a04034022111020000300b0312545184069105d0318446440c1c1505031070602d550b0703111342c0c0c01030500841100c4160400c0c024410b001092542c89000720a021501c985071407100108a142501160445841c0030f421001184182c401c43c41e2a1b80a40f104c01401e007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 387475071 1250 387473821 387473833
    0x5120109080d0f0513020604171006031a1003122609210f03011403030403060c020a03090803030717090a02090c0703080c12011e03080304150c02030906120702 70
    0x6551085141c00c2541120031041d80d980c0c03c540300320400d010307080d040000d260400d20f1482d01500810b00070b202c2c5008145e900028440c46801541d01040042014602e860b400c100040d180d2402c86840c0000f07221280d2202900d0002c86d00340166005104101c03548031201c9110b00c03039803800c292a00030560107840440030040c00e2004503141c4102c0380500c10300f00900500304481060070040c0c500e400c00050201e401c0000c0c0441482a1011001c1300d05442c0c041d11500003440242d00003034518401d0b500000d1060f0b00708151040c4464001500c00e0702944642c0714000b083d40c4072003081d50703039020031950380d0009540020300c0c0300c00d02d45406542e60803100c99800d03280320000c0c0e900031400c5428140c82110840400103100320906038020407181e00241003e2485142003881c69201c000742071306024501031905000c0c80c8405040740200e80134002c41e403010a0948030f29180c01d00c00d80360b1400c0788010380281d003440c3d01d08080341c2c4080202e480a4200034011410300c02002c200c00584e40d40104980c00758858a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 387476321 1250 387475071 387475073
    0x50901030f06031e0c080d0c110a0b0d020d0506060705061b040906120b0601031814030d0c120b0a121b08010603050f0c0f010507060f1b03060f080d0905120109 70
    0x45101c00549040001544d41090600d011007006059911201568000020068000b035000b002d0780c020b641c0101c113801c04070380d4003000501c107904035901c021a040000180014003403940e8014108484000c9010045035807020203010301c070311039044000e200750042000161300582002c462b5075180042800c0b542080d0301c688482c8200c4101c3e4001815241010f0710100401c901e11a10b56070211003840d050000c05c28400b58800c1c51100604014074040794082c142c1c403103000c10020354106210680c01400742d44600403000d800d0b02d0940c0f500f00040d504250000602d400c2041e8070f0320440d90049071302d94003010543c5944800c61a84000b08803085491036001910b007000340140c030040d60048000d03010600702401c42c03600c1c01411445c042d0054039103090380e50690b0303080409e80c0c60036904004086481080989511f00400d88000421282d4509151031841198194803000039540614001c82142e034540040940d0365030240070030030000741d22460a1042d403d0000c0550304080316100045145045 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 387477571 1250 387476321 387476333
    0x6021b010503190b1c0507090204030f03050307050d06091a0915040209040902030a030801051c05030f030a0b0d230312060d020d0b040602130e0915071b081305090106050901030f0603 80
    0x3103c0301c101c91008010040e20506c5002e103e00001800300c031108524151035503440c030f107002c1110480941408004800070b41038034000d4003181c40520382c0320810010161140d090741d0042c01c24140e1916074594410074049a818201c1c09640503801a55014400000706e00400010354000308400340c00c50348841d40400181c07410041002454801c1e00c0f0140c0c00d40c14101440441c46051003840303040c9198021034000700d14003000f12204016101032070f40c0d40fa628822440040c007a0440c0c00c507080513848444100740400701043d0740e4603d14001848118106071541070382e5034029214090030300c52005002c968a07242910000300c2003440902f814888209a855004d0344c000d040b1402e9480355000160b01040c181000c0505000c0e14904e222801c81e8180200303010356525851b000000a82444004111000c1c0501500102c421003c500f04241d50154603080019410224030035000d802c00c0c84010420385080002d05040c1c4143d980c0d007a090180da00011001340c4520030300c200045a4684001c000300d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 387478821 1250 387477571 387477589
    0x3210403150c0f020307150c0e06131424090a0807120204110705060a09062d0609050609040305220303030905060619140f10080106021b010503190b 65
    0xa03000c0300000700d500c601e40c0b000d0081031010511804541007042100005500100c01e8001001e28a4000078100031000b8241c5002c510f40c40819070000001c9451080040030782c80890a44854011900d10071030b1503400c2c080c40081006168034092100300040b0800c40c0d280d0301416024000070040c010065907600b90b9400c10110340c100240c200c2400a0b10f80540c10180a00b104941c44107800524001e07458403059100c20b0f016184060407502c90103100f090240c1a00071702d2134503e141140c03415071100b01c004049031280c0032840040c49420b000d40014a00003501c1082c0c403540e4050308070307042d036611650b0481e0070350300c2003202056030000900b0107041e40c2001d45002c0081d610a440000b60720410381003451400d40003c003a01e100b14100c0044614906103072041c2c100300c40e141d10803003c84055500004085ca5500407015801c41d01c1494161466640b040f0014125102900cd440d400d0012000104001c0381214465003c00c3c000c00110740070200b1103201071020540c0d6a0006031100c10b41c3c1c00034403201c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 387480071 1250 387478821 387478853
    0x4170703091d01030c060f0908070b070b090c211006030b0703140622060801140412050304030512041109101701090f0f020310060b04060801050f03210403 68
    0x5408030414020041d08445400801d500c801c0c500e603143d0300d9541c504010b03001c1d5000c5c8a040204c00098038920701c1c06540c20720b016200700400d44044585900d2841142d411105054424000120104020020110f682e1210f0200038002c3c0500303000340591204640000042900e40707100348050005c1400f0342d032180c1c2000c0c510a1a002d41c550414142c02425940482c28520700390000000748025603a403446255207030741800d60014410400424110010492588106599420241d082010380c044034a450700c5184075101080d111809058221400c1c0022039000300405c0341044100074414030701b081180d01a1180318465889560a800301d6134038a0141d07089209035503000e40510031088004240000d210442008024544644d180d03071500040b286000381c02070030148000300c01d5440c140200f00d00c04c48501410f00100d80d44074070615556200740325034400a440b1000100d882c1c81d005840f07052041c8018001c000d1003940b8032200c90f4804120594030402c40c001c10000000400840c9288184 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 387481321 1250 387480071 387480077
    0x30203040210030c0e0f06120108062a032701090302011b0c0816030509101d100c120e18060a0b0403210311071101170108100504170703 60
    0x20341000c0c810300a040020a00b054103050500c01100840c40e886181e0965a1604a484d030075910b5400011030002e20442001b1070990840000100f17004000050441c003c1d1000800c601d0340e40240c904044c3e80d981200076110f1868000c0001c10700c0d94907400c41035045c0f28007000019150740036101d042c40c07c40303004020440142c0d45412a00d58008001201440724444500300f00c1d0080405940d1740d102ca1103865143d403107001038100c102003810322500a5070007000e40a00000700d000b00403440540b1001c612035107107044013419100c500c2030b424461000c42c80d035059074445001c600e1061f034900c500f40fa9101d801c4420003054428103000c554031858030561754000c4481c04030701030510409022081c11280c00801d200101004104000b032b5006d00c0c05003595000000303007030b500024400d04030040c100c405544402c01d1000300e410001d1200062071189500400d07201e01018880c0d25458445402c1c00344038003421908070f4000c070303424901d8507004039034132500c00d0100c043d40c490520f130111404e8120a00c19000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 387482571 1250 387481321 387481327
    0xe03160614010806010b0412140f0a0b010605180d1106160b0604020903030a0809070509040602030115111903021f02270f010c03051903022a15040f0b070302 69
    0x1141076003280e040d0241c01c0700c0c00501030030f40c144441d01c4440d205501c0341440322042015011f0078010b0769203c940300720070f4880513608250402c01001b0781e140c6c4151002d503a0005d05600000e00d42d80160308944174500c0d4060013042e04003102c010890740032884581600d1002c07031109a6542555000002c084070ba48040f4002c5d0b0080140c108014804c2e001818140960310403c0421007036a00001612503020261801c2c001c1a034840080da81401e0b090b40c484c0d82c0114403a0140801c004003500514181c42c440303a04240d600b40c40c0441128002d00c40a410714480c0c20852842c44490a2441d0074225540640121440d00c01075245103241141040310079102c05902083e0380900003440c0005d9042c21400e6164110300e108507600041c2c41c0c000c0d484160b03040c4200214140f040500503001c1d01d107440c28425515040140f1900c01078040d40c08000d240c805042d18920b628038210820300d856480d507010704010240b803085110320820307001000d032007540d8500c9070240c3c0342c00060074409018070810081d034001d62 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 387483821 1250 387482571 387482591
    0x1e0f0703060617010b09120a060b01120912031a06031503010c0203031b03130807060605330a021632180402040b1206041101020a080d0e031606 63
    0x40301c100d500503608000d8500d59180807140b00b1418181034503c0d4020495444150000040c0920031420203c0c1e41c41c041c0007107240074408203500007084583d0030380f211880d0070810095401203e01c808070091550034506850000c080c4250301003521b08414001c08845646200005a05030b0011610341041d40b6841c003591025060130701071040440e445000650841c00c0c040d11522401c03100c1801519541c1000c400554500010714110b500c0ca600041c9041c6c1c1d034459400c05c0000f8200ea0f000e0a405002000c0000655242c01200b000f2a500075000c1e250302e6452000d200384082d070105020344218030650066000c84960b14800c84005c004540c40003001614070800100c1070041045152602001c2c600807005580340c400f400045003284003405085035a41d480040e0050030b040a841d500278441d02c41040350450006030075401280250340100741404540012640c59420714001814828207001e180041c1000e50000f4050302003410940c0c0c240b000d80c0b0071a0000c1002d10509944c580c0c1c03228a801 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 387485071 1250 387483821 387483827
    0xa0605120a290c090303070618110a080c0105070f0b0708010f060f1d0307030b0c070c051e090709090c17130b0c0f0702131e14040b1e0f07 61
    0x4645000544a00b80100301041d0751120000401c11003001c032000900e241d0303030380d011320846116946c4041c0030041c28090003580d4035003000340303401110300000c84c00d01ca10091900031484022036007000010300000007031200460b4140c010010840355401940305120000c0e803010160fa10400303841e80c481d0110b600d06001010b450b034413640b0031070510512034089140d243c0d0101009e080070200703011055180b80028086803400b101030780064131201c00b18081c446003403250401440c80c18000c1e130414610644840800503a0050403404800c01d61140c04402101d040403800305078880018284440440d54640300042501c1e50700d0003400c0010b000c514000c840480e412456a000080c00f0740401c01d0800307540c1d0345035a510000d0300350460030b400422180000b8050030100c510069019052030021088020400040e003035801d031681d000b2200c65110342c0745804c41e2103200c3c00304a845d5508038582e00e840d1142000080040c09041c1a580c4098410043c0b5003940a81e038001c40c0350440c140e0381454811401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 387486321 1250 387485071 387485093
    0x4080a11030d08191a0904030504090b010314010915080a0606051503040f061503020303040902041508041a0c090405040c06020706020d170a0905070308040e1302180a0605120a 77
    0x3241031180d03050500c8058811560003080044c408800094a003151400c00605141c503810015401003d00040100300365000014004590122905101c2c2501000040d02a83e050000e80313042152071800400510107103800080b20381601184180203140c48034030940c20000c51b440140d80161301d13250200124205801ca01008a400042050075420b046c1e8a0a0b40804881c0c000790080f0345503550f9441705d10b172814035480110350050842e40d41e142c0d26620b00020390007901c108a004801340c01c14072540b50198080c0d80c45075520120342051052681c84c200380c9240080c0c07900700e80100600102d0126185c9202d603600481c007885c4030350302c040e1600078001d25140c00c0d90003440441d006070300d18903a100d4201507420024075a0040302000c3e580c501c1300d0840200704070000600301d0b1003111400410302801000038001d585120319411206d640e07020031030800b2910540001c0d000400d1608216002d810b0303030f920781c3d00001d2401010600ca136071200026040d41269080702550740054a40404021141c510 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 387487571 1250 387486321 387486343
    0x80f0f041a0a0c031206050a0810060504090f080a170a050a0f1109041e02040e0a05090a0b0c0d0609110901120b0108070507030207030c0909110f0f010c05010204080a1103 75
    0xc0c1d49000c0c004500140a62140d180c0141848290320940a901e0584d8100c100600000303041954200e40d20142c0341c6e40e030000d500b0030f0400c451030314102203110300b410b0003015286600451880f40304204d41c2d41d0b28840e9030040000c5420800b2070b00011084401d00d580003070042006140201d454240010031508440c01401515072940c80c2ca84841041c01c2ca900a40340d05410444000071442a151002000900c09003031a003481e500c00107012801c601002500c1d0302404003e0800c02c4241c0e60f031030500e03035524401d4a02501004024000412551046004000a00c804800450380e25555072812003541c2800251850100e00800c200103a035a102508054102c481a1305000341c0703200030f00103030104101621000400000250840501d8020010503000b9640014406402c540d255081001840394000407162290045d0b0b20810034505440007582c1c1c1c090051401c1032040c544c1006581c0c20741d01a0703040f6003a5409010005810000f80140300351607010304440380034030503420708043c104200315039 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 387488821 1250 387487571 387487619
    0x3170a1413050f1b190302041b0f110304030b090f0a050606010311040e130822030b0603010903020c06090111010207060204050a080a0f060b04090f111f1b080f0f04 72
    0x1300480025118540c03201c8a64010b41e00b046019000c00034400401c069504041e401905241c4800c10f000c085c1080c051140c401943c6030100c412642108454180c1c828003502c209070b00510092000c154010075481d04524044c044641401280402d82d0030801072100940300d0382c12040c100075103560036008003500c800c4594a80d901e400d040803116181441e0141081c8c543e03a080c0c120030400c1103200c4e0210ba21610703480c00041c13016600034408210403021408100c80744141480441c4040c10305000f100c0c819680b503000b40120134a03190a002664020b80c0c141c4c0d04020400380344081c1d002084c03004044040c01440003503a600c2c00c0205010041e1000c0c0d002d2445548104400800710342c032210450b02c001d0348018042144c0300418001030240c507540e00302130505003440401404001c1d241889481030401034804010550701c20030700b03001c004400107100e80455803149454403082c6081243c00103551098801038200074091082e00d0030b41d084481403071003003400003d061281142954481480b182e20003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 387490071 1250 387488821 387488833
    0xa09031404030510090302070e040f110121090813060e0306011406070b04030302070b070806010807030218011101230901150506070602090f0916180303170a1413050f 73
    0x540c076980c0e684c00e10070000386aa03980f0381821040601c04d01c01c0c3c1008180041c2104c02500b40350401125210b8488001c0321425030a002580465000b03055090241000c41e040701c40201300102c140d0060200042d00700c50300e10042020784e034000c0d0101e03051400350071269504e1502d001d030007003030528000c81a08028404015600090345079074594088070384107a0301c50076000d03580d03c6614003500a4045c03010001e00803450b2008204500746d120052910600c82680e807222540c5402c40706070124803c0c02e80c010500d412140118003154050903600c0b07461031384100000790381d050034a4440d044404080421007a6050003041c0041c0000034081c3c1d010742c0d03030980f0243c0210b610301000220356110b00c0d50000c200035000f080248043d030b10f4051401ca220301c043e0040200303141000c16800d107610542844008543c51030840c0070484071000807202074030ba05485035070042d000c090004038500001440c4401e8182c640c0020b1801d0039030f0300795007070144100030f0380b110300746106180a40c2800c4800d02c0d1445c83e54003607 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 387491321 1250 387490071 387490073
    0x201111f05150307061404050a03110126070c05100f0b09090304060e041e05010828080a030e031e041505121f0801020412060b101d010c0203060a0903140403 69
    0x31944208840e240d0804549294014000380401d00a0317a000c1544409d200200000b80210002c1c415005842603890080c4204030308404000e03818905c248410740b118400004514600070703500c030207103140100100d0fa4070b100442c0040c4217680300c0c4080c41c0190f584400c1301e901241003c0c5075a41e00002020051030900e400c24500401b502204464103100320b4941001ca640110345414a0b0300c04138684206100640e190b2605540e80c03540c5144044e21140b900a62a4079650100c004c00c071001e41c003002261820600c0b080840107044201c1d00a2107601003048640c40400402c3d9994090390305aa000a1312280741c4141d4000c0014110952028060100921704000400b8107016600203c02c090b071250201e16980c10b800164021b400034100703903200007008201081c0c0c418811042030300c542d4052024862000c00e010a1062941009010980300d015410680080320b81c0c4900da14018982003048103541d8000903d45078003995a000d0b0a0390710b8a08505041e40540101601950701414070b10302851 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 387492571 1250 387491321 387491323
    0x10020d0209030c0616020d290105010801090c080604020a03180f11090405340b09030c0103020405030613050a151d0c10230f0a0207050a05090a090201111f051503 71
    0x920f03c00038402d030f1070032a040042001c117002e030f86c240d502c00200b858051013684523444c21700d840c20700560340460702203000015190705601803035401e1916541d4540350307900d03901c051002035040043c898007810b44403800070188012414880c0040d5001d9489054000e48030304004c0020081c0044040c000c882400800010030030008800010340c880c04c2da04030a00c209007004600d842c1851046e404019102d102c00500b0394061704c0600482c007c11015254040300b03040040d01288200e12626030583c1110000925119100c1140d20700280524261130f9458944d50b200c04040720070f0b98404401b5a42d5840b99034509021419803c00001980300405041c0010000a0100002045143c081180d924901d00c2d61107070841d060495030310071300c0d4626101c681c80d13044080250400341e291001413103601d400181a140c80e2180c0350880e1006044507070f02d03441306e1003140094401214180d0500c84040358040405908214444041009903103842c480c0f01100e1070101902d0b07000d450304111040c2071140840d1950 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 387493821 1250 387492571 387492607
    0x17041a0a0306050f0f010c03030e01181407031a090106090912030e0a17071a01080c150f0f160b0103140c03030c0303070c24020307080c03070906050c10020d0209030c06 74
    0x2d0242410104007d2a15086018003c9405145901d50134080002c4440f10302e640014031081c4103003400e841500e150901155a01e84c0c2e40720141a8801e0044e00300c60184510f041e80b900000030f034001080480d124a030000a840c240b90013141c070703c0070040f203010900780d061023500c40703802171038019001c000010385404c0d08640e10007060401c18200041c800080165040d0352015180d0282c0300139102d980d542c0c450360b4482c40c4492107a4000c0c0e03001500039580c1c2409004075103640c00d418426a040188408401c10b132074021681303045511003072139040070116040300b100c94002c510440c140720030400009000ca040c801c00c4200303035010303900610082c0c1d80b55601000766640f184161404d400850078504198412407102900c100c3e03840280c0b400310b4901d4003943c001314442c450a4466000039150401c00c29102c2c03204a5400001660021040c03018a10034402441104d90b480b0444410000c0341d1401c40490b0302c520302d41c4c950154001000c1d41d06044c00d01c0140100d08040b070310203042c0604918500c041034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 387495071 1250 387493821 387493849
    0x21210090c091e09050414010c0504030519080c250b070b01031509080721090803070605180f030903120306010516080f0304110109050a050d17041a0a0306050f 70
    0x41c01c1d2856114203c410069803100a2090400a01150410b0b003000d001400060342400b085501300154001c0d014041c03c00c86048940c020300a00d0046401042410350000000d4200e030150070401c0550300111040046d50813540b804500030040e180300c151004850001d5620940360000d0601080e0081548a42200e0440b030b0003860003004c2440301328501004040e4002c005088042c04246181072086030420000c0c0843c031001d482d130140d05003086c10b54201c181c0748034a544c0356004000c44400a841030b00010340100600741541140d034003801d8500d0902e100b2502e54001544041010300c440c1c80d003045040c10030090f01020743e01c1c50510400007800ca1240350008805611298811820840c1042c01c803050340a5160140b42c80b800c05250903c6c49000501d40b07280040c041c00804a854a4201d1003502125001071010014503e259902080d0a0343c503510401500420b03c0001441803060803607071031415850300c960303948031505400a401c88505421060045590000050207a100c40100b441c0362 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 387496321 1250 387495071 387495089
    0x7050d0914030301080a0b100509011202030c2107090605101b0503040e0a050f01081b0109120308010e0c0901050a0c052a13090b1f09021210090c09 65
    0x4480c1e04010101e2a003442112032184400000051080d10214100702054490200e03003a1903298070107400541d851074021107511600c4640104640c0039000a21074040e80301070b01fa2010b45113007400196204500c0701e940c44414890090f00204148240b2031000070300b0b00c000c800c1040904100204184441303440c510703401c0c00054510307000b00304a44182d0554440c1d1100c01c8a954130303260301c100c004007201611044a21401c2c60301203a090b164036901c03d416110820000c21030000c01d00c1003203000c5540c1d25032a83c18401d00b0b0101040300c40070618000c8005000752100c01c5a540740c80c13103424020b030004140f0101400c09001640e45030381d1004c200c1d074880003e4a413003040c000250030114100844901e0103400808806000b03440c42d5140006408031080c200c0e50000314566403000318080d10000000184040405400a8000002c3c102e014050400c40381090020303a072030b000e80000700d91004142c0300b0300980050401401c080788812400141000d1903090044002d812005000484107001d01400c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 387497571 1250 387496321 387496331
    0xf09050f0d2d080c120901020702040f0504052d0105250801380d0c020c030a150903020c0d0c0e180d030e120d05010306141605030702011b0f021507050d 67
    0x108144d41000c0c1c903081403a80c80103114a08000f01402e00079031107000d0490040c0e0034924030b01d035400100c0c850148191340040183c40c560107550340c4001d00c082c1c6030800340e410082111f00915100400d2113400d22176000000b01c919000d0840008000e0365000c0c1c7c801d6001c0100200041c02140030b600c100b08a185010480070f080034038040440d00d102d002002c44030000000200c1c1c42018550740341c0104a000f5101d07020b4940c074050f00c0e01030540314008000c01600341c0e00d01d01c80760030320350038907a01038034405010303105039070016428200080c2c0903a06190196403245020781d0034094101d50b200318a03085260088458001c0d0041034003d5103504a075600030f42031540da001e00501802040c01108154140c95007003903502c0600503040001000b003070106441041c90100b1002040032412003007070084d200c0c07180901000c501140704949aa10091000c41113540b41c00850002c020080b0680800f1612a00c44005034421244001c6c0303401040300c5100f603881c0e03502d024132010503084401c640007005044000b2403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 387498821 1250 387497571 387497581
    0x10504060f020114091f0b0a0b07020409080708030405060c04050d1b0b03090106080111030103080912190b0406051b03060d0f05160f0b04050a05040f09050f0d2d08 72
    0x80180550120130340325080d0082000307041340c0007094150003014451003103051703805004120310460390b10086664000704440001c0c00380083c036101800b60300d0310042001c2141500307941c44a10359042044200c900d1280070092204005080c081d03991302000c84803489082c68503040000c1c542a000c1207020348403106922028000c031000c0d5802601038107071011000c1e903030700b40030b04082e009107907134412280c1c0c0b546064006050b4124610859040302d811000399070030421048100001d60f00580301c03405051082c000801e6201111980b9010f505001d840c1c035184601e891b040000030354100900790f414142d4904521452001c2400a80303822810641e0207030b404c81050b25000b02810000340002d41940b045148071400b0030800d513402c4050ba071504501d00e0f00c0310799491941d4101c0c00340380925940f20802407018000f5040c5540a590411818400401e40c0b421070b45425040420700400e840303480d0400e003581102150403c0c2a111400404044001580003031000d90440080658500003045030b0030010070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 387500071 1250 387498821 387498823
    0xb0c030c0106060807030c092625150f09090c02030909091615050301140109051008060f010c05030301030f11030601080601080d0c03170c1e1c020702010504060f02 72
    0x350400d0806008100c110745500303002d424504210365070300010381429040312210b44100385490440e0180901c040200e603a81c404200c480c1d40c11207a1064500c6562040841200c83c0055502e0715482e0345469100a4100340d503d4120202c04280700781480b01070315208404c19405120902141c2140b000040d00400c4900100d003103104c1c10800a030f101030a0001c0c403020901c01b2982c0028000020401c0710340c0c0d991005584a2520307074170000c00c00f01c0c205100401c401c054400c3c3c0c070401302805240c43d085060300e600000b8805055459040006080c8500b048110b08050082042450090801e00180c1d060b55440d580e680c071050000403e281c0d504821002085140040c030003200030001c041e01c58540c0c450703c00300ea80c0d07002440707224071038498403c020b50114090140403103030b15010303511101c01c0304214000096502001c0c0110180e04804c00c0010328040b6041d014401c1003040956950b0b0700c4500300402c0562442559154039a14810060305d00103070703002400c0318120b840c0341c2031820119003032040170303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 387501321 1250 387500071 387500077
    0x30f08161809060303180602010507210b130c120213090e101e0c08040209040f0213020a02030901020c06090603070807140d0e060a1b0c0f080a0e010f03050708010b0c03 74
    0x7030407002d801d111011041540000f810160141e210200485280d13503007204a098603810b58180010691681e50311451009101000c807180030319980c00f1545100400c045421481d44041c164049aa501e10040183d035210150310040c3da8515810341c10a09407483c0c08401405510450001a580c1c2c10100b60300c80c1d082c840460548640c650030002a1245914080c5003030003000002116032030329950780398940c010751505000c0d80c1c0150038207503250364940e07461520240fa504180d0b030001d25009903074000c8025000621002c100359002e5601d41d1800300c0060703e0071300344081c4144038400138010f0340b4460f2120020380364071a0321841c0803c001c0d103589c4030690f001783c034500e20007201080010b03031b0311511a0903400080041980000f1a81d281d0383d030306440c10882e0001940da85501c8284103040030014131504420320240d00a134000c8040b04034981e20f500d001da02040c10a408928140380400e2070b5a00070010b00ca81c140c1c00d003024441da1a2101000b4580c00b0140501c1580440100c1e150918420030019 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 387502571 1250 387501321 387501329
    0x409030f1809020c03070c0b07150b130903020318010806090703181209030c050607050d03020f1204050c09010e161206031a06090a0c020309090406090f0f030f081618 73
    0x4554440b1303465121522075010320016220f40428280000311400d0440071a500203400c1803c0030060700005500801401c0100056540455010840d1003084a0ba105d440c81c0c1900c03940040da81c80420846005030000340b4003140d41402651030403c44c0b40e40780c1c2000a60707c002286030004003000503c807000d03141155850080e103495240c0b40c08500250708181c4080c1501d01418081d00f280b5a05da01b00142c40c0325241c0010300300d0b0080480141464000d4000c4c0c540214640340c161300341400ba1100c8182c1403030842e000c2d601c82d03200d20150841810f03c030140300e0140011030840022850034540746130040750000304200030418034824540c0886c03010347c0070001a41c5c1c40b04288521b0350f49488407440e541010b80303040748165050740120705042d52034403948558a205401030f504029001040003542c881c002c00c15a901911040d8a0740010030805c0c00504451182e122001780104504006000310003488004041c481004c05100301909590310120300c00c0451700d4500c00c00c060385090034051001e141c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 387503821 1250 387502571 387502589
    0x9020102120d140a020f19050405042c06040201091401091502010c092304090221030a03110304110904020102010f0216031112031b1204060e0c0409030f18 68
    0x40d00d03402d040564110703d035402a90440100c1c01d803a0800207070704034400c681c1c1d480b10111080100d114480043d50800044041c242019428a940c07a00810259440c00c0c0e0b0500c031082507454181c8080c103c0c500f00480103460a00204068a02640040c121403d5030103185202c201c901045481a1b11542c40360000d003003540e208000803800c0c400007034080c0c11030b505481c02084180e00045000403007141049881c3c030020000c512100b41e08402d010041102031003e0f81c2052501d202d039180d0f60a000d070b4582200001e40002c41e541c9095000c010129074050310b00c400400ca04206100c0070805169030b0490001742114090001d454510050340181803007403410078814008100ea040b03405882c0c46008405000e9180c400f80046802c1c1c401e9151141204505104081400421200c809003443d850001140380c07504c1c0d02c1d00c1e4845110015080080740c00711480b50301c4490442000f038061020306c8401c0416103044c02844400d60700a021040c0841111042140d08182002d1203903860780720200621000c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 387505071 1250 387503821 387503827
    0x109050928050403030e1f110d1103040302070b09150903030706240614040605070201020709050f041109042003010207061b02010608070806040204020a0507051f2d0902010212 77
    0x2422a07409003808031001e4022901d00040b201c81d41c54040381d02d0490980c1e04c039800c60308544841a110083c04000442055030009204001c48070080d0310803801074008000941340c40345090303e402890080140c00503403140406005c030043c65128164224454001c1c40c41031074403080c4400c0031078a54021410041c241c282800c07400b21100307001c0d03800e540c1130100356810100d0381903d070182070750f40915401703104d104518108410000c8a228001401040b4414416111420f5031400c64106507541504c110140c0080c4406102c1003050181c540d040380c0c0c4c010346258110f894941c0303481d80316113803034035590184103261b1502c10300c0c2d0380d020350440e006035500c02402c20030402d51003040d0380c641044502c070134055864000042149080021114201c03000c5200408113641c9940c00e000181d0400e00c11041030040a100303403000107506005032040050901d081d185c194030040441016154110311001c985a205510040ca0001c03141c0307110300d00b20500e81c01044503212440100d14000d126050021402004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 387506321 1250 387505071 387505141
    0x405060304080715091119030f0215070b07030507030624110304030302010501140405100605070501020d051807050906030a020105030c161b0602190b0a060f060509040e060601090509 80
    0xda408144440d0061040e1801e00c8100f006110354103601031151107c605d40020100001030005010104907440980403161900c4a410612100d0f00b24050031a040c0c0070a900f00710031203606100d5135a003d04140380034425680340220350f402401204202c00e0b101460210070079003082c0200c40c90680741c1d00040441e5a03c42c0d490400074000c0a0a0144031306089603100e4448451916015250003203412129181036285090f10aa5180c0c1c001802111155020304c900c03d00c12590b48103c5105d2003400308140c202c541c000c15454113006454006504c980e2404e000c0c01050703100001d8000e491903080c20f04581d40d40300c50020000c603026a801c40090405100c4152040201d610703c10b241d848143d0070707020842d030b031180c00503030710741d04080b050360444401440c00c1000309440c0c0c0205904902d4103140010459240c1241c80b980004c01d4000038042600094002500d04080c03151451550f4100050101818084002894124948106413143c03461002261840c0040602c0b281c4520440c0a840e80719100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 387507571 1250 387506321 387506363
    0x20a03110321041a040803032e0311091305070b07020105070b040321020c0307020d1115031803041401050a020f0d08040c0b210702070f030b010f08030703020304050603040807 77
    0x3c1d020f00541101e205001c1081001c1d201c0584080d0384a00003d5410742da60905405e030880e0081000c1514000c00d040c4943d60300c449500207401541c005d2520b000041741e10024048145000b40854040b030400d02e00d080049000400e20400342da0121501c10717580d405c203000480d41801116030140007043d030b29050008068001141081000c07030030049811035551521020105e0048640741c440c40d030010000c10005180c0750a002f010030344984201d0b100307081e440380440c10401e4001c0110162402c00000d100c1c0c0c2085500e50f025900a650000710b24090405c0c1080550002c0c3c10205070500c40c02145050095000303218100b04940e4a10882d05045c0100400070f006d800306403019100c064520310301050b07040100301121180380751480c402d00038010085034a19403003001447c0d101180100000800c1c00d102d483c0fa90340056008540ea0051941018811039940c40e140c1d1018030341d98030801900d400a038010064a003210300884a19440b0703619810040d4041c46000320080000450301d408080b40d0354 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 387508821 1250 387507571 387507577
    0x4050c030f0606120a0213081e1606021f0e061501030c030e1f0e070b03100609030c12060f020d1a060a1209050705030a03090819020a03110321 63
    0x80241801d0140c40d4501445201e220307030154510820b5181c80080e480800c942c000b000c04c0704454082076001e6541d107107a01d050544503050441d00b510310000303039581e02e10100600032514640d0301d81c1c0d4829620b0104003035551508000d2140e1450304007078099050314440c3e4485802c10903d202035900c00e250105000052481141c078503804a032400303820f032203160702c07901c940000041410000d140300807203801101080f1715551046080f0f143c641d0284005007409105203001043c0780c2440a46134204404409181d030050381001c000c103c1d80000c10800b15880300a079200701d0b070051501100c11489030800f50007605010310807000050000481c503000800d264030800603103d0749101000e01d00d03d60310030000396202d542100b10024441c5111743e01c00c000030390f0152082901c10021100e006d5070390400703c3d040941c1018150b001c1400d441d010130000710240030ba200c3c4002880d00e885d0b0207400c164001201e84065001c0500300185a132007400494401b0000590010310640307a19610481001c91010315034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 387510071 1250 387508821 387508831
    0x60e0f0d0f05030c03180c13020702012c0607050c04050c04031209051e0301200316030c0c0807050a14010e0124150207030f0501050f0c070b04020f010e04050c03 71
    0x41c01100100d0304a07403044058034007841c1da4100c200d2554941c480280702042003d10b10300068040c0e070355866400c1d0f555a024a40365014160003684400550001403c464080454100c2112031003495804141034144030200800044540a881d42c00c54101030f4030f4440302101441d081441c1c1300502407c1d018441c007620490340b04880c00c41109084010494160f40e540c4a5650840c004c074600d462034a000c06000d00700c0c40e0018000040012807000707101403204a8094840a2101c00801c0c0941e000e00c200354201c0000850034240b007452004d100040806600c1c04e0090620034000c51440200300051002c01c1c2e01c0d03070b0000c00044002041320318040c020404241c14509540c600b1040340f003240c025509003030240d16402e40c00c076151880c041c0d40032a10861810b00c0021401412408000240b40c05540c210842c00b403400000c441ca0085044000c041d000b42049800710b4003404580009011401c94961296041e00d120510080810050710040010402d10f507006041104210600100741d020314410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 387511321 1250 387510071 387510077
    0x20c04051305070b0f120a060306060b0309100f060e16020714031515030d0e0a0b030103110d08040503010903020a0b0601090e0103081804020c0a0c050a12030804060e0f0d 75
    0x58071160705908980d902010000c1c0b9035040b090b4200490f1540001400e4801e40b03400710030b8070381200850800300003602140c0c240300381583d580e001e1040c04910b10420001d005125003851071030034a01c590382d40d62140c0714401035019841d1a180140d441c15600400014180070744248014100a08501c202c803a03c000000010f1003041800680a012859245410507000c0d02a040b000b440e8180304417505030081404100308042c0385885e255490402007070604038065550004098080030401a070184a0340c010303c003403102400180003203035203c8a0f5110f41541103540700807584013481e001c0000d020f0b07035100c01d525520b020109014107070041201ea20080c8607882036480c96849400550700c1d4140360196032000786494006000150f4020010f01c0c082254550074a00440c1440001301079910210400640d5040042c3d8041001031000c010780c003a02040303646820a50401c042c200301006480006802c01c4403403004034003400042da224100003c060000d072a20b400741000741c181d80d412448699000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 387512571 1250 387511321 387511331
    0x20403060b120309061222030f170106050d090f0506010f090b1017150307030c060f030504030f0f051e12070e010915020c030607020601061d03030a0c0c08010903020c04 74
    0x90b40001c82100c41e080401409039081110300385118503526402806010444120a0700b003900c1c01070042e83d64803651180d601d5480041d42d00d0b200034208426054203020300303041c0350014880240c00c4415920001081007001402500078140030001d014080c4016100d070140d080003246207860300b8281c0050303440c9002d05002d2050b01130140003451903440881d030001105488031611224040340c445d50401c1020b1600070b00c076604100000c0c00c02d05140d20031518083d507400100300460300841e1740640420241010802440d15032005000c800100b80020104103003543c0c240c004602460554450040280c00310910401120840200303034090302000304503801200000321154881d000030f840c409010780d50140305a1a121920f881d016280d01c42c8029401001d0f0030b1105920200070b05841040690300806507549450781c00b03455000e100302c40450940c0c0014408803181c80001c100c800c000e00c2854031f4000545141003003100c04c86503401012aa500741404141403560000c0d003203550b44802c941c1000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 387513821 1250 387512571 387512599
    0x403050c032a160506070602030c0d0c0c1109090c010311120115020c06030408070f060f05070e04051f03120507080d090515090c10050c070618050a061403100306020403060b 76
    0x11221061080c680c5c0030b00100409000a070300740d0040e50b0881c1019a0140c00e08800f0380714401501c000708200340001c1c88010403403052182400038980752180640d07001c002d90600086940d1a2045101001c0c140340d200c0071031741e0742680c20908440680e541c0302454800d0f561180251440a100a10084010312640000d034203149400b4003140c4c000c60b800f0f00755902d01604e60b43d0702c6807910f00c000c6065403421b95500780c1d52a04d42c040d000725482038103142e13207007400d0b002c2c05000c100445201030190b401e0341206000d20401280f14062002c181c0360005484000c0f40703040b0034200d901c0c0c803681d0401442402c0200c3c1441d09035407150059009148650151040a1100300f042070008200300c5142d0780d268401042d00c2480e041000807141d442c2c0b0703035192440c0341440c0f00c05031a2801c0000d911420014107050600d03200407000c0709451015140407076045100a1038010028480080c60480344000e4000001180500c2c00e040ca202c0700466000c8025512903a5a0500200401640c2c10b51400761461000001d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 387515071 1250 387513821 387513853
    0xb010b0c100b010909050c030412050f090105090307030212030703030b04150e3d12050312090a02040603030509040b0d02100f0e040207060204061403010501080403050c032a 76
    0x80d0312121100014000c141c10000800003509601c1001c0d41030100780c540110b1442840d0084a10403600c051199540381000e00d44100009800d99a0070b040103408d01170f40455110900842d410040c09180850300c882481c00040d04007801c0794802135006613040a1131109010110107098198001d03202004074120f0b200902007901d405941052a107448464203028407d50300c654150030103a08040444035806212040c1d000003441c1c410401c1000340010500e400d01d040d21404030160285440720341601d01c0d556145a82d80c000c1030403c0041c0c151200005034007060412440c0384490300240180803c59a074140504907034480d809080c0958149119001142040001c0c4500d59501408159000341c0d40e0408444010340150301d00104281494041c1a5a50702e00260000c84d0081c400165200c1c81c0600160030003a17a00c0b103000b8501030900042107a607800411240d4400d070542802d980e5030301070100090462003203000703020305c10000320144656071003007211199021484001301ca03101040e800d03a070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 387516321 1250 387515071 387515077
    0xe0f01050711060112050d050a02100c1101060603060b03060904020d0609080310060509090c030604090c090507032003011203050d0c0c0312020c0c102d0306051008070e0109080d0207030b010b 84
    0x181c41b80d80b000c1602e0000328403a0340280310542c11441629036039411040000103032051000341d9000144800b800c6404031800b840350100130806401c003000644c0c98852628074901008290b2481000e2420028080d9190b4034052000f0941c01042042070070782c01e140c0300750300d600700f40c0d20b01103688001180800d01038002e0046a4a034880100108010744d149424401c45620080401c0e8000fa10703112480001084404500060310004070b0203d071520308903a0050494042c4025141007054900c003101e21000e050040701e0545004203810510045039040649046c410424006201498003070043c10701b651058540e903035944a503a4181c686914070042c101640626200f00c02a504800e00134129454404042d00c1d244500c0c0c1803500e48401c688107202a400c038039082d0703c001200c50451900d501d40d8035100b040041c100c02c8074070262618858500604100380200010305010041c0d0800350160f01070b14030740d402040c00100316101042080c00081d20b9844504c811a83c03440060004142901d0380415 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 387517571 1250 387516321 387516323
    0x1a1e03160903021804060b06040303030203090609030307090605070f240c0f0509040b030f0703050d27050402181c1b0614130810091a01060509040e0f01050711060112 73
    0xa9100c020f000441c05150704e2030140c011a0942d40e601960040ea45a1501910013503009460040c0c03a440e01884141c1401c1c002401b016494000b00108800c4540003819042030710424500141c65000a00d046d50031980b034100c015010082c0007901c0c00f543c4003003940810300354450480901c1042212001503450354205000c0d040480d00900086149003015031000f801030100504603512035a8481505003020300c1500265025040303141c02c01070b0039802c20040c80700c00b00c1c0c40e000094541190121221112a54051284516000110141a40d40081503d083c00a0007004a00c4080040701e0820b6241c0704400110781020b099101c13140903059418190003158000d03101d4090030344040462490b9580f255200420203850140081402c0c901000605440703943c0250015004116080030f6010300585204020300c5002500148401036000081da28109416200450300003800b040301c508090100050325003941c0b0301400c11030070319804079041411380c120000380c1d0b2a076603d4180c4036091056040f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 387518821 1250 387517571 387517579
    0x307031110021b10020102040504050c0c0615101d190501090b070b01120215030103050a020a0b0c10052e051c030c0b040627030f181a1e0316090302 65
    0x18010443e41800a2204160030192000502d072644400c002402c82d44180c800c0003038900042030f100d422080400120f6040800803a240e94a080c0740e00c009500404414010b03400c0140c6403407142ca40a8800d10070000002c001020306840184201425080308158420180041d500380400980f2407600c40031134172803c1d0088a800c4860f030910041c10174a461840c0100d80002480d403542848900b44009140a54454401f84c446900346004102864030f03290852401401c0400441600d8080040c0000030701c50500ea000c603003030765401e125a84008900e12464841e040110010b0329111040c010801600e504030780c00485880c4480348216001c0b400c100003004100803006e80b0f00400d10722040a68020300c210804079400c0c00000c0500d10300303046d1580351442600444902810143c00419078182d85000746440c011050540b2290719086050780318031103040c41000709480015801d00d048486006603030948458400c4440c8500d100c80d40200c627085105503859000c6c07103005125100c86011250018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 387520071 1250 387518821 387518863
    0x703320706050603120d0204080c0906032d01090305090a09060803030c031003060c0c06050c09010c1104110301060f090608040c0501051602040c0f03140702190c05030703111002 78
    0x180e100d4005002c081c0c11941d0611500031000c010226940041900c00f1018001580b203034506543c5070b180200b9912003e00c2902410100411030320000b61400e494414180810034449000700a1654000710b80304c41d0399203508100c03081d010b05802100502c0150000d450003841c190f0b45080100445650380030394151500200007050107000080069070304801804200400c0700d51725a290000c680d07445a00002248118000606004ca0b40c46216400307800001d83d0761808680d0030000b400800b040300001c1c011502034a000840351150360043c0030300140c4501940e038a5031254006052104004c02a20000e1040c203000b042d590300c65850180210740c01210b45190034181001034071550041c2c11403048012452031650090382d1640594145207400d9103034010b00c0e401806008081d5820074a4450b100d40070f920034820601c1d40055070500b2035001d00c402c20000040307441d05805050165000582c10320401401105001481b840e41c400308008543c40c031070b418102c050503a210150102c503031a081c1402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 387521321 1250 387520071 387520073
    0x705060c0703080c0106120b0a05060d1110021204080705030f011e0207020301090203010f06060e0303070c05040b1305010807091d0c04020c0106030f080301090b120319110307033207 80
    0x343c0140c0545410440013143c42c2d5200c0e05d411004c5c980c1c01da01a03030f800c001c580030b000034801c0324460540c01801c10f84442d8446205500d84101041c809224540910515031481c1800340c802c0c00003d0004511140030b035034850340d83c081c81b075994806000b024844e0044e84c05000d2820014448c5481050480010900c0b4058a03aa080c00035000450141e8240d522010314100680e4284141440b181c0103100008040d400c0102c003c010740345958400f4000e034020003000c1d021400e080241c030b0880e142190045203a24215000c52a131300c2080c500340c541a420280080f4101c640840c1801c1502c50160007005448480d1540c0400200300400b640704a0b00119111079460400703070001d290209051002050040c0c3c1c076a50b01510410690b8191152040400103211000360f50050708a1031108640598100002540ea0703a101e00c01d03462500c000b10b0740051001035950142e8400002c006440c4203132910303903480c0d05020b0400c06581007024000c0051007852100d4074a0050044090f01400d580c0781c1c20407000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 387522571 1250 387521321 387521333
    0x1f090b03190b0d05010f05160201020f030c071b090c021204050913021f020733081f141003110412050c060a170703051b07020a0b0f04080705060c0703 66
    0x1c50490b003038000c0390030202c1002003502402441c111001c040d100080c3c5140c429100100100198890021039004210300700c01c408031041525046110700c15002d039940668175000c088550700c812510103082401c2e00c00540c04a136036010b075441d50542c2d02611100464205020060f00c214061103511400e007101040504d205244d0000f601440a811f00f0f40f1a02164501ca40105c81c0071441070050f404981c00707005004445110303548a0400782d100200600401031140001c1030303070071200400c0103102c100142c0413880100c24111903000e01300541c007003281c40e085101c0540070f00c0350000d8002d445034600304002c184284a0106400c03007002c805801e00342407000d40d640601c1d0b038140903100341c81669050310300e550b20f14004210b03400c90b0742c440d114119601144003000caa4000c014000303051400d0f003004070034503403840b013080011002a00b40380d4440c0244001512903006070003207858038401003008070b4101400b200030303c16a201c034411500b0055440301044400e204d0700c0720441041c0c2080c1010800100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 387523821 1250 387522571 387522581
    0x11b03050d14131401062d05100522080c010f020f060c030907080c151b0a0305030a06090603021c0c031410060504150519051f090b0319 60
    0xa45200080385091500018141180c4162025082000c42d41c440034100081c1403100c010108044d0000d020640c5449500700301d120b900c0750000c822000008100a0507060100c000e006040300030244a0419681d6500030700c941c014500350322002140781901125240303d03440b07400482d108031000b011041d04039801111884002580c1d10154491581c1281c4011000e01c0307000d2046840007030840e01d0340751403028586084419400b0b04101d4011040c0280c0980354181580503a45061103a9550b802c5081c074186003000e050140c002660041c20404400c0541c01740044d8050304142000b0300c00e403078440c4155011074265220003980445c001842c03100c0713110070040603c4107034001c0b0507000815649840d900e03d1840d00082d001c200b504100c414010013611032065002070101a9400c21005040c40141a0050000d00905200e034040c1c2010038000169050400d0141c40c0c040c0942021030514214a8254005100070750040b500c2060f011540040d1141500e100b100c411f08035000e0140380d1000700004223 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 387525071 1250 387523821 387523837
    0xa2901140403020315090c06070c0e04020a08062a0909040f08090303040902030a0f0605091810020a03020706050f10140604120f1403030112110d020d080414011b0305 73
    0x40380520000015a600f846030b8907450a0154024140c1e10300190400d05000d281d05440f0710980080c400040407400403070352001620b01244462403642c41d94000604c020f8901d40c01601c3d20b00c185020000703a0100558841c600c130002e900c424462008103221401c0ca8002c0c54051034007d040500010049001d001030024440e0140003100c2c41c0210002c0803a05682c8a60001c0a03025000801d00c900b82010f03101d040b141d40481c1908200c0c0c0b908040009840d00d0340500480403500541d011041c540e5800c0c00800c0f01e20140a10840d038411009030080c1c06034014007001e441442c07609000442205c1c815038003620403015a0112002d50342080100b04049860480080e0401c0e024000482d4443c000400012550300070b20324060500b22a1900103003030460714145500c40d0708103100420502c28007403004102a0750101c1408036010500b00424103521217030304040c1d486040042d00000b4820341c48010300c180ca213052403100a0307a9900c00159108002204500e401c0c444518400012a02c07a5000e0003443d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 387526321 1250 387525071 387525107
    0x1a0d020d1103010f0e0c040b07060c0e091501030509030f04030212070315051501090308031314032b05090a02010e240c0d08131205040f0306050a2901 66
    0x9064001d5039820036001800902e80e0b010f41071140181e040901d5504c041031450817440c10b4200715420405020700d1400800140d11803440e0030025010b54481c0300408000351800713031240b5000c280b03c410802d2010030340b800b113860000031814182000c01116802d240704d5501918003880c5600784020240061010b03141030064640101c00500c00a00e070b40445005c4003000300c0c440c100002120070507543e01141505100b8607040410000e0510001d507944507056141c0110451460f042422000c5401c0c000248107000000f0b085071308a10341100c4000003da65601c0d0001d620f04801c100b01100c20a454440c0c0e00e520400306100158400d410f101e0740380b600500250181c40c0d144d14850503416148060b020810000300d4004000001000000f000c842603241046850410126441040310700d03042c05003580c400b042407500780364098011640107105501c40f0705000b50343c3e0306090005080607101e8008050070030740502e8021880c0c0c0d520f011100c00404204007194103c1006480030b19a00c0040810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 387527571 1250 387526321 387526331
    0x50103150e0f09072403062909030f0a051b0907080115051207020705150a09030204020c0a14010204151115180106140a05061309110714010c091a0d020d 67
    0x40748031103a411215040b0b003e80c26001700c0000640c00b50a0381e4140c0c00c00c00d501000803540b4030303202c0515404480fa0a4149084c550f880c45a9408a4101401c901e0748541c5441a1300c4103030100700d0f000448540c0500394441c1c0c0111520040100400e2410a840581c0020303001401440454902c07861103c0030b40040c20308a1a00798800048158004d0031a00980582c102500810090030511400b07034495004420700f6262550705000034000d581c46000c01b03401681e0100d501e02011000f040254002c98206c591407a002d02c030a0761040c003030340c000c0c0100d502c6012078941d4411418061599043d141c1c60100182c0800e02d441c43c951416080003c09411a24008042180741e5542c2803055601400301d9002c03140629220605129501c40c480d88101d000e400108083d0b8842030011711900103032a058800464070b0b6051301c08d4604940900070703000c0c0c145100702005c50a52501544461516011a256185c1075665100007003114403015180c10b94120381007160901800160b40180780241c41190009070b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 387528821 1250 387527571 387527579
    0x30304050901060804051b010c060209030a0206070b0103111005070b0402041e0c08010506040303020d0c060f15060e1e040c051e04080f030a020d05030c09040510050103150e0f0907 79
    0x78000e04207030b00c20008100d45034184024407405001d031721064400340342240f601c2c0340c0c1c840c00200b1004140501920582d400716040e44169000d2080309210b50b00100300c40e0710b0340220b040214108400380b008071804030010150407901c0c104034424403000c00301500d419003001d40a44a041d151340f0b0040c4100d81c0301c0e0352001096050040c0e0078964080341c071140310018144140e580d002c0e141d01810b0f00101d109150a100400004c0d82c0041c6085007801c181c5407040c803108071403402ca405450881d00d03111420741480410101d9080d2050500304540d070070307a85c01d100700002d20709010b4040868a03c0003403403803010b01800700314201a0801c5400c0201840c01a282c18080000d50340310402182541ca1080000101002403201c04c000da2070b4901012405185800c5010b03001958440b964038044083c00030120014629505010582d4100540580113000f10319080b1920145001940a0340e808245042002c6100010740d1020000340c40c0c80c41c0c0c2d0a00107885e142040e003000c1c0c1d0000d101d141d07540b241c02e001007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 387530071 1250 387528821 387528829
    0x5090a0905010c030506041503050c060c120a020d0e0103021c180218010f05010f0f0e01140c0706030f0908030415020c0f0109110d2316140f040203010506030403030b03030405 77
    0x107654030900d58000440e1b0408508000c26515503803090030f0643c01540b0144080345000c01c46400c2c1030411145240e49075600d6940384d0801840340c00000d0385a0000c2004100c25401040103261404c0c4c2e80e40724050000c00c500107408900902d2255600710b650254080d056030440d82c1302070440461040d00c45500c941c0c69000030704421000c403d480c1035171805801081544404d0803900080c1c8400d0820209406070300a008040071910001003040042052100c1ca00f0390050450049400d038050040d603031450300340003460b80d131180b61003440c2c002407a00ca51148280054400c0c0e50340300380d102400510b1504c8039103441c9101814640c103104415400c02c03810115690401400410b10f41c0c0c80000b0a0791580360400c02d00b040800f5603400c0c01034502e0100c00002070401003404a0680c000001889000040d2509502d0004081c000404941413a5404180345040421800d1000c5c82142c06003a440408010701041e40000e00c1032a07040381c000d10111300003c0c0281c100440b820310103400c507401e09a81b07030006 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 387531321 1250 387530071 387530081
    0x29041d120415020f0d12150306020c06090304060e040e01020f1603230a0305130b01060525080418091a090d02070501022503050708031b0d020705090a090501 69
    0x165580c032800a810403580b220603119016a801e903001506103050f180c0400b0752540581071055040019400b00403001207810751009001c00181c0b1083d1640c1501ca190860080d800401d604400b4442c4000090048500008442c1900ca0b90380c0c41d064010a00340030302014085054aa14441d5000e104a020358460807018140f10104081c900385203050034107010744240401860b4111045500c09064142944030307080740c89503030300740c41c001580b5070303619590416042d16000010443c0203081e0000500b140e111025144124001503012101400181c42040031110500d008200c02c2c01440b00f00030403d00100da49052105901021803490030940e281001d4810b00c2004480321840d01e400d0100543d002c000a2000581d02d000a14001e414000080d560311345542121543d204500c8099001c0104607075450000c581c0413080b00d00a0b501c0f80d000f141c50f07800104101d28018004441e08401c510002050320315241250090701c0030301d082c54140701c2c1d40140144213450a5880c0d402c3d080026030240301d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 387532571 1250 387531321 387531343
    0x1090602070c0902120c0d0e0604060f0617071502101b0305010905061509010509040e060916030c0608060103090f1109010936020a030b0105030129041d 67
    0x1006a07030312481d28094030301407655008510b0451040c0314408503040310403490b0303802c40c403090255500e6801d200c0a41c3d01520400c6000314050080c1c20030300c410000c90380c00c5502c104514281c207001c145e80b10008221000545d140320812603011601c1082000c8400c0d6a010518140d0710503290501580629101516134401d601c000032102c00202c0e9071040c0d0b0600ca01409010498010321441c1881ca002030380e40118001182d00e003140000d01804a030703001e642250359020b405003040c1b10b0106845801e6841d5081150708aa541c016240d0389550342d00700b28522410390f58461008004642018170413503051030000d220b00d06050390b61640038042050354080c0e40260388a8829603581d04041030500c400802c040c0c1c030400000307003009440e0a0600d2251225001040ca4518000c0b1441c1c00c216282c104030326025001e50006907960380401440340c140001070503201c040d0028030900d41c2138482061070341c00182a05610005d12507101d0a1460581c0094401801d40c000603841c02c0441024079042000b6015 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 387533821 1250 387532571 387532583
    0x22104060e0718051503030d15090e01020301031109070206071b0803010305061501050406142125050a0c0311120327070f03030c240218090402030c12030405030109 72
    0x142c841d680720f4140101d503409841c420b04d200e40e068401000c242c0d64003e12980500890721120140c40f0801d00c0d0400000a048030901400410412201103000b58002c2c042960030030b06011090441d030800b0818140520b01c66401482507585280b41191060b90700308100c18121403050480002c1032616002d94003943c09034010740403c2c00d061800d40703a002900740724241807100c01e100402040e40c22000e4501c0c07144849040c150745c1c50740310300c0203ca00305095041100c1588410284800010050040c80801d21080841441002030f40d40c15600c501070315051000050703040041000081c4100b6a05000102440c2101d404500396080040740780c02c205e07080341d5680c60207004d00c00d07074036507840403804540c1081c1c020302406820401008100101408003809102a034110801004040e0080003c12000d007109003004034012540e00029600071450070401d9042c007090541640f4100550900642e8010b00405060082e5010700011080b00f070748901070390005020010b900c0c0c4080c022a0040c0d44612 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 387535071 1250 387533821 387533849
    0x60a0b030c0702041b0f1403073603200307090218120f10090b0a0c0207080a03050301050f1c0b0901060806130c06051305210a0b0a050703022104060e07 67
    0x2c00105903410450401d4108600403403500030303411101f021243c20001c01c0ca02944880b0345040c490910303852071a0000c0909080a0000019550002d0f005080c1c9110f00034044150a204800c10507000f004105103505402c8481d04000c0c80006074014032034980c048c00c1c1031034088204400908490125240c038040c980102520000c1604240001c6507004440d18041111481c1c1ea00c070799150800041404c9405941d5912054403c0d000700403680081800404951603518036240c01021600b081c0f08890182903440c030701c00078a1811030f030000c0502d0032409540020110a88602041c020040c1446015540c3c40b80d0200b84502c2c140300251080e409040e280c8400b1149180c02000c00c201a0300500030444144614032408620a00b40011980200e900c184044400c109420801326000800046841031402c0a0100065002071512030300a50780100f2142c1d90b81c0400781d00764410440d11843c003913100c85c160005880c01201150300300e40520310008286412070140b80c0703040c1c0c1907041400d45003103503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 387536321 1250 387535071 387535121
    0x30816020102010c0c23070812040608100e0f04020109050a0303030501140108040c0b09030106092c2d070f080307060e0d120c030e1209010801090203060a0b030c070204 74
    0x90244540c00d81c0701d49443d00306072000e520b5520002d0700c906085404414101b0100b010170104102a0000d400d002007a1940c0d01486c404005165119200d65008203918100052801e501461100c1c01c8591381061200990f0783c441103e803560400034000c0f8140002e0650100b0141c40c0c06050300041c610985001030b0550604c3e080410700c51005c1d002e10b04124551003040001005254580d0071508458210394031084211b0000c1e0241985403c03144e4494503048501c600f0850313250302603120710f041825620f0101c2d44020010785904490071000d9201e203140c03400301c0344010f00500c10000d01c0c1c2d000003521f80745601c0b0340703004d94082030a6104002e03035403011520106000c1d2500c10742280c83d448a009122070710b61404007030906019101821142581e514403500201d00a812004104644d0301c15030b050400c0550309666141c0100c0811400100100000f2968500b280b00b100c4c000c03040203040c0aa050b2a204144206600040200707210000070312a60005031940e024140452200c0b41c0e03495104002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 387537571 1250 387536321 387536323
    0x1503100f060501090f03050c13090206121503010908030c090103090f0321060f06050d0e0106350c040c210906050601050307080a020c070f1205070602060c0901030b0109030816020102 80
    0x13903500100042180b4031010800250005124962400b0568080f204143c0c0d0300c0c1440c006018401d800703508000700081e102c00524518001c40c0c4a002190b8004054554076800d0500301c030307003840000380f201d4002c0000c2400102c404015112006051501050703a140c107540300405a50040411804565081c20310540b4081101c07a0300d81c1d80710070340010440d40f4a04081d40c2c070f850b10b140c403400d418040001410401c0201039000070305800d06100081c04116542d103107002c410815806140b0b409905503401d080c100040a500c41c11201e0014010700390400c00c0000c1100500b01d0003e08030034004225180c04081d151045078030141d0f10319003000512000c081c00d1020544200030080e0b41000000c03c108129a50824100398104180020041e22540d408090a00e0070065402c0340ca40032001e0700c000503000c89080c410708103c40c0300e0700a46054a65410050380c3e145815a110351241c8400d100c900c00c05c0d48070342c0c0000812441450011090790341c0b62a00312207a44032203c50301501c01002103075015560 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 387538821 1250 387537571 387537587
    0xf0411180303070b13140d0e01110703030816050c10020c0c0901050607060506221505010306030201082d15010e0a0f0302040908120708041703040b1503100f060501 72
    0x200c25800365140051542d602105600c0090104140141c40507002040c040401e28400546801204690300001c2020000e805003982c1440b450019070340d8002d000a00c800401d982003184e505489004003030300e070940504000035940403c58104481070100c9017180f40700b000300100445581c040117a9030450102c0300381c02c2418001c9814050500c440c010400d80e1a0792049403440740c0c000100107001d880381c80000e1031049001c2c9000c07416800305c058584917100c0d542d10080f044042c603c4403404141d41c810040d42a102e441c48081c0c0413a4034640005d99a03491018141c50144060603080d00e00b80e02c1d12001c881c84402900c10381e81110740c0c1c20740d01d0700550300810b0320510307184c046410780d03070a80c81c1425498960a6a00000380240c0d2107101131010000310314191000c4d01e1a03926144100e14180310000d14480d02101e05440f00511017482d01c580c452440202d9001d40c0e04444155400d6840b02030f00850001c000d400e09070144541080000800c0c210f220791040c04000314004202c603451f010005064070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 387540071 1250 387538821 387538867
    0x2030f06011e08060103110f0a080d03150905040b01120c080a03110f010b0604060f0e10180b0306010e040b1903060614062706040f080601030b070f1205060f0411 71
    0x51300c524010320205040d01e0340202c151004880d0707030059a07450400f14052821540c01440d6500c1045400800150160080d64801c0c007a0505103c1680c0d4410380c50003900c0741510060301511500d4018045040c2000c00c1203641401550b140110307a90b500c03c60340c54184003583c160002103d0505440071030000b17201d03003068078a0400003440707586804000218288994420307102130013060300c0009a024040d4003031642140c0010104c50a01c0c091010107071030080b0380180410101d00182c0046400700e00d41e81540d0040d501a555001c04010180074400100b501215a5a10410700c8400c64840708010fa640341c00385106050100340d051500e44400d003400348005446100d0b29081c40b070140341403200440c180b00c003400010034000c607000c01ca000c2103661007281c0081d04814120100412000d0b400605a03049278070a15241c099a902c070307072003100d03141110981e101c0060726110302406c82a545822040d00404010056000c0821942c00281181d01d15000368000540103c1c2d0504080e200748800032441e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 387541321 1250 387540071 387540073
    0x30b010801021918060e0a0806090601090c0f21060503010e0d02010e0d081f080607020106031a010302011e02190c030c080f030a0f0201090f0501140105010516060902030f06011e08 79
    0x140070003082100c9105002e01417101004602c42c0c1c54281e9a941d1201a802012903005660a5003040c400c0d003a141d1809000d8044580d0801c00210030a5108084030700c081d2086540e10707070010340d0704a07103220703405c2001140f080074684503840031506643c280b2480e2200c2c4540402440c0a08010340007a0a4607070170802900180c00c00ca4074401259009055107074040c0070001e000c0060910807048912801d00c0340c01074082c1b0f1055204110100d501581704200740c0e8003d00c00d6100480814200303c421074409d000090001d44c1004100e808088126020b0362106160f0050b101b0072140ea41d0800c0480c0d0300d034002502c02000805041060140b00c02a2801030817041026251400b07a0420855a0f840744c4500c10040200100403411003510139071244010740c0c2d02449502046015003080c0340030703084581c80040c006181d0000002c8640c0903804648140e419507002e0078260142e52504001014035060590b01402032030115013080340309010b0180a803c01c8481081301507000070102480c2001c035004200d507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 387542571 1250 387541321 387541337
    0x5120609070c1106070b040803041407061d0a090c1d03010522030e0924040506030d1107050a0305031201080a0c411e060702010f09030b0108010219 65
    0x41e49900041070181c1e80d8111a00400411100c0041440d52090850240c0108490f0b0140010040342200650186004800020b040c0600036801901c0d0451440780c0f4001c5600402c00d80103000858080600f115001000040056503d00c156420f4441c44690f600000f032111114020304110080c460f10000b00c1540200814600041c0240101c00c20070400100000c0300f00406007010b02c04d40c40004048006408070443c2d08000308041c44a4003000303403440e281c8091400c0e030f2000e0b0606201d804d108450090040410795002e90341a28038a00311f400c0040749025003100410f0640b640601500114443c03130040d075892014001d007518520741038200403c0ca0f08844064401300302c1c10341c0d0150030f071050000d4070380107620500b501d510309100c0c5c10403004040ca0f180c1d20701181400c40c0d070401030007100300b5941d1aa90400440b403041c2c54024600c0b0040c0d100c402441960050b5205189e404e213403441c2810200030183e107030f840346110440d00f640002c02981d00014404005a01c070000022104000e081c9401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 387543821 1250 387542571 387542581
    0x10203010302031e032107031a030a0b0c040e2e2909090a0c030501140a0e0601050405060403050105091b030303160509190f0503030f0d0b01021c05120609 68
    0x620f40740c041c09070444040910000300c1303458106000b122070781015001e0400c000040c0c2d22804024007001c41d8904c1c0070a00d0400d503948a01303400d800090045c4402405401c403c66213139925064028003a01f45020380f0b00c00d22010802000c0404401d00400000d40520307070f0340e81e01c1c8294940c2c000c05941210545074000303000704810190144629480d1440e4400140d41c580e20b0800700c100e07801941d50031540404003400f880011440c81d4807030710883c501c03540c0510003070380c07901c41091000070154201034000921042c100b1540c0203900016422000526020b0710b0242d8401c00188160030603041500d80da5920018094045410401c40071820005241000d1500b40400000e0322804024110030078520409100003905114500f2501c081034001c20103009074509080842c1c9044940c06200540051810045181d140000a50307850851008640307240406145558028241181140d03055102c0d5035004055543c410745041810b80c01c0d650317040d4950040d00c00d841c480381d030b01500341e5025107101400c0c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 387545071 1250 387543821 387543823
    0x706020c03030f0d0b060a12140106020d030207060605030a230a12081902030108010911040e1903090e0a0b01030b010e01080a021c05092a090f06010c1b0501030e01020301030203 78
    0x9070000d02800740c050726103034045401d10103080310550304c80e8030050000e801c4503c81c0d04510f404442042d00b0030308009c044422208911030030020f020708000341c0e101748154006117210340c0040440a106030008100aa994004245005070740c800480d20b001070005603084d600812000c4400455850000f003054903d1a00c904000c0b940c80c45a5200f0000004000b4620070350102d0b007003200806501d8110b40e20740c2e40e1548240202808141100c5411080ca402200b03031925000d0395a48441090103000300d0382801510b40301300031069000300c00b4006411000501c1c07407404580c0d90700c0350f54104004240d841c106000102102c0e080f030701c501c5c140942a1401c00c49030340e00001a0f640314480c50b0b40183d03036143c003e0034008420440d140e4641c1e00f1b0305100c2002280080030824049123403038004130416884440303030440401684162416000035034140041e1802c607034200442e410800605081c0403c0d18a038a50682011105c451003400b1100c0440400c401d50381441b4981981c60400001c41c11941903900107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 387546321 1250 387545071 387545077
    0x4021804030e040f1808040501020f0615090603100203090d0e06031611031b070504060e0f04080a111606020d0c03120b03070e010e060a09020408060712022205030706020c0303 77
    0x550196540d6110540316200a6201c000c004007000e000d8007801aa81c038080e02d1b95882802451b0041c003c59980980c501c00000d445801150001403003d00400d1307110034055440d81c001c0400c3e030326100780380c0f8090501240e44000c602400e01d035809400c41c1140c10202514a00b020940359003e15800c1041002c41003c5240c5400010910301d0043c001080d40b8051754a940248080c4152013140b8411408000381c0c0003503500c0485409890078001103695050f4003801100891300711000349950300000f03000800040042540a800d4208040080c1d04030300f5017460300a200c1c0070b44100c5030109400344031164041007403c110a01c649402c5440706410341d80100203000913105005100d86440344894150348c1808210b002e09030440e0144210f43e07540714a008403441c00e07503038036008616824001c00c1c94042c41c000c46090314501001425035887d12041241c80355062030180744030642c00d01904400e00d4294504100810410540e22519400c2c5810035051824560181c001d542c01019400c169803004420303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 387547571 1250 387546321 387546347
    0x1050c0613020a17010f0e01020415050d020417030703031a0f01140705060705040e010f030c030b0a06050415080f030c0d1107031212290d0c0b0a05030402180403 71
    0x1141a480140384085443d64003190032240c01024482d44d41804240158030500c10742003103080511215581c40041401c0748680c2c0100c0300c111007680401e034000b50044c0010000121514030040c906030b40c4510300210b036007603120019125000060500700703066041c0a40000f18078111424007020618400203180d0944005c0d02070306018120010b0459241d05000741e6900a8214040c0e0310716180003076009195a002d4000ca955540380d4000115100c0c0c100d81c04181929030001c043c82c5038030305580b83da0018000051001d410b4a8541c04007042c00c0d01d0300d000b9a500304030a1401035404504000703001d070400281148403a543d910503c84100c0007080011240305420a84c2480f0841c036410090b510308040c03a6400151031039000f81c0d00c003401181e01408a079445443c04e03a040040c0b004000c04841d0b075034002207000000c4c8500d07d8116071a03203800225610140d209048240d02d241d541c081d4116030350800b68500e0b0128001008010075802c00511024084000402d00680344c909a07030042c00c01000700d51 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 387548821 1250 387547571 387547591
    0x15010e040e070914091501060215090a12030218060f04090504031101020a0f1707020705060904180807020918060c0d0b220e031c0905010908030f0103060b01050c06 72
    0xa5040800406210b1040034242d580c4080c01141411140014000c00c00e803034914582c85901020780000b003407012441d058a41c558058650345142410111001c0d10151215101c0c0c0102a00c010002c1c02d041020395401d401514050f8860303120201c4a9900c0d544940914018541041080aa00310300e40450301602c1d000d10b000500e41e1070301c1c20100c80c101500d905400d0b4541c400182d0010550b08038407a5050364030703207503144141c031034100c041e01c1c00d0320009450201c00b40e44504010b014520f01030020301030f05c2001800c002a00500001547d2108860702000c0e036840c00002041c5c0294203180501a40c01000341b44800e01d110391550720a552503100401c220400349020421078a9003000d6048010f811400030426468880c00498000d81401c504516645c664a007059030086944044203840c04000c219000c008030703009683e0000c010f0700d50000100c0b0903540e19843c2d100061000b20255000310200884001e8540c1145400300484424101e5103050003420310504090200000f041640030b40250 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 387550071 1250 387548821 387548831
    0x9030a060c0522090b0d08090904050c0a09020c0124030803070e06030f091501150507020d0c06050d060602030708160c030209071205060406030201091703040f0906050915010e04 78
    0x90044940e4050400007041c1000c1d06400040750803c03154090307041d9400c4450400291441c8020440f43c034503100001808400241301c180000c0c07900510b49540940240300f52100c11900100080c2c01d122140c1002c070031039a004c100341c00c4000e0b0901c02c00000180000090b082881040e5121b000c0da20280b2004151500001c00101c0440c4141c5c2d40f40c62410b00a0f110300d031242022100d0f0070942d0001c440208013403289042001c81ca000c200440ea049a80c0250810000c1c080c113007003141d142d4002241640c10503c1c3d07800c10b0000504403d500740040c00140d0715a9200c071503505040341550719a0744206c04645c400d0006402080036103041f90045040c017034100c10744010074500401e000c1020351020303600206039410084a15000903240760185c03030a41040059603100d00401c401c039641804042e00080c03500c0003e00000c0d4801c4100445005e00f0001c80303090645d02ca80c4104a841c080e0844491141c0f1144200003505010071515000007454102141041c2c466000802c009250200035110340c3d00c1e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 387551321 1250 387550071 387550091
    0x1706010609171c05270927030304061e060f170c130c090f080601120309090e0a0303050c09131107050717060709150c0c08030705100e0309030a06 64
    0xf081250720508030900c881015022400001c1c2141e0051704407148010300401150348001034041d1a6507459000030480c05554460720756031400380260300d040040c44c031303208240d84ca58881c00300003035803042e07109820215501020f250504107040c0c60100340b411250a0540502c0390803c0d00300c0031400e46240101d807100c81e1400c1c901c00c61401d10483c030829023002c07840d0045a207a101e0f0703800201741c9074000d4560408085c0d4405032107841401d02d12800c1215000000140081c10195580075111b90003413802e1841d0944880500c811280c0e54050300c103003548604114010036030940103840e40003000410842c100103488005c1501d040703403e60014000c070b566041a05019805100383c84640e9040790480d0080d6840d92030501300001c4074410710b81c880c890000021042c911900545082c1e41c04000e0342c060003804584152903000d400c03103040304c15116284020071640030400103015083c0c002c2c2c0040048140222050040b00d12a1501e000350b60000c00039160a41c600040012100394016400580c02400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 387552571 1250 387551321 387551323
    0x304050118090f050601090b16290c1908040b04030e01111e10050709091e0e060f0f06010c02121606170709060c0f030c0203010213170601060917 64
    0x10303081002e141d40761801414110400e0b50200e07104030700c06c1c0c03038548001c0d4981c0144009401000c410700000702905101000150b080c0d00c0c0f0300354400c05581b8514a10b40610ba1151809408850b640503034800443d0a50001c01340c1c0100800d079010a0400340401c1c03c0a4072803000098000b44094280003240c440040143d200e06040c044055542c029146507071000c410b103018520240007407456501c111003050507064168441c030b034080d071999101c0b4180c9074900444000035050100101d01008407504038404558580e0055020b2690964003810042c0344c03003142124540c0e030142c40751203405108020410240d1300250460015501150340580302c490102d41e080c40c2843c85070f25100c0d0141d140000049550b0040149400c100c18210312040e142d03201c0f80215107030009072184600003044103404801090700800f03210400c81c02850b00c01c400001940101c0e0a80e071100f0010441701d100324004101915a01e0802c1e47c450400740b02a10440d45000c00003031112080c1d008551180c04048255010706034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 387553821 1250 387552571 387552617
    0x60506063613060302030606040e1c0c020303030c03010303110106051507061508030405031e1209010e0405040b150301111911100518010207050a030305071713031b0503040501 77
    0x50040014020b4007040c0800005072260348400ca000c4e125000203d1070919290242d107050344201300083c2002e04d24141203045108039004034005102007000050301588040c001140715001e000c943d0b0766254034501e8014141506000800c6a030707450548103208544d254142d0005030781c2d106d240c16032516854200100100707802c03000003e03c1d03800000c7c0000d010030044007520440e80100c09a4550b41c203140104003203035a445400c000c082d000349180d101c0038a40040500441481803501141d515403000110f8112181035600780c4207841040104507030b0783c203060720200240009600030300648544041c1146980030f00b02003d28490381c2d510306449050b100710856500120301000b140d62904818440354020b01080d1010888d030000ca00c0e80300501c00d414000c4406090b800720003400300d2003440c0c0b4201d00610016004c8020000210325007610812000d4089018090f169a003001145861801903c007990710180310562220b21071404010400100950302184c1080c00c08440701149500f108003860 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 387555071 1250 387553821 387553927
    0x60a05040b12070f0f0e100c1a01090609020418090809090c030f070801060f0c0c05040608030c0f15011802090d030215090303011214030c0a05030706050606 69
    0x80c6012500d1401d26070300000e42d0380142c0f5a52a0f4541920554038102c0c0c446010100c090041190b825802d200d5041240d00d0850340e03000351400c580a00315690383c1d041030100515090705000904401803003003c1c0c641c85110002d00740850110318043c030b0810a59100744540c0740d209103d035a103a20482c10301500104441c2c2c54407006180703004914040e0b04412840d002661140b07004d01c00380b4001000c0702d024028440c141c541c584c0364102209622541141c061201c000110360903400710f640028140c82d1405120041c1101c1002b40d920f0305641918a0700d400d0031101080003d0303010104150301c02c440c44100c541076400325030b03070609510314a82c2000f01901c1100740040d0880c5180b20904e0600d0b42c00301d000c040c003201c070b4140c3c1303071940e1254103040c1c6d903d000030301035041c2e1401c1c2e05140000051004807525180406103081d00d06100b00c001c0d50f14107092610302c00b5601c03600700103540340c00c015a6200b6680d008174103e44407400c110b001c0c0714501201c1140a000303400d168080c060003486c0440b1540405e121 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 387556321 1250 387555071 387555089
    0xc020f090705041406130b0d060e01141509010c02280b0405091e0c0c0c0d0309181104090b01210b0307140609010f0908060403021c050c0c060a0504 65
    0xc0e0501c004014442d9200c0e1042812440c0040724400d0249860402ca40c018148400d4264240b420001690700359400312800b0b1540507516000011800965102a40248072031051f80c0462510798090164078111913200c0700da603000400120b01140e0304811419580780c1c0580c0c0310441100c3c0102100300c00b0400e48045552140c4141c80056400307021001402641c40a90b440121070303e400444c600c071020790f25100c5500340792200000e85c000305608090080c8074840d10403a01d10510181c041914104004004e07000a1322741c0c4414040c1c41c1a80050001c03000907003c0c10848500c0c0d0000a00250146000d0722540b152580c1e17003400c42c1e030321801a900c035040c420000e2005003015000041d0062400b03040190090150060004601045030136001e10001d0103846031b45050006401158082d00464101051100ca0321300454030241c1049410303c15442500206115480c1864640c0c021039486102810800101b18220041e0004151b05800d0385c402d503299511113443c21015160760107950030100345 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 387557571 1250 387556321 387556339
    0x20408010204180c0f080a06030c1d0105030607091203031e0f0506010f0e1512040309090b0907020d030b06250b060d08031602032a07050108160c020f 66
    0x120040640c020012070764040700e00826442d030040010192000041048045030409050400d0a401480c8043e4001c110200000d1100d489560f14621300605400282d018042c180061040e044030080980c09480210014091441c01c4000200000f20030b00076007c8003c400454141094040d4000d9a210050a1012a40c0d81c00c10015540142002c140e9448600e00300408501ca6500946c008050401280d550410b41c41d806024403464804a03503064070509010803180c444260822003e60140344030342e0340c80322954907094441c1300b580c2106030b5841c4180c0c408014000403980014020021400030f043c08641500e01c040010300f03c1c01074060000010018041e480d401d00240240c4040480c8903d14507141504c803c014040880c1001000802e43c032130400220700111107082e8505100c082030f00c116403501c580a01c1c0c04003403984810f5400c440000c80c1c009003012080500c1404003030701d820710385095940707045a15501e9040c01185d010007030044120004046d52a408080030311002c003c1c050840c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 387558821 1250 387557571 387557579
    0xf050a0209010b12010f14150c0d0c120e06030f1302060f0a080906040f02310f05061f0e01020a0c08070608070302120a1a1203030105040c0207080a1407090204 70
    0xc0320384d0004201e015802c41c40c00021a5441600c20a40f081c0c43c422004008980b5490f82480201d81c24280d89a25040003442410005031040010441840c45a62554107442c0c21380f628600078001f031004075043c4075815502ca03100d52555016294450348000049040380c0340c07907000b0801e402c2e0f2654003a401482c001500c503581d02c034400081c804240e6954801d001950f407a00c1c056152581502e00410010b4000c030b00b6009442c00703860741c0ba060505080d461140c4100c2c070084140780c01195a806030f205880d40749001c0c0a11851180320303480b0105651940014481c0d04c00f208019140d41e2b0320400740a095180204180d01c00c00c05a49142e41c442035100c183c1d5140d00d070541c1c0e02d4400d4071507840010101c00005901d20311034029070710f0300c0810201c4560745407110745000000c1d1a000c1d0700d6490b24504d41d50240d1107652030b4030341e0400c02c400c06070145980754100310501064918042c407000555103d04820007244000040c0e014200741c1117100c26100000d160f540c58102501540b03c1003a4030300104c1c01003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 387560071 1250 387558821 387558839
    0xd0c020c0a0518130c0f09201309020c0a0206070c090b010c03080f070c0501091a0a0e03070204091a04210f05120a0e0d02010f060e01030f0f050a020901 67
    0x1284408101da41400355965581002002d810031a461105148500041042d040c2c001401c2003c46100c0e18002c50142e40701d4003c402c0d407031060342c81b00620756201e404000303020014050b50a084c1e00d007404107600e4803c0c401100d00f4866200c0c417442241e03e500003008610210203129009a483d40101130607074841c0141802c03203604000e8011005503920f443c07124a040c0d802200c85645aaa043d142e103521540c1c0c428000700d0107900248010207200241d507401c00010800e102d03d070200da2246489000b1a0110f13401449441401418882c81d146041010040e401000007a1048540e0445000c03030450b1541c41c040310320284485814030926084e109000c204508602080040d40548003000700c40c5085040c12244007480c0c07010364000c00d10130001c5480f81700b241c080300340d4071402d5504041040042040313000d1400c01c0d900119170050755114000d45c0c01d01c15501400c0020b200168040b100d650540e100c8129015008100420048606000404000d07041c03202c440d8058000b4820116503a4412003a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 387561321 1250 387560071 387560083
    0x7120320030a0e03190503070915051e0301050607080c01060e01030c090c0206060603161e050c0f030a05040b03040c0e27070608010b07060e190213090b1306020d0c02 73
    0x400050500f0701c400701003c03002040d01e032100101d070303841c00302c03510040c1098400b0741c0b001e8140410003c4a0344003142c2c120aa0111810010055440554401c013031204a92460b40e220300703030f60b2a0321040004008070742c0c03860240c500c07503504603e00941d212159020580100440d03400390302d40400c4d00c00000180080440180200c0e4003818051060f40c2184104a8980004955845c2d02c41803d001007042c0e80006080410190400d04101e0344250b404412502c00040c034814a000140d4005004005640d00b40303c07070b4802d08150030046060035000700d406441030255028200290070044005800c2c003400d00702040c003c0040d80c0c0020f00c0c80c141444402e20712600000018108812a0320511003001e002903850103c0c1c6881d921368078241d003440c0c40c0840c075921104090f10050b880d050038488412060206000b0041d1001c0048a21403980c0305000300b01c21212140f039070396031918181c0000320764001240c0b68848448442900710605500e80301c00203004606120f0030092a000d40d502c02c282d00081c0c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 387562571 1250 387561321 387561331
    0x70302220306020909090c0a410109050a08030421210f0e0f091506220512120703090e0f0105150414100c02090f04030807140712032003 60
    0x1040c0c1181c2d072182d240d250b40340400390100e5000400b218007000400c030852003500e2703842c11045400c000c80c2c901e0100e45104016040380200740342c1c42c4a646030819a001084a4000d142c140c60302c40e0003a2030420250b480c1c0c003840c420114041d501c9203561403480d01d01c910501c00980d10100940d071844003183c0c0100e000704a5190318005c038455a5904031054011002ca26a0100013010a0410403441003801104600500004681f001310710b6100290313914400540132440901d0180f000d19141c55442d0907800395243e02c81400340f041070804100010022800002e85044015015514000ca150446880358030b54049141e059211040c08a90105800e429049910458041c922040c2100080c9003600c120310900140d07003400006440d50f41810612490a1134071801d10711540b0303a040d000710b09000e00840d4114080b289180801003019000724441783c010b1205c0c5414032010303449014100503403060041c050700d00d6500901a4421602c203401113071400c1040c11810011215246805015810a541c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 387563821 1250 387562571 387562579
    0xa20031212010614070f1202120f09030106050d1208040203070504060905191109040b040f05070c03080c0930010c03092109050d0f05120c1006050105030703022203060209 75
    0x140d206032281c0c1300f100350b4100035000303240300c034002c140c654544e20f0302e200794541103003540549159100350600210182c1a400140c003d482c4d519100318040508691650b0400c0340304560045064002c618100b0a16100b0840303410940c1d100e403a9400000d00d0b00311190702c00741d8400d08050000c40d2044c0741d90015030107440c115144450495a0003605c100380c5094075080d881210040c0310a10311454650032011401002400c0000c4018110700d2180645a007102c0d05008662828640c004042c0d10030240c5902c046603650303050420325100002412499031428151044200218080b0718401d10201d8640d05004800200101c0740100000b038098001c2d04025594466200040c0c3c00d22501500c290031025400d5480c0c07014641450304100103248224020303152504032030150300c0028001c11500d10b07a10b0512901c0fa485000742e4801a28041c174a05d140ca4580d410070300c0400807a6009003c6d00d4112041703060258071f03002c0c0c0c0e01c0c80580315900c0d0f000d00f01c032070b1b08114400002d21401750300400714120152 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 387565071 1250 387563821 387563837
    0x20a170c01150302031f02091305060112021303030e01020c04050702071a0301180507090807080c1f1403090c0301110a02120a020307060f02041d01090606020a200312120106 76
    0x103a4a1140000c0f88000394040e04444502c103411350b65000c1750141c050165a00509040515005c40c4074020001c59084a20395584103110180d80c201105440300d0540003401d500d403008405450100d07200e42d1000170113000401d030005103907038020311021118003070207007003004645012500255204054451104400403441e440300d4011060407c5a041c0c46020314001103002001340d0b04401130000910000c2000200c01d0003050481c4207100b080014400c1d60024061005c2800030030204075a2000807101c3d0f00c040b2213002010b540c000380000c080d1081c2c80d0b07150fa102da44008100d403c06445001580c1e06519011181081c20444005800c819a880d4201c6400d800e4100c114009071007884021005640140020000900103030004c0e81e020b04454005800c090351840000f62003819004004810780318000148202c0901d4410b000052034948001c08021156868401c0c4000b41d50360804009650607055030465181040390500c1c0a40c0383c9a5103070b4540724001c0b503031551070080c0980c1c3c1c0020508 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 387566321 1250 387565071 387565091
    0x406090209060f010207120203030403140309040c1d0906120a050a0b0f04050a0f030c0b01080f0c0301051611011104081c0305010302060a030504030215010b070303050912070210020a170c01 83
    0x7a2006180c030f103040c0c00400310a824a221000c2e01703004104100e034103101c00c1001000042a454240e10401e404000450701ea080c0101004241c4590380c4203e410420800002c0502510050840000140c1500c01203000c0d1240004558038040311045052144102c4040e24200321001864509440c011a081d40c4c0548038038620f02580e100c1568064450303070180b40e0850101e02c0f00498102618464140403d816000c1c3e5178409890300c0076403001c3c03c1d07a045010403030175480043c4651039011008400800007031030407245141c00343c80c0b1f902c9040100901d08030741421918003540300346110041040b900303803529510317202e081da101d00b00c1c0c400f09481d10050201185a034000d01445058a80c020419402d00813044022401080024000d500710b10401d001c1c100d00e01c0314803082901074510106490b940e0f416a04026090300c41c00340c1000d0392030380912010801d29004034299808980d0496100c09601251031049141150311a0003030110b10001001e50180380000c80101000001d2100034010301e060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 387567571 1250 387566321 387566329
    0x100c0308070306150e010207140a0611100515030606031c14040b070c0609171207020612150102012003011217120a050c180907110a0f0b060312070308070302040e040609020906 77
    0x610708170903001030ac601001d20041d400b51515140440060303048074994456002d4050030750313030103071110780200070b00286450039402e0500075241c1c014010350082205a0b02e41d100c01066007004040c56080000e0b00041500c611100d1003181d008203a14001d498a03607120f0b0502e8910b00b0b003548a8080490300c2c207600000d0350350040e5903220585100002415410040721442c0e40c0c181c3c4511800c0343c1c081001c03c90308007a003480404841c01103000e660740b003c01132034880003e82100c10507100041024a40c1c071000c06a0004201203a0555141c0541030744110410302d0100c01500e050710041200d8440071a22228542340001880e102c0d801040051001d41c0b9000c0d0f00030700e00c4c45103030a0f81c1c480000180b9210301c2420110780f02600030000d490b01c003c60016451141b4100320fa411003c441300b081600d00e0f0014801e40c5055180c2040044019100c94140c134001c0e590103109803200101800b07031803c000b4000c68000c0d03040e940100030401e0140c0d100e141c02c0c43d15200503c0e20580407446042d420010808a0030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 387568821 1250 387567571 387567599
    0x50f010611070e0a0f1407030507111b0d03110303070203090f010306050d020405090c132406020a0b07140a0c03030509120d0f0615050a030b100c0308070306150e010207 74
    0x440f4002603071158031011060300c0502640f00d0035150340d545526801c031410b8858026584110f00f2690000f6083c10003080c01000c1850800000310a07500020b1108440f107030020b81d4031031490044031b5200340d6445915042e40c202c2c0c040d6403a0305540c000441001107043d004001000e003944111110080c10b21a0700c01981228028040d1030341010141c41040c0c01030801c1c0d880303503402074070100494550f580c04e980001d0311070144503101c110030f81d01c8034103038000c8440740e54407150141050401010b110f403c050300255580725841c0301518921a800c04246014000c03480880c8105061102584d5148015001742c00702030009003c40009180400140480502188503062a400d000c6414a03000e4041015805400c00c66254104aa540c0c100002c100206208050207883c1c10340b5203949a0b0300c8580058101c58500f11550b000b041c0d00b520445c0400c0d4000300b01c1c0c022a5260a201d51316442e20b5000314022300c00e5400800c80305003d07145146a01d078001100d4642414264202c901c425260403144142d54 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 387570071 1250 387568821 387568829
    0x501080a0f23011d07080402040f0204060207050a050d11130b1008090f060f0112050f030a080603060106090308030a050a0b22110708160f060603110a06051801030c0909050f01061107 80
    0x1090701c5001c150006c0c402c0301480c0c2c2040c0010404501502079400e01d00c00c99010340d00c010f0241e80310b86070800c56400e200c1500c000518007254000e1007841c4a4468440910220004a118007124080c010059030580d0110306035800213405040180f19242000e05514400e0f1307410040f9100350300000440140c005001e42c410090031002c1001a403a11141028503c0c5484089640b8041c141c0000826a4104050324440b0b00365500c036041400c2c2601403504001c8182c110030200b0650780c4050003c1100c00d0b0490360054541a40028a560360300c0d01c0500805008052640c40305004034161103e040c2002c0c01d80940ca13200f28200803d0500e03c1c440c1005104036207004055810500c9031600c0d000c0d802ca41d01102c04e00030800308d540040c45580720000c41e00a03400884800e03c200b100200c0c030f810300c50040400303428542007452a042c00c001300300140341c05544402d41010f840c1d08000070007510503038015009084000d428061030400d0750030284d10910074040d03a000140b02034068046500d00142c070714119 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 387571321 1250 387570071 387570119
    0x100207061d0a080a03020d0f0614010804051f090204021c05100608010e0a0b0a03050708060705072109050d050309030607050f0a0522030b040b0106180501080a0f2301 73
    0xb004075540d0340c4901c2d07040a004401459401d001070000e2003114000c51110881000f07000800b82c0c20201c403580c042028001503410054850708100001c0d000080025180a40250700460000b1050104002c0c011a00009401034008600000b01d0310b00d503101000d05055802c01031241d56580c101e590320080c914441c10f03001a80e04401000103045075240300c1c7d00150250130205054252101248080030075600480d01544505401c0200e00304c180104c0c1e402c040c5525200e4513020380364440d520006200d00f1407608500c2641d02240c02d65014040300c100904000d02920107804250620b240c80c1c1d0041f00300d550080c002c000010b80307000e1140c0101d9580c46520b030350b250700f440406442206c40790009a00500e04051403440030803001050300e0075000461080a00c5002480c1502d0302102c0050183e000e90103204580c40c6424801046c8004e080c1034030360030b1a14401d141c5e0b584080001074076047c620b2550f043d285c0101c2c6005030307003000d92451042c0103a4a902504e641ea58001020034441c030b031918018 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 387572571 1250 387571321 387571333
    0x61005070204090c0815100b04050f040b131d0106050621090726010b0111030d09020402070f06020a08070e01081b0c06150102010c050c0307060209010908100207061d 73
    0x10b20745036014218040c0280b03e40c618180e1510000361905500c4418904000d01e141c0c1001080341030720800d04060302d2106072040c2414034200201d21000c00d0703003054074451030711601c1100762a294032015003c0d84844031000e00001518100c9003500811040b046144c3d9428507001041c01d04050301120760920358420400f0303001c0c14565480c4050b0030050820440c42c01580c0d03000420428040d04545040d08403100c0340c10400c8990380150071500b0254040c2c1c180050b5003840000740b10040161001c0480c03103d030200700743c0414170000b0300901c90410010308803902601820300f4403050364054503402c0c0e080d481d0003280d6210030005844072024020707107a0000c2c0b86a8005401032048e084403400807403280902d541801c0592102030f00703040c800c4512484218505a07402d1140d03a090103070f4503140c0d5280c1042031030130661141e400d0301c0b4400d00f27402038551342d0005240d0b103a69110b82e0500303004110314030a54038620708001459001e503102050945026017404c0e80034841070503001d4507034440500e040007049 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 387573821 1250 387572571 387572573
    0x504110706021e0a03020a0906110703060203150310020910090b0d0b0d0602073206041b0f12020f060306030307230d230304080d0911060c0a060506100507 68
    0x30195100030703c0156401a429008828140300f00098090102c01d034802607283d6500c80401005110f569111104104442c00b101d00140400302d01c0c030041d070750041d1015a9a6490118940d07040c2801d5501c1d941501c91540508102c0020b6800b0f00328030102114640da07a4000420103c0d5640080e00036002203400411060302d080d180b03036014a030892006080040c01e00c0c1d540e251a4100d070808402900d140a074103803000006130300001822044107009214a11040103000ca46580c2e080061006042d900c00c10b04045845096981040081240c0c01034088115141c540c03c419034421140100c1c0120100e10b038058452510f0760a4030f1152101034000c5080544645401440281340c48083c07020104207400e09255400601030b200043c005030301c90300c4580f41321208900300c0200700406034803041c4c0284141700004503e0000c54010725418440070851440c2e50400415040030002c2843d800315000421080d0b220b4081500d81c1080d0207082c08016036550242400409100034028400182003002950 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 387575071 1250 387573821 387573833
    0x5060402090c03070f0c0213050403030504020406081c0804050705060309100c020727090b090f07090b0f0d050c190e060a1415070b0901060302030d0e030c0d0510050a0606030605041107 81
    0x243c0c1d8940000e023901d261000201c0e00004448040e50b040d40040d0302d032005c0009504050140000034030000d0004c1000d0045004606011101c481c101e5040001c2840410305011007045010040d2100800e42d6940c0c3c140030b41041d544000d82c101620185062140f00d15425001082070300841321200307840a8296000000c000115410303000d400c052642d504074800c04075039a00072161084440c00f000304a4030405a07640f502d001c0d0a9413002480c2b074102940040c03981c80d04009030400321803e03074003c0010300031807500030704015540c1a416000001d031401149207000354080c0108450200106c44a1071f11480305004031400c1c04d004035407141840071141c441c54244030505000300318508545c24108805030b03a440702c0c801020340e0101e103586e45a00050055103000d210a43c00000ca0782400c2300c07504040703000f003510f50083c0c80e001d41c441d4800c100c4c140148281403182680400e0100300410552400f00300d910014085070048400003072502e4808074850400b840b400c4985000c103881d041c03c260141c2e54403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 387576321 1250 387575071 387575087
    0x2030f0c010e01110c070f051c0201020a08030c120c030405070b0c0c040f0f180b0601030b0d0501020a0807020c06040f0e06060c070602010c080a0203010b031611070305060402090c03070f 82
    0x122400d640c2c5005400c2010803e02c5030341d152110071494184e541901c40600f914000c06504401c00b8550014030821442e6141c081182184a0300a98210740d090741d400140d0412003c44400303000000004200b18003295068000c115440030000039101a4a40c850f41900d04c0c00225402840d0742e0003000107014070344903040500343e0380040c1c0007107800c0b4202100104007034035812280c3c2c002e5140c42d0151448070700b000b80594031080e034500b00100c6a01fa1140c0305c01d00c8941000c1d14040c10700d6a903090000441d2503610050301071039080b500039907580b00c0203200201071a50842d420b07001070040300c40d21075692801104884c225002c4ca14600486401c010125a81e20307005818241e02102c1000300511512044c0b00320002000306800004202d04008405002200000c15900c819441080180142c0e08101c059940008445001c4c101d903110003138007911400d420411480b1176210340c01001040001c001038003071181c0e1081c0c0d2144070035111400e40090354041500d42c00041040224540c0070b9912480780 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 387577571 1250 387576321 387576337
    0xc0403020d030c170f1c0b0607140312011401091505071709220b06040b1c110310082b1809050c070516030507050d1109090d1e02030f 59
    0x902d40700b100c5070036100c0310107a0105c1c41e100503e0002003050400b494240c0c40030500525500d105016a188501c0019880e21480c90001c0c01c4148901110044070000c1060340d100f00c80b060103003002d03035860b1101a1701200c0e4001090303001802a28020072150305144856001e0401919864249201030f40c60360300c400c54100d00789051a1003406a401d071640c5024519010150201001298140d81c5070130b901941c6c03454050f01d018040400042081041e1a0116083d003000c0e040000e601003580c81900d00900b00f50803103020302071400f10500082c1008105608101c51901c0200c0300c0310395811040b10145e06070020709072013409604417800d80c402e00458442e1451204403905d01720407601c440500084803400d80c0c0c0c00c24014408100c600070090204030400d030508507054186001460343d92016920245400703154003405c02410070408000c035004c08051005002031029110b8a03242841076550001c40c105000010340752106402010320040c580d000c0c009030382d8040d40c9007156612a0400c59072207044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 387578821 1250 387577571 387577583
    0xf08061501050d0b280819030807080702010b0a0b250c060c02060d090c0e06120705040b030f0f0c012304030f08070f03080109061707090c0207080604030e03060c0403020d030c 77
    0x5105c007240300e240740b2541e03105082051046400e00040d00c1c50034003258484ca0019251010080101303070040019507000ca02403601c0c0d941541ea0007402c074050900139001d1500842140c0d4007050205844020b089020340c0c040e60225240d100c004401055042014085c1900c0c0e0246001d11003076210b03240b00c0c5269400038090720301c1c01c5c8405241000b12801c0c100300341c0712000351050a10000546d490700c81d40004040b2a01760b2940e4244488544910182c4601c0d0312480d51160f02071403a85080c0281c02803880c1c00400c1c0c81921142c20049511860400d6142c2d000a0001030b102640194540c81001c01c01c2044030701500785030840d030716031048000a010564440784140140c400250082c5800114584070399520105940f4020401050b980940c00108040c00705c0d030103c00c04100c0015842040354807100012036007d068240c00da0400006411554042c001c01042106040c1c101000c03080e8010180c003110b907a55030b43c0c01211024082e6000095108451021110100e4030400401340e81d2030240b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 387580071 1250 387578821 387578839
    0x10121802330c070305070909030824041109190614030c090406090b0411160f02060f0429030408090f12030c0a020405180303060d03050408010203010f08061501050d0b 73
    0x25000c1c4402e4102c0c100a030450b510a1a007071080000038400c000c0184015142130007452a036a0340035080030401001c100100a15480c0f02c18140500c41c03041c08c0103100030f031040000f442009220304a96101650050250b1f00d00121540300040d0300070003404640d000ea84046481004409160042d40041d0054a0818051203040c070b0a44d140e00c205c0c00181115640022000c3d00c61041c4019140c4040c1041361001041c0501d80b070816010580ca2030031680280740411424072840090100c2c015a841c4c46600d0601140200784103c1da101814060009003910140e807403808682110f5030301c4111401850084c0c01c1c49019a242460b0080c0403080e03800a2a003902038140845443c60354200c61460845644000032020960500e0712130590400c04208110b640090300c4c0b40c0c1161340740300c00741c00c00e40581104a0f44c0c0f418944294142d50103005044000d42d92540e548030100d82c0000d583c05090a40d0052002040c0006003c40115050b0001a181e10307080c240c04044500040c48c1c24604c994008201d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 387581321 1250 387580071 387580159
    0x3050f0c0c040c0e030c09090622060221011a041a0d141503070308041a0d05041b0b030f040305250b2703030415060510121802 56
    0xd4010742001107069030b52001d4800004c8200342c606800e00307225601942c0414248540c800001c00d4050b03000461031010f40785200d030501c2540b04c410f807200026185600c08a8041406182541d01c2c1500300034601603148241d0700c0c0c00010580080141269441140400003000f01d41c1c0f00d030740386100c034030002d9a0090030b00062075600800c3c0c5041c1160050034412890400094140514441046042c00e070000c2c4051400d50762480c2c2d092049020790b590780140400d5401c10580068210340c002c0c03040c00303010b1005d810585005030510302e4641c030304441c01c0b40700c08010841c14604015240724443c85065031013140ca4544042d070b115449603c9180a50b18031460101a040c4005120401c0d14884d000d00c800601d0034285001d0004a85c19014840aa030544107a214060000640b9001908418004400301501200d00300825a540c0025005040c0700c3e1105540c030303001000102008500141807045003004c0c001070020b6000c0001c000d500284c0f002240401c2c43703072007130f02800e07000075001d0300800241c42c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 387582571 1250 387581321 387581329
    0xa1a0904030e0a06020d1d0d02100e0108070509030c12012009040b0307080307060b040b0901140a050108010f0e0c0906030c13080316060c200c0102070f0303050f0c0c 73
    0x8480507030120302802600140d50038a281d0000c001d10040c07005e41400340d000500140910003544a00c920320503801031145080d52084107400e02d4650081c4848410403600300054620054211414041494580010411b80c020300071200002c2c4024003411001030800d04000703040c0c1c86070b20300c10741035941c502607003445c1841480d0041000000c80d0317a15881e8403502081006030307400b5400850081d00a14010448840c00105031044982d00c0700340070456030561030114008104002003240d03c43c005a00000300b0400800303c0112440e4141c0e401c04505446d48010f4603486800e118800380e8504624040020500803081a90420005e8043e1486c046050000400c190002c0c1d4004401000001c0c02142488501d181c440051081c4c0003d1800c059516003010300000e100e240c040c0c04142c0303480400b03504900c1060030030400441103130607040100c80500203aa0b1089203c144a000d0306c1500f0b804180c40c549090801c0c122941981c1e901c2c50101e2001c6013980a40003249004024842d0202925017945c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 387583821 1250 387582571 387582589
    0x30b0702011514091003050c060d020705010207080703170705030703180203060403020c1e010c030507060209090f01050a301a010b071502030402010f0e011413091d03030a1a 76
    0x152100e40c801849204004016910001070103080484006036006c200041c0d000ca5441c041034422501c4544915555003220b0181c810050014800d5200180490802070120b02030300c030682c0a0b5072501c2c001040241c51801c0d4140c1940e041c0e010500500020300b18034401d81100c08592000710704c5139003122180d40480d20707104d400d940440241c0c03c440154680c0f81044c0b080503800c0031003717000186208176030001034440565020b020b8204070300003481d0801d1110744d804803141003130083c00f950030520b40f01491070320b082020b00505205080c5031000041200d4644244030400030200b510f00d0001962040c900422128900111111800420600380e08041182a103000300b4003000030301d6882c04980fa00c2c41c503006210750600e41d40b40c414028000543d070311840148000d00c0c13078100311624800140050754885030081d07440b80c2100f40012002c030210000202e40c0121440300000b400000d0309110050a662046280d488007984180000b581d9205142c00080c8000307039001d141888041040041155a8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 387585071 1250 387583821 387583829
    0x9031303320a021810062607120e0c090a0b2403040c0609080a14010e030706150602011e0c03060504050f10240e040f020a0f1b0c030b07020115 63
    0x20b00001048410760030082d11a2100c059001841c41261400c00b19814410400d030013000308000d5100f40074941340614040c21007045011804c1014a03140044c0020310100c82c0c15240e0a00e84c1c20b0400c00030b5504000180416000e80003031001c00d240d52030542d0708008091000c0e12903844100348040301d84040342c0032401d81c0e4441e84070301d81d59681d181c1800e00001a20455012801300981464100700c070fa040420780500081c0d114aa428a8441c0032002c0340c00750122240c2400c0d00d0000083d01c01c10403105600580c11001817103500004190349100690880d591484220005400448002c0b002c0810f984050300704151410700081254542e030104045400c111000408102040244040804001e032400000c2c07a2510094000e4921940c01e9003e190701040c49500340020740b4640c105680d900d400004200012005c115210300c1e039410b00401d040c0c0c500e241400822000c00580c0c045000c2c00800c8030200f03422100791240c0e1881c5030358a404455000382440119561248000034052260345048020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 387586321 1250 387585071 387585073
    0x3020303010e061f0c0c0503060c0d140106020303070f0201090b0a1a040c020c06070c05060f07030f090b1822060503010e0f1009170309060106080903130332 69
    0x3960601c0d00c585041000503140c107226099024540b0b21000c080c084800d0140454a810f600e18821880d040d14500025006180c0c140684020024450b903001d004e0700300c95100c00c00500c010460050502000b5100380142d00042e001000054913240c02402e800c0c5550444d0320002413800801e40710740b60651810340e0303003046c0591200025007082d00c049403101200c4208403000c014180c51401e0181d9a800440d4045000d50f002292003024021706201900082002500e066603030f160302c1d80007240d6948119800c074045403400c551401064400c2c1b480d00c05489400c11440c0c9406429900d202e40d0701c1e00f8a030000d43c0000e40b13401d002c62591401060210380d090703074180854680d003018209801e4903540080140c16500c002c10807424100002026068445154000121401039050041040301c4450440411403000418011011800112241220305550b50985a0780f03410010a840c0d01ca540755580101920110074004507180c0340e10790103681a009090a180b801c48010401e40d071030382034201411 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 387587571 1250 387586321 387586327
    0x3140d0c120c021603030e130e010b03070e040b1906150f0e030a0305120a18110103060e01030f03030b0609040f060f0504090b13020102031b0604051c05040608190504030203 76
    0x50070500d8000c0c00d80004160003e02444010040b0b6200361403c9448080c0400051543c40f1040361618401d4501501c0545014400400c02441c080c0c0a0141498024001d126106000807a1a511703d0958025a0302031410b103916202d105100b044c01901c01c41c0d111040c0d5594100003485180e0700700c0e480d00c4000c20b032035003800c0c0340120f038000c0c00f108418044540250030014074075001a9002c0100c81d007001401c4440240f03600d034209408002d102c0c84143e03048600c444aa218207001c4810b41100d818042640c040c01403d4807401450308001e8203200c0203000c11076901c1c4e18800a80250010700314482c0c040c01d002d0030010000c000800750307501c614a6080d0035a460f0030510661000104e06070152005540602c0100540d40c0d5003020750000820042d020041c88200300110ba2007401211540c5d1095424202c0340c5296800450b1283c1c0182c800301d4641c410700c00000c80080510082c90072948581d1101400d0034940117041e901040010300080e205194042c000c40c51001c0303031252070b000f82d00903402191 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 387588821 1250 387587571 387587597
    0x5090c03100501062102040504060605130506160201050306010c1b06030e010605030a0b0a060306110c01051312180807080619110d090204150b3403140d0c 68
    0x10070a00d0032911008000e00389030050101e90f402180c3e80c1c07030f203207150240300c0c02c43c140c00c0040340002d005903009941e0007820090006006580030300074166401c0440440d0003001d0b038600c02c1104511500b000d80d003035900c02c0c455000c05913000380c0c051681f2030010b061100724108596134003050810301e29040e01501c214071606100d199454450441080400b20082183c1410000005d80d00c1c1854900182030a212400103140201c1039041140111360268051040205200420500d0740185010205335803078000010345440a00000341581500140c452800341075901c41103405001c85485a00c0e91070041340c0000f0300e01800c00a11000740700c2803029150720b0421218815407100201030499100c0d040540795800160018211440398400020000b0710f50f00600c041030161102051140d8021000d41c00002c030080f441000f05a503840503441c1a02c05889041c480c251050740321100031840c00d10910480010380152202c0d910300c40100380540c2400e0b211469034040da01c480074031200086026060364 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 387589928 1107 387588821 387588823
    0x71203051207090311010e210a050303090106030b0903040806150a08030d050405010f09110d030c08030129040825091404020f0927030d05090c03 64
    0x1031000303140c10400070f80004403510041d100c15104100b4000991702c29482102d8034900208401e1000301c0b0842e040c040524034072200c10051080d1114540426800c001540c460000c807000400c0700e504600d0101110707040640010358951081c0300c00d1000f13400100710294001d80c6901c90f2074501d04030f80002030054100381e004141c14040068139000c05421b41d0040e07031059018000034401843c04099610072038a1000c00909071004000c6480000d2a001c15102105402841e214040400307076114005107034000c0e4846c1020f4015103000002029040c0030325003450030180341041c2024030300b508194684640f07030010300300c820801d04515284132144410314003800040b407080161203018140c421562a05a6045c2d1044280441910f800e1601801e958841d42d44401e8000c02c40090f0079000e1400c800d051080c03100d41c08140305d40001592a0311030345200da11400014421131003000300385 = true := by decide +kernel

theorem cover : BRFrame.Cov 387410071 387589928 := by
  have h0 := BRFrame.cov_init 387410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 387410071 ≤ n) (h2 : n < 387589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
