-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3741
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:33:08.794848+00:00
-- url     : https://prove2.me/submissions/4117102b-d5b5-42c2-b9fc-09007690acaf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 672661870 ≤ n < 672841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 672663120 1250 672661870 672661877
    0x2060615041a040e0109020405041407120903180b0307020d0c050a2901030506090d020304051513030c08060703110903210f0c0d030b0901080c01080406021215010f020c01 75
    0x1030414070018182e0396841c540c0320120005000000711100014007280c02402040c800695031400c060603c0290384102c400303810000c0c0710406118040380d02c401c41080d41c03880c0c00c0f40042c822100745401c6640005c05050000d851094584c046600307185400250b015a00740d800702c4400003800502554464200d49c070140c5103401c59003004003c607141c00401082c4040c0c40c5441032081046a81c1542100420f0700305407031640c0f1040c01c002d10b00d40204030003610130f0702074001541028500340002308052422214403144410100b0354800203940126810b01070341c2e00c0b03106504e86545420510303903154011500c00002034240443d003000e6841c00300841e15256409009002041101c2a86c00100980b043c00b501c84000100719515562040300044c0980c40b0300c94015080c20841d0714002429503e184c7c42240c8561b00707100c0100040b000002d00b00d00b03c2d80c07007070070081380c1a6142d007050380003400303070841d07051180c0412800c10049141661059190300400d07200d21058110380b078402c0365550394003d40706020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 672664370 1250 672663120 672663127
    0xa14011a0d02090112020d0605010e0613090209030a020d03081b0403110f12030f0414030d120e0c220c02060601020307030309050c040c08150301112a060c040602060615 74
    0x614800d074000f0a1031103c18180b410b54000c2020000301280d0001d2003004c200799407030906010075a40030742103080700b40e004c03240c503810700184010b03a14428106100e5005c82c50f500050001803070314248201044542c00803e800344250083c1000340442e0300c101c40030080440d501c0c0c11002ea2052100a64050320780000203541206a41000e00507400301da440c0c01d69101c8000d01a008080c13030200014000c0440c43c0310160303160f43c6402d01c99002c2c41c54034002c41d48250414011011125440780c1c00c03100303005a1120104039486c0f44007203141400082c0b900c40b078221000c4815240c05050418490850300c050311010400745a5200c2c04130307160380c42a269140107030020004100443d2090700301440380341c0914103840500e400100000c1c1203603002a094400305041000b00003500c514502d2202800ba03040e0700038083d2150012201c0d009201e85208a01c114205040300704042da001c50001c04a07543d8070040301d1240c04d20140d400304031b8025206460052050000003401c40c188803100c0d48400790301c549110305 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 672665620 1250 672664370 672664387
    0x30408070b0403022a04060b0a05091e04322203050d050a051605070b040f0516030516051212072a03060608010203040309030b0c0409050a14011a 64
    0x41007405003041c0d0440c4503002134141c0340f4000480441078944a415010142c007082410722095400c2503110b200320103018001e40385865009811120022811600201010b04000903d00c8100010399050f81107031812000951200b400f11498902d40409041c034041001c41c4001d41c0604081198803240301c81440011076040340400380407864503071080c20441c0c02e01c00b00c0703204101140d130103c6540300841d403500f040c0034001f00d0007000207000104600d0003615000d1551030b00c0c2c0c00c0c031a0140c40102038491007080c1006000007401b00c20349105555001d03030349a5030340741081580c84c14030040b98003401c10441d00001d0a8900070804251030441740014010700040203146071081c0d00125803e440885007107010504101c41510020301000e8196480c50505085040c64001c4402d19003050106071310400511002c030360400d90000c1225030013405010f0341e58607030714209038601907640300c2c2100705d05102c00e01040c0b505503001955464095405180c45030b036a04000d140480c0c3d1076401e1400d02d941004641c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 672666870 1250 672665620 672665633
    0x12040b090a2403050601020a0605090606120601030c060c03051b0705190302010905040c03090b0405100507090e060d02150a081b0a21110c06180319082a03070e040203040807 76
    0x35880081401507c8c580d10590311250140c99080314001956003201c0704001151038500307103800000440d03400400b504c1d811a0303519848040030340206801c2c4000c5450708002c041c4280b084071102c41c0760604046407030181c00001c1e6900c10490150601c600002d4008183e00a000f50040044940513929407641d40e00d05014000185494a640ca01b05600d469904000c1144941040d004030f12500080c110b00c0c4024203034500711103000d40b1290070410070803001c00c000040c04003425080340c003c84c2c0070302c107202d6180b001900c030501c0340704100031946000c1044070819030000666441610309040506425a00501303441c0c15201d550802c13000b28880303900c0c0b4188183c0c0f101030784070000c5180200103000045c0c40c0c03c000980c2c2014a01000680c845802c001e100c0c0c0300361301d0b120300308070000b001075041100c4a60541c92003a01c0b00048010040d5000014400c8050a41050392004283d400031030310210512046060317502c106c414201080d50011035908906080c402c070ba11840c0c1055210341001c8413991440d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 672668120 1250 672666870 672666881
    0x41a0f011b0501050f040b2208031009050a0204080f0a0201140309010e070b07020310090305030105010c030509040c03060302091e060402031302100518030705060d020c12040b090a2403 81
    0x40c0e151155038001c800004100b4803406010340c80328903054015140c6072170f00410001c002428803c0c42c3c8410035001038019845003d1002c0590b000c2e01207a01c950707400c3c5041c0390480c0b00d42e2040060506160174041050400d60042c425565130005139881c601c02264265624140c0920003400201e05980c070151780903101c000741d80c10000510002c680c2c0350b41c40d825145008070701d8124620071600010880110318080200c0d0f160031403054024015850325881c05012800305104881c103001c41c50300c4450415203d241113814a0134001d00801c111003030760074028001d2542e404228003412084c00410f0010020100d003554101c01c6a41d000c80ba0341d5a5018000a50405040041c0702140e9003002d500594490508015100047d80c5054071017116403a07a02103154020711080c01380e00112410b1255403960741c1101c0c00011210009a580d00601150034138110078541c0c10822480041008254088814000e00c110f83c401c441c0324400341c0d256030b07200000e03104c00c80c00c5082000e0b050f6488030040e03020b074024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 672669370 1250 672668120 672668147
    0x31c09050a080a0207051806010806130e01060b030f07051e090619080a110909060f1c0b0709060e03030901030c2109050d080621070f0311041a0f01 65
    0x41d10261005a41e50301c40940100c219840581c11414040c0b00d01d0038440044500340c030000c0744035940c90603c030700007a200301c901901003030041c5031620550035142c0b03150700f04951160009d002042078696540c44c5845c1c4e504191400d617140c440341008546994401d009880108a6515101111400b01c00010149601a8000980021051052034064085030412040c14045911fa84400749810000c210480704002004e01010350148401c02080e2917007581ea82c0d0001050711104401c001107170028011b01e80d21411200c2c2582501c1c244030401074106c600c64014046a2260604941c40301800d0302c60190a00c242d5406a00a00000e0a250f02ca03401581d403e00e060300385508680160524158205201c01003181c8042e201c603003600411a00b086400000402c92401985d01e0138000006000034540e003414808040d2480d40441c84400c05000480080215400c2c1c03100840c0d070303803820104040007082c40d0381c4550f252816007240312407011410500140014a11b01e00360060340300556107c6500c504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 672670620 1250 672669370 672669373
    0x10302100c0c0e1e15100302042603040807230102060c03240405010f081603080403020909100c111501050a0611010905030c16090603150f0e2d031c0905 67
    0x40704c0d2070740c807000d82a140215100c040c80c4002d00c420000380900034040204420406104010400412640f252000c4182c4071022801c0030855002d408580b46000326000402ea0340181c604c006030900b0252051441c101040d002c680b114500c040069842c1c200459510b1814442000040c1d008880d43c01600125070458800203041002c0202160456409070070a15581c801800b0a2060060410211800b514600b056840c003505550b0350b4100e80c01103210090050100c600440e40d259414400405000417070700c07003001144191500188400d8100c10b901c00d280c011010100800c440b404007a6059982c06096506c1d25460070b10200d0b207a0720a852001402c0d5a51060000090780520090040c0c060b02c10062a4052408804040320049a40015146860b03c5820000507a0340507403c0c10703901845c0f40c00076614101102000140846041c60500ba0140c0c0b03409036030700b0609261a02c0e88924a04c00300203032135200c548482c3c2d207104050a604c500d107011055203041300c165802c98a81c0921440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 672671870 1250 672670620 672670651
    0xf070f020105070506040c230609120f01020a030b0a080f1b180408030f0c160605041109090708071406031b1b030307020118110405150d030503010302100c0c0e 70
    0x4a5041c1000006d40e02124900e09841041200103403100c0103000c1c0d141074200780c2000340030320000a25680301d0291024010b001011456241c044c003407000d8549000302000035541d0f8060303190003d00404030100028803d03c0c581e0008a5001c0c00024800027084038440100124050b44c0741911622140040c15035001d00c408180240c1c120b81e10070f4a900451007105842c3d203d0901c00020303040840001e01e680b0401c1000e00c1034003155558000c03141c4404c1c0c4c002500098944550502c08080040b01c1440c80e000a580d0090007a51100001c0c07000480d0440415500710139200c20ba003003080b01501050607480300d014008a904000216468010440d0444000340b46c503c40041a0852028000d00241c9681002c002c00ca000c039028011300b1601040b64003d030801040e2030344c5140d108800844514000e507a80c100061707102c0a0201461400c20006000451118072032400810980c02400b0407401000004031050a46018070302c01242c039a031145850844d10708024000081c0640201042413000201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 672673120 1250 672671870 672671873
    0x30b1f080604091b090506030c040c0203030109231302120601061202090418080414220b0a050a091509140106080c220816210204090b010801140108030f070f02010507 73
    0x2030b02c860010295885c02040a2400c80101420320401041c143e0056051459030704240364040222419180ba40a000482c0c0b03958030b40001a80b18419141b411a40809050103000c411010105d5089031003101c0b86020304500c8034581d0346600b004c0c070903032010803e1402080202e150540107003841000c0a80300052250b0400c8078a282401041001e07a4111070000381441070802000c180c0f040903c00b643e8113240540000c1030882c4801141055106041d0340c0c21908586507244070043c002410010718009000d0b4481c1d5040d0001c0c1440500d00d800d480d00001e00085c0300307045005c0c2030b84d484003800909040b40c2c600355084c0c40085008080e144404400c010306004161541c5484188a00c9500d003409414189140546001b01903039101104040c40c0c1400c0000e03050701e0103250617010040500100c820401d10115020344010000100804000700000c101d041c1c055110694100c0081042085070340d03245e0b5000e440e407123039001c40707030446000300640c4000c5501034461703408091040c50800d01d444643d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 672674370 1250 672673120 672673163
    0x4021b070909051905100902030a02090109020310082a13020712090602010b030c121024050d050a02060a050408030703020d0216061b050109050d030b1f08060409 71
    0x110340000070415518075880c0d050181c100a8440c5010000146806000f19030700c840c0c1d61071920021403454241c0710220b0308219103041c00f18000c0507074060300c0003a0950b120000d81d0080e4008440015034400c0030701c400980e4920004902084c08800d110a103910180c1020060140502c0c0703105c190811a40c00c8000c540325003600c001c001042c0216505031102112400c0142000320340d40c005002c683c180110360708180c3d0301180014013804d003110100741c003a1500700c5850038002407071803490710645841445003240e4081040d03041020b00c1c20382c680e03010540360300402c1104114541c1c080c041c5e90012070284010b0600780b0080c404011f42e8200070f0705060b900d804a0b8503583c010304080b00140c01440c000b46000342c0412a010140480280380b0380c5540c14075100a00c040d00311811500100e0b1061031244c07e021082d40601c11030398002c3d0030b9602603040241c0150281201088860103400d10b29a080c42101c00e40907440c28881907507580002944030030003004040c0500200c181e8425040d44d00b1846004213 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 672675620 1250 672674370 672674383
    0xa020906030c12070509061603021c02060103021503040302030f0a0915030e070b1e0d020c01050f010f1517190c030617010516110307060c050306120106080c04021b 72
    0x145014082d41d8620100d98107140f850044e0603407041c060240421802507403882c0a6492480c0c00030901701c1e0209407030804a02c0c0c20343d01500c40c401c0d9100c600200d904a6408510b00d41601c0c0251000100c141c200a0746140b0717440100c0307018006810501525890b040400000c04801a8901e080c034050343c0c13544401c2c4103142c032200c81c40d03010a40e00c203c010000c080520185d00200441d03564142014103003c40c000400004680204050310002144044081543d05aa141c0248030b002008203180081c1f030564003103403e0013860520500b03c3c00020b8541c0403244030040b508502d941e62541109a208011204100a00101106330080d40841030514280c400d194250f4034581e00441e825140000c0b5031142e000344a44059903034100004c202c900b103000e20996070303107844a140041c3e007208014203036401d50041d840010200741c2010451580541d001000d540641030445040e00e1440c1d81c101d2031401c84d0a180300e00200d0b6000240d40c0413461a00c0c0d80500519510402c44802509200342400e0130a81d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 672676870 1250 672675620 672675631
    0xa02011b0f2f03070503034602071502070918140c040e0c0607020f0a0305070306021911120d0e10091101090e1f051002060f060117010306050a02090603 67
    0x41020403074054145490b1940100c0b0003043e4040d10346a410000880d4076445212084c6c00011003810103150f102401494100c0041d501013810350843e042c0411980464007403001540040c0321f40880420f045c181104500d41c3d050243e00201b215515160030900580f402002991000c017034200854003044c02418080141c0c4440c80c06006030003a0141000111041c0a05072a402d41c02442c0801e45511200f00726543e803a01140e09002c00e4940000099412085410041c8a8001c0300300020070130802e038015144544803418111300c908241c003000c8900c1207051001c1251a8000c1a81c44054030540009002102296201192181429040a05c1c0c0105c1c0d00c1640300d190340d00c9002c0010300052030445208a80d0902c0c08841c2d80346071030801c0f41240d070040c00c00c54001d25000ea09101800460188100920014129a40d01c041544011b500e640301144d80032841c00800c00090241c0d0310a208034605101080c400c4010b0b642552541c00c01000002d010100c255820409410b041d5503003805988601c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 672678120 1250 672676870 672676913
    0xb060c0a0507060305090d020601030b0606071509110f060a0c17120f070306060203040e060a030606060804150608100504060b030106030803091209210106030b0a020c0f0a02011b0f 79
    0x940f4264000741100c00050100029030050041d94200b6a80420081c1c1182c0d0405418036064942c140098a81d01ca480d400520310f40e07410383d42d44448000c0da0001c4a086008040400c00c0a004005219800c6405880f0b20361194003040010323560350080c01c58465850044109900342950085200784c164019083d20280c2503815040241c51000c2014048d0b10210603d8280483e52030a10061358a0080c2e010f1a400c03e880140020842d4443d0342c00c96005540110051040310350740c207000b520040054400b0365440c9600000404900042c2c042c0404847c00b0b0802030942080000e0000700400c0003420880710181c0b15440d05956580034041e01e40514020810750b9503a0034000412882c024002420b14840c1e60144102d4529036503481501c040d00681d1141417200404a103010340c010203254000400550341d40050041041a60340034081030b0842c101162011402040041e42c0d55801002c005c1c00101003501c2c5170b401404415104071260301c541d28180d40840203035a0004026113100700030702035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 672679370 1250 672678120 672678133
    0x6031a130204150f12020a170a0203060414010f0e06190605060c0c09090105040b07050c0a06110406020d030509031b0f06250e01140319150e06060f04090b060c0a05 72
    0x40000b041303001c030005c100e440304038401030f0a150b010860141c4648a0002d41604102c100c1d14004014040680300d182d0040940c2c2542c9064604880c018080505202030b6610f00034030543d2220303291140010070300c650b034001c120a64421100351521051841030079242910b9002c005035948031200a890000500300181649a080360203001003080010031410480c2c0c100030a000100380c291009542103e01484c002d6550300005403541d14040f50042c0090407e1b1404501ca1a4030120070090030555085030309a420400c8411002c40584200340d40000c001d4008214998549132414464020501030f078080d43c070b42c98401d880c03c5080510483d0a284291681001031003140e080d003c070101c424070701d42012040c11400c140003d080703002c0c3c4546030225020001c0402c8850a041c0f1107000140380998003480003103442c2c6801c620000843c42111f9190803840007042141c80d048007956800300a0034440f1b42418a4081240702601e03089805e2900302808202031011041d061095075803441c05840200b52 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 672680620 1250 672679370 672679379
    0x16080a03180b040b0411060703030b12010c0e040f060302030a0602090a0504140601030e0c0409140106060509010503130c050a09022101120201180f0609170106031a13020415 76
    0xa41e440044100104450125001d00207410001540d81061300650150007642d200d10709010b80180c10102d40e68484400310b00d00c0201a4141c00c100c8182000f951003800c0c8103103000040303003a03501d940e0860300841d006064120550810307030b014602284c9812800b00b40c0c10707600c1c1c011a06141e00c80d00c0546a0940000e4080c02c10f0400742038004c02480b0a940402c44e050700008640228038015000c03e04143e1103d60104104104010b90b291040c0010000c21524407607244c0807100b07034140000103c10394200180010580e003c1e4090365045a010703110945940d85d401109401c511038108125103818040d10045420380f100358940b0068040c1c4480180e441200d4026058100086100e805401080d00c0051000340624035000c03413106d0742801e040d400c050400460074081d03001c9801010702d01e1004100081c070359a0000715101110040182c507440c5180c903041e03003800d80e1500d00002d41150030a601c81d039483c8040445055114910042d0046507100707607070004050380c2d44549a0140030750500410712 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 672681870 1250 672680620 672680627
    0x2010e0d09031415040b07090f050105030f060a050312040815041106130321030b12031c0204240801060f09032904030e0a0f03170c0a1203051b030f01140616080a 71
    0x30107050089d01e1842c02915160000b8800d21000b404916030207148000b04e00e00d9180e8044000141c9001400c1d00d2000300b04001080141e04540300305803080c810000e81e140001070a039034003405030b0340201c100346224a100d024400c44d40c1c84200090303100340e01071800102090001d200f80c002c40a110044007051821998024165560000980e100d00b0640c0b0360601c442000000b201c110482c9144031034946240c886110000b802180e2154a404648981ca0f1b20390340e05200081900075001c0e00c40000d83c0c2d0f00e88400700c40900c6501c4982002c584402e00034408a90300c030841440d03ca8500f02203002d00d0321100945030b00203000390307003c501180088103008290f03e01459520098142e54120109031440d6841390b11040d45034200000c1c084200048040b20b07600c084c000011802c0e003112900c0d240541c03002c0010000d0000702c1d450260002807414820300940d40001f103a000744000d00c85180d26034201200d408099249442030355000300d0801c1800390802c81c0c5010f10300698064112103841d41905032026 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 672683120 1250 672681870 672681887
    0x80f0a081501020102190806010c06020c010204050126130c09090323132c28020a02030d36050c01080405070303050c01020904050103050a0302010e0d09031415040b07 73
    0x1d030659005004280701c188506000407001c100b0351a000c2007a4075a8001a80e00242029002d0500307800041e41c0c0e503c4500540050080751420391f0346d04e1090b81041c4802000369080c1404c18034649840d0040750341000120340c2c850b840ca000d203c0350380e4a142d40300b0801d03040780d11344e08046001c1041c40d00520900a90302d48102e03100c17494482445d14144611240c5d0a44e40c03101d000b1000c100c2d00c030001e0f00c0384ac840e800240040c40440f42c134a45c0a6410308044814481040c00900f012200c8140694800e0131580c0c025124401026001103080c524107942190152150125907815110b680801214624800704041841c8503098507149488241d403c00c40d00b810540304e0b0190501840d0710600c0009600014141d046a4141c82d040b51503440d914091030291103510700c400d1b071050a000000c824000c01240041886d4840d40081240c0a00060a641c03124008141040031031211801040031445a022110300d040e10407054829040b60050f15024102c401d4500340d54101da031108120003c0c3d046080d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 672684370 1250 672683120 672683161
    0x10f05010614033d0b0708032202031903120506060415030219031b020106030c0b0c03040b2814030a0c030e0708011a0406080316080f0a08 61
    0x910040d8101200600490089200c12441800003c000b80780081d41011600300c00c0318488186001010200f084190f284014079085980300440324001202c02075501264800c5507c07105072411952181000c483c1c00c03441456282d000c188202c003580041c1d406225280040c0d800c20420203001604d410000d01d90382100c11400002858002400410fa8848086c0c5e800c40e00f002030000600d12640000710003a0154403c0224810312403103800c00295019040300a40c0410800c9070000100781001c00c038241d900710720010300780c402c05c20310a0240d02c8003000185441c1a100084a160542e02d05070074199a1041483d55554486145443d20540d250b002d070100030a480c0c5803900c43c0f441b40c0161041c41e440040e041405103135850708188180350186c0c21460b0140b01000550b2103480d541c2d1002c42c040d120302c5402c0101c409080c00c10310039074981032003070300185c40c1d00000460518580320840c1c001c4d440050415920031005120403043d4041060040c9104030181d5500301050500000005d01907044010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 672685620 1250 672684370 672684401
    0xf060509090715120510030605090303190b0d020307030803010801050f071403060f030d030e0d0507081204050a0813081c0e21100e1902010f08041b06030b0301 70
    0x6202007000c00003070072426241030f040503801c10010100d081d903003a41c000130710090b2241444108050190740c9841e1900305d034050042408a680c502040755101d00c0111020b200c000c02403001511041490b034412052050080c00c014110000d0f07400283c034002c49a80121806900000140000341c2c084c01640e8100c0506282c9110301d05041102802c03014041e517401c603040d0008000600316903244141c800760f400300601651154140603e008001c1c004e20b2903046500e20071910b06100840c494030403584c60942144e082810407a2000648000100141041c0c0d80e42c89000d8185c004564500c008160b40741e01d06c90b445403058034001019061080e007040d07040301000c5801c1191103542d00304801c1c20100c5003c4910940c00030030f0501022600c50b41c49e0540c5c06910070445000401039050b44840c0082d0035581c1281c01c3c448007038808406144c4902c400034009492920441c2002d03024000c1250058031610b81c440c0520402c040d0b2880f000f600381c4c0100e000079240d004a01c0c0d1404d0038841d8018005000c03a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 672686870 1250 672685620 672685639
    0x2040f08070b07030e030a15022d091201020910021e12042705070207050f060306010f1209021c0b0f16050702040b130509070803192a0302010f0605 65
    0x86408085003e080d1018040c4800103079034001c45c0e5028001e420500b030340800c0c00341c83c006412400200940152032442c6040386100d011001e50b0644e20080c24203041e242e4062403420380b0a0301440074020b0f2103900c006283d134092203c050300343c0c0c07132544a9921a80039402441482d01c0150303002ca064910000019260308a01c641015050200f0308441c16104142c10b0282030300251548015400d9003645200304043c03500c400e20165950119a420446600716034001e035401440d41000042d2000b44c1d00640401d4411407c2080781d1b01507841541024249040080c14170000e070007041d00004401c00d10350300c10f14000c06032020803408651007604105141800c2402c3e142608012001d480e00751004414040d02260172411036070741340c0000d00107200140400344003207551110b0f24040c11042d0760340c4159014490002c120a0000003e8402c441211000b40894601c00c0c101900c58054140c00c00c1c0c241c5660703484d0340300310f000030480c6130041600c00c0d4000a00000ea0451140440342c00d46c0050340f05a1400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 672688120 1250 672686870 672686879
    0x506040c1e05040902030a0b1527040b040f0f0615090e0c0906030c0d0807030306050603042609040218010917101104080601140f0402042d09020c0102040f0807 70
    0x810040d429100b05640004c2c2002d05400020b241841c114402041d1145403010070031007a041c0b00d000299650142d41d80c10ba0a6404034400c1c240303a000400700c3c0d82d0b6610200006000c01c005607210764225000d20542d810032a06a01c44a00e4402412000d80e9403030785a500c9842e0000d00b08207004000d04103048200103485402c24455191110701d001507115560401c04244e142c0d605100c141d0100070000c02409450400e0300d010a05a007240c0c409030042450000d00059070308005041320312a0307034414801c0a807418150301142c105e09103240c80e820144400d00c04400c0c00c0c1c45510040c503e80c0d0082c8020075243c1301c190300040c1b0940e076a4011014030f00c85040090103008000421f00d40c000e200100229904107159a0407000b03000d036a210300050b00c211800000c0d203034448a46544110401e40e801001989800e05100581c841d500ca101200080c1d0794038203150009c031a000011200d040b101000c000d07541d41c0104010303600540d58040e01658000f4040007006841d815940c01001ca1030054500a481e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 672689370 1250 672688120 672688169
    0x7030504030c0219080f010f060618030b041a040b0906100f030605091c08070324050409032d2006060d0c091802040f0e07050f0303160506040c 63
    0x29044001d00449220070707042c102c29942988013000e084550100c50040711040702460181000454881e03226203040c00c042421342c0f059400d0022201c20b20464514a0301d140d46008440c5002041601c50200280301d2031000200104201e00036401419800070030700b00041950300302200a0012820300f44c500c1c42c20000300c003000c91070b01e08480e0810000a1280d42301380170b45062280301c02c3d070ba90560000e0103101f480150007030343c40c42c0030302c015030b0302001442615600082916000324600c8107040c14030f0000c01951400d07400501a540c800d00d020442c007105404801044001c3d2600c00d0050480000081d00d503031740c41100115203140b4080b0802500709825006516510040c01640c012894010320340709004d480103800f0018024450104549626003200071404109010b080b0720035810301255201d15851802040d500e600001d0240803035524020400400d40c0b84c6078401038050006000307180840e681503c40107070300750240001e0621841c092a02e0359030341040d07811007a02410b9600a00592a60 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 672690620 1250 672689370 672689387
    0xf0106020c0d021c0f0c140102120903100510061704080406030b030a050d05041703070b15040e100605010e0105031b1303080a030606020c0f0607020603041e030e03060703050403 78
    0x1d00b940c01c80d41ca00d0280c00030403101c40ca2141c00c070581d605941c6a410400103145105034005000303500d52000b042d103540740186031034204011680107034000705410300c144000c00010401c512008044131400d280703010040c0180d4108950034461000c28443c10000950000720140340c5240b00104e144251500d80e64200c4903000794050303030042580d640c03d000c1c0070b92070412113005c10b942c00c102158840321841d10010166801400b60150100c00880c01c2d005000c400001d4130801a4000803208a80e03913102818049050801c0d601c542c015281d851064071024240a9000a8008e00601040b01424a4005003035810b4034440e89040107000c10400100d04120b510312441c002c0703081e90b0282d84000d0340003c0380c014001600003400e59900002d20060080d0140e0060017100d80310340985028100c068100101d105450701a550003900422199005180460003564814843d0b1140500c2100340a8051209800403000724046a04000c100245180401815034405240d150511480c64180d0f0010700d00403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 672691870 1250 672690620 672690643
    0x40605040315020403231c02250b07060e1203040b0a09030c0b0108150f0c0a1b0c1508010e150913050d02030403060e011b05070303060e0c0904050f010602 68
    0x2c0d03440c05008400c945503011600116000307190764131400030085036108400c86c2c010500507144a680c0c0440d01546003401500c00c91940c5401030020025483c107421a00409403040701101d650101001c215100000007602025010b4100007a0b05052101d07250300d008506560840044014810000010660450190700052005010802c4969441d00f038cd010011100000d008003c1c0c80008140f40d000020242c40d142c0c00c000022800b501e030b01c00c00d641500300c203840c001c444200c10004804d03040d00518209420641c0c0c2c944c035128014443d240e025034030056400c540444442900c1005074241e0003140c15003d4013417551110680d013402011704c84403422440e2144d0040000c1c41c00503840c0d602e5040c010f075000e03802006491001c0301c42c2c80d00075140e600501044450b9840c00000c00183c6405106061205070381511b40e001e0b60034401400d0f01ca0750041d000c201d040586500c8045458048680060300900d941c611898407000a0810401603c00044c460302495215600400c140303030340005d100e9200c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 672693120 1250 672691870 672691883
    0x3070611280807030306030f08030a05070f02030414060d050a02090909070503191b060905120c181008030a020307021002190611070f0b06030d020a030203090114040e0412020f030406050403 83
    0x80f4014070303007030307016026541c0050040d401c0c0042c818140048040218411180d85108000d1943d80250aa80d07250455001100685c011b000610500d40a00740300e6002d004002d02142c201610098201c096400466184403000c0d000b080e10102d42c1416001c80e81c1105118010b03140c082d080801080da10900030304140e42c050b200522000902c05007101d008583c1441c122201c503259107451000c0c0c044001403084a01949051075158041d0b14082584482d20700000c288001d0340d00da02c01038400c404006000d5803805003145100098070001000200700c18070058000d5600e8113402d004004010884681241c1590440e55500342c23290038690f40a01d8203544040005082000115812880d014a00004045642e000b0b05207003440a083c400a200384801c03000c071015000e100f00c0480e112403c0d0130009000d40d006100c0c0d100990b014940d0741d4074203c0740035409030400d40c0d183c4242c110801c0030f5605484880d000e0524131051a030500c05103d00c944510001c41c50b162503d4002802845107100c042c040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 672694370 1250 672693120 672693127
    0x30f030703061706090d0e090604020a050c0601030b1b0403230c04020408031b16060f3006270905030c060c0c0c03010b0d060903020a02030706112808 66
    0x141c066846240a0180c1031a820201c0340c030035010603a5100f080c0c40078565441042d00c40c0f04101c0c40f0f10484061b03034001078010780090f1150418003001c2d40000c203000080c0602401010800082004664001e5000b00c4d4200141d0420001044580507141c0418609180402042c800f083c015078469100450504000d070a04445d1812541040da60b141415031150000500040102000016081540e018039000c1100140c44000c02c0c0d071041682c4841c1900004480d00304091070240c1d0000b60826403034240b078811401800c511718184079074fc800083e0000110f440b101c02060982c440c4101601410b40c00c140203032070003407000d410388100b400310744402c58442d10a0b00c00c0040c14020380d9034102141080303850b03a007440140883c694006460100e00351250299071000b0789414043c03203c81090142caa2501c000e001e0300c0780c1c405043d9081c81503055126207038440b001620304018640043c04c1c40c3c6c0d107010910801505140c10300c0c0d42480c242001c4c60700780302c058000040010000708084e51140080d40e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 672695620 1250 672694370 672694381
    0x3070e060723070509100f08071508222a051c06061505070213061a030c0c0601150f0801030206121e040501140c03131502091519090305030f03 63
    0x3420300f10350042d076000342c852428010540d8400c4e090000b40d442c0030241c1100030b070f15862881d41d40c8002e0f1080e681000c440302c160184d018010b58841e50442100c40c94101000000480041075003892070003256581c8501200414402000fa043c514025000f00900c104618280c00219000c04048010700c00881c1c600003c4104025540106d0050002c440207800e1000c466001600e250040507080c0d0103019080100e01d540a403130710503481a87c02401001c410314075520804400d40e040100001c0f1004c4d02042141d02e040d208112a074001c181c1007e021031181e1031600014200b00d1101c0607041802224001880140e0300c0d0782c01d0380c0d48020860103500c100d6544201d070900c0110f4800b4a21000700c00d40080c8002e0000c10b401134005810f0840854229444428440305070b03210454042d2007000c401b84001d40010b801d44102c42e13198614131009800e05032030000040020304940010840400f0004015410560342842d9494110b03203400c24445503442c42e181d0f03603261b2095003106807141500100054 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 672696870 1250 672695620 672695623
    0x40e060603060d06050718120b010503030703052a030315130c0203191b0b06190501020d0c081c0b150a120b0301061d070311190503151503070e060723 66
    0x80404518011000140c1e80d023810308821240380a0a654090908001052a0800108035004190700d9503829181162610440e1f074090780701941080d1002c103010400310000001c10240d0b02135540c14200e0311407480c2103810480d4164803828104085400c0840d1284a81d80100a451205042d80c4141e140410107910846191506000354a0a01d138206000e00c01d02011605040c891403041d40c581e0030f580482d504007040550588a140d0041c0d00c404590410148100a101002881041013600340400b40405621501201c0050318425603070349510390180c50305130a003419006541001e0f07032070107407501c100801708403806c3d142c41303040c40d01c070140c078152520250b00c410010b00041c0c601d1043c40303078840090b480400050301c01e000064102012001c4c00d03603406080f1246035150880380c00351944004429038203038100500f0300d280a0076004c2c6800c59070300d81060201181000d4011f0796034a11303012202800e40d030f80303088d6218003454051180d1380c00200d5000d00300303013003a5290301c044000d80301000d901d9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 672698120 1250 672696870 672696887
    0x30a020c03040e01080d0804170703020a080c0f070e0f06090912030c0304021e0619090b0c1c0201060f0302040902040231060804020307090b030f12040e060603060d060507 75
    0x10840307031100040006885110310303811810b1301c1600060f0384040b40d54110072038031058140c1e00608514200d8400c0d440d00180d080051400511900580c0c0300820980c40310340107500486070481443d008400c0071024010144942c0028107240c1002102c54101012098281c520040240f0b006001d00004651030060411189861402d419052640c81c5811114402d45403c20341d001c9008086010008071048503075001d5454019000e414582444402c185100c0d0841e452020f1509100d0003010200c0c1890141006010b0006684d00802d403814103200403112a00c1c1b2a05080704691521406000600103041e41c0350440350102e0740843e04981d103000040080c85135020030f80320380442400700e601e10061401c130621247c1c600b000e40d110140d91040d041d10051401c440c0254140c00c19002808490020b921a0404500c09400c03503000030208640523240404988013520701070404542041700c03204001200750f201c0303401d0b9425415424000003159a030300621800400716a140d1002904031b610031010ba = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 672699370 1250 672698120 672698137
    0x30c0316060806181302090a051e1e0103081308031201090c17270f060c0a0207050907021005010614120403120f0b030d050a0c0327080d0f1112030a02 66
    0x142c8217410203c4400d02070002802049024a81c03407800a100ca0504d8484c1501c030ba00749659a0080311544800081e04040c0146503580061140300285141001100090b003e0341c464001103540f0150f45840c90409415030f8011403040d4402c001c0e0180a00d60490040c3c1140c2d459040414400720801c41a00d0b5500c40e9600441050290380170403a01448043d815040c0c0c6100c40342d035400c1d84104800036501c6400c042c49a4055510010200707038450340100042103ca00d881c415191201c0c3c0f50310010741c1c08002a203641d00164000c1f0300180c001c00c02403240c03034010300729410003407901e00750241e048a040c002c150f00c0302c1003040b080c0d001400341800f030011048640f842602c10409041c2d0103444070001c0006c404514081d02c6000340040e4201c0c0a0360807a0a0500e0720f481d00088005541e4045540b00000e54542e001c1c40c480b40030307030702050382d0100300302d00074004a401412410083d054010070f6607a1000d103080410542c2204031a00791404108030000c01c10515083d0b640b81e5a1041c4d1b0000b91190014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 672700620 1250 672699370 672699409
    0x7020103020f0a02010b1206090d0c0206040b0a020610062102032e0303030b040207110d151a0f010c02150a050f0412021c08032202040903030605030c0316060806 71
    0x240f885440740d0650103440882811586681c1e8540d00840255540c0b0049400c2c480a034000161181514024410308244600c0105070500c2c1c02e44451500c0c082c2d0300010a4500580d225406000b0305013421405000941700501e400d0316001c1c0c8420381464845080f00d00000c00e20340c0000410030b0003060034845440c40c01c00c031118821a0702003101c140c4502e061444168002032400241c0c104624050007120341054101b01c00415070141038007041a40310944400305c1e001c00781080d0000000c0098094000302403031f8800c00c220b44014010034882142021404181040085910f100059540b075050807402070a01343c01d01d40b1035129000036143d03807050800810b51640042000900c023121010280d032014402c0c0d901c0b1074203a1100301c00c80300302012000c00401001c003d20004480202c1042002c8103042002002d0049407495004242292012401600000e17143c2ca4280102e05007004201309107442a070080004865080d01e440c4c0b000a14010b050402c0290004a09141e032a820b500952152480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 672701870 1250 672700620 672700627
    0x305070b130c03030810061d220f090c06030207050d1b0f050303040c0b1c050a020403080c010c0e030c0a14060c06070906030b060f1e04080a1a060a0f060507020103020f 74
    0x4e0240c920340c8122010b014286c0004000b18406102e81c04252504041000462403141c0b44030400a500006d0080030843c170603481409008403003240075803144803049460001c2c1c0301d15503042103018480150001810b150040020704001980060030b00418811840c00c9400201003001c100030181c41c10b440030303040d021503448820a004000c030045020358820206400640e58406000300d40d030140705515070030780a0304502102d00440a802030340e84120011401440c1c81c0e1240d40d0140705030024500204e00d81c0d9102c1c01011090340100128a580b60110002d126510042001a00d03616080c081c038143c1c4007040d0b0001285460304400d0300c54501a1005490403480c00324401010100140710740790009042840008590800070f0440704520880040149000800790a400808940c4914240842401c00000171036641c00e003c1181a03510a22000e03070b0211074100071540520026003034510a001c1400100451500e0446010885203181042603c9405d6400160300a004614500e01c5003403000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 672703120 1250 672701870 672701873
    0x30c0708010213060207080304090e070e0109020d2007060207060b061c18080433170a05090c10050c370302070b1308010212180a0305070b130c03 64
    0x10b4000d4142600d18502020240d40d4943c0104e84c1e030505403040050f2500200320500101015030443e00c010000d0384125011240d0f43e48186070800070992108680c0caa000c0f07400380320403240e806145020040d000d070910342240e02160704c034043e00c0b4210b001400d256000684030100309050308130307604910008000644031a0622810108061110b2090106070303d40441548030f01e81c100c401d035010360740080503282402e0403c2e40c130100c0705030f003c1c031014a241ea00d03000300d00113402d000c04c0d41d08002d40380b41d540c2042c0c50900d15640c4400d0310081d280504060400f020000b0b0910001020100410212810407035030910810690781d5100b052000c0c0c0a5000d0b001c6400038401d1092025840700800c81c0c4061399401d8200e155200410b03080c200100142c01c003071810011008907801070030802d8203205400041a40d122000760072a401002c40114400350501000150740450800c440c1d8011103101418a92660350b4005010388030703070200200b0300048100820002000003210524280d8015054a011038071b9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 672704370 1250 672703120 672703123
    0x1101020f0912060c0306090403030e07030c06230d090f0f0506150402070b06040c110a1a280f0204080a150e0304062001090516031a190e030c0708 64
    0x196a40101c001e41c501c40d0b103550340003414510074841c3d604002e040d034888800700412100007030b006504254968003000c50740c40e014804070000f14800c0c22600301d241e00d030000142840015045550001038102a125401000e4204030703940c0148941c00000c0700d890624041e10250240030015010903000f070019400c21100103202030003484100c40004051460b04c00300001da202d428070081c0f02e500f0a00c00304009091640155a0500b0340d41002400b02c20503804052400c01990420784042c200c0004103034058041411040d00500300b0740d0900b141600b08800300b00490300b00428000030325070b6001110307030000280e41903c000d00040401c0d01c815012a0030302828201c0c1c0110040344d841d10b0419820b0300d0041c0002143d08480041d11601d003041100d1030080c0000c4480c80914006540b00c060a0001030301c280062441031b00c2070f05414010710708605002200c3da5001034046110b404020910201e87c454181040d00b1103018003001c0340622407580c1ca10306501510246240902c41c4000100d00c0c00340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 672705620 1250 672704370 672704377
    0x7150201110d200304031e021c05130b0403080319021c02031009060510030e030f07030c0b06040203070813020f04181502040e06100221071a0c090f011101020f 70
    0x254403d140403015004140400c81c03000340c9009010a240080f08800d00c0030f102c11601e1210020300540b080040e1107041081c80e00e0070311601e44005100000c220108194012000001c7d18800c0001c905040c11917490118074400035181264505030001c078144c1d2840e9680480300111001b002041004680101c000c01940054a400d01c11362a6800003040b1580d883c0701300b0040741d00007003401085411405054000300401c45050100340004c10941c2e000424460007014254400e58841d00c981c04107080c02400b4504c05010641306500400900204035440403006d03802c5060500200074918003440083c646d170741070204080c6c1081c1000d04160301142141c540d40c3d2030600030590340312552181c01040080317204501604103181000c00204d4110f0802076034130181e00e40d0a004035021100c0e51512460200e490703802c500700740240000c1c082c00b08041d11040030091444911040c5039030400d007101e110302d07000e154805c0f4062820b004603030a5581c8100f010550749080e00c2c008656806240000e00c85551 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 672706870 1250 672705620 672705641
    0x4090608010e0c1302090109050a030521032a09030607050c0f010b060a2604050607031802012003070c170c030d02100504151409010f0e07150201110d 66
    0x14a050b400d040c101078085114940c0420003421003408000400c00c0710300031340000c54000e042084040e004159134a844600380e010390300400080140c041000b080d0100d05d20385640b02d80140000740240b00d03000303405140302e0036a000b110f860301c03c1c4034841e244d019034540941080260316100e900d0038803103443d0b003010003440d0000c000c0d01980c0303111944076a510b082e2107695101e541c021000304940c044a5114400c07800580c1038486524101e40136130a940c0ca005d0200380c3d0191101d402200074400002c3c1c241c42808084100c01c2000301000384035400180003812000d044644032260300b80142d60340300c1d05008803480d141d400012861369540314040c1902c10051004c6040c442e214650812003103180004e0101029200c07903000b00030740700c0a02032400141102074012110345005107103620030302030a80200d40c0c01c10002c8804c40041e14044d4580ad003540c0003046106202841c2c08d00c811108000032a034070f800c0e070b00404554081041308003822401030000c105210f110600205449210340c0d0303580c10109400c0e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 672708120 1250 672706870 672706873
    0x5130b180a060503070609150507170306030705041a151b010e0c041b0c060212041101080c1c0914150106090602010c09151e0e0306010b070218041704090608 69
    0x458a500038144c1d103285c02e010b00c1011520820040154140f51000c0e446a003009140440c03d04400b030342d802440000c1c01c1c03100014144040104520750074200205c9006141c100c1e01413001010021034464151541c0d2010750241031520101000160000c0860703205031012004d0040c810b02c0100c00038000c00c00d001c40d00140d17005e0301c0400b85461909002d0008154406450740c0d0f00190b2040007a180c001c4881e00440c2e075035402b400210766816101940c01d2041d07006040fa0030012a9100004140481c018a03201c40d480080c054000305507014400382c030541c4003050000940c0e0540d0304001101d4075240c8002d0380c0f10702c100c6038401c04020096020714100e424644030340c0c1c5819103492040c0d007030720354044074540001d4803c40c3c02c00c403500c500c14181072800d1040c10304400341e001e01d144044070105d07040448000300743d04420354465801c08105860041a404440c2402d0524aa0000b03032010840182142a584a1400f2034103001136445d1112300e00d03140030095640d40d5038851502c0054000c0e4414070009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 672709370 1250 672708120 672708131
    0x40908030c04090b0d021804030e10030605030f01090506070e240a26150d050111030709050a21080c06090618060402030d0320160210090f05130b180a 66
    0xa805d00c210300980507503000303010240140c0b288084071000180100280c0030468903842240c01c5440b40301200b0204001554041219810207041c03602d0302c0320802105031160700d8032041002103017000c42d40702e40000c1a440c0c6881443e440c0c0740011800814028103070a00d070583d00c01d000140230150001c000c1607006031250b4204514072003905c0380510060000718401d80402c4001401d030300031040340d070909200c000c06e03243c45080a034071401e084404440d41055031010000501620541040c100300c000c2c03000711014140c407802c2013403005c0303030086071501c00340480c90301032188080006000c00d803031901c24814101c0d1205d142c4001c84a5845d041035914420700c0381c00800c2c003250140c0c0800c94601c50f580283c01443c0700c0440da4001c4004150600008880c1d071800c08101c204410400020b150b9190070345e03115800c4a01c0e03801004403003a03500c2c0400040c040200410403460904103900c1084880482d81011200c00260010015015956480f43d0103501440c00c84456512174103018007820600004004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 672710620 1250 672709370 672709391
    0xf02070c0e0f07120914010603020a12260405060c073f051006080601080d0207050d11030a020406060c05010e120d02090312030f1608010b09040209040908030c0409 72
    0x420030ba40e405040750400c0c00250103680038880c161803509642c0740020740c07103440741c03202c01e0341141030003049009035141c0d81c1c00c105504d04500040040c20701c01305041d60011a580d01c460501c0b402003980441e1410056041100d46124400d0310b0040c040541010355513426180040d031199401d00494404580301c0080b800c80e01c0c5520840041301e0000803400f1031030f01114851500703d40068004540a01c03c94140603486c800f0790203054002e2209000a200d994100001c10703003882c0c000c5400c1421076025440c01c000315940d002c110b81e00303a80c010440411100415011a007480000400690407504200000800ca6809006480314a020344020801015100f01441c1c543d8a00c0d400e003052680c0c03c0c030100101100b0f540c020042044000e00311007610541d15003c4200380c00440300c018614140324104030743c0505c120f041c2400500c503481c0c080c046604040f0400502c0c020704000600550340404d01d8001a1920303401000c01c0350708503a019403607140001e80f1101c1c9500500a44a040d804c01c0c9003800e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 672711870 1250 672710620 672710639
    0x180f050312150f01051303080d0617010c0801052413060e0a080303071101090f06141008120c0316050c01030e12030a050c0d020a18050d12080601050d0f02070c 70
    0x110310030030042407807100354188401105c0c1c5801c2040d245081320040e440000000314460b000381801c052a400100300e503494407281030181c0c02d0048241d44070303906010445600b640d110580303606603581100c42d0a136074a994085040412140f0744a00c04100001596004028134a01c00004a600745c1d039074040c18001903030130b0003038070701e082d108038005a03000b800425038050103010498030741c1c60300c0c00002a041c0e5464858261298a50304183d8800d55115a0107841102244019038003030452110f51031034600c0d18000030740e98a02d40301045002040428a031700c90000900848442c501200d03540c0e0880c07101c508200f6250315162481c140842d281c00e01a1080c1100484c41070380503c600202c0074150360300d070a0380b00043c000040004842090401c80d0141d07814440c40901386107a007650f2141a4540c00c859850700715100d039009607108601403802c04002405c0d01044240700180d0b858008040d40351440166514020145c1001500e810a100e0130b602c03d60f07650181c0740c028001c1c0c1d442c0441e55510311108 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 672713120 1250 672711870 672711901
    0x1c060608060907031a040203090f03040b040302040506181303050d0c020f0f010e03160201020f15040204061403030d151d1f0803120415090b06130c0e0103180f050312 73
    0x1d1700c000366110700222618081d40510780c44000002514202c040a10303880741160302a0304075002c071000119090040d404e02d4407a15601000c19180000c0b560038078500da242c81140201004a5030307025594041c00c15105500790b44d42e00490303a034144403040d4100c070040d4586140000c2c070882482022180440c0f0704c014001c00703244190310b101551802c0c41d80400110116040f40099041d841804174078091100100005000305092410300f101d0790616204100039614107600c10000584041d290030501d40e0040111031035202c908500282d41c42482c0001c20601d04c456110444030940c41544103001e001d081d420714032a140d46c03020074002c002540000c9104078464024600079610030700c02081408214140e1035005406811804002d19600c8884000d46170a101d086883c0e03244034084c41214140354803070b1441c0d106004404d00030030305094401044a142c44000302d04240d19000344008601d00001d40150b0541c10404883d4000160304020f03990358881050040e10880001c002003a00c0c4951082 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 672714370 1250 672713120 672713141
    0x50d0f17040f0e0c0f03070906020d050301031a040f0b180c090c03010303080a06090614010f17270d050702150406020a171b06190b090c1c06060806090703 68
    0xb90200141030044104101400401d80114080104000004171410901540c450b9055960f0840900c1c1001c0009061984d40300255041c05828401840021381d546403045442041d91540300150350340b400c011000c5100300c44080c1c0b05401580c01e21445400345451680158134800c1181d0890103c034003880030541d0105c4104202c1e080c140014000284112019070f04064100e80200d4055140d82c280c2c030440301d240d400b820006a9000c2c2c03441e241d5811582c04510150b80c0d003000c20400c04004800d1040382d1000b00050020b0b484801c10000c06400114050146001c12003190310801120307a001d020350b8861141a0f05c05d40b02d0000d0511040c00090031202030b03e82950103015407160a80e19050301c5400a0f0003a5201402400001d202503504400c803421002c9520080c080e0782408103000408114003101d00510b941410a8090304e5140e18248503000a0000030259545107080c4c080748940c1071401e55110100e081940c00542d1951245086002d48021100c0ea49079842c1c0c050f0550848000c4180e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 672715620 1250 672714370 672714389
    0x31b03023904111312030f0206090d120905070902041d0103050a02011d030624041808030727060201050609240f060a090f080313180204050d0f1704 65
    0x1503495980c1443d03040000001145450142410505501c4034100441078200c0c00b02e01455050007014075500820302148240c69002a0800c3e04001c040c00d03403108609c24448040c0b22030103500d0b8400f802942d021f1103036a0b030401300ba9100141c031581e079003000c0d46c01803144080719070a80485143d0142012400c80c100c2c0e45c01401409203800d60307401583c5180c00d02003c880b20710242d20424035103490510140703102d000c4041e0340890305003180100c180f007000030301d4007107000b81e1074030369850030014a440b032882d881500030000c0c81d2642e548010403281000d44001c8a10011111045044c1703403090140c502c001d88109070000e110a46e2202c00780301c0344c100700702e81c002c0c40e00c0319801030314004995003080c0801181c00a0a5608508120008030f0496032064807a01c000034103109081189080941d81100500003820155190141460118005d54264004e0030030b98030300c000c1043c230002c190740d046800821010f000c0c0e0440750240d08255a000c00400303416100001742078182e120300b060b10303400c42e0244e8a0740c20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 672716870 1250 672715620 672715723
    0x2c03030708060d06020408031b1209010c0c05040e0f01060608150d02210d020f07030b070807110a0b06131e02090d05101b020303010b090409031b0302 66
    0x2214012070140c00d1981151503090000c010402c0b5000600c0a031018100440d07451603540c680000040c11040303c42166000808024154103d10007100c0030400300740307082040c1044900f80086000a945d0109030b201c0e107020006004040085035a100100c1080020440a07035910740a0321201800c0b00c0244c68409220540442490070902c856042d500141c21003d50703910944540903103000c552851502035008070b81d0820b106a040220721601981c001c060066070b85507594440f41c940f030251010781440000000100300074420301240603c00314000c101c4225034142d0038449902401964800c0c0034140038402d165100c080c50081c2c110602e810000ea0060160061842d4029080b40f0800c03580259102c0002c00411382c02c10054a14903600400010514400800d544030403000700505030954000384010807c0048100a40b04050016240845c440c07a86140c200c8803640700c06c48814000c0703800c140c3c280526600040503102048014102c0c01e88015248002102c0000741c0680c1300b2032400716 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 672718120 1250 672716870 672716881
    0x4021807050904022101030b011505182e0f0e10090303051806070804090b092505220609080102070b04080a0e0307031101031a010e09091c032c0303 65
    0x550040130949410051141710011403440070456400a0340243ca04180141c01400750203042c10b03c6442001440c104030349000c1400746101740800113a08620301c10b100c1d094140112646031401506d8030020301240d80010400420060310220f0001c1c40040015040c4d9210000790618820300a400100c1e52190785c074061455600321059882220352070b081f1108901982900d0721510050b258462241101648448c04c00515000301c44030000218450500c000c00c1c07100d00380d000f803042000840b0a0f8a441c1408034864010750b404d108040d6000d410310110000c840c400060701440c2401c0d144580e8400701c4070390761620100c3c01d0380601d51000d03141d04107180220b00021815070080012141c5401c0619604120314000f0741000c0c0682d0054a40e0380040c40000000d6a040c814490a20300c194030030501d42c880900020900504207840c5401000e003400442d403031600c100088462141e410b04205003020420750014050403102e0003510940d030b169a8201c1da05491a42403500031042d2100442c11582c84 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 672719370 1250 672718120 672718129
    0x2091b0d02300f3318061503070203070b0910060e09030a050c01090c0e01090b0a15030b0102010b040e0a0515010311190b04031a18031b01020405090708040218070509 73
    0x40d044c900c4949205298202c1c2c5118607020780c1c20004d60300b40c8406110442014421400515500c132000d1a185404000c8503aa60001c5c019110307000d404500e44982c0e644030709034694428880064101c110000410071003010008226001041c5210b06000c401e584451201113118256000300c4207410078441800000d01c00c00c0a80b240c544070b1000400c00845640325a019045241c1204528218241c014401c1c825203004044241b0320985425865031300d030161401c9100003d00b41c500406d9110f01015130142e2003508001035281e0010010041c0b00864011242d0305c80400e9400c40e00d5014080d214002c000d4000342c058122074100c0b8100da03001102004021026020740c2c1031028002906c54042111180407001d04003131351094028000003101c48514100001004000c022445450800c9007540b03034010081c1c1c0c1002c03007001c03003000680403000059400382c051b0750081e58002c05400b01300418103611a24a40c0218002c0d2050340c1c050840b4400c607502150125008408200c0810819805040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 672720620 1250 672719370 672719401
    0x60c08040e0a0221090d0525140f03090d030e130f0605130504050604030c0503040902181507020a05090a0e060c031e040f080d230412091202091b0d0230 67
    0x80d508c450710022100f5245000ca080a81d10040d1801c000401804c00d0311039003000880d4a0440040007141070110f410001070101141c42401001c0242e440540400c0392141303131081504542c004014041044607240400041c401031080c0d510411030b20110310b000b000103100310b45c000d94002c0040c100c03ea4450302e060f5048020580c0c11101848200703c0020503441c2403010f0822501c1c008002a0351020100802106001941c4c0b42079500c4420001c2500682c0c0b407a010408440b025551001e0a544158500c0d009080800c402c03451800341c01c7c2000401211100294440c07805d440c01c0360800584041d031200500701c00c8400034180b00f84c0d000c80102064941018180600d4803940208001000100d102100900241c0007401c000d00401132000704004014206000201403801d5420f662500f404a1040201444040e0060042d100420070036000002007250803d078081c09141d031041290344c10310082d4400216081c6003821040000c0450520308600340001080290b084110b44403000000880ca0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 672721870 1250 672720620 672720637
    0x5090618030a08030702060603012703030515130209190b0a050d021303030216080615120a0611030a0b04020405010c03120609110901090e10060c08040e0a0221090d05 73
    0x31a102c94900001c5080005502c03800a030b50281005041c040149400d680c04180c148001507003441600060050340000170403001e40510303000c10b90b42c9642c04084155070060340c0e040e400109000d80080c15070405e80041000311030a40380e007801050b20080c4e104040c030f020300940c0d600500401044881a100340c01400390000d8800005213012072806006988582e036038011009a00800c102d0402c50f000c24808030000c05404000e44207502d0110a034000c030701003c80c8198810221a1000440d103802041100c0c80c150f40b0900404c0091140c000000e0365030003c8031400c19140c2000130300180b6090170300a5404075001a164100750ba000c0359000c0d1100340004c40c01d420710b2591090005002111406543e2f00d03110a05151a80d0b902d1000c00100305c070300550403058441107010705000d80740c1041c016200072150945800b1221040620348141980720b02d5000c4042d8107032071401d00810010942c010104e19900040d409450180019503280c070540442d0b07440641e030000400500814051030044c06840c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 672723120 1250 672721870 672721873
    0x312070302041e0302011d032805070605041818020103050712091212050906150a0b0301060216051c0204110706091505090a0b07050d0b0d0609030206070509061803 72
    0x2622030842282c110110070b0300003144948800c3c20020355800814605000c455049051100d180f0706010958600b114440c031040c0d01010180e410128440301d200c1c001140d404810344000665610000307101c0d4019010f000001d0102c0305441c007200c4c10310711501d00d01036070080d00040d030b002468006400500c0300801410501460b40550000c888030b91145140c030a220f02c4420b880d242a250006002108080100f0210b034a07002c240181044c2c00592258031600c04014101c000390344c1d5001c54459001d5034002140072802100200305560003049549040d8142420b0050380c82d50361042040e0f540191400303841d60800503c0030400750600383c21684008421040c50307498401a9a200c00840d02c81c48000d96100c0154070b41111740c075015008041d0420320010040c42c1620310364441401600d0701030030040c02d102d40015000b05003a10750b0000941e54400030f0000d00600341e03d0411130040c018644040700140106000a030301c860080090f00c152800241001341400001010498440103003105e15030316 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 672724370 1250 672723120 672723127
    0x30c08072f0f010c080a0603020303040e13020d14100c0e012a050a02090901090201080a020a0c020d08070b0a021306030b03010e010c17070932030601061716020312070302 75
    0x401c0000c0240c05042c150300400002d40c1004c98a0040c00c44101034004514141040310820150b900082030300c0580d400040e50481c191103421188041800115000f90000c4886500a0500025480c0d40f441c50704400309039000030380b10046c020102d4090800c0382020900010f0070f04001d510614400c280c0c002462440e02c58403c0d00b000d040c644c000c209500301c481b070f4094000c0e00110b00b0b0003501c068002d08400001c1c450b10304590b0002e4100d0360020b01181c5a642c2c003140881ca4103110f01c04041986401610b00c1404036001c0c1801130241d8442407040d00d4090864000c141c1001c003c3c421210b1040ea114901000c860070200c04030064002403180d42d6266488100b1078030140c05c01c0c031440d0040401c5442d500c10260900700c00c42c4180d400104940b00340440b020b410024070004180c170f6004011140c3c1c94030403810003c151100380a13407160111b50503104400000c24440e0f00034000c041c400c040c01d8a01185644c0703040d03904056009480c00c1038010782060009400d40c1c00c1d40d216540d00081d290501509 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 672725620 1250 672724370 672724457
    0x1d121204060b01021f0b0f040e060c160804150818061b0d0c0915020d0c023609150402100f2109031d090c131205070501030c0807 57
    0x1d10600090750140c4142da5440740494910f00350b480c0c210070fa1f406031428807440a2050320f4982358100104000c4248400044c001c500700c031300d00c4030480e07401e0340f003490030391100d466544201070800000f4100e00892100c80c08604074071a1090f070700120090a20046c802a03070303070610342d10025a0780461403640389000d00071104401002d00408491064950b03400d02d41a290070810460907440100c40002c4d500041d4040150903807050301e2081190701504c080c5507203003007035940c02582480c4c0075250f0f1480600b804509490640340090382d0280040b0f00480c0c03890021004008044d20040c1c400952050043c45200c40c128051000b400040009090103044c0040d60b0f44110b20701c0960f44211100035545017901420550044a2240340700010621003845000d140d020540812000d010400540e00c0450880c0d01110718a0b001d03030140c42504858148070380d0624003146e441215005090101e400c00c2d20220301c451003815058429240ca13600c1c400c10700081e0610311101d50940c600382c0403100f001c090401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 672726870 1250 672725620 672725653
    0x180506071d091f050114030604090c05040e010c03060f0b1204030504030b0108060103020a0f081b13090b040210051606150b0a0f030b09060607060e010b041d121204060b0102 76
    0xa1080710800d00d007003400c6030f00104400b0348a016811550620948600b840d54154201c42070366031000c0103980010384268603060803841c60045503c00c683c011b0501038480364450303041d00045841030003602c0c140101512205003440c00802801859502d83c1d003803021035600c225050715603801c5406800c10340d14080d22900c3d0410602000d0f00090840c2c0d000b40b00400841c101245140010807101142414041c10502c4d072986501c2c05003803080503191412504220784d078400130a00d00d190304d0000d0801105445182a11036a0802c44060b0705c24900720b02c15002d10342c0608120340801041c0c80340300910620700c1ea240d000078800c0328000b4035202540000405e00e44590401450260081e8590146e81c0071440c0005040d1801d920b00c850080001100f48499929402e040d03403141c5a1244020501044000c00503004240c802c00c0554443d00380409060300306880d400b25480c0400d481d054440f4108009103c082900c194481d0f07640e10055000042e012800a5100b42d8032040d051041c1c1c0c03480f880a00014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 672728120 1250 672726870 672726889
    0x1b1e120307030e0618091f08010f0b091005130f0f0218031605130e12041508010605120c1b33070f1b030f03180506071d 53
    0x24105035100003044001d00da00010280040741d0b0841c1c0303951410300b442c0030301c00480b14210300c110f0280c180640491904002c954003280c003404081c1e182000369980e014128003804002100ca00000e181010611305820883c40c079500c1080d001503981240d03481c020a12090009207240041010340d01c0724a039507005803600a24a9071110700001585501c141ca905050028070b0072400c0d0300c6030388040c3d0362103000ba409001000c12240201e500c412309000d82c4001e54045d0005603076481c03060080203450480b03e13a1803000380007a240c40125410324200d2448050312003203004c2c01040041642403003061104025100055031101d180060380e42426401c44854080703078081c1c0c1486013a50020040c0c0201d02d800c107415668080f551219102c02440000c040014816014080303d0030410001160340010b40622607913903440000c620301c030903405914280201a041c0c500101000a400c0000f5521141070000c0b07074902c1305030017401421844e2030381041074a42c2194242c8081612801052001c080d9480c00d150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 672729370 1250 672728120 672728149
    0x906030307050616540b040f08030c07091112040f12210203060315040b0f010b04061d0f0d0b0402040e03072f0d0809040501081b1e 58
    0x8031444010142000344c900b0702d80c2868042c0d80003d4078110f9007601c00048500112100a4020500c03c1c030b51000d042c07441070a07032001c5c400501034981001840049890051044400c1406000e0500e500c0b15900713600c1c0e1140c005030a080742e218440901c80180654081c404000b023580c031451904c541c0c01014020040111019540c0303000984012092140b0024418031190049c07910104018400784208412525140300304421640840000e400742c03070400c6110701d0700a41d0f01c0910f401c0d29140c98201c4011804036a9410040c0c1040700001e03082c40e403e801e5034140c3d621501e890480034484403c5204484000c80e01d00d512000441011030262280b08030441218061840c0072403d11701401448140c0d110b101b60140141e004010880200c1c02c1075101206020000d00c0079070098191002d50184074102c42c86069001d940300c0344c0b0704208105000102903e0b1407e450600c02c0c0c2e80c2e1000c50503242c84520410200c0b0000c0550480c030075281424081c40c0440015056000b4810101d01280f14100500c44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 672730620 1250 672729370 672729391
    0x2030c0f011706190e160f0f0c020406030503070f0c0501020c1302030a0b06131a070803060607081e0301090e070501021002130317070c09050c07030c05010b1f2c09060303070506 78
    0x107102d0306c0f010700280240c46082c1070420380381955044a00034255140103a0307003010052010500c0307045583c0e40d040400210f400c1002c03241c841c901400c210110003210881182c1001040000003010f5001007004441960700510221010002500b40400380d400102001c2405540302c0c802502541d0350b6001d484810206010101205e0401030284000b40b03c0241c0482a9141448100006403541003200d82c0a90151a034070380342c0d4820703e0300c0c10403801030106000c0300d00c180e03992033041000c0e000c02a42c103d0700c20410070302c9040b04c03101c142c9440301ea040c091035005030031a5803003c1d20207520750010089403d1b400c1111110303c0c0e0782d455040e02050340500483c1013060000f8950b040c44002c15001d4090000300400f00814200200c00d2512889000c1c801400c1c09070001b280402c0c400c0a42c0f200c040340700050000074007115040c0c055036162555031000030200380b84014041c400e80d920b81e865803d608441101c0d8150701b00c903004010401900402300341d803601c0104002ca00142d014400203015829011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 672731870 1250 672730620 672730649
    0x190504030f230a03090f060204031121060a0e07080712121d22020706140108010b0a0e0c0417010203090c1509010309020f0301060b030402030c0f01170619 68
    0x520082c4507032550322403402400ca0012414240c035009000f2100030a101c2d081c0020511420301c1c000c501407a180d1409025240701043c00418041c40210714001c9560071118048242c207450a60316040001000c010210340c0844001101c001031503008402401c07510080354441699883d200d460082290030030012107400001c1002001001201404031454505010840b0400f85284800d019070840100703205400d0051118000451400350756280032808406550764030b85810a64003422003900d40080a0244070000a02c0c0c02040c4070b0304461080c01411b0b0102d940c40d04180d0400040064605041031804200005044035400c407084680c0b80214002b40c1c0303924004502d03500b819400381c0054010012020079010340c00d00b183c00c4445030311090030005824007803030020400340103036010140d0f015881c22101041662203c4059480f55108504880303544410302e0a200164914100c00c601241c0e00e400c146c44804410b1038865802031014041ca42810348000d901c02902d5a140d002c0c01c05541c005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 672733120 1250 672731870 672731897
    0xb1306170f070312210f020901021203060612040203191b08061312091e0305011a06030106080c0d0603060506130515040c030b0405151f080a0519050403 67
    0x51003000078109161000e09141071071034444101380b1244031503800800c040d100c0c9004a00c05020490110352212241c20030004c22603004a0340250f0003a408540035114115100c440094114216071046101500c50781c1003120300191141000405002281d1500503101200d22002080201002c240e0007641c0000804078071002c0702ca0031280310b81103e0b009400120070800898104071422207140e83c440364002c41c50078104001c80340000c00c1d400071b440a1740b121540c000400411200d81c425280242c000b0401040140742064070b009240c65140d0304100709000410159000345c07030403a40311801154240c0303001c2c0741c6400c6504071400e5030000c40b82107a5a1303090002d90b00701002c2903101e0824100040025040c0302e0a01000e000010307070305030b2180d5124039540c03402c03038401d8005080501c4054414002400e2071440300b08111500d108840c01540021000346c0105d80d14450582089410349440f40d00d62a90700181016000007440072603078503a8146054500c581d40d22500340704a000340d80c4c58080c40c0c0d11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 672734370 1250 672733120 672733123
    0x140729040b01090e1e010b030a0309060f050403020a0e07021006080a1202030c2a040204080304150212040504020304030c0203190302060c0406021506030a05160f0e04080702040b130617 81
    0x10f070440c0310074502c0d1030b00754130000310005440030002c00284e0f50a02900030130484e980c054007519040c0c54043c00b03140030050825401400d801b0654440d91125201c0061f00c2200702c840340a03510001c0d6000300110000c0092090020314240c0002d0a407040d5104032a40c02080e8064650076401310405511800e040014021407030016886448144061490170504d030b81038550310b83c80c6031808540c20000314021001c20074440c85842c001900500207644450784d800203551250000c0c46849140c00e0180e10004a880c0f0108561103940f41c50342000342811304103000e00c002900024001c07000d02c0000300c90390000d80ea08015000e403200183c6482c101503441d51030001d0405e540a0711907211705905000512040360041003060862a003003040c015607603039081c006480e141c40000b01a00394002c0c81e01c4a1070b010320000e00d1205990700907131400d0003141e8811b015036004400311005490041c007400207030010b10b802d030088003405200802c019240d003a0300c59014101e408541c171285101d071b54180a91030401c2e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 672735620 1250 672734370 672734393
    0x1006080f01060824120c1f050d050702010f14060a05010518010c08070c24020a0b1f0b0d060608130203030f030c2502180714072904 58
    0xd04030000d4229500d0540003070310428025101c00400c80b00a400d0030490005048125407000000300120340e0310652114654441034100b041ea03002d542d2448991510501044103100d84c03600c10b5440c245000d200c0300c1d00754010040600280304554a510300a01400000d000f0000c2401c80b100f11a60356040c1402003101602680d8461410b01c80103026a6020320302ca117a890100e032100f0300304458440c00e24a031001c024811448001c1c88401750010200d8000000d412154407092907034070000441c842d03420142e9850a80c00c00080101421a00103083e0300801700030320030046141007001c0c0d00b081e12409851840e0300405d08000303c007030340c40004010050384548030541140944400d0a15220741c6c0c1c021035103900c60b104130910180c2c800408203d0500f01c0d18215005940049521600c00c0566061000c03901c118107010782c07140014484084040500c1c000b81400340704103440750821110b0b208034204607a08400001c1c0ca0705a06801904101c2d6080c0387e0091280b074681440103054a41441c0050861300c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 672736870 1250 672735620 672735631
    0x350601030c0e06010228020a0509010905190915091406040501052d07050f070c08030720010819060314060601020f0307150209040207200a05010c0206040b0c0c0306100608 75
    0x1400b50500d451000c0104074046811a80c01b400c010061800e0b0000ca000c8440992100303411203002000010110010788c0814050004c20001004201546680c3c0d020344807080b0340500710004104c100b140c2c0031940d5001010507172080c9250b840c042c4140221908084007101e043d507459440b82d08010b0750f0f064000c88880641080900d200b1640320034200080000401400b40050120009010b00141e01903000e4076001c903800404a40c01c552203030000b40d22504600d00403030f10950105020740945901d00b011070b9071284180d54903401ca0765804a8030740398844180b0304030009a92000080f000c03904c11041c41e002c003d2902c1c01011181000000207182c00030110305c3c4041c0e03401c1405101c0010b084040355400491200001584481d81000003400034480d0303040041c0038a000000e4054902240394010206007012100d0b100750658030401521141c1d180303c4001e501000400c0140310640c4a074001c3c02c0c420061800311029141144042480c10106031050344106d083e884040003a81d50110341d040d07004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 672738120 1250 672736870 672736873
    0x20106080f0a08030406050603010e07080f06070c0f030c02060c010e010b0a09050903030f0726040c090203010f0302060708040f03050307151a0607050a050d050c0606040204350601030c0e060102 85
    0xc0d002d503203036100c0c0c0d40800b4000070319007600d80c00403131035a940c02d40100b01e02003a6181520642659044401ea984014a1300c0c0c45e031334040e0800203030382c090040d10601c86082c1c00c0808015000340f6541c01f2a081e180c0718070102d80c4001c092241205011003481b403440062920f40002905030400002c2004000b519804080d6160a02007000101c800c04402e494011301180d180b072501d84c0701c042d8260380e0010400c085c42c0407a6603600e10282e0234002c00e01c0c5503004901603002c072606192079650f4182684824020b400d100820640d082005040400c020101c55015145842c14143c03116004c03089920a90300646403039102041b00800d05c00411000c2502c602d0040d400c011240c1c030010401c1c02c9080e500b58903849900082608001d0000034040304095507030007415540300b9001c0314800713006600884211152840b8101c0017a04604140c03080300e00b580d00c0401605400d002164008202a540c030301421164a50210800044d41040081ea80a141320362000e06110b403e040098000c02001001141107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 672739370 1250 672738120 672738133
    0x1060b070201091203050f0304060b0445080a08070809061003030509031e1c020105130b270105070806010f0801030201110102042c06221515020106080f 67
    0x60fa0030a10100403285012040e8200c4062030500b9a910301400d1001e03070004600008002c100001580700b50424201147e0400284c0c1d485a1250070b20030883c0402c1d60074984c8015096211001901601c03541c19004d041d041030780485940b00d0b50b15400160415010500071014030010702d1708400c0c2203520040220003808103292441022015649501c0b01400340440010800d0031510144041c09040380040d039569000c0c000b141c0c801d507641c0e2800007540081c003030b00c00c001d444141c4107000b443c1c081c1c0340c502c0e440c3d1000c014580b81c804c6000402b0340407202050440c0e1940c0c68440e51010310320300c2a602c1c5000052589070003880034018920043c030060402540815102400ba0000c0289041d02d4081c40c2c046d52403070301d00c80154024403840e005031400030f44541c0b0201040c1d082642c500c0b400b40942d4500350303064075440d05009804140010500d21740b03100402e650240c040541c0600c5110310402d0a903010581d4130f11280d608034107451002c40040c1d46030a018840c070402044002284400c402c0100711 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 672740620 1250 672739370 672739373
    0x20f090d14010b181506280e03010c121a100504030b0c0f030a0504060e1605040c021606140415030f1401060c0605150907020d140304030c06051306061701060b07 71
    0x864002480603c02c901d20317240c8440702c0d4603030070183c60a03030300e0391256440b22241a0f012410b0300801d4600120001e86072400d000a941010f01940d012402640ca41101e4541c629a0102c080c0c206c1c4200d038820700060805508169a5a9440d14501907194680f659905c1c21400c0840b003003e0300500018094200700142c61800d8602c40c102c3e40c1c044402d443c0010b05440301d02c2c1000141141642ca006d0320b209904c031a0420707503109031035101141d4045801300725294000c0b070140d80310301281c1c50740d00800700c0300603081150a0207030740350341c01240b000c5000e18030b000e0321900300019141c407549039080003954a0307013910b076007628510401d80003008030304e04202c0c2589024401002204e01204c0106455110008240030740c0c8502420f0403c082c0041c2000c034070b4a000d080c001d5071083d103204200300151a0b04c7c4800c030540c04503412a030207150140d4502c040f2164075100d2802a01b00075103040c071480841030601020618a00c10040a8070307100d0407041e46420600c10850956455420400b4045003c1100a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 672741870 1250 672740620 672740659
    0x2d0201080601050904090b280c080c0a020a0813050f01030902060f07080c01050705030f07110303040f0311100c0f0e0a1401170a0507110619020f090d14010b 69
    0x940c00701091070090390f5000720344c0108000c0d048400004083e00350310424418520981a88501d1500c00b05214010104000e6040740907607103054a030501240500e004203415091000c014070701c040c8140100e4410001990754100190312540b0401d030807400c07410050003507241900c00c80d803c0c10424681444003104030340000d0f0040c8500c0030b80514048000440b035040010140943e0703003005400c80200301500e0030070360103001548120b41c420000004000041d21403409628803000398103030f550095045542c2d03555003c040410700d0100740d042c445094454090394800300b01106218140000101c3c42c0c41c01001c000d040b41e400d0500c03950600c11056400e40d12030b101c1c5000c0d0000c8a01000c0c8824113000d007200142d42195004048060b00c280803810000ea44009400c101c2c000c5103580e90b0a0a81001c545601c0d440d01000e0700c01e655500a0000c00c481c100740e00d6009820941c000081003450840b00760f0014142943d528070481da0b4807040400f40c00006030a12071501c0010058a1418441d0301c52240e40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 672743120 1250 672741870 672741887
    0x6070f1e030c03061a03010e01050a1413060519060f0207050d15090f060209091015080402010318030207091103040c09151205100e0d0c1103030d092d0201 68
    0x103030308156541070090280307442074000c01c00130303c40c0d0400d0310b0b400701180500e4000b03175100b4020450000007000c000650743c101080310404441c1101c400c0c110303c8068500b00445c00541e0803020f40010b48510010940e69070f00007030f0001d0b20ba6000d60000c2203070319011010700204442d140c584217641010300c0030001a01c80024692009500403100d0008406143c0443c00034000d0200142c039400342001200c2c20800941c1c0100301090040316454800d50b5051511604503c4c940030700222220010944d100003401400c141d600304e84141400705554008284131003801c00e4680054005a0044a0400c000300d11449250720000c0d0307134003c80d0315601c0d03d030303e80040c020711a201d01c06199a80e1818450b040c004a89284081c21100a0b0840404000d0405540c2d4004040704070032064506400307800c60b54400100d8420841d60340d210744040104076280c0c01410b4a403205540d4240c0010081041c40c041c0350310611160702d1054956407103800e101d000380b94100c91501074111410303088000d0b81e00540c3c0c008011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 672744370 1250 672743120 672743177
    0x6030d02010b0f01050d020c010507080a110406050901030b120303310b060d0c090f0f0b2b080405130204030506012c0c0c1b01020d210c18030506070f 66
    0x83c0d8802c29821b101c0024461019003400d15407130801440301e41507100c82d9032030103000e1016087c0455548009906250320032842030302c010400801c206a0306500a40180d8982d034001030021804c1d8558075011819940101d4440c42079410610921808a10039402c2c0110901e0200c0420750410340c85e42d80c0417540170050812072041a200e44000100700070700d62400040c00c441c4406014040f01e090504001d80304141c024542e031070401c614000d880c2000030307207101401d40083d0710102400909000c8005620556816038022004010218913616a0700358050342c880000d50040e6032301e185040080c10f041042c8c00070402c1c4604550071003019450060703c1da00c207500b8429105400e84604094071602c1c8250100da003c02d0040d00b2490b0303034070303840d80803400c9451000783c003640c5200c0c0309502d0807030700b84d081410768003040500d41280b51100040356118041c070700076904203250054048104040f4249a40e1700880d4140d002200f0001010303071103d2010780e00c2c0b2450070103104401400d00c00444c242458481c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 672745620 1250 672744370 672744377
    0x81c05190e25030b160207050402160b1014120307080912101509180b070203041d0604180503031f090e0c0a1205121e0406020606030d02010b0f01 64
    0x1105000d090900c44142c42040514041008102e508008541002c140c8001d4908956042c0003519180b8001980b0b074064059034041d004060800702040003d400a0b420b01510300081c0488200040b9095240f80c01540700306c141c80300080c07410b801c10b10020280c0c44040c0c00350044045080c10b280c0d00000b500c8040ea841220252920201c1c80402e01014078004521880e100b102070031042000d40381d111600f64040c2d005907403440c030388806c0301c4020364501a618112a0380c4071f030030100126008111080d004807007441900d240641e40e02050401c10742c259484041980355609004482c5003178404c03c1c1400f0407030314a60404240c0c50711019268000240024840b94510100d03001c400c40c1c40c1203c40141040440403c507180050850913950030042700d82d42c0c0030303950b03a000219003090120600c4075a02d0b0712000400003907400c20750951403138020f600d1240f40015481c000c000782e12000c0b070244c0082c01459006083c1071900701c0406145c0300151b1a110b0a5903d080b984401ca0740342d400c20301411217002e0030b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 672746870 1250 672745620 672745631
    0x708031b01150b031e130b06010e06090402030a2c010608070f050f0406051003022a0a03110309040218130504120c080f040807060212030c0d050601020f0109081c0519 73
    0x40d00600c04d00017000c802c2d04409208003c01c0100320300041d8000d441c0d402104040e40b955a11801515912080e604055000d081803064100b6468682c0045504c441002000304007001d862440c1c0e494824603081e1500b031166410004020100244194401040c400d8000c001c1d0b90310313181d0f030810b9a4125009240c0107840707140440c2102d80321500400024030000c2c0c401c807059512020010020340090850181c020805a95101f080020544801041032020003904500501da581982c0ea42c5c17010b42d000040d070005100b440c90076501d9101401400d21203144d101200010341040002490703d41b901c0c0c40c0101e00e01f01c10700c00031a0211803024001511820302e11407282c0c036030030300302628010004400d03411007000030040740d820301c0410716400f01c605036001caa2400c9c403441a90340450004980d011010750040c0500c2160f0710380d6400c01a0803180c10b005881404e26011805403e6800e0ba802c191404640064070140d40440001301805090301140100b04506050b04c221003044d0696121b0900540c488 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 672748120 1250 672746870 672746881
    0x12020a0e04020a0c050714030d0509030d0c030c170d0b030a150f11030109020a0807020f0a03030b0a080d090f05010c03020c0906060906160b0709052206080708031b01150b03 76
    0x7440084d440c0c1e034002007140c031069a200507807188051f02484540c001e02800409210242c09101034402c81000203001c0d191071886908110b40310b01240c04242c08001982c3c041d0400304600c001030001c486402032600d81e80b007104007660411307501e82202e0103000354807189064020401c0d07003840f1a4030f4260008045003c0110024040141c03000e89420142c141e000000020549816801426031140d640c450720303906d0384c41c00c005903110240529404081d030008900c880009120360311890070100c00421050245032202c2e0741702c3c6410342000c0305401280c03540701c05225480156a626008000c01d04c2e08034812145698020740740c04031008401d024400a01c0030507841c2d034502040d02c40035500a08566141c40542c040e50300224000c0605640e4044d00d0001300e01502d22030080801518400b03071440401c1030b00844848640100300e4040420301c0d48d030b01c00225030880d050001e4001083c1c2c1c40001c681b07078629009242d07202542d980142c21540e00d03002840d505440c249880100300c800b0f5500c2c8a4490f50781c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 672749370 1250 672748120 672748127
    0xc10080f04121e0507050d020106060c140a0f08090910060906050903012003040c060306050604030b3c010b0c1c05040503030a080712090b060d0f05011a0112020a0e04020a 75
    0x1034010203180140f0b41504500b54000f02900000313002c0c4044805aa00b40c2c40140d0899a443c09400e0001703c140d000c142c00b0030501d10f0807118494600045807590b001d03503150200c5c1740c402150126550100000d550b65a803824a400c20341000321400c10b841220300e0311030085d0059480b4851138040c441c011500200d960b4083d4800c072002949000c3ca0740141d03144802c10f60080e4000c89048489226049001c640c0c94800d1290344140c030406045145064210384070b2490480006203901e481811004110300100c1c144070b599801c107051141001c80e0407020516802110341d0581090114070380501505100e00c4002448401d1035183e5444800a54100d040455a44c445d03608400c2c2c06110015030044003560000d20681300c0d950355a01d0032035950040401c00c090303903000e10010f040917201e10702040380c901c1c09446091b1410311503140a80c64202980c1c03a02d00b900d0721444074003101030040100e0700e0156009210142070f8810302008600c0d00b4480c0b50060006a0550055800390350b010550548803400b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 672750620 1250 672749370 672749387
    0x3031801060e0108070e0f130807061d0f010f09080909060102070b0a0f080c0c0703030e12060a06060e01020f070605031305060f010602012d0e011b020c10080f0412 72
    0x10b82c0300882c00b40e60b1100d8510383c0d241c03494892135071201d10030030000d0142c000c1001e003540200761940f24081c0813085500c0b18010354218510583d0066071f40d10480360100f40c0f410b0f03a94424140707007014201d00e0380811411421910050304d02c0400c541800d00d03000c00510240704941d880311048911213225101c640040340760000036004207101d22000030b480b030051070b00300c7c072038000030f40c090760300c071011590303046480b04280c01071031001c01c500d6110010600009020750003842c0412409003012044084c40481d0314540101554406030f0265a03401c14040740341d10400c2c55140400c02c2c0000d26031021110f0300035a6580091140c0d0341040004004119a00402076910404681110444407541454420004204028402e24015618041401d4929004400d4240021116140e00b000c29004460b07a480039060200c82d00c040c0c0e542e50352602c040d61030007480351100d0700c846a008001e10664003051240b0708030480c05407000c0c020300c50100070001006528299200b0741c00b01c0098401038102d5420f981d20311 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 672751870 1250 672750620 672750629
    0x9061406030f130b040f12050f1206010318080301030c060905150d020702060304050c01020c04050108300301030b071115070c0303090b07110115150f020705100905030606010905030303180106 84
    0x444d240c1c1844140812003060a61860140820301c50b50342c1803000c20365003881800207080c0c0c8090103004041c020b1207031480c019032045040c1008903255603d03081420f40c00c822400100ca50304000710061051002c141c1105010b040c4505020034a5402c1900044a02280c0c039042c2901d0440000c40e42d1400d60981c0540391915805020039443c0d041c60310702980c5640c0100b000c3c1e80103101d140c400c03d4645c5401e0145504036180b51014000407281503094500f402e181c480c000501d07464080c00c00101004e0321000b03500130344c0141a10b051504240c207004040c0059a80b5a074210782c41014060a4028044000c03034105009041c40001c2c41d00503d0103030042c14034064060803d074510030820010743c0c0c000a100340c40f00440402001b111007580c2c061003050b0382a01071301440c1c15001080d00060340c0610b80da01c00680c0302e80120b500055440001a80d003121928540d0001100c08008000c0c07810b0030001150400f0090030258000c5040c240407a80da40001020300c840c0025044103030310300035000e500240141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 672753120 1250 672751870 672751883
    0x602090d060501063b030f0d0305011505070203060c07020f040e010b01030e01060e2d0907030221060403120603060203041a070c0f080307050408011509061406030f13 73
    0xd80365410201c0c0100000d1043e00046070300c2442c0c01080030320b0418107501c481c4401c038a458407200c0c0d8a0481a18031501802c15425202d0181c040d00d410700104040042224165000b20300b07507041001071091740b020741003148240b007400c0c000781005035004614281d010070070203201038442e2102d0000540e400310065505030828940070301c4d11034600d010b40200e840c040003a2000d0000d911982d858a0032201c4600c1540c210700003140104040d2480c1c81c02e004110030001055208815242c1d5030440000800d4581641c0740c1d03c6140d080046043c1101e09800c4c2c1084084410290f04545182e15240c00c0018402030800c04407a03041008410302e54401006560424001c64403882e061a0040400c1c5241d0b0700383e4039800b84600006d421500c40e14020020540c456244031000040c2c5e0b4034400b49400180c510300c1805000c0c080070950700703424800d040386420300b0f000181d500ca182c250701d5400c4036081d030045150036600c02201c4030503841c0c2c1c80450741c1103416041c03034050541e1403c20b041c0c0600b40c45e04000303094 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 672754370 1250 672753120 672753139
    0xe060904090311010510080c04020a171812210601030e0d0306140d05070614091e040e0f030708130e07081005060304020f1002150c07030e06090f0d060209 68
    0x181948045142d40c0101d0f1500200001d46522940b142410014400e80001d039100f2103840d030090400703402810040e4110b0a201c40d510035840301c560b41800c0110364001a00d85400e5101c610142e0801c00348401b03018200b200e51502c0003e00c2070780070041403100358008140c44140420f1443c0d120354452018a60445c1c00e40c0e08030403041100a02518141c0f24400d600040902800c0d1945081002e201300103520100425490380b034010300780c909011401d08500d035540140701d291a01d484110701e00c0383c001c055035200c1c1c0301501e038401000100e405201341130791107500100c0d0600510000004a450350360b0402e071043e80307482403401c080f0282e80054001c3c04885010900340180c05c0d82000c0c00500880201d60710380c1c07009850710207006450000702ca0180d880708d41e9030f01c540040c0c18282800f00f00080326106664055070100030000080100b510490b1410100041040c241355001c0b0312004c0745801100c030985080c1030100090081102400303070612038000442514104030007681110454a0082d00c43c060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 672755620 1250 672754370 672754373
    0x1401090f090b090a0c020d08040609151d0a02010207050f040219090f060309022409090403052101031a0c120901090209130b0a1503061e0c02060c0403030e06090409 72
    0x10b404460561802145940c010408903141c1d030154190125065008141c00e80724004121341001010340296049581c41030f880300441c00035076042c05040c4075480d000c0364010b0755038100309810b4502c1000c070380c130380e08603000000042c3e034081107510840303404513120311103802c20f02c1c0060001e1080d901940244e444034001c1ca00d8040e000244802110341031071316000301d1651210107405480d03041030020350000c8c060f03814512104030b1090400403044071100e02400c120608001c9124138100ba20300f94003103140490200305166000000ca4541c606224654945514550710410007549148001c24400040e10000d189149000280d6146411584900010303040c4403001d14020030f4006002c3c0c1c01030303c06500040c0f554000d5200310303003240e910171191220b80d507030700a5120042000c5440e80502c0ca102100010214189005c0c180d10f440030b01c4500d50102d0203030030300a0111160140305200b590410300811820000301d03800c6d54120fa2b01f50034880908035034180025168494960304070752081c50301000744d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 672756870 1250 672755620 672755639
    0xe15010e07080115080f04110607110906180123030715020d08070813020f0402041e08190809011403011214010b030304120c030605040803040c05040203060603011401090f 75
    0xe0040c078403034807400d4450340ca03543d0443c0510707060307005000416030745408120000030b08415654413a0203440400514020900000d540d540052400c0e102d10101854200180ca0219002600654201c0c0d0050081a601100c3d4801c504148104c03807021501c6c40d01c0c1c0b150307542950982c3e45401c4004081d240b0240d10b40007884000218a5001c02c014440c6000d11785002c0c1c0100c0c08035001d0042d41d00c6007042540c5106800d040c10310842401c036000b02c1105c101850035212400a0405440c81c501102441c40c40711004502e0107415038000d042aa0203103800c500055207031454082d005801020395a40d500400c0010b9800460305611030404c1c080000002506e07040040703824400602c22960903441c417208078901406e8418040c68241d141c0c10402040040c404102102c2800c40d02c1032403c48542541ca449160844008a601b62040c0c030000003004200200c81a414018140441d011401c44c140364000c030f4800e000500800c00c81140240c6505400c0c0e0046c010400242602d10903100880c1e102c1951a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 672758120 1250 672756870 672756899
    0x40801380103020d09050304080a060b030c0108040f1a070302070611030618040501090b0103030c0302160506031311060d090312050705040b0903030c01050403051314030a121b0302010c0e061201090e1501 89
    0x644bc10f5181000d02e1b50103140100b03a40341101d005030b59001d030b00d840d03a4440041c14501103000b01d44900c0380441c1030582e5000f0794950f074850045070f1001610b030701042c140a010349851030030b4050001010010001e156942e207500e924280010030040b52565210b2174460b004041004020f401e00f10804000010980e0000607031806a00c01c2d0300341d030042031080c3c805904104560040f980d01050038400240100c12043d00407500741d000306588284480540082003031503201040b03400362291500c0d0710030103041d0042c51180406c2900c003420801490031180050550290b4040c0d071001000000b6941c0c01603a00704242c5030303034080c0701000f005241400d180282031303940031802c001c1ca004044140041d02c001006400e0783e402d00c0c05405403400c180556100a51076942c400502c040c040748030405a110a100a08201198400d400004103003102402c0500340e9440050814030903541000402441400c25086904440100340e000c2100403184040c0c40c1842060300e07c0005402d015400001c001d003899005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 672759370 1250 672758120 672758123
    0x8010905010b1c02010905040f0f0515040e06070203160c05030615362508011e1d040c05060f19020a03050717040506040801380103020d09050304080a 66
    0x10640c3e40070401010000005500c40081e01049100f9000c2181c1e00703003500004141703004180c000540d08040c0000138201c6100390b40e001c1108507500724100b11400d280c0b00e070a00c40040a40108124030385400025580d1081503250500c0045030280c580400040c40190300c0034107001070985070355190103429100d0180f0702c0081244104d141c0000480c00b54042c500b00200000754130742c8410308074852542441d0008000d08144002140114460513400d400f09000400069654440307084e5450900910007585090300004a0180241c40c1002031182d140655201c100d8100303c1d0010a54882c14041c804034100e6200d950402c1c000200c42480c2e00c0044002c282c0301c41034074200000c081102c98200e079200314840000340411030402400d0046141c01149a9088800c4004035103025140c4002c90129040396102055580d1240d8141c514100b045100d150078441c200340c1c546090022140182400840c110b08a0505500003001d05400c0107542201d019690480200e9503640d96070b002d640d41d1207265410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 672760620 1250 672759370 672759379
    0x20c16050603090a03051b060106020d020601080d08070c06061a0c190807081617040e090a0521040f0602160b0403080f03071106070e010e09040c1202030708010905010b 74
    0x801103003918190094038000c00440008001c02c6202e941c0544c0c003a41b0440301400da50100c0b00c8180c41c00001000040d010b8a07456000e00381e4000e03850400780c503004041e00b0cc110f031a000461040303100c1e0781c0031280903807007001f901c3d040d02c2c40c008600f4082c00030240740c0c00c0070700005000c907030fa20720107400c040007044201c074603008480a04000c06c03040010343e00c07007080061940c0c80030000070020034030b0000a0300d0341c441da0002c07a0003c00c04c99030710340c84645061160382c0d541b94008141040032801110140340d1001210b00a030508101654030192100070f407101503101803203000351039071107a80b0f480e0541d4050035900802008094860201a59525800070010800c060501c8081814078000069404403540440c2e43c900b0503402d0980070005800040c1043d04020300c4141c102482c0701e0400050740152029118a4071103000c102c001448804d4001d22103000e10750303203024400010000b41044003121080700710300d000360980e4030000742041c40a82c46002d441d820312200da81840010342c4880300300301003142d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 672761870 1250 672760620 672760663
    0x70c020a0e100b1201091527060902030f040b0a0608031c05060105040f050105030a020d1d0c0f06032707030b060906010e030c090414101a01020303010521030409020c 73
    0x10710344280d00c101316450f400b02c1c400f60010840f000550300a04207a0002c1d0109030309560702d03171640d403110719400c1800c100101d02c40c1e1503116066040d841080c2c0074180920055285290515008044140140004280311a03260000f42d40004035441240600030801c1540d60314009034030400555a0750b00e602501303282c0717000c000c5001580102c0495044a580a0030803025a14060065581e504010078a0110b15001c001c1c0c101a90184e129128001202c0700f900c4c10394624201190f86084514003209001e0401c1c95030216017940c0380026281d000701c0e00c41d060600c0f03040118244004e0826170003070f0086803043d03c0b004002c00280048461140d007040e00c60200c42d81d81c650044858407a00c145c00b9400d50403090b44407085060851a5a0303010380143c10030107070b404207801003516003005c4901e403040c0c01c0e60700e140d00c0d01d240748068100449441d09100450030355042c41c000071007490f50785034174204840c10350040c20300c0346000744192402040e01031821519009075514041d11030000304541d04801c000f20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 672763120 1250 672761870 672761879
    0x11a0f0906011709030909010321080c0f09130c05121b030c2811060109020c0304050d0303110a0c1202070303021c12050106091a0c0a0605070c020a0e10 67
    0xe5815a110701016074a48141a408010152400c00058890061404100000c4249469140b003681c001d52252000c5460710100501d4200c1501c070041251041000348030034060907030749032003d6894801c03910704080d82e16000280081d4034542040603248101d0300b000181c0000e0f580040c050a0b0b1070070410703402c2440f40c1e11050b103420701c08071260460410400500200c0e100043e00000361000180007520480c010b014043c04000a58a264851000600420441c506010306000090042200c0300f020b5041120000e80c16469020364040c0e42e0040d82d1201c030a00625100c0d4010140c004d078034030030855449500c128014030041e0301301c0d816100c4080c40700301c1c041e50501c00558a001c4030b130564042e1440000d031f0f07400c800928605014203400c1100d50a0383e00d01c4002948541402482244c0f0350091080c9001c08800000000d25006010b0715024081e98104c07a8004c900d1015459000c1f6000410b541c83d2202600c0b541c81704003001e50009241d1001213220881204264060580001e00c8500071f40d44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 672764370 1250 672763120 672763129
    0x503060a0c120f0b1216060c0c030b040312020d09141b220e0102030921040302010e0111010504060e060903040303020a080d09140706030f0606021509030c011a0f 71
    0x903201e00000070740d0000410044500c07a40c0291200c0c042240082141149400042c081c031005e2103180c0d0603908060404090036032200c000d4030040c040703030420050035005605ca06d600b80d80c50f840007900000340346d00001c0406100305c000f115501c070800c2e011510380750100c285800034865410704440020145a9540c4ac07a00c1c000740b82601900c0000c9000c4d40c0c29588814031008c00002c000050f40143c020031008190747daa40140748103d10742000068070381c078180804624080c1024444105584081d2640d030042c100402221300b80c0b602800c1c0611031101e940012a0284050340c002c18007035107000300788010070007143c02c20b604449030a030894407503484d00440140c480c8102e06c00140540e10845400d0002100c80d40a0000304208450028540510382c45046e0403086900c000c48030394001c0e2806020302600f510501785240301c80311040000c1410400013a40d500c01703801d1000c4496124000080d8140401c000710345441c0e4035000217125500202c4d810100c981d501056580c0325054a4001c0c4105061 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 672765620 1250 672764370 672764381
    0xf030c010b09010509160917011a150f09010c060e03070b011e05120c181e15010e040f06150909020c0303040b13050a0c083a03060503060a05010503060a 67
    0x4000f08204186d4542001c2e103058405549505014880781120019031102c00902c00c020307505010b030000c03400401080c41d060844804030a1984100c617400c0c2c91110309038020301940c841d00800801166901e8810005a84282401800500071810308107a001e03100e4001c0f0181c00068880c1c0b00354000780c0d0b01d90301c0700704141c001e8040310801d44040c90b0007040280786c0750394507444010040041d21765018141010901e2070324000280300f1000415420302079041e00c410403001340c0c0410700d502000030b424200a51601d07032030b501940c0703410000441c50001081c2d40d03980c80240181001041004003694500600300111240131109001c94801c07080052500014000c03900307c51014809076142d40d542d0342d12200da41d8005042c6a001c0c110050161002503010400c480c0300e036000306003820b0064500f44000d0300d40b1552003080c004d01d0815518254a024840c5000c2c0c4003c0c442e5171490300c40034031460f0118024501c9030b01540c1d1611540e024044001c40c0f81d032107241070358415000c2d24890365800301c03848140c88 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 672766870 1250 672765620 672765629
    0x8070506101401051c050c030123061b160e0108011107050c01080c070804061e0e10050904111603030b010207030c0902030a1d010c09050a0302090a020304140f030c010b0901 76
    0x8030300c0441580d9903101380c00600f003010f00039400c80003110381c00d020303141220300841c0d50f032903030040020050100c003d42c1144401c50500444805600c00c1c00200807400b5070007140038a01c82d0403180f0142544220341400100080d40100414500301941c680c00a811000d003072017800d2403946400c40300b00011a0840c200c403041c58110000300031031140e000c011101d81c1030060041150700024898040080d090a00801c0240020303944c10020b020114052005942d40c01c0400043c0301503011060f005444502c0b070074610030414100151508901400b003000b800c40441d03000c44000300095180700c80041d851840544600a607002c21086091200584c3c0e100e02d00d020280600090703a00800c0b070303c0110f030011507009006071804107000c0403180c000c2d418142903a80f2100c90741d45586c01c550301154060680c00003003a00312071030b200b168510707000300d00301280c003034070405440341c0000c0000c040c0b040840c18034400d10f9054040300c0800c520b404502d03840e5000700499003215401e0464400b154035160243e503060300e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 672768120 1250 672766870 672766889
    0x309060a050112032c1e0f1e04090302010e01060603232401120603081b0c010f0302030901180c060f03050f07110c03190618170c0a020a030807050610 66
    0x254003205610002244204010079070300044060060303103440e2910312042241545106d60b0000c101c200170001da50f0844602c1c180100c0b4050064016800c02c9411003600c10802d641c0001c0820650038224054600040416000c0d0708010f40090850391660150400010822008410313500c0c0d04009008101c09460010808620f9010820f40303c010030340e40f410305031050500f8080702c00201e4080c1c056502e25441510009000f10303880c00711300c40c2003010202980c440d80150840310041c0001802c1111170010041c00c140d03011000030b100f0b40b000d41c0100b0440f0380d21a0100c90b010121314004200f406140920350010705243c07000c40d03c442c06070066038007482420703107070019030703921240100d412030007080f80304255220385041d12680e91010702811a090317540310002e121404483c203140b0b05503404019a60000c200042e400b0000c5a5070a1001d00001c0008130a56603a000c100c0ea050b1800b05c10f01c00296009403009400010000c20b07000500e16039114409540880e50b42100a000e070090911452842 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 672769370 1250 672768120 672768137
    0x5031905072c0709050112140a090201140c1c03060e07050f0d050c04090c0206061021020c030a0e0f0f061b070909020405012702090103110309060a05011203 69
    0x21615102c00e2080c4200140c0a0540603a60328805688681d4007540c410000c03a0200703105004550340149030000301e6003081018020341d8000c89080424040080c20540c0d00d660340e103002c01c00c6a1207072461b041e283c0a80300c120b81d220204038081e142c49104a000385002c0b03940c030b02c4841a203107000b40100d03000c4844122441c046940c503060161019401450800e040490402404207103d42c04d1159074052109003502540f070701c0c140b90303047c0c0c21580640030701c10541d80321004100440d6103041000c0c8a00803180f412007541c00307090901400100980746840300c400d0003c030b0b11070400c0030300101505a5120302c1e500c0d450344102c503006201d004101c01c04015000b58904d640c83c0c42d00d0419200820901010411040b914180720700b00c0ba0074100325400c4200960b458a1040c801d5113050700440d030140034840c00f180035904200c900d0444002460a41d02d6600f17801180458260f030003944031140f00c0c00180b00c083d0340d030714110241d075403a03000848519690074074043c00880c151200123a031100d070350703031580b60b615a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 672770620 1250 672769370 672769379
    0x9150f040206072108040c05010c080f0d021209010225050a03140c0f07030b0c0307020303010303030f0b2214060f0d0204060518072304090c03090209100503190507 72
    0xb9258000801034904110b884005030481c12a80c81030319005500d41c1d1813482606281c60214100e070002e030701c5141000080c208400100e0845412a545184070b0300c2e43d20340e101030b40f0020320068003034007032030b44442071045040059510f4107400a0018001d580f001c0200307901c0341d8400e4020410300b9640074260b6844019108000390040085407800c076030100c0c04908042c04400d06a203403007004241032032aa00141e03070400412044403011a001215510940d05620f00864029620b00051001404040c0c440c0102c400b03020440d804407080000260013042c500d07025400d81e9002d0820300340300591040ca4100c08100c50110682501e00460008001c0c007120700440e010065241c2d0451402c0c0c5c0c0c050ba44210000300b5584400048031403209090a041640c90702d00d2029001c450314183c2001d0702d0061141d1202c1515154048400fa1104201c0c000380401754050210010710542000030b40044200c5c05204211101880401c00c0781c50440c21107005220702003600342c00700000d220003403090703010440500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 672771870 1250 672770620 672770629
    0x7030b0a080f0c01020114041a1801020a0807020c09010b040603020c030904050a1b0908100c0e031204090e03130515270405090f060c0a020a06060e09150f0402 70
    0x8001050050041491646a140181c00c1030002c1518030000c1c2d0190380f084200d560280076041c01a26242c02c3e14001d843c0503217582240210303c03081410740c44081c00000b41d001c1601c6d9002c42c10a404074008540302e192514015005650503903404e4050320452082000b1440c00b10344085c1031f580b500b407c0a00b0f00d40780c88016000b0350099120321007070b40010f0007885d28984030341c8030f068807a00048102050004010300150f210108078000d01c010030030941014030040000180740b4045016451000070000023030101118680d030f8081d000e40e03143c090300380316505d010380ca01c0142007a20000c1d01c2c108081d02481e5280b0b6a40c4c4101900925160710041e0200b0072850305550503040d2041101034240340211407410500c1503e1042e0040000550b510300c140100e080c54403506038012500401400503550421185a84c0d40005000c00c500c1c01001511500c2c50f4401c3c0441054075610a0040c840302da21103a841d0740c0d1260440b501101441650b01a0083c2070740a0b040ca8010300d444400e4443d561195020700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 672773120 1250 672771870 672771881
    0xf070b09060408030d0501050a050607050606090403050c010c0c150b091b0906030406270201021902031c02060f0a050c04030b04020f1c060e06060f041821020c04060b030703 76
    0x55501c0842400000b5002d00c0c140000e00c00907401c00c00004281d8103010800c03561840c50303000789002c2c400030f01c11680090000119203030400070480f0f4000c400d0b41ca61038200d0b081d01c100c5c0c032505259400c180144020a4000944102c002c0c1f00e80000429400390050074400c079128403016641c00081040411854000c480500b14410020140940b81100b03030004120f070356200761804c544440d9519120b185010002c002031884403100502d44c0f4104080d600002e5a941011072100c40751201240514110354013044039a264465046030720008081c114406521501c0c100d8a841ca131654000015040244500c00d0512829010700e8043c1800d055844840c4000001401240c004c040c64569107020759031504031449130314481d01c9841d1061010302d04074081d103890f0311070710003c1e510000c01c1c04820341c1d032a200c800448a040e0380c00102140324420901c84045d811a02900c0821150911031070360091070010080c49172a9000c40b10800b400c0340a11088030300600c181464a0018400300c1c0940e482038008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 672774370 1250 672773120 672773137
    0x1c030c0c020f03240108010e06040809190302130b010e0d023a210e0109050420070b1b19110109051005071b0b180a1208060a080f070b 59
    0x1100c440c1068048181401200201c40c0002c4c04481001044824024015000142a0702c009030469051a648500c654060b407480c80d8402c1d05c1540c040404d5480c007910312001140c0007000c03144009071502c00400288918801d1074001a9601d100c0c0b502403c14400803100994060101c05402c00b1481640030240110004049243d0303c40e50529810b2921804100040b40107c1000d141b406036004251200491400c14000380902c43e80510780702c0c0c2e0000701880888500340c1d03021030a2a00c0c1e8103941103c0041201d2410120342c0441e6420600102040c81482081c02c8440030011480c5148581c0c0b0b14082d91850340c02c01c81d8140d104000b070f18850320071100795209400c004030351214a41d4415042a003807100e4420102d81d1b4100b0841038640c041d4994030300c0c0c2c0300280358204001064880d0821440000d000350000b40c000703045066000c2040000c281030580140d1112441c4140100c0107041310401c0d21035074070551140602042000700422038000201c5501700900c05245410302002454222885 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 672775620 1250 672774370 672774373
    0x803071115010b040f09050702210c0618071a160f020616200145090b01171b0d0e0304050316030b0c03040804030807051c030c0c020f03 60
    0x68040418564a8100e40030300f242e034841a48450038014006000c416642c0710800c054102414000c0380398000c18160320703d81d0980804980b01c02c2c409849100340c421020b409540b84103090030030600705040039200500c83c0203441034916450740c0f5070200006208090a98003141c0701040a4003401e081c0542c88180ca070702c40c0246c2c00e448041d0741c002503d6600030845611803650170710070340d104000d446004111101f040022001c070900d58000001e241c4940407260380c000e203507110000d08042e0240512401c6003200080b445111080301c03020401d084d01301e4820450ba650400144c0403080d8045c000c2910040b02c190314403a260703035a08400140b48911090703910580c1c202081403500c000038900801c0c01e2420041c0c011580e643c80c1c1010305180c0a8a60b01a00c050300e1241d4007403002401025410742c120400c101d41540360740340d0b420000003e109581c801000d1080004028003004000f040e0380c0c1c1c11101800c084954904031200035030075120701075510000522a050000014a00102040c403c50000350 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 672776870 1250 672775620 672775633
    0xf061101060306090803090609120d23090f0708060c030a0213080105070507020123030c031b0d0b0907030b031207030e04180b07020a05150408160303150803030408030711 75
    0x407200d00c2250311009059448200c00404c0000c4054100071035904070100b20018115117842b1030700700030075014141802814540b070700c0100702a80c1c9101c003880b8800204225800143c149039070169070700e820091240700c130350061081c0001c0c8420080345040c440d41500034142d01d140d5030044218025800994075205001034908041281c03002480340c64802d002c1d9803151952140b0b540009090303011120302c00101100c15002ca0030b01828000142c82c1c111100200d01c6890f40c54a10b03c0c2d040d640018009080707040341c00314031545807003140c1d0000d51040f5002ccd07803440090388403c0b00440036074041e40d01c800e4255116540e00240080900000c14480d4060702d0084100081d03035000500341da441000901c08541c45204050503c42d4001070749800444074001000d4081170303a56215180c61107080e908000e48400400113060200704c0d030843c2c54800341480d2803030601420b840c0c0031300200a61001200c0000c2103030004103551100000300c90180e03401145050031a82d940c40101e91200701040001410f018a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 672778120 1250 672776870 672776873
    0x504050127060801082b03090203150405070303030e0a02031f1503050105101d07081306241203080109050604110a09030209070309020d0213110a030b0a0905010f0611010603 76
    0x80e1103541c0034002c1c90f620099203500d007651592601e050100210707140c03840c001e15600c0e04c080401d140283d031364031400e007c101c0741c40318000030f810702c1c6070340b6036103208255210100000c04c1408134482080c0c0c0e2180d201007001e41d0258441c1c1d69140c0401c00001e416074481d603d21000b1110401e09511940c582c00d5000c11020417034050030032119210341c400ca426a4480c0d0030310410b50705c445403ea01810b80c01c90381070b108140d41443e40135a03c070701801c44020300c00d401d0b01107007064000e00041c40e80e00d900600d0078030030008107440c194081b607441900441c80d81c90a020200380c0a10005034800401d0300b5550b048240e13424203c0354002404040c0107158040d982e00150050481740c00c015106204050300c0e01048a407443c011301940036401017030354041620300f114810050303948040003607086805407411052542312008010023011460022948a0008120517490640c1900308214103802030f04c060403215507070f0340041c0a1311030a008028041000c0e21042c4203035482101c1c984039200003000007141c010743d4bd = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 672779370 1250 672778120 672778187
    0xe01030f02091314130206070b09120f0a08070f02150c1902101a0d060c030b0a090903022b050c010209040510240906120b040e0307140d05040501 64
    0x551a0141c0c102c0d85450280c804d40c3d0600c0d00035507001074800520104c584480c1c0c00240700c0d21070713141e008000344214404200d541c1c80403c0364a07141d00d24010f00568620000417040020780001c141200020901030000e50303098880c14119600c0c180701c0d00203010b50000403d480450503801415101100c0c0d080c003928200304940005a50b9010840c2c01406011240d41e002d602645d04124005480c200d020b6074101c0182c0324101c4141806801c031400144092203064210041d090324a043ca45c82440c24002040d00c103901c1d8004581c007403098080382c440c0c1c40054103000420480f0400ba0b404000205140009103010704028020300b801540010700c2c240c4010000b88c103d683c03c0d94000c500c81c1c2c000c2001d101c05d481c1d880701e2804000c11003420003c282c07001c0c14028240c82c058000c0d401000041c0c103e450f804401e64001d990034942c000c1c0184100341007156029600c0c0c0080f0420303241445440b0761a4402c0c00080381c8443c008090303941d8149440e0900c40156032034040e146a0300c4000d24980c00d0b43c0802c980 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 672780620 1250 672779370 672779389
    0x201020c130c080a020403030507030e042d060608040b04021504030503030114040e010b0906061e040b07020102010c1106060108061206250e0a030611040308030717010609060e01030f0209 82
    0x5030300003900102c480c070020f011040003003040081c03620403c010b0000c00d4101040d544500e5040c60300743d8054642c040401c2c050159a600d01c8844212074020405000c2c000d00e078502c4a103a6040c080000540d201d40854959506030b4014007000040c0c004200941003484000c080304080b001c46610f03080e03407545e95500d1a4001d80c80305581007141f51074001645024010403100140c5c0000038403403240800700161891b074016110900c94200003545105102003428202e010002070394907651a2a5100040021a0700c9540101d0044d4600030a508840b070050b80800011003c80c0014205551a64010340c0c8075900645010703800951030020700000d11040000d01d114610b4155075540901c254985041020710b00c25070700040c891150f42d540e030320b030711340080f404200c039082a00414280e03c00980d0094900c99600054902940001048a10340d00320281003800000324001c0489a83d03210402c5690150307900545000886442c540541580702c3e4010a940c60410140146080c03c1070000900c0003d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 672781870 1250 672780620 672780649
    0x20909070c1106030c03163c030501080307110f0418020f0a1a161b03030909060e06060d1b26010503070302061b030301090509011a06030c070201020c 66
    0x44800c0341e200204200910140900503064481505500b0140b50344813190000805100900f926455a00da40c0740c41030100c40c014221481116074006564114403807084184c4004020490070751400c10041c43c42442854104c52080b0040c50500301180d48034041c2224202c40e1540c0840356018221180e51103208071000559011002c3c20304600f0b03031040c484030680054034184501d1850104015500c035840d03501d00700d034102522241d920074403464289048110b51030f02418051094401c20341910b4a008007106483c080d450380313118186e45070591002d4a940780600c01c0100c05280c0403a0480c100074020740700081800301d002c40e6001a10f07010440340c0320743e14050400200c1080081c50006c44c0c000c0042c040c14008111400f5a605243c0400e42c0e89095110081c090381c40060006250b40c2c140f4a00c0070b01f1111881030382d5503540d40d41d0030000584020344080c0c0503546880d00006501603038880304500c10001030100e904503500c0000d4000c1d01c1d00003200607815802240341d940d44540c2c0d1610800f00c0c46 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 672783120 1250 672781870 672781877
    0x403050a021302091807030b1203040501031d0604050105072d05071416180608120f04030c091a04050906010501120b130207052505062a07090c0216030809010302090907 74
    0x601d89100000e0a44240f18445800358649e010603e012810200c100e4042d01c000f82404103070382c12100a00d03002ca1940400b108218010002403004000040d04400c0c0034480d255220800003100d0030034410000400a62100c080056941c4001074600820203080d07000d01500c0d03d110303289400f200c500e040c4849003a260945402e640010702c50069403c1400d042010b20f0340c010410f0394108001a55a5405601542411032020940c00801c1041c0811103015640c00100c0030f0006948104802c0a1710090780341142d419140b8807004070314180761180070f126004130001004103074640001900c554280014140a40d91140320346078083d00c852160b5861618402c0006969460740d0403d02c1c2400369034101c49060400c0c556a00c0ca081e5030200101c8141c80040313844560360a05a1020414050751401c0344030700b4443d1400d03410604d0350103e0883d040380c0c80d600c41402003450141040341c03568824003507005404080d090600100304250090f10088006050042ca824945c3d40028101d803401c54160002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 672784370 1250 672783120 672783169
    0x1707060e0423010f0b07170d09020303040305010b010212121501030b06070f0b010506040e0115030b0405090607020d0f09120c050604120c0f060c03121d0102120c0403050a02130209 79
    0x2070244c50703022000410300c1070011401c0c04150380d100c61210580075208000084003242e07502c01c40c1c1c059800003c15aa0050880e035445d96245043c1d8080d0040c030350105d0250040c2c400c0300c0002036403e03003258030f4180070381c003000c115036182000c1d14803040281c0d0390036041682c0d0344004074158503890000c1c00414002d224200006000d45040c26054105030003040c019a000d000402294050a0303509054441011985151041c000402c034014040090801d07800350030001444081480491402d020f20340942c00e8942803501200309449051401030a8000030345e03100e004010010a415069000c14882c95034000140e40e20400180107400c203400155480086604001c2046000408200200014020099600c1ca007000240161600b480e018040c070907444032a0300d80034915488800510131040c0d040340340845a440c144d00035003080440c0c8110740d00e9000811011002c02055800f2290f20900070072058003d40c1c00c0c490400d16498041e100d10360248040c5401e030365066098000300d030440b0181081c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 672785620 1250 672784370 672784379
    0x151104050f0f0a23030a150f0504030e1c05070605090109060206040b27070e0702010c030b030d031e09030e040605240c030d02070b040c1707060e042301 67
    0xc07854181c098082c8074403919084914035071510f000c3c803000c4800d0001c105070500c1d4000d00310301c41d1200c01ca04856046c062069030404101c0103d52010100b0f01109041161040083d55081100c0c410390380507001c00c0c005800d0140500e01a051280c49044100042c903400000342c1d503080c071301011a0404d502007040480c0789111075a104c0200b00080038544020521424151624090800041c02c3c1080c0d40d80c5442080740000244600c1a40705402c102c1120707540c0e40c0d80d40c465103088000703442010055007420414030469110303028030411694002c4c050158041c1c0e481d0142e0080c0030201c0c42d080b03c2c1c03140f1076030090b009a052281c071030380320f00035150f2206c840744407001c00088030196080719128952024039a4102040b481540241800040c03000365243d40020209185007d2000c24012170790000074003c0800c428080c015008611a030901069a03445035001c601ea81030a5008004c50341c80140108100e502c10b66100046850190000036200d010382c8004c440240740c180d90881040e0070900400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 672786870 1250 672785620 672785629
    0x1b0604060b01080c1903110705030d090b060f0603221a0a050a020c06040f080d1508060105030106180203060109030b09010c020d02030a090614090603041406070e0a060c15110405 78
    0x103500204e4914418074110b14400c64201903403003181400b00f0150740c1c2e80c0ca500358800c1c80d000c89400c01c5c2c1250850740c5416507030780d0200c041c1034011812146c980c03240c0007003078003401c1c4020810300c1c0750130041c00c25084d5550208080400031071002081461102c031001c01000c0303038141d6258041c1000070308200f010b92911078044000e980c006070a00c0d55140c8100420590b00102240304d0b6001a880742187c407981d00e66042810050050341620054503242640b180020320f502140c002c2100c2c2445c050714080d0b0780e81c804240c01c0b00c2d8540315402d00e0005000b4066411a0ba50340203562150f8141020b0050645a0300d44054541003101c071210b00703079500c5000714000b603010000b580c51080d0f00d100031894075850880041013981644610014002c0c0c01e501c90940310f481405031801590082c0015440c0e1034681064040e44110051001e114001c6a0106044510440e240441c00c00064040c1c0062440c0500c125600e40607804259800c18124011042083c020b0140c20700d2800e12056503500ea904180401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 672788120 1250 672786870 672786887
    0xb1f0f080d1b080a1101150306110a230d0603080d291003270201090603110702090c090306070e040e064c1a031b1b0604060b01 56
    0x50144120002c0d008603621000c50210440380e0300c03141458984c620710b002510701c0000c00030b0b14102035003400302c1a085030f20600d04440450b801a1424800c1400c10100c50020340b00d003c8035000003441051002c50803c8505903118290340e07610700c543e850405080288402c03104c0682040381e4811000821030b2083d50103004d0303011102080182902c2142d4002c09000c1c1c001e6a5511182c040c42e209151300c0c85a5010ba800300f18440c1100c59000300c03082e190080b03924000c0a1401c00c0f80490a50100850f003980309104081003d80590442751a100300c580822604c52801030249d03d5002040002c01d1080d103042c00203a01584c0c036512080c015210190401c010f88004236684509039005108018008008042200752050f94050903000d0f401c3c42610f5080b1000c0d1820048150300b50803012031495180b800200c800c4400c40e00c41017806a86031290410907100590762444011203130150000da00c9110801000194000c12501c11000d002c1c40d400c6040c440d00300d42c01d5449960b6402180160358000919 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 672789370 1250 672788120 672788143
    0xc1b13110301091b0e010e040609060b040501020f03040806060409170a090906050d03080604090609020307030308040b07050a12051f0801020c0c060a05270603010b1c0209010c0b1f0f08 81
    0x42c507410000d1007000030301d0401d10707017122070400000d451402200d4843c0e030700c50000341c80105818002c2603203a070b0048150354800e100d80c0e070041c0b0503030084180184c0044103480640781c000d005400b144d01c4020030000034006444090784c000411841c0007064076405002004a1061038849103509803400700c0180854400354021405002e60740d07200d03400294020780141d44032608503400075945001d070400301c000300b8245d94000c2d09032040b4407021003856084003e261203148075514900c07943d602c031702c4119141c1c000c00c0565000300c0c00c04e4220042d640c159811030f40d4410768004031092404c0c0b02041d030a00c1c00005603c411000e942c00178580c1003003102400480518042503c4648c5040144c04006015104035254011454904003502c1188444504411081c00b8005c0c0b00351b0300ca584501e0200c0c05940099400102e010944600b54164003140c001c1d00c00e600704c16190800034806507220750701652001420307600d05459001440c00469801c41d100405004541c00703030000c4d981444035107442c00c070701d4206 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 672790620 1250 672789370 672789401
    0x150f04020315060303070209040f020d0f06180308010501050a0e060f040e10060e09070201090f0c060e0a030209011401140a05041d01180b061b0c030709020c1b1311030109 75
    0x10032000740c0380042103d004550540c0c015234035075240d0034421000340c004540203600c800ca1118820610060040017204c00e03005070b00c20041e101899046004007101c208008000c9182c140042205600940c083e2558800c0743c28078842200a10700020400d600240c3e01c402c00c072030301203424002c04d14480c3c0102e501000b07070840841008d01f420b0307000e424a0700001d07a00b03101b40744074400191018800c1d004140040c2d8000001c1403941800d240a82d0b401c4003a00502000441c07071a9510001d01d04036001c0b0003220b401a00d0455980d00703052400800d032a20b440528144206140290031a01000300100b180f05001d030b0350030b030729a418110703079081840c050701a178404218800c1c010321800c082c5a1fa5062503e08600000440c20090303000f281441c000c0340c107100c034124000a5900d001e16800308998882c902d048040d6a00039407141141812400350504002e03080d440903110780c6059402c2d00082c5410440101040c0882c10811000d6056400c01d0341001703154600400104142607083c0542c0c01464010030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 672791870 1250 672790620 672790663
    0xc0c1908100b0a150c0c12210807051806121501180909020d0b041b06031112070e0907020c09072d090b070602040302030d0201090b070c05150f040203 66
    0x1400644425601d0281300d9a40c010640e4120f103050107604c0000e421540140b0b5105820350310310343d81d2014504c5990650743d4107581301d6002410310042c480111030f19140d4a4001003525500f404462540041c03042c08000780281d002d078102c6503a14805000c1c13040840c0754840341803030029407108048861550141c103010700807406207440f8400b0b8842c002980d0a110000849504c01d0001444080d070158014002240a0060000b4041400d0460b8820a07ca003290074000350307500011030482d090b8801c4090f603550b09012031100358036160b1525801c11401d141403440348002c2c0f07002542c00481662400090303844000c202c942810300580a6a00405038109056040c015049170130b04005140020503054001c0c4010fa09150301a10500019000c010591601e4840c00e01d0108002c1d446408107a03c2403107a0021001030398414041e800305107034031010002c20340e00c42507015101d601049000319514055144010074206c0c615000c40c3c03081100c142e0410040c02c090052505099140d140c250301c094416 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 672793120 1250 672791870 672791891
    0x1f031b08060c1b0102040b04140f1909020c15070c05060c090a03120216080c03060f0103020a06050f0f0a030c0807030e03031b0c060103080304141c050c0c190810 71
    0x8400f580c800c59046408a0400504041e40a00a10594000c1071031f090002c5008240300b0900d990142a42d0410707035410410500c54000c10011941c20038010000c1407460505106990303d64015000c0d07401c00a00711081029034480003007414804450040010340c4800203c03041c00010021103800200202010345400c1201c00412224400c030701014044100216410b040c4501c2000641e08294540c03c440510b243c6882c001500c44026443e01c034464800c0d50045506865610f00190499600400103641c00380741960503100d542040150013034400041c030140d16403504006c0100040280c5540000c0c942c54014406410750001a11410805103425141040c210700041225001503200050f05280e0221550071100b900c54149488854010b5800020412401c00084c50050344541104203a0460140105980381d50800d02c1001014419a84808040c09240204118003e000503031310000010404a03240b5024a000c000b0015600703081004008000e0010100700d4209080901540030345 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 672794370 1250 672793120 672793141
    0x1003050403081617071823241204061805061b09031507030c11060103061a03010e060103050d02011a060c0106030b070f0207050a08030a081f031b0806 66
    0x402035080b003811008040011402100d00303101802941304601a01d24080000070b2070504040e030001c050020f04038000c01d03160b042503008041d0031541c10100d03040300054001c01070045080d142030070f00c0903201d5040c4548100842e0050609443e441e00381d00c041c1c24207107405d030100c0f00c6400a800ba414204000c0000145022840a030068580c1460482c1c084000f502150a0b10078400c44503854882c581a8001d01d44c1901007451044800f501d04100c00502d1503026140b0704000160040a50050f070014000139410340d00c15024814100d0404948101c50f0004c02c1c21941c00098070342955000710010070070041c0030001000030302e20301d04c0244964000c0c1605403014440404425105203008901598822030940c4640700640d0000300c043c4180c1080100070341807111041241c2c005002d03204020405040003156102100c10f84002140f80c501e80503130440c2c0c00c4034060b1920030742034a141c015421840c0c1d18a4041e01031030045107038290303c031348075140c20040d5810380d030054580b82c11030300400841404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 672795620 1250 672794370 672794387
    0x80a120e060d0509030d150509090c090a0f0906020c0109150e031b0a0503040f0f0509010e0109020703030e06090312010e0c090d0302010e060c07050f0705031b061905091003050403 79
    0xb0784007000c20180c4500b9200c80c00c40c003400000c000c002d0300e0240c2c2c0340c80c0754210850b048111002500c5001c1030b903d5403d8451303107806003428065044483e200202d1146441684550280c01010200080340015030313454100382d9001d01d6154045a440da132040701408680b1000418500058808010102c0b80c1c0c1c01ca186c84e801341d4030452600340d00c004401600300c10244018030358641c3c401c0550340d030380340c840c042100f5180043c0501c800101c0e50400c04140c40c200340c143c0e24140e602e6046034502c560301c0c10550001a5018800481c1010f444801e1042180020441c1600400708400030b5a216851940e021a142405038042c103a2100400c0074440341c0e9051b00d08843c1d42c0e81040d5910346900c0140d0038217901408610310301a443d40308070b608104001d80c1000150002c14410390a40e1195128a8607041c1d450520f4008c55506400c0003007051600055140d002c0c00c450009030900e814645418440851042c9440c0200301003400060500c10910b01048000d14024450a0400841c00e041d10001e00c04039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 672796870 1250 672795620 672795637
    0x90c010210090203010605060301030f120507031704030c06090b0a0b0f060a200307080307030507020a03020d08191107031812020405040807020607050a02010e0109030b0609041b080a120e06 83
    0x181c2d80c0001c1819501c0a41242025040290186d603803035035646000001d48075100340944c0c240074038140402000b40f0030411031314041d0705680c0c1d1101c038401002e514007108202400032400e0010000320107002841c28040c0c079a00c1c50290003441c2c6280f40a42c41c1c2c1040da14981e040742c0c8559012201d5501030340e0703982c0070b0f9020000545000012004801201d66020301426a0702001e440041181010000001d00841c4100305c1c6a90501c80c2d9124098140c1e0758940c10200100580c0204040605481c4039070b49003503004140d00c2050b48a810b540c83e56400321040e00c1100e907890303240094810189130300000003801180c0700c0090450614a0030101c0d0905003809080240310300c0d180c1d00420103002d045000e0f01e1699400900442d0b40b20300a1800c903a80d2551000101d02040d540e08689180d5070050310001c0440390802542c445980d1600e08001041000810854408003c500200c400794014640388002e0400c0c2c500811401002d41020665003a034030401804104024001d0b408170707141c0006481008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 672798120 1250 672796870 672796903
    0x5010e060f18120109060b0405160f0203130611070609150c030212390a020105131d09100c0f030b130218180c0f0706060302031014090c0102 62
    0x20071100c0e0301e0402c040e00d00494103074080d80329030900c0314200d81940a41c1102d807203144100208681c00c0e09210584400f00c80b1814030204044408040d2805204034004540c442e2060303a141c15060345245044444039046400019600e0469094040e000c10841d4003a1409051081449107480d070380705515a0214034100801c038002426008060080080001f07484c1c11880081e290884a0b0320308011200e0030f45000d402003100c0850044490b50340c1078100b0942d2540c405014000415001540c0990103000b808807410340b0b00ca000075907520008511004800713941c660104a0400d100c5082c54129005070001c1001d03e482d1410035800d03000801c02d007a00c1d409003808030729071100c000007840a800c1d910030000501d00000d14155046442408641101001c60344800d444c82142c031603411034030040b0f41440c1501800c0009201d07108030140a489554466180440c15640341e6000c01d08049035200008070164071090468010741a1460082d8000c440d031004242c41100700300000e5603409055100740c0344 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 672799370 1250 672798120 672798127
    0x1321170405190f0c060f0201050703090503161b06020d0f09240c0c0e0702190218041403040608060f0d0b0a0507090e1008210708031305151005010e060f 67
    0x4008515076860f83d00364201e10560b19141e6a4403002d861480101403a6005510301000201900d01912030f8021b45904500150708102000c2220401c1d0607003918262440715200d603150310a8640f290b440c00c00340040e0780c0540070102803240082c20441440c80c00000384000f03144103000d0200c2d03010600c2da41d403000703141390010042e00f440c0c01e8031075040134000034201065104000c2803c3e01c29413030b200d00480300c40d821981400340c002c20f0700042402c4224000e42c0320100307801d44c81a58904e04882500903026804c0e48900641d00d144d4030785140d01c02d510917000b180b030441c1049070610b808003200241c11415100c200003a0480c0d99420441d0304018035000310b095590300410b241911503d40540a010f02500410550038031400b424005410b500c1020281d200d81701042c890007034001c04007510301000304544c2d400d1504650340c4140c0341e00014a03480341303522a5140b45010034820407600001c0c0f41e0340324041009040071041070f00b0806041d00164140410080d805855844d1602102d014518200c81c080e01d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 672800620 1250 672799370 672799373
    0x5160b070e09070c021f1e0e0a03050a020a0504090b04020904031e09090509031603030b150409050906010b04060e2b080c0c0405040201090e132117040519 68
    0x401c00740320341c0d03110303086081101004007907604680c03034201d100e000319014a640e4170310020748034030b0140c1d00140400003150b80700352458440140001c4580c450307136410004040b0340f46601148224003d07920560b07041c2d12441e044425410041e80c20707405820700351030510800c00c1e05e0300d8205a001000e00024060280c4000042c1414824051002c0c0f144481c445101450b900f1440203050f0f0034140206481c1901e0100404c0711540c0000c01ca410790040c6144d0040031340107680b410380c0202150410b941c0c00950b003210080802603000c004201034200c141001810b4100380012515110050304041c802450401c030a0001f80e4201c2816141c6190494551400b111590101d00c04032844003000b4101035000c0348000200321544c006005034071048800c0380e04c560307030007820407040c0d43c41520041d01003034025105101c03441d09040d200d43e000300040090411000542d0f110134807050340c1c92610240b800040e40d03a00c1c500e58072828000400080130b20704280390a107611620303145c801e2841012100c00000400c0360 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 672801870 1250 672800620 672800627
    0x30a0e011b0503160506100807050613080303010608041115091e030a031e08010617072d0e010c110d0f1502030f16080f0601030915020705010c05160b07 67
    0x109420b42c4101965107a038102c1181c0c01804602c0201103c06015030b00c0001c0c03001403001c0007202140c01100c0203025051a020600090b03034000310324045100440500403030b021100300000c500030951940c40b045103151078240040c0c072049040c041d40c070850440c041929445400e10039a0030355902100d4501d1000d51101d1020f8502c891740c071007240c040c0102c4440800741600200740c2c05001d40401405403c44202380800c07200c03d0003d006a00c0801c04102480c007e108045413019807081d03580c1480a00401d0000241005015440f022448550215078401d0700d0303070303214100000303a510030300300307011034600c10fa44d4810b807140d0700540031b409908041c807440c00b441a45100c2d0540541c0091180d10190b4084c29480046c1d4812605242d8004180d03010175100b00541503818401d50a69881048945030194000b080c0318010b04500d0405483c4d0342850040780700d42040301020700c55600016980c0440c3d2403c1425203850502c0d4809002080c03020080c0140303d031403d80d40d941e5100c80c900719a90703104c1c08181c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 672803120 1250 672801870 672801917
    0xc20010c0e310c030e070303081605070212070503210315060909010608040b070c150e070f06033603050c030d0203090f0c120723030303091c02030a0e01 67
    0x500460700c4010050704942d080c2d0f8044008911203540901c1010005401c0d561344e02031500c00107000444100c0050b9a400e18220081a01071092810502d0142c00d41c000450300300c030355a040507958008d103004200e01d16081000b502441e0020b056504006c240d40304071040e0b80030040189400811361080b030500d80e510300e41201c00401c8002c1c807100ca1561181da00030907410044400700c900c1001c00e408104200c1c0920141d0b44815848081035614040000b5a00046c0c6510010155548220036010a200100103440e02c0604200d540016021801c0b14144070400041c15844826001000c1852000b901640c61101141d42504060341c0e81c0b0301c85c01086103980315201020207100e101109124503190040b44c40c40040c0400000c81f541807072044204110901c5c2c204101c070040d800b03d001080b2041c0b000c40100c040b8500044565440d14519003c24110307442181d225205801c5160849040c2c1d5141200c070088540910040d030401c108c0703160203850305c948644054103006d01d05401d104281c0d40460319 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 672804370 1250 672803120 672803179
    0xc1d03011122050609090604180510090b1f0b0708090603040f11040b011d041b0f0906050f0d0b0609030a0c050a0b030613020c100c20010c0e 62
    0x3825035440000045040c2d002c0d01c0c1071041078050070104001000e190003c181c42003200c0080002840352212000c0000419601c0708050b4180d21170000540401d801740000c1000d13006070b000100300500c103458101541c4030020103a0352002840d1921010305000c0391a07450664400c03c215590328182400c0c1110140a20f035001540450700200f00000c2005814038125514452200701c0b03840c00c284800c00c42516103040f15a400980801180700180b00070f01d80b14010820040c000089281d000510850320b0002c0c440444003040b0038801c0d2000c2d0b140d11041100c010074851800318180700b1a03024613610340c481c2c403041c4080107448991100351a0b844001300c4100081c02021141200c0d4140390000500d6801c0c41030700c0c40380c000e0b0f0310000b44220b01042200d102e498003d00c03201d880010a400700b40250000b9524007001d100b03042108034030324824400d07401c00b9007031a03d540780d4800d0b88a0554585520f039003404501641420b090080c03054002e840c1c140d00100840300c50b040c505003090604500c4042091 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 672805620 1250 672804370 672804401
    0x40806010b071506060210063303060306050f0f010b0f16060608031201030512040302030309040207030516080c011b020a030e1302120f10030201090303140706061d0a0c1d0301 77
    0x41c0010080d800161341f4058004046051011075510360800b40b21480085e10b154406a402802d03840f10000301b000d0880d14051810001440d90320307a00c40008a420464109603080143e50a200008180d03001550040031603a00e1103103002c2d001c00622000340a4113200f1401080d88000c88010880c2c00e4004034041d1002200b201e480b40440c3e0980c1c00303038041c20700c03042d00c3c5030141c0845a00b499040b001120256900500110300e404c0d1100d0030721009501c411400d90800c80144400c40c01c1e246002c1c0f007022024090311040b521610380303804c1d40382120b8105c0c031000300484210010100c22500869503500e845d425085c041300524408020411180003092140f603600c0c80000c42c0316a201d4013154041c014806210104401d945414407150418068000a0b001c10301c00401040000d102c2e03480390123070141c2c807110349040616968500c1e09030f0380990082d00c9401e1480000303043d04040485001c0e80505400c6082c08060132a010280c0035011200c40c00741240007101a1107001c1d202504507002d680302204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 672806870 1250 672805620 672805631
    0xd060f06200c180f0a061d0405031917090a0f0803040c05210c06040e01210818240406030b031f0b180702060c0723061b040806010b0715 60
    0x44083d5400c1412195040d402140350081a555403180c400c03d401d0392243c0840c0015a07000043e01c0501c0d030340080003110613120810a0044032180c504407101071410a4851444c03c0c04a582c000081d084001d09032a90f0b0f83c001d04410b4041034482a8110b03101350007113007181d641d032194140028495200e030041500400040c81742d000c84c694070001100d0407403080c41610f0541d100902001424440e0348643c80580308401d0060155522444000c0c60101240111190300f90307055032200304030f8108112888000d0f8200c0c0c9010080c0c14408404158201c11400d55454144c0501c1c3e110910b0189010320b40400d9070780d02103500941ca04000160841460100f180d0302e000c910700d5900083c0c4102c1d0703050350049a40703840001d81c4100c0b00b12454010012a0080c04643e614003401c81c150b9000148199000700e00241c42c602d21003841c4800c1e809125074a4050001450b00c0c860141c14505403291060407001c00301700812090750007155a9042da00030191150f900c030218182010302c02c002c404502006032400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 672808120 1250 672806870 672806899
    0x120070b19031404120c0f05100e010b280905090102070501060501080c1206012f0d0509010c150b0603010f030614040f020d020301020c01020f0d060f06200c 69
    0x40001e80003000c02240d41020451019008900b69698104022210010746020800042400c440d44904411500d8004055116074442e00b00380640988140c3d003a821128403401a41128040c030712105103248024014200007a02050584001c600c042d960343c844441440c00790703110000c03403400802e5401c07024003681c100200901c0c000d62041c04111019840c2c810006460350140c103403c1e11400242400d2400d180c0d030b05e120f00b000345c3c10060015042180d29004400003900041d10700c0824100305a01c00f800b801c216030b8461170140c14a010a05000047c06402000d80e031040d202d1441a9110750035020002460403e08040c0900c2690258412004400880c49145030308541044034090f490501500b103914106001422055a0240070711074025044009800c0138421103c2551024000500d4180244401800c98122400340410304030300080d202000b880901610b4003a10b14441e405225614100e8041d01003036029038a11124045500e89400314031040c0801c261481e0064000620300e10f0ba07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 672809370 1250 672808120 672808139
    0x10207050f0706170c0901020709021b0609031e1e1b0d050403020901032907030606120e0303010e0c0909010f33030b0a09060e062d012007 61
    0x340c405204920070a4800200c0c14811420070299660002c4c0c0c20100e61290319001c40c503a44422480c5055220305c400001d4128107910041600c3c0050784401a18009035256050420310301424a0310f003179005225994000d4100100700d0003030071910000690300c54100c4c81015800e104407c40105041e00402e14103000004510840710400c3c8070020341c2c07229071900380243d4443c001ca01003c0d400005500050000900004090466007c003415400100307032400500000400115800c1001a40310302c010081c0c0b642101c1c080c0390507010114180f10302400c1c40c101c03903500e00051050444d40b4070500302013441d511400d4100c1c0c640c00c001405000c282d41e15125080440052441409003605603801d80301d1000d000241021840c0c0040282200d501502d1502100648071803102c1070303800020384400180402d82c9108080061000343d0b90900c82e46001004c01c4035550000b84402140d038100b42a06002e0800a80100d04140c800d080800481e43d4102c0c1e20070300c02841c8020700e04188036006000c140c6109 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 672810620 1250 672809370 672809383
    0x1a01060309030206101a030406021b010b031515090c07050a0b01051002010c020703120e090a0b09090703050601030f0602040b0d051503030a0507060b0d0b01060c050c04050c09101101020705 83
    0xa40803644c141c0c07102d104001c1c02c0c0c502c2c3d00c90a0f200600d13010240c60200d886000031030f041400344001500300448030400300c14080b03400801c800715a641d1212a11141005e2024446030030440744142514601014a020a6030320007040c644242c20810004150391214801c0d07070555604030040313404803901440e200580880a00500c0c3c0700d000c04044007a4654414000c0c542c046485602034040303180307181d4500075441c401041c1401404401300ea80079268448001d024428203a405020071a41004400c6c00090a00075000900d5034120f000309101003000054031504480d44400c030b400d9420600d00f0100000c0c050780c1c200c4a02e00c0300009045200006030381045000d41c01425034541601090b1040550300d10503940000042641400020f02143c03003580070056a210140c140d10512101e03503294814181d098225101182100d0311000134001c04201407e010181614100030a082400d0714826900502d03078224403d00d580c00c034140d0345030f01c1074800e282000740c0c0030001d540f42c41083ca440e036241c16 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 672811870 1250 672810620 672810623
    0x319090b0a020a030b0d0221032506060f0e0f0a0902040c02010902120f120c0102040b0715060902030106091401110601140111010b010906050c011103130209061e0d1a01060309 77
    0xa0170310700943d9551030910b102d00441913000b0003040342c20b8110074219500f004201540c04950100703003c400d050300c45100178860405800c01d0442d0540000e49410012284207412004800307000040038404210844c06a640098400c030701440b0a07540c40e4041e50140144510081d085030601110305030494054010840640c82180c0c407421400d401c03802d00b07990b0b103000101c290b00d0b42e0104013040c8003642c8400c028900f00b28180001352805454003d850580e0b408010210303001290010181c1d10034441d813152138040c0100e81e400b9481d5501d03090000301608403e01441d180d842c071280150b1120f0703014072691246803080e281034a40641e0b40c0d01d00c540c110301101c0f00e0b030b5021440e000b4040c86030302010f101e01d10021074141c4402803094113055003140c1c0d170b0f00440c0c10b2502c1596035903101c9403400c9a41014600c25490a00d1010200c2e845105105808802030400d034014049030000c1c16100803050303200e022402e4161403c403280301c1e05050040f42401c201248110f1403010f0000481c645078103070040046503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 672813120 1250 672811870 672811877
    0x30901180f030c050f0d080316020322050a0b0a020604030f0318060608150f041209170105070e090402010c060b130207080705011b090b0f0f190201051b0319090b0a020a 74
    0x488002800750301b02c588040100320000402c00036042150060704078004000c140704882c2005d4045040c514641c03100c0110b07030200031804004000c5845c1405941c2c01500303030000c10354103081e400306020703644402c0940000c0038010150400300440303210781e20410340104100a41c944c07402c118141600101964020250b40f80142045040700c1d45440744440d004500c2140c54941c160f503280c139905904820170b4010400c03c0055140001c10065150034200c2245403d4000251800d02034805440c15801083c4c00307005171b00d100304100150313811144190380e0f1a0000d001051a02c80600006c0c3c4940b808000c510301107102050860070b00220101911020344076000030031003491302820149291400342d8801c80000d404440c103001510b9014040d100d55415501e085083c102150b943c1d12643d009030004210f2518050201d4607000d9090080390780010180800b02c10518100e610200386100051055180190b54040c7d0002600a0781c40900055006061540b4a040c8801548007a60210310040c000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 672814370 1250 672813120 672813139
    0x2030705040e07030b091c0e0f1e0f04020c10060306050a0203100b0f041214060f0702031605030702041107060b060910030e010b09090f01051602030901180f030c05 72
    0x46003000d210b0505240d0020009040c0c562131641c0d124070040b4000d01140e44d0b07004039080d92441500c1c0381c00c211224101c175203c1c208000c60040a1001c800c0089100340d1003110403030518009500403500c000c1010200b0341d02c2407103940f50a40498068860304050445501c924415180e001c40c0325400401907920800090046413560401601640800d440310344088070b10400030042140d00d540204000c48800402d00c1c00d084d40c82400485070783c00e412065038000c00007520f9801821043c07003c641d2018140c07000280c142403440c0000d42e24002c1e015601500410312200c0410701408006490f004c0354024804e0118204101202460b90440d250454075542000104109494100259100ea41c0c0240c00403220a40c660802c4000d44140300c034000d03065507900641e480d2500e900781c038644034511840c020b24440c80c028850608485004180044c007011006100b504a68048101c1c0d00441c806d203010140801544913003e01400c0c980d10480180001803400420000c2d400704050031240c040301c13983c0c00d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 672815620 1250 672814370 672814379
    0x605030109031403100801090c0509070305150f060f0f0c10140402010c08091005090a140d0602030711030705011d1603080c0f03030f0f0105010c330c0804020307 71
    0x81e544000d9004001c11201003040303508908440146600c0000c910305060740640e202881421100b09081c190342454407888284054100f500d42c0a4214031603280410442c41c6c8060218440c80041407964800c0180b10201189940d4500556200c1c0c50041d14865540705e004191000705e5012540030380084c09100d0078500507006521074401c05500c140c0e0001480d035500d500442d1000c0901d40100c4030a401403294070200e880d184001c1c081400d241e103409503941460000c000c1c0103a89076001407000e00017030001801d00e07268200503801d00c0394030540141c0c49450f00e0a054a807603107813400120782840b010480c003007840015041503907019107d01c40d11446820350905940c0301c201052201c221884000010400605068010000003d2540c01d8888800507400024110b034070540d0750080d80e680d008244000e41c11003951450050401b42058005007955654200d22101081601c080d02d001c01c421a50340b0300042c6180c41d407800410401009207014895000e8803035075040c0d805030b0080c880e2040c0400c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 672816870 1250 672815620 672815623
    0x180b010905150a1719121b06020307030603020a05030c030703080c0a1403030615190e13092111120a140d0203090d110c1905060f1803161e0509071101060503 69
    0x1440e030400d01c41c04070501c03410010754600000840c41007c1c61a900040000304500b071000e135010313000c284e0b4040b031038511358010800303c820355810640c401d4000b112800710540d0001105000c50f94404030f03140e21021340f480b41d54102107400310080d1400c02e80041c400ca04000c044010f5100d03610071103c0d1010b1071404944000c850160006154144010300d00340c03030740d160103081070b034855150013041402484180c4201609035011180111402e000b0100800710405004071038400080035403a20841d01d00022103040d903120803034070718404290f500113050300d941d80c803441c00c1c0c00d141120038518603070390b8000400105c025030046440c400940541c9803912500c82c03103458a0f0b10301d03400c035000805034503956008000c100c40e500d01e10701c01007180c0701d0000287c3d41c42d42d030301070004208001c2c4059114450444816142e103a0034030b055200c2c0e0401140b00300200c81885244055a2000e40b20154580414031b0501040b0102c0d005541d101c0860020460a1344d0321071603882ca4008428002d1180c00e68950030f06 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 672818120 1250 672816870 672816913
    0xa0c1502061e060307180606031103090d12060801020a0807020c0109050306190209090106030c0207140607081803120408070501091a13090903080406180b010905150a17 74
    0x6540441c484980d1000d030b00300544201d078000764000c0a03a95066074030704130100c0d4416601038100e0101c0e01c41e101007284070707058440c080c84000075070442455490300c0b0150648515440301810240100b00032034410001d61980910040d08240008664420b0003c0d0083c01c0c62100300d92841c0144103084a4082c2035115452035012a04081c00400003920307540981c494100112030078001d25a403d11030446143c0c0c50080d0380d4000d0800c1e0314001958010400e000341400360b141c00400c0d072642c210303e802805807180401c0390002500000c425444060300e40c400c84004465030341181d40751281c07100611006004000034011204004119540940c0d64401074500d0070031032054010785401b14001c81860491000101034400c001000c1c00c0c41143c441004208035601003800b500040c94842c200310420440e8480d604180850f1404801c1c404142da0700d4200485050290a51003502c4002207064000d0b11000c98035581e2004080404242c1c44501d003038801075031644403140b1446600b2190b43d00c2156040301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 672819370 1250 672818120 672818131
    0x110a060617150c1b01110408070e0114040903031e0b040507021b04020739050a080a02040e0705151201090b090f1312050a091a0403110d050a0c150206 66
    0x460b48070382e6a03034a850b2019040282400c401c5592000e000f41c0502081c856854904c40c08078076070f91030303070308261086240000a80100300001040e40050000340c0784c945851411041c116404203c9081c5454101c01030900300d40000011080e01c1c1440032480c6454219680801c0140c070700300720542d01e0f0101240d807045904c0610138540e071003040102050402c1c2d002803e4003800780171100d010710001c40c0301c030426040c80210a9a40308510362118401138404d84082e00802088030040056414401829154042c01d14020711031640c0395a0f185c00e082c0180007010042c01c1c0208010f15507445031540d200c1507844208005002201a400400c14540c0d13480780349880d0002904405075070356210f0b89100641e4014244801925100002c000003a20b205c1d42c2d0400403106a48aa03103855540c10082c249016540041040c40040c024210001c5802c034161002c07250403001e0203403c6480e240206140400302580507269014090b8010140420354610504446102d28500c4c4807482c0d06c002281c641c40107941 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 672820620 1250 672819370 672819403
    0x1103091b060f03040813081f0b01050a030f1b020d110a0b0606030a02121e0f0115030f060503031201181a09040203011506022503150903110a060617 65
    0x202c0c407540c00550007440d032040c4a6940b05241c81e50030340000c0b441e04040e030320001003075200c66100608600300200c415401484560b041c400e080f03040b000a000c902907056402d04140e5181c80c1c040c03100d6210303040600c10060801c00e900c101ea400003002501c40300c0781d09a00b0301042d42070103480c002640014400d40b0150f00720440e100140c07103107000c2003060303880a052240f00f25020f0007013120469800840502850005060180b840c0f11031050f03a001c05d0000b048036110741c4101004122017181100403c10001d140c0c6400142c9400380000030000b4030407070704615003501c40459069000c04101c084203050751321004083d0310140c03840c501c480c10b546000d2000a0307403640c201110314003800c0c5a00440c2e00f191008001003143c564040c0c0c03a07911104075074010720060b070115035055000c1003407094400c680104065502078081c00c50311200400040e9140303c1915903652480780052502c14010356060881d201c040c2c0350040554100302000d810540941c03240001103d100e03044100c40060400769030700c3c0f40c19 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 672821870 1250 672820620 672820627
    0x3130f1a030919081903050103060c020c010f080601030e060c0705152202042301030308160207170a0507080f070906061e0909090309080d181a04091103091b06 70
    0x664600c4080844482200c0c851420305c0100c540c100c10003a07112243c451540d00242a6146091000944292145078019500300642541040c0da111190800c2a02c8074200a0358a45034080100d0080010010351040c90056005110740403040000506076640610b044820b0101291845c0075000c10035602d01d0101030481d034210007803a01c10001361400a00041c8001000c0340c910110342e0440404074a25050f0601c405d006104068102e801c041d01b05c068000001110003c0701c0000e0350b01c1d10701c0d0040050380786410480025001d000c1091030541907018056400003561281c030b042d51080401c190403064010500003003201109403244030111840c84e6220840b48413411180d844000195060208001c02d01c2c0002c2000e181038040c100303100d44030703036103841340a03107844410350901d8101c0003148100600c50010062101c9030006250079500c1c02d100310b601180c030b82c1b554811148a81c0c6d00180c0c1e0581032042c44d0351a401c0403009540b00341410f0094421649410750b03041c404c00002650f0a51115050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 672823120 1250 672821870 672821893
    0x6020c06030115030f020406020c01090f050a05090408041e060e15070b0a090827041107151416020c010c122609010203041b080a03050c03130f1a0309 66
    0x1841c1c0600102c40714103000400c05d03080f8115100740e902030b81201c80541d100303440e0407800396884103059005040d501480d500d440c5c2000000b49001001e442161321444180002c6400c2c080408100c0700104082900e11903031080405100758001817620456011810302004041607040000b0004810074010b03101500d01a410391712114503180260482882540d230f003284100051503100101030611700440d582244000300398102c0641384544020350f0040e81042c000e207042c10002c1c41035910540d408014a01044030921059000b4107803000d03061011140d100c107100c13800e035402564261400003170f802c0c2c031521681c0318010b588104c411b010050000100106400400e4880d0104d0594035140c3c0042003a00c0a6885101c2c03288081603400c05000e96001051104200d194208007014039205081c40c0c584900d0158040d48130183c0c08400f42c203101c1c002503d13055030982401224140e0054030000000c0940313544450700b5000080c01990440100043c1c000c0742c1ca510310017a01e100303180c044001c0c1480e0249 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 672824370 1250 672823120 672823139
    0x1050901080a031b05190b24060706090213050c0307030606050705150702030d06031a0112080306011b0f060b032406120109140607090902030403300606030207060606020c060301 78
    0x4002e081e0f40d0f1b03001d00c00f21012401510242c2e51156805103c0880807820b0480c40c008219000c06845180645120705082d0191039040580e42400c0c3c01c418000342140d29030011496110100c107070180b1440c40c14007006490755111019601440181d0340c104102c1c1d487d040280d0b660710400c03c014101e80d00c141c03d4042c0100389035102c00ea000b006841501e081440c0b03199400144c4420380c00c2200c00704008075100c05a800c00e00521401031040d8604c08410303082c15128032115200c090401030420401d41d41c00410480348400d80040c0b20f41c400c042c5070440404c0d041000080a020304018841d010b400c08150203c3c1c5e01584601c12000e401e8820760380c94a50740104021500180c0540c0300654031500d203580030404c0c0d0342210149500300000340c0303120b00d0200c800400201084e04105070061040c8144000320342d00000340076050305602d0180070402846121221443c00300458040342a09100d00429a25410380281030b54a01c5900244819600d5180c00c0e80c440e0b200c8244180c100d6402c0c80100155440c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 672825620 1250 672824370 672824417
    0x7060504060b13090218070906030e01110d050603013b0a0b0f0f0f1e071211130506070b07270329010b0406050a050c100501050901080a03 61
    0x455000007a000b11044003180514401e03802c1031214035503c00029003942448000f106408813140342c00d2403940b80034800580072603010302a5104040d070785c60400a04c9002507114419002440c0c013400d44400f403882060b00549011901940607500700700200540c2124003400c1c0396990302040c2c1500d030002c0a01202500140000c0b40caa0140c4a00800c81020800e202036181c024540ca41c40d10a031403031329441d00c548040e0080e2403440e100036460100a0b43c2c0500c107100021218030082201c20300e4481d030400b241d1258403888495030680c43c7c40c00d03803480c01c01c11000400d107006401c51800c0c08079560313404000042c0640c40700039094044000005224038401e125031900521150030350407481e20039080f40910300c03800e60021195600800680b4804d00900991160743c5912580804c1d210741c104841c03241640518482c040601c5000700f00340c41800e01910a0721440000541118031046110170340c8005000d0a2203064007421f81c40d0300101d0041c4000c64440c00301501500ca00c41b1281440f0300322006180c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 672826870 1250 672825620 672825623
    0x3340206042c011401020f0a0206030402150909070e040614181b0403030c02090f070c081605030f03550c080a05070c1a0903040b0c010f05010506070807060504 70
    0x342d0b03104400700c0345081d02d10140a800e10707854010740041a40000783c0340c40c61004c43d4400b0396024076001e20060392a202241e40c03181d810707110081380c1b01c1140540f0000303004401446078080410170030040201d600500120300740c0760884090140039519003500c080011031700841178200140008814020507034885d655000002020700341d0003141c003501d1180e40e42c3c11a800440c00102d50320350010030340c030f4a0718a150b0041c03801c2000191506044101828000c10000002c00020022038155000854010030660f1181c10405a03641c540f074011009200d81c0c4111002d4070494428549a002e45020301002c505481c105050300b00d07860f01300d0442c0e44540c9803a01820a80f0000c1030076600c60305880c5d02400040344400e0f147d003040742c1041a043ca0694078000c0000d41003081c00d051100102c0c0086480320000b260100c5041841e480d22200c1c581903210300d400c48408050005400100340e0740540c00040c2042e85103100300074598880c4100050351081440113002520300384034120110300180d210303a4101c2d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 672828120 1250 672826870 672826919
    0x50c0d0215090a030813050103050c031e060f030a0b01030516030305040e0a060f0602160b180112060f08070609090b220b1504030c0b07120f020c030334020604 70
    0x41c0d0344e0f03a52025a94045003038819503404a5104101c1035070580590b64001c3d80d520030f00c9066103400001d65101002c0881c802580300301d0b00b03000c10f0b180e40b1400b180c60781400d80a400c0c0d50029103542854104100280b0045545104e14038140c200c80c2c07a62301d01c03101507940c5550b4082c5017034a010100504404003403c511846035468100080840001c90004010310107078004d4810000c5038060030300c2e800482e9109103400c0904002030404900c450135412680c00c024204550743e40d8034660b16100605d01034000000501d0703010804608030f040090050122004c0345d59201040e6240c1d04940d05450b0b8000d101904800815220903012080b0000c0c2146002c42080c00621022024002000e11840800300031f029100000c042c420300c202c509004012303010000c121460a0030540c1d540080c107000360541000c00045401c1c25032528405c1c0174114803020000c084075120307003003000d02001c00c3e4150000e601034041417050228440740011048516543c0003050281018584290b4510340081340c161660300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 672829370 1250 672828120 672828139
    0x302071e05012d08090c010c0503090103090f0506130203100c080c0f07150f11070506040620071505182a030604050a0203060f01231c050a050c0d021509 67
    0x14004682c203c0c0311559010759aa8000742400400503007003046100405040007076080540012420001c00c882400100b0300e00000e03040280e013407044582000c04c100806034000c03002408a02840312845401040c02201a101e004815a5014023102c0400c02e082003c078102034000766048c00e20002500320442c05007012807418000d5918541c040071056003140c052a4ad590b000ea40d0a0307094458080b40205043d0f01620b845d0f0740381c031044e0380c400c401480144019280c10040707928840b40c0a101c1030b581e50f91808241c9400552134000da10303108414000d000d262500f40011002c050030210108010315042c040d00762010301820313814048480040c0089040c20b102c080080940701045031034481c90140000e8590300d00548101400e011015080c01041d0340d401d001840754081040074644a03102141c00740554005240101d03400240184a1011036034100b03604009203c80401c003130140c07034418030550300041e41d81e804100101da00c07810081c0d00a1115406004100709000080203800e000030450110b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 672830620 1250 672829370 672829427
    0x3051804050901062c1807050d060b0f0402042d05031b0a0603060602120a031401030b0a0e1b0f240414150a052101120302071e0501 58
    0x5451080c0d88000b5540e6407250100b0421922012140c140d140341082101d03086420030000b00c600001034003220507007442d02c0300d1550304502040300800178003016021241c0450a400c0030f200800c030721031840d80100702c0b03401d52800ca4a400c0c42214147d6035001440c12403520710f000d002c560900201c1c2c4400168100f15408550350340e040010208010103000c100301000c0d00e2000348824240c2caa40040e00741401c061081c402c854000c80c40f41c035462118050151246000312b4100c000c1c100300380403d01100e62100000c0b050095281d0014450005c254007441003c5040c00b205a0b0703a650440c3c00f03904400e00804080c0c4505d82642c0e50052140014500105c0c0d07400300e022145003012044001e945014000b03401c005181c1c0340b129140c5d43d205c0440d0249a90220080b00000500c10300c00003900700a000160314412000d4818001e071020081e5210389019a100e08070709121624410040e80980b0550800044180d4041c11081d1054200b540002c8114078040042d50629949101c0c540c0041d2103000228 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 672831870 1250 672830620 672830629
    0x30f080912011503020f0a152106090207050129010302210915070306150c15050705041406041412030c06040503180f03071a0405130b0a0f080a030518 66
    0x82059210f6038900086841e500c10401500b000c517030024001e5603030660800c9030b010301040203120700e01c01e81481500c4031024440d0009402c49400d1003005240351100100f0103220751340c05004020310660007001110380c0f11200001a01c8204880c240c01e11540c040b80240c1d501c02d4002d00300b04800162881d41244040f03000c44842201260130241c158000c0700040314280c039151489411100506040080d6420207240004061100e8024810702103010045d80411a05401e59840c1e601031079000c110078101240001c0c01c5a0062081380f054241e9000c070b0400614040c1c0c101c2c2c00b01c0c0c08184010841112950611500309420124003985001c01c1c810040c1402c03050000c184990b108a002c0c581d01c5c0380f0002c41c103400720007082035507015120000680501d51000500d00069400b08881c074034183d140801400480c2c81150005600300c4441c99101d101520650014955410120342d00603205440b860281ca101040344240d00d01c6910070203082d00442c2c020002001840b1000c607021006010540208 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 672833120 1250 672831870 672831881
    0x5070c1e08060c0304031b05060f0c04150207171902040b010507020a03060b03011407020307060b0a0b0a021501140d030c0602040f0b030402010201060b16020f0a0e070f0315030f08091201 82
    0xf0150440000100b2040680c040e860081080c0807040a841c0c01541e40c81d00303541e59000400050703182c5540d001080c04006010242c070300810300d00c10074107074520b5144002522600203104401c0c0340440c00702c040321302031008107000d9601000503423102c031060506d40030400a8908000c0302030510404002d0600980c4402c0100d03000355010b445c0100710707105a142403608541004031011102c0c000101800f800d140e022045500e065000040410003500d40750006103c05203507400f54030410710010360242c0c0385402181d00707002d81c11944044c0c80140c1c0c2c5c400e0043c003110301c2c07164080c2e8040c032440c44c00000039004800c9076403040e0241d103005060944400712501e002c0c0c502d4000400036030020040004544c1d0900030b4501030030300c00341d10300d08007a01e500c07003e20300f1461000001d200b40e003061034000c07107038444009441c0100b64010318190302e030800300009003107040e561a4103000203003411519444851100308050807258840c1c0b1240f2010182c0e2035001460708150101a407150031126499020b400034080c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 672834370 1250 672833120 672833131
    0x1061e110d05160812041b03110603091f0b0901080c010f081f03031106090a110d11090a020304050d02060c040902160c03030f0e0a0503061602101407080705070c1e0806 74
    0x2c0c0307941406c00d420640c4079403e020a2102c680344040205100145260794941c440020986da42c64680d213a0720b80705801c055010407c2442d01d03011607080402207101d42c20104001e60180e0f15400666201c101145d240c01c181404140403c0b00310b0f140f108842d10800302c49902044c1e00c10040c504a80c0c5a00100181348264400d41c00134000d1001703042c440d0424043c1c1d90300108420000d0102500079034038812130740c1440404521072000c0c03401890601804401a03816103800400403403081c42d281030810000e400940f02a1810721481c01581d600c2d0b40000f0f5001d026807406590b45051900d80b81c1e881001e54403990034020100307034064403140062010117080c802303107100351a40705c1010307880c0780000c28011030200e0302c0384039124100d010030442e100855815080010070710201481041508142c0c58043d0081d80000f0f180d1038400340190507108441604d02802c0980da0f500207548850301c0803070b6103000d100409000310a4005080003010307026580c010000c100f9000d44254150b8421405003050404c840 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 672835620 1250 672834370 672834397
    0x712030503240d060b130f050f0912120604110703020f0d090b090d0219030c03110609030312090715030e121309110d020301061e110d051608 62
    0x61050402c442c10a800d100e1a1100100700080d0740358001584400310200302804aa5a03180007038056218001e404100f1880d00c0070900c821801054103000400c002c443d0700c200b01c0c40100110710035003c0840c50328030309a0440101814040c0c0c003440d00850040141402d64001d68601115185903c100e0282090034081e801070310155240780100c60074a06080d403c0000c20580b40d500788140c51f1181c0541c0c03200070f003d807000c000c1d04840f48082081c4e4064144103031201071a008000bc10005000e848600340c1c0d100d06200a00000c4d89030030f02c120b0b40128201c266142d0003d0120084550402481603484150303d01100c13032070703035841c20301a00a2200300b09640c00662252081d5030980002c101d203840c600d000100061505403030181c55032007204640039281c2803e8603001c80b5064807000c602030f16600e4002c1d0f5011503403541d4500c0081c1840d00a184038091007590040700c02055801640310b94801213140004e0202a551100111034a41c040303c925002c1043c001d2440c004900000c0240101085210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 672836870 1250 672835620 672835627
    0x70e19020d060b190e010c2009180708150a0506030a06020c03180d0203030a050a02030c0d030c121509200304030305071112090d08071b0f080705031203040507120305 73
    0xb0f2018103199044d4800014002024a510a10390b400741c000b074281f1784c0200c0368021000d43c040358407400444004406522400903818803281c07c5c645031180f080000a18121160607559240b030b243c90b1046814507a0200c446e00c00021002c11143e08281e9200e0401003d5601c2074095648440490304140d0b0410560b50002c940307255030b814480b0040131031078000c13179903500e01b080305a000036500c0c419159141c08201001c54426040c500130410340e268040030300c007540c0040030000b03c001c00601507a8807440004285000004240301c041c071420b0390b00c00700380c14101c00c0306e400c15022801810306040e51070008240c49100341004083d40f001f0318000c0b480b03564049018140484020001c0403014448407140d00030003260001f9400013811071302100c4003a650b509000c40c1c18104040d85014400000d0201100861110390a9440e00c07004002e43d20a50401007100d80c60f010440c0d40c60815004030b81d0182d01110010407825201070243d80d100b4400d500302c03283c003501c400c00340d900450401e01c21008500f020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 672838120 1250 672836870 672836887
    0x100f240302120f1008011b05090a0305101b08160806010207050d1b080d08010303081e07020115060f080c18030d020d0f050a0e010809030c2a03070e19020d060b 70
    0x2d0390500405c0c0c901c000340000c0054401c4401d1044142150005101d40011419502e4507104024401180c0110030f170340303084007010704d41000340ca880700950b101041140100e100c964020300b0014000d1060307220001c00b0641048003500c1ca0500a800b0506512a5039400200e039500c244455416900c12080025a88515000c100d040045500070003500c1d0800510080c40e29444074006045a4041c40c00d80c2d11034540113402d10411504503400c440604800e410401802d0701500080c041e1441026041c009030b0f510030003122101030725a0750000040311040070a00c0c2204160240c013101881d004104030b800c2e802400a441c00b01061044c80141c1c000c00e003154441900400d42d16510401410101d107031084204000389440000c90255044c01003440120b05c0c8060704206959002480c80215400417481c9404a0203610120702c81010038901703c081c01249040c0400c0304c6044419801d070064150321101c03845141210080042d0300d189070b0a028002c01085980281002046511034443d600d8080c3e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 672839370 1250 672838120 672838141
    0x50f010603110f04020f0d090c1203020a0b0906090a03110f0a03121a0f0618060d150b040b0301120302030702031006140d0b070c0f1a100f240302120f 66
    0x100100f030384901e1061040703108841901084030341149403903100003010038440c542440c1d24021038000b0f107801180c441e10760040640002d0071032509802040100d05541c0c84420055440104a0350000c072600855031140c0024083d21248254072b440005a616060056900d10720303084504000b40d0004e408400c004183d40090b1040b0001c41003c1c0140c040352512540100d4003600444100c00c1c000c2000269825902024404040c1240c0c0c0050105541d02d08014240024100351080c05882c0d0203035003400280180000220342c00c9450000c001803c680c645054100c145285caa029410b42c00200074200060383d081c40705030382007a0031100000e15a400e00c040c04d0400240b4401c41c0c2d000d999064002c40c0801c10101540f6070041c0c00d4645030210710b01034501402a12402c810050106000740220000d090440859500c594400b040000d140e0342c1d650f004c1c808403441481000003004140300303804905061214201c01d00040c50801500e007107200c3d680e550100c501200c814407807030b94102c2841210707001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 672840620 1250 672839370 672839389
    0x12f070c03050d05120c03040f03052d0315040e0d030b01170702150603010c02070e0a1103090c030d0203130b0901030905060a0e070801202a0d0305240904050f01060311 74
    0x6d51240780c90842c5400d80e6102007030a180c41000d4107101002c143c40764207a56450301c0e00160a07450784011180c00e2080440ca14580055810201500c1403c8141d5030500303192007400c001e020b0384402402c2200002100341e0082000307504940c100a00c810700200d20704186460305018071460b9000380060341c0200900081c4007400343c102032180e4144004031075040c3d07000070014280d4501c401e006010b038a426003060018804c0020f8072030000b20100c104100c100300441e049800031810750590b40c0018400200b04e80728070581d810100c030995000ea0610660820b0030142c0501c90040c1000602c0c0d81e22911054a480021151503114039101e0080c880c142070240005c00041a281000780144440c0007051700c1c09503c0022000207802c004500d003407201d20000e514407008050361001c40d4800c242d0400071500c4800c00782503074000c02d09004c041380c0d002c401d4000700100c090800310501c440010314000c220316a9805081030359144070740494916102c80078800d000045208126402103000c2c0d52051000501c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 672841726 1106 672840620 672840631
    0x7050a1716060203040b0106141204150921090b09091017030301060315030c030308100f15031a0105070f06060305030a0e03012f070c03050d0512 64
    0x10b900079030117540601c80c800c0c6d03da80ca641c0180e482c01012043c04500543c1084081860704c80100283d40084c440e4400312258100c40e546041940d034286403c2d9030040d00c40c0a681c1d600441058481c400380c0003403d18241080c41c085100d42c05009105405008408840008000000e829241c40c007418003200310041c09003540d0200d5036690000d000c1d100201c0e1501c60095219640034804000720b0342c0c04080e0780f00c01c60131980c0446198001400d1456020464140452120542c807464009001c6070036030755521881d109001400d03150001c58518103d01040e054558070b0f40c1c081c084803400c81c1c104500b800081554a13004004145944c805402c6000c0400c1d00d250f0b056022011120b289001c43c0240040302450710403440c14200030584190381b25814a502c7d201201c4107001d8080d070b078052200011041c0d0359850b80c41c10564030000020002e1000105884045040841c094100 = true := by decide +kernel

theorem cover : BRFrame.Cov 672661870 672841726 := by
  have h0 := BRFrame.cov_init 672661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 672661870 ≤ n) (h2 : n < 672841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
